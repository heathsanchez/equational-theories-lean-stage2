#!/usr/bin/env python3
"""Small model-specific audit of the verified TRUE fallback prompt."""

import argparse
import hashlib
import json
import os
import re
import signal
import sys
import textwrap
import time
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from judge.verify import verify_answer
from pipeline.proxy import _to_judge_problem


PROBLEMS = ROOT / "examples/problems/sample_200.json"
BASELINE = ROOT / "experiments/mathgraph/results/compact_superposition_promotion_summary.json"

MODELS = (
    "google/gemma-4-31b-it",
    "openai/gpt-oss-120b",
)


def digest(problem):
    return hashlib.sha256(
        (problem["equation1"] + "\0" + problem["equation2"]).encode()
    ).hexdigest()


def equation_variables(equation):
    return list(dict.fromkeys(re.findall(r"[A-Za-z][A-Za-z0-9_]*", equation)))


def prompt(problem, feedback=None):
    diagnosis = (
        "\nThe previous candidate was rejected by Lean:\n" + feedback[-1800:]
        if feedback else ""
    )
    target_intros = " ".join(equation_variables(problem["equation2"]))
    return f"""Prove this equational implication for every magma in Lean 4.

Source law: {problem['equation1']}
Target law: {problem['equation2']}

Your proof is inserted after `intro G _ h`; those three binders ALREADY EXIST.
Do NOT write `intro G _ h`. Begin with exactly `intro {target_intros}`.
Here `h` states the source law with arguments in source-variable order.
Derive every projection, absorption, constancy, or diagonal lemma explicitly
from specializations of h. Do not assume associativity or commutativity. Use
compact `have`, `rw`, `congrArg`, `Eq.symm`, and `Eq.trans` steps.
Do not use sorry, admit, axioms, imports, or theorem declarations.
Do all planning silently. Do not explain the proof or repeat the problem.
{diagnosis}

Return ONLY JSON:
{{"proof":"<Lean tactic body beginning with target-variable intros>"}}
"""


class RequestDeadline(TimeoutError):
    pass


def _deadline(_signum, _frame):
    raise RequestDeadline("OpenRouter request exceeded the hard deadline")


def request_model(key, model, text, maximum_tokens, timeout_seconds):
    body = {
        "model": model,
        "messages": [{"role": "user", "content": text}],
        "temperature": 0,
        "max_tokens": maximum_tokens,
        "response_format": {
            "type": "json_schema",
            "json_schema": {
                "name": "lean_proof",
                "strict": True,
                "schema": {
                    "type": "object",
                    "properties": {"proof": {"type": "string"}},
                    "required": ["proof"],
                    "additionalProperties": False,
                },
            },
        },
        "provider": {"sort": "throughput", "allow_fallbacks": True},
    }
    if model == "openai/gpt-oss-120b":
        body["reasoning"] = {"effort": "low", "exclude": True}
    payload = json.dumps(body).encode()
    request = urllib.request.Request(
        "https://openrouter.ai/api/v1/chat/completions",
        data=payload,
        headers={
            "Authorization": "Bearer " + key,
            "Content-Type": "application/json",
            "HTTP-Referer": "https://github.com/heathsanchez/equational-theories-lean-stage2",
            "X-Title": "MathGraph verified fallback audit",
        },
        method="POST",
    )
    previous = signal.signal(signal.SIGALRM, _deadline)
    signal.alarm(timeout_seconds)
    try:
        with urllib.request.urlopen(request, timeout=timeout_seconds) as response:
            return json.loads(response.read())
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, previous)


def extract_proof(response):
    try:
        text = response["choices"][0]["message"]["content"]
        if not isinstance(text, str):
            return None
        text = text.strip()
    except (AttributeError, KeyError, IndexError, TypeError):
        return None
    if text.startswith("```"):
        text = text.split("\n", 1)[-1]
        if text.endswith("```"):
            text = text[:-3]
    try:
        payload = json.loads(text)
    except (json.JSONDecodeError, ValueError):
        left, right = text.find("{"), text.rfind("}")
        if left < 0 or right <= left:
            return None
        try:
            payload = json.loads(text[left:right + 1])
        except (json.JSONDecodeError, ValueError):
            return None
    proof = payload.get("proof") if isinstance(payload, dict) else None
    if not isinstance(proof, str):
        return None
    proof = proof.strip()
    if proof.startswith("by\n"):
        proof = proof[3:].lstrip()
    if (
        not proof
        or any(token in proof for token in (
            "sorry", "admit", "axiom", "theorem", "import ",
            "def submission", "native_decide",
        ))
    ):
        return None
    return proof


def certificate(proof):
    proof = textwrap.dedent(proof)
    body = "\n".join(
        "  " + line if line.strip() else ""
        for line in proof.splitlines()
    )
    return (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n" + body + "\n"
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--true-count", type=int, default=5)
    parser.add_argument("--false-count", type=int, default=4)
    parser.add_argument("--max-tokens", type=int, default=8192)
    parser.add_argument("--request-timeout", type=int, default=90)
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--model", choices=MODELS)
    args = parser.parse_args()
    key = os.environ.get("OPENROUTER_API_KEY")
    if not key:
        raise SystemExit("OPENROUTER_API_KEY is required")
    problems = json.loads(PROBLEMS.read_text())
    summary = json.loads(BASELINE.read_text())
    accepted = set(summary["sample_200"]["new_hits"])
    # Reconstruct the complete 181 accepted set from the clean result when
    # available; otherwise use known labels and the frozen residual IDs below.
    known_residual_true = {
        "true_1698_555", "true_1604_1822", "true_2860_3458",
        "true_2061_307", "true_1738_1258",
        "true_2654_2864", "true_2789_898", "true_2935_3138",
        "true_2135_2128", "true_1500_498", "true_691_1976",
        "true_2771_2775", "true_4561_4566",
        "true_2055_2656", "true_1636_1839",
    }
    true_pool = sorted(
        (p for p in problems if p["id"] in known_residual_true),
        key=digest,
    )[:args.true_count]
    false_pool = sorted(
        (
            p for p in problems
            if p["id"] in {
                "false_907_2534", "false_1682_411",
                "false_2370_1248", "false_3145_3481",
            }
        ),
        key=digest,
    )[:args.false_count]
    audit = true_pool + false_pool
    records = []
    selected_models = (args.model,) if args.model else MODELS
    for model in selected_models:
        for problem in audit:
            started = time.monotonic()
            record = {
                "model": model,
                "id": problem["id"],
                "expected": problem["answer"],
                "content_sha256": digest(problem),
            }
            try:
                feedback = None
                attempts = []
                for round_number in range(1, args.rounds + 1):
                    response = request_model(
                        key, model, prompt(problem, feedback), args.max_tokens,
                        args.request_timeout,
                    )
                    attempt = {"round": round_number}
                    attempt["usage"] = response.get("usage", {})
                    choice = (
                        response.get("choices", [{}])[0]
                        if response.get("choices") else {}
                    )
                    message = choice.get("message", {})
                    content = message.get("content")
                    attempt["finish_reason"] = choice.get("finish_reason")
                    attempt["content_characters"] = (
                        len(content) if isinstance(content, str) else 0
                    )
                    attempt["reasoning_characters"] = len(
                        message.get("reasoning") or ""
                    )
                    proof = extract_proof(response)
                    attempt["parsed"] = proof is not None
                    if proof is None:
                        feedback = "No valid JSON proof was returned."
                        attempts.append(attempt)
                        continue
                    attempt["proof"] = proof
                    code = certificate(proof)
                    attempt["certificate_bytes"] = len(code.encode())
                    if attempt["certificate_bytes"] > 100000:
                        attempt["judge_status"] = "oversized"
                        feedback = "The certificate exceeded 100000 bytes."
                        attempts.append(attempt)
                        continue
                    judged = verify_answer(
                        _to_judge_problem(problem),
                        json.dumps({"verdict": "true", "code": code}),
                    )
                    attempt["judge_status"] = judged.get("status")
                    attempt["judge_error_code"] = judged.get("error_code")
                    attempt["judge_message"] = judged.get("message")
                    attempts.append(attempt)
                    if attempt["judge_status"] == "accepted":
                        break
                    feedback = attempt["judge_message"] or "Lean rejected it."
                record["attempts"] = attempts
                if attempts:
                    record.update({
                        key: attempts[-1].get(key)
                        for key in (
                            "finish_reason", "content_characters",
                            "reasoning_characters", "parsed",
                            "certificate_bytes", "judge_status",
                            "judge_error_code", "judge_message",
                        )
                    })
                    record["usage"] = attempts[-1].get("usage", {})
            except (
                OSError, urllib.error.URLError, ValueError, RequestDeadline
            ) as error:
                record["api_error"] = type(error).__name__ + ": " + str(error)
            record["seconds"] = round(time.monotonic() - started, 6)
            records.append(record)
            print(json.dumps(record), flush=True)
    args.output.write_text(json.dumps({
        "models": selected_models,
        "true_opportunities": len(true_pool),
        "false_controls": len(false_pool),
        "records": records,
    }, indent=2))


if __name__ == "__main__":
    main()
