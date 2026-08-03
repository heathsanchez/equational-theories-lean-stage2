"""Build the four Stage 2 entrypoints from the provenance-clean solver core."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "submissions" / "mathgraph_cleanroom" / "solver.py"
DESTINATIONS = {
    "solo_gemma": ROOT / "submissions" / "mathgraph_cleanroom_solo_gemma" / "solver.py",
    "solo_oss": ROOT / "submissions" / "mathgraph_cleanroom_solo_oss" / "solver.py",
    "marathon_gemma": ROOT / "submissions" / "mathgraph_cleanroom_marathon_gemma" / "solver.py",
    "marathon_oss": ROOT / "submissions" / "mathgraph_cleanroom_marathon_oss" / "solver.py",
}


GEMMA_PROMPT = '''PROMPT = """You are the final proof-producing fallback for an equational
implication over an arbitrary magma in Lean 4.

Source law: {problem.equation1}
Target law: {problem.equation2}

The deterministic solver exhausted its replayable proof and countermodel
constructors. Construct a checkable TRUE proof. Your text is inserted after:
  intro G _ h

Here h is the universally quantified source law. Introduce every target
variable, specialize h explicitly, and use compact `have`, `rw`, `congrArg`,
`Eq.symm`, and `Eq.trans` steps. Never assume associativity or commutativity.
Do not use sorry, admit, axioms, imports, declarations, native_decide, or prose.

Judge feedback from earlier attempts:
{history.attempts}

Attempt: {solver.round}

Return only JSON:
{{"proof":"<Lean tactic body beginning with target-variable intros>"}}
"""


'''

OSS_PROMPT = '''PROMPT = """You are the final certificate-producing fallback for an
equational implication over arbitrary magmas in Lean 4.

Source law: {problem.equation1}
Target law: {problem.equation2}

Produce one complete Lean file exposing `def submission : Goal := ...`.
You may prove TRUE from the source law or FALSE with a verified magma.
Never use sorry, admit, new axioms, or native_decide.

Judge feedback from earlier attempts:
{history.attempts}

Attempt: {solver.round}

Return only JSON:
{{"verdict":"true|false","code":"<complete Lean source>"}}
"""


'''

GEMMA_HELPERS = '''def call_llm(context):
    print(json.dumps({"call": "llm", "context": context}), flush=True)
    response = read_message()
    return response if response is not None else {}


def extract_llm_proof(text):
    if not isinstance(text, str):
        return None
    text = text.strip()
    if text.startswith("```"):
        text = text.split("\\n", 1)[-1]
        if text.endswith("```"):
            text = text[:-3]
    try:
        payload = json.loads(text.strip())
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
    if proof.startswith("by\\n"):
        proof = proof[3:].lstrip()
    forbidden = ("sorry", "admit", "axiom", "theorem", "def submission",
                 "import ", "native_decide")
    if (not proof or len(proof.encode()) > 90000
            or any(token in proof for token in forbidden)):
        return None
    return proof


def make_llm_true_certificate(proof):
    proof = textwrap.dedent(proof)
    body = "\\n".join("  " + line if line.strip() else ""
                       for line in proof.splitlines())
    return ("import JudgeProblem\\n\\ndef submission : Goal := by\\n"
            "  intro G _ h\\n" + body + "\\n")


'''

OSS_HELPERS = '''def call_llm(context):
    print(json.dumps({"call": "llm", "context": context}), flush=True)
    response = read_message()
    return response if response is not None else {}


def extract_llm_certificate(text):
    if not isinstance(text, str):
        return None
    text = text.strip()
    if text.startswith("```"):
        text = text.split("\\n", 1)[-1]
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
    if not isinstance(payload, dict):
        return None
    verdict, code = payload.get("verdict"), payload.get("code")
    lowered = code.lower() if isinstance(code, str) else ""
    if (verdict not in {"true", "false"} or not isinstance(code, str)
            or not code.strip() or len(code.encode()) > 100000
            or any(token in lowered for token in
                   ("sorry", "admit", "native_decide", "axiom "))
            or "def submission" not in code):
        return None
    return verdict, code.strip() + "\\n"


'''

GEMMA_FALLBACK = '''    for round_index in range(3):
        response = call_llm({"round": round_index})
        if "error" in response:
            break
        proof = extract_llm_proof(response.get("response"))
        if proof is None:
            continue
        code = make_llm_true_certificate(proof)
        if judge("true", code).get("status") == "accepted":
            return

    # Unresolved: EOF is intentional. Never guess.
'''

OSS_FALLBACK = '''    for round_index in range(4):
        response = call_llm({"round": round_index})
        if "error" in response:
            break
        candidate = extract_llm_certificate(response.get("response"))
        if candidate is None:
            continue
        verdict, code = candidate
        if judge(verdict, code).get("status") == "accepted":
            return

    # Unresolved: EOF is intentional. Never guess.
'''

MARATHON_STATE = '''MARATHON_MESSAGES = []
MARATHON_OUTPUT = None
MARATHON_PROBLEM_ID = None
MARATHON_RECORDED = set()


class MarathonCandidateRecorded(Exception):
    pass


'''


def solo(base, model):
    prompt = GEMMA_PROMPT if model == "gemma" else OSS_PROMPT
    helpers = GEMMA_HELPERS if model == "gemma" else OSS_HELPERS
    fallback = GEMMA_FALLBACK if model == "gemma" else OSS_FALLBACK
    text = base.replace("import heapq\n", "import heapq\nimport textwrap\n", 1)
    text = text.replace("\n\nclass ParseError", "\n\n" + prompt + "class ParseError", 1)
    text = text.replace("\n\ndef term_depth(term):", "\n\n" + helpers + "def term_depth(term):", 1)
    marker = "    # Unresolved: EOF is intentional. Never guess and never ask an LLM.\n"
    if marker not in text:
        raise RuntimeError("solo fallback marker missing")
    return text.replace(marker, fallback, 1)


def solo_deterministic(base, model):
    prompt = GEMMA_PROMPT if model == "gemma" else OSS_PROMPT
    return base.replace("\n\nclass ParseError", "\n\n" + prompt + "class ParseError", 1)


def precision_base(base):
    replacements = {
        'COMPACT_SUPERPOSITION_FAST = {\n    "seconds": 5.0,':
            'COMPACT_SUPERPOSITION_FAST = {\n    "seconds": 1.5,',
        '    "maximum_term_size": 90,\n    "maximum_replay_term_size": 420,':
            '    "maximum_term_size": 55,\n    "maximum_replay_term_size": 240,',
        '    "maximum_depth": 20,\n    "maximum_rules": 900,':
            '    "maximum_depth": 12,\n    "maximum_rules": 256,',
        '    "maximum_rounds": 96,\n    "new_clauses_per_round": 900,':
            '    "maximum_rounds": 24,\n    "new_clauses_per_round": 256,',
        '    "maximum_clauses": 60000,\n    "normalization_steps": 384,\n'
        '    "maximum_proof_nodes": 180000,':
            '    "maximum_clauses": 5000,\n    "normalization_steps": 160,\n'
            '    "maximum_proof_nodes": 30000,',
        '        for _ in range(2000):': '        for _ in range(500):',
        '    local_seconds = min(30.0, max(0.1, timeout / 30.0))':
            '    local_seconds = min(4.0, max(0.1, timeout / 30.0))',
        '    local_seed_salts = (0, 0x94D049BB133111EB)':
            '    local_seed_salts = (0,)',
    }
    text = base
    for old, new in replacements.items():
        if text.count(old) != 1:
            raise RuntimeError(f"precision marker mismatch: {old!r}")
        text = text.replace(old, new, 1)
    return text


def marathon(base, with_llm):
    text = base.replace("import json\n", "import json\nimport os\n", 1)
    text = text.replace("\n\ndef read_message():", "\n\n" + MARATHON_STATE + "def read_message():", 1)
    text = text.replace(
        "def read_message():\n    line = sys.stdin.readline()",
        "def read_message():\n    if MARATHON_MESSAGES:\n"
        "        return MARATHON_MESSAGES.pop(0)\n    line = sys.stdin.readline()",
        1,
    )
    old_judge = '''def judge(verdict, code):
    print(json.dumps({"call": "judge", "verdict": verdict, "code": code}), flush=True)
    response = read_message()
    return response if response is not None else {}
'''
    new_judge = '''def judge(verdict, code):
    if MARATHON_OUTPUT is not None and MARATHON_PROBLEM_ID is not None:
        try:
            with open(MARATHON_OUTPUT, "a", encoding="utf-8") as output:
                output.write(json.dumps({"id": MARATHON_PROBLEM_ID,
                    "verdict": verdict, "code": code}, ensure_ascii=False) + "\\n")
                output.flush()
                os.fsync(output.fileno())
            MARATHON_RECORDED.add(MARATHON_PROBLEM_ID)
            raise MarathonCandidateRecorded
        except OSError:
            return {}
    print(json.dumps({"call": "judge", "verdict": verdict, "code": code}), flush=True)
    response = read_message()
    return response if response is not None else {}
'''
    if old_judge not in text:
        raise RuntimeError("judge marker missing")
    text = text.replace(old_judge, new_judge, 1)
    llm_pass = ""
    if with_llm:
        llm_pass = '''
    try:
        from marathon_llm import call_llm
    except ImportError:
        call_llm = None
    if call_llm is not None:
        residuals = [p for p in problems if p.get("id") not in MARATHON_RECORDED]
        residuals.sort(key=lambda p: (len(p.get("equation1", ""))
                                      + len(p.get("equation2", "")), p.get("id", "")))
        config = {"model": os.environ.get("JUDGE_MARATHON_MODEL", "openai/gpt-oss-120b"),
                  "max_output_tokens": 60000, "temperature": 0.0,
                  "reasoning_effort": "medium", "use_seed": True, "seed": 0,
                  "http_timeout_seconds": 600.0}
        for problem in residuals:
            if time.monotonic() + 15 >= started + budget:
                break
            prompt = ("Prove this implication for every magma in Lean 4.\\nSource law: "
                      + problem["equation1"] + "\\nTarget law: " + problem["equation2"]
                      + "\\nReturn only JSON {\\\"proof\\\":\\\"<tactics after intro G _ h>\\\"}. "
                        "Do not use sorry, admit, axioms, imports, declarations, or native_decide.")
            try:
                response = call_llm(prompt, config=config)
                payload = json.loads(response.get("response", ""))
                proof = payload.get("proof")
            except Exception:
                continue
            if not isinstance(proof, str) or any(t in proof for t in
                    ("sorry", "admit", "axiom", "theorem", "def submission", "import ", "native_decide")):
                continue
            body = "\\n".join("  " + line if line.strip() else "" for line in proof.splitlines())
            code = "import JudgeProblem\\n\\ndef submission : Goal := by\\n  intro G _ h\\n" + body + "\\n"
            if len(code.encode()) > 100000:
                continue
            try:
                with open(MARATHON_OUTPUT, "a", encoding="utf-8") as output:
                    output.write(json.dumps({"id": problem["id"], "verdict": "true", "code": code}) + "\\n")
                    output.flush()
                    os.fsync(output.fileno())
            except OSError:
                break
'''
    new_main = '''def main():
    global MARATHON_OUTPUT, MARATHON_PROBLEM_ID
    if "JUDGE_MARATHON_MANIFEST" not in os.environ:
        try:
            run_solo()
        except MarathonCandidateRecorded:
            pass
        return
    manifest = os.environ["JUDGE_MARATHON_MANIFEST"]
    MARATHON_OUTPUT = os.environ["JUDGE_MARATHON_OUTPUT"]
    budget = float(os.environ.get("JUDGE_MARATHON_BUDGET_SECONDS", "3600"))
    started = time.monotonic()
    with open(manifest, encoding="utf-8") as source:
        problems = [json.loads(line) for line in source if line.strip()]
    for index, problem in enumerate(problems):
        remaining = budget - (time.monotonic() - started)
        if remaining <= 5:
            break
        MARATHON_PROBLEM_ID = problem.get("id")
        MARATHON_MESSAGES[:] = [{"problem": problem, "budget": {"timeout_seconds":
            max(1.0, min(300.0, remaining / max(1, len(problems) - index)))}}]
        try:
            run_solo()
        except MarathonCandidateRecorded:
            pass
''' + llm_pass + '''    MARATHON_PROBLEM_ID = None
'''
    old_main = "def main():\n    run_solo()\n"
    if old_main not in text:
        raise RuntimeError("main marker missing")
    return text.replace(old_main, new_main, 1)


def main():
    base = BASE.read_text(encoding="utf-8")
    precision = precision_base(base)
    outputs = {
        "solo_gemma": solo_deterministic(precision, "gemma"),
        "solo_oss": solo_deterministic(base, "oss"),
        "marathon_gemma": marathon(precision, False),
        "marathon_oss": marathon(base, False),
    }
    for name, text in outputs.items():
        compile(text, str(DESTINATIONS[name]), "exec")
        DESTINATIONS[name].parent.mkdir(parents=True, exist_ok=True)
        DESTINATIONS[name].write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
