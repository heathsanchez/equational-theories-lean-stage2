#!/usr/bin/env python3
import argparse, base64, hashlib, json, zlib
from pathlib import Path

PAYLOAD = "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"
SOURCE_SHA256 = "42c96092bad4b03ce13ab80df927675b65ab65225bff1d971ff328949a6ef7f4"
TARGET_SHA256 = "3d6e5848b615af7ee7565e33a8ef835f3454a1094fce8a6dc346a96e9795235f"
TARGET_BYTES = 427661

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--source", required=True)
    ap.add_argument("--output", required=True)
    ap.add_argument("--max-output-tokens", type=int, default=65536)
    args=ap.parse_args()
    src=Path(args.source).read_bytes()
    if hashlib.sha256(src).hexdigest()!=SOURCE_SHA256:
        raise SystemExit("source SHA mismatch")
    lines=src.decode("utf-8").splitlines(keepends=True)
    ops=json.loads(zlib.decompress(base64.b64decode(PAYLOAD)))
    out=[]; pos=0
    for tag,i1,i2,repl in ops:
        out.extend(lines[pos:i1]); out.extend(repl); pos=i2
    out.extend(lines[pos:])
    text="".join(out)
    raw=text.encode("utf-8")
    if len(raw)!=TARGET_BYTES or hashlib.sha256(raw).hexdigest()!=TARGET_SHA256:
        raise SystemExit("reconstruction mismatch")
    if args.max_output_tokens!=65536:
        old='"max_output_tokens": 65536'
        new=f'"max_output_tokens": {args.max_output_tokens}'
        if text.count(old)!=1:
            raise SystemExit("expected one max_output_tokens site")
        text=text.replace(old,new)
    p=Path(args.output); p.parent.mkdir(parents=True,exist_ok=True); p.write_text(text,encoding="utf-8")
    print(json.dumps({"bytes":p.stat().st_size,"sha256":hashlib.sha256(p.read_bytes()).hexdigest(),"max_output_tokens":args.max_output_tokens},sort_keys=True))
if __name__=="__main__": main()
