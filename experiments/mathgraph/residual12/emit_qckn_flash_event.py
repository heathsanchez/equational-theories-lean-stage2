#!/usr/bin/env python3
from __future__ import annotations
import argparse,hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
DEFAULT_EVIDENCE=Path(__file__).with_name("promotion_qualification_summary.json")
AUTHORITY="sair-stage2@run:32700065430"
VERIFIER="lean4.32.2-platform-harness-v1"
def canonical(v): return json.dumps(v,sort_keys=True,separators=(",",":"))
def h_bytes(b): return hashlib.sha256(b).hexdigest()
def h_text(s): return hashlib.sha256(s.encode()).hexdigest()
def build_event(*,source_commit,evidence_path=DEFAULT_EVIDENCE):
    if len(source_commit)!=40 or any(c not in "0123456789abcdef" for c in source_commit): raise ValueError("source commit must be full SHA")
    raw=evidence_path.read_bytes(); evidence=json.loads(raw)
    if evidence.get("status")!="PROMOTION_QUALIFIED": raise ValueError("source evidence is not PROMOTION_QUALIFIED")
    cap={"capability_id":"sair:residual12-portfolio:v1","input_type":"sair-stage2-portfolio","output_type":"qualification-status",
      "semantics":[["residual12-portfolio","promotion-qualified"]],"guard_inputs":["residual12-portfolio"],
      "certificate_id":"run:32700065430/artifact:9510286240","dependencies":[],"authority_snapshot":AUTHORITY,"verifier_id":VERIFIER,
      "provenance_ids":["portfolio-commit:76ef25c02bd660efef75d752355214a84d9243b7","run:32700065430"],"cost":0}
    payload={"capability":cap,"oracle":[["residual12-portfolio","promotion-qualified"]],"support_ids":[],"origin":"sair-stage2"}
    event={"schema":"qckn-flash-external-event-v1","event_id":"sair:residual12-portfolio:v1","event_kind":"capability_admission",
      "repository":"heathsanchez/equational-theories-lean-stage2","commit":source_commit,"authority_snapshot":AUTHORITY,"verifier_id":VERIFIER,
      "source_evidence_sha256":h_bytes(raw),"payload":payload,"payload_sha256":h_text(canonical(payload))}
    return evidence,event
def main():
    p=argparse.ArgumentParser();p.add_argument("--commit",required=True);p.add_argument("--out",type=Path,required=True);p.add_argument("--evidence",type=Path,default=DEFAULT_EVIDENCE);a=p.parse_args()
    e,v=build_event(source_commit=a.commit,evidence_path=a.evidence);a.out.mkdir(parents=True,exist_ok=True)
    (a.out/"evidence.json").write_bytes(a.evidence.read_bytes());(a.out/"event.json").write_text(canonical(v));print("QCKN_FLASH_EVENT="+v["event_id"])
if __name__=="__main__":main()
