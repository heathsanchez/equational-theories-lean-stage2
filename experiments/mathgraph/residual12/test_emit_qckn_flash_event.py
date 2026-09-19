import hashlib
import json
import unittest
from pathlib import Path

from emit_qckn_flash_event import build_event, canonical, DEFAULT_EVIDENCE


class SairFlashEventEmitterTests(unittest.TestCase):
    def test_promotion_qualified_portfolio_emits_capability(self):
        raw = DEFAULT_EVIDENCE.read_bytes()
        evidence, event = build_event(
            source_commit="0123456789abcdef0123456789abcdef01234567",
            evidence_path=DEFAULT_EVIDENCE,
        )
        self.assertEqual(evidence["status"], "PROMOTION_QUALIFIED")
        self.assertEqual(event["event_kind"], "capability_admission")
        self.assertEqual(
            event["source_evidence_sha256"],
            hashlib.sha256(raw).hexdigest(),
        )
        self.assertEqual(
            event["payload_sha256"],
            hashlib.sha256(canonical(event["payload"]).encode()).hexdigest(),
        )
        self.assertEqual(
            event["payload"]["capability"]["capability_id"],
            "sair:residual12-portfolio:v1",
        )
        self.assertEqual(evidence["checks"]["solo_platform_harness"], "66/66 passed")
        self.assertIn("25", evidence["checks"]["marathon_platform_harness"])

    def test_nonqualified_evidence_is_rejected(self):
        import tempfile
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "e.json"
            payload = json.loads(DEFAULT_EVIDENCE.read_text())
            payload["status"] = "NOT_QUALIFIED"
            path.write_text(json.dumps(payload))
            with self.assertRaisesRegex(ValueError, "PROMOTION_QUALIFIED"):
                build_event(
                    source_commit="0123456789abcdef0123456789abcdef01234567",
                    evidence_path=path,
                )


if __name__ == "__main__":
    unittest.main()
