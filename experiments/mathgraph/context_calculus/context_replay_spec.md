# Context Replay Specification Status

Status: **deferred after Phase 1 falsification**.

The sole valid prefix was replayed directly using the existing trusted
primitives:

1. a concrete source instance;
2. a reversed concrete source instance;
3. a congruence lift through the exact outer context;
4. transitivity.

This was sufficient to validate the one explicit derived lemma without adding
a context replay rule. Five other rejected prefixes lacked an exact embedded
source instance, so a context replayer could not make them valid.

Any future context-replay experiment must begin from independently valid
context derivations rather than the rejected candidate templates.
