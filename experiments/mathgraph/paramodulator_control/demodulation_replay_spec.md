# Forward-demodulation replay

Every demodulation is serialized as a normal `para` node containing:

- demodulator clause ID;
- demodulator orientation;
- parent clause ID;
- selected literal side;
- exact subterm path.

The existing translator independently freshens the demodulator, reconstructs
the unifier, applies the substitution, checks the path, and recomputes both
resulting literal sides.

The resulting compact equality plan is then checked twice:

1. by the external congruence-plan verifier bundled into the frozen specialist;
2. by `audit_stair_climber_components.replay_plan`, a separately authored
   MathGraph parser and contextual rewrite replayer.

Only after both replay paths accept is Lean code generated and passed to the
official judge. A search hit that fails either replay is an abstention.

Required corruption tests alter, independently:

- demodulator ID;
- orientation;
- parent clause;
- literal side;
- path;
- final target.

Every corruption must be rejected before any result can be considered for
promotion.
