import JudgeProblem
import JudgeDecide.DecideBang
import JudgeFinOp.MemoFinOp
open MemoFinOp

def submission : Goal := by
  let candidateMagma : Magma (Fin 2) := {
    op := finOpTable "[[0,0],[1,1]]"
  }
  refine ⟨Fin 2, candidateMagma, ?_⟩
  decideFin!
