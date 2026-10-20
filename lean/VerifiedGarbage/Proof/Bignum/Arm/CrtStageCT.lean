module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! # Compose leakage proofs while retaining independent secret states -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

def CrtSelected (g : CrtGeometry) (bs : Fin 7 → List Byte) (child : BitVec 32) (s : State) : Prop :=
  CrtShared g bs s ∧ LayoutFrameReady child (workspaceWords g.words) g.words s

theorem crt_seq_ct {P1 P2 Q1 Q2 : State → Prop} {a b : Prog isa}
    (first : RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) a (fun _ _ => True))
    (wp1 : ∀ s, P1 s → WP isa a s Q1) (wp2 : ∀ s, P2 s → WP isa a s Q2)
    (second : RelCT isa (fun s t => Q1 s ∧ Q2 t ∧ s.sp = t.sp) b (fun _ _ => True)) :
    RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) (.seq a b) (fun _ _ => True) := by
  have start := (relCT_keep_sp first (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp1 s h.1, wp2 t h.2.1⟩)
  exact start.seq (second.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
