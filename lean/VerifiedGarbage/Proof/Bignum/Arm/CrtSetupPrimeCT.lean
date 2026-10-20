module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtEnterPrimeCT
import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtEnterPrime
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Factor workspace initialization has no secret-dependent accesses -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

structure CrtSetupPrimeInput (base child : BitVec 32) (len slot w : Nat) (s : State) : Prop
    extends CrtEnterInput base child (8 * len) slot w s where
  childWorkspace : Workspace s child (8 * len)

theorem crt_setupPrime_ct {base child : BitVec 32} {len slot w : Nat}
    (fit : 220 ≤ 8 * len) (slotFit : slot + 4 ≤ 8 * len) (hs : slot < 4096) :
    RelCT isa (fun s t => CrtSetupPrimeInput base child len slot w s ∧ CrtSetupPrimeInput base child len slot w t)
      (setupPrime slot) (fun _ _ => True) := by
  let P := CrtSetupPrimeInput base child len slot w
  have enter := (crt_enterPrime_ct (base := base) (child := child) (size := 8 * len) (w := w)
    (by omega) slotFit hs).mono (P' := fun s t => P s ∧ P t)
    (fun _ _ h => ⟨h.1.toCrtEnterInput, h.2.toCrtEnterInput⟩) (fun _ _ _ => trivial)
  have wp (s : State) (h : P s) : WP isa (enterPrime slot) s (fun t => t.gpr .r0 = child) :=
    WP.mono (crt_enterPrime_ok s h.workspace h.childWorkspace (by omega) slotFit hs fit h.ptr h.count h.link)
      (fun _ j => j.1)
  refine (pair_posts enter wp).seq ?_
  intro s t tr1 tr2 u v h e1 e2
  exact ⟨setup_ct s t tr1 tr2 u v trivial trivial (h.1.trans h.2.symm) e1 e2, trivial⟩

end VG.Proof.Bignum.Arm
