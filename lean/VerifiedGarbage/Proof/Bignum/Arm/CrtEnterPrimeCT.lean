module
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeArgs
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.Arm.Workspace
meta import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.StageCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Moving between CRT workspaces depends only on their public pointers -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont

structure CrtEnterInput (base child : BitVec 32) (size slot w : Nat) (s : State) : Prop where
  workspace : Workspace s base size
  ptr : s.gpr .r0 = base
  count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w
  link : s.mem.readW (off (State.addr base) slot) 32 = child

theorem crt_enterPrime_ct {base child : BitVec 32} {size slot w : Nat}
    (fit : 52 ≤ size) (slotFit : slot + 4 ≤ size) (hs : slot < 4096) :
    RelCT isa (fun s t => CrtEnterInput base child size slot w s ∧ CrtEnterInput base child size slot w t)
      (enterPrime slot) (fun _ _ => True) := by
  let P := CrtEnterInput base child size slot w
  have head : RelCT isa (fun s t => P s ∧ P t) (.block (primeArgs slot)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : P s) : WP isa (.block (primeArgs slot)) s (fun t => t.gpr .r2 = child) :=
    WP.mono (crt_primeArgs_ok s h.workspace fit slotFit hs h.ptr h.count h.link) (fun _ j => j.2.1)
  refine (pair_posts head wp).seq ?_
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r2]) _ (by taint_decide)
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h.1.trans h.2.symm

end VG.Proof.Bignum.Arm
