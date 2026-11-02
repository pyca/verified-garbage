module
public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpState
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpStepCT
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpStep
import VerifiedGarbage.Proof.Bignum.Arm.ExpBitTest
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.Exp
meta import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpState
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpStepCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpStep
meta import VerifiedGarbage.Proof.Bignum.Arm.ExpBitTest
meta import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Only the public exponent bit controls a branch -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

variable {ok : Prop}
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

structure ExpBitInput (ok : Prop) (base : BitVec 32) (len w M x E V : Nat) (s : State) : Prop where
  power : ExpState ok base len w M x E s
  byte : s.mem.readW (VG.Proof.Mont.off (State.addr base) 200) 32 = BitVec.ofNat 32 V

theorem ExpBitInput.square (s : State) {base : BitVec 32} {len w M x E V : Nat}
    (h : ExpBitInput ok base len w M x E V s) : WP isa (squareOp 6 6) s (ExpBitInput ok base len w M x (2 * E) V) := by
  refine WP.mono (exp_square_ok s h.power) ?_
  rintro t ⟨power, keeps, _, _⟩
  have size : 256 ≤ 8 * len := by
    have := h.power.ready.layout.2.2.1
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
    omega
  exact ⟨power, (keeps_header_readW keeps size (d := 200) (bits := 32) (by decide)).trans h.byte⟩

theorem ExpBitInput.test (s : State) {base : BitVec 32} {len w M x E V : Nat}
    (h : ExpBitInput ok base len w M x E V s) (hv : V < 2 ^ 32) :
    WP isa (.block expBitTest) s fun t => ExpState ok base len w M x E t ∧ t.z = decide (V / 128 % 2 = 0) := by
  have size : 204 ≤ 8 * len := by
    have := h.power.ready.layout.2.2.1
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
    omega
  refine WP.mono (expBitTest_ok s h.power.ready.workspace size h.power.ready.ptr hv h.byte) ?_
  rintro t ⟨zero, mem, rest⟩
  exact ⟨h.power.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.power.ready.ptr), zero⟩

theorem expBit_ct {base : BitVec 32} {len w M1 M2 x1 x2 E V : Nat}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (hv : V < 2 ^ 32) :
    RelCT isa (fun s t => ExpBitInput ok base len w M1 x1 E V s ∧
      ExpBitInput ok base len w M2 x2 E V t ∧ s.sp = t.sp) expBit (fun _ _ => True) := by
  let P := fun (s t : State) => ExpBitInput ok base len w M1 x1 E V s ∧
    ExpBitInput ok base len w M2 x2 E V t ∧ s.sp = t.sp
  have square := (relCT_keep_sp ((exp_square_ct (len := len) (w := w)).mono (P' := P)
    (fun _ _ h => ⟨h.1.power, h.2.1.power, h.2.2⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨h.1.square s, h.2.1.square t⟩)
  let Q := fun (s t : State) => s.sp = t.sp ∧ ExpBitInput ok base len w M1 x1 (2 * E) V s ∧
    ExpBitInput ok base len w M2 x2 (2 * E) V t
  have test : RelCT isa Q (.block expBitTest) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1.power.ready.ptr.trans h.2.2.power.ready.ptr.symm
  have tested := (relCT_keep_sp test (fun _ _ h => h.1)).wp
    (fun s t h => ⟨h.2.1.test s hv, h.2.2.test t hv⟩)
  refine square.seq (tested.seq (RelCT.ite ?_ ?_ ?_))
  · intro s t h
    change some (!s.z) = some (!t.z)
    rw [h.2.1.2, h.2.2.2]
  · apply (exp_multiply_ct (base := base) (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2) (E := 2 * E) fit).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1, h.1.1⟩) (fun _ _ h => h)
  · exact RelCT.block_nil (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm.ConditionalExp
