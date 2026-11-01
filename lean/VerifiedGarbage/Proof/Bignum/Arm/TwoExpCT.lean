module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpStep

public import VerifiedGarbage.Impl.Bignum.Arm.TwoExp

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpBits
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.SelectArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Arm.TwoExpStep
meta import VerifiedGarbage.Impl.Bignum.Arm.TwoExp
meta import VerifiedGarbage.Proof.Bignum.Arm.TwoExpBits
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SelectArrayCT
meta import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Generator-two exponentiation hides the scalar and modulus

The supplied arithmetic routines hide their operands. Selection scans all
words, and bit-loop branches depend only on the public position in a byte.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

abbrev Ready (base : BitVec 32) (len w : Nat) (P : State → Prop) (s : State) : Prop :=
  ∃ M E, Power base len w M E s ∧ P s

structure Timing {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : Kernel base len w P regions) : Prop where
  square : RelCT isa (fun s t => Ready base len w P s ∧ Ready base len w P t ∧ s.sp = t.sp)
    K.square (fun _ _ => True)
  twice : RelCT isa (fun s t => Ready base len w P s ∧ Ready base len w P t ∧ s.sp = t.sp)
    K.twice (fun _ _ => True)

theorem digit_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0)
    (.block VG.Impl.Bignum.Arm.TwoExp.digit) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

theorem bit_ct {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : Kernel base len w P regions) (ct : Timing K) :
    RelCT isa (fun s t => Ready base len w P s ∧ Ready base len w P t ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.TwoExp.bit K.square K.twice) (fun _ _ => True) := by
  have square (s : State) (h : Ready base len w P s) : WP isa K.square s (Ready base len w P) := by
    obtain ⟨M, E, state, p⟩ := h
    exact WP.mono (K.square_ok s E state p) fun _ k => ⟨M, 2 * E, k.1, k.2.1⟩
  have twice (s : State) (h : Ready base len w P s) : WP isa K.twice s (Ready base len w P) := by
    obtain ⟨M, E, state, p⟩ := h
    exact WP.mono (K.twice_ok s E state p) fun _ k => ⟨M, E, k.1, k.2.2.2.1⟩
  have digit (s : State) (h : Ready base len w P s) :
      WP isa (.block VG.Impl.Bignum.Arm.TwoExp.digit) s (SelectArrayReady base len w) := by
    obtain ⟨M, E, state, _⟩ := h
    refine WP.mono (digit_ok s state.ready (V := (s.mem.readW (off (State.addr base) 200) 32).toNat)
      (s.mem.readW (off (State.addr base) 200) 32).isLt (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])) ?_
    rintro t ⟨_, mem, rest⟩
    have next := state.ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans state.ready.ptr)
    exact ⟨next.workspace, next.layout, next.width, next.ptr⟩
  unfold VG.Impl.Bignum.Arm.TwoExp.bit
  refine relCT_chain ct.square square square ?_
  refine relCT_chain ct.twice twice twice ?_
  refine relCT_chain
    (digit_ct.mono
      (fun _ _ h => (Classical.choose_spec (Classical.choose_spec h.1)).1.ready.ptr.trans
        (Classical.choose_spec (Classical.choose_spec h.2.1)).1.ready.ptr.symm) (fun _ _ h => h))
    digit digit ?_
  exact selectArray_ct (by decide : 6 < 8) (by decide : 6 < 8) (by decide : 1 < 8)

theorem round_ct {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : Kernel base len w P regions) (ct : Timing K) :
    RelCT isa (fun s t => Ready base len w P s ∧ Ready base len w P t ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.TwoExp.round K.square K.twice) (fun _ _ => True) := by
  have ready (s : State) (h : Ready base len w P s) :
      WP isa (VG.Impl.Bignum.Arm.TwoExp.bit K.square K.twice) s (ArithmeticReady base len w) := by
    obtain ⟨M, E, state, p⟩ := h
    exact WP.mono (bit_ok K s state p (V := (s.mem.readW (off (State.addr base) 200) 32).toNat)
      (s.mem.readW (off (State.addr base) 200) 32).isLt (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]))
      fun _ k => k.1.ready
  have shifted (s : State) (h : ArithmeticReady base len w s) :
      WP isa (.block expShift) s fun t => t.gpr .r0 = base := by
    have size : 204 ≤ 8 * len := by
      have fits := h.layout.2.2.1
      simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] at fits
      omega
    exact WP.mono (expShift_ok s h.workspace size h.ptr (V := (s.mem.readW
      (off (State.addr base) 200) 32).toNat) (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]))
      fun _ k => (k.2.gpr .r0 (by simp)).trans h.ptr
  unfold VG.Impl.Bignum.Arm.TwoExp.round
  refine relCT_chain (bit_ct K ct) ready ready ?_
  exact relCT_chain (Q₁ := fun s => s.gpr .r0 = base) (Q₂ := fun s => s.gpr .r0 = base)
    (expShift_ct.mono (fun _ _ h => h.1.ptr.trans h.2.1.ptr.symm) (fun _ _ h => h))
    shifted shifted (expDecrement_ct.mono (fun _ _ h => h.1.trans h.2.1.symm) (fun _ _ h => h))

theorem bits_ct {base : BitVec 32} {len w M1 M2 E1 E2 v1 v2 : Nat}
    {P : State → Prop} {regions : List Region}
    (K : Kernel base len w P regions) (ct : Timing K) (hv1 : v1 < 256) (hv2 : v2 < 256) :
    RelCT isa (fun s t => (BitState base len w M1 E1 v1 0 s ∧ P s) ∧
      (BitState base len w M2 E2 v2 0 t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.TwoExp.bits K.square K.twice) (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ j, j + k = 8 ∧ 0 < k ∧
    BitState base len w M1 E1 v1 j s ∧ P s ∧ BitState base len w M2 E2 v2 j t ∧ P t ∧ s.sp = t.sp
  have step : ∀ k, RelCT isa (I k) (VG.Impl.Bignum.Arm.TwoExp.round K.square K.twice) fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m, m < k ∧ I m s t) := by
    intro k s t tr1 tr2 u z h e1 e2
    obtain ⟨j, jk, hk, hs, ps, ht, pt, sp⟩ := h
    have hj : j < 8 := by omega
    have c := relCT_keep_sp (round_ct K ct) (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := c s t tr1 tr2 u z
      ⟨⟨M1, E1 * 2 ^ j + v1 / 2 ^ (8 - j), hs.power, ps⟩,
       ⟨M2, E2 * 2 ^ j + v2 / 2 ^ (8 - j), ht.power, pt⟩, sp⟩ e1 e2
    obtain ⟨_, _, run1, next1, p1, zero1, _, _, _⟩ := bitState_step K s hs ps hv1 hj
    obtain ⟨_, _, run2, next2, p2, zero2, _, _, _⟩ := bitState_step K t ht pt hv2 hj
    obtain ⟨-, rfl⟩ := Exec.det e1 run1
    obtain ⟨-, rfl⟩ := Exec.det e2 run2
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!_) = some (!_)
      rw [zero1, zero2]
    · intro again
      have notLast : j + 1 ≠ 8 := by
        intro last
        change some (!_) = some true at again
        simp only [zero1, last, decide_true, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at again
      exact ⟨k - 1, by omega, j + 1, by omega, by omega, next1, p1, next2, p2, sp'⟩
  unfold VG.Impl.Bignum.Arm.TwoExp.bits
  exact (RelCT.loop I step 8).mono
    (fun _ _ h => ⟨0, by decide, by decide, h.1.1, h.1.2, h.2.1.1, h.2.1.2, h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Bignum.Arm.TwoExp
