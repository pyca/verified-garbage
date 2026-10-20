module

public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Bignum.Arm.WindowPhase
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowBit

import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowBitCT
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowBytes
import VerifiedGarbage.Proof.Bignum.Arm.ExpByteHeadCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay

/-! # Shared-window byte iteration preserves a fixed public exponent schedule -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.SharedWindow
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.Bignum.Arm.TwoExp (Montgomery MontgomeryTiming)
section
variable {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
variable (K : Montgomery base len w P regions) (ct : MontgomeryTiming K)
include ct

theorem byteBody_ct {ep : BitVec 32} {M1 M2 x1 x2 j : Nat} {eb1 eb2 : List Byte}
    (fits : arrAt w 16 ≤ 8 * len) (hj1 : j < eb1.length)
    (hj2 : j < eb2.length) :
    RelCT isa (fun s t => (WinByteLoop base ep len w M1 x1 eb1 j s ∧ P s) ∧ (WinByteLoop base ep len w M2 x2 eb2 j t ∧ P t) ∧
      s.sp = t.sp) (.seq expByteHead (.seq (VG.Impl.Bignum.Arm.SharedWindow.bits K.op) (.block expByteNext))) (fun _ _ => True) := by
  -- after the head: the bits of the byte
  have head (s : State) {M x : Nat} {eb : List Byte} (h : WinByteLoop base ep len w M x eb j s ∧ P s)
      (hj : j < eb.length) :
      WP isa expByteHead s fun t => WinBitState base len w M x (pre eb j) (eb[j]).toNat (8 * j) 0 t ∧ P t := by
    obtain ⟨⟨A, p, state, sum⟩, ptr, _, _, sourceFit, read, _, bytes⟩ := h.1
    have address : State.addr (ep + BitVec.ofNat 32 j) = State.addr ep + BitVec.ofNat 64 j :=
      addr_add (by omega)
    have current : InRegions (s.rd ++ s.wr) (State.addr (ep + BitVec.ofNat 32 j)) 1 := by
      rw [address]; exact CallLay.inRegions_sub read (by omega) (by omega)
    refine WP.mono (windowByteHead_ok s state ptr current) ?_
    rintro u ⟨stateU, byteU, countU, _, frameU, restU⟩
    rw [address, bytes j hj] at byteU
    have v256 := (eb[j]).isLt
    exact ⟨⟨⟨A, p, stateU, by rw [sum, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, show 2 ^ 8 = 256 from rfl,
      Nat.div_eq_of_lt v256, Nat.add_zero]⟩, by rw [Nat.pow_zero, Nat.mul_one]; exact byteU, countU⟩, K.stable frameU restU h.2⟩
  have bits (u : State) {M x E v n : Nat} (h : WinBitState base len w M x E v n 0 u ∧ P u) (hv : v < 256) :
      WP isa (VG.Impl.Bignum.Arm.SharedWindow.bits K.op) u fun y => y.gpr .r0 = base :=
    WP.mono (sharedWindowBits_ok K u h.1 h.2 hv) fun _ ⟨⟨_, _, k, _⟩, _⟩ => k.power.ready.ptr
  refine relCT_chain (Q₁ := fun s => WinBitState base len w M1 x1 (pre eb1 j) (eb1[j]).toNat (8 * j) 0 s ∧ P s)
    (Q₂ := fun s => WinBitState base len w M2 x2 (pre eb2 j) (eb2[j]).toNat (8 * j) 0 s ∧ P s)
    ((expByteHead_ct (base := base) (ep := ep + BitVec.ofNat 32 j) (len := len) (w := w)).mono
      (fun _ _ h => ⟨⟨(Classical.choose_spec (Classical.choose_spec h.1.1.state)).1.power.ready, h.1.1.pointer⟩,
        ⟨(Classical.choose_spec (Classical.choose_spec h.2.1.1.state)).1.power.ready, h.2.1.1.pointer⟩⟩)
      (fun _ _ h => h))
    (fun s h => head s h hj1) (fun s h => head s h hj2) ?_
  exact relCT_chain (Q₁ := fun s => s.gpr .r0 = base) (Q₂ := fun s => s.gpr .r0 = base)
    (bits_ct K ct fits (eb1[j]).isLt (eb2[j]).isLt)
    (fun s h => bits s h (eb1[j]).isLt) (fun s h => bits s h (eb2[j]).isLt)
    (expByteNext_ct.mono (fun _ _ h => h.1.trans h.2.1.symm) (fun _ _ h => h))

theorem bytes_ct {ep : BitVec 32} {M1 M2 x1 x2 : Nat} {eb1 eb2 : List Byte}
    (fits : arrAt w 16 ≤ 8 * len) (positive : 0 < eb1.length)
    (length : eb1.length = eb2.length)
    (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb1.length⟩ r) :
    RelCT isa (fun s t => (WinByteLoop base ep len w M1 x1 eb1 0 s ∧ P s) ∧ (WinByteLoop base ep len w M2 x2 eb2 0 t ∧ P t) ∧
      s.sp = t.sp) (VG.Impl.Bignum.Arm.SharedWindow.bytes K.op) (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ j, j + k = eb1.length ∧ 0 < k ∧
    (WinByteLoop base ep len w M1 x1 eb1 j s ∧ P s) ∧ (WinByteLoop base ep len w M2 x2 eb2 j t ∧ P t) ∧ s.sp = t.sp
  have step : ∀ k, RelCT isa (I k) (.seq expByteHead (.seq (VG.Impl.Bignum.Arm.SharedWindow.bits K.op) (.block expByteNext))) fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m, m < k ∧ I m s t) := by
    intro k s t tr1 tr2 u z h e1 e2
    obtain ⟨j, jk, hk, hs, ht, sp⟩ := h
    have ct := relCT_keep_sp (byteBody_ct K ct (base := base) (ep := ep) (M1 := M1) (M2 := M2) (x1 := x1)
      (x2 := x2) (j := j) (eb1 := eb1) (eb2 := eb2) fits (by omega) (by omega)) (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := ct s t tr1 tr2 u z ⟨hs, ht, sp⟩ e1 e2
    obtain ⟨_, _, run1, next1, zero1, pn1, _, _⟩ := sharedWindowByteStep_ok K s hs.1 hs.2 (by omega) separate
    obtain ⟨_, _, run2, next2, zero2, pn2, _, _⟩ := sharedWindowByteStep_ok K t ht.1 ht.2 (by omega) (by rw [← length]; exact separate)
    obtain ⟨-, rfl⟩ := Exec.det e1 run1
    obtain ⟨-, rfl⟩ := Exec.det e2 run2
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!_) = some (!_)
      rw [zero1, zero2, length]
    · intro again
      have notLast : j + 1 ≠ eb1.length := by
        intro last
        change some (!_) = some true at again
        simp only [zero1, last, decide_true, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at again
      exact ⟨k - 1, by omega, j + 1, by omega, by omega, ⟨next1, pn1⟩, ⟨next2, pn2⟩, sp'⟩
  unfold VG.Impl.Bignum.Arm.SharedWindow.bytes
  exact (RelCT.loop I step eb1.length).mono
    (fun _ _ h => ⟨0, by omega, positive, h.1, h.2.1, h.2.2⟩) (fun _ _ h => h)

end
end VG.Proof.Bignum.Arm.SharedWindow
