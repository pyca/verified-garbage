module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpStep

public import VerifiedGarbage.Impl.Bignum.Arm.TwoExp

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpCT
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpByteState
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpByteHead
import VerifiedGarbage.Proof.Bignum.Arm.ExpByteHeadCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # The generator-two exponent-buffer loop has a public schedule

The two compared buffers may contain arbitrary different scalars. Only
their common address and length determine the loop's trace.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Impl.Bignum.Arm

theorem byte_ct {base ep : BitVec 32} {len w M1 M2 E1 E2 : Nat} {b1 b2 : Byte}
    {P : State → Prop} {regions : List Region}
    (K : Kernel base len w P regions) (ct : Timing K) :
    RelCT isa (fun s t => (ByteInput base ep len w M1 E1 b1 s ∧ P s) ∧
      (ByteInput base ep len w M2 E2 b2 t ∧ P t) ∧ s.sp = t.sp)
      (.seq expByteHead (.seq (VG.Impl.Bignum.Arm.TwoExp.bits K.square K.twice) (.block expByteNext)))
      (fun _ _ => True) := by
  have head (s : State) {M E : Nat} {b : Byte} (h : ByteInput base ep len w M E b s ∧ P s) :
      WP isa expByteHead s fun t => BitState base len w M E b.toNat 0 t ∧ P t := by
    refine WP.mono (byteHead_ok s h.1.power h.1.pointer h.1.read) ?_
    rintro t ⟨state, _, frame, rest⟩
    rw [h.1.byte] at state
    exact ⟨state, K.stable frame (rest.mono (by decide)) h.2⟩
  have bits (s : State) {M E : Nat} {b : Byte} (h : BitState base len w M E b.toNat 0 s ∧ P s) :
      WP isa (VG.Impl.Bignum.Arm.TwoExp.bits K.square K.twice) s (ArithmeticReady base len w) :=
    WP.mono (bits_ok K s h.1 h.2 b.isLt) fun _ k => k.1.ready
  refine relCT_chain
    (expByteHead_ct.mono
      (fun _ _ h => ⟨⟨h.1.1.power.ready, h.1.1.pointer⟩, ⟨h.2.1.1.power.ready, h.2.1.1.pointer⟩⟩)
      (fun _ _ h => h)) (fun s h => head s h) (fun s h => head s h) ?_
  exact relCT_chain (bits_ct K ct b1.isLt b2.isLt) (fun s h => bits s h) (fun s h => bits s h)
    (expByteNext_ct.mono (fun _ _ h => h.1.ptr.trans h.2.1.ptr.symm) (fun _ _ h => h))

theorem byteBody_ct {base ep : BitVec 32} {len w M1 M2 j : Nat} {eb1 eb2 : List Byte}
    {P : State → Prop} {regions : List Region}
    (K : Kernel base len w P regions) (ct : Timing K) (hj1 : j < eb1.length) (hj2 : j < eb2.length) :
    RelCT isa (fun s t => ByteState base ep len w M1 P regions eb1 j s ∧
      ByteState base ep len w M2 P regions eb2 j t ∧ s.sp = t.sp)
      (.seq expByteHead (.seq (VG.Impl.Bignum.Arm.TwoExp.bits K.square K.twice) (.block expByteNext)))
      (fun _ _ => True) :=
  (byte_ct K ct).mono
    (fun _ _ h => ⟨⟨h.1.input hj1, h.1.persistent⟩, ⟨h.2.1.input hj2, h.2.1.persistent⟩, h.2.2⟩)
    (fun _ _ h => h)

theorem bytes_ct {base ep : BitVec 32} {len w M1 M2 : Nat} {eb1 eb2 : List Byte}
    {P : State → Prop} {regions : List Region}
    (K : Kernel base len w P regions) (ct : Timing K) (positive : 0 < eb1.length)
    (length : eb1.length = eb2.length) :
    RelCT isa (fun s t => ByteState base ep len w M1 P regions eb1 0 s ∧
      ByteState base ep len w M2 P regions eb2 0 t ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.TwoExp.bytes K.square K.twice) (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ j, j + k = eb1.length ∧ 0 < k ∧
    ByteState base ep len w M1 P regions eb1 j s ∧ ByteState base ep len w M2 P regions eb2 j t ∧ s.sp = t.sp
  have step : ∀ k, RelCT isa (I k)
      (.seq expByteHead (.seq (VG.Impl.Bignum.Arm.TwoExp.bits K.square K.twice) (.block expByteNext))) fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m, m < k ∧ I m s t) := by
    intro k s t tr1 tr2 u z h e1 e2
    obtain ⟨j, jk, hk, hs, ht, sp⟩ := h
    have c := relCT_keep_sp (byteBody_ct (ep := ep) (M1 := M1) (M2 := M2) K ct (by omega : j < eb1.length) (by omega : j < eb2.length))
      (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := c s t tr1 tr2 u z ⟨hs, ht, sp⟩ e1 e2
    obtain ⟨_, _, run1, next1, zero1, _, _⟩ := byteState_step K s hs (by omega)
    obtain ⟨_, _, run2, next2, zero2, _, _⟩ := byteState_step K t ht (by omega)
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
      exact ⟨k - 1, by omega, j + 1, by omega, by omega, next1, next2, sp'⟩
  unfold VG.Impl.Bignum.Arm.TwoExp.bytes
  exact (RelCT.loop I step eb1.length).mono
    (fun _ _ h => ⟨0, by omega, positive, h.1, h.2.1, h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Bignum.Arm.TwoExp
