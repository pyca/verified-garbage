module

import VerifiedGarbage.Proof.Bignum.Arm.SetBaseStep
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Impl.Bignum.Arm.SetBases
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Construct the eight shared RSA array pointers -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

structure BasesInv (s0 : State) (base : BitVec 32) (w i : Nat) (s : State) : Prop where
  index : i ≤ 8
  ptr : s.gpr .r0 = base + BitVec.ofNat 32 (64 + 8 * i)
  cursor : s.gpr .r4 = base + BitVec.ofNat 32 (arrAt w i)
  count : s.gpr .lr = BitVec.ofNat 32 (8 - i)
  header : ∀ j < i, word s.mem (State.addr base) (64 + 8 * j) =
    off (State.addr base) (arrAt w j)
  outside : Outside (State.addr base) 64 (8 * i) s0.mem s.mem
  rest : Rest [.r0, .r4, .lr] s0 s

theorem setBasesBody_ok {s0 s : State} {base : BitVec 32} {size w i : Nat}
    (ws : Workspace s0 base size) (fits : arrAt w 8 ≤ size)
    (inv : BasesInv s0 base w i s) (hi : i < 8)
    (stride : s0.gpr .r5 = BitVec.ofNat 32 (8 * (w + 2))) (zero : s0.gpr .r3 = 0) :
    WP isa (.block setBaseStep) s fun t => BasesInv s0 base w (i + 1) t ∧
      t.z = decide (i + 1 = 8) := by
  have nowrap := ws.nowrap
  have headerFits : 128 ≤ size := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have arrayFits : arrAt w i < size := by
    have hm := Nat.mul_le_mul_right (8 * (w + 2)) (by omega : i + 1 ≤ 8)
    rw [Nat.add_mul, Nat.one_mul] at hm
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits ⊢
    omega
  have writable (d : Nat) (hd : d + 4 ≤ size) : InRegions s.wr (off (State.addr base) d) 4 := by
    rw [inv.rest.wr]
    exact ws.write hd
  have alo : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr base) (64 + 8 * i) :=
    (ws.congr inv.rest.wr).ea (off := 64 + 8 * i) (imm := 0) inv.ptr (by omega)
  have ahi : State.addr (s.gpr .r0 + BitVec.ofNat 32 4) = off (State.addr base) (64 + 8 * i) + BitVec.ofNat 64 4 := by
    rw [inv.ptr, Offset.add_add, addr_add (by omega)]
    exact (Offset.add_add _ _ _).symm
  have whi : InRegions s.wr (off (State.addr base) (64 + 8 * i) + BitVec.ofNat 64 4) 4 := by
    rw [Offset.add_add]
    exact writable _ (by omega)
  refine WP.mono (setBaseStep_ok s _ alo ahi (writable _ (by omega)) whi
    ((inv.rest.gpr .r3 (by simp)).trans zero)) ?_
  rintro t ⟨mem, ptr, cursor, count, z, rest⟩
  have outside := writeW_outside s.mem (State.addr base) (d := 64 + 8 * i)
    (State.addr (s.gpr .r4)) (by omega)
  rw [← mem] at outside
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, inv.rest.trans rest⟩, ?_⟩
  · rw [ptr, inv.ptr]
    change base + BitVec.ofNat 32 (64 + 8 * i) + BitVec.ofNat 32 8 = _
    rw [Offset.add_add]
    congr 1
  · rw [cursor, inv.cursor, inv.rest.gpr .r5 (by simp), stride, Offset.add_add]
    rw [show arrAt w i + 8 * (w + 2) = arrAt w (i + 1) by
      simp only [arrAt, Proof.Rsa.Mont.hdrBytes, Nat.add_mul, Nat.one_mul, Nat.add_assoc]]
  · rw [count, inv.count]
    change BitVec.ofNat 32 (8 - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · intro j hj
    by_cases he : j = i
    · subst j
      rw [mem, word_writeW_self, inv.cursor, addr_add (by omega)]
    · rw [outside.word (d := 64 + 8 * j) (by omega) (by omega)]
      exact inv.header j (by omega)
  · exact (inv.outside.mono (Nat.le_refl _) (by omega)).trans (outside.mono (by omega) (by omega))
  · rw [z, inv.count]
    change (BitVec.ofNat 32 (8 - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show 8 - i - 1 = 0 ↔ i + 1 = 8 by omega]

/-- Fill all eight 64-bit pointer slots, leaving the remaining memory unchanged. -/
theorem setBases_ok (s : State) {base : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fits : arrAt w 8 ≤ size)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 64)
    (cursor : s.gpr .r4 = base + BitVec.ofNat 32 256)
    (count : s.gpr .lr = BitVec.ofNat 32 8)
    (stride : s.gpr .r5 = BitVec.ofNat 32 (8 * (w + 2))) (zero : s.gpr .r3 = 0) :
    WP isa setBases s (BasesInv s base w 8) := by
  let inv := fun k t => ∃ i, i + k = 8 ∧ 0 < k ∧ BasesInv s base w i t
  unfold setBases
  refine WP.loop (M := isa) inv ?_ 8 s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (setBasesBody_ok ws fits hi (by omega) stride zero) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = 8
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by decide, by decide, ?_⟩
    exact ⟨by decide, by simpa using ptr, by simpa [arrAt, Proof.Rsa.Mont.hdrBytes] using cursor,
      by simpa using count, by intro j hj; omega, Outside.refl _ _ _ _, Rest.refl _ _⟩

end VG.Proof.Bignum.Arm
