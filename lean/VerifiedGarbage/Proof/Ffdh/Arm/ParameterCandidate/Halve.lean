module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.HalfByte
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.HalveOctets
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Bignum.Arm.MaskBytes
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! In-place division of the candidate encoding by two. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)
open VG.Proof.Bignum.Arm (MaskCtx)
open VG.Proof.Ffdh.ParameterCandidate (carryAt carryAt_le carryAt_next halfOctets halfOctets_get)

structure HalfInv (s0 : State) (dst : BitVec 32) (bs : List Byte) (i : Nat) (s : State) : Prop where
  index : i ≤ bs.length
  dest : s.gpr .r0 = dst + BitVec.ofNat 32 i
  count : s.gpr .lr = BitVec.ofNat 32 (bs.length - i)
  carry : s.gpr .r2 = BitVec.ofNat 32 (128 * carryAt 0 bs i)
  last : ∀ j, i = j + 1 → s.gpr .r1 =
    BitVec.ofNat 32 ((bs[j]?.getD 0).toNat / 2 + 128 * carryAt 0 bs j)
  shifted : ∀ j < i, s.mem (State.addr (dst + BitVec.ofNat 32 j)) =
    VG.Proof.Ffdh.ParameterCandidate.halfByte (carryAt 0 bs j) (bs[j]?.getD 0)
  outside : ∀ a, (∀ j < i, a ≠ State.addr (dst + BitVec.ofNat 32 j)) → s.mem a = s0.mem a
  rest : Rest [.r0, .r1, .r2, .r3, .lr] s0 s

theorem halveBody_ok {s0 s : State} {dst : BitVec 32} {bs : List Byte} {i : Nat}
    (ctx : MaskCtx s0 dst bs.length)
    (bytes : ∀ j < bs.length, s0.mem (State.addr (dst + BitVec.ofNat 32 j)) = bs[j]?.getD 0)
    (inv : HalfInv s0 dst bs i s) (more : i < bs.length) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.halfByte) s fun t =>
      HalfInv s0 dst bs (i + 1) t ∧ t.z = decide (i + 1 = bs.length) := by
  have read := ctx.readable i more
  have write := ctx.writable i more
  rw [← inv.rest.rd, ← inv.rest.wr, ← inv.dest] at read
  rw [← inv.rest.wr, ← inv.dest] at write
  refine WP.mono (halfByte_ok s read write) ?_
  rintro t ⟨⟨ptr, word, carry, count, zero, mem⟩, rest⟩
  have original : s.mem (State.addr (s.gpr .r0)) = bs[i]?.getD 0 := by
    rw [inv.dest, inv.outside _ (fun j hj same => by
      have := ctx.distinct i more j (by omega) same
      omega), bytes i more]
  have newByte : (((s.mem (State.addr (s.gpr .r0))).setWidth 32 >>> 1 |||
      s.gpr .r2).setWidth 8) =
        VG.Proof.Ffdh.ParameterCandidate.halfByte (carryAt 0 bs i) (bs[i]?.getD 0) := by
    rw [original, inv.carry]
    exact halfByte_encoding _ (carryAt_le (by decide) bs i)
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, inv.rest.trans rest⟩, ?_⟩
  · rw [ptr, inv.dest, BitVec.add_assoc]
    change dst + (BitVec.ofNat 32 i + BitVec.ofNat 32 1) = _
    rw [← BitVec.ofNat_add]
  · rw [count, inv.count]
    change BitVec.ofNat 32 (bs.length - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · rw [carry, original, halfByte_carry, carryAt_next 0 more]
    simp only [List.getElem?_eq_getElem more, Option.getD_some]
  · intro j hj
    have same : j = i := by omega
    subst j
    rw [word, original, inv.carry, halfByte_value _ (carryAt_le (by decide) bs i)]
  · intro j hj
    rw [mem, VG.WriteBytes.writeW8_apply, inv.dest]
    by_cases same : j = i
    · subst j
      rw [ite_eq_left rfl]
      rw [← inv.dest]
      exact newByte
    · have different : State.addr (dst + BitVec.ofNat 32 j) ≠ State.addr (dst + BitVec.ofNat 32 i) :=
        fun h => same (ctx.distinct j (by omega) i more h)
      rw [ite_eq_right different]
      exact inv.shifted j (by omega)
  · intro a ha
    rw [mem, VG.WriteBytes.writeW8_apply, inv.dest, ite_eq_right (ha i (by omega))]
    exact inv.outside a fun j hj => ha j (by omega)
  · rw [zero, inv.count]
    change (BitVec.ofNat 32 (bs.length - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega),
      ofNat_beq_zero (by have := ctx.countFits; omega)]
    simp only [show bs.length - i - 1 = 0 ↔ i + 1 = bs.length by omega]

theorem halveLoop_ok (s : State) {dst : BitVec 32} {bs : List Byte}
    (ctx : MaskCtx s dst bs.length) (positive : 0 < bs.length)
    (bytes : ∀ j < bs.length, s.mem (State.addr (dst + BitVec.ofNat 32 j)) = bs[j]?.getD 0)
    (dest : s.gpr .r0 = dst) (count : s.gpr .lr = BitVec.ofNat 32 bs.length)
    (carry : s.gpr .r2 = 0) :
    WP isa (.loop (.block VG.Impl.Ffdh.Arm.ParameterCandidate.halfByte) .ne) s
      (HalfInv s dst bs bs.length) := by
  let inv := fun k t => ∃ i, i + k = bs.length ∧ 0 < k ∧ HalfInv s dst bs i t
  refine WP.loop (M := isa) inv ?_ bs.length s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (halveBody_ok ctx bytes hi (by omega)) ?_
    rintro u ⟨hu, hz⟩
    by_cases last : i + 1 = bs.length
    · left
      refine ⟨?_, last ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, last, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu⟩
      change some (!u.z) = some true
      simp only [hz, last, decide_false, Bool.not_false]
  · refine ⟨0, by omega, positive, ?_⟩
    exact ⟨by omega, by simpa using dest, by simpa using count,
      by simpa [carryAt] using carry, by intro j hj; omega, by intro j hj; omega,
      by intros; rfl, Rest.refl _ _⟩

theorem HalfInv.encoding {s0 s : State} {dst : BitVec 32} {bs : List Byte}
    (inv : HalfInv s0 dst bs bs.length s) (fits : dst.toNat + bs.length ≤ 2 ^ 32) :
    Spec.Rsa.bytesAt s.mem (State.addr dst) bs.length = halfOctets 0 bs := by
  apply List.ext_getElem
  · rw [VG.Proof.Bignum.bytesAt_length, VG.Proof.Ffdh.ParameterCandidate.halfOctets_length]
  · intro j hj hj'
    have bound : j < bs.length := by rwa [VG.Proof.Bignum.bytesAt_length] at hj
    have byte := inv.shifted j bound
    rw [VG.Arm.addr_add (by omega : dst.toNat + j < 2 ^ 32)] at byte
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    rw [halfOctets_get 0 bound]
    simpa only [List.getElem?_eq_getElem bound, Option.getD_some] using byte

theorem HalfInv.value {s0 s : State} {dst : BitVec 32} {bs : List Byte}
    (inv : HalfInv s0 dst bs bs.length s) (fits : dst.toNat + bs.length ≤ 2 ^ 32) :
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) bs.length) = Spec.Rsa.os2ip bs / 2 := by
  rw [inv.encoding fits, VG.Proof.Ffdh.ParameterCandidate.halfOctets_zero]

end VG.Proof.Ffdh.Arm.ParameterCandidate
