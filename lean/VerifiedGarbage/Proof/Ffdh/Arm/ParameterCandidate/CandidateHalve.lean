module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Table
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateResidue
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ReadContext
public import VerifiedGarbage.Proof.Bignum.Arm.MaskBytes
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.HalveOctets
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTStackBlocks
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `Ffdh.Arm.ParameterCandidate.CTHalve`, which the modules that import this one used -/

section

/-! In-place q construction traverses precisely the public candidate width. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_taint)

def HalveRead (p : BitVec 32 × Nat) (s : State) : Prop := ReadContext p.1 p.2 s
private def HalvePointers (p : BitVec 32 × Nat) (s : State) : Prop :=
  s.gpr .r0 = p.1 ∧ s.gpr .lr = BitVec.ofNat 32 p.2

theorem halveQ_ct : RelCT isa (Two HalveRead) VG.Impl.Ffdh.Arm.ParameterCandidate.halveQ (fun _ _ => True) := by
  have head : RelCT isa (Two HalveRead) (.block [.ldrSp .r0 4, .ldrSp .lr 12, .mov .r2 (.imm 0)]) (Two HalvePointers) :=
    two_post (halveHead_ct.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      have out := h.out
      have width := h.width
      change s.mem.readW (State.addr (s.sp + 4#32)) 32 = p.1 at out
      change s.mem.readW (State.addr (s.sp + 12#32)) 32 = BitVec.ofNat 32 p.2 at width
      ffrun [HalvePointers, BitVec.add_zero, h.frame.read (d := 4) (by decide), h.frame.read (d := 12) (by decide), out, width])
  obtain ⟨hint, checked⟩ := halveLoop_taint
  have loop : RelCT isa (Two HalvePointers) (.loop (.block VG.Impl.Ffdh.Arm.ParameterCandidate.halfByte) .ne)
      (fun _ _ => True) := by
    refine two_taint [.r0, .lr] ?_ checked
    intro p s t a b r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact a.1.trans b.1.symm
    · exact a.2.trans b.2.symm
  have tail : RelCT isa (fun s t => s.sp = t.sp)
      (.block [.dp .and .r1 .r1 (.imm 1), .cmp .r1 (.imm 0)]) (fun _ _ => True) :=
    (stackOnly_ct _ rfl).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  exact head.seq ((relCT_keep_sp loop (fun _ _ ⟨_, _, _, sp⟩ => sp)).seq
    (tail.seq (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.HalveResult`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.Halve`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.HalfByte`, which only this module used -/

section

/-! Native byte halving implements the shared safe-prime encoding recurrence. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

theorem halfByte_ok (s : State)
    (read : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0)) 1)
    (write : InRegions s.wr (State.addr (s.gpr .r0)) 1) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.halfByte) s fun t =>
      (t.gpr .r0 = s.gpr .r0 + 1 ∧
        t.gpr .r1 = (s.mem (State.addr (s.gpr .r0))).setWidth 32 >>> 1 ||| s.gpr .r2 ∧
        t.gpr .r2 = ((s.mem (State.addr (s.gpr .r0))).setWidth 32 &&& 1) <<< 7 ∧
        t.gpr .lr = s.gpr .lr - 1 ∧ t.z = (s.gpr .lr - 1 == 0) ∧
        t.mem = s.mem.writeW (State.addr (s.gpr .r0))
          (((s.mem (State.addr (s.gpr .r0))).setWidth 32 >>> 1 ||| s.gpr .r2).setWidth 8)) ∧
        Rest [.r0, .r1, .r2, .r3, .lr] s t := by
  refine withRest_all [.r0, .r1, .r2, .r3, .lr] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.halfByte
  ffrun [BitVec.add_zero, read, write]

theorem halfByte_value (b : Byte) {carry : Nat} (bound : carry ≤ 1) :
    ((b.setWidth 32 >>> 1) ||| BitVec.ofNat 32 (128 * carry)) =
      BitVec.ofNat 32 (b.toNat / 2 + 128 * carry) := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_using [] : b.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega_using [bound] : 128 * carry < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega_using [bound] : b.toNat / 2 + 128 * carry < 2 ^ 32)]
  rw [Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt (by omega_using [] : b.toNat / 2 < 2 ^ 7) carry]
  omega_using []

theorem halfByte_encoding (b : Byte) {carry : Nat} (bound : carry ≤ 1) :
    (((b.setWidth 32 >>> 1) ||| BitVec.ofNat 32 (128 * carry)).setWidth 8) =
      VG.Proof.Ffdh.ParameterCandidate.halfByte carry b := by
  rw [halfByte_value b bound]
  simp only [VG.Proof.Ffdh.ParameterCandidate.halfByte, BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 32)]

theorem halfByte_carry (b : Byte) :
    ((b.setWidth 32 &&& 1) <<< 7) = BitVec.ofNat 32 (128 * (b.toNat % 2)) := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by omega_using [] : b.toNat < 2 ^ 32), Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  change ((b.toNat &&& (2 ^ 1 - 1)) * 2 ^ 7) % 2 ^ 32 = (128 * (b.toNat % 2)) % 2 ^ 32
  rw [Nat.and_two_pow_sub_one_eq_mod]
  congr 1
  omega_using []

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


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
      have := ctx.distinct i more j (by omega_using [more, hj]) same
      omega_using [hj, this]), bytes i more]
  have newByte : (((s.mem (State.addr (s.gpr .r0))).setWidth 32 >>> 1 |||
      s.gpr .r2).setWidth 8) =
        VG.Proof.Ffdh.ParameterCandidate.halfByte (carryAt 0 bs i) (bs[i]?.getD 0) := by
    rw [original, inv.carry]
    exact halfByte_encoding _ (carryAt_le (by decide) bs i)
  refine ⟨⟨by omega_using [more], ?_, ?_, ?_, ?_, ?_, ?_, inv.rest.trans rest⟩, ?_⟩
  · rw [ptr, inv.dest, BitVec.add_assoc]
    change dst + (BitVec.ofNat 32 i + BitVec.ofNat 32 1) = _
    rw [← BitVec.ofNat_add]
  · rw [count, inv.count]
    change BitVec.ofNat 32 (bs.length - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [more])]
    congr 1
  · rw [carry, original, halfByte_carry, carryAt_next 0 more]
    simp only [List.getElem?_eq_getElem more, Option.getD_some]
  · intro j hj
    have same : j = i := by omega_using [hj]
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
        fun h => same (ctx.distinct j (by omega_using [more, hj]) i more h)
      rw [ite_eq_right different]
      exact inv.shifted j (by omega_using [hj, same])
  · intro a ha
    rw [mem, VG.WriteBytes.writeW8_apply, inv.dest, ite_eq_right (ha i (by omega_using []))]
    exact inv.outside a fun j hj => ha j (by omega_using [hj])
  · rw [zero, inv.count]
    change (BitVec.ofNat 32 (bs.length - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [more]),
      ofNat_beq_zero (by have := ctx.countFits; omega_using [this])]
    simp only [show bs.length - i - 1 = 0 ↔ i + 1 = bs.length by omega_using [more]]

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
    refine WP.mono (halveBody_ok ctx bytes hi (by omega_using [hik, hk])) ?_
    rintro u ⟨hu, hz⟩
    by_cases last : i + 1 = bs.length
    · left
      refine ⟨?_, last ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, last, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega_using [hk], i + 1, by omega_using [hik, hk], by omega_using [hik, hk, last], hu⟩
      change some (!u.z) = some true
      simp only [hz, last, decide_false, Bool.not_false]
  · refine ⟨0, by omega_using [], positive, ?_⟩
    exact ⟨by omega_using [], by simpa using dest, by simpa using count,
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
    rw [VG.Arm.addr_add (by omega_using [fits, bound] : dst.toNat + j < 2 ^ 32)] at byte
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    rw [halfOctets_get 0 bound]
    simpa only [List.getElem?_eq_getElem bound, Option.getD_some] using byte

theorem HalfInv.value {s0 s : State} {dst : BitVec 32} {bs : List Byte}
    (inv : HalfInv s0 dst bs bs.length s) (fits : dst.toNat + bs.length ≤ 2 ^ 32) :
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) bs.length) = Spec.Rsa.os2ip bs / 2 := by
  rw [inv.encoding fits, VG.Proof.Ffdh.ParameterCandidate.halfOctets_zero]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! Output framing and final parity of the native byte-halving loop. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Ffdh.ParameterCandidate (carryAt carryAt_le halfByte_val)

theorem HalfInv.frame {s0 s : State} {dst : BitVec 32} {bs : List Byte} {i : Nat}
    (inv : HalfInv s0 dst bs i s) (fit : dst.toNat + bs.length ≤ 2 ^ 32) :
    Frame [⟨State.addr dst, bs.length⟩] s0.mem s.mem := by
  intro a ha
  apply inv.outside a
  intro j hj equal
  apply ha ⟨State.addr dst, bs.length⟩ (by simp)
  rw [equal, VG.Arm.addr_add (by have := inv.index; omega_using [fit, hj, this])]
  exact Offset.contains_base _ (by have := inv.index; omega_using [hj, this]) (by have := inv.index; omega_using [fit, hj, this])

theorem HalfInv.parity {s0 s : State} {dst : BitVec 32} {bs : List Byte}
    (inv : HalfInv s0 dst bs bs.length s) (positive : 0 < bs.length)
    (fits : dst.toNat + bs.length ≤ 2 ^ 32) :
    (s.gpr .r1).toNat % 2 = (Spec.Rsa.os2ip bs / 2) % 2 := by
  have last := inv.last (bs.length - 1) (by omega_using [positive])
  have byte := inv.shifted (bs.length - 1) (by omega_using [positive])
  rw [VG.Arm.addr_add (by omega_using [fits] : dst.toNat + (bs.length - 1) < 2 ^ 32)] at byte
  have carry := carryAt_le (by decide : 0 ≤ 1) bs (bs.length - 1)
  have byteBound := (bs[bs.length - 1]?.getD 0).isLt
  have value : (s.gpr .r1).toNat =
      (bs[bs.length - 1]?.getD 0).toNat / 2 + 128 * carryAt 0 bs (bs.length - 1) := by
    rw [last, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [carry] :
      (bs[bs.length - 1]?.getD 0).toNat / 2 + 128 * carryAt 0 bs (bs.length - 1) < 2 ^ 32)]
  have residue := candidate_mod8_last s.mem (State.addr dst) positive
  rw [inv.value fits, byte, halfByte_val carry] at residue
  omega_using [value, residue]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Divide the shaped p into q in place without disturbing the RSA sieve table. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/HalveQ.lean`, which only this module imported.
section

/-! Complete candidate halving, including native argument loads and q's parity. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.ParameterCandidate (halfOctets)

private theorem halveHead_ok {s : State} {dst : BitVec 32} {n : Nat}
    (frame : SavedFrame (readValues dst n) [4, 12] s) :
    WP isa (.block [.ldrSp .r0 4, .ldrSp .lr 12, .mov .r2 (.imm 0)]) s fun t =>
      (t.gpr .r0 = dst ∧ t.gpr .lr = BitVec.ofNat 32 n ∧ t.gpr .r2 = 0 ∧ t.mem = s.mem) ∧
        Rest [.r0, .r2, .lr] s t := by
  have out : s.mem.readW (State.addr (s.sp + 4#32)) 32 = dst := frame.saved 4 (by simp)
  have width : s.mem.readW (State.addr (s.sp + 12#32)) 32 = BitVec.ofNat 32 n := frame.saved 12 (by simp)
  refine withRest_all [.r0, .r2, .lr] ?_ (by rfl) (by rfl)
  ffrun [BitVec.add_zero, frame.read (d := 4) (by decide), frame.read (d := 12) (by decide), out, width]

private theorem andOne (x : BitVec 32) : x &&& 1 = BitVec.ofNat 32 (x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x.toNat % 2 < 2 ^ 32)]
  change x.toNat &&& (2 ^ 1 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ _

private theorem halveTail_ok (s : State) :
    WP isa (.block [.dp .and .r1 .r1 (.imm 1), .cmp .r1 (.imm 0)]) s fun t =>
      (t.z = decide ((s.gpr .r1).toNat % 2 = 0) ∧ t.mem = s.mem) ∧ Rest [.r1] s t := by
  have zero : ((s.gpr .r1 &&& 1) - (0 : BitVec 32) == (0 : BitVec 32)) =
      decide ((s.gpr .r1).toNat % 2 = 0) := by
    change ((s.gpr .r1 &&& 1) - 0#32 == 0#32) = _
    rw [BitVec.sub_zero, andOne]
    exact ofNat_beq_zero (by omega)
  refine withRest_all [.r1] ?_ (by rfl) (by rfl)
  ffrun [zero]

theorem halveQ_ok {s : State} {dst : BitVec 32} {bs : List Byte}
    (frame : SavedFrame (readValues dst bs.length) [4, 12] s)
    (ctx : MaskCtx s dst bs.length) (positive : 0 < bs.length)
    (fits : dst.toNat + bs.length ≤ 2 ^ 32)
    (bytes : ∀ j < bs.length, s.mem (State.addr (dst + BitVec.ofNat 32 j)) = bs[j]?.getD 0) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.halveQ s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) bs.length = halfOctets 0 bs ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (State.addr dst) bs.length) = Spec.Rsa.os2ip bs / 2 ∧
      t.z = decide ((Spec.Rsa.os2ip bs / 2) % 2 = 0) ∧
      Frame [⟨State.addr dst, bs.length⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.halveQ VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (halveHead_ok frame) ?_)
  rintro u ⟨⟨ptr, count, carry, memory⟩, rest⟩
  have ctxU : MaskCtx u dst bs.length := ⟨ctx.countFits,
    by intro i hi; rw [rest.rd, rest.wr]; exact ctx.readable i hi,
    by intro i hi; rw [rest.wr]; exact ctx.writable i hi, ctx.distinct⟩
  refine WP.seq (WP.mono (halveLoop_ok u ctxU positive
    (by intro j hj; rw [memory]; exact bytes j hj) ptr count carry) ?_)
  intro v inv
  refine WP.seq (WP.mono (halveTail_ok v) ?_)
  rintro t ⟨⟨flagT, memoryT⟩, restT⟩
  have changed := inv.frame fits
  rw [memory] at changed
  refine WP.block_nil ⟨?_, ?_, ?_, ?_,
    ((rest.mono (by simp)).trans inv.rest).trans (restT.mono (by simp))⟩
  · rw [memoryT]
    exact inv.encoding fits
  · rw [memoryT]
    exact inv.value fits
  · rw [flagT, inv.parity positive fits]
  · rwa [memoryT]

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (arrAt)

theorem candidateHalveValue_ok {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.halveQ s fun t =>
      CandidateContext p consumed t ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length) = (p.candidate - 1) / 2 ∧
      t.z = decide (((p.candidate - 1) / 2) % 2 = 0) ∧
      Frame [⟨State.addr p.out, p.length⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let bs := Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length
  have size : bs.length = p.length := by simp [bs, Spec.Rsa.bytesAt]
  have saved : SavedFrame (readValues p.out bs.length) [4, 12] s := by rw [size]; exact h.read_context.frame
  have mask : MaskCtx s p.out bs.length := by rw [size]; exact h.mask
  have bytes : ∀ j < bs.length, s.mem (State.addr (p.out + BitVec.ofNat 32 j)) = bs[j]?.getD 0 := by
    intro j hj
    have bound : j < p.length := by rwa [size] at hj
    rw [VG.Arm.addr_add (by have fit : p.out.toNat + p.length ≤ 2 ^ 32 := p.outputFits; omega_using [bound, fit])]
    simp only [bs, Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range bound, Option.map_some, Option.getD_some]
  refine WP.mono (halveQ_ok saved mask (by rw [size]; have := p.length_bounds; omega_using [this])
    (by rw [size]; exact p.outputFits) bytes) ?_
  rintro t ⟨_, value, zero, changed, rest⟩
  rw [size] at value changed
  have source : Spec.Rsa.os2ip bs = p.candidate := number
  have half : p.candidate / 2 = (p.candidate - 1) / 2 := by have := p.candidate_odd; omega_using [this]
  rw [source, half] at value zero
  exact ⟨h.after_output changed rest, value, zero, changed,
    rest.mono (by simp [roundClobbers])⟩


end VG.Proof.Ffdh.Arm.ParameterCandidate
