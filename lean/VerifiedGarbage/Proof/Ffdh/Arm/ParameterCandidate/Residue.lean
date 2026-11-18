module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ReadContext
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ResidueLow
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ResidueBytes
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialValue
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialStart
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialOctets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialFlag
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! ### `Ffdh.Arm.ParameterCandidate.TrialResidue`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.TrialSmall`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.TrialLoop`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.TrialLoopFrom`, which only this module used -/

section

/-! A bounded initial carry lets the same RSA reducer test p and p-1 from the same bytes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

private def loopRegs : List Reg := [.r0, .r1, .r2, .r5, .r6, .r7]

theorem trialLoop_from_ok (s : State) {n divisor inverse initial : Nat}
    (positive : 0 < n) (fits : n < 2 ^ 32)
    (count : s.gpr .r1 = BitVec.ofNat 32 n) (read : TrialReadable s (s.gpr .r0) n)
    (acc : s.gpr .r2 = BitVec.ofNat 32 initial) (initialBound : initial < 2*divisor)
    (divValue : s.gpr .r3 = BitVec.ofNat 32 divisor) (divBound : 3 ≤ divisor ∧ divisor < 8162)
    (invValue : (s.gpr .r4).toNat = inverse) (invCorrect : (divisor * inverse + 1) % 2 ^ 16 = 0) :
    WP isa (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.trialStep .ne) s fun t =>
      ∃ next j, next < 2 * divisor ∧ t.gpr .r2 = BitVec.ofNat 32 next ∧
        next * 2 ^ (16 * j) % divisor = (initial+trialValue s.mem (s.gpr .r0) n) % divisor ∧
        t.gpr .r1 = 0 ∧ t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r5, .r6, .r7] s t := by
  let original := initial+trialValue s.mem (s.gpr .r0) n
  let inv := fun k t => ∃ j a, 0 < k ∧ k < 2 ^ 32 ∧
    TrialReadable t (t.gpr .r0) k ∧ t.gpr .r1 = BitVec.ofNat 32 k ∧
    a < 2 * divisor ∧ t.gpr .r2 = BitVec.ofNat 32 a ∧
    (a + trialValue t.mem (t.gpr .r0) k) * 2 ^ (16 * j) % divisor = original % divisor ∧
    t.mem = s.mem ∧ Rest loopRegs s t
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro k u h
    obtain ⟨j, a, kp, kfit, readable, cnt, ab, av, cong, memory, rest⟩ := h
    refine WP.mono (trialStep_ok u kp kfit cnt (readable.low kp) (fun h => readable.high h)
      av ab ((rest.gpr .r3 (by simp [loopRegs])).trans divValue) divBound
      (by rw [rest.gpr .r4 (by simp [loopRegs])]; exact invValue) invCorrect) ?_
    rintro t ⟨b, bb, step, bv, ptr, cnt', flag, mem, keep⟩
    have congruence : (b + trialValue t.mem (t.gpr .r0) (k - min 2 k)) *
        2 ^ (16 * (j + 1)) % divisor = original % divisor := by
      rw [trialValue_step u.mem (u.gpr .r0) kp] at cong
      rw [mem, ptr]
      exact trialRemaining_congruence step cong
    have nextRead : TrialReadable t (t.gpr .r0) (k - min 2 k) := by
      rw [ptr]
      exact readable.advance keep (Nat.min_le_right 2 k)
    have kept : Rest loopRegs s t := rest.trans keep
    by_cases last : k ≤ 2
    · have remZero : k - min 2 k = 0 := by omega_using [last]
      left
      refine ⟨?_, b, j + 1, bb, bv, ?_, ?_, mem.trans memory, kept⟩
      · change some (!t.z) = some false
        simp only [flag, last, decide_true, Bool.not_true]
      · simpa only [remZero, trialValue, Nat.add_zero] using congruence
      · rw [cnt', remZero]
        rfl
    · right
      refine ⟨?_, k - min 2 k, by omega_using [kp], j + 1, b, by omega_using [last], by omega_using [kfit],
        nextRead, cnt', bb, bv, congruence, mem.trans memory, kept⟩
      change some (!t.z) = some true
      simp only [flag, last, decide_false, Bool.not_false]
  · refine ⟨0, initial, positive, fits, read, count, initialBound, acc, ?_, rfl, Rest.refl _ _⟩
    · simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
      rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! The original zero-carry trial loop delegates to the shared bounded-carry proof. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

theorem trialLoop_ok (s : State) {n divisor inverse : Nat}
    (positive : 0 < n) (fits : n < 2 ^ 32)
    (count : s.gpr .r1 = BitVec.ofNat 32 n) (read : TrialReadable s (s.gpr .r0) n)
    (acc : s.gpr .r2 = 0)
    (divValue : s.gpr .r3 = BitVec.ofNat 32 divisor) (divBound : 3 ≤ divisor ∧ divisor < 8162)
    (invValue : (s.gpr .r4).toNat = inverse) (invCorrect : (divisor * inverse + 1) % 2 ^ 16 = 0) :
    WP isa (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.trialStep .ne) s fun t =>
      ∃ next j, next < 2 * divisor ∧ t.gpr .r2 = BitVec.ofNat 32 next ∧
        next * 2 ^ (16 * j) % divisor = trialValue s.mem (s.gpr .r0) n % divisor ∧
        t.gpr .r1 = 0 ∧ t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r5, .r6, .r7] s t := by
  simpa only [Nat.zero_add] using trialLoop_from_ok s (initial:=0) positive fits count read
    (by simpa using acc) (by have := divBound.1; omega_using [divBound]) divValue divBound invValue invCorrect

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! Trial division of an entire FFDH candidate by one prime, using RSA's
verified native reducer and inverse computation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

private def trialRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7]

theorem trialSmall_value_ok (s : State) (dst : BitVec 32) {n prime : Nat}
    (positive : 0 < n) (fits : n < 2 ^ 32) (bufferFits : dst.toNat + n ≤ 2 ^ 32)
    (primeBound : prime < 1024)
    (divisor : s.gpr .r7 = BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry prime))
    (readOut : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 4)) 4)
    (readWidth : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 12)) 4)
    (out : s.mem.readW (State.addr (s.sp + 4)) 32 = dst)
    (width : s.mem.readW (State.addr (s.sp + 12)) 32 = BitVec.ofNat 32 n)
    (read : TrialReadable s (dst + BitVec.ofNat 32 n) n) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.trialSmall s fun t =>
      ∃ next steps, next < 2 * VG.Impl.RsaKeyGen.tabEntry prime ∧ t.gpr .r2 = BitVec.ofNat 32 next ∧
        next * 2 ^ (16 * steps) % VG.Impl.RsaKeyGen.tabEntry prime =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % VG.Impl.RsaKeyGen.tabEntry prime ∧
      t.z = decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) %
        VG.Impl.RsaKeyGen.tabEntry prime = 0) ∧ t.mem = s.mem ∧
        Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7] s t := by
  have facts := VG.Proof.RsaKeyGen.tabEntry_facts primeBound
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.trialSmall VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (trialStart_ok s dst n readOut readWidth out width) ?_)
  rintro u ⟨⟨ptr, cnt, zero, div, inverse, mem⟩, rest⟩
  have readable : TrialReadable u (u.gpr .r0) n := by
    rw [ptr]
    intro i hi
    rw [rest.rd, rest.wr]
    exact read i hi
  have inv : (u.gpr .r4).toNat =
      (VG.Proof.RsaKeyGen.ninv (BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry prime))).toNat := by
    rw [inverse, divisor]
  refine WP.seq (WP.mono (trialLoop_ok u positive fits cnt readable zero (div.trans divisor)
    facts.2 inv (VG.Proof.RsaKeyGen.ninv_tab primeBound)) ?_)
  rintro v ⟨next, steps, bound, value, congruence, _, memory, keep⟩
  have inputValue : trialValue u.mem (u.gpr .r0) n =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) := by
    rw [mem, ptr, trialValue_octets, trialBytes_at _ _ fits bufferFits]
  rw [inputValue] at congruence
  have divides := trialDigit_divides facts.1 bound congruence
  have divV : v.gpr .r3 = BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry prime) :=
    (keep.gpr .r3 (by simp)).trans (div.trans divisor)
  have preserved : Rest trialRegs s v := (rest.mono (by simp [trialRegs])).trans (keep.mono (by simp [trialRegs]))
  refine WP.seq (WP.mono (trialFlag_ok v) ?_)
  rintro t ⟨flag, memT, restT⟩
  refine WP.block_nil ⟨next, steps, bound, (restT.gpr .r2 (by simp)).trans value, congruence,
    ?_, memT.trans (memory.trans mem), preserved.trans (restT.mono (by simp))⟩
  rw [flag, value, divV, ofNat_beq_zero (by omega_using [facts, bound] : next < 2 ^ 32),
    ofNat_beq_eq (by omega_using [facts, bound] : next < 2 ^ 32) (by omega_using [facts] : VG.Impl.RsaKeyGen.tabEntry prime < 2 ^ 32),
    ← Bool.decide_or]
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using divides.symm

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! The shared RSA radix-2^16 remainder is an ordinary remainder modulo
3 and 5, because its radix is 1 modulo either divisor. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

theorem trialPrime3 : VG.Impl.RsaKeyGen.tabEntry 0 = 3 := by
  unfold VG.Impl.RsaKeyGen.tabEntry VG.Impl.RsaKeyGen.slots
  rw [VG.Impl.RsaKeyGen.primes.lit_eq]
  rfl

theorem trialPrime5 : VG.Impl.RsaKeyGen.tabEntry 1 = 5 := by
  unfold VG.Impl.RsaKeyGen.tabEntry VG.Impl.RsaKeyGen.slots
  rw [VG.Impl.RsaKeyGen.primes.lit_eq]
  rfl

private theorem radix_fixed {prime : Nat} (bound : prime < 2) (steps : Nat) :
    2 ^ (16 * steps) % VG.Impl.RsaKeyGen.tabEntry prime = 1 := by
  have fixed : 2 ^ 16 % VG.Impl.RsaKeyGen.tabEntry prime = 1 := by
    rcases (by omega_using [bound] : prime = 0 ∨ prime = 1) with rfl | rfl
    · rw [trialPrime3]
    · rw [trialPrime5]
  rw [Nat.pow_mul, Nat.pow_mod, fixed, Nat.one_pow]
  have positive : 1 < VG.Impl.RsaKeyGen.tabEntry prime := by
    rcases (by omega_using [bound] : prime = 0 ∨ prime = 1) with rfl | rfl
    · rw [trialPrime3]; decide
    · rw [trialPrime5]; decide
  exact Nat.mod_eq_of_lt positive

theorem trialSmall_residue_ok (s : State) (dst : BitVec 32) {n prime : Nat}
    (positive : 0 < n) (fits : n < 2 ^ 32) (bufferFits : dst.toNat + n ≤ 2 ^ 32)
    (primeBound : prime < 2)
    (divisor : s.gpr .r7 = BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry prime))
    (readOut : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 4)) 4)
    (readWidth : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 12)) 4)
    (out : s.mem.readW (State.addr (s.sp + 4)) 32 = dst)
    (width : s.mem.readW (State.addr (s.sp + 12)) 32 = BitVec.ofNat 32 n)
    (read : TrialReadable s (dst + BitVec.ofNat 32 n) n) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.trialSmall s fun t =>
      ∃ next, next < 2 * VG.Impl.RsaKeyGen.tabEntry prime ∧ t.gpr .r2 = BitVec.ofNat 32 next ∧
        next % VG.Impl.RsaKeyGen.tabEntry prime =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % VG.Impl.RsaKeyGen.tabEntry prime ∧
        t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7] s t := by
  refine WP.mono (trialSmall_value_ok s dst positive fits bufferFits (by omega_using [primeBound]) divisor
    readOut readWidth out width read) ?_
  rintro t ⟨next, steps, bound, value, congruence, _, memory, rest⟩
  have residue : next % VG.Impl.RsaKeyGen.tabEntry prime =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % VG.Impl.RsaKeyGen.tabEntry prime := by
    rw [Nat.mul_mod, radix_fixed primeBound steps, Nat.mul_one, Nat.mod_mod] at congruence
    exact congruence
  exact ⟨next, bound, value, residue, memory, rest⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Complete generator residue screening, using the shared RSA reducer. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/ResidueEquals.lean`, which only this module imported.
section

/-! Short public residue tests after the shared RSA radix-2^16 reducer. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm

theorem residueEquals_ok (s : State) (first : Nat) (rest : List Nat)
    (bounds : ∀ v ∈ first :: rest, v < 256) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.residueEquals (first :: rest)) s fun t =>
      t.z = (first :: rest).any (fun v => s.gpr .r2 == BitVec.ofNat 32 v) ∧ t.mem = s.mem ∧ Rest [] s t := by
  induction rest generalizing first s with
  | nil =>
    simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.residueEquals]
    refine wp_cmp (op2_imm (encodable_byte (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := bounds first (by simp); omega)]
      exact bounds first (by simp)))) fun t changed flag => WP.block_nil ?_
    refine ⟨?_, changed.mem, changed.rest []⟩
    rw [flag, sub_beq_zero]
    simp only [List.any_cons, List.any_nil, Bool.or_false]
  | cons next rest ih =>
    simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.residueEquals]
    refine WP.seq (wp_cmp (op2_imm (encodable_byte (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := bounds first (by simp); omega)]
      exact bounds first (by simp)))) fun u changed flag => WP.block_nil ?_)
    have zero : u.z = (s.gpr .r2 == BitVec.ofNat 32 first) := by rw [flag, sub_beq_zero]
    by_cases same : (s.gpr .r2 == BitVec.ofNat 32 first) = true
    · refine WP.ite true (by change some u.z = some true; rw [zero, same]) ?_ (by intro h; cases h)
      intro _
      exact WP.block_nil ⟨by simp only [List.any_cons, same, Bool.true_or]; exact zero.trans same,
        changed.mem, changed.rest []⟩
    · have different : (s.gpr .r2 == BitVec.ofNat 32 first) = false := by
        cases h : (s.gpr .r2 == BitVec.ofNat 32 first) <;> simp_all
      refine WP.ite false (by change some u.z = some false; rw [zero, different]) (by intro h; cases h) ?_
      intro _
      refine WP.mono (ih u next (by intro v hv; exact bounds v (by simp only [List.mem_cons] at hv ⊢; exact .inr hv))) ?_
      rintro t ⟨last, memory, restT⟩
      refine ⟨?_, memory.trans changed.mem, (changed.rest []).trans restT⟩
      rw [List.any_cons, different, Bool.false_or]
      simpa only [changed.gpr] using last

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/ResiduePrime.lean`, which only this module imported.
section

/-! Compose the shared trial reducer with a bounded public residue list. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

private theorem residueAny {acc : Nat} {values : List Nat}
    (accBound : acc < 2 ^ 32) (bounds : ∀ v ∈ values, v < 256) :
    values.any (fun v => BitVec.ofNat 32 acc == BitVec.ofNat 32 v) = decide (acc ∈ values) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨v, hv, equal⟩
    rw [ofNat_beq_eq accBound (by have := bounds v hv; omega), decide_eq_true_eq] at equal
    rwa [equal]
  · intro member
    exact ⟨acc, member, by simp⟩

theorem residuePrime_ok {s : State} {dst : BitVec 32} {n prime : Nat}
    (h : ReadContext dst n s) (primeBound : prime < 2) (first : Nat) (rest : List Nat)
    (bounds : ∀ v ∈ first :: rest, v < 256) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.residuePrime
      (VG.Impl.RsaKeyGen.tabEntry prime) (first :: rest)) s fun t =>
      ∃ acc, acc < 2 * VG.Impl.RsaKeyGen.tabEntry prime ∧
        acc % VG.Impl.RsaKeyGen.tabEntry prime =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % VG.Impl.RsaKeyGen.tabEntry prime ∧
        t.z = decide (acc ∈ first :: rest) ∧ t.mem = s.mem ∧
        Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7] s t := by
  have small : VG.Impl.RsaKeyGen.tabEntry prime < 256 := by
    rcases (by omega : prime = 0 ∨ prime = 1) with rfl | rfl
    · rw [trialPrime3]; decide
    · rw [trialPrime5]; decide
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.residuePrime VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (wp_mov (op2_imm (encodable_byte (by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : VG.Impl.RsaKeyGen.tabEntry prime < 2 ^ 32)]
    exact small))) fun u moved => WP.block_nil ?_)
  have ctx := h.after_memory moved.mem (moved.rest (by simp : Reg.r7 ∈ [Reg.r7]))
  refine WP.seq (WP.mono (trialSmall_residue_ok u dst h.positive h.countFits h.bufferFits
    primeBound moved.gpr (ctx.frame.read (by decide)) (ctx.frame.read (by decide)) ctx.out ctx.width ctx.readable) ?_)
  rintro v ⟨acc, bound, value, residue, memory, keep⟩
  refine WP.seq (WP.mono (residueEquals_ok v first rest bounds) ?_)
  rintro t ⟨flag, memT, restT⟩
  refine WP.block_nil ⟨acc, bound, ?_, ?_, memT.trans (memory.trans moved.mem),
    (moved.rest (by simp : Reg.r7 ∈ [Reg.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7])).trans
      (keep.trans (restT.mono (by simp)))⟩
  · simpa only [moved.mem] using residue
  · rw [value, residueAny (by omega : acc < 2 ^ 32) bounds] at flag
    exact flag

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

private theorem residue3_accept {acc p : Nat} (bound : acc < 6)
    (residue : acc % 3 = p % 3) (low : p % 8 = 3) :
    (acc ∈ [2, 5]) ↔ p % 24 = 11 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  have criterion := residue24 (n := p)
  omega_using [bound, residue, low]

private theorem residue5_accept {acc p : Nat} (bound : acc < 10)
    (residue : acc % 5 = p % 5) (odd : p % 2 = 1) :
    (acc ∈ [2, 3, 7, 8]) ↔ p % 10 = 3 ∨ p % 10 = 7 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  have criterion := residue10 odd
  omega_using [bound, residue, odd]

theorem residue2_ok {s : State} {dst : BitVec 32} {n : Nat} (h : ReadContext dst n s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.residue2 s fun t =>
      t.z = decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % 24 = 11) ∧
        t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.residue2
  refine WP.seq (WP.mono (residueLow_ok s dst n (h.frame.read (by decide))
    (h.frame.read (by decide)) h.out h.width (h.readable.low h.positive)) ?_)
  rintro u ⟨⟨flag, memory⟩, rest⟩
  have last := candidate_mod8_last s.mem (State.addr dst) h.positive
  rw [h.lastAddress, ← last] at flag
  let p := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)
  change u.z = decide (p % 8 = 3) at flag
  by_cases low : p % 8 = 3
  · refine WP.ite true (by change some u.z = some true; rw [flag, decide_eq_true low]) ?_ (by intro h; cases h)
    intro _
    have trial := residuePrime_ok (h.after_memory memory rest) (prime := 0) (by decide) 2 [5] (by simp)
    rw [trialPrime3] at trial
    refine WP.mono trial ?_
    rintro t ⟨acc, bound, residue, accepted, memT, restT⟩
    have congruence : acc % 3 = p % 3 := by simpa only [memory] using residue
    exact ⟨accepted.trans (decide_eq_decide.mpr (residue3_accept bound congruence low)),
      memT.trans memory, (rest.mono (by simp)).trans restT⟩
  · refine WP.ite false (by change some u.z = some false; rw [flag, decide_eq_false low]) (by intro h; cases h) ?_
    intro _
    have reject : ¬ p % 24 = 11 := by have criterion := residue24 (n := p); omega_using [low]
    refine WP.block_nil ⟨?_, memory, rest.mono (by simp)⟩
    change u.z = decide (p % 24 = 11)
    rw [flag, decide_eq_false low, decide_eq_false reject]

theorem residue5_ok {s : State} {dst : BitVec 32} {n : Nat} (h : ReadContext dst n s)
    (odd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.residue5 s fun t =>
      t.z = decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % 10 = 3 ∨
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % 10 = 7) ∧
        t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.residue5
  have trial := residuePrime_ok h (prime := 1) (by decide) 2 [3, 7, 8] (by simp)
  rw [trialPrime5] at trial
  refine WP.mono trial ?_
  rintro t ⟨acc, bound, residue, flag, memory, rest⟩
  exact ⟨flag.trans (decide_eq_decide.mpr (residue5_accept bound residue odd)), memory, rest⟩

theorem residueHead_ok {s : State} {dst : BitVec 32} {n generator : Nat}
    (h : ReadContext dst n s) (bound : generator < 2 ^ 32)
    (saved : s.mem.readW (State.addr (s.sp + 28#32)) 32 = BitVec.ofNat 32 generator) :
    WP isa (.block [.ldrSp .r1 28, .cmp .r1 (.imm 2)]) s fun t =>
      (t.z = decide (generator = 2) ∧ t.mem = s.mem) ∧ Rest [.r1] s t := by
  have read := h.frame.read (d := 28) (by decide)
  have zero : ((BitVec.ofNat 32 generator - (2 : BitVec 32)) == (0 : BitVec 32)) = decide (generator = 2) := by
    rw [sub_beq_zero]
    exact ofNat_beq_eq bound (by decide)
  refine withRest_all [.r1] ?_ (by rfl) (by rfl)
  ffrun [BitVec.add_zero, read, saved, zero]

theorem residue_ok {s : State} {dst : BitVec 32} {n generator : Nat}
    (h : ReadContext dst n s) (allowed : generator = 2 ∨ generator = 5)
    (saved : s.mem.readW (State.addr (s.sp + 28#32)) 32 = BitVec.ofNat 32 generator)
    (odd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.residue s fun t =>
      t.z = (if generator = 2 then
        decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % 24 = 11) else
        decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % 10 = 3 ∨
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % 10 = 7)) ∧
      t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.residue
  refine WP.seq (WP.mono (residueHead_ok h (by rcases allowed with rfl | rfl <;> decide) saved) ?_)
  rintro u ⟨⟨flag, memory⟩, rest⟩
  by_cases two : generator = 2
  · refine WP.ite true (by change some u.z = some true; rw [flag, decide_eq_true two]) ?_ (by intro h; cases h)
    intro _
    refine WP.mono (residue2_ok (h.after_memory memory rest)) ?_
    rintro t ⟨flagT, memoryT, restT⟩
    refine ⟨?_, memoryT.trans memory, (rest.mono (by simp)).trans restT⟩
    simpa only [memory, ite_eq_left two] using flagT
  · refine WP.ite false (by change some u.z = some false; rw [flag, decide_eq_false two]) (by intro h; cases h) ?_
    intro _
    refine WP.mono (residue5_ok (h.after_memory memory rest) (by simpa only [memory] using odd)) ?_
    rintro t ⟨flagT, memoryT, restT⟩
    refine ⟨?_, memoryT.trans memory, (rest.mono (by simp)).trans restT⟩
    simpa only [memory, ite_eq_right two] using flagT

end VG.Proof.Ffdh.Arm.ParameterCandidate
