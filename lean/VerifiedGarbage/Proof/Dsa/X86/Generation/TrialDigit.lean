module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Trial
public import VerifiedGarbage.Impl.Mont.X86.Words

/-! Each candidate word is consumed in two bounded radix-2^16 digits. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

def digitHalf (x : BitVec 32) (high : Bool) : BitVec 32 :=
  if high then x >>> 16 else x &&& 65535

theorem digit_half_bound (x : BitVec 32) (high : Bool) :
    (digitHalf x high).toNat < 2 ^ 16 := by
  cases high
  · change (x &&& 65535).toNat < _
    rw [BitVec.toNat_and, show (65535 : BitVec 32).toNat = 2 ^ 16 - 1 by rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (Nat.two_pow_pos 16)
  · change (x >>> 16).toNat < _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := x.isLt
    omega

private theorem load_half {s : State} {offset : Nat} {x : BitVec 32} (high : Bool)
    (read : readSrc s (.mem (at_ .ebp offset)) = some x) :
    WP isa (.block ([.mov .eax (.mem (at_ .ebp offset))] ++
      (if high then [.shift .shr .eax 16] else [.alu .and .eax (.imm 65535)]))) s fun t =>
      t.gpr .eax = digitHalf x high ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  cases high
  · refine wp_movS read fun u U _ => wp_logicS (Or.inl rfl) rfl fun t T => WP.block_nil ?_
    exact ⟨by rw [T.gpr, U.gpr]; rfl, T.mem.trans U.mem, U.keeps.trans T.keeps⟩
  · refine wp_movS read fun u U _ => wp_shr (by decide) fun t T _ => WP.block_nil ?_
    exact ⟨by rw [T.gpr, U.gpr]; rfl, T.mem.trans U.mem, U.keeps.trans T.keeps⟩

theorem trial_digit {s : State} {offset : Nat} {x : BitVec 32} (high : Bool)
    (read : readSrc s (.mem (at_ .ebp offset)) = some x) :
    WP isa (.block (trialDigit offset high)) s fun t =>
      t.gpr .edi = trialWord (digitHalf x high) (s.gpr .edi) (s.gpr .esi) (s.gpr .ebx) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .edi] s t := by
  unfold trialDigit
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (load_half high read) ?_)
  rintro u ⟨value, mem, K⟩
  refine WP.block_append (WP.mono (trial_reduce u) ?_)
  rintro v ⟨reduced, mem', K'⟩
  refine wp_movS rfl fun t U _ => WP.block_nil ⟨?_, U.mem.trans (mem'.trans mem),
    ((K.mono (by decide)).trans (K'.mono (by decide))).trans (U.keeps.mono (by decide))⟩
  rw [U.gpr, reduced, value, K.1 .edi (by decide), K.1 .esi (by decide), K.1 .ebx (by decide)]

theorem trial_candidate_word {s : State} {offset : Nat} {x : BitVec 32}
    (read : readSrc s (.mem (at_ .ebp offset)) = some x)
    (ha : (s.gpr .edi).toNat < 2 * (s.gpr .ebx).toNat)
    (hs : 3 ≤ (s.gpr .ebx).toNat ∧ (s.gpr .ebx).toNat < 8162)
    (hi : ((s.gpr .ebx).toNat * (s.gpr .esi).toNat + 1) % 2 ^ 16 = 0) :
    WP isa (trialCandidateWord offset) s fun t =>
      (t.gpr .edi).toNat < 2 * (s.gpr .ebx).toNat ∧
      (t.gpr .edi).toNat * 2 ^ 32 % (s.gpr .ebx).toNat =
        (x.toNat + (s.gpr .edi).toNat) % (s.gpr .ebx).toNat ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .edi] s t := by
  unfold trialCandidateWord
  refine WP.seq (WP.mono (trial_digit false read) ?_)
  rintro u ⟨first, mem, K⟩
  have R := trial_word_reduces (digit_half_bound x false) ha hs hi
  have ru : readSrc u (.mem (at_ .ebp offset)) = some x := by
    have eq : readSrc u (.mem (at_ .ebp offset)) = readSrc s (.mem (at_ .ebp offset)) := by
      show u.load32 (u.ea (at_ .ebp offset)) = s.load32 (s.ea (at_ .ebp offset))
      have address : u.ea (at_ .ebp offset) = s.ea (at_ .ebp offset) := by
        simp only [State.ea, at_, K.1 .ebp (by decide)]
      simp only [State.load32, address, mem, K.2.1, K.2.2]
    exact eq.trans read
  have ua : (u.gpr .edi).toNat < 2 * (u.gpr .ebx).toNat := by
    rw [first, K.1 .ebx (by decide)]
    exact R.1
  have us : 3 ≤ (u.gpr .ebx).toNat ∧ (u.gpr .ebx).toNat < 8162 := by
    rw [K.1 .ebx (by decide)]; exact hs
  have ui : ((u.gpr .ebx).toNat * (u.gpr .esi).toNat + 1) % 2 ^ 16 = 0 := by
    rw [K.1 .ebx (by decide), K.1 .esi (by decide)]; exact hi
  refine WP.mono (trial_digit true ru) ?_
  rintro t ⟨second, mem', K'⟩
  have T := trial_word_reduces (digit_half_bound x true) ua us ui
  rw [K.1 .ebx (by decide), K.1 .esi (by decide)] at T
  refine ⟨by rw [second, K.1 .esi (by decide), K.1 .ebx (by decide)]; exact T.1,
    ?_, mem'.trans mem, K.trans K'⟩
  rw [second, K.1 .esi (by decide), K.1 .ebx (by decide)]
  have lo : (digitHalf x false).toNat = x.toNat % 2 ^ 16 := by
    change (x &&& 65535).toNat = _
    rw [BitVec.toNat_and, show (65535 : BitVec 32).toNat = 2 ^ 16 - 1 by rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have high : (digitHalf x true).toNat = x.toNat / 2 ^ 16 := by
    change (x >>> 16).toNat = _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have r1 : (u.gpr .edi).toNat * 2 ^ 16 % (s.gpr .ebx).toNat =
      (x.toNat % 2 ^ 16 + (s.gpr .edi).toNat) % (s.gpr .ebx).toNat := by
    rw [first, ← lo]; exact R.2
  have r2 := T.2
  rw [high] at r2
  have result := VG.Proof.RsaKeyGen.trial_word16 (j := 0)
    (V := (s.gpr .edi).toNat) r1 r2 (by simp)
  change _ = ((s.gpr .edi).toNat + 1 * x.toNat) % _ at result
  rw [Nat.one_mul, Nat.add_comm (s.gpr .edi).toNat x.toNat] at result
  exact result

end VG.Proof.Dsa.X86.Generation
