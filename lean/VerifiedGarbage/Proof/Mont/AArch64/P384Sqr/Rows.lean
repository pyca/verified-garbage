module

public import VerifiedGarbage.Impl.Mont.AArch64.P384Sqr
public import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product

/-!
# P-384's Montgomery square on AArch64: the products of distinct words

`offDiag` (`Impl/Mont/AArch64/P384Sqr.lean`) runs a row for each word
`a_i`, `i < 5`, adding `2^(64 (2i + 1)) a_i [a_(i+1) … a_5]`
(`sqRow_ok`, one symbolic execution for any `i`), so that the accumulator holds
`odd [a]`, the sum of `2^(64 (i + j)) a_i a_j` over `i < j` (`offDiag_ok`).
-/

@[expose] public section

-- Powers of two up to `2^768` (the accumulator) are evaluated.
set_option exponentiation.threshold 1024

namespace VG.Proof.Mont.AArch64.P384Sqr

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P384Sqr VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P384Mul (rwVal_regs)
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

/-- `[a]`'s words after word `i`, as a row multiplies by them. -/
abbrev sqWords (i : Nat) : List RWord := (aRegs.drop (i + 1)).map fun r => .gen (.reg r)

/-- The multiplier of row `i`. -/
abbrev sqX (i : Nat) : Reg := aRegs.getD i .x4

/-- What row `i` needs of its registers. -/
theorem sqRow_facts : ∀ i < 5, (P384Mul.accRegs.take (2 * i + 1)).length = 2 * i + 1 ∧
    (sqRowRegs i).length = 6 - i ∧ (aRegs.drop (i + 1)).length = 5 - i ∧
    P384Mul.accRegs = P384Mul.accRegs.take (2 * i + 1) ++ (sqRowRegs i ++ P384Mul.accRegs.drop (7 + i)) ∧
    (sqRowRegs i).Nodup ∧
    (∀ t ∈ sqRowRegs i, t ≠ .x0 ∧ t ≠ .x2 ∧ t ≠ .x3 ∧ t ≠ .x7 ∧ t ≠ sqX i) ∧
    (∀ r ∈ aRegs.drop (i + 1), r ∉ sqRowRegs i ∧ r ≠ .x2 ∧ r ≠ .x3) ∧
    sqX i ≠ .x2 ∧ sqX i ≠ .x3 ∧ Reg.x27 ∉ Reg.x2 :: .x3 :: sqRowRegs i ∧
    Reg.x7 ∉ Reg.x2 :: .x3 :: sqRowRegs i ∧ sqX i ∉ Reg.x2 :: .x3 :: sqRowRegs i ∧
    (∀ r ∈ aRegs, r ∉ Reg.x2 :: .x3 :: sqRowRegs i) ∧
    (∀ r ∈ P384Mul.accRegs.take (2 * i + 1), r ∉ Reg.x2 :: .x3 :: sqRowRegs i) ∧
    (∀ r ∈ P384Mul.accRegs.drop (7 + i), r ∉ Reg.x2 :: .x3 :: sqRowRegs i) ∧
    (∀ r ∈ Reg.x2 :: .x3 :: sqRowRegs i, r ∈ Reg.x2 :: .x3 :: P384Mul.accRegs) := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> decide

theorem sqRowOk {i : Nat} (hi : i < 5) : RowOk 48 (sqX i) (sqRowRegs i) (sqWords i) := by
  obtain ⟨-, -, -, -, hnd, hregs, hrd, hx2, hx3, -⟩ := sqRow_facts i hi
  have hw : ∀ w ∈ sqWords i, ∃ r ∈ aRegs.drop (i + 1), w = .gen (.reg r) := fun w hw => by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
    exact ⟨r, hr, rfl⟩
  refine ⟨hnd, hregs, fun w h => ?_, fun w h q hq => ?_, hx2, hx3⟩
  · obtain ⟨r, hr, rfl⟩ := hw w h
    exact ⟨(hrd r hr).2.1, (hrd r hr).2.2⟩
  · obtain ⟨r, hr, rfl⟩ := hw w h
    simp only [RWord.reads, Src.reads, Option.mem_def, Option.some.injEq] at hq
    subst hq
    exact hrd _ hr

/-- Row `i`: `[acc] += 2^(64 (2i + 1)) a_i [a_(i+1) … a_5]`, the accumulator
being below `2^(64 (6 + i))` before and `2^(64 (7 + i))` after. -/
theorem sqRow_ok {i : Nat} (hi : i < 5) {s : State} {base : Addr} (hp : Ptr s .x27 base 48)
    (hz : s.gpr .x7 = 0) (hv : regsVal s P384Mul.accRegs < 2 ^ (64 * (6 + i))) :
    WP isa (.block (sqRow i)) s fun t =>
      regsVal t P384Mul.accRegs = regsVal s P384Mul.accRegs +
        2 ^ (64 * (2 * i + 1)) * ((s.gpr (sqX i)).toNat * regsVal s (aRegs.drop (i + 1))) ∧
      regsVal t P384Mul.accRegs < 2 ^ (64 * (7 + i)) ∧
      Keeps (.x2 :: .x3 :: sqRowRegs i) s t := by
  obtain ⟨hlen, hrl, hwl, hsplit, -, -, -, -, -, f27, -, -, -, flo, fhi, -⟩ := sqRow_facts i hi
  have hR := sqRowOk hi
  -- The accumulator around the row's words.
  have hv' := hv
  rw [hsplit, regsVal_append, regsVal_append, hlen, hrl] at hv'
  have hQ : 2 ^ (64 * (6 + i)) = 2 ^ (64 * (2 * i + 1)) * 2 ^ (64 * (5 - i)) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hQ' : 2 ^ (64 * (6 - i)) = 2 ^ 64 * 2 ^ (64 * (5 - i)) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hQ'' : 2 ^ (64 * (7 + i)) = 2 ^ (64 * (2 * i + 1)) * (2 ^ 64 * 2 ^ (64 * (5 - i))) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  generalize hP : 2 ^ (64 * (2 * i + 1)) = P at hQ hQ'' hv' ⊢
  generalize hQv : 2 ^ (64 * (5 - i)) = Q at hQ hQ' hQ''
  have hPpos : 0 < P := hP ▸ Nat.two_pow_pos _
  generalize hL : regsVal s (P384Mul.accRegs.take (2 * i + 1)) = L at hv'
  generalize hT : regsVal s (sqRowRegs i) = T at hv'
  generalize hRst : regsVal s (P384Mul.accRegs.drop (7 + i)) = Rst at hv'
  rw [hQ', hQ] at hv'
  have hin : T + 2 ^ 64 * Q * Rst < Q := by
    refine Nat.lt_of_mul_lt_mul_left (a := P) ?_
    have : P * (T + 2 ^ 64 * Q * Rst) ≤ L + P * (T + 2 ^ 64 * Q * Rst) := Nat.le_add_left _ _
    omega
  have hRst0 : Rst = 0 := by
    rcases Nat.eq_zero_or_pos Rst with h | h
    · exact h
    · have : 2 ^ 64 * Q ≤ 2 ^ 64 * Q * Rst := Nat.le_mul_of_pos_right _ h
      omega
  have hW := regsVal_lt s (aRegs.drop (i + 1))
  rw [hwl, hQv] at hW
  have hx := (s.gpr (sqX i)).isLt
  have hxW : (s.gpr (sqX i)).toNat * regsVal s (aRegs.drop (i + 1)) ≤
      (2 ^ 64 - 1) * regsVal s (aRegs.drop (i + 1)) := Nat.mul_le_mul_right _ (by omega)
  refine WP.mono (row_ok hp hz hR (by decide) (by decide) (fun h => f27 (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ h))) (by simp only [List.length_map, hwl, hrl]; omega)
    (by rw [rwVal_regs, hT, hrl, hQ']; simp only [sqX] at hxW ⊢; omega)) fun t ⟨e, k⟩ => ?_
  rw [rwVal_regs, hT] at e
  have hlo : regsVal t (P384Mul.accRegs.take (2 * i + 1)) = L :=
    hL ▸ regsVal_congr fun r hr => k.gpr r (flo r hr)
  have hhi : regsVal t (P384Mul.accRegs.drop (7 + i)) = Rst :=
    hRst ▸ regsVal_congr fun r hr => k.gpr r (fhi r hr)
  have hLlt : L < P := by
    have := regsVal_lt s (P384Mul.accRegs.take (2 * i + 1)); rw [hlen, hP, hL] at this; exact this
  have hacc : regsVal t P384Mul.accRegs = L + P * (T + (s.gpr (sqX i)).toNat *
      regsVal s (aRegs.drop (i + 1))) := by
    rw [hsplit, regsVal_append, regsVal_append, hlen, hrl, hlo, hhi, e, hRst0, hP]; simp
  have hs : regsVal s P384Mul.accRegs = L + P * T := by
    rw [hsplit, regsVal_append, regsVal_append, hlen, hrl, hL, hT, hRst, hRst0, hP]; simp
  have hT' : T + (s.gpr (sqX i)).toNat * regsVal s (aRegs.drop (i + 1)) ≤ 2 ^ 64 * Q - 1 := by omega
  have h1 := Nat.mul_le_mul_left P hT'
  have h2 : P * (2 ^ 64 * Q - 1) + P = P * (2 ^ 64 * Q) := by
    rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ (by
      have : 0 < Q := hQv ▸ Nat.two_pow_pos _; exact Nat.mul_pos (by decide) this))]
  refine ⟨by rw [hacc, hs, Nat.mul_add, Nat.add_assoc], by rw [hacc, hQ'']; omega, k⟩

end VG.Proof.Mont.AArch64.P384Sqr
