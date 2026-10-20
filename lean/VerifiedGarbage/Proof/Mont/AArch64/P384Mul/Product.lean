module

import VerifiedGarbage.Proof.Mont.AArch64.Rounds
import VerifiedGarbage.Proof.Mont.AArch64.Chain
public import VerifiedGarbage.Proof.Mont.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# P-384's Montgomery product on AArch64: the product

`prod` (`Impl/Mont/AArch64/P384Mul.lean`) clears the twelve words of
`accRegs` and adds `a_i [b]` to its words `i` to `i + 6` for each word `a_i`
of `[a]` (`row_ok`), leaving `[acc] = [a] [b]` (`prod_ok`). `addHigh` adds the high half to the
low half (`addHigh_ok`).
-/

@[expose] public section

-- Powers of two up to `2^448` (the product's rows) are evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.Mont.AArch64.P384Mul

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P384Mul VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut Word64.addCarry_value)

/-- `[b]`'s words, as a row multiplies by them. -/
abbrev bWordsR : List RWord := bRegs384.map fun r => .gen (.reg r)

theorem rwVal_regs (s : State) (base : Addr) :
    ∀ rs : List Reg, rwVal s base (rs.map fun r => .gen (.reg r)) = regsVal s rs
  | [] => rfl
  | r :: rs => by
    rw [List.map_cons, rwVal, rwVal_regs s base rs, regsVal]
    rfl

theorem rowOk (size : Nat) : ∀ i < 6, RowOk size .x1 (rowRegs i) bWordsR := by
  have hw : ∀ w ∈ bWordsR, ∃ r ∈ bRegs384, w = .gen (.reg r) := fun w hw => by
    simpa [eq_comm] using hw
  have hb : ∀ i < 6, ∀ r ∈ bRegs384, r ∉ rowRegs i ∧ r ≠ .x2 ∧ r ≠ .x3 := by decide
  intro i hi
  refine ⟨by revert i; decide, by revert i; decide, fun w h => ?_, fun w h q hq => ?_, by decide, by decide⟩
  · obtain ⟨r, hr, rfl⟩ := hw w h
    exact ⟨(hb i hi r hr).2.1, (hb i hi r hr).2.2⟩
  · obtain ⟨r, hr, rfl⟩ := hw w h
    simp only [RWord.reads, Src.reads, Option.mem_def, Option.some.injEq] at hq
    subst hq
    exact hb i hi _ hr

/-- The accumulator around row `i`'s words. -/
theorem acc_split : ∀ i < 6, accRegs = accRegs.take i ++ (rowRegs i ++ accRegs.drop (i + 7)) := by decide

/-- What the rows need of their registers. -/
theorem row_facts : ∀ i < 6, (accRegs.take i).length = i ∧ (rowRegs i).length = 7 ∧
    ra ∉ Reg.x2 :: .x3 :: rowRegs i ∧ Reg.x7 ∉ Reg.x2 :: .x3 :: rowRegs i ∧
    (∀ r ∈ bRegs384, r ∉ Reg.x2 :: .x3 :: rowRegs i) ∧
    (∀ r ∈ accRegs.take i, r ∉ Reg.x2 :: .x3 :: rowRegs i) ∧
    (∀ r ∈ accRegs.drop (i + 7), r ∉ Reg.x2 :: .x3 :: rowRegs i) ∧
    (∀ r ∈ Reg.x2 :: .x3 :: rowRegs i, r ∈ Reg.x1 :: .x2 :: .x3 :: accRegs) := by
  decide

/-- The rows `0` to `n - 1`: `[acc] = [a_0 … a_(n-1)] [b]`. -/
theorem rowsN_ok {pa : Addr} {B : Nat} :
    ∀ n ≤ 6, ∀ (s : State), Ptr s ra pa 48 → s.gpr .x7 = 0 → regsVal s bRegs384 = B →
      regsVal s accRegs = wordsVal s.mem pa 0 n * B →
      WP isa (.block ((List.range (6 - n)).flatMap fun i =>
          .ldr .x .x1 ra (8 * (n + i)) :: row ra .x1 (rowRegs (n + i)) bWordsR)) s fun t =>
        regsVal t accRegs = wordsVal s.mem pa 0 6 * B ∧ Keeps (.x1 :: .x2 :: .x3 :: accRegs) s t := by
  intro n hn
  induction h : 6 - n generalizing n with
  | zero =>
    intro s _ _ _ hv
    obtain rfl : n = 6 := by omega
    exact WP.block_nil ⟨hv, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    intro s hp hz hB hv
    rw [List.range_succ_eq_map, List.flatMap_cons, WP.block_append_iff]
    simp only [Nat.add_zero]
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ldR_ok hp (d := 8 * n) (by omega) (by omega) .x1) fun s₁ ⟨l₁, k₁, _⟩ => ?_
    have hn6 : n < 6 := by omega
    have hp₁ : Ptr s₁ ra pa 48 := hp.of_keeps k₁ (by decide)
    have hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ (by decide), hz]
    have hB₁ : regsVal s₁ bRegs384 = B := by
      rw [← hB]; exact regsVal_congr fun r hr => k₁.gpr r (by revert r; decide)
    have hacc₁ : regsVal s₁ accRegs = regsVal s accRegs :=
      regsVal_congr fun r hr => k₁.gpr r (by revert r; decide)
    have hR := rowOk 48 n hn6
    obtain ⟨hlen, hrl, fra, f7, fb, flo, fhi, fsub⟩ := row_facts n hn6
    -- The row's words are below `2^384`.
    have hsplit := acc_split n hn6
    have hv₁ := hacc₁.trans hv
    rw [hsplit, regsVal_append, regsVal_append, hlen] at hv₁
    rw [hrl] at hv₁
    have hA := wordsVal_lt s.mem pa 0 n
    have hBl : B < 2 ^ 384 := by
      have := regsVal_lt s bRegs384
      rw [hB, show 64 * bRegs384.length = 384 from rfl] at this
      exact this
    have hAB : wordsVal s.mem pa 0 n * B < 2 ^ (64 * n) * 2 ^ 384 := by
      exact Nat.mul_lt_mul_of_lt_of_le hA (Nat.le_of_lt hBl) (Nat.two_pow_pos 384)
    have hrow : regsVal s₁ (rowRegs n) < 2 ^ 384 := by
      refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (64 * n)) ?_
      have : 2 ^ (64 * n) * regsVal s₁ (rowRegs n) ≤ wordsVal s.mem pa 0 n * B := by
        rw [← hv₁, Nat.mul_add]; omega
      omega
    have hx := (s₁.gpr .x1).isLt
    have hxB : (s₁.gpr .x1).toNat * B ≤ (2 ^ 64 - 1) * 2 ^ 384 :=
      Nat.mul_le_mul (by omega) (Nat.le_of_lt hBl)
    refine WP.mono (row_ok hp₁ hz₁ hR (by decide) (by decide) (fun h => fra (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
      (by rw [hrl]; decide) (by rw [rwVal_regs, hB₁, hrl]; omega)) fun s₂ ⟨e₂, k₂⟩ => ?_
    rw [rwVal_regs, hB₁] at e₂
    have hs₂ : Ptr s₂ ra pa 48 := hp₁.of_keeps k₂ fra
    have hz₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ f7, hz₁]
    have hB₂ : regsVal s₂ bRegs384 = B := by
      rw [← hB₁]; exact regsVal_congr fun r hr => k₂.gpr r (fb r hr)
    have hlo : regsVal s₂ (accRegs.take n) = regsVal s₁ (accRegs.take n) :=
      regsVal_congr fun r hr => k₂.gpr r (flo r hr)
    have hhi : regsVal s₂ (accRegs.drop (n + 7)) = regsVal s₁ (accRegs.drop (n + 7)) :=
      regsVal_congr fun r hr => k₂.gpr r (fhi r hr)
    have hmem : s₂.mem = s.mem := by rw [k₂.mem, k₁.mem]
    have hv₂ : regsVal s₂ accRegs = wordsVal s₂.mem pa 0 (n + 1) * B := by
      rw [hmem, wordsVal_succ_top, Nat.zero_add, ← l₁, hsplit, regsVal_append, regsVal_append, hlen, hrl,
        hlo, hhi, e₂]
      rw [← hlen] at hv₁ ⊢
      have hv₁' := hv₁
      rw [hlen] at hv₁'
      rw [hlen, Nat.add_mul, ← hv₁', Nat.mul_assoc]
      simp only [Nat.mul_add]
      omega
    have := ih (n + 1) (by omega) (by omega) s₂ hs₂ hz₂ hB₂ hv₂
    simp only [show ∀ i, n + 1 + i = n + (i + 1) from fun i => by omega] at this
    rw [List.flatMap_map]
    refine WP.mono this fun t ⟨e, k₃⟩ => ⟨by rw [e, hmem], (k₁.mono (by sub_regs)).trans
      ((k₂.mono fsub).trans k₃)⟩

/-- The product: `[acc] = [a] [b]`, `x7` being zero. -/
theorem prod_ok {s : State} {pa : Addr} (hp : Ptr s ra pa 48) (hz : s.gpr .x7 = 0) :
    WP isa (.block prod) s fun t =>
      regsVal t accRegs = wordsVal s.mem pa 0 6 * regsVal s bRegs384 ∧
      Keeps (.x1 :: .x2 :: .x3 :: accRegs) s t := by
  rw [prod, WP.block_append_iff]
  refine WP.mono (zeros_ok s accRegs) fun s₁ ⟨z₁, k₁⟩ => ?_
  have hB : regsVal s₁ bRegs384 = regsVal s bRegs384 :=
    regsVal_congr fun r hr => k₁.gpr r (by revert r; decide)
  have h0 : regsVal s₁ accRegs = wordsVal s₁.mem pa 0 0 * regsVal s bRegs384 := by
    rw [regsVal_zero z₁, wordsVal, Nat.zero_mul]
  have := rowsN_ok 0 (Nat.zero_le _) s₁ (hp.of_keeps k₁ (by decide)) (by rw [k₁.gpr _ (by decide), hz]) hB h0
  simp only [Nat.zero_add, Nat.sub_zero] at this
  refine WP.mono this fun t ⟨e, k₂⟩ => ⟨by rw [e, k₁.mem], (k₁.mono (by sub_regs)).trans k₂⟩

/-- `ts += hs` with the carry flag in, `adcs` throughout, and its carry out. -/
theorem adcsIn_ok : ∀ (ts hs : List Reg) (s : State), ts.length = hs.length → ts.Nodup →
    (∀ h ∈ hs, h ∉ ts) →
    WP isa (.block (addsIn false ts hs)) s fun t =>
      regsVal t ts + 2 ^ (64 * ts.length) * t.c.toNat = regsVal s ts + regsVal s hs + s.c.toNat ∧
      Keeps ts s t
  | [], [], s, _, _, _ => WP.block_nil ⟨by simp [regsVal], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | [], _ :: _, _, h, _, _ => absurd h (by simp)
  | _ :: _, [], _, h, _, _ => absurd h (by simp)
  | t :: ts, h :: hs, s, hl, hnd, hd => by
    rw [addsIn, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (addc_ok s t t h false (c := s.c) rfl) fun s₁ ⟨v₁, c₁, k₁⟩ => ?_
    have htn : t ∉ ts := (List.nodup_cons.mp hnd).1
    have hhs : ∀ q ∈ hs, q ∉ ts := fun q hq hm => hd q (List.mem_cons_of_mem _ hq) (List.mem_cons_of_mem _ hm)
    refine WP.mono (adcsIn_ok ts hs s₁ (by simpa using hl) (List.nodup_cons.mp hnd).2 hhs) fun s₂ ⟨e₂, k₂⟩ => ?_
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    have ht : t ≠ h := fun e => hd h (List.mem_cons_self ..) (e ▸ List.mem_cons_self ..)
    have g₁ : s₂.gpr t = s₁.gpr t := k₂.gpr t htn
    have gt : regsVal s₁ ts = regsVal s ts := regsVal_congr fun r hr => k₁.gpr r (by
      simp only [List.mem_singleton]; rintro rfl; exact htn hr)
    have gh : regsVal s₁ hs = regsVal s hs := regsVal_congr fun r hr => k₁.gpr r (by
      simp only [List.mem_singleton]; rintro rfl
      exact hd r (List.mem_cons_of_mem _ hr) (List.mem_cons_self ..))
    have hh : s₁.gpr h = s.gpr h := k₁.gpr h (by simpa using Ne.symm ht)
    have ev := Word64.addCarry_value (s.gpr t) (s.gpr h) s.c
    rw [← v₁, ← c₁] at ev
    rw [gt, gh] at e₂
    simp only [regsVal, List.length_cons, g₁, pow64_succ]
    simp only [Nat.mul_assoc] at ev ⊢
    omega

/-- `[x21; low] = low + high`. -/
theorem addHigh_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block addHigh) s fun t =>
      regsVal t lowRegs + 2 ^ 384 * (t.gpr .x21).toNat = regsVal s lowRegs + regsVal s highRegs ∧
      Keeps (.x21 :: lowRegs) s t := by
  rw [addHigh, show lowRegs = .x8 :: lowRegs.tail from rfl, show highRegs = .x14 :: highRegs.tail from rfl,
    addsIn, List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addc_ok s .x8 .x8 .x14 true (c := false) rfl) fun s₁ ⟨v₁, c₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adcsIn_ok lowRegs.tail highRegs.tail s₁ rfl (by decide) (by decide)) fun s₂ ⟨e₂, k₂⟩ => ?_
  apply WP.of_runBlock
  have z₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hz]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write, BitVec.setWidth_eq,
    Option.some.injEq, exists_eq_left', z₂]
  refine ⟨?_, ⟨fun r hr => ?_, by rw [RegUpd.mem_write, k₂.mem, k₁.mem], by rw [RegUpd.rd_write, k₂.rd, k₁.rd],
    by rw [RegUpd.wr_write, k₂.wr, k₁.wr], by rw [RegUpd.sp_write, k₂.sp, k₁.sp]⟩⟩
  · have gt : regsVal s₁ lowRegs.tail = regsVal s lowRegs.tail :=
      regsVal_congr fun r hr => k₁.gpr r (by revert r; decide)
    have gh : regsVal s₁ highRegs.tail = regsVal s highRegs.tail :=
      regsVal_congr fun r hr => k₁.gpr r (by revert r; decide)
    have g8 : s₂.gpr .x8 = s₁.gpr .x8 := k₂.gpr _ (by decide)
    have h14 : s₁.gpr .x14 = s.gpr .x14 := k₁.gpr _ (by decide)
    have hlow : regsVal (s₂.write .x .x21 (0 + 0 + BitVec.ofNat Size.x.bits s₂.c.toNat)) (.x8 :: lowRegs.tail) =
        regsVal s₂ (.x8 :: lowRegs.tail) := regsVal_congr fun r hr =>
      RegUpd.gpr_write_of_ne _ _ _ (by revert r; decide)
    have hc : ((0 : BitVec 64) + 0 + BitVec.ofNat 64 s₂.c.toNat).toNat = s₂.c.toNat := by
      cases s₂.c <;> rfl
    rw [hlow, ite_true]
    dsimp only [Size.bits]
    rw [hc]
    have ev := Word64.addCarry_value (s.gpr .x8) (s.gpr .x14) false
    rw [← v₁, ← c₁] at ev
    rw [gt, gh, show 64 * lowRegs.tail.length = 320 from rfl] at e₂
    simp only [regsVal, g8]
    simp only [Bool.toNat_false] at ev
    omega
  · simp only [List.mem_cons, not_or] at hr
    rw [RegUpd.gpr_write_of_ne _ _ _ hr.1, k₂.gpr _ hr.2.2, k₁.gpr _ (by simpa using hr.2.1)]

end VG.Proof.Mont.AArch64.P384Mul
