module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.LazyP521
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnX
public import VerifiedGarbage.Proof.Mont.X86_64.Sub256
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# P-521 on x86-64 with BMI2 and ADX: the lazy operations

The carry chains of `Impl/Weierstrass/X86_64/LazyP521.lean` on the numbers in
memory.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.LazyP521

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Impl.Weierstrass.X86_64.LazyP521 VG.Impl.Weierstrass.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono add_carry adc_carry)

/-! ## The registers -/

theorem fresh : FreshX regs := xWin_fresh 9

theorem regs_sub : ∀ r ∈ regs, r ∈ xRegs := xWin_sub 9

theorem regs_len : regs.length = 9 := rfl

theorem rdi_not_regs : Reg.rdi ∉ regs := by decide

/-- The registers the operations write. -/
abbrev opRegs : List Reg := .rax :: .rcx :: .rdx :: xRegs

theorem regs_opRegs : ∀ r ∈ regs, r ∈ opRegs := by decide

/-- The number in the registers by its low, middle and top words. -/
theorem regsVal_split (s : State) : regsVal s regs =
    (s.gpr lowR).toNat + 2 ^ 64 * (hval (xg s) 10 7 + (2 ^ 64) ^ 7 * (s.gpr topR).toNat) := by
  rw [regsVal_xWin]
  have h : hval (xg s) 9 9 = xg s 9 + 2 ^ 64 * (hval (xg s) 10 7 + (2 ^ 64) ^ 7 * xg s 17) := by
    rw [← hval_succ_last]; rfl
  rw [h]; rfl

theorem mid_lt (s : State) : hval (xg s) 10 7 < (2 ^ 64) ^ 7 := hval_lt fun _ _ _ => (s.gpr _).isLt

theorem mid_congr {s s' : State} (h : ∀ c, 10 ≤ c → c < 17 → s'.gpr (xAcc c) = s.gpr (xAcc c)) :
    hval (xg s') 10 7 = hval (xg s) 10 7 :=
  hval_congr fun c h1 h2 => by simp only [xg]; rw [h c h1 (by omega_using [h2])]

theorem mid_ne_top {c : Nat} (h1 : 10 ≤ c) (h2 : c < 17) : xAcc c ≠ topR := xAcc_ne_of h2 (by omega_using [h1])
theorem mid_ne_low {c : Nat} (h1 : 10 ≤ c) (h2 : c < 17) : xAcc c ≠ lowR :=
  (xAcc_ne_of (show 9 < c by omega_using [h1]) (by omega_using [h2])).symm
theorem mid_ne_rax (c : Nat) : xAcc c ≠ .rax := (xAcc_ne c).1

/-! ## The chains -/

/-- `nots`, along registers. -/
theorem notsAux_ok : ∀ (ts : List Reg) (s : State), ts.Nodup →
    WP isa (.block (ts.map fun t => Instr.alu .xor t (.imm (-1)))) s fun s' =>
      regsVal s' ts + regsVal s ts + 1 = 2 ^ (64 * ts.length) ∧ Keeps ts s s'
  | [], s, _ => WP.block_nil ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, hn => by
    rw [List.map_cons, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.alu .xor t (.imm (-1))]) s fun s₁ =>
        (s₁.gpr t).toNat + (s.gpr t).toNat + 1 = 2 ^ 64 ∧ Keeps [t] s s₁ by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
        RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
      refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
      · rw [show ((-1 : BitVec 32).signExtend 64) = BitVec.allOnes 64 by decide, BitVec.xor_allOnes,
          BitVec.toNat_not]
        have := (s.gpr t).isLt
        omega_using [this]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false])
      fun s₁ ⟨e₁, k₁⟩ => ?_
    obtain htn := (List.nodup_cons.mp hn).1
    refine WP.mono (notsAux_ok ts s₁ (List.nodup_cons.mp hn).2) fun s₂ ⟨e₂, k₂⟩ =>
      ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    obtain hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => htn (h ▸ hq))
    rw [hR] at e₂
    simp only [regsVal, List.length_cons, pow64_succ, k₂.1 t htn]
    omega_using [e₁, e₂]

theorem nots_ok (s : State) : WP isa (.block nots) s fun s' =>
    regsVal s' regs + regsVal s regs + 1 = (2 ^ 64) ^ 9 ∧ Keeps regs s s' :=
  WP.mono (notsAux_ok regs s fresh.1) fun _ ⟨e, k⟩ =>
    ⟨by rw [Nat.pow_mul, show regs.length = 9 from rfl] at e; exact e, k⟩

/-- `chainAdd_ok` for `FreshX` registers. -/
theorem chainAddX_ok {s : State} {base : Addr} {size c₀ : Nat} (hs : ScrC s base size c₀) {t : Reg}
    {ts : List Reg} {b : Nat} (hb : b + 8 * (t :: ts).length ≤ size) (hf : FreshX (t :: ts)) :
    WP isa (.block (chainC c₀ .add .adc (t :: ts) b)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      regsVal s' (t :: ts) + 2 ^ (64 * (t :: ts).length) * c'.toNat =
        regsVal s (t :: ts) + wordsVal s.mem base b (t :: ts).length ∧ Keeps (t :: ts) s s' := by
  simp only [List.length_cons] at hb ⊢
  rw [chainC, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.alu .add t (.mem (rc c₀ b))]) s (fun s₁ =>
      (s₁.gpr t).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ (s.gpr t).toNat + (word s.mem base b).toNat)).toNat =
        (s.gpr t).toNat + (word s.mem base b).toNat ∧
      s₁.cf = some (decide (2 ^ 64 ≤ (s.gpr t).toNat + (word s.mem base b).toNat)) ∧
      Keeps [t] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc_rc hs (d := b) (by omega_arith), Option.bind_some, RegUpd.gpr_setReg,
      RegUpd.cf_setReg, RegUpd.cf_arithFlags, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨add_carry _ _, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.2.2.2.2 h.symm)
  refine WP.mono (chainAdcX_ok ts hs₁ c₁ (b := b + 8) (by omega_arith) hf.tail) fun s₂ ⟨c', c₂, e₂, k₂⟩ => ?_
  have ht : s₂.gpr t = s₁.gpr t := k₂.1 t hf.head.1
  have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.1 (h ▸ hq))
  rw [hR, k₁.2.1] at e₂
  refine ⟨c', c₂, ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  simp only [regsVal, wordsVal, pow64_succ, ht]
  rw [Nat.mul_assoc]
  omega_arith

/-- `[b]` added to the registers. -/
theorem chain_ok {s : State} {base : Addr} {size : Nat} (hs : ScrC s base size 0) {b : Nat}
    (hb : b + 72 ≤ size) :
    WP isa (.block (chainC 0 .add .adc regs b)) s fun s' => ∃ c : Nat, c ≤ 1 ∧
      regsVal s' regs + (2 ^ 64) ^ 9 * c = regsVal s regs + wordsVal s.mem base b 9 ∧ Keeps regs s s' :=
  WP.mono (chainAddX_ok (t := xAcc 9) (ts := xHi) hs hb fresh) fun _ ⟨c, _, e, k⟩ =>
    ⟨c.toNat, Bool.toNat_le c, by rw [Nat.pow_mul, show (xAcc 9 :: xHi).length = 9 from rfl] at e; exact e, k⟩

/-- `[a]` into the registers. -/
theorem load_ok {s : State} {base : Addr} {size : Nat} (hs : ScrC s base size 0) {a : Nat} (ha : a + 72 ≤ size) :
    WP isa (.block (loadsC 0 regs a)) s fun s' =>
      regsVal s' regs = wordsVal s.mem base a 9 ∧ Keeps regs s s' :=
  loadsX_ok regs hs ha fresh

/-- The registers doubled. -/
theorem dbl_ok (s : State) : WP isa (.block (dblChain .add regs)) s fun s' => ∃ c : Nat, c ≤ 1 ∧
    regsVal s' regs + (2 ^ 64) ^ 9 * c = 2 * regsVal s regs ∧ Keeps regs s s' :=
  WP.mono (dblChainX_ok (t := xAcc 9) (ts := xHi) fresh) fun _ ⟨c, e, _, k⟩ =>
    ⟨c.toNat, Bool.toNat_le c, by rw [Nat.pow_mul, show (xAcc 9 :: xHi).length = 9 from rfl] at e; exact e, k⟩

/-- The registers stored at `[o]`. -/
theorem store_ok {s : State} {base : Addr} {size : Nat} (hs : ScrC s base size 0) {o : Nat} (ho : o + 72 ≤ size)
    {ts : List Reg} (hl : ts.length = 9) (hn : ts.Nodup) :
    WP isa (.block (storesC 0 ts o)) s fun s' =>
      wordsVal s'.mem base o 9 = regsVal s ts ∧ KeepRegs [] s s' ∧ Outside base o 72 s.mem s'.mem := by
  have h := storesC_ok ts hs (o := o) (by rw [hl]; exact ho) hn
  rw [hl] at h
  exact h

/-- `k` added to the top word. -/
theorem addTop_ok (s : State) {k : Nat} {v : BitVec 32} (hv : (v.signExtend 64).toNat = k) :
    WP isa (.block [.alu .add topR (.imm v)]) s fun s' => ∃ c : Nat, c ≤ 1 ∧
      regsVal s' regs + (2 ^ 64) ^ 9 * c = regsVal s regs + k * (2 ^ 64) ^ 8 ∧ Keeps regs s s' := by
  have h : WP isa (.block [.alu .add topR (.imm v)]) s fun s' => ∃ c : Bool,
      (s'.gpr topR).toNat + 2 ^ 64 * c.toNat = (s.gpr topR).toNat + k ∧ Keeps [topR] s s' := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
      RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
    refine ⟨_, by rw [← hv]; exact add_carry _ _, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  refine WP.mono h fun s' ⟨c, e, kk⟩ => ⟨c.toNat, Bool.toNat_le c, ?_, kk.mono (by decide)⟩
  have hl : s'.gpr lowR = s.gpr lowR := kk.1 _ (by decide)
  have hm : hval (xg s') 10 7 = hval (xg s) 10 7 := mid_congr fun c h1 h2 =>
    kk.1 _ (by simpa using mid_ne_top h1 h2)
  rw [regsVal_split, regsVal_split s, hl, hm]
  generalize (2 ^ 64) ^ 7 * 1 = z
  omega_using [e]

/-- `adcs`, along registers. -/
theorem adcs_ok : ∀ (ts : List Reg) {s : State} {c : Bool}, ts.Nodup → s.cf = some c →
    WP isa (.block (adcs ts)) s fun s' => ∃ c' : Nat, c' ≤ 1 ∧
      regsVal s' ts + 2 ^ (64 * ts.length) * c' = regsVal s ts + c.toNat ∧ Keeps ts s s'
  | [], s, c, _, _ => WP.block_nil ⟨c.toNat, Bool.toNat_le c, by simp [regsVal], fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, c, hn, hc => by
    rw [adcs, List.map_cons, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.alu .adc t (.imm 0)]) s fun s₁ => ∃ c₁ : Bool, s₁.cf = some c₁ ∧
        (s₁.gpr t).toNat + 2 ^ 64 * c₁.toNat = (s.gpr t).toNat + c.toNat ∧ Keeps [t] s s₁ by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
        Option.map_some, hc, RegUpd.gpr_setReg_self, RegUpd.cf_setReg, RegUpd.cf_arithFlags, Option.some.injEq,
        exists_eq_left']
      refine ⟨by simpa using adc_carry (s.gpr t) ((0 : BitVec 32).signExtend 64) c, fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨c₁, cf₁, e₁, k₁⟩ => ?_
    obtain htn := (List.nodup_cons.mp hn).1
    refine WP.mono (adcs_ok ts (List.nodup_cons.mp hn).2 cf₁) fun s₂ ⟨c₂, hc₂, e₂, k₂⟩ =>
      ⟨c₂, hc₂, ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    obtain hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => htn (h ▸ hq))
    rw [hR] at e₂
    simp only [regsVal, List.length_cons, pow64_succ, k₂.1 t htn]
    rw [Nat.mul_assoc]
    omega_using [e₁, e₂]

/-! ## The fold -/

/-- `foldHi`: the top word's bits from 9 added to the low word, the rest
kept. -/
theorem foldHi_ok (s : State) : WP isa (.block foldHi) s fun s' => ∃ c : Bool, s'.cf = some c ∧
    (s'.gpr lowR).toNat + 2 ^ 64 * c.toNat = (s.gpr lowR).toNat + (s.gpr topR).toNat / 512 ∧
    (s'.gpr topR).toNat = (s.gpr topR).toNat % 512 ∧ hval (xg s') 10 7 = hval (xg s) 10 7 ∧
    Keeps (.rax :: regs) s s' := by
  rw [show foldHi = [.mov .rax (.reg topR), .shift .shr .rax 9] ++ ([.alu .and topR (.imm 511)] ++
    ([.alu .add lowR (.reg .rax)] : List Instr)) from rfl, WP.block_append_iff]
  refine WP.mono (top_ok s topR) fun s₁ ⟨e₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (and511_ok s₁ topR) fun s₂ ⟨e₂, k₂⟩ => ?_
  refine WP.mono (show WP isa (.block [.alu .add lowR (.reg .rax)]) s₂ fun s₃ => ∃ c : Bool, s₃.cf = some c ∧
      (s₃.gpr lowR).toNat + 2 ^ 64 * c.toNat = (s₂.gpr lowR).toNat + (s₂.gpr .rax).toNat ∧ Keeps [lowR] s₂ s₃ by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
      RegUpd.gpr_setReg_self, RegUpd.cf_setReg, RegUpd.cf_arithFlags, Option.some.injEq, exists_eq_left']
    refine ⟨add_carry _ _, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₃ ⟨c, cf, e₃, k₃⟩ => ?_
  refine ⟨c, cf, ?_, ?_, ?_, ((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans (k₃.mono (by decide))⟩
  · rw [e₃, k₂.1 lowR (by decide), k₁.1 lowR (by decide), k₂.1 .rax (by decide), e₁]
  · rw [k₃.1 topR (by decide), e₂, k₁.1 topR (by decide)]
  · refine mid_congr fun c h1 h2 => ?_
    rw [k₃.1 _ (by simpa using mid_ne_low h1 h2), k₂.1 _ (by simpa using mid_ne_top h1 h2),
      k₁.1 _ (by simpa using mid_ne_rax c)]

/-- The arithmetic of `fold`. -/
theorem fold_arith {m x L t x1 c1 c2 H1 x2 c3 M1 t1 : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (hx : x < 2 ^ 64) (hL : L < (2 ^ 64) ^ 7) (ht : t < 2048) (hc1 : c1 ≤ 1) (hc3 : c3 ≤ 1) (hx1 : x1 < 2 ^ 64)
    (hM1 : M1 < (2 ^ 64) ^ 7)
    (e1 : x1 + 2 ^ 64 * c1 = x + t / 512)
    (e2 : H1 + (2 ^ 64) ^ 8 * c2 = L + (2 ^ 64) ^ 7 * (t % 512) + c1) (eH : H1 = M1 + (2 ^ 64) ^ 7 * t1)
    (e3 : x2 + 2 ^ 64 * c3 = x1 + t1 / 512) :
    ∃ q, x2 + 2 ^ 64 * (M1 + (2 ^ 64) ^ 7 * (t1 % 512)) + q * m = x + 2 ^ 64 * (L + (2 ^ 64) ^ 7 * t) ∧
      x2 + 2 ^ 64 * (M1 + (2 ^ 64) ^ 7 * (t1 % 512)) ≤ m := by
  obtain hm' : m = 512 * (2 ^ 64) ^ 8 - 1 := by omega_using [hm]
  subst hm'
  have hh : t / 512 ≤ 3 := by omega_using [ht]
  have hr : t % 512 < 512 := Nat.mod_lt _ (by decide)
  have ed : t = 512 * (t / 512) + t % 512 := (Nat.div_add_mod t 512).symm
  generalize t / 512 = h at *
  generalize t % 512 = r at *
  subst ed
  have hc2 : c2 = 0 := by omega_arith
  subst hc2
  have hV : x1 + 2 ^ 64 * H1 = x + 2 ^ 64 * (L + (2 ^ 64) ^ 7 * r) + h := by omega_arith
  have ht1 : t1 ≤ 512 := by omega_arith
  rcases Nat.lt_or_ge t1 512 with hlt | hge
  · rw [Nat.div_eq_of_lt hlt] at e3
    rw [Nat.mod_eq_of_lt hlt]
    refine ⟨h, ?_, ?_⟩ <;> omega_arith
  · obtain rfl : t1 = 512 := by omega_using [ht1, hge]
    have hM0 : M1 = 0 := by omega_arith
    have hx13 : x1 < 3 := by omega_arith
    simp only [Nat.reduceMod, Nat.reduceDiv] at e3 ⊢
    refine ⟨h + 1, ?_, ?_⟩ <;> omega_arith

theorem hi_val (s : State) : regsVal s ((List.range 8).map fun k => xAcc (10 + k)) =
    hval (xg s) 10 7 + (2 ^ 64) ^ 7 * (s.gpr topR).toNat := by
  rw [show regsVal s ((List.range 8).map fun k => xAcc (10 + k)) = hval (xg s) 10 8 from regsVal_xAccs s 8 10,
    hval_succ_last]; rfl

/-- `fold`: a number below `4p` becomes one at most `p`, congruent to it. -/
theorem fold_ok {m : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (s : State) (hV : regsVal s regs < 2048 * (2 ^ 64) ^ 8) :
    WP isa (.block fold) s fun s' => (∃ q, regsVal s' regs + q * m = regsVal s regs) ∧ regsVal s' regs ≤ m ∧
      Keeps (.rax :: regs) s s' := by
  have ht : (s.gpr topR).toNat < 2048 := by
    rw [regsVal_split] at hV; omega_arith
  rw [fold, List.append_assoc, WP.block_append_iff]
  refine WP.mono (foldHi_ok s) fun s₁ ⟨c₁, cf₁, e₁, t₁, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adcs_ok _ (by decide) cf₁) fun s₂ ⟨c₂, _, e₂, k₂⟩ => ?_
  refine WP.mono (foldHi_ok s₂) fun s₃ ⟨c₃, _, e₃, t₃, m₃, k₃⟩ => ?_
  rw [hi_val, hi_val, m₁, t₁, Nat.pow_mul, List.length_map, List.length_range] at e₂
  have hl₂ : s₂.gpr lowR = s₁.gpr lowR := k₂.1 lowR (by decide)
  obtain ⟨q, hq, hle⟩ := fold_arith hm (s.gpr lowR).isLt (mid_lt s) ht (Bool.toNat_le c₁) (Bool.toNat_le c₃)
    (s₁.gpr lowR).isLt (mid_lt s₂) e₁ e₂ rfl (by rw [← hl₂]; exact e₃)
  refine ⟨⟨q, ?_⟩, ?_, (k₁.trans (k₂.mono (by decide))).trans k₃⟩
  · rw [regsVal_split s₃, regsVal_split s, m₃, t₃]; exact hq
  · rw [regsVal_split s₃, m₃, t₃]; exact hle

/-! ## The operations between products -/

/-- What an operation between products keeps. -/
def LKeep (base : Addr) (o : Nat) (s s' : State) : Prop :=
  KeepRegs opRegs s s' ∧ Outside base o 72 s.mem s'.mem

/-- A store after `c`, code that keeps the memory and all but `opRegs`. -/
theorem storeAfter_ok {c : List Instr} {base : Addr} {size o : Nat} {s : State} (hs : ScrC s base size 0)
    (ho : o + 72 ≤ size) {ts : List Reg} (hl : ts.length = 9) (hn : ts.Nodup) {Q : Nat → Prop}
    (h : WP isa (.block c) s fun s' => Q (regsVal s' ts) ∧ Keeps opRegs s s') :
    WP isa (.block (c ++ storesC 0 ts o)) s fun s' => Q (wordsVal s'.mem base o 9) ∧ LKeep base o s s' := by
  rw [WP.block_append_iff]
  refine WP.mono h fun s₁ ⟨q, k₁⟩ => ?_
  refine WP.mono (store_ok (hs.of_keeps k₁ (by decide)) ho hl hn) fun s₂ ⟨e₂, k₂, O₂⟩ => ⟨by rw [e₂]; exact q, ?_, ?_⟩
  · exact ⟨fun r hr => (k₂.gpr r List.not_mem_nil).trans (k₁.1 r hr), k₂.rd.trans k₁.2.2.1, k₂.wr.trans k₁.2.2.2⟩
  · rw [← k₁.2.1]; exact O₂

theorem wv_lt (m : Mem) (base : Addr) (a : Nat) : wordsVal m base a 9 < (2 ^ 64) ^ 9 := by
  rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ 9

section
variable {base : Addr} {size o a b m : Nat} {s : State}

theorem scr_keeps {s' : State} (hs : ScrC s base size 0) (k : Keeps regs s s') : ScrC s' base size 0 :=
  hs.of_keeps k rdi_not_regs

theorem add_ok (hs : ScrC s base size 0) (ho : o + 72 ≤ size) (ha : a + 72 ≤ size) (hb : b + 72 ≤ size)
    (hV : wordsVal s.mem base a 9 + wordsVal s.mem base b 9 < (2 ^ 64) ^ 9) :
    WP isa (.block (loadsC 0 regs a ++ chainC 0 .add .adc regs b ++ storesC 0 regs o)) s fun s' =>
      wordsVal s'.mem base o 9 = wordsVal s.mem base a 9 + wordsVal s.mem base b 9 ∧ LKeep base o s s' := by
  refine storeAfter_ok (ts := regs) (c := loadsC 0 regs a ++ chainC 0 .add .adc regs b)
    (Q := fun v => v = wordsVal s.mem base a 9 + wordsVal s.mem base b 9) hs ho regs_len fresh.1 ?_
  rw [WP.block_append_iff]
  refine WP.mono (load_ok hs ha) fun s₁ ⟨e₁, k₁⟩ => ?_
  refine WP.mono (chain_ok (scr_keeps hs k₁) hb) fun s₂ ⟨c, _, e₂, k₂⟩ =>
    ⟨?_, (k₁.mono regs_opRegs).trans (k₂.mono regs_opRegs)⟩
  rw [e₁, k₁.2.1] at e₂
  omega_arith

/-- `p - [b]` and `[a]` in the registers, but for the top word's 512. -/
theorem subs_ok (hs : ScrC s base size 0) (ha : a + 72 ≤ size) (hb : b + 72 ≤ size) :
    WP isa (.block (subs a b)) s fun s' => ∃ c, c ≤ 1 ∧
      regsVal s' regs + (2 ^ 64) ^ 9 * c + wordsVal s.mem base b 9 + 1 = (2 ^ 64) ^ 9 + wordsVal s.mem base a 9 ∧
      Keeps regs s s' := by
  rw [subs, List.append_assoc, WP.block_append_iff]
  refine WP.mono (load_ok hs hb) fun s₁ ⟨e₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (nots_ok s₁) fun s₂ ⟨e₂, k₂⟩ => ?_
  refine WP.mono (chain_ok (scr_keeps (scr_keeps hs k₁) k₂) ha) fun s₃ ⟨c, hc, e₃, k₃⟩ =>
    ⟨c, hc, ?_, (k₁.trans k₂).trans k₃⟩
  rw [k₂.2.1, k₁.2.1] at e₃
  omega_arith

theorem top512 (s : State) : WP isa (.block [.alu .add topR (.imm 512)]) s fun s' => ∃ c : Nat, c ≤ 1 ∧
    regsVal s' regs + (2 ^ 64) ^ 9 * c = regsVal s regs + 512 * (2 ^ 64) ^ 8 ∧ Keeps regs s s' :=
  addTop_ok s (by decide)

theorem top1024 (s : State) : WP isa (.block [.alu .add topR (.imm 1024)]) s fun s' => ∃ c : Nat, c ≤ 1 ∧
    regsVal s' regs + (2 ^ 64) ^ 9 * c = regsVal s regs + 1024 * (2 ^ 64) ^ 8 ∧ Keeps regs s s' :=
  addTop_ok s (by decide)

theorem regs9_lt (s : State) : regsVal s regs < (2 ^ 64) ^ 9 := by
  have := regsVal_lt s regs
  rwa [Nat.pow_mul, show regs.length = 9 from rfl] at this

/-- `[a] + (p - [b])` in the registers. -/
theorem subTop_ok (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hs : ScrC s base size 0) (ha : a + 72 ≤ size)
    (hb : b + 72 ≤ size) (hB : wordsVal s.mem base b 9 ≤ m) (hA : wordsVal s.mem base a 9 ≤ 4 * m) :
    WP isa (.block (subs a b ++ ([.alu .add topR (.imm 512)] : List Instr))) s fun s' =>
      regsVal s' regs = wordsVal s.mem base a 9 + (m - wordsVal s.mem base b 9) ∧ Keeps regs s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (subs_ok hs ha hb) fun s₁ ⟨c₁, h₁, e₁, k₁⟩ => ?_
  refine WP.mono (top512 s₁) fun s₂ ⟨c₂, h₂, e₂, k₂⟩ => ⟨?_, k₁.trans k₂⟩
  have l₂ := regs9_lt s₂
  have l₁ := regs9_lt s₁
  omega_arith

theorem sub_ok (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hs : ScrC s base size 0) (ho : o + 72 ≤ size)
    (ha : a + 72 ≤ size) (hb : b + 72 ≤ size) (hB : wordsVal s.mem base b 9 ≤ m)
    (hA : wordsVal s.mem base a 9 ≤ 4 * m) :
    WP isa (.block (subs a b ++ ([.alu .add topR (.imm 512)] : List Instr) ++ storesC 0 regs o)) s fun s' =>
      wordsVal s'.mem base o 9 = wordsVal s.mem base a 9 + (m - wordsVal s.mem base b 9) ∧ LKeep base o s s' :=
  storeAfter_ok (ts := regs) (c := subs a b ++ ([.alu .add topR (.imm 512)] : List Instr))
    (Q := fun v => v = wordsVal s.mem base a 9 + (m - wordsVal s.mem base b 9)) hs ho regs_len fresh.1
    (WP.mono (subTop_ok hm hs ha hb hB hA) fun _ ⟨e, k⟩ => ⟨e, k.mono regs_opRegs⟩)

theorem subF_ok (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hs : ScrC s base size 0) (ho : o + 72 ≤ size)
    (ha : a + 72 ≤ size) (hb : b + 72 ≤ size) (hB : wordsVal s.mem base b 9 ≤ m)
    (hA : wordsVal s.mem base a 9 ≤ m) :
    WP isa (.block (subs a b ++ ([.alu .add topR (.imm 512)] : List Instr) ++ fold ++ storesC 0 regs o)) s fun s' =>
      ((∃ q, wordsVal s'.mem base o 9 + q * m = wordsVal s.mem base a 9 + (m - wordsVal s.mem base b 9)) ∧
        wordsVal s'.mem base o 9 ≤ m) ∧ LKeep base o s s' := by
  refine storeAfter_ok (ts := regs) (c := subs a b ++ ([.alu .add topR (.imm 512)] : List Instr) ++ fold)
    (Q := fun v => (∃ q, v + q * m = wordsVal s.mem base a 9 + (m - wordsVal s.mem base b 9)) ∧ v ≤ m) hs ho regs_len fresh.1 ?_
  rw [WP.block_append_iff]
  refine WP.mono (subTop_ok hm hs ha hb hB (by omega_using [hA])) fun s₁ ⟨e₁, k₁⟩ => ?_
  refine WP.mono (fold_ok hm s₁ (by rw [e₁]; omega_arith)) fun s₂ ⟨q, l, k₂⟩ =>
    ⟨⟨by rw [← e₁]; exact q, l⟩, (k₁.mono regs_opRegs).trans (k₂.mono (by decide))⟩

theorem sub2_ok (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hs : ScrC s base size 0) (ho : o + 72 ≤ size)
    (ha : a + 72 ≤ size) (hb : b + 72 ≤ size) (hB : wordsVal s.mem base b 9 ≤ m)
    (hA : wordsVal s.mem base a 9 ≤ m) :
    WP isa (.block (loadsC 0 regs b ++ nots ++ dblChain .add regs ++ chainC 0 .add .adc regs a ++
        ([.alu .add topR (.imm 1024)] : List Instr) ++ fold ++ storesC 0 regs o)) s fun s' =>
      ((∃ q, wordsVal s'.mem base o 9 + q * m = wordsVal s.mem base a 9 + 2 * (m - wordsVal s.mem base b 9)) ∧
        wordsVal s'.mem base o 9 ≤ m) ∧ LKeep base o s s' := by
  refine storeAfter_ok (ts := regs) (c := loadsC 0 regs b ++ nots ++ dblChain .add regs ++ chainC 0 .add .adc regs a ++
      ([.alu .add topR (.imm 1024)] : List Instr) ++ fold)
    (Q := fun v => (∃ q, v + q * m = wordsVal s.mem base a 9 + 2 * (m - wordsVal s.mem base b 9)) ∧ v ≤ m) hs ho regs_len fresh.1 ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (load_ok hs hb) fun s₁ ⟨e₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (nots_ok s₁) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dbl_ok s₂) fun s₃ ⟨c₃, h₃, e₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  have k₁₃ := (k₁.trans k₂).trans k₃
  refine WP.mono (chain_ok (scr_keeps hs k₁₃) ha) fun s₄ ⟨c₄, h₄, e₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (top1024 s₄) fun s₅ ⟨c₅, h₅, e₅, k₅⟩ => ?_
  rw [k₁₃.2.1] at e₄
  have l₅ := regs9_lt s₅
  have l₄ := regs9_lt s₄
  have l₃ := regs9_lt s₃
  obtain e : regsVal s₅ regs = wordsVal s.mem base a 9 + 2 * (m - wordsVal s.mem base b 9) := by omega_arith
  refine WP.mono (fold_ok hm s₅ (by rw [e]; omega_arith)) fun s₆ ⟨q, l, k₆⟩ =>
    ⟨⟨by rw [← e]; exact q, l⟩, (((k₁₃.trans k₄).trans k₅).mono regs_opRegs).trans (k₆.mono (by decide))⟩

theorem tri_ok (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hs : ScrC s base size 0) (ho : o + 72 ≤ size)
    (ha : a + 72 ≤ size) (hA : wordsVal s.mem base a 9 ≤ m) :
    WP isa (.block (loadsC 0 regs a ++ dblChain .add regs ++ chainC 0 .add .adc regs a ++ storesC 0 regs o)) s fun s' =>
      wordsVal s'.mem base o 9 = 3 * wordsVal s.mem base a 9 ∧ LKeep base o s s' := by
  refine storeAfter_ok (ts := regs) (c := loadsC 0 regs a ++ dblChain .add regs ++ chainC 0 .add .adc regs a)
    (Q := fun v => v = 3 * wordsVal s.mem base a 9) hs ho regs_len fresh.1 ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (load_ok hs ha) fun s₁ ⟨e₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dbl_ok s₁) fun s₂ ⟨c₂, h₂, e₂, k₂⟩ => ?_
  refine WP.mono (chain_ok (scr_keeps hs (k₁.trans k₂)) ha) fun s₃ ⟨c₃, h₃, e₃, k₃⟩ =>
    ⟨?_, ((k₁.trans k₂).trans k₃).mono regs_opRegs⟩
  rw [k₂.2.1, k₁.2.1] at e₃
  omega_arith

end

/-! ## Halving -/

theorem shld63_ok (s : State) (d r : Reg) :
    WP isa (.block [.shld d r 63]) s fun s' =>
      (s'.gpr d).toNat = (s.gpr d).toNat % 2 * 2 ^ 63 + (s.gpr r).toNat / 2 ∧ Keeps [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execShld, show 1 ≤ 63 ∧ 63 ≤ 63 by decide, and_self,
    ite_true, RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun q hq => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
    have h1 := (s.gpr r).isLt
    rw [show (s.gpr d).toNat * 2 ^ 63 % 2 ^ 64 = 2 ^ 63 * ((s.gpr d).toNat % 2) by omega_arith,
      ← Nat.two_pow_add_eq_or_of_lt (by omega_arith)]
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hq, ite_false]

/-- The bits the rotation moves into the top word. -/
theorem rotTop_ok (s : State) :
    WP isa (.block [.mov .rax (.reg lowR), .alu .and .rax (.imm 1), .shift .shl .rax 8, .mov .rcx (.reg topR),
      .shift .shr .rcx 1, .alu .add .rcx (.reg .rax)]) s fun s' =>
      (s'.gpr .rcx).toNat = (s.gpr topR).toNat / 2 + (s.gpr lowR).toNat % 2 * 256 ∧ Keeps [.rax, .rcx] s s' := by
  apply WP.of_runBlock
  have h1 : (lowR = Reg.rax) = False := by decide
  have h2 : (topR = Reg.rax) = False := by decide
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift, readSrc, Option.bind_some,
    Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, h2, reduceCtorEq, ite_true, ite_false,
    show 1 ≤ 8 ∧ 8 ≤ 63 by decide, show 1 ≤ 1 ∧ 1 ≤ 63 by decide, and_self, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun q hq => ?_, rfl, rfl, rfl⟩
  · have hl := (s.gpr lowR).isLt
    have ht := (s.gpr topR).isLt
    rw [show ((1 : BitVec 32).signExtend 64) = BitVec.ofNat 64 (2 ^ 1 - 1) by decide, BitVec.toNat_add,
      BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 2 ^ 1 - 1 < 2 ^ 64 by decide), Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hq.1, hq.2, ite_false]

/-- The arithmetic of the rotation: `x i` the words, `y i` the rotated ones. -/
theorem rot_arith {m x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    {V W : Nat}
    (hV : V = x0 + 2 ^ 64 * (x1 + 2 ^ 64 * (x2 + 2 ^ 64 * (x3 + 2 ^ 64 * (x4 + 2 ^ 64 * (x5 + 2 ^ 64 * (x6 +
      2 ^ 64 * (x7 + 2 ^ 64 * x8))))))))
    (hW : W = (x1 % 2 * 2 ^ 63 + x0 / 2) + 2 ^ 64 * ((x2 % 2 * 2 ^ 63 + x1 / 2) + 2 ^ 64 * ((x3 % 2 * 2 ^ 63 + x2 / 2) +
      2 ^ 64 * ((x4 % 2 * 2 ^ 63 + x3 / 2) + 2 ^ 64 * ((x5 % 2 * 2 ^ 63 + x4 / 2) + 2 ^ 64 * ((x6 % 2 * 2 ^ 63 + x5 / 2) +
      2 ^ 64 * ((x7 % 2 * 2 ^ 63 + x6 / 2) + 2 ^ 64 * ((x8 % 2 * 2 ^ 63 + x7 / 2) + 2 ^ 64 * (x8 / 2 + x0 % 2 * 256))))))))) :
    2 * W = V + x0 % 2 * m := by
  obtain hm' : m = 512 * (2 ^ 64) ^ 8 - 1 := by omega_using [hm]
  subst hm'
  omega_arith

theorem regs_words (s : State) : regsVal s regs = (s.gpr (xAcc 9)).toNat + 2 ^ 64 * ((s.gpr (xAcc 10)).toNat + 2 ^ 64 * ((s.gpr (xAcc 11)).toNat + 2 ^ 64 * ((s.gpr (xAcc 12)).toNat + 2 ^ 64 * ((s.gpr (xAcc 13)).toNat + 2 ^ 64 * ((s.gpr (xAcc 14)).toNat + 2 ^ 64 * ((s.gpr (xAcc 15)).toNat + 2 ^ 64 * ((s.gpr (xAcc 16)).toNat + 2 ^ 64 * ((s.gpr (xAcc 17)).toNat + 2 ^ 64 * 0)))))))) := rfl

theorem half_words (s : State) : regsVal s halfRegs = (s.gpr (xAcc 10)).toNat + 2 ^ 64 * ((s.gpr (xAcc 11)).toNat + 2 ^ 64 * ((s.gpr (xAcc 12)).toNat + 2 ^ 64 * ((s.gpr (xAcc 13)).toNat + 2 ^ 64 * ((s.gpr (xAcc 14)).toNat + 2 ^ 64 * ((s.gpr (xAcc 15)).toNat + 2 ^ 64 * ((s.gpr (xAcc 16)).toNat + 2 ^ 64 * ((s.gpr (xAcc 17)).toNat + 2 ^ 64 * ((s.gpr .rcx).toNat + 2 ^ 64 * 0)))))))) := rfl

theorem rot_ok {m : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (s : State) :
    WP isa (.block rot) s fun s' =>
      2 * regsVal s' halfRegs = regsVal s regs + (s.gpr lowR).toNat % 2 * m ∧ Keeps opRegs s s' := by
  rw [show rot = [.mov .rax (.reg lowR), .alu .and .rax (.imm 1), .shift .shl .rax 8, .mov .rcx (.reg topR),
      .shift .shr .rcx 1, .alu .add .rcx (.reg .rax)] ++ ([.shld (xAcc 17) (xAcc 16) 63, .shld (xAcc 16) (xAcc 15) 63, .shld (xAcc 15) (xAcc 14) 63, .shld (xAcc 14) (xAcc 13) 63, .shld (xAcc 13) (xAcc 12) 63, .shld (xAcc 12) (xAcc 11) 63, .shld (xAcc 11) (xAcc 10) 63, .shld (xAcc 10) (xAcc 9) 63] : List Instr) from rfl,
    WP.block_append_iff]
  refine WP.mono (rotTop_ok s) fun t0 ⟨e0, k0⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (shld63_ok t0 (xAcc 17) (xAcc 16)) fun t1 ⟨e1, k1⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (shld63_ok t1 (xAcc 16) (xAcc 15)) fun t2 ⟨e2, k2⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (shld63_ok t2 (xAcc 15) (xAcc 14)) fun t3 ⟨e3, k3⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (shld63_ok t3 (xAcc 14) (xAcc 13)) fun t4 ⟨e4, k4⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (shld63_ok t4 (xAcc 13) (xAcc 12)) fun t5 ⟨e5, k5⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (shld63_ok t5 (xAcc 12) (xAcc 11)) fun t6 ⟨e6, k6⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (shld63_ok t6 (xAcc 11) (xAcc 10)) fun t7 ⟨e7, k7⟩ => ?_
  refine WP.mono (shld63_ok t7 (xAcc 10) (xAcc 9)) fun t8 ⟨e8, k8⟩ => ?_
  have f17 : (t8.gpr (xAcc 17)).toNat = (s.gpr (xAcc 17)).toNat % 2 * 2 ^ 63 + (s.gpr (xAcc 16)).toNat / 2 := by
    rw [k8.1 (xAcc 17) (by decide), k7.1 (xAcc 17) (by decide), k6.1 (xAcc 17) (by decide), k5.1 (xAcc 17) (by decide), k4.1 (xAcc 17) (by decide), k3.1 (xAcc 17) (by decide), k2.1 (xAcc 17) (by decide), e1, k0.1 (xAcc 17) (by decide), k0.1 (xAcc 16) (by decide)]
  have f16 : (t8.gpr (xAcc 16)).toNat = (s.gpr (xAcc 16)).toNat % 2 * 2 ^ 63 + (s.gpr (xAcc 15)).toNat / 2 := by
    rw [k8.1 (xAcc 16) (by decide), k7.1 (xAcc 16) (by decide), k6.1 (xAcc 16) (by decide), k5.1 (xAcc 16) (by decide), k4.1 (xAcc 16) (by decide), k3.1 (xAcc 16) (by decide), e2, k1.1 (xAcc 16) (by decide), k0.1 (xAcc 16) (by decide), k1.1 (xAcc 15) (by decide), k0.1 (xAcc 15) (by decide)]
  have f15 : (t8.gpr (xAcc 15)).toNat = (s.gpr (xAcc 15)).toNat % 2 * 2 ^ 63 + (s.gpr (xAcc 14)).toNat / 2 := by
    rw [k8.1 (xAcc 15) (by decide), k7.1 (xAcc 15) (by decide), k6.1 (xAcc 15) (by decide), k5.1 (xAcc 15) (by decide), k4.1 (xAcc 15) (by decide), e3, k2.1 (xAcc 15) (by decide), k1.1 (xAcc 15) (by decide), k0.1 (xAcc 15) (by decide), k2.1 (xAcc 14) (by decide), k1.1 (xAcc 14) (by decide), k0.1 (xAcc 14) (by decide)]
  have f14 : (t8.gpr (xAcc 14)).toNat = (s.gpr (xAcc 14)).toNat % 2 * 2 ^ 63 + (s.gpr (xAcc 13)).toNat / 2 := by
    rw [k8.1 (xAcc 14) (by decide), k7.1 (xAcc 14) (by decide), k6.1 (xAcc 14) (by decide), k5.1 (xAcc 14) (by decide), e4, k3.1 (xAcc 14) (by decide), k2.1 (xAcc 14) (by decide), k1.1 (xAcc 14) (by decide), k0.1 (xAcc 14) (by decide), k3.1 (xAcc 13) (by decide), k2.1 (xAcc 13) (by decide), k1.1 (xAcc 13) (by decide), k0.1 (xAcc 13) (by decide)]
  have f13 : (t8.gpr (xAcc 13)).toNat = (s.gpr (xAcc 13)).toNat % 2 * 2 ^ 63 + (s.gpr (xAcc 12)).toNat / 2 := by
    rw [k8.1 (xAcc 13) (by decide), k7.1 (xAcc 13) (by decide), k6.1 (xAcc 13) (by decide), e5, k4.1 (xAcc 13) (by decide), k3.1 (xAcc 13) (by decide), k2.1 (xAcc 13) (by decide), k1.1 (xAcc 13) (by decide), k0.1 (xAcc 13) (by decide), k4.1 (xAcc 12) (by decide), k3.1 (xAcc 12) (by decide), k2.1 (xAcc 12) (by decide), k1.1 (xAcc 12) (by decide), k0.1 (xAcc 12) (by decide)]
  have f12 : (t8.gpr (xAcc 12)).toNat = (s.gpr (xAcc 12)).toNat % 2 * 2 ^ 63 + (s.gpr (xAcc 11)).toNat / 2 := by
    rw [k8.1 (xAcc 12) (by decide), k7.1 (xAcc 12) (by decide), e6, k5.1 (xAcc 12) (by decide), k4.1 (xAcc 12) (by decide), k3.1 (xAcc 12) (by decide), k2.1 (xAcc 12) (by decide), k1.1 (xAcc 12) (by decide), k0.1 (xAcc 12) (by decide), k5.1 (xAcc 11) (by decide), k4.1 (xAcc 11) (by decide), k3.1 (xAcc 11) (by decide), k2.1 (xAcc 11) (by decide), k1.1 (xAcc 11) (by decide), k0.1 (xAcc 11) (by decide)]
  have f11 : (t8.gpr (xAcc 11)).toNat = (s.gpr (xAcc 11)).toNat % 2 * 2 ^ 63 + (s.gpr (xAcc 10)).toNat / 2 := by
    rw [k8.1 (xAcc 11) (by decide), e7, k6.1 (xAcc 11) (by decide), k5.1 (xAcc 11) (by decide), k4.1 (xAcc 11) (by decide), k3.1 (xAcc 11) (by decide), k2.1 (xAcc 11) (by decide), k1.1 (xAcc 11) (by decide), k0.1 (xAcc 11) (by decide), k6.1 (xAcc 10) (by decide), k5.1 (xAcc 10) (by decide), k4.1 (xAcc 10) (by decide), k3.1 (xAcc 10) (by decide), k2.1 (xAcc 10) (by decide), k1.1 (xAcc 10) (by decide), k0.1 (xAcc 10) (by decide)]
  have f10 : (t8.gpr (xAcc 10)).toNat = (s.gpr (xAcc 10)).toNat % 2 * 2 ^ 63 + (s.gpr (xAcc 9)).toNat / 2 := by
    rw [e8, k7.1 (xAcc 10) (by decide), k6.1 (xAcc 10) (by decide), k5.1 (xAcc 10) (by decide), k4.1 (xAcc 10) (by decide), k3.1 (xAcc 10) (by decide), k2.1 (xAcc 10) (by decide), k1.1 (xAcc 10) (by decide), k0.1 (xAcc 10) (by decide), k7.1 (xAcc 9) (by decide), k6.1 (xAcc 9) (by decide), k5.1 (xAcc 9) (by decide), k4.1 (xAcc 9) (by decide), k3.1 (xAcc 9) (by decide), k2.1 (xAcc 9) (by decide), k1.1 (xAcc 9) (by decide), k0.1 (xAcc 9) (by decide)]
  have fc : (t8.gpr .rcx).toNat = (s.gpr (xAcc 17)).toNat / 2 + (s.gpr (xAcc 9)).toNat % 2 * 256 := by
    rw [k8.1 .rcx (by decide), k7.1 .rcx (by decide), k6.1 .rcx (by decide), k5.1 .rcx (by decide), k4.1 .rcx (by decide), k3.1 .rcx (by decide), k2.1 .rcx (by decide), k1.1 .rcx (by decide), e0]
  refine ⟨?_, ((((((((k0.mono (by decide)).trans (k1.mono (by decide))).trans (k2.mono (by decide))).trans (k3.mono (by decide))).trans (k4.mono (by decide))).trans (k5.mono (by decide))).trans (k6.mono (by decide))).trans (k7.mono (by decide))).trans (k8.mono (by decide))⟩
  rw [half_words, f17, f16, f15, f14, f13, f12, f11, f10, fc, regs_words]
  simp only [Nat.mul_zero, Nat.add_zero]
  exact rot_arith hm rfl rfl

theorem half_ok {base : Addr} {size o a m : Nat} {s : State} (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (hs : ScrC s base size 0) (ho : o + 72 ≤ size) (ha : a + 72 ≤ size) (hA : wordsVal s.mem base a 9 ≤ m) :
    WP isa (.block (loadsC 0 regs a ++ rot ++ storesC 0 halfRegs o)) s fun s' =>
      ((∃ q, 2 * wordsVal s'.mem base o 9 = wordsVal s.mem base a 9 + q * m) ∧ wordsVal s'.mem base o 9 ≤ m) ∧
      LKeep base o s s' := by
  have hl : halfRegs.length = 9 := rfl
  have hn : halfRegs.Nodup := by decide
  refine storeAfter_ok (ts := halfRegs) (c := loadsC 0 regs a ++ rot)
    (Q := fun v => (∃ q, 2 * v = wordsVal s.mem base a 9 + q * m) ∧ v ≤ m) hs ho hl hn ?_
  rw [WP.block_append_iff]
  refine WP.mono (load_ok hs ha) fun s₁ ⟨e₁, k₁⟩ => ?_
  refine WP.mono (rot_ok hm s₁) fun s₂ ⟨e₂, k₂⟩ => ⟨⟨⟨_, by rw [← e₁]; exact e₂⟩, ?_⟩, (k₁.mono regs_opRegs).trans k₂⟩
  have h2 : (s₁.gpr lowR).toNat % 2 * m ≤ 1 * m := Nat.mul_le_mul_right _ (by omega_using [])
  rw [e₁] at e₂
  omega_using [e₂, h2, hA]

/-! ## The products -/

/-- The pointer `r = rdi + a`. -/
theorem ptr_ok {s : State} {base : Addr} {size a : Nat} {r : Reg} (hs : Scr s base size) (ha : a < 2 ^ 31) (hr : r ≠ .rdi) :
    WP isa (.block (ptr r a)) s fun s' => s'.gpr r = off base a ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [ptr, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some, Option.map_some,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun q hq => ?_, rfl, rfl, rfl⟩
  · rw [hs.rdi, se_imm ha]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq, ite_false]

theorem mulFn_ok {s : State} {base : Addr} {Z a b m : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    (hsi : s.gpr .rsi = off base a) (hbx : s.gpr .rbx = off base b) (ha : a + 72 ≤ 3520) (hb : b + 72 ≤ 3520)
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (hAB : wordsVal s.mem base a 9 * wordsVal s.mem base b 9 < (2 ^ 64) ^ 9 * m) :
    WP isa mulFn s (Mont.Core m base (wordsVal s.mem base a 9) (wordsVal s.mem base b 9) s) := by
  have hft : (Mont.fnMod true).tmp = Mont.fnTmp := rfl
  have hft' : Mont.fnTmp = 4024 := rfl
  have hpa := Mont.ptrC_of hs hsi (show a + 72 ≤ Z by omega_using [hZ, ha]) (by decide) (Or.inr (Or.inl rfl))
  have hpb := Mont.ptrC_of hs hbx (show b + 72 ≤ Z by omega_using [hZ, hb]) (by decide) (Or.inr (Or.inr rfl))
  have hat : ∀ n < 9, Apart (off base a) (0 + 8 * n) 8 base (Mont.fnMod true).tmp (8 * n) := fun n hn => by
    have h : Apart (off base a) 0 72 base (Mont.fnMod true).tmp (8 * n) :=
      Mont.apart_off base (by rw [hft, hft']; omega_using [ha]) (by omega_using [ha])
    exact h.mono (by omega_using []) (by omega_using [hn])
  have hbt : Apart (off base b) 0 72 base (Mont.fnMod true).tmp 72 :=
    Mont.apart_off base (by rw [hft, hft']; omega_using [hb]) (by omega_using [hb])
  rw [mulFn, WP.block_append_iff]
  refine WP.mono (xRows_ok hs.toC hpa hpb (M := Mont.fnMod true) (a := 0) (b := 0) (by omega_using [])
    (by omega_using []) (by rw [hft, hft']; omega_using [hZ]) hat hbt 8 (Nat.le_refl _)) fun s₃ ⟨k₃, O₃, e₃⟩ => ?_
  have hs₃ : ScrC s₃ base Z 0 := hs.toC.of_keepRegs k₃ (by decide)
  refine WP.mono (xRed_ok hs₃ (M := Mont.fnMod true) (by rw [hft, hft']; omega_using [hZ])) fun s₄ ⟨acc, e₄, k₄, O₄⟩ => ?_
  have e₃' : wordsVal s₃.mem base (Mont.fnMod true).tmp 9 + (2 ^ 64) ^ 9 * hval (xg s₃) 9 9 =
      wordsVal s.mem base a 9 * wordsVal s.mem base b 9 := by
    have := e₃
    rwa [Mont.wordsVal_off, Mont.wordsVal_off] at this
  rw [e₃'] at e₄
  obtain ⟨hW1, hW2, eW⟩ := mulP_arith1P hm hAB (wv_lt _ _ _) e₄.symm
  refine ⟨⟨fun r hr => ?_, by rw [k₄.rd, k₃.rd], by rw [k₄.wr, k₃.wr]⟩, fun x hx => ?_, hW1, hW2, _, eW⟩
  · rw [k₄.gpr r hr, k₃.gpr r hr]
  · rw [O₄ x (by rw [hft]; simp only [Mont.fnTmp] at hx ⊢; omega_using [hx]), O₃ x (by rw [hft]; exact hx)]

end VG.Proof.Weierstrass.X86_64.LazyP521
