module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.LazyP521
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnX
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJNorm
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinLoop
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.Weierstrass.JacMadd
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Mont.X86_64.Ops
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
theorem ptr_ok {s : State} {base : Addr} {size a : Nat} {r : Reg} (hs : Scr s base size) (ha : a < 2 ^ 31) :
    WP isa (.block (ptr r a)) s fun s' => s'.gpr r = off base a ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [ptr, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some, Option.map_some,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun q hq => ?_, rfl, rfl, rfl⟩
  · rw [hs.rdi, se_imm ha]
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
    exact h.sub (by omega_using []) (by omega_using [hn])
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

/-! ### The calls -/

/-- `rbx` into `xmm7`. -/
theorem saveB_ok (s : State) : WP isa (.block [.xop (.movq .xmm7 .rbx)]) s fun s' =>
    s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm .xmm7 = (0 : BitVec 64) ++ s.gpr .rbx := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, Option.some.injEq, exists_eq_left',
    Mont.setXmm_gpr, Mont.setXmm_mem, Mont.setXmm_rd, Mont.setXmm_wr, Mont.setXmm_xmm, ↓reduceIte]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- `rbx` into `xmm7` and `rsi` into `xmm6`. -/
theorem saveBS_ok (s : State) : WP isa (.block [.xop (.movq .xmm7 .rbx), .xop (.movq .xmm6 .rsi)]) s fun s' =>
    s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm .xmm7 = (0 : BitVec 64) ++ s.gpr .rbx ∧
      s'.xmm .xmm6 = (0 : BitVec 64) ++ s.gpr .rsi := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, Option.some.injEq, exists_eq_left',
    Mont.setXmm_gpr, Mont.setXmm_mem, Mont.setXmm_rd, Mont.setXmm_wr, Mont.setXmm_xmm, reduceCtorEq, ↓reduceIte]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem loadB_ok (s : State) : WP isa (.block [.movqR .rbx .xmm7]) s fun s' =>
    s'.gpr .rbx = qword (s.xmm .xmm7) 0 ∧ Keeps [.rbx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg_self]
  refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

theorem loadS_ok (s : State) : WP isa (.block [.movqR .rsi .xmm6]) s fun s' =>
    s'.gpr .rsi = qword (s.xmm .xmm6) 0 ∧ Keeps [.rsi] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg_self]
  refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- What a product by a call does. -/
def MulPost (m : Nat) (base : Addr) (o a b : Nat) (s s' : State) : Prop :=
  wordsVal s'.mem base o 9 < m ∧
    wordsVal s'.mem base o 9 * (2 ^ 64) ^ 9 % m = wordsVal s.mem base a 9 * wordsVal s.mem base b 9 % m ∧
    KeepRegs opRegs s s' ∧
    ∀ x, (ofs base x < o ∨ o + 72 ≤ ofs base x) → (ofs base x < Mont.fnTmp ∨ Mont.fnTmp + 72 ≤ ofs base x) →
      s'.mem x = s.mem x

/-- A core's result made canonical and stored. -/
theorem canon_ok {s s₁ : State} {base : Addr} {Z o a b m : Nat} (hs₁ : Scr s₁ base Z) (ho : o + 72 ≤ Z)
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (h : Mont.Core m base (wordsVal s.mem base a 9) (wordsVal s.mem base b 9) s s₁) :
    WP isa (.block (xCanon 0 o)) s₁ (MulPost m base o a b s) := by
  obtain ⟨k₁, O₁, hW1, hW2, U, eW⟩ := h
  refine WP.mono (xCanon_ok hs₁.toC ho hm hW1 hW2) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hmo : 0 < m := by omega_using [hW1, hW2]
  refine ⟨by rw [e₂]; exact Nat.mod_lt _ hmo,
    by rw [e₂, Nat.mod_mul_mod, Nat.mul_comm, eW, Nat.add_mul_mod_self_right],
    ⟨fun r hr => ?_, by rw [k₂.rd, k₁.rd], by rw [k₂.wr, k₁.wr]⟩, fun x hx hx' => ?_⟩
  · rw [k₂.gpr r (fun h => hr (by
      rcases List.mem_cons.mp h with h | h
      · exact h ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))), k₁.gpr r hr]
  · rw [O₂ x hx, O₁ x hx']

theorem sqrCall_ok {s : State} {base : Addr} {Z o a m : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    (ho : o + 72 ≤ 3520) (ha : a + 72 ≤ 3520) (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (hAB : wordsVal s.mem base a 9 * wordsVal s.mem base a 9 < (2 ^ 64) ^ 9 * m) :
    WP isa (sqrCall o a).inline s (MulPost m base o a a s) := by
  simp only [sqrCall, Code.inline, sqrFn]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (saveB_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁, x₁⟩ => ?_
  have hs₁ : Scr s₁ base Z := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  refine WP.mono (WP.vecKeep rfl (ptr_ok hs₁ (r := .rbx) (a := a) (by omega_using [ha])))
    fun s₂ ⟨⟨b₂, k₂⟩, x₂, _⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have hm₂ : s₂.mem = s.mem := k₂.2.1.trans m₁
  refine WP.seq (WP.mono (WP.vecKeep (by decide +kernel) (Mont.sqrCore_okP hs₂ hZ b₂ ha hm (by rw [hm₂]; exact hAB)))
    fun s₃ ⟨C₃, x₃, _⟩ => ?_)
  have hs₃ : Scr s₃ base Z := hs₂.of_keepRegs C₃.1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep (c := .block (xCanon 0 o)) (by rfl) (canon_ok hs₃ (o := o) (by omega_using [hZ, ho]) hm C₃))
    fun s₄ ⟨⟨l₄, e₄, k₄, mm₄⟩, x₄, _⟩ => ?_
  refine WP.mono (loadB_ok s₄) fun s₅ ⟨b₅, k₅⟩ => ?_
  rw [hm₂] at e₄
  refine ⟨by rw [k₅.2.1]; exact l₄, by rw [k₅.2.1]; exact e₄,
    ⟨fun r hr => ?_, by rw [k₅.2.2.1, k₄.rd, k₂.2.2.1, rd₁], by rw [k₅.2.2.2, k₄.wr, k₂.2.2.2, wr₁]⟩,
    fun x h1 h2 => by rw [k₅.2.1, mm₄ x h1 h2, hm₂]⟩
  by_cases hb : r = .rbx
  · rw [hb, b₅, x₄, x₃, x₂, x₁, Mont.qword_lo]
  · rw [k₅.1 r (by simpa using hb), k₄.gpr r hr, k₂.1 r (by simpa using hb), g₁]

theorem mulCall_ok {s : State} {base : Addr} {Z o a b m : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    (ho : o + 72 ≤ 3520) (ha : a + 72 ≤ 3520) (hb : b + 72 ≤ 3520) (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (hAB : wordsVal s.mem base a 9 * wordsVal s.mem base b 9 < (2 ^ 64) ^ 9 * m) :
    WP isa (LazyP521.mulCall o a b).inline s (MulPost m base o a b s) := by
  simp only [LazyP521.mulCall, Code.inline]
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (saveBS_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁, x₁, y₁⟩ => ?_
  have hs₁ : Scr s₁ base Z := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep rfl (ptr_ok hs₁ (r := .rsi) (a := a) (by omega_using [ha])))
    fun s₂ ⟨⟨b₂, k₂⟩, x₂, _⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (WP.vecKeep rfl (ptr_ok hs₂ (r := .rbx) (a := b) (by omega_using [hb])))
    fun s₃ ⟨⟨b₃, k₃⟩, x₃, _⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have hm₃ : s₃.mem = s.mem := k₃.2.1.trans (k₂.2.1.trans m₁)
  refine WP.seq (WP.mono (WP.vecKeep (by decide +kernel) (mulFn_ok hs₃ hZ (by rw [k₃.1 _ (by decide), b₂]) b₃ ha hb hm
    (by rw [hm₃]; exact hAB))) fun s₄ ⟨C₄, x₄, _⟩ => ?_)
  have hs₄ : Scr s₄ base Z := hs₃.of_keepRegs C₄.1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep (c := .block (xCanon 0 o)) (by rfl) (canon_ok hs₄ (o := o) (by omega_using [hZ, ho]) hm C₄))
    fun s₅ ⟨⟨l₅, e₅, k₅, mm₅⟩, x₅, _⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (WP.vecKeep rfl (loadB_ok s₅)) fun s₆ ⟨⟨b₆, k₆⟩, x₆, _⟩ => ?_
  refine WP.mono (loadS_ok s₆) fun s₇ ⟨b₇, k₇⟩ => ?_
  rw [hm₃] at e₅
  refine ⟨by rw [k₇.2.1, k₆.2.1]; exact l₅, by rw [k₇.2.1, k₆.2.1]; exact e₅,
    ⟨fun r hr => ?_, by rw [k₇.2.2.1, k₆.2.2.1, k₅.rd, k₃.2.2.1, k₂.2.2.1, rd₁],
      by rw [k₇.2.2.2, k₆.2.2.2, k₅.wr, k₃.2.2.2, k₂.2.2.2, wr₁]⟩,
    fun x h1 h2 => by rw [k₇.2.1, k₆.2.1, mm₅ x h1 h2, hm₃]⟩
  by_cases hs : r = .rsi
  · rw [hs, b₇, x₆, x₅, x₄, x₃, x₂, y₁, Mont.qword_lo]
  · rw [k₇.1 r (by simpa using hs)]
    by_cases hb : r = .rbx
    · rw [hb, b₆, x₅, x₄, x₃, x₂, x₁, Mont.qword_lo]
    · rw [k₆.1 r (by simpa using hb), k₅.gpr r hr, k₃.1 r (by simpa using hb), k₂.1 r (by simpa using hs), g₁]

/-! ## Programs -/

/-- A number's bound: below `m` for `0`, else at most `k m`. -/
def Bd (m k v : Nat) : Prop := v ≤ max k 1 * m ∧ (k = 0 → v < m)

/-- The slots of `L` hold numbers in their bounds, which stand for `E`. -/
structure LInv (M : Mod) (base : Addr) (size m : Nat) [NeZero m] (Sl : Nat → Prop) (L : Bounds)
    (E : Nat → Fin m) (s : State) : Prop where
  scr : Scr s base size
  mod : ModOkW M size m s.mem base
  sl : ∀ x k, L.lookup x = some k → Sl x
  bd : ∀ x k, L.lookup x = some k → Bd m k (wordsVal s.mem base x M.n)
  val : ∀ x k, L.lookup x = some k → toM m (2 ^ (64 * M.n)) (wordsVal s.mem base x M.n) = E x

/-- An operation writing `o`, which then holds `v` with the bound `k`. -/
theorem LInv.update {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    {L : Bounds} {E : Nat → Fin m} {s s' : State} (hI : LInv M base size m Sl L E s) {o k : Nat}
    (ho : Sl o) (hk : OpKeep M base o s s') (hr : Bd m k (wordsVal s'.mem base o M.n)) {v : Fin m}
    (hv : toM m (2 ^ (64 * M.n)) (wordsVal s'.mem base o M.n) = v) :
    LInv M base size m Sl ((o, k) :: L) (Function.update E o v) s' := by
  have hn := hI.scr.nowrap
  have hlo := hL.le o ho
  have hmo := hL.mo o ho
  have hto := hL.tmp o ho
  have hM := hI.mod
  have heq : ∀ x, Sl x → x ≠ o → wordsVal s'.mem base x M.n = wordsVal s.mem base x M.n :=
    fun x hx hxo => by
      have := hL.apart x o hx ho hxo
      have := hL.tmp x hx
      have := hL.le x hx
      exact opKeep_wordsVal hk (by omega_arith) (by omega_arith) (by omega_arith)
  have look : ∀ x k', ((o, k) :: L).lookup x = some k' → (x = o ∧ k' = k) ∨ (x ≠ o ∧ L.lookup x = some k') := by
    intro x k' h
    rw [List.lookup_cons] at h
    by_cases hx : x = o
    · subst hx; simp only [beq_self_eq_true, Option.some.injEq] at h; exact Or.inl ⟨rfl, h.symm⟩
    · rw [beq_eq_false_iff_ne.mpr hx] at h; exact Or.inr ⟨hx, h⟩
  refine ⟨⟨(hk.gpr _ (rdi_not_clob _)).trans hI.scr.rdi, hk.wr ▸ hI.scr.wr, hn⟩,
    ⟨hM.n0, hM.mo, hM.tmp, hM.sep, ?_, hM.inv, hM.red⟩, ?_, ?_, ?_⟩
  · have := hM.mo
    have := hM.sep
    rw [opKeep_wordsVal hk (by omega_arith) (by omega_arith) (by omega_arith)]
    exact hM.val
  · intro x k' h
    rcases look x k' h with ⟨rfl, -⟩ | ⟨-, h⟩
    · exact ho
    · exact hI.sl x k' h
  · intro x k' h
    rcases look x k' h with ⟨rfl, rfl⟩ | ⟨hx, h⟩
    · exact hr
    · rw [heq x (hI.sl x k' h) hx]; exact hI.bd x k' h
  · intro x k' h
    rcases look x k' h with ⟨rfl, rfl⟩ | ⟨hx, h⟩
    · rw [Function.update_self]; exact hv
    · rw [Function.update_of_ne hx, heq x (hI.sl x k' h) hx]; exact hI.val x k' h

/-- A half, modulo P-521's `p`. -/
def halfF (m : Nat) [NeZero m] : Fin m := Fin.ofNat m (2 ^ 520)

/-- An operation on what the slots stand for. -/
def run {m : Nat} [NeZero m] (E : Nat → Fin m) : LOp → Nat → Fin m
  | .mul o a b => Function.update E o (E a * E b)
  | .add o a b => Function.update E o (E a + E b)
  | .sub o a b => Function.update E o (E a - E b)
  | .tri o a => Function.update E o (E a + E a + E a)
  | .sub2 o a b => Function.update E o (E a - E b - E b)
  | .subF o a b => Function.update E o (E a - E b)
  | .half o a => Function.update E o (E a * halfF m)
  | .cadd o a b => Function.update E o (E a + E b)
  | .csub o a b => Function.update E o (E a - E b)

def runs {m : Nat} [NeZero m] (ops : List LOp) (E : Nat → Fin m) : Nat → Fin m := ops.foldl run E

/-! ### What numbers stand for -/

section
variable {m : Nat} [NeZero m] {R : Nat}

theorem toM_congr {x y : Nat} (h : x % m = y % m) : toM m R x = toM m R y := by
  unfold toM; rw [ofNat_eq_ofNat.mpr h]

theorem toM_plus (A B : Nat) : toM m R (A + B) = toM m R A + toM m R B := by
  rw [← toM_add R A B]; exact toM_congr (Nat.mod_mod _ _).symm

theorem toM_minus {A B : Nat} (h : B ≤ m) : toM m R (A + (m - B)) = toM m R A - toM m R B := by
  rw [← toM_sub (R := R) (A := A) (B := B) (by omega_using [h])]
  refine toM_congr ?_
  rw [Nat.mod_mod, show A + (m - B) = A + m - B by omega_using [h]]

theorem toM_fold {v q x : Nat} (h : v + q * m = x) : toM m R v = toM m R x := by
  subst h; exact toM_congr (Nat.add_mul_mod_self_right _ _ _).symm

theorem halfF_two (hm : m + 1 = 512 * (2 ^ 64) ^ 8) : halfF m + halfF m = 1 := by
  apply Fin.ext
  rw [Fin.val_add]
  simp only [halfF, Fin.val_ofNat, Nat.add_mod_mod, Nat.mod_add_mod]
  show _ = 1 % m
  obtain hm' : m = 512 * (2 ^ 64) ^ 8 - 1 := by omega_using [hm]
  subst hm'
  decide +kernel

theorem toM_half (hm : m + 1 = 512 * (2 ^ 64) ^ 8) {v q A : Nat} (h : 2 * v = A + q * m) :
    toM m R v = toM m R A * halfF m := by
  have h1 : toM m R v + toM m R v = toM m R A := by
    rw [← toM_plus, ← Nat.two_mul]
    exact (toM_fold (q := q) h.symm).symm
  have h2 := halfF_two hm
  rw [← h1]
  grind

end

section
variable {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}

theorem LKeep.op {o : Nat} {s s' : State} (hn9 : M.n = 9) (h : LKeep base o s s') : OpKeep M base o s s' :=
  ⟨fun r hr => h.1.gpr r fun h' => hr (by rw [hn9]; exact xRegs_clob r h'), h.1.rd, h.1.wr,
    fun x hx _ => h.2 x (by rw [hn9] at hx; exact hx)⟩

theorem prod_lt {ka kb A B : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (ha : ka ≤ 8) (hb : kb ≤ 8)
    (hA : Bd m ka A) (hB : Bd m kb B) : A * B < (2 ^ 64) ^ 9 * m := by
  have h1 : A ≤ 8 * m := Nat.le_trans hA.1 (Nat.mul_le_mul_right _ (by omega_using [ha]))
  have h2 : B ≤ 8 * m := Nat.le_trans hB.1 (Nat.mul_le_mul_right _ (by omega_using [hb]))
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  calc A * B ≤ (8 * m) * (8 * m) := Nat.mul_le_mul h1 h2
    _ = (64 * m) * m := by grind
    _ < (2 ^ 64) ^ 9 * m := Nat.mul_lt_mul_of_pos_right (by omega_arith) hm0

/-- An operation, whose bounds `step` checks. -/
theorem op_ok (hL : Lay M size Sl) (hm : UnitMod m (2 ^ (64 * M.n))) (hred : M.red = .friendly p521Ws)
    (ht : M.tmp = Mont.fnTmp) {L L' : Bounds} {E : Nat → Fin m} {s : State} (hI : LInv M base size m Sl L E s)
    {op : LOp} (ho : Sl op.out) (hs : step L op = some L') :
    WP isa (code M op).inline s fun s' => OpKeep M base op.out s s' ∧ LInv M base size m Sl L' (run E op) s' := by
  obtain ⟨hn9, hp⟩ := p521_of_red hred hI.mod.red
  have hsz : ∀ x, Sl x → x + 72 ≤ size := fun x hx => by have := hL.le x hx; rwa [hn9] at this
  have hz := hI.scr.toC
  have W : ∀ (mm : Mem) (x : Nat), wordsVal mm base x M.n = wordsVal mm base x 9 := fun mm x => by rw [hn9]
  have B := hI.bd
  have V := hI.val
  have S := hI.sl
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  cases op with
  | mul o a b =>
    change Sl o at ho
    simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨ka, hka, kb, hkb, ⟨h1, h2, hlow⟩, rfl⟩ := hs
    simp only [Mont.lowArgs, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hlow
    obtain ⟨⟨l1, l2⟩, l3⟩ := hlow
    have hZ : 4096 ≤ size := by
      have := hI.mod.tmp; rw [ht, hn9] at this; simp only [Mont.fnTmp] at this; omega_using [this]
    have hAB := prod_lt hp h1 h2 (B a ka hka) (B b kb hkb)
    rw [W, W] at hAB
    have key : WP isa (code M (.mul o a b)).inline s (MulPost m base o a b s) := by
      simp only [LazyP521.code]
      split
      · rename_i hab
        subst hab
        exact sqrCall_ok hI.scr hZ l1 l2 hp hAB
      · exact mulCall_ok hI.scr hZ l1 l2 l3 hp hAB
    refine WP.mono key fun s' ⟨lt, e, k, mm⟩ => ?_
    have ok : OpKeep M base o s s' := ⟨fun r hr => k.gpr r fun h' => hr (by rw [hn9]; exact xRegs_clob r h'), k.rd, k.wr,
      fun x hx hx' => mm x (by rw [hn9] at hx; exact hx) (by rw [hn9, ht] at hx'; exact hx')⟩
    refine ⟨ok, hI.update hL ho ok ⟨by rw [W, show max 0 1 = 1 by decide, Nat.one_mul]; exact Nat.le_of_lt lt, fun _ => by rw [W]; exact lt⟩ ?_⟩
    rw [toM_mul hm (A := wordsVal s.mem base a M.n) (B := wordsVal s.mem base b M.n)
      (by rw [W, W, W, hn9, Nat.pow_mul 2 64 9]; exact e), V a ka hka, V b kb hkb]
  | add o a b =>
    change Sl o at ho
    simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨ka, hka, kb, hkb, ⟨h1, h2⟩, rfl⟩ := hs
    have bA := (B a ka hka).1; have bB := (B b kb hkb).1
    rw [W] at bA bB
    have hA4 : wordsVal s.mem base a 9 ≤ 4 * m := Nat.le_trans bA (Nat.mul_le_mul_right _ (by omega_using [h1]))
    have hB4 : wordsVal s.mem base b 9 ≤ 4 * m := Nat.le_trans bB (Nat.mul_le_mul_right _ (by omega_using [h2]))
    refine WP.mono (add_ok hz (hsz o ho) (hsz a (S a ka hka)) (hsz b (S b kb hkb)) (by omega_arith)) fun s' ⟨e, k⟩ =>
      ⟨k.op hn9, hI.update hL ho (k.op hn9) ⟨?_, fun h => absurd h (by omega_using [])⟩ ?_⟩
    · rw [W, e, show max (max ka 1 + max kb 1) 1 = max ka 1 + max kb 1 by omega_using [], Nat.add_mul]
      exact Nat.add_le_add bA bB
    · rw [W, e, toM_plus, ← W, ← W, V a ka hka, V b kb hkb]
  | sub o a b =>
    change Sl o at ho
    simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨ka, hka, kb, hkb, ⟨h1, h2⟩, rfl⟩ := hs
    have bA := (B a ka hka).1; have bB := (B b kb hkb).1
    rw [W] at bA bB
    have hA4 : wordsVal s.mem base a 9 ≤ 4 * m := Nat.le_trans bA (Nat.mul_le_mul_right _ (by omega_using [h1]))
    have hB1 : wordsVal s.mem base b 9 ≤ m := by rw [show max kb 1 = 1 by omega_using [h2], Nat.one_mul] at bB; exact bB
    refine WP.mono (sub_ok hp hz (hsz o ho) (hsz a (S a ka hka)) (hsz b (S b kb hkb)) hB1 hA4) fun s' ⟨e, k⟩ =>
      ⟨k.op hn9, hI.update hL ho (k.op hn9) ⟨?_, fun h => absurd h (by omega_using [])⟩ ?_⟩
    · rw [W, e, show max (max ka 1 + 1) 1 = max ka 1 + 1 by omega_using [], Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add bA (Nat.sub_le _ _)
    · rw [W, e, toM_minus hB1, ← W, ← W, V a ka hka, V b kb hkb]
  | tri o a =>
    change Sl o at ho
    simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨ka, hka, h1, rfl⟩ := hs
    have bA := (B a ka hka).1
    rw [W, show max ka 1 = 1 by omega_using [h1], Nat.one_mul] at bA
    refine WP.mono (tri_ok hp hz (hsz o ho) (hsz a (S a ka hka)) bA) fun s' ⟨e, k⟩ =>
      ⟨k.op hn9, hI.update hL ho (k.op hn9) ⟨?_, fun h => absurd h (by omega_using [])⟩ ?_⟩
    · rw [W, e, show max 3 1 = 3 by decide]; exact Nat.mul_le_mul_left _ bA
    · rw [W, e, show 3 * wordsVal s.mem base a 9 = wordsVal s.mem base a 9 + wordsVal s.mem base a 9 +
        wordsVal s.mem base a 9 by omega_using [], toM_plus, toM_plus, ← W, V a ka hka]
  | sub2 o a b =>
    change Sl o at ho
    simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨ka, hka, kb, hkb, ⟨h1, h2⟩, rfl⟩ := hs
    have bA := (B a ka hka).1; have bB := (B b kb hkb).1
    rw [W, show max ka 1 = 1 by omega_using [h1], Nat.one_mul] at bA
    rw [W, show max kb 1 = 1 by omega_using [h2], Nat.one_mul] at bB
    refine WP.mono (sub2_ok hp hz (hsz o ho) (hsz a (S a ka hka)) (hsz b (S b kb hkb)) bB bA) fun s' ⟨⟨⟨q, e⟩, l⟩, k⟩ =>
      ⟨k.op hn9, hI.update hL ho (k.op hn9) ⟨by rw [W, show max 1 1 = 1 by decide, Nat.one_mul]; exact l,
        fun h => absurd h (by omega_using [])⟩ ?_⟩
    rw [W, toM_fold e, show wordsVal s.mem base a 9 + 2 * (m - wordsVal s.mem base b 9) =
      wordsVal s.mem base a 9 + (m - wordsVal s.mem base b 9) + (m - wordsVal s.mem base b 9) by omega_using [],
      toM_minus bB, toM_minus bB, ← W, ← W, V a ka hka, V b kb hkb]
  | subF o a b =>
    change Sl o at ho
    simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨ka, hka, kb, hkb, ⟨h1, h2⟩, rfl⟩ := hs
    have bA := (B a ka hka).1; have bB := (B b kb hkb).1
    rw [W, show max ka 1 = 1 by omega_using [h1], Nat.one_mul] at bA
    rw [W, show max kb 1 = 1 by omega_using [h2], Nat.one_mul] at bB
    refine WP.mono (subF_ok hp hz (hsz o ho) (hsz a (S a ka hka)) (hsz b (S b kb hkb)) bB bA) fun s' ⟨⟨⟨q, e⟩, l⟩, k⟩ =>
      ⟨k.op hn9, hI.update hL ho (k.op hn9) ⟨by rw [W, show max 1 1 = 1 by decide, Nat.one_mul]; exact l,
        fun h => absurd h (by omega_using [])⟩ ?_⟩
    rw [W, toM_fold e, toM_minus bB, ← W, ← W, V a ka hka, V b kb hkb]
  | half o a =>
    change Sl o at ho
    simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨ka, hka, h1, rfl⟩ := hs
    have bA := (B a ka hka).1
    rw [W, show max ka 1 = 1 by omega_using [h1], Nat.one_mul] at bA
    refine WP.mono (half_ok hp hz (hsz o ho) (hsz a (S a ka hka)) bA) fun s' ⟨⟨⟨q, e⟩, l⟩, k⟩ =>
      ⟨k.op hn9, hI.update hL ho (k.op hn9) ⟨by rw [W, show max 1 1 = 1 by decide, Nat.one_mul]; exact l,
        fun h => absurd h (by omega_using [])⟩ ?_⟩
    rw [W, toM_half hp e, ← W, V a ka hka]
  | cadd o a b =>
    change Sl o at ho
    simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨ka, hka, kb, hkb, ⟨h1, rfl⟩, rfl⟩ := hs
    have bA := (B a ka hka).1; have bB := (B b 0 hkb).2 rfl
    rw [show max ka 1 = 1 by omega_using [h1], Nat.one_mul] at bA
    have sa := S a ka hka; have sb := S b 0 hkb
    refine WP.mono (_root_.VG.Proof.Mont.X86_64.add_ok hI.scr hI.mod (hL.le o ho) (hL.le a sa) (hL.le b sb) (hL.tmp o ho)
      (hL.tmp a sa) (hL.tmp b sb) (hL.mo o ho) (by omega_using [bA, bB])) fun s' ⟨k, e⟩ =>
      ⟨k, hI.update hL ho k ⟨?_, fun _ => by rw [e]; exact Nat.mod_lt _ hm0⟩ ?_⟩
    · rw [e, show max 0 1 = 1 by decide, Nat.one_mul]; exact Nat.le_of_lt (Nat.mod_lt _ hm0)
    · rw [e, toM_add, V a ka hka, V b 0 hkb]
  | csub o a b =>
    change Sl o at ho
    simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨ka, hka, kb, hkb, ⟨rfl, rfl⟩, rfl⟩ := hs
    have bA := (B a 0 hka).2 rfl; have bB := (B b 0 hkb).2 rfl
    have sa := S a 0 hka; have sb := S b 0 hkb
    refine WP.mono (_root_.VG.Proof.Mont.X86_64.sub_ok hI.scr hI.mod (hL.le o ho) (hL.le a sa) (hL.le b sb) (hL.tmp o ho)
      (hL.tmp a sa) (hL.tmp b sb) (hL.mo o ho) bA bB) fun s' ⟨k, e⟩ =>
      ⟨k, hI.update hL ho k ⟨?_, fun _ => by rw [e]; exact Nat.mod_lt _ hm0⟩ ?_⟩
    · rw [e, show max 0 1 = 1 by decide, Nat.one_mul]; exact Nat.le_of_lt (Nat.mod_lt _ hm0)
    · rw [e, toM_sub (by omega_using [bB]), V a 0 hka, V b 0 hkb]

/-- A program, whose bounds `check` checks. -/
theorem prog_ok (hL : Lay M size Sl) (hm : UnitMod m (2 ^ (64 * M.n))) (hred : M.red = .friendly p521Ws)
    (ht : M.tmp = Mont.fnTmp) : ∀ (ops : List LOp) {L L' : Bounds} {E : Nat → Fin m} {s : State},
      LInv M base size m Sl L E s → (∀ op ∈ ops, Sl op.out) → check L ops = some L' →
      WP isa (prog M ops).inline s fun s' => ProgKeep M base (ops.map LOp.out) s s' ∧
        LInv M base size m Sl L' (runs ops E) s'
  | [], L, L', E, s, hI, _, hc => by
    simp only [check, Option.some.injEq] at hc
    subst hc
    exact WP.block_nil ⟨ProgKeep.refl _ _ _ s, hI⟩
  | op :: ops, L, L', E, s, hI, hS, hc => by
    simp only [check, Option.bind_eq_some_iff] at hc
    obtain ⟨L₁, h₁, hc⟩ := hc
    show WP isa (Code.seq (code M op).inline (prog M ops).inline) s _
    refine WP.seq (WP.mono (op_ok hL hm hred ht hI (hS op (List.mem_cons_self ..)) h₁) fun s₁ ⟨k₁, I₁⟩ => ?_)
    refine WP.mono (prog_ok hL hm hred ht ops I₁ (fun op' h => hS op' (List.mem_cons_of_mem _ h)) hc) fun s₂ ⟨k₂, I₂⟩ =>
      ⟨⟨fun r hr => (k₂.gpr r hr).trans (k₁.gpr r hr), k₂.rd.trans k₁.rd, k₂.wr.trans k₁.wr, fun x hx hx' => ?_⟩, I₂⟩
    rw [List.map_cons] at hx
    rw [k₂.mem x (fun w hw => hx w (List.mem_cons_of_mem _ hw)) hx', k₁.mem x (hx _ (List.mem_cons_self ..)) hx']

end

/-! ## The points -/

open Spec.Weierstrass VG.Impl.Weierstrass VG.Proof.Weierstrass

theorem mem_of_lookup : ∀ {L : Bounds} {x k : Nat}, L.lookup x = some k → (x, k) ∈ L
  | (y, j) :: L, x, k, h => by
    rw [List.lookup_cons] at h
    by_cases hx : x = y
    · subst hx; simp only [beq_self_eq_true, Option.some.injEq] at h; subst h; exact List.mem_cons_self ..
    · rw [beq_eq_false_iff_ne.mpr hx] at h; exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem LInv.of_mem {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} {L : Bounds}
    {E : Nat → Fin m} {s : State} (hs : Scr s base size) (hM : ModOkW M size m s.mem base)
    (h : ∀ p ∈ L, Sl p.1 ∧ Bd m p.2 (wordsVal s.mem base p.1 M.n) ∧
      toM m (2 ^ (64 * M.n)) (wordsVal s.mem base p.1 M.n) = E p.1) : LInv M base size m Sl L E s :=
  ⟨hs, hM, fun x k hx => (h (x, k) (mem_of_lookup hx)).1, fun x k hx => (h (x, k) (mem_of_lookup hx)).2.1,
    fun x k hx => (h (x, k) (mem_of_lookup hx)).2.2⟩

theorem Bd.mono {m k j v : Nat} (h : Bd m k v) (hj : k ≤ j) (h0 : j = 0 → k = 0) : Bd m j v :=
  ⟨Nat.le_trans h.1 (Nat.mul_le_mul_right _ (by omega_using [hj])), fun e => h.2 (h0 e)⟩

theorem Bd.lt {m v : Nat} (h : Bd m 0 v) : v < m := h.2 rfl

theorem Bd.of_lt {m v : Nat} (h : v < m) : Bd m 0 v :=
  ⟨by rw [show max 0 1 = 1 by decide, Nat.one_mul]; exact Nat.le_of_lt h, fun _ => h⟩

/-- A slot a program does not write. -/
theorem progKeep_wordsVal {M : Mod} {base : Addr} {size : Nat} {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hn : base.toNat + size ≤ 2 ^ 64) {W : List Nat} {s s' : State} (h : ProgKeep M base W s s')
    (hW : ∀ w ∈ W, Sl w) {y : Nat} (hy : Sl y) (hyW : y ∉ W) :
    wordsVal s'.mem base y M.n = wordsVal s.mem base y M.n := by
  have hle := hL.le y hy
  have ht := hL.tmp y hy
  have key : ∀ k z, y ≤ z → z + 8 * k ≤ y + 8 * M.n → wordsVal s'.mem base z k = wordsVal s.mem base z k := by
    intro k
    induction k with
    | zero => intro _ _ _; rfl
    | succ k ih =>
      intro z h1 h2
      simp only [wordsVal]
      have hw : word s'.mem base z = word s.mem base z :=
        Mem.readW_congr fun i hi => h.mem _ (fun w hw => by
          have := hL.apart y w hy (hW w hw) (fun e => hyW (e ▸ hw))
          rw [ofs_off base (by omega_arith)]; omega_arith)
          (by rw [ofs_off base (by omega_arith)]; omega_arith)
      rw [ih (z + 8) (by omega_using [h1]) (by omega_using [h2]), hw]
  exact key M.n y (Nat.le_refl _) (Nat.le_refl _)

/-- The doubling, with `H = 2Y` in place of `Y`. -/
theorem dbl_run {m : Nat} [NeZero m] (S : RcbSlots) (p : Pt) (E : Nat → Fin m) {Y : Fin m}
    (hd : [S.t0, S.t1, S.t2, S.t3, p.x, p.y, p.z].Nodup) (hY : E p.y = Y + Y) :
    (runs (dblOps S p) E p.x = (dblJF (E p.x) Y (E p.z)).1 ∧
      runs (dblOps S p) E p.y = (dblJF (E p.x) Y (E p.z)).2.1 + (dblJF (E p.x) Y (E p.z)).2.1) ∧
      runs (dblOps S p) E p.z = (dblJF (E p.x) Y (E p.z)).2.2 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  rcases hd with ⟨⟨h01, h02, h03, h04, h05, h06⟩, ⟨h12, h13, h14, h15, h16⟩, ⟨h23, h24, h25, h26⟩,
    ⟨h34, h35, h36⟩, ⟨h45, h46⟩, h56, _⟩
  have h10 := Ne.symm h01
  have h20 := Ne.symm h02
  have h30 := Ne.symm h03
  have h40 := Ne.symm h04
  have h50 := Ne.symm h05
  have h60 := Ne.symm h06
  have h21 := Ne.symm h12
  have h31 := Ne.symm h13
  have h41 := Ne.symm h14
  have h51 := Ne.symm h15
  have h61 := Ne.symm h16
  have h32 := Ne.symm h23
  have h42 := Ne.symm h24
  have h52 := Ne.symm h25
  have h62 := Ne.symm h26
  have h43 := Ne.symm h34
  have h53 := Ne.symm h35
  have h63 := Ne.symm h36
  have h54 := Ne.symm h45
  have h64 := Ne.symm h46
  have h65 := Ne.symm h56
  simp only [dblOps, runs, List.foldl, run, Function.update_apply, dblJF, *, ite_true, ite_false]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> grind

theorem lazyChecks_spec {L : Bounds} {ops : List LOp} {want : Bounds} (h : WinCfg.lazyChecks L ops want = true) :
    ∃ L', check L ops = some L' ∧ ∀ w ∈ want, L'.lookup w.1 = some w.2 := by
  unfold WinCfg.lazyChecks at h
  split at h
  · exact absurd h (by decide)
  · rename_i L' hL
    exact ⟨L', hL, fun w hw => by simpa using List.all_eq_true.mp h w hw⟩

/-- What `lazyOk` says. -/
theorem lazyOk_spec {K : WinCfg} (h : WinCfg.lazyOk K = true) :
    [K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5, K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.D.x, K.D.y, K.D.z, K.zero].Nodup ∧
    K.M.n = 9 ∧ K.M.red = .friendly p521Ws ∧ K.M.tmp = Mont.fnTmp ∧
    (∃ L, check (WinCfg.lazyBounds K) (dblOps K.S K.R) = some L ∧ L.lookup K.R.x = some 1 ∧ L.lookup K.R.y = some 1 ∧
      L.lookup K.R.z = some 0) ∧
    ∃ L, check (WinCfg.lazyAddBounds K) (maddOps K.S K.R K.E K.D) = some L ∧ L.lookup K.D.x = some 0 ∧
      L.lookup K.D.y = some 0 ∧ L.lookup K.D.z = some 0 := by
  rw [WinCfg.lazyOk, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h4⟩, h5⟩ := h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h1
  obtain ⟨⟨⟨-, h1⟩, h2⟩, h3⟩ := h1
  obtain ⟨L, c, l⟩ := lazyChecks_spec h4
  obtain ⟨L', c', l'⟩ := lazyChecks_spec h5
  exact ⟨h0, of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3,
    ⟨L, c, l (_, 1) (by simp), l (_, 1) (by simp), l (_, 0) (by simp)⟩,
    ⟨L', c', l' (_, 0) (by simp), l' (_, 0) (by simp), l' (_, 0) (by simp)⟩⟩

section
variable {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}

/-- The slots the lazy programs write, in `rcbW`. -/
theorem dbl_outs (S : RcbSlots) (p : Pt) : ∀ x ∈ (dblOps S p).map LOp.out, x ∈ rcbW S p := by
  intro x hx
  simp only [dblOps, List.map_cons, List.map_nil, LOp.out, List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false]
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]

theorem madd_outs (S : RcbSlots) (p q o : Pt) : ∀ x ∈ (maddOps S p q o).map LOp.out, x ∈ rcbW S o := by
  intro x hx
  simp only [maddOps, List.map_cons, List.map_nil, LOp.out, List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false]
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]

theorem nodup_zero {a b c d e f x y z u v i j k w : Nat}
    (h : [a, b, c, d, e, f, x, y, z, u, v, i, j, k, w].Nodup) : w ≠ x ∧ w ≠ y := by
  constructor <;> (rintro rfl; simp at h)

theorem nodup_dbl {a b c d e f x y z u v i j k w : Nat}
    (h : [a, b, c, d, e, f, x, y, z, u, v, i, j, k, w].Nodup) : [a, b, c, d, x, y, z].Nodup :=
  h.sublist (by
    refine .cons_cons _ (.cons_cons _ (.cons_cons _ (.cons_cons _ (.cons _ (.cons _ (.cons_cons _ (.cons_cons _ (.cons_cons _ ?_))))))))
    exact List.nil_sublist _)

/-- A lazy doubling. -/
theorem dblLazy_ok (hz : WinCfg.lazyOk K = true) (hL : WinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n)))
    (hC : Law C) (hM3 : AM3 C) {E : Nat → Fe C} {s : State}
    (hI : LInv K.M base size C.p (· ∈ winSlots K) (WinCfg.lazyBounds K) E s) {Y : Fe C} (hY : E K.R.y = Y + Y)
    {Q : Point C} (hQ : onCurve C Q = true) (hJ : InvJ C (E K.R.x) Y (E K.R.z) Q) :
    WP isa (prog K.M (dblOps K.S K.R)).inline s fun t => ProgKeep K.M base (rcbW K.S K.R) s t ∧
      ∃ (E' : Nat → Fe C) (Y' : Fe C), LInv K.M base size C.p (· ∈ winSlots K) (WinCfg.lazyBounds K) E' t ∧
        E' K.R.y = Y' + Y' ∧ InvJ C (E' K.R.x) Y' (E' K.R.z) (Spec.Weierstrass.add Q Q) ∧
        Bd C.p 1 (wordsVal t.mem base K.R.y K.M.n) := by
  obtain ⟨hnd, -, hred, ht, ⟨L, hc, lx, ly, lz⟩, -⟩ := lazyOk_spec hz
  obtain oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  obtain w := winJ_sl oR (fun x hx => winOther_mem (oR x hx)) (fun x hx => winOther_mem (oR x hx))
  refine WP.mono (prog_ok hL.lay hp hred ht _ hI (fun op hop => w.1 _ (List.mem_append_left _
    (dbl_outs _ _ _ (List.mem_map_of_mem hop)))) hc) fun t ⟨k, I⟩ => ⟨k.mono (dbl_outs _ _), ?_⟩
  obtain ⟨⟨rx, ry⟩, rz⟩ := dbl_run K.S K.R E (nodup_dbl hnd) hY
  refine ⟨_, _, LInv.of_mem I.scr I.mod fun p hp' => ?_, ry, ?_, I.bd _ _ ly⟩
  · simp only [WinCfg.lazyBounds, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl
    · exact ⟨I.sl _ _ lx, I.bd _ _ lx, I.val _ _ lx⟩
    · exact ⟨I.sl _ _ ly, (I.bd _ _ ly).mono (j := 2) (by decide) (by decide), I.val _ _ ly⟩
    · exact ⟨I.sl _ _ lz, I.bd _ _ lz, I.val _ _ lz⟩
  · exact InvJ.dbl' hC hM3 hQ hJ (by rw [rx, rz])

/-- A program over `rcbW`'s slots, as the loop's frame. -/
theorem progKeep_next {o : Pt} (ho : ∀ x ∈ [o.x, o.y, o.z], x ∈ winOther K) (hL : WinLay K size)
    {Rp : Fe C → Fe C → Fe C → Point C → Prop} {P : Point C} {s₀ s t : State}
    (hS : WinStR K C base size Rp P s₀ s) (k : ProgKeep K.M base (rcbW K.S o) s t) :
    WinStR K C base size Rp P s₀ t ∧ KeepRegs (clob K.M.n) s t ∧ Unch base (loopW K) s.mem t.mem := by
  obtain w := winJ_sl ho (fun x hx => winOther_mem (ho x hx)) (fun x hx => winOther_mem (ho x hx))
  have kr : KeepRegs (clob K.M.n) s t := ⟨k.gpr, k.rd, k.wr⟩
  have U : Unch base (loopW K) s.mem t.mem := k.unch.mono fun v hv => by
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hv ⊢
    rcases hv with ⟨y, hy, rfl⟩ | rfl
    · exact Or.inl ⟨y, w.2 y hy, rfl⟩
    · exact Or.inr rfl
  exact ⟨hS.next hL (k.scr hS.scr) (kr.mono clob_powClob) U, kr, U⟩

/-- A Jacobian point doubled: `H = 2Y`. -/
theorem hdbl_check (K : WinCfg) (a b : Nat) : check [(K.R.y, 0), (K.R.x, a), (K.R.z, b)] [.add K.R.y K.R.y K.R.y] =
    some [(K.R.y, 2), (K.R.y, 0), (K.R.x, a), (K.R.z, b)] := by
  simp [check, step]

/-- `quadLazy`: `R = 16 R` (`quadJ_ok`). -/
theorem quadLazy_ok (hz : WinCfg.lazyOk K = true) (hL : WinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n)))
    (hC : Law C) (hM3 : AM3 C) {P : Point C} {k : Nat}
    (hP : onCurve C P = true) {Rp : Fe C → Fe C → Fe C → Point C → Prop} {s₀ s : State}
    (hF : WinFixed K C base s₀ P k) (hS : WinStR K C base size Rp P s₀ s) {i : Nat} (hi : i < 4096)
    (hb : s.gpr .rbx = BitVec.ofNat 64 i) {e : Nat}
    (hlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
      (mul e P)) :
    WP isa (WinCfg.quadLazy K).inline s fun s' =>
      WinStR K C base size Rp P s₀ s' ∧ s'.gpr .rbx = s.gpr .rbx ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      InvJ C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (mul (16 * e) P) := by
  obtain ⟨hnd, hn9, hred, ht, -, -⟩ := lazyOk_spec hz
  have hp9 : C.p + 1 = 512 * (2 ^ 64) ^ 8 := (p521_of_red hred hS.mod.red).2
  obtain oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  have sR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winSlots K := fun x hx => winOther_mem (oR x hx)
  have oQ := fun (a : Nat) => hC.onCurve_mul hP a
  have rW : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ rcbW K.S K.R := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbW]
  have hne := nodup_dbl hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hne
  obtain ⟨-, -, -, -, ⟨hxy, hxz⟩, hyz, -⟩ := hne
  rw [WinCfg.quadLazy]
  simp only [Code.inline]
  -- `H = 2Y`.
  have I₀ : LInv K.M base size C.p (· ∈ winSlots K) [(K.R.y, 0), (K.R.x, 0), (K.R.z, 0)] (tmv C K.M.n base s) s :=
    LInv.of_mem hS.scr hS.mod fun p hp' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl
      · exact ⟨sR _ (by simp), Bd.of_lt (hlt _ (by simp)), rfl⟩
      · exact ⟨sR _ (by simp), Bd.of_lt (hlt _ (by simp)), rfl⟩
      · exact ⟨sR _ (by simp), Bd.of_lt (hlt _ (by simp)), rfl⟩
  refine WP.seq (WP.mono (prog_ok hL.lay hp hred ht _ I₀ (fun op hop => by
    simp only [List.mem_singleton] at hop; subst hop; exact sR _ (by simp [LOp.out])) (hdbl_check K 0 0))
    fun s₁ ⟨k₁, I₁⟩ => ?_)
  obtain ⟨S₁, kr₁, -⟩ := progKeep_next oR hL hS (k₁.mono (W' := rcbW K.S K.R) fun x hx => by
    simp only [List.map_cons, List.map_nil, LOp.out, List.mem_singleton] at hx; subst hx; exact rW _ (by simp))
  have b₁ : s₁.gpr .rbx = BitVec.ofNat 64 i := by rw [kr₁.gpr _ (rbx_not_clob _), hb]
  have E₁ : ∀ x, x ≠ K.R.y → runs [.add K.R.y K.R.y K.R.y] (tmv C K.M.n base s) x = tmv C K.M.n base s x := fun x hx => by
    simp only [runs, List.foldl, run, Function.update_of_ne hx]
  have E₁y : runs [.add K.R.y K.R.y K.R.y] (tmv C K.M.n base s) K.R.y =
      tmv C K.M.n base s K.R.y + tmv C K.M.n base s K.R.y := by
    simp only [runs, List.foldl, run, Function.update_self]
  generalize hE₁ : runs [.add K.R.y K.R.y K.R.y] (tmv C K.M.n base s) = F₁ at I₁ E₁ E₁y
  have J₁ : LInv K.M base size C.p (· ∈ winSlots K) (WinCfg.lazyBounds K) F₁ s₁ :=
    LInv.of_mem I₁.scr I₁.mod fun p hp' => by
      have hlx : List.lookup K.R.x [(K.R.y, 2), (K.R.y, 0), (K.R.x, 0), (K.R.z, 0)] = some 0 := by
        simp [List.lookup_cons, beq_eq_false_iff_ne.mpr hxy]
      have hlz : List.lookup K.R.z [(K.R.y, 2), (K.R.y, 0), (K.R.x, 0), (K.R.z, 0)] = some 0 := by
        simp [List.lookup_cons, beq_eq_false_iff_ne.mpr (Ne.symm hyz), beq_eq_false_iff_ne.mpr (Ne.symm hxz)]
      have hly : List.lookup K.R.y [(K.R.y, 2), (K.R.y, 0), (K.R.x, 0), (K.R.z, 0)] = some 2 := by
        simp
      simp only [WinCfg.lazyBounds, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl
      · exact ⟨sR _ (by simp), (I₁.bd _ _ hlx).mono (j := 1) (by decide) (by decide), I₁.val _ _ hlx⟩
      · exact ⟨sR _ (by simp), I₁.bd _ _ hly, I₁.val _ _ hly⟩
      · exact ⟨sR _ (by simp), I₁.bd _ _ hlz, I₁.val _ _ hlz⟩
  -- The doublings.
  refine WP.seq (WP.mono (quadStart_ok s₁ b₁) fun s₂ ⟨b₂, kc₂⟩ => ?_)
  have lk : ∀ {E : Nat → Fe C} {t t' : State}, LInv K.M base size C.p (· ∈ winSlots K) (WinCfg.lazyBounds K) E t →
      Keeps [.rbx] t t' → LInv K.M base size C.p (· ∈ winSlots K) (WinCfg.lazyBounds K) E t' := fun I k =>
    ⟨I.scr.of_keeps k (by decide), by rw [k.2.1]; exact I.mod, I.sl, by rw [k.2.1]; exact I.bd, by rw [k.2.1]; exact I.val⟩
  let LI := fun j st => WinStR K C base size Rp P s₀ st ∧
    st.gpr .rbx = BitVec.ofNat 64 (i + 4096 * j) ∧ ∃ (E : Nat → Fe C) (Y : Fe C),
    LInv K.M base size C.p (· ∈ winSlots K) (WinCfg.lazyBounds K) E st ∧ E K.R.y = Y + Y ∧
    InvJ C (E K.R.x) Y (E K.R.z) (mul (4 ^ (2 - j) * e) P) ∧ (j < 2 → Bd C.p 1 (wordsVal st.mem base K.R.y K.M.n))
  obtain start : LI 2 s₂ := ⟨S₁.rbxKeeps hL kc₂, b₂, F₁, _, lk J₁ kc₂, E₁y, by
    rw [E₁ _ hxy, E₁ _ (Ne.symm hyz)]; simpa using hR, fun h => absurd h (by decide)⟩
  obtain body : ∀ j st, 1 ≤ j → j ≤ 2 → LI j st →
      WP isa (WinCfg.lazyPair K).inline st fun st' => LI (j - 1) st' ∧ st'.cf = some (decide (j - 1 = 0)) := by
    intro j st hj hj' ⟨S, b, E, Y, I, hY, J, _⟩
    simp only [WinCfg.lazyPair, Code.inline]
    refine WP.seq (WP.mono (dblLazy_ok hz hL hp hC hM3 I hY (oQ _) J) fun st₁ ⟨k₁', E', Y', I', hY', J', _⟩ => ?_)
    obtain ⟨S', kr', -⟩ := progKeep_next oR hL S k₁'
    rw [hC.double hP] at J'
    refine WP.seq (WP.mono (dblLazy_ok hz hL hp hC hM3 I' hY' (oQ _) J') fun st₂ ⟨k₂', E'', Y'', I'', hY'', J'', B''⟩ => ?_)
    obtain ⟨S'', kr'', -⟩ := progKeep_next oR hL S' k₂'
    rw [hC.double hP] at J''
    obtain ar : 2 * (2 * (4 ^ (2 - j) * e)) = 4 ^ (2 - (j - 1)) * e := by
      obtain hj12 : j = 1 ∨ j = 2 := by omega_using [hj, hj']
      rcases hj12 with rfl | rfl <;> simp <;> omega_using []
    rw [ar] at J''
    obtain b' : st₂.gpr .rbx = BitVec.ofNat 64 (i + 4096 * j) := by
      rw [kr''.gpr _ (rbx_not_clob _), kr'.gpr _ (rbx_not_clob _), b]
    refine WP.mono (quadCount_ok st₂ hi hj hj' b') fun st₃ ⟨b₃, c₃, kc₃⟩ => ?_
    exact ⟨⟨S''.rbxKeeps hL kc₃, b₃, E'', Y'', lk I'' kc₃, hY'', J'', fun _ => by rw [kc₃.2.1]; exact B''⟩, c₃⟩
  refine WP.seq (WP.mono (quadLoop_ok body (fun _ h => h) start) fun s₅ ⟨S₅, b₅, E₅, Y₅, I₅, hY₅, J₅, B₅⟩ => ?_)
  obtain rb₅ : s₅.gpr .rbx = s.gpr .rbx := by simpa only [Nat.mul_zero, Nat.add_zero, hb] using b₅
  replace J₅ : InvJ C (E₅ K.R.x) Y₅ (E₅ K.R.z) (mul (16 * e) P) := by simpa using J₅
  replace B₅ := B₅ (by decide)
  -- `Y = H / 2`, and `X` and `Y` canonical.
  obtain ⟨-, -, ro_lt, ro_z⟩ := S₅.ro_tmv hL hF
  have lx₅ : List.lookup K.R.x (WinCfg.lazyBounds K) = some 1 := by simp [WinCfg.lazyBounds]
  have ly₅ : List.lookup K.R.y (WinCfg.lazyBounds K) = some 2 := by
    simp [WinCfg.lazyBounds, List.lookup_cons, beq_eq_false_iff_ne.mpr (Ne.symm hxy)]
  have lz₅ : List.lookup K.R.z (WinCfg.lazyBounds K) = some 0 := by
    simp [WinCfg.lazyBounds, List.lookup_cons, beq_eq_false_iff_ne.mpr (Ne.symm hxz), beq_eq_false_iff_ne.mpr (Ne.symm hyz)]
  have zW : K.zero ∈ winRo K := by simp [winRo]
  obtain ⟨zx, zy⟩ := nodup_zero hnd
  have I₆ : LInv K.M base size C.p (· ∈ winSlots K) [(K.R.y, 1), (K.R.x, 1), (K.zero, 0)] (tmv C K.M.n base s₅) s₅ :=
    LInv.of_mem S₅.scr S₅.mod fun p hp' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl
      · exact ⟨sR _ (by simp), B₅, rfl⟩
      · exact ⟨sR _ (by simp), I₅.bd _ _ lx₅, rfl⟩
      · exact ⟨by win_mem, Bd.of_lt (ro_lt _ zW), rfl⟩
  have hc₆ : check [(K.R.y, 1), (K.R.x, 1), (K.zero, 0)]
      [.half K.R.y K.R.y, .cadd K.R.y K.R.y K.zero, .cadd K.R.x K.R.x K.zero] =
      some [(K.R.x, 0), (K.R.y, 0), (K.R.y, 1), (K.R.y, 1), (K.R.x, 1), (K.zero, 0)] := by
    simp [check, step, List.lookup_cons, beq_eq_false_iff_ne.mpr zx, beq_eq_false_iff_ne.mpr zy,
      beq_eq_false_iff_ne.mpr hxy]
  refine WP.mono (prog_ok hL.lay hp hred ht _ I₆ (fun op hop => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl <;> exact sR _ (by simp [LOp.out])) hc₆) fun s₇ ⟨k₇, I₇⟩ => ?_
  have outs : ∀ x ∈ ([.half K.R.y K.R.y, .cadd K.R.y K.R.y K.zero, .cadd K.R.x K.R.x K.zero] : List LOp).map LOp.out,
      x = K.R.y ∨ x = K.R.x := by
    intro x hx
    simp only [List.map_cons, List.map_nil, LOp.out, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨S₇, kr₇, -⟩ := progKeep_next oR hL S₅ (k₇.mono (W' := rcbW K.S K.R) fun x hx => by
    rcases outs x hx with rfl | rfl <;> exact rW _ (by simp))
  have lx₇ : List.lookup K.R.x [(K.R.x, 0), (K.R.y, 0), (K.R.y, 1), (K.R.y, 1), (K.R.x, 1), (K.zero, 0)] = some 0 := by
    simp
  have ly₇ : List.lookup K.R.y [(K.R.x, 0), (K.R.y, 0), (K.R.y, 1), (K.R.y, 1), (K.R.x, 1), (K.zero, 0)] = some 0 := by
    simp [List.lookup_cons, beq_eq_false_iff_ne.mpr (Ne.symm hxy)]
  have zv : tmv C K.M.n base s₅ K.zero = 0 := by
    show toM _ _ (wordsVal _ _ _ _) = 0
    rw [ro_z]; exact toM_zero _ _
  have z₇ : wordsVal s₇.mem base K.R.z K.M.n = wordsVal s₅.mem base K.R.z K.M.n :=
    progKeep_wordsVal hL.lay hS.scr.nowrap k₇ (fun x hx => by
      rcases outs x hx with rfl | rfl <;> exact sR _ (by simp)) (sR _ (by simp)) (fun h => by
      rcases outs _ h with h | h
      · exact hyz h.symm
      · exact hxz h.symm)
  have hx : tmv C K.M.n base s₇ K.R.x = E₅ K.R.x := by
    show toM _ _ _ = _
    rw [I₇.val _ _ lx₇]
    simp only [runs, List.foldl, run, Function.update_apply, hxy, zy, ite_true, ite_false]
    rw [zv]
    have : tmv C K.M.n base s₅ K.R.x = E₅ K.R.x := I₅.val _ _ lx₅
    rw [this]; grind
  have hy : tmv C K.M.n base s₇ K.R.y = Y₅ := by
    show toM _ _ _ = _
    rw [I₇.val _ _ ly₇]
    simp only [runs, List.foldl, run, Function.update_apply, hxy, zy, Ne.symm hxy, ite_true, ite_false]
    rw [zv]
    have h1 : tmv C K.M.n base s₅ K.R.y = E₅ K.R.y := I₅.val _ _ ly₅
    have h2 := halfF_two hp9
    rw [h1, hY₅]
    grind
  have hzz : tmv C K.M.n base s₇ K.R.z = E₅ K.R.z := by
    show toM _ _ _ = _
    rw [z₇]; exact I₅.val _ _ lz₅
  refine ⟨S₇, by rw [kr₇.gpr _ (rbx_not_clob _), rb₅], fun x hx => ?_, by rw [hx, hy, hzz]; exact J₅⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact (I₇.bd _ _ lx₇).lt
  · exact (I₇.bd _ _ ly₇).lt
  · rw [z₇]; exact (I₅.bd _ _ lz₅).lt

/-- The mixed addition's formula. -/
theorem madd_run {m : Nat} [NeZero m] (S : RcbSlots) (p q o : Pt) (E : Nat → Fin m) {w : Nat}
    (hd : [S.t0, S.t1, S.t2, S.t3, S.t4, S.t5, p.x, p.y, p.z, q.x, q.y, o.x, o.y, o.z, w].Nodup) :
    (runs (maddOps S p q o) E o.x, runs (maddOps S p q o) E o.y, runs (maddOps S p q o) E o.z) =
      maddJF (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h0_1, h0_2, h0_3, h0_4, h0_5, h0_6, h0_7, h0_8, h0_9, h0_10, h0_11, h0_12, h0_13, h0_14⟩, ⟨h1_2, h1_3, h1_4, h1_5, h1_6, h1_7, h1_8, h1_9, h1_10, h1_11, h1_12, h1_13, h1_14⟩, ⟨h2_3, h2_4, h2_5, h2_6, h2_7, h2_8, h2_9, h2_10, h2_11, h2_12, h2_13, h2_14⟩, ⟨h3_4, h3_5, h3_6, h3_7, h3_8, h3_9, h3_10, h3_11, h3_12, h3_13, h3_14⟩, ⟨h4_5, h4_6, h4_7, h4_8, h4_9, h4_10, h4_11, h4_12, h4_13, h4_14⟩, ⟨h5_6, h5_7, h5_8, h5_9, h5_10, h5_11, h5_12, h5_13, h5_14⟩, ⟨h6_7, h6_8, h6_9, h6_10, h6_11, h6_12, h6_13, h6_14⟩, ⟨h7_8, h7_9, h7_10, h7_11, h7_12, h7_13, h7_14⟩, ⟨h8_9, h8_10, h8_11, h8_12, h8_13, h8_14⟩, ⟨h9_10, h9_11, h9_12, h9_13, h9_14⟩, ⟨h10_11, h10_12, h10_13, h10_14⟩, ⟨h11_12, h11_13, h11_14⟩, ⟨h12_13, h12_14⟩, -⟩ := hd
  have s1_0 := Ne.symm h0_1
  have s2_0 := Ne.symm h0_2
  have s3_0 := Ne.symm h0_3
  have s4_0 := Ne.symm h0_4
  have s5_0 := Ne.symm h0_5
  have s6_0 := Ne.symm h0_6
  have s7_0 := Ne.symm h0_7
  have s8_0 := Ne.symm h0_8
  have s9_0 := Ne.symm h0_9
  have s10_0 := Ne.symm h0_10
  have s11_0 := Ne.symm h0_11
  have s12_0 := Ne.symm h0_12
  have s13_0 := Ne.symm h0_13
  have s2_1 := Ne.symm h1_2
  have s3_1 := Ne.symm h1_3
  have s4_1 := Ne.symm h1_4
  have s5_1 := Ne.symm h1_5
  have s6_1 := Ne.symm h1_6
  have s7_1 := Ne.symm h1_7
  have s8_1 := Ne.symm h1_8
  have s9_1 := Ne.symm h1_9
  have s10_1 := Ne.symm h1_10
  have s11_1 := Ne.symm h1_11
  have s12_1 := Ne.symm h1_12
  have s13_1 := Ne.symm h1_13
  have s3_2 := Ne.symm h2_3
  have s4_2 := Ne.symm h2_4
  have s5_2 := Ne.symm h2_5
  have s6_2 := Ne.symm h2_6
  have s7_2 := Ne.symm h2_7
  have s8_2 := Ne.symm h2_8
  have s9_2 := Ne.symm h2_9
  have s10_2 := Ne.symm h2_10
  have s11_2 := Ne.symm h2_11
  have s12_2 := Ne.symm h2_12
  have s13_2 := Ne.symm h2_13
  have s4_3 := Ne.symm h3_4
  have s5_3 := Ne.symm h3_5
  have s6_3 := Ne.symm h3_6
  have s7_3 := Ne.symm h3_7
  have s8_3 := Ne.symm h3_8
  have s9_3 := Ne.symm h3_9
  have s10_3 := Ne.symm h3_10
  have s11_3 := Ne.symm h3_11
  have s12_3 := Ne.symm h3_12
  have s13_3 := Ne.symm h3_13
  have s5_4 := Ne.symm h4_5
  have s6_4 := Ne.symm h4_6
  have s7_4 := Ne.symm h4_7
  have s8_4 := Ne.symm h4_8
  have s9_4 := Ne.symm h4_9
  have s10_4 := Ne.symm h4_10
  have s11_4 := Ne.symm h4_11
  have s12_4 := Ne.symm h4_12
  have s13_4 := Ne.symm h4_13
  have s6_5 := Ne.symm h5_6
  have s7_5 := Ne.symm h5_7
  have s8_5 := Ne.symm h5_8
  have s9_5 := Ne.symm h5_9
  have s10_5 := Ne.symm h5_10
  have s11_5 := Ne.symm h5_11
  have s12_5 := Ne.symm h5_12
  have s13_5 := Ne.symm h5_13
  have s12_11 := Ne.symm h11_12
  have s13_11 := Ne.symm h11_13
  have s13_12 := Ne.symm h12_13
  simp only [maddOps, runs, List.foldl, run, Function.update_apply, maddJF, *, ite_true, ite_false]

/-- The lazy mixed addition into `D`. -/
theorem maddLazy_ok (hz : WinCfg.lazyOk K = true) (hL : WinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n)))
    {s : State} (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base)
    (hltR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hltE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s.mem base x K.M.n < C.p) :
    WP isa (prog K.M (maddOps K.S K.R K.E K.D)).inline s fun t => ProgKeep K.M base (rcbW K.S K.D) s t ∧
      (∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal t.mem base x K.M.n < C.p) ∧
      (tmv C K.M.n base t K.D.x, tmv C K.M.n base t K.D.y, tmv C K.M.n base t K.D.z) =
        maddJF (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
          (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) := by
  obtain ⟨hnd, -, hred, ht, -, L, hc, lx, ly, lz⟩ := lazyOk_spec hz
  obtain oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  obtain oE := pt_other (K := K) (p := K.E) (Or.inr (Or.inl rfl))
  obtain oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  obtain w := winJ_sl oD (fun x hx => winOther_mem (oR x hx)) (fun x hx => winOther_mem (oE x hx))
  have I₀ : LInv K.M base size C.p (· ∈ winSlots K) (WinCfg.lazyAddBounds K) (tmv C K.M.n base s) s :=
    LInv.of_mem hs hM fun p hp' => by
      simp only [WinCfg.lazyAddBounds, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl
      · exact ⟨winOther_mem (oR _ (by simp)), Bd.of_lt (hltR _ (by simp)), rfl⟩
      · exact ⟨winOther_mem (oR _ (by simp)), Bd.of_lt (hltR _ (by simp)), rfl⟩
      · exact ⟨winOther_mem (oR _ (by simp)), Bd.of_lt (hltR _ (by simp)), rfl⟩
      · exact ⟨winOther_mem (oE _ (by simp)), Bd.of_lt (hltE _ (by simp)), rfl⟩
      · exact ⟨winOther_mem (oE _ (by simp)), Bd.of_lt (hltE _ (by simp)), rfl⟩
  refine WP.mono (prog_ok hL.lay hp hred ht _ I₀ (fun op hop => w.1 _ (List.mem_append_left _
    (madd_outs _ _ _ _ _ (List.mem_map_of_mem hop)))) hc) fun t ⟨k, I⟩ => ⟨k.mono (madd_outs _ _ _ _), fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact (I.bd _ _ lx).lt
    · exact (I.bd _ _ ly).lt
    · exact (I.bd _ _ lz).lt
  · refine Eq.trans ?_ (madd_run K.S K.R K.E K.D (tmv C K.M.n base s) hnd)
    show (toM _ _ _, toM _ _ _, toM _ _ _) = _
    rw [I.val _ _ lx, I.val _ _ ly, I.val _ _ lz]

end

end VG.Proof.Weierstrass.X86_64.LazyP521
