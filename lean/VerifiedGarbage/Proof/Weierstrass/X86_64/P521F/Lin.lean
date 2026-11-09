module
-- separate module: the P-521 fast window's proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Weierstrass.X86_64.P521F.Red
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-!
# P-521 on x86-64: the sum and the difference (`sAdd`, `sSub`)

s2n-bignum's `add_p521` and `sub_p521` (`Impl/Weierstrass/X86_64/P521Fast.lean`):
the operands' words into registers through one carry chain (`ldOp_adc_ok`,
`ldOp_sub_ok`), then the correction through the borrow, each word stored
once final (`sbbSt_ok`): `[o] = ([a] + [b]) mod p` (`sAdd_ok`) and
`[o] = ([a] - [b]) mod p` (`sSub_ok`) for `[a]`, `[b]` below `p`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.P521F

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64.P521F
open VG.Impl.Weierstrass.X86_64.Mont (fnTmp)
open VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono sub_borrow sbb_borrow adc_carry)

variable {Z : Nat}

/-! ## Steps -/

theorem subS_ok (s : State) (x : Reg) {src : Src} {v : BitVec 64} (hsrc : readSrc s src = some v) :
    WP isa (.block [.alu .sub x src]) s fun s' => ∃ c', s'.cf = some c' ∧
      (s'.gpr x).toNat + v.toNat = (s.gpr x).toNat + 2 ^ 64 * c'.toNat ∧ Keeps [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, hsrc, Option.bind_some,
    RegUpd.gpr_setReg_self, RegUpd.cf_setReg, RegUpd.cf_arithFlags, Option.some.injEq, exists_eq_left']
  refine ⟨sub_borrow _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

theorem sbbS_ok (s : State) (x : Reg) {src : Src} {v : BitVec 64} (hsrc : readSrc s src = some v)
    {c : Bool} (hc : s.cf = some c) :
    WP isa (.block [.alu .sbb x src]) s fun s' => ∃ c', s'.cf = some c' ∧
      (s'.gpr x).toNat + v.toNat + c.toNat = (s.gpr x).toNat + 2 ^ 64 * c'.toNat ∧ Keeps [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, hsrc, Option.bind_some,
    Option.map_some, hc, RegUpd.gpr_setReg_self, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
    Option.some.injEq, exists_eq_left']
  refine ⟨sbb_borrow _ _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

theorem pair_append (x y : Instr) (l : List Instr) : [x, y] ++ l = [x] ++ ([y] ++ l) := rfl

theorem imm0_toNat : ((0 : BitVec 32).signExtend 64).toNat = 0 := by decide

/-- The registers `ts`: not `rdi`, distinct. -/
def LinRegs (ts : List Reg) : Prop := ts.Nodup ∧ ∀ t ∈ ts, t ≠ .rdi

theorem LinRegs.tail {t : Reg} {ts : List Reg} (h : LinRegs (t :: ts)) : LinRegs ts :=
  ⟨(List.nodup_cons.mp h.1).2, fun q hq => h.2 q (List.mem_cons_of_mem _ hq)⟩


theorem two_pow_and (x k : Nat) : 2 ^ k &&& x = 2 ^ k * (x / 2 ^ k % 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ k) with h | h
  · rw [h, Nat.mul_zero, Nat.zero_testBit]
    by_cases hi : k = i
    · subst hi; simp [Nat.testBit, Nat.shiftRight_eq_div_pow, h]
    · simp [hi]
  · rw [h, Nat.mul_one, Nat.testBit_two_pow]
    by_cases hi : k = i
    · subst hi; simp [Nat.testBit, Nat.shiftRight_eq_div_pow, h]
    · simp [hi]

/-- `rdx = 512 ⌊r14 / 512⌋`, CF set when that is zero, for `r14 < 1024`. -/
theorem selTop_ok (s : State) (ht : (s.gpr .r14).toNat < 1024) :
    WP isa (.block [.mov32 .rdx (.imm 512), .alu .and .rdx (.reg .r14), .alu .cmp .rdx (.imm 512)]) s
      fun s' => (s'.gpr .rdx).toNat = 512 * ((s.gpr .r14).toNat / 512) ∧
        s'.cf = some (decide ((s.gpr .r14).toNat < 512)) ∧ Keeps [.rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, Option.bind_some,
    Option.map_some, State.setReg32, RegUpd.gpr_setReg_self, RegUpd.cf_arithFlags,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_arithFlags,
    RegUpd.gpr_setReg_of_ne _ _ (show Reg.r14 ≠ Reg.rdx by decide)]
  have hv : (BitVec.setWidth 64 (512 : BitVec 32) &&& s.gpr .r14).toNat = 512 * ((s.gpr .r14).toNat / 512) := by
    rw [BitVec.toNat_and, show (BitVec.setWidth 64 (512 : BitVec 32)).toNat = 2 ^ 9 from rfl, two_pow_and]
    omega
  rw [hv, show (BitVec.signExtend 64 (512 : BitVec 32)).toNat = 512 by decide]
  refine ⟨rfl, by simp only [decide_eq_decide]; omega, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr]

/-! ## The chains -/

/-- `ldOp .adc .adc ts a b`: `[a] + [b] + c` into `ts`. -/
theorem ldOp_adc_ok (hZ : 4096 ≤ Z) : ∀ (ts : List Reg) {s : State} {base : Addr} {a b : Nat} {c : Bool},
    Scr s base Z → LinRegs ts → a + 8 * ts.length ≤ 4096 → b + 8 * ts.length ≤ 4096 → s.cf = some c →
    WP isa (.block (ldOp .adc .adc ts a b)) s fun s' => ∃ c', s'.cf = some c' ∧
      regsVal s' ts + 2 ^ (64 * ts.length) * c'.toNat =
        wordsVal s.mem base a ts.length + wordsVal s.mem base b ts.length + c.toNat ∧ Keeps ts s s'
  | [], s, _, _, _, c, _, _, _, _, hc => WP.block_nil ⟨c, hc, by simp [regsVal, wordsVal], fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, a, b, c, hs, hr, ha, hb, hc => by
    simp only [List.length_cons] at ha hb
    obtain ⟨htn, htr⟩ := List.nodup_cons.mp hr.1
    have ht := hr.2 t (List.mem_cons_self ..)
    rw [ldOp, pair_append, WP.block_append_iff]
    refine WP.mono (movR_ok s t (sc_ok hZ hs (d := a) (by omega))) fun s₁ ⟨r₁, cf₁, _, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by simpa using ht.symm)
    rw [WP.block_append_iff]
    refine WP.mono (adcS_ok s₁ t (sc_ok hZ hs₁ (d := b) (by omega)) (cf₁.trans hc)) fun s₂ ⟨c₂, cf₂, e₂, k₂⟩ => ?_
    have hs₂ := hs₁.of_keeps k₂ (by simpa using ht.symm)
    refine WP.mono (ldOp_adc_ok hZ ts hs₂ hr.tail (a := a + 8) (b := b + 8) (by omega) (by omega) cf₂)
      fun s₃ ⟨c₃, cf₃, e₃, k₃⟩ => ⟨c₃, cf₃, ?_, ?_⟩
    · have hm : s₂.mem = s.mem := k₂.2.1.trans k₁.2.1
      have hx : s₃.gpr t = s₂.gpr t := k₃.1 t htn
      rw [hm] at e₃
      rw [r₁, k₁.2.1] at e₂
      simp only [regsVal, wordsVal, List.length_cons, hx]
      rw [pow64_succ]
      rw [show 2 ^ 64 * 2 ^ (64 * ts.length) * c₃.toNat = 2 ^ 64 * (2 ^ (64 * ts.length) * c₃.toNat) by
        rw [Nat.mul_assoc]]
      omega
    · exact (k₁.mono (by simp)).trans ((k₂.mono (by simp)).trans (k₃.mono fun r h => List.mem_cons_of_mem _ h))

/-- `ldOp .sub .sbb ts a b`: `[a] - [b]` into `ts`, the borrow out. -/
theorem ldOp_sbb_ok (hZ : 4096 ≤ Z) : ∀ (ts : List Reg) {s : State} {base : Addr} {a b : Nat} {c : Bool},
    Scr s base Z → LinRegs ts → a + 8 * ts.length ≤ 4096 → b + 8 * ts.length ≤ 4096 → s.cf = some c →
    WP isa (.block (ldOp .sbb .sbb ts a b)) s fun s' => ∃ c', s'.cf = some c' ∧
      regsVal s' ts + wordsVal s.mem base b ts.length + c.toNat =
        wordsVal s.mem base a ts.length + 2 ^ (64 * ts.length) * c'.toNat ∧ Keeps ts s s'
  | [], s, _, _, _, c, _, _, _, _, hc => WP.block_nil ⟨c, hc, by simp [regsVal, wordsVal], fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, a, b, c, hs, hr, ha, hb, hc => by
    simp only [List.length_cons] at ha hb
    obtain ⟨htn, htr⟩ := List.nodup_cons.mp hr.1
    have ht := hr.2 t (List.mem_cons_self ..)
    rw [ldOp, pair_append, WP.block_append_iff]
    refine WP.mono (movR_ok s t (sc_ok hZ hs (d := a) (by omega))) fun s₁ ⟨r₁, cf₁, _, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by simpa using ht.symm)
    rw [WP.block_append_iff]
    refine WP.mono (sbbS_ok s₁ t (sc_ok hZ hs₁ (d := b) (by omega)) (cf₁.trans hc)) fun s₂ ⟨c₂, cf₂, e₂, k₂⟩ => ?_
    have hs₂ := hs₁.of_keeps k₂ (by simpa using ht.symm)
    refine WP.mono (ldOp_sbb_ok hZ ts hs₂ hr.tail (a := a + 8) (b := b + 8) (by omega) (by omega) cf₂)
      fun s₃ ⟨c₃, cf₃, e₃, k₃⟩ => ⟨c₃, cf₃, ?_, ?_⟩
    · have hm : s₂.mem = s.mem := k₂.2.1.trans k₁.2.1
      have hx : s₃.gpr t = s₂.gpr t := k₃.1 t htn
      rw [hm] at e₃
      rw [r₁, k₁.2.1] at e₂
      simp only [regsVal, wordsVal, List.length_cons, hx]
      rw [pow64_succ]
      rw [show 2 ^ 64 * 2 ^ (64 * ts.length) * c₃.toNat = 2 ^ 64 * (2 ^ (64 * ts.length) * c₃.toNat) by
        rw [Nat.mul_assoc]]
      omega
    · exact (k₁.mono (by simp)).trans ((k₂.mono (by simp)).trans (k₃.mono fun r h => List.mem_cons_of_mem _ h))

/-- `sub` then `sbb`: `ldOp .sub .sbb` is `ldOp .sbb .sbb` from CF clear. -/
theorem ldOp_sub_ok (hZ : 4096 ≤ Z) {t : Reg} {ts : List Reg} {s : State} {base : Addr} {a b : Nat}
    (hs : Scr s base Z) (hr : LinRegs (t :: ts)) (ha : a + 8 * (ts.length + 1) ≤ 4096)
    (hb : b + 8 * (ts.length + 1) ≤ 4096) :
    WP isa (.block (ldOp .sub .sbb (t :: ts) a b)) s fun s' => ∃ c', s'.cf = some c' ∧
      regsVal s' (t :: ts) + wordsVal s.mem base b (ts.length + 1) =
        wordsVal s.mem base a (ts.length + 1) + 2 ^ (64 * (ts.length + 1)) * c'.toNat ∧ Keeps (t :: ts) s s' := by
  obtain ⟨htn, htr⟩ := List.nodup_cons.mp hr.1
  have ht := hr.2 t (List.mem_cons_self ..)
  rw [ldOp, pair_append, WP.block_append_iff]
  refine WP.mono (movR_ok s t (sc_ok hZ hs (d := a) (by omega))) fun s₁ ⟨r₁, cf₁, _, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by simpa using ht.symm)
  rw [WP.block_append_iff]
  refine WP.mono (subS_ok s₁ t (sc_ok hZ hs₁ (d := b) (by omega))) fun s₂ ⟨c₂, cf₂, e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by simpa using ht.symm)
  refine WP.mono (ldOp_sbb_ok hZ ts hs₂ hr.tail (a := a + 8) (b := b + 8) (by omega) (by omega) cf₂)
    fun s₃ ⟨c₃, cf₃, e₃, k₃⟩ => ⟨c₃, cf₃, ?_, ?_⟩
  · have hm : s₂.mem = s.mem := k₂.2.1.trans k₁.2.1
    have hx : s₃.gpr t = s₂.gpr t := k₃.1 t htn
    rw [hm] at e₃
    rw [r₁, k₁.2.1] at e₂
    simp only [regsVal, wordsVal, hx]
    rw [pow64_succ]
    rw [show 2 ^ 64 * 2 ^ (64 * ts.length) * c₃.toNat = 2 ^ 64 * (2 ^ (64 * ts.length) * c₃.toNat) by
      rw [Nat.mul_assoc]]
    omega
  · exact (k₁.mono (by simp)).trans ((k₂.mono (by simp)).trans (k₃.mono fun r h => List.mem_cons_of_mem _ h))

/-- `sbbSt ts o`: the borrow `c` taken from `ts`, each word stored at `[o + 8k]`. -/
theorem sbbSt_ok (hZ : 4096 ≤ Z) : ∀ (ts : List Reg) {s : State} {base : Addr} {o : Nat} {c : Bool},
    Scr s base Z → LinRegs ts → o + 8 * ts.length ≤ 4096 → s.cf = some c →
    WP isa (.block (sbbSt ts o)) s fun s' => ∃ c', s'.cf = some c' ∧
      wordsVal s'.mem base o ts.length + c.toNat = regsVal s ts + 2 ^ (64 * ts.length) * c'.toNat ∧
      regsVal s' ts = wordsVal s'.mem base o ts.length ∧ KeepRegs ts s s' ∧
      Outside base o (8 * ts.length) s.mem s'.mem
  | [], s, _, _, c, _, _, _, hc => WP.block_nil ⟨c, hc, by simp [regsVal, wordsVal], by simp [regsVal, wordsVal],
      ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | t :: ts, s, base, o, c, hs, hr, ho, hc => by
    have hnw := hs.nowrap
    simp only [List.length_cons] at ho
    obtain ⟨htn, htr⟩ := List.nodup_cons.mp hr.1
    have ht := hr.2 t (List.mem_cons_self ..)
    rw [sbbSt, pair_append, WP.block_append_iff]
    refine WP.mono (sbbS_ok s t (src := .imm 0) (v := (0 : BitVec 32).signExtend 64) rfl hc)
      fun s₁ ⟨c₁, cf₁, e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by simpa using ht.symm)
    rw [WP.block_append_iff]
    refine WP.mono (storeX_ok hs₁ t (d := o) (by omega)) fun s₂ ⟨m₂, g₂, cf₂, _, rd₂, wr₂⟩ => ?_
    have hs₂ : Scr s₂ base Z := ⟨by rw [g₂]; exact hs₁.rdi, by rw [wr₂]; exact hs₁.wr, hnw⟩
    have O₂ : Outside base o 8 s.mem s₂.mem := by rw [m₂, k₁.2.1]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (sbbSt_ok hZ ts hs₂ hr.tail (o := o + 8) (by omega) (cf₂.trans cf₁))
      fun s₃ ⟨c₃, cf₃, e₃, r₃, k₃, O₃⟩ => ⟨c₃, cf₃, ?_, ?_, ?_, ?_⟩
    · have hw : word s₃.mem base o = s₁.gpr t := by
        rw [O₃.word (by omega) (by omega), m₂, word_writeW_self]
      have hR : regsVal s₂ ts = regsVal s ts := regsVal_congr fun q hq => by
        rw [g₂, k₁.1 q (by simp only [List.mem_singleton]; rintro rfl; exact htn hq)]
      rw [hR] at e₃
      rw [imm0_toNat] at e₁
      simp only [regsVal, wordsVal, List.length_cons, hw]
      rw [pow64_succ]
      rw [show 2 ^ 64 * 2 ^ (64 * ts.length) * c₃.toNat = 2 ^ 64 * (2 ^ (64 * ts.length) * c₃.toNat) by
        rw [Nat.mul_assoc]]
      omega
    · have hw : word s₃.mem base o = s₁.gpr t := by
        rw [O₃.word (by omega) (by omega), m₂, word_writeW_self]
      simp only [regsVal, wordsVal, List.length_cons, r₃, hw]
      rw [k₃.gpr t htn, g₂]
    · exact ⟨fun r hr => by
        simp only [List.mem_cons, not_or] at hr
        rw [k₃.gpr r hr.2, g₂, k₁.1 r (by simpa using hr.1)],
        by rw [k₃.rd, rd₂, k₁.2.2.1], by rw [k₃.wr, wr₂, k₁.2.2.2]⟩
    · simp only [List.length_cons]
      rw [show 8 * (ts.length + 1) = 8 + 8 * ts.length by omega]
      exact (O₂.mono (Nat.le_refl _) (by omega)).trans (O₃.mono (by omega) (by omega))


/-! ## The sum -/

theorem p8 : (2 : Nat) ^ (64 * 8) = (2 ^ 64) ^ 8 := Nat.pow_mul 2 64 8

theorem p9 : (2 : Nat) ^ (64 * 9) = (2 ^ 64) ^ 9 := Nat.pow_mul 2 64 9

theorem sAdd_arith {m W8 L R R' A c5 c6 : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (hW : W8 < (2 ^ 64) ^ 8) (hL : L < (2 ^ 64) ^ 8) (hR' : R' < 2 ^ 64)
    (e3 : L + (2 ^ 64) ^ 8 * R = A + 1) (e5 : W8 + (decide (R < 512)).toNat = L + (2 ^ 64) ^ 8 * c5)
    (e6 : R' + 512 * (R / 512) + c5 = R + 2 ^ 64 * c6) (hA : A < 2 * m) :
    W8 + (2 ^ 64) ^ 8 * R' = A % m := by
  have hd : (decide (R < 512)).toNat = if R < 512 then 1 else 0 := by
    by_cases h : R < 512 <;> simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false,
      ite_true, ite_false]
  rw [hd] at e5
  by_cases hA' : A < m
  · rw [Nat.mod_eq_of_lt hA']
    split at e5 <;> omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    split at e5 <;> omega

theorem regsAW (s : State) :
    regsVal s AW = regsVal s (AW.take 8) + (2 ^ 64) ^ 8 * (s.gpr .r14).toNat := by
  have h := regsVal_append s (AW.take 8) (AW.drop 8)
  rw [List.take_append_drop] at h
  rw [h, show (AW.take 8).length = 8 from rfl, show AW.drop 8 = [.r14] from rfl, p8]
  simp only [regsVal, Nat.mul_zero, Nat.add_zero]

/-- `sAdd`: `[o] = ([a] + [b]) mod p` for `[a] + [b] < 2p`. -/
theorem sAdd_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} {o a b : Nat} (hs : Scr s base Z)
    (ho : o + 72 ≤ 4096) (ha : a + 72 ≤ 4096) (hb : b + 72 ≤ 4096)
    {m : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (hAB : wordsVal s.mem base a 9 + wordsVal s.mem base b 9 < 2 * m) :
    WP isa (.block (sAdd o a b)) s fun s' =>
      wordsVal s'.mem base o 9 = (wordsVal s.mem base a 9 + wordsVal s.mem base b 9) % m ∧
      KeepRegs (.rdx :: AW) s s' ∧ Outside base o 72 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [sAdd]
  simp only [List.append_assoc]
  rw [pair_append, WP.block_append_iff]
  refine WP.mono (xorZ_ok s .rdx) fun s₁ ⟨z₁, _, _, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (cmpM1_ok s₁ .rdx z₁) fun s₂ ⟨cf₂, _, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have hm₂ : s₂.mem = s.mem := k₂.2.1.trans k₁.2.1
  rw [WP.block_append_iff]
  refine WP.mono (ldOp_adc_ok hZ AW hs₂ ⟨by decide, by decide⟩ (a := a) (b := b)
    (by rw [show AW.length = 9 from rfl]; omega) (by rw [show AW.length = 9 from rfl]; omega) cf₂)
    fun s₃ ⟨c₃, cf₃, e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [hm₂, show AW.length = 9 from rfl, regsAW] at e₃
  have hL := regsVal_lt s₃ (AW.take 8)
  rw [show (AW.take 8).length = 8 from rfl, p8] at hL
  have hc₃ : c₃ = false := by cases c₃ <;> simp only [Bool.toNat_true, Bool.toNat_false] at e₃ ⊢ <;> omega
  subst hc₃
  replace e₃ : regsVal s₃ (AW.take 8) + (2 ^ 64) ^ 8 * (s₃.gpr .r14).toNat =
      wordsVal s.mem base a 9 + wordsVal s.mem base b 9 + 1 := by
    have h0 : false.toNat = 0 := rfl
    have h1 : true.toNat = 1 := rfl
    omega
  have h14 : (s₃.gpr .r14).toNat < 1024 := by omega
  rw [WP.block_append_iff]
  refine WP.mono (selTop_ok s₃ h14) fun s₄ ⟨d₄, cf₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sbbSt_ok hZ (AW.take 8) hs₄ ⟨by decide, by decide⟩ (o := o)
    (by rw [show (AW.take 8).length = 8 from rfl]; omega) cf₄) fun s₅ ⟨c₅, cf₅, e₅, r₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  rw [show ∀ x y : Instr, [x, y] = [x] ++ [y] from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (sbbS_ok s₅ .r14 (src := .reg .rdx) rfl cf₅) fun s₆ ⟨c₆, _, e₆, k₆⟩ => ?_
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  refine WP.mono (storeX_ok hs₆ .r14 (d := o + 64) (by omega)) fun s₇ ⟨m₇, g₇, _, _, rd₇, wr₇⟩ => ?_
  have hR : regsVal s₄ (AW.take 8) = regsVal s₃ (AW.take 8) :=
    regsVal_congr fun q hq => k₄.1 q (by
      rw [List.mem_singleton]; rintro rfl; exact absurd hq (by decide))
  have g14 : s₅.gpr .r14 = s₄.gpr .r14 := k₅.gpr _ (by decide)
  have gdx : s₅.gpr .rdx = s₄.gpr .rdx := k₅.gpr _ (by decide)
  have g14' : s₄.gpr .r14 = s₃.gpr .r14 := k₄.1 _ (by decide)
  rw [show (AW.take 8).length = 8 from rfl, hR, p8] at e₅
  rw [g14, gdx, d₄, g14'] at e₆
  have hw : wordsVal s₇.mem base o 9 = wordsVal s₅.mem base o 8 + (2 ^ 64) ^ 8 * (s₆.gpr .r14).toNat := by
    rw [wordsVal_succ_last, m₇, word_writeW_self, (writeW_outside s₆.mem base _ (by omega)).wordsVal
      (by omega) (by omega), k₆.2.1]
  refine ⟨?_, ?_, ?_⟩
  · rw [hw]
    have hW := wordsVal_lt s₅.mem base o 8
    rw [p8] at hW
    exact sAdd_arith hm hW hL (s₆.gpr .r14).isLt e₃ e₅ e₆ hAB
  · refine ⟨fun r hr => ?_, by rw [rd₇, k₆.2.2.1, k₅.rd, k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1],
      by rw [wr₇, k₆.2.2.2, k₅.wr, k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]⟩
    simp only [List.mem_cons, not_or] at hr
    have hr' : r ∉ AW := hr.2
    have h14 : r ∉ [Reg.r14] := fun h => hr' (by
      rw [List.mem_singleton] at h; subst h; decide)
    rw [g₇, k₆.1 r h14, k₅.gpr r (fun h => hr' (List.mem_of_mem_take h)),
      k₄.1 r (by simpa using hr.1), k₃.1 r hr', k₂.1 r (by simp), k₁.1 r (by simpa using hr.1)]
  · have O₄ : Outside base o 72 s.mem s₄.mem := by
      rw [k₄.2.1, k₃.2.1, hm₂]; exact Outside.refl _ _ _ _
    have O₆ : Outside base o 72 s₅.mem s₇.mem := by
      rw [m₇, k₆.2.1]; exact (writeW_outside (d := o + 64) _ _ _ (by omega)).mono (by omega) (by omega)
    rw [show (AW.take 8).length = 8 from rfl] at O₅
    exact (O₄.trans (O₅.mono (Nat.le_refl _) (by omega))).trans O₆

/-! ## The difference -/

theorem regsSW (s : State) :
    regsVal s SW = regsVal s (SW.take 8) + (2 ^ 64) ^ 8 * (s.gpr .r14).toNat := by
  have h := regsVal_append s (SW.take 8) (SW.drop 8)
  rw [List.take_append_drop] at h
  rw [h, show (SW.take 8).length = 8 from rfl, show SW.drop 8 = [.r14] from rfl, p8]
  simp only [regsVal, Nat.mul_zero, Nat.add_zero]

theorem sSub_arith {m W8 L R R' A B c c5 c6 : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (hW : W8 < (2 ^ 64) ^ 8) (hL : L < (2 ^ 64) ^ 8) (hR' : R' < 2 ^ 64) (hR : R < 2 ^ 64) (hc : c ≤ 1)
    (hc5 : c5 ≤ 1) (hc6 : c6 ≤ 1) (e3 : L + (2 ^ 64) ^ 8 * R + B = A + (2 ^ 64) ^ 9 * c) (e5 : W8 + c = L + (2 ^ 64) ^ 8 * c5)
    (e6 : R' + c5 = R + 2 ^ 64 * c6) (hA : A < m) (hB : B < m) :
    W8 + (2 ^ 64) ^ 8 * (R' % 512) = (A + (m - B)) % m := by
  obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
  · have hR5 : R < 512 := by omega
    obtain rfl : c5 = 0 := by omega
    obtain rfl : c6 = 0 := by omega
    rw [Nat.mod_eq_of_lt (show R' < 512 by omega),
      show A + (m - B) = (A - B) + m by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show A - B < m by omega)]
    omega
  · obtain rfl : c6 = 0 := by
      rcases Nat.lt_or_ge c6 1 with h | h
      · omega
      · exfalso
        obtain rfl : c6 = 1 := by omega
        obtain rfl : R = 0 := by omega
        omega
    have hV : W8 + (2 ^ 64) ^ 8 * R' + (B + 1) = A + (2 ^ 64) ^ 9 := by omega
    have hd := Nat.div_add_mod R' 512
    have hq : R' / 512 = 2 ^ 55 - 1 := by omega
    rw [Nat.mod_eq_of_lt (show A + (m - B) < m by omega)]
    omega

/-- `sSub`: `[o] = ([a] - [b]) mod p` for `[a]`, `[b]` below `p`. -/
theorem sSub_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} {o a b : Nat} (hs : Scr s base Z)
    (ho : o + 72 ≤ 4096) (ha : a + 72 ≤ 4096) (hb : b + 72 ≤ 4096)
    {m : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (hA : wordsVal s.mem base a 9 < m) (hB : wordsVal s.mem base b 9 < m) :
    WP isa (.block (sSub o a b)) s fun s' =>
      wordsVal s'.mem base o 9 = (wordsVal s.mem base a 9 + (m - wordsVal s.mem base b 9)) % m ∧
      KeepRegs SW s s' ∧ Outside base o 72 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [sSub]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldOp_sub_ok hZ (t := .rax) (ts := SW.tail) hs ⟨by decide, by decide⟩ (a := a) (b := b)
    (by rw [show SW.tail.length = 8 from rfl]; omega) (by rw [show SW.tail.length = 8 from rfl]; omega))
    fun s₃ ⟨c₃, cf₃, e₃, k₃⟩ => ?_
  have hs₃ := hs.of_keeps k₃ (by decide)
  rw [show Reg.rax :: SW.tail = SW from rfl, show SW.tail.length + 1 = 9 from rfl, regsSW, p9] at e₃
  have hL := regsVal_lt s₃ (SW.take 8)
  rw [show (SW.take 8).length = 8 from rfl, p8] at hL
  rw [WP.block_append_iff]
  refine WP.mono (sbbSt_ok hZ (SW.take 8) hs₃ ⟨by decide, by decide⟩ (o := o)
    (by rw [show (SW.take 8).length = 8 from rfl]; omega) cf₃) fun s₅ ⟨c₅, cf₅, e₅, r₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₃.of_keepRegs k₅ (by decide)
  rw [show ∀ (x y z : Instr), [x, y, z] = [x] ++ [y, z] from fun _ _ _ => rfl, WP.block_append_iff]
  refine WP.mono (sbbS_ok s₅ .r14 (src := .imm 0) (v := (0 : BitVec 32).signExtend 64) rfl cf₅)
    fun s₆ ⟨c₆, _, e₆, k₆⟩ => ?_
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  rw [show ∀ x y : Instr, [x, y] = [x] ++ [y] from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (and511_ok s₆ .r14) fun s₇ ⟨a₇, k₇⟩ => ?_
  have hs₇ := hs₆.of_keeps k₇ (by decide)
  refine WP.mono (storeX_ok hs₇ .r14 (d := o + 64) (by omega)) fun s₈ ⟨m₈, g₈, _, _, rd₈, wr₈⟩ => ?_
  have g14 : s₅.gpr .r14 = s₃.gpr .r14 := k₅.gpr _ (by decide)
  rw [show (SW.take 8).length = 8 from rfl, p8] at e₅
  rw [g14, imm0_toNat] at e₆
  have hw : wordsVal s₈.mem base o 9 = wordsVal s₅.mem base o 8 + (2 ^ 64) ^ 8 * (s₇.gpr .r14).toNat := by
    rw [wordsVal_succ_last, m₈, word_writeW_self, (writeW_outside s₇.mem base _ (by omega)).wordsVal
      (by omega) (by omega), k₇.2.1, k₆.2.1]
  refine ⟨?_, ?_, ?_⟩
  · rw [hw, a₇]
    have hW := wordsVal_lt s₅.mem base o 8
    rw [p8] at hW
    exact sSub_arith hm hW hL (s₆.gpr .r14).isLt (s₃.gpr .r14).isLt (Bool.toNat_le _)
      (Bool.toNat_le _) (Bool.toNat_le _) e₃ e₅ (by omega) hA hB
  · refine ⟨fun r hr => ?_, by rw [rd₈, k₇.2.2.1, k₆.2.2.1, k₅.rd, k₃.2.2.1],
      by rw [wr₈, k₇.2.2.2, k₆.2.2.2, k₅.wr, k₃.2.2.2]⟩
    have h14 : r ∉ [Reg.r14] := fun h => hr (by
      rw [List.mem_singleton] at h; subst h; decide)
    rw [g₈, k₇.1 r h14, k₆.1 r h14, k₅.gpr r (fun h => hr (List.mem_of_mem_take h)), k₃.1 r hr]
  · have O₃ : Outside base o 72 s.mem s₅.mem := by
      rw [show (SW.take 8).length = 8 from rfl] at O₅
      rw [k₃.2.1] at O₅
      exact O₅.mono (Nat.le_refl _) (by omega)
    have O₈ : Outside base o 72 s₅.mem s₈.mem := by
      rw [m₈, k₇.2.1, k₆.2.1]; exact (writeW_outside (d := o + 64) _ _ _ (by omega)).mono (by omega) (by omega)
    exact O₃.trans O₈

end VG.Proof.Weierstrass.X86_64.P521F
