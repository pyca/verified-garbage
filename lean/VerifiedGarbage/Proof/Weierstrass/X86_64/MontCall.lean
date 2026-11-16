module

import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnB
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Reloc
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnX
import VerifiedGarbage.Proof.Mont.X86_64.CsubR
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Mont.X86_64.Chain
import VerifiedGarbage.Proof.Mont.X86_64.Round
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnN
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Mont.X86_64.CsubS
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Mont.X86_64.Ops

/-! ### `Weierstrass.X86_64.MontFnN6`, which only this module used -/

section

/-! ### `Weierstrass.X86_64.MontFn6`, which only this module used -/

section

/-!
# P-384's product modulo `p` as a function, on x86-64

`mulFn6 adx` (`Impl/Weierstrass/X86_64/Mont.lean`) runs the inline product
`mulRounds` (or `sqrSA`, when `a = b`) relocated: its operands at the
markers read through `rbx = ws + a`, `rsi = ws + b` and `rsi = ws + o`.
With those registers so (`PtrsAt`), the relocated code runs as the inline
code at the offsets `a`, `b` and `o` (`wp_unptr`, with `sqrSA_reloc`,
`mulRounds_reloc`, `stores_reloc`), whose proofs then apply
(`sqrSA_ok`, `mulRounds_ok`); `csubR_ok` reduces the result without the
modulus in memory. The function changes only `fnClob`, `[o]` and its
temporary area, bytes `fnTmp6` to 4095 (`mulFn6_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.Mont

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Impl.Weierstrass.X86_64.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- P-384's prime. -/
abbrev p384 : Nat :=
  39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319

/-- An offset the functions of six words take: apart from their temporary
area, and within the working space. -/
def Arg6 (Z x : Nat) : Prop := (x + 48 ≤ fnTmp6 ∨ 4096 ≤ x) ∧ x + 48 ≤ Z

theorem fnTmp6_eq : fnTmp6 = 4048 := rfl

/-! ## The relocated code is the inline code -/

theorem sqrSA_reloc (adx : Bool) (a o : Nat) :
    (sqrSA (fnMod6 adx) mO mA).map (Instr.mapMem (unptr [(.rbx, a), (.rsi, o)] ∘ relocTo [(mA, .rbx), (mO, .rsi)])) =
      sqrSA (fnMod6 adx) o a := by
  cases adx <;> kernel_rfl

theorem mulRounds_reloc (adx : Bool) (a b : Nat) :
    (mulRounds (fnMod6 adx) mA mB).map
        (Instr.mapMem (unptr [(.rbx, a), (.rsi, b)] ∘ relocTo [(mA, .rbx), (mB, .rsi)])) =
      mulRounds (fnMod6 adx) a b := by
  cases adx <;> kernel_rfl

theorem storesW_reloc (o : Nat) :
    (stores sqWin6 mO).map (Instr.mapMem (unptr [(.rsi, o)] ∘ relocTo [(mO, .rsi)])) = stores sqWin6 o := rfl

theorem storesL_reloc (o : Nat) :
    (stores low6 mO).map (Instr.mapMem (unptr [(.rsi, o)] ∘ relocTo [(mO, .rsi)])) = stores low6 o := rfl

/-! ## The relocated code keeps its pointers -/

theorem sqr_keeps : ∀ adx : Bool,
    (reloc [(mA, .rbx), (mO, .rsi)] (sqrSA (fnMod6 adx) mO mA)).all (keepsPtrs [.rbx, .rsi]) = true := by
  decide +kernel

theorem mul_keeps : ∀ adx : Bool,
    (reloc [(mA, .rbx), (mB, .rsi)] (mulRounds (fnMod6 adx) mA mB)).all (keepsPtrs [.rbx, .rsi]) = true := by
  decide +kernel

theorem storesW_keeps : (reloc [(mO, .rsi)] (stores sqWin6 mO)).all (keepsPtrs [.rsi]) = true := by
  decide +kernel

theorem storesL_keeps : (reloc [(mO, .rsi)] (stores low6 mO)).all (keepsPtrs [.rsi]) = true := by
  decide +kernel

theorem mul_scal : ∀ adx : Bool,
    scalCode (.block (reloc [(mA, .rbx), (mB, .rsi)] (mulRounds (fnMod6 adx) mA mB))) = true := by
  decide +kernel

theorem csubR_scal : scalCode (.block (csubR low6 top6)) = true := by decide +kernel

theorem storesL_scal : scalCode (.block (reloc [(mO, .rsi)] (stores low6 mO))) = true := by decide +kernel

theorem sqr6_scal : ∀ adx : Bool, scalCode (.block (sqr6 adx)) = true := by decide +kernel

/-- The modulus of the function, as the rounds take it: P-384's `p`, never read
from memory. -/
theorem modOkR6 (adx : Bool) {Z m : Nat} (hZ : 48 ≤ Z) (hm : m = p384) (mem : Mem) (base : Addr) :
    ModOkR (fnMod6 adx) Z m mem base where
  n0 := by cases adx <;> decide
  n7 := by cases adx <;> decide
  mo := hZ
  val := fun h => absurd h (by cases adx <;> decide)
  inv := by subst hm; cases adx <;> decide +kernel
  red := by subst hm; cases adx <;> decide +kernel

/-! ## Steps -/

/-- `add rsi, rdi`. -/
theorem addRsiRdi_ok (s : State) :
    WP isa (.block [.alu .add .rsi (.reg .rdi)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rdi + s.gpr .rsi ∧ Keeps [.rsi] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨BitVec.add_comm _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- `o` into `xmm6`, `rsi = rcx`. -/
theorem keepO_ok (s : State) :
    WP isa (.block [.xop (.movq .xmm6 .rsi), .mov .rsi (.reg .rcx)]) s fun s' =>
      s'.xmm .xmm6 = (0 : BitVec 64) ++ s.gpr .rsi ∧ (∀ x, x ≠ .xmm6 → s'.xmm x = s.xmm x) ∧
        s'.gpr .rsi = s.gpr .rcx ∧ Keeps [.rsi] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, readSrc, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, RegUpd.xmm_setReg, setXmm_xmm, setXmm_gpr,
    ↓reduceIte]
  refine ⟨trivial, fun x hx => ?_, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [hx, ↓reduceIte]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, setXmm_gpr]

/-- `rsi` from `xmm6`, plus `rdi`. -/
theorem backO_ok (s : State) :
    WP isa (.block [.movqR .rsi .xmm6, .alu .add .rsi (.reg .rdi)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rdi + qword (s.xmm .xmm6) 0 ∧ s'.xmm = s.xmm ∧ Keeps [.rsi] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [BitVec.add_comm]; rfl
  · simp only [RegUpd.xmm_setReg, RegUpd.xmm_arithFlags]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- The registers the products' branches change. -/
abbrev brClob : List Reg := [.rax, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The square, `a = b`: `[o] = [a]² R⁻¹ mod p`. -/
theorem sqr6_ok (adx : Bool) {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    {o a m : Nat} (hm : m = p384) (hbx : s.gpr .rbx = off base a) (hsi : s.gpr .rsi = BitVec.ofNat 64 o)
    (ho : Arg6 Z o) (ha : Arg6 Z a) (hA : wordsVal s.mem base a 6 < m) :
    WP isa (.block (sqr6 adx)) s fun s' =>
      KeepRegs brClob s s' ∧
      (∀ x, (ofs base x < o ∨ o + 48 ≤ ofs base x) → (ofs base x < fnTmp6 ∨ 4096 ≤ ofs base x) →
        s'.mem x = s.mem x) ∧
      wordsVal s'.mem base o 6 < m ∧
      wordsVal s'.mem base o 6 * 2 ^ (64 * 6) % m = wordsVal s.mem base a 6 * wordsVal s.mem base a 6 % m := by
  have hnw := hs.nowrap
  unfold Arg6 at ho ha
  rw [fnTmp6_eq] at ho ha ⊢
  simp only [sqr6, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (addRsiRdi_ok s) fun s₁ ⟨e₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain hp₁ : PtrsAt [(.rbx, a), (.rsi, o)] s₁ := .two (by rw [k₁.1 _ (by decide), hbx, hs₁.rdi])
    (by rw [e₁, k₁.1 _ (by decide), hs.rdi, hsi])
  obtain w₂ := sqrSA_ok (M := fnMod6 adx) hs₁ hm (by simp only [fnMod6, fnTmp6]; omega_using [hZ]) (o := o) (a := a)
    (by omega_using [ho]) (by omega_using [ha]) (by simp only [fnMod6, fnTmp6]; omega_using [ho]) (by simp only [fnMod6, fnTmp6]; omega_using [ha])
    (by rw [k₁.2.1]; exact hA)
  rw [← sqrSA_reloc, ← reloc_unptr] at w₂
  rw [WP.block_append_iff]
  refine WP.mono (wp_unptr (rs := [.rbx, .rsi]) (by simp) _ (sqr_keeps adx) hp₁ w₂)
    fun s₂ ⟨k₂, O₂, _, lt₂, res₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (csubR_ok s₂ (ts := sqWin6) (top := .r8) rfl ⟨by decide, by decide⟩ hm lt₂)
    fun s₃ ⟨e₃, k₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  obtain hp₃ : PtrsAt [(.rsi, o)] s₃ := .one (by
    rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₃.1 .rdi (by decide), k₂.gpr .rdi (by decide)]
    exact hp₁ .rsi o rfl)
  obtain w₄ := stores_ok sqWin6 hs₃ (o := o) (by simp only [sqWin6, List.length_cons, List.length_nil]; omega_using [ho])
    (by decide)
  rw [← storesW_reloc, ← reloc_unptr] at w₄
  refine WP.mono (wp_unptr (rs := [.rsi]) (by simp) _ storesW_keeps hp₃ w₄)
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  simp only [show sqWin6.length = 6 from rfl, Nat.reduceMul] at e₄ O₄
  obtain hval : wordsVal s₄.mem base o 6 =
      (regsVal s₂ sqWin6 + 2 ^ (64 * 6) * (s₂.gpr .r8).toNat) % m := by rw [e₄, e₃]
  have hmem₁ : s₁.mem = s.mem := k₁.2.1
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun x hx hx' => ?_, ?_, ?_⟩
  · rw [k₄.gpr r (by simp), k₃.1 r (not_mem_of hr (by decide)), k₂.gpr r (not_mem_of hr (by decide)),
      k₁.1 r (not_mem_of hr (by decide))]
  · rw [k₄.rd, k₃.2.2.1, k₂.rd, k₁.2.2.1]
  · rw [k₄.wr, k₃.2.2.2, k₂.wr, k₁.2.2.2]
  · rw [O₄ x hx, k₃.2.1, O₂ x hx (by simp only [fnMod6, fnTmp6]; omega_using [hx']), hmem₁]
  · rw [hval]; exact Nat.mod_lt _ (by rw [hm]; decide)
  · rw [hval, ← hmem₁]; exact res₂

/-- The product, `a ≠ b`: `[o] = [a] [b] R⁻¹ mod p`. -/
theorem mul6_ok (adx : Bool) {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    {o a b m : Nat} (hm : m = p384) (hbx : s.gpr .rbx = off base a) (hcx : s.gpr .rcx = off base b)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 o)
    (ho : Arg6 Z o) (ha : Arg6 Z a) (hb : Arg6 Z b) (hB : wordsVal s.mem base b 6 < m) :
    WP isa (.block (mul6 adx)) s fun s' =>
      KeepRegs brClob s s' ∧
      (∀ x, (ofs base x < o ∨ o + 48 ≤ ofs base x) → (ofs base x < fnTmp6 ∨ 4096 ≤ ofs base x) →
        s'.mem x = s.mem x) ∧
      wordsVal s'.mem base o 6 < m ∧
      wordsVal s'.mem base o 6 * 2 ^ (64 * 6) % m = wordsVal s.mem base a 6 * wordsVal s.mem base b 6 % m ∧
      ∀ x, x ≠ .xmm6 → s'.xmm x = s.xmm x := by
  have hnw := hs.nowrap
  unfold Arg6 at ho ha hb
  rw [fnTmp6_eq] at ho ha hb ⊢
  simp only [mul6, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (keepO_ok s) fun s₁ ⟨x₁, xo₁, e₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain hp₁ : PtrsAt [(.rbx, a), (.rsi, b)] s₁ := .two (by rw [k₁.1 _ (by decide), hbx, hs₁.rdi])
    (by rw [e₁, hcx, hs₁.rdi])
  have hmem₁ : s₁.mem = s.mem := k₁.2.1
  obtain w₂ := mulRounds_ok (M := fnMod6 adx) hs₁ (modOkR6 adx (by omega_using [hZ]) hm _ _) (a := a) (b := b)
    (by simp only [fnMod6]; omega_using [ha]) (by simp only [fnMod6]; omega_using [hb]) (by rw [hmem₁]; exact hB)
  rw [← mulRounds_reloc, ← reloc_unptr] at w₂
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep (mul_scal adx) (wp_unptr (rs := [.rbx, .rsi]) (by simp) _ (mul_keeps adx) hp₁ w₂))
    fun s₂ ⟨⟨⟨U, eU⟩, hT, k₂⟩, x₂, _⟩ => ?_
  simp only [show (fnMod6 adx).n = 6 from rfl] at eU hT k₂
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  -- The accumulator's value as `csubR` sees it: its top word is zero.
  obtain hV : regsVal s₂ low6 + 2 ^ (64 * 6) * (s₂.gpr top6).toNat = regsVal s₂ (wins 6 6) := by
    simp only [low6, top6]
    rw [wins_split 6 6, regsVal_append, show ((List.range 6).map (win 6 6)).length = 6 from rfl]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
    have hT' := hT
    rw [wins_split 6 6, regsVal_append, show ((List.range 6).map (win 6 6)).length = 6 from rfl] at hT'
    simp only [regsVal, Nat.mul_zero, Nat.add_zero] at hT'
    obtain hm' : m < 2 ^ (64 * 6) := (p384_bounds hm).1
    have : (s₂.gpr (win 6 6 (6 + 1))).toNat = 0 := by
      generalize (2 : Nat) ^ (64 * 6) = Q at hT' hm'
      by_contra hne
      have : Q * 2 ^ 64 ≤ Q * ((s₂.gpr (win 6 6 6)).toNat + 2 ^ 64 * (s₂.gpr (win 6 6 (6 + 1))).toNat) :=
        Nat.mul_le_mul_left _ (by omega_using [hne])
      omega_using [hZ, hm, hbx, hcx, hsi, ho, ha, hb, hB, hnw, x₁, e₁, eU, hT, hT', hm', hne, this]
    rw [this, Nat.mul_zero, Nat.add_zero]
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep csubR_scal (csubR_ok s₂ (ts := low6) (top := top6) rfl ⟨by decide, by decide⟩ hm
    (by rw [hV]; exact hT))) fun s₃ ⟨⟨e₃, k₃⟩, x₃, _⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (backO_ok s₃) fun s₄ ⟨e₄, x₄, k₄⟩ => ?_
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  obtain hp₄ : PtrsAt [(.rsi, o)] s₄ := .one (by
    rw [e₄, x₃, x₂, x₁, qword_lo, hsi, k₄.1 .rdi (by decide)])
  obtain w₅ := stores_ok low6 hs₄ (o := o) (by simp only [low6, List.length_map, List.length_range]; omega_using [ho])
    (by decide)
  rw [← storesL_reloc, ← reloc_unptr] at w₅
  refine WP.mono (WP.vecKeep storesL_scal (wp_unptr (rs := [.rsi]) (by simp) _ storesL_keeps hp₄ w₅))
    fun s₅ ⟨⟨e₅, k₅, O₅⟩, x₅, _⟩ => ?_
  simp only [show low6.length = 6 from rfl, Nat.reduceMul] at e₅ O₅
  obtain hval : wordsVal s₅.mem base o 6 = regsVal s₂ (wins 6 6) % m := by
    rw [e₅, show regsVal s₄ low6 = regsVal s₃ low6 from regsVal_congr fun q hq => k₄.1 q (by
      intro h; simp only [List.mem_singleton] at h; subst h; revert hq; decide), e₃, hV]
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun x hx hx' => ?_, ?_, ?_, fun x hx => ?_⟩
  · rw [k₅.gpr r (by simp), k₄.1 r (not_mem_of hr (by decide)), k₃.1 r (not_mem_of hr (by decide)),
      k₂.1 r (not_mem_of hr (by decide)), k₁.1 r (not_mem_of hr (by decide))]
  · rw [k₅.rd, k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
  · rw [k₅.wr, k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  · rw [O₅ x hx, k₄.2.1, k₃.2.1, k₂.2.1, hmem₁]
  · rw [hval]; exact Nat.mod_lt _ (by rw [hm]; decide)
  · rw [hval, Nat.mod_mul_mod, Nat.mul_comm, eU, ← hmem₁]
    simp only [Nat.add_mul_mod_self_right]
  · rw [x₅, x₄, x₃, x₂, xo₁ x hx]

/-! ## The function -/

/-- `[o] = [a] [b] 2⁻³⁸⁴ mod p` for P-384's `p = m`, the offsets the low
halves of `rsi`, `rdx` and `rcx`: the function changes only `fnClob`, `[o]`
and its temporary area, bytes `fnTmp6` to 4095. -/
theorem mulFn6_ok (adx : Bool) {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    {m : Nat} (hm : m = p384) (ho : Arg6 Z (argOf s .rsi)) (ha : Arg6 Z (argOf s .rdx))
    (hb : Arg6 Z (argOf s .rcx)) (hB : wordsVal s.mem base (argOf s .rcx) 6 < m) :
    WP isa (mulFn6 adx) s fun s' =>
      wordsVal s'.mem base (argOf s .rsi) 6 < m ∧
      wordsVal s'.mem base (argOf s .rsi) 6 * (2 ^ 64) ^ 6 % m =
        wordsVal s.mem base (argOf s .rdx) 6 * wordsVal s.mem base (argOf s .rcx) 6 % m ∧
      KeepRegs fnClob s s' ∧
      ∀ x, (ofs base x < argOf s .rsi ∨ argOf s .rsi + 48 ≤ ofs base x) →
        (ofs base x < fnTmp6 ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x := by
  refine WP.seq (WP.mono (WP.block_append_iff.mp (entry_ok hs)) fun s₀ h₀ => WP.seq (WP.mono h₀
    fun s₁ ⟨hs₁, bx₁, cx₁, zf₁, si₁, x0, x1, x2, x3, x4, x5, k₁, m₁⟩ => ?_))
  generalize hO : argOf s .rsi = o at *
  generalize hA : argOf s .rdx = a at *
  generalize hBb : argOf s .rcx = b at *
  obtain hQ : (2 : Nat) ^ (64 * 6) = (2 ^ 64) ^ 6 := Nat.pow_mul 2 64 6
  refine WP.seq (WP.mono (show WP isa (.ite .e (.block (sqr6 adx)) (.block (mul6 adx))) s₁ (fun s' =>
      KeepRegs brClob s₁ s' ∧
      (∀ x, (ofs base x < o ∨ o + 48 ≤ ofs base x) → (ofs base x < fnTmp6 ∨ 4096 ≤ ofs base x) →
        s'.mem x = s₁.mem x) ∧
      wordsVal s'.mem base o 6 < m ∧
      wordsVal s'.mem base o 6 * 2 ^ (64 * 6) % m = wordsVal s₁.mem base a 6 * wordsVal s₁.mem base b 6 % m ∧
      ∀ x, x ≠ .xmm6 → s'.xmm x = s₁.xmm x) from ?_) fun s₂ h₂ => ?_)
  · refine WP.ite (decide (a = b)) zf₁ (fun h => ?_) (fun _ => mul6_ok adx hs₁ hZ hm bx₁ cx₁ si₁ ho ha hb
      (by rw [m₁]; exact hB))
    obtain hab : a = b := of_decide_eq_true h
    subst hab
    exact WP.mono (WP.vecKeep (sqr6_scal adx) (sqr6_ok adx hs₁ hZ hm bx₁ si₁ ho ha (by rw [m₁]; exact hB)))
      fun s' ⟨⟨k, O, lt, e⟩, xm, _⟩ => ⟨k, O, lt, e, fun x _ => by rw [xm]⟩
  obtain ⟨k₂, O₂, lt₂, e₂, xm₂⟩ := h₂
  refine WP.mono (restores_ok s₂) fun s₃ ⟨b₃, p₃, r12₃, r13₃, r14₃, r15₃, k₃⟩ => ?_
  rw [m₁] at e₂ O₂
  refine ⟨by rw [k₃.2.1]; exact lt₂, by rw [k₃.2.1, ← hQ]; exact e₂,
    ⟨fun r hr => ?_, by rw [k₃.2.2.1, k₂.rd, k₁.rd], by rw [k₃.2.2.2, k₂.wr, k₁.wr]⟩, fun x hx hx' => ?_⟩
  · rcases not_clob_cases r hr with hsv | rfl | rfl
    · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hsv
      rcases hsv with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [b₃, xm₂ _ (by decide), x0, qword_lo]
      · rw [p₃, xm₂ _ (by decide), x1, qword_lo]
      · rw [r12₃, xm₂ _ (by decide), x2, qword_lo]
      · rw [r13₃, xm₂ _ (by decide), x3, qword_lo]
      · rw [r14₃, xm₂ _ (by decide), x4, qword_lo]
      · rw [r15₃, xm₂ _ (by decide), x5, qword_lo]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  · rw [k₃.2.1, O₂ x hx hx']

end VG.Proof.Weierstrass.X86_64.Mont

end

end


/-!
# P-384's product modulo `n` as a function, on x86-64

`mulFnN6 adx` (`Impl/Weierstrass/X86_64/Mont.lean`) keeps `o` in `xmm6`
(`keepO_ok`) and the words at `fnMoN6` in `xmm7`–`xmm12`
(`saveSteps_ok`), stores `n` there (`setConst`), then runs the inline
product's rounds `mulRounds` relocated: its operands at the markers read
through `rbx = ws + a` and `rsi = ws + b`. With those registers so
(`PtrsAt`), the relocated code runs as the inline code at the offsets `a`
and `b` (`wp_unptr`, `mulRoundsN6_reloc`), whose proof then applies
(`mulRounds_ok`), `n` now in memory. `csub` reduces the result with `n` in
memory, which is stored through `rsi = ws + o` (`backO_ok`, `stores_ok`).
It puts the words back (`restoreSteps_ok`), so the function changes only
`fnClob`, `[o]` and its temporary area, bytes `fnTmp6` to 4095
(`mulFnN6_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.Mont

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Impl.Weierstrass.X86_64.Mont
open VG.Proof.Weierstrass (Unch)
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- An offset `vg_p384_mul_mod_n` takes: apart from `n` and its temporary
area, and within the working space. -/
def ArgN6 (Z x : Nat) : Prop := (x + 96 ≤ fnTmp6 ∨ 4096 ≤ x) ∧ x + 48 ≤ Z

theorem fnMoN6_eq : fnMoN6 = 4000 := rfl

theorem n384_lt : n384 < 2 ^ (64 * 6) := by decide +kernel

/-! ## The relocated code is the inline code -/

theorem mulRoundsN6_reloc (adx : Bool) (a b : Nat) :
    (mulRounds (fnModN6 adx) mA mB).map
        (Instr.mapMem (unptr [(.rbx, a), (.rsi, b)] ∘ relocTo [(mA, .rbx), (mB, .rsi)])) =
      mulRounds (fnModN6 adx) a b := by
  cases adx <;> kernel_rfl

theorem mulN6_keeps : ∀ adx : Bool,
    (reloc [(mA, .rbx), (mB, .rsi)] (mulRounds (fnModN6 adx) mA mB)).all (keepsPtrs [.rbx, .rsi]) = true := by
  decide +kernel

theorem mulN6_scal : ∀ adx : Bool,
    scalCode (.block (reloc [(mA, .rbx), (mB, .rsi)] (mulRounds (fnModN6 adx) mA mB))) = true := by
  decide +kernel

theorem storeN6_scal : scalCode (.block storeN6) = true := by decide +kernel

theorem csubN6_scal : ∀ adx : Bool, scalCode (.block (csub (fnModN6 adx) low6 top6)) = true := by decide +kernel

/-- The modulus of the product, as the rounds take it, once stored. -/
theorem modOkRN6 (adx : Bool) {Z : Nat} (hZ : 4096 ≤ Z) {mem : Mem} {base : Addr}
    (hv : wordsVal mem base fnMoN6 6 = n384) : ModOkR (fnModN6 adx) Z n384 mem base where
  n0 := by cases adx <;> decide
  n7 := by cases adx <;> decide
  mo := by simp only [fnModN6, fnMoN6, fnTmp6]; omega_using [hZ]
  val := .of_val hv
  inv := by cases adx <;> decide +kernel
  red := by cases adx <;> decide +kernel

theorem keepX6_ne : ∀ i j, i < j → j < 6 → keepX6 i ≠ keepX6 j := by
  intro i j hij hj
  obtain h : ∀ j < 6, ∀ i < j, keepX6 i ≠ keepX6 j := by decide
  exact h j hj i hij

theorem keepX6_ne6 : ∀ i < 6, keepX6 i ≠ .xmm6 := by decide

/-- The middle of `mulFnN6`: the product, `[o] = [a] [b] R⁻¹ mod n`, with `n`
stored over bytes it restores; it changes `[o]` and the temporary area only,
and no vector register but `xmm6`–`xmm12`. -/
theorem mulN6_ok (adx : Bool) {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    {o a b : Nat} (hbx : s.gpr .rbx = off base a) (hcx : s.gpr .rcx = off base b)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 o)
    (ho : ArgN6 Z o) (ha : ArgN6 Z a) (hb : ArgN6 Z b) (hB : wordsVal s.mem base b 6 < n384) :
    WP isa (.block (mulN6 adx)) s fun s' =>
      KeepRegs brClob s s' ∧
      (∀ x, (ofs base x < o ∨ o + 48 ≤ ofs base x) → (ofs base x < fnTmp6 ∨ 4096 ≤ ofs base x) →
        s'.mem x = s.mem x) ∧
      (∀ x, x ≠ .xmm6 → (∀ i < 6, x ≠ keepX6 i) → s'.xmm x = s.xmm x) ∧
      wordsVal s'.mem base o 6 < n384 ∧
      wordsVal s'.mem base o 6 * 2 ^ (64 * 6) % n384 = wordsVal s.mem base a 6 * wordsVal s.mem base b 6 % n384 := by
  have hnw := hs.nowrap
  unfold ArgN6 at ho ha hb
  rw [fnTmp6_eq] at ho ha hb ⊢
  simp only [mulN6, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (keepO_ok s) fun s₁ ⟨x₁, xo₁, e₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  rw [WP.block_append_iff]
  refine WP.mono (saveSteps_ok (d := fnMoN6) keepX6 6 s₁ hs₁ (by rw [fnMoN6_eq]; omega_using [hZ]) keepX6_ne)
    fun s₁' ⟨x₁', o₁', m₁', k₁'⟩ => ?_
  obtain hs₁' := hs₁.of_keepRegs k₁' (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep storeN6_scal
    (setConst_ok (n := 6) (o := fnMoN6) (x := n384) hs₁' (by rw [fnMoN6_eq]; omega_using [hZ]) n384_lt))
    fun s₂ ⟨⟨v₂, k₂, O₂⟩, x₂, _⟩ => ?_
  obtain hs₂ := hs₁'.of_keepRegs k₂ (by decide)
  obtain far : ∀ x, (x + 96 ≤ 4048 ∨ 4096 ≤ x) → x + 48 ≤ Z →
      wordsVal s₂.mem base x 6 = wordsVal s.mem base x 6 := fun x hx hxZ => by
    rw [(show Unch base [(fnMoN6, 8 * 6)] s₁'.mem s₂.mem from
      fun y hy => O₂ y (hy _ (List.mem_singleton_self _))).wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; dsimp only; rw [fnMoN6_eq]; omega_using [hx]) (by omega_using [hnw, hxZ]), m₁', hm₁]
  obtain g₂ : ∀ r, r ≠ .rax → s₂.gpr r = s₁.gpr r := fun r hr => by
    rw [k₂.gpr r (by simpa using hr), k₁'.gpr r (by simpa using hr)]
  have hp₂ : PtrsAt [(.rbx, a), (.rsi, b)] s₂ := .two
    (by rw [g₂ _ (by decide), k₁.1 _ (by decide), hbx, hs₂.rdi])
    (by rw [g₂ _ (by decide), e₁, hcx, hs₂.rdi])
  obtain w₃ := mulRounds_ok (M := fnModN6 adx) hs₂ (modOkRN6 adx hZ v₂) (a := a) (b := b)
    (by simp only [fnModN6]; omega_using [ha]) (by simp only [fnModN6]; omega_using [hb])
    (by simp only [fnModN6]; rw [far b hb.1 hb.2]; exact hB)
  rw [← mulRoundsN6_reloc adx, ← reloc_unptr] at w₃
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep (mulN6_scal adx) (wp_unptr (rs := [.rbx, .rsi]) (by simp) _ (mulN6_keeps adx) hp₂ w₃))
    fun s₃ ⟨⟨⟨U, eU⟩, hT, k₃⟩, x₃, _⟩ => ?_
  simp only [show (fnModN6 adx).n = 6 from rfl] at eU hT k₃
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  -- The accumulator's value as `csub` sees it: its top word is zero.
  obtain hV : regsVal s₃ low6 + 2 ^ (64 * 6) * (s₃.gpr top6).toNat = regsVal s₃ (wins 6 6) := by
    simp only [low6, top6]
    rw [wins_split 6 6, regsVal_append, show ((List.range 6).map (win 6 6)).length = 6 from rfl]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
    have hT' := hT
    rw [wins_split 6 6, regsVal_append, show ((List.range 6).map (win 6 6)).length = 6 from rfl] at hT'
    simp only [regsVal, Nat.mul_zero, Nat.add_zero] at hT'
    have hm' : n384 < 2 ^ (64 * 6) := n384_lt
    have : (s₃.gpr (win 6 6 (6 + 1))).toNat = 0 := by
      generalize (2 : Nat) ^ (64 * 6) = Q at hT' hm'
      by_contra hne
      have : Q * 2 ^ 64 ≤ Q * ((s₃.gpr (win 6 6 6)).toNat + 2 ^ 64 * (s₃.gpr (win 6 6 (6 + 1))).toNat) :=
        Nat.mul_le_mul_left _ (by omega_using [hne])
      omega_using [hT', hm', this]
    rw [this, Nat.mul_zero, Nat.add_zero]
  obtain hmo₃ : wordsVal s₃.mem base (fnModN6 adx).mo (fnModN6 adx).n = n384 := by rw [k₃.2.1]; exact v₂
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep (csubN6_scal adx) (csub_ok hs₃ (M := fnModN6 adx) (ts := low6) (top := top6) rfl (by simp only [fnModN6]; decide)
    ⟨by decide, by decide⟩ (by simp only [fnModN6, fnMoN6, fnTmp6]; omega_using [hZ]) (by simp only [fnModN6, fnTmp6]; omega_using [hZ])
    (by simp only [fnModN6, fnMoN6, fnTmp6]; omega_using []) (fun h => absurd h (by simp only [fnModN6]; decide)) hmo₃
    (by rw [show (fnModN6 adx).n = 6 from rfl, hV]; exact hT))) fun s₄ ⟨⟨e₄, k₄, O₄⟩, x₄, _⟩ => ?_
  simp only [show (fnModN6 adx).n = 6 from rfl] at e₄ O₄
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (backO_ok s₄) fun s₅ ⟨e₅, x₅, k₅⟩ => ?_
  obtain hs₅ := hs₄.of_keeps k₅ (by decide)
  obtain hp₅ : PtrsAt [(.rsi, o)] s₅ := .one (by
    rw [e₅, x₄, x₃, x₂, o₁' .xmm6 (fun j hj => (keepX6_ne6 j hj).symm), x₁, qword_lo, hsi, k₅.1 .rdi (by decide)])
  obtain w₆ := stores_ok low6 hs₅ (o := o) (by simp only [low6, List.length_map, List.length_range]; omega_using [ho])
    (by decide)
  rw [← storesL_reloc, ← reloc_unptr] at w₆
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep storesL_scal (wp_unptr (rs := [.rsi]) (by simp) _ storesL_keeps hp₅ w₆))
    fun s₆ ⟨⟨e₆, k₆, O₆⟩, x₆, _⟩ => ?_
  simp only [show low6.length = 6 from rfl, Nat.reduceMul] at e₆ O₆
  obtain hs₆ : Scr s₆ base Z := ⟨(k₆.gpr _ (by simp)).trans hs₅.rdi, k₆.wr ▸ hs₅.wr, hnw⟩
  refine WP.mono (restoreSteps_ok (d := fnMoN6) keepX6 6 s₆ hs₆ (by rw [fnMoN6_eq]; omega_using [hZ]))
    fun s₇ ⟨e₇, O₇, x₇, k₇⟩ => ?_
  obtain hval₆ : wordsVal s₆.mem base o 6 = regsVal s₃ (wins 6 6) % n384 := by
    rw [e₆, show regsVal s₅ low6 = regsVal s₄ low6 from regsVal_congr fun q hq => k₅.1 q (by
      intro h; simp only [List.mem_singleton] at h; subst h; revert hq; decide), e₄, hV]
  obtain hval : wordsVal s₇.mem base o 6 = regsVal s₃ (wins 6 6) % n384 := by
    rw [O₇.unch.wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; dsimp only; rw [fnMoN6_eq]; omega_using [ho]) (by omega_using [ho, hnw]), hval₆]
  have hm₃ : s₃.mem = s₂.mem := k₃.2.1
  refine ⟨⟨fun r hr => ?_, by rw [k₇.rd, k₆.rd, k₅.2.2.1, k₄.rd, k₃.2.2.1, k₂.rd, k₁'.rd, k₁.2.2.1],
      by rw [k₇.wr, k₆.wr, k₅.2.2.2, k₄.wr, k₃.2.2.2, k₂.wr, k₁'.wr, k₁.2.2.2]⟩,
    fun x hx hx' => ?_, fun x hx hx6 => ?_, ?_, ?_⟩
  · have hra : r ≠ .rax := fun h => hr (h ▸ by decide)
    rw [k₇.gpr r (by simpa using hra), k₆.gpr r (by simp), k₅.1 r (not_mem_of hr (by decide)),
      k₄.gpr r (not_mem_of hr (by decide)), k₃.1 r (not_mem_of hr (by decide)), g₂ r hra,
      k₁.1 r (not_mem_of hr (by decide))]
  · by_cases hin : 4000 ≤ ofs base x ∧ ofs base x < 4048
    · -- A byte of the words restored.
      obtain hp : ∃ i < 6, ∃ j < 8, x = off base (fnMoN6 + 8 * i) + BitVec.ofNat 64 j := by
        refine ⟨(ofs base x - 4000) / 8, by omega_using [hin], (ofs base x - 4000) % 8, Nat.mod_lt _ (by decide), ?_⟩
        rw [off, Offset.add_add, fnMoN6_eq, show 4000 + 8 * ((ofs base x - 4000) / 8) + (ofs base x - 4000) % 8 =
          ofs base x by omega_using [hin], BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      obtain ⟨i, hi, j, hj, rfl⟩ := hp
      obtain hw : word s₇.mem base (fnMoN6 + 8 * i) = word s.mem base (fnMoN6 + 8 * i) := by
        rw [e₇ i hi, x₆, x₅, x₄, x₃, x₂, x₁' i hi, qword_lo, hm₁]
      exact byte_of_word hw hj
    · rw [O₇ x (by rw [fnMoN6_eq]; omega_using [hin]), O₆ x hx, k₅.2.1, O₄ x (by simp only [fnModN6, fnTmp6]; omega_using [hx']), hm₃,
        O₂ x (by rw [fnMoN6_eq]; omega_using [hin]), m₁', hm₁]
  · rw [x₇, x₆, x₅, x₄, x₃, x₂, o₁' x hx6, xo₁ x hx]
  · rw [hval]; exact Nat.mod_lt _ (by decide)
  · rw [hval, Nat.mod_mul_mod, Nat.mul_comm, eU, far a ha.1 ha.2, far b hb.1 hb.2]
    simp only [Nat.add_mul_mod_self_right]

/-! ## The function -/

/-- `[o] = [a] [b] 2⁻³⁸⁴ mod n` for P-384's `n`, the offsets the low halves
of `rsi`, `rdx` and `rcx`: the function changes only `fnClob`, `[o]` and its
temporary area, bytes `fnTmp6` to 4095. -/
theorem mulFnN6_ok (adx : Bool) {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    (ho : ArgN6 Z (argOf s .rsi)) (ha : ArgN6 Z (argOf s .rdx)) (hb : ArgN6 Z (argOf s .rcx))
    (hB : wordsVal s.mem base (argOf s .rcx) 6 < n384) :
    WP isa (mulFnN6 adx) s fun s' =>
      wordsVal s'.mem base (argOf s .rsi) 6 < n384 ∧
      wordsVal s'.mem base (argOf s .rsi) 6 * (2 ^ 64) ^ 6 % n384 =
        wordsVal s.mem base (argOf s .rdx) 6 * wordsVal s.mem base (argOf s .rcx) 6 % n384 ∧
      KeepRegs fnClob s s' ∧
      ∀ x, (ofs base x < argOf s .rsi ∨ argOf s .rsi + 48 ≤ ofs base x) →
        (ofs base x < fnTmp6 ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x := by
  refine WP.seq (WP.mono (WP.block_append_iff.mp (entry_ok hs)) fun s₀ h₀ => WP.seq (WP.mono h₀
    fun s₁ ⟨hs₁, bx₁, cx₁, _, si₁, x0, x1, x2, x3, x4, x5, k₁, m₁⟩ => ?_))
  generalize hO : argOf s .rsi = o at *
  generalize hA : argOf s .rdx = a at *
  generalize hBb : argOf s .rcx = b at *
  obtain hQ : (2 : Nat) ^ (64 * 6) = (2 ^ 64) ^ 6 := Nat.pow_mul 2 64 6
  refine WP.seq (WP.mono (mulN6_ok adx hs₁ hZ bx₁ cx₁ si₁ ho ha hb (by rw [m₁]; exact hB))
    fun s₂ ⟨k₂, O₂, xm₂, lt₂, e₂⟩ => ?_)
  obtain xk : ∀ x, x ∈ [XReg.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5] → s₂.xmm x = s₁.xmm x := fun x hx =>
    xm₂ x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine WP.mono (restores_ok s₂) fun s₃ ⟨b₃, p₃, r12₃, r13₃, r14₃, r15₃, k₃⟩ => ?_
  rw [m₁] at e₂ O₂
  refine ⟨by rw [k₃.2.1]; exact lt₂, by rw [k₃.2.1, ← hQ]; exact e₂,
    ⟨fun r hr => ?_, by rw [k₃.2.2.1, k₂.rd, k₁.rd], by rw [k₃.2.2.2, k₂.wr, k₁.wr]⟩, fun x hx hx' => ?_⟩
  · rcases not_clob_cases r hr with hsv | rfl | rfl
    · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hsv
      rcases hsv with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [b₃, xk _ (by simp), x0, qword_lo]
      · rw [p₃, xk _ (by simp), x1, qword_lo]
      · rw [r12₃, xk _ (by simp), x2, qword_lo]
      · rw [r13₃, xk _ (by simp), x3, qword_lo]
      · rw [r14₃, xk _ (by simp), x4, qword_lo]
      · rw [r15₃, xk _ (by simp), x5, qword_lo]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  · rw [k₃.2.1, O₂ x hx hx']

end VG.Proof.Weierstrass.X86_64.Mont

end

end


/-!
# Products modulo P-521's and P-384's `p` by calls, on x86-64

`mulCall_ok`: a call of `vg_p521_mul_mod_p` or `vg_p521_mul_mod_p_adx`
(`Mont.mulCall`), inlined (`Code.inline`, as `CallInline.lean` relates it to
the call), keeps and computes what the inline product does
(`Proof/Mont/X86_64/Ops.lean`'s `mul_ok`), for P-521's `p` with the
functions' temporary area: the functions change only `[o]` and that area, and
the call keeps `rsi` in `r12`, which the functions restore. `mulCall6_ok` is
the same for `vg_p384_mul_mod_p` and `vg_p384_mul_mod_p_adx`, for offsets
apart from their temporary area (`lowArgs 6`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.Mont

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Impl.Weierstrass.X86_64.Mont
open VG.Proof.X25519.X86_64 (Keeps)

/-- The call's arguments: `rsi` into `r12`, the offsets into `esi`, `edx`
and `ecx`. -/
theorem callArgs_ok (s : State) {o a b : Nat} (ho : o < 2 ^ 32) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    WP isa (.block [.mov .r12 (.reg .rsi), .mov32 .rsi (.imm (BitVec.ofNat 32 o)),
      .mov32 .rdx (.imm (BitVec.ofNat 32 a)), .mov32 .rcx (.imm (BitVec.ofNat 32 b))]) s fun s' =>
      s'.gpr .r12 = s.gpr .rsi ∧ argOf s' .rsi = o ∧ argOf s' .rdx = a ∧ argOf s' .rcx = b ∧
      Keeps [.r12, .rsi, .rdx, .rcx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, Option.map_some,
    State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, reduceCtorEq, ite_true,
    ite_false, argOf, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  refine ⟨trivial, by omega_using [ho], by omega_using [ha], by omega_using [hb], fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2, RegUpd.gpr_setReg_of_ne _ _ hr.2.2.1,
    RegUpd.gpr_setReg_of_ne _ _ hr.2.1, RegUpd.gpr_setReg_of_ne _ _ hr.1]

/-- The code of either function, which calls none. -/
theorem fn_ok {body : Prog isa} (hbody : body = mulFn ∨ body = mulFnX) {s : State} {base : Addr} {Z : Nat}
    (hs : Scr s base Z) (hZ : 4096 ≤ Z) {m : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (ho : argOf s .rsi + 72 ≤ 3520) (ha : argOf s .rdx + 72 ≤ 3520) (hb : argOf s .rcx + 72 ≤ 3520)
    (hB : wordsVal s.mem base (argOf s .rcx) 9 < m) :
    WP isa body s fun s' =>
      wordsVal s'.mem base (argOf s .rsi) 9 < m ∧
      wordsVal s'.mem base (argOf s .rsi) 9 * (2 ^ 64) ^ 9 % m =
        wordsVal s.mem base (argOf s .rdx) 9 * wordsVal s.mem base (argOf s .rcx) 9 % m ∧
      KeepRegs fnClob s s' ∧
      ∀ x, (ofs base x < argOf s .rsi ∨ argOf s .rsi + 72 ≤ ofs base x) →
        (ofs base x < fnTmp ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x := by
  rcases hbody with rfl | rfl
  · exact mulFn_ok hs hZ hm ho ha hb hB
  · exact mulFnX_ok hs hZ hm ho ha hb hB

/-- The registers the inline products keep, for nine words. -/
theorem not_clob9 : ∀ r : Reg, r ∉ clob 9 → r = .rbx ∨ r = .rsp ∨ r = .rsi ∨ r = .rdi := by
  intro r; cases r <;> decide

/-- A product modulo P-521's `p` by a call of `body`, inlined: as the inline
product (`mul_ok`), for offsets below the functions' own working space. -/
theorem mulCall_ok {f : String} {body : Prog isa} (hbody : body = mulFn ∨ body = mulFnX) {s : State}
    {base : Addr} {Z : Nat} (hs : Scr s base Z) {M : Mod} {m : Nat} (hM : ModOkW M Z m s.mem base)
    (hred : M.red = .friendly p521Ws) (ht : M.tmp = fnTmp) {o a b : Nat} (hlow : lowArgs 9 o a b = true)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (mulCall f body o a b).inline s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  obtain ⟨hn9, hm⟩ := p521_of_red hred hM.red
  obtain hZ : 4096 ≤ Z := by have := hM.tmp; rw [ht, hn9] at this; simp only [fnTmp] at this; omega_using [this]
  simp only [lowArgs, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hlow
  obtain ⟨⟨ho, ha⟩, hb⟩ := hlow
  rw [hn9] at hB ⊢
  simp only [mulCall, Code.inline]
  refine WP.seq (WP.mono (callArgs_ok s (o := o) (a := a) (b := b) (by omega_using [ho]) (by omega_using [ha]) (by omega_using [hb]))
    fun s₁ ⟨r12₁, o₁, a₁, b₁, k₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  refine WP.seq (WP.mono (fn_ok hbody hs₁ hZ hm (by rw [o₁]; omega_using [ho]) (by rw [a₁]; omega_using [ha]) (by rw [b₁]; omega_using [hb])
    (by rw [b₁, hm₁]; exact hB)) fun s₂ ⟨lt₂, e₂, k₂, m₂⟩ => ?_)
  refine WP.mono (movReg_ok s₂ .rsi .r12) fun s₃ ⟨v₃, k₃⟩ => ?_
  rw [o₁] at lt₂ e₂ m₂
  rw [a₁, b₁, hm₁] at e₂
  have hm₃ : s₃.mem = s₂.mem := k₃.2.1
  refine ⟨⟨fun r hr => ?_, by rw [k₃.2.2.1, k₂.rd, k₁.2.2.1], by rw [k₃.2.2.2, k₂.wr, k₁.2.2.2],
    fun x hx ht' => ?_⟩, by rw [hm₃]; exact lt₂, by rw [hm₃, Nat.pow_mul 2 64 9]; exact e₂⟩
  · rw [hn9] at hr
    rcases not_clob9 r hr with rfl | rfl | rfl | rfl
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [v₃, k₂.gpr _ (by decide), r12₁]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
  · rw [hn9] at hx ht'
    rw [ht] at ht'
    rw [hm₃, m₂ x hx (by simp only [fnTmp] at ht' ⊢; omega_using [ht']), hm₁]

/-- The registers the inline products keep, for six words. -/
theorem not_clob6 : ∀ r : Reg, r ∉ clob 6 → r = .rbx ∨ r = .rsp ∨ r = .rsi ∨ r = .rdi := by
  intro r; cases r <;> decide

theorem fn6_ok {body : Prog isa} (hbody : body = mulFn6 false ∨ body = mulFn6 true) {s : State} {base : Addr}
    {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z) {m : Nat} (hm : m = p384) (ho : Arg6 Z (argOf s .rsi))
    (ha : Arg6 Z (argOf s .rdx)) (hb : Arg6 Z (argOf s .rcx)) (hB : wordsVal s.mem base (argOf s .rcx) 6 < m) :
    WP isa body s fun s' =>
      wordsVal s'.mem base (argOf s .rsi) 6 < m ∧
      wordsVal s'.mem base (argOf s .rsi) 6 * (2 ^ 64) ^ 6 % m =
        wordsVal s.mem base (argOf s .rdx) 6 * wordsVal s.mem base (argOf s .rcx) 6 % m ∧
      KeepRegs fnClob s s' ∧
      ∀ x, (ofs base x < argOf s .rsi ∨ argOf s .rsi + 48 ≤ ofs base x) →
        (ofs base x < fnTmp6 ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x := by
  rcases hbody with rfl | rfl
  · exact mulFn6_ok false hs hZ hm ho ha hb hB
  · exact mulFn6_ok true hs hZ hm ho ha hb hB

/-- A product modulo P-384's `p` by a call of `body`, inlined: as the inline
product (`mul_ok`), for offsets apart from the functions' temporary area. -/
theorem mulCall6_ok {f : String} {body : Prog isa} (hbody : body = mulFn6 false ∨ body = mulFn6 true)
    {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) {M : Mod} {m : Nat} (hM : ModOkW M Z m s.mem base)
    (hsp : M.sparse = true) (ht : M.tmp = fnTmp6) {o a b : Nat} (hlow : lowArgs 6 o a b = true)
    (hoZ : o + 8 * M.n ≤ Z) (haZ : a + 8 * M.n ≤ Z) (hbZ : b + 8 * M.n ≤ Z)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (mulCall f body o a b).inline s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  obtain ⟨hn6, hm⟩ := Mod.ok_sparse hM.red hsp
  obtain hZ : 4096 ≤ Z := by have := hM.tmp; rw [ht, hn6] at this; simp only [fnTmp6] at this; omega_using [this]
  simp only [lowArgs, show ¬ (6 = 9) by decide, show ¬ (6 = 8) by decide, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hlow
  obtain ⟨⟨ho, ha⟩, hb⟩ := hlow
  rw [hn6] at hB hoZ haZ hbZ ⊢
  obtain h31 : ∀ x, (x + 96 ≤ fnTmp6 ∨ 4096 ≤ x ∧ x < 2 ^ 31) → x < 2 ^ 32 := fun x h => by
    simp only [fnTmp6] at h; omega_using [h]
  simp only [mulCall, Code.inline]
  refine WP.seq (WP.mono (callArgs_ok s (o := o) (a := a) (b := b) (h31 o ho) (h31 a ha) (h31 b hb))
    fun s₁ ⟨r12₁, o₁, a₁, b₁, k₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  obtain arg : ∀ x, (x + 96 ≤ fnTmp6 ∨ 4096 ≤ x ∧ x < 2 ^ 31) → x + 48 ≤ Z → Arg6 Z x := fun x h hz =>
    ⟨h.imp (fun h => by simp only [fnTmp6] at h ⊢; omega_using [h]) And.left, hz⟩
  refine WP.seq (WP.mono (fn6_ok hbody hs₁ hZ hm (by rw [o₁]; exact arg o ho hoZ) (by rw [a₁]; exact arg a ha haZ)
    (by rw [b₁]; exact arg b hb hbZ) (by rw [b₁, hm₁]; exact hB)) fun s₂ ⟨lt₂, e₂, k₂, m₂⟩ => ?_)
  refine WP.mono (movReg_ok s₂ .rsi .r12) fun s₃ ⟨v₃, k₃⟩ => ?_
  rw [o₁] at lt₂ e₂ m₂
  rw [a₁, b₁, hm₁] at e₂
  have hm₃ : s₃.mem = s₂.mem := k₃.2.1
  refine ⟨⟨fun r hr => ?_, by rw [k₃.2.2.1, k₂.rd, k₁.2.2.1], by rw [k₃.2.2.2, k₂.wr, k₁.2.2.2],
    fun x hx ht' => ?_⟩, by rw [hm₃]; exact lt₂, by rw [hm₃, Nat.pow_mul 2 64 6]; exact e₂⟩
  · rw [hn6] at hr
    rcases not_clob6 r hr with rfl | rfl | rfl | rfl
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [v₃, k₂.gpr _ (by decide), r12₁]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
  · rw [hn6] at hx ht'
    rw [ht] at ht'
    rw [hm₃, m₂ x hx (by simp only [fnTmp6] at ht' ⊢; omega_using [ht']), hm₁]

/-- A product modulo P-521's `n` (`Mod.fnN`) by a call of `mulFnN`, inlined: as
the inline product, for the functions' temporary area. -/
theorem mulCallN_ok {f : String} {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) {M : Mod} {m : Nat}
    (hM : ModOkW M Z m s.mem base) (hf : M.fnN = true) (hn9 : M.n = 9) (ht : M.tmp = fnTmp)
    {o a b : Nat} (hlow : lowArgs 9 o a b = true) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (mulCall f mulFnN o a b).inline s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  obtain hm : m = n521 := by
    rcases Mod.ok_fnN hM.red hf with ⟨_, hm⟩ | ⟨h6, _⟩
    · exact hm
    · omega
  have hm' : m = n521 := hm
  obtain hZ : 4096 ≤ Z := by have := hM.tmp; rw [ht, hn9] at this; simp only [fnTmp] at this; omega_using [this]
  simp only [lowArgs, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hlow
  obtain ⟨⟨ho, ha⟩, hb⟩ := hlow
  rw [hn9] at hB ⊢
  simp only [mulCall, Code.inline]
  refine WP.seq (WP.mono (callArgs_ok s (o := o) (a := a) (b := b) (by omega_using [ho]) (by omega_using [ha]) (by omega_using [hb]))
    fun s₁ ⟨r12₁, o₁, a₁, b₁, k₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  refine WP.seq (WP.mono (mulFnN_ok hs₁ hZ (by rw [o₁]; exact ho) (by rw [a₁]; exact ha) (by rw [b₁]; exact hb)
    (by rw [b₁, hm₁, ← hm']; exact hB)) fun s₂ ⟨lt₂, e₂, k₂, m₂⟩ => ?_)
  refine WP.mono (movReg_ok s₂ .rsi .r12) fun s₃ ⟨v₃, k₃⟩ => ?_
  rw [o₁] at lt₂ e₂ m₂
  rw [a₁, b₁, hm₁] at e₂
  have hm₃ : s₃.mem = s₂.mem := k₃.2.1
  refine ⟨⟨fun r hr => ?_, by rw [k₃.2.2.1, k₂.rd, k₁.2.2.1], by rw [k₃.2.2.2, k₂.wr, k₁.2.2.2],
    fun x hx ht' => ?_⟩, by rw [hm₃, hm']; exact lt₂, by rw [hm₃, Nat.pow_mul 2 64 9, hm']; exact e₂⟩
  · rw [hn9] at hr
    rcases not_clob9 r hr with rfl | rfl | rfl | rfl
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [v₃, k₂.gpr _ (by decide), r12₁]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
  · rw [hn9] at hx ht'
    rw [ht] at ht'
    rw [hm₃, m₂ x hx (by simp only [fnTmp] at ht' ⊢; omega_using [ht']), hm₁]

theorem mulCall8_ok (order : Bool) {f : String} {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) {M : Mod} {m : Nat}
    (hM : ModOkW M Z m s.mem base) (hf : M.fnMod = some (Wide8.modulus order)) (hn8 : M.n = 8) (ht : M.tmp = Wide8.tmp)
    {o a b : Nat} (hlow : lowArgs 8 o a b = true) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (mulCall f (Wide8.fn order) o a b).inline s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  obtain hm' : m = Wide8.modulus order := (Mod.ok_fnMod hM.red hf).symm
  obtain hZ : 4096 ≤ Z := by have := hM.tmp; rw [ht, hn8] at this; simp only [Wide8.tmp] at this; omega_using [this]
  simp only [lowArgs, show ¬ (8 = 9) by decide, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hlow
  obtain ⟨⟨ho, ha⟩, hb⟩ := hlow
  rw [hn8] at hB ⊢
  simp only [mulCall, Code.inline]
  refine WP.seq (WP.mono (callArgs_ok s (o := o) (a := a) (b := b) (by omega_using [ho]) (by omega_using [ha]) (by omega_using [hb]))
    fun s₁ ⟨r12₁, o₁, a₁, b₁, k₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  refine WP.seq (WP.mono (Wide8.fn_ok order hs₁ hZ (by rw [o₁]; exact ho) (by rw [a₁]; exact ha) (by rw [b₁]; exact hb)
    (by rw [b₁, hm₁, ← hm']; exact hB)) fun s₂ ⟨lt₂, e₂, k₂, m₂⟩ => ?_)
  refine WP.mono (movReg_ok s₂ .rsi .r12) fun s₃ ⟨v₃, k₃⟩ => ?_
  rw [o₁] at lt₂ e₂ m₂
  rw [a₁, b₁, hm₁] at e₂
  have hm₃ : s₃.mem = s₂.mem := k₃.2.1
  refine ⟨⟨fun r hr => ?_, by rw [k₃.2.2.1, k₂.rd, k₁.2.2.1], by rw [k₃.2.2.2, k₂.wr, k₁.2.2.2],
    fun x hx ht' => ?_⟩, by rw [hm₃, hm']; exact lt₂, by rw [hm₃, Nat.pow_mul 2 64 8, hm']; exact e₂⟩
  · rw [hn8] at hr
    rcases not_clob9 r (show r ∉ clob 9 from hr) with rfl | rfl | rfl | rfl
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [v₃, k₂.gpr _ (by decide), r12₁]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
  · rw [hn8] at hx ht'
    rw [ht] at ht'
    rw [hm₃, m₂ x hx (by simp only [Wide8.tmp] at ht' ⊢; omega_using [ht']), hm₁]

theorem fnN6_ok {body : Prog isa} (hbody : body = mulFnN6 false ∨ body = mulFnN6 true) {s : State} {base : Addr}
    {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z) (ho : ArgN6 Z (argOf s .rsi))
    (ha : ArgN6 Z (argOf s .rdx)) (hb : ArgN6 Z (argOf s .rcx)) (hB : wordsVal s.mem base (argOf s .rcx) 6 < n384) :
    WP isa body s fun s' =>
      wordsVal s'.mem base (argOf s .rsi) 6 < n384 ∧
      wordsVal s'.mem base (argOf s .rsi) 6 * (2 ^ 64) ^ 6 % n384 =
        wordsVal s.mem base (argOf s .rdx) 6 * wordsVal s.mem base (argOf s .rcx) 6 % n384 ∧
      KeepRegs fnClob s s' ∧
      ∀ x, (ofs base x < argOf s .rsi ∨ argOf s .rsi + 48 ≤ ofs base x) →
        (ofs base x < fnTmp6 ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x := by
  rcases hbody with rfl | rfl
  · exact mulFnN6_ok false hs hZ ho ha hb hB
  · exact mulFnN6_ok true hs hZ ho ha hb hB

/-- A product modulo P-384's `n` (`Mod.fnN`) by a call of `mulFnN6 adx`, inlined:
as the inline product, for offsets apart from `n` and the functions'
temporary area. -/
theorem mulCallN6_ok {f : String} {body : Prog isa} (hbody : body = mulFnN6 false ∨ body = mulFnN6 true) {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) {M : Mod} {m : Nat}
    (hM : ModOkW M Z m s.mem base) (hf : M.fnN = true) (hn6 : M.n = 6) (ht : M.tmp = fnTmp6)
    {o a b : Nat} (hlow : lowArgs 6 o a b = true)
    (hoZ : o + 8 * M.n ≤ Z) (haZ : a + 8 * M.n ≤ Z) (hbZ : b + 8 * M.n ≤ Z)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (mulCall f body o a b).inline s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  obtain hm : m = n384 := by
    rcases Mod.ok_fnN hM.red hf with ⟨h9, _⟩ | ⟨_, hm⟩
    · omega
    · exact hm
  obtain hZ : 4096 ≤ Z := by have := hM.tmp; rw [ht, hn6] at this; simp only [fnTmp6] at this; omega_using [this]
  simp only [lowArgs, show ¬ (6 = 9) by decide, show ¬ (6 = 8) by decide, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hlow
  obtain ⟨⟨ho, ha⟩, hb⟩ := hlow
  rw [hn6] at hB hoZ haZ hbZ ⊢
  obtain h31 : ∀ x, (x + 96 ≤ fnTmp6 ∨ 4096 ≤ x ∧ x < 2 ^ 31) → x < 2 ^ 32 := fun x h => by
    simp only [fnTmp6] at h; omega_using [h]
  simp only [mulCall, Code.inline]
  refine WP.seq (WP.mono (callArgs_ok s (o := o) (a := a) (b := b) (h31 o ho) (h31 a ha) (h31 b hb))
    fun s₁ ⟨r12₁, o₁, a₁, b₁, k₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  obtain arg : ∀ x, (x + 96 ≤ fnTmp6 ∨ 4096 ≤ x ∧ x < 2 ^ 31) → x + 48 ≤ Z → ArgN6 Z x := fun x h hz =>
    ⟨h.imp id And.left, hz⟩
  refine WP.seq (WP.mono (fnN6_ok hbody hs₁ hZ (by rw [o₁]; exact arg o ho hoZ) (by rw [a₁]; exact arg a ha haZ)
    (by rw [b₁]; exact arg b hb hbZ) (by rw [b₁, hm₁, ← hm]; exact hB)) fun s₂ ⟨lt₂, e₂, k₂, m₂⟩ => ?_)
  refine WP.mono (movReg_ok s₂ .rsi .r12) fun s₃ ⟨v₃, k₃⟩ => ?_
  rw [o₁] at lt₂ e₂ m₂
  rw [a₁, b₁, hm₁] at e₂
  have hm₃ : s₃.mem = s₂.mem := k₃.2.1
  refine ⟨⟨fun r hr => ?_, by rw [k₃.2.2.1, k₂.rd, k₁.2.2.1], by rw [k₃.2.2.2, k₂.wr, k₁.2.2.2],
    fun x hx ht' => ?_⟩, by rw [hm₃, hm]; exact lt₂, by rw [hm₃, Nat.pow_mul 2 64 6, hm]; exact e₂⟩
  · rw [hn6] at hr
    rcases not_clob6 r hr with rfl | rfl | rfl | rfl
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [v₃, k₂.gpr _ (by decide), r12₁]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
  · rw [hn6] at hx ht'
    rw [ht] at ht'
    rw [hm₃, m₂ x hx (by simp only [fnTmp6] at ht' ⊢; omega_using [ht']), hm₁]

end VG.Proof.Weierstrass.X86_64.Mont
