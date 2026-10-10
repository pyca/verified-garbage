import VerifiedGarbage.Proof.Weierstrass.X86_64.Reloc
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnX
import VerifiedGarbage.Proof.Mont.X86_64.SqrM
import VerifiedGarbage.Proof.Mont.X86_64.MulS
import VerifiedGarbage.Proof.Mont.X86_64.CsubR

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
  simp only [sqrSA_eq, List.map_append]
  cases adx <;>
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) rfl (congrArg₂ (· ++ ·) rfl rfl)) (congrArg₂ (· ++ ·) rfl
    (congrArg₂ (· ++ ·) rfl (congrArg₂ (· ++ ·) rfl (congrArg₂ (· ++ ·) rfl (congrArg₂ (· ++ ·) rfl
      (congrArg₂ (· ++ ·) rfl rfl))))))

theorem mulRounds_reloc (adx : Bool) (a b : Nat) :
    (mulRounds (fnMod6 adx) mA mB).map
        (Instr.mapMem (unptr [(.rbx, a), (.rsi, b)] ∘ relocTo [(mA, .rbx), (mB, .rsi)])) =
      mulRounds (fnMod6 adx) a b := by
  cases adx
  · simp only [mulRounds, show (fnMod6 false).adx = false from rfl, Bool.false_eq_true, false_and, ↓reduceIte,
      show (fnMod6 false).n = 6 from rfl, show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.map_append]
    refine congrArg₂ (· ++ ·) rfl (congrArg₂ (· ++ ·) rfl (congrArg₂ (· ++ ·) rfl (congrArg₂ (· ++ ·) rfl
      (congrArg₂ (· ++ ·) rfl (congrArg₂ (· ++ ·) rfl rfl)))))
  · simp only [mulRounds, show (fnMod6 true).adx = true from rfl, show (fnMod6 true).sparse = true from rfl,
      show (fnMod6 true).n = 6 from rfl, and_self, ↓reduceIte,
      show List.range 5 = [0, 1, 2, 3, 4] from rfl, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.map_append]
    refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) rfl rfl) (congrArg₂ (· ++ ·) rfl (congrArg₂ (· ++ ·) rfl
      (congrArg₂ (· ++ ·) rfl (congrArg₂ (· ++ ·) rfl rfl))))

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

theorem off_eq (base : Addr) (x : Nat) : off base x = base + BitVec.ofNat 64 x := rfl

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
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hp₁ : PtrsAt [(.rbx, a), (.rsi, o)] s₁ := .two (by rw [k₁.1 _ (by decide), hbx, hs₁.rdi])
    (by rw [e₁, k₁.1 _ (by decide), hs.rdi, hsi])
  have w₂ := sqrSA_ok (M := fnMod6 adx) hs₁ hm (by simp only [fnMod6, fnTmp6]; omega) (o := o) (a := a)
    (by omega) (by omega) (by simp only [fnMod6, fnTmp6]; omega) (by simp only [fnMod6, fnTmp6]; omega)
    (by rw [k₁.2.1]; exact hA)
  rw [← sqrSA_reloc, ← reloc_unptr] at w₂
  rw [WP.block_append_iff]
  refine WP.mono (wp_unptr (rs := [.rbx, .rsi]) (by simp) _ (sqr_keeps adx) hp₁ w₂)
    fun s₂ ⟨k₂, O₂, _, lt₂, res₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (csubR_ok s₂ (ts := sqWin6) (top := .r8) rfl ⟨by decide, by decide⟩ hm lt₂)
    fun s₃ ⟨e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have hp₃ : PtrsAt [(.rsi, o)] s₃ := .one (by
    rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₃.1 .rdi (by decide), k₂.gpr .rdi (by decide)]
    exact hp₁ .rsi o rfl)
  have w₄ := stores_ok sqWin6 hs₃ (o := o) (by simp only [sqWin6, List.length_cons, List.length_nil]; omega)
    (by decide)
  rw [← storesW_reloc, ← reloc_unptr] at w₄
  refine WP.mono (wp_unptr (rs := [.rsi]) (by simp) _ storesW_keeps hp₃ w₄)
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  simp only [show sqWin6.length = 6 from rfl, Nat.reduceMul] at e₄ O₄
  have hval : wordsVal s₄.mem base o 6 =
      (regsVal s₂ sqWin6 + 2 ^ (64 * 6) * (s₂.gpr .r8).toNat) % m := by rw [e₄, e₃]
  have hmem₁ : s₁.mem = s.mem := k₁.2.1
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun x hx hx' => ?_, ?_, ?_⟩
  · rw [k₄.gpr r (by simp), k₃.1 r (not_mem_of hr (by decide)), k₂.gpr r (not_mem_of hr (by decide)),
      k₁.1 r (not_mem_of hr (by decide))]
  · rw [k₄.rd, k₃.2.2.1, k₂.rd, k₁.2.2.1]
  · rw [k₄.wr, k₃.2.2.2, k₂.wr, k₁.2.2.2]
  · rw [O₄ x hx, k₃.2.1, O₂ x hx (by simp only [fnMod6, fnTmp6]; omega), hmem₁]
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
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hp₁ : PtrsAt [(.rbx, a), (.rsi, b)] s₁ := .two (by rw [k₁.1 _ (by decide), hbx, hs₁.rdi])
    (by rw [e₁, hcx, hs₁.rdi])
  have hmem₁ : s₁.mem = s.mem := k₁.2.1
  have w₂ := mulRounds_ok (M := fnMod6 adx) hs₁ (modOkR6 adx (by omega) hm _ _) (a := a) (b := b)
    (by simp only [fnMod6]; omega) (by simp only [fnMod6]; omega) (by rw [hmem₁]; exact hB)
  rw [← mulRounds_reloc, ← reloc_unptr] at w₂
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep (mul_scal adx) (wp_unptr (rs := [.rbx, .rsi]) (by simp) _ (mul_keeps adx) hp₁ w₂))
    fun s₂ ⟨⟨⟨U, eU⟩, hT, k₂⟩, x₂, _⟩ => ?_
  simp only [show (fnMod6 adx).n = 6 from rfl] at eU hT k₂
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  -- The accumulator's value as `csubR` sees it: its top word is zero.
  have hV : regsVal s₂ low6 + 2 ^ (64 * 6) * (s₂.gpr top6).toNat = regsVal s₂ (wins 6 6) := by
    simp only [low6, top6]
    rw [wins_split 6 6, regsVal_append, show ((List.range 6).map (win 6 6)).length = 6 from rfl]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
    have hT' := hT
    rw [wins_split 6 6, regsVal_append, show ((List.range 6).map (win 6 6)).length = 6 from rfl] at hT'
    simp only [regsVal, Nat.mul_zero, Nat.add_zero] at hT'
    have hm' : m < 2 ^ (64 * 6) := (p384_bounds hm).1
    have : (s₂.gpr (win 6 6 (6 + 1))).toNat = 0 := by
      generalize (2 : Nat) ^ (64 * 6) = Q at hT' hm'
      by_contra hne
      have : Q * 2 ^ 64 ≤ Q * ((s₂.gpr (win 6 6 6)).toNat + 2 ^ 64 * (s₂.gpr (win 6 6 (6 + 1))).toNat) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    rw [this, Nat.mul_zero, Nat.add_zero]
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep csubR_scal (csubR_ok s₂ (ts := low6) (top := top6) rfl ⟨by decide, by decide⟩ hm
    (by rw [hV]; exact hT))) fun s₃ ⟨⟨e₃, k₃⟩, x₃, _⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (backO_ok s₃) fun s₄ ⟨e₄, x₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have hp₄ : PtrsAt [(.rsi, o)] s₄ := .one (by
    rw [e₄, x₃, x₂, x₁, qword_lo, hsi, k₄.1 .rdi (by decide)])
  have w₅ := stores_ok low6 hs₄ (o := o) (by simp only [low6, List.length_map, List.length_range]; omega)
    (by decide)
  rw [← storesL_reloc, ← reloc_unptr] at w₅
  refine WP.mono (WP.vecKeep storesL_scal (wp_unptr (rs := [.rsi]) (by simp) _ storesL_keeps hp₄ w₅))
    fun s₅ ⟨⟨e₅, k₅, O₅⟩, x₅, _⟩ => ?_
  simp only [show low6.length = 6 from rfl, Nat.reduceMul] at e₅ O₅
  have hval : wordsVal s₅.mem base o 6 = regsVal s₂ (wins 6 6) % m := by
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
  have hQ : (2 : Nat) ^ (64 * 6) = (2 ^ 64) ^ 6 := Nat.pow_mul 2 64 6
  refine WP.seq (WP.mono (show WP isa (.ite .e (.block (sqr6 adx)) (.block (mul6 adx))) s₁ (fun s' =>
      KeepRegs brClob s₁ s' ∧
      (∀ x, (ofs base x < o ∨ o + 48 ≤ ofs base x) → (ofs base x < fnTmp6 ∨ 4096 ≤ ofs base x) →
        s'.mem x = s₁.mem x) ∧
      wordsVal s'.mem base o 6 < m ∧
      wordsVal s'.mem base o 6 * 2 ^ (64 * 6) % m = wordsVal s₁.mem base a 6 * wordsVal s₁.mem base b 6 % m ∧
      ∀ x, x ≠ .xmm6 → s'.xmm x = s₁.xmm x) from ?_) fun s₂ h₂ => ?_)
  · refine WP.ite (decide (a = b)) zf₁ (fun h => ?_) (fun _ => mul6_ok adx hs₁ hZ hm bx₁ cx₁ si₁ ho ha hb
      (by rw [m₁]; exact hB))
    have hab : a = b := of_decide_eq_true h
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
