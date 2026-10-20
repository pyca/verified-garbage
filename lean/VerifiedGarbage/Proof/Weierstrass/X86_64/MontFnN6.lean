module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFn6
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnN
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Mont.X86_64.CsubS
import VerifiedGarbage.Proof.Mont.X86_64.Chain
import VerifiedGarbage.Proof.Mont.X86_64.Round
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block

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
  have h : ∀ j < 6, ∀ i < j, keepX6 i ≠ keepX6 j := by decide
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
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  rw [WP.block_append_iff]
  refine WP.mono (saveSteps_ok (d := fnMoN6) keepX6 6 s₁ hs₁ (by rw [fnMoN6_eq]; omega_using [hZ]) keepX6_ne)
    fun s₁' ⟨x₁', o₁', m₁', k₁'⟩ => ?_
  have hs₁' := hs₁.of_keepRegs k₁' (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep storeN6_scal
    (setConst_ok (n := 6) (o := fnMoN6) (x := n384) hs₁' (by rw [fnMoN6_eq]; omega_using [hZ]) n384_lt))
    fun s₂ ⟨⟨v₂, k₂, O₂⟩, x₂, _⟩ => ?_
  have hs₂ := hs₁'.of_keepRegs k₂ (by decide)
  have far : ∀ x, (x + 96 ≤ 4048 ∨ 4096 ≤ x) → x + 48 ≤ Z →
      wordsVal s₂.mem base x 6 = wordsVal s.mem base x 6 := fun x hx hxZ => by
    rw [(show Unch base [(fnMoN6, 8 * 6)] s₁'.mem s₂.mem from
      fun y hy => O₂ y (hy _ (List.mem_singleton_self _))).wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; dsimp only; rw [fnMoN6_eq]; omega_using [hx]) (by omega_using [hnw, hxZ]), m₁', hm₁]
  have g₂ : ∀ r, r ≠ .rax → s₂.gpr r = s₁.gpr r := fun r hr => by
    rw [k₂.gpr r (by simpa using hr), k₁'.gpr r (by simpa using hr)]
  have hp₂ : PtrsAt [(.rbx, a), (.rsi, b)] s₂ := .two
    (by rw [g₂ _ (by decide), k₁.1 _ (by decide), hbx, hs₂.rdi])
    (by rw [g₂ _ (by decide), e₁, hcx, hs₂.rdi])
  have w₃ := mulRounds_ok (M := fnModN6 adx) hs₂ (modOkRN6 adx hZ v₂) (a := a) (b := b)
    (by simp only [fnModN6]; omega_using [ha]) (by simp only [fnModN6]; omega_using [hb])
    (by simp only [fnModN6]; rw [far b hb.1 hb.2]; exact hB)
  rw [← mulRoundsN6_reloc adx, ← reloc_unptr] at w₃
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep (mulN6_scal adx) (wp_unptr (rs := [.rbx, .rsi]) (by simp) _ (mulN6_keeps adx) hp₂ w₃))
    fun s₃ ⟨⟨⟨U, eU⟩, hT, k₃⟩, x₃, _⟩ => ?_
  simp only [show (fnModN6 adx).n = 6 from rfl] at eU hT k₃
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  -- The accumulator's value as `csub` sees it: its top word is zero.
  have hV : regsVal s₃ low6 + 2 ^ (64 * 6) * (s₃.gpr top6).toNat = regsVal s₃ (wins 6 6) := by
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
  have hmo₃ : wordsVal s₃.mem base (fnModN6 adx).mo (fnModN6 adx).n = n384 := by rw [k₃.2.1]; exact v₂
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep (csubN6_scal adx) (csub_ok hs₃ (M := fnModN6 adx) (ts := low6) (top := top6) rfl (by simp only [fnModN6]; decide)
    ⟨by decide, by decide⟩ (by simp only [fnModN6, fnMoN6, fnTmp6]; omega_using [hZ]) (by simp only [fnModN6, fnTmp6]; omega_using [hZ])
    (by simp only [fnModN6, fnMoN6, fnTmp6]; omega_using []) (fun h => absurd h (by simp only [fnModN6]; decide)) hmo₃
    (by rw [show (fnModN6 adx).n = 6 from rfl, hV]; exact hT))) fun s₄ ⟨⟨e₄, k₄, O₄⟩, x₄, _⟩ => ?_
  simp only [show (fnModN6 adx).n = 6 from rfl] at e₄ O₄
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (backO_ok s₄) fun s₅ ⟨e₅, x₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  have hp₅ : PtrsAt [(.rsi, o)] s₅ := .one (by
    rw [e₅, x₄, x₃, x₂, o₁' .xmm6 (fun j hj => (keepX6_ne6 j hj).symm), x₁, qword_lo, hsi, k₅.1 .rdi (by decide)])
  have w₆ := stores_ok low6 hs₅ (o := o) (by simp only [low6, List.length_map, List.length_range]; omega_using [ho])
    (by decide)
  rw [← storesL_reloc, ← reloc_unptr] at w₆
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep storesL_scal (wp_unptr (rs := [.rsi]) (by simp) _ storesL_keeps hp₅ w₆))
    fun s₆ ⟨⟨e₆, k₆, O₆⟩, x₆, _⟩ => ?_
  simp only [show low6.length = 6 from rfl, Nat.reduceMul] at e₆ O₆
  have hs₆ : Scr s₆ base Z := ⟨(k₆.gpr _ (by simp)).trans hs₅.rdi, k₆.wr ▸ hs₅.wr, hnw⟩
  refine WP.mono (restoreSteps_ok (d := fnMoN6) keepX6 6 s₆ hs₆ (by rw [fnMoN6_eq]; omega_using [hZ]))
    fun s₇ ⟨e₇, O₇, x₇, k₇⟩ => ?_
  have hval₆ : wordsVal s₆.mem base o 6 = regsVal s₃ (wins 6 6) % n384 := by
    rw [e₆, show regsVal s₅ low6 = regsVal s₄ low6 from regsVal_congr fun q hq => k₅.1 q (by
      intro h; simp only [List.mem_singleton] at h; subst h; revert hq; decide), e₄, hV]
  have hval : wordsVal s₇.mem base o 6 = regsVal s₃ (wins 6 6) % n384 := by
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
      have hp : ∃ i < 6, ∃ j < 8, x = off base (fnMoN6 + 8 * i) + BitVec.ofNat 64 j := by
        refine ⟨(ofs base x - 4000) / 8, by omega_using [hin], (ofs base x - 4000) % 8, Nat.mod_lt _ (by decide), ?_⟩
        rw [off, Offset.add_add, fnMoN6_eq, show 4000 + 8 * ((ofs base x - 4000) / 8) + (ofs base x - 4000) % 8 =
          ofs base x by omega_using [hin], BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      obtain ⟨i, hi, j, hj, rfl⟩ := hp
      have hw : word s₇.mem base (fnMoN6 + 8 * i) = word s.mem base (fnMoN6 + 8 * i) := by
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
  have hQ : (2 : Nat) ^ (64 * 6) = (2 ^ 64) ^ 6 := Nat.pow_mul 2 64 6
  refine WP.seq (WP.mono (mulN6_ok adx hs₁ hZ bx₁ cx₁ si₁ ho ha hb (by rw [m₁]; exact hB))
    fun s₂ ⟨k₂, O₂, xm₂, lt₂, e₂⟩ => ?_)
  have xk : ∀ x, x ∈ [XReg.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5] → s₂.xmm x = s₁.xmm x := fun x hx =>
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
