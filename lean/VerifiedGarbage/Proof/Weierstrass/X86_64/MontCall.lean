import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnB
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFn6
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Framework.X86_64.CallInline

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
  refine ⟨trivial, by omega, by omega, by omega, fun r hr => ?_, rfl, rfl, rfl⟩
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
  have hZ : 4096 ≤ Z := by have := hM.tmp; rw [ht, hn9] at this; simp only [fnTmp] at this; omega
  simp only [lowArgs, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hlow
  obtain ⟨⟨ho, ha⟩, hb⟩ := hlow
  rw [hn9] at hB ⊢
  simp only [mulCall, Code.inline]
  refine WP.seq (WP.mono (callArgs_ok s (o := o) (a := a) (b := b) (by omega) (by omega) (by omega))
    fun s₁ ⟨r12₁, o₁, a₁, b₁, k₁⟩ => ?_)
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  refine WP.seq (WP.mono (fn_ok hbody hs₁ hZ hm (by rw [o₁]; omega) (by rw [a₁]; omega) (by rw [b₁]; omega)
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
    rw [hm₃, m₂ x hx (by simp only [fnTmp] at ht' ⊢; omega), hm₁]

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
  have hZ : 4096 ≤ Z := by have := hM.tmp; rw [ht, hn6] at this; simp only [fnTmp6] at this; omega
  simp only [lowArgs, show ¬ (6 = 9) by decide, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hlow
  obtain ⟨⟨ho, ha⟩, hb⟩ := hlow
  rw [hn6] at hB hoZ haZ hbZ ⊢
  have h31 : ∀ x, (x + 48 ≤ fnTmp6 ∨ 4096 ≤ x ∧ x < 2 ^ 31) → x < 2 ^ 32 := fun x h => by
    simp only [fnTmp6] at h; omega
  simp only [mulCall, Code.inline]
  refine WP.seq (WP.mono (callArgs_ok s (o := o) (a := a) (b := b) (h31 o ho) (h31 a ha) (h31 b hb))
    fun s₁ ⟨r12₁, o₁, a₁, b₁, k₁⟩ => ?_)
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have arg : ∀ x, (x + 48 ≤ fnTmp6 ∨ 4096 ≤ x ∧ x < 2 ^ 31) → x + 48 ≤ Z → Arg6 Z x := fun x h hz =>
    ⟨h.imp id And.left, hz⟩
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
    rw [hm₃, m₂ x hx (by simp only [fnTmp6] at ht' ⊢; omega), hm₁]

end VG.Proof.Weierstrass.X86_64.Mont
