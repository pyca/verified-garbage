import VerifiedGarbage.Proof.Weierstrass.X86_64.Reloc
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnX
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Mont.X86_64.MulF
import VerifiedGarbage.Proof.Weierstrass.Unch

/-!
# P-521's product modulo `n` as a function, on x86-64

`mulFnN` (`Impl/Weierstrass/X86_64/Mont.lean`) stores `n` at `fnMoN`
(`setConst`), then runs the inline product by columns `mulF` relocated: its
operands at the markers read through `rbx = ws + a`, `rbp = ws + b` and
`rsi = ws + o`. With those registers so (`PtrsAt`), the relocated code runs
as the inline code at the offsets `a`, `b` and `o` (`wp_unptr`,
`mulF_reloc`), whose proof then applies (`mulF_ok`), `n` now in memory. The
function changes only `fnClob`, `[o]` and bytes `fnMoN` to 4095, where it
leaves `n` (`mulFnN_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64.Mont

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Impl.Weierstrass.X86_64.Mont
open VG.Proof.Weierstrass (Unch)
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

theorem fnMoN_eq : fnMoN = 3952 := rfl

theorem n521_lt : n521 < 2 ^ (64 * 9) := by decide +kernel

/-! ## The relocated code is the inline code -/

theorem mulF_reloc (o a b : Nat) :
    (mulF fnModN mO mA mB).map
        (Instr.mapMem (unptr [(.rbx, a), (.rbp, b), (.rsi, o)] ∘ relocTo [(mA, .rbx), (mB, .rbp), (mO, .rsi)])) =
      mulF fnModN o a b := by
  simp only [mulF, show List.range (2 * fnModN.n) =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] from rfl,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append]
  repeat (first | rfl | refine congrArg₂ (· ++ ·) ?_ ?_)

theorem mulN_keeps :
    (reloc [(mA, .rbx), (mB, .rbp), (mO, .rsi)] (mulF fnModN mO mA mB)).all
      (keepsPtrs [.rbx, .rbp, .rsi]) = true := by
  decide +kernel

theorem mulN_scal : scalCode (.block mulN) = true := by decide +kernel

theorem PtrsAt.three {s : State} {r r' r'' : Reg} {c c' c'' : Nat} (h : s.gpr r = s.gpr .rdi + BitVec.ofNat 64 c)
    (h' : s.gpr r' = s.gpr .rdi + BitVec.ofNat 64 c') (h'' : s.gpr r'' = s.gpr .rdi + BitVec.ofNat 64 c'') :
    PtrsAt [(r, c), (r', c'), (r'', c'')] s := by
  intro q d hq
  simp only [List.lookup] at hq
  split at hq
  · rename_i he; cases hq; exact (beq_iff_eq.mp he) ▸ h
  · exact PtrsAt.two h' h'' q d hq

/-- The modulus of the product, as `mulF` takes it, once stored. -/
theorem modOkN {Z : Nat} (hZ : 4096 ≤ Z) {mem : Mem} {base : Addr} (hv : wordsVal mem base fnMoN 9 = n521) :
    ModOkW fnModN Z n521 mem base where
  n0 := by decide
  mo := by simp only [fnModN, fnMoN, fnTmp]; omega
  tmp := by simp only [fnModN, fnTmp]; omega
  sep := by decide
  val := hv
  inv := by decide +kernel
  red := by decide +kernel

/-- `rbp = rcx`, `rsi += rdi`. -/
theorem ptrsN_ok (s : State) :
    WP isa (.block [.mov .rbp (.reg .rcx), .alu .add .rsi (.reg .rdi)]) s fun s' =>
      s'.gpr .rbp = s.gpr .rcx ∧ s'.gpr .rsi = s.gpr .rdi + s.gpr .rsi ∧ Keeps [.rbp, .rsi] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨?_, BitVec.add_comm _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ↓reduceIte]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr.2, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr.1]

/-- The middle of `mulFnN`: `n` stored and the product, `[o] = [a] [b] R⁻¹
mod n`; it changes `[o]` and bytes `fnMoN` to 4095 only, leaving `n` at
`fnMoN`, and no vector register. -/
theorem mulN_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    {o a b : Nat} (hbx : s.gpr .rbx = off base a) (hcx : s.gpr .rcx = off base b)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 o)
    (ho : o + 72 ≤ 3520) (ha : a + 72 ≤ 3520) (hb : b + 72 ≤ 3520) (hB : wordsVal s.mem base b 9 < n521) :
    WP isa (.block mulN) s fun s' =>
      KeepRegs (.rbp :: .rsi :: clob 9) s s' ∧
      (∀ x, (ofs base x < o ∨ o + 72 ≤ ofs base x) → (ofs base x < fnMoN ∨ 4096 ≤ ofs base x) →
        s'.mem x = s.mem x) ∧
      wordsVal s'.mem base fnMoN 9 = n521 ∧
      wordsVal s'.mem base o 9 < n521 ∧
      wordsVal s'.mem base o 9 * 2 ^ (64 * 9) % n521 = wordsVal s.mem base a 9 * wordsVal s.mem base b 9 % n521 := by
  have hnw := hs.nowrap
  simp only [mulN, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ptrsN_ok s) fun s₁ ⟨bp₁, si₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok (n := 9) (o := fnMoN) (x := n521) hs₁ (by rw [fnMoN_eq]; omega) n521_lt)
    fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have far : ∀ x, x + 72 ≤ 3520 → wordsVal s₂.mem base x 9 = wordsVal s.mem base x 9 := fun x hx => by
    rw [(show Unch base [(fnMoN, 8 * 9)] s₁.mem s₂.mem from
      fun y hy => O₂ y (hy _ (List.mem_singleton_self _))).wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; dsimp only; rw [fnMoN_eq]; omega) (by omega), hm₁]
  have hp₂ : PtrsAt [(.rbx, a), (.rbp, b), (.rsi, o)] s₂ := .three
    (by rw [k₂.gpr _ (by decide), k₁.1 _ (by decide), hbx, hs₂.rdi])
    (by rw [k₂.gpr _ (by decide), bp₁, hcx, hs₂.rdi])
    (by rw [k₂.gpr _ (by decide), si₁, hsi, hs.rdi, hs₂.rdi])
  have w₃ := mulF_ok hs₂ (modOkN hZ v₂) rfl (o := o) (a := a) (b := b)
    (by simp only [fnModN]; omega) (by simp only [fnModN]; omega) (by simp only [fnModN]; omega)
    (by simp only [fnModN, fnTmp]; omega) (by simp only [fnModN, fnTmp]; omega)
    (by simp only [fnModN, fnTmp]; omega) (by simp only [fnModN, fnMoN, fnTmp]; omega)
    (by simp only [fnModN]; rw [far b hb]; exact hB)
  rw [← mulF_reloc, ← reloc_unptr] at w₃
  refine WP.mono (wp_unptr (rs := [.rbx, .rbp, .rsi]) (by simp) _ mulN_keeps hp₂ w₃)
    fun s₃ ⟨k₃, lt₃, e₃⟩ => ?_
  simp only [show fnModN.n = 9 from rfl] at k₃ lt₃ e₃
  refine ⟨⟨fun r hr => ?_, by rw [k₃.rd, k₂.rd, k₁.2.2.1], by rw [k₃.wr, k₂.wr, k₁.2.2.2]⟩,
    fun x hx hx' => ?_, ?_, lt₃, by rw [e₃, far a ha, far b hb]⟩
  · simp only [List.mem_cons, not_or] at hr
    rw [k₃.gpr r hr.2.2, k₂.gpr r (by
      intro h; simp only [List.mem_singleton] at h; subst h; exact hr.2.2 (by decide)),
      k₁.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.1⟩)]
  · rw [k₃.mem x hx (by simp only [fnModN, fnTmp]; rw [fnMoN_eq] at hx'; omega),
      O₂ x (by rw [fnMoN_eq] at hx' ⊢; omega), hm₁]
  · rw [show wordsVal s₃.mem base fnMoN 9 = wordsVal s₂.mem base fnMoN 9 from
      (show Unch base [(o, 8 * 9), (fnTmp, 8 * 9)] s₂.mem s₃.mem from fun y hy =>
        k₃.mem y (hy _ (List.mem_cons_self ..)) (hy _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))).wordsVal
        (fun w hw => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl <;> dsimp only <;> simp only [fnTmp, fnMoN] <;> omega) (by
        rw [fnMoN_eq]; omega)]
    exact v₂

/-- Two memories whose `k` words at `d` have the same number agree on their
bytes. -/
theorem mem_of_wordsVal {m m' : Mem} {base : Addr} :
    ∀ (k d : Nat), wordsVal m base d k = wordsVal m' base d k → d + 8 * k ≤ 2 ^ 64 →
      ∀ x, d ≤ ofs base x → ofs base x < d + 8 * k → m x = m' x
  | 0, _, _, _, _, h₁, h₂ => absurd h₂ (by omega)
  | k + 1, d, h, hb, x, h₁, h₂ => by
    simp only [wordsVal] at h
    have l₁ := (word m base d).isLt
    have l₂ := (word m' base d).isLt
    have hw : word m base d = word m' base d := BitVec.eq_of_toNat_eq (by omega)
    by_cases hx : ofs base x < d + 8
    · have hj : ofs base x - d < 8 := by omega
      have e : x = off base d + BitVec.ofNat 64 (ofs base x - d) := by
        rw [off, Offset.add_add, show d + (ofs base x - d) = ofs base x by omega, BitVec.ofNat_toNat,
          BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      have r : ∀ q : Mem, q (off base d + BitVec.ofNat 64 (ofs base x - d)) =
          (word q base d).extractLsb' (8 * (ofs base x - d)) 8 := fun q => by
        change _ = ((q.read (off base d) 8).setWidth 64).extractLsb' _ 8
        rw [BitVec.setWidth_eq, Mem.extractLsb'_read _ _ hj]
      rw [e, r m, r m', hw]
    · have hr : wordsVal m base (d + 8) k = wordsVal m' base (d + 8) k := by
        have := congrArg BitVec.toNat hw; omega
      exact mem_of_wordsVal k (d + 8) hr (by omega) x (by omega) (by omega)

/-! ## The function -/

/-- `[o] = [a] [b] 2⁻⁵⁷⁶ mod n` for P-521's `n`, the offsets the low halves of
`rsi`, `rdx` and `rcx`: the function changes only `fnClob`, `[o]` and bytes
`fnMoN` to 4095, where it leaves `n`. -/
theorem mulFnN_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    (ho : argOf s .rsi + 72 ≤ 3520) (ha : argOf s .rdx + 72 ≤ 3520) (hb : argOf s .rcx + 72 ≤ 3520)
    (hB : wordsVal s.mem base (argOf s .rcx) 9 < n521) :
    WP isa mulFnN s fun s' =>
      wordsVal s'.mem base (argOf s .rsi) 9 < n521 ∧
      wordsVal s'.mem base (argOf s .rsi) 9 * (2 ^ 64) ^ 9 % n521 =
        wordsVal s.mem base (argOf s .rdx) 9 * wordsVal s.mem base (argOf s .rcx) 9 % n521 ∧
      KeepRegs fnClob s s' ∧
      wordsVal s'.mem base fnMoN 9 = n521 ∧
      ∀ x, (ofs base x < argOf s .rsi ∨ argOf s .rsi + 72 ≤ ofs base x) →
        (ofs base x < fnMoN ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x := by
  refine WP.seq (WP.mono (WP.block_append_iff.mp (entry_ok hs)) fun s₀ h₀ => WP.seq (WP.mono h₀
    fun s₁ ⟨hs₁, bx₁, cx₁, _, si₁, x0, x1, x2, x3, x4, x5, k₁, m₁⟩ => ?_))
  generalize hO : argOf s .rsi = o at *
  generalize hA : argOf s .rdx = a at *
  generalize hBb : argOf s .rcx = b at *
  have hQ : (2 : Nat) ^ (64 * 9) = (2 ^ 64) ^ 9 := Nat.pow_mul 2 64 9
  refine WP.seq (WP.mono (WP.vecKeep mulN_scal (mulN_ok hs₁ hZ bx₁ cx₁ si₁ ho ha hb (by rw [m₁]; exact hB)))
    fun s₂ ⟨⟨k₂, O₂, n₂, lt₂, e₂⟩, xm₂, _⟩ => ?_)
  refine WP.mono (restores_ok s₂) fun s₃ ⟨b₃, p₃, r12₃, r13₃, r14₃, r15₃, k₃⟩ => ?_
  rw [m₁] at e₂ O₂
  refine ⟨by rw [k₃.2.1]; exact lt₂, by rw [k₃.2.1, ← hQ]; exact e₂,
    ⟨fun r hr => ?_, by rw [k₃.2.2.1, k₂.rd, k₁.rd], by rw [k₃.2.2.2, k₂.wr, k₁.wr]⟩,
    by rw [k₃.2.1]; exact n₂, fun x hx hx' => ?_⟩
  · rcases not_clob_cases r hr with hsv | rfl | rfl
    · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hsv
      rcases hsv with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [b₃, xm₂, x0, qword_lo]
      · rw [p₃, xm₂, x1, qword_lo]
      · rw [r12₃, xm₂, x2, qword_lo]
      · rw [r13₃, xm₂, x3, qword_lo]
      · rw [r14₃, xm₂, x4, qword_lo]
      · rw [r15₃, xm₂, x5, qword_lo]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  · rw [k₃.2.1, O₂ x hx hx']

end VG.Proof.Weierstrass.X86_64.Mont
