module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.Reloc
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnX
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Mont.X86_64.MulF
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# P-521's product modulo `n` as a function, on x86-64

`mulFnN` (`Impl/Weierstrass/X86_64/Mont.lean`) keeps the words at `fnMoN` in
`xmm6`–`xmm14` (`saveSteps_ok`), stores `n` there (`setConst`), then runs the
inline product by columns `mulF` relocated: its operands at the markers read
through `rbx = ws + a`, `rbp = ws + b` and `rsi = ws + o`. With those
registers so (`PtrsAt`), the relocated code runs as the inline code at the
offsets `a`, `b` and `o` (`wp_unptr`, `mulF_reloc`), whose proof then applies
(`mulF_ok`), `n` now in memory. It puts the words back (`restoreSteps_ok`),
so the function changes only `fnClob`, `[o]` and its temporary area, bytes
`fnTmp` to 4095 (`mulFnN_ok`).
-/

@[expose] public section

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
  kernel_rfl

theorem mulN_keeps :
    (reloc [(mA, .rbx), (mB, .rbp), (mO, .rsi)] (mulF fnModN mO mA mB)).all
      (keepsPtrs [.rbx, .rbp, .rsi]) = true := by
  decide +kernel

theorem storeN_scal : scalCode (.block storeN) = true := by decide +kernel

theorem mulFR_scal : scalCode (.block (reloc [(mA, .rbx), (mB, .rbp), (mO, .rsi)] (mulF fnModN mO mA mB))) = true := by
  decide +kernel

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
      s'.gpr .rbp = s.gpr .rcx ∧ s'.gpr .rsi = s.gpr .rdi + s.gpr .rsi ∧ Keeps [.rbp, .rsi] s s' ∧
        s'.xmm = s.xmm := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨?_, BitVec.add_comm _ _, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ↓reduceIte]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr.2, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr.1]

theorem ea_sc' {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (d : Nat) : s.ea (sc d) = off base d := by
  simp only [State.ea, sc, BitVec.ofInt_natCast, hs.rdi]

/-- Word `d` into `r`, through `rax`. -/
theorem saveStep_ok {s : State} {base : Addr} {Z d : Nat} (hs : Scr s base Z) (hd : d + 8 ≤ Z) (r : XReg) :
    WP isa (.block [.mov .rax (.mem (sc d)), .xop (.movq r .rax)]) s fun t =>
      t.xmm r = (0 : BitVec 64) ++ word s.mem base d ∧ (∀ x, x ≠ r → t.xmm x = s.xmm x) ∧
        t.mem = s.mem ∧ KeepRegs [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, readSrc, Option.map_some,
    State.load64, ea_sc, hs.rdi, ld_sc hs (d := d) (by omega), ite_true, Option.some.injEq,
    exists_eq_left', RegUpd.xmm_setXmm_self, RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun x hx => RegUpd.xmm_setXmm_of_ne _ _ hx, rfl, ⟨fun q hq => ?_, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg, hq, ite_false]

/-- `xs j` into word `d + 8 j`, through `rax`. -/
theorem restoreStep_ok {s : State} {base : Addr} {Z d : Nat} (hs : Scr s base Z) (hd : d + 8 ≤ Z) (r : XReg) :
    WP isa (.block [.movqR .rax r, .store (sc d) .rax]) s fun t =>
      t.mem = s.mem.writeW (off base d) (qword (s.xmm r) 0) ∧ t.xmm = s.xmm ∧ KeepRegs [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_sc,
    RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, reduceCtorEq, ite_true, ite_false,
    hs.rdi, st_sc hs (d := d) (by omega), Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ⟨fun q hq => ?_, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [RegUpd.gpr_setReg, hq, ite_false]

/-- Words `0 … k - 1` from `d` into `xs j`. -/
theorem saveSteps_ok {base : Addr} {Z d : Nat} (xs : Nat → XReg) :
    ∀ k (s : State), Scr s base Z → d + 8 * k ≤ Z → (∀ i j, i < j → j < k → xs i ≠ xs j) →
      WP isa (.block ((List.range k).flatMap fun j =>
          [.mov .rax (.mem (sc (d + 8 * j))), .xop (.movq (xs j) .rax)])) s fun t =>
        (∀ j < k, t.xmm (xs j) = (0 : BitVec 64) ++ word s.mem base (d + 8 * j)) ∧
        (∀ x, (∀ j < k, x ≠ xs j) → t.xmm x = s.xmm x) ∧ t.mem = s.mem ∧ KeepRegs [.rax] s t
  | 0, s, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl,
      ⟨fun _ _ => rfl, rfl, rfl⟩⟩
  | k + 1, s, hs, hd, hx => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (saveSteps_ok xs k s hs (by omega) fun i j hi hj => hx i j hi (by omega))
      fun u ⟨x₁, o₁, m₁, k₁⟩ => ?_
    have hu := hs.of_keepRegs k₁ (by decide)
    refine WP.mono (saveStep_ok hu (d := d + 8 * k) (by omega) (xs k)) fun t ⟨x₂, o₂, m₂, k₂⟩ => ?_
    refine ⟨fun j hj => ?_, fun x hx' => ?_, m₂.trans m₁, k₁.trans k₂⟩
    · by_cases he : j = k
      · subst he; rw [x₂, m₁]
      · rw [o₂ _ (hx j k (by omega) (by omega)), x₁ j (by omega)]
    · rw [o₂ x (hx' k (by omega)), o₁ x fun j hj => hx' j (by omega)]

/-- `xs j` into words `0 … k - 1` from `d`. -/
theorem restoreSteps_ok {base : Addr} {Z d : Nat} (xs : Nat → XReg) :
    ∀ k (s : State), Scr s base Z → d + 8 * k ≤ Z →
      WP isa (.block ((List.range k).flatMap fun j =>
          [.movqR .rax (xs j), .store (sc (d + 8 * j)) .rax])) s fun t =>
        (∀ j < k, word t.mem base (d + 8 * j) = qword (s.xmm (xs j)) 0) ∧
        Outside base d (8 * k) s.mem t.mem ∧ t.xmm = s.xmm ∧ KeepRegs [.rax] s t
  | 0, s, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, rfl,
      ⟨fun _ _ => rfl, rfl, rfl⟩⟩
  | k + 1, s, hs, hd => by
    have hnw := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (restoreSteps_ok xs k s hs (by omega)) fun u ⟨e₁, O₁, x₁, k₁⟩ => ?_
    have hu := hs.of_keepRegs k₁ (by decide)
    refine WP.mono (restoreStep_ok hu (d := d + 8 * k) (by omega) (xs k)) fun t ⟨m₂, x₂, k₂⟩ => ?_
    have O₂ : Outside base (d + 8 * k) 8 u.mem t.mem := by rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega)),
      x₂.trans x₁, k₁.trans k₂⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.word (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₂, word_writeW_self, x₁]

/-- Bytes whose word reads the same are the same. -/
theorem byte_of_word {m m' : Mem} {base : Addr} {d : Nat} (h : word m base d = word m' base d) {j : Nat}
    (hj : j < 8) : m (off base d + BitVec.ofNat 64 j) = m' (off base d + BitVec.ofNat 64 j) := by
  have e := congrArg (fun v : BitVec 64 => v.extractLsb' (8 * j) 8) h
  change ((m.read (off base d) 8).setWidth 64).extractLsb' (8 * j) 8 =
    ((m'.read (off base d) 8).setWidth 64).extractLsb' (8 * j) 8 at e
  rw [BitVec.setWidth_eq, BitVec.setWidth_eq, Mem.extractLsb'_read _ _ hj, Mem.extractLsb'_read _ _ hj] at e
  exact e

theorem keepX_ne : ∀ i j, i < j → j < 9 → keepX i ≠ keepX j := by
  intro i j hij hj
  have h : ∀ j < 9, ∀ i < j, keepX i ≠ keepX j := by decide
  exact h j hj i hij

/-- The middle of `mulFnN`: the product, `[o] = [a] [b] R⁻¹ mod n`, with `n`
stored over bytes it restores; it changes `[o]` and the temporary area only,
and no vector register but `xmm6`–`xmm10`. -/
theorem mulN_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    {o a b : Nat} (hbx : s.gpr .rbx = off base a) (hcx : s.gpr .rcx = off base b)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 o)
    (ho : o + 72 ≤ 3520) (ha : a + 72 ≤ 3520) (hb : b + 72 ≤ 3520) (hB : wordsVal s.mem base b 9 < n521) :
    WP isa (.block mulN) s fun s' =>
      KeepRegs (.rbp :: .rsi :: clob 9) s s' ∧
      (∀ x, (ofs base x < o ∨ o + 72 ≤ ofs base x) → (ofs base x < fnTmp ∨ 4096 ≤ ofs base x) →
        s'.mem x = s.mem x) ∧
      (∀ x, (∀ i < 9, x ≠ keepX i) → s'.xmm x = s.xmm x) ∧
      wordsVal s'.mem base o 9 < n521 ∧
      wordsVal s'.mem base o 9 * 2 ^ (64 * 9) % n521 = wordsVal s.mem base a 9 * wordsVal s.mem base b 9 % n521 := by
  have hnw := hs.nowrap
  simp only [mulN, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ptrsN_ok s) fun s₁ ⟨bp₁, si₁, k₁, xs₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  rw [WP.block_append_iff]
  refine WP.mono (saveSteps_ok (d := fnMoN) keepX 9 s₁ hs₁ (by rw [fnMoN_eq]; omega) keepX_ne)
    fun s₁' ⟨x₁', o₁', m₁', k₁'⟩ => ?_
  have hs₁' := hs₁.of_keepRegs k₁' (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep storeN_scal
    (setConst_ok (n := 9) (o := fnMoN) (x := n521) hs₁' (by rw [fnMoN_eq]; omega) n521_lt))
    fun s₂ ⟨⟨v₂, k₂, O₂⟩, x₂, _⟩ => ?_
  have hs₂ := hs₁'.of_keepRegs k₂ (by decide)
  have far : ∀ x, x + 72 ≤ 3520 → wordsVal s₂.mem base x 9 = wordsVal s.mem base x 9 := fun x hx => by
    rw [(show Unch base [(fnMoN, 8 * 9)] s₁'.mem s₂.mem from
      fun y hy => O₂ y (hy _ (List.mem_singleton_self _))).wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; dsimp only; rw [fnMoN_eq]; omega) (by omega), m₁', hm₁]
  have g₂ : ∀ r, r ≠ .rax → s₂.gpr r = s₁.gpr r := fun r hr => by
    rw [k₂.gpr r (by simpa using hr), k₁'.gpr r (by simpa using hr)]
  have hp₂ : PtrsAt [(.rbx, a), (.rbp, b), (.rsi, o)] s₂ := .three
    (by rw [g₂ _ (by decide), k₁.1 _ (by decide), hbx, hs₂.rdi])
    (by rw [g₂ _ (by decide), bp₁, hcx, hs₂.rdi])
    (by rw [g₂ _ (by decide), si₁, hsi, hs.rdi, hs₂.rdi])
  have w₃ := mulF_ok hs₂ (modOkN hZ v₂) rfl (o := o) (a := a) (b := b)
    (by simp only [fnModN]; omega) (by simp only [fnModN]; omega) (by simp only [fnModN]; omega)
    (by simp only [fnModN, fnTmp]; omega) (by simp only [fnModN, fnTmp]; omega)
    (by simp only [fnModN, fnTmp]; omega) (by simp only [fnModN, fnMoN, fnTmp]; omega)
    (by simp only [fnModN]; rw [far b hb]; exact hB)
  rw [← mulF_reloc, ← reloc_unptr] at w₃
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep mulFR_scal (wp_unptr (rs := [.rbx, .rbp, .rsi]) (by simp) _ mulN_keeps hp₂ w₃))
    fun s₃ ⟨⟨k₃, lt₃, e₃⟩, x₃, _⟩ => ?_
  simp only [show fnModN.n = 9 from rfl] at k₃ lt₃ e₃
  have hs₃ : Scr s₃ base Z := ⟨(k₃.gpr _ (by decide)).trans hs₂.rdi, k₃.wr ▸ hs₂.wr, hnw⟩
  refine WP.mono (restoreSteps_ok (d := fnMoN) keepX 9 s₃ hs₃ (by rw [fnMoN_eq]; omega))
    fun s₄ ⟨e₄, O₄, x₄, k₄⟩ => ?_
  have hm₄ : ∀ x, ofs base x < 3952 ∨ 4024 ≤ ofs base x → s₄.mem x = s₃.mem x := fun x hx =>
    O₄ x (by rw [fnMoN_eq]; omega)
  refine ⟨⟨fun r hr => ?_, by rw [k₄.rd, k₃.rd, k₂.rd, k₁'.rd, k₁.2.2.1],
      by rw [k₄.wr, k₃.wr, k₂.wr, k₁'.wr, k₁.2.2.2]⟩,
    fun x hx hx' => ?_, fun x hx => ?_, by rw [O₄.unch.wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; dsimp only; rw [fnMoN_eq]; omega) (by omega)]; exact lt₃, ?_⟩
  · simp only [List.mem_cons, not_or] at hr
    have hra : r ≠ .rax := fun h => hr.2.2 (h ▸ by decide)
    rw [k₄.gpr r (by simpa using hra), k₃.gpr r hr.2.2, g₂ r hra,
      k₁.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.1⟩)]
  · by_cases hin : 3952 ≤ ofs base x ∧ ofs base x < 4024
    · -- A byte of the words restored.
      have hp : ∃ i < 9, ∃ j < 8, x = off base (fnMoN + 8 * i) + BitVec.ofNat 64 j := by
        refine ⟨(ofs base x - 3952) / 8, by omega, (ofs base x - 3952) % 8, Nat.mod_lt _ (by decide), ?_⟩
        rw [off, Offset.add_add, fnMoN_eq, show 3952 + 8 * ((ofs base x - 3952) / 8) + (ofs base x - 3952) % 8 =
          ofs base x by omega, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      obtain ⟨i, hi, j, hj, rfl⟩ := hp
      have hw : word s₄.mem base (fnMoN + 8 * i) = word s.mem base (fnMoN + 8 * i) := by
        rw [e₄ i hi, x₃, x₂, x₁' i hi, qword_lo, hm₁]
      exact byte_of_word hw hj
    · rw [hm₄ x (by omega), k₃.mem x hx (by simp only [fnModN, fnTmp] at hx' ⊢; omega),
        O₂ x (by rw [fnMoN_eq]; omega), m₁', hm₁]
  · rw [x₄, x₃, x₂, o₁' x hx, xs₁]
  · rw [O₄.unch.wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; dsimp only; rw [fnMoN_eq]; omega) (by omega), e₃, far a ha, far b hb]

/-! ## The function -/

/-- `[o] = [a] [b] 2⁻⁵⁷⁶ mod n` for P-521's `n`, the offsets the low halves of
`rsi`, `rdx` and `rcx`: the function changes only `fnClob`, `[o]` and its
temporary area, bytes `fnTmp` to 4095. -/
theorem mulFnN_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    (ho : argOf s .rsi + 72 ≤ 3520) (ha : argOf s .rdx + 72 ≤ 3520) (hb : argOf s .rcx + 72 ≤ 3520)
    (hB : wordsVal s.mem base (argOf s .rcx) 9 < n521) :
    WP isa mulFnN s fun s' =>
      wordsVal s'.mem base (argOf s .rsi) 9 < n521 ∧
      wordsVal s'.mem base (argOf s .rsi) 9 * (2 ^ 64) ^ 9 % n521 =
        wordsVal s.mem base (argOf s .rdx) 9 * wordsVal s.mem base (argOf s .rcx) 9 % n521 ∧
      KeepRegs fnClob s s' ∧
      ∀ x, (ofs base x < argOf s .rsi ∨ argOf s .rsi + 72 ≤ ofs base x) →
        (ofs base x < fnTmp ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x := by
  refine WP.seq (WP.mono (WP.block_append_iff.mp (entry_ok hs)) fun s₀ h₀ => WP.seq (WP.mono h₀
    fun s₁ ⟨hs₁, bx₁, cx₁, _, si₁, x0, x1, x2, x3, x4, x5, k₁, m₁⟩ => ?_))
  generalize hO : argOf s .rsi = o at *
  generalize hA : argOf s .rdx = a at *
  generalize hBb : argOf s .rcx = b at *
  have hQ : (2 : Nat) ^ (64 * 9) = (2 ^ 64) ^ 9 := Nat.pow_mul 2 64 9
  refine WP.seq (WP.mono (mulN_ok hs₁ hZ bx₁ cx₁ si₁ ho ha hb (by rw [m₁]; exact hB))
    fun s₂ ⟨k₂, O₂, xm₂, lt₂, e₂⟩ => ?_)
  have xk : ∀ x, x ∈ [XReg.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5] → s₂.xmm x = s₁.xmm x := fun x hx =>
    xm₂ x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
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
