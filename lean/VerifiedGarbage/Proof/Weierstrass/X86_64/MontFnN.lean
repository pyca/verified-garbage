import VerifiedGarbage.Proof.Weierstrass.X86_64.Reloc
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnX
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Mont.X86_64.MulF
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Mont.Words128

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

/-- A 16-byte load into `r`. -/
theorem loadPiece_ok {s : State} {base : Addr} {Z a : Nat} (hs : Scr s base Z) (ha : a + 16 ≤ Z) (r : XReg) :
    WP isa (.block [.movdquLoad r (sc a)]) s fun t =>
      t.xmm r = s.mem.readW (off base a) 128 ∧ (∀ x, x ≠ r → t.xmm x = s.xmm x) ∧ t.mem = s.mem ∧
        t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hr : InRegions (s.rd ++ s.wr) (off base a) 16 :=
    ⟨_, List.mem_append_right _ hs.wr, hs.contains ha (by decide)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, ea_sc' hs, hr, ite_true,
    Option.map_some, RegUpd.xmm_setXmm_self, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun x hx => RegUpd.xmm_setXmm_of_ne _ _ hx, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

/-- A 16-byte store of `r`. -/
theorem storePiece_ok {s : State} {base : Addr} {Z o : Nat} (hs : Scr s base Z) (ho : o + 16 ≤ Z) (r : XReg) :
    WP isa (.block [.movdquStore (sc o) r]) s fun t =>
      t.mem.readW (off base o) 128 = s.xmm r ∧ Outside base o 16 s.mem t.mem ∧ t.xmm = s.xmm ∧
        t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hw : InRegions s.wr (off base o) 16 := ⟨_, hs.wr, hs.contains ho (by decide)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store128, ea_sc' hs, hw, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨Mem.readW_writeW_self (n := 16) _ _ _ (by decide),
    writeW128_out s.mem base (s.xmm r) (by have := hs.nowrap; omega), ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

/-- Pieces `0 … k - 1` of 16 bytes from `d` into `xs i`. -/
theorem loadPieces_ok {base : Addr} {Z d : Nat} (xs : Nat → XReg) :
    ∀ k (s : State), Scr s base Z → d + 16 * k ≤ Z → (∀ i j, i < j → j < k → xs i ≠ xs j) →
      WP isa (.block ((List.range k).map fun i => .movdquLoad (xs i) (sc (d + 16 * i)))) s fun t =>
        (∀ i < k, t.xmm (xs i) = s.mem.readW (off base (d + 16 * i)) 128) ∧
        (∀ x, (∀ i < k, x ≠ xs i) → t.xmm x = s.xmm x) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧
        t.rd = s.rd ∧ t.wr = s.wr
  | 0, s, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | k + 1, s, hs, hd, hx => by
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (loadPieces_ok xs k s hs (by omega) fun i j hi hj => hx i j hi (by omega))
      fun u ⟨x₁, o₁, m₁, g₁, r₁, w₁⟩ => ?_
    have hu : Scr u base Z := ⟨by rw [g₁]; exact hs.rdi, w₁ ▸ hs.wr, hs.nowrap⟩
    refine WP.mono (loadPiece_ok hu (a := d + 16 * k) (by omega) (xs k)) fun t ⟨x₂, o₂, m₂, g₂, r₂, w₂⟩ => ?_
    refine ⟨fun i hi => ?_, fun x hx' => ?_, m₂.trans m₁, g₂.trans g₁, r₂.trans r₁, w₂.trans w₁⟩
    · by_cases he : i = k
      · subst he; rw [x₂, m₁]
      · rw [o₂ _ (hx i k (by omega) (by omega)), x₁ i (by omega)]
    · rw [o₂ x (hx' k (by omega)), o₁ x fun i hi => hx' i (by omega)]

/-- `xs i` into pieces `0 … k - 1` of 16 bytes from `d`. -/
theorem storePieces_ok {base : Addr} {Z d : Nat} (xs : Nat → XReg) :
    ∀ k (s : State), Scr s base Z → d + 16 * k ≤ Z →
      WP isa (.block ((List.range k).map fun i => .movdquStore (sc (d + 16 * i)) (xs i))) s fun t =>
        (∀ i < k, t.mem.readW (off base (d + 16 * i)) 128 = s.xmm (xs i)) ∧
        Outside base d (16 * k) s.mem t.mem ∧ t.xmm = s.xmm ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr
  | 0, s, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, rfl, rfl, rfl, rfl⟩
  | k + 1, s, hs, hd => by
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (storePieces_ok xs k s hs (by omega)) fun u ⟨e₁, O₁, x₁, g₁, r₁, w₁⟩ => ?_
    have hu : Scr u base Z := ⟨by rw [g₁]; exact hs.rdi, w₁ ▸ hs.wr, hs.nowrap⟩
    refine WP.mono (storePiece_ok hu (o := d + 16 * k) (by omega) (xs k)) fun t ⟨e₂, O₂, x₂, g₂, r₂, w₂⟩ => ?_
    have hnw := hs.nowrap
    refine ⟨fun i hi => ?_, fun x hx => ?_, x₂.trans x₁, g₂.trans g₁, r₂.trans r₁, w₂.trans w₁⟩
    · by_cases he : i = k
      · subst he; rw [e₂, x₁]
      · rw [Mem.readW_congr fun j hj => O₂ _ (by rw [ofs_off base (by omega)]; omega), e₁ i (by omega)]
    · rw [O₂ x (by omega), O₁ x (by omega)]

/-- Bytes whose 16-byte piece reads the same are the same. -/
theorem byte_of_readW128 {m m' : Mem} {a : Addr} (h : m.readW a 128 = m'.readW a 128) {j : Nat} (hj : j < 16) :
    m (a + BitVec.ofNat 64 j) = m' (a + BitVec.ofNat 64 j) := by
  have e := congrArg (fun v : BitVec 128 => v.extractLsb' (8 * j) 8) h
  change ((m.read a 16).setWidth 128).extractLsb' (8 * j) 8 = ((m'.read a 16).setWidth 128).extractLsb' (8 * j) 8 at e
  rw [BitVec.setWidth_eq, BitVec.setWidth_eq, Mem.extractLsb'_read _ _ hj, Mem.extractLsb'_read _ _ hj] at e
  exact e

theorem keepX_ne : ∀ i j, i < j → j < 5 → keepX i ≠ keepX j := by
  intro i j hij hj
  have h : ∀ j < 5, ∀ i < j, keepX i ≠ keepX j := by decide
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
      (∀ x, (∀ i < 5, x ≠ keepX i) → s'.xmm x = s.xmm x) ∧
      wordsVal s'.mem base o 9 < n521 ∧
      wordsVal s'.mem base o 9 * 2 ^ (64 * 9) % n521 = wordsVal s.mem base a 9 * wordsVal s.mem base b 9 % n521 := by
  have hnw := hs.nowrap
  have hD : fnMoN - 8 = 3944 := rfl
  simp only [mulN, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ptrsN_ok s) fun s₁ ⟨bp₁, si₁, k₁, xs₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  rw [WP.block_append_iff]
  refine WP.mono (loadPieces_ok (d := fnMoN - 8) keepX 5 s₁ hs₁ (by rw [hD]; omega) keepX_ne)
    fun s₁' ⟨x₁', o₁', m₁', g₁', r₁', w₁'⟩ => ?_
  have hs₁' : Scr s₁' base Z := ⟨by rw [g₁']; exact hs₁.rdi, w₁' ▸ hs₁.wr, hnw⟩
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep storeN_scal
    (setConst_ok (n := 9) (o := fnMoN) (x := n521) hs₁' (by rw [fnMoN_eq]; omega) n521_lt))
    fun s₂ ⟨⟨v₂, k₂, O₂⟩, x₂, _⟩ => ?_
  have hs₂ := hs₁'.of_keepRegs k₂ (by decide)
  have far : ∀ x, x + 72 ≤ 3520 → wordsVal s₂.mem base x 9 = wordsVal s.mem base x 9 := fun x hx => by
    rw [(show Unch base [(fnMoN, 8 * 9)] s₁'.mem s₂.mem from
      fun y hy => O₂ y (hy _ (List.mem_singleton_self _))).wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; dsimp only; rw [fnMoN_eq]; omega) (by omega), m₁', hm₁]
  have hp₂ : PtrsAt [(.rbx, a), (.rbp, b), (.rsi, o)] s₂ := .three
    (by rw [k₂.gpr _ (by decide), g₁', k₁.1 _ (by decide), hbx, hs₂.rdi])
    (by rw [k₂.gpr _ (by decide), g₁', bp₁, hcx, hs₂.rdi])
    (by rw [k₂.gpr _ (by decide), g₁', si₁, hsi, hs.rdi, hs₂.rdi])
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
  refine WP.mono (storePieces_ok (d := fnMoN - 8) keepX 5 s₃ hs₃ (by rw [hD]; omega))
    fun s₄ ⟨e₄, O₄, x₄, g₄, r₄, w₄⟩ => ?_
  have hm₄ : ∀ x, ofs base x < 3944 ∨ 4024 ≤ ofs base x → s₄.mem x = s₃.mem x := fun x hx =>
    O₄ x (by rw [hD]; omega)
  refine ⟨⟨fun r hr => ?_, by rw [r₄, k₃.rd, k₂.rd, r₁', k₁.2.2.1], by rw [w₄, k₃.wr, k₂.wr, w₁', k₁.2.2.2]⟩,
    fun x hx hx' => ?_, fun x hx => ?_, by rw [O₄.unch.wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; dsimp only; rw [hD]; omega) (by omega)]; exact lt₃, ?_⟩
  · simp only [List.mem_cons, not_or] at hr
    rw [g₄, k₃.gpr r hr.2.2, k₂.gpr r (by
      intro h; simp only [List.mem_singleton] at h; subst h; exact hr.2.2 (by decide)), g₁',
      k₁.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.1⟩)]
  · by_cases hin : 3944 ≤ ofs base x ∧ ofs base x < 4024
    · -- A byte of the pieces restored.
      have hp : ∃ i < 5, ∃ j < 16, x = off base (fnMoN - 8 + 16 * i) + BitVec.ofNat 64 j := by
        refine ⟨(ofs base x - 3944) / 16, by omega, (ofs base x - 3944) % 16, Nat.mod_lt _ (by decide), ?_⟩
        rw [off, Offset.add_add, hD, show 3944 + 16 * ((ofs base x - 3944) / 16) + (ofs base x - 3944) % 16 =
          ofs base x by omega, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      obtain ⟨i, hi, j, hj, rfl⟩ := hp
      have hpiece : s₄.mem.readW (off base (fnMoN - 8 + 16 * i)) 128 =
          s.mem.readW (off base (fnMoN - 8 + 16 * i)) 128 := by
        rw [e₄ i hi, x₃, x₂, x₁' i hi, hm₁]
      exact byte_of_readW128 hpiece hj
    · rw [hm₄ x (by omega), k₃.mem x hx (by simp only [fnModN, fnTmp] at hx' ⊢; omega),
        O₂ x (by rw [fnMoN_eq]; omega), m₁', hm₁]
  · rw [x₄, x₃, x₂, o₁' x hx, xs₁]
  · rw [O₄.unch.wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; dsimp only; rw [hD]; omega) (by omega), e₃, far a ha, far b hb]

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
