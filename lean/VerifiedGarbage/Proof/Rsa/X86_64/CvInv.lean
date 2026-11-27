module

-- separate module: the inverse's proofs import algebra, and `CvCheck` is imported by many modules
public import VerifiedGarbage.Proof.Rsa.X86_64.CvCheck
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
public import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
public import VerifiedGarbage.Proof.Rsa.X86_64.WordGuard
public import VerifiedGarbage.Proof.Rsa.X86_64.WordFast
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Rsa.X86_64.ShlCl
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Loop
import Mathlib.Tactic.Positivity

/-! ### `Rsa.X86_64.CvTail`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_crt_values` on x86-64: `qInv`'s scaling on the guarded path

On the path the public guard of `wordChoice` takes, the inverse leaves out its
`K = 15 n + 10` modular doublings (`inverseNS`), and `qTail` multiplies `[x₂]`
by `2^K` modulo `p` instead: for `K = 64 Q + T` (`T < 64`), its low `n + 1`
words shifted left by `T` bits straight into word `Q` of `WordDivide`'s
dividend `[d]` (`qShift_ok`), whose remainder modulo `p`, from the dividend's
top digit (`startT_ok`, `Q + 2` digits), is `[x₂] 2^K mod p` (`cvQTail_ok`);
`d` is kept in `[aSv]` meanwhile.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The words `[x₂] 2^T` is placed up, `Q = ⌊K / 64⌋` for `K = 15 (w / 2) + 10`. -/
def tailQ (W : Nat) : Nat := (15 * (W / 2) + 10) / 64

/-- The bits `[x₂]` is shifted by, `T = K mod 64`. -/
def tailT (W : Nat) : Nat := (15 * (W / 2) + 10) % 64

theorem tail_split (W : Nat) : 15 * (W / 2) + 10 = 64 * tailQ W + tailT W := by
  unfold tailQ tailT; omega_using []

theorem se10 : BitVec.signExtend 64 (10 : BitVec 32) = BitVec.ofNat 64 10 := by decide

theorem se2 : BitVec.signExtend 64 (2 : BitVec 32) = BitVec.ofNat 64 2 := by decide

theorem shr1W {W : Nat} (hW : W < 2 ^ 24) : BitVec.ofNat 64 W >>> 1 = BitVec.ofNat 64 (W / 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_using [hW]

/-- `K = 15 n + 10` into `rax`, for `n` in `r12` (`n < 2^24`). -/
theorem k15_eq (n : Nat) :
    (BitVec.ofNat 64 n <<< 4 - BitVec.ofNat 64 n + BitVec.ofNat 64 10 : BitVec 64) =
      BitVec.ofNat 64 (15 * n + 10) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_using []

/-- `startT`: the first digit's index `Q + 2`, from `w` in `r12`. -/
theorem startT_ok {W : Nat} (hW : 6 ≤ W) (hW' : W < 2 ^ 24) :
    WordDivide.StartOk WordDivide.startT W (tailQ W + 2) where
  pos := by omega_using []
  fit := by unfold tailQ; omega_using [hW]
  lt := by unfold tailQ; omega_using [hW']
  run := fun {s} h12 => by
    refine WP.mono (WP.keep [.rax, .r12] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (tailQ W + 2) ∧
      t.gpr .r12 = BitVec.ofNat 64 (W / 2) ∧ t.mem = s.mem) ?_ rfl) fun t ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, c, k⟩
    xrun [WordDivide.startT, h12, shr1W hW', se10, se2, k15_eq (W / 2)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      show (2 : BitVec 64).toNat = 2 from rfl, Nat.reducePow]
    unfold tailQ; simp (disch := omega_using [hW']) only [Nat.mod_eq_of_lt]

/-- `shSetup`'s arithmetic: `rax := 8 Q`, `rcx := T` and `r12 := n + 1`, from `w` in `r12`. -/
theorem shArith_ok {s : State} {W : Nat} (hW' : W < 2 ^ 24) (h12 : s.gpr .r12 = BitVec.ofNat 64 W) :
    WP isa (.block [.shift .shr .r12 1, .mov .rax (.reg .r12), .shift .shl .rax 4, .alu .sub .rax (.reg .r12),
      .alu .add .rax (.imm 10), .mov .rcx (.reg .rax), .alu .and .rcx (.imm 63), .shift .shr .rax 6,
      .shift .shl .rax 3, .alu .add .r12 (.imm 1)]) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (8 * tailQ W) ∧ t.gpr .rcx = BitVec.ofNat 64 (tailT W) ∧
        t.gpr .r12 = BitVec.ofNat 64 (W / 2 + 1) ∧ t.mem = s.mem ∧ Keep [.rax, .rcx, .r12] s t := by
  refine WP.mono (WP.keep [.rax, .rcx, .r12] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (8 * tailQ W) ∧
    t.gpr .rcx = BitVec.ofNat 64 (tailT W) ∧ t.gpr .r12 = BitVec.ofNat 64 (W / 2 + 1) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, c, d, k⟩
  obtain e63 : ∀ x : Nat, x &&& 63 = x % 64 := fun x => Nat.and_two_pow_sub_one_eq_mod x 6
  xrun [h12, shr1W hW', se10, k15_eq (W / 2)]
  refine ⟨?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq
  · simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow, Nat.reducePow]
    unfold tailQ; simp (disch := omega_using [hW']) only [Nat.mod_eq_of_lt]; omega_using []
  · simp only [BitVec.toNat_and, BitVec.toNat_ofNat, show (BitVec.signExtend 64 (63 : BitVec 32)).toNat = 63 from rfl,
      e63, Nat.reducePow]
    unfold tailT; simp (disch := omega) only [Nat.mod_eq_of_lt]
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl, Nat.reducePow]
    simp (disch := omega_using [hW']) only [Nat.mod_eq_of_lt]

/-- `shSetup` and its loop: `[x₂]`'s low `n + 1` words times `2^T`, at word `Q` of `[d]`. -/
theorem qShift_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) :
    WP isa (.seq (.block shSetup) (wordLoop 1 shlClBody)) s fun t => CvS I m₀ t ∧
      wv t.mem I.B (slot (wk I.k) aD + 8 * tailQ (wk I.k)) (wk I.k / 2 + 1) =
        wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k / 2 + 1) * 2 ^ tailT (wk I.k) % 2 ^ (64 * (wk I.k / 2 + 1)) ∧
      Outside I.B (slot (wk I.k) aD + 8 * tailQ (wk I.k)) (8 * (wk I.k / 2 + 1)) s.mem t.mem := by
  have hn := h.ws.scr.nowrap
  have hw := h.ws.w2
  have hw1 := h.ws.w1
  obtain sD := h.ws.sl (j := aD) (by decide)
  obtain sX := h.ws.sl (j := aX₂) (by decide)
  obtain hq : tailQ (wk I.k) + (wk I.k / 2 + 1) ≤ wk I.k := by unfold tailQ; omega_using [hw1]
  obtain hT : tailT (wk I.k) < 64 := by unfold tailT; omega_using []
  obtain far : slot (wk I.k) aD + 8 * (wk I.k + 2) ≤ slot (wk I.k) aX₂ := by
    simp only [slot, VG.Impl.Rsa.X86_64.Keys.CrtValues.aD, aX₂]; omega_arith
  unfold shSetup
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_))
  refine WP.block_append_iff.mpr (WP.mono (shArith_ok hw h12) fun s₂ ⟨ax, cx, r12, m₂, k₂⟩ => ?_)
  rw [← List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono (base2_ok aX₂ aD (r₁ := .r8) (r₂ := .rsi) (by decide) (by decide)
    (by decide) (((k₁.trans k₂).gpr (by decide)).trans h.ws.rdi) ((k₂.gpr (by decide)).trans h9) (by decide))
    fun s₃ ⟨h8, hsi, m₃, k₃⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.rsi] (Q := fun t =>
    t.gpr .rsi = off I.B (slot (wk I.k) aD + 8 * tailQ (wk I.k)) ∧ t.mem = s₃.mem) (by
      xrun [hsi, (k₃.gpr (by decide)).trans ax]
      rw [← off_off]) rfl) fun s₄ ⟨⟨hsi₄, m₄⟩, k₄⟩ => ?_)
  obtain k14 := ((k₁.trans k₂).trans k₃).trans k₄
  obtain hs₄ := h.ws.scr.congr k14.2.2
  obtain mm : s₄.mem = s.mem := by rw [m₄, m₃, m₂, m₁]
  obtain h8₄ : s₄.gpr .r8 = off I.B (slot (wk I.k) aX₂) := (k₄.gpr (by decide)).trans h8
  obtain cx₄ : s₄.gpr .rcx = BitVec.ofNat 64 (tailT (wk I.k)) := ((k₃.trans k₄).gpr (by decide)).trans cx
  obtain r12₄ : s₄.gpr .r12 = BitVec.ofNat 64 (wk I.k / 2 + 1) := ((k₃.trans k₄).gpr (by decide)).trans r12
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = s₄.mem.writeW
      (off I.B (slot (wk I.k) aD + 8 * tailQ (wk I.k))) (word s.mem I.B (slot (wk I.k) aX₂) <<< tailT (wk I.k))) (by
    xrun [State.ea, at0, h8₄, hsi₄, cx₄, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₄.ld (d := slot (wk I.k) aX₂) (by omega_arith), hs₄.st (d := slot (wk I.k) aD + 8 * tailQ (wk I.k)) (by omega_arith),
      mm, execShiftCl, VarShiftOp.eval, cl_eq hT]) rfl)
    fun s₅ ⟨m₅, k₅⟩ => (show WP isa (wordLoop 1 shlClBody) s₅ _ from ?_)
  obtain hs₅ := hs₄.congr k₅.2.2
  refine WP.mono (shlCl_ok hT hs₅ ((k₅.gpr (by decide)).trans hsi₄) ((k₅.gpr (by decide)).trans h8₄)
    ((k₅.gpr (by decide)).trans r12₄) ((k₅.gpr (by decide)).trans cx₄) (by omega_using [hw1]) (by omega_arith)
    (by omega_arith) (by omega_arith) (.inl (by omega_arith)) (by
      rw [m₅, word_writeW_self, (writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith), mm,
        BitVec.toNat_shiftLeft, Nat.shiftLeft_eq])) fun u ⟨v, _, o, k₆⟩ => ?_
  obtain Jv : wv s₅.mem I.B (slot (wk I.k) aX₂) (wk I.k / 2 + 1) =
      wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k / 2 + 1) := by
    rw [m₅, (writeW_outside _ _ _ (by omega_arith)).wv (by omega_arith) (by omega_arith), mm]
  obtain ou : Outside I.B (slot (wk I.k) aD + 8 * tailQ (wk I.k)) (8 * (wk I.k / 2 + 1)) s.mem u.mem := by
    intro x hx
    rw [o x (by omega_arith), m₅, writeW_outside _ _ _ (by omega_arith) x (by omega_arith), mm]
  refine ⟨h.step (Frm.of_outside ou (List.mem_singleton_self _)) (fun r hr => ?_) (fun r hr => ?_)
    ((k14.trans k₅).trans k₆) (by decide), by rw [v, Jv], ou⟩
  · rw [List.mem_singleton.mp hr]; exact Or.inl (by have := slot_lin (wk I.k) aD; dsimp only; omega_arith)
  · rw [List.mem_singleton.mp hr]; dsimp only; omega_arith

/-- `qTail`: on a `p` of `n = w / 2` words with its top bit set, `[x₂] := [x₂] 2^K mod p`
for `[x₂] < p`; it keeps `p`, `q`, `d` and the mask. -/
theorem cvQTail_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) :
    WP isa (seqs qTail) s fun t => CvS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (∀ j, j = aP ∨ j = aQ ∨ j = aD →
        wv t.mem I.B (slot (wk I.k) j) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k)) ∧
      (2 ^ (64 * (wk I.k / 2) - 1) ≤ wv s.mem I.B (slot (wk I.k) aP) (wk I.k) →
        wv s.mem I.B (slot (wk I.k) aP) (wk I.k) < 2 ^ (64 * (wk I.k / 2)) →
        wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k) < wv s.mem I.B (slot (wk I.k) aP) (wk I.k) →
        wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) =
          wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k) * 2 ^ (15 * (wk I.k / 2) + 10) %
            wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have hw := h.ws.w2
  have hk1 := L.k1
  obtain hW6 : 6 ≤ wk I.k := by unfold wk; omega_using [hk1]
  obtain hZ17 : slot (wk I.k) 17 ≤ I.Z := by
    have hz := L.z
    simp only [slot, Impl.Bignum.hdrBytes, wk]
    omega_using [hk1, hz]
  obtain hq : tailQ (wk I.k) + (wk I.k / 2 + 1) ≤ wk I.k := by unfold tailQ; omega_using [hW6]
  obtain hT : tailT (wk I.k) < 64 := by unfold tailT; omega_using []
  obtain ot : ∀ {m m' : Mem} {j i Ln : Nat}, Outside I.B (slot (wk I.k) j) Ln m m' → Ln ≤ 8 * (wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (slot (wk I.k) i) (wk I.k) = wv m I.B (slot (wk I.k) i) (wk I.k) :=
    fun o hL hij hi => outside_arr o hL hij (by omega_arith) hi hZ hn
  obtain hmw : ∀ {m m' : Mem} {j L' : Nat}, Outside I.B (slot (wk I.k) j) L' m m' →
      mword m' I.B = mword m I.B := fun {_ _ j _} o =>
    o.word (Or.inl (by have := hdr_lt_slot (wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith))
      (by change 8 * 22 + 8 ≤ 2 ^ 64; decide)
  simp only [qTail, seqs]
  -- `[aSv] := d`.
  refine WP.seq (WP.mono (zeroA_ok h.ws (j := aSv) (by decide)) fun s₁ ⟨_, o₁, k₁⟩ => ?_)
  obtain h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₁.ws (o := aSv) (a := aD) (by decide) (by decide) (by decide))
    fun s₂ ⟨c₂, o₂, k₂⟩ => ?_)
  obtain h₂ := h₁.arr (by decide) (by omega_arith) o₂ k₂ (by decide)
  rw [ot o₁ (Nat.le_refl _) (by decide) (by decide)] at c₂
  obtain u₂ : ∀ i, i < 16 → i ≠ aSv → wv s₂.mem I.B (slot (wk I.k) i) (wk I.k) = wv s.mem I.B (slot (wk I.k) i) (wk I.k) :=
    fun i hi hne => by rw [ot o₂ (by omega_arith) hne hi, ot o₁ (Nat.le_refl _) hne hi]
  -- `[d] := [x₂] 2^T` at word `Q`.
  refine WP.seq (WP.mono (zeroA_ok h₂.ws (j := aD) (by decide)) fun s₅ ⟨z₅, o₅, k₅⟩ => ?_)
  obtain h₅ := h₂.arr (by decide) (Nat.le_refl _) o₅ k₅ (by decide)
  refine WP.seq (WP.mono (qShift_ok h₅) fun s₆ ⟨h₆, c₆, o₆⟩ => ?_)
  -- `[c] := p`.
  refine WP.seq (WP.mono (zeroA_ok h₆.ws (j := aC) (by decide)) fun s₇ ⟨_, o₇, k₇⟩ => ?_)
  obtain h₇ := h₆.arr (by decide) (Nat.le_refl _) o₇ k₇ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₇.ws (o := aC) (a := aP) (by decide) (by decide) (by decide))
    fun s₈ ⟨c₈, o₈, k₈⟩ => ?_)
  obtain h₈ := h₇.arr (by decide) (by omega_arith) o₈ k₈ (by decide)
  -- The reduction.
  refine WP.seq (WP.mono (WordDivide.fastAtWith_ok h₈.ws hZ17 hW6 (startT_ok hW6 hw)) fun s₉ ⟨v₉, f₉, k₉⟩ => ?_)
  obtain bound : ∀ r ∈ WordDivide.normRanges (wk I.k), r.1 + r.2 ≤ I.Z := by
    intro r hr
    simp only [WordDivide.normRanges, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact h.ws.sl (by decide)
    · exact WordDivide.all_bound h.ws hZ17 hr
  obtain h₉ := h₈.step f₉ (by
    intro r hr
    simp only [WordDivide.normRanges, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact Mut.ofSlot _ _ _
    · exact WordDivide.all_mut hr) bound k₉ (by decide)
  obtain f9 : ∀ i, i = aP ∨ i = aQ ∨ i = aD ∨ i = aX₂ ∨ i = aSv →
      wv s₉.mem I.B (slot (wk I.k) i) (wk I.k) = wv s₈.mem I.B (slot (wk I.k) i) (wk I.k) := fun i hi => by
    apply f₉.wv_eq _ (by have := h.ws.sl (j := i) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide); omega_arith)
    intro r hr
    simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [VG.Impl.Rsa.X86_64.WordDivide.aM, VG.Impl.Rsa.X86_64.WordDivide.aR, VG.Impl.Rsa.X86_64.WordDivide.aT,
        VG.Impl.Rsa.X86_64.WordDivide.aV, VG.Impl.Rsa.X86_64.Keys.CrtValues.aP,
        VG.Impl.Rsa.X86_64.Keys.CrtValues.aQ, VG.Impl.Rsa.X86_64.Keys.CrtValues.aD, aX₂, aSv, slot] <;> omega_arith
  obtain mw9 : mword s₉.mem I.B = mword s₈.mem I.B := f₉.word_eq (by
    intro r hr
    simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [VG.Impl.Rsa.X86_64.WordDivide.aM, VG.Impl.Rsa.X86_64.WordDivide.aR,
        VG.Impl.Rsa.X86_64.WordDivide.aT, VG.Impl.Rsa.X86_64.WordDivide.aV, slot, Public.sMask, sFn,
        Impl.Bignum.hdrBytes] <;> omega_arith) (by change 8 * 22 + 8 ≤ 2 ^ 64; decide)
  -- `[x₂] :=` the remainder, `[d] := [aSv]`.
  refine WP.seq (WP.mono (zeroA_ok h₉.ws (j := aX₂) (by decide)) fun s₁₀ ⟨_, o₁₀, k₁₀⟩ => ?_)
  obtain h₁₀ := h₉.arr (by decide) (Nat.le_refl _) o₁₀ k₁₀ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₁₀.ws (o := aX₂) (a := aV) (by decide) (by decide) (by decide))
    fun s₁₁ ⟨c₁₁, o₁₁, k₁₁⟩ => ?_)
  obtain h₁₁ := h₁₀.arr (by decide) (by omega_arith) o₁₁ k₁₁ (by decide)
  refine WP.mono (copyA_ok h₁₁.ws (o := aD) (a := aSv) (by decide) (by decide) (by decide))
    fun t ⟨ct, ot', kt⟩ => ?_
  obtain ht := h₁₁.arr (by decide) (by omega_arith) ot' kt (by decide)
  -- What each piece leaves.
  obtain o6 : ∀ i, i < 16 → i ≠ aD → wv s₆.mem I.B (slot (wk I.k) i) (wk I.k) = wv s₅.mem I.B (slot (wk I.k) i) (wk I.k) :=
    fun i hi hne => o₆.wv (by have := slot_far (w := wk I.k) hne; omega_arith)
      (by have := h.ws.sl hi; omega_arith)
  obtain pre : ∀ i, i < 16 → i ≠ aSv → i ≠ aX₂ → i ≠ aD → i ≠ aC → i ≠ aV → i ≠ 8 →
      wv t.mem I.B (slot (wk I.k) i) (wk I.k) = wv s.mem I.B (slot (wk I.k) i) (wk I.k) := fun i hi h1 h2 h3 h4 h5 h6 => by
    obtain e9 : wv s₉.mem I.B (slot (wk I.k) i) (wk I.k) = wv s₈.mem I.B (slot (wk I.k) i) (wk I.k) := by
      apply f₉.wv_eq _ (by have := h.ws.sl hi; omega_arith)
      intro r hr
      simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      obtain a1 := slot_far (w := wk I.k) (show i ≠ 9 from h4)
      obtain a2 := slot_far (w := wk I.k) (show i ≠ 3 from h5)
      obtain a3 := slot_far (w := wk I.k) h6
      rcases hr with rfl | rfl | rfl | rfl <;>
        simp only [VG.Impl.Rsa.X86_64.WordDivide.aM, VG.Impl.Rsa.X86_64.WordDivide.aR,
          VG.Impl.Rsa.X86_64.WordDivide.aT, VG.Impl.Rsa.X86_64.WordDivide.aV] at a1 a2 a3 ⊢
      · omega_arith
      · omega_arith
      · omega_arith
      · have := slot_lt (w := wk I.k) hi; have := slot_lin (wk I.k) 16; omega_arith
    rw [ot ot' (by omega_arith) h3 hi, ot o₁₁ (by omega_arith) h2 hi, ot o₁₀ (Nat.le_refl _) h2 hi, e9,
      ot o₈ (by omega_arith) h4 hi, ot o₇ (Nat.le_refl _) h4 hi, o6 i hi h3, ot o₅ (Nat.le_refl _) h3 hi,
      u₂ i hi h1]
  obtain aSvT : wv s₁₁.mem I.B (slot (wk I.k) aSv) (wk I.k) = wv s.mem I.B (slot (wk I.k) aD) (wk I.k) := by
    rw [ot o₁₁ (by omega_arith) (by decide) (by decide), ot o₁₀ (Nat.le_refl _) (by decide) (by decide),
      f9 aSv (by simp), ot o₈ (by omega_arith) (by decide) (by decide), ot o₇ (Nat.le_refl _) (by decide) (by decide),
      o6 aSv (by decide) (by decide), ot o₅ (Nat.le_refl _) (by decide) (by decide), c₂]
  obtain sD := h.ws.sl (j := aD) (by decide)
  obtain sX := h.ws.sl (j := aX₂) (by decide)
  refine ⟨ht, ?_, ?_, ?_⟩
  · have mw6 : mword s₆.mem I.B = mword s₅.mem I.B :=
      o₆.word (Or.inl (by have := hdr_lt_slot (wk I.k) aD (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith))
        (by change 8 * 22 + 8 ≤ 2 ^ 64; decide)
    rw [hmw ot', hmw o₁₁, hmw o₁₀, mw9, hmw o₈, hmw o₇, mw6, hmw o₅, hmw o₂, hmw o₁]
  · intro j hj
    rcases hj with rfl | rfl | rfl
    · exact pre aP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact pre aQ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [ct, aSvT]
  · intro hPt hPlt hx
    obtain hn1 : 1 ≤ wk I.k / 2 := by omega_using [hW6]
    generalize hP : wv s.mem I.B (slot (wk I.k) aP) (wk I.k) = P at hPt hPlt hx
    generalize hX : wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k) = x at hx
    obtain hP1 : 2 ^ (64 * (wk I.k / 2)) * 2 ^ 64 = 2 ^ (64 * (wk I.k / 2 + 1)) := by
      rw [← pow_add]; congr 1
    obtain hxT : x * 2 ^ tailT (wk I.k) < 2 ^ (64 * (wk I.k / 2 + 1)) := by
      rw [← hP1]
      exact Nat.mul_lt_mul_of_lt_of_le (by omega_using [hPlt, hx]) (Nat.pow_le_pow_right (by decide) hT.le) (by positivity)
    obtain hxn : x < 2 ^ (64 * (wk I.k / 2 + 1)) := by
      have : 2 ^ (64 * (wk I.k / 2)) ≤ 2 ^ (64 * (wk I.k / 2 + 1)) := Nat.pow_le_pow_right (by decide) (by omega_using [])
      omega_using [hPlt, hx, hP1]
    obtain x5 : wv s₅.mem I.B (slot (wk I.k) aX₂) (wk I.k) = x := by
      rw [ot o₅ (Nat.le_refl _) (by decide) (by decide), u₂ aX₂ (by decide) (by decide), hX]
    obtain xl5 : wv s₅.mem I.B (slot (wk I.k) aX₂) (wk I.k / 2 + 1) = x :=
      (wv_low_of_lt (by omega_using [hW6]) (by rw [x5]; exact hxn)).trans x5
    rw [xl5, Nat.mod_eq_of_lt hxT] at c₆
    obtain zD : ∀ i, i < wk I.k + 2 → word s₅.mem I.B (slot (wk I.k) aD + 8 * i) = 0 :=
      (wv_eq_zero_iff _ _ _ _).mp z₅
    obtain dlow : wv s₆.mem I.B (slot (wk I.k) aD) (tailQ (wk I.k)) = 0 := by
      rw [o₆.wv (Or.inl (by omega_using [])) (by omega_arith)]
      exact wv_zero fun i hi => zD i (by omega_using [hq, hi])
    obtain dhigh : wv s₆.mem I.B (slot (wk I.k) aD + 8 * tailQ (wk I.k) + 8 * (wk I.k / 2 + 1))
        (wk I.k - tailQ (wk I.k) - (wk I.k / 2 + 1)) = 0 := by
      rw [o₆.wv (Or.inr (by omega_using [])) (by omega_arith)]
      exact wv_zero fun i hi => by
        rw [show slot (wk I.k) aD + 8 * tailQ (wk I.k) + 8 * (wk I.k / 2 + 1) + 8 * i =
          slot (wk I.k) aD + 8 * (tailQ (wk I.k) + (wk I.k / 2 + 1) + i) by omega_using []]
        exact zD _ (by omega_using [hi])
    obtain d6 : wv s₆.mem I.B (slot (wk I.k) aD) (wk I.k) = 2 ^ (64 * tailQ (wk I.k)) * (x * 2 ^ tailT (wk I.k)) := by
      obtain e := wv_add s₆.mem I.B (slot (wk I.k) aD) (tailQ (wk I.k)) (wk I.k - tailQ (wk I.k))
      obtain e' := wv_add s₆.mem I.B (slot (wk I.k) aD + 8 * tailQ (wk I.k)) (wk I.k / 2 + 1)
        (wk I.k - tailQ (wk I.k) - (wk I.k / 2 + 1))
      rw [show tailQ (wk I.k) + (wk I.k - tailQ (wk I.k)) = wk I.k by omega_using [hq]] at e
      rw [show wk I.k / 2 + 1 + (wk I.k - tailQ (wk I.k) - (wk I.k / 2 + 1)) = wk I.k - tailQ (wk I.k) by omega_using [hq],
        c₆, dhigh, Nat.mul_zero, Nat.add_zero] at e'
      rw [e, dlow, e', Nat.zero_add]
    obtain d8 : wv s₈.mem I.B (slot (wk I.k) aD) (wk I.k) = 2 ^ (64 * tailQ (wk I.k)) * (x * 2 ^ tailT (wk I.k)) := by
      rw [ot o₈ (by omega_arith) (by decide) (by decide), ot o₇ (Nat.le_refl _) (by decide) (by decide), d6]
    obtain hXlt : wv s₈.mem I.B (slot (wk I.k) aD) (wk I.k) <
        2 ^ (64 * (tailQ (wk I.k) + 2 + (wk I.k / 2 - 1))) := by
      rw [d8, show 64 * (tailQ (wk I.k) + 2 + (wk I.k / 2 - 1)) = 64 * tailQ (wk I.k) + 64 * (wk I.k / 2 + 1) by omega_using [hW6],
        pow_add]
      exact Nat.mul_lt_mul_of_le_of_lt (Nat.le_refl _) hxT (by positivity)
    obtain p8 : wv s₈.mem I.B (slot (wk I.k) aC) (wk I.k) = P := by
      rw [c₈, ot o₇ (Nat.le_refl _) (by decide) (by decide), o6 aP (by decide) (by decide),
        ot o₅ (Nat.le_refl _) (by decide) (by decide), u₂ aP (by decide) (by decide), hP]
    obtain pn : wv s₈.mem I.B (slot (wk I.k) aC) (wk I.k / 2) = P :=
      (wv_low_of_lt (by omega_using []) (by rw [p8]; exact hPlt)).trans p8
    obtain top := WordDivide.top_of_bound (m := s₈.mem) (B := I.B) (e := slot (wk I.k) aC) (n := wk I.k / 2) hn1
      (by rw [pn]; exact hPt)
    obtain r9 := v₉ hXlt top
    change wv s₉.mem I.B (slot (wk I.k) aV) (wk I.k + 1) =
      wv s₈.mem I.B (slot (wk I.k) aD) (wk I.k) % wv s₈.mem I.B (slot (wk I.k) aC) (wk I.k / 2) at r9
    rw [d8, pn] at r9
    obtain hlt : 2 ^ (64 * tailQ (wk I.k)) * (x * 2 ^ tailT (wk I.k)) % P < 2 ^ (64 * wk I.k) :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega_using [hx]))
        (Nat.le_trans hPlt.le (Nat.pow_le_pow_right (by decide) (by omega_using [])))
    obtain r9' : wv s₉.mem I.B (slot (wk I.k) aV) (wk I.k) = 2 ^ (64 * tailQ (wk I.k)) * (x * 2 ^ tailT (wk I.k)) % P :=
      (wv_low_of_lt (by omega_using []) (by rw [r9]; exact hlt)).trans r9
    rw [ot ot' (by omega_arith) (by decide) (by decide), c₁₁, ot o₁₀ (Nat.le_refl _) (by decide) (by decide), r9',
      tail_split, pow_add, pow_mul]
    congr 1; ring


/-- The public guard of `wordChoice` and `guarded` holds. -/
def cvGuard (I : CvIn) : Prop := WordDivide.guardVal (wk I.k) I.k I.pl I.ql ((I.nb[0]?).getD 0) = 0

instance (I : CvIn) : Decidable (cvGuard I) := by unfold cvGuard; infer_instance

theorem cvGuard_iff {I : CvIn} (L : CvLens I) :
    cvGuard I ↔ WordDivide.guardVal (wk I.k) I.k I.pl I.ql (I.nb[0]'(by rw [L.nl]; have := L.k1; omega_using [this])) = 0 := by
  obtain hnl : 0 < I.nb.length := by rw [L.nl]; have := L.k1; omega_using [this]
  simp only [cvGuard, List.getElem?_eq_getElem hnl, Option.getD_some]

/-- `guarded a b` runs `a` where the guard holds, else `b`, from the state after
the guard (which keeps the memory). -/
theorem cvGuarded_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) {a b : Prog isa}
    {Q : State → Prop}
    (ha : ∀ s₂, CvS I m₀ s₂ → s₂.mem = s.mem → cvGuard I → WP isa a s₂ Q)
    (hb : ∀ s₂, CvS I m₀ s₂ → s₂.mem = s.mem → ¬ cvGuard I → WP isa b s₂ Q) :
    WP isa (guarded a b) s Q := by
  unfold guarded
  refine WP.seq (WP.mono (WordDivide.guardHead_ok h) fun s₁ ⟨h₁, m₁, h12, hdx⟩ => ?_)
  refine WP.seq (WP.mono (WordDivide.guardTail_ok h₁ L h12 hdx) fun s₂ ⟨h₂, m₂, hz⟩ => ?_)
  refine WP.ite (WordDivide.guardVal (wk I.k) I.k I.pl I.ql (I.nb[0]'(by rw [L.nl]; have := L.k1; omega_using [this])) == 0)
    (by simp only [eval, hz]) (fun hg => ha s₂ h₂ (m₂.trans m₁) ((cvGuard_iff L).mpr (by simpa using hg)))
    (fun hg => hb s₂ h₂ (m₂.trans m₁) (fun g => by simp [(cvGuard_iff L).mp g] at hg))

/-- The guarded `qTail`: `[x₂] 2^K mod p` where the guard holds, for a `p` of
`n` words with its top bit set and `[x₂] < p`; `[x₂]` unchanged elsewhere. -/
theorem cvTailG_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) :
    WP isa (guarded (seqs qTail) (.block [])) s fun t => CvS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (∀ j, j = aP ∨ j = aQ ∨ j = aD →
        wv t.mem I.B (slot (wk I.k) j) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k)) ∧
      (cvGuard I → 2 ^ (64 * (wk I.k / 2) - 1) ≤ wv s.mem I.B (slot (wk I.k) aP) (wk I.k) →
        wv s.mem I.B (slot (wk I.k) aP) (wk I.k) < 2 ^ (64 * (wk I.k / 2)) →
        wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k) < wv s.mem I.B (slot (wk I.k) aP) (wk I.k) →
        wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) =
          wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k) * 2 ^ (15 * (wk I.k / 2) + 10) %
            wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) ∧
      (¬ cvGuard I → wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) = wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k)) := by
  refine cvGuarded_ok h L (fun s₂ h₂ m₂ g => ?_) (fun s₂ h₂ m₂ g => ?_)
  · refine WP.mono (cvQTail_ok h₂ L) fun t ⟨ht, mt, pt, vt⟩ => ⟨ht, by rw [mt, m₂], fun j hj => by rw [pt j hj, m₂],
      fun _ a b c => by rw [m₂] at vt; exact vt a b c, fun ng => absurd g ng⟩
  · exact WP.block_nil ⟨h₂, by rw [m₂], fun j _ => by rw [m₂], fun g' => absurd g' g, fun _ => by rw [m₂]⟩

end VG.Proof.Rsa.X86_64

end

end

/-!
# `vg_rsa_crt_values` on x86-64: `qInv`

`invPart` (`cvInv_ok`): `qInv = q⁻¹ mod p` by the batched divstep inverse,
and `gcd(q, p) = 1` and'ed into the mask (`cvGcd_ok`). Where the public guard
holds, the inverse is `inverseNS` and `qTail` scales its result by `2^K`
(`cvInvG_ok`, `CvTail.lean`'s `cvTailG_ok`); `p q = n`, which the mask
requires, gives `p` the top bit `qTail` needs.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-- The primes' width in words, `⌈max(p_len, q_len) / 8⌉`. -/
def nOf (pl ql : Nat) : Nat := (max pl ql + 7) / 8

theorem add7_shr3 {x : Nat} (hx : x < 2 ^ 32) :
    (BitVec.ofNat 64 x + BitVec.signExtend 64 (7 : BitVec 32)) >>> 3 = BitVec.ofNat 64 ((x + 7) / 8) := by
  rw [show BitVec.signExtend 64 (7 : BitVec 32) = BitVec.ofNat 64 7 by decide]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_using [hx]

/-- `ws` and `nPQ`: `w`, the stride and the primes' width. -/
theorem nPQ_ok {s : State} {B : Addr} {Z w pl ql : Nat} (h : Ws s B Z w)
    (hp : Bignum.word s.mem B (8 * sPl) = BitVec.ofNat 64 pl) (hq : Bignum.word s.mem B (8 * sQl) = BitVec.ofNat 64 ql)
    (hpl : pl < 2 ^ 32) (hql : ql < 2 ^ 32) :
    WP isa (.block (ws ++ nPQ)) s fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .r13 = BitVec.ofNat 64 (nOf pl ql) ∧ t.gpr .rdi = B ∧
      t.mem = s.mem ∧ Keep [.r12, .r9, .r13, .rax] s t := by
  refine WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_)
  obtain hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans h.rdi
  obtain hs₁ := h.scr.congr k₁.2.2
  obtain hl₁ : ∀ i < 32, InRegions (s₁.rd ++ s₁.wr) (off B (8 * i)) 8 := fun i hi =>
    hs₁.ld (by have := h.h256; omega_arith)
  refine WP.mono (WP.keep [.r13, .rax] (Q := fun t => t.gpr .r13 = BitVec.ofNat 64 (nOf pl ql) ∧ t.mem = s₁.mem)
    ?_ rfl) fun t ⟨⟨h13, mt⟩, kt⟩ =>
      ⟨(kt.gpr (by decide)).trans h12, (kt.gpr (by decide)).trans h9, h13, (kt.gpr (by decide)).trans hdi₁,
        mt.trans m₁, (k₁.trans kt).mono (by simp)⟩
  obtain hp₁ : Bignum.word s₁.mem B (8 * sPl) = BitVec.ofNat 64 pl := by rw [m₁]; exact hp
  obtain hq₁ : Bignum.word s₁.mem B (8 * sQl) = BitVec.ofNat 64 ql := by rw [m₁]; exact hq
  unfold nPQ nOf
  by_cases hlt : pl < ql
  · have hm : max pl ql = ql := by omega_using [hlt]
    rw [hm]
    xrun [State.ea, hdr, hdi₁, hdrOff, hl₁ sPl (by decide), hl₁ sQl (by decide), hp₁, hq₁,
      Nat.mod_eq_of_lt (show pl < 2 ^ 64 by omega_using [hpl]), Nat.mod_eq_of_lt (show ql < 2 ^ 64 by omega_using [hql]), hlt, execCmov, eval, readSrc, BitVec.toNat_ofNat]
    exact add7_shr3 (by omega_using [hql])
  · have hm : max pl ql = pl := by omega_using [hlt]
    rw [hm]
    xrun [State.ea, hdr, hdi₁, hdrOff, hl₁ sPl (by decide), hl₁ sQl (by decide), hp₁, hq₁,
      Nat.mod_eq_of_lt (show pl < 2 ^ 64 by omega_using [hpl]), Nat.mod_eq_of_lt (show ql < 2 ^ 64 by omega_using [hql]), hlt, execCmov, eval, readSrc, BitVec.toNat_ofNat]
    exact add7_shr3 (by omega_using [hpl])

theorem pow256_le {l n : Nat} (h : l ≤ 8 * n) : 256 ^ l ≤ 2 ^ (64 * n) := by
  rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by omega_using [h])

/-- The inverse at the primes' width `n`, of the low `n` words of `q` and
`p`: `inverseN_ok`'s, after `nPQ`, whatever the arrays hold. -/
theorem invQ_gen [InvLaw] {s : State} {B : Addr} {Z w pl ql : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z)
    (hw20 : w < 2 ^ 20) (hp : Bignum.word s.mem B (8 * sPl) = BitVec.ofNat 64 pl)
    (hq : Bignum.word s.mem B (8 * sQl) = BitVec.ofNat 64 ql) (hpl1 : 1 ≤ pl) (hplw : pl ≤ 8 * w)
    (hqlw : ql ≤ 8 * w) :
    WP isa (.seq (.block (ws ++ nPQ)) (inverseN aQ aV aX₂ aP)) s fun t => t.gpr .rdi = B ∧
      Frm B [(slot w aV, 8 * w), (slot w aX₂, 8 * w), (slot w 16, 80 * (w + 2))] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t ∧
      (wv s.mem B (slot w aP) (nOf pl ql) % 2 = 1 →
        wv t.mem B (slot w aV) w = Nat.gcd (wv s.mem B (slot w aQ) (nOf pl ql)) (wv s.mem B (slot w aP) (nOf pl ql)) ∧
        ((wv s.mem B (slot w aP) (nOf pl ql) : Nat) : Int) ∣
          (wv t.mem B (slot w aX₂) w : Int) * wv s.mem B (slot w aQ) (nOf pl ql) - wv t.mem B (slot w aV) w ∧
        wv t.mem B (slot w aX₂) w < wv s.mem B (slot w aP) (nOf pl ql)) := by
  obtain hn1 : 1 ≤ nOf pl ql := by unfold nOf; omega_using [hpl1]
  obtain hnw : nOf pl ql ≤ w := by unfold nOf; omega_using [hplw, hqlw]
  refine WP.seq (WP.mono (nPQ_ok h hp hq (by omega_using [hw20, hplw]) (by omega_using [hw20, hqlw])) fun s₁ ⟨_, h9, h13, _, m₁, k₁⟩ => ?_)
  obtain h₁ : Ws s₁ B Z w := h.congr (rs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) k₁ (by decide)
  rw [← m₁]
  exact WP.mono (InvLaw.inverseN_ok h₁ hZ h9 h13 hn1 hnw (by omega_using [hw20, hnw]) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t ⟨dt, ft, kt, ht⟩ => ⟨dt, ft, (k₁.trans kt).mono (by decide), ht⟩

/-- The inverse at the primes' width, `q⁻¹ mod p`: `inverse_ok`'s result
for `p < 256 ^ p_len` and `q < 256 ^ q_len`. -/
theorem invQ_ok [InvLaw] {s : State} {B : Addr} {Z w pl ql : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z)
    (hw20 : w < 2 ^ 20) (hp : Bignum.word s.mem B (8 * sPl) = BitVec.ofNat 64 pl)
    (hq : Bignum.word s.mem B (8 * sQl) = BitVec.ofNat 64 ql) (hpl1 : 1 ≤ pl) (hplw : pl ≤ 8 * w)
    (hqlw : ql ≤ 8 * w) (hP : wv s.mem B (slot w aP) w < 256 ^ pl) (hQ : wv s.mem B (slot w aQ) w < 256 ^ ql) :
    WP isa (.seq (.block (ws ++ nPQ)) (inverseN aQ aV aX₂ aP)) s fun t => t.gpr .rdi = B ∧
      Frm B [(slot w aV, 8 * w), (slot w aX₂, 8 * w), (slot w 16, 80 * (w + 2))] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t ∧
      (wv s.mem B (slot w aP) w % 2 = 1 →
        wv t.mem B (slot w aV) w = Nat.gcd (wv s.mem B (slot w aQ) w) (wv s.mem B (slot w aP) w) ∧
        ((wv s.mem B (slot w aP) w : Nat) : Int) ∣
          (wv t.mem B (slot w aX₂) w : Int) * wv s.mem B (slot w aQ) w - wv t.mem B (slot w aV) w ∧
        wv t.mem B (slot w aX₂) w < wv s.mem B (slot w aP) w) := by
  obtain hnw : nOf pl ql ≤ w := by unfold nOf; omega_using [hplw, hqlw]
  obtain hpn : pl ≤ 8 * nOf pl ql := by unfold nOf; omega_using []
  obtain hqn : ql ≤ 8 * nOf pl ql := by unfold nOf; omega_using []
  obtain eP := wv_low_of_lt hnw (Nat.lt_of_lt_of_le hP (pow256_le hpn))
  obtain eQ := wv_low_of_lt hnw (Nat.lt_of_lt_of_le hQ (pow256_le hqn))
  rw [← eP, ← eQ]
  exact invQ_gen h hZ hw20 hp hq hpl1 hplw hqlw

/-- `invQ_gen` for `inverseNS`. -/
theorem invQS_gen [InvLaw] {s : State} {B : Addr} {Z w pl ql : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z)
    (hw20 : w < 2 ^ 20) (hp : Bignum.word s.mem B (8 * sPl) = BitVec.ofNat 64 pl)
    (hq : Bignum.word s.mem B (8 * sQl) = BitVec.ofNat 64 ql) (hpl1 : 1 ≤ pl) (hplw : pl ≤ 8 * w)
    (hqlw : ql ≤ 8 * w) :
    WP isa (.seq (.block (ws ++ nPQ)) (inverseNS aQ aV aX₂ aP)) s fun t => t.gpr .rdi = B ∧
      Frm B [(slot w aV, 8 * w), (slot w aX₂, 8 * w), (slot w 16, 80 * (w + 2))] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  obtain hn1 : 1 ≤ nOf pl ql := by unfold nOf; omega_using [hpl1]
  obtain hnw : nOf pl ql ≤ w := by unfold nOf; omega_using [hplw, hqlw]
  refine WP.seq (WP.mono (nPQ_ok h hp hq (by omega_using [hw20, hplw]) (by omega_using [hw20, hqlw])) fun s₁ ⟨_, h9, h13, _, m₁, k₁⟩ => ?_)
  obtain h₁ : Ws s₁ B Z w := h.congr (rs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) k₁ (by decide)
  rw [← m₁]
  exact WP.mono (InvLaw.inverseNS_ok h₁ hZ h9 h13 hn1 hnw (by omega_using [hw20, hnw]) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t ⟨dt, ft, kt, _⟩ => ⟨dt, ft, (k₁.trans kt).mono (by decide)⟩

/-- `invQ_ok` for `inverseNS`: `[x₂] 2^(15 n + 10)` for `[x₂]`. -/
theorem invQS_ok [InvLaw] {s : State} {B : Addr} {Z w pl ql : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z)
    (hw20 : w < 2 ^ 20) (hp : Bignum.word s.mem B (8 * sPl) = BitVec.ofNat 64 pl)
    (hq : Bignum.word s.mem B (8 * sQl) = BitVec.ofNat 64 ql) (hpl1 : 1 ≤ pl) (hplw : pl ≤ 8 * w)
    (hqlw : ql ≤ 8 * w) (hP : wv s.mem B (slot w aP) w < 256 ^ pl) (hQ : wv s.mem B (slot w aQ) w < 256 ^ ql) :
    WP isa (.seq (.block (ws ++ nPQ)) (inverseNS aQ aV aX₂ aP)) s fun t => t.gpr .rdi = B ∧
      Frm B [(slot w aV, 8 * w), (slot w aX₂, 8 * w), (slot w 16, 80 * (w + 2))] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t ∧
      (wv s.mem B (slot w aP) w % 2 = 1 →
        wv t.mem B (slot w aV) w = Nat.gcd (wv s.mem B (slot w aQ) w) (wv s.mem B (slot w aP) w) ∧
        ((wv s.mem B (slot w aP) w : Nat) : Int) ∣
          (wv t.mem B (slot w aX₂) w : Int) * 2 ^ (15 * nOf pl ql + 10) * wv s.mem B (slot w aQ) w -
            wv t.mem B (slot w aV) w ∧
        wv t.mem B (slot w aX₂) w < wv s.mem B (slot w aP) w) := by
  obtain hn1 : 1 ≤ nOf pl ql := by unfold nOf; omega_using [hpl1]
  obtain hnw : nOf pl ql ≤ w := by unfold nOf; omega_using [hplw, hqlw]
  obtain hpn : pl ≤ 8 * nOf pl ql := by unfold nOf; omega_using []
  obtain hqn : ql ≤ 8 * nOf pl ql := by unfold nOf; omega_using []
  obtain eP := wv_low_of_lt hnw (Nat.lt_of_lt_of_le hP (pow256_le hpn))
  obtain eQ := wv_low_of_lt hnw (Nat.lt_of_lt_of_le hQ (pow256_le hqn))
  rw [← eP, ← eQ]
  refine WP.seq (WP.mono (nPQ_ok h hp hq (by omega_using [hw20, hplw]) (by omega_using [hw20, hqlw])) fun s₁ ⟨_, h9, h13, _, m₁, k₁⟩ => ?_)
  obtain h₁ : Ws s₁ B Z w := h.congr (rs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) k₁ (by decide)
  rw [← m₁]
  exact WP.mono (InvLaw.inverseNS_ok h₁ hZ h9 h13 hn1 hnw (by omega_using [hw20, hnw]) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t ⟨dt, ft, kt, ht⟩ => ⟨dt, ft, (k₁.trans kt).mono (by decide), ht⟩

/-- The inverse's frame, as `CvS` and the arrays and the mask it keeps. -/
theorem cvInvFrame {I : CvIn} {m₀ : Mem} {s t : State} (h : CvS I m₀ s)
    (f : Frm I.B [(slot (wk I.k) aV, 8 * wk I.k), (slot (wk I.k) aX₂, 8 * wk I.k), (slot (wk I.k) 16, 80 * (wk I.k + 2))]
      s.mem t.mem)
    (k : Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t) (L : CvLens I) :
    CvS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      ∀ j, j < 16 → j ≠ aV → j ≠ aX₂ →
        wv t.mem I.B (slot (wk I.k) j) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) := by
  have hn := h.ws.scr.nowrap
  have h256 := h.ws.h256
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  obtain e16 := slot_lin (wk I.k) 16
  obtain hZ26 : slot (wk I.k) 26 ≤ I.Z := by
    have := slot_lin (wk I.k) 26; have := L.z; have := L.k1; unfold wk at *; omega_arith
  refine ⟨h.step f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Mut.ofSlot _ _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only
    · have := h.ws.sl (j := aV) (by decide); omega_arith
    · have := h.ws.sl (j := aX₂) (by decide); omega_arith
    · have := slot_lin (wk I.k) 26; omega_arith) k (by decide), ?_, fun j hj h2 h4 => ?_⟩
  · exact f.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · have := hdr_lt_slot (wk I.k) aV (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith
      · have := hdr_lt_slot (wk I.k) aX₂ (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith
      · have := hdr_lt_slot (wk I.k) 16 (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith)
      (by omega_arith)
  · exact f.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · have := slot_far (w := wk I.k) h2; omega_arith
      · have := slot_far (w := wk I.k) h4; omega_arith
      · have := slot_lt (w := wk I.k) hj; omega_arith) (by have := h.ws.sl hj; omega_arith)

/-- The guarded inverse: `[x₂] q ≡ gcd(q, p)` scaled by `2^K` where the guard holds. -/
theorem cvInvG_ok [InvLaw] {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I)
    (hPl : wv s.mem I.B (slot (wk I.k) aP) (wk I.k) < 256 ^ I.pl)
    (hQl : wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) < 256 ^ I.ql) :
    WP isa (guarded (.seq (.block (ws ++ nPQ)) (inverseNS aQ aV aX₂ aP)) (.seq (.block (ws ++ nPQ)) (inverseN aQ aV aX₂ aP)))
      s fun t => CvS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
        (∀ j, j < 16 → j ≠ aV → j ≠ aX₂ →
          wv t.mem I.B (slot (wk I.k) j) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k)) ∧
        (wv s.mem I.B (slot (wk I.k) aP) (wk I.k) % 2 = 1 →
          wv t.mem I.B (slot (wk I.k) aV) (wk I.k) =
            Nat.gcd (wv s.mem I.B (slot (wk I.k) aQ) (wk I.k)) (wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) ∧
          ((wv s.mem I.B (slot (wk I.k) aP) (wk I.k) : Nat) : Int) ∣
            (wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) : Int) *
              (if cvGuard I then 2 ^ (15 * (wk I.k / 2) + 10) else 1) * wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) -
              wv t.mem I.B (slot (wk I.k) aV) (wk I.k) ∧
          wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) < wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) := by
  obtain hZ26 : slot (wk I.k) 26 ≤ I.Z := by
    have := slot_lin (wk I.k) 26; have := L.z; have := L.k1; unfold wk at *; omega_arith
  obtain hw20 : wk I.k < 2 ^ 20 := by have := L.k2; unfold wk; omega_using [this]
  refine cvGuarded_ok h L (fun s₂ h₂ m₂ g => ?_) (fun s₂ h₂ m₂ g => ?_)
  · rw [← m₂] at hPl hQl ⊢
    refine WP.mono (invQS_ok h₂.ws hZ26 hw20 h₂.args.pl h₂.args.ql L.pl1
      (by have := L.pl2; unfold wk; omega_using [this]) (by have := L.ql2; unfold wk; omega_using [this]) hPl hQl) fun t ⟨_, f, k, hv⟩ => ?_
    obtain ⟨ht, hm, ha⟩ := cvInvFrame h₂ f k L
    obtain ⟨hw2, hwk, hpk, hpq, -⟩ := WordDivide.guard_zero (by have := L.k2; unfold wk; omega_using [this])
      (by have := L.k2; omega_using [this]) (by have := L.k2; have := L.pl2; omega_arith) (by have := L.k2; have := L.ql2; omega_arith)
      ((cvGuard_iff L).mp g)
    obtain hn : nOf I.pl I.ql = wk I.k / 2 := by unfold nOf; omega_using [hw2, hwk, hpk, hpq]
    rw [hn] at hv
    refine ⟨ht, hm, ha, fun hp => ?_⟩
    obtain ⟨e1, e2, e3⟩ := hv hp
    simp only [g, ↓reduceIte]
    exact ⟨e1, e2, e3⟩
  · rw [← m₂] at hPl hQl ⊢
    refine WP.mono (invQ_ok h₂.ws hZ26 hw20 h₂.args.pl h₂.args.ql L.pl1
      (by have := L.pl2; unfold wk; omega_using [this]) (by have := L.ql2; unfold wk; omega_using [this]) hPl hQl) fun t ⟨_, f, k, hv⟩ => ?_
    obtain ⟨ht, hm, ha⟩ := cvInvFrame h₂ f k L
    refine ⟨ht, hm, ha, fun hp => ?_⟩
    obtain ⟨e1, e2, e3⟩ := hv hp
    simp only [g, ↓reduceIte, Int.mul_one]
    exact ⟨e1, e2, e3⟩

/-- `gcdPart`: the mask of `[v] = 1` and'ed into the mask; only `[c]` changes. -/
theorem cvGcd_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) {c : Bool} (hc : mword s.mem I.B = mask c) :
    WP isa (seqs gcdPart) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mask (c && decide (wv s.mem I.B (slot (wk I.k) aV) (wk I.k) = 1)) ∧
      ∀ j, j < 16 → j ≠ aC → wv t.mem I.B (slot (wk I.k) j) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  obtain hmw : ∀ {m m' : Mem} {j L' : Nat}, Outside I.B (slot (wk I.k) j) L' m m' → L' ≤ 8 * (wk I.k + 2) →
      mword m' I.B = mword m I.B := fun {_ _ j _} o _ =>
    o.word (Or.inl (by have := hdr_lt_slot (wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith))
      (by omega_arith)
  obtain wvw : ∀ {m m' : Mem} {j : Nat}, j < 16 →
      wv m' I.B (slot (wk I.k) j) (wk I.k + 2) = wv m I.B (slot (wk I.k) j) (wk I.k + 2) →
      wv m' I.B (slot (wk I.k) j) (wk I.k) = wv m I.B (slot (wk I.k) j) (wk I.k) := fun {m m' j} _ e => by
    obtain e1 := wv_add m I.B (slot (wk I.k) j) (wk I.k) 2
    obtain e2 := wv_add m' I.B (slot (wk I.k) j) (wk I.k) 2
    obtain l1 := wv_lt m I.B (slot (wk I.k) j) (wk I.k)
    obtain l2 := wv_lt m' I.B (slot (wk I.k) j) (wk I.k)
    rw [e] at e2
    have := congrArg (· % 2 ^ (64 * wk I.k)) (e1.symm.trans e2)
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2] at this
    exact this.symm
  obtain ot : ∀ {m m' : Mem} {j i Ln : Nat}, Outside I.B (slot (wk I.k) j) Ln m m' → Ln ≤ 8 * (wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (slot (wk I.k) i) (wk I.k) = wv m I.B (slot (wk I.k) i) (wk I.k) :=
    fun o hL hij hi => outside_arr o hL hij (by omega_arith) hi hZ hn
  simp only [gcdPart, List.cons_append, List.nil_append]
  -- `[c] := 1`, and the mask of `[v] = 1`.
  refine WP.seq (WP.mono (zeroA_ok h.ws (j := aC) (by decide)) fun s₉ ⟨z₉, o₉, k₉⟩ => ?_)
  obtain h₉ := h.arr (by decide) (Nat.le_refl _) o₉ k₉ (by decide)
  refine WP.seq (WP.mono (setOneA_ok h₉.ws (j := aC) (by decide)) fun s₁₀ ⟨m₁₀, k₁₀⟩ => ?_)
  obtain o₁₀ := writeW_outside s₉.mem I.B (1 : BitVec 64) (d := slot (wk I.k) aC) (by have := h.ws.sl (j := aC) (by decide); omega_arith)
  rw [← m₁₀] at o₁₀
  obtain h₁₀ := h₉.arr (by decide) (by omega_arith) o₁₀ k₁₀ (by decide)
  obtain vC : wv s₁₀.mem I.B (slot (wk I.k) aC) (wk I.k) = 1 := by
    rw [m₁₀, wv_low (by have := h.ws.w1; omega_arith), word_writeW_self,
      (writeW_outside s₉.mem I.B (1 : BitVec 64) (d := slot (wk I.k) aC) (by
        have := h.ws.sl (j := aC) (by decide); omega_arith)).wv (Or.inr (by omega_arith)) (by have := h.ws.sl (j := aC) (by decide); omega_arith)]
    obtain hz : ∀ q < wk I.k + 2, VG.Proof.Bignum.word s₉.mem I.B (slot (wk I.k) aC + 8 * q) = 0 :=
      (wv_eq_zero_iff _ _ _ _).mp z₉
    rw [wv_zero (n := wk I.k - 1) fun q hq => by
      have := hz (1 + q) (by omega_arith)
      rwa [show slot (wk I.k) aC + 8 * (1 + q) = slot (wk I.k) aC + 8 + 8 * q by omega_arith] at this]
    rfl
  obtain vV₁₀ : wv s₁₀.mem I.B (slot (wk I.k) aV) (wk I.k) = wv s.mem I.B (slot (wk I.k) aV) (wk I.k) := by
    rw [ot o₁₀ (by omega_arith) (by decide) (by decide), ot o₉ (Nat.le_refl _) (by decide) (by decide)]
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok h₁₀.ws (a := aV) (b := aC) (by decide) (by decide))
    fun s₁₁ ⟨hz₁₁, m₁₁, k₁₁⟩ => ?_)
  obtain h₁₁ := h₁₀.step (rs := []) (by rw [m₁₁]; exact Frm.refl _ _ _) (by simp) (by simp) k₁₁ (by decide)
  rw [vC, vV₁₀] at hz₁₁
  simp only [seqs]
  refine WP.mono (andZero_ok (c := c) h₁₁.ws (by rw [m₁₁]; exact (hmw o₁₀ (by omega_arith)).trans ((hmw o₉ (Nat.le_refl _)).trans hc)) hz₁₁)
    fun t ⟨mt, kt⟩ => ?_
  obtain ⟨ht, hmt, at'⟩ := h₁₁.mask mt kt (by decide)
  exact ⟨ht, hmt, fun j hj hne => by
    rw [wvw hj (at' j hj), m₁₁, ot o₁₀ (by omega_arith) hne hj, ot o₉ (Nat.le_refl _) hne hj]⟩

/-- `invPart`: `qInv` into `aX₂` and `gcd(q, p) = 1` and'ed into `sMask`,
for a mask that is set only if `p q = n`, so `p` is odd and above 1 (and, on
the guarded path, of `n = w / 2` words with its top bit set). -/
theorem cvInv_ok [InvLaw] {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) {c : Bool}
    (hc : mword s.mem I.B = mask c) (hPl : wv s.mem I.B (slot (wk I.k) aP) (wk I.k) < 256 ^ I.pl)
    (hQl : wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) < 256 ^ I.ql)
    (hcP : c = true → wv s.mem I.B (slot (wk I.k) aP) (wk I.k) % 2 = 1 ∧ 1 < wv s.mem I.B (slot (wk I.k) aP) (wk I.k))
    (hP : wv s.mem I.B (slot (wk I.k) aP) (wk I.k) = Spec.Rsa.os2ip I.pb)
    (hcN : c = true → Spec.Rsa.os2ip I.pb * Spec.Rsa.os2ip I.qb = Spec.Rsa.os2ip I.nb) :
    WP isa (seqs invPart) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mask (c && decide (Nat.gcd (wv s.mem I.B (slot (wk I.k) aQ) (wk I.k))
        (wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) = 1)) ∧
      (c = true → ((wv s.mem I.B (slot (wk I.k) aP) (wk I.k) : Nat) : Int) ∣
          (wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) : Int) * wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) -
            Nat.gcd (wv s.mem I.B (slot (wk I.k) aQ) (wk I.k)) (wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) ∧
        wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) < wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) ∧
      ∀ j, j = aP ∨ j = aQ ∨ j = aD → wv t.mem I.B (slot (wk I.k) j) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) := by
  unfold invPart
  rw [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [gcdPart])
    (WP.mono (cvInvG_ok h L hPl hQl) fun s₁ ⟨h₁, m₁, a₁, v₁⟩ => ?_)
  refine wp_seqs_append (by simp [gcdPart]) (by simp)
    (WP.mono (cvGcd_ok h₁ (c := c) (by rw [m₁, hc])) fun s₂ ⟨h₂, m₂, a₂⟩ => ?_)
  simp only [seqs]
  refine WP.mono (cvTailG_ok h₂ L) fun t ⟨ht, mt, pt, gt, nt⟩ => ?_
  obtain aPQD : ∀ j, j = aP ∨ j = aQ ∨ j = aD →
      wv s₂.mem I.B (slot (wk I.k) j) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) := fun j hj => by
    rcases hj with rfl | rfl | rfl <;>
      rw [a₂ _ (by decide) (by decide), a₁ _ (by decide) (by decide) (by decide)]
  obtain xV : wv s₂.mem I.B (slot (wk I.k) aX₂) (wk I.k) = wv s₁.mem I.B (slot (wk I.k) aX₂) (wk I.k) :=
    a₂ _ (by decide) (by decide)
  obtain vV : wv s₂.mem I.B (slot (wk I.k) aV) (wk I.k) = wv s₁.mem I.B (slot (wk I.k) aV) (wk I.k) :=
    a₂ _ (by decide) (by decide)
  refine ⟨ht, ?_, fun hcT => ?_, fun j hj => by rw [pt j hj, aPQD j hj]⟩
  · rw [mt, m₂]
    congr 1
    cases c
    · rfl
    · obtain ⟨hp, _⟩ := hcP rfl
      rw [(v₁ hp).1]
  · obtain ⟨hp, hp1⟩ := hcP hcT
    obtain ⟨e1, e2, e3⟩ := v₁ hp
    obtain P2 : wv s₂.mem I.B (slot (wk I.k) aP) (wk I.k) = wv s.mem I.B (slot (wk I.k) aP) (wk I.k) := aPQD aP (by simp)
    by_cases g : cvGuard I
    · simp only [g, ↓reduceIte] at e2
      obtain ⟨hw2, hwk, hpk, hpq, -⟩ := WordDivide.guard_zero (by have := L.k2; unfold wk; omega_using [this])
        (by have := L.k2; omega_using [this]) (by have := L.k2; have := L.pl2; omega_arith) (by have := L.k2; have := L.ql2; omega_arith)
        ((cvGuard_iff L).mp g)
      obtain ⟨⟨fp1, fp2⟩, -⟩ := WordDivide.factors_word L ((cvGuard_iff L).mp g) (hcN hcT)
      rw [← hP] at fp1 fp2
      obtain hx : wv s₂.mem I.B (slot (wk I.k) aX₂) (wk I.k) < wv s₂.mem I.B (slot (wk I.k) aP) (wk I.k) := by
        rw [xV, P2]; exact e3
      obtain vt := gt g (by rw [P2]; omega_using [fp1]) (by rw [P2]; exact fp2) hx
      rw [P2, xV] at vt
      refine ⟨?_, by rw [vt]; exact Nat.mod_lt _ (by omega_using [hp])⟩
      rw [vt, ← e1]
      obtain d1 : ((wv s.mem I.B (slot (wk I.k) aP) (wk I.k) : Nat) : Int) ∣
          (wv s₁.mem I.B (slot (wk I.k) aX₂) (wk I.k) : Int) * 2 ^ (15 * (wk I.k / 2) + 10) -
            ((wv s₁.mem I.B (slot (wk I.k) aX₂) (wk I.k) * 2 ^ (15 * (wk I.k / 2) + 10) %
              wv s.mem I.B (slot (wk I.k) aP) (wk I.k) : Nat) : Int) := by
        obtain hc : ((wv s₁.mem I.B (slot (wk I.k) aX₂) (wk I.k) * 2 ^ (15 * (wk I.k / 2) + 10) %
            wv s.mem I.B (slot (wk I.k) aP) (wk I.k) : Nat) : Int) =
            (wv s₁.mem I.B (slot (wk I.k) aX₂) (wk I.k) : Int) * 2 ^ (15 * (wk I.k / 2) + 10) %
              ((wv s.mem I.B (slot (wk I.k) aP) (wk I.k) : Nat) : Int) := by push_cast; rfl
        rw [hc]; exact Int.dvd_self_sub_of_emod_eq rfl
      obtain e : ((wv s₁.mem I.B (slot (wk I.k) aX₂) (wk I.k) * 2 ^ (15 * (wk I.k / 2) + 10) %
            wv s.mem I.B (slot (wk I.k) aP) (wk I.k) : Nat) : Int) * wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) -
            wv s₁.mem I.B (slot (wk I.k) aV) (wk I.k) =
          ((wv s₁.mem I.B (slot (wk I.k) aX₂) (wk I.k) : Int) * 2 ^ (15 * (wk I.k / 2) + 10) *
              wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) - wv s₁.mem I.B (slot (wk I.k) aV) (wk I.k)) -
          ((wv s₁.mem I.B (slot (wk I.k) aX₂) (wk I.k) : Int) * 2 ^ (15 * (wk I.k / 2) + 10) -
            ((wv s₁.mem I.B (slot (wk I.k) aX₂) (wk I.k) * 2 ^ (15 * (wk I.k / 2) + 10) %
              wv s.mem I.B (slot (wk I.k) aP) (wk I.k) : Nat) : Int)) * wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) := by
        ring
      rw [e]
      exact Int.dvd_sub e2 (d1.mul_right _)
    · simp only [g, ↓reduceIte, Int.mul_one] at e2
      rw [nt g, xV]
      exact ⟨by rw [← e1]; exact e2, e3⟩

end VG.Proof.Rsa.X86_64
