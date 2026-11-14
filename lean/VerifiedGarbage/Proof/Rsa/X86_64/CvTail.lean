module

public import VerifiedGarbage.Proof.Rsa.X86_64.CvCheck
public import VerifiedGarbage.Proof.Rsa.X86_64.WordGuard
public import VerifiedGarbage.Proof.Rsa.X86_64.WordFast
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Rsa.X86_64.ShlCl
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Loop
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

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
  have e63 : ∀ x : Nat, x &&& 63 = x % 64 := fun x => Nat.and_two_pow_sub_one_eq_mod x 6
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
  have sD := h.ws.sl (j := aD) (by decide)
  have sX := h.ws.sl (j := aX₂) (by decide)
  have hq : tailQ (wk I.k) + (wk I.k / 2 + 1) ≤ wk I.k := by unfold tailQ; omega_using [hw1]
  have hT : tailT (wk I.k) < 64 := by unfold tailT; omega_using []
  have far : slot (wk I.k) aD + 8 * (wk I.k + 2) ≤ slot (wk I.k) aX₂ := by
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
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have hs₄ := h.ws.scr.congr k14.2.2
  have mm : s₄.mem = s.mem := by rw [m₄, m₃, m₂, m₁]
  have h8₄ : s₄.gpr .r8 = off I.B (slot (wk I.k) aX₂) := (k₄.gpr (by decide)).trans h8
  have cx₄ : s₄.gpr .rcx = BitVec.ofNat 64 (tailT (wk I.k)) := ((k₃.trans k₄).gpr (by decide)).trans cx
  have r12₄ : s₄.gpr .r12 = BitVec.ofNat 64 (wk I.k / 2 + 1) := ((k₃.trans k₄).gpr (by decide)).trans r12
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = s₄.mem.writeW
      (off I.B (slot (wk I.k) aD + 8 * tailQ (wk I.k))) (word s.mem I.B (slot (wk I.k) aX₂) <<< tailT (wk I.k))) (by
    xrun [State.ea, at0, h8₄, hsi₄, cx₄, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₄.ld (d := slot (wk I.k) aX₂) (by omega_arith), hs₄.st (d := slot (wk I.k) aD + 8 * tailQ (wk I.k)) (by omega_arith),
      mm, execShiftCl, VarShiftOp.eval, cl_eq hT]) rfl)
    fun s₅ ⟨m₅, k₅⟩ => (show WP isa (wordLoop 1 shlClBody) s₅ _ from ?_)
  have hs₅ := hs₄.congr k₅.2.2
  refine WP.mono (shlCl_ok hT hs₅ ((k₅.gpr (by decide)).trans hsi₄) ((k₅.gpr (by decide)).trans h8₄)
    ((k₅.gpr (by decide)).trans r12₄) ((k₅.gpr (by decide)).trans cx₄) (by omega_using [hw1]) (by omega_arith)
    (by omega_arith) (by omega_arith) (.inl (by omega_arith)) (by
      rw [m₅, word_writeW_self, (writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith), mm,
        BitVec.toNat_shiftLeft, Nat.shiftLeft_eq])) fun u ⟨v, _, o, k₆⟩ => ?_
  have Jv : wv s₅.mem I.B (slot (wk I.k) aX₂) (wk I.k / 2 + 1) =
      wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k / 2 + 1) := by
    rw [m₅, (writeW_outside _ _ _ (by omega_arith)).wv (by omega_arith) (by omega_arith), mm]
  have ou : Outside I.B (slot (wk I.k) aD + 8 * tailQ (wk I.k)) (8 * (wk I.k / 2 + 1)) s.mem u.mem := by
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
  have hW6 : 6 ≤ wk I.k := by unfold wk; omega_using [hk1]
  have hZ17 : slot (wk I.k) 17 ≤ I.Z := by
    have hz := L.z
    simp only [slot, Impl.Bignum.hdrBytes, wk]
    omega_using [hk1, hz]
  have hq : tailQ (wk I.k) + (wk I.k / 2 + 1) ≤ wk I.k := by unfold tailQ; omega_using [hW6]
  have hT : tailT (wk I.k) < 64 := by unfold tailT; omega_using []
  have ot : ∀ {m m' : Mem} {j i Ln : Nat}, Outside I.B (slot (wk I.k) j) Ln m m' → Ln ≤ 8 * (wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (slot (wk I.k) i) (wk I.k) = wv m I.B (slot (wk I.k) i) (wk I.k) :=
    fun o hL hij hi => outside_arr o hL hij (by omega_arith) hi hZ hn
  have hmw : ∀ {m m' : Mem} {j L' : Nat}, Outside I.B (slot (wk I.k) j) L' m m' →
      mword m' I.B = mword m I.B := fun {_ _ j _} o =>
    o.word (Or.inl (by have := hdr_lt_slot (wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith))
      (by change 8 * 22 + 8 ≤ 2 ^ 64; decide)
  simp only [qTail, seqs]
  -- `[aSv] := d`.
  refine WP.seq (WP.mono (zeroA_ok h.ws (j := aSv) (by decide)) fun s₁ ⟨_, o₁, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₁.ws (o := aSv) (a := aD) (by decide) (by decide) (by decide))
    fun s₂ ⟨c₂, o₂, k₂⟩ => ?_)
  have h₂ := h₁.arr (by decide) (by omega_arith) o₂ k₂ (by decide)
  rw [ot o₁ (Nat.le_refl _) (by decide) (by decide)] at c₂
  have u₂ : ∀ i, i < 16 → i ≠ aSv → wv s₂.mem I.B (slot (wk I.k) i) (wk I.k) = wv s.mem I.B (slot (wk I.k) i) (wk I.k) :=
    fun i hi hne => by rw [ot o₂ (by omega_arith) hne hi, ot o₁ (Nat.le_refl _) hne hi]
  -- `[d] := [x₂] 2^T` at word `Q`.
  refine WP.seq (WP.mono (zeroA_ok h₂.ws (j := aD) (by decide)) fun s₅ ⟨z₅, o₅, k₅⟩ => ?_)
  have h₅ := h₂.arr (by decide) (Nat.le_refl _) o₅ k₅ (by decide)
  refine WP.seq (WP.mono (qShift_ok h₅) fun s₆ ⟨h₆, c₆, o₆⟩ => ?_)
  -- `[c] := p`.
  refine WP.seq (WP.mono (zeroA_ok h₆.ws (j := aC) (by decide)) fun s₇ ⟨_, o₇, k₇⟩ => ?_)
  have h₇ := h₆.arr (by decide) (Nat.le_refl _) o₇ k₇ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₇.ws (o := aC) (a := aP) (by decide) (by decide) (by decide))
    fun s₈ ⟨c₈, o₈, k₈⟩ => ?_)
  have h₈ := h₇.arr (by decide) (by omega_arith) o₈ k₈ (by decide)
  -- The reduction.
  refine WP.seq (WP.mono (WordDivide.fastAtWith_ok h₈.ws hZ17 hW6 (startT_ok hW6 hw)) fun s₉ ⟨v₉, f₉, k₉⟩ => ?_)
  have bound : ∀ r ∈ WordDivide.normRanges (wk I.k), r.1 + r.2 ≤ I.Z := by
    intro r hr
    simp only [WordDivide.normRanges, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact h.ws.sl (by decide)
    · exact WordDivide.all_bound h.ws hZ17 hr
  have h₉ := h₈.step f₉ (by
    intro r hr
    simp only [WordDivide.normRanges, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact Mut.ofSlot _ _ _
    · exact WordDivide.all_mut hr) bound k₉ (by decide)
  have f9 : ∀ i, i = aP ∨ i = aQ ∨ i = aD ∨ i = aX₂ ∨ i = aSv →
      wv s₉.mem I.B (slot (wk I.k) i) (wk I.k) = wv s₈.mem I.B (slot (wk I.k) i) (wk I.k) := fun i hi => by
    apply f₉.wv_eq _ (by have := h.ws.sl (j := i) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide); omega_arith)
    intro r hr
    simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [VG.Impl.Rsa.X86_64.WordDivide.aM, VG.Impl.Rsa.X86_64.WordDivide.aR, VG.Impl.Rsa.X86_64.WordDivide.aT,
        VG.Impl.Rsa.X86_64.WordDivide.aV, VG.Impl.Rsa.X86_64.Keys.CrtValues.aP,
        VG.Impl.Rsa.X86_64.Keys.CrtValues.aQ, VG.Impl.Rsa.X86_64.Keys.CrtValues.aD, aX₂, aSv, slot] <;> omega_arith
  have mw9 : mword s₉.mem I.B = mword s₈.mem I.B := f₉.word_eq (by
    intro r hr
    simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [VG.Impl.Rsa.X86_64.WordDivide.aM, VG.Impl.Rsa.X86_64.WordDivide.aR,
        VG.Impl.Rsa.X86_64.WordDivide.aT, VG.Impl.Rsa.X86_64.WordDivide.aV, slot, Public.sMask, sFn,
        Impl.Bignum.hdrBytes] <;> omega_arith) (by change 8 * 22 + 8 ≤ 2 ^ 64; decide)
  -- `[x₂] :=` the remainder, `[d] := [aSv]`.
  refine WP.seq (WP.mono (zeroA_ok h₉.ws (j := aX₂) (by decide)) fun s₁₀ ⟨_, o₁₀, k₁₀⟩ => ?_)
  have h₁₀ := h₉.arr (by decide) (Nat.le_refl _) o₁₀ k₁₀ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₁₀.ws (o := aX₂) (a := aV) (by decide) (by decide) (by decide))
    fun s₁₁ ⟨c₁₁, o₁₁, k₁₁⟩ => ?_)
  have h₁₁ := h₁₀.arr (by decide) (by omega_arith) o₁₁ k₁₁ (by decide)
  refine WP.mono (copyA_ok h₁₁.ws (o := aD) (a := aSv) (by decide) (by decide) (by decide))
    fun t ⟨ct, ot', kt⟩ => ?_
  have ht := h₁₁.arr (by decide) (by omega_arith) ot' kt (by decide)
  -- What each piece leaves.
  have o6 : ∀ i, i < 16 → i ≠ aD → wv s₆.mem I.B (slot (wk I.k) i) (wk I.k) = wv s₅.mem I.B (slot (wk I.k) i) (wk I.k) :=
    fun i hi hne => o₆.wv (by have := slot_far (w := wk I.k) hne; omega_arith)
      (by have := h.ws.sl hi; omega_arith)
  have pre : ∀ i, i < 16 → i ≠ aSv → i ≠ aX₂ → i ≠ aD → i ≠ aC → i ≠ aV → i ≠ 8 →
      wv t.mem I.B (slot (wk I.k) i) (wk I.k) = wv s.mem I.B (slot (wk I.k) i) (wk I.k) := fun i hi h1 h2 h3 h4 h5 h6 => by
    have e9 : wv s₉.mem I.B (slot (wk I.k) i) (wk I.k) = wv s₈.mem I.B (slot (wk I.k) i) (wk I.k) := by
      apply f₉.wv_eq _ (by have := h.ws.sl hi; omega_arith)
      intro r hr
      simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      have a1 := slot_far (w := wk I.k) (show i ≠ 9 from h4)
      have a2 := slot_far (w := wk I.k) (show i ≠ 3 from h5)
      have a3 := slot_far (w := wk I.k) h6
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
  have aSvT : wv s₁₁.mem I.B (slot (wk I.k) aSv) (wk I.k) = wv s.mem I.B (slot (wk I.k) aD) (wk I.k) := by
    rw [ot o₁₁ (by omega_arith) (by decide) (by decide), ot o₁₀ (Nat.le_refl _) (by decide) (by decide),
      f9 aSv (by simp), ot o₈ (by omega_arith) (by decide) (by decide), ot o₇ (Nat.le_refl _) (by decide) (by decide),
      o6 aSv (by decide) (by decide), ot o₅ (Nat.le_refl _) (by decide) (by decide), c₂]
  have sD := h.ws.sl (j := aD) (by decide)
  have sX := h.ws.sl (j := aX₂) (by decide)
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
    have hn1 : 1 ≤ wk I.k / 2 := by omega_using [hW6]
    generalize hP : wv s.mem I.B (slot (wk I.k) aP) (wk I.k) = P at hPt hPlt hx
    generalize hX : wv s.mem I.B (slot (wk I.k) aX₂) (wk I.k) = x at hx
    have hP1 : 2 ^ (64 * (wk I.k / 2)) * 2 ^ 64 = 2 ^ (64 * (wk I.k / 2 + 1)) := by
      rw [← pow_add]; congr 1
    have hxT : x * 2 ^ tailT (wk I.k) < 2 ^ (64 * (wk I.k / 2 + 1)) := by
      rw [← hP1]
      exact Nat.mul_lt_mul_of_lt_of_le (by omega_using [hPlt, hx]) (Nat.pow_le_pow_right (by decide) hT.le) (by positivity)
    have hxn : x < 2 ^ (64 * (wk I.k / 2 + 1)) := by
      have : 2 ^ (64 * (wk I.k / 2)) ≤ 2 ^ (64 * (wk I.k / 2 + 1)) := Nat.pow_le_pow_right (by decide) (by omega_using [])
      omega_using [hPlt, hx, hP1]
    have x5 : wv s₅.mem I.B (slot (wk I.k) aX₂) (wk I.k) = x := by
      rw [ot o₅ (Nat.le_refl _) (by decide) (by decide), u₂ aX₂ (by decide) (by decide), hX]
    have xl5 : wv s₅.mem I.B (slot (wk I.k) aX₂) (wk I.k / 2 + 1) = x :=
      (wv_low_of_lt (by omega_using [hW6]) (by rw [x5]; exact hxn)).trans x5
    rw [xl5, Nat.mod_eq_of_lt hxT] at c₆
    have zD : ∀ i, i < wk I.k + 2 → word s₅.mem I.B (slot (wk I.k) aD + 8 * i) = 0 :=
      (wv_eq_zero_iff _ _ _ _).mp z₅
    have dlow : wv s₆.mem I.B (slot (wk I.k) aD) (tailQ (wk I.k)) = 0 := by
      rw [o₆.wv (Or.inl (by omega_using [])) (by omega_arith)]
      exact wv_zero fun i hi => zD i (by omega_using [hq, hi])
    have dhigh : wv s₆.mem I.B (slot (wk I.k) aD + 8 * tailQ (wk I.k) + 8 * (wk I.k / 2 + 1))
        (wk I.k - tailQ (wk I.k) - (wk I.k / 2 + 1)) = 0 := by
      rw [o₆.wv (Or.inr (by omega_using [])) (by omega_arith)]
      exact wv_zero fun i hi => by
        rw [show slot (wk I.k) aD + 8 * tailQ (wk I.k) + 8 * (wk I.k / 2 + 1) + 8 * i =
          slot (wk I.k) aD + 8 * (tailQ (wk I.k) + (wk I.k / 2 + 1) + i) by omega_using []]
        exact zD _ (by omega_using [hi])
    have d6 : wv s₆.mem I.B (slot (wk I.k) aD) (wk I.k) = 2 ^ (64 * tailQ (wk I.k)) * (x * 2 ^ tailT (wk I.k)) := by
      have e := wv_add s₆.mem I.B (slot (wk I.k) aD) (tailQ (wk I.k)) (wk I.k - tailQ (wk I.k))
      have e' := wv_add s₆.mem I.B (slot (wk I.k) aD + 8 * tailQ (wk I.k)) (wk I.k / 2 + 1)
        (wk I.k - tailQ (wk I.k) - (wk I.k / 2 + 1))
      rw [show tailQ (wk I.k) + (wk I.k - tailQ (wk I.k)) = wk I.k by omega_using [hq]] at e
      rw [show wk I.k / 2 + 1 + (wk I.k - tailQ (wk I.k) - (wk I.k / 2 + 1)) = wk I.k - tailQ (wk I.k) by omega_using [hq],
        c₆, dhigh, Nat.mul_zero, Nat.add_zero] at e'
      rw [e, dlow, e', Nat.zero_add]
    have d8 : wv s₈.mem I.B (slot (wk I.k) aD) (wk I.k) = 2 ^ (64 * tailQ (wk I.k)) * (x * 2 ^ tailT (wk I.k)) := by
      rw [ot o₈ (by omega_arith) (by decide) (by decide), ot o₇ (Nat.le_refl _) (by decide) (by decide), d6]
    have hXlt : wv s₈.mem I.B (slot (wk I.k) aD) (wk I.k) <
        2 ^ (64 * (tailQ (wk I.k) + 2 + (wk I.k / 2 - 1))) := by
      rw [d8, show 64 * (tailQ (wk I.k) + 2 + (wk I.k / 2 - 1)) = 64 * tailQ (wk I.k) + 64 * (wk I.k / 2 + 1) by omega_using [hW6],
        pow_add]
      exact Nat.mul_lt_mul_of_le_of_lt (Nat.le_refl _) hxT (by positivity)
    have p8 : wv s₈.mem I.B (slot (wk I.k) aC) (wk I.k) = P := by
      rw [c₈, ot o₇ (Nat.le_refl _) (by decide) (by decide), o6 aP (by decide) (by decide),
        ot o₅ (Nat.le_refl _) (by decide) (by decide), u₂ aP (by decide) (by decide), hP]
    have pn : wv s₈.mem I.B (slot (wk I.k) aC) (wk I.k / 2) = P :=
      (wv_low_of_lt (by omega_using []) (by rw [p8]; exact hPlt)).trans p8
    have top := WordDivide.top_of_bound (m := s₈.mem) (B := I.B) (e := slot (wk I.k) aC) (n := wk I.k / 2) hn1
      (by rw [pn]; exact hPt)
    have r9 := v₉ hXlt top
    change wv s₉.mem I.B (slot (wk I.k) aV) (wk I.k + 1) =
      wv s₈.mem I.B (slot (wk I.k) aD) (wk I.k) % wv s₈.mem I.B (slot (wk I.k) aC) (wk I.k / 2) at r9
    rw [d8, pn] at r9
    have hlt : 2 ^ (64 * tailQ (wk I.k)) * (x * 2 ^ tailT (wk I.k)) % P < 2 ^ (64 * wk I.k) :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega_using [hx]))
        (Nat.le_trans hPlt.le (Nat.pow_le_pow_right (by decide) (by omega_using [])))
    have r9' : wv s₉.mem I.B (slot (wk I.k) aV) (wk I.k) = 2 ^ (64 * tailQ (wk I.k)) * (x * 2 ^ tailT (wk I.k)) % P :=
      (wv_low_of_lt (by omega_using []) (by rw [r9]; exact hlt)).trans r9
    rw [ot ot' (by omega_arith) (by decide) (by decide), c₁₁, ot o₁₀ (Nat.le_refl _) (by decide) (by decide), r9',
      tail_split, pow_add, pow_mul]
    congr 1; ring


/-- The public guard of `wordChoice` and `guarded` holds. -/
def cvGuard (I : CvIn) : Prop := WordDivide.guardVal (wk I.k) I.k I.pl I.ql ((I.nb[0]?).getD 0) = 0

instance (I : CvIn) : Decidable (cvGuard I) := by unfold cvGuard; infer_instance

theorem cvGuard_iff {I : CvIn} (L : CvLens I) :
    cvGuard I ↔ WordDivide.guardVal (wk I.k) I.k I.pl I.ql (I.nb[0]'(by rw [L.nl]; have := L.k1; omega_using [this])) = 0 := by
  have hnl : 0 < I.nb.length := by rw [L.nl]; have := L.k1; omega_using [this]
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
