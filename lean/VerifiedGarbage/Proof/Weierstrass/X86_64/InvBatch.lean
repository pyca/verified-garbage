module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvPacked
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Framework.Omega
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Divstep.TcS
import Mathlib.Tactic.LinearCombination
import VerifiedGarbage.Proof.Divstep.Packed
public import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import Aesop.BuiltinRules
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Weierstrass.InvMask
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Mont.X86_64.WideOps
import Mathlib.Data.Int.ModEq
public import Mathlib.Data.BitVec

/-! ### `Weierstrass.X86_64.InvRed`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.X86_64.InvWords`, which this module and modules that import it used -/

section

/-!
# Inversion by divsteps on x86-64: numbers of several words

The operations of a batch on words of the working space, as numbers: the
mask of a word's sign (`maskOf_ok`), a masked copy (`maskCopy_ok`), the
signed linear combination `w [x] + w' [y]` (`linR_ok`, column by column in
registers),
and the arithmetic shift by 59 (`shr59_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono toNat_ofBool)

/-! ## Masks -/

/-- The mask of a word's sign. -/
def smask (x : BitVec 64) : BitVec 64 := 0 - x >>> 63

theorem smask_toNat (x : BitVec 64) : (smask x).toNat = sgnW x := by
  rw [smask, BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  unfold sgnW; split <;> simp <;> omega_arith

theorem smask_isMask (x : BitVec 64) : IsMask (smask x) := by
  obtain hv := smask_toNat x
  unfold sgnW at hv; split at hv
  · exact Or.inr (BitVec.eq_of_toNat_eq (by rw [hv, BitVec.toNat_allOnes]))
  · exact Or.inl (BitVec.eq_of_toNat_eq (by rw [hv]; rfl))

/-- `v` masked by a word's sign: `v` if it is negative. -/
theorem masked_smask (x : BitVec 64) (v : Nat) : masked (smask x) v = if 2 ^ 63 ≤ x.toNat then v else 0 := by
  obtain hv := smask_toNat x
  by_cases h : 2 ^ 63 ≤ x.toNat
  · have e : smask x = BitVec.allOnes 64 := BitVec.eq_of_toNat_eq (by
      rw [hv, BitVec.toNat_allOnes]; unfold sgnW; simp only [h, ↓reduceIte])
    simp only [masked, e, h, ↓reduceIte]
  · have e : smask x ≠ BitVec.allOnes 64 := fun e => by
      rw [e, BitVec.toNat_allOnes] at hv; unfold sgnW at hv; simp only [h, ↓reduceIte] at hv
      exact absurd hv (by decide)
    simp only [masked, e, h, ↓reduceIte]

/-- `d = ` the mask of `src`'s sign, through `rax`. -/
theorem maskOf_ok (s : State) {d src : Reg} (hd : d ≠ .rax) :
    WP isa (.block (maskOf d src)) s fun t =>
      t.gpr d = smask (s.gpr src) ∧ Keeps [d, .rax] s t := by
  irun [maskOf, RegUpd.gpr_setReg_self]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [hd, ite_false, smask]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]

/-! ## Masked copies -/

/-- `[dst] = [src] & m` (`k` words). -/
theorem maskCopy_ok {base : Addr} {size : Nat} {m : Reg} (hm : m ≠ .r8) :
    ∀ (k : Nat) {s : State} {dst src : Nat}, Scr s base size → IsMask (s.gpr m) →
      dst + 8 * k ≤ size → src + 8 * k ≤ size → (dst + 8 * k ≤ src ∨ src + 8 * k ≤ dst) →
      WP isa (.block (maskCopy m dst src k)) s fun t =>
        wordsVal t.mem base dst k = masked (s.gpr m) (wordsVal s.mem base src k) ∧
        KeepRegs [.r8] s t ∧ Outside base dst (8 * k) s.mem t.mem
  | 0, s, _, _, _, _, _, _, _ => WP.block_nil ⟨by simp [wordsVal, masked], ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, s, dst, src, hs, hmask, hdst, hsrc, hsep => by
    have hn := hs.nowrap
    rw [maskCopy, WP.block_append_iff]
    obtain h1 : WP isa (.block [.mov .r8 (.mem (sc src)), .alu .and .r8 (.reg m), .store (sc dst) .r8]) s
        fun t => t.mem = s.mem.writeW (off base dst) (word s.mem base src &&& s.gpr m) ∧ KeepRegs [.r8] s t := by
      rw [← List.singleton_append, WP.block_append_iff]
      refine WP.mono (movMem_ok hs .r8 (d := src) (by omega_using [hsrc])) fun u ⟨lu, _, ku⟩ => ?_
      rw [← List.singleton_append, WP.block_append_iff]
      obtain hmu : u.gpr m = s.gpr m := ku.1 m (by simp [hm])
      obtain ha : WP isa (.block [.alu .and .r8 (.reg m)]) u fun v =>
          v.gpr .r8 = word s.mem base src &&& s.gpr m ∧ Keeps [.r8] u v := by
        irun [hmu, lu]
        exact ⟨fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false], rfl, rfl, rfl⟩
      refine WP.mono ha fun v ⟨av, kv⟩ => ?_
      obtain hsv := (hs.of_keeps ku (by decide)).of_keeps kv (by decide)
      refine WP.mono (storeReg_ok hsv .r8 (d := dst) (by omega_using [hdst])) fun t ⟨mt, gt, _, kt⟩ => ⟨?_, ?_⟩
      · rw [mt, av, kv.2.1, ku.2.1]
      · exact ((Keeps.regs ku).trans (Keeps.regs kv)).trans (kt.mono (by decide))
    refine WP.mono h1 fun s₁ ⟨m₁, k₁⟩ => ?_
    obtain hs₁ := hs.of_keepRegs k₁ (by decide)
    obtain O₁ : Outside base dst 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega_using [hdst, hn])
    obtain hm₁ : s₁.gpr m = s.gpr m := k₁.gpr m (by simp [hm])
    refine WP.mono (maskCopy_ok hm k hs₁ (dst := dst + 8) (src := src + 8) (by rw [hm₁]; exact hmask)
      (by omega_using [hdst]) (by omega_using [hsrc]) (by omega_using [hsep])) fun t ⟨e, kt, Ot⟩ => ?_
    refine ⟨?_, k₁.trans kt, fun x hx => by rw [Ot x (by omega_using [hx]), O₁ x (by omega_using [hx])]⟩
    obtain hS : wordsVal s₁.mem base (src + 8) k = wordsVal s.mem base (src + 8) k :=
      O₁.wordsVal (by omega_using [hsep]) (by omega_using [hsrc, hn])
    obtain hw : word t.mem base dst = word s₁.mem base dst := Ot.word (by omega_using []) (by omega_using [hdst, hn])
    rw [hm₁, hS] at e
    simp only [wordsVal]
    rw [hw, e, m₁, word_writeW_self, and_mask hmask, ← masked_add]

/-! ## The signed linear combination -/

/-- `omega` on the layout alone of `linR_ok`: first without its disjunctions,
which it would split, then with one. -/
tactic_template "inv_lin_omega" : tactic =>
  `(tactic| first
    | omega_using [hkK, hK, hk', hx, hy, hT, hU, hn]
    | omega_using [hkK, hK, hk', hx, hy, hT, hU, hn, hTx]
    | omega_using [hkK, hK, hk', hx, hy, hT, hU, hn, hTy]
    | omega_using [hkK, hK, hk', hx, hy, hT, hU, hn, hUT]
    | omega_using [hkK, hK, hk', hx, hy, hT, hU, hn, hUx]
    | omega_using [hkK, hK, hk', hx, hy, hT, hU, hn, hUy]
    | omega_using [hkK, hK, hk', hx, hy, hT, hU, hTx, hTy, hUT, hUx, hUy, hn])

/-! ## The shift by 59 -/

/-- `r8 *= 32`. -/
theorem shl5_ok (s : State) :
    WP isa (.block shl5) s fun t => (t.gpr .r8).toNat = (s.gpr .r8).toNat * 32 % 2 ^ 64 ∧ Keeps [.r8] s t := by
  irun [shl5]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]

/-- A word of the shift: `(lo >> 59) + 32 hi` does not wrap. -/
theorem shr_word (lo y : BitVec 64) {hi : Nat} (hy : y.toNat = hi * 32 % 2 ^ 64) :
    (lo >>> 59 + y).toNat = (lo.toNat / 2 ^ 59 + 2 ^ 5 * hi) % 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hy]
  have := lo.isLt
  omega_using []

/-- `[d] = (rax >> 59) + 32 r8`. -/
theorem shrTail_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat} (hd : d + 8 ≤ size) :
    WP isa (.block (shrTail d)) s fun t =>
      (word t.mem base d).toNat = ((s.gpr .rax).toNat / 2 ^ 59 + 2 ^ 5 * (s.gpr .r8).toNat) % 2 ^ 64 ∧
      KeepRegs [.rax, .r8] s t ∧ Outside base d 8 s.mem t.mem := by
  have hn := hs.nowrap
  rw [shrTail, List.append_assoc, WP.block_append_iff]
  obtain h1 : WP isa (.block [.shift .shr .rax 59]) s fun t => t.gpr .rax = s.gpr .rax >>> 59 ∧ Keeps [.rax] s t := by
    irun
    exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono h1 fun s₁ ⟨a₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (shl5_ok s₁) fun s₂ ⟨c₂, k₂⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  obtain h3 : WP isa (.block [.alu .add .rax (.reg .r8)]) s₂ fun t =>
      t.gpr .rax = s₂.gpr .rax + s₂.gpr .r8 ∧ Keeps [.rax] s₂ t := by
    irun
    exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono h3 fun s₃ ⟨a₃, k₃⟩ => ?_
  obtain hs₃ := ((hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  refine WP.mono (storeReg_ok hs₃ .rax hd) fun t ⟨mt, _, _, kt⟩ => ⟨?_, ?_, ?_⟩
  · rw [mt, word_writeW_self, a₃, k₂.1 .rax (by decide), a₁,
      shr_word _ _ (by rw [c₂, k₁.1 .r8 (by decide)])]
  · exact ((((Keeps.regs k₁).mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
      ((Keeps.regs k₃).mono (by decide))).trans (kt.mono (by decide))
  · rw [mt, k₃.2.1, k₂.2.1, k₁.2.1]; exact writeW_outside _ _ _ (by omega_using [hd, hn])

/-- `d = src`. -/
theorem movReg_ok (s : State) (d src : Reg) :
    WP isa (.block [.mov d (.reg src)]) s fun t => t.gpr d = s.gpr src ∧ Keeps [d] s t := by
  irun [RegUpd.gpr_setReg_self]
  exact ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩

/-- Words `0 … j - 1` of `[src] >> 59` (`j + 1 ≤ L` words of `[src]`). -/
theorem shrRows_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {dst src L : Nat}
    (hsrc : src + 8 * L ≤ size) (hdst : dst + 8 * L ≤ size) (hsep : dst + 8 * L ≤ src ∨ src + 8 * L ≤ dst) :
    ∀ j, j + 1 ≤ L → WP isa (.block ((List.range j).flatMap (shrStep dst src))) s fun t =>
      wordsVal t.mem base dst j = (wordsVal s.mem base src (j + 1) / 2 ^ 59) % 2 ^ (64 * j) ∧
      KeepRegs [.rax, .r8] s t ∧ Outside base dst (8 * j) s.mem t.mem
  | 0, _ => WP.block_nil ⟨by simp only [wordsVal, Nat.mul_zero, Nat.pow_zero, Nat.mod_one],
    ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | j + 1, hj => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (shrRows_ok hs hsrc hdst hsep j (by omega_using [hj])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    obtain hs₁ := hs.of_keepRegs k₁ (by decide)
    rw [shrStep, ← List.singleton_append, List.append_assoc, WP.block_append_iff]
    refine WP.mono (movMem_ok hs₁ .rax (d := src + 8 * j) (by omega_using [hsrc, hj])) fun s₂ ⟨l₂, _, k₂⟩ => ?_
    obtain hs₂ := hs₁.of_keeps k₂ (by decide)
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (movMem_ok hs₂ .r8 (d := src + 8 * (j + 1)) (by omega_using [hsrc, hj])) fun s₃ ⟨l₃, _, k₃⟩ => ?_
    obtain hs₃ := hs₂.of_keeps k₃ (by decide)
    refine WP.mono (shrTail_ok hs₃ (d := dst + 8 * j) (by omega_using [hdst, hj])) fun t ⟨e, kt, Ot⟩ =>
      ⟨?_, ((k₁.trans ((Keeps.regs k₂).mono (by decide))).trans ((Keeps.regs k₃).mono (by decide))).trans kt,
        fun x hx => by rw [Ot x (by omega_using [hx]), k₃.2.1, k₂.2.1, O₁ x (by omega_using [hx])]⟩
    obtain w₂ : word s₁.mem base (src + 8 * j) = word s.mem base (src + 8 * j) := O₁.word (by omega_using [hsep, hj]) (by omega_using [hsrc, hj, hn])
    obtain w₃ : word s₂.mem base (src + 8 * (j + 1)) = word s.mem base (src + 8 * (j + 1)) := by
      rw [k₂.2.1]; exact O₁.word (by omega_using [hsep, hj]) (by omega_using [hsrc, hj, hn])
    rw [wordsVal_succ_top, Ot.wordsVal (by omega_using []) (by omega_using [hdst, hj, hn]), k₃.2.1, k₂.2.1, e₁, e, k₃.1 .rax (by decide), l₂,
      l₃, w₂, w₃, wordsVal_succ_top s.mem base src (j + 1), wordsVal_succ_top s.mem base src j, pow64_succ,
      Nat.mul_comm (2 ^ 64) (2 ^ (64 * j))]
    exact (shr_arith j _ _ _ (wordsVal_lt _ _ _ _)).symm

/-- `[dst] = [src] >> 59`, arithmetic (`L ≥ 1` words). -/
theorem shr59_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {dst src L : Nat} (hL : 1 ≤ L)
    (hsrc : src + 8 * L ≤ size) (hdst : dst + 8 * L ≤ size) (hsep : dst + 8 * L ≤ src ∨ src + 8 * L ≤ dst) :
    WP isa (.block (shr59 dst src L)) s fun t =>
      wordsVal t.mem base dst L = (sext s.mem base src L / 2 ^ 59) % 2 ^ (64 * L) ∧
      KeepRegs [.rax, .rdx, .r8] s t ∧ Outside base dst (8 * L) s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨j, rfl⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega_using [hL]⟩
  simp only [shr59, Nat.add_sub_cancel]
  rw [List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (shrRows_ok hs hsrc hdst hsep j (Nat.le_refl _)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movMem_ok hs₁ .rdx (d := src + 8 * j) (by omega_using [hsrc])) fun s₂ ⟨l₂, _, k₂⟩ => ?_
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (maskOf_ok s₂ (d := .r8) (src := .rdx) (by decide)) fun s₃ ⟨g₃, k₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movReg_ok s₃ .rax .rdx) fun s₄ ⟨g₄, k₄⟩ => ?_
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (shrTail_ok hs₄ (d := dst + 8 * j) (by omega_using [hdst])) fun t ⟨e, kt, Ot⟩ =>
    ⟨?_, (((k₁.mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
      (((Keeps.regs k₃).mono (by decide)).trans ((Keeps.regs k₄).mono (by decide)))).trans (kt.mono (by decide)),
      fun x hx => by rw [Ot x (by omega_using [hx]), k₄.2.1, k₃.2.1, k₂.2.1, O₁ x (by omega_using [hx])]⟩
  obtain w₂ : word s₁.mem base (src + 8 * j) = word s.mem base (src + 8 * j) := O₁.word (by omega_using [hsep]) (by omega_using [hn, hsrc])
  rw [wordsVal_succ_top, Ot.wordsVal (by omega_using []) (by omega_using [hn, hdst]), k₄.2.1, k₃.2.1, k₂.2.1, e₁, e, g₄,
    k₄.1 .r8 (by decide), g₃, smask_toNat, k₃.1 .rdx (by decide), l₂, w₂, sext, Nat.add_sub_cancel,
    wordsVal_succ_top s.mem base src j, pow64_succ, Nat.mul_comm (2 ^ 64) (2 ^ (64 * j))]
  exact (shr_arith j _ _ _ (wordsVal_lt _ _ _ _)).symm

/-! ## The signed linear combination in registers

`linR` computes the signed `w [x] + w' [y]` modulo `2^(64 K)` (`linR_ok`):
with `a = |w|`
and `M` the mask of `w`'s sign, `w X ≡ a (X ⊕ M) + (a & M)` (`X ⊕ M` over `K`
words is `X` or `2^(64 K) - 1 - X`, `xorSum_zero`, `xorSum_ones`), and the
sum is taken column by column: each column's two products added to the
accumulator `r8`, `r13`, which never overflows for `a`, `|w'| ≤ 2^62`
(`linCol_ok`), its low word stored. -/

/-! ## Absolute values -/

/-- `|x|` of a signed word: `(x ⊕ mask) - mask`. -/
def absW (x : BitVec 64) : BitVec 64 := (x ^^^ smask x) - smask x

theorem absW_toNat (x : BitVec 64) : (absW x).toNat = x.toInt.natAbs := by
  have hx := x.isLt
  obtain ht := Divstep.toInt_sgn x
  obtain hv := smask_toNat x
  unfold sgnW at hv
  unfold absW
  by_cases h : 2 ^ 63 ≤ x.toNat
  · have e : smask x = BitVec.allOnes 64 := BitVec.eq_of_toNat_eq (by rw [hv, BitVec.toNat_allOnes, ite_eq_left_of_eq_true _ _ (eq_true h)])
    rw [e, BitVec.xor_allOnes, BitVec.toNat_sub, BitVec.toNat_not, BitVec.toNat_allOnes]
    simp only [h, ↓reduceIte] at ht
    omega_using [h, ht]
  · have e : smask x = 0 := BitVec.eq_of_toNat_eq (by rw [hv, ite_eq_right_of_eq_false _ _ (eq_false h)]; rfl)
    rw [e]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.xor_zero, BitVec.sub_zero]
    simp only [h, ↓reduceIte] at ht
    omega_using [ht]

/-- `a = |w|` and `[sl]` the mask of `w`'s sign. -/
theorem absMask_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w a : Reg}
    (hw : w ∉ [Reg.rax, .rdx]) (ha : a ∉ [Reg.rax, .rdx]) (haw : a ≠ w) {sl : Nat} (hsl : sl + 8 ≤ size) :
    WP isa (.block (absMask w a sl)) s fun t =>
      t.gpr a = absW (s.gpr w) ∧ t.mem = s.mem.writeW (off base sl) (smask (s.gpr w)) ∧
      KeepRegs [.rax, .rdx, a] s t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw ha
  rw [absMask, show ∀ (i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ : Instr), [i₁, i₂, i₃, i₄, i₅, i₆, i₇, i₈] =
    [i₁, i₂, i₃, i₄] ++ ([i₅] ++ [i₆, i₇, i₈]) from fun _ _ _ _ _ _ _ _ => rfl, WP.block_append_iff]
  have h₁ : WP isa (.block [.mov .rax (.reg w), .shift .shr .rax 63, .mov32 .rdx (.imm 0),
      .alu .sub .rdx (.reg .rax)]) s fun t => t.gpr .rdx = smask (s.gpr w) ∧ Keeps [.rax, .rdx] s t := by
    irun
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
    · simp only [smask]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]
  refine WP.mono h₁ fun s₁ ⟨d₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storeReg_ok hs₁ .rdx hsl) fun s₂ ⟨m₂, g₂, _, k₂⟩ => ?_
  have hw₂ : s₂.gpr w = s.gpr w := by rw [g₂]; exact k₁.1 w (by simp [hw.1, hw.2])
  have hd₂ : s₂.gpr .rdx = smask (s.gpr w) := by rw [g₂, d₁]
  have h₃ : WP isa (.block [.mov a (.reg w), .alu .xor a (.reg .rdx), .alu .sub a (.reg .rdx)]) s₂
      fun t => t.gpr a = absW (s.gpr w) ∧ Keeps [a] s₂ t := by
    have h1 : ¬Reg.rdx = a := fun h => ha.2 h.symm
    have h2 : ¬w = a := fun h => haw h.symm
    irun [h1, h2, RegUpd.gpr_setReg_self]
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
    · rw [hw₂, hd₂]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  refine WP.mono h₃ fun t ⟨at', kt⟩ => ⟨at', ?_, ?_⟩
  · rw [kt.2.1, m₂, d₁, k₁.2.1]
  · exact ((Keeps.regs k₁).mono (by regions_sub)).trans ((k₂.mono (by regions_sub)).trans ((Keeps.regs kt).mono (by regions_sub)))

/-! ## Small blocks -/

/-- `d &= [x]`. -/
theorem andMem_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (d : Reg) {x : Nat}
    (hx : x + 8 ≤ size) :
    WP isa (.block [.alu .and d (.mem (sc x))]) s fun t =>
      t.gpr d = s.gpr d &&& word s.mem base x ∧ Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc_sc hs hx, Option.bind_some,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `d ^= [x]`. -/
theorem xorMem_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (d : Reg) {x : Nat}
    (hx : x + 8 ≤ size) :
    WP isa (.block [.alu .xor d (.mem (sc x))]) s fun t =>
      t.gpr d = s.gpr d ^^^ word s.mem base x ∧ Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc_sc hs hx, Option.bind_some,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- The arithmetic of `r8, r13 += rdx:rax` (`add`, `adc`), which does not overflow. -/
theorem acc_arith (lo hi a c : BitVec 64) {P : Nat} (hlo : lo.toNat = P % 2 ^ 64) (hhi : hi.toNat = P / 2 ^ 64)
    (hb : a.toNat + 2 ^ 64 * c.toNat + P < 2 ^ 128) :
    (a + lo).toNat + 2 ^ 64 *
        (c + hi + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + lo.toNat))).setWidth 64).toNat =
      a.toNat + 2 ^ 64 * c.toNat + P := by
  obtain ha := a.isLt; have hc := c.isLt
  simp only [BitVec.toNat_add, toNat_ofBool, hlo, hhi]
  by_cases h : 2 ^ 64 ≤ a.toNat + P % 2 ^ 64 <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_using [hb, h]

/-- `r8, r13 += rax · m`. -/
theorem macc_ok (s : State) (m : Reg)
    (hb : (s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r13).toNat + (s.gpr .rax).toNat * (s.gpr m).toNat < 2 ^ 128) :
    WP isa (.block [.mul m, .alu .add .r8 (.reg .rax), .alu .adc .r13 (.reg .rdx)]) s fun t =>
      (t.gpr .r8).toNat + 2 ^ 64 * (t.gpr .r13).toNat =
        (s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r13).toNat + (s.gpr .rax).toNat * (s.gpr m).toNat ∧
      Keeps [.rax, .rdx, .r8, .r13] s t := by
  irun [RegUpd.cf_setReg]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have hp := Nat.mul_lt_mul'' (s.gpr .rax).isLt (s.gpr m).isLt
    exact acc_arith _ _ _ _ (BitVec.toNat_ofNat _ _)
      (by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hp])) hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2, ite_false]

/-- `[x] ⊕ [sl]`, as a number. -/
abbrev xorW (m : Mem) (base : Addr) (x sl : Nat) : Nat := (word m base x ^^^ word m base sl).toNat

/-- `r8, r13 += m · ([x] ⊕ [sl])`. -/
theorem linTerm_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {m : Reg}
    (hm : m ≠ .rax) {x sl : Nat} (hx : x + 8 ≤ size) (hsl : sl + 8 ≤ size)
    (hb : (s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r13).toNat + 2 ^ 64 * (s.gpr m).toNat ≤ 2 ^ 128) :
    WP isa (.block (linTerm m x sl)) s fun t =>
      (t.gpr .r8).toNat + 2 ^ 64 * (t.gpr .r13).toNat =
        (s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r13).toNat + (s.gpr m).toNat * xorW s.mem base x sl ∧
      Keeps [.rax, .rdx, .r8, .r13] s t := by
  rw [linTerm, show ∀ (i₁ i₂ i₃ i₄ i₅ : Instr), [i₁, i₂, i₃, i₄, i₅] = [i₁] ++ ([i₂] ++ [i₃, i₄, i₅])
    from fun _ _ _ _ _ => rfl, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .rax hx) fun s₁ ⟨l₁, _, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (xorMem_ok hs₁ .rax hsl) fun s₂ ⟨l₂, k₂⟩ => ?_
  obtain g : ∀ r, r ≠ .rax → s₂.gpr r = s.gpr r := fun r hr =>
    (k₂.1 r (by simp [hr])).trans (k₁.1 r (by simp [hr]))
  obtain hv : (s₂.gpr .rax).toNat = xorW s.mem base x sl := by rw [l₂, l₁, k₁.2.1]
  obtain hwl := (word s.mem base x ^^^ word s.mem base sl).isLt
  obtain hml : xorW s.mem base x sl * (s.gpr m).toNat ≤ (2 ^ 64 - 1) * (s.gpr m).toNat :=
    Nat.mul_le_mul_right _ (by omega_using [hv])
  refine WP.mono (macc_ok s₂ m (by
    rw [hv, g .r8 (by decide), g .r13 (by decide), g m hm]
    rw [Nat.sub_mul, Nat.one_mul] at hml
    omega_using [hb, hml])) fun t ⟨e, kt⟩ => ⟨?_, ((k₁.mono (by regions_sub)).trans (k₂.mono (by regions_sub))).trans kt⟩
  rw [e, hv, g .r8 (by decide), g .r13 (by decide), g m hm, Nat.mul_comm (s.gpr m).toNat]

/-- `r8, r13 += m · [sl]`. -/
theorem linTermTop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {m : Reg}
    (hm : m ≠ .rax) {sl : Nat} (hsl : sl + 8 ≤ size)
    (hb : (s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r13).toNat + 2 ^ 64 * (s.gpr m).toNat ≤ 2 ^ 128) :
    WP isa (.block (linTermTop m sl)) s fun t =>
      (t.gpr .r8).toNat + 2 ^ 64 * (t.gpr .r13).toNat =
        (s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r13).toNat + (s.gpr m).toNat * (word s.mem base sl).toNat ∧
      Keeps [.rax, .rdx, .r8, .r13] s t := by
  rw [linTermTop, show ∀ (i₁ i₂ i₃ i₄ : Instr), [i₁, i₂, i₃, i₄] = [i₁] ++ [i₂, i₃, i₄]
    from fun _ _ _ _ => rfl, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .rax hsl) fun s₁ ⟨l₁, _, k₁⟩ => ?_
  obtain g : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r := fun r hr => k₁.1 r (by simp [hr])
  obtain hwl := (word s.mem base sl).isLt
  obtain hml : (word s.mem base sl).toNat * (s.gpr m).toNat ≤ (2 ^ 64 - 1) * (s.gpr m).toNat :=
    Nat.mul_le_mul_right _ (by omega_using [])
  refine WP.mono (macc_ok s₁ m (by
    rw [l₁, g .r8 (by decide), g .r13 (by decide), g m hm]
    rw [Nat.sub_mul, Nat.one_mul] at hml
    omega_using [hb, hml])) fun t ⟨e, kt⟩ => ⟨?_, (k₁.mono (by regions_sub)).trans kt⟩
  rw [e, l₁, g .r8 (by decide), g .r13 (by decide), g m hm, Nat.mul_comm (s.gpr m).toNat]

/-- `[T] = r8`, `r8 = r13`, `r13 = 0`. -/
theorem linOut_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {T : Nat} (hT : T + 8 ≤ size) :
    WP isa (.block (linOut T)) s fun t =>
      t.mem = s.mem.writeW (off base T) (s.gpr .r8) ∧ t.gpr .r8 = s.gpr .r13 ∧ t.gpr .r13 = 0 ∧
      KeepRegs [.r8, .r13] s t := by
  rw [linOut, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (storeReg_ok hs .r8 hT) fun s₁ ⟨m₁, g₁, _, k₁⟩ => ?_
  obtain h : WP isa (.block [.mov .r8 (.reg .r13), .mov32 .r13 (.imm 0)]) s₁ fun t =>
      t.gpr .r8 = s₁.gpr .r13 ∧ t.gpr .r13 = 0 ∧ Keeps [.r8, .r13] s₁ t := by
    irun
    refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]
  refine WP.mono h fun t ⟨e8, e13, kt⟩ => ⟨by rw [kt.2.1, m₁], by rw [e8, g₁], e13,
    (k₁.mono (by regions_sub)).trans (Keeps.regs kt)⟩

/-- The accumulator's start: `r8 = (rcx & [U]) + (rbp & [U + 8])`, `r13 = 0`. -/
theorem linInit_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {U : Nat} (hU : U + 16 ≤ size)
    (hm : IsMask (word s.mem base U)) (hm' : IsMask (word s.mem base (U + 8)))
    (ha : (s.gpr .rcx).toNat ≤ 2 ^ 62) (hb : (s.gpr .rbp).toNat ≤ 2 ^ 62) :
    WP isa (.block (linInit U)) s fun t =>
      (t.gpr .r8).toNat = masked (word s.mem base U) (s.gpr .rcx).toNat +
        masked (word s.mem base (U + 8)) (s.gpr .rbp).toNat ∧ t.gpr .r13 = 0 ∧ Keeps [.rax, .r8, .r13] s t := by
  rw [linInit, show ∀ (i₁ i₂ i₃ i₄ i₅ i₆ : Instr), [i₁, i₂, i₃, i₄, i₅, i₆] =
    [i₁] ++ ([i₂] ++ ([i₃] ++ ([i₄] ++ [i₅, i₆]))) from fun _ _ _ _ _ _ => rfl, WP.block_append_iff]
  obtain h₁ : WP isa (.block [.mov .r8 (.reg .rcx)]) s fun t => t.gpr .r8 = s.gpr .rcx ∧ Keeps [.r8] s t := by
    irun
    exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono h₁ fun s₁ ⟨e₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (andMem_ok hs₁ .r8 (x := U) (by omega_using [hU])) fun s₂ ⟨e₂, k₂⟩ => ?_
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  obtain h₃ : WP isa (.block [.mov .rax (.reg .rbp)]) s₂ fun t => t.gpr .rax = s₂.gpr .rbp ∧ Keeps [.rax] s₂ t := by
    irun
    exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono h₃ fun s₃ ⟨e₃, k₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (andMem_ok hs₃ .rax (x := U + 8) (by omega_using [hU])) fun s₄ ⟨e₄, k₄⟩ => ?_
  obtain hm₄ : s₄.mem = s.mem := by rw [k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1]
  obtain hm₃ : s₃.mem = s.mem := by rw [k₃.2.1, k₂.2.1, k₁.2.1]
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  obtain v8 : (s₄.gpr .r8).toNat = masked (word s.mem base U) (s.gpr .rcx).toNat := by
    rw [k₄.1 .r8 (by decide), k₃.1 .r8 (by decide), e₂, e₁, hm₁, and_mask hm]
  obtain vax : (s₄.gpr .rax).toNat = masked (word s.mem base (U + 8)) (s.gpr .rbp).toNat := by
    rw [e₄, e₃, hm₃, k₂.1 .rbp (by decide), k₁.1 .rbp (by decide), and_mask hm']
  obtain h₅ : WP isa (.block [.alu .add .r8 (.reg .rax), .mov32 .r13 (.imm 0)]) s₄ fun t =>
      t.gpr .r8 = s₄.gpr .r8 + s₄.gpr .rax ∧ t.gpr .r13 = 0 ∧ Keeps [.r8, .r13] s₄ t := by
    irun
    exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false], rfl, rfl, rfl⟩
  refine WP.mono h₅ fun t ⟨e8, e13, kt⟩ => ⟨?_, e13, ?_⟩
  · have m1 := masked_le (word s.mem base U) (s.gpr .rcx).toNat
    obtain m2 := masked_le (word s.mem base (U + 8)) (s.gpr .rbp).toNat
    rw [e8, BitVec.toNat_add, v8, vax]
    exact Nat.mod_eq_of_lt (by omega_using [ha, hb, m1, m2])
  · exact ((((k₁.mono (by regions_sub)).trans (k₂.mono (by regions_sub))).trans (k₃.mono (by regions_sub))).trans
      (k₄.mono (by regions_sub))).trans (kt.mono (by regions_sub))

/-- A column: `[T'] + 2^64 r8' = r8 + rcx X + rbp Y` for `X`, `Y` the
terms' words; `r13` stays zero. -/
theorem linCol_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {T x y U i : Nat} (hx : x + 8 * i + 8 ≤ size) (hy : y + 8 * i + 8 ≤ size) (hU : U + 16 ≤ size)
    (hT : (T + 8 * i) + 8 ≤ size) (h13 : s.gpr .r13 = 0) (ha : (s.gpr .rcx).toNat ≤ 2 ^ 62)
    (hb : (s.gpr .rbp).toNat ≤ 2 ^ 62) :
    WP isa (.block (linCol T x y U i)) s fun t =>
      (word t.mem base (T + 8 * i)).toNat + 2 ^ 64 * (t.gpr .r8).toNat =
        (s.gpr .r8).toNat + (s.gpr .rcx).toNat * xorW s.mem base (x + 8 * i) U + (s.gpr .rbp).toNat * xorW s.mem base (y + 8 * i) (U + 8) ∧
      t.gpr .r13 = 0 ∧ KeepRegs [.rax, .rdx, .r8, .r13] s t ∧ Outside base (T + 8 * i) 8 s.mem t.mem := by
  have hn := hs.nowrap
  rw [linCol, List.append_assoc, WP.block_append_iff]
  obtain hr8 := (s.gpr .r8).isLt
  obtain z : (s.gpr .r13).toNat = 0 := by rw [h13]; rfl
  refine WP.mono (linTerm_ok hs (m := .rcx) (by decide) (x := x + 8 * i) (sl := U) hx (by omega_using [hU]) (by
    rw [z]; omega_using [])) fun s₁ ⟨e₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  rw [z, Nat.mul_zero, Nat.add_zero] at e₁
  obtain hXl : xorW s.mem base (x + 8 * i) U < 2 ^ 64 := BitVec.isLt _
  obtain hYl : xorW s.mem base (y + 8 * i) (U + 8) < 2 ^ 64 := BitVec.isLt _
  obtain hmX : (s.gpr .rcx).toNat * xorW s.mem base (x + 8 * i) U ≤ 2 ^ 62 * (2 ^ 64 - 1) := Nat.mul_le_mul ha (by omega_using [hXl])
  obtain hmY : (s.gpr .rbp).toNat * xorW s.mem base (y + 8 * i) (U + 8) ≤ 2 ^ 62 * (2 ^ 64 - 1) := Nat.mul_le_mul hb (by omega_using [hYl])
  have g₁ : ∀ r, r ∉ [Reg.rax, .rdx, .r8, .r13] → s₁.gpr r = s.gpr r := k₁.1
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  rw [WP.block_append_iff]
  refine WP.mono (linTerm_ok hs₁ (m := .rbp) (by decide) (x := y + 8 * i) (sl := U + 8) hy (by omega_using [hU]) (by
    rw [e₁, g₁ .rbp (by decide)]; omega_using [hb, hmX])) fun s₂ ⟨e₂, k₂⟩ => ?_
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (linOut_ok hs₂ hT) fun t ⟨mt, e8, e13, kt⟩ => ⟨?_, e13, ?_, ?_⟩
  · have hsum : (s₂.gpr .r8).toNat + 2 ^ 64 * (s₂.gpr .r13).toNat =
        (s.gpr .r8).toNat + (s.gpr .rcx).toNat * xorW s.mem base (x + 8 * i) U + (s.gpr .rbp).toNat * xorW s.mem base (y + 8 * i) (U + 8) := by
      rw [e₂, e₁, g₁ .rbp (by decide), hm₁]
    rw [mt, word_writeW_self, e8, hsum]
  · exact ((Keeps.regs k₁).trans (Keeps.regs k₂)).trans (kt.mono (by regions_sub))
  · rw [mt, k₂.2.1, hm₁]; exact writeW_outside _ _ _ (by omega_using [hT, hn])

/-- A column: `[T'] + 2^64 r8' = r8 + rcx X + rbp Y` for `X`, `Y` the
terms' words; `r13` stays zero. -/
theorem linColTop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {T U k : Nat} (hU : U + 16 ≤ size)
    (hT : (T + 8 * k) + 8 ≤ size) (h13 : s.gpr .r13 = 0) (ha : (s.gpr .rcx).toNat ≤ 2 ^ 62)
    (hb : (s.gpr .rbp).toNat ≤ 2 ^ 62) :
    WP isa (.block (linColTop T U k)) s fun t =>
      (word t.mem base (T + 8 * k)).toNat + 2 ^ 64 * (t.gpr .r8).toNat =
        (s.gpr .r8).toNat + (s.gpr .rcx).toNat * (word s.mem base U).toNat + (s.gpr .rbp).toNat * (word s.mem base (U + 8)).toNat ∧
      t.gpr .r13 = 0 ∧ KeepRegs [.rax, .rdx, .r8, .r13] s t ∧ Outside base (T + 8 * k) 8 s.mem t.mem := by
  have hn := hs.nowrap
  rw [linColTop, List.append_assoc, WP.block_append_iff]
  obtain hr8 := (s.gpr .r8).isLt
  obtain z : (s.gpr .r13).toNat = 0 := by rw [h13]; rfl
  refine WP.mono (linTermTop_ok hs (m := .rcx) (by decide) (sl := U) (by omega_using [hU]) (by
    rw [z]; omega_using [])) fun s₁ ⟨e₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  rw [z, Nat.mul_zero, Nat.add_zero] at e₁
  obtain hXl : (word s.mem base U).toNat < 2 ^ 64 := BitVec.isLt _
  obtain hYl : (word s.mem base (U + 8)).toNat < 2 ^ 64 := BitVec.isLt _
  obtain hmX : (s.gpr .rcx).toNat * (word s.mem base U).toNat ≤ 2 ^ 62 * (2 ^ 64 - 1) := Nat.mul_le_mul ha (by omega_using [])
  obtain hmY : (s.gpr .rbp).toNat * (word s.mem base (U + 8)).toNat ≤ 2 ^ 62 * (2 ^ 64 - 1) := Nat.mul_le_mul hb (by omega_using [])
  have g₁ : ∀ r, r ∉ [Reg.rax, .rdx, .r8, .r13] → s₁.gpr r = s.gpr r := k₁.1
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  rw [WP.block_append_iff]
  refine WP.mono (linTermTop_ok hs₁ (m := .rbp) (by decide) (sl := U + 8) (by omega_using [hU]) (by
    rw [e₁, g₁ .rbp (by decide)]; omega_using [hb, hmX])) fun s₂ ⟨e₂, k₂⟩ => ?_
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (linOut_ok hs₂ hT) fun t ⟨mt, e8, e13, kt⟩ => ⟨?_, e13, ?_, ?_⟩
  · have hsum : (s₂.gpr .r8).toNat + 2 ^ 64 * (s₂.gpr .r13).toNat =
        (s.gpr .r8).toNat + (s.gpr .rcx).toNat * (word s.mem base U).toNat + (s.gpr .rbp).toNat * (word s.mem base (U + 8)).toNat := by
      rw [e₂, e₁, g₁ .rbp (by decide), hm₁]
    rw [mt, word_writeW_self, e8, hsum]
  · exact ((Keeps.regs k₁).trans (Keeps.regs k₂)).trans (kt.mono (by regions_sub))
  · rw [mt, k₂.2.1, hm₁]; exact writeW_outside _ _ _ (by omega_using [hT, hn])

/-! ## The columns -/

/-- `[x …] ⊕ [sl]` over `i` words, as a number. -/
def xorSum (m : Mem) (base : Addr) (x sl : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => xorSum m base x sl i + 2 ^ (64 * i) * xorW m base (x + 8 * i) sl

/-- Columns `0 … i - 1`: `[T …] + 2^(64 i) r8' = r8 + rcx (X ⊕ M) + rbp (Y ⊕ M')`. -/
theorem linCols_ok {base : Addr} {size T x y U : Nat} (hU : U + 16 ≤ size) :
    ∀ (i : Nat) {s : State}, Scr s base size → x + 8 * i ≤ size → y + 8 * i ≤ size → T + 8 * i ≤ size →
      (T + 8 * i ≤ x ∨ x + 8 * i ≤ T) → (T + 8 * i ≤ y ∨ y + 8 * i ≤ T) → (T + 8 * i ≤ U ∨ U + 16 ≤ T) →
      s.gpr .r13 = 0 → (s.gpr .rcx).toNat ≤ 2 ^ 62 → (s.gpr .rbp).toNat ≤ 2 ^ 62 →
      WP isa (.block (linCols T x y U i)) s fun t =>
        wordsVal t.mem base T i + 2 ^ (64 * i) * (t.gpr .r8).toNat =
          (s.gpr .r8).toNat + (s.gpr .rcx).toNat * xorSum s.mem base x U i +
            (s.gpr .rbp).toNat * xorSum s.mem base y (U + 8) i ∧
        t.gpr .r13 = 0 ∧ KeepRegs [.rax, .rdx, .r8, .r13] s t ∧ Outside base T (8 * i) s.mem t.mem
  | 0, s, _, _, _, _, _, _, _, h13, _, _ => WP.block_nil ⟨by simp [wordsVal, xorSum], h13,
      ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | i + 1, s, hs, hx, hy, hT, hTx, hTy, hTU, h13, ha, hb => by
    have hn := hs.nowrap
    rw [linCols, WP.block_append_iff]
    refine WP.mono (linCols_ok hU i hs (by omega_using [hx]) (by omega_using [hy]) (by omega_using [hT]) (by omega_using [hTx]) (by omega_using [hTy]) (by omega_using [hTU])
      h13 ha hb) fun s₁ ⟨e₁, z₁, k₁, O₁⟩ => ?_
    obtain hs₁ := hs.of_keepRegs k₁ (by decide)
    obtain gc : s₁.gpr .rcx = s.gpr .rcx := k₁.gpr _ (by decide)
    obtain gb : s₁.gpr .rbp = s.gpr .rbp := k₁.gpr _ (by decide)
    refine WP.mono (linCol_ok hs₁ (T := T) (x := x) (y := y) (U := U) (i := i) (by omega_using [hx]) (by omega_using [hy]) hU
      (by omega_using [hT]) z₁ (by rw [gc]; exact ha) (by rw [gb]; exact hb)) fun t ⟨e₂, z₂, k₂, O₂⟩ =>
        ⟨?_, z₂, k₁.trans k₂, fun a ha' => by
          rw [O₂ a (by omega_using [ha']), O₁ a (by omega_using [ha'])]⟩
    obtain wx : xorW s₁.mem base (x + 8 * i) U = xorW s.mem base (x + 8 * i) U := by
      simp only [xorW]; rw [O₁.word (by omega_using [hTx]) (by omega_using [hx, hn]), O₁.word (by omega_using [hTU]) (by omega_using [hU, hn])]
    obtain wy : xorW s₁.mem base (y + 8 * i) (U + 8) = xorW s.mem base (y + 8 * i) (U + 8) := by
      simp only [xorW]; rw [O₁.word (by omega_using [hTy]) (by omega_using [hy, hn]), O₁.word (by omega_using [hTU]) (by omega_using [hU, hn])]
    obtain wT : wordsVal t.mem base T i = wordsVal s₁.mem base T i := O₂.wordsVal (by omega_using []) (by omega_using [hT, hn])
    rw [gc, gb, wx, wy] at e₂
    rw [wordsVal_succ_top, wT, pow64_succ]
    simp only [xorSum]
    generalize 2 ^ (64 * i) = P at *
    generalize (word t.mem base (T + 8 * i)).toNat = W at *
    generalize (s.gpr .rcx).toNat = A at *
    generalize (s.gpr .rbp).toNat = B at *
    grind

/-- With a zero mask, `X ⊕ M = X`. -/
theorem xorSum_zero {m : Mem} {base : Addr} {x sl : Nat} (h : word m base sl = 0) :
    ∀ k, xorSum m base x sl k = wordsVal m base x k
  | 0 => rfl
  | k + 1 => by
    rw [xorSum, xorSum_zero h k, wordsVal_succ_top, xorW, h]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.xor_zero]

/-- With an all-ones mask, `X ⊕ M = 2^(64 k) - 1 - X`. -/
theorem xorSum_ones {m : Mem} {base : Addr} {x sl : Nat} (h : word m base sl = BitVec.allOnes 64) :
    ∀ k, xorSum m base x sl k + wordsVal m base x k + 1 = 2 ^ (64 * k)
  | 0 => rfl
  | k + 1 => by
    obtain ih := xorSum_ones (x := x) h k
    obtain hw : xorW m base (x + 8 * k) sl + (word m base (x + 8 * k)).toNat = 2 ^ 64 - 1 := by
      rw [xorW, h, BitVec.xor_allOnes, BitVec.toNat_not]
      have := (word m base (x + 8 * k)).isLt; omega_using []
    rw [xorSum, wordsVal_succ_top, pow64_succ]
    generalize 2 ^ (64 * k) = P at *
    generalize xorW m base (x + 8 * k) sl = A at *
    generalize (word m base (x + 8 * k)).toNat = B at *
    have : P * A + P * B = P * (2 ^ 64 - 1) := by rw [← Nat.mul_add, hw]
    rw [Nat.mul_sub, Nat.mul_one] at this
    obtain hP : P ≤ P * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
    omega_using [ih, this]

/-- One side of the sum: `(|w| & M) + |w| (X ⊕ M) ≡ w X` modulo `Q`, for
`X ⊕ M = X` with `M = 0` and `Q - 1 - X` with `M` all ones. -/
theorem side_cong {w : BitVec 64} {X S Q : Nat} (h0 : smask w = 0 → S = X)
    (h1 : smask w = BitVec.allOnes 64 → S + X + 1 = Q) :
    ∃ j : Int, ((masked (smask w) (absW w).toNat + (absW w).toNat * S : Nat) : Int) =
      w.toInt * X + j * Q := by
  obtain ht := Divstep.toInt_sgn w
  obtain hv := smask_toNat w
  obtain ha := absW_toNat w
  unfold sgnW at hv
  have hw := w.isLt
  by_cases h : 2 ^ 63 ≤ w.toNat
  · have e : smask w = BitVec.allOnes 64 :=
      BitVec.eq_of_toNat_eq (by rw [hv, BitVec.toNat_allOnes, ite_eq_left_of_eq_true _ _ (eq_true h)])
    obtain hS := h1 e
    simp only [h, ↓reduceIte] at ht
    refine ⟨(absW w).toNat, ?_⟩
    simp only [masked, e, ↓reduceIte]
    obtain hA : ((absW w).toNat : Int) = -w.toInt := by rw [ha]; omega_using [ht]
    obtain hS' : (S : Int) = Q - 1 - X := by omega_using [hS]
    push_cast
    rw [hS', hA]
    grind
  · have e : smask w = 0 := BitVec.eq_of_toNat_eq (by rw [hv, ite_eq_right_of_eq_false _ _ (eq_false h)]; rfl)
    obtain hS := h0 e
    simp only [h, ↓reduceIte] at ht
    refine ⟨0, ?_⟩
    simp only [masked, e, show (0 : BitVec 64) ≠ BitVec.allOnes 64 by decide, ↓reduceIte]
    obtain hA : ((absW w).toNat : Int) = w.toInt := by rw [ha]; omega_using [ht]
    push_cast
    rw [hS, hA]
    grind

/-! ## The combination -/

/-- `[T] = w [x] + w' [y]` modulo `2^(64 K)` (`k ≤ K ≤ k + 1`), for `|w|`, `|w'| ≤ 2^62`. -/
theorem linR_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w w' : Reg}
    (hw : w ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13]) (hw' : w' ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13])
    {T x y U k K : Nat} (hkK : k ≤ K) (hK : 3 ≤ K) (hk' : K ≤ k + 1)
    (hx : x + 8 * k ≤ size) (hy : y + 8 * k ≤ size) (hT : T + 8 * K ≤ size) (hU : U + 8 * (K - 1) ≤ size)
    (hTx : T + 8 * K ≤ x ∨ x + 8 * k ≤ T) (hTy : T + 8 * K ≤ y ∨ y + 8 * k ≤ T)
    (hUT : U + 8 * (K - 1) ≤ T ∨ T + 8 * K ≤ U) (hUx : U + 8 * (K - 1) ≤ x ∨ x + 8 * k ≤ U)
    (hUy : U + 8 * (K - 1) ≤ y ∨ y + 8 * k ≤ U)
    (hu : (s.gpr w).toInt.natAbs ≤ 2 ^ 62) (hv : (s.gpr w').toInt.natAbs ≤ 2 ^ 62) :
    WP isa (.block (linR w w' T x y U k K)) s fun t =>
      (wordsVal t.mem base T K : Int) % ((2 ^ (64 * K) : Nat) : Int) =
        ((s.gpr w).toInt * wordsVal s.mem base x k + (s.gpr w').toInt * wordsVal s.mem base y k) %
          ((2 ^ (64 * K) : Nat) : Int) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s t ∧ Unch base [(T, 8 * K), (U, 8 * (K - 1))] s.mem t.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw hw'
  rw [linR, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  -- `rcx = |w|`, `[U]` its mask.
  refine WP.mono (absMask_ok hs (w := w) (a := .rcx) (by simp [hw.1, hw.2.2.1]) (by decide)
    (fun h => hw.2.1 h.symm) (sl := U) (by inv_lin_omega)) fun s₁ ⟨a₁, m₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  obtain gw' : s₁.gpr w' = s.gpr w' := k₁.gpr _ (by simp [hw'.1, hw'.2.1, hw'.2.2.1])
  rw [WP.block_append_iff]
  -- `rbp = |w'|`, `[U + 8]` its mask.
  refine WP.mono (absMask_ok hs₁ (w := w') (a := .rbp) (by simp [hw'.1, hw'.2.2.1]) (by decide)
    (fun h => hw'.2.2.2.1 h.symm) (sl := U + 8) (by inv_lin_omega)) fun s₂ ⟨a₂, m₂, k₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [gw'] at a₂ m₂
  obtain c₂ : s₂.gpr .rcx = absW (s.gpr w) := by rw [k₂.gpr _ (by decide), a₁]
  obtain O₁ : Outside base U 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by inv_lin_omega)
  obtain O₂ : Outside base (U + 8) 8 s₁.mem s₂.mem := by rw [m₂]; exact writeW_outside _ _ _ (by inv_lin_omega)
  obtain U₂ : Unch base [(U, 16)] s.mem s₂.mem := fun a ha => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at ha
    rw [O₂ a (by omega_using [ha]), O₁ a (by omega_using [ha])]
  obtain wU : word s₂.mem base U = smask (s.gpr w) := by
    rw [O₂.word (by inv_lin_omega) (by inv_lin_omega), m₁, word_writeW_self]
  obtain wU8 : word s₂.mem base (U + 8) = smask (s.gpr w') := by rw [m₂, word_writeW_self]
  obtain bA : (absW (s.gpr w)).toNat ≤ 2 ^ 62 := by rw [absW_toNat]; exact hu
  obtain bB : (absW (s.gpr w')).toNat ≤ 2 ^ 62 := by rw [absW_toNat]; exact hv
  rw [WP.block_append_iff]
  -- The accumulator's start.
  refine WP.mono (linInit_ok hs₂ (U := U) (by inv_lin_omega) (by rw [wU]; exact smask_isMask _)
    (by rw [wU8]; exact smask_isMask _) (by rw [c₂]; exact bA) (by rw [a₂]; exact bB))
    fun s₃ ⟨e₃, z₃, k₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  obtain c₃ : s₃.gpr .rcx = absW (s.gpr w) := by rw [k₃.1 _ (by decide), c₂]
  obtain b₃ : s₃.gpr .rbp = absW (s.gpr w') := by rw [k₃.1 _ (by decide), a₂]
  have hm₃ : s₃.mem = s₂.mem := k₃.2.1
  rw [c₂, a₂, wU, wU8] at e₃
  rw [WP.block_append_iff]
  -- The columns of the numbers' words.
  refine WP.mono (linCols_ok (T := T) (x := x) (y := y) (U := U) (by inv_lin_omega) k hs₃ hx hy (by inv_lin_omega)
    (by inv_lin_omega) (by inv_lin_omega) (by inv_lin_omega) z₃ (by rw [c₃]; exact bA) (by rw [b₃]; exact bB))
    fun s₄ ⟨e₄, z₄, k₄, O₄⟩ => ?_
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  rw [c₃, b₃, hm₃, e₃] at e₄
  -- `X ⊕ M` as `X` or `2^(64 k) - 1 - X`.
  obtain eX : wordsVal s₂.mem base x k = wordsVal s.mem base x k := U₂.wordsVal (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; inv_lin_omega) (by inv_lin_omega)
  obtain eY : wordsVal s₂.mem base y k = wordsVal s.mem base y k := U₂.wordsVal (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; inv_lin_omega) (by inv_lin_omega)
  obtain zx := fun h => (xorSum_zero (m := s₂.mem) (base := base) (x := x) (sl := U) (wU.trans h) k).trans eX
  obtain zy := fun h => (xorSum_zero (m := s₂.mem) (base := base) (x := y) (sl := U + 8) (wU8.trans h) k).trans eY
  obtain ox := fun h => eX ▸ xorSum_ones (m := s₂.mem) (base := base) (x := x) (sl := U) (wU.trans h) k
  obtain oy := fun h => eY ▸ xorSum_ones (m := s₂.mem) (base := base) (x := y) (sl := U + 8) (wU8.trans h) k
  obtain hall := (BitVec.allOnes 64 : BitVec 64).isLt
  have hallv : (BitVec.allOnes 64 : BitVec 64).toNat = 2 ^ 64 - 1 := BitVec.toNat_allOnes
  -- The result, from the sum and the carry out `R`.
  obtain fin : ∀ {t : State} {R : Nat} (Sx Sy : Nat),
      wordsVal t.mem base T K + 2 ^ (64 * K) * R =
        masked (smask (s.gpr w)) (absW (s.gpr w)).toNat + masked (smask (s.gpr w')) (absW (s.gpr w')).toNat +
          (absW (s.gpr w)).toNat * Sx + (absW (s.gpr w')).toNat * Sy →
      (smask (s.gpr w) = 0 → Sx = wordsVal s.mem base x k) →
      (smask (s.gpr w) = BitVec.allOnes 64 → Sx + wordsVal s.mem base x k + 1 = 2 ^ (64 * K)) →
      (smask (s.gpr w') = 0 → Sy = wordsVal s.mem base y k) →
      (smask (s.gpr w') = BitVec.allOnes 64 → Sy + wordsVal s.mem base y k + 1 = 2 ^ (64 * K)) →
      (wordsVal t.mem base T K : Int) % ((2 ^ (64 * K) : Nat) : Int) =
        ((s.gpr w).toInt * wordsVal s.mem base x k + (s.gpr w').toInt * wordsVal s.mem base y k) %
          ((2 ^ (64 * K) : Nat) : Int) := by
    intro t R Sx Sy hsum h0 h1 h0' h1'
    obtain ⟨j₁, e₁⟩ := side_cong h0 h1
    obtain ⟨j₂, e₂⟩ := side_cong h0' h1'
    obtain hI := congrArg (Nat.cast : Nat → Int) hsum
    push_cast at hI e₁ e₂
    have : (wordsVal t.mem base T K : Int) = (s.gpr w).toInt * wordsVal s.mem base x k +
        (s.gpr w').toInt * wordsVal s.mem base y k + (j₁ + j₂ - R) * ((2 ^ (64 * K) : Nat) : Int) := by
      push_cast; grind
    rw [this, Int.add_mul_emod_self_right]
  by_cases hk : k < K
  · -- The column past the numbers' words.
    obtain eK : K = k + 1 := by omega_using [hk', hk]
    simp only [hk, ↓reduceIte]
    refine WP.mono (linColTop_ok hs₄ (T := T) (U := U) (k := k) (by inv_lin_omega) (by omega_using [hT, eK]) z₄
      (by rw [k₄.gpr _ (by decide), c₃]; exact bA) (by rw [k₄.gpr _ (by decide), b₃]; exact bB))
      fun t ⟨e₅, _, k₅, O₅⟩ => ⟨?_, ?_, ?_⟩
    · have wU' : word s₄.mem base U = smask (s.gpr w) := by rw [O₄.word (by inv_lin_omega) (by inv_lin_omega), hm₃, wU]
      obtain wU8' : word s₄.mem base (U + 8) = smask (s.gpr w') := by
        rw [O₄.word (by inv_lin_omega) (by inv_lin_omega), hm₃, wU8]
      rw [k₄.gpr .rcx (by decide), k₄.gpr .rbp (by decide), c₃, b₃, wU', wU8'] at e₅
      obtain wT : wordsVal t.mem base T k = wordsVal s₄.mem base T k := O₅.wordsVal (by inv_lin_omega) (by inv_lin_omega)
      refine fin (R := (t.gpr .r8).toNat)
        (xorSum s₂.mem base x U k + 2 ^ (64 * k) * (smask (s.gpr w)).toNat)
        (xorSum s₂.mem base y (U + 8) k + 2 ^ (64 * k) * (smask (s.gpr w')).toNat) ?_ ?_ ?_ ?_ ?_
      · rw [eK, wordsVal_succ_top, wT, pow64_succ]
        generalize 2 ^ (64 * k) = P at *
        grind
      · intro h; rw [h, zx h]; simp
      · intro h; rw [h, hallv, eK, pow64_succ]; have := ox h
        generalize 2 ^ (64 * k) = P at *
        rw [Nat.mul_sub, Nat.mul_one]
        obtain hP : P ≤ P * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
        omega_using [this]
      · intro h; rw [h, zy h]; simp
      · intro h; rw [h, hallv, eK, pow64_succ]; have := oy h
        generalize 2 ^ (64 * k) = P at *
        rw [Nat.mul_sub, Nat.mul_one]
        obtain hP : P ≤ P * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
        omega_using [this]
    · exact (((k₁.mono (by regions_sub)).trans (k₂.mono (by regions_sub))).trans
        ((Keeps.regs k₃).mono (by regions_sub))).trans ((k₄.trans k₅).mono (by regions_sub))
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at ha
      rw [O₅ a (by omega_using [ha, eK]), O₄ a (by omega_using [ha, eK]), hm₃, U₂ a (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega_using [ha, hK])]
  · have eK : K = k := by omega_using [hkK, hk]
    simp only [hk, ↓reduceIte]
    refine WP.block_nil ⟨?_, ?_, ?_⟩
    · subst eK
      exact fin (R := (s₄.gpr .r8).toNat) (xorSum s₂.mem base x U K) (xorSum s₂.mem base y (U + 8) K)
        (by rw [e₄]) zx ox zy oy
    · exact (((k₁.mono (by regions_sub)).trans (k₂.mono (by regions_sub))).trans
        ((Keeps.regs k₃).mono (by regions_sub))).trans (k₄.mono (by regions_sub))
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at ha
      rw [O₄ a (by omega_using [ha, eK, hkK]), hm₃, U₂ a (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega_using [ha, hK])]

end VG.Proof.Weierstrass.X86_64

end

end

/-!
# Inversion by divsteps on x86-64: the reduction of the coefficients

The reduction `mredS` of a signed number of `n + 1` words to `Divstep.mredRaw`
(`mredS_ok`): `k = t₀ m`, `[t]` sign-extended and plus `k p`, then its words
`1 … n + 1`; and the normalization `normC` of a signed number of `n + 1` words
in `(-p, 2p)` to `Divstep.norm` (`normC_ok`), by carry chains with `p` under masks.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono add_carry adc_carry sub_borrow sbb_borrow)

theorem sext0 : (0 : BitVec 32).signExtend 64 = 0 := by decide

/-- `rcx = t₀ m mod 2^64`. -/
theorem kOf_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (M : Mod) {t : Nat}
    (ht : t + 8 ≤ size) :
    WP isa (.block (kOf M t)) s fun u =>
      (u.gpr .rcx).toNat = (word s.mem base t).toNat * M.minv.toNat % 2 ^ 64 ∧
      Keeps [.rax, .rcx, .rdx] s u := by
  rw [kOf, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .rax ht) fun s₁ ⟨l₁, _, k₁⟩ => ?_
  obtain h : WP isa (.block [.movImm64 .rcx M.minv, .mul .rcx, .mov .rcx (.reg .rax)]) s₁ fun u =>
      u.gpr .rcx = BitVec.ofNat 64 ((s₁.gpr .rax).toNat * M.minv.toNat) ∧ Keeps [.rax, .rcx, .rdx] s₁ u := by
    irun [RegUpd.gpr_setReg_self]
    refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  refine WP.mono h fun u ⟨c, k⟩ => ⟨?_, (k₁.mono (by decide)).trans k⟩
  rw [c, BitVec.toNat_ofNat, l₁]

/-- Word `n + 1` of `[t]`: word `n`'s sign. -/
theorem sextTop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (M : Mod) {t : Nat}
    (ht : t + 8 * (M.n + 2) ≤ size) :
    WP isa (.block (sextTop M t)) s fun u =>
      wordsVal u.mem base t (M.n + 2) =
        wordsVal s.mem base t (M.n + 1) + 2 ^ (64 * (M.n + 1)) * sgnW (word s.mem base (t + 8 * M.n)) ∧
      KeepRegs [.rax, .rdx, .r8] s u ∧ Outside base (t + 8 * (M.n + 1)) 8 s.mem u.mem := by
  have hn := hs.nowrap
  rw [sextTop, List.append_assoc, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .rdx (d := t + 8 * M.n) (by omega_using [ht])) fun s₁ ⟨l₁, _, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (maskOf_ok s₁ (d := .r8) (src := .rdx) (by decide)) fun s₂ ⟨g₂, k₂⟩ => ?_
  obtain hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  refine WP.mono (storeReg_ok hs₂ .r8 (d := t + 8 * (M.n + 1)) (by omega_using [ht])) fun u ⟨mu, _, _, ku⟩ => ?_
  obtain hm₂ : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  obtain O := writeW_outside s₂.mem base (d := t + 8 * (M.n + 1)) (s₂.gpr .r8) (by omega_using [ht, hn])
  refine ⟨?_, (((Keeps.regs k₁).mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
    (ku.mono (by decide)), by rw [mu, ← hm₂]; exact O⟩
  rw [show M.n + 2 = M.n + 1 + 1 from rfl, mu, wordsVal_succ_top, word_writeW_self,
    O.wordsVal (by omega_using []) (by omega_using [ht, hn]), hm₂, g₂, smask_toNat, l₁]

/-- `[d] += rbp` (two words), modulo `2^128`. -/
theorem carry2_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat} (hd : d + 16 ≤ size) :
    WP isa (.block (carry2 d)) s fun u =>
      wordsVal u.mem base d 2 = (wordsVal s.mem base d 2 + (s.gpr .rbp).toNat) % 2 ^ 128 ∧
      KeepRegs [.r8] s u ∧ Outside base d 16 s.mem u.mem := by
  have hn := hs.nowrap
  rw [carry2, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .r8 (d := d) (by omega_using [hd])) fun s₁ ⟨l₁, _, k₁⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  obtain ha : WP isa (.block [.alu .add .r8 (.reg .rbp)]) s₁ fun v =>
      v.gpr .r8 = s₁.gpr .r8 + s₁.gpr .rbp ∧
        v.cf = some (decide (2 ^ 64 ≤ (s₁.gpr .r8).toNat + (s₁.gpr .rbp).toNat)) ∧ Keeps [.r8] s₁ v := by
    irun
    exact ⟨rfl, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono ha fun s₂ ⟨a₂, c₂, k₂⟩ => ?_
  obtain hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (storeReg_ok hs₂ .r8 (d := d) (by omega_using [hd])) fun s₃ ⟨m₃, g₃, f₃, k₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movMem_ok hs₃ .r8 (d := d + 8) (by omega_using [hd])) fun s₄ ⟨l₄, f₄, k₄⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  obtain hc : WP isa (.block [.alu .adc .r8 (.imm 0)]) s₄ fun v =>
      v.gpr .r8 = s₄.gpr .r8 + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ (s₁.gpr .r8).toNat + (s₁.gpr .rbp).toNat))).setWidth 64 ∧
        Keeps [.r8] s₄ v := by
    irun [f₄, f₃, c₂, sext0]
    exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono hc fun s₅ ⟨a₅, k₅⟩ => ?_
  obtain hs₅ := (hs₃.of_keeps k₄ (by decide)).of_keeps k₅ (by decide)
  refine WP.mono (storeReg_ok hs₅ .r8 (d := d + 8) (by omega_using [hd])) fun u ⟨mu, _, _, ku⟩ => ?_
  obtain O₃ := writeW_outside s₂.mem base (d := d) (s₂.gpr .r8) (by omega_using [hd, hn])
  obtain O₅ := writeW_outside s₅.mem base (d := d + 8) (s₅.gpr .r8) (by omega_using [hd, hn])
  obtain hm₂ : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  obtain hm₅ : s₅.mem = s₃.mem := by rw [k₅.2.1, k₄.2.1]
  refine ⟨?_, ((((Keeps.regs k₁).trans (Keeps.regs k₂)).trans (k₃.mono (by decide))).trans (((Keeps.regs k₄).trans
    (Keeps.regs k₅)).trans (ku.mono (by decide)))).mono (by decide), fun x hx => ?_⟩
  · have w0 : word u.mem base d = s₂.gpr .r8 := by
      rw [mu, O₅.word (by omega_using []) (by omega_using [hd, hn]), hm₅, m₃, word_writeW_self]
    obtain w1 : word u.mem base (d + 8) = s₅.gpr .r8 := by rw [mu, word_writeW_self]
    obtain e₄ : s₄.gpr .r8 = word s.mem base (d + 8) := by
      rw [l₄, m₃, O₃.word (by omega_using []) (by omega_using [hd, hn]), hm₂]
    obtain hrbp : s₁.gpr .rbp = s.gpr .rbp := k₁.1 .rbp (by decide)
    obtain h1 := add_carry (s₁.gpr .r8) (s₁.gpr .rbp)
    simp only [wordsVal, Nat.add_zero, Nat.mul_zero]
    rw [w0, w1, a₂, a₅, e₄, l₁, hrbp]
    rw [l₁, hrbp] at h1
    have := (word s.mem base d + s.gpr .rbp).isLt
    generalize decide (2 ^ 64 ≤ (word s.mem base d).toNat + (s.gpr .rbp).toNat) = c at *
    obtain h2 := adc_carry (word s.mem base (d + 8)) 0 c
    generalize decide (2 ^ 64 ≤ (word s.mem base (d + 8)).toNat + (0 : BitVec 64).toNat + c.toNat) = c' at h2
    rw [show (0 : BitVec 64).toNat = 0 from rfl] at h2
    have := (word s.mem base (d + 8) + 0 + (BitVec.ofBool c).setWidth 64).isLt
    have := Bool.toNat_le c
    have := Bool.toNat_le c'
    omega_using [h1, h2]
  · rw [mu, O₅ x (by omega_using [hx]), hm₅, m₃, O₃ x (by omega_using [hx]), hm₂]

theorem zext0' : (0 : BitVec 32).setWidth 64 = 0 := by decide
theorem sextm1 : (-1 : BitVec 32).signExtend 64 = BitVec.allOnes 64 := by decide

/-- `[U + 8 n] = 0`. -/
theorem zeroTop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {U n : Nat}
    (hU : U + 8 * n + 8 ≤ size) :
    WP isa (.block (zeroTop U n)) s fun u =>
      word u.mem base (U + 8 * n) = 0 ∧ KeepRegs [.r8] s u ∧ Outside base (U + 8 * n) 8 s.mem u.mem := by
  have hn := hs.nowrap
  rw [zeroTop, ← List.singleton_append, WP.block_append_iff]
  obtain h : WP isa (.block [.mov32 .r8 (.imm 0)]) s fun v => v.gpr .r8 = 0 ∧ Keeps [.r8] s v := by
    irun [zext0']
    exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono h fun s₁ ⟨g₁, k₁⟩ => ?_
  refine WP.mono (storeReg_ok (hs.of_keeps k₁ (by decide)) .r8 (d := U + 8 * n) (by omega_using [hU]))
    fun u ⟨mu, _, _, ku⟩ => ⟨by rw [mu, word_writeW_self, g₁], (Keeps.regs k₁).trans (ku.mono (by decide)),
      by rw [mu, ← k₁.2.1]; exact writeW_outside _ _ _ (by omega_using [hU, hn])⟩

theorem masked_allOnes (v : Nat) : masked (BitVec.allOnes 64) v = v := by simp [masked]

/-- A number of words and its carry out. -/
theorem mod_of_carry {X Y M c : Nat} (h : X + M * c = Y) (hX : X < M) : X = Y % M := by
  rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hX]

/-- `2^(64 (n + 1)) = A B` with `A = 2^(64 n)` and `B = 2^64`. -/
theorem pow64_succ' (n : Nat) : 2 ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by
  rw [pow64_succ, Nat.mul_comm]

/-- `[t + 8] += p` (`n + 1` words, modulo `2^(64 (n + 1))`) if it is negative. -/
theorem addIfNeg_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (M : Mod) {t U : Nat}
    (ht : t + 8 * (M.n + 2) ≤ size) (hU : U + 8 * (M.n + 1) ≤ size) (hmo : M.mo + 8 * M.n ≤ size)
    (htU : t + 8 * (M.n + 2) ≤ U ∨ U + 8 * (M.n + 1) ≤ t)
    (hUm : U + 8 * (M.n + 1) ≤ M.mo ∨ M.mo + 8 * M.n ≤ U)
    (htm : t + 8 * (M.n + 2) ≤ M.mo ∨ M.mo + 8 * M.n ≤ t)
    (hU0 : word s.mem base (U + 8 * M.n) = 0) :
    WP isa (.block (addIfNeg M t U)) s fun u =>
      wordsVal u.mem base (t + 8) (M.n + 1) =
        (wordsVal s.mem base (t + 8) (M.n + 1) +
          if 2 ^ (64 * M.n) * 2 ^ 63 ≤ wordsVal s.mem base (t + 8) (M.n + 1) then wordsVal s.mem base M.mo M.n
          else 0) % (2 ^ (64 * M.n) * 2 ^ 64) ∧
      KeepRegs [.rax, .rdx, .r8, .r13] s u ∧ Unch base [(t + 8, 8 * (M.n + 1)), (U, 8 * M.n)] s.mem u.mem := by
  have hn := hs.nowrap
  rw [addIfNeg, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .rdx (d := t + 8 * (M.n + 1)) (by omega_arith)) fun s₁ ⟨l₁, _, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (maskOf_ok s₁ (d := .r13) (src := .rdx) (by decide)) fun s₂ ⟨g₂, k₂⟩ => ?_
  obtain hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  obtain hm₂ : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  rw [WP.block_append_iff]
  refine WP.mono (maskCopy_ok (m := .r13) (by decide) M.n hs₂ (dst := U) (src := M.mo)
    (by rw [g₂]; exact smask_isMask _) (by omega_arith) hmo (by omega_arith)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  refine WP.mono (chainWAdd_ok (M.n + 1) hs₃ (op := .add) (c := false) (t := t + 8) (a := t + 8) (b := U)
    (.inl ⟨rfl, rfl⟩) (.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith) (.inl rfl) (by unfold Near; omega_arith))
    fun u ⟨c, _, e, ku, Ou⟩ => ⟨?_, (((Keeps.regs k₁).mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
      ((k₃.mono (by decide)).trans (ku.mono (by decide))), ?_⟩
  · have hR : wordsVal s₃.mem base (t + 8) (M.n + 1) = wordsVal s.mem base (t + 8) (M.n + 1) := by
      rw [O₃.wordsVal (by omega_arith) (by omega_arith), hm₂]
    obtain hUv : wordsVal s₃.mem base U (M.n + 1) =
        if 2 ^ (64 * M.n) * 2 ^ 63 ≤ wordsVal s.mem base (t + 8) (M.n + 1) then wordsVal s.mem base M.mo M.n
        else 0 := by
      rw [wordsVal_succ_top, e₃, O₃.word (by omega_arith) (by omega_arith), hm₂, hU0, g₂, masked_smask, l₁,
        show t + 8 * (M.n + 1) = t + 8 + 8 * M.n by omega_arith, show (0 : BitVec 64).toNat = 0 from rfl,
        Nat.mul_zero, Nat.add_zero]
      by_cases h : 2 ^ (64 * M.n) * 2 ^ 63 ≤ wordsVal s.mem base (t + 8) (M.n + 1)
      · have h' := (sgn_iff s.mem base (t + 8) M.n).mpr h
        simp only [h, h', ↓reduceIte]
      · have h' := mt (sgn_iff s.mem base (t + 8) M.n).mp h
        simp only [h, h', ↓reduceIte]
    simp only [Bool.toNat_false, Nat.add_zero] at e
    rw [hR, hUv, pow64_succ'] at e
    obtain hlt : wordsVal u.mem base (t + 8) (M.n + 1) < 2 ^ (64 * M.n) * 2 ^ 64 := by
      rw [← pow64_succ']; exact wordsVal_lt _ _ _ _
    exact mod_of_carry e hlt
  · rw [← hm₂]
    refine (O₃.unch.trans Ou.unch).mono fun v hv => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
    rcases hv with h | h <;> simp [h]

/-- `[t + 8] -= p` (`n + 1` words, modulo `2^(64 (n + 1))`). -/
theorem subP_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (M : Mod) {t U : Nat}
    (ht : t + 8 * (M.n + 2) ≤ size) (hU : U + 8 * (M.n + 1) ≤ size) (hmo : M.mo + 8 * M.n ≤ size)
    (htU : t + 8 * (M.n + 2) ≤ U ∨ U + 8 * (M.n + 1) ≤ t)
    (hUm : U + 8 * (M.n + 1) ≤ M.mo ∨ M.mo + 8 * M.n ≤ U)
    (hU0 : word s.mem base (U + 8 * M.n) = 0) :
    WP isa (.block (subP M t U)) s fun u =>
      (wordsVal u.mem base (t + 8) (M.n + 1) + wordsVal s.mem base M.mo M.n) % (2 ^ (64 * M.n) * 2 ^ 64) =
        wordsVal s.mem base (t + 8) (M.n + 1) ∧
      KeepRegs [.r8, .r13] s u ∧ Unch base [(t + 8, 8 * (M.n + 1)), (U, 8 * M.n)] s.mem u.mem := by
  have hn := hs.nowrap
  rw [subP, List.append_assoc, WP.block_append_iff]
  obtain h : WP isa (.block [.mov .r13 (.imm (-1))]) s fun v => v.gpr .r13 = BitVec.allOnes 64 ∧ Keeps [.r13] s v := by
    irun [sextm1]
    exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono h fun s₁ ⟨g₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (maskCopy_ok (m := .r13) (by decide) M.n hs₁ (dst := U) (src := M.mo)
    (by rw [g₁]; exact Or.inr rfl) (by omega_using [hU]) hmo (by omega_using [hUm])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (chainWSub_ok (M.n + 1) hs₂ (op := .sub) (c := false) (t := t + 8) (a := t + 8) (b := U)
    (.inl ⟨rfl, rfl⟩) (.inl (by omega_using [])) (by omega_using [ht]) (by omega_using [ht]) (by omega_using [hU]) (.inl rfl) (by unfold Near; omega_using [htU]))
    fun u ⟨c, _, e, ku, Ou⟩ => ⟨?_, ((Keeps.regs k₁).mono (by decide)).trans
      ((k₂.mono (by decide)).trans (ku.mono (by decide))), ?_⟩
  · have hR : wordsVal s₂.mem base (t + 8) (M.n + 1) = wordsVal s.mem base (t + 8) (M.n + 1) := by
      rw [O₂.wordsVal (by omega_using [htU]) (by omega_using [ht, hn]), k₁.2.1]
    obtain hUv : wordsVal s₂.mem base U (M.n + 1) = wordsVal s.mem base M.mo M.n := by
      rw [wordsVal_succ_top, e₂, O₂.word (by omega_using []) (by omega_using [hU, hn]), k₁.2.1, hU0, g₁, masked_allOnes,
        show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    simp only [Bool.toNat_false, Nat.add_zero] at e
    rw [hR, hUv, pow64_succ'] at e
    obtain hlt : wordsVal s.mem base (t + 8) (M.n + 1) < 2 ^ (64 * M.n) * 2 ^ 64 := by
      rw [← pow64_succ']; exact wordsVal_lt _ _ _ _
    exact (mod_of_carry e.symm hlt).symm
  · rw [← k₁.2.1]
    refine (O₂.unch.trans Ou.unch).mono fun v hv => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
    rcases hv with h | h <;> simp [h]

/-- A low part below `A` and a high part modulo `Q`. -/
theorem low_high_mod {L A y Q : Nat} (hL : L < A) (hQ : 0 < Q) : L + A * (y % Q) = (L + A * y) % (A * Q) := by
  obtain h1 : L + A * (y % Q) < A * Q := by
    obtain h2 : A * (y % Q + 1) ≤ A * Q := Nat.mul_le_mul_left A (Nat.mod_lt y hQ)
    rw [Nat.mul_succ] at h2
    omega_using [hL, h2]
  conv => rhs; rw [← Nat.mod_add_div y Q, Nat.mul_add, ← Nat.add_assoc, ← Nat.mul_assoc, Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt h1).symm

/-- Apart from each range of a list written out. -/
tactic_template "inv_apart_arith" : tactic => `(tactic| (simp only [List.mem_cons, List.not_mem_nil, or_false,
                   forall_eq_or_imp, forall_eq] <;> omega_arith))

/-- `[dst] = mredRaw p m T` (`n + 1` words, signed), for `[t]` (`n + 1` words) holding `T`,
`|T| ≤ 2^63 p`. -/
theorem mredS_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {p : Nat}
    (hM : ModOkW M size p s.mem base) {dst t : Nat}
    (ht : t + 8 * (M.n + 2) ≤ size) (hd : dst + 8 * (M.n + 1) ≤ size)
    (htm : t + 8 * (M.n + 2) ≤ M.mo ∨ M.mo + 8 * M.n ≤ t)
    (hdt : dst + 8 * (M.n + 1) ≤ t ∨ t + 8 * (M.n + 2) ≤ dst)
    {T : Int} (hT : |T| ≤ 2 ^ 63 * p)
    (hW : (wordsVal s.mem base t (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
      T % ((2 ^ (64 * (M.n + 1)) : Nat) : Int)) :
    WP isa (.block (mredS M dst t)) s fun u =>
      (wordsVal u.mem base dst (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
        Divstep.mredRaw p M.minv.toNat T % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s u ∧
      Unch base [(t, 8 * (M.n + 2)), (dst, 8 * (M.n + 1))] s.mem u.mem := by
  have hn := hs.nowrap
  have hP : wordsVal s.mem base M.mo M.n = p := hM.val
  have hmo := hM.mo
  simp only [mredS, List.append_assoc]
  -- `rcx = k`.
  rw [WP.block_append_iff]
  refine WP.mono (kOf_ok hs M (t := t) (by omega_using [ht])) fun s₁ ⟨x₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  -- `[t]` sign-extended.
  rw [WP.block_append_iff]
  refine WP.mono (sextTop_ok hs₁ M ht) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  -- `[t] += k p`.
  rw [WP.block_append_iff]
  refine WP.mono (memRow_ok hs₂ (k := M.n) (t := t) (d := M.mo) (by omega_using [ht]) hmo (by omega_using [htm])) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (carry2_ok hs₃ (d := t + 8 * M.n) (by omega_using [ht])) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  -- `[dst] = R`.
  refine WP.mono (copy_ok (M.n + 1) hs₄ (o := dst) (a := t + 8) hd (by omega_using [ht]) (by omega_using [hdt]))
    fun u ⟨eu, ku, Ou⟩ => ?_
  refine ⟨?_, (((((Keeps.regs k₁).mono (by decide)).trans (k₂.mono (by decide))).trans
    (k₃.mono (by decide))).trans (k₄.mono (by decide))).trans (ku.mono (by decide)), fun x hx => ?_⟩
  rotate_left
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    rw [Ou x (by omega_using [hx]), O₄ x (by omega_using [hx]), O₃ x (by omega_using [hx]), O₂ x (by omega_using [hx]),
      k₁.2.1]
  -- The arithmetic.
  obtain hp0 : 0 < p := by
    have := hM.inv
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h, Nat.zero_mul] at this; exact absurd this (by decide)
    · exact h
  obtain hpA : p < 2 ^ (64 * M.n) := hP ▸ wordsVal_lt _ _ _ _
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  obtain hrcx : s₂.gpr .rcx = s₁.gpr .rcx := k₂.gpr .rcx (by decide)
  obtain P₂ : wordsVal s₂.mem base M.mo M.n = p := by rw [O₂.wordsVal (by omega_using [htm]) (by omega_using [hn, hmo]), hm₁, hP]
  rw [hrcx, P₂] at e₃
  rw [hm₁, pow64_succ', sgnW_top] at e₂
  obtain eL : wordsVal s₄.mem base t M.n = wordsVal s₃.mem base t M.n := O₄.wordsVal (by omega_using []) (by omega_using [ht, hn])
  obtain eH : wordsVal s₃.mem base (t + 8 * M.n) 2 = wordsVal s₂.mem base (t + 8 * M.n) 2 :=
    O₃.wordsVal (by omega_using []) (by omega_using [ht, hn])
  obtain sp₂ := wordsVal_split s₂.mem base t M.n 2
  obtain sp₄ := wordsVal_split s₄.mem base t M.n 2
  rw [e₄, eH, eL] at sp₄
  obtain hL₃ := wordsVal_lt s₃.mem base t M.n
  obtain hE : wordsVal s₄.mem base t (M.n + 2) =
      (wordsVal s.mem base t (M.n + 1) + 2 ^ (64 * M.n) * 2 ^ 64 *
        (if 2 ^ (64 * M.n) * 2 ^ 63 ≤ wordsVal s.mem base t (M.n + 1) then 2 ^ 64 - 1 else 0) +
        (s₁.gpr .rcx).toNat * p) % (2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64) := by
    rw [sp₄, low_high_mod hL₃ (by decide), Nat.mul_assoc (2 ^ (64 * M.n)) (2 ^ 64) (2 ^ 64),
      show (2 : Nat) ^ 64 * 2 ^ 64 = 2 ^ 128 by rw [← Nat.pow_add], ← e₂, sp₂]
    generalize (2 : Nat) ^ (64 * M.n) * 2 ^ 128 = Q
    generalize (s₃.gpr .rbp).toNat = r at *
    generalize (s₁.gpr .rcx).toNat * p = kp at *
    generalize (2 : Nat) ^ (64 * M.n) = A at *
    rw [Nat.mul_add, show wordsVal s₃.mem base t M.n + (A * wordsVal s₂.mem base (t + 8 * M.n) 2 + A * r) =
      wordsVal s₂.mem base t M.n + A * wordsVal s₂.mem base (t + 8 * M.n) 2 + kp by omega_using [e₃]]
  have eR : wordsVal s₄.mem base t (M.n + 2) =
      (word s₄.mem base t).toNat + 2 ^ 64 * wordsVal s₄.mem base (t + 8) (M.n + 1) := rfl
  obtain hR : wordsVal s₄.mem base (t + 8) (M.n + 1) = wordsVal s₄.mem base t (M.n + 2) / 2 ^ 64 := by
    rw [eR, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (BitVec.isLt _), Nat.zero_add]
  obtain hk : (s₁.gpr .rcx).toNat = wordsVal s.mem base t (M.n + 1) % 2 ^ 64 * M.minv.toNat % 2 ^ 64 := by
    rw [x₁, wordsVal, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (BitVec.isLt _)]
  obtain hW1 : wordsVal s.mem base t (M.n + 1) < 2 ^ (64 * M.n) * 2 ^ 64 := by
    rw [← pow64_succ']; exact wordsVal_lt _ _ _ _
  obtain key := Divstep.mredRaw_nat (A := 2 ^ (64 * M.n)) (B := 2 ^ 64) (H := 2 ^ 63) (p := p) (m := M.minv.toNat)
    (t := T) (W := wordsVal s.mem base t (M.n + 1)) (k := (s₁.gpr .rcx).toNat)
    (E := wordsVal s₄.mem base t (M.n + 2)) (R := wordsVal s₄.mem base (t + 8) (M.n + 1))
    rfl rfl (Nat.two_pow_pos _) hp0 hpA hM.inv hT hW1 (by rw [← pow64_succ']; exact hW) hk hE hR
  rw [eu, pow64_succ']
  exact key

/-- `[t + 8]` (`n + 1` words) holding `r ∈ (-p, 2p)` brought to `norm p r` (its low `n` words). -/
theorem normC_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {p : Nat}
    (hM : ModOkW M size p s.mem base) {t U : Nat}
    (ht : t + 8 * (M.n + 2) ≤ size) (hU : U + 8 * (M.n + 1) ≤ size)
    (htm : t + 8 * (M.n + 2) ≤ M.mo ∨ M.mo + 8 * M.n ≤ t)
    (htU : t + 8 * (M.n + 2) ≤ U ∨ U + 8 * (M.n + 1) ≤ t) (hUm : U + 8 * (M.n + 1) ≤ M.mo ∨ M.mo + 8 * M.n ≤ U)
    {r : Int} (hr0 : -(p : Int) < r) (hr1 : r < 2 * p)
    (hR : (wordsVal s.mem base (t + 8) (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
      r % ((2 ^ (64 * (M.n + 1)) : Nat) : Int)) :
    WP isa (.block (normC M t U)) s fun u =>
      (wordsVal u.mem base (t + 8) M.n : Int) = Divstep.norm p r ∧
      KeepRegs [.rax, .rdx, .r8, .r13] s u ∧
      Unch base [(t + 8, 8 * (M.n + 1)), (U, 8 * (M.n + 1))] s.mem u.mem := by
  have hn := hs.nowrap
  have hP : wordsVal s.mem base M.mo M.n = p := hM.val
  have hmo := hM.mo
  simp only [normC, List.append_assoc]
  -- `[U + 8 n] = 0`.
  rw [WP.block_append_iff]
  refine WP.mono (zeroTop_ok hs (U := U) (n := M.n) (by omega_using [hU])) fun s₅ ⟨z₅, k₅, O₅⟩ => ?_
  obtain hs₅ := hs.of_keepRegs k₅ (by decide)
  obtain P₅ : wordsVal s₅.mem base M.mo M.n = p := by
    rw [O₅.wordsVal (by omega_using [hUm]) (by omega_using [hn, hmo]), hP]
  obtain R₅ : wordsVal s₅.mem base (t + 8) (M.n + 1) = wordsVal s.mem base (t + 8) (M.n + 1) :=
    O₅.wordsVal (by omega_using [htU]) (by omega_using [ht, hn])
  -- `R₁ = R + (p if negative)`.
  rw [WP.block_append_iff]
  refine WP.mono (addIfNeg_ok hs₅ M ht hU hmo htU hUm htm z₅) fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  obtain hs₆ := hs₅.of_keepRegs k₆ (by decide)
  obtain P₆ : wordsVal s₆.mem base M.mo M.n = p := by rw [O₆.wordsVal (by inv_apart_arith) (by omega_using [hn, hmo]), P₅]
  obtain z₆ : word s₆.mem base (U + 8 * M.n) = 0 := by rw [O₆.word (by inv_apart_arith) (by omega_using [hU, hn]), z₅]
  -- `R₂ = R₁ - p`.
  rw [WP.block_append_iff]
  refine WP.mono (subP_ok hs₆ M ht hU hmo htU hUm z₆) fun s₇ ⟨e₇, k₇, O₇⟩ => ?_
  obtain hs₇ := hs₆.of_keepRegs k₇ (by decide)
  obtain P₇ : wordsVal s₇.mem base M.mo M.n = p := by rw [O₇.wordsVal (by inv_apart_arith) (by omega_using [hn, hmo]), P₆]
  obtain z₇ : word s₇.mem base (U + 8 * M.n) = 0 := by rw [O₇.word (by inv_apart_arith) (by omega_using [hU, hn]), z₆]
  -- `R₃ = R₂ + (p if negative)`.
  refine WP.mono (addIfNeg_ok hs₇ M ht hU hmo htU hUm htm z₇) fun u ⟨e₈, k₈, O₈⟩ => ?_
  refine ⟨?_, ((k₅.mono (by decide)).trans (k₆.mono (by decide))).trans ((k₇.mono (by decide)).trans
    (k₈.mono (by decide))), fun x hx => ?_⟩
  rotate_left
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    rw [O₈ x (by inv_apart_arith), O₇ x (by inv_apart_arith), O₆ x (by inv_apart_arith), O₅ x (by omega_using [hx])]
  obtain hpA : p < 2 ^ (64 * M.n) := hP ▸ wordsVal_lt _ _ _ _
  rw [R₅, P₅] at e₆
  rw [P₆] at e₇
  rw [P₇] at e₈
  obtain hR₂1 : wordsVal s₇.mem base (t + 8) (M.n + 1) < 2 ^ (64 * M.n) * 2 ^ 64 := by
    rw [← pow64_succ']; exact wordsVal_lt _ _ _ _
  obtain hR1 : wordsVal s.mem base (t + 8) (M.n + 1) < 2 ^ (64 * M.n) * 2 ^ 64 := by
    rw [← pow64_succ']; exact wordsVal_lt _ _ _ _
  obtain key := Divstep.norm_nat (A := 2 ^ (64 * M.n)) (B := 2 ^ 64) (H := 2 ^ 63) (p := p) (r := r)
    (R := wordsVal s.mem base (t + 8) (M.n + 1)) (R₁ := wordsVal s₆.mem base (t + 8) (M.n + 1))
    (R₂ := wordsVal s₇.mem base (t + 8) (M.n + 1)) (R₃ := wordsVal u.mem base (t + 8) (M.n + 1))
    rfl rfl (Nat.two_pow_pos _) hpA hr0 hr1 hR1 (by rw [← pow64_succ']; exact hR) e₆ hR₂1 e₇ e₈
  obtain ⟨r0, r1⟩ := Divstep.norm_range hr0 hr1
  obtain hR₃ : wordsVal u.mem base (t + 8) (M.n + 1) < 2 ^ (64 * M.n) := by
    have : (wordsVal u.mem base (t + 8) (M.n + 1) : Int) < 2 ^ (64 * M.n) := by
      rw [key]; have : (p : Int) < 2 ^ (64 * M.n) := by exact_mod_cast hpA
      omega_arith
    exact_mod_cast this
  obtain hlow : wordsVal u.mem base (t + 8) M.n = wordsVal u.mem base (t + 8) (M.n + 1) := by
    obtain h := congrArg (· % 2 ^ (64 * M.n)) (wordsVal_succ_top u.mem base (t + 8) M.n)
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wordsVal_lt _ _ _ _), Nat.mod_eq_of_lt hR₃] at h
    exact h.symm
  rw [hlow, key]

end VG.Proof.Weierstrass.X86_64

end

end

/-!
# Inversion by divsteps on x86-64: a batch

The signed linear combinations of a batch as integers modulo the words'
range (`linR_ok`), the shift by 59 of a multiple of `2^59` (`shrM_ok`), and a
batch: `59` divsteps on the low words, then `f`, `g`, `a`, `b` updated by
their matrix, as `Divstep.batchS` (`batch_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- A coefficient of a batch's matrix is below `2^62` in magnitude. -/
theorem coef_natAbs {u : Int} (h : |u| ≤ 2 ^ 59) : (BitVec.ofInt 64 u).toInt.natAbs ≤ 2 ^ 62 := by
  rw [Divstep.toInt_small h]
  have := Int.natCast_natAbs u
  omega_using [h, this]

/-- `[dst] = y / 2^59` modulo `2^(64 L)`, for `[src] ≡ y` with `|y| < 2^(64 L - 1)`
a multiple of `2^59`. -/
theorem shrM_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {dst src L : Nat} (hL : 1 ≤ L)
    (hsrc : src + 8 * L ≤ size) (hdst : dst + 8 * L ≤ size) (hsep : dst + 8 * L ≤ src ∨ src + 8 * L ≤ dst) {y z : Int}
    (hy : (wordsVal s.mem base src L : Int) % ((2 ^ (64 * L) : Nat) : Int) = y % ((2 ^ (64 * L) : Nat) : Int))
    (hy1 : -((2 ^ (64 * (L - 1)) * 2 ^ 63 : Nat) : Int) ≤ y) (hy2 : y < ((2 ^ (64 * (L - 1)) * 2 ^ 63 : Nat) : Int))
    (hz : y = 2 ^ 59 * z) :
    WP isa (.block (shr59 dst src L)) s fun t =>
      (wordsVal t.mem base dst L : Int) % ((2 ^ (64 * L) : Nat) : Int) = z % ((2 ^ (64 * L) : Nat) : Int) ∧
      KeepRegs [.rax, .rdx, .r8] s t ∧ Outside base dst (8 * L) s.mem t.mem := by
  refine WP.mono (shr59_ok hs hL hsrc hdst hsep) fun t ⟨e, k, O⟩ => ⟨?_, k, O⟩
  obtain ⟨j, rfl⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega_using [hL]⟩
  simp only [Nat.add_sub_cancel] at hy1 hy2 ⊢
  obtain hQ : 2 ^ (64 * (j + 1)) = 2 * (2 ^ (64 * j) * 2 ^ 63) := by
    rw [pow64_succ, show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl]; ring
  rw [sext, Nat.add_sub_cancel, sgnW_top, hQ] at e
  rw [hQ] at hy ⊢
  exact Divstep.shr_nat (c := 2 ^ 59) (B := 2 ^ 64) rfl rfl (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
    (by have := wordsVal_lt s.mem base src (j + 1); rw [hQ] at this; exact this) hy hy1 hy2 hz e

theorem modOk_out {M : Mod} {size p : Nat} {mem mem' : Mem} {base : Addr} (hM : ModOkW M size p mem base)
    {W : List (Nat × Nat)} (hU : Unch base W mem mem') (hsep : ∀ w ∈ W, M.mo + 8 * M.n ≤ w.1 ∨ w.1 + w.2 ≤ M.mo)
    (hn : base.toNat + size ≤ 2 ^ 64) : ModOkW M size p mem' base :=
  ⟨hM.n0, hM.mo, hM.tmp, hM.sep, by rw [hU.wordsVal hsep (by have := hM.mo; omega_using [hn, this])]; exact hM.val,
    hM.inv, hM.red⟩

/-- Half a batch's update of `f`, `g`: `[dst] = (u f + v g) / 2^59` (`L` words, signed). -/
theorem fHalf_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w w' : Reg}
    (hw : w ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13]) (hw' : w' ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13])
    {u v : Int} (hu : s.gpr w = BitVec.ofInt 64 u) (hv : s.gpr w' = BitVec.ofInt 64 v) (huv : |u| + |v| ≤ 2 ^ 59)
    {T x y U dst L : Nat} (hL : 3 ≤ L) (hx : x + 8 * L ≤ size) (hy : y + 8 * L ≤ size) (hT : T + 8 * L ≤ size)
    (hU : U + 8 * (L - 1) ≤ size) (hd : dst + 8 * L ≤ size)
    (hTx : T + 8 * L ≤ x ∨ x + 8 * L ≤ T) (hTy : T + 8 * L ≤ y ∨ y + 8 * L ≤ T)
    (hUT : U + 8 * (L - 1) ≤ T ∨ T + 8 * L ≤ U) (hUx : U + 8 * (L - 1) ≤ x ∨ x + 8 * L ≤ U)
    (hUy : U + 8 * (L - 1) ≤ y ∨ y + 8 * L ≤ U) (hdT : dst + 8 * L ≤ T ∨ T + 8 * L ≤ dst) {p : Nat} {f g : Int}
    (hf : (wordsVal s.mem base x L : Int) % ((2 ^ (64 * L) : Nat) : Int) = f % ((2 ^ (64 * L) : Nat) : Int))
    (hg : (wordsVal s.mem base y L : Int) % ((2 ^ (64 * L) : Nat) : Int) = g % ((2 ^ (64 * L) : Nat) : Int))
    (hfb : |f| ≤ p) (hgb : |g| ≤ p) (hp : p < 2 ^ (64 * (L - 1))) (hdiv : 2 ^ 59 ∣ u * f + v * g) :
    WP isa (.block (linR w w' T x y U L L ++ shr59 dst T L)) s fun t =>
      (wordsVal t.mem base dst L : Int) % ((2 ^ (64 * L) : Nat) : Int) =
        ((u * f + v * g) / 2 ^ 59) % ((2 ^ (64 * L) : Nat) : Int) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s t ∧
      Unch base [(T, 8 * L), (U, 8 * (L - 1)), (dst, 8 * L)] s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (linR_ok hs hw hw' (k := L) (K := L) (Nat.le_refl _) hL (by omega_using []) hx hy hT hU hTx hTy hUT hUx hUy
    (by rw [hu]; exact coef_natAbs (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv))
    (by rw [hv]; exact coef_natAbs (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv)))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [hu, hv, Divstep.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv), Divstep.cong_comb hf hg] at e₁
  obtain ⟨b1, b2⟩ := Divstep.comb_range (A := 2 ^ (64 * (L - 1))) huv hfb hgb hp
  refine WP.mono (shrM_ok hs₁ (dst := dst) (src := T) (by omega_using [hL]) hT hd hdT e₁ b1 b2 (Int.mul_ediv_cancel' hdiv).symm)
    fun t ⟨e, k, O⟩ => ⟨e, k₁.trans (k.mono (by decide)), (O₁.trans O.unch).mono fun w hw => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h | h <;> simp [h]⟩

/-- Half a batch's update of `a`, `b`: `[dst] = mredRaw (u a + v b)` (`n + 1` words, signed). -/
theorem abHalf_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {p : Nat}
    (hM : ModOkW M size p s.mem base) (hn2 : 2 ≤ M.n) {w w' : Reg}
    (hw : w ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13]) (hw' : w' ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13])
    {u v : Int} (hu : s.gpr w = BitVec.ofInt 64 u) (hv : s.gpr w' = BitVec.ofInt 64 v) (huv : |u| + |v| ≤ 2 ^ 59)
    {T x y U dst : Nat} (hx : x + 8 * (M.n + 1) ≤ size) (hy : y + 8 * (M.n + 1) ≤ size)
    (hT : T + 8 * (M.n + 2) ≤ size) (hU : U + 8 * M.n ≤ size) (hd : dst + 8 * (M.n + 1) ≤ size)
    (hTx : T + 8 * (M.n + 2) ≤ x ∨ x + 8 * (M.n + 1) ≤ T) (hTy : T + 8 * (M.n + 2) ≤ y ∨ y + 8 * (M.n + 1) ≤ T)
    (hUT : U + 8 * M.n ≤ T ∨ T + 8 * (M.n + 2) ≤ U) (hUx : U + 8 * M.n ≤ x ∨ x + 8 * (M.n + 1) ≤ U)
    (hUy : U + 8 * M.n ≤ y ∨ y + 8 * (M.n + 1) ≤ U) (hdT : dst + 8 * (M.n + 1) ≤ T ∨ T + 8 * (M.n + 2) ≤ dst)
    (hTm : T + 8 * (M.n + 2) ≤ M.mo ∨ M.mo + 8 * M.n ≤ T) (hUm : U + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ U)
    {a b : Int}
    (ha : (wordsVal s.mem base x (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
      a % ((2 ^ (64 * (M.n + 1)) : Nat) : Int))
    (hb : (wordsVal s.mem base y (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
      b % ((2 ^ (64 * (M.n + 1)) : Nat) : Int))
    (ha0 : |a| ≤ 2 * p) (hb0 : |b| ≤ 2 * p) :
    WP isa (.block (linR w w' T x y U (M.n + 1) (M.n + 1) ++ mredS M dst T)) s fun t =>
      (wordsVal t.mem base dst (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
        Divstep.mredRaw p M.minv.toNat (u * a + v * b) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s t ∧
      Unch base [(T, 8 * (M.n + 2)), (U, 8 * M.n), (dst, 8 * (M.n + 1))] s.mem t.mem := by
  have hn := hs.nowrap
  have hn0 := hM.n0
  rw [WP.block_append_iff]
  -- `omega` given the fact it needs: the context has eight disjunctions it would split.
  refine WP.mono (linR_ok hs hw hw' (k := M.n + 1) (K := M.n + 1) (Nat.le_refl _) (by omega_using [hn2])
    (by omega_using []) hx hy (by omega_using [hT]) (by omega_using [hU]) (by omega_using [hTx])
    (by omega_using [hTy]) (by omega_using [hUT]) (by omega_using [hUx]) (by omega_using [hUy])
    (by rw [hu]; exact coef_natAbs (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv))
    (by rw [hv]; exact coef_natAbs (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv))) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [hu, hv, Divstep.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv), Divstep.cong_comb ha hb] at e₁
  obtain hM₁ := modOk_out hM O₁ (by
    have := hM.mo
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] <;> omega_arith) hn
  obtain hT' : |u * a + v * b| ≤ 2 ^ 63 * (p : Int) := by
    have := Divstep.comb_le huv ha0 hb0
    obtain hp0 : (0 : Int) ≤ p := Int.natCast_nonneg _
    exact le_trans this (by omega_arith)
  obtain O₁' : Unch base [(T, 8 * (M.n + 2)), (U, 8 * M.n)] s.mem s₁.mem := fun z hz => O₁ z (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz ⊢
    omega_using [hz])
  refine WP.mono (mredS_ok hs₁ hM₁ hT hd hTm hdT hT' e₁) fun t ⟨e, k, O⟩ =>
    ⟨e, k₁.trans k, (O₁'.trans O).mono fun w hw => ?_⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
  rcases hw with h | h | h | h <;> simp [h]

/-! ## A batch -/

/-- The slots, from the working area. -/
theorem slots (P : InvCfg) :
    P.L = P.M.n + 1 ∧ P.sF = P.tbl ∧ P.sG = P.tbl + 8 * P.M.n + 8 ∧ P.sA = P.tbl + 16 * P.M.n + 16 ∧
      P.sB = P.tbl + 24 * P.M.n + 24 ∧ P.sNF = P.tbl + 32 * P.M.n + 32 ∧ P.sNG = P.tbl + 40 * P.M.n + 40 ∧
      P.sT = P.tbl + 48 * P.M.n + 48 ∧ P.sU = P.tbl + 56 * P.M.n + 64 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [InvCfg.L, InvCfg.sG, InvCfg.sA, InvCfg.sB, InvCfg.sNF, InvCfg.sNG, InvCfg.sT, InvCfg.sU] <;>
    omega_using []

/-- The slots' arithmetic, from `slots` and the layout (named `eL` … `eU`, `n4`, `htbl`, `hn`). -/
tactic_template "inv_slot_omega" : tactic =>
  `(tactic| ((try simp only [eL, eF, eG, eA, eB, eNF, eNG, eT, eU]); omega_using [n4, htbl, hn]))

/-- What a batch writes: the working area. -/
def batchW (P : InvCfg) : List (Nat × Nat) := [(P.tbl, invTbl P.M.n)]

/-- The registers the divsteps and the updates write. -/
abbrev wordRegs : List Reg := [.rax, .rbx, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13]

/-- The registers a batch writes: those and the count in `r14`. -/
abbrev batchRegs : List Reg := .r14 :: wordRegs

/-- The batch state in memory: `d` in `rbx`, `f`, `g`, `a`, `b` (two's complement,
`n + 1` words). -/
structure IInv (P : InvCfg) (base : Addr) (I : Divstep.IState) (s : State) : Prop where
  d : s.gpr .rbx = BitVec.ofInt 64 I.d
  f : (wordsVal s.mem base P.sF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = I.f % ((2 ^ (64 * P.L) : Nat) : Int)
  g : (wordsVal s.mem base P.sG P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = I.g % ((2 ^ (64 * P.L) : Nat) : Int)
  a : (wordsVal s.mem base P.sA P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = I.a % ((2 ^ (64 * P.L) : Nat) : Int)
  b : (wordsVal s.mem base P.sB P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = I.b % ((2 ^ (64 * P.L) : Nat) : Int)

/-- `[d] = [a]`, through `rax`. -/
theorem copy1_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d a : Nat} (hd : d + 8 ≤ size)
    (ha : a + 8 ≤ size) :
    WP isa (.block (copy 1 d a)) s fun t =>
      t.mem = s.mem.writeW (off base d) (word s.mem base a) ∧ KeepRegs [.rax] s t := by
  rw [copy, copy, List.append_nil, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .rax ha) fun s₁ ⟨c₁, _, k₁⟩ => ?_
  refine WP.mono (storeReg_ok (hs.of_keeps k₁ (by decide)) .rax hd) fun t ⟨m, _, _, k⟩ =>
    ⟨by rw [m, c₁, k₁.2.1], (Keeps.regs k₁).trans (k.mono (by regions_sub))⟩

theorem xor_m1 (x : BitVec 64) : x ^^^ (-1 : BitVec 32).signExtend 64 = ~~~x := by
  rw [show (-1 : BitVec 32).signExtend 64 = BitVec.allOnes 64 by decide, BitVec.xor_allOnes]

/-- `rbx = ~rbx`. -/
theorem notRbx_ok (s : State) :
    WP isa (.block [.alu .xor .rbx (.imm (-1))]) s fun t => t.gpr .rbx = ~~~s.gpr .rbx ∧ Keeps [.rbx] s t := by
  irun [xor_m1]
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ↓reduceIte]

/-- A batch's start: the low words of `f`, `g` at `[sT]`, `[sT + 8]`, and `~d`. -/
theorem batchStart_ok {P : InvCfg} {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hF : P.sF + 8 ≤ size) (hG : P.sG + 8 ≤ size) (hT : P.sT + 16 ≤ size) (hGT : P.sG + 8 ≤ P.sT) :
    WP isa (.block P.batchStart) s fun t =>
      word t.mem base P.sT = word s.mem base P.sF ∧ word t.mem base (P.sT + 8) = word s.mem base P.sG ∧
      t.gpr .rbx = ~~~s.gpr .rbx ∧ KeepRegs [.rax, .rbx] s t ∧ Outside base P.sT 16 s.mem t.mem := by
  have hn := hs.nowrap
  rw [InvCfg.batchStart, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy1_ok hs (d := P.sT) (a := P.sF) (by omega_using [hT]) hF) fun s₁ ⟨m₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  refine WP.mono (copy1_ok hs₁ (d := P.sT + 8) (a := P.sG) (by omega_using [hT]) hG) fun s₂ ⟨m₂, k₂⟩ => ?_
  refine WP.mono (notRbx_ok s₂) fun t ⟨b, k⟩ => ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [k.2.1, m₂, word_apart _ _ _ (by omega_using []) (by omega_using [hT, hn]) (by omega_using [hT, hn]), m₁, word_writeW_self]
  · rw [k.2.1, m₂, word_writeW_self, m₁, word_apart _ _ _ (by omega_using [hGT]) (by omega_using [hT, hGT, hn]) (by omega_using [hT, hn])]
  · rw [b, k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  · exact ((k₁.mono (by regions_sub)).trans (k₂.mono (by regions_sub))).trans ((Keeps.regs k).mono (by regions_sub))
  · rw [k.2.1, m₂, m₁]
    exact ((writeW_outside _ _ _ (by omega_using [hT, hn])).mono (by omega_using []) (by omega_using [])).trans
      ((writeW_outside _ _ _ (by omega_using [hT, hn])).mono (by omega_using []) (by omega_using []))

/-- The low word of numbers of `L` words congruent modulo `2^(64 L)`. -/
theorem low_cong {P : InvCfg} {m : Mem} {base : Addr} {d : Nat} {x : Int}
    (h : (wordsVal m base d P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = x % ((2 ^ (64 * P.L) : Nat) : Int)) :
    ((word m base d).toNat : Int) % 2 ^ 64 = x % 2 ^ 64 := by
  obtain hdvd : ((2 : Int) ^ 64) ∣ ((2 ^ (64 * P.L) : Nat) : Int) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_dvd_pow 2 (by unfold InvCfg.L; omega_using [])
  obtain low : ((word m base d).toNat : Int) % 2 ^ 64 = (wordsVal m base d P.L : Int) % 2 ^ 64 := by
    unfold InvCfg.L; rw [wordsVal]; push_cast; rw [Int.add_mul_emod_self_left]
  rw [low, ← Int.emod_emod_of_dvd _ hdvd, h, Int.emod_emod_of_dvd _ hdvd]

/-- A batch's words: `59` divsteps from the low words of `f`, `g`, in chunks,
leave `d` and the matrix in `rbx`, `r9`–`r12`. -/
theorem words_ok {P : InvCfg} {base : Addr} {size : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    {I : Divstep.IState} (hI : IInv P base I s) (hd : |I.d| ≤ 2 ^ 30) (hf1 : I.f % 2 = 1) :
    WP isa (.block P.words) s fun t =>
      t.gpr .rbx = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).d ∧
      t.gpr .r9 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).u ∧
      t.gpr .r10 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).v ∧
      t.gpr .r11 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).q ∧
      t.gpr .r12 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).r ∧
      Outside base P.sT 24 s.mem t.mem ∧ KeepRegs wordRegs s t := by
  obtain ⟨eL, eF, eG, -, -, -, -, eT, -⟩ := slots P
  obtain n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl
  have hn := hs.nowrap
  set T0 := Divstep.MSt.init I.d I.f I.g with hT0
  have f0 : T0.f % 2 = 1 := hf1
  obtain odd : ∀ k, (Divstep.msteps k T0).f % 2 = 1 := Divstep.msteps_f_odd f0
  obtain dd : ∀ k, |(Divstep.msteps k T0).d| ≤ 2 ^ 30 + 2 * k := fun k => by
    have := Divstep.msteps_d T0 k
    rw [show T0.d = I.d from rfl] at this
    omega_arith
  obtain hT : P.sT + 24 ≤ size := by omega_using [eT, htbl, n4]
  rw [InvCfg.words]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (batchStart_ok hs (by omega_using [eF, htbl]) (by omega_using [eG, htbl]) (by omega_using [hT]) (by omega_using [eG, eT]))
    fun s₁ ⟨wf₁, wg₁, b₁, k₁, o₁⟩ => ?_
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  obtain c₁ : ChunkAt base P.sT 64 true T0 s₁ :=
    ⟨by rw [b₁, hI.d]; rfl, by rw [wf₁]; exact low_cong hI.f, by rw [wg₁]; exact low_cong hI.g,
      fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun h => absurd h (by decide)⟩
  rw [WP.block_append_iff]
  refine WP.mono (pchunk_ok hs₁ (n := 15) (K := 64) (last := false) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ hT f0 (by rw [show T0.d = I.d from rfl]; push_cast; omega_arith) c₁)
    fun s₂ ⟨d₂, u₂, v₂, q₂, r₂, w₂, k₂, o₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain ⟨f₂, g₂⟩ := w₂ rfl
  rw [WP.block_append_iff]
  refine WP.mono (pchunk_ok hs₂ (n := 15) (K := 49) (first := false) (last := false) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ hT (odd 15) (by have := dd 15; norm_num at this ⊢; omega_arith)
    ⟨d₂, f₂, g₂, fun h => absurd h (by decide), fun _ => ⟨u₂, v₂, q₂, r₂⟩⟩)
    fun s₃ ⟨d₃, u₃, v₃, q₃, r₃, w₃, k₃, o₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  obtain ⟨f₃, g₃⟩ := w₃ rfl
  rw [← Divstep.msteps_add] at d₃ u₃ v₃ q₃ r₃ f₃ g₃
  rw [WP.block_append_iff]
  refine WP.mono (pchunk_ok hs₃ (n := 15) (K := 34) (first := false) (last := false) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ hT (odd 30) (by have := dd 30; norm_num at this ⊢; omega_arith)
    ⟨d₃, f₃, g₃, fun h => absurd h (by decide), fun _ => ⟨u₃, v₃, q₃, r₃⟩⟩)
    fun s₄ ⟨d₄, u₄, v₄, q₄, r₄, w₄, k₄, o₄⟩ => ?_
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  obtain ⟨f₄, g₄⟩ := w₄ rfl
  rw [← Divstep.msteps_add] at d₄ u₄ v₄ q₄ r₄ f₄ g₄
  rw [WP.block_append_iff]
  refine WP.mono (pchunk_ok hs₄ (n := 14) (K := 19) (first := false) (last := true) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ hT (odd 45) (by have := dd 45; norm_num at this ⊢; omega_arith)
    ⟨d₄, f₄, g₄, fun h => absurd h (by decide), fun _ => ⟨u₄, v₄, q₄, r₄⟩⟩)
    fun s₅ ⟨d₅, u₅, v₅, q₅, r₅, _, k₅, o₅⟩ => ?_
  rw [← Divstep.msteps_add] at d₅ u₅ v₅ q₅ r₅
  refine WP.mono (notRbx_ok s₅) fun t ⟨b, k⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [b, d₅, BitVec.not_not]
  · rw [k.1 _ (by decide), u₅]
  · rw [k.1 _ (by decide), v₅]
  · rw [k.1 _ (by decide), q₅]
  · rw [k.1 _ (by decide), r₅]
  · rw [k.2.1]
    exact ((((o₁.mono (by omega_using []) (by omega_using [])).trans o₂).trans o₃).trans o₄).trans o₅
  · exact ((((k₁.mono (by decide)).trans k₂).trans k₃).trans k₄).trans k₅ |>.trans ((Keeps.regs k).mono (by decide))

/-- Each range of a list written out in one of another's, by `inv_slot_omega`. -/
tactic_template "inv_cover_omega" : tactic =>
  `(tactic| (set_option linter.unusedSimpArgs false in
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, exists_eq_or_imp, exists_eq_left] <;> inv_slot_omega))

/-- Both halves of the update of `f`, `g` into `f'`, `g'`. -/
abbrev fgHalves (P : InvCfg) : List Instr :=
  (linR .r9 .r10 P.sT P.sF P.sG P.sU P.L P.L ++ shr59 P.sNF P.sT P.L) ++
  (linR .r11 .r12 P.sT P.sF P.sG P.sU P.L P.L ++ shr59 P.sNG P.sT P.L)

/-- The update of `f`, `g`. -/
abbrev fgCode (P : InvCfg) : List Instr :=
  fgHalves P ++ (copy P.L P.sF P.sNF ++ copy P.L P.sG P.sNG)

/-- `f' = (u f + v g) / 2^59`, `g' = (q f + r g) / 2^59`, by the matrix in `r9`–`r12`. -/
theorem fgHalves_ok {P : InvCfg} {base : Addr} {size p : Nat} (hL : InvLay P size) {s : State}
    (hs : Scr s base size) (hp : p < 2 ^ (64 * P.M.n)) {u v q r f g : Int}
    (h9 : s.gpr .r9 = BitVec.ofInt 64 u) (h10 : s.gpr .r10 = BitVec.ofInt 64 v)
    (h11 : s.gpr .r11 = BitVec.ofInt 64 q) (h12 : s.gpr .r12 = BitVec.ofInt 64 r)
    (huv : |u| + |v| ≤ 2 ^ 59) (hqr : |q| + |r| ≤ 2 ^ 59)
    (hF : (wordsVal s.mem base P.sF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = f % ((2 ^ (64 * P.L) : Nat) : Int))
    (hG : (wordsVal s.mem base P.sG P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = g % ((2 ^ (64 * P.L) : Nat) : Int))
    (hf : |f| ≤ p) (hg : |g| ≤ p) (hdf : 2 ^ 59 ∣ u * f + v * g) (hdg : 2 ^ 59 ∣ q * f + r * g) :
    WP isa (.block (fgHalves P)) s fun t =>
      (wordsVal t.mem base P.sNF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
        ((u * f + v * g) / 2 ^ 59) % ((2 ^ (64 * P.L) : Nat) : Int) ∧
      (wordsVal t.mem base P.sNG P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
        ((q * f + r * g) / 2 ^ 59) % ((2 ^ (64 * P.L) : Nat) : Int) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s t ∧
      Unch base [(P.sNF, 32 * P.M.n + 32)] s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
  obtain n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl
  obtain hp' : p < 2 ^ (64 * (P.L - 1)) := by rw [eL, Nat.add_sub_cancel]; exact hp
  rw [WP.block_append_iff]
  refine WP.mono (fHalf_ok hs (w := .r9) (w' := .r10) (by decide) (by decide) h9 h10 huv
    (T := P.sT) (x := P.sF) (y := P.sG) (U := P.sU) (dst := P.sNF) (L := P.L) (by inv_slot_omega) (by inv_slot_omega)
    (by inv_slot_omega) (by inv_slot_omega) (by inv_slot_omega) (by inv_slot_omega) (by inv_slot_omega) (by inv_slot_omega)
    (by inv_slot_omega) (by inv_slot_omega) (by inv_slot_omega) (by inv_slot_omega) hF hG hf hg hp' hdf) fun s₁ ⟨e₁, k₁, U₁⟩ => ?_
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  obtain U₁' : Unch base [(P.sNF, 32 * P.M.n + 32)] s.mem s₁.mem := Unch.cover U₁ (by inv_cover_omega)
  obtain rF : wordsVal s₁.mem base P.sF P.L = wordsVal s.mem base P.sF P.L :=
    U₁'.wordsVal (by inv_cover_omega) (by inv_slot_omega)
  obtain rG : wordsVal s₁.mem base P.sG P.L = wordsVal s.mem base P.sG P.L :=
    U₁'.wordsVal (by inv_cover_omega) (by inv_slot_omega)
  refine WP.mono (fHalf_ok hs₁ (w := .r11) (w' := .r12) (by decide) (by decide)
    (by rw [k₁.gpr _ (by decide)]; exact h11) (by rw [k₁.gpr _ (by decide)]; exact h12) hqr
    (T := P.sT) (x := P.sF) (y := P.sG) (U := P.sU) (dst := P.sNG) (L := P.L) (by inv_slot_omega) (by inv_slot_omega)
    (by inv_slot_omega) (by inv_slot_omega) (by inv_slot_omega) (by inv_slot_omega) (by inv_slot_omega) (by inv_slot_omega)
    (by inv_slot_omega) (by inv_slot_omega) (by inv_slot_omega) (by inv_slot_omega)
    (by rw [rF]; exact hF) (by rw [rG]; exact hG) hf hg hp' hdg) fun t ⟨e₂, k₂, U₂⟩ => ⟨?_, e₂, k₁.trans k₂,
      Unch.cover (U₁'.trans U₂) (by inv_cover_omega)⟩
  rw [U₂.wordsVal (by inv_cover_omega) (by inv_slot_omega)]; exact e₁

/-- A batch's update of `f`, `g`, by the matrix in `r9`–`r12`. -/
theorem fgUpd_ok {P : InvCfg} {base : Addr} {size p : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hp : p < 2 ^ (64 * P.M.n)) {u v q r f g : Int}
    (h9 : s.gpr .r9 = BitVec.ofInt 64 u) (h10 : s.gpr .r10 = BitVec.ofInt 64 v)
    (h11 : s.gpr .r11 = BitVec.ofInt 64 q) (h12 : s.gpr .r12 = BitVec.ofInt 64 r)
    (huv : |u| + |v| ≤ 2 ^ 59) (hqr : |q| + |r| ≤ 2 ^ 59)
    (hF : (wordsVal s.mem base P.sF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = f % ((2 ^ (64 * P.L) : Nat) : Int))
    (hG : (wordsVal s.mem base P.sG P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = g % ((2 ^ (64 * P.L) : Nat) : Int))
    (hf : |f| ≤ p) (hg : |g| ≤ p) (hdf : 2 ^ 59 ∣ u * f + v * g) (hdg : 2 ^ 59 ∣ q * f + r * g) :
    WP isa (.block (fgCode P)) s fun t =>
      (wordsVal t.mem base P.sF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
        ((u * f + v * g) / 2 ^ 59) % ((2 ^ (64 * P.L) : Nat) : Int) ∧
      (wordsVal t.mem base P.sG P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
        ((q * f + r * g) / 2 ^ 59) % ((2 ^ (64 * P.L) : Nat) : Int) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s t ∧
      Unch base [(P.sF, 16 * P.M.n + 16), (P.sNF, 32 * P.M.n + 32)] s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
  obtain n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl
  rw [WP.block_append_iff]
  refine WP.mono (fgHalves_ok hL hs hp h9 h10 h11 h12 huv hqr hF hG hf hg hdf hdg) fun s₂ ⟨e₁, e₂, k₂, U₂⟩ => ?_
  obtain hs₂ := hs.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok P.L hs₂ (o := P.sF) (a := P.sNF) (by inv_slot_omega) (by inv_slot_omega) (by inv_slot_omega))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  obtain rNG : wordsVal s₃.mem base P.sNG P.L = wordsVal s₂.mem base P.sNG P.L :=
    O₃.wordsVal (by inv_slot_omega) (by inv_slot_omega)
  refine WP.mono (copy_ok P.L hs₃ (o := P.sG) (a := P.sNG) (by inv_slot_omega) (by inv_slot_omega) (by inv_slot_omega))
    fun t ⟨e₄, k₄, O₄⟩ => ⟨?_, ?_, k₂.trans ((k₃.trans k₄).mono (by decide)), ?_⟩
  · rw [O₄.wordsVal (by inv_slot_omega) (by inv_slot_omega), e₃]; exact e₁
  · rw [e₄, rNG]; exact e₂
  · exact Unch.cover (U₂.trans (O₃.unch.trans O₄.unch)) (by inv_cover_omega)

/-- `inv_slot_omega` with the modulus's place (`hmt`, `hmo`). -/
tactic_template "inv_slotm_omega" : tactic =>
  `(tactic| ((try simp only [eL, eF, eG, eA, eB, eNF, eNG, eT, eU]); omega_using [n4, htbl, hn, hmt, hmo]))

/-- Both halves of the update of `a`, `b`, into `a'` and `b`. -/
abbrev abHalves (P : InvCfg) : List Instr :=
  (linR .r9 .r10 P.sT P.sA P.sB P.sU P.L P.L ++ mredS P.M P.sNF P.sT) ++
  (linR .r11 .r12 P.sT P.sA P.sB P.sU P.L P.L ++ mredS P.M P.sB P.sT)

/-- The update of `a`, `b`. -/
abbrev abCode (P : InvCfg) : List Instr := abHalves P ++ copy P.L P.sA P.sNF

/-- `a' = mredRaw (u a + v b)`, `b = mredRaw (q a + r b)`, by the matrix in `r9`–`r12`. -/
theorem abHalves_ok {P : InvCfg} {base : Addr} {size p : Nat} (hL : InvLay P size) {s : State}
    (hs : Scr s base size) (hM : ModOkW P.M size p s.mem base) {u v q r a b : Int}
    (h9 : s.gpr .r9 = BitVec.ofInt 64 u) (h10 : s.gpr .r10 = BitVec.ofInt 64 v)
    (h11 : s.gpr .r11 = BitVec.ofInt 64 q) (h12 : s.gpr .r12 = BitVec.ofInt 64 r)
    (huv : |u| + |v| ≤ 2 ^ 59) (hqr : |q| + |r| ≤ 2 ^ 59)
    (hA : (wordsVal s.mem base P.sA P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = a % ((2 ^ (64 * P.L) : Nat) : Int))
    (hB : (wordsVal s.mem base P.sB P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = b % ((2 ^ (64 * P.L) : Nat) : Int))
    (ha : |a| ≤ 2 * p) (hb : |b| ≤ 2 * p) :
    WP isa (.block (abHalves P)) s fun t =>
      (wordsVal t.mem base P.sNF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
        Divstep.mredRaw p P.M.minv.toNat (u * a + v * b) % ((2 ^ (64 * P.L) : Nat) : Int) ∧
      (wordsVal t.mem base P.sB P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
        Divstep.mredRaw p P.M.minv.toNat (q * a + r * b) % ((2 ^ (64 * P.L) : Nat) : Int) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s t ∧
      Unch base [(P.sB, 40 * P.M.n + 40)] s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
  obtain n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl; have hmt := hL.mo_tbl; unfold invTbl at hmt
  have hmo := hM.mo
  rw [WP.block_append_iff]
  refine WP.mono (abHalf_ok hs hM (by omega_using [n4]) (w := .r9) (w' := .r10) (by decide) (by decide) h9 h10 huv
    (T := P.sT) (x := P.sA) (y := P.sB) (U := P.sU) (dst := P.sNF) (by inv_slotm_omega) (by inv_slotm_omega)
    (by inv_slotm_omega) (by inv_slotm_omega) (by inv_slotm_omega) (by inv_slotm_omega) (by inv_slotm_omega) (by inv_slotm_omega)
    (by inv_slotm_omega) (by inv_slotm_omega) (by inv_slotm_omega) (by inv_slotm_omega) (by inv_slotm_omega) hA hB ha hb)
    fun s₁ ⟨e₁, k₁, U₁⟩ => ?_
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  obtain U₁' : Unch base [(P.sB, 40 * P.M.n + 40)] s.mem s₁.mem := Unch.cover U₁ (by inv_cover_omega)
  obtain rA : wordsVal s₁.mem base P.sA (P.M.n + 1) = wordsVal s.mem base P.sA (P.M.n + 1) :=
    U₁'.wordsVal (by inv_cover_omega) (by inv_slot_omega)
  obtain rB : wordsVal s₁.mem base P.sB (P.M.n + 1) = wordsVal s.mem base P.sB (P.M.n + 1) :=
    U₁.wordsVal (by inv_cover_omega) (by inv_slot_omega)
  obtain M₁ := modOk_out hM U₁' (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; inv_slotm_omega) hn
  refine WP.mono (abHalf_ok hs₁ M₁ (by omega_using [n4]) (w := .r11) (w' := .r12) (by decide) (by decide)
    (by rw [k₁.gpr _ (by decide)]; exact h11) (by rw [k₁.gpr _ (by decide)]; exact h12) hqr
    (T := P.sT) (x := P.sA) (y := P.sB) (U := P.sU) (dst := P.sB) (by inv_slotm_omega) (by inv_slotm_omega)
    (by inv_slotm_omega) (by inv_slotm_omega) (by inv_slotm_omega) (by inv_slotm_omega) (by inv_slotm_omega) (by inv_slotm_omega)
    (by inv_slotm_omega) (by inv_slotm_omega) (by inv_slotm_omega) (by inv_slotm_omega) (by inv_slotm_omega)
    (by rw [rA]; exact hA) (by rw [rB]; exact hB) ha hb) fun t ⟨e₂, k₂, U₂⟩ =>
      ⟨?_, e₂, k₁.trans k₂, Unch.cover (U₁'.trans U₂) (by inv_cover_omega)⟩
  rw [U₂.wordsVal (by inv_cover_omega) (by inv_slot_omega)]; exact e₁

/-- A batch's update of `a`, `b`, by the matrix in `r9`–`r12`. -/
theorem abUpd_ok {P : InvCfg} {base : Addr} {size p : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size p s.mem base) {u v q r a b : Int}
    (h9 : s.gpr .r9 = BitVec.ofInt 64 u) (h10 : s.gpr .r10 = BitVec.ofInt 64 v)
    (h11 : s.gpr .r11 = BitVec.ofInt 64 q) (h12 : s.gpr .r12 = BitVec.ofInt 64 r)
    (huv : |u| + |v| ≤ 2 ^ 59) (hqr : |q| + |r| ≤ 2 ^ 59)
    (hA : (wordsVal s.mem base P.sA P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = a % ((2 ^ (64 * P.L) : Nat) : Int))
    (hB : (wordsVal s.mem base P.sB P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = b % ((2 ^ (64 * P.L) : Nat) : Int))
    (ha : |a| ≤ 2 * p) (hb : |b| ≤ 2 * p) :
    WP isa (.block (abCode P)) s fun t =>
      (wordsVal t.mem base P.sA P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
        Divstep.mredRaw p P.M.minv.toNat (u * a + v * b) % ((2 ^ (64 * P.L) : Nat) : Int) ∧
      (wordsVal t.mem base P.sB P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
        Divstep.mredRaw p P.M.minv.toNat (q * a + r * b) % ((2 ^ (64 * P.L) : Nat) : Int) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s t ∧
      Unch base [(P.sA, 48 * P.M.n + 48)] s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
  obtain n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl
  rw [WP.block_append_iff]
  refine WP.mono (abHalves_ok hL hs hM h9 h10 h11 h12 huv hqr hA hB ha hb) fun s₂ ⟨e₁, e₂, k₂, U₂⟩ => ?_
  obtain hs₂ := hs.of_keepRegs k₂ (by decide)
  refine WP.mono (copy_ok P.L hs₂ (o := P.sA) (a := P.sNF) (by inv_slot_omega) (by inv_slot_omega) (by inv_slot_omega))
    fun t ⟨e₃, k₃, O₃⟩ => ⟨by rw [e₃]; exact e₁, by rw [O₃.wordsVal (by inv_slot_omega) (by inv_slot_omega)]; exact e₂,
      k₂.trans (k₃.mono (by decide)), Unch.cover (U₂.trans O₃.unch) (by inv_cover_omega)⟩

/-- The count of batches less one, its zero flag whether it is now zero. -/
theorem batchEnd_ok (s : State) {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64)
    (hb : s.gpr .r14 = BitVec.ofNat 64 j) :
    WP isa (.block InvCfg.batchEnd) s fun s' =>
      s'.gpr .r14 = BitVec.ofNat 64 (j - 1) ∧ s'.zf = some (decide (j - 1 = 0)) ∧ Keeps [.r14] s s' := by
  apply WP.of_runBlock
  simp only [InvCfg.batchEnd, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, RegUpd.gpr_setReg, RegUpd.zf_setReg, RegUpd.zf_arithFlags, ite_true, Option.some.injEq,
    exists_eq_left', hb, sext1]
  obtain e : BitVec.ofNat 64 j - 1 = BitVec.ofNat 64 (j - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    rw [Nat.mod_eq_of_lt hj', Nat.mod_eq_of_lt (by omega_using [hj'] : j - 1 < 2 ^ 64)]
    omega_using [hj, hj']
  refine ⟨e, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [e]
    congr 1
    by_cases h : j - 1 = 0
    · rw [h]; simp
    · rw [decide_eq_false h]
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hj'])] at this
      exact h this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem update_eq (P : InvCfg) :
    P.fgUpdate ++ P.abUpdate ++ InvCfg.batchEnd = fgCode P ++ (abCode P ++ InvCfg.batchEnd) := by
  simp only [fgCode, fgHalves, abCode, abHalves, InvCfg.fgUpdate, InvCfg.abUpdate, List.append_assoc]

/-- A batch: `59` divsteps on the low words, then `f`, `g`, `a`, `b` by their matrix,
and the count less one. -/
theorem batch_ok {P : InvCfg} {base : Addr} {size p : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size p s.mem base) {I : Divstep.IState} (hI : IInv P base I s)
    (hd : |I.d| ≤ 2 ^ 30) (hf1 : I.f % 2 = 1) (hf : |I.f| ≤ p) (hg : |I.g| ≤ p)
    (ha : |I.a| ≤ 2 * p) (hb : |I.b| ≤ 2 * p) {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64)
    (hc : s.gpr .r14 = BitVec.ofNat 64 j) :
    WP isa P.batch s fun t =>
      (IInv P base (Divstep.batchS 59 p P.M.minv.toNat I) t ∧ t.gpr .r14 = BitVec.ofNat 64 (j - 1) ∧
        KeepRegs batchRegs s t ∧ Unch base (batchW P) s.mem t.mem) ∧ t.zf = some (decide (j - 1 = 0)) := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
  obtain n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl; have hmt := hL.mo_tbl; unfold invTbl at hmt
  have hmo := hM.mo
  obtain hp : p < 2 ^ (64 * P.M.n) := hM.val ▸ wordsVal_lt _ _ _ _
  obtain ⟨buv, bqr⟩ := Divstep.msteps_bnd I.d I.f I.g 59
  obtain ⟨mf, mg⟩ := Divstep.msteps_mat (d := I.d) (g := I.g) hf1 59
  rw [InvCfg.batch, List.append_assoc (P.words ++ _), List.append_assoc P.words, WP.block_append_iff]
  refine WP.mono (words_ok hL hs hI hd hf1) fun s₂ h₂ => ?_
  obtain ⟨hD, hU, hV, hQ, hR, O₂, k₂⟩ := h₂
  obtain hs₂ := hs.of_keepRegs k₂ (by decide)
  obtain hM₂ : ModOkW P.M size p s₂.mem base := modOk_out hM O₂.unch (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; inv_slotm_omega) hn
  rw [← List.append_assoc, update_eq, WP.block_append_iff]
  refine WP.mono (fgUpd_ok hL hs₂ hp hU hV hQ hR buv bqr (by rw [O₂.wordsVal (by inv_slot_omega) (by inv_slot_omega)]; exact hI.f)
    (by rw [O₂.wordsVal (by inv_slot_omega) (by inv_slot_omega)]; exact hI.g) hf hg
    ⟨_, mf.symm⟩ ⟨_, mg.symm⟩) fun s₃ ⟨eF₃, eG₃, k₃, U₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have g₃ : ∀ r ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .r13], s₃.gpr r = s₂.gpr r := k₃.gpr
  obtain M₃ : ModOkW P.M size p s₃.mem base := modOk_out hM₂ U₃ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; inv_slotm_omega) hn
  rw [WP.block_append_iff]
  refine WP.mono (abUpd_ok hL hs₃ M₃ (by rw [g₃ _ (by decide)]; exact hU) (by rw [g₃ _ (by decide)]; exact hV)
    (by rw [g₃ _ (by decide)]; exact hQ) (by rw [g₃ _ (by decide)]; exact hR) buv bqr
    (by rw [U₃.wordsVal (by inv_cover_omega) (by inv_slot_omega), O₂.wordsVal (by inv_slot_omega) (by inv_slot_omega)]; exact hI.a)
    (by rw [U₃.wordsVal (by inv_cover_omega) (by inv_slot_omega), O₂.wordsVal (by inv_slot_omega) (by inv_slot_omega)]; exact hI.b)
    ha hb) fun s₄ ⟨eA₄, eB₄, k₄, U₄⟩ => ?_
  obtain c₄ : s₄.gpr .r14 = BitVec.ofNat 64 j := by
    rw [k₄.gpr _ (by decide), g₃ _ (by decide), k₂.gpr _ (by decide), hc]
  refine WP.mono (batchEnd_ok s₄ hj hj' c₄) fun t ⟨ct, zt, kt⟩ =>
    ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ct, ?_, ?_⟩, zt⟩
  · simp only [Divstep.batchS]
    rw [kt.1 _ (by decide), k₄.gpr _ (by decide), g₃ _ (by decide)]; exact hD
  · simp only [Divstep.batchS]
    rw [kt.2.1, U₄.wordsVal (by inv_cover_omega) (by inv_slot_omega)]; exact eF₃
  · simp only [Divstep.batchS]
    rw [kt.2.1, U₄.wordsVal (by inv_cover_omega) (by inv_slot_omega)]; exact eG₃
  · simp only [Divstep.batchS]
    rw [kt.2.1]; exact eA₄
  · simp only [Divstep.batchS]
    rw [kt.2.1]; exact eB₄
  · exact ((k₂.mono (by decide)).trans ((k₃.trans k₄).mono (by decide))).trans ((Keeps.regs kt).mono (by decide))
  · rw [kt.2.1]; exact Unch.cover ((O₂.unch.trans U₃).trans U₄) (by unfold batchW invTbl; inv_cover_omega)

end VG.Proof.Weierstrass.X86_64
