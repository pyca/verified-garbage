import VerifiedGarbage.Proof.Weierstrass.AArch64.InvRed
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Inversion by divsteps on AArch64: a batch

The signed linear combinations of a batch as integers modulo the words'
range (`linM_ok`), the shift by 59 of a multiple of `2^59` (`shrM_ok`), and a
batch: `59` divsteps on the low words, then `f`, `g`, `a`, `b` updated by
their matrix, as `Divstep.batch` (`batch_ok`).
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- `2^64 [x]` modulo `2^(64 K)` reads only `K - 1` of `[x]`'s words. -/
theorem shifted_cong (m : Mem) (base : Addr) (x : Nat) {k K : Nat} (hk : K - 1 ≤ k) (hK : 1 ≤ K) :
    ((2 ^ 64 * wordsVal m base x (K - 1) : Nat) : Int) % ((2 ^ (64 * K) : Nat) : Int) =
      ((2 ^ 64 * wordsVal m base x k : Nat) : Int) % ((2 ^ (64 * K) : Nat) : Int) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = K - 1 + j := ⟨k - (K - 1), by omega⟩
  rw [wordsVal_split, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add, show 64 + 64 * (K - 1) = 64 * K by omega]
  push_cast
  rw [Int.add_mul_emod_self_left]

/-- `[T] = u [x] + v [y]` modulo `2^(64 K)`, for words `u`, `v` (signed) in `w`, `w'`. -/
theorem linM_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (h12 : s.gpr .x12 = 0)
    {w w' : Reg} (hw : w ∉ [Reg.x0, .x2, .x3, .x8, .x9, .x10, .x12, .x16, .x17])
    (hw' : w' ∉ [Reg.x0, .x2, .x3, .x8, .x9, .x10, .x12, .x16, .x17])
    {T x y k K : Nat} (h1 : 1 ≤ k) (hkK : k ≤ K) (hK : 2 ≤ K) (hk' : K ≤ k + 1)
    (hx : x + 8 * k ≤ size) (hx8 : x % 8 = 0) (hy : y + 8 * k ≤ size) (hy8 : y % 8 = 0)
    (hT : T + 8 * K ≤ size) (hT8 : T % 8 = 0)
    (hTx : T + 8 * K ≤ x ∨ x + 8 * k ≤ T) (hTy : T + 8 * K ≤ y ∨ y + 8 * k ≤ T) :
    WP isa (.block (maskOf .x16 w ++ maskOf .x17 w' ++ lin w w' .x16 .x17 T x y k K)) s fun t =>
      (wordsVal t.mem base T K : Int) % ((2 ^ (64 * K) : Nat) : Int) =
        ((s.gpr w).toInt * wordsVal s.mem base x k + (s.gpr w').toInt * wordsVal s.mem base y k) %
          ((2 ^ (64 * K) : Nat) : Int) ∧
      KeepRegs [.x2, .x3, .x8, .x9, .x10, .x16, .x17] s t ∧ Outside base T (8 * K) s.mem t.mem := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw hw'
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (maskOf_ok s (d := .x16) (r := w) h12 (by decide)) fun s₁ ⟨g₁, m₁, k₁, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (maskOf_ok s₁ (d := .x17) (r := w') (by rw [k₁.gpr _ (by decide), h12]) (by decide))
    fun s₂ ⟨g₂, m₂, k₂, _⟩ => ?_
  have hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  have ew : s₂.gpr w = s.gpr w := by
    rw [k₂.gpr _ (by simp [hw.2.2.2.2.2.2.2.2]), k₁.gpr _ (by simp [hw.2.2.2.2.2.2.2.1])]
  have ew' : s₂.gpr w' = s.gpr w' := by
    rw [k₂.gpr _ (by simp [hw'.2.2.2.2.2.2.2.2]), k₁.gpr _ (by simp [hw'.2.2.2.2.2.2.2.1])]
  have g₁' : (s₂.gpr .x16).toNat = sgnW (s.gpr w) := by rw [k₂.gpr _ (by decide), g₁]
  have g₂' : (s₂.gpr .x17).toNat = sgnW (s.gpr w') := by rw [g₂, k₁.gpr _ (by simp [hw'.2.2.2.2.2.2.2.1])]
  have m₂' : s₂.mem = s.mem := by rw [k₂.mem, k₁.mem]
  refine WP.mono (lin_ok hs₂ (w := w) (w' := w') (mw := .x16) (mw' := .x17)
    (by simp [hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1])
    (by simp [hw'.1, hw'.2.1, hw'.2.2.1, hw'.2.2.2.1, hw'.2.2.2.2.1, hw'.2.2.2.2.2.1])
    (by decide) (by decide) (by rw [k₂.gpr _ (by decide)]; exact m₁) m₂
    (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), h12]) h1 hkK hK hk' hx hx8 hy hy8 hT hT8 hTx hTy)
    fun t ⟨e, kt, O⟩ => ⟨?_, ((Keeps.regs k₁).mono (by decide)).trans (((Keeps.regs k₂).mono (by decide)).trans
      (kt.mono (by decide))), by rw [← m₂']; exact O⟩
  rw [masked_sgn g₁', masked_sgn g₂', ew, ew', m₂'] at e
  have e' := congrArg (Nat.cast : Nat → Int) e
  push_cast at e'
  rw [← Divstep.toInt_sgn, ← Divstep.toInt_sgn]
  refine Divstep.lin_words (X' := wordsVal s.mem base x (K - 1)) (Y' := wordsVal s.mem base y (K - 1)) ?_ ?_ ?_
  · have := shifted_cong s.mem base x (k := k) (K := K) (by omega) (by omega); push_cast at this; exact this
  · have := shifted_cong s.mem base y (k := k) (K := K) (by omega) (by omega); push_cast at this; exact this
  · push_cast; convert e' using 3

/-- `[dst] = y / 2^59` modulo `2^(64 L)`, for `[src] ≡ y` with `|y| < 2^(64 L - 1)`
a multiple of `2^59`. -/
theorem shrM_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (h12 : s.gpr .x12 = 0)
    {dst src L : Nat} (hL : 1 ≤ L)
    (hsrc : src + 8 * L ≤ size) (hs8 : src % 8 = 0) (hdst : dst + 8 * L ≤ size) (hd8 : dst % 8 = 0)
    (hsep : dst + 8 * L ≤ src ∨ src + 8 * L ≤ dst) {y z : Int}
    (hy : (wordsVal s.mem base src L : Int) % ((2 ^ (64 * L) : Nat) : Int) = y % ((2 ^ (64 * L) : Nat) : Int))
    (hy1 : -((2 ^ (64 * (L - 1)) * 2 ^ 63 : Nat) : Int) ≤ y) (hy2 : y < ((2 ^ (64 * (L - 1)) * 2 ^ 63 : Nat) : Int))
    (hz : y = 2 ^ 59 * z) :
    WP isa (.block (shr59 dst src L)) s fun t =>
      (wordsVal t.mem base dst L : Int) % ((2 ^ (64 * L) : Nat) : Int) = z % ((2 ^ (64 * L) : Nat) : Int) ∧
      KeepRegs [.x2, .x3, .x8, .x9] s t ∧ Outside base dst (8 * L) s.mem t.mem := by
  refine WP.mono (shr59_ok hs h12 hL hsrc hs8 hdst hd8 hsep) fun t ⟨e, k, O⟩ => ⟨?_, k, O⟩
  obtain ⟨j, rfl⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hy1 hy2 ⊢
  have hQ : 2 ^ (64 * (j + 1)) = 2 * (2 ^ (64 * j) * 2 ^ 63) := by
    rw [pow64_succ, show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl]; ring
  rw [sext, Nat.add_sub_cancel, sgnW_top, hQ] at e
  rw [hQ] at hy ⊢
  exact Divstep.shr_nat (c := 2 ^ 59) (B := 2 ^ 64) rfl rfl (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
    (by have := wordsVal_lt s.mem base src (j + 1); rw [hQ] at this; exact this) hy hy1 hy2 hz e

theorem modOk_out {M : Mod} {size p : Nat} {mem mem' : Mem} {base : Addr} (hM : ModOk M size p mem base) {o len : Nat}
    (hO : Outside base o len mem mem') (hsep : o + len ≤ M.mo ∨ M.mo + 8 * M.n ≤ o) (hn : base.toNat + size ≤ 2 ^ 64) :
    ModOk M size p mem' base :=
  ⟨hM.n0, hM.n7, hM.mo, hM.tmp, hM.sep, by rw [hO.wordsVal (by omega) (by have := hM.mo; omega)]; exact hM.val,
    hM.inv, hM.red⟩

/-- Half a batch's update of `f`, `g`: `[dst] = (u f + v g) / 2^59` (`L` words, signed). -/
theorem fHalf_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (h12 : s.gpr .x12 = 0)
    {w w' : Reg} (hw : w ∉ [Reg.x0, .x2, .x3, .x8, .x9, .x10, .x12, .x16, .x17])
    (hw' : w' ∉ [Reg.x0, .x2, .x3, .x8, .x9, .x10, .x12, .x16, .x17])
    {u v : Int} (hu : s.gpr w = BitVec.ofInt 64 u) (hv : s.gpr w' = BitVec.ofInt 64 v) (huv : |u| + |v| ≤ 2 ^ 59)
    {T x y dst L : Nat} (hL : 2 ≤ L) (hx : x + 8 * L ≤ size) (hx8 : x % 8 = 0) (hy : y + 8 * L ≤ size)
    (hy8 : y % 8 = 0) (hT : T + 8 * L ≤ size) (hT8 : T % 8 = 0) (hd : dst + 8 * L ≤ size) (hd8 : dst % 8 = 0)
    (hTx : T + 8 * L ≤ x ∨ x + 8 * L ≤ T) (hTy : T + 8 * L ≤ y ∨ y + 8 * L ≤ T)
    (hdT : dst + 8 * L ≤ T ∨ T + 8 * L ≤ dst) {p : Nat} {f g : Int}
    (hf : (wordsVal s.mem base x L : Int) % ((2 ^ (64 * L) : Nat) : Int) = f % ((2 ^ (64 * L) : Nat) : Int))
    (hg : (wordsVal s.mem base y L : Int) % ((2 ^ (64 * L) : Nat) : Int) = g % ((2 ^ (64 * L) : Nat) : Int))
    (hfb : |f| ≤ p) (hgb : |g| ≤ p) (hp : p < 2 ^ (64 * (L - 1))) (hdiv : 2 ^ 59 ∣ u * f + v * g) :
    WP isa (.block ((maskOf .x16 w ++ maskOf .x17 w' ++ lin w w' .x16 .x17 T x y L L) ++ shr59 dst T L)) s
      fun t =>
        (wordsVal t.mem base dst L : Int) % ((2 ^ (64 * L) : Nat) : Int) =
          ((u * f + v * g) / 2 ^ 59) % ((2 ^ (64 * L) : Nat) : Int) ∧
        KeepRegs [.x2, .x3, .x8, .x9, .x10, .x16, .x17] s t ∧ Unch base [(T, 8 * L), (dst, 8 * L)] s.mem t.mem := by
  have hn := hs.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (linM_ok hs h12 hw hw' (k := L) (K := L) (by omega) (Nat.le_refl _) hL (by omega) hx hx8 hy hy8
    hT hT8 hTx hTy) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [hu, hv, Divstep.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv), Divstep.cong_comb hf hg] at e₁
  obtain ⟨b1, b2⟩ := Divstep.comb_range (A := 2 ^ (64 * (L - 1))) huv hfb hgb hp
  refine WP.mono (shrM_ok hs₁ (by rw [k₁.gpr _ (by decide), h12]) (dst := dst) (src := T) (by omega) hT hT8 hd hd8
    hdT e₁ b1 b2 (Int.mul_ediv_cancel' hdiv).symm) fun t ⟨e, k, O⟩ =>
      ⟨e, k₁.trans (k.mono (by decide)), (O₁.unch.trans O.unch).mono fun w hw => by simpa using hw⟩

/-- Half a batch's update of `a`, `b`: `[dst] = mred (u a + v b)` (`n` words). -/
theorem abHalf_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {p : Nat}
    (hM : ModOk M size p s.mem base) (hmo8 : M.mo % 8 = 0) (h12 : s.gpr .x12 = 0)
    {w w' : Reg} (hw : w ∉ [Reg.x0, .x2, .x3, .x8, .x9, .x10, .x12, .x16, .x17])
    (hw' : w' ∉ [Reg.x0, .x2, .x3, .x8, .x9, .x10, .x12, .x16, .x17])
    {u v : Int} (hu : s.gpr w = BitVec.ofInt 64 u) (hv : s.gpr w' = BitVec.ofInt 64 v) (huv : |u| + |v| ≤ 2 ^ 59)
    {T x y dst : Nat} (hx : x + 8 * M.n ≤ size) (hx8 : x % 8 = 0) (hy : y + 8 * M.n ≤ size)
    (hy8 : y % 8 = 0) (hT : T + 8 * (M.n + 2) ≤ size) (hT8 : T % 8 = 0) (hd : dst + 8 * M.n ≤ size)
    (hd8 : dst % 8 = 0) (hTx : T + 8 * (M.n + 2) ≤ x ∨ x + 8 * M.n ≤ T) (hTy : T + 8 * (M.n + 2) ≤ y ∨ y + 8 * M.n ≤ T)
    (hdT : dst + 8 * M.n ≤ T ∨ T + 8 * (M.n + 2) ≤ dst) (hTm : T + 8 * (M.n + 2) ≤ M.mo ∨ M.mo + 8 * M.n ≤ T)
    {a b : Int} (ha : (wordsVal s.mem base x M.n : Int) = a) (hb : (wordsVal s.mem base y M.n : Int) = b)
    (ha0 : |a| ≤ p) (hb0 : |b| ≤ p) :
    WP isa (.block ((maskOf .x16 w ++ maskOf .x17 w' ++ lin w w' .x16 .x17 T x y M.n (M.n + 1)) ++ mredC M dst T)) s
      fun t =>
        (wordsVal t.mem base dst M.n : Int) = Divstep.mred p M.minv.toNat (u * a + v * b) ∧
        KeepRegs [.x2, .x3, .x8, .x9, .x10, .x16, .x17] s t ∧
        Unch base [(T, 8 * (M.n + 2)), (dst, 8 * M.n)] s.mem t.mem := by
  have hn := hs.nowrap
  have hn0 := hM.n0
  rw [WP.block_append_iff]
  refine WP.mono (linM_ok hs h12 hw hw' (k := M.n) (K := M.n + 1) (by omega) (by omega) (by omega) (by omega) hx hx8
    hy hy8 (by omega) hT8 (by omega) (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [hu, hv, Divstep.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv), ha, hb] at e₁
  have hM₁ := modOk_out hM O₁ (by omega) hn
  have hT' : |u * a + v * b| ≤ 2 ^ 63 * (p : Int) := by
    have := Divstep.comb_le huv ha0 hb0
    have hp : (0 : Int) ≤ p := Int.natCast_nonneg _
    nlinarith
  refine WP.mono (mredC_ok hs₁ hM₁ hmo8 (by rw [k₁.gpr _ (by decide), h12]) hT hT8 hd hd8 hTm hdT hT' e₁)
    fun t ⟨e, k, m₁, Ot, Od⟩ => ⟨e, k₁.trans k, ?_⟩
  exact ((O₁.mono (n' := 8 * (M.n + 2)) (Nat.le_refl _) (by omega)).unch.trans (Ot.unch.trans Od.unch)).mono
    fun w hw => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h | h <;> simp [h]

/-! ## A batch -/

/-- `r = imm`. -/
theorem movzI_ok (s : State) (r : Reg) (imm : BitVec 16) :
    WP isa (.block [.movz .x r imm 0]) s fun t => t.gpr r = imm.setWidth 64 ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
    ite_true, RegUpd.gpr_write_self, Option.some.injEq, exists_eq_left', Nat.mul_zero, BitVec.shiftLeft_zero,
    BitVec.setWidth_eq]
  refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  exact RegUpd.gpr_write_of_ne _ _ _ hq

/-- The slots, from the table area. -/
theorem slots (P : InvCfg) :
    P.L = P.M.n + 1 ∧ P.sF = P.tbl ∧ P.sG = P.tbl + 8 * (P.M.n + 1) ∧ P.sA = P.tbl + 16 * (P.M.n + 1) ∧
      P.sB = P.tbl + 16 * (P.M.n + 1) + 8 * P.M.n ∧ P.sNF = P.tbl + 16 * (P.M.n + 1) + 16 * P.M.n ∧
      P.sNG = P.tbl + 24 * (P.M.n + 1) + 16 * P.M.n ∧ P.sT = P.tbl + 32 * (P.M.n + 1) + 16 * P.M.n := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [InvCfg.L, InvCfg.sG, InvCfg.sA, InvCfg.sB, InvCfg.sNF, InvCfg.sNG, InvCfg.sT] <;> omega

/-- What a batch writes: the slots, `7 n + 6` words. -/
def batchW (P : InvCfg) : List (Nat × Nat) := [(P.tbl, 8 * (7 * P.M.n + 6))]

/-- The batch state in memory: `d` in `x1`, `f`, `g` (two's complement, `n + 1`
words), `a`, `b` (`n` words). -/
structure IInv (P : InvCfg) (base : Addr) (I : Divstep.IState) (s : State) : Prop where
  d : s.gpr .x1 = BitVec.ofInt 64 I.d
  f : (wordsVal s.mem base P.sF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = I.f % ((2 ^ (64 * P.L) : Nat) : Int)
  g : (wordsVal s.mem base P.sG P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = I.g % ((2 ^ (64 * P.L) : Nat) : Int)
  a : (wordsVal s.mem base P.sA P.M.n : Int) = I.a
  b : (wordsVal s.mem base P.sB P.M.n : Int) = I.b

/-- A batch's start: the counter, `x11 = 1`, `x12 = 0`, the low words of `f`, `g`, the identity. -/
theorem batchStart_ok {P : InvCfg} {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hF : P.sF + 8 ≤ size) (hF8 : P.sF % 8 = 0) (hG : P.sG + 8 ≤ size) (hG8 : P.sG % 8 = 0)
    {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64) (h19 : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block P.batchStart) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j - 1) ∧ t.gpr .x11 = 1 ∧ t.gpr .x12 = 0 ∧
      t.gpr .x2 = word s.mem base P.sF ∧ t.gpr .x3 = word s.mem base P.sG ∧
      t.gpr .x4 = 1 ∧ t.gpr .x5 = 0 ∧ t.gpr .x6 = 0 ∧ t.gpr .x7 = 1 ∧ t.mem = s.mem ∧
      KeepRegs [.x2, .x3, .x4, .x5, .x6, .x7, .x11, .x12, .x19] s t := by
  rw [InvCfg.batchStart, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (decCounter_ok s hj hj' h19) fun s₁ ⟨c₁, k₁⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzI_ok s₁ .x11 1) fun s₂ ⟨c₂, k₂⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzI_ok s₂ .x12 0) fun s₃ ⟨c₃, k₃⟩ => ?_
  have hs₃ : Scr s₃ base size := ((hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok hs₃ hF hF8 .x2) fun s₄ ⟨c₄, k₄, _⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok (hs₃.of_keeps k₄ (by decide)) hG hG8 .x3) fun s₅ ⟨c₅, k₅, _⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzI_ok s₅ .x4 1) fun s₆ ⟨c₆, k₆⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzI_ok s₆ .x5 0) fun s₇ ⟨c₇, k₇⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzI_ok s₇ .x6 0) fun s₈ ⟨c₈, k₈⟩ => ?_
  refine WP.mono (movzI_ok s₈ .x7 1) fun t ⟨c₉, k₉⟩ => ?_
  have m₃ : s₃.mem = s.mem := by rw [k₃.mem, k₂.mem, k₁.mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, c₉, ?_, ?_⟩
  · rw [k₉.gpr _ (by decide), k₈.gpr _ (by decide), k₇.gpr _ (by decide), k₆.gpr _ (by decide),
      k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), c₁]
  · rw [k₉.gpr _ (by decide), k₈.gpr _ (by decide), k₇.gpr _ (by decide), k₆.gpr _ (by decide),
      k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), c₂]; rfl
  · rw [k₉.gpr _ (by decide), k₈.gpr _ (by decide), k₇.gpr _ (by decide), k₆.gpr _ (by decide),
      k₅.gpr _ (by decide), k₄.gpr _ (by decide), c₃]; rfl
  · rw [k₉.gpr _ (by decide), k₈.gpr _ (by decide), k₇.gpr _ (by decide), k₆.gpr _ (by decide),
      k₅.gpr _ (by decide), c₄, m₃]
  · rw [k₉.gpr _ (by decide), k₈.gpr _ (by decide), k₇.gpr _ (by decide), k₆.gpr _ (by decide), c₅, k₄.mem, m₃]
  · rw [k₉.gpr _ (by decide), k₈.gpr _ (by decide), k₇.gpr _ (by decide), c₆]; rfl
  · rw [k₉.gpr _ (by decide), k₈.gpr _ (by decide), c₇]; rfl
  · rw [k₉.gpr _ (by decide), c₈]; rfl
  · rw [k₉.mem, k₈.mem, k₇.mem, k₆.mem, k₅.mem, k₄.mem, m₃]
  · exact (((((((((Keeps.regs k₁).mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
      ((Keeps.regs k₃).mono (by decide))).trans ((Keeps.regs k₄).mono (by decide))).trans
      ((Keeps.regs k₅).mono (by decide))).trans ((Keeps.regs k₆).mono (by decide))).trans
      ((Keeps.regs k₇).mono (by decide))).trans ((Keeps.regs k₈).mono (by decide))).trans
      ((Keeps.regs k₉).mono (by decide))

/-- The update of `f`, `g`. -/
abbrev fgCode (P : InvCfg) : List Instr :=
  ((maskOf .x16 .x4 ++ maskOf .x17 .x5 ++ lin .x4 .x5 .x16 .x17 P.sT P.sF P.sG P.L P.L) ++ shr59 P.sNF P.sT P.L) ++
  (((maskOf .x16 .x6 ++ maskOf .x17 .x7 ++ lin .x6 .x7 .x16 .x17 P.sT P.sF P.sG P.L P.L) ++ shr59 P.sNG P.sT P.L) ++
  (copyW P.sF P.sNF P.L ++ copyW P.sG P.sNG P.L))

/-- The update of `a`, `b`. -/
abbrev abCode (P : InvCfg) : List Instr :=
  ((maskOf .x16 .x4 ++ maskOf .x17 .x5 ++ lin .x4 .x5 .x16 .x17 P.sT P.sA P.sB P.M.n (P.M.n + 1)) ++
    mredC P.M P.sNF P.sT) ++
  (((maskOf .x16 .x6 ++ maskOf .x17 .x7 ++ lin .x6 .x7 .x16 .x17 P.sT P.sA P.sB P.M.n (P.M.n + 1)) ++
    mredC P.M P.sB P.sT) ++ copyW P.sA P.sNF P.M.n)

theorem update_eq (P : InvCfg) :
    (.movz .x .x12 0 0 :: P.fgUpdate) ++ P.abUpdate = ([.movz .x .x12 0 0] : List Instr) ++ (fgCode P ++ abCode P) := by
  simp only [fgCode, abCode, InvCfg.fgUpdate, InvCfg.abUpdate, InvCfg.L, List.append_assoc, List.cons_append,
    List.nil_append]

theorem Unch.wv2 {base : Addr} {a b : Nat × Nat} {m m' : Mem} (h : Unch base [a, b] m m') {d k : Nat}
    (h1 : d + 8 * k ≤ a.1 ∨ a.1 + a.2 ≤ d) (h2 : d + 8 * k ≤ b.1 ∨ b.1 + b.2 ≤ d) (hd : d + 8 * k ≤ 2 ^ 64) :
    wordsVal m' base d k = wordsVal m base d k :=
  h.wordsVal (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact h1
    · exact h2) hd

/-- A batch's words: `59` divsteps from the low words of `f`, `g` and the identity
leave `d` and the matrix in `x1`, `x4`–`x7`. -/
theorem words_ok {P : InvCfg} {base : Addr} {size : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    {I : Divstep.IState} (hI : IInv P base I s) (hd : |I.d| ≤ 2 ^ 30) (hf1 : I.f % 2 = 1)
    {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64) (h19 : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block P.batchStart) s fun s₁ => WP isa (wsteps 59) s₁ fun t =>
      let m := Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)
      t.gpr .x1 = BitVec.ofInt 64 m.d ∧ t.gpr .x4 = BitVec.ofInt 64 m.u ∧ t.gpr .x5 = BitVec.ofInt 64 m.v ∧
      t.gpr .x6 = BitVec.ofInt 64 m.q ∧ t.gpr .x7 = BitVec.ofInt 64 m.r ∧
      t.gpr .x19 = BitVec.ofNat 64 (j - 1) ∧ t.mem = s.mem ∧
      KeepRegs [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x19] s t := by
  obtain ⟨eL, eF, eG, -, -, -, -, -⟩ := slots P
  have n4 := hL.n4; have htbl := hL.tbl; have htbl8 := hL.tbl8
  refine WP.mono (batchStart_ok hs (by omega) (by omega) (by omega) (by omega) hj hj' h19)
    fun s₁ ⟨c19, c11, c12, c2, c3, c4, c5, c6, c7, m₁, k₁⟩ => ?_
  refine WP.mono (wstepsLoop_ok (N := 59) (by decide) (by decide) s₁ c11 c12) fun s₂ ⟨r₂, k₂⟩ => ?_
  have hdvd : ((2 : Int) ^ 64) ∣ ((2 ^ (64 * P.L) : Nat) : Int) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_dvd_pow 2 (by omega)
  have low : ∀ (m : Mem) (d : Nat), ((word m base d).toNat : Int) % 2 ^ 64 =
      (wordsVal m base d P.L : Int) % 2 ^ 64 := fun m d => by
    rw [eL, wordsVal]; push_cast; rw [Int.add_mul_emod_self_left]
  have hrel : (regsW s₁).rel (Divstep.MSt.init I.d I.f I.g) 64 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show s₁.gpr .x1 = _; rw [k₁.gpr _ (by decide)]; exact hI.d
    · show s₁.gpr .x4 = _; rw [c4]; simp only [Divstep.MSt.init]; decide
    · show s₁.gpr .x5 = _; rw [c5]; simp only [Divstep.MSt.init]; decide
    · show s₁.gpr .x6 = _; rw [c6]; simp only [Divstep.MSt.init]; decide
    · show s₁.gpr .x7 = _; rw [c7]; simp only [Divstep.MSt.init]; decide
    · show ((s₁.gpr .x2).toNat : Int) % 2 ^ 64 = I.f % 2 ^ 64
      rw [c2, low, ← Int.emod_emod_of_dvd _ hdvd, hI.f, Int.emod_emod_of_dvd _ hdvd]
    · show ((s₁.gpr .x3).toNat : Int) % 2 ^ 64 = I.g % 2 ^ 64
      rw [c3, low, ← Int.emod_emod_of_dvd _ hdvd, hI.g, Int.emod_emod_of_dvd _ hdvd]
  have hrel' := Divstep.wsteps_rel (K := 64) (by decide) hrel (by show |I.d| + 2 * 64 < 2 ^ 62; omega) hf1 59
    (by decide)
  rw [← r₂] at hrel'
  obtain ⟨hD, hU, hV, hQ, hR, -, -⟩ := hrel'
  exact ⟨hD, hU, hV, hQ, hR, by rw [k₂.gpr _ (by decide), c19], by rw [k₂.mem, m₁],
    (k₁.mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))⟩

/-- A batch's update of `f`, `g`, by the matrix in `x4`–`x7`. -/
theorem fgUpd_ok {P : InvCfg} {base : Addr} {size p : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hp : p < 2 ^ (64 * P.M.n)) (h12 : s.gpr .x12 = 0) {u v q r f g : Int}
    (h4 : s.gpr .x4 = BitVec.ofInt 64 u) (h5 : s.gpr .x5 = BitVec.ofInt 64 v)
    (h6 : s.gpr .x6 = BitVec.ofInt 64 q) (h7 : s.gpr .x7 = BitVec.ofInt 64 r)
    (huv : |u| + |v| ≤ 2 ^ 59) (hqr : |q| + |r| ≤ 2 ^ 59)
    (hF : (wordsVal s.mem base P.sF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = f % ((2 ^ (64 * P.L) : Nat) : Int))
    (hG : (wordsVal s.mem base P.sG P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = g % ((2 ^ (64 * P.L) : Nat) : Int))
    (hf : |f| ≤ p) (hg : |g| ≤ p) (hdf : 2 ^ 59 ∣ u * f + v * g) (hdg : 2 ^ 59 ∣ q * f + r * g) :
    WP isa (.block (fgCode P)) s fun t =>
      (wordsVal t.mem base P.sF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
        ((u * f + v * g) / 2 ^ 59) % ((2 ^ (64 * P.L) : Nat) : Int) ∧
      (wordsVal t.mem base P.sG P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
        ((q * f + r * g) / 2 ^ 59) % ((2 ^ (64 * P.L) : Nat) : Int) ∧
      KeepRegs [.x2, .x3, .x8, .x9, .x10, .x16, .x17] s t ∧
      Unch base [(P.sT, 8 * P.L), (P.sNF, 8 * P.L), (P.sNG, 8 * P.L), (P.sF, 8 * P.L), (P.sG, 8 * P.L)] s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT⟩ := slots P
  have n4 := hL.n4; have htbl := hL.tbl; have htbl8 := hL.tbl8
  have hp' : p < 2 ^ (64 * (P.L - 1)) := by rw [eL, Nat.add_sub_cancel]; exact hp
  rw [WP.block_append_iff]
  refine WP.mono (fHalf_ok hs h12 (w := .x4) (w' := .x5) (by decide) (by decide) h4 h5 huv
    (T := P.sT) (x := P.sF) (y := P.sG) (dst := P.sNF) (L := P.L) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn])
    (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn])
    hF hG hf hg hp' hdf) fun s₁ ⟨e₁, k₁, U₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have rF : wordsVal s₁.mem base P.sF P.L = wordsVal s.mem base P.sF P.L :=
    Unch.wv2 U₁ (Or.inl (show P.sF + 8 * P.L ≤ P.sT by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn])) (Or.inl (show P.sF + 8 * P.L ≤ P.sNF by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]))
      (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn])
  have rG : wordsVal s₁.mem base P.sG P.L = wordsVal s.mem base P.sG P.L :=
    Unch.wv2 U₁ (Or.inl (show P.sG + 8 * P.L ≤ P.sT by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn])) (Or.inl (show P.sG + 8 * P.L ≤ P.sNF by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]))
      (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn])
  rw [WP.block_append_iff]
  refine WP.mono (fHalf_ok hs₁ (by rw [k₁.gpr _ (by decide), h12]) (w := .x6) (w' := .x7) (by decide) (by decide)
    (by rw [k₁.gpr _ (by decide)]; exact h6) (by rw [k₁.gpr _ (by decide)]; exact h7) hqr
    (T := P.sT) (x := P.sF) (y := P.sG) (dst := P.sNG) (L := P.L) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn])
    (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn])
    (by rw [rF]; exact hF) (by rw [rG]; exact hG) hf hg hp' hdg) fun s₂ ⟨e₂, k₂, U₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have rNF : wordsVal s₂.mem base P.sNF P.L = wordsVal s₁.mem base P.sNF P.L :=
    Unch.wv2 U₂ (Or.inl (show P.sNF + 8 * P.L ≤ P.sT by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn])) (Or.inl (show P.sNF + 8 * P.L ≤ P.sNG by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]))
      (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn])
  rw [WP.block_append_iff]
  refine WP.mono (copyW_ok hs₂ (dst := P.sF) (src := P.sNF) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) P.L (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn])
    (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn])) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have rNG : wordsVal s₃.mem base P.sNG P.L = wordsVal s₂.mem base P.sNG P.L := O₃.wordsVal (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn])
  refine WP.mono (copyW_ok hs₃ (dst := P.sG) (src := P.sNG) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) P.L (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn])
    (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn])) fun t ⟨e₄, k₄, O₄⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [O₄.wordsVal (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn]), e₃, rNF]; exact e₁
  · rw [e₄, rNG]; exact e₂
  · exact (k₁.trans k₂).trans ((k₃.trans k₄).mono (by decide))
  · refine ((U₁.trans U₂).trans (O₃.unch.trans O₄.unch)).mono fun w hw => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h | h | h | h | h <;> simp only [h, true_or, or_true]

/-- A batch's update of `a`, `b`, by the matrix in `x4`–`x7`. -/
theorem abUpd_ok {P : InvCfg} {base : Addr} {size p : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOk P.M size p s.mem base) (h12 : s.gpr .x12 = 0) {u v q r a b : Int}
    (h4 : s.gpr .x4 = BitVec.ofInt 64 u) (h5 : s.gpr .x5 = BitVec.ofInt 64 v)
    (h6 : s.gpr .x6 = BitVec.ofInt 64 q) (h7 : s.gpr .x7 = BitVec.ofInt 64 r)
    (huv : |u| + |v| ≤ 2 ^ 59) (hqr : |q| + |r| ≤ 2 ^ 59)
    (hA : (wordsVal s.mem base P.sA P.M.n : Int) = a) (hB : (wordsVal s.mem base P.sB P.M.n : Int) = b)
    (ha : |a| ≤ p) (hb : |b| ≤ p) :
    WP isa (.block (abCode P)) s fun t =>
      (wordsVal t.mem base P.sA P.M.n : Int) = Divstep.mred p P.M.minv.toNat (u * a + v * b) ∧
      (wordsVal t.mem base P.sB P.M.n : Int) = Divstep.mred p P.M.minv.toNat (q * a + r * b) ∧
      KeepRegs [.x2, .x3, .x8, .x9, .x10, .x16, .x17] s t ∧
      Unch base [(P.sT, 8 * (P.M.n + 2)), (P.sNF, 8 * P.M.n), (P.sB, 8 * P.M.n), (P.sA, 8 * P.M.n)] s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT⟩ := slots P
  have n4 := hL.n4; have htbl := hL.tbl; have htbl8 := hL.tbl8; have hmt := hL.mo_tbl; have hmo := hM.mo
  rw [WP.block_append_iff]
  refine WP.mono (abHalf_ok hs hM hL.mo8 h12 (w := .x4) (w' := .x5) (by decide) (by decide) h4 h5 huv
    (T := P.sT) (x := P.sA) (y := P.sB) (dst := P.sNF) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo])
    (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) hA hB ha hb)
    fun s₁ ⟨e₁, k₁, U₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have rA : wordsVal s₁.mem base P.sA P.M.n = wordsVal s.mem base P.sA P.M.n :=
    Unch.wv2 U₁ (Or.inl (show P.sA + 8 * P.M.n ≤ P.sT by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]))
      (Or.inl (show P.sA + 8 * P.M.n ≤ P.sNF by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo])) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo])
  have rB : wordsVal s₁.mem base P.sB P.M.n = wordsVal s.mem base P.sB P.M.n :=
    Unch.wv2 U₁ (Or.inl (show P.sB + 8 * P.M.n ≤ P.sT by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]))
      (Or.inl (show P.sB + 8 * P.M.n ≤ P.sNF by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo])) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo])
  have M₁ : ModOk P.M size p s₁.mem base := ⟨hM.n0, hM.n7, hM.mo, hM.tmp, hM.sep,
    by rw [Unch.wv2 U₁ (by dsimp only; omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by dsimp only; omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo])]; exact hM.val, hM.inv, hM.red⟩
  rw [WP.block_append_iff]
  refine WP.mono (abHalf_ok hs₁ M₁ hL.mo8 (by rw [k₁.gpr _ (by decide), h12]) (w := .x6) (w' := .x7) (by decide)
    (by decide) (by rw [k₁.gpr _ (by decide)]; exact h6) (by rw [k₁.gpr _ (by decide)]; exact h7) hqr
    (T := P.sT) (x := P.sA) (y := P.sB) (dst := P.sB) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo])
    (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo])
    (by rw [rA]; exact hA) (by rw [rB]; exact hB) ha hb) fun s₂ ⟨e₂, k₂, U₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have rNF : wordsVal s₂.mem base P.sNF P.M.n = wordsVal s₁.mem base P.sNF P.M.n :=
    Unch.wv2 U₂ (Or.inl (show P.sNF + 8 * P.M.n ≤ P.sT by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]))
      (Or.inr (show P.sB + 8 * P.M.n ≤ P.sNF by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo])) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo])
  refine WP.mono (copyW_ok hs₂ (dst := P.sA) (src := P.sNF) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) P.M.n (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo])
    (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo])) fun t ⟨e₃, k₃, O₃⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [e₃, rNF]; exact e₁
  · rw [O₃.wordsVal (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo]) (by omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, n4, htbl, htbl8, hn, hmt, hmo])]; exact e₂
  · exact (k₁.trans k₂).trans (k₃.mono (by decide))
  · refine ((U₁.trans U₂).trans O₃.unch).mono fun w hw => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h | h | h | h <;> simp only [h, true_or, or_true]

/-- A batch: `59` divsteps on the low words, then `f`, `g`, `a`, `b` by their matrix. -/
theorem batch_ok {P : InvCfg} {base : Addr} {size p : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOk P.M size p s.mem base) {I : Divstep.IState} (hI : IInv P base I s)
    (hd : |I.d| ≤ 2 ^ 30) (hf1 : I.f % 2 = 1) (hf : |I.f| ≤ p) (hg : |I.g| ≤ p)
    (ha : |I.a| ≤ p) (hb : |I.b| ≤ p) {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa P.batch s fun t =>
      IInv P base (Divstep.batch 59 p P.M.minv.toNat I) t ∧ t.gpr .x19 = BitVec.ofNat 64 (j - 1) ∧
      KeepRegs [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x16, .x17, .x19] s t ∧
      Unch base (batchW P) s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT⟩ := slots P
  have n4 := hL.n4; have htbl := hL.tbl; have htbl8 := hL.tbl8
  have hp : p < 2 ^ (64 * P.M.n) := hM.val ▸ wordsVal_lt _ _ _ _
  obtain ⟨buv, bqr⟩ := Divstep.msteps_bnd I.d I.f I.g 59
  obtain ⟨mf, mg⟩ := Divstep.msteps_mat (d := I.d) (g := I.g) hf1 59
  rw [InvCfg.batch]
  refine WP.seq (WP.mono (words_ok hL hs hI hd hf1 hj hj' h19) fun s₁ h₁ => WP.seq (WP.mono h₁ fun s₂ h₂ => ?_))
  obtain ⟨hD, hU, hV, hQ, hR, c19, m₂, k₂⟩ := h₂
  have hs₂ := hs.of_keepRegs k₂ (by decide)
  rw [update_eq, WP.block_append_iff]
  refine WP.mono (movzI_ok s₂ .x12 0) fun s₃ ⟨c12, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have z₃ : s₃.gpr .x12 = 0 := by rw [c12]; rfl
  have m₃ : s₃.mem = s.mem := by rw [k₃.mem, m₂]
  rw [WP.block_append_iff]
  refine WP.mono (fgUpd_ok hL hs₃ hp z₃ (u := _) (v := _) (q := _) (r := _)
    (by rw [k₃.gpr _ (by decide)]; exact hU) (by rw [k₃.gpr _ (by decide)]; exact hV)
    (by rw [k₃.gpr _ (by decide)]; exact hQ) (by rw [k₃.gpr _ (by decide)]; exact hR) buv bqr
    (by rw [m₃]; exact hI.f) (by rw [m₃]; exact hI.g) hf hg ⟨_, mf.symm⟩ ⟨_, mg.symm⟩)
    fun s₄ ⟨eF₄, eG₄, k₄, U₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have g₄ : ∀ r ∉ [Reg.x2, .x3, .x8, .x9, .x10, .x16, .x17], s₄.gpr r = s₃.gpr r := k₄.gpr
  have rd₄ : ∀ {d k : Nat}, d + 8 * k ≤ P.sNF → P.sG + 8 * P.L ≤ d → d + 8 * k ≤ size →
      wordsVal s₄.mem base d k = wordsVal s₃.mem base d k := fun h1 h2 h3 =>
    U₄.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
        omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, h1, h2]) (by omega_using [h3, hn])
  have M₄ : ModOk P.M size p s₄.mem base := ⟨hM.n0, hM.n7, hM.mo, hM.tmp, hM.sep,
    by
      rw [U₄.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        have hmt := hL.mo_tbl
        rcases hw with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
          omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, hmt, n4]) (by have := hM.mo; omega_using [this, hn]), m₃]
      exact hM.val, hM.inv, hM.red⟩
  refine WP.mono (abUpd_ok hL hs₄ M₄ (by rw [g₄ _ (by decide), z₃]) (u := _) (v := _) (q := _) (r := _)
    (by rw [g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hU) (by rw [g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hV)
    (by rw [g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hQ) (by rw [g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hR)
    buv bqr (by rw [rd₄ (by omega) (by omega) (by omega), m₃]; exact hI.a)
    (by rw [rd₄ (by omega) (by omega) (by omega), m₃]; exact hI.b) ha hb) fun t ⟨eA₅, eB₅, k₅, U₅⟩ => ?_
  have rd₅ : ∀ {d k : Nat}, d + 8 * k ≤ P.sA → d + 8 * k ≤ size →
      wordsVal t.mem base d k = wordsVal s₄.mem base d k := fun h1 h3 =>
    U₅.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> dsimp only <;>
        omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, h1]) (by omega_using [h3, hn])
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [Divstep.batch]
    rw [k₅.gpr _ (by decide), g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hD
  · simp only [Divstep.batch]
    rw [rd₅ (by omega) (by omega)]; exact eF₄
  · simp only [Divstep.batch]
    rw [rd₅ (by omega) (by omega)]; exact eG₄
  · simp only [Divstep.batch]; exact eA₅
  · simp only [Divstep.batch]; exact eB₅
  · rw [k₅.gpr _ (by decide), g₄ _ (by decide), k₃.gpr _ (by decide)]; exact c19
  · refine (((k₂.mono ?_).trans ((Keeps.regs k₃).mono ?_)).trans (k₄.mono ?_)).trans (k₅.mono ?_) <;> decide
  · have U := U₄.trans U₅
    rw [m₃] at U
    refine (U.outside fun w hw => ?_).unch
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
      omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT]

end VG.Proof.Weierstrass.AArch64
