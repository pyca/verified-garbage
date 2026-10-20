module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvBatchStart
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvRed
public import VerifiedGarbage.Proof.Divstep.TcS
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvPacked
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvWords
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Inversion by divsteps on AArch64: a batch

The signed linear combinations of a batch as integers modulo the words'
range (`linM_ok`), the shift by 59 of a multiple of `2^59` (`shrM_ok`), and a
batch: `59` divsteps on the low words, then `f`, `g`, `a`, `b` updated by
their matrix, as `Divstep.batch` (`batch_ok`). For `InvCfg.inv`, the same with
`a`, `b` signed in `n + 1` words: one word of Montgomery reduction left signed
(`mredS_ok`, `Divstep.mredRaw`), a signed number in `(-p, 2p)` brought into
`[0, p)` at the end (`normC_ok`, `Divstep.norm`), and a batch as
`Divstep.batchS` (`batchS_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

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
  · have := shifted_cong s.mem base x (k := k) (K := K) (by omega_using [hk']) (by omega_using [hK]); push_cast at this; exact this
  · have := shifted_cong s.mem base y (k := k) (K := K) (by omega_using [hk']) (by omega_using [hK]); push_cast at this; exact this
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
  obtain ⟨j, rfl⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega_using [hL]⟩
  simp only [Nat.add_sub_cancel] at hy1 hy2 ⊢
  have hQ : 2 ^ (64 * (j + 1)) = 2 * (2 ^ (64 * j) * 2 ^ 63) := by
    rw [pow64_succ, show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl]; ring
  rw [sext, Nat.add_sub_cancel, sgnW_top, hQ] at e
  rw [hQ] at hy ⊢
  exact Divstep.shr_nat (c := 2 ^ 59) (B := 2 ^ 64) rfl rfl (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
    (by have := wordsVal_lt s.mem base src (j + 1); rw [hQ] at this; exact this) hy hy1 hy2 hz e

theorem modOk_out {M : Mod} {size p : Nat} {mem mem' : Mem} {base : Addr} (hM : ModOkA M size p mem base) {o len : Nat}
    (hO : Outside base o len mem mem') (hsep : o + len ≤ M.mo ∨ M.mo + 8 * M.n ≤ o) (hn : base.toNat + size ≤ 2 ^ 64) :
    ModOkA M size p mem' base :=
  ⟨hM.n0, hM.n10, hM.mo, hM.tmp, hM.sep, by rw [hO.wordsVal (by omega_using [hsep]) (by have := hM.mo; omega_using [hn, this])]; exact hM.val,
    hM.inv, hM.red, hM.call⟩

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
  refine WP.mono (linM_ok hs h12 hw hw' (k := L) (K := L) (by omega_using [hL]) (Nat.le_refl _) hL (by omega_using []) hx hx8 hy hy8
    hT hT8 hTx hTy) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [hu, hv, Divstep.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv), Divstep.cong_comb hf hg] at e₁
  obtain ⟨b1, b2⟩ := Divstep.comb_range (A := 2 ^ (64 * (L - 1))) huv hfb hgb hp
  refine WP.mono (shrM_ok hs₁ (by rw [k₁.gpr _ (by decide), h12]) (dst := dst) (src := T) (by omega_using [hL]) hT hT8 hd hd8
    hdT e₁ b1 b2 (Int.mul_ediv_cancel' hdiv).symm) fun t ⟨e, k, O⟩ =>
      ⟨e, k₁.trans (k.mono (by decide)), (O₁.unch.trans O.unch).mono fun w hw => by simpa using hw⟩

/-- Half a batch's update of `a`, `b`: `[dst] = mred (u a + v b)` (`n` words). -/
theorem abHalf_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {p : Nat}
    (hM : ModOkA M size p s.mem base) (hmo8 : M.mo % 8 = 0) (h12 : s.gpr .x12 = 0)
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
  refine WP.mono (linM_ok hs h12 hw hw' (k := M.n) (K := M.n + 1) (by omega_using [hn0]) (by omega_using []) (by omega_using [hn0]) (by omega_using []) hx hx8
    hy hy8 (by omega_using [hT]) hT8 (by omega_using [hTx]) (by omega_using [hTy])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [hu, hv, Divstep.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv), ha, hb] at e₁
  have hM₁ := modOk_out hM O₁ (by omega_using [hTm]) hn
  have hT' : |u * a + v * b| ≤ 2 ^ 63 * (p : Int) := by
    have := Divstep.comb_le huv ha0 hb0
    exact le_trans this (Int.mul_le_mul_of_nonneg_right (by omega_using []) (Int.natCast_nonneg _))
  refine WP.mono (mredC_ok hs₁ hM₁ hmo8 (by rw [k₁.gpr _ (by decide), h12]) hT hT8 hd hd8 hTm hdT hT' e₁)
    fun t ⟨e, k, m₁, Ot, Od⟩ => ⟨e, k₁.trans k, ?_⟩
  exact ((O₁.mono (n' := 8 * (M.n + 2)) (Nat.le_refl _) (by omega_using [])).unch.trans (Ot.unch.trans Od.unch)).mono
    fun w hw => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h | h <;> simp [h]

/-! ## A batch -/

/-- The update of `f`, `g`, staged in `[nf]`, `[ng]`, through `[t]`. -/
abbrev fgCodeAt (P : InvCfg) (nf ng t : Nat) : List Instr :=
  ((maskOf .x16 .x4 ++ maskOf .x17 .x5 ++ lin .x4 .x5 .x16 .x17 t P.sF P.sG P.L P.L) ++ shr59 nf t P.L) ++
  (((maskOf .x16 .x6 ++ maskOf .x17 .x7 ++ lin .x6 .x7 .x16 .x17 t P.sF P.sG P.L P.L) ++ shr59 ng t P.L) ++
  (copyW P.sF nf P.L ++ copyW P.sG ng P.L))

theorem fgUpdateAt_eq (P : InvCfg) (nf ng t : Nat) : P.fgUpdateAt nf ng t = fgCodeAt P nf ng t := by
  simp only [fgCodeAt, InvCfg.fgUpdateAt, List.append_assoc]

/-- The update of `f`, `g`. -/
abbrev fgCode (P : InvCfg) : List Instr := fgCodeAt P P.sNF P.sNG P.sT

/-- The update of `a`, `b`. -/
abbrev abCode (P : InvCfg) : List Instr :=
  ((maskOf .x16 .x4 ++ maskOf .x17 .x5 ++ lin .x4 .x5 .x16 .x17 P.sT P.sA P.sB P.M.n (P.M.n + 1)) ++
    mredC P.M P.sNF P.sT) ++
  (((maskOf .x16 .x6 ++ maskOf .x17 .x7 ++ lin .x6 .x7 .x16 .x17 P.sT P.sA P.sB P.M.n (P.M.n + 1)) ++
    mredC P.M P.sB P.sT) ++ copyW P.sA P.sNF P.M.n)

theorem update_eq (P : InvCfg) :
    (.movz .x .x12 0 0 :: P.fgUpdate) ++ P.abUpdate = ([.movz .x .x12 0 0] : List Instr) ++ (fgCode P ++ abCode P) := by
  simp only [fgCode, abCode, InvCfg.fgUpdate, InvCfg.fgUpdateAt, InvCfg.abUpdate, InvCfg.L, List.append_assoc, List.cons_append,
    List.nil_append]

theorem Unch.wv2 {base : Addr} {a b : Nat × Nat} {m m' : Mem} (h : Unch base [a, b] m m') {d k : Nat}
    (h1 : d + 8 * k ≤ a.1 ∨ a.1 + a.2 ≤ d) (h2 : d + 8 * k ≤ b.1 ∨ b.1 + b.2 ≤ d) (hd : d + 8 * k ≤ 2 ^ 64) :
    wordsVal m' base d k = wordsVal m base d k :=
  h.wordsVal (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact h1
    · exact h2) hd

/-- A batch's words: `59` packed divsteps from the low words of `f`, `g`
leave `d` and the matrix in `x1`, `x4`–`x7`. -/
theorem words_ok {P : InvCfg} {base : Addr} {size : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    {I : Divstep.IState} (hI : IInv P base I s) (hd : |I.d| ≤ 2 ^ 30) (hf1 : I.f % 2 = 1)
    {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64) (h19 : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block P.batchStart) s fun s₁ => WP isa (.block pwords) s₁ fun t =>
      let m := Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)
      t.gpr .x1 = BitVec.ofInt 64 m.d ∧ t.gpr .x4 = BitVec.ofInt 64 m.u ∧ t.gpr .x5 = BitVec.ofInt 64 m.v ∧
      t.gpr .x6 = BitVec.ofInt 64 m.q ∧ t.gpr .x7 = BitVec.ofInt 64 m.r ∧
      t.gpr .x19 = BitVec.ofNat 64 (j - 1) ∧ t.mem = s.mem ∧
      KeepRegs [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x16, .x17, .x19] s t := by
  obtain ⟨eL, eF, eG, -, -, -, -, -⟩ := slots P
  have n4 := hL.n4; have htbl := hL.tbl; have htbl8 := hL.tbl8
  refine WP.mono (batchStart_ok hs (by omega_using [eF, n4, htbl]) (by omega_using [eF, htbl8]) (by omega_using [eG, n4, htbl]) (by omega_using [eG, htbl8]) hj hj' h19)
    fun s₁ ⟨c19, _, _, c2, c3, _, _, _, _, m₁, k₁⟩ => ?_
  have hdvd : ((2 : Int) ^ 64) ∣ ((2 ^ (64 * P.L) : Nat) : Int) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_dvd_pow 2 (by omega_using [eL])
  have low : ∀ (m : Mem) (d : Nat), ((word m base d).toNat : Int) % 2 ^ 64 =
      (wordsVal m base d P.L : Int) % 2 ^ 64 := fun m d => by
    rw [eL, wordsVal]; push_cast; rw [Int.add_mul_emod_self_left]
  refine WP.mono (pwords_ok s₁ (g := I.g) hd hf1 (by rw [k₁.gpr _ (by decide)]; exact hI.d)
    (by rw [c2, low, ← Int.emod_emod_of_dvd _ hdvd, hI.f, Int.emod_emod_of_dvd _ hdvd])
    (by rw [c3, low, ← Int.emod_emod_of_dvd _ hdvd, hI.g, Int.emod_emod_of_dvd _ hdvd]))
    fun t ⟨hD, hU, hV, hQ, hR, k₂⟩ => ?_
  exact ⟨hD, hU, hV, hQ, hR, by rw [k₂.gpr _ (by decide), c19], by rw [k₂.mem, m₁],
    (k₁.mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))⟩

/-- A batch's update of `f`, `g`, by the matrix in `x4`–`x7`, staged in `[nf]`, `[ng]`
through `[t]`, past `g` in the table. -/
theorem fgUpdAt_ok {P : InvCfg} {nf ng t : Nat} {base : Addr} {size p : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hnf : P.sG + 8 * P.L ≤ nf) (hng : nf + 8 * P.L ≤ ng) (htt : ng + 8 * P.L ≤ t)
    (hte : t + 8 * P.L ≤ P.tbl + 9 * (8 * P.M.n)) (hnf8 : nf % 8 = 0) (hng8 : ng % 8 = 0) (ht8 : t % 8 = 0)
    (hp : p < 2 ^ (64 * P.M.n)) (h12 : s.gpr .x12 = 0) {u v q r f g : Int}
    (h4 : s.gpr .x4 = BitVec.ofInt 64 u) (h5 : s.gpr .x5 = BitVec.ofInt 64 v)
    (h6 : s.gpr .x6 = BitVec.ofInt 64 q) (h7 : s.gpr .x7 = BitVec.ofInt 64 r)
    (huv : |u| + |v| ≤ 2 ^ 59) (hqr : |q| + |r| ≤ 2 ^ 59)
    (hF : (wordsVal s.mem base P.sF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = f % ((2 ^ (64 * P.L) : Nat) : Int))
    (hG : (wordsVal s.mem base P.sG P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = g % ((2 ^ (64 * P.L) : Nat) : Int))
    (hf : |f| ≤ p) (hg : |g| ≤ p) (hdf : 2 ^ 59 ∣ u * f + v * g) (hdg : 2 ^ 59 ∣ q * f + r * g) :
    WP isa (.block (fgCodeAt P nf ng t)) s fun t' =>
      (wordsVal t'.mem base P.sF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
        ((u * f + v * g) / 2 ^ 59) % ((2 ^ (64 * P.L) : Nat) : Int) ∧
      (wordsVal t'.mem base P.sG P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
        ((q * f + r * g) / 2 ^ 59) % ((2 ^ (64 * P.L) : Nat) : Int) ∧
      KeepRegs [.x2, .x3, .x8, .x9, .x10, .x16, .x17] s t' ∧
      Unch base [(t, 8 * P.L), (nf, 8 * P.L), (ng, 8 * P.L), (P.sF, 8 * P.L), (P.sG, 8 * P.L)] s.mem t'.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, -, -, -, -, -⟩ := slots P
  have n4 := hL.n4; have htbl := hL.tbl; have htbl8 := hL.tbl8
  have hp' : p < 2 ^ (64 * (P.L - 1)) := by rw [eL, Nat.add_sub_cancel]; exact hp
  rw [WP.block_append_iff]
  refine WP.mono (fHalf_ok hs h12 (w := .x4) (w' := .x5) (by decide) (by decide) h4 h5 huv
    (T := t) (x := P.sF) (y := P.sG) (dst := nf) (L := P.L) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    hF hG hf hg hp' hdf) fun s₁ ⟨e₁, k₁, U₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have rF : wordsVal s₁.mem base P.sF P.L = wordsVal s.mem base P.sF P.L :=
    Unch.wv2 U₁ (Or.inl (show P.sF + 8 * P.L ≤ t by omega_arith)) (Or.inl (show P.sF + 8 * P.L ≤ nf by omega_arith))
      (by omega_arith)
  have rG : wordsVal s₁.mem base P.sG P.L = wordsVal s.mem base P.sG P.L :=
    Unch.wv2 U₁ (Or.inl (show P.sG + 8 * P.L ≤ t by omega_arith)) (Or.inl (show P.sG + 8 * P.L ≤ nf by omega_arith))
      (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (fHalf_ok hs₁ (by rw [k₁.gpr _ (by decide), h12]) (w := .x6) (w' := .x7) (by decide) (by decide)
    (by rw [k₁.gpr _ (by decide)]; exact h6) (by rw [k₁.gpr _ (by decide)]; exact h7) hqr
    (T := t) (x := P.sF) (y := P.sG) (dst := ng) (L := P.L) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by rw [rF]; exact hF) (by rw [rG]; exact hG) hf hg hp' hdg) fun s₂ ⟨e₂, k₂, U₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have rNF : wordsVal s₂.mem base nf P.L = wordsVal s₁.mem base nf P.L :=
    Unch.wv2 U₂ (Or.inl (show nf + 8 * P.L ≤ t by omega_arith)) (Or.inl (show nf + 8 * P.L ≤ ng by omega_arith))
      (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (copyW_ok hs₂ (dst := P.sF) (src := nf) (by omega_arith) (by omega_arith) P.L (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have rNG : wordsVal s₃.mem base ng P.L = wordsVal s₂.mem base ng P.L := O₃.wordsVal (by omega_arith) (by omega_arith)
  refine WP.mono (copyW_ok hs₃ (dst := P.sG) (src := ng) (by omega_arith) (by omega_arith) P.L (by omega_arith) (by omega_arith)
    (by omega_arith)) fun t' ⟨e₄, k₄, O₄⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [O₄.wordsVal (by omega_arith) (by omega_arith), e₃, rNF]; exact e₁
  · rw [e₄, rNG]; exact e₂
  · exact (k₁.trans k₂).trans ((k₃.trans k₄).mono (by decide))
  · refine ((U₁.trans U₂).trans (O₃.unch.trans O₄.unch)).mono fun w hw => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h | h | h | h | h <;> simp only [h, true_or, or_true]

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
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT⟩ := slots P
  have n4 := hL.n4; have htbl8 := hL.tbl8
  exact fgUpdAt_ok hL hs (by omega_using [eL, eG, eNF]) (by omega_using [eL, eNF, eNG])
    (by omega_using [eL, eNG, eT]) (by omega_using [eL, eT, n4]) (by omega_using [eNF, htbl8])
    (by omega_using [eNG, htbl8]) (by omega_using [eT, htbl8]) hp h12 h4 h5 h6 h7 huv hqr hF hG hf hg hdf hdg

/-- A batch's update of `a`, `b`, by the matrix in `x4`–`x7`. -/
theorem abUpd_ok {P : InvCfg} {base : Addr} {size p : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkA P.M size p s.mem base) (h12 : s.gpr .x12 = 0) {u v q r a b : Int}
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
    (T := P.sT) (x := P.sA) (y := P.sB) (dst := P.sNF) (by omega_using [eA, n4, htbl]) (by omega_using [eA, htbl8]) (by omega_using [eB, n4, htbl]) (by omega_using [eB, htbl8]) (by omega_using [eT, n4, htbl])
    (by omega_using [eT, htbl8]) (by omega_using [eNF, n4, htbl]) (by omega_using [eNF, htbl8]) (by omega_using [eA, eT]) (by omega_using [eB, eT]) (by omega_using [eNF, eT]) (by omega_using [eT, n4, hmt]) hA hB ha hb)
    fun s₁ ⟨e₁, k₁, U₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have rA : wordsVal s₁.mem base P.sA P.M.n = wordsVal s.mem base P.sA P.M.n :=
    Unch.wv2 U₁ (Or.inl (show P.sA + 8 * P.M.n ≤ P.sT by omega_using [eA, eT]))
      (Or.inl (show P.sA + 8 * P.M.n ≤ P.sNF by omega_using [eA, eNF])) (by omega_using [eA, n4, htbl, hn])
  have rB : wordsVal s₁.mem base P.sB P.M.n = wordsVal s.mem base P.sB P.M.n :=
    Unch.wv2 U₁ (Or.inl (show P.sB + 8 * P.M.n ≤ P.sT by omega_using [eB, eT]))
      (Or.inl (show P.sB + 8 * P.M.n ≤ P.sNF by omega_using [eB, eNF])) (by omega_using [eB, n4, htbl, hn])
  have M₁ : ModOkA P.M size p s₁.mem base := ⟨hM.n0, hM.n10, hM.mo, hM.tmp, hM.sep,
    by rw [Unch.wv2 U₁ (by dsimp only; omega_using [eT, n4, hmt]) (by dsimp only; omega_using [eNF, hmt]) (by omega_using [hn, hmo])]; exact hM.val, hM.inv, hM.red, hM.call⟩
  rw [WP.block_append_iff]
  refine WP.mono (abHalf_ok hs₁ M₁ hL.mo8 (by rw [k₁.gpr _ (by decide), h12]) (w := .x6) (w' := .x7) (by decide)
    (by decide) (by rw [k₁.gpr _ (by decide)]; exact h6) (by rw [k₁.gpr _ (by decide)]; exact h7) hqr
    (T := P.sT) (x := P.sA) (y := P.sB) (dst := P.sB) (by omega_using [eA, n4, htbl]) (by omega_using [eA, htbl8]) (by omega_using [eB, n4, htbl]) (by omega_using [eB, htbl8]) (by omega_using [eT, n4, htbl])
    (by omega_using [eT, htbl8]) (by omega_using [eB, n4, htbl]) (by omega_using [eB, htbl8]) (by omega_using [eA, eT]) (by omega_using [eB, eT]) (by omega_using [eB, eT]) (by omega_using [eT, n4, hmt])
    (by rw [rA]; exact hA) (by rw [rB]; exact hB) ha hb) fun s₂ ⟨e₂, k₂, U₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have rNF : wordsVal s₂.mem base P.sNF P.M.n = wordsVal s₁.mem base P.sNF P.M.n :=
    Unch.wv2 U₂ (Or.inl (show P.sNF + 8 * P.M.n ≤ P.sT by omega_using [eNF, eT]))
      (Or.inr (show P.sB + 8 * P.M.n ≤ P.sNF by omega_using [eB, eNF])) (by omega_using [eNF, n4, htbl, hn])
  refine WP.mono (copyW_ok hs₂ (dst := P.sA) (src := P.sNF) (by omega_using [eNF, htbl8]) (by omega_using [eA, htbl8]) P.M.n (by omega_using [eNF, n4, htbl]) (by omega_using [eA, n4, htbl])
    (by omega_using [eA, eNF])) fun t ⟨e₃, k₃, O₃⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [e₃, rNF]; exact e₁
  · rw [O₃.wordsVal (by omega_using [eA, eB]) (by omega_using [eB, n4, htbl, hn])]; exact e₂
  · exact (k₁.trans k₂).trans (k₃.mono (by decide))
  · refine ((U₁.trans U₂).trans O₃.unch).mono fun w hw => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h | h | h | h <;> simp only [h, true_or, or_true]

/-- A batch: `59` divsteps on the low words, then `f`, `g`, `a`, `b` by their matrix. -/
theorem batch_ok {P : InvCfg} {base : Addr} {size p : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkA P.M size p s.mem base) {I : Divstep.IState} (hI : IInv P base I s)
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
        omega_using [eNF, eT, h1, eNG, eF, eG, h2]) (by omega_using [h3, hn])
  have M₄ : ModOkA P.M size p s₄.mem base := ⟨hM.n0, hM.n10, hM.mo, hM.tmp, hM.sep,
    by
      rw [U₄.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        have hmt := hL.mo_tbl
        rcases hw with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
          omega_using [eL, eT, hmt, n4, eNF, eNG, eF, eG]) (by have := hM.mo; omega_using [this, hn]), m₃]
      exact hM.val, hM.inv, hM.red, hM.call⟩
  refine WP.mono (abUpd_ok hL hs₄ M₄ (by rw [g₄ _ (by decide), z₃]) (u := _) (v := _) (q := _) (r := _)
    (by rw [g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hU) (by rw [g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hV)
    (by rw [g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hQ) (by rw [g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hR)
    buv bqr (by rw [rd₄ (by omega_using [eA, eNF]) (by omega_using [eL, eG, eA]) (by omega_using [eA, n4, htbl]), m₃]; exact hI.a)
    (by rw [rd₄ (by omega_using [eB, eNF]) (by omega_using [eL, eG, eB]) (by omega_using [eB, n4, htbl]), m₃]; exact hI.b) ha hb) fun t ⟨eA₅, eB₅, k₅, U₅⟩ => ?_
  have rd₅ : ∀ {d k : Nat}, d + 8 * k ≤ P.sA → d + 8 * k ≤ size →
      wordsVal t.mem base d k = wordsVal s₄.mem base d k := fun h1 h3 =>
    U₅.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> dsimp only <;>
        omega_using [eA, eT, h1, eNF, eB]) (by omega_using [h3, hn])
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [Divstep.batch]
    rw [k₅.gpr _ (by decide), g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hD
  · simp only [Divstep.batch]
    rw [rd₅ (by omega_using [eL, eF, eA]) (by omega_using [eL, eF, n4, htbl])]; exact eF₄
  · simp only [Divstep.batch]
    rw [rd₅ (by omega_using [eL, eG, eA]) (by omega_using [eL, eG, n4, htbl])]; exact eG₄
  · simp only [Divstep.batch]; exact eA₅
  · simp only [Divstep.batch]; exact eB₅
  · rw [k₅.gpr _ (by decide), g₄ _ (by decide), k₃.gpr _ (by decide)]; exact c19
  · refine (((k₂.mono ?_).trans ((Keeps.regs k₃).mono ?_)).trans (k₄.mono ?_)).trans (k₅.mono ?_) <;> decide
  · have U := U₄.trans U₅
    rw [m₃] at U
    refine (U.outside fun w hw => ?_).unch
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
      omega_using [eL, eT, eNF, eNG, eF, eG, eB, eA]

/-! ## Signed coefficients -/

/-- `[t + 8]` (`n + 1` words) holding `r ∈ (-p, 2p)` becomes `norm p r`, in `[0, p)`. -/
theorem normC_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {p : Nat}
    (hM : ModOkA M size p s.mem base) (hmo8 : M.mo % 8 = 0) (h12 : s.gpr .x12 = 0) {t : Nat}
    (ht : t + 8 * (M.n + 2) ≤ size) (ht8 : t % 8 = 0) (htm : t + 8 * (M.n + 2) ≤ M.mo ∨ M.mo + 8 * M.n ≤ t)
    {r : Int} (hr0 : -(p : Int) < r) (hr1 : r < 2 * p)
    (hR : (wordsVal s.mem base (t + 8) (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
      r % ((2 ^ (64 * (M.n + 1)) : Nat) : Int)) :
    WP isa (.block (normC M t)) s fun u =>
      (wordsVal u.mem base (t + 8) (M.n + 1) : Int) = Divstep.norm p r ∧
      KeepRegs [.x2, .x3, .x9] s u ∧ Outside base (t + 8) (8 * (M.n + 1)) s.mem u.mem := by
  have hn := hs.nowrap
  have hP : wordsVal s.mem base M.mo M.n = p := hM.val
  have hmo := hM.mo
  simp only [normC, List.append_assoc]
  -- `r`'s sign.
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs (d := t + 8 * (M.n + 1)) (by omega_arith) (by omega_arith) .x3) fun s₃ ⟨l₃, k₃, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sgnMask_ok s₃ (by rw [k₃.gpr _ (by decide), h12])) fun s₄ ⟨g₄, mk₄, k₄, _⟩ => ?_
  have hs₄ := (hs.of_keeps k₃ (by decide)).of_keeps k₄ (by decide)
  have z₄ : s₄.gpr .x12 = 0 := by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), h12]
  have m₄ : s₄.mem = s.mem := by rw [k₄.mem, k₃.mem]
  -- `R₁ = R + (p if negative)`.
  rw [WP.block_append_iff]
  refine WP.mono (chainAdd_ok hs₄ (m := some .x9) ⟨by decide, mk₄⟩ z₄ (d := t + 8) (mo := M.mo) (n := M.n) hmo
    hmo8 (by omega_arith) (by omega_arith) (by omega_arith)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  have z₅ : s₅.gpr .x12 = 0 := by rw [k₅.gpr _ (by decide), z₄]
  have P₅ : wordsVal s₅.mem base M.mo M.n = p := by rw [O₅.wordsVal (by omega_arith) (by omega_arith), m₄, hP]
  -- `R₂ = R₁ - p`.
  rw [WP.block_append_iff]
  refine WP.mono (chainSub_ok hs₅ z₅ (d := t + 8) (mo := M.mo) (n := M.n) hmo hmo8 (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  have z₆ : s₆.gpr .x12 = 0 := by rw [k₆.gpr _ (by decide), z₅]
  have P₆ : wordsVal s₆.mem base M.mo M.n = p := by rw [O₆.wordsVal (by omega_arith) (by omega_arith), P₅]
  -- `R₂`'s sign.
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs₆ (d := t + 8 * (M.n + 1)) (by omega_arith) (by omega_arith) .x3) fun s₇ ⟨l₇, k₇, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sgnMask_ok s₇ (by rw [k₇.gpr _ (by decide), z₆])) fun s₈ ⟨g₈, mk₈, k₈, _⟩ => ?_
  have hs₈ := (hs₆.of_keeps k₇ (by decide)).of_keeps k₈ (by decide)
  have z₈ : s₈.gpr .x12 = 0 := by rw [k₈.gpr _ (by decide), k₇.gpr _ (by decide), z₆]
  have m₈ : s₈.mem = s₆.mem := by rw [k₈.mem, k₇.mem]
  -- `R₃ = R₂ + (p if negative)`.
  refine WP.mono (chainAdd_ok hs₈ (m := some .x9) ⟨by decide, mk₈⟩ z₈ (d := t + 8) (mo := M.mo) (n := M.n) hmo
    hmo8 (by omega_arith) (by omega_arith) (by omega_arith)) fun u ⟨e₉, k₉, O₉⟩ => ?_
  refine ⟨?_, ((((((Keeps.regs k₃).mono (by decide)).trans ((Keeps.regs k₄).mono (by decide))).trans
    (k₅.mono (by decide))).trans (k₆.mono (by decide))).trans ((Keeps.regs k₇).mono (by decide))).trans
    (((Keeps.regs k₈).mono (by decide)).trans (k₉.mono (by decide))), fun x hx => ?_⟩
  rotate_left
  · rw [O₉ x hx, m₈, O₆ x hx, O₅ x hx, m₄]
  -- The arithmetic.
  have hpA : p < 2 ^ (64 * M.n) := hP ▸ wordsVal_lt _ _ _ _
  have hQ : 2 ^ (64 * (M.n + 1)) = 2 ^ (64 * M.n) * 2 ^ 64 := by rw [pow64_succ, Nat.mul_comm]
  have l₃' : s₃.gpr .x3 = word s.mem base (t + 8 + 8 * M.n) := by
    rw [l₃, show t + 8 * (M.n + 1) = t + 8 + 8 * M.n by omega_arith]
  have l₇' : s₇.gpr .x3 = word s₆.mem base (t + 8 + 8 * M.n) := by
    rw [l₇, show t + 8 * (M.n + 1) = t + 8 + 8 * M.n by omega_arith]
  exact Divstep.norm_nat (A := 2 ^ (64 * M.n)) (B := 2 ^ 64) (H := 2 ^ 63) (p := p) (r := r)
    (R := wordsVal s.mem base (t + 8) (M.n + 1)) (R₁ := wordsVal s₅.mem base (t + 8) (M.n + 1))
    (R₂ := wordsVal s₆.mem base (t + 8) (M.n + 1)) (R₃ := wordsVal u.mem base (t + 8) (M.n + 1))
    rfl rfl (Nat.two_pow_pos _) hpA hr0 hr1 (hQ ▸ wordsVal_lt _ _ _ _) (by rw [← hQ]; exact hR)
    (by rw [e₅]; simp only [mk]; rw [masked_top (by rw [g₄, l₃']), m₄, hP, hQ])
    (hQ ▸ wordsVal_lt _ _ _ _) (by rw [P₅, hQ] at e₆; exact e₆)
    (by rw [e₉]; simp only [mk]; rw [masked_top (by rw [g₈, l₇']), m₈, P₆, hQ])

/-- `[dst] ≡ mredRaw p m T` (`n + 1` words, signed), for `[t]` (`n + 1` words)
holding `T`, `|T| ≤ 2^63 p`. -/
theorem mredS_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {p : Nat}
    (hM : ModOkA M size p s.mem base) (hmo8 : M.mo % 8 = 0) (h12 : s.gpr .x12 = 0) {dst t : Nat}
    (ht : t + 8 * (M.n + 2) ≤ size) (ht8 : t % 8 = 0) (hd : dst + 8 * (M.n + 1) ≤ size) (hd8 : dst % 8 = 0)
    (htm : t + 8 * (M.n + 2) ≤ M.mo ∨ M.mo + 8 * M.n ≤ t)
    (hdt : dst + 8 * (M.n + 1) ≤ t ∨ t + 8 * (M.n + 2) ≤ dst)
    {T : Int} (hT : |T| ≤ 2 ^ 63 * p)
    (hW : (wordsVal s.mem base t (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
      T % ((2 ^ (64 * (M.n + 1)) : Nat) : Int)) :
    WP isa (.block (mredS M dst t)) s fun u =>
      (wordsVal u.mem base dst (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
        Divstep.mredRaw p M.minv.toNat T % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) ∧
      KeepRegs [.x2, .x3, .x8, .x9, .x10, .x16, .x17] s u ∧
      ∃ m₁, Outside base t (8 * (M.n + 2)) s.mem m₁ ∧ Outside base dst (8 * (M.n + 1)) m₁ u.mem := by
  have hn := hs.nowrap
  have hP : wordsVal s.mem base M.mo M.n = p := hM.val
  have hmo := hM.mo
  simp only [mredS, List.append_assoc]
  -- `x16 = k`, `[t]` sign-extended.
  rw [WP.block_append_iff]
  refine WP.mono (mredHead_ok hs h12 ht ht8) fun s₁ ⟨x₁, e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have z₁ : s₁.gpr .x12 = 0 := by rw [k₁.gpr _ (by decide), h12]
  have P₁ : wordsVal s₁.mem base M.mo M.n = p := by rw [O₁.wordsVal (by omega_arith) (by omega_arith), hP]
  -- `[t] += k p`.
  rw [WP.block_append_iff]
  refine WP.mono (mulAdd_ok hs₁ (w := .x16) (by decide) z₁ (dst := t) (src := M.mo) (k := M.n) (K := M.n + 2)
    (by omega_arith) hmo hmo8 ht ht8 htm) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  -- `[dst] = R`.
  refine WP.mono (copyW_ok hs₂ (dst := dst) (src := t + 8) (by omega_arith) hd8 (M.n + 1) (by omega_arith) hd
    (by omega_arith)) fun u ⟨eu, ku, Ou⟩ => ?_
  refine ⟨?_, ((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans (ku.mono (by decide)), s₂.mem,
    fun x hx => by rw [O₂ x hx, O₁ x (by omega_arith)], Ou⟩
  -- The arithmetic.
  have hp0 : 0 < p := by
    have := hM.inv
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h, Nat.zero_mul] at this; exact absurd this (by decide)
    · exact h
  have hpA : p < 2 ^ (64 * M.n) := hP ▸ wordsVal_lt _ _ _ _
  have hQ : 2 ^ (64 * (M.n + 1)) = 2 ^ (64 * M.n) * 2 ^ 64 := by rw [pow64_succ, Nat.mul_comm]
  have hQ' : 2 ^ (64 * (M.n + 2)) = 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := by
    rw [show M.n + 2 = M.n + 1 + 1 from rfl, pow64_succ, hQ, Nat.mul_comm]
  have eR : wordsVal s₂.mem base t (M.n + 2) % 2 ^ 64 + 2 ^ 64 * wordsVal s₂.mem base (t + 8) (M.n + 1) =
      wordsVal s₂.mem base t (M.n + 2) := by
    rw [show M.n + 2 = M.n + 1 + 1 from rfl, wordsVal, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (BitVec.isLt _)]
  have key := Divstep.mredRaw_nat (A := 2 ^ (64 * M.n)) (B := 2 ^ 64) (H := 2 ^ 63) (p := p) (m := M.minv.toNat)
    (t := T) (W := wordsVal s.mem base t (M.n + 1)) (k := (s₁.gpr .x16).toNat)
    (E := wordsVal s₂.mem base t (M.n + 2)) (R := wordsVal s₂.mem base (t + 8) (M.n + 1))
    rfl rfl (Nat.two_pow_pos _) hp0 hpA hM.inv hT (hQ ▸ wordsVal_lt _ _ _ _) (by rw [← hQ]; exact hW)
    (by rw [x₁, wordsVal, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (BitVec.isLt _)])
    (by rw [e₂, e₁, P₁, sgnW_top, hQ', hQ])
    (by have := eR; omega_arith)
  rw [eu, hQ]
  exact key

/-! ## A batch with signed coefficients -/

/-- The signed batches' slots, from the table area. -/
theorem slotsS (P : InvCfg) :
    P.sBS = P.tbl + 24 * (P.M.n + 1) ∧ P.sNFS = P.tbl + 32 * (P.M.n + 1) ∧
      P.sNGS = P.tbl + 40 * (P.M.n + 1) ∧ P.sTS = P.tbl + 48 * (P.M.n + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [InvCfg.sTS, InvCfg.sNGS, InvCfg.sNFS, InvCfg.sBS, InvCfg.sA, InvCfg.L] <;> omega

/-- What a signed batch writes: the slots, `7 n + 8` words. -/
def batchWS (P : InvCfg) : List (Nat × Nat) := [(P.tbl, 8 * (7 * P.M.n + 8))]

/-- The signed batch state in memory: `d` in `x1`, `f`, `g`, `a`, `b` (two's
complement, `n + 1` words). -/
structure IInvS (P : InvCfg) (base : Addr) (I : Divstep.IState) (s : State) : Prop where
  d : s.gpr .x1 = BitVec.ofInt 64 I.d
  f : (wordsVal s.mem base P.sF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = I.f % ((2 ^ (64 * P.L) : Nat) : Int)
  g : (wordsVal s.mem base P.sG P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = I.g % ((2 ^ (64 * P.L) : Nat) : Int)
  a : (wordsVal s.mem base P.sA P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = I.a % ((2 ^ (64 * P.L) : Nat) : Int)
  b : (wordsVal s.mem base P.sBS P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = I.b % ((2 ^ (64 * P.L) : Nat) : Int)

/-- The batch state as `IInv` has it, for the low words of `f`, `g`. -/
theorem IInvS.toIInv {P : InvCfg} {base : Addr} {I : Divstep.IState} {s : State} (h : IInvS P base I s) :
    IInv P base ⟨I.d, I.f, I.g, wordsVal s.mem base P.sA P.M.n, wordsVal s.mem base P.sB P.M.n⟩ s :=
  ⟨h.d, h.f, h.g, rfl, rfl⟩

/-- Half a batch's update of `a`, `b`: `[dst] ≡ mredRaw (u a + v b)` (`n + 1` words, signed). -/
theorem abHalfS_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {p : Nat}
    (hM : ModOkA M size p s.mem base) (hmo8 : M.mo % 8 = 0) (h12 : s.gpr .x12 = 0)
    {w w' : Reg} (hw : w ∉ [Reg.x0, .x2, .x3, .x8, .x9, .x10, .x12, .x16, .x17])
    (hw' : w' ∉ [Reg.x0, .x2, .x3, .x8, .x9, .x10, .x12, .x16, .x17])
    {u v : Int} (hu : s.gpr w = BitVec.ofInt 64 u) (hv : s.gpr w' = BitVec.ofInt 64 v) (huv : |u| + |v| ≤ 2 ^ 59)
    {T x y dst : Nat} (hx : x + 8 * (M.n + 1) ≤ size) (hx8 : x % 8 = 0) (hy : y + 8 * (M.n + 1) ≤ size)
    (hy8 : y % 8 = 0) (hT : T + 8 * (M.n + 2) ≤ size) (hT8 : T % 8 = 0) (hd : dst + 8 * (M.n + 1) ≤ size)
    (hd8 : dst % 8 = 0) (hTx : T + 8 * (M.n + 2) ≤ x ∨ x + 8 * (M.n + 1) ≤ T)
    (hTy : T + 8 * (M.n + 2) ≤ y ∨ y + 8 * (M.n + 1) ≤ T)
    (hdT : dst + 8 * (M.n + 1) ≤ T ∨ T + 8 * (M.n + 2) ≤ dst) (hTm : T + 8 * (M.n + 2) ≤ M.mo ∨ M.mo + 8 * M.n ≤ T)
    {a b : Int}
    (ha : (wordsVal s.mem base x (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
      a % ((2 ^ (64 * (M.n + 1)) : Nat) : Int))
    (hb : (wordsVal s.mem base y (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
      b % ((2 ^ (64 * (M.n + 1)) : Nat) : Int))
    (ha0 : |a| ≤ 2 * p) (hb0 : |b| ≤ 2 * p) :
    WP isa (.block ((maskOf .x16 w ++ maskOf .x17 w' ++ lin w w' .x16 .x17 T x y (M.n + 1) (M.n + 1)) ++
        mredS M dst T)) s
      fun t =>
        (wordsVal t.mem base dst (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
          Divstep.mredRaw p M.minv.toNat (u * a + v * b) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) ∧
        KeepRegs [.x2, .x3, .x8, .x9, .x10, .x16, .x17] s t ∧
        Unch base [(T, 8 * (M.n + 2)), (dst, 8 * (M.n + 1))] s.mem t.mem := by
  have hn := hs.nowrap
  have hn0 := hM.n0
  rw [WP.block_append_iff]
  refine WP.mono (linM_ok hs h12 hw hw' (k := M.n + 1) (K := M.n + 1) (by omega_using []) (Nat.le_refl _)
    (by omega_using [hn0]) (by omega_using []) hx hx8 hy hy8 (by omega_using [hT]) hT8 (by omega_using [hTx])
    (by omega_using [hTy])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [hu, hv, Divstep.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv), Divstep.cong_comb ha hb] at e₁
  have hM₁ := modOk_out hM O₁ (by omega_using [hTm]) hn
  have hp0 : (0 : Int) < p := by
    have := hM.inv
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h, Nat.zero_mul] at this; exact absurd this (by decide)
    · exact_mod_cast h
  have hT' : |u * a + v * b| ≤ 2 ^ 63 * (p : Int) := Divstep.comb_le2 (N := 59) (by decide) hp0 huv ha0 hb0
  refine WP.mono (mredS_ok hs₁ hM₁ hmo8 (by rw [k₁.gpr _ (by decide), h12]) hT hT8 hd hd8 hTm hdT hT' e₁)
    fun t ⟨e, k, m₁, Ot, Od⟩ => ⟨e, k₁.trans k, ?_⟩
  exact ((O₁.mono (n' := 8 * (M.n + 2)) (Nat.le_refl _) (by omega_using [])).unch.trans (Ot.unch.trans Od.unch)).mono
    fun w hw => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h | h <;> simp [h]

/-- The update of `a`, `b`, signed. -/
abbrev abCodeS (P : InvCfg) : List Instr :=
  ((maskOf .x16 .x4 ++ maskOf .x17 .x5 ++ lin .x4 .x5 .x16 .x17 P.sTS P.sA P.sBS (P.M.n + 1) (P.M.n + 1)) ++
    mredS P.M P.sNFS P.sTS) ++
  (((maskOf .x16 .x6 ++ maskOf .x17 .x7 ++ lin .x6 .x7 .x16 .x17 P.sTS P.sA P.sBS (P.M.n + 1) (P.M.n + 1)) ++
    mredS P.M P.sBS P.sTS) ++ copyW P.sA P.sNFS (P.M.n + 1))

theorem updateS_eq (P : InvCfg) :
    (.movz .x .x12 0 0 :: P.fgUpdateAt P.sNFS P.sNGS P.sTS) ++ P.abUpdateS =
      ([.movz .x .x12 0 0] : List Instr) ++ (fgCodeAt P P.sNFS P.sNGS P.sTS ++ abCodeS P) := by
  simp only [fgCodeAt, abCodeS, InvCfg.fgUpdateAt, InvCfg.abUpdateS, InvCfg.L, List.append_assoc, List.cons_append,
    List.nil_append]

/-- A signed batch's update of `a`, `b`, by the matrix in `x4`–`x7`. -/
theorem abUpdS_ok {P : InvCfg} {base : Addr} {size p : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkA P.M size p s.mem base) (h12 : s.gpr .x12 = 0) {u v q r a b : Int}
    (h4 : s.gpr .x4 = BitVec.ofInt 64 u) (h5 : s.gpr .x5 = BitVec.ofInt 64 v)
    (h6 : s.gpr .x6 = BitVec.ofInt 64 q) (h7 : s.gpr .x7 = BitVec.ofInt 64 r)
    (huv : |u| + |v| ≤ 2 ^ 59) (hqr : |q| + |r| ≤ 2 ^ 59)
    (hA : (wordsVal s.mem base P.sA P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = a % ((2 ^ (64 * P.L) : Nat) : Int))
    (hB : (wordsVal s.mem base P.sBS P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = b % ((2 ^ (64 * P.L) : Nat) : Int))
    (ha : |a| ≤ 2 * p) (hb : |b| ≤ 2 * p) :
    WP isa (.block (abCodeS P)) s fun t =>
      (wordsVal t.mem base P.sA P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
        Divstep.mredRaw p P.M.minv.toNat (u * a + v * b) % ((2 ^ (64 * P.L) : Nat) : Int) ∧
      (wordsVal t.mem base P.sBS P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
        Divstep.mredRaw p P.M.minv.toNat (q * a + r * b) % ((2 ^ (64 * P.L) : Nat) : Int) ∧
      KeepRegs [.x2, .x3, .x8, .x9, .x10, .x16, .x17] s t ∧
      Unch base [(P.sTS, 8 * (P.M.n + 2)), (P.sNFS, 8 * P.L), (P.sBS, 8 * P.L), (P.sA, 8 * P.L)] s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, -, -, eA, -, -, -, -⟩ := slots P
  obtain ⟨eB, eNF, -, eT⟩ := slotsS P
  have n4 := hL.n4; have htbl := hL.tbl; have htbl8 := hL.tbl8; have hmt := hL.mo_tbl; have hmo := hM.mo
  rw [eL] at hA hB ⊢
  rw [WP.block_append_iff]
  refine WP.mono (abHalfS_ok hs hM hL.mo8 h12 (w := .x4) (w' := .x5) (by decide) (by decide) h4 h5 huv
    (T := P.sTS) (x := P.sA) (y := P.sBS) (dst := P.sNFS) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) hA hB ha hb)
    fun s₁ ⟨e₁, k₁, U₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have rA : wordsVal s₁.mem base P.sA (P.M.n + 1) = wordsVal s.mem base P.sA (P.M.n + 1) :=
    Unch.wv2 U₁ (by dsimp only; omega_arith) (by dsimp only; omega_arith) (by omega_arith)
  have rB : wordsVal s₁.mem base P.sBS (P.M.n + 1) = wordsVal s.mem base P.sBS (P.M.n + 1) :=
    Unch.wv2 U₁ (by dsimp only; omega_arith) (by dsimp only; omega_arith) (by omega_arith)
  have M₁ : ModOkA P.M size p s₁.mem base := ⟨hM.n0, hM.n10, hM.mo, hM.tmp, hM.sep,
    by rw [Unch.wv2 U₁ (by dsimp only; omega_arith) (by dsimp only; omega_arith) (by omega_arith)]; exact hM.val,
    hM.inv, hM.red, hM.call⟩
  rw [WP.block_append_iff]
  refine WP.mono (abHalfS_ok hs₁ M₁ hL.mo8 (by rw [k₁.gpr _ (by decide), h12]) (w := .x6) (w' := .x7) (by decide)
    (by decide) (by rw [k₁.gpr _ (by decide)]; exact h6) (by rw [k₁.gpr _ (by decide)]; exact h7) hqr
    (T := P.sTS) (x := P.sA) (y := P.sBS) (dst := P.sBS) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith)
    (by rw [rA]; exact hA) (by rw [rB]; exact hB) ha hb) fun s₂ ⟨e₂, k₂, U₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have rNF : wordsVal s₂.mem base P.sNFS (P.M.n + 1) = wordsVal s₁.mem base P.sNFS (P.M.n + 1) :=
    Unch.wv2 U₂ (by dsimp only; omega_arith) (by dsimp only; omega_arith) (by omega_arith)
  refine WP.mono (copyW_ok hs₂ (dst := P.sA) (src := P.sNFS) (by omega_arith) (by omega_arith) (P.M.n + 1)
    (by omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨e₃, k₃, O₃⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [e₃, rNF]; exact e₁
  · rw [O₃.wordsVal (by omega_arith) (by omega_arith)]; exact e₂
  · exact (k₁.trans k₂).trans (k₃.mono (by decide))
  · rw [← eL]
    refine ((U₁.trans U₂).trans O₃.unch).mono fun w hw => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h | h | h | h <;> simp only [h, eL, true_or, or_true]

/-- A signed batch: `59` divsteps on the low words, then `f`, `g`, `a`, `b` by their matrix. -/
theorem batchS_ok {P : InvCfg} {base : Addr} {size p : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkA P.M size p s.mem base) {I : Divstep.IState} (hI : IInvS P base I s)
    (hd : |I.d| ≤ 2 ^ 30) (hf1 : I.f % 2 = 1) (hf : |I.f| ≤ p) (hg : |I.g| ≤ p)
    (ha : |I.a| ≤ 2 * p) (hb : |I.b| ≤ 2 * p) {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa P.batchS s fun t =>
      IInvS P base (Divstep.batchS 59 p P.M.minv.toNat I) t ∧ t.gpr .x19 = BitVec.ofNat 64 (j - 1) ∧
      KeepRegs [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x16, .x17, .x19] s t ∧
      Unch base (batchWS P) s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, -, -, -, -⟩ := slots P
  obtain ⟨eB, eNF, eNG, eT⟩ := slotsS P
  have n4 := hL.n4; have htbl := hL.tbl; have htbl8 := hL.tbl8
  have hp : p < 2 ^ (64 * P.M.n) := hM.val ▸ wordsVal_lt _ _ _ _
  obtain ⟨buv, bqr⟩ := Divstep.msteps_bnd I.d I.f I.g 59
  obtain ⟨mf, mg⟩ := Divstep.msteps_mat (d := I.d) (g := I.g) hf1 59
  rw [InvCfg.batchS]
  refine WP.seq (WP.mono (words_ok hL hs hI.toIInv hd hf1 hj hj' h19) fun s₁ h₁ => WP.seq (WP.mono h₁ fun s₂ h₂ => ?_))
  obtain ⟨hD, hU, hV, hQ, hR, c19, m₂, k₂⟩ := h₂
  have hs₂ := hs.of_keepRegs k₂ (by decide)
  rw [updateS_eq, WP.block_append_iff]
  refine WP.mono (movzI_ok s₂ .x12 0) fun s₃ ⟨c12, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have z₃ : s₃.gpr .x12 = 0 := by rw [c12]; rfl
  have m₃ : s₃.mem = s.mem := by rw [k₃.mem, m₂]
  rw [WP.block_append_iff]
  refine WP.mono (fgUpdAt_ok hL hs₃ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) hp z₃ (u := _) (v := _) (q := _) (r := _)
    (by rw [k₃.gpr _ (by decide)]; exact hU) (by rw [k₃.gpr _ (by decide)]; exact hV)
    (by rw [k₃.gpr _ (by decide)]; exact hQ) (by rw [k₃.gpr _ (by decide)]; exact hR) buv bqr
    (by rw [m₃]; exact hI.f) (by rw [m₃]; exact hI.g) hf hg ⟨_, mf.symm⟩ ⟨_, mg.symm⟩)
    fun s₄ ⟨eF₄, eG₄, k₄, U₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have g₄ : ∀ r ∉ [Reg.x2, .x3, .x8, .x9, .x10, .x16, .x17], s₄.gpr r = s₃.gpr r := k₄.gpr
  have rd₄ : ∀ {d k : Nat}, d + 8 * k ≤ P.sNFS → P.sG + 8 * P.L ≤ d → d + 8 * k ≤ size →
      wordsVal s₄.mem base d k = wordsVal s₃.mem base d k := fun h1 h2 h3 =>
    U₄.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by omega_using [h3, hn])
  have M₄ : ModOkA P.M size p s₄.mem base := ⟨hM.n0, hM.n10, hM.mo, hM.tmp, hM.sep,
    by
      rw [U₄.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        have hmt := hL.mo_tbl
        rcases hw with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith)
        (by have := hM.mo; omega_using [this, hn]), m₃]
      exact hM.val, hM.inv, hM.red, hM.call⟩
  refine WP.mono (abUpdS_ok hL hs₄ M₄ (by rw [g₄ _ (by decide), z₃]) (u := _) (v := _) (q := _) (r := _)
    (by rw [g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hU) (by rw [g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hV)
    (by rw [g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hQ) (by rw [g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hR)
    buv bqr (by rw [rd₄ (by omega_arith) (by omega_arith) (by omega_arith), m₃]; exact hI.a)
    (by rw [rd₄ (by omega_arith) (by omega_arith) (by omega_arith), m₃]; exact hI.b) ha hb)
    fun t ⟨eA₅, eB₅, k₅, U₅⟩ => ?_
  have rd₅ : ∀ {d k : Nat}, d + 8 * k ≤ P.sA → d + 8 * k ≤ size →
      wordsVal t.mem base d k = wordsVal s₄.mem base d k := fun h1 h3 =>
    U₅.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by omega_using [h3, hn])
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [Divstep.batchS]
    rw [k₅.gpr _ (by decide), g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hD
  · simp only [Divstep.batchS]
    rw [rd₅ (by omega_arith) (by omega_arith)]; exact eF₄
  · simp only [Divstep.batchS]
    rw [rd₅ (by omega_arith) (by omega_arith)]; exact eG₄
  · simp only [Divstep.batchS]; exact eA₅
  · simp only [Divstep.batchS]; exact eB₅
  · rw [k₅.gpr _ (by decide), g₄ _ (by decide), k₃.gpr _ (by decide)]; exact c19
  · refine (((k₂.mono ?_).trans ((Keeps.regs k₃).mono ?_)).trans (k₄.mono ?_)).trans (k₅.mono ?_) <;> decide
  · have U := U₄.trans U₅
    rw [m₃] at U
    refine (U.outside fun w hw => ?_).unch
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith

end VG.Proof.Weierstrass.AArch64
