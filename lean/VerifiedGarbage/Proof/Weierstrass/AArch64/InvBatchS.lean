module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvBatch
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvRedS
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-!
# Inversion by divsteps on AArch64: a batch with signed coefficients

A batch of `InvCfg.inv` (`batchS`): `59` divsteps on the low words, then `f`,
`g` by their matrix as in `batch`, and `a`, `b`, signed in `n + 1` words, by
one word of Montgomery reduction (`mredS`), as `Divstep.batchS`
(`batchS_ok`), for `a`, `b` in `(-p, 2p)`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

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
