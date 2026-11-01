module

import VerifiedGarbage.Proof.Weierstrass.BytesLen
public import VerifiedGarbage.Proof.Ecdsa.Arm.Stages
public import VerifiedGarbage.Proof.Ecdsa.Arm.MulFn
import VerifiedGarbage.Proof.Weierstrass.Arm.Rep
public import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Arm.Finish
import VerifiedGarbage.Proof.Ecdsa.Arm.Scalar
import VerifiedGarbage.Proof.Ecdsa.Arm.Middle
import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Weierstrass.Pow
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Weierstrass.MulContract

/-!
# ECDSA on 32-bit ARM: the whole function

`sign_ok`: `Cfg.sign` computes the specification's signature of the hash
with `d` and `k`, for any curve the proof of the code supports (`CfgOk`)
whose group law the proofs support (`Law`), restores the callee-saved
registers and changes memory only in the working space and `out`. Four
stages, each a lemma, as on x86 (`Proof/Ecdsa/X86/Main.lean`): the
setup and the tables of bits (`stage₁`, in `Stages.lean`), `[k]G` and
`Z^(p-2)` (`stage₂`), `x`, `r`, the checks and `k^(n-2)` (`stage₃`), and
`s`, its check and the result (`stage₄`); `signWith_eq` connects what they
compute to the specification.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.Arm (Rest)

variable {c : Cfg} {A : Args}

/-- The ranges of numbered slots and of the accumulator. -/
abbrev slWk (c : Cfg) (l : List Nat) : List (Nat × Nat) := slW c l ++ [(c.wk, 64 * c.n)]

theorem apart_slWk (h7 : c.n < 10) {l : List Nat} {i : Nat} (hi : i < 45) (hl : i ∉ l) :
    ∀ w ∈ slWk c l, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_slW hl) (apart_wk h7 hi)

theorem tbl_apart_slWk (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i < 45) {j t : Nat} :
    ∀ w ∈ slWk c l, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t :=
  apart_append (tbl_apart_slW h7 hl j t) (tbl_apart_wk h7 j t)

theorem fixedOk_slWk (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i = TMP ∨ 12 ≤ i) : FixedOk c (slWk c l) :=
  (fixedOk_slW hl).append (fixedOk_wk h7)

theorem slWk_le (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i < 45) : ∀ w ∈ slWk c l, w.1 + w.2 ≤ size := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact sl_le c h7 (hl i hi)
  · rw [List.mem_singleton.mp hw]
    exact wk_le c h7 (M := c.MP') rfl

theorem flag_le (h0 : 0 < c.n) (h7 : c.n < 10) : ∀ w ∈ [(c.sl FLAG, 4)], w.1 + w.2 ≤ size := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  have := sl_le c h7 (i := FLAG) (by decide)
  dsimp only
  omega_arith

/-! ### The point functions' slots

For coordinates of at most 6 words, the ladder calls the point functions
(`ladderP_ok`), which also write their slots and own working space (`ptW`),
above every numbered slot and below the tables. -/

/-- The ladder's slots are below the point functions'. -/
theorem ladPt (h6 : c.n ≤ 6) : VG.Proof.Weierstrass.Arm.Point.LadPt c.ladderCfg where
  sl := by
    rw [ladSlots_eq]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have : ∀ i ∈ [AP, B3P, GX, GY, ONEP, RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ],
      i < 45 := by decide
    exact sl_below_pt h6 (this i hi)
  mo := sl_below_pt h6 (i := MP) (by decide)

theorem apart_ptW {i : Nat} (hi : i < 45) :
    ∀ w ∈ VG.Proof.Weierstrass.Arm.Point.ptW c.n, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  unfold VG.Proof.Weierstrass.Arm.Point.ptW at hw
  split at hw
  · rw [List.mem_singleton.mp hw]; exact Or.inl (sl_below_pt ‹_› hi)
  · simp at hw

theorem tbl_apart_ptW (j t : Nat) :
    ∀ w ∈ VG.Proof.Weierstrass.Arm.Point.ptW c.n, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  unfold VG.Proof.Weierstrass.Arm.Point.ptW at hw
  split at hw
  · rw [List.mem_singleton.mp hw, bitsAt_eq]; have := oAt_le c; dsimp only; omega_arith
  · simp at hw

theorem fixedOk_ptW : FixedOk c (VG.Proof.Weierstrass.Arm.Point.ptW c.n) := by
  intro w hw
  unfold VG.Proof.Weierstrass.Arm.Point.ptW at hw
  split at hw
  · rw [List.mem_singleton.mp hw]
    exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_pt ‹_› (i := 12) (by decide)))
  · simp at hw

theorem ptW_le : ∀ w ∈ VG.Proof.Weierstrass.Arm.Point.ptW c.n, w.1 + w.2 ≤ size := by
  intro w hw
  unfold VG.Proof.Weierstrass.Arm.Point.ptW at hw
  split at hw
  · rw [List.mem_singleton.mp hw]; have := oAt_le c; dsimp only [size]; omega_arith
  · simp at hw

/-- What the ladder writes: numbered slots, the accumulator and the point
functions' slots. -/
abbrev slWkP (c : Cfg) (l : List Nat) : List (Nat × Nat) := slWk c l ++ VG.Proof.Weierstrass.Arm.Point.ptW c.n

theorem apart_slWkP (h7 : c.n < 10) {l : List Nat} {i : Nat} (hi : i < 45) (hl : i ∉ l) :
    ∀ w ∈ slWkP c l, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_slWk h7 hi hl) (apart_ptW hi)

theorem tbl_apart_slWkP (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i < 45) {j t : Nat} :
    ∀ w ∈ slWkP c l, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t :=
  apart_append (tbl_apart_slWk h7 hl) (tbl_apart_ptW j t)

theorem fixedOk_slWkP (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i = TMP ∨ 12 ≤ i) : FixedOk c (slWkP c l) :=
  (fixedOk_slWk h7 hl).append fixedOk_ptW

theorem slWkP_le (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i < 45) : ∀ w ∈ slWkP c l, w.1 + w.2 ≤ size :=
  fun w hw => (List.mem_append.mp hw).elim (slWk_le h7 hl w) (ptW_le w)

/-- The flag word apart from what the ladder writes. -/
theorem flag_unchP {base : Addr} {l : List Nat} {m m' : Mem} (hu : Unch base (slWkP c l) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 32) (hl : FLAG ∉ l) :
    m'.readW (off base (c.sl FLAG)) 32 = m.readW (off base (c.sl FLAG)) 32 := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine Unch.readW32 hu (fun w hw => ?_) (by omega_arith)
  rcases apart_slWkP (c := c) h7 (i := FLAG) (by decide) hl w hw with h | h
  · exact Or.inl (by omega_arith)
  · exact Or.inr h

/-- After `[k]G` and `Z^(p-2)`. -/
structure St₂ (c : Cfg) (A : Args) (s₀ : State) (base : Addr) (s : State) : Prop extends Keep c s₀ base s where
  k : sv c base s K = kv c A s₀
  d : sv c base s D = dv c A s₀
  e : sv c base s E = ev c A s₀
  flag : flagW c base s = BitVec.allOnes 32
  t₂ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 2 + t)) = if (c.C.n - 2).testBit t then 1 else 0
  rep : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
    (tmv c.C c.n base s (c.sl RZ)) (mul (kv c A s₀) (G c.C))
  acc_lt : sv c base s ACC < c.C.p
  acc : toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) = tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2)
  rz_lt : sv c base s RZ < c.C.p

/-- The generator multiplication result needed by all later ECDSA stages. -/
def GeneratorPost (c : Cfg) (base : Addr) (k : Nat) (s t : State) : Prop :=
  Rest powClob s t ∧ Unch base (VG.Proof.Weierstrass.Arm.Point.ladWp c.ladderCfg c.wk ++ genX c) s.mem t.mem ∧
  ModOkW c.MP' size c.C.p t.mem base ∧
  (∀ x ∈ [c.sl RX,c.sl RY,c.sl RZ],wordsVal t.mem base x c.n<c.C.p) ∧
  Rep c.C (tmv c.C c.n base t (c.sl RX)) (tmv c.C c.n base t (c.sl RY))
    (tmv c.C c.n base t (c.sl RZ)) (mul k (G c.C))

/-- The default generator implementation, shared by the unmodified callers. -/
theorem generator_ladder_ok (hc : CfgOk c) (hC : Law c.C) {s₀ : State} {base : Addr} {s : State}
    (hS : St₁ c A s₀ base s) :
    WP isa (VG.Impl.Weierstrass.Arm.Point.ladderP c.ladderCfg c.SP false c.umaal) s
      (GeneratorPost c base (kv c A s₀) s) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hS.scr.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F := hS.fixed
  have hkl : kv c A s₀ < 2 ^ (8 * c.C.len) :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (ofBytes_bytesAt_lt _ _ _)
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have hlt : ∀ x ∈ ladR c.ladderCfg, wordsVal s.mem base x c.MP'.n < c.C.p := by
    intro x hx
    have hx' : x ∈ [AP, B3P, GX, GY, ONEP, RX, RY, RZ].map c.sl := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show sv c base s i < c.C.p
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F.ap (hmont _)
    · exact lt_of_eq_of_lt F.b3p (hmont _)
    · exact lt_of_eq_of_lt F.gx (hmont _)
    · exact lt_of_eq_of_lt F.gy (hmont _)
    · exact lt_of_eq_of_lt F.onep (Nat.mod_lt _ (by omega_arith))
    · exact lt_of_eq_of_lt hS.rx (by omega_arith)
    · exact lt_of_eq_of_lt hS.ry (hmont _)
    · exact lt_of_eq_of_lt hS.rz (by omega_arith)
  have hG : Rep c.C (tmv c.C c.n base s (c.sl GX)) (tmv c.C c.n base s (c.sl GY))
      (tmv c.C c.n base s (c.sl ONEP)) (G c.C) := by
    show Rep c.C (toM _ _ (wordsVal s.mem base (c.sl GX) c.n)) (toM _ _ (wordsVal s.mem base (c.sl GY) c.n))
      (toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n)) (G c.C)
    rw [F.gx, F.gy, F.onep, toM_cmont hc, toM_cmont hc, toM_one hpR]
    exact rep_affine' hC _ _
  have hR : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
      (tmv c.C c.n base s (c.sl RZ)) (mul (kv c A s₀ >>> (8 * c.C.len)) (G c.C)) := by
    show Rep c.C (toM _ _ (sv c base s RX)) (toM _ _ (sv c base s RY)) (toM _ _ (sv c base s RZ)) _
    rw [hS.rx, hS.ry, hS.rz, toM_cmont hc, toM_zero, shiftRight_eq_zero hkl, mul_zero_pt]
    exact rep_infinity' hC
  have hstep := step_rep (L := c.ladderCfg) (k := kv c A s₀) hC hc.onG (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl AP) c.n) = _
      rw [F.ap]; exact toM_cmont hc _)
    (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl B3P) c.n) = _
      rw [F.b3p]; exact toM_cmont hc _) hG
  have henc := scalarBits_enc hc
  refine WP.mono (VG.Proof.Weierstrass.Arm.Point.ladderP_ok (a0 := false) (u := c.umaal) (ladLay hc) (ladWk hc) hc.fp ladPt hpR
    (bitsAt_lt hc (j := 0) (by decide)) hS.scr hS.far (modP_of hc F.mp) hlt nofun hstep hR
      (fun t ht => hS.t₀ t (Nat.lt_of_lt_of_le ht (scalarBits_le hc))) henc)
    fun s₅ ⟨K₅, U₅, M₅, L₅, R₅⟩ => ?_
  rw [Nat.shiftRight_zero] at R₅
  exact ⟨K₅, U₅.mono fun w hw => List.mem_append_left _ hw, M₅, L₅, R₅⟩

/-- The common inversion and state preservation after any verified generator routine. -/
theorem stage₂With (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (hS : St₁ c A s₀ base s)
    {generator : Prog isa} (hMul : WP isa generator s (GeneratorPost c base (kv c A s₀) s))
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', St₂ c A s₀ base s' → WP isa rest s' Q) :
    WP isa (.seq generator (.seq (pow c.powP c.SP c.umaal) rest)) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hS.scr.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F := hS.fixed
  have henc : encodable (BitVec.ofNat 32 (64*c.n))=true := by
    have en : ∀ n<10,encodable (BitVec.ofNat 32 (64*n))=true := by decide
    exact en _ h7
  refine WP.seq (WP.mono hMul fun s₅ ⟨K₅,U₅,M₅,L₅,R₅⟩ => ?_)
  rw [VG.Proof.Weierstrass.Arm.Point.ladWp, ladWx_eq] at U₅
  have hs₅ := hS.scr.of_rest K₅ (by decide)
  have hf₅ := hS.far.of_rest K₅
  have F₅ := F.unch h7 hn ((fixedOk_slWkP h7 (by decide)).append (fixedOk_genX h7)) U₅
  refine WP.seq (WP.mono (pow_ok (P := c.powP) (e := c.C.p - 2) (powLayP hc) (powWkP hc) hc.fp hpR
    (bitsAt_lt hc (j := 1) (by decide)) hs₅ hf₅ M₅
    (L₅ (c.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))) F₅.onep
    (fun t ht => by
      show s₅.mem (off base (bitsAt c.n 1 + t)) = _
      rw [tbl_unch U₅ h7 (j := 1) (by decide) ht
        (apart_append (tbl_apart_slWkP h7 (by decide)) (tbl_apart_genX h7 (by decide) ht))]
      exact hS.t₁ t ht)
    (show c.C.p - 2 < 2 ^ (64 * c.n) by have := hc.p_lt; omega_arith) henc) fun s₆ ⟨K₆, U₆, lt₆, v₆⟩ => h s₆ ?_)
  rw [powWxP_eq] at U₆
  have e₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] →
      i ∉ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP] →
      sv c base s₆ i = sv c base s i := fun hi h₁ h₂ =>
    (sv_unch U₆ h7 hn hi (apart_slWk h7 hi h₁)).trans (sv_unch U₅ h7 hn hi
      (apart_append (apart_slWkP h7 hi h₂) (apart_genX h7 hi fun h => h₁ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega))))
  have r₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₆ i = sv c base s₅ i := fun hi h₁ =>
    sv_unch U₆ h7 hn hi (apart_slWk h7 hi h₁)
  have K₅₆ : Rest work s s₆ := (K₅.mono powClob_work).trans (K₆.mono powClob_work)
  refine ⟨⟨hs₅.of_rest K₆ (by decide), hf₅.of_rest K₆, hS.rest.trans (K₅₆.mono (by simp)), by rw [K₅₆.gpr _ (by decide), hS.lr],
    F₅.unch h7 hn (fixedOk_slWk h7 (by decide)) U₆,
    whole_of (whole_of' hS.whole U₅ fun w hw => (List.mem_append.mp hw).elim
      (fun h => by have := slWkP_le h7 (by decide) w h; dsimp only [size] at this; omega) (genX_le h7 w))
      U₆ (slWk_le h7 (by decide))⟩,
    by rw [e₆ (by decide) (by decide) (by decide), hS.k],
    by rw [e₆ (by decide) (by decide) (by decide), hS.d],
    by rw [e₆ (by decide) (by decide) (by decide), hS.e],
    by rw [flagW, flag_unch U₆ h7 h0 hn (by decide), Unch.readW32 U₅ (fun w hw => by
        rcases apart_append (apart_slWkP (c := c) h7 (i := FLAG) (by decide) (by decide))
          (apart_genX (c := c) h7 (i := FLAG) (by decide) (by decide)) w hw with h | h
        · exact Or.inl (by have := sl_le c h7 (i := FLAG) (by decide); omega_arith)
        · exact Or.inr h) (by have := sl_le c h7 (i := FLAG) (by decide); omega_arith),
      ← flagW, hS.flag],
    ?_, ?_, lt₆, ?_, ?_⟩
  · intro t ht
    rw [tbl_unch U₆ h7 (j := 2) (by decide) ht (tbl_apart_slWk h7 (by decide)),
      tbl_unch U₅ h7 (j := 2) (by decide) ht
        (apart_append (tbl_apart_slWkP h7 (by decide)) (tbl_apart_genX h7 (by decide) ht))]
    exact hS.t₂ t ht
  · show Rep c.C (toM _ _ (sv c base s₆ RX)) (toM _ _ (sv c base s₆ RY)) (toM _ _ (sv c base s₆ RZ)) _
    rw [r₆ (i := RX) (by decide) (by decide), r₆ (i := RY) (by decide) (by decide),
      r₆ (i := RZ) (by decide) (by decide)]
    exact R₅
  · show _ = toM _ _ (sv c base s₆ RZ) ^ _
    rw [r₆ (i := RZ) (by decide) (by decide)]
    exact v₆
  · rw [r₆ (i := RZ) (by decide) (by decide)]
    exact L₅ (c.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

/-- `[k]G` by the generic ladder, then `Z^(p-2)`. -/
theorem stage₂ (hc : CfgOk c) (hC : Law c.C) {s₀ : State} {base : Addr} {s : State} (hS : St₁ c A s₀ base s)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', St₂ c A s₀ base s' → WP isa rest s' Q) :
    WP isa (.seq (VG.Impl.Weierstrass.Arm.Point.ladderP c.ladderCfg c.SP false c.umaal) (.seq (pow c.powP c.SP c.umaal) rest)) s Q :=
  stage₂With hc hS (generator_ladder_ok hc hC hS) h

/-- After `x`, `r`, the checks and `k^(n-2)`. -/
structure St₃ (c : Cfg) (A : Args) (s₀ : State) (base : Addr) (s : State) : Prop extends Keep c s₀ base s where
  d : sv c base s D = dv c A s₀
  e : sv c base s E = ev c A s₀
  rep : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
    (tmv c.C c.n base s (c.sl RZ)) (mul (kv c A s₀) (G c.C))
  x_lt : sv c base s X < c.C.p
  x : Fin.ofNat c.C.p (sv c base s X) =
    tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2)
  rr : sv c base s RR = sv c base s X % c.C.n
  flag : flagW c base s = BitVec.allOnes 32 &&&
    mask32 (0 < dv c A s₀ ∧ dv c A s₀ < c.C.n) &&& mask32 (0 < kv c A s₀ ∧ kv c A s₀ < c.C.n) &&&
    mask32 (sv c base s X % c.C.n ≠ 0)
  acc : toM c.C.n (2 ^ (64 * c.n)) (sv c base s ACC) = Fin.ofNat c.C.n (kv c A s₀) ^ (c.C.n - 2)

/-- `x`, `r`, `k R mod n` and the checks, then `k^(n-2)`. -/
theorem stage₃ (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (hS : St₂ c A s₀ base s)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', St₃ c A s₀ base s' → WP isa rest s' Q) :
    WP isa (.seq c.middle (.seq (pow c.powN c.SN c.umaal) rest)) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hS.scr.nowrap
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have F := hS.fixed
  have henc : encodable (BitVec.ofNat 32 (64 * c.n)) = true := by
    have : ∀ n < 10, encodable (BitVec.ofNat 32 (64 * n)) = true := by decide
    exact this _ h7
  refine WP.seq ?_
  rw [middle_eq]
  refine midOps_ok hc hS.scr hS.far (modP_of hc F.mp) (modN_of hc F.mn) hS.acc_lt F.one F.zero F.r2n
    fun s₇ Mp => ?_
  have F₇ := F.unch h7 hn (fixedOk_slWk h7 (l := [XM, X, RR, KM, TMP]) (by decide)) Mp.unch
  refine WP.mono (checks_ok hc Mp.scr F₇.mn) fun s₈ ⟨f₈, k₈, O₈⟩ => ?_
  have hs₈ := Mp.scr.of_rest k₈ (by decide)
  have hf₈ := (hS.far.of_rest Mp.rest).of_rest k₈
  have F₈ := F₇.unch h7 hn fixedOk_flag O₈.unch
  have e₈ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₈ i = sv c base s₇ i := fun hi hf =>
    sv_flag O₈ h0 h7 hn hi hf
  have e₇ : ∀ {i}, i < 45 → i ∉ [XM, X, RR, KM, TMP] → sv c base s₇ i = sv c base s i := fun hi hl =>
    sv_unch Mp.unch h7 hn hi (apart_slWk h7 hi hl)
  refine WP.seq (WP.mono (pow_ok (P := c.powN) (e := c.C.n - 2) (powLayN hc) (powWkN hc) hc.fn hnR
    (bitsAt_lt hc (j := 2) (by decide)) hs₈ hf₈
    (modN_of hc F₈.mn) (lt_of_eq_of_lt (e₈ (i := KM) (by decide) (by decide)) Mp.km_lt) F₈.onen
    (fun t ht => by
      show s₈.mem (off base (bitsAt c.n 2 + t)) = _
      rw [tbl_unch O₈.unch h7 (j := 2) (by decide) ht (tbl_apart_flag h7 h0 2 t),
        tbl_unch Mp.unch h7 (j := 2) (by decide) ht (tbl_apart_slWk h7 (by decide))]
      exact hS.t₂ t ht)
    (show c.C.n - 2 < 2 ^ (64 * c.n) by have := hc.n_lt; omega_arith) henc) fun s₉ ⟨K₉, U₉, lt₉, v₉⟩ => h s₉ ?_)
  rw [powWxN_eq] at U₉
  have e₉ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₉ i = sv c base s₈ i := fun hi hl =>
    sv_unch U₉ h7 hn hi (apart_slWk h7 hi hl)
  -- The slots `middle` and the power do not write.
  have a₉ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → i ≠ FLAG → i ∉ [XM, X, RR, KM, TMP] →
      sv c base s₉ i = sv c base s i := fun hi h₁ h₂ h₃ =>
    ((e₉ hi h₁).trans (e₈ hi h₂)).trans (e₇ hi h₃)
  have x₉ : sv c base s₉ X = sv c base s₇ X :=
    (e₉ (i := X) (by decide) (by decide)).trans (e₈ (by decide) (by decide))
  have rr₉ : sv c base s₉ RR = sv c base s₇ RR :=
    (e₉ (i := RR) (by decide) (by decide)).trans (e₈ (by decide) (by decide))
  have tR : ∀ i ∈ [RX, RY, RZ], tmv c.C c.n base s₉ (c.sl i) = tmv c.C c.n base s (c.sl i) := by
    intro i hi
    show toM _ _ (sv c base s₉ i) = toM _ _ (sv c base s i)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rw [a₉ (by decide) (by decide) (by decide) (by decide)]
  have K₇₉ : Rest work s s₉ := (Mp.rest.mono callClob_work).trans ((k₈.mono (by decide)).trans (K₉.mono powClob_work))
  refine ⟨⟨hs₈.of_rest K₉ (by decide), hf₈.of_rest K₉, hS.rest.trans (K₇₉.mono (by simp)), by rw [K₇₉.gpr _ (by decide), hS.lr],
    F₈.unch h7 hn (fixedOk_slWk h7 (by decide)) U₉,
    whole_of (whole_of (whole_of hS.whole Mp.unch (slWk_le h7 (by decide))) O₈.unch (flag_le h0 h7)) U₉
      (slWk_le h7 (by decide))⟩,
    by rw [a₉ (i := D) (by decide) (by decide) (by decide) (by decide), hS.d],
    by rw [a₉ (i := E) (by decide) (by decide) (by decide) (by decide), hS.e],
    by rw [tR RX (by simp), tR RY (by simp), tR RZ (by simp)]; exact hS.rep,
    by rw [x₉]; exact Mp.x_lt,
    by rw [x₉, Mp.x, tR RX (by simp), tR RZ (by simp), hS.acc],
    by rw [rr₉, x₉]; exact Mp.rr, ?_, ?_⟩
  · rw [flagW, flag_unch U₉ h7 h0 hn (by decide), ← flagW, f₈, flagW, flag_unch Mp.unch h7 h0 hn (by decide),
      ← flagW, hS.flag, e₇ (i := D) (by decide) (by decide), e₇ (i := K) (by decide) (by decide), hS.d, hS.k,
      Mp.rr, x₉]
  · refine v₉.trans ?_
    show toM c.C.n (2 ^ (64 * c.n)) (sv c base s₈ KM) ^ _ = _
    rw [e₈ (i := KM) (by decide) (by decide), Mp.km, hS.k]

/-- The result the contract asks for: the specification's signature of the
hash with `d` and `k`, big-endian, and `1`, or zeros and `0`. -/
def SignPost (c : Cfg) (s₀ s' : State) : Prop :=
  match Spec.Ecdsa.signWith c.C (ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r1) c.C.len))
      (Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r2) c.C.len))
      (ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r3) c.C.len)) with
  | some rs => s'.gpr .r0 = 1 ∧
      Spec.Ecdsa.bytesAt s'.mem (ptr s₀ .r0) (2 * c.C.len) = Spec.Ecdsa.encode c.C rs
  | none => s'.gpr .r0 = 0 ∧
      Spec.Ecdsa.bytesAt s'.mem (ptr s₀ .r0) (2 * c.C.len) = List.replicate (2 * c.C.len) 0

/-- What the ABI asks for: the callee-saved registers and `lr` restored,
`sp` kept; and memory changed only in the working space, then in `out`. -/
structure SignKeep (c : Cfg) (s₀ s' : State) : Prop where
  saved : ∀ rd ∈ Cfg.saved, s'.gpr rd.1 = s₀.gpr rd.1
  sp : s'.sp = s₀.sp
  frame : ∃ m : Mem, Unch (scPtr s₀) [(0, 8192)] s₀.mem m ∧ Outside (ptr s₀ .r0) 0 (2 * c.C.len) m s'.mem

/-- `s`, its check, and the result. -/
theorem stage₄ (hc : CfgOk c) (hC : Law c.C) {s₀ : State} {extra : List Region} (hp : Pre c s₀ extra) {base : Addr} (hb : base = scPtr s₀)
    {s : State} (hS : St₃ c .sign s₀ base s) :
    WP isa c.scalar s fun s' => SignKeep c s₀ s' ∧ SignPost c s₀ s' := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hS.scr.nowrap
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have F := hS.fixed
  rw [scalar_eq]
  refine scalarIn_ok hc hS.scr hS.far (modN_of hc F.mn) F.r2n
    fun s₁₀ hs₁₀ hM₁₀ K₁₀ U₁₀ _ dm em trm tdm tem => ?_
  have F₁₀ := F.unch h7 hn (fixedOk_slWk h7 (l := [RM, DM, EM, TT, SM, SS, TMP]) (by decide)) U₁₀
  refine scalarOut_ok hc hs₁₀ (hS.far.of_rest K₁₀) hM₁₀ F₁₀.one dm em
    fun s₁₁ hs₁₁ K₁₁ U₁₁ ss_lt ss => ?_
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine VG.Proof.X25519.Arm.WP.append (checkNonzero_ok c hs₁₁ h0 (sl_le c h7 (i := SS) (by decide)) (by omega_arith))
    fun s₁₂ ⟨f₁₂, k₁₂, O₁₂⟩ => ?_
  have hs₁₂ := hs₁₁.of_rest k₁₂ (by decide)
  have F₁₂ := (F₁₀.unch h7 hn (fixedOk_slWk h7 (l := [RM, DM, EM, TT, SM, SS, TMP]) (by decide)) U₁₁).unch
    h7 hn fixedOk_flag O₁₂.unch
  have W₁₂ : Unch base [(0, 8192)] s₀.mem s₁₂.mem :=
    whole_of (whole_of (whole_of hS.whole U₁₀ (slWk_le h7 (by decide))) U₁₁ (slWk_le h7 (by decide)))
      O₁₂.unch (flag_le h0 h7)
  have acc₁₀ : sv c base s₁₀ ACC = sv c base s ACC :=
    sv_unch U₁₀ h7 hn (by decide) (apart_slWk h7 (by decide) (by decide))
  have rr₁₂ : sv c base s₁₂ RR = sv c base s RR :=
    ((sv_flag O₁₂ h0 h7 hn (i := RR) (by decide) (by decide)).trans
      (sv_unch U₁₁ h7 hn (by decide) (apart_slWk h7 (by decide) (by decide)))).trans
      (sv_unch U₁₀ h7 hn (by decide) (apart_slWk h7 (by decide) (by decide)))
  have ss₁₂ : sv c base s₁₂ SS = sv c base s₁₁ SS := sv_flag O₁₂ h0 h7 hn (by decide) (by decide)
  -- The flag.
  have hflag : flagW c base s₁₂ =
      mask32 (decide ((((0 < dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n) ∧ (0 < kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n)) ∧
        sv c base s X % c.C.n ≠ 0) ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0) = true) := by
    rw [f₁₂, flagW, flag_unch U₁₁ h7 h0 hn (by decide), flag_unch U₁₀ h7 h0 hn (by decide), ← flagW, hS.flag,
      BitVec.allOnes_and, mask32_and, mask32_and, mask32_and]
    simp only [mask32, decide_eq_true_eq]
  have K₁₂' : Rest work s s₁₂ := (K₁₀.mono callClob_work).trans ((K₁₁.mono callClob_work).trans (k₁₂.mono (by decide)))
  have K₁₂ : Rest (.lr :: work) s₀ s₁₂ := hS.rest.trans (K₁₂'.mono (by simp))
  have lr₁₂ : s₁₂.gpr .lr = s₀.gpr .r0 := by rw [K₁₂'.gpr _ (by decide), hS.lr]
  have hw : (⟨State.addr (s₀.gpr .r0), 2 * c.C.len⟩ : Region) ∈ s₁₂.wr := by
    rw [K₁₂.wr, hp.wr]; simp
  refine WP.mono (finish_ok hc hs₁₂ lr₁₂ hp.out_fit hw (hb ▸ hp.out_sc.sub_right (sc_sub s₀)) F₁₂.saved _
    hflag) fun s' ⟨bytes, ret, saved, others, Oout⟩ => ⟨⟨saved, by rw [others.sp, K₁₂.sp],
      ⟨s₁₂.mem, hb ▸ W₁₂, Oout⟩⟩, ?_⟩
  -- The specification.
  have hsig := signWith_eq hC (C := c.C) (d := dv c .sign s₀) (e := ev c .sign s₀) (k := kv c .sign s₀) hS.rep hS.x_lt hS.x
    (s := wordsVal s₁₁.mem base (c.sl SS) c.n) ss_lt (by
      rw [ss, trm, tdm, tem, acc₁₀, hS.acc, hS.rr, hS.d, hS.e, Lean.Grind.AddCommMonoid.add_comm])
  unfold SignPost
  have he : ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r2) c.C.len) >>> c.sh = ev c .sign s₀ :=
    congrArg (_ >>> ·) (shAt_self c E).symm
  rw [← dv_eq (A := .sign) (shAt_E_D c), ← kv_eq (A := .sign) (shAt_E_K c), hashToInt_eq c, he, hsig]
  rw [ss₁₂, rr₁₂, hS.rr] at bytes
  by_cases hP : 1 ≤ dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n ∧ 1 ≤ kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n ∧
      sv c base s X % c.C.n ≠ 0 ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0
  · have hd : decide ((((0 < dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n) ∧ (0 < kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n)) ∧
        sv c base s X % c.C.n ≠ 0) ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0) = true := by
      simp only [decide_eq_true_eq]; omega_arith
    rw [ite_eq_left_of_eq_true _ _ (eq_true hP)]
    refine ⟨by rw [ret, hd]; rfl, ?_⟩
    rw [bytes, hd, ite_eq_left_of_eq_true _ _ (eq_true rfl), Spec.Ecdsa.encode]
  · have hd : decide ((((0 < dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n) ∧ (0 < kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n)) ∧
        sv c base s X % c.C.n ≠ 0) ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0) = false := by
      simp only [decide_eq_false_iff_not]; omega_arith
    rw [ite_eq_right_of_eq_false _ _ (eq_false hP)]
    refine ⟨by rw [ret, hd]; rfl, ?_⟩
    rw [bytes, hd]; rfl

/-- The shared signing pipeline with an interchangeable generator multiplication. -/
theorem signWith_ok (hc : CfgOk c) (hC : Law c.C) {s₀ : State} {extra : List Region}
    (hp : Pre c s₀ extra) {generator : Prog isa}
    (hMul : ∀ s, St₁ c .sign s₀ (scPtr s₀) s → s.syms=s₀.syms →
      WP isa generator s (GeneratorPost c (scPtr s₀) (kv c .sign s₀) s)) :
    WP isa (c.signWith generator) s₀ fun s' => SignKeep c s₀ s' ∧ SignPost c s₀ s' := by
  have setupRun := stage₁ hc hp.setup (rest := .block [])
    (Q := fun s => St₁ c .sign s₀ (scPtr s₀) s) (fun _ S => WP.block_nil S)
  have run := WP.mono_syms setupRun fun s S sy =>
    stage₂With hc S (hMul s S sy) fun _ S₂ => stage₃ hc S₂ fun _ S₃ => stage₄ hc hC hp rfl S₃
  simpa only [Cfg.signWith,Cfg.setup,WP.seq_iff (M := isa),WP.block_nil_iff (M := isa)] using run

/-- `gen`: `R = [k]G`, by the call or the ladder. -/
theorem generator_gen_ok (hc : CfgOk c) (hC : Law c.C) {s₀ : State} {base : Addr} {s : State}
    (hS : St₁ c A s₀ base s) : WP isa c.gen s (GeneratorPost c base (kv c A s₀) s) := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F := hS.fixed
  have hkl : kv c A s₀ < 2 ^ (8 * c.C.len) :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (ofBytes_bytesAt_lt _ _ _)
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have hG : Rep c.C (tmv c.C c.n base s (c.sl GX)) (tmv c.C c.n base s (c.sl GY))
      (tmv c.C c.n base s (c.sl ONEP)) (G c.C) := by
    show Rep c.C (toM _ _ (wordsVal s.mem base (c.sl GX) c.n)) (toM _ _ (wordsVal s.mem base (c.sl GY) c.n))
      (toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n)) (G c.C)
    rw [F.gx, F.gy, F.onep, toM_cmont hc, toM_cmont hc, toM_one hpR]
    exact rep_affine' hC _ _
  have hstep := step_rep' (L := pLadder c GX GY) (k := kv c A s₀) (a0 := c.qA0) hC hc.onG (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl AP) c.n) = _
      rw [F.ap]; exact toM_cmont hc _)
    (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl B3P) c.n) = _
      rw [F.b3p]; exact toM_cmont hc _) hG
    (fun h => ⟨by
      simp only [Impl.Ecdsa.Arm.Cfg.qA0, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.2.1]; rfl, by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl ONEP) c.n) = 1
      rw [F.onep]; exact toM_one hpR⟩)
  refine WP.mono (qMul_ok hc hS.scr hS.far F (px := GX) (py := GY) (by decide)
    (lt_of_eq_of_lt F.gx (hmont _)) (lt_of_eq_of_lt F.gy (hmont _)) hS.rx hS.ry hS.rz hstep
    (by rw [shiftRight_eq_zero hkl, mul_zero_pt]; exact rep_infinity' hC) (fun _ => hS.k)
    (fun _ t ht => hS.t₀ t ht)) fun t ⟨K, U, M, L, R⟩ => ?_
  rw [Nat.shiftRight_zero] at R
  exact ⟨K, U, M, L, R⟩

/-- `vg_ecdsa_<curve>_sign` computes the specification's signature, restores
the callee-saved registers and changes only the working space and `out`. -/
theorem sign_ok (hc : CfgOk c) (hC : Law c.C) {s₀ : State} (hp : Pre c s₀) :
    WP isa c.sign s₀ fun s' => SignKeep c s₀ s' ∧ SignPost c s₀ s' :=
  signWith_ok hc hC hp fun _ S _ => generator_gen_ok hc hC S

end VG.Proof.Ecdsa.Arm
