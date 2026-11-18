module

public import VerifiedGarbage.Spec.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Projective
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdh.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Points
import VerifiedGarbage.Proof.Ecdsa.AArch64.Scalar
import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `Ecdsa.Verify.AArch64.ProjectiveFlags`, which this module and modules that import it used -/

section

/-! ## `FinalState` -/

@[expose] public section

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 (RM')

/-- The numerical and frame facts used by the final signature check.
The point-multiplication proof supplies its group result separately. -/
structure FinalState (c : Cfg) (s₀ : State) (base : Addr) (g : Reg → BitVec 64)
    (s : State) : Prop where
  scr : Scr s base size
  wr : s.wr = s₀.wr
  rd : s.rd = s₀.rd
  fixed : Fixed c base g s.mem
  flag : word s.mem base (c.sl FLAG) =
    mask (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n))
  rm_lt : sv c base s RM' < c.C.n
  rm : toM c.C.n (2 ^ (64 * c.n)) (sv c base s RM') = Fin.ofNat c.C.n (sigR c s₀)
  rz_lt : sv c base s RZ < c.C.p
  unch : Unch base [(0, size)] s₀.mem s.mem
  k : sv c base s K = sigR c s₀
  rx_lt : sv c base s RX < c.C.p


theorem Pts.toFinalState {c : Cfg} {s₀ : State} {base : Addr} {g : Reg → BitVec 64}
    {Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop} {s : State}
    (h : Pts c s₀ base g Q₁ Q₂ s) : FinalState c s₀ base g s :=
  ⟨h.scr,h.wr,h.rd,h.fixed,h.flag,h.rm_lt,h.rm,h.rz_lt,h.unch,h.k,h.rx_lt⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `Final` -/

section

/-!
# ECDSA verification on AArch64: `x` and the result

`tail_ok`: from what `points_ok` leaves, the signature's power gives
`Z^(p-2)`, and `final` computes `x = X Z^(p-2)` out of Montgomery's form,
`x R mod n` and `x R - r R mod n`, ands the masks of `Z ≠ 0` and of that
difference being zero (`x ≡ r` modulo `n`) into the flag, returns its low
bit and restores the callee-saved registers (`vfinish_ok`).
-/

namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Impl.Ecdsa.Verify.AArch64 (RM' XN W)

variable {c : Cfg}

theorem vfinish_eq (c : Cfg) : Impl.Ecdsa.Verify.AArch64.Cfg.finish c =
    ([ld .x3 (c.sl FLAG)] : List Instr) ++ (Spill.restoreCode .x0 Cfg.saved ++
      ([.movz .x .x1 1 0, .logic .and .x .x0 .x3 .x1] : List Instr)) := by
  simp only [Impl.Ecdsa.Verify.AArch64.Cfg.finish, List.append_assoc]; rfl

/-- The return value and the callee-saved registers. -/
theorem vfinish_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (hsv : Spill.Saved base g Cfg.saved s.mem) (b : Bool)
    (hf : word s.mem base (c.sl FLAG) = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block (Impl.Ecdsa.Verify.AArch64.Cfg.finish c)) s fun s' =>
      (s'.gpr .x0).setWidth 32 = (if b then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) := by
  obtain hF := sl_le c hc.n10 (i := FLAG) (by decide)
  rw [vfinish_eq, WP.block_append_iff]
  refine WP.mono (ld_ok hs (d := c.sl FLAG) (by have := hc.n0; omega_arith) (sl_mod8 c FLAG) .x3)
    fun s₁ ⟨e₁, k₁, _⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  refine Spill.restore_ok hs₁.x0 (by decide) (by decide) (fun p hp => ?_) (by rw [k₁.mem]; exact hsv)
    fun s₂ R₂ => ?_
  · have := saved_lt p hp
    exact ⟨_, List.mem_append_right _ hs₁.wr, hs₁.contains (by have : size = 8192 := rfl; omega_arith) (by decide)⟩
  refine WP.mono (retBit_ok s₂) fun s₃ ⟨e₃, k₃⟩ => ⟨?_, fun r hr => ?_⟩
  · have hx3 : Reg.x3 ∉ Cfg.saved.map Prod.fst := by decide
    rw [e₃, R₂.other _ hx3, e₁, hf, mask_bit]
  · have : r ∉ [Reg.x0, .x1] := by
      revert r; decide
    rw [k₃.gpr r this]
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact R₂.gpr p hp

/-- `[o] = ([a] - [b]) mod m`, on slots. -/
theorem slSub_ok {M : Mod} {m : Nat} (hMn : M.n = c.n) (h7 : c.n < 10) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkA M size m s.mem base) (hMA : ModA M) {o a b : Nat} (ho : o < 45)
    (ha : a < 45) (hb : b < 45) (hA : sv c base s a < m) (hB : sv c base s b < m) :
    WP isa (.block (Impl.Mont.AArch64.sub M (c.sl o) (c.sl a) (c.sl b))) s fun s' =>
      OpKeep M base (c.sl o) s s' ∧ sv c base s' o = (sv c base s a + m - sv c base s b) % m := by
  have := sub_ok hs hM hMA (o := c.sl o) (a := c.sl a) (b := c.sl b) (by rw [hMn]; exact sl_le c h7 ho)
    (by rw [hMn]; exact sl_le c h7 ha) (by rw [hMn]; exact sl_le c h7 hb) (sl_mod8 c o) (sl_mod8 c a)
    (sl_mod8 c b) (by rw [hMn]; exact hA)
    (by rw [hMn]; exact hB)
  rw [hMn] at this
  exact this

theorem final_eq (c : Cfg) : Impl.Ecdsa.Verify.AArch64.Cfg.final c =
    .seq (c.mulPP (c.sl XM) (c.sl RX) (c.sl ACC))
    (.seq (c.mulPP (c.sl X) (c.sl XM) (c.sl ONE))
    (.seq (c.mulNP (c.sl XN) (c.sl X) (c.sl R2N))
    (.seq (.block (Impl.Mont.AArch64.sub c.MN' (c.sl W) (c.sl XN) (c.sl RM')))
      (.block (c.checkNonzero (c.sl RZ) ++ (Impl.Ecdh.AArch64.Cfg.checkZero c (c.sl W) ++
        Impl.Ecdsa.Verify.AArch64.Cfg.finish c)))))) := by
  simp only [Impl.Ecdsa.Verify.AArch64.Cfg.final, List.append_assoc]

/-- `Z^(p-2)`, `x`, the last checks and the result. -/
theorem tail_ok (hc : BaseCfgOk c) {s₀ : State} {base : Addr} {g : Reg → BitVec 64}
    {s : State} (hP : FinalState c s₀ base g s) :
    WP isa (.seq c.pPow (Impl.Ecdsa.Verify.AArch64.Cfg.final c)) s fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        (s'.gpr .x0).setWidth 32 = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
          (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
          Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀) then 1 else 0 := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hP.scr.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  obtain hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hn3 := hc.n_ge
  have F := hP.fixed
  obtain hf : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  -- `Z^(p-2)`.
  refine WP.seq (WP.mono (pPow_ok hc hP.scr (modP_of hc F.mp) hP.rz_lt)
    fun s₁ ⟨K₁, U₁, lt₁, v₁⟩ => ?_)
  obtain hs₁ := hP.scr.of_keepRegs K₁ (x0_not_powClob h7)
  obtain F₁ := F.unch h7 hn (fixedOk_chainWc hc) U₁
  obtain e₁ : ∀ {i}, i < 45 → i ∉ [ACC, TMP] → sv c base s₁ i = sv c base s i := fun hi hl =>
    sv_unch U₁ h7 hn hi (apart_chainWc hc hi hl)
  rw [final_eq]
  -- `XM = X · ACC`.
  obtain hM₁ := modP_of hc F₁.mp
  refine WP.seq (WP.mono (slMulP_ok hc hs₁ hM₁ (o := XM) (a := RX) (b := ACC) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) lt₁) fun s₂ ⟨k₂, _, e₂⟩ => ?_)
  obtain hs₂ := k₂.scr hs₁
  obtain M₂ := hM₁.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  obtain v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ TMP → sv c base s₂ i = sv c base s₁ i := fun hi h₁ h₂ =>
    sv_keep (MP'_n c) rfl h7 hn k₂ hi h₁ h₂
  -- `X = XM · 1`.
  obtain one₂ : sv c base s₂ ONE = 1 := (v₂ (by decide) (by decide) (by decide)).trans F₁.one
  refine WP.seq (WP.mono (slMulP_ok hc hs₂ M₂ (o := X) (a := XM) (b := ONE) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [one₂]; omega_arith)) fun s₃ ⟨k₃, lt₃, e₃⟩ => ?_)
  obtain hs₃ := k₃.scr hs₂
  obtain v₃ : ∀ {i}, i < 45 → i ≠ X → i ≠ TMP → sv c base s₃ i = sv c base s₂ i := fun hi h₁ h₂ =>
    sv_keep (MP'_n c) rfl h7 hn k₃ hi h₁ h₂
  obtain x₃ : Fin.ofNat c.C.p (sv c base s₃ X) =
      tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) := by
    have acc₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RZ) ^ (c.C.p - 2) := v₁
    rw [toM_one_mul hpR (by rw [e₃, one₂]), toM_mul hpR e₂, acc₁]
    show toM _ _ (sv c base s₁ RX) * _ = toM _ _ (sv c base s RX) * toM _ _ (sv c base s RZ) ^ _
    rw [e₁ (by decide) (by decide)]
  -- `XN = x R mod n`, `W = XN - r R mod n`.
  obtain hMN₃ := modN_of hc (show wordsVal s₃.mem base (c.sl MN) c.n = c.C.n from
    (v₃ (by decide) (by decide) (by decide)).trans ((v₂ (by decide) (by decide) (by decide)).trans
      ((e₁ (by decide) (by decide)).trans F.mn)))
  obtain r2₃ : sv c base s₃ R2N = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n :=
    (v₃ (by decide) (by decide) (by decide)).trans ((v₂ (by decide) (by decide) (by decide)).trans
      ((e₁ (by decide) (by decide)).trans F.r2n))
  refine WP.seq (WP.mono (slMulN_ok hc hs₃ hMN₃ (o := XN) (a := X) (b := R2N) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [r2₃]; exact Nat.mod_lt _ (by omega_arith))) fun s₄ ⟨k₄, lt₄, e₄⟩ => ?_)
  obtain hs₄ := k₄.scr hs₃
  obtain M₄ := hMN₃.keepA64 (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₄ (by decide) (by decide)
  obtain v₄ : ∀ {i}, i < 45 → i ≠ XN → i ≠ TMP → sv c base s₄ i = sv c base s₃ i := fun hi h₁ h₂ =>
    sv_keep (MN'_n c) rfl h7 hn k₄ hi h₁ h₂
  obtain rm₄ : sv c base s₄ RM' = sv c base s RM' := by
    rw [v₄ (by decide) (by decide) (by decide), v₃ (by decide) (by decide) (by decide),
      v₂ (by decide) (by decide) (by decide), e₁ (by decide) (by decide)]
  refine WP.seq (WP.mono (slSub_ok (MN'_n c) h7 hs₄ M₄ (MN'_A c) (o := W) (a := XN) (b := RM') (by decide)
    (by decide) (by decide) lt₄ (by rw [rm₄]; exact hP.rm_lt)) fun s₅ ⟨k₅, e₅⟩ => ?_)
  obtain hs₅ := k₅.scr hs₄
  obtain v₅ : ∀ {i}, i < 45 → i ≠ W → i ≠ TMP → sv c base s₅ i = sv c base s₄ i := fun hi h₁ h₂ =>
    sv_keep (MN'_n c) rfl h7 hn k₅ hi h₁ h₂
  obtain w₅ : sv c base s₅ W = 0 ↔ Fin.ofNat c.C.n (sv c base s₃ X) = Fin.ofNat c.C.n (sigR c s₀) := by
    obtain hlt : sv c base s₅ W < c.C.n := by rw [e₅]; exact Nat.mod_lt _ (by omega_arith)
    rw [← toM_eq_zero_iff hnR hlt, e₅, toM_sub (by rw [rm₄]; have := hP.rm_lt; omega_arith), rm₄, hP.rm,
      toM_r2 hnR (by rw [e₄, r2₃])]
    constructor <;> intro h <;> grind
  -- The checks and the result.
  rw [WP.block_append_iff]
  refine WP.mono (checkNonzero_ok c hs₅ h0 (sl_le c h7 (i := RZ) (by decide)) hf
    (sl_mod8 c RZ) (sl_mod8 c FLAG)) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  obtain hs₆ := hs₅.of_keepRegs k₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checkZero_ok c hs₆ h0 (sl_le c h7 (i := W) (by decide)) hf
    (sl_mod8 c W) (sl_mod8 c FLAG)) fun s₇ ⟨f₇, k₇, O₇⟩ => ?_
  obtain hs₇ := hs₆.of_keepRegs k₇ (by decide)
  obtain U : Unch base (chainWc c ++ slW c [ACC, PT, TMP, XM, X, XN, W] ++ [(c.sl FLAG, 8)]) s.mem s₇.mem := by
    refine (U₁.trans ((unch_slots (MP'_n c) rfl k₂.unch (l := [XM, TMP]) (by simp) (by simp)).trans
      ((unch_slots (MP'_n c) rfl k₃.unch (l := [X, TMP]) (by simp) (by simp)).trans
      ((unch_slots (MN'_n c) rfl k₄.unch (l := [XN, TMP]) (by simp) (by simp)).trans
      ((unch_slots (MN'_n c) rfl k₅.unch (l := [W, TMP]) (by simp) (by simp)).trans
      (O₆.unch.trans O₇.unch)))))).mono fun w hw => ?_
    obtain sl : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ [ACC, PT, TMP, XM, X, XN, W]) → w ∈ slW c l →
        w ∈ chainWc c ++ slW c [ACC, PT, TMP, XM, X, XN, W] ++ [(c.sl FLAG, 8)] := fun hl hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (hl i hi)))
    simp only [List.mem_append] at hw
    rcases hw with hw | hw | hw | hw | hw | hw | hw
    · exact List.mem_append_left _ (List.mem_append_left _ hw)
    · exact sl (by decide) hw
    · exact sl (by decide) hw
    · exact sl (by decide) hw
    · exact sl (by decide) hw
    · exact List.mem_append_right _ hw
    · exact List.mem_append_right _ hw
  obtain hsv : Spill.Saved base g Cfg.saved s₇.mem :=
    Saved.unch F.saved (fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl | rfl
          exacts [sl_ge64 c ACC, Nat.le_trans (sl_ge64 c CT) (invTbl_ge hc), invTmp_ge64 hc]
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
          exact sl_ge64 c i
      · rw [List.mem_singleton.mp hw]
        exact sl_ge64 c FLAG)
      U
  obtain z₆ : sv c base s₅ RZ = sv c base s RZ := by
    rw [v₅ (by decide) (by decide) (by decide), v₄ (by decide) (by decide) (by decide),
      v₃ (by decide) (by decide) (by decide), v₂ (by decide) (by decide) (by decide),
      e₁ (by decide) (by decide)]
  obtain hflag : word s₇.mem base (c.sl FLAG) = if decide ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
      (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
      Fin.ofNat c.C.n (sv c base s₃ X) = Fin.ofNat c.C.n (sigR c s₀)) then BitVec.allOnes 64 else 0 := by
    obtain hW₆ : wordsVal s₆.mem base (c.sl W) c.n = sv c base s₅ W :=
      sv_flag O₆ h0 h7 hn (by decide) (by decide)
    obtain U₅ : Unch base (chainWc c ++ slW c [ACC, PT, TMP, XM, X, XN, W]) s.mem s₅.mem := by
      refine (U₁.trans ((unch_slots (MP'_n c) rfl k₂.unch (l := [XM, TMP]) (by simp) (by simp)).trans
        ((unch_slots (MP'_n c) rfl k₃.unch (l := [X, TMP]) (by simp) (by simp)).trans
        ((unch_slots (MN'_n c) rfl k₄.unch (l := [XN, TMP]) (by simp) (by simp)).trans
        (unch_slots (MN'_n c) rfl k₅.unch (l := [W, TMP]) (by simp) (by simp)))))).mono fun w hw => ?_
      obtain sl : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ [ACC, PT, TMP, XM, X, XN, W]) → w ∈ slW c l →
          w ∈ chainWc c ++ slW c [ACC, PT, TMP, XM, X, XN, W] := fun hl hw => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        exact List.mem_append_right _ (List.mem_map_of_mem (hl i hi))
      simp only [List.mem_append] at hw
      rcases hw with hw | hw | hw | hw | hw
      · exact List.mem_append_left _ hw
      · exact sl (by decide) hw
      · exact sl (by decide) hw
      · exact sl (by decide) hw
      · exact sl (by decide) hw
    have z₆' : wordsVal s₅.mem base (c.sl RZ) c.n = sv c base s RZ := z₆
    rw [f₇, f₆, hW₆, flag_unch_cw hc U₅ h7 h0 hn (by decide), hP.flag, z₆', mask_and, mask_and]
    simp only [mask, w₅, decide_eq_true_eq, and_assoc]
  refine WP.mono (vfinish_ok hc hs₇ hsv _ hflag) fun s' ⟨ret, saved⟩ => ⟨saved, _, lt₃, x₃, ?_⟩
  rw [ret]
  simp only [decide_eq_true_eq]

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `ProjectiveFlags` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

variable {c : VG.Impl.Ecdsa.AArch64.Cfg}

theorem projective_mov (s : State) (r : Reg) :
    WP isa (.block [.addImm .x r .x2 0]) s fun t => t.gpr r = s.gpr .x2 ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show (0 : Nat) < 4096 by decide,
    ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  exact RegUpd.gpr_write_of_ne _ _ _ hq

theorem projective_combine (s : State) :
    WP isa (.block [.logic .and .x .x2 .x2 .x6, .logic .orr .x .x2 .x2 .x4]) s fun t =>
      t.gpr .x2 = (s.gpr .x2 &&& s.gpr .x6) ||| s.gpr .x4 ∧ Keeps [.x2] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left', ↓reduceIte, reduceCtorEq]
  refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  simp only [RegUpd.gpr_write, hq, ↓reduceIte]

theorem projective_mask_or (p q : Prop) [Decidable p] [Decidable q] :
    mask p ||| mask q = mask (p ∨ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [mask, hp, hq]

/-- The public-coordinate comparisons leave their combined mask in `x2`. -/
theorem projectiveMatch_ok (hc : BaseCfgOk c) {s : State} {base : Addr} (hs : Scr s base size) :
    WP isa (.block (Impl.Ecdsa.Verify.AArch64.Cfg.projectiveMatch c)) s fun t =>
      t.gpr .x2 = mask (sv c base s W = 0 ∨
        (sv c base s K < sv c base s MN ∧ sv c base s XN = 0)) ∧
      Keeps [.x1, .x2, .x4, .x5, .x6, .x7, .x16] s t := by
  have hz := hc.n0
  have hl := hc.n10
  rw [Impl.Ecdsa.Verify.AArch64.Cfg.projectiveMatch]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok c hs hz (sl_le c hl (i := W) (by decide)) (sl_mod8 c W)) fun s₁ ⟨e₁,k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (projective_mov s₁ .x4) fun s₂ ⟨e₂,k₂⟩ => ?_
  obtain hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ltN_ok c hs₂ hz (sl_le c hl (i := K) (by decide))
    (sl_le c hl (i := MN) (by decide)) (sl_mod8 c K) (sl_mod8 c MN)) fun s₃ ⟨e₃,k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (projective_mov s₃ .x6) fun s₄ ⟨e₄,k₄⟩ => ?_
  obtain hs₄ := (hs₂.of_keeps k₃ (by decide)).of_keeps k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok c hs₄ hz (sl_le c hl (i := XN) (by decide)) (sl_mod8 c XN)) fun s₅ ⟨e₅,k₅⟩ => ?_
  refine WP.mono (projective_combine s₅) fun s₆ ⟨e₆,k₆⟩ => ⟨?_, ?_⟩
  · rw [e₆, e₅, k₅.gpr .x6 (by decide), e₄, e₃, k₅.gpr .x4 (by decide),
      k₄.gpr .x4 (by decide), k₃.gpr .x4 (by decide), e₂, e₁,
      k₄.mem, k₃.mem, k₂.mem, k₁.mem, mask_and, projective_mask_or]
    simp only [sv, or_comm, and_comm]
  · exact (k₁.mono (by sub_regs)).trans ((k₂.mono (by sub_regs)).trans
      ((k₃.mono (by sub_regs)).trans ((k₄.mono (by sub_regs)).trans
        ((k₅.mono (by sub_regs)).trans (k₆.mono (by sub_regs))))))


/-- The comparisons, nonzero test, return value and ABI restoration. -/
theorem projectiveChecks_ok (hc : BaseCfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    {g : Reg → BitVec 64} (hsv : Spill.Saved base g VG.Impl.Ecdsa.AArch64.Cfg.saved s.mem)
    (A : Prop) [Decidable A] (hf : word s.mem base (c.sl FLAG) = mask A) :
    WP isa (.block (Impl.Ecdsa.Verify.AArch64.Cfg.projectiveChecks c)) s fun t =>
      (∀ r ∈ VG.Impl.Ecdsa.AArch64.Cfg.saved.map Prod.fst, t.gpr r = g r) ∧
      (t.gpr .x0).setWidth 32 = if A ∧ sv c base s RZ ≠ 0 ∧
        (sv c base s W = 0 ∨ (sv c base s K < sv c base s MN ∧ sv c base s XN = 0)) then 1 else 0 := by
  have h0 := hc.n0
  have h7 := hc.n10
  obtain hflag : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  rw [Impl.Ecdsa.Verify.AArch64.Cfg.projectiveChecks]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (projectiveMatch_ok hc hs) fun s₁ ⟨e₁,k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (andFlag_ok c hs₁ hflag (sl_mod8 c FLAG)) fun s₂ ⟨e₂,k₂,O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checkNonzero_ok c hs₂ h0 (sl_le c h7 (i := RZ) (by decide)) hflag
    (sl_mod8 c RZ) (sl_mod8 c FLAG)) fun s₃ ⟨e₃,k₃,O₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  obtain U : Unch base [(c.sl FLAG, 8)] s.mem s₃.mem := by
    rw [← k₁.mem]
    exact (O₂.unch.trans O₃.unch).mono (by intro w hw; simpa using hw)
  obtain saved := Saved.unch hsv (fun w hw => by
    rw [List.mem_singleton.mp hw]
    exact sl_ge64 c FLAG) U
  obtain z₂ : wordsVal s₂.mem base (c.sl RZ) c.n = sv c base s RZ := by
    rw [show wordsVal s₂.mem base (c.sl RZ) c.n = sv c base s₁ RZ from
      sv_flag O₂ h0 h7 hs.nowrap (by decide) (by decide)]
    show wordsVal s₁.mem base (c.sl RZ) c.n = _
    rw [k₁.mem]
  obtain flag₃ : word s₃.mem base (c.sl FLAG) =
      mask (A ∧ sv c base s RZ ≠ 0 ∧
        (sv c base s W = 0 ∨ (sv c base s K < sv c base s MN ∧ sv c base s XN = 0))) := by
    rw [e₃,e₂,k₁.mem,hf,e₁,z₂,mask_and,mask_and]
    simp only [and_left_comm, and_comm]
  refine WP.mono (vfinish_ok hc hs₃ saved (decide (A ∧ sv c base s RZ ≠ 0 ∧
      (sv c base s W = 0 ∨ (sv c base s K < sv c base s MN ∧ sv c base s XN = 0)))) (by simpa only [mask, decide_eq_true_eq] using flag₃))
    fun t ⟨ret,keep⟩ => ⟨keep,?_⟩
  simpa only [decide_eq_true_eq] using ret

end VG.Proof.Ecdsa.Verify.AArch64

end

end

end

/-! ## `ProjectiveArithmetic` -/

@[expose] public section

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Impl.Ecdsa.Verify.AArch64.Cfg (projectiveOps)
variable {c : VG.Impl.Ecdsa.AArch64.Cfg}

abbrev projectiveSlots : List Nat := [X, XM, RZ, W, RX, ACC, XN]
abbrev projectiveReads : List Nat := [XM, RZ, RX, ACC]
abbrev projectiveWrites : List Nat := [X, W, XM, X, XN, TMP]

theorem projectiveOps_rename (sl : Nat → Nat) :
    projectiveOps sl = (projectiveOps id).map (FOp.rename sl) := rfl

theorem projectiveOps_run (hc : BaseCfgOk c) (e : Nat → Fe c.C) :
    runOps (projectiveOps c.sl) e (c.sl W) = e (c.sl RX) - e (c.sl XM) * e (c.sl RZ) ∧
    runOps (projectiveOps c.sl) e (c.sl XN) =
      e (c.sl RX) - (e (c.sl XM) + e (c.sl ACC)) * e (c.sl RZ) := by
  have hout : ∀ op ∈ projectiveOps id, op.out ≠ TMP ∧ op.out ≠ 54 ∧ op.out ≠ 61 ∧ op.out ≠ 82 := by decide
  have H := runOps_rename c.sl (projectiveOps id) e (fun op hop _ h =>
    sl_inj c hc.n0 h (.inr (hout op hop).2) (.inl (hout op hop).1))
  rw [← projectiveOps_rename] at H
  exact ⟨congrFun H W, congrFun H XN⟩

/-- The five field operations compute both projective differences. -/
theorem projectiveOps_ok (hc : BaseCfgOk c) {s : State} {base : Addr}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hlt : ∀ i ∈ projectiveReads, sv c base s i < c.C.p) :
    WP isa (fprogB c.MP' (projectiveOps c.sl)) s fun t =>
      Scr t base size ∧ Unch base (slW c projectiveWrites) s.mem t.mem ∧
      sv c base t W < c.C.p ∧ sv c base t XN < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t W) =
        tmv c.C c.n base s (c.sl RX) - tmv c.C c.n base s (c.sl XM) * tmv c.C c.n base s (c.sl RZ) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t XN) =
        tmv c.C c.n base s (c.sl RX) -
          (tmv c.C c.n base s (c.sl XM) + tmv c.C c.n base s (c.sl ACC)) * tmv c.C c.n base s (c.sl RZ) := by
  have hL : Lay c.MP' size (· ∈ projectiveSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  have hAl : Aligned c.MP' (· ∈ projectiveSlots.map c.sl) := ⟨fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx; exact sl_mod8 c i, MP'_A c,
    fun f m' h => (hc.call_p f m' h).2⟩
  have I : Inv c.MP' base size c.C.p (· ∈ projectiveSlots.map c.sl) (projectiveReads.map c.sl)
      (tmv c.C c.n base s) s := by
    refine ⟨hs, hM, ?_, ?_, fun _ _ => rfl⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have sub : ∀ i ∈ projectiveReads, i ∈ projectiveSlots := by decide
      exact List.mem_map_of_mem (sub i hi)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact hlt i hi
  have reads : readsOk (projectiveOps c.sl) (projectiveReads.map c.sl) = true := by
    rw [projectiveOps_rename]
    exact readsOk_rename c.sl (by decide)
  have hS : ∀ op ∈ projectiveOps c.sl, ∀ x ∈ op.out :: op.ins, x ∈ projectiveSlots.map c.sl := by
    intro op hop x hx
    simp only [projectiveOps, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> exact List.mem_map_of_mem (by decide)
  have hLo : ∀ op ∈ projectiveOps c.sl, Low c.MP' (op.out :: op.ins) := fun op hop =>
    Low.of_call fun _ _ _ x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (hS op hop x hx)
      have key : ∀ i ∈ projectiveSlots, i < 45 ∧ i ≠ TMP := by decide
      exact sl_own c hc.n10 (key i hi).1 (key i hi).2
  refine WP.mono (fprogB_ok hL hAl (unitMod_pow_two hc.p_odd _) _ I hS hLo reads)
    fun t ⟨keep, It⟩ => ?_
  have w : c.sl W ∈ validAfter (projectiveOps c.sl) (projectiveReads.map c.sl) := by
    simp [mem_validAfter, projectiveOps, FOp.out]
  have xn : c.sl XN ∈ validAfter (projectiveOps c.sl) (projectiveReads.map c.sl) := by
    simp [mem_validAfter, projectiveOps, FOp.out]
  have run := projectiveOps_run hc (tmv c.C c.n base s)
  exact ⟨It.scr, keep.unch, It.lt _ w, It.lt _ xn, (It.val _ w).trans run.1, (It.val _ xn).trans run.2⟩


abbrev projectivePrepareW : List Nat := [XM, ACC, MN]
abbrev projectiveAllW : List Nat := [XM, ACC, MN, X, W, XN, TMP]

theorem projectivePrepare_ok (hc : BaseCfgOk c) {s : State} {base : Addr} (hs : Scr s base size) :
    WP isa (.block (Impl.Ecdsa.Verify.AArch64.Cfg.projectivePrepare c)) s fun t =>
      Scr t base size ∧ Unch base (slW c projectivePrepareW) s.mem t.mem ∧
      sv c base t XM = c.R * c.R % c.C.p ∧ sv c base t ACC = c.mont c.C.n ∧
      sv c base t MN = c.C.p - c.C.n := by
  have hp := hc.p_ge
  have hpR := hc.p_lt
  have r2 : c.R * c.R % c.C.p < 2 ^ (64 * c.n) :=
    Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hpR
  have mont : c.mont c.C.n < 2 ^ (64 * c.n) :=
    Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hpR
  have sub : c.C.p - c.C.n < 2 ^ (64 * c.n) := by omega_arith
  rw [Impl.Ecdsa.Verify.AArch64.Cfg.projectivePrepare, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setSl_ok hc hs (o := XM) (by decide) r2) fun s₁ ⟨e₁,k₁,O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setSl_ok hc hs₁ (o := ACC) (by decide) mont) fun s₂ ⟨e₂,k₂,O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (setSl_ok hc hs₂ (o := MN) (by decide) sub) fun s₃ ⟨e₃,k₃,O₃⟩ => ?_
  have o : ∀ {s t : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem t.mem → i < 45 → i ≠ j →
      j ≠ 54 ∧ j ≠ 61 ∧ j ≠ 82 → sv c base t i = sv c base s i := fun O hi hij hj => sv_out O hc.n10 hs.nowrap hi hij hj
  exact ⟨hs₂.of_keepRegs k₃ (by decide), O₁.unch.trans (O₂.unch.trans O₃.unch),
    by rw [o O₃ (by decide) (by decide) (by decide), o O₂ (by decide) (by decide) (by decide), e₁],
    by rw [o O₃ (by decide) (by decide) (by decide), e₂], e₃⟩

/-- Convert `r` with the shared eight-word product when available. -/
theorem projectiveConvert_ok (hc : BaseCfgOk c) {s : State} {base : Addr}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hB : sv c base s XM < c.C.p) :
    WP isa (Impl.Ecdsa.Verify.AArch64.Cfg.projectiveConvert c) s fun t =>
      OpKeep c.MP' base (c.sl XM) s t ∧ sv c base t XM < c.C.p ∧
      sv c base t XM * 2 ^ (64 * c.n) % c.C.p = sv c base s K * sv c base s XM % c.C.p := by
  unfold Impl.Ecdsa.Verify.AArch64.Cfg.projectiveConvert
  split
  · exact slMulP_ok hc hs hM (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hB
  · exact slMul_ok (MP'_n c) hc.n10 hs hM (MP'_A c) (by decide) (by decide) (by decide) hB

/-- Prepare constants, convert `r`, and compute both differences. -/
theorem projectiveArithmetic_ok (hc : BaseCfgOk c) {s : State} {base : Addr}
    (hs : Scr s base size) (hmp : sv c base s MP = c.C.p)
    (hrx : sv c base s RX < c.C.p) (hrz : sv c base s RZ < c.C.p) :
    WP isa (.seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.projectivePrepare c))
      (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.projectiveConvert c)
        (fprogB c.MP' (projectiveOps c.sl)))) s fun t =>
      Scr t base size ∧ Unch base (slW c projectiveAllW) s.mem t.mem ∧
      sv c base t MN = c.C.p - c.C.n ∧ sv c base t W < c.C.p ∧ sv c base t XN < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t W) =
        tmv c.C c.n base s (c.sl RX) - Fin.ofNat c.C.p (sv c base s K) * tmv c.C c.n base s (c.sl RZ) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t XN) =
        tmv c.C c.n base s (c.sl RX) -
          (Fin.ofNat c.C.p (sv c base s K) + Fin.ofNat c.C.p c.C.n) * tmv c.C c.n base s (c.sl RZ) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp := hc.p_ge
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine WP.seq (WP.mono (projectivePrepare_ok hc hs) fun s₁ ⟨hs₁,U₁,xm₁,acc₁,mn₁⟩ => ?_)
  have v₁ : ∀ {i}, i < 45 → i ∉ projectivePrepareW → sv c base s₁ i = sv c base s i :=
    fun hi hl => sv_unch U₁ h7 hn hi (apart_slW hl)
  have M₁ : ModOkA c.MP' size c.C.p s₁.mem base := modP_of hc
    ((v₁ (i := MP) (by decide) (by decide)).trans hmp)
  refine WP.seq (WP.mono (projectiveConvert_ok hc hs₁ M₁ (by rw [xm₁]; exact Nat.mod_lt _ (by omega_arith)))
    fun s₂ ⟨k₂,lt₂,e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ TMP → sv c base s₂ i = sv c base s₁ i :=
    fun hi hio hit => sv_keep (MP'_n c) rfl h7 hn k₂ hi hio hit
  have M₂ := M₁.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  have xm₂ : tmv c.C c.n base s₂ (c.sl XM) = Fin.ofNat c.C.p (sv c base s K) := by
    show toM _ _ (sv c base s₂ XM) = _
    rw [toM_r2 (A := sv c base s₁ K) hpR (by rw [e₂, xm₁]; rfl), v₁ (by decide) (by decide)]
  have acc₂ : tmv c.C c.n base s₂ (c.sl ACC) = Fin.ofNat c.C.p c.C.n := by
    show toM _ _ (sv c base s₂ ACC) = _
    rw [v₂ (by decide) (by decide) (by decide), acc₁]
    exact toM_cmont hc _
  have tv₂ : ∀ {i}, i < 45 → i ∉ projectivePrepareW → i ≠ TMP →
      tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := fun {i} hi hl ht => by
    show toM _ _ (sv c base s₂ i) = toM _ _ (sv c base s i)
    rw [v₂ hi (fun he => hl (by rw [he]; decide)) ht, v₁ hi hl]
  refine WP.mono (projectiveOps_ok hc hs₂ M₂ (fun i hi => ?_)) fun s₃ ⟨hs₃,U₃,wlt,xnlt,wval,xnval⟩ => ?_
  · simp only [projectiveReads, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact lt₂
    · rw [v₂ (by decide) (by decide) (by decide), v₁ (by decide) (by decide)]; exact hrz
    · rw [v₂ (by decide) (by decide) (by decide), v₁ (by decide) (by decide)]; exact hrx
    · rw [v₂ (by decide) (by decide) (by decide), acc₁]; exact Nat.mod_lt _ (by omega_arith)
  have U₂ : Unch base (slW c [XM, TMP]) s₁.mem s₂.mem := k₂.unch
  have U : Unch base (slW c projectiveAllW) s.mem s₃.mem :=
    ((U₁.trans U₂).trans U₃).mono (by
      intro w hw
      simp only [slW, projectivePrepareW, projectiveWrites, projectiveAllW, List.map_cons, List.map_nil,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with ((h | h | h) | (h | h)) | (h | h | h | h | h | h) <;> simp [h])
  have mn₃ : sv c base s₃ MN = c.C.p - c.C.n := by
    have kept : sv c base s₃ MN = sv c base s₂ MN :=
      sv_unch U₃ h7 hn (i := MN) (by decide) (apart_slW (by decide))
    rw [kept, v₂ (by decide) (by decide) (by decide), mn₁]
  refine ⟨hs₃,U,mn₃,wlt,xnlt,?_,?_⟩
  · rw [wval, xm₂, tv₂ (by decide) (by decide) (by decide), tv₂ (by decide) (by decide) (by decide)]
  · rw [xnval, xm₂, acc₂, tv₂ (by decide) (by decide) (by decide), tv₂ (by decide) (by decide) (by decide)]

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `ProjectiveFinal` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
variable {c : VG.Impl.Ecdsa.AArch64.Cfg}

/-- The inversion-free final check has the same result as affine conversion. -/
theorem projectiveFinal_ok (hc : BaseCfgOk c) (hC : Law c.C) (hnp : c.C.n < c.C.p)
    (hpn : c.C.p ≤ 2 * c.C.n) {s₀ : State} {base : Addr} {g : Reg → BitVec 64}
    {s : State} (hP : FinalState c s₀ base g s) :
    WP isa (Impl.Ecdsa.Verify.AArch64.Cfg.projectiveFinal c) s fun s' =>
      (∀ r ∈ VG.Impl.Ecdsa.AArch64.Cfg.saved.map Prod.fst, s'.gpr r = g r) ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        (s'.gpr .x0).setWidth 32 = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
          (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
          Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀) then 1 else 0 := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hP.scr.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  let A := KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
    (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)
  let fx := tmv c.C c.n base s (c.sl RX)
  let fz := tmv c.C c.n base s (c.sl RZ)
  let xo := (fx * fz ^ (c.C.p - 2)).val
  rw [Impl.Ecdsa.Verify.AArch64.Cfg.projectiveFinal]
  refine WP.seq (WP.mono (projectiveArithmetic_ok hc hP.scr hP.fixed.mp hP.rx_lt hP.rz_lt)
    fun t ⟨ht,U,mn,wlt,xnlt,wval,xnval⟩ => ?_)
  have v : ∀ {i}, i < 45 → i ∉ projectiveAllW → sv c base t i = sv c base s i :=
    fun hi hl => sv_unch U h7 hn hi (apart_slW hl)
  have saved := Saved.unch hP.fixed.saved (fun w hw => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact sl_ge64 c i) U
  have flag : word t.mem base (c.sl FLAG) = mask A := by
    rw [U.word (fun w hw => ?_) (by have := sl_le c h7 (i := FLAG) (by decide); omega_arith)]
    · exact hP.flag
    · exact (apart_slW (c := c) (i := FLAG) (by decide)) w hw |>.elim
        (fun h => Or.inl (by have := hc.n0; omega_arith)) Or.inr
  have wz : sv c base t W = 0 ↔ fx = Fin.ofNat c.C.p (sigR c s₀) * fz := by
    rw [← toM_eq_zero_iff hpR wlt, wval, hP.k]
    change fx - Fin.ofNat c.C.p (sigR c s₀) * fz = 0 ↔ _
    constructor <;> intro h <;> grind
  have xnz : sv c base t XN = 0 ↔ fx = (Fin.ofNat c.C.p (sigR c s₀) + Fin.ofNat c.C.p c.C.n) * fz := by
    rw [← toM_eq_zero_iff hpR xnlt, xnval, hP.k]
    change fx - (Fin.ofNat c.C.p (sigR c s₀) + Fin.ofNat c.C.p c.C.n) * fz = 0 ↔ _
    constructor <;> intro h <;> grind
  have z : fz ≠ 0 ↔ sv c base s RZ ≠ 0 := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
  refine WP.mono (projectiveChecks_ok hc ht saved A flag) fun s' ⟨keep,ret⟩ => ?_
  refine ⟨keep, xo, (fx * fz ^ (c.C.p - 2)).isLt, Fin.ofNat_val_eq_self _, ?_⟩
  simp only [v (i := RZ) (by decide) (by decide), v (i := K) (by decide) (by decide), hP.k, mn, wz, xnz] at ret
  have iff : (A ∧ sv c base s RZ ≠ 0 ∧
      (fx = Fin.ofNat c.C.p (sigR c s₀) * fz ∨
        (sigR c s₀ < c.C.p - c.C.n ∧ fx = (Fin.ofNat c.C.p (sigR c s₀) + Fin.ofNat c.C.p c.C.n) * fz))) ↔
      (A ∧ sv c base s RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
    constructor
    · rintro ⟨ha,hz,hm⟩
      exact ⟨ha,hz,(Proof.Ecdsa.projective_matches hC hnp hpn (z.mpr hz) ha.2.1.2).mpr hm⟩
    · rintro ⟨ha,hz,hm⟩
      exact ⟨ha,hz,(Proof.Ecdsa.projective_matches hC hnp hpn (z.mpr hz) ha.2.1.2).mp hm⟩
  simpa only [iff] using ret

theorem tail_dispatch_ok (hc : BaseCfgOk c) (hC : Law c.C) {s₀ : State} {base : Addr} {g : Reg → BitVec 64}
    {s : State} (hP : FinalState c s₀ base g s) :
    WP isa (Impl.Ecdsa.Verify.AArch64.Cfg.tail c) s fun s' =>
      (∀ r ∈ VG.Impl.Ecdsa.AArch64.Cfg.saved.map Prod.fst, s'.gpr r = g r) ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        (s'.gpr .x0).setWidth 32 = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
          (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
          Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀) then 1 else 0 := by
  unfold Impl.Ecdsa.Verify.AArch64.Cfg.tail
  split
  · rename_i h
    exact projectiveFinal_ok hc hC h.1 h.2 hP
  · exact tail_ok hc hP

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `Main` -/

section

/-!
# ECDSA verification on AArch64: the whole function

`verify_ok`: `Cfg.verify` returns 1 exactly if the specification's
verification of the signature holds, for any curve the proof of the code
supports (`CfgOk`) whose group law the proofs support (`Law`), and
restores the callee-saved registers. `front_ok`, `mid_ok`, `points_ok` and
`tail_dispatch_ok` compute what `verify_eq` connects to the specification.
-/

namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V)

variable {c : Cfg}

/-- The result the contract asks for: 1 exactly if the specification's
verification holds. -/
def VPost (c : Cfg) (s₀ s' : State) : Prop :=
  (s'.gpr .x0).setWidth 32 =
    if Spec.Ecdsa.verify c.C (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len))
      (Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x1) c.C.len))
      (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (2 * c.C.len)) then 1 else 0

theorem verify_eq'' (c : Cfg) : Impl.Ecdsa.Verify.AArch64.Cfg.verify c =
    .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.args c)) (.seq (.seq (.block (c.setupWith (some D)))
      (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) (.block [])))
      (.seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.loadS c)) (.seq (.block (Impl.Ecdh.AArch64.Cfg.peer c))
      (.seq (Impl.Ecdh.AArch64.Cfg.validate c) (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.scalars c)
      (.seq c.nPow (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.uv c)
      (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.points c) (Impl.Ecdsa.Verify.AArch64.Cfg.tail c))))))))) := rfl

/-- What the slot of Montgomery's one stands for. -/
theorem onep_tmv (hc : BaseCfgOk c) {base : Addr} {g : Reg → BitVec 64} {s : State}
    (F : Fixed c base g s.mem) : tmv c.C c.n base s (c.sl ONEP) = 1 := by
  show toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n) = _
  rw [F.onep]; exact toM_one (unitMod_pow_two hc.p_odd _)

/-- `vg_ecdsa_<curve>_verify` returns whether the specification's
verification holds, and restores the callee-saved registers. -/
theorem verify_ok (hc : CfgOk c) (hC : Law c.C) (hT : CombOkW c.C Cfg.combW (Cfg.combJ c.n) c.tbl c.start)
    {s₀ : State} (hp : VPre c s₀) :
    WP isa (Impl.Ecdsa.Verify.AArch64.Cfg.verify c) s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ VPost c s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  rw [verify_eq'']
  refine front_ok hc hp fun g s₁ hg hF => mid_ok hc hF fun s₂ hM => ?_
  have F₂ := hM.fixed
  have h1 := onep_tmv hc F₂
  -- The point the window method multiplies.
  let P := peerPt c (s₀.mem (s₀.gpr .x0) = 4) (keyX c s₀) (keyY c s₀)
  have hPc : onCurve c.C P = true := peerPt_onCurve hc _ _ _
  have hG : Rep c.C (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl GX)) (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl GY))
      (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl ONEP)) (G c.C) := by
    show Rep c.C (toM _ _ (wordsVal s₂.mem _ (c.sl GX) c.n)) (toM _ _ (wordsVal s₂.mem _ (c.sl GY) c.n))
      (toM _ _ (wordsVal s₂.mem _ (c.sl ONEP) c.n)) (G c.C)
    rw [F₂.gx, F₂.gy, toM_cmont hc, toM_cmont hc, show toM c.C.p (2 ^ (64 * c.n))
      (wordsVal s₂.mem (s₀.gpr .x3) (c.sl ONEP) c.n) = 1 from h1]
    exact rep_affine' hC _ _
  have hQ : Rep c.C (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl PX)) (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl PY))
      (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl ONEP)) P := by
    rw [h1]
    exact peerPt_rep hC _ _ _ hM.px hM.py
  have hu : sv c (s₀.gpr .x3) s₂ U < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
  have hv : sv c (s₀.gpr .x3) s₂ V < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
  refine points_ok hc hM
    (Q₁ := fun j X Y Z => Rep c.C X Y Z (mul (sv c (s₀.gpr .x3) s₂ U >>> j) (G c.C)))
    (Q₂ := fun j X Y Z => Rep c.C X Y Z (mul (sv c (s₀.gpr .x3) s₂ V >>> j) P))
    hC hT hp.tbl (fun X Y Z h => by simp only [Nat.shiftRight_zero]; exact h) hPc hQ
    (fun X Y Z h => by simp only [Nat.shiftRight_zero]; exact h) fun s₃ hP => ?_
  refine WP.mono (tail_dispatch_ok hc hC hP.toFinalState) fun s' ⟨saved, xo, hxo, hx, ret⟩ =>
    ⟨fun r hr => (saved r hr).trans (hg r hr), ?_⟩
  obtain ⟨X1, Y1, Z1, X2, Y2, Z2, q1, q2, hsum⟩ := hP.pt
  have q1' : Rep c.C X1 Y1 Z1 (mul (sv c (s₀.gpr .x3) s₂ U) (G c.C)) := by
    have := q1; simp only [Nat.shiftRight_zero] at this; exact this
  have q2' : Rep c.C X2 Y2 Z2 (mul (sv c (s₀.gpr .x3) s₂ V) P) := by
    have := q2; simp only [Nat.shiftRight_zero] at this; exact this
  have hR := Rep.add hC (hC.onCurve_mul hc.onG _) (hC.onCurve_mul hPc _) q1' q2' hsum.symm
  -- The arguments as the specification reads them.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega_arith
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).head? = some (s₀.mem (s₀.gpr .x0)) := by
    rw [peer_bytes]; rfl
  have hxv : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s₀ := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
  have hyv : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s₀ := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (s₀.gpr .x0)) (keyX c s₀) (keyY c s₀),
      P = .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    show peerPt c _ _ _ = _
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have h16 : 2 * c.C.len = c.C.len + c.C.len := by omega_arith
  have hr : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (2 * c.C.len)).take c.C.len) = sigR c s₀ := by
    rw [h16, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]
  have hs : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (2 * c.C.len)).drop c.C.len) = sigS c s₀ := by
    rw [h16, bytesAt_add, List.drop_left' (length_bytesAt _ _ _)]
  have hspec := Proof.Ecdsa.verify_eq hC hlen hb0 hxv hyv hP' hr hs hM.u_lt hM.v_lt hM.u hM.v hR hxo hx
  -- The conditions.
  have hz := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
  have hiff : (Ecdh.Valid c.C (s₀.mem (s₀.gpr .x0)) (keyX c s₀) (keyY c s₀) ∧
      (1 ≤ sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (1 ≤ sigS c s₀ ∧ sigS c s₀ < c.C.n) ∧
      tmv c.C c.n (s₀.gpr .x3) s₃ (c.sl RZ) ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) ↔
      ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
        sv c (s₀.gpr .x3) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
    constructor
    · rintro ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hZ, he⟩
      exact ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hz.mp hZ, he⟩
    · rintro ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hZ, he⟩
      exact ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hz.mpr hZ, he⟩
  unfold VPost
  rw [hashToInt_eq c, hspec, ret]
  by_cases h : (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
      sv c (s₀.gpr .x3) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)
  · rw [ite_eq_left (decide_eq_true (hiff.mpr h)), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp (of_decide_eq_true h'))), ite_eq_right h]

end VG.Proof.Ecdsa.Verify.AArch64

end
