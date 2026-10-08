import VerifiedGarbage.Proof.Ecdh.AArch64.Window
import VerifiedGarbage.Proof.Ecdh.Exchange

/-!
# ECDH on AArch64: the result, and the whole function

## `x`, the checks and the result

`middle` computes `x = X Z^(p-2)` from `X` and the power in `ACC`, left
Montgomery's form by a multiplication by 1, ands the masks of `d ∈ [1, n-1]`
and `Z ≠ 0` into the flag, and writes `x` or zeros (`middle_ok`); `finish`
writes the result as the signature's does (`ecFinish_ok`).
-/

namespace VG.Proof.Ecdh.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

variable {c : Cfg}

theorem finish_eq (c : Cfg) : Impl.Ecdh.AArch64.Cfg.finish c =
    ([ld .x3 (c.sl FLAG)] : List Instr) ++ (storeBytes c.C.len c.n .x20 0 (c.sl X) ++
    (Spill.restoreCode .x0 Cfg.saved ++ ([.movz .x .x1 1 0, .logic .and .x .x0 .x3 .x1] : List Instr))) := by
  simp only [Impl.Ecdh.AArch64.Cfg.finish, List.append_assoc]; rfl

/-- `x` or zeros, the return value and the callee-saved registers. -/
theorem ecFinish_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {out : Addr}
    (hx20 : s.gpr .x20 = out) (hfit : out.toNat + c.C.len ≤ 2 ^ 64) (hw : (⟨out, c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, c.C.len⟩ ⟨base, size⟩)
    {g : Reg → BitVec 64} (hsv : Spill.Saved base g Cfg.saved s.mem) (b : Bool)
    (hf : word s.mem base (c.sl FLAG) = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block (Impl.Ecdh.AArch64.Cfg.finish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out c.C.len =
        (if b then toBytes c.C.len (sv c base s X) else List.replicate c.C.len 0) ∧
      (s'.gpr .x0).setWidth 32 = (if b then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) := by
  have h7 := hc.n10
  have hn0 := hc.n0
  have hn := hs.nowrap
  have hl8 := hc.len8
  have hlo := hc.len_lo
  have hhi := hc.len_hi
  have hX := sl_le c h7 (i := X) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have h0 : ∀ e, out + BitVec.ofNat 64 0 + BitVec.ofNat 64 e = out + BitVec.ofNat 64 e := fun e =>
    congrArg (· + BitVec.ofNat 64 e) (BitVec.add_zero out)
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (ld_ok hs (d := c.sl FLAG) (by omega) (sl_mod8 c FLAG) .x3) fun s₁ ⟨e₁, k₁, _⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.mem
  have hx20₁ : s₁.gpr .x20 = out := by rw [k₁.gpr _ (by decide), hx20]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok hs₁ (dst := .x20) (d := 0) (a := c.sl X) (by decide) (by decide) (by decide) b
    (by rw [e₁, hf]) hX (sl_mod8 c X) (by omega) hlo hhi (by omega) (by rw [hx20₁, BitVec.add_zero]; omega)
    (fun e m he => ⟨_, by rw [k₁.wr]; exact hw, by
      rw [hx20₁, h0]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [hx20₁, BitVec.add_zero]; exact (hd.symm.sub_left (Offset.sub_base base hX))))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  rw [hx20₁, BitVec.add_zero] at e₂ O₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have U₂ := O₂.unch_far hd.symm
  have hx3₂ : s₂.gpr .x3 = if b then BitVec.allOnes 64 else 0 := by
    rw [k₂.gpr _ (by decide), e₁, hf]
  have hsv₂ : Spill.Saved base g Cfg.saved s₂.mem := by
    have h16 : ∀ w ∈ [(size, 2 ^ 64)], 64 ≤ w.1 := fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw; decide
    exact Saved.unch (hm₁ ▸ hsv) h16 U₂
  refine Spill.restore_ok hs₂.x0 (by decide) (by decide) (fun p hp => ?_) hsv₂ fun s₃ R₃ => ?_
  · have := saved_lt p hp
    exact ⟨_, List.mem_append_right _ hs₂.wr, hs₂.contains (by have : size = 8192 := rfl; omega) (by decide)⟩
  refine WP.mono (retBit_ok s₃) fun s₄ ⟨e₄, k₄⟩ => ⟨?_, ?_, fun r hr => ?_⟩
  · rw [k₄.mem, R₃.mem, e₂, hm₁]
  · have hx3 : Reg.x3 ∉ Cfg.saved.map Prod.fst := by decide
    rw [e₄, R₃.other _ hx3, hx3₂, mask_bit]
  · have : r ∉ [Reg.x0, .x1] := by
      revert r; decide
    rw [k₄.gpr r this]
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact R₃.gpr p hp

theorem middle_eq (c : Cfg) : Impl.Ecdh.AArch64.Cfg.middle c =
    .seq (.block (Impl.Mont.AArch64.mul c.MP' (c.sl XM) (c.sl RX) (c.sl ACC)))
    (.seq (.block (Impl.Mont.AArch64.mul c.MP' (c.sl X) (c.sl XM) (c.sl ONE)))
    (.block (c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ Impl.Ecdh.AArch64.Cfg.finish c))) := rfl

/-- Whether the result is a shared secret: the peer's key (`V`), `d` in
`[1, n-1]`, and `Z ≠ 0`. -/
abbrev ok (c : Cfg) (base : Addr) (s : State) (V : Prop) [Decidable V] : Bool :=
  decide ((V ∧ 0 < sv c base s D ∧ sv c base s D < c.C.n) ∧ sv c base s RZ ≠ 0)

/-- `x`, the checks of `d` and `Z`, and the result. -/
theorem middle_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) (hacc : sv c base s ACC < c.C.p)
    {V : Prop} [Decidable V] (hflag : word s.mem base (c.sl FLAG) = mask V) {out : Addr}
    (hx20 : s.gpr .x20 = out) (hfit : out.toNat + c.C.len ≤ 2 ^ 64) (hw : (⟨out, c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, c.C.len⟩ ⟨base, size⟩) :
    WP isa (Impl.Ecdh.AArch64.Cfg.middle c) s fun s' => ∃ xv, xv < c.C.p ∧
      Fin.ofNat c.C.p xv =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      Spec.Ecdsa.bytesAt s'.mem out c.C.len =
        (if ok c base s V then toBytes c.C.len xv else List.replicate c.C.len 0) ∧
      (s'.gpr .x0).setWidth 32 = (if ok c base s V then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hf : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  rw [middle_eq]
  have hM := modP_of hc F.mp
  have hone : sv c base s ONE = 1 := F.one
  -- `XM = X · ACC`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) h7 hs hM (MP'_A c) (o := XM) (a := RX) (b := ACC) (by decide)
    (by decide) (by decide) hacc) fun s₁ ⟨k₁, _, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have kP₁ := hM.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have v₁ : ∀ {i}, i < 45 → i ≠ XM → i ≠ TMP → sv c base s₁ i = sv c base s i := fun hi h₁ h₂ =>
    sv_keep (MP'_n c) rfl h7 hn k₁ hi h₁ h₂
  -- `X = XM · 1`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) h7 hs₁ kP₁ (MP'_A c) (o := X) (a := XM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [v₁ (by decide) (by decide) (by decide), hone]; omega))
    fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ X → i ≠ TMP → sv c base s₂ i = sv c base s i := fun hi h₁ h₂ h₃ =>
    (sv_keep (MP'_n c) rfl h7 hn k₂ hi h₂ h₃).trans (v₁ hi h₁ h₃)
  have x₂ : Fin.ofNat c.C.p (sv c base s₂ X) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) := by
    rw [toM_one_mul hpR (by rw [e₂, v₁ (i := ONE) (by decide) (by decide) (by decide), hone]),
      toM_mul hpR e₁]
  have U₂ : Unch base (slW c [XM, X, TMP]) s.mem s₂.mem :=
    ((unch_slots (MP'_n c) rfl k₁.unch (l := [XM, X, TMP]) (by simp) (by simp)).trans
      (unch_slots (MP'_n c) rfl k₂.unch (l := [XM, X, TMP]) (by simp) (by simp))).mono
      fun w hw => by simp only [List.mem_append, or_self] at hw; exact hw
  have F₂ := F.unch h7 hn (fixedOk_slW (l := [XM, X, TMP]) (by decide)) U₂
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (checkRange_ok c hs₂ h0 (sl_le c h7 (i := D) (by decide)) (sl_le c h7 (i := MN) (by decide))
    hf (sl_mod8 c D) (sl_mod8 c MN) (sl_mod8 c FLAG)) fun s₅ ⟨f₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₂.of_keepRegs k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checkNonzero_ok c hs₅ h0 (sl_le c h7 (i := RZ) (by decide)) hf
    (sl_mod8 c RZ) (sl_mod8 c FLAG)) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  have F₆ := (F₂.unch h7 hn fixedOk_flag O₅.unch).unch h7 hn fixedOk_flag O₆.unch
  have hflag₆ : word s₆.mem base (c.sl FLAG) = if ok c base s V then BitVec.allOnes 64 else 0 := by
    have hMN : wordsVal s₂.mem base (c.sl MN) c.n = c.C.n := F₂.mn
    have z₂ : wordsVal s₂.mem base (c.sl RZ) c.n = sv c base s RZ := v₂ (by decide) (by decide) (by decide) (by decide)
    have d₂ : wordsVal s₂.mem base (c.sl D) c.n = sv c base s D := v₂ (by decide) (by decide) (by decide) (by decide)
    rw [f₆, f₅, flag_unch U₂ h7 h0 hn (by decide), hflag, sv_flag O₅ h0 h7 hn (i := RZ) (by decide)
      (by decide), hMN, z₂, d₂, mask_and, mask_and]
    simp only [mask, decide_eq_true_eq, and_assoc]
  have hx20₆ : s₆.gpr .x20 = out := by
    rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₂.gpr _ (x20_not_clob h7),
      k₁.gpr _ (x20_not_clob h7), hx20]
  have hw₆ : (⟨out, c.C.len⟩ : Region) ∈ s₆.wr := by rw [k₆.wr, k₅.wr, k₂.wr, k₁.wr]; exact hw
  refine WP.mono (ecFinish_ok hc hs₆ hx20₆ hfit hw₆ hd F₆.saved _ hflag₆) fun s' ⟨bytes, ret, saved⟩ =>
    ⟨_, lt₂, x₂, ?_, ret, saved⟩
  have x₆ : sv c base s₆ X = sv c base s₂ X := (sv_flag O₆ h0 h7 hn (i := X) (by decide) (by decide)).trans
    (sv_flag O₅ h0 h7 hn (i := X) (by decide) (by decide))
  rw [bytes, x₆]

end VG.Proof.Ecdh.AArch64

/-!
## The whole function

`exchange_ok`: `Cfg.exchange` computes the specification's shared secret of
`d` and the peer's public key, for any curve the ECDSA proof supports
(`CfgOk`), and restores the callee-saved registers.

After `args`, the signature's setup and tables (`stage₁`, whose `SetupPre`
the arguments meet as they are) read `d` and the peer's `x`; then `peer_ok`,
`validate_ok`, `winPow_ok` and `middle_ok`; `exchange_eq` connects what they
compute to the specification.
-/

namespace VG.Proof.Ecdh.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Impl.Ecdh.AArch64 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)

variable {c : Cfg}

/-- The arguments: `out = x0` (`len` bytes), `d = x1` (`len` bytes),
`peer = x2` (`1 + 2 len` bytes) and `scratch = x3`, readable and writable as
the contract says and apart from each other as it says. -/
structure EPre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x1, c.C.len⟩, ⟨s.gpr .x2, 1 + 2 * c.C.len⟩]
  wr : s.wr = [⟨s.gpr .x0, c.C.len⟩, ⟨s.gpr .x3, size⟩]
  out_sc : Region.Disjoint ⟨s.gpr .x0, c.C.len⟩ ⟨s.gpr .x3, size⟩
  d_sc : Region.Disjoint ⟨s.gpr .x1, c.C.len⟩ ⟨s.gpr .x3, size⟩
  peer_sc : Region.Disjoint ⟨s.gpr .x2, 1 + 2 * c.C.len⟩ ⟨s.gpr .x3, size⟩
  out_fit : (s.gpr .x0).toNat + c.C.len ≤ 2 ^ 64
  sc_fit : (s.gpr .x3).toNat + size ≤ 2 ^ 64

/-- The private key. -/
abbrev dk (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x1) c.C.len)

/-- The result the contract asks for: the specification's shared secret, and
`1`, or zeros and `0`. -/
def EPost (c : Cfg) (s₀ s' : State) : Prop :=
  match Spec.Ecdh.exchange c.C (dk c s₀) (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (1 + 2 * c.C.len)) with
  | some z => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .x0) c.C.len = z
  | none => (s'.gpr .x0).setWidth 32 = 0 ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .x0) c.C.len = List.replicate c.C.len 0

theorem args_ok (s : State) :
    WP isa (.block Impl.Ecdh.AArch64.Cfg.args) s fun s' =>
      s'.gpr .x4 = s.gpr .x3 ∧ s'.gpr .x6 = s.gpr .x2 ∧ s'.gpr .x3 = s.gpr .x1 ∧
        s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 1 ∧ Keeps [.x2, .x3, .x4, .x6] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Ecdh.AArch64.Cfg.args, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (0 : Nat) < 4096 by decide, show (1 : Nat) < 4096 by decide, ite_true, RegUpd.gpr_write,
    BitVec.setWidth_eq, BitVec.add_zero, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- The point the window method multiplies: the peer's, if its key is valid as the
code checks it, else `G`. -/
def peerPt (c : Cfg) (b4 : Prop) [Decidable b4] (x y : Nat) : Point c.C :=
  if h : ((b4 ∧ x < c.C.p) ∧ y < c.C.p) ∧ OnCurve c (Fin.ofNat c.C.p x) (Fin.ofNat c.C.p y) then .affine ⟨x, h.1.1.2⟩ ⟨y, h.1.2⟩ else G c.C

theorem peerPt_onCurve (hc : BaseCfgOk c) (b4 : Prop) [Decidable b4] (x y : Nat) :
    onCurve c.C (peerPt c b4 x y) = true := by
  unfold peerPt
  split
  · next h => exact (onCurve_iff _ _).mpr h.2
  · exact hc.onG

theorem peerPt_rep (hC : Law c.C) (b4 : Prop) [Decidable b4] (x y : Nat) {X Y : Fe c.C}
    (hX : X = if ((b4 ∧ x < c.C.p) ∧ y < c.C.p) ∧ OnCurve c (Fin.ofNat c.C.p x) (Fin.ofNat c.C.p y)
      then Fin.ofNat c.C.p x else Fin.ofNat c.C.p c.C.gx)
    (hY : Y = if ((b4 ∧ x < c.C.p) ∧ y < c.C.p) ∧ OnCurve c (Fin.ofNat c.C.p x) (Fin.ofNat c.C.p y)
      then Fin.ofNat c.C.p y else Fin.ofNat c.C.p c.C.gy) :
    Rep c.C X Y 1 (peerPt c b4 x y) := by
  unfold peerPt
  by_cases h : ((b4 ∧ x < c.C.p) ∧ y < c.C.p) ∧ OnCurve c (Fin.ofNat c.C.p x) (Fin.ofNat c.C.p y)
  · rw [dite_eq_left h]; rw [ite_eq_left h] at hX hY
    rw [hX, hY]
    exact ⟨one_ne_zero_fe hC, by rw [EcKey.fe_eq h.1.1.2 rfl, Lean.Grind.Semiring.mul_one],
      by rw [EcKey.fe_eq h.1.2 rfl, Lean.Grind.Semiring.mul_one]⟩
  · rw [dite_eq_right h]; rw [ite_eq_right h] at hX hY; rw [hX, hY]
    exact rep_affine' hC _ _

/-- The peer's key: `04`, `x` and `y`. -/
theorem peer_bytes (m : Mem) (p : Addr) (n : Nat) :
    Spec.Ecdsa.bytesAt m p (1 + 2 * n) = m p :: (Spec.Ecdsa.bytesAt m (p + BitVec.ofNat 64 1) n ++
      Spec.Ecdsa.bytesAt m (p + BitVec.ofNat 64 (1 + n)) n) := by
  have h1 : Spec.Ecdsa.bytesAt m p 1 = [m p] := by
    simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero]
  rw [show 1 + 2 * n = 1 + (n + n) by omega, bytesAt_add, bytesAt_add, h1, BitVec.add_assoc,
    BitVec.ofNat_add_ofNat]
  rfl

theorem exchange_eq' (c : Cfg) : Impl.Ecdh.AArch64.Cfg.exchange c =
    .seq (.block Impl.Ecdh.AArch64.Cfg.args) (.seq (.seq (.block c.setup)
      (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) (.block [])))
    (.seq (.block (Impl.Ecdh.AArch64.Cfg.peer c)) (.seq (Impl.Ecdh.AArch64.Cfg.validate c)
    (.seq (c.winPrep (c.sl K)) (.seq (WinCfg.window (winQ c)) (.seq c.pPow
      (Impl.Ecdh.AArch64.Cfg.middle c))))))) := rfl

/-- `vg_ecdh_<curve>` computes the specification's shared secret and restores
the callee-saved registers. -/
theorem exchange_ok (hc : CfgOk c) (hC : Law c.C) {s₀ : State} (hp : EPre c s₀) :
    WP isa (Impl.Ecdh.AArch64.Cfg.exchange c) s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ EPost c s₀ s' := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  rw [exchange_eq']
  refine WP.seq (WP.mono (args_ok s₀) fun s₁ ⟨x4₁, x6₁, x3₁, x2₁, k₁⟩ => ?_)
  have x1₁ : s₁.gpr .x1 = s₀.gpr .x1 := k₁.gpr _ (by decide)
  have x0₁ : s₁.gpr .x0 = s₀.gpr .x0 := k₁.gpr _ (by decide)
  have hrd₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [k₁.rd, k₁.wr]
  have hl8 := hc.len8
  have hhi := hc.len_hi
  have hsp : SetupPre c s₁ := by
    refine ⟨by rw [k₁.wr, hp.wr, x4₁]; simp, fun e he => ?_, fun e he => ?_, fun e he => ?_, ?_, ?_, ?_,
      by rw [x4₁]; exact hp.sc_fit⟩
    · rw [x3₁, hrd₁, hp.rd]
      exact ⟨_, by simp, Offset.contains_base _ he (by omega)⟩
    · rw [x1₁, hrd₁, hp.rd]
      exact ⟨_, by simp, Offset.contains_base _ he (by omega)⟩
    · rw [x2₁, hrd₁, hp.rd, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact ⟨⟨s₀.gpr .x2, 1 + 2 * c.C.len⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [x1₁, x4₁]; exact hp.d_sc
    · rw [x2₁, x4₁]; exact hp.peer_sc.sub_left (Offset.sub_base _ (by omega))
    · rw [x3₁, x4₁]; exact hp.d_sc
  refine WP.seq (WP.mono (stage₁ hc (.inl rfl) hsp (rest := .block []) (Q := St₁ c none s₁ (s₁.gpr .x4))
    fun _ S => WP.block_nil S) fun s₂ S₂ => ?_)
  rw [x4₁] at S₂
  have hn := S₂.scr.nowrap
  have hq₂ : s₂.gpr .x6 = s₀.gpr .x2 := by rw [S₂.gpr _ (by decide), x6₁]
  have hrw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [S₂.rd, S₂.wr, hrd₁]
  -- The peer's key.
  refine WP.seq (WP.mono (peer_ok hc S₂.scr hq₂ (by rw [hrw₂, hp.rd]; simp) hp.peer_sc S₂.fixed.mp)
    fun s₃ ⟨hs₃, k₃, U₃, r2₃, bp₃, y₃, f₃⟩ => ?_)
  have F₃ := S₂.fixed.unch h7 hn ((fixedOk_slW (l := [R2P, BP, QY]) (by decide)).append fixedOk_flag) U₃
  have e₃ : ∀ {i}, i < 45 → i ∉ [R2P, BP, QY] → i ≠ FLAG →
      sv c (s₀.gpr .x3) s₃ i = sv c (s₀.gpr .x3) s₂ i := fun hi hl hf =>
    sv_unch U₃ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have x₃ : sv c (s₀.gpr .x3) s₃ E = sv c (s₀.gpr .x3) s₂ E := e₃ (by decide) (by decide) (by decide)
  -- The peer's key has not changed.
  have W₂ : Outside (s₀.gpr .x3) 0 size s₀.mem s₂.mem := fun x hx =>
    (S₂.unch x fun w hw => by rw [List.mem_singleton.mp hw]; exact hx).trans (congrFun k₁.mem x)
  have hq0 : s₂.mem (s₀.gpr .x2) = s₀.mem (s₀.gpr .x2) := by
    have := keep_of_disjoint' W₂ hp.peer_sc (by omega) (i := 0) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  -- What the code checks of the peer's key so far.
  have hf₃ : word s₃.mem (s₀.gpr .x3) (c.sl FLAG) = mask (((s₀.mem (s₀.gpr .x2) = 4 ∧
      sv c (s₀.gpr .x3) s₃ E < c.C.p) ∧ sv c (s₀.gpr .x3) s₃ QY < c.C.p)) := by
    rw [f₃, S₂.flag, BitVec.allOnes_and, mask_and, mask_and, x₃, hq0]
  refine WP.seq (WP.mono (validate_ok hc hs₃ F₃ r2₃ bp₃ hf₃)
    fun s₄ ⟨hs₄, g₄, rd₄, wr₄, U₄, f₄, px_lt, py_lt, px, py⟩ => ?_)
  have F₄ := F₃.unch h7 hn ((fixedOk_slW (l := [QXM, QYM, TMP, W0, W1, W2, W3, PY]) (by decide)).append
    fixedOk_flag) U₄
  have e₄ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY] → i ≠ FLAG →
      sv c (s₀.gpr .x3) s₄ i = sv c (s₀.gpr .x3) s₃ i := fun hi hl hf =>
    sv_unch U₄ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  -- `[d]P`, then `Z^(p-2)`.
  have hk₄ : sv c (s₀.gpr .x3) s₄ K = dk c s₀ := by
    rw [e₄ (by decide) (by decide) (by decide), e₃ (by decide) (by decide) (by decide), S₂.k]
    simp only [kv, dk, k₁.mem, x3₁]
  refine winPow_ok hc hC hs₄ F₄ (peerPt_onCurve hc _ _ _) px_lt py_lt
    (peerPt_rep hC _ _ _ px py |> fun h => by
      show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x3) s₄ PX))
        (toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x3) s₄ PY))
        (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₄.mem (s₀.gpr .x3) (c.sl ONEP) c.n)) _
      rw [F₄.onep, toM_one hpR]; exact h)
    fun s₅ L => ?_
  have hs₅ := L.scr
  have F₅ := F₄.unch h7 hn (fixedOk_winX.append ((fixedOk_slW (by decide)).append fixedOk_chainWc))
    L.unch
  have e₅ : ∀ {i}, i < 45 → i ∉ otherI ++ tblI ++ [TMP] → i ∉ [ACC, TMP] →
      sv c (s₀.gpr .x3) s₅ i = sv c (s₀.gpr .x3) s₄ i :=
    fun hi h₁ h₂ => sv_unch L.unch h7 hn hi
      (apart_append (apart_winX hi) (apart_append (apart_slW h₁) (apart_chainWc hi h₂)))
  have hflag₅ := f₄
  rw [← flag_unch_win L.unch h7 h0 hn (by decide)] at hflag₅
  have hx20₅ : s₅.gpr .x20 = s₀.gpr .x0 := by
    rw [L.gpr _ (x20_not_combClob h7) (x20_not_powClob h7), g₄ _ (x20_not_clob h7), k₃.gpr _ (by decide),
      S₂.x20, x0₁]
  have hw₅ : (⟨s₀.gpr .x0, c.C.len⟩ : Region) ∈ s₅.wr := by
    rw [L.wr, wr₄, k₃.wr, S₂.wr, k₁.wr, hp.wr]; simp
  refine WP.mono (middle_ok hc hs₅ F₅ L.acc_lt hflag₅ hx20₅ hp.out_fit hw₅ hp.out_sc)
    fun s' ⟨xv, hxl, hxv, bytes, ret, saved⟩ => ⟨fun r hr => ?_, ?_⟩
  · have hsv : ∀ r ∈ Cfg.saved.map Prod.fst, r ∉ [Reg.x2, .x3, .x4, .x6] := by decide
    rw [saved r hr, k₁.gpr r (hsv r hr)]
  -- The specification.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (1 + 2 * c.C.len)).head? = some (s₀.mem (s₀.gpr .x2)) := by
    rw [peer_bytes]; rfl
  have hxs : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      sv c (s₀.gpr .x3) s₃ E := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _), x₃, S₂.e,
      shAt_none, Nat.shiftRight_zero]
    simp only [ev, k₁.mem, x2₁]
  have hys : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      sv c (s₀.gpr .x3) s₃ QY := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _), y₃,
      bytesAt_keep W₂ (hp.peer_sc.sub_left (Offset.sub_base _ (by omega))) (by omega) (by omega)]
  have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (s₀.gpr .x2)) (sv c (s₀.gpr .x3) s₃ E) (sv c (s₀.gpr .x3) s₃ QY),
      peerPt c (s₀.mem (s₀.gpr .x2) = 4) (sv c (s₀.gpr .x3) s₃ E) (sv c (s₀.gpr .x3) s₃ QY) =
        .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have hR := L.q
  rw [hk₄] at hR
  have hxoX : Fin.ofNat c.C.p xv = tmv c.C c.n (s₀.gpr .x3) s₅ (c.sl RX) *
      tmv c.C c.n (s₀.gpr .x3) s₅ (c.sl RZ) ^ (c.C.p - 2) := by rw [hxv, L.acc]
  have hspec := exchange_eq hC hlen hb0 hxs hys hP' hR hxl hxoX
  have hD₅ : sv c (s₀.gpr .x3) s₅ D = dk c s₀ := by
    rw [e₅ (by decide) (by decide) (by decide), e₄ (by decide) (by decide) (by decide),
      e₃ (by decide) (by decide) (by decide), S₂.d, shAt_none, Nat.shiftRight_zero]
    simp only [dv, dk, k₁.mem, x1₁]
  have hz : tmv c.C c.n (s₀.gpr .x3) s₅ (c.sl RZ) ≠ 0 ↔ sv c (s₀.gpr .x3) s₅ RZ ≠ 0 :=
    not_congr (toM_eq_zero_iff hpR L.rz_lt)
  unfold EPost
  rw [hspec]
  by_cases hcond : (1 ≤ dk c s₀ ∧ dk c s₀ < c.C.n) ∧
      Ecdh.Valid c.C (s₀.mem (s₀.gpr .x2)) (sv c (s₀.gpr .x3) s₃ E) (sv c (s₀.gpr .x3) s₃ QY) ∧
      tmv c.C c.n (s₀.gpr .x3) s₅ (c.sl RZ) ≠ 0
  · have hok : ok c (s₀.gpr .x3) s₅ (PeerOk c (s₀.gpr .x3) s₃ ((s₀.mem (s₀.gpr .x2) = 4 ∧
        sv c (s₀.gpr .x3) s₃ E < c.C.p) ∧ sv c (s₀.gpr .x3) s₃ QY < c.C.p)) = true := by
      refine decide_eq_true ⟨⟨⟨⟨⟨hcond.2.1.1, hcond.2.1.2.1⟩, hcond.2.1.2.2.1⟩, hcond.2.1.2.2.2⟩, ?_, ?_⟩,
        hz.mp hcond.2.2⟩
      · rw [hD₅]; exact hcond.1.1
      · rw [hD₅]; exact hcond.1.2
    rw [ite_eq_left hcond]
    exact ⟨by rw [ret, hok]; rfl, by rw [bytes, hok]; rfl⟩
  · have hok : ok c (s₀.gpr .x3) s₅ (PeerOk c (s₀.gpr .x3) s₃ ((s₀.mem (s₀.gpr .x2) = 4 ∧
        sv c (s₀.gpr .x3) s₃ E < c.C.p) ∧ sv c (s₀.gpr .x3) s₃ QY < c.C.p)) = false := by
      refine decide_eq_false fun h => hcond ⟨⟨?_, ?_⟩, ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2⟩,
        hz.mpr h.2⟩
      · rw [← hD₅]; exact h.1.2.1
      · rw [← hD₅]; exact h.1.2.2
    rw [ite_eq_right hcond]
    exact ⟨by rw [ret, hok]; rfl, by rw [bytes, hok]; rfl⟩

end VG.Proof.Ecdh.AArch64
