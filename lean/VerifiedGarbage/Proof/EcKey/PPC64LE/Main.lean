module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
public import VerifiedGarbage.Impl.EcKey.PPC64LE
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.EcKey
import VerifiedGarbage.Proof.EcKey.PPC64LE.Finish
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.SlotOps
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Flags
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout

/-!
# Elliptic curve public keys on PPC64LE: the whole function

As on 32-bit ARM (`Proof/EcKey/Arm/Main.lean`). `middle_ok`: `middle`
computes `x = X Z^(p-2)` and `y = Y Z^(p-2)` from the power in `ACC`, each
left Montgomery's form (`pkOps_ok`), ands the masks of `d ∈ [1, n-1]` and
`Z ≠ 0` into the flag, and writes the result (`pkFinish_ok`).

`publicKey_ok`: `Cfg.publicKey` computes the specification's public key of
`d`, for any curve the proof of the code supports (`CfgOk`, coordinates of 3
to 6 words) whose group law the proofs support (`Law`), restores the
callee-saved registers and `lr`, and changes memory only in the working
space and `out`. The code up to `Z^(p-2)` is the signature's, with its setup
reading `k`, `d` and the hash all from `d` (`Args.publicKey`).
-/

@[expose] public section

namespace VG.Proof.EcKey.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Weierstrass.PPC64LE.Point VG.Proof.Ecdsa.PPC64LE
  VG.Spec.Weierstrass
open VG.Impl.EcKey.PPC64LE (YM Y Args.publicKey)

variable {c : Cfg}

theorem middle_eq (c : Cfg) : Impl.EcKey.PPC64LE.Cfg.middle c =
    .seq (mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC))
    (.seq (mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE))
    (.seq (mulCall c.SP (c.sl YM) (c.sl RY) (c.sl ACC))
    (.seq (mulCall c.SP (c.sl Y) (c.sl YM) (c.sl ONE))
    (.block (c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ Impl.EcKey.PPC64LE.Cfg.finish c))))) := rfl

/-- What `middle`'s field operations leave. -/
structure OpsPost (c : Cfg) (s₀ : State) (base : Addr) (s s' : State) : Prop extends Keep c s₀ base s' where
  same : ∀ {i}, i < 45 → i ∉ [XM, X, YM, Y] → sv c base s' i = sv c base s i
  flag : flagW c base s' = flagW c base s
  x_lt : sv c base s' X < c.C.p
  x : Fin.ofNat c.C.p (sv c base s' X) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
  y_lt : sv c base s' Y < c.C.p
  y : Fin.ofNat c.C.p (sv c base s' Y) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s RY) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)

/-- The four field operations of `middle`. -/
theorem pkOps_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (K : Keep c s₀ base s)
    (hacc : sv c base s ACC < c.C.p) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', OpsPost c s₀ base s s' → WP isa rest s' Q) :
    WP isa (.seq (mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC))
      (.seq (mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE))
      (.seq (mulCall c.SP (c.sl YM) (c.sl RY) (c.sl ACC))
      (.seq (mulCall c.SP (c.sl Y) (c.sl YM) (c.sl ONE)) rest)))) s Q := by
  have h7 := hc.n10
  have hn := K.ws.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hone : sv c base s ONE = 1 := K.fixed.one
  -- `XM = X · ACC`.
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 K.ws (o := XM) (a := RX) (b := ACC) (by decide) (by decide)
    (by decide) hacc) fun s₁ ⟨k₁, U₁, _, e₁⟩ => ?_)
  have K₁ := K.step h7 k₁ (hU := U₁) (hW := fixedOk_callW h7 (by decide)) (hWs := callW_le h7 (by decide))
  have v₁ : ∀ {i}, i < 45 → i ≠ XM → sv c base s₁ i = sv c base s i := fun hi h₁ =>
    sv_unch U₁ h7 hn hi (apart_callW h7 hi h₁)
  -- `X = XM · 1`.
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 K₁.ws (o := X) (a := XM) (b := ONE) (by decide) (by decide)
    (by decide) (by rw [v₁ (by decide) (by decide), hone]; omega)) fun s₂ ⟨k₂, U₂, lt₂, e₂⟩ => ?_)
  have K₂ := K₁.step h7 k₂ (hU := U₂) (hW := fixedOk_callW h7 (by decide)) (hWs := callW_le h7 (by decide))
  have v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ X → sv c base s₂ i = sv c base s i := fun hi h₁ h₂ =>
    (sv_unch U₂ h7 hn hi (apart_callW h7 hi h₂)).trans (v₁ hi h₁)
  have x₂ : Fin.ofNat c.C.p (sv c base s₂ X) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) := by
    rw [toM_one_mul hpR (by rw [e₂, v₁ (i := ONE) (by decide) (by decide), hone]), toM_mul hpR e₁]
  -- `YM = Y · ACC`.
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 K₂.ws (o := YM) (a := RY) (b := ACC) (by decide) (by decide)
    (by decide) (by rw [v₂ (by decide) (by decide) (by decide)]; exact hacc)) fun s₃ ⟨k₃, U₃, _, e₃⟩ => ?_)
  have K₃ := K₂.step h7 k₃ (hU := U₃) (hW := fixedOk_callW h7 (by decide)) (hWs := callW_le h7 (by decide))
  have v₃ : ∀ {i}, i < 45 → i ≠ XM → i ≠ X → i ≠ YM → sv c base s₃ i = sv c base s i := fun hi h₁ h₂ h₃ =>
    (sv_unch U₃ h7 hn hi (apart_callW h7 hi h₃)).trans (v₂ hi h₁ h₂)
  -- `Y = YM · 1`.
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 K₃.ws (o := Y) (a := YM) (b := ONE) (by decide) (by decide)
    (by decide) (by rw [v₃ (by decide) (by decide) (by decide) (by decide), hone]; omega))
    fun s₄ ⟨k₄, U₄, lt₄, e₄⟩ => h s₄ ?_)
  have K₄ := K₃.step h7 k₄ (hU := U₄) (hW := fixedOk_callW h7 (by decide)) (hWs := callW_le h7 (by decide))
  have v₄ : ∀ {i}, i < 45 → i ∉ [XM, X, YM, Y] → sv c base s₄ i = sv c base s i := fun hi hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    exact (sv_unch U₄ h7 hn hi (apart_callW h7 hi hl.2.2.2)).trans (v₃ hi hl.1 hl.2.1 hl.2.2.1)
  have X₄ : sv c base s₄ X = sv c base s₂ X :=
    (sv_unch U₄ h7 hn (i := X) (by decide) (apart_callW h7 (by decide) (by decide))).trans
      (sv_unch U₃ h7 hn (i := X) (by decide) (apart_callW h7 (by decide) (by decide)))
  have e₃' : sv c base s₃ YM * 2 ^ (64 * c.n) % c.C.p = sv c base s RY * sv c base s ACC % c.C.p := by
    rw [e₃, v₂ (i := RY) (by decide) (by decide) (by decide), v₂ (i := ACC) (by decide) (by decide) (by decide)]
  have fl : flagW c base s₄ = flagW c base s := by
    simp only [flagW]
    rw [flag_callW hc.n0 h7 (o := Y) (by decide) U₄, flag_callW hc.n0 h7 (o := YM) (by decide) U₃,
      flag_callW hc.n0 h7 (o := X) (by decide) U₂, flag_callW hc.n0 h7 (o := XM) (by decide) U₁]
  refine ⟨K₄, v₄, fl, by rw [X₄]; exact lt₂, by rw [X₄]; exact x₂, lt₄, ?_⟩
  rw [toM_one_mul hpR (by rw [e₄, v₃ (i := ONE) (by decide) (by decide) (by decide) (by decide), hone]),
    toM_mul hpR e₃']

/-- Whether the public key is a point the result encodes: `d` in `[1, n-1]`
and `Z ≠ 0`. -/
abbrev ok (c : Cfg) (base : Addr) (s : State) : Bool :=
  decide ((0 < sv c base s D ∧ sv c base s D < c.C.n) ∧ sv c base s RZ ≠ 0)

/-- `x`, `y`, the checks and the result, from a state that kept what the
stages keep since `s₀`. -/
theorem middle_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (K : Keep c s₀ base s)
    (hacc : sv c base s ACC < c.C.p) (hflag : flagW c base s = BitVec.allOnes 64)
    (hofit : (s₀.gpr .r3).toNat + (1 + 2 * c.C.len) ≤ 2 ^ 64)
    (hw : (⟨s₀.gpr .r3, 1 + 2 * c.C.len⟩ : Region) ∈ s₀.wr)
    (hd : Region.Disjoint ⟨s₀.gpr .r3, 1 + 2 * c.C.len⟩ ⟨base, size⟩) :
    WP isa (Impl.EcKey.PPC64LE.Cfg.middle c) s fun s' => ∃ xv yv, xv < c.C.p ∧
      Fin.ofNat c.C.p xv =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      yv < c.C.p ∧ Fin.ofNat c.C.p yv =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RY) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .r3) (1 + 2 * c.C.len) =
        (if ok c base s then 4 :: (toBytes c.C.len xv ++ toBytes c.C.len yv)
          else List.replicate (1 + 2 * c.C.len) 0) ∧
      s'.gpr .r3 = (if ok c base s then 1 else 0) ∧
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧ s'.lr = s₀.lr ∧
      ∃ m, Unch base [(0, size)] s₀.mem m ∧ Outside (s₀.gpr .r3) 0 (1 + 2 * c.C.len) m s'.mem := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := K.ws.nowrap
  have hsz : size = 8192 := rfl
  have hfl : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  rw [middle_eq]
  refine pkOps_ok hc K hacc fun s₄ Op => ?_
  rw [List.append_assoc]
  refine wp_append (WP.mono (checkRange_ok c Op.ws.ws Op.ws.at3 (sl_al c D) h0
    (by have := sl_le c h7 (i := D) (by decide); omega) (by have := sl_le c h7 (i := MN) (by decide); omega) hfl)
    fun s₅ ⟨f₅, k₅, O₅⟩ => ?_)
  have K₅ := Op.toKeep.step h7 (k₅.rk (rs' := [.r0, .r4, .r5, .r6, .r7, .r8, .r9])) (hU := O₅.unch) (hW := fixedOk_flag) (hWs := by
    intro w hw; rw [List.mem_singleton.mp hw]; exact hfl)
  refine wp_append (WP.mono (checkNonzero_ok c K₅.ws.ws K₅.ws.at3 (sl_al c RZ) h0
    (by have := sl_le c h7 (i := RZ) (by decide); omega) hfl) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_)
  have K₆ := K₅.step h7 (k₆.rk (rs' := [.r4, .r5])) (hU := O₆.unch) (hW := fixedOk_flag) (hWs := by
    intro w hw; rw [List.mem_singleton.mp hw]; exact hfl)
  have e₆ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₆ i = sv c base s₄ i := fun hi hif =>
    (sv_unch O₆.unch h7 hn hi (apart_flag h0 hif)).trans (sv_unch O₅.unch h7 hn hi (apart_flag h0 hif))
  have hMN : wordsVal s₄.mem base (c.sl MN) c.n = c.C.n := Op.fixed.mn
  have z₅ : wordsVal s₅.mem base (c.sl RZ) c.n = sv c base s RZ :=
    (sv_unch O₅.unch h7 hn (i := RZ) (by decide) (apart_flag h0 (by decide))).trans (Op.same (by decide) (by decide))
  have d₄ : wordsVal s₄.mem base (c.sl D) c.n = sv c base s D := Op.same (by decide) (by decide)
  have hflag₆ : flagW c base s₆ = mask64 (ok c base s = true) := by
    rw [f₆, f₅, Op.flag, hflag, hMN, z₅, d₄, BitVec.allOnes_and, mask64_and]
    simp only [ok, decide_eq_true_eq]
  refine WP.mono (pkFinish_ok hc K₆.ws (by rw [K₆.r14]) hofit (by rw [K₆.rk.wr]; exact hw) hd _ hflag₆)
    fun s' ⟨bytes, r3, lr, r14, r31, rk, out⟩ => ?_
  have x₆ : sv c base s₆ X = sv c base s₄ X := e₆ (by decide) (by decide)
  have y₆ : sv c base s₆ Y = sv c base s₄ Y := e₆ (by decide) (by decide)
  have hsv := K₆.fixed.saved
  refine ⟨_, _, Op.x_lt, Op.x, Op.y_lt, Op.y, by rw [bytes, x₆, y₆], r3, ?_, by rw [rk.sp, K₆.rk.sp],
    by rw [lr, K₆.fixed.savedLr], s₆.mem, K₆.whole, out⟩
  intro r hr
  have hcases : ∀ r ∈ preserved, r = .r14 ∨ r = .r31 ∨
      (r ∉ [Reg.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] ∧ r ∉ work) := by decide
  rcases hcases r hr with rfl | rfl | ⟨h₁, h₂⟩
  · rw [r14]; exact hsv (.r14, 0) (by decide)
  · rw [r31]; exact hsv (.r31, 8) (by decide)
  · rw [rk.gpr r h₁, K₆.rk.gpr r h₂]

/-- What the function needs: `d` readable, `out` and the working space
writable, the working space apart from both. -/
structure PkPre (c : Cfg) (s : State) (extra : List Region := []) : Prop where
  rd : s.rd = [⟨s.gpr .r4, c.C.len⟩] ++ extra
  wr : s.wr = [⟨s.gpr .r3, 1 + 2 * c.C.len⟩, ⟨s.gpr .r5, size⟩]
  out_sc : Region.Disjoint ⟨s.gpr .r3, 1 + 2 * c.C.len⟩ ⟨s.gpr .r5, size⟩
  d_sc : Region.Disjoint ⟨s.gpr .r4, c.C.len⟩ ⟨s.gpr .r5, size⟩
  out_fit : (s.gpr .r3).toNat + (1 + 2 * c.C.len) ≤ 2 ^ 64
  d_fit : (s.gpr .r4).toNat + c.C.len ≤ 2 ^ 64
  sc_fit : (s.gpr .r5).toNat + size ≤ 2 ^ 64

theorem PkPre.setup {s : State} {extra : List Region} (hp : PkPre c s extra) : SetupPre c Args.publicKey s where
  shift := .inl rfl
  k_reg := by decide
  d_reg := by decide
  e_reg := by decide
  sc_reg := by decide
  wr := by show (⟨s.gpr .r5, size⟩ : Region) ∈ s.wr; rw [hp.wr]; simp
  sc_fit := hp.sc_fit
  k_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.d_fit; omega)
  d_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.d_fit; omega)
  e_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.d_fit; omega)
  k_sc := hp.d_sc
  d_sc := hp.d_sc
  e_sc := hp.d_sc
  k_fit := hp.d_fit
  d_fit := hp.d_fit
  e_fit := hp.d_fit

/-- The private key. -/
abbrev dk (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r4) c.C.len)

/-- The result the contract asks for: the specification's public key of `d`,
`04 ‖ x ‖ y`, and `1`, or zeros and `0`. -/
def PkPost (c : Cfg) (s₀ s' : State) : Prop :=
  match Spec.EcKey.publicKey c.C (dk c s₀) with
  | some (.affine x y) => s'.gpr .r3 = 1 ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .r3) (1 + 2 * c.C.len) = Spec.EcKey.encodePoint (.affine x y)
  | _ => s'.gpr .r3 = 0 ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .r3) (1 + 2 * c.C.len) = List.replicate (1 + 2 * c.C.len) 0

/-- What the function keeps: the callee-saved registers, `sp` and `lr`, and
memory but the working space and `out`. -/
structure PkKeep (c : Cfg) (s₀ s' : State) : Prop where
  saved : ∀ r ∈ preserved, s'.gpr r = s₀.gpr r
  sp : s'.sp = s₀.sp
  lr : s'.lr = s₀.lr
  frame : ∃ m : Mem, Unch (s₀.gpr .r5) [(0, size)] s₀.mem m ∧ Outside (s₀.gpr .r3) 0 (1 + 2 * c.C.len) m s'.mem

theorem publicKey_eq' (c : Cfg) : Impl.EcKey.PPC64LE.Cfg.publicKey c =
    .seq (.seq (.block (c.setupWith Args.publicKey)) (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n))
      (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n))
      (.seq (Point.ladderP (ladderAt c GX GY) c.SP) (.seq (pow c.powP c.SP) (.block [])))))))
      (Impl.EcKey.PPC64LE.Cfg.middle c) := rfl

/-- `vg_ec_<curve>_public_key` computes the specification's public key and
restores the callee-saved registers and `lr`. -/
theorem publicKey_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {s₀ : State}
    {extra : List Region} (hp : PkPre c s₀ extra) :
    WP isa (Impl.EcKey.PPC64LE.Cfg.publicKey c) s₀ fun s' => PkKeep c s₀ s' ∧ PkPost c s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  rw [publicKey_eq']
  refine WP.seq (stage₁ hc hp.setup fun s₁ S₁ => ?_)
  have F := S₁.fixed
  have hG : Rep c.C (tmv c.C c.n (s₀.gpr .r5) s₁ (c.sl GX)) (tmv c.C c.n (s₀.gpr .r5) s₁ (c.sl GY))
      (tmv c.C c.n (s₀.gpr .r5) s₁ (c.sl ONEP)) (G c.C) := by
    show Rep c.C (toM _ _ (wordsVal s₁.mem _ (c.sl GX) c.n)) (toM _ _ (wordsVal s₁.mem _ (c.sl GY) c.n))
      (toM _ _ (wordsVal s₁.mem _ (c.sl ONEP) c.n)) (G c.C)
    rw [F.gx, F.gy, F.onep, toM_cmont hc, toM_cmont hc, toM_one hpR]
    exact rep_affine' hC _ _
  refine stage₂ hc h3 hC (gx := GX) (gy := GY) (by decide) (by decide) (by decide) (by decide) S₁ hc.onG hG
    (lt_of_eq_of_lt F.gx (hmont _)) (lt_of_eq_of_lt F.gy (hmont _)) fun s₂ S₂ => WP.block_nil ?_
  have hd' : Region.Disjoint ⟨s₀.gpr .r3, 1 + 2 * c.C.len⟩ ⟨s₀.gpr .r5, size⟩ := hp.out_sc
  refine WP.mono (middle_ok hc S₂.toKeep S₂.acc_lt S₂.flag hp.out_fit (by rw [hp.wr]; simp) hd')
    fun s' ⟨xv, yv, hxl, hx, hyl, hy, bytes, r3, saved, sp, lr, frame⟩ => ⟨⟨saved, sp, lr, frame⟩, ?_⟩
  -- The specification.
  have hk : kv c Args.publicKey s₀ = dk c s₀ := Nat.shiftRight_zero
  have hD : sv c (s₀.gpr .r5) s₂ D = dk c s₀ := (S₂.d).trans Nat.shiftRight_zero
  have hR := S₂.rep
  rw [hk] at hR
  have hxX : Fin.ofNat c.C.p xv = tmv c.C c.n (s₀.gpr .r5) s₂ (c.sl RX) *
      tmv c.C c.n (s₀.gpr .r5) s₂ (c.sl RZ) ^ (c.C.p - 2) := by rw [hx, S₂.acc]
  have hyY : Fin.ofNat c.C.p yv = tmv c.C c.n (s₀.gpr .r5) s₂ (c.sl RY) *
      tmv c.C c.n (s₀.gpr .r5) s₂ (c.sl RZ) ^ (c.C.p - 2) := by rw [hy, S₂.acc]
  have hz := toM_eq_zero_iff hpR (x := sv c (s₀.gpr .r5) s₂ RZ) S₂.rz_lt
  unfold PkPost
  rw [publicKey_eq hC hR hxl hxX hyl hyY]
  by_cases hd : 1 ≤ dk c s₀ ∧ dk c s₀ < c.C.n
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]
    by_cases h0 : sv c (s₀.gpr .r5) s₂ RZ = 0
    · have hok : ok c (s₀.gpr .r5) s₂ = false := decide_eq_false (by rw [hD]; omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true (hz.mpr h0))]
      exact ⟨by rw [r3, hok]; rfl, by rw [bytes, hok]; rfl⟩
    · have hok : ok c (s₀.gpr .r5) s₂ = true := decide_eq_true (by rw [hD]; omega)
      rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => h0 (hz.mp h)))]
      refine ⟨by rw [r3, hok]; rfl, ?_⟩
      rw [bytes, hok]
      rfl
  · have hok : ok c (s₀.gpr .r5) s₂ = false := decide_eq_false (by rw [hD]; omega)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
    exact ⟨by rw [r3, hok]; rfl, by rw [bytes, hok]; rfl⟩

end VG.Proof.EcKey.PPC64LE
