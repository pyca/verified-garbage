module

public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Front
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Scalars
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Points
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Middle
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Finish
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Flags
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Peer
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Main
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Main
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.Weierstrass.MulContract

/-! ### `Ecdsa.Verify.PPC64LE.Final`, which only this module used -/

section

/-!
# ECDSA verification on PPC64LE: `x` and the result

As on 32-bit ARM (`Proof/Ecdsa/Verify/Arm/Final.lean`). `vtail_ok`: from
what `points_ok` leaves, the signature's power gives `Z^(p-2)`, and `final`
computes `x = X Z^(p-2)` out of Montgomery's form, `x R mod n` and
`x R - r R mod n`, ands the masks of `Z ≠ 0` and of that difference being
zero (`x ≡ r` modulo `n`) into the flag, returns its low bit and restores
`lr`, `r14` and `r31` (`vfinish_ok`). It writes only the working space.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdh.PPC64LE VG.Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.Point (tmv)
open VG.Impl.Ecdsa.Verify.PPC64LE (RM' XN W)

variable {c : Cfg}

theorem vfinish_eq (c : Cfg) : Impl.Ecdsa.Verify.PPC64LE.Cfg.finish c =
    .load .d .r10 wb (c.sl FLAG) :: .li .r4 1 :: .logic .and .r4 .r10 .r4 :: (Cfg.restore ++ [mov .r3 .r4]) := rfl

/-- The return value, and `lr`, `r14` and `r31` from the working space. -/
theorem vfinish_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base) (b : Bool)
    (hf : flagW c base s = mask64 (b = true)) :
    WP isa (.block (Impl.Ecdsa.Verify.PPC64LE.Cfg.finish c)) s fun s' =>
      s'.gpr .r3 = (if b then 1 else 0) ∧
      s'.lr = word s.mem base Cfg.lrAt ∧ s'.gpr .r14 = word s.mem base 0 ∧ s'.gpr .r31 = word s.mem base 8 ∧
      Rk [.r0, .r3, .r4, .r10, .r14, .r31] s s' ∧ s'.mem = s.mem := by
  have h7 := hc.n10
  have hsz : size = 8192 := rfl
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have hs := hw.ws
  have h3 := hw.at3
  rw [vfinish_eq]
  refine wp_step (ld0_ok hs h3 (by decide) (sl_al c FLAG) (by omega_arith)) ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_logic ?_
  have hs₁ := hs.write .r10 (word s.mem base (c.sl FLAG))
  have h3₁ := h3.write (d := .r10) (word s.mem base (c.sl FLAG))
  refine restore_ok ((hs₁.write _ _).write _ _) ((h3₁.write _).write _) (by omega_arith) fun t Kt mt lrt r14t r31t => ?_
  refine wp_step exec_mov (WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩)
  · simp only [write_gpr, ite_true]
    rw [Kt.gpr _ (by decide)]
    simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
    rw [show word s.mem base (c.sl FLAG) = mask64 (b = true) from hf]
    exact mask_bit b
  · simp only [write_lr]; rw [lrt]; rfl
  · simp only [write_gpr, reduceCtorEq, ite_false]; rw [r14t]; rfl
  · simp only [write_gpr, reduceCtorEq, ite_false]; rw [r31t]; rfl
  · exact ((((Kp.write s (d := .r10) _ (rs := [.r0, .r3, .r4, .r10, .r14, .r31]) (by decide)).trans
      (Kp.write _ (d := .r4) (BitVec.ofNat 64 1) (by decide))).trans
      (Kp.write _ (d := .r4) _ (by decide))).rk.trans (Kt.mono (by decide))).trans
      (Kp.write t (d := .r3) _ (rs := [.r0, .r3, .r4, .r10, .r14, .r31]) (by decide)).rk
  · simp only [write_mem]; rw [mt]; rfl

theorem final_eq (c : Cfg) : Impl.Ecdsa.Verify.PPC64LE.Cfg.final c =
    .seq (mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC))
    (.seq (mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE))
    (.seq (mulCall c.SN (c.sl XN) (c.sl X) (c.sl R2N))
    (.seq (subCall c.SN (c.sl W) (c.sl XN) (c.sl RM'))
      (.block (c.checkNonzero (c.sl RZ) ++ (Impl.Ecdh.PPC64LE.Cfg.checkZero c (c.sl W) ++
        Impl.Ecdsa.Verify.PPC64LE.Cfg.finish c)))))) := by
  simp only [Impl.Ecdsa.Verify.PPC64LE.Cfg.final, progs, List.append_assoc]

/-- `Z^(p-2)`, `x`, the last checks and the result. -/
theorem vtail_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {u v : Nat} {P : Point c.C} {s : State}
    (hP : Pts c s₀ base u v P s) :
    WP isa (.seq c.invP (Impl.Ecdsa.Verify.PPC64LE.Cfg.final c)) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧ s'.lr = s₀.lr ∧
      Unch base [(0, size)] s₀.mem s'.mem ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        s'.gpr .r3 = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
          (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
          Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀) then 1 else 0 := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hP.ws.nowrap
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hn3 := hc.n_ge
  have hfl : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  -- `Z^(p-2)`.
  refine WP.seq (WP.mono (chainPow_ok (P := c.chainP) (S := c.SP) (e := c.C.p - 2) hc.fpk hc.fpm (modP hc)
    (chainLayP hc) hpR hP.ws hP.rz_lt hc.chainP) fun s₁ ⟨k₁, U₁, lt₁, v₁⟩ => ?_)
  rw [chainWP_eq] at U₁
  have K₁ : Keep c s₀ base s₁ := hP.toKeep.step h7 k₁ (hU := U₁) (hW := fixedOk_chainW h7) (hWs := chainW_le h7)
  have e₁ : ∀ {i}, i < 45 → i ≠ ACC → (i < DX ∨ T2 < i) → sv c base s₁ i = sv c base s i := fun hi hr ht =>
    sv_unch U₁ h7 hn hi (apart_chainW h7 hi hr ht)
  have fl₁ : flagW c base s₁ = flagW c base s := by
    have apF : ∀ w ∈ [(c.sl ACC, 8 * c.n), (c.sl DX, 9 * (8 * c.n)), (own c.n, 64 * c.n)],
        c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := fun w hw => by
      have := sl_le c h7 (i := FLAG) (by decide)
      rcases apart_chainW h7 (i := FLAG) (by decide) (by decide) (by decide) w hw with h | h
      · exact Or.inl (by omega_arith)
      · exact Or.inr h
    rw [flagW, U₁.word apF (by omega_arith), ← flagW]
  rw [final_eq]
  -- `XM = X · ACC`.
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 K₁.ws (o := XM) (a := RX) (b := ACC) (by decide)
    (by decide) (by decide) lt₁) fun s₂ ⟨k₂, U₂, _, e₂⟩ => ?_)
  obtain ⟨K₂, f₂, -, v₂⟩ := K₁.call h0 h7 (o := XM) (by decide) (by decide) (by decide) k₂ U₂
  -- `X = XM · 1`.
  have one₂ : sv c base s₂ ONE = 1 := (v₂ (by decide) (by decide)).trans K₁.fixed.one
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 K₂.ws (o := X) (a := XM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [one₂]; omega_arith)) fun s₃ ⟨k₃, U₃, lt₃, e₃⟩ => ?_)
  obtain ⟨K₃, f₃, -, v₃⟩ := K₂.call h0 h7 (o := X) (by decide) (by decide) (by decide) k₃ U₃
  have x₃ : Fin.ofNat c.C.p (sv c base s₃ X) =
      tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) := by
    have acc₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ ACC) = tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) := v₁
    rw [toM_one_mul hpR (by rw [e₃, one₂]), toM_mul hpR e₂, acc₁]
    show toM _ _ (sv c base s₁ RX) * _ = toM _ _ (sv c base s RX) * _
    rw [e₁ (by decide) (by decide) (by decide)]
  -- `XN = x R mod n`, `W = XN - r R mod n`.
  have r2₃ : sv c base s₃ R2N = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n := K₃.fixed.r2n
  refine WP.seq (WP.mono (slMul_ok hc.fn hc.fnk hc.fnm h7 K₃.ws (o := XN) (a := X) (b := R2N) (by decide)
    (by decide) (by decide) (by rw [r2₃]; exact Nat.mod_lt _ (by omega_arith))) fun s₄ ⟨k₄, U₄, lt₄, e₄⟩ => ?_)
  obtain ⟨K₄, f₄, -, v₄⟩ := K₃.call h0 h7 (o := XN) (by decide) (by decide) (by decide) k₄ U₄
  have rm₄ : sv c base s₄ RM' = sv c base s RM' := by
    rw [v₄ (by decide) (by decide), v₃ (by decide) (by decide), v₂ (by decide) (by decide),
      e₁ (by decide) (by decide) (by decide)]
  refine WP.seq (WP.mono (slSub_ok hc.fn hc.fnk hc.fnm h7 K₄.ws (o := W) (a := XN) (b := RM') (by decide)
    (by decide) (by decide) lt₄ (by rw [rm₄]; exact hP.rm_lt)) fun s₅ ⟨k₅, U₅, e₅⟩ => ?_)
  obtain ⟨K₅, f₅, -, v₅⟩ := K₄.call h0 h7 (o := W) (by decide) (by decide) (by decide) k₅ U₅
  have w₅ : sv c base s₅ W = 0 ↔ Fin.ofNat c.C.n (sv c base s₃ X) = Fin.ofNat c.C.n (sigR c s₀) := by
    have hlt : sv c base s₅ W < c.C.n := by rw [e₅]; exact Nat.mod_lt _ (by omega_arith)
    rw [← toM_eq_zero_iff hnR hlt, e₅, toM_sub (by rw [rm₄]; have := hP.rm_lt; omega_arith), rm₄, hP.rm,
      toM_r2 hnR (by rw [e₄, r2₃])]
    constructor <;> intro h <;> grind
  -- The checks and the result.
  rw [WP.block_append_iff]
  refine WP.mono (checkNonzero_ok c K₅.ws.ws K₅.ws.at3 (sl_al c RZ) h0
    (by have := sl_le c h7 (i := RZ) (by decide); omega_arith) hfl) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  have K₆ := K₅.step h7 (k₆.rk (rs' := [.r4, .r5])) (hU := O₆.unch) (hW := fixedOk_flag) (hWs := by
    intro w hw; rw [List.mem_singleton.mp hw]; exact hfl)
  rw [WP.block_append_iff]
  refine WP.mono (checkZero_ok c K₆.ws.ws K₆.ws.at3 (sl_al c W) h0
    (by have := sl_le c h7 (i := W) (by decide); omega_arith) hfl) fun s₇ ⟨f₇, k₇, O₇⟩ => ?_
  have K₇ := K₆.step h7 (k₇.rk (rs' := [.r4, .r5])) (hU := O₇.unch) (hW := fixedOk_flag) (hWs := by
    intro w hw; rw [List.mem_singleton.mp hw]; exact hfl)
  have z₅ : wordsVal s₅.mem base (c.sl RZ) c.n = sv c base s RZ := by
    show sv c base s₅ RZ = _
    rw [v₅ (by decide) (by decide), v₄ (by decide) (by decide), v₃ (by decide) (by decide),
      v₂ (by decide) (by decide), e₁ (by decide) (by decide) (by decide)]
  have hW₆ : wordsVal s₆.mem base (c.sl W) c.n = sv c base s₅ W :=
    sv_unch O₆.unch h7 hn (i := W) (by decide) (apart_flag h0 (by decide))
  have hflag : flagW c base s₇ = mask64 (decide ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
      (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
      Fin.ofNat c.C.n (sv c base s₃ X) = Fin.ofNat c.C.n (sigR c s₀)) = true) := by
    rw [f₇, f₆, hW₆, f₅, f₄, f₃, f₂, fl₁, hP.flag, z₅, mask64_and, mask64_and]
    simp only [w₅, decide_eq_true_eq, and_assoc]
  refine WP.mono (vfinish_ok hc K₇.ws _ hflag) fun s' ⟨ret, lr, r14, r31, rk, hm⟩ =>
    ⟨?_, by rw [rk.sp, K₇.rk.sp], by rw [lr, K₇.fixed.savedLr], by rw [hm]; exact K₇.whole, _, lt₃, x₃, ?_⟩
  · intro r hr
    have hcases : ∀ r ∈ preserved, r = .r14 ∨ r = .r31 ∨
        (r ∉ [Reg.r0, .r3, .r4, .r10, .r14, .r31] ∧ r ∉ work) := by decide
    rcases hcases r hr with rfl | rfl | ⟨h₁, h₂⟩
    · rw [r14]; exact K₇.fixed.saved (.r14, 0) (by decide)
    · rw [r31]; exact K₇.fixed.saved (.r31, 8) (by decide)
    · rw [rk.gpr r h₁, K₇.rk.gpr r h₂]
  · rw [ret]
    simp only [decide_eq_true_eq]

end VG.Proof.Ecdsa.Verify.PPC64LE

end

end


/-!
# ECDSA verification on PPC64LE: the whole function

As on 32-bit ARM (`Proof/Ecdsa/Verify/Arm/Main.lean`). `verify_ok`:
`Cfg.verify` returns 1 exactly if the specification's verification of the
signature holds, for any curve the proof of the code supports (`CfgOk`)
whose group law the proofs support (`Law`), restores the callee-saved
registers and `lr`, keeps `sp` and writes only the working space.
`front_ok`, `mid_ok`, `points_ok` and `vtail_ok` compute what
`Proof.Ecdsa.verify_eq` connects to the specification.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdh.PPC64LE VG.Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.Point (tmv)
open VG.Impl.Ecdh.PPC64LE (PX PY)
open VG.Impl.Ecdsa.Verify.PPC64LE (U V)

variable {c : Cfg}

/-- The result the contract asks for: 1 exactly if the specification's
verification holds. -/
def VPost (c : Cfg) (s₀ s' : State) : Prop :=
  s'.gpr .r3 =
    if Spec.Ecdsa.verify c.C (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r3) (1 + 2 * c.C.len))
      (Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r4) c.C.len))
      (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) (2 * c.C.len)) then 1 else 0

/-- What the function keeps: the callee-saved registers, `sp` and `lr`, and
memory but the working space. -/
structure VKeep (s₀ s' : State) : Prop where
  saved : ∀ r ∈ preserved, s'.gpr r = s₀.gpr r
  sp : s'.sp = s₀.sp
  lr : s'.lr = s₀.lr
  frame : Unch (s₀.gpr .r6) [(0, size)] s₀.mem s'.mem

theorem verifyWith_eq (c : Cfg) (pts : Prog isa) : Impl.Ecdsa.Verify.PPC64LE.Cfg.verifyWith c pts =
    .seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.prefix' c) (.seq (.block (Impl.Ecdsa.Verify.PPC64LE.Cfg.loadS c))
      (.seq (.block (Impl.Ecdh.PPC64LE.Cfg.peerAt c .r14)) (.seq (Impl.Ecdh.PPC64LE.Cfg.validate c)
      (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.scalars c) (.seq c.invN
      (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.uv c) (.seq pts
      (.seq c.invP (Impl.Ecdsa.Verify.PPC64LE.Cfg.final c))))))))) := rfl

/-- What a computation of `[u]G + [v]Q` into `R` does, as `points_ok` states
it: from the stages before (`Mid`, naming the statics `s₀` names), with the
key's point `P` at `PX`, `PY`, `ONEP`, it leaves `Pts`. -/
def PtsOk (c : Cfg) (s₀ : State) (pts : Prog isa) : Prop :=
  ∀ {s : State}, Mid c s₀ (s₀.gpr .r6) s → s.syms = s₀.syms → ∀ {P : Point c.C}, onCurve c.C P = true →
    Rep c.C (tmv c.C c.n (s₀.gpr .r6) s (c.sl PX)) (tmv c.C c.n (s₀.gpr .r6) s (c.sl PY))
      (tmv c.C c.n (s₀.gpr .r6) s (c.sl ONEP)) P →
    ∀ {rest : Prog isa} {Q : State → Prop},
      (∀ s', Pts c s₀ (s₀.gpr .r6) (sv c (s₀.gpr .r6) s U) (sv c (s₀.gpr .r6) s V) P s' → WP isa rest s' Q) →
      WP isa (.seq pts rest) s Q

/-- `Cfg.verifyWith c pts` returns whether the specification's verification
holds, and restores the callee-saved registers, for `pts` computing
`[u]G + [v]Q` as `PtsOk` states. -/
theorem verifyWith_ok (hc : CfgOk c) (hC : Law c.C) {s₀ : State}
    {extra : List Region} (hp : VPre c s₀ extra) {pts : Prog isa} (hpts : PtsOk c s₀ pts) :
    WP isa (Impl.Ecdsa.Verify.PPC64LE.Cfg.verifyWith c pts) s₀ fun s' => VKeep s₀ s' ∧ VPost c s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have setupRun := front_ok hc hp (rest := .seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.scalars c)
    (.seq c.invN (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.uv c) (.block []))))
    (Q := fun s => Mid c s₀ (s₀.gpr .r6) s) (fun _ F => mid_ok hc F fun _ M => WP.block_nil M)
  have finish : ∀ s₂, Mid c s₀ (s₀.gpr .r6) s₂ → s₂.syms = s₀.syms →
      WP isa (.seq pts (.seq c.invP (Impl.Ecdsa.Verify.PPC64LE.Cfg.final c))) s₂
        (fun t => VKeep s₀ t ∧ VPost c s₀ t) := by
    intro s₂ hM syms₂
    -- The point the second ladder multiplies.
    let P := peerPt c (s₀.mem (s₀.gpr .r3) = 4) (keyX c s₀) (keyY c s₀)
    have hPc : onCurve c.C P = true := peerPt_onCurve hc _ _ _
    have h1 : tmv c.C c.n (s₀.gpr .r6) s₂ (c.sl ONEP) = 1 := by
      show toM _ _ (wordsVal s₂.mem _ (c.sl ONEP) c.n) = _
      rw [hM.fixed.onep]; exact toM_one hpR
    have hQ : Rep c.C (tmv c.C c.n (s₀.gpr .r6) s₂ (c.sl PX)) (tmv c.C c.n (s₀.gpr .r6) s₂ (c.sl PY))
        (tmv c.C c.n (s₀.gpr .r6) s₂ (c.sl ONEP)) P := by
      rw [h1]
      exact peerPt_rep hC _ _ _ hM.px hM.py
    refine hpts hM syms₂ hPc hQ fun s₃ hP => ?_
    refine WP.mono (vtail_ok hc hP) fun s' ⟨saved, sp, lr, frame, xo, hxo, hx, ret⟩ =>
      ⟨⟨saved, sp, lr, frame⟩, ?_⟩
    have hR := hP.pt
    -- The arguments as the specification reads them.
    have hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r3) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
      rw [length_bytesAt]; omega_using []
    have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r3) (1 + 2 * c.C.len)).head? = some (s₀.mem (s₀.gpr .r3)) := by
      rw [peer_bytes]; rfl
    have hxv : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r3) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
        keyX c s₀ := by
      rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
    have hyv : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r3) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
        keyY c s₀ := by
      rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
    have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (s₀.gpr .r3)) (keyX c s₀) (keyY c s₀),
        P = .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
      show peerPt c _ _ _ = _
      unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
    have h16 : 2 * c.C.len = c.C.len + c.C.len := by omega_using []
    have hr : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) (2 * c.C.len)).take c.C.len) = sigR c s₀ := by
      rw [h16, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]
    have hs : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) (2 * c.C.len)).drop c.C.len) = sigS c s₀ := by
      rw [h16, bytesAt_add, List.drop_left' (length_bytesAt _ _ _)]
    have hspec := Proof.Ecdsa.verify_eq hC hlen hb0 hxv hyv hP' hr hs hM.u_lt hM.v_lt hM.u hM.v hR hxo hx
    -- The conditions.
    have hz := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
    have hiff : (Ecdh.Valid c.C (s₀.mem (s₀.gpr .r3)) (keyX c s₀) (keyY c s₀) ∧
        (1 ≤ sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (1 ≤ sigS c s₀ ∧ sigS c s₀ < c.C.n) ∧
        tmv c.C c.n (s₀.gpr .r6) s₃ (c.sl RZ) ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) ↔
        ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
          sv c (s₀.gpr .r6) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
      constructor
      · rintro ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hZ, he⟩
        exact ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hz.mp hZ, he⟩
      · rintro ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hZ, he⟩
        exact ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hz.mpr hZ, he⟩
    unfold VPost
    rw [hashToInt_eq c, hspec, ret]
    by_cases h : (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
        sv c (s₀.gpr .r6) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)
    · rw [ite_eq_left (decide_eq_true (hiff.mpr h)), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hiff.mp (of_decide_eq_true h'))), ite_eq_right h]
  have run := VG.PPC64LE.WP.mono_syms setupRun finish
  simpa only [Impl.Ecdsa.Verify.PPC64LE.Cfg.verifyWith, Impl.Ecdsa.Verify.PPC64LE.Cfg.backWith,
    WP.seq_iff (M := isa), WP.block_nil_iff (M := isa)] using run

/-- `vg_ecdsa_<curve>_verify` returns whether the specification's
verification holds, and restores the callee-saved registers. -/
theorem verify_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {s₀ : State}
    {extra : List Region} (hp : VPre c s₀ extra) :
    WP isa (Impl.Ecdsa.Verify.PPC64LE.Cfg.verify c) s₀ fun s' => VKeep s₀ s' ∧ VPost c s₀ s' :=
  verifyWith_ok hc hC hp fun hM _ _ hP hQ _ _ h => points_ok hc h3 hC hM hP hQ h

end VG.Proof.Ecdsa.Verify.PPC64LE
