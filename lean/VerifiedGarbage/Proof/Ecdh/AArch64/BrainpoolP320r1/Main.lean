module

public import VerifiedGarbage.Proof.Ecdh.AArch64.Main
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP320r1.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP320r1.GMul
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst

/-! ### `Ecdh.AArch64.BrainpoolP320r1.Mul`, which only this module used -/

section

/-! # brainpoolP320r1 multiplication of a point, by a call of `vg_brainpoolp320r1_mul` -/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.BrainpoolP320r1

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.BrainpoolP320r1
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdh.AArch64.BrainpoolP320r1
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.BrainpoolP320r1

/-- A point that coordinates with `Z = 1` stand for is the affine point of
their `X` and `Y`. -/
theorem affine_of_rep_one {C : Curve} (hC : Law C) {X Y : Fe C} {P : Point C} (h : Rep C X Y 1 P) :
    P = .affine X Y := by
  cases P with
  | infinity => exact absurd h.2.2 hC.one_ne_zero
  | affine x y =>
    obtain ⟨-, hx, hy⟩ := h
    rw [Lean.Grind.Semiring.mul_one] at hx hy
    rw [hx, hy]

/-- What `qMul` writes: the call's, and `EXPP`'s slot. -/
abbrev qW : List (Nat × Nat) := slW brainpoolp320r1 [EXPP] ++ gW

theorem qMul_ok (hc : BaseCfgOk brainpoolp320r1) (hC : Law brainpoolp320r1.C)
    {P : Point brainpoolp320r1.C} (hP : onCurve brainpoolp320r1.C P = true)
    {base : Addr} {g : Reg → BitVec 64} {s : State} (hs : Scr s base size)
    (F : Fixed brainpoolp320r1 base g s.mem)
    (hpx : sv brainpoolp320r1 base s PX < brainpoolp320r1.C.p) (hpy : sv brainpoolp320r1 base s PY < brainpoolp320r1.C.p)
    (hG : Rep brainpoolp320r1.C (tmv brainpoolp320r1.C brainpoolp320r1.n base s (brainpoolp320r1.sl PX))
      (tmv brainpoolp320r1.C brainpoolp320r1.n base s (brainpoolp320r1.sl PY)) (tmv brainpoolp320r1.C brainpoolp320r1.n base s (brainpoolp320r1.sl ONEP)) P) :
    WP isa qMul s fun s' => KeepRegs (powClob 5) s s' ∧
      Unch base qW s.mem s'.mem ∧ Fixed brainpoolp320r1 base g s'.mem ∧
      ModOkA brainpoolp320r1.MP' size brainpoolp320r1.C.p s'.mem base ∧
      (∀ x ∈ [brainpoolp320r1.sl RX, brainpoolp320r1.sl RY, brainpoolp320r1.sl RZ], wordsVal s'.mem base x brainpoolp320r1.n < brainpoolp320r1.C.p) ∧
      Rep brainpoolp320r1.C (tmv brainpoolp320r1.C brainpoolp320r1.n base s' (brainpoolp320r1.sl RX))
        (tmv brainpoolp320r1.C brainpoolp320r1.n base s' (brainpoolp320r1.sl RY))
        (tmv brainpoolp320r1.C brainpoolp320r1.n base s' (brainpoolp320r1.sl RZ)) (mul (sv brainpoolp320r1 base s K) P) ∧
      sv brainpoolp320r1 base s' EXPP = brainpoolp320r1.mont (3 * brainpoolp320r1.C.b) := by
  have hn := hs.nowrap
  have h7 := hc.n10
  have hp3 := hc.p_ge
  have hpR := unitMod_pow_two hc.p_odd (64 * brainpoolp320r1.n)
  refine WP.seq (WP.mono (setConst_ok hs (n := 5) (o := brainpoolp320r1.sl EXPP)
    (x := brainpoolp320r1.mont (3 * brainpoolp320r1.C.b)) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨b₁, K₁, O₁⟩ => ?_)
  have U₁ : Unch base (slW brainpoolp320r1 [EXPP]) s.mem s₁.mem := O₁.unch
  have hs₁ := hs.of_keepRegs K₁ (by decide)
  have F₁ := F.unch h7 hn (fixedOk_slW (l := [EXPP]) (by decide)) U₁
  have e₁ : ∀ {i}, i < 45 → i ≠ EXPP → sv brainpoolp320r1 base s₁ i = sv brainpoolp320r1 base s i :=
    fun hi he => sv_unch U₁ h7 hn hi (apart_slW (by simpa using he))
  have eP : ∀ {i}, i < 45 → i ≠ EXPP →
      tmv brainpoolp320r1.C brainpoolp320r1.n base s₁ (brainpoolp320r1.sl i) = tmv brainpoolp320r1.C brainpoolp320r1.n base s (brainpoolp320r1.sl i) :=
    fun hi he => congrArg (fun x => toM brainpoolp320r1.C.p (2 ^ (64 * brainpoolp320r1.n)) x) (e₁ hi he)
  have hone : tmv brainpoolp320r1.C brainpoolp320r1.n base s (brainpoolp320r1.sl ONEP) = 1 := by
    show toM _ _ (wordsVal s.mem base (brainpoolp320r1.sl ONEP) brainpoolp320r1.n) = 1
    rw [F.onep]; exact toM_one (m := brainpoolp320r1.C.p) (R := 2 ^ (64 * brainpoolp320r1.n)) hpR
  rw [hone] at hG
  have hPe := affine_of_rep_one hC hG
  have hPe₁ : P = .affine (tmv brainpoolp320r1.C brainpoolp320r1.n base s₁ (brainpoolp320r1.sl PX)) (tmv brainpoolp320r1.C brainpoolp320r1.n base s₁ (brainpoolp320r1.sl PY)) := by
    show P = .affine (tmv brainpoolp320r1.C brainpoolp320r1.n base s₁ (brainpoolp320r1.sl PX)) (tmv brainpoolp320r1.C brainpoolp320r1.n base s₁ (brainpoolp320r1.sl PY))
    rw [eP (i := PX) (by decide) (by decide), eP (i := PY) (by decide) (by decide)]; exact hPe
  refine WP.mono (mulAt_ok hc (.inr (.inl rfl)) (.inl (by decide)) ladLayM ladAM hC mulFn_v mulFn_nf
    (name := "vg_brainpoolp320r1_mul") (px := PX) (py := PY) (by decide) (by decide)
    (by decide) (by decide) (by decide) hs₁ F₁ (by rw [e₁ (by decide) (by decide)]; exact hpx)
    (by rw [e₁ (by decide) (by decide)]; exact hpy) (by rw [← hPe₁]; exact hP))
    fun s' ⟨K, U, F', M, L, R⟩ => ⟨(K₁.mono (by decide)).trans K, U₁.trans U, F', M, L, ?_, ?_⟩
  · rw [← hPe₁, e₁ (by decide) (by decide)] at R; exact R
  · exact (sv_unch U h7 hn (i := EXPP) (by decide)
      (apart_append (apart_slW (by decide)) (apart_mulWF (.inl (by decide)) (by decide) (by decide)))).trans b₁

end VG.Proof.Ecdh.AArch64.BrainpoolP320r1

end

end


/-! # Peer multiplication followed by inversion -/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.BrainpoolP320r1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdh.AArch64 VG.Impl.Ecdh.AArch64.BrainpoolP320r1
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.BrainpoolP320r1
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

structure LadPost (base : Addr) (g : Reg → BitVec 64) (P : Point brainpoolp320r1.C) (k : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ powClob brainpoolp320r1.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (qW ++ chainWc brainpoolp320r1) s.mem s'.mem
  fixed : Fixed brainpoolp320r1 base g s'.mem
  q : Rep brainpoolp320r1.C (tmv brainpoolp320r1.C brainpoolp320r1.n base s' (brainpoolp320r1.sl RX)) (tmv brainpoolp320r1.C brainpoolp320r1.n base s' (brainpoolp320r1.sl RY))
    (tmv brainpoolp320r1.C brainpoolp320r1.n base s' (brainpoolp320r1.sl RZ)) (mul k P)
  acc_lt : sv brainpoolp320r1 base s' ACC < brainpoolp320r1.C.p
  acc : toM brainpoolp320r1.C.p (2 ^ (64 * brainpoolp320r1.n)) (sv brainpoolp320r1 base s' ACC) = tmv brainpoolp320r1.C brainpoolp320r1.n base s' (brainpoolp320r1.sl RZ) ^ (brainpoolp320r1.C.p - 2)
  rz_lt : sv brainpoolp320r1 base s' RZ < brainpoolp320r1.C.p

/-- `[d]P` by windows, then `Z^(p-2)`. -/
theorem ladPow_ok (hc : BaseCfgOk brainpoolp320r1) (hC : Law brainpoolp320r1.C) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed brainpoolp320r1 base g s.mem) {P : Point brainpoolp320r1.C} (hP : onCurve brainpoolp320r1.C P = true)
    (hpx : sv brainpoolp320r1 base s PX < brainpoolp320r1.C.p) (hpy : sv brainpoolp320r1 base s PY < brainpoolp320r1.C.p)
    (hrep : Rep brainpoolp320r1.C (tmv brainpoolp320r1.C brainpoolp320r1.n base s (brainpoolp320r1.sl PX)) (tmv brainpoolp320r1.C brainpoolp320r1.n base s (brainpoolp320r1.sl PY))
      (tmv brainpoolp320r1.C brainpoolp320r1.n base s (brainpoolp320r1.sl ONEP)) P)
    {rest : Prog isa} {R : State → Prop}
    (h : ∀ s', LadPost base g P (sv brainpoolp320r1 base s K) s s' → WP isa rest s' R) :
    WP isa (.seq qMul (.seq brainpoolp320r1.pPow rest)) s R := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * brainpoolp320r1.n)
  refine WP.seq (WP.mono (qMul_ok hc hC hP hs F hpx hpy hrep)
    fun s₃ ⟨K₃, U₃, F₃, M₃, L₃, R₃, _⟩ => ?_)
  have hs₃ := hs.of_keepRegs K₃ (x0_not_powClob h7)
  have rz₃ : wordsVal s₃.mem base (brainpoolp320r1.sl RZ) brainpoolp320r1.n < brainpoolp320r1.C.p := L₃ _ (by simp)
  refine WP.seq (WP.mono (pPow_ok hc hs₃ M₃ rz₃)
    fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => h s₄ ?_)
  have r₄ : ∀ {i}, i < 45 → i ∉ [ACC, TMP] → sv brainpoolp320r1 base s₄ i = sv brainpoolp320r1 base s₃ i := fun hi h₁ =>
    sv_unch U₄ h7 hn hi (apart_chainWc hc hi h₁)
  refine ⟨hs₃.of_keepRegs K₄ (x0_not_powClob h7), fun r hr => ?_, by rw [K₄.rd, K₃.rd],
    by rw [K₄.wr, K₃.wr], U₃.trans U₄, F₃.unch h7 hn (fixedOk_chainWc hc) U₄, ?_, lt₄, ?_, ?_⟩
  · rw [K₄.gpr r hr, K₃.gpr r hr]
  · show Rep _ (toM _ _ (sv brainpoolp320r1 base s₄ RX)) (toM _ _ (sv brainpoolp320r1 base s₄ RY)) (toM _ _ (sv brainpoolp320r1 base s₄ RZ)) _
    rw [r₄ (i := RX) (by decide) (by decide), r₄ (i := RY) (by decide) (by decide),
      r₄ (i := RZ) (by decide) (by decide)]
    exact R₃
  · show _ = toM _ _ (sv brainpoolp320r1 base s₄ RZ) ^ _
    rw [r₄ (i := RZ) (by decide) (by decide)]
    exact v₄
  · rw [r₄ (i := RZ) (by decide) (by decide)]; exact rz₃

end VG.Proof.Ecdh.AArch64.BrainpoolP320r1

/-! # brainpoolP320r1 ECDH with the general ladder -/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.BrainpoolP320r1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdh.AArch64 VG.Impl.Ecdh.AArch64.BrainpoolP320r1
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.BrainpoolP320r1
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

theorem exchange_ok (hc : BaseCfgOk brainpoolp320r1) (hC : Law brainpoolp320r1.C) {s₀ : State} (hp : EPre brainpoolp320r1 s₀) :
    WP isa Impl.Ecdh.AArch64.BrainpoolP320r1.exchange s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ EPost brainpoolp320r1 s₀ s' := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hsz : size = 8192 := rfl
  obtain hpR := unitMod_pow_two hc.p_odd (64 * brainpoolp320r1.n)
  have hp3 := hc.p_ge
  unfold Impl.Ecdh.AArch64.BrainpoolP320r1.exchange
  refine WP.seq (WP.mono (args_ok s₀) fun s₁ ⟨x4₁, x6₁, x3₁, x2₁, k₁⟩ => ?_)
  obtain x1₁ : s₁.gpr .x1 = s₀.gpr .x1 := k₁.gpr _ (by decide)
  obtain x0₁ : s₁.gpr .x0 = s₀.gpr .x0 := k₁.gpr _ (by decide)
  obtain hrd₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [k₁.rd, k₁.wr]
  have hl8 := hc.len8
  have hhi := hc.len_hi
  obtain hsp : SetupPre brainpoolp320r1 s₁ := by
    refine ⟨by rw [k₁.wr, hp.wr, x4₁]; simp, fun e he => ?_, fun e he => ?_, fun e he => ?_, ?_, ?_, ?_,
      by rw [x4₁]; exact hp.sc_fit⟩
    · rw [x3₁, hrd₁, hp.rd]
      exact ⟨_, by simp, Offset.contains_base _ he (by omega_arith)⟩
    · rw [x1₁, hrd₁, hp.rd]
      exact ⟨_, by simp, Offset.contains_base _ he (by omega_arith)⟩
    · rw [x2₁, hrd₁, hp.rd, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact ⟨⟨s₀.gpr .x2, 1 + 2 * brainpoolp320r1.C.len⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [x1₁, x4₁]; exact hp.d_sc
    · rw [x2₁, x4₁]; exact hp.peer_sc.sub_left (Offset.sub_base _ (by omega_arith))
    · rw [x3₁, x4₁]; exact hp.d_sc
  refine WP.seq (WP.mono (stage₁ hc (.inl rfl) hsp (rest := .block []) (Q := St₁ brainpoolp320r1 none s₁ (s₁.gpr .x4))
    fun _ S => WP.block_nil S) fun s₂ S₂ => ?_)
  rw [x4₁] at S₂
  have hn := S₂.scr.nowrap
  obtain hq₂ : s₂.gpr .x6 = s₀.gpr .x2 := by rw [S₂.gpr _ (by decide), x6₁]
  obtain hrw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [S₂.rd, S₂.wr, hrd₁]
  -- The peer's key.
  refine WP.seq (WP.mono (peer_ok hc S₂.scr hq₂ (by rw [hrw₂, hp.rd]; simp) hp.peer_sc)
    fun s₃ ⟨hs₃, k₃, U₃, r2₃, bp₃, y₃, f₃⟩ => ?_)
  obtain F₃ := S₂.fixed.unch h7 hn ((fixedOk_slW (l := [R2P, BP, QY]) (by decide)).append fixedOk_flag) U₃
  obtain e₃ : ∀ {i}, i < 45 → i ∉ [R2P, BP, QY] → i ≠ FLAG →
      sv brainpoolp320r1 (s₀.gpr .x3) s₃ i = sv brainpoolp320r1 (s₀.gpr .x3) s₂ i := fun hi hl hf =>
    sv_unch U₃ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  obtain x₃ : sv brainpoolp320r1 (s₀.gpr .x3) s₃ E = sv brainpoolp320r1 (s₀.gpr .x3) s₂ E := e₃ (by decide) (by decide) (by decide)
  -- The peer's key has not changed.
  obtain W₂ : Outside (s₀.gpr .x3) 0 size s₀.mem s₂.mem := fun x hx =>
    (S₂.unch x fun w hw => by rw [List.mem_singleton.mp hw]; exact hx).trans (congrFun k₁.mem x)
  obtain hq0 : s₂.mem (s₀.gpr .x2) = s₀.mem (s₀.gpr .x2) := by
    have := keep_of_disjoint' W₂ hp.peer_sc (by omega_arith) (i := 0) (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  -- What the code checks of the peer's key so far.
  obtain hf₃ : word s₃.mem (s₀.gpr .x3) (brainpoolp320r1.sl FLAG) = mask (s₀.mem (s₀.gpr .x2) = 4) := by
    rw [f₃, S₂.flag, BitVec.allOnes_and, hq0]
  refine WP.seq (WP.mono (validate_ok hc hs₃ F₃ r2₃ bp₃ hf₃)
    fun s₄ ⟨hs₄, g₄, rd₄, wr₄, U₄, f₄, px_lt, py_lt, px, py⟩ => ?_)
  obtain F₄ := F₃.unch h7 hn ((fixedOk_slW (l := [QXM, QYM, TMP, W0, W1, W2, W3, PY]) (by decide)).append
    fixedOk_flag) U₄
  obtain e₄ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY] → i ≠ FLAG →
      sv brainpoolp320r1 (s₀.gpr .x3) s₄ i = sv brainpoolp320r1 (s₀.gpr .x3) s₃ i := fun hi hl hf =>
    sv_unch U₄ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  -- `[d]P`, then `Z^(p-2)`.
  obtain hk₄ : sv brainpoolp320r1 (s₀.gpr .x3) s₄ K = dk brainpoolp320r1 s₀ := by
    rw [e₄ (by decide) (by decide) (by decide), e₃ (by decide) (by decide) (by decide), S₂.k]
    simp only [kv, dk, k₁.mem, x3₁]
  refine ladPow_ok hc hC hs₄ F₄ (peerPt_onCurve hc _ _ _) px_lt py_lt
    (peerPt_rep hC _ _ _ px py |> fun h => by
      show Rep brainpoolp320r1.C (toM brainpoolp320r1.C.p (2 ^ (64 * brainpoolp320r1.n)) (sv brainpoolp320r1 (s₀.gpr .x3) s₄ PX))
        (toM brainpoolp320r1.C.p (2 ^ (64 * brainpoolp320r1.n)) (sv brainpoolp320r1 (s₀.gpr .x3) s₄ PY))
        (toM brainpoolp320r1.C.p (2 ^ (64 * brainpoolp320r1.n)) (wordsVal s₄.mem (s₀.gpr .x3) (brainpoolp320r1.sl ONEP) brainpoolp320r1.n)) _
      rw [F₄.onep, toM_one hpR]; exact h) fun s₅ L => ?_
  have hs₅ := L.scr
  have F₅ := L.fixed
  obtain aq : ∀ {i}, i < 45 → i ∉ [EXPP, BM, RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ,
      TMP] → i ≠ 54 ∧ i ≠ 61 ∧ i ≠ 82 → ∀ w ∈ qW, brainpoolp320r1.sl i + 8 * brainpoolp320r1.n ≤ w.1 ∨ w.1 + w.2 ≤ brainpoolp320r1.sl i :=
    fun hi hl ha => by
      obtain s₁ : ∀ x ∈ [EXPP], x ∈ [EXPP, BM, RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY,
        DZ, TMP] := by decide
      obtain s₂ : ∀ x ∈ [BM], x ∈ [EXPP, BM, RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY,
        DZ, TMP] := by decide
      obtain s₃ : ∀ x ∈ [RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP],
        x ∈ [EXPP, BM, RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP] := by decide
      exact apart_append (apart_slW (fun h => hl (s₁ _ h)) ha)
        (apart_append (apart_slW (fun h => hl (s₂ _ h)) ha) (apart_mulWF (.inl (by decide)) hi (fun h => hl (s₃ _ h)) ha))
  obtain e₅ : ∀ {i}, i < 45 → i ∉ [EXPP, BM, RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY,
      DZ, TMP] → i ∉ [ACC, TMP] →
      sv brainpoolp320r1 (s₀.gpr .x3) s₅ i = sv brainpoolp320r1 (s₀.gpr .x3) s₄ i :=
    fun hi h₁ h₂ => sv_unch L.unch h7 hn hi
      (apart_append (aq hi h₁ (by constructor <;> omega_arith)) (apart_chainWc hc hi h₂))
  have hflag₅ := f₄
  obtain hf₅ : word s₅.mem (s₀.gpr .x3) (brainpoolp320r1.sl FLAG) = word s₄.mem (s₀.gpr .x3) (brainpoolp320r1.sl FLAG) := by
    obtain hF := sl_le brainpoolp320r1 h7 (i := FLAG) (by decide)
    refine L.unch.word (fun w hw => ?_) (by omega_arith)
    obtain ha := apart_append (aq (i := FLAG) (by decide) (by decide) (by decide))
      (apart_chainWc hc (i := FLAG) (by decide) (by decide)) w hw
    rcases ha with ha | ha
    · exact .inl (by omega_arith)
    · exact .inr ha
  rw [← hf₅] at hflag₅
  obtain hx20₅ : s₅.gpr .x20 = s₀.gpr .x0 := by
    rw [L.gpr _ (x20_not_powClob h7), g₄ _ (x20_not_clob h7), k₃.gpr _ (by decide),
      S₂.x20, x0₁]
  obtain hw₅ : (⟨s₀.gpr .x0, brainpoolp320r1.C.len⟩ : Region) ∈ s₅.wr := by
    rw [L.wr, wr₄, k₃.wr, S₂.wr, k₁.wr, hp.wr]; simp
  refine WP.mono (middle_ok hc hs₅ F₅ L.acc_lt hflag₅ hx20₅ hp.out_fit hw₅ hp.out_sc)
    fun s' ⟨xv, hxl, hxv, bytes, ret, saved⟩ => ⟨fun r hr => ?_, ?_⟩
  · have hsv : ∀ r ∈ Cfg.saved.map Prod.fst, r ∉ [Reg.x2, .x3, .x4, .x6] := by decide
    rw [saved r hr, k₁.gpr r (hsv r hr)]
  -- The specification.
  obtain hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (1 + 2 * brainpoolp320r1.C.len)).length = 2 * brainpoolp320r1.C.len + 1 := by
    rw [length_bytesAt]; omega_arith
  obtain hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (1 + 2 * brainpoolp320r1.C.len)).head? = some (s₀.mem (s₀.gpr .x2)) := by
    rw [peer_bytes]; rfl
  obtain hxs : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (1 + 2 * brainpoolp320r1.C.len)).drop 1).take brainpoolp320r1.C.len) =
      sv brainpoolp320r1 (s₀.gpr .x3) s₃ E := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _), x₃, S₂.e,
      shAt_none, Nat.shiftRight_zero]
    simp only [ev, k₁.mem, x2₁]
  obtain hys : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (1 + 2 * brainpoolp320r1.C.len)).drop (brainpoolp320r1.C.len + 1)) =
      sv brainpoolp320r1 (s₀.gpr .x3) s₃ QY := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _), y₃,
      bytesAt_keep W₂ (hp.peer_sc.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith) (by omega_arith)]
  obtain hP' : ∀ h : Ecdh.Valid brainpoolp320r1.C (s₀.mem (s₀.gpr .x2)) (sv brainpoolp320r1 (s₀.gpr .x3) s₃ E) (sv brainpoolp320r1 (s₀.gpr .x3) s₃ QY),
      peerPt brainpoolp320r1 (s₀.mem (s₀.gpr .x2) = 4) (sv brainpoolp320r1 (s₀.gpr .x3) s₃ E) (sv brainpoolp320r1 (s₀.gpr .x3) s₃ QY) =
        .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have hR := L.q
  rw [hk₄] at hR
  obtain hxoX : Fin.ofNat brainpoolp320r1.C.p xv = tmv brainpoolp320r1.C brainpoolp320r1.n (s₀.gpr .x3) s₅ (brainpoolp320r1.sl RX) *
      tmv brainpoolp320r1.C brainpoolp320r1.n (s₀.gpr .x3) s₅ (brainpoolp320r1.sl RZ) ^ (brainpoolp320r1.C.p - 2) := by rw [hxv, L.acc]
  obtain hspec := exchange_eq hC hlen hb0 hxs hys hP' hR hxl hxoX
  obtain hD₅ : sv brainpoolp320r1 (s₀.gpr .x3) s₅ D = dk brainpoolp320r1 s₀ := by
    rw [e₅ (by decide) (by decide) (by decide), e₄ (by decide) (by decide) (by decide),
      e₃ (by decide) (by decide) (by decide), S₂.d, shAt_none, Nat.shiftRight_zero]
    simp only [dv, dk, k₁.mem, x1₁]
  obtain hz : tmv brainpoolp320r1.C brainpoolp320r1.n (s₀.gpr .x3) s₅ (brainpoolp320r1.sl RZ) ≠ 0 ↔ sv brainpoolp320r1 (s₀.gpr .x3) s₅ RZ ≠ 0 :=
    not_congr (toM_eq_zero_iff hpR L.rz_lt)
  unfold EPost
  rw [hspec]
  by_cases hcond : (1 ≤ dk brainpoolp320r1 s₀ ∧ dk brainpoolp320r1 s₀ < brainpoolp320r1.C.n) ∧
      Ecdh.Valid brainpoolp320r1.C (s₀.mem (s₀.gpr .x2)) (sv brainpoolp320r1 (s₀.gpr .x3) s₃ E) (sv brainpoolp320r1 (s₀.gpr .x3) s₃ QY) ∧
      tmv brainpoolp320r1.C brainpoolp320r1.n (s₀.gpr .x3) s₅ (brainpoolp320r1.sl RZ) ≠ 0
  · have hok : ok brainpoolp320r1 (s₀.gpr .x3) s₅ (PeerOk brainpoolp320r1 (s₀.gpr .x3) s₃ ((s₀.mem (s₀.gpr .x2) = 4 ∧
        sv brainpoolp320r1 (s₀.gpr .x3) s₃ E < brainpoolp320r1.C.p) ∧ sv brainpoolp320r1 (s₀.gpr .x3) s₃ QY < brainpoolp320r1.C.p)) = true := by
      refine decide_eq_true ⟨⟨⟨⟨⟨hcond.2.1.1, hcond.2.1.2.1⟩, hcond.2.1.2.2.1⟩, hcond.2.1.2.2.2⟩, ?_, ?_⟩,
        hz.mp hcond.2.2⟩
      · rw [hD₅]; exact hcond.1.1
      · rw [hD₅]; exact hcond.1.2
    rw [ite_eq_left hcond]
    exact ⟨by rw [ret, hok]; rfl, by rw [bytes, hok]; rfl⟩
  · have hok : ok brainpoolp320r1 (s₀.gpr .x3) s₅ (PeerOk brainpoolp320r1 (s₀.gpr .x3) s₃ ((s₀.mem (s₀.gpr .x2) = 4 ∧
        sv brainpoolp320r1 (s₀.gpr .x3) s₃ E < brainpoolp320r1.C.p) ∧ sv brainpoolp320r1 (s₀.gpr .x3) s₃ QY < brainpoolp320r1.C.p)) = false := by
      refine decide_eq_false fun h => hcond ⟨⟨?_, ?_⟩, ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2⟩,
        hz.mpr h.2⟩
      · rw [← hD₅]; exact h.1.2.1
      · rw [← hD₅]; exact h.1.2.2
    rw [ite_eq_right hcond]
    exact ⟨by rw [ret, hok]; rfl, by rw [bytes, hok]; rfl⟩

end VG.Proof.Ecdh.AArch64.BrainpoolP320r1
