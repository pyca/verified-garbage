import VerifiedGarbage.Proof.Ecdh.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Ecdh.AArch64.MulOk

namespace VG.Proof.Ecdh.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Impl.Ecdh.AArch64 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)
variable {c : Cfg}

/-- The established inputs to an arbitrary scalar multiplication. -/
def MulInput (c : Cfg) (s : State) : Prop :=
  ∃ (base : Addr) (g : Reg → BitVec 64) (P : Point c.C),
    Scr s base size ∧ Fixed c base g s.mem ∧ onCurve c.C P = true ∧
    sv c base s PX < c.C.p ∧ sv c base s PY < c.C.p ∧
    Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P

theorem beforeMul_eq' (c : Cfg) : Impl.Ecdh.AArch64.Cfg.beforeMul c =
    .seq (.block Impl.Ecdh.AArch64.Cfg.args)
      (.seq (.seq (.block (c.setupWith none)) (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) (.block [])))
      (.seq (.block (Impl.Ecdh.AArch64.Cfg.peer c)) (Impl.Ecdh.AArch64.Cfg.validate c))) := rfl

theorem beforeMul_ok (hc : CfgOk c) (hC : Law c.C) {s₀ : State} (hp : EPre c s₀) :
    WP isa (Impl.Ecdh.AArch64.Cfg.beforeMul c) s₀ fun s =>
      MulInput c s ∧ s.gpr .x0 = s₀.gpr .x3 ∧ s.gpr .x20 = s₀.gpr .x0 := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  rw [beforeMul_eq']
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
  refine WP.mono (validate_ok hc hs₃ F₃ r2₃ bp₃ hf₃)
    fun s₄ ⟨hs₄, g₄, rd₄, wr₄, U₄, f₄, px_lt, py_lt, px, py⟩ => ?_
  have F₄ := F₃.unch h7 hn ((fixedOk_slW (l := [QXM, QYM, TMP, W0, W1, W2, W3, PY]) (by decide)).append
    fixedOk_flag) U₄
  refine ⟨⟨_, _, peerPt c (s₀.mem (s₀.gpr .x2) = 4)
      (sv c (s₀.gpr .x3) s₃ E) (sv c (s₀.gpr .x3) s₃ QY),
      hs₄, F₄, peerPt_onCurve hc _ _ _, px_lt, py_lt, ?_⟩, hs₄.x0, ?_⟩
  · have h := peerPt_rep hC _ _ _ px py
    show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x3) s₄ PX))
      (toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x3) s₄ PY))
      (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₄.mem (s₀.gpr .x3) (c.sl ONEP) c.n)) _
    rw [F₄.onep, toM_one hpR]
    exact h
  · rw [g₄ _ (x20_not_clob h7), k₃.gpr _ (by decide), S₂.x20, x0₁]

end VG.Proof.Ecdh.AArch64
