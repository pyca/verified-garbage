import VerifiedGarbage.Impl.P256.EcdhJac.Frontend
import VerifiedGarbage.Proof.P256.EcdhJac.Setup
import VerifiedGarbage.Proof.Ecdh.AArch64.WithMul
import VerifiedGarbage.Proof.Ecdh.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Ecdh.AArch64.MulOk

namespace VG.Proof.P256.EcdhJac.Frontend
open VG.Proof.Ecdh.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Impl.Ecdh.AArch64 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)
variable {c : Cfg}

theorem exchangeWith_eq' (c : Cfg) (mq inverse : Prog isa) : Impl.P256.EcdhJac.Frontend.exchange c mq inverse =
    .seq (.block Impl.Ecdh.AArch64.Cfg.args)
      (.seq (.block (c.setupWith none))
      (.seq (.block (Impl.Ecdh.AArch64.Cfg.peer c)) (.seq (Impl.Ecdh.AArch64.Cfg.validate c)
      (.seq mq (.seq inverse (Impl.Ecdh.AArch64.Cfg.middle c)))))) := rfl

theorem exchangeWith_ok (hc : CfgOk c) (hC : Law c.C) {mq inverse : Prog isa} (hm : MulWithInverseOk c mq inverse) (hn4 : c.n = 4)
    (hmc : CallsKeep (Impl.Ecdh.AArch64.Cfg.middle c))
    (hmu : KeepsUntouched (Impl.Ecdh.AArch64.Cfg.middle c)) {s₀ : State} (hp : EPre c s₀) :
    WP isa (Impl.P256.EcdhJac.Frontend.exchange c mq inverse) s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧
      (∀ r ∈ untouched, s'.gpr r = s₀.gpr r) ∧ EPost c s₀ s' := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  rw [exchangeWith_eq']
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
  refine WP.seq (WP.mono (Setup.setup_only_ok hc hsp) fun s₂ S₂ => ?_)
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
  refine hm hs₄ F₄ (peerPt_onCurve hc _ _ _) px_lt py_lt
    (peerPt_rep hC _ _ _ px py |> fun h => by
      show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x3) s₄ PX))
        (toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x3) s₄ PY))
        (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₄.mem (s₀.gpr .x3) (c.sl ONEP) c.n)) _
      rw [F₄.onep, toM_one hpR]; exact h)
    fun s₅ L => ?_
  have hs₅ := L.scr
  have F₅ := L.fixed
  have hflag₅ := L.flag.trans f₄
  have hx20₅ : s₅.gpr .x20 = s₀.gpr .x0 := by
    rw [L.x20, g₄ _ (x20_not_clob h7), k₃.gpr _ (by decide),
      S₂.x20, x0₁]
  have hw₅ : (⟨s₀.gpr .x0, c.C.len⟩ : Region) ∈ s₅.wr := by
    rw [L.wr, wr₄, k₃.wr, S₂.wr, k₁.wr, hp.wr]; simp
  obtain ⟨tm, s', em, xv, hxl, hxv, bytes, ret, saved⟩ :=
    middle_ok hc hs₅ F₅ L.acc_lt hflag₅ hx20₅ hp.out_fit hw₅ hp.out_sc
  refine ⟨tm, s', em, (fun r hr => ?_), (fun r hr => ?_), ?_⟩
  · have hsv : ∀ r ∈ Cfg.saved.map Prod.fst, r ∉ [Reg.x2, .x3, .x4, .x6] := by decide
    rw [saved r hr, k₁.gpr r (hsv r hr)]
  · have hncl : r ∉ clob c.n := by
      rw [hn4]
      revert hr
      revert r
      decide
    have hpcl : r ∉ [Reg.x0, .x1, .x2, .x5, .x16, .x17, .x19, .x20] :=
      (by decide : ∀ r ∈ untouched, r ∉ [Reg.x0, .x1, .x2, .x5, .x16, .x17, .x19, .x20]) r hr
    have ha : r ∉ [Reg.x2, .x3, .x4, .x6] :=
      (by decide : ∀ r ∈ untouched, r ∉ [Reg.x2, .x3, .x4, .x6]) r hr
    have hb : r ∉ [Reg.x1, .x2, .x5, .x7, .x16, .x17] :=
      (by decide : ∀ r ∈ untouched, r ∉ [Reg.x1, .x2, .x5, .x7, .x16, .x17]) r hr
    rw [untouched_keep em hmc hmu r hr, L.extra r hr, g₄ r hncl,
      k₃.gpr r hb, S₂.gpr r hpcl, k₁.gpr r ha]
  -- The specification.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (1 + 2 * c.C.len)).head? = some (s₀.mem (s₀.gpr .x2)) := by
    rw [peer_bytes]; rfl
  have hxs : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      sv c (s₀.gpr .x3) s₃ E := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _), x₃, S₂.e]
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
  have hspec := exchange_eq_of_range hC hlen hb0 hxs hys hP' hR hxl hxoX
  have hD₅ : sv c (s₀.gpr .x3) s₅ D = dk c s₀ := by
    rw [L.d, e₄ (by decide) (by decide) (by decide),
      e₃ (by decide) (by decide) (by decide), S₂.d]
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

end VG.Proof.P256.EcdhJac.Frontend
