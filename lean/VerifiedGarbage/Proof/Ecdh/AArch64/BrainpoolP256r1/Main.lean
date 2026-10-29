module

public import VerifiedGarbage.Proof.Ecdh.AArch64.Main
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.AArch64
import VerifiedGarbage.Proof.Ecdh.AArch64.BrainpoolP256r1.MulPow
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Framework.Offset

/-! # brainpoolP256r1 ECDH with the general ladder -/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.BrainpoolP256r1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdh.AArch64 VG.Impl.Ecdh.AArch64.BrainpoolP256r1
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.BrainpoolP256r1
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

theorem exchange_ok (hc : BaseCfgOk brainpoolp256r1) (hC : Law brainpoolp256r1.C) {s₀ : State} (hp : EPre brainpoolp256r1 s₀) :
    WP isa Impl.Ecdh.AArch64.BrainpoolP256r1.exchange s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ EPost brainpoolp256r1 s₀ s' := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * brainpoolp256r1.n)
  have hp3 := hc.p_ge
  unfold Impl.Ecdh.AArch64.BrainpoolP256r1.exchange
  refine WP.seq (WP.mono (args_ok s₀) fun s₁ ⟨x4₁, x6₁, x3₁, x2₁, k₁⟩ => ?_)
  have x1₁ : s₁.gpr .x1 = s₀.gpr .x1 := k₁.gpr _ (by decide)
  have x0₁ : s₁.gpr .x0 = s₀.gpr .x0 := k₁.gpr _ (by decide)
  have hrd₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [k₁.rd, k₁.wr]
  have hl8 := hc.len8
  have hhi := hc.len_hi
  have hsp : SetupPre brainpoolp256r1 s₁ := by
    refine ⟨by rw [k₁.wr, hp.wr, x4₁]; simp, fun e he => ?_, fun e he => ?_, fun e he => ?_, ?_, ?_, ?_,
      by rw [x4₁]; exact hp.sc_fit⟩
    · rw [x3₁, hrd₁, hp.rd]
      exact ⟨_, by simp, Offset.contains_base _ he (by omega_arith)⟩
    · rw [x1₁, hrd₁, hp.rd]
      exact ⟨_, by simp, Offset.contains_base _ he (by omega_arith)⟩
    · rw [x2₁, hrd₁, hp.rd, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact ⟨⟨s₀.gpr .x2, 1 + 2 * brainpoolp256r1.C.len⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [x1₁, x4₁]; exact hp.d_sc
    · rw [x2₁, x4₁]; exact hp.peer_sc.sub_left (Offset.sub_base _ (by omega_arith))
    · rw [x3₁, x4₁]; exact hp.d_sc
  refine WP.seq (WP.mono (stage₁ hc (.inl rfl) hsp (rest := .block []) (Q := St₁ brainpoolp256r1 none s₁ (s₁.gpr .x4))
    fun _ S => WP.block_nil S) fun s₂ S₂ => ?_)
  rw [x4₁] at S₂
  have hn := S₂.scr.nowrap
  have hq₂ : s₂.gpr .x6 = s₀.gpr .x2 := by rw [S₂.gpr _ (by decide), x6₁]
  have hrw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [S₂.rd, S₂.wr, hrd₁]
  -- The peer's key.
  refine WP.seq (WP.mono (peer_ok hc S₂.scr hq₂ (by rw [hrw₂, hp.rd]; simp) hp.peer_sc)
    fun s₃ ⟨hs₃, k₃, U₃, r2₃, bp₃, y₃, f₃⟩ => ?_)
  have F₃ := S₂.fixed.unch h7 hn ((fixedOk_slW (l := [R2P, BP, QY]) (by decide)).append fixedOk_flag) U₃
  have e₃ : ∀ {i}, i < 45 → i ∉ [R2P, BP, QY] → i ≠ FLAG →
      sv brainpoolp256r1 (s₀.gpr .x3) s₃ i = sv brainpoolp256r1 (s₀.gpr .x3) s₂ i := fun hi hl hf =>
    sv_unch U₃ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have x₃ : sv brainpoolp256r1 (s₀.gpr .x3) s₃ E = sv brainpoolp256r1 (s₀.gpr .x3) s₂ E := e₃ (by decide) (by decide) (by decide)
  -- The peer's key has not changed.
  have W₂ : Outside (s₀.gpr .x3) 0 size s₀.mem s₂.mem := fun x hx =>
    (S₂.unch x fun w hw => by rw [List.mem_singleton.mp hw]; exact hx).trans (congrFun k₁.mem x)
  have hq0 : s₂.mem (s₀.gpr .x2) = s₀.mem (s₀.gpr .x2) := by
    have := keep_of_disjoint' W₂ hp.peer_sc (by omega_arith) (i := 0) (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  -- What the code checks of the peer's key so far.
  have hf₃ : word s₃.mem (s₀.gpr .x3) (brainpoolp256r1.sl FLAG) = mask (s₀.mem (s₀.gpr .x2) = 4) := by
    rw [f₃, S₂.flag, BitVec.allOnes_and, hq0]
  refine WP.seq (WP.mono (validate_ok hc hs₃ F₃ r2₃ bp₃ hf₃)
    fun s₄ ⟨hs₄, g₄, rd₄, wr₄, U₄, f₄, px_lt, py_lt, px, py⟩ => ?_)
  have F₄ := F₃.unch h7 hn ((fixedOk_slW (l := [QXM, QYM, TMP, W0, W1, W2, W3, PY]) (by decide)).append
    fixedOk_flag) U₄
  have e₄ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY] → i ≠ FLAG →
      sv brainpoolp256r1 (s₀.gpr .x3) s₄ i = sv brainpoolp256r1 (s₀.gpr .x3) s₃ i := fun hi hl hf =>
    sv_unch U₄ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  -- `[d]P`, then `Z^(p-2)`.
  have hk₄ : sv brainpoolp256r1 (s₀.gpr .x3) s₄ K = dk brainpoolp256r1 s₀ := by
    rw [e₄ (by decide) (by decide) (by decide), e₃ (by decide) (by decide) (by decide), S₂.k]
    simp only [kv, dk, k₁.mem, x3₁]
  refine ladPow_ok hc hC hs₄ F₄ (peerPt_onCurve hc _ _ _) px_lt py_lt
    (peerPt_rep hC _ _ _ px py |> fun h => by
      show Rep brainpoolp256r1.C (toM brainpoolp256r1.C.p (2 ^ (64 * brainpoolp256r1.n)) (sv brainpoolp256r1 (s₀.gpr .x3) s₄ PX))
        (toM brainpoolp256r1.C.p (2 ^ (64 * brainpoolp256r1.n)) (sv brainpoolp256r1 (s₀.gpr .x3) s₄ PY))
        (toM brainpoolp256r1.C.p (2 ^ (64 * brainpoolp256r1.n)) (wordsVal s₄.mem (s₀.gpr .x3) (brainpoolp256r1.sl ONEP) brainpoolp256r1.n)) _
      rw [F₄.onep, toM_one hpR]; exact h) fun s₅ L => ?_
  have hs₅ := L.scr
  have F₅ := L.fixed
  have aq : ∀ {i}, i < 45 → i ∉ [EXPP, BM, RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ,
      TMP] → i ≠ 54 ∧ i ≠ 61 ∧ i ≠ 82 → ∀ w ∈ qW, brainpoolp256r1.sl i + 8 * brainpoolp256r1.n ≤ w.1 ∨ w.1 + w.2 ≤ brainpoolp256r1.sl i :=
    fun hi hl ha => by
      have s₁ : ∀ x ∈ [EXPP], x ∈ [EXPP, BM, RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY,
        DZ, TMP] := by decide
      have s₂ : ∀ x ∈ [BM], x ∈ [EXPP, BM, RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY,
        DZ, TMP] := by decide
      have s₃ : ∀ x ∈ [RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP],
        x ∈ [EXPP, BM, RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP] := by decide
      exact apart_append (apart_slW (fun h => hl (s₁ _ h)) ha)
        (apart_append (apart_slW (fun h => hl (s₂ _ h)) ha) (apart_mulWF (.inl (by decide)) hi (fun h => hl (s₃ _ h)) ha))
  have e₅ : ∀ {i}, i < 45 → i ∉ [EXPP, BM, RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY,
      DZ, TMP] → i ∉ [ACC, TMP] →
      sv brainpoolp256r1 (s₀.gpr .x3) s₅ i = sv brainpoolp256r1 (s₀.gpr .x3) s₄ i :=
    fun hi h₁ h₂ => sv_unch L.unch h7 hn hi
      (apart_append (aq hi h₁ (by constructor <;> omega_arith)) (apart_chainWc hc hi h₂))
  have hflag₅ := f₄
  have hf₅ : word s₅.mem (s₀.gpr .x3) (brainpoolp256r1.sl FLAG) = word s₄.mem (s₀.gpr .x3) (brainpoolp256r1.sl FLAG) := by
    have hF := sl_le brainpoolp256r1 h7 (i := FLAG) (by decide)
    refine L.unch.word (fun w hw => ?_) (by omega_arith)
    have ha := apart_append (aq (i := FLAG) (by decide) (by decide) (by decide))
      (apart_chainWc hc (i := FLAG) (by decide) (by decide)) w hw
    rcases ha with ha | ha
    · exact .inl (by omega_arith)
    · exact .inr ha
  rw [← hf₅] at hflag₅
  have hx20₅ : s₅.gpr .x20 = s₀.gpr .x0 := by
    rw [L.gpr _ (x20_not_powClob h7), g₄ _ (x20_not_clob h7), k₃.gpr _ (by decide),
      S₂.x20, x0₁]
  have hw₅ : (⟨s₀.gpr .x0, brainpoolp256r1.C.len⟩ : Region) ∈ s₅.wr := by
    rw [L.wr, wr₄, k₃.wr, S₂.wr, k₁.wr, hp.wr]; simp
  refine WP.mono (middle_ok hc hs₅ F₅ L.acc_lt hflag₅ hx20₅ hp.out_fit hw₅ hp.out_sc)
    fun s' ⟨xv, hxl, hxv, bytes, ret, saved⟩ => ⟨fun r hr => ?_, ?_⟩
  · have hsv : ∀ r ∈ Cfg.saved.map Prod.fst, r ∉ [Reg.x2, .x3, .x4, .x6] := by decide
    rw [saved r hr, k₁.gpr r (hsv r hr)]
  -- The specification.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (1 + 2 * brainpoolp256r1.C.len)).length = 2 * brainpoolp256r1.C.len + 1 := by
    rw [length_bytesAt]; omega_arith
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (1 + 2 * brainpoolp256r1.C.len)).head? = some (s₀.mem (s₀.gpr .x2)) := by
    rw [peer_bytes]; rfl
  have hxs : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (1 + 2 * brainpoolp256r1.C.len)).drop 1).take brainpoolp256r1.C.len) =
      sv brainpoolp256r1 (s₀.gpr .x3) s₃ E := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _), x₃, S₂.e,
      shAt_none, Nat.shiftRight_zero]
    simp only [ev, k₁.mem, x2₁]
  have hys : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (1 + 2 * brainpoolp256r1.C.len)).drop (brainpoolp256r1.C.len + 1)) =
      sv brainpoolp256r1 (s₀.gpr .x3) s₃ QY := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _), y₃,
      bytesAt_keep W₂ (hp.peer_sc.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith) (by omega_arith)]
  have hP' : ∀ h : Ecdh.Valid brainpoolp256r1.C (s₀.mem (s₀.gpr .x2)) (sv brainpoolp256r1 (s₀.gpr .x3) s₃ E) (sv brainpoolp256r1 (s₀.gpr .x3) s₃ QY),
      peerPt brainpoolp256r1 (s₀.mem (s₀.gpr .x2) = 4) (sv brainpoolp256r1 (s₀.gpr .x3) s₃ E) (sv brainpoolp256r1 (s₀.gpr .x3) s₃ QY) =
        .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have hR := L.q
  rw [hk₄] at hR
  have hxoX : Fin.ofNat brainpoolp256r1.C.p xv = tmv brainpoolp256r1.C brainpoolp256r1.n (s₀.gpr .x3) s₅ (brainpoolp256r1.sl RX) *
      tmv brainpoolp256r1.C brainpoolp256r1.n (s₀.gpr .x3) s₅ (brainpoolp256r1.sl RZ) ^ (brainpoolp256r1.C.p - 2) := by rw [hxv, L.acc]
  have hspec := exchange_eq hC hlen hb0 hxs hys hP' hR hxl hxoX
  have hD₅ : sv brainpoolp256r1 (s₀.gpr .x3) s₅ D = dk brainpoolp256r1 s₀ := by
    rw [e₅ (by decide) (by decide) (by decide), e₄ (by decide) (by decide) (by decide),
      e₃ (by decide) (by decide) (by decide), S₂.d, shAt_none, Nat.shiftRight_zero]
    simp only [dv, dk, k₁.mem, x1₁]
  have hz : tmv brainpoolp256r1.C brainpoolp256r1.n (s₀.gpr .x3) s₅ (brainpoolp256r1.sl RZ) ≠ 0 ↔ sv brainpoolp256r1 (s₀.gpr .x3) s₅ RZ ≠ 0 :=
    not_congr (toM_eq_zero_iff hpR L.rz_lt)
  unfold EPost
  rw [hspec]
  by_cases hcond : (1 ≤ dk brainpoolp256r1 s₀ ∧ dk brainpoolp256r1 s₀ < brainpoolp256r1.C.n) ∧
      Ecdh.Valid brainpoolp256r1.C (s₀.mem (s₀.gpr .x2)) (sv brainpoolp256r1 (s₀.gpr .x3) s₃ E) (sv brainpoolp256r1 (s₀.gpr .x3) s₃ QY) ∧
      tmv brainpoolp256r1.C brainpoolp256r1.n (s₀.gpr .x3) s₅ (brainpoolp256r1.sl RZ) ≠ 0
  · have hok : ok brainpoolp256r1 (s₀.gpr .x3) s₅ (PeerOk brainpoolp256r1 (s₀.gpr .x3) s₃ ((s₀.mem (s₀.gpr .x2) = 4 ∧
        sv brainpoolp256r1 (s₀.gpr .x3) s₃ E < brainpoolp256r1.C.p) ∧ sv brainpoolp256r1 (s₀.gpr .x3) s₃ QY < brainpoolp256r1.C.p)) = true := by
      refine decide_eq_true ⟨⟨⟨⟨⟨hcond.2.1.1, hcond.2.1.2.1⟩, hcond.2.1.2.2.1⟩, hcond.2.1.2.2.2⟩, ?_, ?_⟩,
        hz.mp hcond.2.2⟩
      · rw [hD₅]; exact hcond.1.1
      · rw [hD₅]; exact hcond.1.2
    rw [ite_eq_left hcond]
    exact ⟨by rw [ret, hok]; rfl, by rw [bytes, hok]; rfl⟩
  · have hok : ok brainpoolp256r1 (s₀.gpr .x3) s₅ (PeerOk brainpoolp256r1 (s₀.gpr .x3) s₃ ((s₀.mem (s₀.gpr .x2) = 4 ∧
        sv brainpoolp256r1 (s₀.gpr .x3) s₃ E < brainpoolp256r1.C.p) ∧ sv brainpoolp256r1 (s₀.gpr .x3) s₃ QY < brainpoolp256r1.C.p)) = false := by
      refine decide_eq_false fun h => hcond ⟨⟨?_, ?_⟩, ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2⟩,
        hz.mpr h.2⟩
      · rw [← hD₅]; exact h.1.2.1
      · rw [← hD₅]; exact h.1.2.2
    rw [ite_eq_right hcond]
    exact ⟨by rw [ret, hok]; rfl, by rw [bytes, hok]; rfl⟩

end VG.Proof.Ecdh.AArch64.BrainpoolP256r1
