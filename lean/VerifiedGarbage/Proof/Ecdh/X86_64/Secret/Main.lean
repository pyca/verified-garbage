import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Mul
import VerifiedGarbage.Proof.Ecdh.X86_64.Main

/-! The secret Jacobian ECDH implementation computes the shared-secret specification and restores the ABI. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Proof.X25519.X86_64 (Keeps)
open VG.Impl.Ecdh.X86_64 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)

theorem exchange_ok {c : Cfg} (hc : CfgOk c) (hCurve : c.C=Spec.P256.curve)
    (hL : SecretLay (Impl.Ecdh.X86_64.Window5.cfg c) size) (hC : Law c.C) (hO : PeerOrder c.C)
    {s₀ : State} (hp : EPre c s₀) :
    WP isa (Impl.Ecdh.X86_64.Window5.exchange c) s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ EPost c s₀ s' := by
  have h0 := hc.n0
  have h7 := hc.n10
  have := hc.len8; have := hc.len_lo; have := hc.len_hi
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  rw [Impl.Ecdh.X86_64.Window5.exchange]
  have hn4 : c.n=4 := hL.n
  refine WP.seq (WP.mono (args_ok s₀) fun s₁ ⟨r8₁, r9₁, rcx₁, rdx₁, k₁⟩ => ?_)
  have rsi₁ : s₁.gpr .rsi = s₀.gpr .rsi := k₁.1 _ (by decide)
  have rdi₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.1 _ (by decide)
  have hrd₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [k₁.2.2.1, k₁.2.2.2]
  have hsp : SetupPre c s₁ := by
    refine ⟨by rw [k₁.2.2.2, hp.wr, r8₁]; simp, fun e he => ?_, fun e he => ?_, fun e he => ?_, ?_, ?_, ?_,
      by rw [r8₁]; exact hp.sc_fit⟩
    · rw [rcx₁, hrd₁, hp.rd]
      exact ⟨_, by simp, Offset.contains_base _ he (by have := hp.out_fit; omega)⟩
    · rw [rsi₁, hrd₁, hp.rd]
      exact ⟨_, by simp, Offset.contains_base _ he (by have := hp.out_fit; omega)⟩
    · rw [rdx₁, hrd₁, hp.rd, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact ⟨⟨s₀.gpr .rdx, 1 + 2 * c.C.len⟩, by simp,
        Offset.contains_base _ (by omega) (by have := hp.out_fit; omega)⟩
    · rw [rsi₁, r8₁]; exact hp.d_sc
    · rw [rdx₁, r8₁]; exact hp.peer_sc.sub_left (Offset.sub_base _ (by omega))
    · rw [rcx₁, r8₁]; exact hp.d_sc
  refine WP.seq (WP.mono (stage₁ hc (hs := none) (Or.inl rfl) hsp (rest := .block [])
    (Q := St₁ c none s₁ (s₁.gpr .r8))
    fun _ S => WP.block_nil S) fun s₂ S₂ => ?_)
  rw [r8₁] at S₂
  have hn := S₂.scr.nowrap
  have hq₂ : s₂.gpr .r9 = s₀.gpr .rdx := by rw [S₂.gpr _ (by decide), r9₁]
  have hrw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [S₂.rd, S₂.wr, hrd₁]
  -- The peer's key.
  refine WP.seq (WP.mono (peer_ok hc S₂.scr hq₂ (by rw [hrw₂, hp.rd]; simp) hp.peer_sc S₂.fixed.mp)
    fun s₃ ⟨hs₃, k₃, U₃, r2₃, bp₃, y₃, f₃⟩ => ?_)
  have F₃ := S₂.fixed.unch h7 hn ((fixedOk_slW (l := [R2P, BP, QY]) (by decide)).append fixedOk_flag) U₃
  have e₃ : ∀ {i}, i < 45 → i ∉ [R2P, BP, QY] → i ≠ FLAG →
      sv c (s₀.gpr .rcx) s₃ i = sv c (s₀.gpr .rcx) s₂ i := fun hi hl hf =>
    sv_unch U₃ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have x₃ : sv c (s₀.gpr .rcx) s₃ E = sv c (s₀.gpr .rcx) s₂ E := e₃ (by decide) (by decide) (by decide)
  -- The peer's key has not changed.
  have W₂ : Outside (s₀.gpr .rcx) 0 size s₀.mem s₂.mem := fun x hx =>
    (S₂.unch x fun w hw => by rw [List.mem_singleton.mp hw]; exact hx).trans (congrFun k₁.2.1 x)
  have hq0 : s₂.mem (s₀.gpr .rdx) = s₀.mem (s₀.gpr .rdx) := by
    have := keep_of_disjoint' W₂ hp.peer_sc (by omega) (i := 0) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  -- What the code checks of the peer's key so far.
  have hf₃ : word s₃.mem (s₀.gpr .rcx) (c.sl FLAG) = mask (((s₀.mem (s₀.gpr .rdx) = 4 ∧
      sv c (s₀.gpr .rcx) s₃ E < c.C.p) ∧ sv c (s₀.gpr .rcx) s₃ QY < c.C.p)) := by
    rw [f₃, S₂.flag, BitVec.allOnes_and, mask_and, mask_and, x₃, hq0]
  refine WP.seq (WP.mono (validate_ok hc hs₃ F₃ r2₃ bp₃ hf₃)
    fun s₄ ⟨hs₄, g₄, rd₄, wr₄, U₄, f₄, px_lt, py_lt, px, py⟩ => ?_)
  have F₄ := F₃.unch h7 hn ((fixedOk_slW (l := [QXM, QYM, TMP, W0, W1, W2, W3, PY]) (by decide)).append
    fixedOk_flag) U₄
  have e₄ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY] → i ≠ FLAG →
      sv c (s₀.gpr .rcx) s₄ i = sv c (s₀.gpr .rcx) s₃ i := fun hi hl hf =>
    sv_unch U₄ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have t₄ : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
      s₄.mem (off (s₀.gpr .rcx) (bitsAt c.n j + t)) = s₂.mem (off (s₀.gpr .rcx) (bitsAt c.n j + t)) :=
    fun hj t ht => by
      rw [tbl_unch U₄ h7 hn hj ht (apart_append (tbl_apart_slW (by decide) _ t) (tbl_apart_flag h0 _ t)),
        tbl_unch U₃ h7 hn hj ht (apart_append (tbl_apart_slW (by decide) _ t) (tbl_apart_flag h0 _ t))]
  have H := mulPow_ok hc hCurve hL hC hO hs₄ F₄
    (by rw [e₄ (by decide) (by decide) (by decide)]; exact bp₃)
    (peerPt_onCurve hc _ _ _) px_lt py_lt
    (peerPt_rep hC _ _ _ px py |> fun h => by
      show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .rcx) s₄ PX))
        (toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .rcx) s₄ PY))
        (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₄.mem (s₀.gpr .rcx) (c.sl ONEP) c.n)) _
      rw [F₄.onep, toM_one hpR]; exact h)
    (fun t ht => by rw [t₄ (j := 1) (by decide) t ht, S₂.t₁ t ht])
  apply WP.seq
  rw [WP.seq_iff] at H
  refine WP.mono H fun a Ha => ?_
  apply WP.seq
  rw [WP.seq_iff] at Ha
  refine WP.mono Ha fun b Hb => ?_
  apply WP.seq
  refine WP.mono Hb fun s₅ L => ?_
  have hs₅ := L.scr
  have F₅ := F₄.unch h7 hn (fixedOk_mulW hn4) L.unch
  have e₅ : sv c (s₀.gpr .rcx) s₅ D=sv c (s₀.gpr .rcx) s₄ D :=
    sv_unch L.unch h7 hn (by decide) (apart_mulW hn4 (by decide))
  have hflag₅ := f₄
  have hF := sl_le c h7 (i := FLAG) (by decide)
  rw [← L.unch.word (fun w hw => by
    rcases apart_mulW (c := c) (i := FLAG) hn4 (by decide) w hw with h | h
    · exact Or.inl (by omega)
    · exact Or.inr h) (by omega)] at hflag₅
  have hrsi₅ : s₅.gpr .rsi = s₀.gpr .rdi := by
    rw [L.keep.gpr _ (rsi_not_invClob _), g₄ _ (rsi_not_clob _), k₃.gpr _ (by decide), S₂.rsi, rdi₁]
  have hw₅ : (⟨s₀.gpr .rdi, c.C.len⟩ : Region) ∈ s₅.wr := by
    rw [L.keep.wr, wr₄, k₃.wr, S₂.wr, k₁.2.2.2, hp.wr]; simp
  refine WP.mono (middle_ok hc hs₅ F₅ L.acc_lt hflag₅ hrsi₅ hw₅ hp.out_sc hp.out_fit)
    fun s' ⟨xv, hxl, hxv, bytes, rax, saved⟩ => ⟨fun r hr => ?_, ?_⟩
  · have hsv : ∀ r ∈ Cfg.saved.map Prod.fst, r ∉ [Reg.r8, .r9, .rcx, .rdx] := by decide
    rw [saved r hr, k₁.1 r (hsv r hr)]
  -- The specification.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) (1 + 2 * c.C.len)).head? = some (s₀.mem (s₀.gpr .rdx)) := by
    rw [peer_bytes]; rfl
  have hxs : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      sv c (s₀.gpr .rcx) s₃ E := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _), x₃, S₂.e]
    simp only [k₁.2.1, rdx₁, shAt_none, Nat.shiftRight_zero]
  have hys : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      sv c (s₀.gpr .rcx) s₃ QY := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _), y₃,
      bytesAt_keep W₂ (hp.peer_sc.sub_left (Offset.sub_base _ (by omega))) (by omega) (by omega)]
  have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (s₀.gpr .rdx)) (sv c (s₀.gpr .rcx) s₃ E) (sv c (s₀.gpr .rcx) s₃ QY),
      peerPt c (s₀.mem (s₀.gpr .rdx) = 4) (sv c (s₀.gpr .rcx) s₃ E) (sv c (s₀.gpr .rcx) s₃ QY) =
        .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have hk : sv c (s₀.gpr .rcx) s₂ K = dk c s₀ := by rw [S₂.k]; simp only [kv, dk, k₁.2.1, rcx₁]
  have hk₄ : sv c (s₀.gpr .rcx) s₄ K=dk c s₀ := by
    rw [e₄ (by decide) (by decide) (by decide),e₃ (by decide) (by decide) (by decide),hk]
  have hR := L.point
  rw [hk₄] at hR
  have hxoX : Fin.ofNat c.C.p xv = tmv c.C c.n (s₀.gpr .rcx) s₅ (c.sl RX) *
      tmv c.C c.n (s₀.gpr .rcx) s₅ (c.sl RZ) ^ (c.C.p - 2) := by rw [hxv, L.acc]
  have hspec := exchange_xOnly hlen hb0 hxs hys hP' hR hxl hxoX
  have hD₅ : sv c (s₀.gpr .rcx) s₅ D = dk c s₀ := by
    rw [e₅, e₄ (by decide) (by decide) (by decide),
      e₃ (by decide) (by decide) (by decide), S₂.d, shAt_none, Nat.shiftRight_zero]
    simp only [dv, dk, k₁.2.1, rsi₁]
  have hz : tmv c.C c.n (s₀.gpr .rcx) s₅ (c.sl RZ) ≠ 0 ↔ sv c (s₀.gpr .rcx) s₅ RZ ≠ 0 :=
    not_congr (toM_eq_zero_iff hpR L.rz_lt)
  unfold EPost
  rw [hspec]
  by_cases hcond : (1 ≤ dk c s₀ ∧ dk c s₀ < c.C.n) ∧
      Ecdh.Valid c.C (s₀.mem (s₀.gpr .rdx)) (sv c (s₀.gpr .rcx) s₃ E) (sv c (s₀.gpr .rcx) s₃ QY) ∧
      tmv c.C c.n (s₀.gpr .rcx) s₅ (c.sl RZ) ≠ 0
  · have hok : ok c (s₀.gpr .rcx) s₅ (PeerOk c (s₀.gpr .rcx) s₃ ((s₀.mem (s₀.gpr .rdx) = 4 ∧
        sv c (s₀.gpr .rcx) s₃ E < c.C.p) ∧ sv c (s₀.gpr .rcx) s₃ QY < c.C.p)) = true := by
      refine decide_eq_true ⟨⟨⟨⟨⟨hcond.2.1.1, hcond.2.1.2.1⟩, hcond.2.1.2.2.1⟩, hcond.2.1.2.2.2⟩, ?_, ?_⟩,
        hz.mp hcond.2.2⟩
      · rw [hD₅]; exact hcond.1.1
      · rw [hD₅]; exact hcond.1.2
    rw [ite_eq_left hcond]
    exact ⟨by rw [rax, hok]; rfl, by rw [bytes, hok]; rfl⟩
  · have hok : ok c (s₀.gpr .rcx) s₅ (PeerOk c (s₀.gpr .rcx) s₃ ((s₀.mem (s₀.gpr .rdx) = 4 ∧
        sv c (s₀.gpr .rcx) s₃ E < c.C.p) ∧ sv c (s₀.gpr .rcx) s₃ QY < c.C.p)) = false := by
      refine decide_eq_false fun h => hcond ⟨⟨?_, ?_⟩, ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2⟩,
        hz.mpr h.2⟩
      · rw [← hD₅]; exact h.1.2.1
      · rw [← hD₅]; exact h.1.2.2
    rw [ite_eq_right hcond]
    exact ⟨by rw [rax, hok]; rfl, by rw [bytes, hok]; rfl⟩


end VG.Proof.Ecdh.X86_64.Secret
