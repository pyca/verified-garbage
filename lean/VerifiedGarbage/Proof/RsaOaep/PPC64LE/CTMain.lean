module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTMgf
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTLabel
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Correct
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Em
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry

/-!
# RSAES-OAEP encryption on PPC64LE: constant time

Untrusted: everything here is checked by Lean. Two runs from entry states
with the anchor's public data leak alike: the code between the calls by the
taint analysis (`CTBlocks`), the hash functions' calls by their contracts
(`CTCalls`), MGF1's loops on counters both runs agree on (`mgfXor_ct`), the
call of `vg_rsa_public_precomputed_checked` by its contract (`pdCallCT`),
and the branches on the public lengths (`two_ite`); what each run satisfies
between them follows from correctness.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo Two Pins two_post two_ite two_alloc wp_li wp_addi wp_subi wp_mov
  wp_nil eval_nonzero pdCallCT)

/-- Two calls of `vg_rsa_public_precomputed_checked` from `AtCall`, for
entry states with the anchor's public data, agree on what the callee may
leak. -/
theorem call_ct {D : Nat} :
    RelCT isa (Two fun a t => ∃ s, PreO D s ∧ PubO a s ∧ ∃ EM, AtCall s EM t) Impl.RsaPkcs1Sig.PPC64LE.pubCall
      fun _ _ => True := by
  refine pdCallCT fun t₁ t₂ ⟨a, ⟨s₁, P₁, p₁, EM₁, c₁⟩, ⟨s₂, P₂, p₂, EM₂, c₂⟩⟩ => ⟨pdOk_of P₁ c₁,
    pdOk_of P₂ c₂, ⟨?_, fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [c₁.sv.sp, c₂.sv.sp, fb, fb, p₁.sp, p₂.sp]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.g3, c₂.g3, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [c₁.g4, c₂.g4, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [c₁.g5, c₂.g5, p₁.args 5 (by decide), p₂.args 5 (by decide)]
    · rw [c₁.g6, c₂.g6, p₁.args 6 (by decide), p₂.args 6 (by decide)]
    · rw [c₁.g7, c₂.g7, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [c₁.g8, c₂.g8, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [c₁.g9, c₂.g9, p₁.S, p₂.S]
    · rw [c₁.g10, c₂.g10, p₁.g _ (by decide), p₂.g _ (by decide)]
  · rw [c₁.a0, c₂.a0, p₁.S, p₂.S]
  · rw [c₁.a1, c₂.a1, p₁.args 4 (by decide), p₂.args 4 (by decide)]
  · rw [c₁.g5, c₂.g5, c₁.g6, c₂.g6, words_entry c₁.mem P₁.kp ((P₁.sp).sub_left (sc_sub P₁)) P₁.wp,
      words_entry c₂.mem P₂.kp ((P₂.sp).sub_left (sc_sub P₂)) P₂.wp, p₁.w, p₂.w]
  · rw [c₁.g7, c₂.g7, c₁.g8, c₂.g8,
      bytes_entry c₁.mem P₁.ke ((P₁.es.symm).sub_left (sc_sub P₁)) (by have := P₁.we; omega),
      bytes_entry c₂.mem P₂.ke ((P₂.es.symm).sub_left (sc_sub P₂)) (by have := P₂.we; omega), p₁.e, p₂.e]

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (hG : HashOK G) (cG : HashCT hG) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)

include cG hGh hGl hGv in
/-- `mgfXor`, with its lengths and offsets the anchor's. -/
theorem mgf_any (q : State → Nat × Nat × Nat × Nat) :
    RelCT isa (Two fun a t => MgfA S vO (PreO H.D) PubO (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2 a t ∧
      MFit (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2) (mgfXor G) fun _ _ => True :=
  (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfA S vO (PreO H.D) PubO x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXor_ct (oaepOk H.D) hG cG x.2 hGh hGl hGv).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨q a, h₁.2⟩, a, h₁.1, h₂.1⟩) fun _ _ h => h

/-- The checks passed, in terms of the anchor. -/
abbrev HK (D : Nat) (a : State) : Prop := 2 * D + 2 + (stackArg a 1).toNat ≤ (a.gpr .r6).toNat

theorem hk_of {D : Nat} {a s : State} (p : PubO a s) (h : HK D a) : 2 * D + 2 + mLen s ≤ kk s := by
  simp only [mLen, kk, p.args 1 (by decide), p.g .r6 (by decide)]; exact h

/-- `B` with the checks passed. -/
def Bk (D : Nat) (a t : State) : Prop := BO D a t ∧ HK D a

theorem bk_pins {D : Nat} {α : Type} {Φ : α → State → Prop} (A : α → State) (h : ∀ x t, Φ x t → BO D (A x) t) :
    Pins Φ [] := fun x t₁ t₂ h₁ h₂ => ⟨((h x t₁ h₁).sp (oaepOk D)).trans ((h x t₂ h₂).sp (oaepOk D)).symm, fun _ h => nomatch h⟩

include cH cG hGh hGl hGv in
theorem encMain_ct : RelCT isa (Two fun a t => ∃ s, PreO H.D s ∧ PubO a s ∧ Entered s t ∧ HK H.D a)
    (encMain H G) fun _ _ => True := by
  have F := hfits hH
  obtain ⟨hE, _, _, _, _, _⟩ := offs
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  -- `EM` before masking.
  refine two_seq (Ψ := Bk H.D) (encEm_taint H fun a t₁ t₂ ⟨s₁, _, p₁, E₁, _⟩ ⟨s₂, _, p₂, E₂, _⟩ => ?_)
    (fun a t ⟨s, P, p, E, hk⟩ => WP.mono (encEm_ok P rfl hD0 hD64 E (hk_of p hk)) fun t' ⟨b, _⟩ =>
      ⟨⟨s, P, p, b⟩, hk⟩) ?_
  · have f₁ := E₁.base.agree ((oaepOk H.D).agree p₁)
    have f₂ := E₂.base.agree ((oaepOk H.D).agree p₂)
    refine ⟨f₁.1.trans f₂.1.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [E₁.r9, E₂.r9, p₁.args 0 (by decide), p₂.args 0 (by decide)]
    · rw [E₁.r10, E₂.r10, p₁.args 1 (by decide), p₂.args 1 (by decide)]
    · rw [E₁.r11, E₂.r11, p₁.args 2 (by decide), p₂.args 2 (by decide)]
    · exact f₁.2.1.trans f₂.2.1.symm
    · exact (f₁.2.2 _ (by decide)).trans (f₂.2.2 _ (by decide)).symm
  -- The label's hash, and `lHash`.
  refine two_seq (Ψ := Bk H.D) ((hashLabel_ct hH cH).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨s, P, p, b⟩, hk⟩ => WP.mono (hashLabel_ok P hH b) fun t' ⟨b', _⟩ =>
      ⟨⟨s, P, p, b'⟩, hk⟩) ?_
  refine two_seq (Ψ := Bk H.D) (copyLh_taint H (pins_of (oaepOk H.D) (fun _ _ h => h.1) [.r14]))
    (fun a t ⟨⟨s, P, p, b⟩, hk⟩ => WP.mono (copyLh_ok P hH rfl b) fun t' ⟨b', _⟩ => ⟨⟨s, P, p, b'⟩, hk⟩) ?_
  -- `DB` with MGF1 of the seed.
  let q₁ : State → Nat × Nat × Nat × Nat := fun a => (1, H.D, 1 + H.D, (a.gpr .r6).toNat - H.D - 1)
  refine two_seq (Ψ := fun a t => (MgfA S vO (PreO H.D) PubO (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2 a t ∧
      MFit (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2) ∧ HK H.D a)
    (dbArgs_taint H (bk_pins id fun _ _ h => h.1)) (fun a t ⟨⟨s, P, p, b⟩, hk⟩ => ?_) ?_
  · have k2 := P.k2
    have ek : (a.gpr .r6).toNat = (s.gpr .r6).toNat := by rw [p.g .r6 (by decide)]
    refine wp_addi (h := by omega) fun t₁ o₁ e₁ => wp_li (by omega) fun t₂ o₂ e₂ =>
      wp_addi (h := by omega) fun t₃ o₃ e₃ => wp_subi (h := by omega) fun t₄ o₄ e₄ => wp_nil ?_
    have k₄ : Only [.r24, .r25, .r26, .r27] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    show (MgfA S vO (PreO H.D) PubO 1 H.D (1 + H.D) ((a.gpr .r6).toNat - H.D - 1) a t₄ ∧
      MFit 1 H.D (1 + H.D) ((a.gpr .r6).toNat - H.D - 1)) ∧ HK H.D a
    refine ⟨⟨⟨s, P, p, b.only P.fits k₄, ?_, ?_, ?_, ?_⟩, ⟨by omega, by omega, .inl (by omega), by omega⟩⟩, hk⟩
    · rw [o₄.get .r24, o₃.get .r24, o₂.get .r24, e₁, b.r14, p.S, hE]
    · rw [o₄.get .r25, o₃.get .r25, e₂]
    · rw [o₄.get .r26, e₃, o₂.get .r14, o₁.get .r14, b.r14, p.S, hE, Nat.zero_add]
    · rw [e₄, o₃.get .r15, o₂.get .r15, o₁.get .r15, b.r15, sub_k (by omega)]; congr 1; omega
  refine two_seq (Ψ := Bk H.D) ((mgf_any hG cG hGh hGl hGv q₁).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨⟨s, P, p, b, h24, h25, h26, h27⟩, hf⟩, hk⟩ =>
    WP.mono (mgfXor_ok P.fits hG hGh hGl hGv hf b (by rw [h24, p.S]) h25 (by rw [h26, p.S]) h27)
      fun t' ⟨b', _⟩ => ⟨⟨s, P, p, b'⟩, hk⟩) ?_
  -- The seed with MGF1 of `maskedDB`.
  let q₂ : State → Nat × Nat × Nat × Nat := fun a => (1 + H.D, (a.gpr .r6).toNat - H.D - 1, 1, H.D)
  refine two_seq (Ψ := fun a t => (MgfA S vO (PreO H.D) PubO (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2 a t ∧
      MFit (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2) ∧ HK H.D a)
    (seedArgs_taint H (bk_pins id fun _ _ h => h.1)) (fun a t ⟨⟨s, P, p, b⟩, hk⟩ => ?_) ?_
  · have k2 := P.k2
    have ek : (a.gpr .r6).toNat = (s.gpr .r6).toNat := by rw [p.g .r6 (by decide)]
    refine wp_addi (h := by omega) fun t₁ o₁ e₁ => wp_subi (h := by omega) fun t₂ o₂ e₂ =>
      wp_addi (h := by omega) fun t₃ o₃ e₃ => wp_li (by omega) fun t₄ o₄ e₄ => wp_nil ?_
    have k₄ : Only [.r24, .r25, .r26, .r27] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    show (MgfA S vO (PreO H.D) PubO (1 + H.D) ((a.gpr .r6).toNat - H.D - 1) 1 H.D a t₄ ∧
      MFit (1 + H.D) ((a.gpr .r6).toNat - H.D - 1) 1 H.D) ∧ HK H.D a
    refine ⟨⟨⟨s, P, p, b.only P.fits k₄, ?_, ?_, ?_, ?_⟩, ⟨by omega, by omega, .inr (by omega), by omega⟩⟩, hk⟩
    · rw [o₄.get .r24, o₃.get .r24, o₂.get .r24, e₁, b.r14, p.S, hE, Nat.zero_add]
    · rw [o₄.get .r25, o₃.get .r25, e₂, o₁.get .r15, b.r15, sub_k (by omega)]; congr 1; omega
    · rw [o₄.get .r26, e₃, o₂.get .r14, o₁.get .r14, b.r14, p.S, hE]
    · rw [e₄]
  refine two_seq (Ψ := Bk H.D) ((mgf_any hG cG hGh hGl hGv q₂).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨⟨s, P, p, b, h24, h25, h26, h27⟩, hf⟩, hk⟩ =>
    WP.mono (mgfXor_ok P.fits hG hGh hGl hGv hf b (by rw [h24, p.S]) h25 (by rw [h26, p.S]) h27)
      fun t' ⟨b', _⟩ => ⟨⟨s, P, p, b'⟩, hk⟩) ?_
  -- The public-key operation.
  exact two_seq (pubArgs_taint (bk_pins id fun _ _ h => h.1)) (fun a t ⟨⟨s, P, p, b⟩, _⟩ =>
    WP.mono (pubArgs_ok P b rfl) fun t' h => ⟨s, P, p, _, h⟩) call_ct

theorem entered_only {s t t' : State} {rs : List Reg} {D : Nat} (P : PreO D s) (E : Entered s t)
    (o : Only rs t t') (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs ++ ([.r9, .r10, .r11] : List Reg) := by decide) : Entered s t' := by
  have g : ∀ r ∈ [Reg.r9, .r10, .r11], t'.gpr r = t.gpr r := fun r hr =>
    o.gpr r fun h => hrs r h (List.mem_append_right _ hr)
  exact ⟨E.base.only P.fits o fun r h h' => hrs r h (List.mem_append_left _ h'), (g _ (by decide)).trans E.r9,
    (g _ (by decide)).trans E.r10, (g _ (by decide)).trans E.r11⟩

include cH cG hGh hGl hGv in
theorem checks_ct : RelCT isa (Two fun a t => ∃ s, PreO H.D s ∧ PubO a s ∧ Entered s t) (checks H G)
    fun _ _ => True := by
  have hD64 := hH.hD64
  let K := fun (a : State) => (a.gpr .r6).toNat
  refine two_seq (Ψ := fun a t => ∃ s, PreO H.D s ∧ PubO a s ∧ Entered s t ∧
      (t.gpr .r3 != 0) = decide (K a < 2 * H.D + 2))
    (chkK_taint H (bk_pins id fun _ _ ⟨s, P, p, E⟩ => ⟨s, P, p, E.base⟩)) (fun a t ⟨s, P, p, E⟩ => ?_) ?_
  · have k2 := P.k2
    have ka : (a.gpr .r6).toNat ≤ 1024 := by rw [← p.g .r6 (by decide)]; exact P.k2
    refine wp_li (by omega) fun t₁ o₁ e₁ => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_sub fun t₂ o₂ e₂ =>
      VG.Proof.RsaPkcs1Sig.PPC64LE.wp_lsr fun t₃ o₃ e₃ => wp_nil ?_
    have k₃ : Only [.r3] t t₃ := (o₁.trans (o₂.trans o₃)).mono
    refine ⟨s, P, p, entered_only P E k₃, ?_⟩
    rw [e₃, e₂, e₁, o₁.get .r15, E.base.r15, ← ofNat_toNat (s.gpr .r6), p.g .r6 (by decide)]
    exact ne_zero_ltBit (by omega) (by omega)
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, c₁⟩ ⟨_, _, _, _, c₂⟩ => by rw [eval_nonzero, eval_nonzero, c₁, c₂])
    (fail_taint (pins_of (oaepOk H.D) (fun _ _ ⟨⟨s, P, p, E, _⟩, _⟩ => ⟨s, P, p, E.base⟩) [.r15, .r16])) ?_
  refine two_seq (Ψ := fun a t => ∃ s, PreO H.D s ∧ PubO a s ∧ Entered s t ∧ 2 * H.D + 2 ≤ K a ∧
      (t.gpr .r3 != 0) = decide (K a - (2 * H.D + 2) < (stackArg a 1).toNat))
    (chkMsg_taint H (bk_pins id fun _ _ ⟨⟨s, P, p, E, _⟩, _⟩ => ⟨s, P, p, E.base⟩))
    (fun a t ⟨⟨s, P, p, E, c⟩, hc⟩ => ?_) ?_
  · have k2 := P.k2
    have hk : 2 * H.D + 2 ≤ K a := by rw [eval_nonzero, c] at hc; simpa using hc
    have ek : K a = (s.gpr .r6).toNat := by simp only [K]; rw [p.g .r6 (by decide)]
    refine wp_li (by omega) fun t₄ o₄ e₄ => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_sub fun t₅ o₅ e₅ =>
      VG.Proof.RsaPkcs1Sig.PPC64LE.wp_sub fun t₆ o₆ e₆ => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_lsr fun t₇ o₇ e₇ =>
      VG.Proof.RsaPkcs1Sig.PPC64LE.wp_lsr fun t₈ o₈ e₈ => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_or fun t₉ o₉ e₉ =>
      wp_nil ?_
    have k₉ : Only [.r3, .r4] t t₉ := (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans o₉))))).mono
    refine ⟨s, P, p, entered_only P E k₉, hk, ?_⟩
    rw [e₉, e₈, o₇.get .r10, o₆.get .r10, o₅.get .r10, o₄.get .r10, E.r10, o₈.get .r4, e₇, e₆,
      o₅.get .r10, o₄.get .r10, E.r10, e₅, o₄.get .r15, E.base.r15, e₄,
      ← ofNat_toNat (s.gpr .r6), ← ofNat_toNat (stackArg s 1), Offset.ofNat_sub_ofNat (by omega),
      p.args 1 (by decide), ← ek]
    exact msgBit (by omega) (stackArg a 1).isLt
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, _, c₁⟩ ⟨_, _, _, _, _, c₂⟩ => by
      rw [eval_nonzero, eval_nonzero, c₁, c₂])
    (fail_taint (pins_of (oaepOk H.D) (fun _ _ ⟨⟨s, P, p, E, _⟩, _⟩ => ⟨s, P, p, E.base⟩) [.r15, .r16])) ?_
  refine (encMain_ct hH cH hG cG hGh hGl hGv).mono (fun _ _ h => ?_) fun _ _ h => h
  obtain ⟨a, ⟨⟨s₁, P₁, p₁, E₁, hk, c₁⟩, h₁⟩, ⟨⟨s₂, P₂, p₂, E₂, -, -⟩, -⟩⟩ := h
  rw [eval_nonzero, c₁] at h₁
  have : ¬ (K a - (2 * H.D + 2) < (stackArg a 1).toNat) := by simpa using h₁
  have hK : HK H.D a := by simp only [HK, K] at *; omega
  exact ⟨a, ⟨s₁, P₁, p₁, E₁, hK⟩, ⟨s₂, P₂, p₂, E₂, hK⟩⟩

variable {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D)

include cH cG hGh hGl hGv hHh hHl in
theorem code_ct : RelCT isa (Two fun a s => PreO H.D s ∧ PubO a s) (encrypt H G) fun _ _ => True := by
  refine two_alloc (R := fun _ _ => True) (fun a s₁ s₂ h₁ h₂ =>
    ⟨h₁.2.sp.trans h₂.2.sp.symm, fun _ h => nomatch h⟩) ?_
  refine two_seq (Ψ := fun a t => ∃ s, PreO H.D s ∧ PubO a s ∧ Entered s t)
    (entry_taint fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂, allocated_sp, allocated_sp, h₁.2.sp,
      h₂.2.sp], fun _ h => nomatch h⟩)
    (fun a u ⟨s, ⟨P, p⟩, e⟩ => by subst e; exact WP.mono (entry_ok P) fun t E => ⟨s, P, p, E⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, PreO H.D s ∧ PubO a s ∧ Saves s t)
    (checks_ct hH cH hG cG hGh hGl hGv) fun a t ⟨s, P, p, E⟩ =>
      WP.mono (checks_done hH hG hHh hHl hGh hGl hGv P E) fun t' d => ⟨s, P, p, d.1⟩) ?_
  exact restore_taint fun a t₁ t₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
    ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.sp, p₂.sp], fun _ h => nomatch h⟩

end

end VG.Proof.RsaOaep.PPC64LE
