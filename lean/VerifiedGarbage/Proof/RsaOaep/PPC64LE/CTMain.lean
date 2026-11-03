module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTMgfT
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTLabel
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Correct
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Em
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry

/-!
# RSAES-OAEP encryption on PPC64LE: constant time

Untrusted: everything here is checked by Lean. Two runs from entry states
with the anchor's public data leak alike: the code between the calls by the
taint analysis (`CTBlocks`), the hash functions' calls by their contracts
(`CTCalls`), MGF1's loops on counters both runs agree on, with the table at
the same address and its functions at the same addresses (`mgfXorT_ct`), the
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
      bytes_entry c₁.mem P₁.ke ((P₁.es.symm).sub_left (sc_sub P₁)) (by have := P₁.we; omega_arith),
      bytes_entry c₂.mem P₂.ke ((P₂.es.symm).sub_left (sc_sub P₂)) (by have := P₂.we; omega_arith), p₁.e, p₂.e]

/-- The precondition, with MGF1's table, `G`'s, on entry. -/
def PreT (D : Nat) (G : Hash) (f : Fns) (s : State) : Prop := PreO D s ∧ TabS G f 7 S s (stackArg s 7)

/-- The public data, with MGF1's table at the anchor's address and `G`'s
functions at the anchor's addresses. -/
def PubT (G : Hash) (a s : State) : Prop :=
  PubO a s ∧ stackArg s 7 = stackArg a 7 ∧ s.syms G.initN = a.syms G.initN ∧ s.syms G.updN = a.syms G.updN ∧
    s.syms G.finN = a.syms G.finN

theorem okT (D : Nat) (G : Hash) (f : Fns) : Ok S vO (PreT D G f) (PubT G) :=
  ⟨fun P => P.1.fits, fun p => (oaepOk D).agree p.1⟩

theorem tabT (D : Nat) (G : Hash) (f : Fns) : TabA G f 7 S (PreT D G f) (PubT G) :=
  ⟨fun P => P.2, fun p => p.2.1, fun p => p.2.2.1, fun p => p.2.2.2.1, fun p => p.2.2.2.2⟩

/-- `t` has `Base` from an entry state with `G`'s table and `a`'s public
data, and its addresses of statics. -/
abbrev BG (D : Nat) (G : Hash) (f : Fns) : State → State → Prop := BT S vO (PreT D G f) (PubT G)

theorem BG.bo {D : Nat} {G : Hash} {f : Fns} {a t : State} (h : BG D G f a t) : BO D a t :=
  let ⟨s, P, p, b, _⟩ := h; ⟨s, P.1, p.1, b⟩

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (hG : HashOK G) (cG : HashCT hG) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {f : Fns}

include cG hGh hGl hGv in
/-- `mgfXorT`, with its lengths and offsets the anchor's. -/
theorem mgf_any (q : State → Nat × Nat × Nat × Nat) :
    RelCT isa (Two fun a t => MgfAT S vO (PreT H.D G f) (PubT G) (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2 a t ∧
      MFit (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2) (mgfXorT f 7) fun _ _ => True :=
  (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfAT S vO (PreT H.D G f) (PubT G) x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXorT_ct (okT H.D G f) hG cG x.2 hGh hGl hGv (tabT H.D G f)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨q a, h₁.2⟩, a, h₁.1, h₂.1⟩) fun _ _ h => h

/-- The checks passed, in terms of the anchor. -/
abbrev HK (D : Nat) (a : State) : Prop := 2 * D + 2 + (stackArg a 1).toNat ≤ (a.gpr .r6).toNat

theorem hk_of {D : Nat} {a s : State} (p : PubO a s) (h : HK D a) : 2 * D + 2 + mLen s ≤ kk s := by
  simp only [mLen, kk, p.args 1 (by decide), p.g .r6 (by decide)]; exact h

/-- `BG` with the checks passed. -/
def Bk (D : Nat) (G : Hash) (f : Fns) (a t : State) : Prop := BG D G f a t ∧ HK D a

theorem bk_pins {D : Nat} {α : Type} {Φ : α → State → Prop} (A : α → State) (h : ∀ x t, Φ x t → BO D (A x) t) :
    Pins Φ [] := fun x t₁ t₂ h₁ h₂ => ⟨((h x t₁ h₁).sp (oaepOk D)).trans ((h x t₂ h₂).sp (oaepOk D)).symm, fun _ h => nomatch h⟩

include cH cG hGh hGl hGv in
theorem encMain_ct : RelCT isa (Two fun a t => ∃ s, PreT H.D G f s ∧ PubT G a s ∧ Entered s t ∧ t.syms = s.syms ∧
    HK H.D a) (encMain H f) fun _ _ => True := by
  have F := hfits hH
  obtain ⟨hE, _, _, _, _, _⟩ := offs
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  -- `EM` before masking.
  refine two_seq (Ψ := Bk H.D G f) (encEm_taint H fun a t₁ t₂ ⟨s₁, _, ⟨p₁, _⟩, E₁, _⟩ ⟨s₂, _, ⟨p₂, _⟩, E₂, _⟩ => ?_)
    (fun a t ⟨s, P, p, E, sy, hk⟩ => WP.mono_syms (encEm_ok P.1 rfl hD0 hD64 E (hk_of p.1 hk)) fun t' ⟨b, _⟩ y =>
      ⟨⟨s, P, p, b, y.trans sy⟩, hk⟩) ?_
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
  refine two_seq (Ψ := Bk H.D G f) ((hashLabel_ct hH cH).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1.bo, h₂.1.bo⟩)
    fun _ _ h => h) (fun a t ⟨⟨s, P, p, b, sy⟩, hk⟩ => WP.mono_syms (hashLabel_ok P.1 hH b) fun t' ⟨b', _⟩ y =>
      ⟨⟨s, P, p, b', y.trans sy⟩, hk⟩) ?_
  refine two_seq (Ψ := Bk H.D G f) (copyLh_taint H (pins_of (oaepOk H.D) (fun _ _ h => h.1.bo) [.r14]))
    (fun a t ⟨⟨s, P, p, b, sy⟩, hk⟩ => WP.mono_syms (copyLh_ok P.1 hH rfl b) fun t' ⟨b', _⟩ y =>
      ⟨⟨s, P, p, b', y.trans sy⟩, hk⟩) ?_
  -- `DB` with MGF1 of the seed.
  let q₁ : State → Nat × Nat × Nat × Nat := fun a => (1, H.D, 1 + H.D, (a.gpr .r6).toNat - H.D - 1)
  refine two_seq (Ψ := fun a t => (MgfAT S vO (PreT H.D G f) (PubT G) (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2 a t ∧
      MFit (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2) ∧ HK H.D a)
    (dbArgs_taint H (bk_pins id fun _ _ h => h.1.bo)) (fun a t ⟨⟨s, P, p, b, sy⟩, hk⟩ => ?_) ?_
  · have k2 := P.1.k2
    have ek : (a.gpr .r6).toNat = (s.gpr .r6).toNat := by rw [p.1.g .r6 (by decide)]
    refine WP.of_syms (wp_addi (h := by omega_arith) fun t₁ o₁ e₁ => wp_li (by omega_arith) fun t₂ o₂ e₂ =>
      wp_addi (h := by omega_arith) fun t₃ o₃ e₃ => wp_subi (h := by omega_arith) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
    have k₄ : Only [.r24, .r25, .r26, .r27] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    show (MgfAT S vO (PreT H.D G f) (PubT G) 1 H.D (1 + H.D) ((a.gpr .r6).toNat - H.D - 1) a t₄ ∧
      MFit 1 H.D (1 + H.D) ((a.gpr .r6).toNat - H.D - 1)) ∧ HK H.D a
    refine ⟨⟨⟨s, P, p, b.only P.1.fits k₄, y.trans sy, ?_, ?_, ?_, ?_⟩, ⟨by omega, by omega, .inl (by omega), by omega⟩⟩, hk⟩
    · rw [o₄.get .r24, o₃.get .r24, o₂.get .r24, e₁, b.r14, p.1.S, hE]
    · rw [o₄.get .r25, o₃.get .r25, e₂]
    · rw [o₄.get .r26, e₃, o₂.get .r14, o₁.get .r14, b.r14, p.1.S, hE, Nat.zero_add]
    · rw [e₄, o₃.get .r15, o₂.get .r15, o₁.get .r15, b.r15, sub_k (by omega)]; congr 1; omega
  refine two_seq (Ψ := Bk H.D G f) ((mgf_any hG cG hGh hGl hGv q₁).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨⟨s, P, p, b, sy, h24, h25, h26, h27⟩, hf⟩, hk⟩ =>
    WP.mono (mgfXorT_ok P.1.fits hG P.2 hGh hGl hGv hf b sy (by rw [h24, p.1.S]) h25 (by rw [h26, p.1.S]) h27)
      fun t' ⟨⟨b', _⟩, y⟩ => ⟨⟨s, P, p, b', y⟩, hk⟩) ?_
  -- The seed with MGF1 of `maskedDB`.
  let q₂ : State → Nat × Nat × Nat × Nat := fun a => (1 + H.D, (a.gpr .r6).toNat - H.D - 1, 1, H.D)
  refine two_seq (Ψ := fun a t => (MgfAT S vO (PreT H.D G f) (PubT G) (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2 a t ∧
      MFit (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2) ∧ HK H.D a)
    (seedArgs_taint H (bk_pins id fun _ _ h => h.1.bo)) (fun a t ⟨⟨s, P, p, b, sy⟩, hk⟩ => ?_) ?_
  · have k2 := P.1.k2
    have ek : (a.gpr .r6).toNat = (s.gpr .r6).toNat := by rw [p.1.g .r6 (by decide)]
    refine WP.of_syms (wp_addi (h := by omega_arith) fun t₁ o₁ e₁ => wp_subi (h := by omega_arith) fun t₂ o₂ e₂ =>
      wp_addi (h := by omega_arith) fun t₃ o₃ e₃ => wp_li (by omega_arith) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
    have k₄ : Only [.r24, .r25, .r26, .r27] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    show (MgfAT S vO (PreT H.D G f) (PubT G) (1 + H.D) ((a.gpr .r6).toNat - H.D - 1) 1 H.D a t₄ ∧
      MFit (1 + H.D) ((a.gpr .r6).toNat - H.D - 1) 1 H.D) ∧ HK H.D a
    refine ⟨⟨⟨s, P, p, b.only P.1.fits k₄, y.trans sy, ?_, ?_, ?_, ?_⟩, ⟨by omega_arith, by omega_arith, .inr (by omega_arith), by omega_arith⟩⟩, hk⟩
    · rw [o₄.get .r24, o₃.get .r24, o₂.get .r24, e₁, b.r14, p.1.S, hE, Nat.zero_add]
    · rw [o₄.get .r25, o₃.get .r25, e₂, o₁.get .r15, b.r15, sub_k (by omega)]; congr 1; omega
    · rw [o₄.get .r26, e₃, o₂.get .r14, o₁.get .r14, b.r14, p.1.S, hE]
    · rw [e₄]
  refine two_seq (Ψ := Bk H.D G f) ((mgf_any hG cG hGh hGl hGv q₂).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨⟨s, P, p, b, sy, h24, h25, h26, h27⟩, hf⟩, hk⟩ =>
    WP.mono (mgfXorT_ok P.1.fits hG P.2 hGh hGl hGv hf b sy (by rw [h24, p.1.S]) h25 (by rw [h26, p.1.S]) h27)
      fun t' ⟨⟨b', _⟩, y⟩ => ⟨⟨s, P, p, b', y⟩, hk⟩) ?_
  -- The public-key operation.
  exact two_seq (pubArgs_taint (bk_pins id fun _ _ h => h.1.bo)) (fun a t ⟨⟨s, P, p, b, _⟩, _⟩ =>
    WP.mono (pubArgs_ok P.1 b rfl) fun t' h => ⟨s, P.1, p.1, _, h⟩) call_ct

theorem entered_only {s t t' : State} {rs : List Reg} {D : Nat} (P : PreO D s) (E : Entered s t)
    (o : Only rs t t') (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs ++ ([.r9, .r10, .r11] : List Reg) := by decide) : Entered s t' := by
  have g : ∀ r ∈ [Reg.r9, .r10, .r11], t'.gpr r = t.gpr r := fun r hr =>
    o.gpr r fun h => hrs r h (List.mem_append_right _ hr)
  exact ⟨E.base.only P.fits o fun r h h' => hrs r h (List.mem_append_left _ h'), (g _ (by decide)).trans E.r9,
    (g _ (by decide)).trans E.r10, (g _ (by decide)).trans E.r11⟩

include cH cG hGh hGl hGv in
theorem checks_ct : RelCT isa (Two fun a t => ∃ s, PreT H.D G f s ∧ PubT G a s ∧ Entered s t ∧ t.syms = s.syms)
    (checks H f) fun _ _ => True := by
  have hD64 := hH.hD64
  let K := fun (a : State) => (a.gpr .r6).toNat
  refine two_seq (Ψ := fun a t => ∃ s, PreT H.D G f s ∧ PubT G a s ∧ Entered s t ∧ t.syms = s.syms ∧
      (t.gpr .r3 != 0) = decide (K a < 2 * H.D + 2))
    (chkK_taint H (bk_pins id fun _ _ ⟨s, P, p, E, _⟩ => ⟨s, P.1, p.1, E.base⟩)) (fun a t ⟨s, P, p, E, sy⟩ => ?_) ?_
  · have k2 := P.1.k2
    have ka : (a.gpr .r6).toNat ≤ 1024 := by rw [← p.1.g .r6 (by decide)]; exact P.1.k2
    refine WP.of_syms (wp_li (by omega_arith) fun t₁ o₁ e₁ => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_sub fun t₂ o₂ e₂ =>
      VG.Proof.RsaPkcs1Sig.PPC64LE.wp_lsr fun t₃ o₃ e₃ => wp_nil fun y => ?_)
    have k₃ : Only [.r3] t t₃ := (o₁.trans (o₂.trans o₃)).mono
    refine ⟨s, P, p, entered_only P.1 E k₃, y.trans sy, ?_⟩
    rw [e₃, e₂, e₁, o₁.get .r15, E.base.r15, ← ofNat_toNat (s.gpr .r6), p.1.g .r6 (by decide)]
    exact ne_zero_ltBit (by omega_arith) (by omega_arith)
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, _, c₁⟩ ⟨_, _, _, _, _, c₂⟩ => by rw [eval_nonzero, eval_nonzero, c₁, c₂])
    (fail_taint (pins_of (oaepOk H.D) (fun _ _ ⟨⟨s, P, p, E, _⟩, _⟩ => ⟨s, P.1, p.1, E.base⟩) [.r15, .r16])) ?_
  refine two_seq (Ψ := fun a t => ∃ s, PreT H.D G f s ∧ PubT G a s ∧ Entered s t ∧ t.syms = s.syms ∧
      2 * H.D + 2 ≤ K a ∧ (t.gpr .r3 != 0) = decide (K a - (2 * H.D + 2) < (stackArg a 1).toNat))
    (chkMsg_taint H (bk_pins id fun _ _ ⟨⟨s, P, p, E, _⟩, _⟩ => ⟨s, P.1, p.1, E.base⟩))
    (fun a t ⟨⟨s, P, p, E, sy, c⟩, hc⟩ => ?_) ?_
  · have k2 := P.1.k2
    have hk : 2 * H.D + 2 ≤ K a := by rw [eval_nonzero, c] at hc; simpa using hc
    have ek : K a = (s.gpr .r6).toNat := by simp only [K]; rw [p.1.g .r6 (by decide)]
    refine WP.of_syms (wp_li (by omega_arith) fun t₄ o₄ e₄ => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_sub fun t₅ o₅ e₅ =>
      VG.Proof.RsaPkcs1Sig.PPC64LE.wp_sub fun t₆ o₆ e₆ => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_lsr fun t₇ o₇ e₇ =>
      VG.Proof.RsaPkcs1Sig.PPC64LE.wp_lsr fun t₈ o₈ e₈ => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_or fun t₉ o₉ e₉ =>
      wp_nil fun y => ?_)
    have k₉ : Only [.r3, .r4] t t₉ := (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans o₉))))).mono
    refine ⟨s, P, p, entered_only P.1 E k₉, y.trans sy, hk, ?_⟩
    rw [e₉, e₈, o₇.get .r10, o₆.get .r10, o₅.get .r10, o₄.get .r10, E.r10, o₈.get .r4, e₇, e₆,
      o₅.get .r10, o₄.get .r10, E.r10, e₅, o₄.get .r15, E.base.r15, e₄,
      ← ofNat_toNat (s.gpr .r6), ← ofNat_toNat (stackArg s 1), Offset.ofNat_sub_ofNat (by omega_arith),
      p.1.args 1 (by decide), ← ek]
    exact msgBit (by omega_arith) (stackArg a 1).isLt
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, _, _, c₁⟩ ⟨_, _, _, _, _, _, c₂⟩ => by
      rw [eval_nonzero, eval_nonzero, c₁, c₂])
    (fail_taint (pins_of (oaepOk H.D) (fun _ _ ⟨⟨s, P, p, E, _⟩, _⟩ => ⟨s, P.1, p.1, E.base⟩) [.r15, .r16])) ?_
  refine (encMain_ct hH cH hG cG hGh hGl hGv).mono (fun _ _ h => ?_) fun _ _ h => h
  obtain ⟨a, ⟨⟨s₁, P₁, p₁, E₁, y₁, hk, c₁⟩, h₁⟩, ⟨⟨s₂, P₂, p₂, E₂, y₂, -, -⟩, -⟩⟩ := h
  rw [eval_nonzero, c₁] at h₁
  have : ¬ (K a - (2 * H.D + 2) < (stackArg a 1).toNat) := by simpa using h₁
  have hK : HK H.D a := by simp only [HK, K] at *; omega_arith
  exact ⟨a, ⟨s₁, P₁, p₁, E₁, y₁, hK⟩, ⟨s₂, P₂, p₂, E₂, y₂, hK⟩⟩

variable {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D)

include cH cG hGh hGl hGv hHh hHl in
theorem code_ct : RelCT isa (Two fun a s => PreT H.D G f s ∧ PubT G a s) (encrypt H f) fun _ _ => True := by
  refine two_alloc (R := fun _ _ => True) (fun a s₁ s₂ h₁ h₂ =>
    ⟨h₁.2.1.sp.trans h₂.2.1.sp.symm, fun _ h => nomatch h⟩) ?_
  refine two_seq (Ψ := fun a t => ∃ s, PreT H.D G f s ∧ PubT G a s ∧ Entered s t ∧ t.syms = s.syms)
    (entry_taint fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂, allocated_sp, allocated_sp, h₁.2.1.sp,
      h₂.2.1.sp], fun _ h => nomatch h⟩)
    (fun a u ⟨s, ⟨P, p⟩, e⟩ => by subst e; exact WP.mono_syms (entry_ok P.1) fun t E y => ⟨s, P, p, E, y⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, PreT H.D G f s ∧ PubT G a s ∧ Saves s t)
    (checks_ct hH cH hG cG hGh hGl hGv) fun a t ⟨s, P, p, E, y⟩ =>
      WP.mono (checks_done hH hG hHh hHl hGh hGl hGv P.1 P.2 E y) fun t' d => ⟨s, P, p, d.1⟩) ?_
  exact restore_taint fun a t₁ t₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
    ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.1.sp, p₂.1.sp], fun _ h => nomatch h⟩

end

end VG.Proof.RsaOaep.PPC64LE
