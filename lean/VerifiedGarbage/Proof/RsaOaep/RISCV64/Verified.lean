module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBase
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTMgfT
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Correct
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Em
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Label
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Main
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-OAEP encryption on RISC-V: constant time

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/CTLabel.lean`, `CTMain.lean`). Two runs are
compared through an anchor `a`, a state with their public data (`PubO`):
the pointers and lengths, `e`'s bytes and the precomputed values;
`BO D a t`: `t` has `Base` from an entry state with `a`'s public data.
`hashLabel_ct`: the label's hash (with the label's pointer and length in
`s6` and `s7`, `LabB`). `code_ct`: the code between the calls by the taint
analysis (`CTBlocks`), the hash functions' calls by their contracts
(`init_ct`, `upd_ct`, `fin_ct`), MGF1's loops on counters both runs agree
on, with the table at the same address and its functions at the same
addresses (`mgfXorT_ct`), the call of `vg_rsa_public_precomputed_checked` by
its contract (`pdCallCT`), and the branches on the public lengths
(`two_ite`); what each run satisfies between them follows from correctness.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo Two Pins two_post two_ite two_alloc wp_li wp_addi wp_subi
  wp_mov wp_sub wp_srl wp_or wp_nil eval_nonzero pdCallCT)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn)

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s. -/
structure PubO (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7], s.gpr r = a.gpr r
  args : ∀ i < 7, stackArg s i = stackArg a i
  e : Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .a4) (a.gpr .a5).toNat
  w : Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 5) (stackArg a 6).toNat

theorem PubO.S {a s : State} (p : PubO a s) : S s = stackArg a 3 := p.args 3 (by decide)

/-- `PubO` gives what the shared code needs. -/
theorem oaepOk (D : Nat) : Ok S vO (PreO D) PubO where
  fits P := P.fits
  agree {a s} p := ⟨p.sp, p.S, fun r hr => by
    simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [vO] <;> exact p.g _ (by decide)⟩

/-- `t` has `Base` from an entry state with `a`'s public data. -/
abbrev BO (D : Nat) : State → State → Prop := B S vO (PreO D) PubO

/-! ## The label's hash -/

section
variable {H : Hash} (hH : HashOK H) (cH : HashCT hH) (hF : H.F ≤ 208)

/-- `BO`, with the label's pointer and length in `s6` and `s7`. -/
def LabB (H : Hash) (a t : State) : Prop := BO H.D a t ∧ t.gpr .s6 = a.gpr .a6 ∧ t.gpr .s7 = a.gpr .a7

/-- The label's update: its arguments. -/
def LabU (H : Hash) (a t : State) : Prop :=
  LabB H a t ∧ t.gpr .a0 = off (stackArg a 3) oSt ∧ t.gpr .a1 = 0 ∧ t.gpr .a2 = a.gpr .a6 ∧
    t.gpr .a3 = a.gpr .a7

/-- The label's finalize: its arguments. -/
def LabF (H : Hash) (a t : State) : Prop :=
  BO H.D a t ∧ t.gpr .a0 = off (stackArg a 3) oSt ∧ t.gpr .a1 = a.gpr .a7 ∧ t.gpr .a2 = off (stackArg a 3) oDig

theorem LabB.keep {a t t' : State} (h : LabB H a t) (hb : BO H.D a t') (h6 : t'.gpr .s6 = t.gpr .s6)
    (h7 : t'.gpr .s7 = t.gpr .s7) : LabB H a t' := ⟨hb, h6.trans h.2.1, h7.trans h.2.2⟩

include hH in
theorem lab_args {a t : State} (h : LabU H a t) :
    ∃ s, PreO H.D s ∧ UpdArgs S vO H s t (s.gpr .a6) (s.gpr .a7).toNat ∧ PubO a s := by
  obtain ⟨⟨⟨s, P, p, b⟩, -, -⟩, h0, -, h2, h3⟩ := h
  have F := hfits hH
  obtain ⟨_, _, _, _, _⟩ := offs
  have hl : lR s ∈ s.rd := by rw [P.hrd]; simp
  have hc : Covers [lR s] (t.rd ++ t.wr) :=
    Covers.left (by rw [b.rd]; exact Covers.of_mem fun r hr => (List.mem_singleton.mp hr) ▸ hl)
  refine ⟨s, P, ⟨P.fits, b, by rw [h0, p.S], by rw [h2, p.g _ (by decide)], by rw [h3, p.g _ (by decide)],
    hc, (P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega)), P.kl.sub_left (cR_sub s)⟩, p⟩

include hH cH hF in
theorem hashLabel_ct : RelCT isa (Two (LabB H)) (hashLabel H) fun _ _ => True := by
  have X := oaepOk H.D
  refine two_seq (Ψ := fun a t => LabB H a t ∧ t.gpr .a0 = off (S a) oSt)
    (st_taint (pins_of X (fun _ _ h => h.1) [])) (fun a t h => ?_) ?_
  · exact wp_addi (imm := oSt) fun t' o e => wp_nil ⟨h.keep (h.1.only X o) (o.get .s6) (o.get .s7),
      by rw [e, (h.1.agree X).2.1]⟩
  refine two_seq (Ψ := LabB H) (init_two X hH cH fun _ _ h => ⟨h.1.1, h.2⟩) (fun a t h => ?_) ?_
  · obtain ⟨⟨⟨s, P, p, b⟩, h6, h7⟩, h0⟩ := h
    exact WP.mono (init_ok P.fits hH hF b (by rw [h0, p.S])) fun t' ⟨b', g', _⟩ =>
      ⟨⟨s, P, p, b'⟩, (g' .s6 (by decide)).trans h6, (g' .s7 (by decide)).trans h7⟩
  refine two_seq (Ψ := LabU H) (upd1_taint (pins_of X (fun _ _ h => h.1) [])) (fun a t h => ?_) ?_
  · obtain ⟨⟨s, P, p, b⟩, h6, h7⟩ := h
    refine wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_li (imm := 0) (by decide) fun t₂ o₂ e₂ =>
      wp_mov fun t₃ o₃ e₃ => wp_mov fun t₄ o₄ e₄ => wp_nil ?_
    have k : Only [.a0, .a1, .a2, .a3] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    refine ⟨⟨⟨s, P, p, b.only P.fits k⟩, by rw [k.get .s6, h6], by rw [k.get .s7, h7]⟩, ?_, ?_, ?_, ?_⟩
    · rw [o₄.get .a0, o₃.get .a0, o₂.get .a0, e₁, b.s0, p.S]
    · rw [o₄.get .a1, o₃.get .a1, e₂]; rfl
    · rw [o₄.get .a2, e₃, o₂.get .s6, o₁.get .s6, h6]
    · rw [e₄, o₃.get .s7, o₂.get .s7, o₁.get .s7, h7]
  refine two_seq (Ψ := LabB H) (upd_ct (S := S) (vf := vO) cH hF fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_)
    (fun a t h => ?_) ?_
  · obtain ⟨s₁, -, A₁, p₁⟩ := lab_args hH h₁
    obtain ⟨s₂, -, A₂, p₂⟩ := lab_args hH h₂
    refine ⟨s₁, s₂, _, _, _, _, A₁, A₂, fun r hr => ?_,
      (A₁.b.agree (X.agree p₁)).1.trans (A₂.b.agree (X.agree p₂)).1.symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.1.trans h₂.2.2.2.1.symm,
      h₁.2.2.2.2.trans h₂.2.2.2.2.symm]
  · obtain ⟨s, P, A, p⟩ := lab_args hH h
    exact WP.mono (upd_ok A.P hH hF A.b A.h0 A.h2 A.h3 A.hdc A.hd₁ A.hd₃) fun t' ⟨b', g', _⟩ =>
      h.1.keep ⟨s, P, p, b'⟩ (g' .s6 (by decide)) (g' .s7 (by decide))
  refine two_seq (Ψ := LabF H) (lab3_taint (pins_of X (fun _ _ h => h.1) [])) (fun a t h => ?_) ?_
  · obtain ⟨⟨s, P, p, b⟩, _, h7⟩ := h
    refine wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_addi (imm := oDig) fun t₃ o₃ e₃ =>
      wp_nil ?_
    have k : Only [.a0, .a1, .a2] t t₃ := (o₁.trans (o₂.trans o₃)).mono
    refine ⟨⟨s, P, p, b.only P.fits k⟩, ?_, ?_, ?_⟩
    · rw [o₃.get .a0, o₂.get .a0, e₁, b.s0, p.S]
    · rw [o₃.get .a1, e₂, o₁.get .s7, h7]
    · rw [e₃, o₂.get .s0, o₁.get .s0, b.s0, p.S]
  refine fin_ct (S := S) (vf := vO) cH hF fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_
  obtain ⟨⟨s₁, P₁, p₁, b₁⟩, x0, x1, x2⟩ := h₁
  obtain ⟨⟨s₂, P₂, p₂, b₂⟩, y0, y1, y2⟩ := h₂
  refine ⟨s₁, s₂, ⟨P₁.fits, b₁, by rw [x0, p₁.S], by rw [x2, p₁.S]⟩,
    ⟨P₂.fits, b₂, by rw [y0, p₂.S], by rw [y2, p₂.S]⟩, fun r hr => ?_,
    (b₁.agree (X.agree p₁)).1.trans (b₂.agree (X.agree p₂)).1.symm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [x0.trans y0.symm, x1.trans y1.symm, x2.trans y2.symm]

end

/-! ## The function -/

/-- Two calls of `vg_rsa_public_precomputed_checked` from `AtCall`, for
entry states with the anchor's public data, agree on what the callee may
leak. -/
theorem call_ct {D : Nat} :
    RelCT isa (Two fun a t => ∃ s, PreO D s ∧ PubO a s ∧ ∃ EM, AtCall s EM t) Impl.RsaPkcs1Sig.RISCV64.pubCall
      fun _ _ => True := by
  refine pdCallCT fun t₁ t₂ ⟨a, ⟨s₁, P₁, p₁, EM₁, c₁⟩, ⟨s₂, P₂, p₂, EM₂, c₂⟩⟩ => ⟨pdOk_of P₁ c₁,
    pdOk_of P₂ c₂, ⟨?_, fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [c₁.sv.sp, c₂.sv.sp, fb, fb, p₁.sp, p₂.sp]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.g0, c₂.g0, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [c₁.g1, c₂.g1, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [c₁.g2, c₂.g2, p₁.args 5 (by decide), p₂.args 5 (by decide)]
    · rw [c₁.g3, c₂.g3, p₁.args 6 (by decide), p₂.args 6 (by decide)]
    · rw [c₁.g4, c₂.g4, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [c₁.g5, c₂.g5, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [c₁.g6, c₂.g6, p₁.S, p₂.S]
    · rw [c₁.g7, c₂.g7, p₁.g _ (by decide), p₂.g _ (by decide)]
  · rw [c₁.a0, c₂.a0, p₁.S, p₂.S]
  · rw [c₁.a1, c₂.a1, p₁.args 4 (by decide), p₂.args 4 (by decide)]
  · rw [c₁.g2, c₂.g2, c₁.g3, c₂.g3, words_entry c₁.mem P₁.kp ((P₁.sp).sub_left (sc_sub P₁)) P₁.wp,
      words_entry c₂.mem P₂.kp ((P₂.sp).sub_left (sc_sub P₂)) P₂.wp, p₁.w, p₂.w]
  · rw [c₁.g4, c₂.g4, c₁.g5, c₂.g5,
      bytes_entry c₁.mem P₁.ke ((P₁.es.symm).sub_left (sc_sub P₁)) (by have := P₁.we; omega),
      bytes_entry c₂.mem P₂.ke ((P₂.es.symm).sub_left (sc_sub P₂)) (by have := P₂.we; omega), p₁.e, p₂.e]

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
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (hG : HashOK G) (cG : HashCT hG) (fH : FitsF H)
  (fG : FitsF G) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
  (hGv : Proof.Mgf1.Valid Gs) {f : Fns}

include cG fG hGh hGl hGv in
/-- `mgfXorT`, with its lengths and offsets the anchor's. -/
theorem mgf_any (q : State → Nat × Nat × Nat × Nat) :
    RelCT isa (Two fun a t => MgfAT S vO (PreT H.D G f) (PubT G) (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2 a t ∧
      MFit (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2) (mgfXorT f 7) fun _ _ => True :=
  (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfAT S vO (PreT H.D G f) (PubT G) x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXorT_ct (okT H.D G f) hG cG fG x.2 hGh hGl hGv (tabT H.D G f)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨q a, h₁.2⟩, a, h₁.1, h₂.1⟩) fun _ _ h => h

/-- The checks passed, in terms of the anchor. -/
abbrev HK (D : Nat) (a : State) : Prop := 2 * D + 2 + (stackArg a 1).toNat ≤ (a.gpr .a3).toNat

theorem hk_of {D : Nat} {a s : State} (p : PubO a s) (h : HK D a) : 2 * D + 2 + mLen s ≤ kk s := by
  simp only [mLen, kk, p.args 1 (by decide), p.g .a3 (by decide)]; exact h

/-- `BG` with the checks passed. -/
def Bk (D : Nat) (G : Hash) (f : Fns) (a t : State) : Prop := BG D G f a t ∧ HK D a

theorem bk_pins {D : Nat} {α : Type} {Φ : α → State → Prop} (A : α → State) (h : ∀ x t, Φ x t → BO D (A x) t) :
    Pins Φ [] := fun x t₁ t₂ h₁ h₂ =>
  ⟨((h x t₁ h₁).sp (oaepOk D)).trans ((h x t₂ h₂).sp (oaepOk D)).symm, fun _ h => nomatch h⟩

include cH fH cG fG hGh hGl hGv in
theorem encMain_ct : RelCT isa (Two fun a t => ∃ s, PreT H.D G f s ∧ PubT G a s ∧ Entered s t ∧ t.syms = s.syms ∧
    HK H.D a) (encMain H f) fun _ _ => True := by
  have F := hfits hH
  obtain ⟨hE, _, _, _, _⟩ := offs
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  have X := oaepOk H.D
  -- `EM` before masking.
  refine two_seq (Ψ := fun a t => (BG H.D G f a t ∧ t.gpr .s6 = a.gpr .a6 ∧ t.gpr .s7 = a.gpr .a7) ∧ HK H.D a)
    (encEm_taint H fun a t₁ t₂ ⟨s₁, _, ⟨p₁, _⟩, E₁, _⟩ ⟨s₂, _, ⟨p₂, _⟩, E₂, _⟩ => ?_)
    (fun a t ⟨s, P, p, E, sy, hk⟩ => WP.mono_syms (encEm_ok P.1 rfl hD0 hD64 E (hk_of p.1 hk))
      fun t' ⟨b, g6, g7, _⟩ y => ⟨⟨⟨s, P, p, b, y.trans sy⟩, by rw [g6, p.1.g _ (by decide)],
        by rw [g7, p.1.g _ (by decide)]⟩, hk⟩) ?_
  · have f₁ := E₁.base.agree (X.agree p₁)
    have f₂ := E₂.base.agree (X.agree p₂)
    refine ⟨f₁.1.trans f₂.1.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [E₁.t2, E₂.t2, p₁.args 0 (by decide), p₂.args 0 (by decide)]
    · rw [E₁.t3, E₂.t3, p₁.args 1 (by decide), p₂.args 1 (by decide)]
    · rw [E₁.t4, E₂.t4, p₁.args 2 (by decide), p₂.args 2 (by decide)]
    · exact f₁.2.1.trans f₂.2.1.symm
    · exact (f₁.2.2 _ (by decide)).trans (f₂.2.2 _ (by decide)).symm
  -- The label's hash, and `lHash`.
  refine two_seq (Ψ := Bk H.D G f) ((hashLabel_ct hH cH fH).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, ⟨h₁.1.1.bo, h₁.1.2⟩, ⟨h₂.1.1.bo, h₂.1.2⟩⟩) fun _ _ h => h)
    (fun a t ⟨⟨⟨s, P, p, b, sy⟩, h6, h7⟩, hk⟩ => WP.mono_syms (hashLabel_ok P.1 hH fH b
      (by rw [h6, p.1.g _ (by decide)]) (by rw [h7, p.1.g _ (by decide)])) fun t' ⟨b', _⟩ y =>
      ⟨⟨s, P, p, b', y.trans sy⟩, hk⟩) ?_
  refine two_seq (Ψ := Bk H.D G f) (copyLh_taint H (pins_of X (fun _ _ h => h.1.bo) [.s0]))
    (fun a t ⟨⟨s, P, p, b, sy⟩, hk⟩ => WP.mono_syms (copyLh_ok P.1 hH rfl b) fun t' ⟨b', _⟩ y =>
      ⟨⟨s, P, p, b', y.trans sy⟩, hk⟩) ?_
  -- `DB` with MGF1 of the seed.
  let q₁ : State → Nat × Nat × Nat × Nat := fun a => (1, H.D, 1 + H.D, (a.gpr .a3).toNat - H.D - 1)
  refine two_seq (Ψ := fun a t => (MgfAT S vO (PreT H.D G f) (PubT G) (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1
      (q₁ a).2.2.2 a t ∧ MFit (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2) ∧ HK H.D a)
    (dbArgs_taint H (bk_pins id fun _ _ h => h.1.bo)) (fun a t ⟨⟨s, P, p, b, sy⟩, hk⟩ => ?_) ?_
  · have k2 := P.1.k2
    have ek : (a.gpr .a3).toNat = (s.gpr .a3).toNat := by rw [p.1.g .a3 (by decide)]
    refine WP.of_syms (wp_addi (imm := oEm + 1) (h := by omega) fun t₁ o₁ e₁ => wp_li (imm := H.D) (by omega)
      fun t₂ o₂ e₂ => wp_addi (imm := oEm + 1 + H.D) (h := by omega) fun t₃ o₃ e₃ =>
      wp_subi (imm := H.D + 1) (h := by omega) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
    have k₄ : Only [.s6, .s7, .s8, .s9] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    show (MgfAT S vO (PreT H.D G f) (PubT G) 1 H.D (1 + H.D) ((a.gpr .a3).toNat - H.D - 1) a t₄ ∧
      MFit 1 H.D (1 + H.D) ((a.gpr .a3).toNat - H.D - 1)) ∧ HK H.D a
    refine ⟨⟨⟨s, P, p, b.only P.1.fits k₄, y.trans sy, ?_, ?_, ?_, ?_⟩,
      ⟨by omega, by omega, .inl (by omega), by omega⟩⟩, hk⟩
    · rw [o₄.get .s6, o₃.get .s6, o₂.get .s6, e₁, b.s0, p.1.S, hE]
    · rw [o₄.get .s7, o₃.get .s7, e₂]
    · rw [o₄.get .s8, e₃, o₂.get .s0, o₁.get .s0, b.s0, p.1.S, hE, Nat.zero_add]
    · rw [e₄, o₃.get .s1, o₂.get .s1, o₁.get .s1, b.s1, sub_k (by omega)]; congr 1; omega
  refine two_seq (Ψ := Bk H.D G f) ((mgf_any hG cG fG hGh hGl hGv q₁).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩) fun _ _ h => h)
    (fun a t ⟨⟨⟨s, P, p, b, sy, h6, h7, h8, h9⟩, hf⟩, hk⟩ =>
    WP.mono (mgfXorT_ok P.1.fits hG fG P.2 hGh hGl hGv hf b sy (by rw [h6, p.1.S]) h7 (by rw [h8, p.1.S]) h9)
      fun t' ⟨⟨b', _⟩, y⟩ => ⟨⟨s, P, p, b', y⟩, hk⟩) ?_
  -- The seed with MGF1 of `maskedDB`.
  let q₂ : State → Nat × Nat × Nat × Nat := fun a => (1 + H.D, (a.gpr .a3).toNat - H.D - 1, 1, H.D)
  refine two_seq (Ψ := fun a t => (MgfAT S vO (PreT H.D G f) (PubT G) (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1
      (q₂ a).2.2.2 a t ∧ MFit (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2) ∧ HK H.D a)
    (seedArgs_taint H (bk_pins id fun _ _ h => h.1.bo)) (fun a t ⟨⟨s, P, p, b, sy⟩, hk⟩ => ?_) ?_
  · have k2 := P.1.k2
    have ek : (a.gpr .a3).toNat = (s.gpr .a3).toNat := by rw [p.1.g .a3 (by decide)]
    refine WP.of_syms (wp_addi (imm := oEm + 1 + H.D) (h := by omega) fun t₁ o₁ e₁ =>
      wp_subi (imm := H.D + 1) (h := by omega) fun t₂ o₂ e₂ => wp_addi (imm := oEm + 1) (h := by omega)
      fun t₃ o₃ e₃ => wp_li (imm := H.D) (by omega) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
    have k₄ : Only [.s6, .s7, .s8, .s9] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    show (MgfAT S vO (PreT H.D G f) (PubT G) (1 + H.D) ((a.gpr .a3).toNat - H.D - 1) 1 H.D a t₄ ∧
      MFit (1 + H.D) ((a.gpr .a3).toNat - H.D - 1) 1 H.D) ∧ HK H.D a
    refine ⟨⟨⟨s, P, p, b.only P.1.fits k₄, y.trans sy, ?_, ?_, ?_, ?_⟩,
      ⟨by omega, by omega, .inr (by omega), by omega⟩⟩, hk⟩
    · rw [o₄.get .s6, o₃.get .s6, o₂.get .s6, e₁, b.s0, p.1.S, hE, Nat.zero_add]
    · rw [o₄.get .s7, o₃.get .s7, e₂, o₁.get .s1, b.s1, sub_k (by omega)]; congr 1; omega
    · rw [o₄.get .s8, e₃, o₂.get .s0, o₁.get .s0, b.s0, p.1.S, hE]
    · rw [e₄]
  refine two_seq (Ψ := Bk H.D G f) ((mgf_any hG cG fG hGh hGl hGv q₂).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩) fun _ _ h => h)
    (fun a t ⟨⟨⟨s, P, p, b, sy, h6, h7, h8, h9⟩, hf⟩, hk⟩ =>
    WP.mono (mgfXorT_ok P.1.fits hG fG P.2 hGh hGl hGv hf b sy (by rw [h6, p.1.S]) h7 (by rw [h8, p.1.S]) h9)
      fun t' ⟨⟨b', _⟩, y⟩ => ⟨⟨s, P, p, b', y⟩, hk⟩) ?_
  -- The public-key operation.
  exact two_seq (pubArgs_taint (bk_pins id fun _ _ h => h.1.bo)) (fun a t ⟨⟨s, P, p, b, _⟩, _⟩ =>
    WP.mono (pubArgs_ok P.1 b rfl) fun t' h => ⟨s, P.1, p.1, _, h⟩) call_ct

theorem entered_only {s t t' : State} {rs : List Reg} {D : Nat} (P : PreO D s) (E : Entered s t)
    (o : Only rs t t')
    (hrs : ∀ r ∈ rs, r ∉ fixed ++ ([.s6, .s7, .t2, .t3, .t4] : List Reg) := by decide) : Entered s t' := by
  have g : ∀ r ∈ [Reg.s6, .s7, .t2, .t3, .t4], t'.gpr r = t.gpr r := fun r hr =>
    o.gpr r fun h => hrs r h (List.mem_append_right _ hr)
  exact ⟨E.base.only P.fits o fun r h h' => hrs r h (List.mem_append_left _ h'), (g _ (by decide)).trans E.s6,
    (g _ (by decide)).trans E.s7, (g _ (by decide)).trans E.t2, (g _ (by decide)).trans E.t3,
    (g _ (by decide)).trans E.t4⟩

include cH fH cG fG hGh hGl hGv in
theorem checks_ct : RelCT isa (Two fun a t => ∃ s, PreT H.D G f s ∧ PubT G a s ∧ Entered s t ∧ t.syms = s.syms)
    (checks H f) fun _ _ => True := by
  have hD64 := hH.hD64
  let K := fun (a : State) => (a.gpr .a3).toNat
  refine two_seq (Ψ := fun a t => ∃ s, PreT H.D G f s ∧ PubT G a s ∧ Entered s t ∧ t.syms = s.syms ∧
      (t.gpr .a0 != 0) = decide (K a < 2 * H.D + 2))
    (chkK_taint H (bk_pins id fun _ _ ⟨s, P, p, E, _⟩ => ⟨s, P.1, p.1, E.base⟩)) (fun a t ⟨s, P, p, E, sy⟩ => ?_) ?_
  · have k2 := P.1.k2
    have ka : (a.gpr .a3).toNat ≤ 1024 := by rw [← p.1.g .a3 (by decide)]; exact P.1.k2
    refine WP.of_syms (wp_li (imm := 2 * H.D + 2) (by omega) fun t₁ o₁ e₁ => wp_sub fun t₂ o₂ e₂ =>
      wp_srl fun t₃ o₃ e₃ => wp_nil fun y => ?_)
    have k₃ : Only [.a0] t t₃ := (o₁.trans (o₂.trans o₃)).mono
    refine ⟨s, P, p, entered_only P.1 E k₃, y.trans sy, ?_⟩
    rw [e₃, e₂, e₁, o₁.get .s1, E.base.s1, ← ofNat_toNat (s.gpr .a3), p.1.g .a3 (by decide)]
    exact ne_zero_ltBit (by omega) (by omega)
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, _, c₁⟩ ⟨_, _, _, _, _, c₂⟩ => by rw [eval_nonzero, eval_nonzero, c₁, c₂])
    (fail_taint (pins_of (oaepOk H.D) (fun _ _ ⟨⟨s, P, p, E, _⟩, _⟩ => ⟨s, P.1, p.1, E.base⟩) [.s1, .s2])) ?_
  refine two_seq (Ψ := fun a t => ∃ s, PreT H.D G f s ∧ PubT G a s ∧ Entered s t ∧ t.syms = s.syms ∧
      2 * H.D + 2 ≤ K a ∧ (t.gpr .a0 != 0) = decide (K a - (2 * H.D + 2) < (stackArg a 1).toNat))
    (chkMsg_taint H (bk_pins id fun _ _ ⟨⟨s, P, p, E, _⟩, _⟩ => ⟨s, P.1, p.1, E.base⟩))
    (fun a t ⟨⟨s, P, p, E, sy, c⟩, hc⟩ => ?_) ?_
  · have k2 := P.1.k2
    have hk : 2 * H.D + 2 ≤ K a := by rw [eval_nonzero, c] at hc; simpa using hc
    have ek : K a = (s.gpr .a3).toNat := by simp only [K]; rw [p.1.g .a3 (by decide)]
    refine WP.of_syms (wp_li (imm := 2 * H.D + 2) (by omega) fun t₄ o₄ e₄ => wp_sub fun t₅ o₅ e₅ =>
      wp_sub fun t₆ o₆ e₆ => wp_srl fun t₇ o₇ e₇ => wp_srl fun t₈ o₈ e₈ => wp_or fun t₉ o₉ e₉ =>
        wp_nil fun y => ?_)
    have k₉ : Only [.a0, .a1] t t₉ := (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans o₉))))).mono
    refine ⟨s, P, p, entered_only P.1 E k₉, y.trans sy, hk, ?_⟩
    rw [e₉, e₈, o₇.get .t3, o₆.get .t3, o₅.get .t3, o₄.get .t3, E.t3, o₈.get .a1, e₇, e₆,
      o₅.get .t3, o₄.get .t3, E.t3, e₅, o₄.get .s1, E.base.s1, e₄,
      ← ofNat_toNat (s.gpr .a3), ← ofNat_toNat (stackArg s 1), Offset.ofNat_sub_ofNat (by omega),
      p.1.args 1 (by decide), ← ek]
    exact msgBit (by omega) (stackArg a 1).isLt
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, _, _, c₁⟩ ⟨_, _, _, _, _, _, c₂⟩ => by
      rw [eval_nonzero, eval_nonzero, c₁, c₂])
    (fail_taint (pins_of (oaepOk H.D) (fun _ _ ⟨⟨s, P, p, E, _⟩, _⟩ => ⟨s, P.1, p.1, E.base⟩) [.s1, .s2])) ?_
  refine (encMain_ct hH cH hG cG fH fG hGh hGl hGv).mono (fun _ _ h => ?_) fun _ _ h => h
  obtain ⟨a, ⟨⟨s₁, P₁, p₁, E₁, y₁, hk, c₁⟩, h₁⟩, ⟨⟨s₂, P₂, p₂, E₂, y₂, -, -⟩, -⟩⟩ := h
  rw [eval_nonzero, c₁] at h₁
  have : ¬ (K a - (2 * H.D + 2) < (stackArg a 1).toNat) := by simpa using h₁
  have hK : HK H.D a := by simp only [HK, K] at *; omega
  exact ⟨a, ⟨s₁, P₁, p₁, E₁, y₁, hK⟩, ⟨s₂, P₂, p₂, E₂, y₂, hK⟩⟩

variable {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D)

include cH fH cG fG hGh hGl hGv hHh hHl in
theorem code_ct : RelCT isa (Two fun a s => PreT H.D G f s ∧ PubT G a s) (encrypt H f) fun _ _ => True := by
  refine two_alloc (R := fun _ _ => True) ?_
  refine two_seq (Ψ := fun a t => ∃ s, PreT H.D G f s ∧ PubT G a s ∧ Entered s t ∧ t.syms = s.syms)
    (entry_taint fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; simp only [allocd, h₁.2.1.sp,
      h₂.2.1.sp], fun _ h => nomatch h⟩)
    (fun a u ⟨s, ⟨P, p⟩, e⟩ => by subst e; exact WP.mono_syms (entry_ok P.1) fun t E y => ⟨s, P, p, E, y⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, PreT H.D G f s ∧ PubT G a s ∧ Saves s t)
    (checks_ct hH cH hG cG fH fG hGh hGl hGv) fun a t ⟨s, P, p, E, y⟩ =>
      WP.mono (checks_done hH hG fH fG hHh hHl hGh hGl hGv P.1 P.2 E y) fun t' d => ⟨s, P, p, d.1⟩) ?_
  exact restore_taint fun a t₁ t₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
    ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.1.sp, p₂.1.sp], fun _ h => nomatch h⟩

end

end VG.Proof.RsaOaep.RISCV64

/-!
# RSAES-OAEP encryption on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Verified.lean`): the contract's public data as
`PubO`, with the table's (`pubT_of`); constant time (`code_constantTime`,
from `code_ct`); states meeting the precondition for the hash functions the
label is hashed with, with MGF1's table that of any `w` of `vs`, at
`0x300000` (`enc_sat`); and `enc_verified`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.HashTable.RISCV64 (TVar tables fnsOf Coh)

theorem leak_eq {a b c d : List Byte} {w w' : List (BitVec 64)} (ha : a.length = c.length)
    (hb : b.length = d.length)
    (h : (a ++ b).map (·.toNat) ++ w.map (·.toNat) = (c ++ d).map (·.toNat) ++ w'.map (·.toNat)) :
    b = d ∧ w = w' := by
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [ha, hb])
  have hi : a ++ b = c ++ d := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₁
  exact ⟨(List.append_inj hi ha).2, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₂⟩

/-- The contract's public data: `PubO`, MGF1's table at the same address,
the tables' functions at the same addresses, and the same tables held. -/
theorem pubT_of {Hs : Spec.Mgf1.Hash} {ts : List FnTable} {s₁ s₂ : State} (h : (encSpec Hs ts).pub s₁ s₂) :
    PubO s₁ s₂ ∧ stackArg s₂ 7 = stackArg s₁ 7 ∧
      (∀ f ∈ (ts.map (fun T : FnTable => T.fns)).flatten, s₁.syms f = s₂.syms f) ∧
      ∀ T ∈ ts, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 7) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 7) (FnTable.words isa s₂ T)) := by
  have e : stackBytes = 335 + 1 := rfl
  unfold encSpec at h
  rw [e] at h
  sig_pub [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig, Spec.RsaOaep.encryptPrecomputedSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs,
    stackArgs_eight, List.append_eq, List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htab, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
  obtain ⟨he, hw⟩ := leak_eq (by simp [bytesAt_length, h3]) (by simp [bytesAt_length, h5]) hl
  refine ⟨⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, he.symm, hw.symm⟩, a7.symm, hsy,
    fun T hT => htab _ _ rfl rfl T hT⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm]

theorem pubO_refl (s : State) : PubO s s := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

section
variable {H : Hash} (hH : HashOK H) (cH : HashCT hH) (fH : FitsF H) {Hs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D)
include cH fH hHh hHl

/-- Constant time: the table of the first run, which the public data makes
the second's, at the same address with its functions at the same addresses. -/
theorem code_constantTime {vs : List TVar} (hc : Coh vs) :
    ConstantTime isa (encSpec Hs (tables vs)).pre (encSpec Hs (tables vs)).pub (encrypt H (fnsOf vs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨⟨T, hT, hh⟩, -⟩ := spec_tab h₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨p, a7, hsy, hiff⟩ := pubT_of hp
  have hn := Proof.HashTable.RISCV64.mem_names hw
  have P₁ : PreO H.D s₁ := hHl ▸ preO_of h₁
  have P₂ : PreO H.D s₂ := hHl ▸ preO_of h₂
  exact code_ct hH cH w.l.ok w.l.ct fH w.l.fits w.l.hash w.l.len w.l.valid hHh hHl _ _ _ _ _ _
    ⟨s₁, ⟨⟨P₁, tabS_entry hc h₁ hw hh⟩, pubO_refl s₁, rfl, rfl, rfl, rfl⟩,
      ⟨P₂, tabS_entry hc h₂ hw ((hiff _ hT).mp hh)⟩, p, a7, (hsy _ hn.1).symm, (hsy _ hn.2.1).symm,
      (hsy _ hn.2.2).symm⟩ e₁ e₂

/-- `vg_rsa_oaep_<H>_mgf1_encrypt_precomputed` against its contract, for the
tables of `vs`, given a state meeting it. -/
theorem enc_verified {vs : List TVar} (hc : Coh vs) (hsat : ∃ s, (encSpec Hs (tables vs)).pre s) :
    Verified RISCV64.target (encrypt H (fnsOf vs)) (encSpec Hs (tables vs)) :=
  ⟨code_correct hH fH hHh hHl hc, code_constantTime hH cH fH hHh hHl hc, hsat⟩

end

/-! ## A state meeting the precondition -/

/-- A state meeting encryption's contract for a seed of `D` bytes, but for
the table: a 512-bit modulus, a one-byte `e`, an empty label and message,
the seed, a working space of 2080 words, 16 words of `pre` at `0x5000`, the
stack arguments at `sp`, and MGF1's table's address `0x300000`. -/
def encSatState (D : Nat) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 64 | .a4 => 0x3000 | .a5 => 1 | .a6 => 0x4000
    | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10001 then 0x41
    else bif Nat.beq a.toNat 0x10011 then 0x42 else bif Nat.beq a.toNat 0x1001A then 0x02
    else bif Nat.beq a.toNat 0x10020 then 0x20 else bif Nat.beq a.toNat 0x10021 then 0x08
    else bif Nat.beq a.toNat 0x10029 then 0x50 else bif Nat.beq a.toNat 0x10030 then 16
    else bif Nat.beq a.toNat 0x1003A then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x4100, 0⟩, ⟨0x4200, D⟩, ⟨0x5000, 128⟩, ⟨0x300000, 40⟩,
    ⟨0x10000, 64⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 16640⟩]

section
variable {vs : List TVar} {w : TVar}

theorem stackArgAddr_sat (D j : Nat) (hj : j < 8) :
    (stackArgAddr (encSatState D) j).toNat + 8 ≤ 0x300000 := by
  revert j; show ∀ j < 8, (stackArgAddr (encSatState 0) j).toNat + 8 ≤ 0x300000; decide

theorem stackArg_sat {D j : Nat} {v : Addr} (hj : j < 8) (e : stackArg (encSatState 0) j = v) :
    stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) j = v :=
  (Proof.HashTable.RISCV64.withTable_below _ _ _ (stackArgAddr_sat D j hj)).trans e

theorem sat_a0 (D : Nat) : stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 0 = 0x4100 :=
  stackArg_sat (by decide) (by decide)
theorem sat_a1 (D : Nat) : stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 1 = 0 :=
  stackArg_sat (by decide) (by decide)
theorem sat_a2 (D : Nat) : stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 2 = 0x4200 :=
  stackArg_sat (by decide) (by decide)
theorem sat_a3 (D : Nat) : stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 3 = 0x20000 :=
  stackArg_sat (by decide) (by decide)
theorem sat_a4 (D : Nat) : stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 4 = 2080 :=
  stackArg_sat (by decide) (by decide)
theorem sat_a5 (D : Nat) : stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 5 = 0x5000 :=
  stackArg_sat (by decide) (by decide)
theorem sat_a6 (D : Nat) : stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 6 = 16 :=
  stackArg_sat (by decide) (by decide)
theorem sat_a7 (D : Nat) : stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 7 = 0x300000 :=
  stackArg_sat (by decide) (by decide)
theorem sat_e (D : Nat) : stackArgAddr (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 0 = 0x10000 :=
  show stackArgAddr (encSatState 0) 0 = _ by decide

/-- A state meeting the contract, for the hash functions the label is hashed
with, with MGF1's table that of `w`, at `0x300000`. -/
theorem enc_sat {H : Spec.Mgf1.Hash} (hH : H ∈ labelHashes) (hw : w ∈ vs)
    (hl : (Proof.HashTable.RISCV64.names vs).length < 2 ^ 32) : ∃ s, (encSpec H (tables vs)).pre s := by
  refine ⟨Proof.HashTable.RISCV64.withTable (encSatState H.len) vs w, ?_⟩
  have e : stackBytes = 335 + 1 := rfl
  unfold encSpec
  rw [e]
  simp only [labelHashes, List.mem_cons, List.not_mem_nil, or_false] at hH
  rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    sig_pre [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig, Spec.RsaOaep.encryptPrecomputedSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
      argRegs, stackArgs_eight, List.append_eq, List.range, List.range.loop]
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq, exists_eq_left', sat_a0, sat_a1, sat_a2, sat_a3, sat_a4, sat_a5, sat_a6,
      sat_a7, sat_e]
    sig_and_intros
    all_goals first
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
      | exact ⟨Proof.HashTable.RISCV64.tableOf w, List.mem_map_of_mem hw, Proof.HashTable.RISCV64.withTable_held _ _ _⟩
      | exact Proof.HashTable.symsOf_distinct hl
      | (simp only [Spec.Rsa.lenValid]; decide)

end

end VG.Proof.RsaOaep.RISCV64
