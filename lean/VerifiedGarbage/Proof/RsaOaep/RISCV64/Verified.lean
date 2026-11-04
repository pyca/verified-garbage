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
  args : ∀ i < 8, stackArg s i = stackArg a i
  e : Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .a4) (a.gpr .a5).toNat
  w : Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 6) (stackArg a 7).toNat

theorem PubO.S {a s : State} (p : PubO a s) : S s = stackArg a 4 := p.args 4 (by decide)

/-- `PubO` gives what the shared code needs. -/
theorem oaepOk (D : Nat) : Ok S vO (PreO D) PubO where
  fits P := P.fits
  agree {a s} p := ⟨p.sp, p.S, fun r hr => by
    simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [vO] <;> exact p.g _ (by decide)⟩

/-- `t` has `Base` from an entry state with `a`'s public data. -/
abbrev BO (D : Nat) : State → State → Prop := B S vO (PreO D) PubO

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
    · rw [c₁.g2, c₂.g2, p₁.args 6 (by decide), p₂.args 6 (by decide)]
    · rw [c₁.g3, c₂.g3, p₁.args 7 (by decide), p₂.args 7 (by decide)]
    · rw [c₁.g4, c₂.g4, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [c₁.g5, c₂.g5, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [c₁.g6, c₂.g6, p₁.S, p₂.S]
    · rw [c₁.g7, c₂.g7, p₁.g _ (by decide), p₂.g _ (by decide)]
  · rw [c₁.a0, c₂.a0, p₁.S, p₂.S]
  · rw [c₁.a1, c₂.a1, p₁.args 5 (by decide), p₂.args 5 (by decide)]
  · rw [c₁.g2, c₂.g2, c₁.g3, c₂.g3, words_entry c₁.mem P₁.kp ((P₁.sp).sub_left (sc_sub P₁)) P₁.wp,
      words_entry c₂.mem P₂.kp ((P₂.sp).sub_left (sc_sub P₂)) P₂.wp, p₁.w, p₂.w]
  · rw [c₁.g4, c₂.g4, c₁.g5, c₂.g5,
      bytes_entry c₁.mem P₁.ke ((P₁.es.symm).sub_left (sc_sub P₁)) (by have := P₁.we; omega),
      bytes_entry c₂.mem P₂.ke ((P₂.es.symm).sub_left (sc_sub P₂)) (by have := P₂.we; omega), p₁.e, p₂.e]

/-- The precondition, with MGF1's table, `G`'s, and the label's hash
function's, `H`'s, on entry. -/
def PreT (D : Nat) (G H : Hash) (f : Fns) (s : State) : Prop :=
  PreO D s ∧ TabS G f 9 S s (stackArg s 9) ∧ TabS H f 8 S s (stackArg s 8)

/-- The public data, with both tables at the anchor's addresses and their
hash functions' functions at the anchor's addresses. -/
def PubT (G H : Hash) (a s : State) : Prop :=
  PubO a s ∧ stackArg s 9 = stackArg a 9 ∧ s.syms G.initN = a.syms G.initN ∧ s.syms G.updN = a.syms G.updN ∧
    s.syms G.finN = a.syms G.finN ∧ stackArg s 8 = stackArg a 8 ∧ s.syms H.initN = a.syms H.initN ∧
    s.syms H.updN = a.syms H.updN ∧ s.syms H.finN = a.syms H.finN

theorem okT (D : Nat) (G H : Hash) (f : Fns) : Ok S vO (PreT D G H f) (PubT G H) :=
  ⟨fun P => P.1.fits, fun p => (oaepOk D).agree p.1⟩

theorem tabT (D : Nat) (G H : Hash) (f : Fns) : TabA G f 9 S (PreT D G H f) (PubT G H) :=
  ⟨fun P => P.2.1, fun p => p.2.1, fun p => p.2.2.1, fun p => p.2.2.2.1, fun p => p.2.2.2.2.1⟩

theorem tabL (D : Nat) (G H : Hash) (f : Fns) : TabA H f 8 S (PreT D G H f) (PubT G H) :=
  ⟨fun P => P.2.2, fun p => p.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.2.1,
    fun p => p.2.2.2.2.2.2.2.2⟩

/-- `t` has `Base` from an entry state with `G`'s table and `a`'s public
data, and its addresses of statics. -/
abbrev BG (D : Nat) (G H : Hash) (f : Fns) : State → State → Prop := BT S vO (PreT D G H f) (PubT G H)

theorem BG.bo {D : Nat} {G H : Hash} {f : Fns} {a t : State} (h : BG D G H f a t) : BO D a t :=
  let ⟨s, P, p, b, _⟩ := h; ⟨s, P.1, p.1, b⟩

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (hG : HashOK G) (cG : HashCT hG) (fH : FitsF H)
  (fG : FitsF G) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
  (hGv : Proof.Mgf1.Valid Gs) {f : Fns}

include cG fG hGh hGl hGv in
/-- `mgfXorT`, with its lengths and offsets the anchor's. -/
theorem mgf_any (q : State → Nat × Nat × Nat × Nat) :
    RelCT isa (Two fun a t => MgfAT S vO (PreT H.D G H f) (PubT G H) (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2 a t ∧
      MFit (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2) (mgfXorT f 9) fun _ _ => True :=
  (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfAT S vO (PreT H.D G H f) (PubT G H) x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXorT_ct (okT H.D G H f) hG cG fG x.2 hGh hGl hGv (tabT H.D G H f)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨q a, h₁.2⟩, a, h₁.1, h₂.1⟩) fun _ _ h => h

/-- The checks passed, in terms of the anchor. -/
abbrev HK (D : Nat) (a : State) : Prop := 2 * D + 2 + (stackArg a 1).toNat ≤ (a.gpr .a3).toNat

theorem hk_of {D : Nat} {a s : State} (p : PubO a s) (h : HK D a) : 2 * D + 2 + mLen s ≤ kk s := by
  simp only [mLen, kk, p.args 1 (by decide), p.g .a3 (by decide)]; exact h

/-- `BG` with the checks passed. -/
def Bk (D : Nat) (G H : Hash) (f : Fns) (a t : State) : Prop := BG D G H f a t ∧ HK D a

theorem bk_pins {D : Nat} {α : Type} {Φ : α → State → Prop} (A : α → State) (h : ∀ x t, Φ x t → BO D (A x) t) :
    Pins Φ [] := fun x t₁ t₂ h₁ h₂ =>
  ⟨((h x t₁ h₁).sp (oaepOk D)).trans ((h x t₂ h₂).sp (oaepOk D)).symm, fun _ h => nomatch h⟩

include cH fH cG fG hGh hGl hGv in
theorem encMain_ct : RelCT isa (Two fun a t => ∃ s, PreT H.D G H f s ∧ PubT G H a s ∧ Entered s t ∧ t.syms = s.syms ∧
    HK H.D a) (encMain H f) fun _ _ => True := by
  have F := hfits hH
  obtain ⟨hE, _, _, _, _⟩ := offs
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  have X := oaepOk H.D
  -- `EM` before masking.
  refine two_seq (Ψ := fun a t => (BG H.D G H f a t ∧ t.gpr .s6 = a.gpr .a6 ∧ t.gpr .s7 = a.gpr .a7) ∧ HK H.D a)
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
  -- The label's hash, through its table, and `lHash`.
  refine two_seq (Ψ := Bk H.D G H f) ((hashLabelT_ct (vf := vO) (okT H.D G H f).s hH cH fH (tabL H.D G H f)
      (R := fun ac t => t.gpr .s6 = ac.1.gpr .a6 ∧ t.gpr .s7 = ac.1.gpr .a7)
      (L := fun s => s.gpr .a6) (N := fun s => (s.gpr .a7).toNat)
      (fun _ _ _ ⟨h6, h7⟩ g => ⟨(g .s6 (by decide)).trans h6, (g .s7 (by decide)).trans h7⟩)
      (fun _ p => ⟨p.1.g _ (by decide), by rw [p.1.g .a7 (by decide)]⟩)
      (fun P => ⟨by rw [P.1.hrd]; simp, (P.1.ls.sub_right (sc_sub P.1)).sub_right (sc_in (by omega)),
        P.1.kl.sub_left (cR_sub _), BitVec.isLt _⟩)
      (fun h => upd1_taint h) (fun h => lab3_taint h) (fun ac t b ⟨h6, h7⟩ => ?_) (fun ac t b ⟨_, h7⟩ => ?_)).mono
      (fun _ _ ⟨a, h₁, h₂⟩ => ⟨(a, 0), h₁.1, h₂.1⟩) fun _ _ h => h)
    (fun a t ⟨⟨⟨s, P, p, b, sy⟩, h6, h7⟩, hk⟩ => WP.mono (hashLabelT_ok P.1 hH fH P.2.2 b sy
      (by rw [h6, p.1.g _ (by decide)]) (by rw [h7, p.1.g _ (by decide)])) fun t' ⟨⟨b', _⟩, y⟩ =>
      ⟨⟨s, P, p, b', y⟩, hk⟩) ?_
  · refine WP.of_syms (wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_li (imm := 0) (by decide) fun t₂ o₂ e₂ =>
      wp_mov fun t₃ o₃ e₃ => wp_mov fun t₄ o₄ e₄ => wp_nil fun y => ?_)
    have k : Only [.a0, .a1, .a2, .a3] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    obtain ⟨s, P, p, bb, sy⟩ := b
    refine ⟨⟨s, P, p, bb.only P.1.fits k, y.trans sy⟩, ⟨by rw [k.get .s6, h6], by rw [k.get .s7, h7]⟩, ?_, ?_, ?_,
      ?_⟩
    · rw [o₄.get .a0, o₃.get .a0, o₂.get .a0, e₁, bb.s0, p.1.S]
    · rw [o₄.get .a1, o₃.get .a1, e₂]; rfl
    · rw [o₄.get .a2, e₃, o₂.get .s6, o₁.get .s6, h6]
    · rw [e₄, o₃.get .s7, o₂.get .s7, o₁.get .s7, h7, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · refine WP.of_syms (wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ =>
      wp_addi (imm := oDig) fun t₃ o₃ e₃ => wp_nil fun y => ?_)
    have k : Only [.a0, .a1, .a2] t t₃ := (o₁.trans (o₂.trans o₃)).mono
    obtain ⟨s, P, p, bb, sy⟩ := b
    refine ⟨⟨s, P, p, bb.only P.1.fits k, y.trans sy⟩, ?_, ?_, ?_⟩
    · rw [o₃.get .a0, o₂.get .a0, e₁, bb.s0, p.1.S]
    · rw [o₃.get .a1, e₂, o₁.get .s7, h7, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [e₃, o₂.get .s0, o₁.get .s0, bb.s0, p.1.S]
  refine two_seq (Ψ := Bk H.D G H f) (copyLh_taint H (pins_of X (fun _ _ h => h.1.bo) [.s0]))
    (fun a t ⟨⟨s, P, p, b, sy⟩, hk⟩ => WP.mono_syms (copyLh_ok P.1 hH rfl b) fun t' ⟨b', _⟩ y =>
      ⟨⟨s, P, p, b', y.trans sy⟩, hk⟩) ?_
  -- `DB` with MGF1 of the seed.
  let q₁ : State → Nat × Nat × Nat × Nat := fun a => (1, H.D, 1 + H.D, (a.gpr .a3).toNat - H.D - 1)
  refine two_seq (Ψ := fun a t => (MgfAT S vO (PreT H.D G H f) (PubT G H) (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1
      (q₁ a).2.2.2 a t ∧ MFit (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2) ∧ HK H.D a)
    (dbArgs_taint H (bk_pins id fun _ _ h => h.1.bo)) (fun a t ⟨⟨s, P, p, b, sy⟩, hk⟩ => ?_) ?_
  · have k2 := P.1.k2
    have ek : (a.gpr .a3).toNat = (s.gpr .a3).toNat := by rw [p.1.g .a3 (by decide)]
    refine WP.of_syms (wp_addi (imm := oEm + 1) (h := by omega) fun t₁ o₁ e₁ => wp_li (imm := H.D) (by omega)
      fun t₂ o₂ e₂ => wp_addi (imm := oEm + 1 + H.D) (h := by omega) fun t₃ o₃ e₃ =>
      wp_subi (imm := H.D + 1) (h := by omega) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
    have k₄ : Only [.s6, .s7, .s8, .s9] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    show (MgfAT S vO (PreT H.D G H f) (PubT G H) 1 H.D (1 + H.D) ((a.gpr .a3).toNat - H.D - 1) a t₄ ∧
      MFit 1 H.D (1 + H.D) ((a.gpr .a3).toNat - H.D - 1)) ∧ HK H.D a
    refine ⟨⟨⟨s, P, p, b.only P.1.fits k₄, y.trans sy, ?_, ?_, ?_, ?_⟩,
      ⟨by omega, by omega, .inl (by omega), by omega⟩⟩, hk⟩
    · rw [o₄.get .s6, o₃.get .s6, o₂.get .s6, e₁, b.s0, p.1.S, hE]
    · rw [o₄.get .s7, o₃.get .s7, e₂]
    · rw [o₄.get .s8, e₃, o₂.get .s0, o₁.get .s0, b.s0, p.1.S, hE, Nat.zero_add]
    · rw [e₄, o₃.get .s1, o₂.get .s1, o₁.get .s1, b.s1, sub_k (by omega)]; congr 1; omega
  refine two_seq (Ψ := Bk H.D G H f) ((mgf_any hG cG fG hGh hGl hGv q₁).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩) fun _ _ h => h)
    (fun a t ⟨⟨⟨s, P, p, b, sy, h6, h7, h8, h9⟩, hf⟩, hk⟩ =>
    WP.mono (mgfXorT_ok P.1.fits hG fG P.2.1 hGh hGl hGv hf b sy (by rw [h6, p.1.S]) h7 (by rw [h8, p.1.S]) h9)
      fun t' ⟨⟨b', _⟩, y⟩ => ⟨⟨s, P, p, b', y⟩, hk⟩) ?_
  -- The seed with MGF1 of `maskedDB`.
  let q₂ : State → Nat × Nat × Nat × Nat := fun a => (1 + H.D, (a.gpr .a3).toNat - H.D - 1, 1, H.D)
  refine two_seq (Ψ := fun a t => (MgfAT S vO (PreT H.D G H f) (PubT G H) (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1
      (q₂ a).2.2.2 a t ∧ MFit (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2) ∧ HK H.D a)
    (seedArgs_taint H (bk_pins id fun _ _ h => h.1.bo)) (fun a t ⟨⟨s, P, p, b, sy⟩, hk⟩ => ?_) ?_
  · have k2 := P.1.k2
    have ek : (a.gpr .a3).toNat = (s.gpr .a3).toNat := by rw [p.1.g .a3 (by decide)]
    refine WP.of_syms (wp_addi (imm := oEm + 1 + H.D) (h := by omega) fun t₁ o₁ e₁ =>
      wp_subi (imm := H.D + 1) (h := by omega) fun t₂ o₂ e₂ => wp_addi (imm := oEm + 1) (h := by omega)
      fun t₃ o₃ e₃ => wp_li (imm := H.D) (by omega) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
    have k₄ : Only [.s6, .s7, .s8, .s9] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    show (MgfAT S vO (PreT H.D G H f) (PubT G H) (1 + H.D) ((a.gpr .a3).toNat - H.D - 1) 1 H.D a t₄ ∧
      MFit (1 + H.D) ((a.gpr .a3).toNat - H.D - 1) 1 H.D) ∧ HK H.D a
    refine ⟨⟨⟨s, P, p, b.only P.1.fits k₄, y.trans sy, ?_, ?_, ?_, ?_⟩,
      ⟨by omega, by omega, .inr (by omega), by omega⟩⟩, hk⟩
    · rw [o₄.get .s6, o₃.get .s6, o₂.get .s6, e₁, b.s0, p.1.S, hE, Nat.zero_add]
    · rw [o₄.get .s7, o₃.get .s7, e₂, o₁.get .s1, b.s1, sub_k (by omega)]; congr 1; omega
    · rw [o₄.get .s8, e₃, o₂.get .s0, o₁.get .s0, b.s0, p.1.S, hE]
    · rw [e₄]
  refine two_seq (Ψ := Bk H.D G H f) ((mgf_any hG cG fG hGh hGl hGv q₂).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩) fun _ _ h => h)
    (fun a t ⟨⟨⟨s, P, p, b, sy, h6, h7, h8, h9⟩, hf⟩, hk⟩ =>
    WP.mono (mgfXorT_ok P.1.fits hG fG P.2.1 hGh hGl hGv hf b sy (by rw [h6, p.1.S]) h7 (by rw [h8, p.1.S]) h9)
      fun t' ⟨⟨b', _⟩, y⟩ => ⟨⟨s, P, p, b', y⟩, hk⟩) ?_
  -- The public-key operation.
  exact two_seq (pubArgs_taint (bk_pins id fun _ _ h => h.1.bo)) (fun a t ⟨⟨s, P, p, b, _⟩, _⟩ =>
    WP.mono (pubArgs_ok P.1 b rfl) fun t' h => ⟨s, P.1, p.1, _, h⟩) call_ct

include cH fH cG fG hGh hGl hGv in
theorem checks_ct : RelCT isa (Two fun a t => ∃ s, PreT H.D G H f s ∧ PubT G H a s ∧ Entered s t ∧ t.syms = s.syms)
    (checks H f) fun _ _ => True := by
  have hD64 := hH.hD64
  let K := fun (a : State) => (a.gpr .a3).toNat
  refine two_seq (Ψ := fun a t => ∃ s, PreT H.D G H f s ∧ PubT G H a s ∧ Entered s t ∧ t.syms = s.syms ∧
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
  refine two_seq (Ψ := fun a t => ∃ s, PreT H.D G H f s ∧ PubT G H a s ∧ Entered s t ∧ t.syms = s.syms ∧
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
theorem code_ct (hl : H.D ∈ lens) :
    RelCT isa (Two fun a s => PreT H.D G H f s ∧ PubT G H a s) (encrypt f) fun _ _ => True := by
  have hD64 := hH.hD64
  refine two_alloc (R := fun _ _ => True) ?_
  refine two_seq (Ψ := fun a t => ∃ s, PreT H.D G H f s ∧ PubT G H a s ∧ Entered s t ∧ t.syms = s.syms)
    (entry_taint fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; simp only [allocd, h₁.2.1.sp,
      h₂.2.1.sp], fun _ h => nomatch h⟩)
    (fun a u ⟨s, ⟨P, p⟩, e⟩ => by subst e; exact WP.mono_syms (entry_ok P.1) fun t E y => ⟨s, P, p, E, y⟩) ?_
  -- The label's hash function's digest length to `a0`.
  let E₀ := fun (a : State) (t : State) => ∃ s, PreT H.D G H f s ∧ PubT G H a s ∧ Entered s t ∧ t.syms = s.syms ∧
    t.gpr .a0 = BitVec.ofNat 64 H.D
  have hlen : RelCT isa (Two fun a t => ∃ s, PreT H.D G H f s ∧ PubT G H a s ∧ Entered s t ∧ t.syms = s.syms)
      (.block (lenLoad 8)) (Two E₀) := (tword_two (okT H.D G H f).s (tabL H.D G H f)
      (Φ := fun (ac : State × Nat) t => ∃ s, PreT H.D G H f s ∧ PubT G H ac.1 s ∧ Entered s t ∧ t.syms = s.syms)
      (fun _ _ ⟨s, P, p, E, y⟩ => ⟨s, P, p, E.base, y⟩) (d := .a0) (.inr (.inr rfl)) (k := 4) (by decide)
      (v := fun _ => BitVec.ofNat 64 H.D) fun P _ => P.2.2.d).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨(a, 0), h₁, h₂⟩)
      fun _ _ ⟨ac, ⟨t₁, ⟨s₁, P₁, p₁, E₁, y₁⟩, o₁, z₁, e₁⟩, ⟨t₂, ⟨s₂, P₂, p₂, E₂, y₂⟩, o₂, z₂, e₂⟩⟩ =>
        ⟨ac.1, ⟨s₁, P₁, p₁, entered_only P₁.1 E₁ o₁, z₁.trans y₁, e₁⟩, ⟨s₂, P₂, p₂, entered_only P₂.1 E₂ o₂,
          z₂.trans y₂, e₂⟩⟩
  refine RelCT.seq hlen ?_
  -- The code for that length.
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, PreT H.D G H f s ∧ PubT G H a s ∧ Saves s t)
    (byLen_ct (D := H.D) (Φ := E₀) (by omega) (fun _ _ ⟨_, _, _, _, _, h0⟩ => h0)
      (fun _ t₁ t₂ ⟨_, P₁, p₁, E₁, _⟩ ⟨_, P₂, p₂, E₂, _⟩ =>
        (E₁.base.agree ((oaepOk H.D).agree p₁.1)).1.trans (E₂.base.agree ((oaepOk H.D).agree p₂.1)).1.symm)
      (fun _ _ _ ⟨s, P, p, E, y, h0⟩ o y' => ⟨s, P, p, entered_only P.1 E o, y'.trans y, by rw [o.get .a0]; exact h0⟩)
      ?_ hl lens_certs)
    fun a t ⟨s, P, p, E, y, h0⟩ => ?_) ?_
  · rw [checks_D (G := ofLen H.D) (G' := H) rfl]
    exact (checks_ct hH cH hG cG fH fG hGh hGl hGv).mono (fun _ _ ⟨a, ⟨s₁, P₁, p₁, E₁, y₁, _⟩, ⟨s₂, P₂, p₂, E₂, y₂, _⟩⟩ =>
      ⟨a, ⟨s₁, P₁, p₁, E₁, y₁⟩, ⟨s₂, P₂, p₂, E₂, y₂⟩⟩) fun _ _ h => h
  · refine byLen_ok (D := H.D) (by omega)
      (F := fun u => Entered s u ∧ u.syms = s.syms ∧ u.gpr .a0 = BitVec.ofNat 64 H.D)
      (fun _ h => h.2.2) (fun u u' ⟨E', y', r0'⟩ o y => ⟨entered_only P.1 E' o, y.trans y',
        by rw [o.get .a0]; exact r0'⟩) ?_ hl (fun x hx => (lens_certs x hx).1) t ⟨E, y, h0⟩
    intro u ⟨E', y', _⟩
    rw [checks_D (G := ofLen H.D) (G' := H) rfl]
    exact WP.mono (checks_done hH hG fH fG hHh hHl hGh hGl hGv P.1 P.2.1 P.2.2 E' y') fun t' d => ⟨s, P, p, d.1⟩
  exact restore_taint fun a t₁ t₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
    ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.1.sp, p₂.1.sp], fun _ h => nomatch h⟩

end

end VG.Proof.RsaOaep.RISCV64

/-!
# RSAES-OAEP encryption on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Verified.lean`): the contract's public data as
`PubO`, with the tables' (`pubT_of`); constant time (`code_constantTime`,
from `code_ct`); states meeting the precondition, with both tables that of
any `w` of `vs`, at `0x300000` (`enc_sat`); and `enc_verified`.
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

/-- The contract's public data: `PubO`, the tables at the same addresses,
the tables' functions at the same addresses, and the same tables held. -/
theorem pubT_of {ts : List FnTable} {s₁ s₂ : State} (h : (encSpec ts).pub s₁ s₂) :
    PubO s₁ s₂ ∧ stackArg s₂ 9 = stackArg s₁ 9 ∧ stackArg s₂ 8 = stackArg s₁ 8 ∧
      (∀ f ∈ (ts.map (fun T : FnTable => T.fns)).flatten, s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ ts, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 8) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 8) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ ts, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 9) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 9) (FnTable.words isa s₂ T)) := by
  have e : stackBytes = 335 + 1 := rfl
  unfold encSpec at h
  rw [e] at h
  sig_pub [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs,
    stackArgs_ten, List.append_eq, List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htabL, htab, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  obtain ⟨he, hw⟩ := leak_eq (by simp [bytesAt_length, h3]) (by simp [bytesAt_length, h5]) hl
  refine ⟨⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, he.symm, hw.symm⟩, a9.symm, a8.symm,
    fun f hf => hsy f (List.mem_append_left _ hf), fun T hT => htabL _ _ rfl rfl T hT, fun T hT => htab _ _ rfl rfl T hT⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm]

theorem pubO_refl (s : State) : PubO s s := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- Constant time: the tables of the first run, which the public data makes
the second's, at the same addresses with their functions at the same
addresses. -/
theorem code_constantTime {vs : List TVar} (hc : Coh vs) :
    ConstantTime isa (encSpec (tables vs)).pre (encSpec (tables vs)).pub (encrypt (fnsOf vs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨⟨T₁, hT₁, hhL₁⟩, ⟨T, hT, hh₁⟩, hpw₁⟩ := spec_tab h₁
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨p, a9, a8, hsy, hiffL, hiff⟩ := pubT_of hp
  have hhL₂ := (hiffL _ hT₁).mp hhL₁
  have hh₂ := (hiff _ hT).mp hh₁
  have hpw₂ := (spec_tab h₂).2.2
  have hn := Proof.HashTable.RISCV64.mem_names hw
  have hnL := Proof.HashTable.RISCV64.mem_names hw₁
  have hH₁ := Proof.HashTable.RISCV64.hashAt_tableOf (Proof.HashTable.RISCV64.held_tableOf hhL₁).2.1
  have hH₂ := Proof.HashTable.RISCV64.hashAt_tableOf (Proof.HashTable.RISCV64.held_tableOf hhL₂).2.1
  have P₁ : PreO w₁.H.D s₁ := w₁.l.len ▸ preO_of h₁ hH₁
  have P₂ : PreO w₁.H.D s₂ := w₁.l.len ▸ preO_of h₂ hH₂
  have q₁ := hpw₁.sublist (List.sublist_append_left _ _)
  have q₂ := hpw₂.sublist (List.sublist_append_left _ _)
  exact code_ct w₁.l.ok w₁.l.ct w.l.ok w.l.ct w₁.l.fits w.l.fits w.l.hash w.l.len w.l.valid w₁.l.hash w₁.l.len
    w₁.l.lens_mem _ _ _ _ _ _
    ⟨s₁, ⟨⟨P₁, tabS_entry hc P₁ q₁ hw hh₁, tabS_entryL hc P₁ q₁ hw₁ hhL₁⟩, pubO_refl s₁, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl⟩,
      ⟨P₂, tabS_entry hc P₂ q₂ hw hh₂, tabS_entryL hc P₂ q₂ hw₁ hhL₂⟩, p, a9, (hsy _ hn.1).symm,
      (hsy _ hn.2.1).symm, (hsy _ hn.2.2).symm, a8, (hsy _ hnL.1).symm, (hsy _ hnL.2.1).symm,
      (hsy _ hnL.2.2).symm⟩ e₁ e₂

/-- `vg_rsa_oaep_encrypt_precomputed` against its contract, for the tables
of `vs`, given a state meeting it. -/
theorem enc_verified {vs : List TVar} (hc : Coh vs) (hsat : ∃ s, (encSpec (tables vs)).pre s) :
    Verified RISCV64.target (encrypt (fnsOf vs)) (encSpec (tables vs)) :=
  ⟨code_correct hc, code_constantTime hc, hsat⟩

/-! ## A state meeting the precondition -/

/-- A state meeting encryption's contract for a seed of `D` bytes, but for
the tables: a 512-bit modulus, a one-byte `e`, an empty label and message,
the seed, a working space of 2080 words, 16 words of `pre` at `0x5000`, the
stack arguments at `sp`, and both tables' address `0x300000`. -/
def encSatState (D : Nat) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 64 | .a4 => 0x3000 | .a5 => 1 | .a6 => 0x4000
    | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10001 then 0x41
    else bif Nat.beq a.toNat 0x10011 then 0x42 else bif Nat.beq a.toNat 0x10018 then BitVec.ofNat 8 D
    else bif Nat.beq a.toNat 0x10022 then 0x02
    else bif Nat.beq a.toNat 0x10028 then 0x20 else bif Nat.beq a.toNat 0x10029 then 0x08
    else bif Nat.beq a.toNat 0x10031 then 0x50 else bif Nat.beq a.toNat 0x10038 then 16
    else bif Nat.beq a.toNat 0x10042 then 0x30 else bif Nat.beq a.toNat 0x1004A then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x4100, 0⟩, ⟨0x4200, D⟩, ⟨0x5000, 128⟩, ⟨0x300000, 40⟩,
    ⟨0x300000, 40⟩, ⟨0x10000, 80⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 16640⟩]

section
variable {vs : List TVar} {w : TVar}

theorem stackArgAddr_sat (D j : Nat) (hj : j < 10) :
    (stackArgAddr (encSatState D) j).toNat + 8 ≤ 0x300000 := by
  revert j; show ∀ j < 10, (stackArgAddr (encSatState 0) j).toNat + 8 ≤ 0x300000; decide

theorem sat_a0 {D : Nat} (hD : D ∈ Impl.RsaOaep.RISCV64.lens) :
    stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 0 = 0x4100 :=
  (Proof.HashTable.RISCV64.withTable_below _ _ _ (stackArgAddr_sat D 0 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.RISCV64.lens, stackArg (encSatState D) 0 = 0x4100 by decide) D hD)
theorem sat_a1 {D : Nat} (hD : D ∈ Impl.RsaOaep.RISCV64.lens) :
    stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 1 = 0 :=
  (Proof.HashTable.RISCV64.withTable_below _ _ _ (stackArgAddr_sat D 1 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.RISCV64.lens, stackArg (encSatState D) 1 = 0 by decide) D hD)
theorem sat_a2 {D : Nat} (hD : D ∈ Impl.RsaOaep.RISCV64.lens) :
    stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 2 = 0x4200 :=
  (Proof.HashTable.RISCV64.withTable_below _ _ _ (stackArgAddr_sat D 2 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.RISCV64.lens, stackArg (encSatState D) 2 = 0x4200 by decide) D hD)
theorem sat_a3 {D : Nat} (hD : D ∈ Impl.RsaOaep.RISCV64.lens) :
    stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 3 = BitVec.ofNat 64 D :=
  (Proof.HashTable.RISCV64.withTable_below _ _ _ (stackArgAddr_sat D 3 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.RISCV64.lens, stackArg (encSatState D) 3 = BitVec.ofNat 64 D by decide) D hD)
theorem sat_a4 {D : Nat} (hD : D ∈ Impl.RsaOaep.RISCV64.lens) :
    stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 4 = 0x20000 :=
  (Proof.HashTable.RISCV64.withTable_below _ _ _ (stackArgAddr_sat D 4 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.RISCV64.lens, stackArg (encSatState D) 4 = 0x20000 by decide) D hD)
theorem sat_a5 {D : Nat} (hD : D ∈ Impl.RsaOaep.RISCV64.lens) :
    stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 5 = 2080 :=
  (Proof.HashTable.RISCV64.withTable_below _ _ _ (stackArgAddr_sat D 5 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.RISCV64.lens, stackArg (encSatState D) 5 = 2080 by decide) D hD)
theorem sat_a6 {D : Nat} (hD : D ∈ Impl.RsaOaep.RISCV64.lens) :
    stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 6 = 0x5000 :=
  (Proof.HashTable.RISCV64.withTable_below _ _ _ (stackArgAddr_sat D 6 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.RISCV64.lens, stackArg (encSatState D) 6 = 0x5000 by decide) D hD)
theorem sat_a7 {D : Nat} (hD : D ∈ Impl.RsaOaep.RISCV64.lens) :
    stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 7 = 16 :=
  (Proof.HashTable.RISCV64.withTable_below _ _ _ (stackArgAddr_sat D 7 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.RISCV64.lens, stackArg (encSatState D) 7 = 16 by decide) D hD)
theorem sat_a8 {D : Nat} (hD : D ∈ Impl.RsaOaep.RISCV64.lens) :
    stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 8 = 0x300000 :=
  (Proof.HashTable.RISCV64.withTable_below _ _ _ (stackArgAddr_sat D 8 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.RISCV64.lens, stackArg (encSatState D) 8 = 0x300000 by decide) D hD)
theorem sat_a9 {D : Nat} (hD : D ∈ Impl.RsaOaep.RISCV64.lens) :
    stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 9 = 0x300000 :=
  (Proof.HashTable.RISCV64.withTable_below _ _ _ (stackArgAddr_sat D 9 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.RISCV64.lens, stackArg (encSatState D) 9 = 0x300000 by decide) D hD)
theorem sat_e (D : Nat) : stackArgAddr (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 0 = 0x10000 :=
  show stackArgAddr (encSatState 0) 0 = _ by decide

/-- A state meeting the contract, with both tables that of `w`, at
`0x300000`. -/
theorem enc_sat (hw : w ∈ vs) (hl : (Proof.HashTable.RISCV64.names vs).length < 2 ^ 32) :
    ∃ s, (encSpec (tables vs)).pre s := by
  have hha : ∀ s : State, Spec.HashTable.hashAt 64 (Proof.HashTable.RISCV64.withTable s vs w).mem 0x300000 =
      some w.l.G := fun s => Proof.HashTable.RISCV64.hashAt_tableOf
        (Proof.HashTable.RISCV64.held_tableOf (Proof.HashTable.RISCV64.withTable_held s vs w)).2.1
  have hl' : w.l.G.len ∈ Impl.RsaOaep.RISCV64.lens := w.l.len ▸ w.l.lens_mem
  generalize hDd : w.l.G.len = D at hl'
  refine ⟨Proof.HashTable.RISCV64.withTable (encSatState D) vs w, ?_⟩
  have e : stackBytes = 335 + 1 := rfl
  have hha' := hha (encSatState D)
  have a0 := sat_a0 (vs := vs) (w := w) hl'
  have a1 := sat_a1 (vs := vs) (w := w) hl'
  have a2 := sat_a2 (vs := vs) (w := w) hl'
  have a3 := sat_a3 (vs := vs) (w := w) hl'
  have a4 := sat_a4 (vs := vs) (w := w) hl'
  have a5 := sat_a5 (vs := vs) (w := w) hl'
  have a6 := sat_a6 (vs := vs) (w := w) hl'
  have a7 := sat_a7 (vs := vs) (w := w) hl'
  have a8 := sat_a8 (vs := vs) (w := w) hl'
  have a9 := sat_a9 (vs := vs) (w := w) hl'
  unfold encSpec
  rw [e]
  simp only [Impl.RsaOaep.RISCV64.lens, List.mem_cons, List.not_mem_nil, or_false] at hl'
  rcases hl' with rfl | rfl | rfl | rfl | rfl
  all_goals
    sig_pre [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig, Spec.RsaOaep.seedLenOk,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
      argRegs, stackArgs_ten, List.append_eq, List.range, List.range.loop]
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, sat_e]
    sig_and_intros
    all_goals first
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
      | exact ⟨Proof.HashTable.RISCV64.tableOf w, List.mem_map_of_mem hw, Proof.HashTable.RISCV64.withTable_held _ _ _⟩
      | (intro H' hH'
         obtain rfl := Option.some.inj (hha'.symm.trans hH')
         rw [hDd]; rfl)
      | exact Proof.HashTable.symsOf_distinct2 hl
      | (simp only [Spec.Rsa.lenValid]; decide)

end

end VG.Proof.RsaOaep.RISCV64
