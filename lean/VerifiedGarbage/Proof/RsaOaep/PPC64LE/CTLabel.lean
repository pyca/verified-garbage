module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBase
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Label
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Pre

/-!
# RSAES-OAEP encryption on PPC64LE: two runs, and the label's hash

Untrusted: everything here is checked by Lean. Two runs are compared through
an anchor `a`, a state with their public data (`PubO`): the pointers and
lengths, `e`'s bytes and the precomputed values; `BO D a t`: `t` has `Base`
from an entry state with `a`'s public data (`B`, `Proof/RsaOaep/PPC64LE/CTBase.lean`,
with `oaepOk`). `hashLabel_ct`: the
label's hash, its blocks by the taint analysis and its calls by
`init_ct`, `upd_ct`, `fin_ct`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo Two Pins two_post wp_li wp_addi wp_mov wp_nil)

/-- The public data of an entry state `s` is the anchor `a`'s. -/
structure PubO (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], s.gpr r = a.gpr r
  args : ∀ i < 7, stackArg s i = stackArg a i
  e : Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r7) (a.gpr .r8).toNat
  w : Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 5) (stackArg a 6).toNat

theorem PubO.S {a s : State} (p : PubO a s) : S s = stackArg a 3 := p.args 3 (by decide)
theorem PubO.a3 {a s : State} (p : PubO a s) : stackArg s 3 = stackArg a 3 := p.args 3 (by decide)

/-- `PubO` gives what the shared code needs. -/
theorem oaepOk (D : Nat) : Ok S vO (PreO D) PubO where
  fits P := P.fits
  agree {a s} p := ⟨p.sp, p.S, fun r hr => by
    simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [vO]
    · exact p.g _ (by decide)
    · exact p.g _ (by decide)
    · exact p.g _ (by decide)
    · exact p.g _ (by decide)
    · exact p.g _ (by decide)
    · exact p.g _ (by decide)
    · exact p.args 5 (by decide)
    · exact p.args 6 (by decide)
    · exact p.args 4 (by decide)⟩

/-- `t` has `Base` from an entry state with `a`'s public data. -/
abbrev BO (D : Nat) : State → State → Prop := B S vO (PreO D) PubO

section
variable {H : Hash} (hH : HashOK H) (cH : HashCT hH)

/-- The label's update: its arguments. -/
def LabU (H : Hash) (a t : State) : Prop :=
  BO H.D a t ∧ t.gpr .r3 = off (stackArg a 3) oSt ∧ t.gpr .r4 = 0 ∧ t.gpr .r5 = a.gpr .r9 ∧
    t.gpr .r6 = a.gpr .r10 ∧ t.gpr .r7 = off (stackArg a 3) oW

/-- The label's finalize: its arguments. -/
def LabF (H : Hash) (a t : State) : Prop :=
  BO H.D a t ∧ t.gpr .r3 = off (stackArg a 3) oSt ∧ t.gpr .r4 = a.gpr .r10 ∧
    t.gpr .r5 = off (stackArg a 3) oDig ∧ t.gpr .r6 = off (stackArg a 3) oW

include hH in
theorem lab_args {a t : State} (h : LabU H a t) :
    ∃ s, PreO H.D s ∧ UpdArgs S vO H s t (s.gpr .r9) (s.gpr .r10).toNat ∧ PubO a s := by
  obtain ⟨⟨s, P, p, b⟩, h3, -, h5, h6, h7⟩ := h
  have F := hfits hH
  obtain ⟨_, _, _, _, _, _⟩ := offs
  have hl : lR s ∈ s.rd := by rw [P.hrd]; simp
  have hc : Covers [lR s] (t.rd ++ t.wr) :=
    Covers.left (by rw [b.rd]; exact Covers.of_mem fun r hr => (List.mem_singleton.mp hr) ▸ hl)
  refine ⟨s, P, ⟨P.fits, b, by rw [h3, p.S], by rw [h5, p.g _ (by decide)], by rw [h6, p.g _ (by decide)],
    by rw [h7, p.S], hc,
    (P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega)),
    (P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega)), P.kl.sub_left (cR_sub s)⟩, p⟩

include cH in
theorem hashLabel_ct : RelCT isa (Two (BO H.D)) (hashLabel H) fun _ _ => True := by
  refine two_seq (st_taint (pins_of (oaepOk H.D) (fun _ _ h => h) [])) (fun a t h => st_wp (oaepOk H.D) h) ?_
  refine two_seq (init_two (oaepOk H.D) hH cH fun _ _ h => h) (fun a t h => init_wp (oaepOk H.D) hH h.1 h.2) ?_
  refine two_seq (Ψ := LabU H) (lab2_taint (pins_of (oaepOk H.D) (fun _ _ h => h) [])) (fun a t h => ?_) ?_
  · obtain ⟨s, P, p, b⟩ := h
    refine wp_addi fun t₁ o₁ e₁ => wp_li (by decide) fun t₂ o₂ e₂ => wp_mov fun t₃ o₃ e₃ =>
      wp_mov fun t₄ o₄ e₄ => wp_addi fun t₅ o₅ e₅ => wp_nil ?_
    have k : Only [.r3, .r4, .r5, .r6, .r7] t t₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
    refine ⟨⟨s, P, p, b.only P.fits k⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [o₅.get .r3, o₄.get .r3, o₃.get .r3, o₂.get .r3, e₁, b.r14, p.S]
    · rw [o₅.get .r4, o₄.get .r4, o₃.get .r4, e₂]; rfl
    · rw [o₅.get .r5, o₄.get .r5, e₃, o₂.get .r19, o₁.get .r19, b.r19, p.g _ (by decide)]
    · rw [o₅.get .r6, e₄, o₃.get .r20, o₂.get .r20, o₁.get .r20, b.r20, p.g _ (by decide)]
    · rw [e₅, o₄.get .r14, o₃.get .r14, o₂.get .r14, o₁.get .r14, b.r14, p.S]
  refine two_seq (Ψ := BO H.D) (upd_ct (S := S) (vf := vO) cH fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_) (fun a t h => ?_) ?_
  · obtain ⟨s₁, -, A₁, p₁⟩ := lab_args hH h₁
    obtain ⟨s₂, -, A₂, p₂⟩ := lab_args hH h₂
    refine ⟨s₁, s₂, _, _, _, _, A₁, A₂, fun r hr => ?_, (A₁.b.agree ((oaepOk H.D).agree p₁)).1.trans (A₂.b.agree ((oaepOk H.D).agree p₂)).1.symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.1.trans h₂.2.2.2.1.symm,
      h₁.2.2.2.2.1.trans h₂.2.2.2.2.1.symm, h₁.2.2.2.2.2.trans h₂.2.2.2.2.2.symm]
  · obtain ⟨s, P, A, p⟩ := lab_args hH h
    exact WP.mono (upd_ok A.P hH A.b A.h3 A.h5 A.h6 A.h7 A.hdc A.hd₁ A.hd₂ A.hd₃) fun t' ⟨b', _⟩ =>
      ⟨s, P, p, b'⟩
  refine two_seq (Ψ := LabF H) (lab3_taint (pins_of (oaepOk H.D) (fun _ _ h => h) [])) (fun a t h => ?_) ?_
  · obtain ⟨s, P, p, b⟩ := h
    refine wp_addi fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_addi fun t₃ o₃ e₃ => wp_addi fun t₄ o₄ e₄ =>
      wp_nil ?_
    have k : Only [.r3, .r4, .r5, .r6] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    refine ⟨⟨s, P, p, b.only P.fits k⟩, ?_, ?_, ?_, ?_⟩
    · rw [o₄.get .r3, o₃.get .r3, o₂.get .r3, e₁, b.r14, p.S]
    · rw [o₄.get .r4, o₃.get .r4, e₂, o₁.get .r20, b.r20, p.g _ (by decide)]
    · rw [o₄.get .r5, e₃, o₂.get .r14, o₁.get .r14, b.r14, p.S]
    · rw [e₄, o₃.get .r14, o₂.get .r14, o₁.get .r14, b.r14, p.S]
  refine fin_ct (S := S) (vf := vO) cH fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_
  obtain ⟨⟨s₁, P₁, p₁, b₁⟩, x3, x4, x5, x6⟩ := h₁
  obtain ⟨⟨s₂, P₂, p₂, b₂⟩, y3, y4, y5, y6⟩ := h₂
  refine ⟨s₁, s₂, ⟨P₁.fits, b₁, by rw [x3, p₁.S], by rw [x5, p₁.S], by rw [x6, p₁.S]⟩,
    ⟨P₂.fits, b₂, by rw [y3, p₂.S], by rw [y5, p₂.S], by rw [y6, p₂.S]⟩, fun r hr => ?_,
    (b₁.agree ((oaepOk H.D).agree p₁)).1.trans (b₂.agree ((oaepOk H.D).agree p₂)).1.symm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [x3.trans y3.symm, x4.trans y4.symm, x5.trans y5.symm, x6.trans y6.symm]

end

end VG.Proof.RsaOaep.PPC64LE
