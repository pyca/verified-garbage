module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTCalls
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Label
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base

/-!
# RSAES-OAEP encryption on PPC64LE: two runs, and the label's hash

Untrusted: everything here is checked by Lean. Two runs are compared through
an anchor `a`, a state with their public data (`PubO`): the pointers and
lengths, `e`'s bytes and the precomputed values. `B a t`: `t` has `Base`
from an entry state with `a`'s public data, so that the registers `Base`
fixes hold `a`'s values (`B.fx`). `two_seq`: a piece checked for both runs,
then what each run satisfies after it by correctness. `hashLabel_ct`: the
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

/-- `t` has `Base` from an entry state with `a`'s public data. -/
def B (D : Nat) (a t : State) : Prop := ∃ s, PreO D s ∧ PubO a s ∧ Base s t

/-- What `Base` fixes, from the anchor. -/
def fxv (a : State) : Reg → BitVec 64
  | .r14 => stackArg a 3
  | .r15 => a.gpr .r6
  | .r16 => a.gpr .r3
  | .r17 => a.gpr .r7
  | .r18 => a.gpr .r8
  | .r19 => a.gpr .r9
  | .r20 => a.gpr .r10
  | .r21 => stackArg a 5
  | .r22 => stackArg a 6
  | .r23 => stackArg a 4
  | _ => 0

theorem Base.fx {a s t : State} (p : PubO a s) (h : Base s t) :
    t.sp = fb a ∧ ∀ r ∈ fx, t.gpr r = fxv a r := by
  refine ⟨by rw [h.sp, fb, fb, p.sp], fun r hr => ?_⟩
  have hr' : r = .r14 ∨ r = .r15 ∨ r = .r16 ∨ r = .r17 ∨ r = .r18 ∨ r = .r19 ∨ r = .r20 ∨ r = .r21 ∨
      r = .r22 ∨ r = .r23 := by
    revert r; decide
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.r14, p.args 3 (by decide)]; rfl
  · rw [h.r15, p.g _ (by decide)]; rfl
  · rw [h.r16, p.g _ (by decide)]; rfl
  · rw [h.r17, p.g _ (by decide)]; rfl
  · rw [h.r18, p.g _ (by decide)]; rfl
  · rw [h.r19, p.g _ (by decide)]; rfl
  · rw [h.r20, p.g _ (by decide)]; rfl
  · rw [h.r21, p.args 5 (by decide)]; rfl
  · rw [h.r22, p.args 6 (by decide)]; rfl
  · rw [h.r23, p.args 4 (by decide)]; rfl

theorem PubO.S {a s : State} (p : PubO a s) : S s = stackArg a 3 := p.args 3 (by decide)
theorem PubO.a3 {a s : State} (p : PubO a s) : stackArg s 3 = stackArg a 3 := p.args 3 (by decide)

/-- Pins of states with `B` and more. -/
theorem pins_of {D : Nat} {Φ : State → State → Prop} (h : ∀ a t, Φ a t → B D a t) (rs : List Reg)
    (hrs : ∀ r ∈ rs, r ∈ fx := by decide) : Pins Φ rs := fun a t₁ t₂ h₁ h₂ => by
  obtain ⟨_, -, p₁, b₁⟩ := h a t₁ h₁
  obtain ⟨_, -, p₂, b₂⟩ := h a t₂ h₂
  have f₁ := b₁.fx p₁
  have f₂ := b₂.fx p₂
  exact ⟨f₁.1.trans f₂.1.symm, fun r hr => (f₁.2 r (hrs r hr)).trans (f₂.2 r (hrs r hr)).symm⟩

/-- A piece of code checked for both runs, then the rest from what each run
satisfies after it. -/
theorem two_seq {α : Type} {Φ Ψ : α → State → Prop} {R : State → State → Prop} {c₁ c₂ : Prog isa}
    (h₁ : RelCT isa (Two Φ) c₁ fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c₁ s (Ψ a))
    (h₂ : RelCT isa (Two Ψ) c₂ R) : RelCT isa (Two Φ) (.seq c₁ c₂) R :=
  RelCT.seq (two_post h₁ hw) h₂

section
variable {H : Hash} (hH : HashOK H) (cH : HashCT hH)

/-- The label's update: its arguments. -/
def LabU (H : Hash) (a t : State) : Prop :=
  B H.D a t ∧ t.gpr .r3 = off (stackArg a 3) oSt ∧ t.gpr .r4 = 0 ∧ t.gpr .r5 = a.gpr .r9 ∧
    t.gpr .r6 = a.gpr .r10 ∧ t.gpr .r7 = off (stackArg a 3) oW

/-- The label's finalize: its arguments. -/
def LabF (H : Hash) (a t : State) : Prop :=
  B H.D a t ∧ t.gpr .r3 = off (stackArg a 3) oSt ∧ t.gpr .r4 = a.gpr .r10 ∧
    t.gpr .r5 = off (stackArg a 3) oDig ∧ t.gpr .r6 = off (stackArg a 3) oW

theorem st_wp {D : Nat} {a t : State} (h : B D a t) :
    WP isa (.block [.addi .r3 .r14 oSt]) t fun t' => B D a t' ∧ t'.gpr .r3 = off (stackArg a 3) oSt := by
  obtain ⟨s, P, p, b⟩ := h
  exact wp_addi fun t' o e => wp_nil ⟨⟨s, P, p, b.only P o⟩, by rw [e, b.r14, p.a3]⟩

include cH in
theorem init_two {D : Nat} {Φ : State → State → Prop}
    (h : ∀ a t, Φ a t → B D a t ∧ t.gpr .r3 = off (stackArg a 3) oSt) :
    RelCT isa (Two Φ) H.callInit fun _ _ => True :=
  init_ct (D := D) cH fun t₁ t₂ ⟨a, h₁, h₂⟩ => by
    obtain ⟨⟨s₁, P₁, p₁, b₁⟩, e₁⟩ := h a t₁ h₁
    obtain ⟨⟨s₂, P₂, p₂, b₂⟩, e₂⟩ := h a t₂ h₂
    exact ⟨s₁, s₂, P₁, b₁, by rw [e₁, p₁.S], P₂, b₂, by rw [e₂, p₂.S], e₁.trans e₂.symm,
      (b₁.fx p₁).1.trans (b₂.fx p₂).1.symm⟩

include hH in
theorem init_wp {D : Nat} {a t : State} (h : B D a t) (h3 : t.gpr .r3 = off (stackArg a 3) oSt) :
    WP isa H.callInit t (B D a) := by
  obtain ⟨s, P, p, b⟩ := h
  exact WP.mono (init_ok P hH b (by rw [h3, p.S])) fun t' ⟨b', _⟩ => ⟨s, P, p, b'⟩

include hH in
theorem lab_args {a t : State} (h : LabU H a t) :
    ∃ s, UpdArgs H.D H s t (s.gpr .r9) (s.gpr .r10).toNat ∧ PubO a s := by
  obtain ⟨⟨s, P, p, b⟩, h3, -, h5, h6, h7⟩ := h
  have F := hfits hH
  obtain ⟨_, _, _, _, _, _⟩ := offs
  have hl : lR s ∈ s.rd := by rw [P.hrd]; simp
  have hc : Covers [lR s] (t.rd ++ t.wr) :=
    Covers.left (by rw [b.rd]; exact Covers.of_mem fun r hr => (List.mem_singleton.mp hr) ▸ hl)
  refine ⟨s, ⟨P, b, by rw [h3, p.S], by rw [h5, p.g _ (by decide)], by rw [h6, p.g _ (by decide)],
    by rw [h7, p.S], hc,
    (P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega)),
    (P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega)), P.kl.sub_left (cR_sub s)⟩, p⟩

include cH in
theorem hashLabel_ct : RelCT isa (Two (B H.D)) (hashLabel H) fun _ _ => True := by
  refine two_seq (st_taint (pins_of (fun _ _ h => h) [])) (fun a t h => st_wp h) ?_
  refine two_seq (init_two hH cH fun _ _ h => h) (fun a t h => init_wp hH h.1 h.2) ?_
  refine two_seq (Ψ := LabU H) (lab2_taint (pins_of (fun _ _ h => h) [])) (fun a t h => ?_) ?_
  · obtain ⟨s, P, p, b⟩ := h
    refine wp_addi fun t₁ o₁ e₁ => wp_li (by decide) fun t₂ o₂ e₂ => wp_mov fun t₃ o₃ e₃ =>
      wp_mov fun t₄ o₄ e₄ => wp_addi fun t₅ o₅ e₅ => wp_nil ?_
    have k : Only [.r3, .r4, .r5, .r6, .r7] t t₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
    refine ⟨⟨s, P, p, b.only P k⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [o₅.get .r3, o₄.get .r3, o₃.get .r3, o₂.get .r3, e₁, b.r14, p.a3]
    · rw [o₅.get .r4, o₄.get .r4, o₃.get .r4, e₂]; rfl
    · rw [o₅.get .r5, o₄.get .r5, e₃, o₂.get .r19, o₁.get .r19, b.r19, p.g _ (by decide)]
    · rw [o₅.get .r6, e₄, o₃.get .r20, o₂.get .r20, o₁.get .r20, b.r20, p.g _ (by decide)]
    · rw [e₅, o₄.get .r14, o₃.get .r14, o₂.get .r14, o₁.get .r14, b.r14, p.a3]
  refine two_seq (Ψ := B H.D) (upd_ct (D := H.D) cH fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_) (fun a t h => ?_) ?_
  · obtain ⟨s₁, A₁, p₁⟩ := lab_args hH h₁
    obtain ⟨s₂, A₂, p₂⟩ := lab_args hH h₂
    refine ⟨s₁, s₂, _, _, _, _, A₁, A₂, fun r hr => ?_, (A₁.b.fx p₁).1.trans (A₂.b.fx p₂).1.symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.1.trans h₂.2.2.2.1.symm,
      h₁.2.2.2.2.1.trans h₂.2.2.2.2.1.symm, h₁.2.2.2.2.2.trans h₂.2.2.2.2.2.symm]
  · obtain ⟨s, A, p⟩ := lab_args hH h
    exact WP.mono (upd_ok A.P hH A.b A.h3 A.h5 A.h6 A.h7 A.hdc A.hd₁ A.hd₂ A.hd₃) fun t' ⟨b', _⟩ =>
      ⟨s, A.P, p, b'⟩
  refine two_seq (Ψ := LabF H) (lab3_taint (pins_of (fun _ _ h => h) [])) (fun a t h => ?_) ?_
  · obtain ⟨s, P, p, b⟩ := h
    refine wp_addi fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_addi fun t₃ o₃ e₃ => wp_addi fun t₄ o₄ e₄ =>
      wp_nil ?_
    have k : Only [.r3, .r4, .r5, .r6] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    refine ⟨⟨s, P, p, b.only P k⟩, ?_, ?_, ?_, ?_⟩
    · rw [o₄.get .r3, o₃.get .r3, o₂.get .r3, e₁, b.r14, p.a3]
    · rw [o₄.get .r4, o₃.get .r4, e₂, o₁.get .r20, b.r20, p.g _ (by decide)]
    · rw [o₄.get .r5, e₃, o₂.get .r14, o₁.get .r14, b.r14, p.a3]
    · rw [e₄, o₃.get .r14, o₂.get .r14, o₁.get .r14, b.r14, p.a3]
  refine fin_ct (D := H.D) cH fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_
  obtain ⟨⟨s₁, P₁, p₁, b₁⟩, x3, x4, x5, x6⟩ := h₁
  obtain ⟨⟨s₂, P₂, p₂, b₂⟩, y3, y4, y5, y6⟩ := h₂
  refine ⟨s₁, s₂, ⟨P₁, b₁, by rw [x3, p₁.S], by rw [x5, p₁.S], by rw [x6, p₁.S]⟩,
    ⟨P₂, b₂, by rw [y3, p₂.S], by rw [y5, p₂.S], by rw [y6, p₂.S]⟩, fun r hr => ?_,
    (b₁.fx p₁).1.trans (b₂.fx p₂).1.symm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [x3.trans y3.symm, x4.trans y4.symm, x5.trans y5.symm, x6.trans y6.symm]

end

end VG.Proof.RsaOaep.PPC64LE
