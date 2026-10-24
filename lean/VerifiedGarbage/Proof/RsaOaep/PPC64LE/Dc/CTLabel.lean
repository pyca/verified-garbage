module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.CTBase
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.CTBlocks
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTCalls
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Label
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE.Decrypt
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two

/-!
# RSAES-OAEP decryption on PPC64LE: the label's hash, twice

Untrusted: everything here is checked by Lean. `hashLabel_ct`: two runs of
the label's hash from states with `DX` leak alike: its blocks by the taint
analysis, its calls by `init_ct`, `upd_ct` and `fin_ct`, whose arguments
(`UpdArgs`, `FinArgs`) hold for the decoding's `Base` and so for the shared
code's (`UpdArgs.toX`, `FinArgs.toX`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two two_post wp_li wp_addi wp_mov wp_nil)

section
variable {s : State} (P : PreD s) {m : Mem} (hm : Frame [kD s, scR s] s.mem m) {rc : Nat} (hrc : rc ≤ 2)
include P hm hrc

theorem UpdArgs.toX {H : Hash} {t : State} {d : Addr} {l : Nat} (A : UpdArgs (SD s) (VD s rc) H (withMem s m) t d l) :
    PreX (bx s m rc) ∧ UpdArgs SX VX H (bx s m rc) t d l := by
  obtain ⟨pX, bX⟩ := Dec.toX P hm rc hrc A.b
  have h13 : SX (bx s m rc) = Sd s := stackArg_bx P hm rc (i := 13) (by decide)
  have e : ∀ o, off (SD s (withMem s m)) o = off (SX (bx s m rc)) o := fun o => by rw [h13]
  exact ⟨pX, pX, bX, A.h3.trans (e _), A.h5, A.h6, A.h7.trans (e _), A.hdc, by rw [← e]; exact A.hd₁,
    by rw [← e]; exact A.hd₂, A.hd₃⟩

theorem FinArgs.toX {t : State} (A : FinArgs (SD s) (VD s rc) (withMem s m) t) :
    PreX (bx s m rc) ∧ FinArgs SX VX (bx s m rc) t := by
  obtain ⟨pX, bX⟩ := Dec.toX P hm rc hrc A.b
  have h13 : SX (bx s m rc) = Sd s := stackArg_bx P hm rc (i := 13) (by decide)
  have e : ∀ o, off (SD s (withMem s m)) o = off (SX (bx s m rc)) o := fun o => by rw [h13]
  exact ⟨pX, pX, bX, A.h3.trans (e _), A.h5.trans (e _), A.h6.trans (e _)⟩

omit hrc in
theorem pubX_bx {a : State} (p : PubD a s) : PubX a (bx s m rc) :=
  ⟨p.sp, (stackArg_bx P hm rc (by decide)).trans (p.args 13 (by decide))⟩

end

/-- The label's update: its arguments. -/
def LabU (a t : State) : Prop :=
  DX a t ∧ t.gpr .r3 = off (stackArg a 13) oSt ∧ t.gpr .r4 = 0 ∧ t.gpr .r5 = stackArg a 9 ∧
    t.gpr .r6 = stackArg a 10 ∧ t.gpr .r7 = off (stackArg a 13) oW

/-- The label's finalize: its arguments. -/
def LabF (a t : State) : Prop :=
  DX a t ∧ t.gpr .r3 = off (stackArg a 13) oSt ∧ t.gpr .r4 = stackArg a 10 ∧
    t.gpr .r5 = off (stackArg a 13) oDig ∧ t.gpr .r6 = off (stackArg a 13) oW

section
variable {H : Hash} (hH : HashOK H) (cH : HashCT hH)

theorem off13 {a s : State} (p : PubD a s) (o : Nat) : off (stackArg a 13) o = off (Sd s) o := by
  show off (stackArg a 13) o = off (stackArg s 13) o
  rw [p.args 13 (by decide)]

include hH in
theorem labU_args {a t : State} (h : LabU a t) : ∃ s m, PreD s ∧ PubD a s ∧ Frame [kD s, scR s] s.mem m ∧
    UpdArgs (SD s) (VD s (rcOf (privO s))) H (withMem s m) t (stackArg s 9) (stackArg s 10).toNat := by
  obtain ⟨⟨s, m, P, p, hm, b⟩, h3, -, h5, h6, h7⟩ := h
  have F := hfits hH
  obtain ⟨_, _, _, _, _, _⟩ := offs
  have hl : lR s ∈ (withMem s m).rd := by show lR s ∈ s.rd; rw [P.hrd]; simp
  refine ⟨s, m, P, p, hm, fitsM P, b, h3.trans (off13 p _), by rw [h5, p.args 9 (by decide)],
    by rw [h6, p.args 10 (by decide)], h7.trans (off13 p _),
    Covers.left (by rw [b.rd]; exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact hl),
    (P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega)),
    (P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega)),
    P.kl.sub_left fun a ha => kR_sub a (cR_sub (withMem s m) a ha)⟩

theorem labF_args {a t : State} (h : LabF a t) : ∃ s m, PreD s ∧ PubD a s ∧ Frame [kD s, scR s] s.mem m ∧
    FinArgs (SD s) (VD s (rcOf (privO s))) (withMem s m) t := by
  obtain ⟨⟨s, m, P, p, hm, b⟩, h3, -, h5, h6⟩ := h
  exact ⟨s, m, P, p, hm, fitsM P, b, h3.trans (off13 p _), h5.trans (off13 p _), h6.trans (off13 p _)⟩

include hH cH in
theorem hashLabel_ct : RelCT isa (Two DX) (Dec.hashLabel H) fun _ _ => True := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _, _⟩ := offs
  -- `init`.
  refine two_seq (Ψ := fun a t => DX a t ∧ t.gpr .r3 = off (stackArg a 13) oSt)
    (st_taint (dx_pins (fun _ _ h => h) [])) (fun a t h => wp_addi fun t' o e => wp_nil
      ⟨h.only o, by rw [e, h.pins.2.1]⟩) ?_
  refine two_seq (Ψ := DX) (init_ct (S := SX) (vf := VX) cH fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_)
    (fun a t ⟨⟨s, m, P, p, hm, b⟩, h3⟩ => WP.mono (init_ok (fitsM P) hH b (h3.trans (off13 p _)))
      fun t' h' => ⟨s, m, P, p, hm, h'.1⟩) ?_
  · obtain ⟨⟨s₁, m₁, P₁, p₁, hm₁, b₁⟩, x3⟩ := h₁
    obtain ⟨⟨s₂, m₂, P₂, p₂, hm₂, b₂⟩, y3⟩ := h₂
    obtain ⟨f₁, c₁⟩ := toX P₁ hm₁ _ (rcOf_le _) b₁
    obtain ⟨f₂, c₂⟩ := toX P₂ hm₂ _ (rcOf_le _) b₂
    have q₁ := pubX_bx P₁ hm₁ (rc := rcOf (privO s₁)) p₁
    have q₂ := pubX_bx P₂ hm₂ (rc := rcOf (privO s₂)) p₂
    exact ⟨_, _, f₁, c₁, x3.trans (congrArg (off · oSt) q₁.2.symm), f₂, c₂,
      y3.trans (congrArg (off · oSt) q₂.2.symm), x3.trans y3.symm,
      (Base.spA okX q₁ c₁).trans (Base.spA okX q₂ c₂).symm⟩
  -- `update` with the label.
  refine two_seq (Ψ := LabU) (lab2_taint (dx_pins (fun _ _ h => h) [])) (fun a t h => ?_) ?_
  · refine wp_addi fun t₁ o₁ e₁ => wp_li (by decide) fun t₂ o₂ e₂ => wp_mov fun t₃ o₃ e₃ =>
      wp_mov fun t₄ o₄ e₄ => wp_addi fun t₅ o₅ e₅ => wp_nil ?_
    have k : Only [.r3, .r4, .r5, .r6, .r7] t t₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
    obtain ⟨-, r14, -, -, -, r18, r19⟩ := h.pins
    refine ⟨h.only k, ?_, ?_, ?_, ?_, ?_⟩
    · rw [o₅.get .r3, o₄.get .r3, o₃.get .r3, o₂.get .r3, e₁, r14]
    · rw [o₅.get .r4, o₄.get .r4, o₃.get .r4, e₂]; rfl
    · rw [o₅.get .r5, o₄.get .r5, e₃, o₂.get .r18, o₁.get .r18, r18]
    · rw [o₅.get .r6, e₄, o₃.get .r19, o₂.get .r19, o₁.get .r19, r19]
    · rw [e₅, o₄.get .r14, o₃.get .r14, o₂.get .r14, o₁.get .r14, r14]
  refine two_seq (Ψ := DX) (upd_ct (S := SX) (vf := VX) cH fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_) (fun a t h => ?_) ?_
  · obtain ⟨s₁, m₁, P₁, p₁, hm₁, A₁⟩ := labU_args hH h₁
    obtain ⟨s₂, m₂, P₂, p₂, hm₂, A₂⟩ := labU_args hH h₂
    obtain ⟨-, B₁⟩ := UpdArgs.toX P₁ hm₁ (rcOf_le _) A₁
    obtain ⟨-, B₂⟩ := UpdArgs.toX P₂ hm₂ (rcOf_le _) A₂
    refine ⟨_, _, _, _, _, _, B₁, B₂, fun r hr => ?_, (Base.spA okX (pubX_bx P₁ hm₁ (rc := rcOf (privO s₁)) p₁) B₁.b).trans
      (Base.spA okX (pubX_bx P₂ hm₂ (rc := rcOf (privO s₂)) p₂) B₂.b).symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.1.trans h₂.2.2.2.1.symm,
      h₁.2.2.2.2.1.trans h₂.2.2.2.2.1.symm, h₁.2.2.2.2.2.trans h₂.2.2.2.2.2.symm]
  · obtain ⟨s, m, P, p, hm, A⟩ := labU_args hH h
    exact WP.mono (upd_ok A.P hH A.b A.h3 A.h5 A.h6 A.h7 A.hdc A.hd₁ A.hd₂ A.hd₃) fun t' h' =>
      ⟨s, m, P, p, hm, h'.1⟩
  -- `finalize`.
  refine two_seq (Ψ := LabF) (lab3_taint (dx_pins (fun _ _ h => h) [])) (fun a t h => ?_) ?_
  · refine wp_addi fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_addi fun t₃ o₃ e₃ => wp_addi fun t₄ o₄ e₄ =>
      wp_nil ?_
    have k : Only [.r3, .r4, .r5, .r6] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    obtain ⟨-, r14, -, -, -, -, r19⟩ := h.pins
    refine ⟨h.only k, ?_, ?_, ?_, ?_⟩
    · rw [o₄.get .r3, o₃.get .r3, o₂.get .r3, e₁, r14]
    · rw [o₄.get .r4, o₃.get .r4, e₂, o₁.get .r19, r19]
    · rw [o₄.get .r5, e₃, o₂.get .r14, o₁.get .r14, r14]
    · rw [e₄, o₃.get .r14, o₂.get .r14, o₁.get .r14, r14]
  refine fin_ct (S := SX) (vf := VX) cH fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_
  obtain ⟨s₁, m₁, P₁, p₁, hm₁, A₁⟩ := labF_args h₁
  obtain ⟨s₂, m₂, P₂, p₂, hm₂, A₂⟩ := labF_args h₂
  obtain ⟨-, B₁⟩ := FinArgs.toX P₁ hm₁ (rcOf_le _) A₁
  obtain ⟨-, B₂⟩ := FinArgs.toX P₂ hm₂ (rcOf_le _) A₂
  refine ⟨_, _, B₁, B₂, fun r hr => ?_, (Base.spA okX (pubX_bx P₁ hm₁ (rc := rcOf (privO s₁)) p₁) B₁.b).trans
    (Base.spA okX (pubX_bx P₂ hm₂ (rc := rcOf (privO s₂)) p₂) B₂.b).symm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.1.trans h₂.2.2.2.1.symm,
    h₁.2.2.2.2.trans h₂.2.2.2.2.symm]

include hH in
/-- The label's hash keeps `DX`. -/
theorem hashLabel_dx {a t : State} (h : DX a t) : WP isa (Dec.hashLabel H) t (DX a) :=
  let ⟨s, m, P, p, hm, b⟩ := h
  WP.mono (hashLabel_ok P hH b) fun _ h' => ⟨s, m, P, p, hm, h'.1⟩

end

end VG.Proof.RsaOaep.PPC64LE.Dec
