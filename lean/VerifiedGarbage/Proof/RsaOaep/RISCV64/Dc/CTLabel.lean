module

-- separate module: it builds in parallel with `CTPriv` and the proofs of correctness, which `Verified` also needs.

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.CTBase
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.CTBlocks
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Label
import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.RsaOaep.RISCV64.Decrypt
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two

/-!
# RSAES-OAEP decryption on RISC-V: the label's hash, twice

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/CTLabel.lean`): `hashLabel_ct`, two runs of the
label's hash from states with `DX` leak alike: its blocks by the taint
analysis, its calls by `init_ct`, `upd_ct` and `fin_ct`, whose arguments
(`UpdArgs`, `FinArgs`) hold for the decoding's `Base` and so for the shared
code's (`UpdArgs.toX`, `FinArgs.toX`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Two two_post wp_li wp_addi wp_addSp wp_mov wp_nil)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off offs hfits UpdArgs FinArgs HashCT init_ct upd_ct fin_ct init_ok
  upd_ok fin_ok two_seq st_taint sc_in cR_sub)

section
variable {s : State} (P : PreD s) {m : Mem} (hm : Frame [kD s, scR s] s.mem m) {rc : Nat} (hrc : rc ≤ 2)
include P hm hrc

theorem UpdArgs.toX {H : Hash} {t : State} {d : Addr} {l : Nat}
    (A : UpdArgs (SD s) (VD s rc) H (withMem s m) t d l) :
    PreX (bx s m rc) ∧ UpdArgs SX VX H (bx s m rc) t d l := by
  obtain ⟨pX, bX⟩ := Dec.toX P hm rc hrc A.b
  have h13 : SX (bx s m rc) = Sd s := stackArg_bx P hm rc (i := 13) (by decide)
  have e : ∀ o, off (SD s (withMem s m)) o = off (SX (bx s m rc)) o := fun o => by rw [h13]
  exact ⟨pX, pX, bX, A.h0.trans (e _), A.h2, A.h3, A.hdc, by rw [← e]; exact A.hd₁, A.hd₃⟩

theorem FinArgs.toX {t : State} (A : FinArgs (SD s) (VD s rc) (withMem s m) t) :
    PreX (bx s m rc) ∧ FinArgs SX VX (bx s m rc) t := by
  obtain ⟨pX, bX⟩ := Dec.toX P hm rc hrc A.b
  have h13 : SX (bx s m rc) = Sd s := stackArg_bx P hm rc (i := 13) (by decide)
  have e : ∀ o, off (SD s (withMem s m)) o = off (SX (bx s m rc)) o := fun o => by rw [h13]
  exact ⟨pX, pX, bX, A.h0.trans (e _), A.h2.trans (e _)⟩

omit hrc in
theorem pubX_bx {a : State} (p : PubD a s) : PubX a (bx s m rc) :=
  ⟨p.sp, (stackArg_bx P hm rc (by decide)).trans (p.args 13 (by decide))⟩

end

/-- The label's update: its arguments. -/
def LabU (a t : State) : Prop :=
  DX a t ∧ t.gpr .a0 = off (stackArg a 13) oSt ∧ t.gpr .a1 = 0 ∧ t.gpr .a2 = stackArg a 9 ∧
    t.gpr .a3 = stackArg a 10

/-- The label's finalize: its arguments. -/
def LabF (a t : State) : Prop :=
  DX a t ∧ t.gpr .a0 = off (stackArg a 13) oSt ∧ t.gpr .a1 = stackArg a 10 ∧
    t.gpr .a2 = off (stackArg a 13) oDig

theorem off13 {a s : State} (p : PubD a s) (o : Nat) : off (stackArg a 13) o = off (Sd s) o := by
  show off (stackArg a 13) o = off (stackArg s 13) o
  rw [p.args 13 (by decide)]

section
variable {H : Hash} (hH : HashOK H) (cH : HashCT hH) (hF : H.F ≤ 208)

include hH in
theorem labU_args {a t : State} (h : LabU a t) : ∃ s m, PreD s ∧ PubD a s ∧ Frame [kD s, scR s] s.mem m ∧
    UpdArgs (SD s) (VD s (rcOf (privO s))) H (withMem s m) t (stackArg s 9) (stackArg s 10).toNat := by
  obtain ⟨⟨s, m, P, p, hm, b⟩, h0, -, h2, h3⟩ := h
  have F := hfits hH
  obtain ⟨_, _, _, _, _⟩ := offs
  have hl : lR s ∈ (withMem s m).rd := by show lR s ∈ s.rd; rw [P.hrd]; simp
  refine ⟨s, m, P, p, hm, fits P rfl rfl, b, h0.trans (off13 p _), by rw [h2, p.args 9 (by decide)],
    by rw [h3, p.args 10 (by decide)],
    Covers.left (by rw [b.rd]; exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact hl),
    (P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega)),
    P.kl.sub_left fun a ha => kR_sub a (cR_sub (withMem s m) a ha)⟩

theorem labF_args {a t : State} (h : LabF a t) : ∃ s m, PreD s ∧ PubD a s ∧ Frame [kD s, scR s] s.mem m ∧
    FinArgs (SD s) (VD s (rcOf (privO s))) (withMem s m) t := by
  obtain ⟨⟨s, m, P, p, hm, b⟩, h0, -, h2⟩ := h
  exact ⟨s, m, P, p, hm, fits P rfl rfl, b, h0.trans (off13 p _), h2.trans (off13 p _)⟩

/-- `s0 + d`, from `DX`. -/
theorem s0_off {a t : State} (h : DX a t) (d : Nat) : t.gpr .s0 + BitVec.ofNat 64 d = off (stackArg a 13) d := by
  rw [h.pins.2.1]

include hH cH hF in
theorem hashLabel_ct : RelCT isa (Two DX) (Dec.hashLabel H) fun _ _ => True := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _⟩ := offs
  -- `init`.
  refine two_seq (Ψ := fun a t => DX a t ∧ t.gpr .a0 = off (stackArg a 13) oSt)
    (st_taint (dx_pins (fun _ _ h => h) [])) (fun a t h => wp_addi (imm := oSt) fun t' o e => wp_nil
      ⟨h.only o, by rw [e, s0_off h]⟩) ?_
  refine two_seq (Ψ := DX) (init_ct (S := SX) (vf := VX) cH fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_)
    (fun a t ⟨⟨s, m, P, p, hm, b⟩, h0⟩ => WP.mono (init_ok (fits P (s' := withMem s m) rfl rfl) hH hF b (h0.trans (off13 p _)))
      fun t' h' => ⟨s, m, P, p, hm, h'.1⟩) ?_
  · obtain ⟨⟨s₁, m₁, P₁, p₁, hm₁, b₁⟩, x0⟩ := h₁
    obtain ⟨⟨s₂, m₂, P₂, p₂, hm₂, b₂⟩, y0⟩ := h₂
    obtain ⟨f₁, c₁⟩ := toX P₁ hm₁ _ (rcOf_le _) b₁
    obtain ⟨f₂, c₂⟩ := toX P₂ hm₂ _ (rcOf_le _) b₂
    have q₁ := pubX_bx P₁ hm₁ (rc := rcOf (privO s₁)) p₁
    have q₂ := pubX_bx P₂ hm₂ (rc := rcOf (privO s₂)) p₂
    exact ⟨_, _, f₁, c₁, x0.trans (congrArg (off · oSt) q₁.2.symm), f₂, c₂,
      y0.trans (congrArg (off · oSt) q₂.2.symm), x0.trans y0.symm,
      (Proof.RsaOaep.RISCV64.Base.spA okX q₁ c₁).trans (Proof.RsaOaep.RISCV64.Base.spA okX q₂ c₂).symm⟩
  -- `update` with the label.
  refine two_seq (Ψ := LabU) (lab2_taint (dx_pins (fun _ _ h => h) [])) (fun a t h => ?_) ?_
  · obtain ⟨s, m, P, p, hm, b⟩ := h
    unfold argBase
    refine wp_addSp (imm := frameBytes) (fun t₁ o₁ e₁ => wp_addi (imm := oSt) fun t₂ o₂ e₂ =>
      wp_li (imm := 0) (by decide) fun t₃ o₃ e₃ => ?_) (by decide)
    have K₃ : Only [.t6, .a0, .a1] t t₃ := (o₁.trans (o₂.trans o₃)).mono
    have g6 : t₃.gpr .t6 = s.sp := by rw [o₃.get .t6, o₂.get .t6, e₁, b.sv.sp, BitVec.sub_add_cancel]
    refine wp_argB P hm (j := 9) (by decide) g6 (K₃.rd.trans b.rd) (by rw [K₃.mem]; exact b.mem)
      fun t₄ o₄ e₄ => wp_argB P hm (j := 10) (by decide) (by rw [o₄.get .t6, g6])
        ((o₄.rd.trans K₃.rd).trans b.rd) (by rw [o₄.mem, K₃.mem]; exact b.mem) fun t₅ o₅ e₅ => wp_nil ?_
    have k : Only [.t6, .a0, .a1, .a2, .a3] t t₅ := (K₃.trans (o₄.trans o₅)).mono
    refine ⟨⟨s, m, P, p, hm, b.only (fits P rfl rfl) k⟩, ?_, ?_, ?_, ?_⟩
    · rw [o₅.get .a0, o₄.get .a0, o₃.get .a0, e₂, o₁.get .s0]
      exact congrArg (off · oSt) (b.s0.trans (p.args 13 (by decide)))
    · rw [o₅.get .a1, o₄.get .a1, e₃]; rfl
    · rw [o₅.get .a2, e₄, p.args 9 (by decide)]
    · rw [e₅, p.args 10 (by decide)]
  refine two_seq (Ψ := DX) (upd_ct (S := SX) (vf := VX) cH hF fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_) (fun a t h => ?_) ?_
  · obtain ⟨s₁, m₁, P₁, p₁, hm₁, A₁⟩ := labU_args hH h₁
    obtain ⟨s₂, m₂, P₂, p₂, hm₂, A₂⟩ := labU_args hH h₂
    obtain ⟨-, B₁⟩ := UpdArgs.toX P₁ hm₁ (rcOf_le _) A₁
    obtain ⟨-, B₂⟩ := UpdArgs.toX P₂ hm₂ (rcOf_le _) A₂
    refine ⟨_, _, _, _, _, _, B₁, B₂, fun r hr => ?_,
      (Proof.RsaOaep.RISCV64.Base.spA okX (pubX_bx P₁ hm₁ (rc := rcOf (privO s₁)) p₁) B₁.b).trans
      (Proof.RsaOaep.RISCV64.Base.spA okX (pubX_bx P₂ hm₂ (rc := rcOf (privO s₂)) p₂) B₂.b).symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.1.trans h₂.2.2.2.1.symm,
      h₁.2.2.2.2.trans h₂.2.2.2.2.symm]
  · obtain ⟨s, m, P, p, hm, A⟩ := labU_args hH h
    exact WP.mono (upd_ok A.P hH hF A.b A.h0 A.h2 A.h3 A.hdc A.hd₁ A.hd₃) fun t' h' =>
      ⟨s, m, P, p, hm, h'.1⟩
  -- `finalize`.
  refine two_seq (Ψ := LabF) (lab3_taint (dx_pins (fun _ _ h => h) [])) (fun a t h => ?_) ?_
  · obtain ⟨s, m, P, p, hm, b⟩ := h
    unfold argBase
    refine wp_addSp (imm := frameBytes) (fun t₁ o₁ e₁ => wp_addi (imm := oSt) fun t₂ o₂ e₂ => ?_) (by decide)
    have g6 : t₂.gpr .t6 = s.sp := by rw [o₂.get .t6, e₁, b.sv.sp, BitVec.sub_add_cancel]
    refine wp_argB P hm (j := 10) (by decide) g6 ((o₂.rd.trans o₁.rd).trans b.rd)
      (by rw [o₂.mem, o₁.mem]; exact b.mem) fun t₃ o₃ e₃ => wp_addi (imm := oDig) fun t₄ o₄ e₄ => wp_nil ?_
    have k : Only [.t6, .a0, .a1, .a2] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    refine ⟨⟨s, m, P, p, hm, b.only (fits P rfl rfl) k⟩, ?_, ?_, ?_⟩
    · rw [o₄.get .a0, o₃.get .a0, e₂, o₁.get .s0]
      exact congrArg (off · oSt) (b.s0.trans (p.args 13 (by decide)))
    · rw [o₄.get .a1, e₃, p.args 10 (by decide)]
    · rw [e₄, o₃.get .s0, o₂.get .s0, o₁.get .s0]
      exact congrArg (off · oDig) (b.s0.trans (p.args 13 (by decide)))
  refine fin_ct (S := SX) (vf := VX) cH hF fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_
  obtain ⟨s₁, m₁, P₁, p₁, hm₁, A₁⟩ := labF_args h₁
  obtain ⟨s₂, m₂, P₂, p₂, hm₂, A₂⟩ := labF_args h₂
  obtain ⟨-, B₁⟩ := FinArgs.toX P₁ hm₁ (rcOf_le _) A₁
  obtain ⟨-, B₂⟩ := FinArgs.toX P₂ hm₂ (rcOf_le _) A₂
  refine ⟨_, _, B₁, B₂, fun r hr => ?_,
    (Proof.RsaOaep.RISCV64.Base.spA okX (pubX_bx P₁ hm₁ (rc := rcOf (privO s₁)) p₁) B₁.b).trans
    (Proof.RsaOaep.RISCV64.Base.spA okX (pubX_bx P₂ hm₂ (rc := rcOf (privO s₂)) p₂) B₂.b).symm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.trans h₂.2.2.2.symm]

include hH hF in
/-- The label's hash keeps `DX`. -/
theorem hashLabel_dx {a t : State} (h : DX a t) : WP isa (Dec.hashLabel H) t (DX a) :=
  let ⟨s, m, P, p, hm, b⟩ := h
  WP.mono (hashLabel_ok P hH hF hm b) fun _ h' => ⟨s, m, P, p, hm, h'.1⟩

end

end VG.Proof.RsaOaep.RISCV64.Dec
