module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.CT2
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Correct
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.CT2
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Correct
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: constant time

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecCT4.lean`): the loops of `CL` and `AM`
(`clLoop_ct`, `amLoop_ct`), from `prfLoop_ct` with the taint checks of their
blocks; the alternative length, the scan and the output, which make no call,
by one taint check from the registers `Post` fixes (`tail_ct`); and the whole
function (`code_ct`), from the two entry states' `Env`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (mov)

theorem clTaint : PrfTaint lengthLabel clLen [.li .t1 8] sCL where
  msg := ⟨_, by taint_decide⟩
  ini := ⟨_, by taint_decide⟩
  upd := ⟨_, by taint_decide⟩
  fin := ⟨_, by taint_decide⟩
  incr := ⟨_, by taint_decide⟩

theorem amTaint : PrfTaint messageLabel amLen [mov .t1 .s9] sAM where
  msg := ⟨_, by taint_decide⟩
  ini := ⟨_, by taint_decide⟩
  upd := ⟨_, by taint_decide⟩
  fin := ⟨_, by taint_decide⟩
  incr := ⟨_, by taint_decide⟩

section
variable {e : Env}

theorem clLoop_ct : RelCT isa (Rel e PostAt) clLoop (Rel e fun s u => PostAt s u ∧ u.gpr .s9 = nbOf s) := by
  unfold clLoop
  refine RelCT.seq (rel_step [.s1] (P' := L 0) (by unfold clInit; taint_decide) (pin_post (fun _ _ h => h) _)
    fun s u h ⟨_, _, P⟩ => ?_) ?_
  · have hk := h.k2
    unfold clInit
    refine wp_li (imm := 0) (by decide) fun v₁ p₁ f₁ => wp_addi (imm := 31) (fun v₂ p₂ f₂ =>
      wp_srl (sh := 5) fun t₁ p₃ f₃ => wp_nil ?_) (by decide)
    have O : Only [.s8, .s9] u t₁ := (p₁.trans (p₂.trans p₃)).mono
    exact ⟨⟨_, _, P.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)⟩,
      by rw [p₃.get .s8, p₂.get .s8, f₁], by rw [f₃, f₂, p₁.get .s1, P.s1, nb_eq hk]⟩
  exact prfLoop_ct clTaint (C := fun _ => BitVec.ofNat 64 8) rfl
    (fun i hi => Offset.ofNat_sub_ofNat (by omega)) (N := 8) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (fun i hi s R EM u h P x8 => WP.mono (msgCL_ok (by rw [P.s0]) x8 (by omega) (P.msgW h)) fun w ⟨⟨F, _⟩, K⟩ => ⟨F, K⟩)
    (fun s u _ => count8_ok u)

theorem amLoop_ct :
    RelCT isa (Rel e fun s u => PostAt s u ∧ u.gpr .s9 = nbOf s) amLoop (Rel e PostAt) := by
  unfold amLoop
  refine RelCT.seq (rel_step [] (P' := L 0) (by taint_decide)
    (fun a b ⟨⟨_, _, A⟩, _⟩ ⟨⟨_, _, B⟩, _⟩ => ⟨(post_agree A B).1, fun _ h => nomatch h⟩)
    fun s u h ⟨⟨_, _, P⟩, h9⟩ => wp_li (imm := 0) (by decide) fun t₁ p₁ f₁ => wp_nil
      ⟨⟨_, _, P.keep h p₁.keep (ws := []) (by rw [p₁.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)⟩,
        f₁, by rw [p₁.get .s9, h9]⟩) ?_
  refine (prfLoop_ct amTaint (C := nbOf) (by rw [nbOf, nbOf, e.r])
    (fun i hi => Offset.ofNat_sub_ofNat (by omega)) (N := ((e.s₁.gpr .a4).toNat + 31) / 32)
    (by have := e.h₁.k1; omega) (by have := e.h₁.k2; omega) (by decide) (by have := e.h₁.k2; unfold sAM scrBytes; omega)
    (by decide) (by decide)
    (fun i hi s R EM u h P x8 => WP.mono (msgAM_ok (by rw [P.s0]) x8 P.s1 (by have := e.h₁.k2; omega) h.k2 (P.msgW h))
      fun w ⟨⟨F, _⟩, K⟩ => ⟨F, K⟩)
    (fun s u hu => count_ok u _ hu)).mono (fun _ _ h => h) fun _ _ ⟨a, b⟩ => ⟨a.1, b.1⟩

/-! ## The rest -/

theorem tail_ct : RelCT isa (Rel e PostAt) (.seq maskPart (.seq alPart (.seq scanPart selPart))) fun _ _ => True :=
  rel_of (rs := [.s0, .s1, .s2, .s3]) (by taint_decide) fun a b hab =>
    pin_post (fun _ _ h => h) [.s0, .s1, .s2, .s3] (by decide) a b hab.1 hab.2

theorem body_ct : RelCT isa (Rel e PEnt) body fun _ _ => True := by
  unfold body
  refine RelCT.seq setup_ct (RelCT.seq priv_ct (RelCT.seq dBuild_ct (RelCT.seq hashD_ct
    (RelCT.seq kdkMac_ct (RelCT.seq clLoop_ct (RelCT.seq amLoop_ct tail_ct))))))

end

/-- A frame that allocates `bytes`, its body from both allocated states: the
allocation accesses no memory. -/
theorem rel_alloc {P : State → State → Prop} {bytes : Nat} {body : Prog isa} {R : State → State → Prop}
    (hb : RelCT isa (fun u₁ u₂ => ∃ s₁ s₂, P s₁ s₂ ∧ u₁ = allocd bytes s₁ ∧ u₂ = allocd bytes s₂) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ _ =>
    cases e₂ with
    | frame p₂ b₂ _ =>
      obtain ⟨ht, -⟩ := hb _ _ _ _ _ _ ⟨_, _, hp, alloc_eq p₁, alloc_eq p₂⟩ b₁ b₂
      refine ⟨?_, trivial⟩
      rw [ht]
      simp [addrs]

theorem code_ct : ConstantTime isa (Spec.RsaPkcs1Enc.decryptContract RISCV64.abi stackBytes).pre
    (Spec.RsaPkcs1Enc.decryptContract RISCV64.abi stackBytes).pub code :=
  RelCT.constantTime (rel_alloc ((RelCT.exists_ fun e : Env => body_ct (e := e)).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, ea, eb⟩ => ⟨⟨s₁, s₂, dPre_of h₁, dPre_of h₂, same_of hp⟩, ea, eb⟩)
    fun _ _ h => h))

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec
