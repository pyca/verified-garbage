module

public import VerifiedGarbage.Proof.AesSiv.PPC64LE.Env
public import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.AesCtr.PPC64LE.Call
public import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Common

/-!
# AES-SIV on PPC64LE: relating two runs

Untrusted: everything here is checked by Lean. As for AES-CCM and
AES-GCM-SIV (`Proof/AesCcm/PPC64LE/Rel.lean`, whose relations of runs the
constant-time proofs use): the code between calls is related by the taint
analysis, from the registers the environment pins to the same public values
in both runs and those the correctness proofs pin (`rel_env`); each call by
its callee's proof (`rel_upd`, `rel_fin`, `rel_ctr`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.PPC64LE

open VG VG.PPC64LE
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_taint)

/-- The registers the environment pins. -/
abbrev envRegs : List Reg := [.r14, .r15, .r16, .r22, .r23, .r24]

/-- Two runs in the same environment agree on its registers. -/
theorem Env.agree {c : Cx} {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) :
    ∀ r ∈ envRegs, σ₁.gpr r = σ₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [E₁.r14, E₂.r14]
  · rw [E₁.r15, E₂.r15]
  · rw [E₁.r16, E₂.r16]
  · rw [E₁.r22, E₂.r22]
  · rw [E₁.r23, E₂.r23]
  · rw [E₁.r24, E₂.r24]

theorem agree_nil {a b : State} : ∀ r ∈ ([] : List Reg), a.gpr r = b.gpr r := fun _ h => nomatch h

theorem agree_cons {a b : State} {r : Reg} {rs : List Reg} (h : a.gpr r = b.gpr r)
    (hs : ∀ q ∈ rs, a.gpr q = b.gpr q) : ∀ q ∈ r :: rs, a.gpr q = b.gpr q := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact h
  · exact hs q hq

/-- Code the taint analysis checks, from the environment's registers and
`rs`, on which the two runs agree. -/
theorem rel_env {c : Cx} {code : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (E₁ : Env c σ₁) (E₂ : Env c σ₂)
    (hsp : σ₁.sp = σ₂.sp) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ rs)) code h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) code TT :=
  let ⟨_, hc⟩ := hc
  rel_taint (envRegs ++ rs) hsp (fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact Env.agree E₁ E₂ r h
    · exact hr r h) hc

/-! ## The calls -/

/-- A call of `vg_cmac_aes_update` with the same arguments in both runs. -/
theorem rel_upd {σ₁ σ₂ : State} {K C D S : Addr} {R n : Nat}
    (h₁ : Proof.CmacAes.Stream.PPC64LE.UArgs σ₁ K C D S R n) (h₂ : Proof.CmacAes.Stream.PPC64LE.UArgs σ₂ K C D S R n)
    (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) Impl.CmacAes.Stream.PPC64LE.updCall TT :=
  Proof.CmacAes.Stream.PPC64LE.upd_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨h₁, h₂, hsp⟩

/-- A call of `vg_cmac_aes_finalize` with the same arguments in both runs. -/
theorem rel_fin {σ₁ σ₂ : State} {K St Q S : Addr} {L R : Nat}
    (h₁ : Proof.CmacAes.Stream.PPC64LE.FArgs σ₁ K St Q S L R) (h₂ : Proof.CmacAes.Stream.PPC64LE.FArgs σ₂ K St Q S L R)
    (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) Impl.CmacAes.Stream.PPC64LE.finCall TT :=
  Proof.CmacAes.Stream.PPC64LE.fin_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨h₁, h₂, hsp⟩

/-- A call of `vg_aes_ctr32` with the same arguments in both runs. -/
theorem rel_ctr {σ₁ σ₂ : State} {K C D S : Addr} {R n : Nat}
    (h₁ : Proof.AesCtr.PPC64LE.CtrCall σ₁ K C D S R n) (h₂ : Proof.AesCtr.PPC64LE.CtrCall σ₂ K C D S R n)
    (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) Impl.AesCtr.PPC64LE.ctrCall TT :=
  Proof.AesCtr.PPC64LE.ctr_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨h₁, h₂, hsp⟩

end VG.Proof.AesSiv.PPC64LE
