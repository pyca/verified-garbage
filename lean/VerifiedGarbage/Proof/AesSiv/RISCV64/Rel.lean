module

public import VerifiedGarbage.Proof.AesSiv.RISCV64.Env
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Rel
public import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.AesCtr.RISCV64.Call
public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common

/-!
# AES-SIV on RISC-V: relating two runs

Untrusted: everything here is checked by Lean. As for AES-CCM
(`Proof/AesCcm/RISCV64/Rel.lean`, whose `Runs`, `Runs.of_wp`, `Runs.keep`,
`rel_seqR`, `rel_post` and `rel_of_eq2` the constant-time proofs also use):
the code between calls is related by the taint analysis, from the registers
the environment pins to the same public values in both runs and those the
correctness proofs pin (`rel_env`); each call by its callee's proof
(`rel_upd`, `rel_fin`, `rel_ctr`), after which the environment and the
registers the pieces keep across calls still hold (`upd_runs`, `fin_runs`,
`ctr_runs`). As on PPC64LE (`Proof/AesSiv/PPC64LE/Rel.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_taint)
open VG.Proof.AesCcm.RISCV64 (Runs Runs.of_wp)

/-- The registers the environment pins. -/
abbrev envRegs : List Reg := [.s1, .s2, .s3, .s9, .s10, .s11]

/-- Two runs in the same environment agree on its registers. -/
theorem Env.agree {c : Cx} {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) :
    ∀ r ∈ envRegs, σ₁.gpr r = σ₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [E₁.s1, E₂.s1]
  · rw [E₁.s2, E₂.s2]
  · rw [E₁.s3, E₂.s3]
  · rw [E₁.s9, E₂.s9]
  · rw [E₁.s10, E₂.s10]
  · rw [E₁.s11, E₂.s11]

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
    (h₁ : Proof.CmacAes.Stream.RISCV64.UArgs σ₁ K C D S R n) (h₂ : Proof.CmacAes.Stream.RISCV64.UArgs σ₂ K C D S R n)
    (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) Impl.CmacAes.Stream.RISCV64.updCall TT :=
  Proof.CmacAes.Stream.RISCV64.upd_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨h₁, h₂, hsp⟩

/-- A call of `vg_cmac_aes_finalize` with the same arguments in both runs. -/
theorem rel_fin {σ₁ σ₂ : State} {K St Q S : Addr} {L R : Nat}
    (h₁ : Proof.CmacAes.Stream.RISCV64.FArgs σ₁ K St Q S L R)
    (h₂ : Proof.CmacAes.Stream.RISCV64.FArgs σ₂ K St Q S L R)
    (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) Impl.CmacAes.Stream.RISCV64.finCall TT :=
  Proof.CmacAes.Stream.RISCV64.fin_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨h₁, h₂, hsp⟩

/-- A call of `vg_aes_ctr32` with the same arguments in both runs. -/
theorem rel_ctr {σ₁ σ₂ : State} {K C D S : Addr} {R n : Nat}
    (h₁ : Proof.AesCtr.RISCV64.CtrCall σ₁ K C D S R n) (h₂ : Proof.AesCtr.RISCV64.CtrCall σ₂ K C D S R n)
    (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) Impl.AesCtr.RISCV64.ctrCall TT :=
  Proof.AesCtr.RISCV64.ctr_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨h₁, h₂, hsp⟩

/-! ## After the calls -/

/-- The callee-saved registers the pieces keep across calls, besides the
environment's. -/
abbrev callKept : List Reg := [.s0, .s4, .s5, .s6, .s7, .s8]

theorem callKept_preserved : ∀ r ∈ callKept, r ∈ preserved := by decide

/-- After a call of `vg_cmac_aes_update`: the environment and our registers. -/
theorem upd_runs {c : Cx} {s : State} {K C D S : Addr} {R n : Nat} (E : Env c s)
    (h : Proof.CmacAes.Stream.RISCV64.UArgs s K C D S R n) :
    Runs Impl.CmacAes.Stream.RISCV64.updCall s fun s' => Env c s' ∧ s'.sp = s.sp ∧
      ∀ r ∈ callKept, s'.gpr r = s.gpr r :=
  Runs.of_wp (WP.mono (Proof.CmacAes.Stream.RISCV64.upd_call h) fun _ U =>
    ⟨E.of_pk (PK.ofSaved U.rd U.wr U.sp U.saved), U.sp, fun r hr => U.saved r (callKept_preserved r hr)⟩)

/-- After a call of `vg_cmac_aes_finalize`: the environment and our registers. -/
theorem fin_runs {c : Cx} {s : State} {K St Q S : Addr} {L R : Nat} (E : Env c s)
    (h : Proof.CmacAes.Stream.RISCV64.FArgs s K St Q S L R) :
    Runs Impl.CmacAes.Stream.RISCV64.finCall s fun s' => Env c s' ∧ s'.sp = s.sp ∧
      ∀ r ∈ callKept, s'.gpr r = s.gpr r :=
  Runs.of_wp (WP.mono (Proof.CmacAes.Stream.RISCV64.fin_call h) fun _ U =>
    ⟨E.of_pk (PK.ofSaved U.rd U.wr U.sp U.saved), U.sp, fun r hr => U.saved r (callKept_preserved r hr)⟩)

/-- After a call of `vg_aes_ctr32`: the environment and our registers. -/
theorem ctr_runs {c : Cx} {s : State} {K C D S : Addr} {R n : Nat} (E : Env c s)
    (h : Proof.AesCtr.RISCV64.CtrCall s K C D S R n) :
    Runs Impl.AesCtr.RISCV64.ctrCall s fun s' => Env c s' ∧ s'.sp = s.sp ∧
      ∀ r ∈ callKept, s'.gpr r = s.gpr r :=
  Runs.of_wp (WP.mono (Proof.AesCtr.RISCV64.ctr_call h) fun _ U =>
    ⟨E.of_pk (PK.ofSaved U.rd U.wr U.sp U.saved), U.sp, fun r hr => U.saved r (callKept_preserved r hr)⟩)

end VG.Proof.AesSiv.RISCV64
