module

import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Wp
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Rel
public import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Callee
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Env
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM-SIV on RISC-V: relating two runs

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcmSiv/PPC64LE/Rel.lean`), with AES-CCM's relations of runs
(`Proof/AesCcm/RISCV64/Rel.lean`): the code between calls is related by the
taint analysis, from the registers the environment pins to the same public
values in both runs and those the correctness proofs pin (`rel_env`); each
call by its callee's proof (`rel_ctr`, `rel_gh`, `rel_key`). What the next
piece needs of each run holds after every run of the previous one: by its
correctness proof, or, for the registers code without calls does not write,
by its instructions alone (`Runs.kept`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.RISCV64
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_taint)
open VG.Proof.AesCcm.RISCV64 (Runs Runs.of_wp Runs.keep)
open VG.Proof.AesGcm.RISCV64 (CtrCall GhCall KeyCall)

/-- The registers the environment pins. -/
abbrev envRegs : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8]

/-- Two runs in the same environment agree on its registers. -/
theorem Env.agree {c : Cx} {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) :
    ∀ r ∈ envRegs, σ₁.gpr r = σ₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [E₁.s0, E₂.s0]
  · rw [E₁.s1, E₂.s1]
  · rw [E₁.s2, E₂.s2]
  · rw [E₁.s3, E₂.s3]
  · rw [E₁.s4, E₂.s4]
  · rw [E₁.s5, E₂.s5]
  · rw [E₁.s6, E₂.s6]
  · rw [E₁.s7, E₂.s7]
  · rw [E₁.s8, E₂.s8]

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

/-- What a piece leaves to the next: the environment, the stack pointer and
the registers the pieces pass on. -/
abbrev Kept (c : Cx) (s s' : State) : Prop :=
  Env c s' ∧ s'.sp = s.sp ∧ ∀ r ∈ [Reg.s9, .s10, .s11], s'.gpr r = s.gpr r

theorem Kept.trans {c : Cx} {s t u : State} (h₁ : Kept c s t) (h₂ : Kept c t u) : Kept c s u :=
  ⟨h₂.1, h₂.2.1.trans h₁.2.1, fun r hr => (h₂.2.2 r hr).trans (h₁.2.2 r hr)⟩

/-- Code without calls that writes none of the environment's registers, nor
`s9`–`s11`. -/
theorem Runs.kept {c : Cx} {code : Prog isa} {s : State} (E : Env c s) (rs : List Reg)
    (hc : writesOnly rs code = true)
    (hd : ∀ r ∈ keepRegs ++ ([.s9, .s10, .s11] : List Reg), r ∉ rs := by decide)
    (hn : code.noCalls = true := by decide +kernel) : Runs code s (Kept c s) :=
  (Runs.keep rs hc hn).mono fun _ ⟨k, sp⟩ =>
    ⟨E.of_pk ⟨k.2.1, k.2.2, sp, fun r hr => k.1 r (hd r (List.mem_append_left _ hr))⟩, sp, fun r hr =>
      k.1 r (hd r (List.mem_append_right _ hr))⟩

/-- What a call leaves: the environment, the stack pointer and `s9`–`s11`. -/
theorem kept_saved {c : Cx} {s s' : State} (E : Env c s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hs : ∀ r ∈ preserved, s'.gpr r = s.gpr r) : Kept c s s' :=
  ⟨E.of_pk (PK.ofSaved hrd hwr hsp hs), hsp, fun r hr => hs r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)⟩

/-! ## The calls -/

theorem rel_ctr {σ₁ σ₂ : State} {K C D S : Addr} {R n : Nat} (h₁ : CtrCall σ₁ K C D S R n)
    (h₂ : CtrCall σ₂ K C D S R n) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) Impl.AesGcm.RISCV64.ctrCall TT :=
  Proof.AesGcm.RISCV64.ctr_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, C, D, S, R, n, h₁, h₂, hsp⟩

theorem rel_gh {σ₁ σ₂ : State} {H Y D S : Addr} {n : Nat} (h₁ : GhCall σ₁ H Y D S n) (h₂ : GhCall σ₂ H Y D S n)
    (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) Impl.AesGcm.RISCV64.ghCall TT :=
  Proof.AesGcm.RISCV64.gh_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨H, Y, D, S, n, h₁, h₂, hsp⟩

theorem rel_key {σ₁ σ₂ : State} {K : Addr} {kl : Nat} {C S : Addr} (h₁ : KeyCall σ₁ K kl C S)
    (h₂ : KeyCall σ₂ K kl C S) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) Impl.AesGcm.RISCV64.keyCall TT :=
  Proof.AesGcm.RISCV64.key_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, kl, C, S, h₁, h₂, hsp⟩

theorem ctr_runs {c : Cx} {s : State} {K C D S : Addr} {R n : Nat} (E : Env c s) (h : CtrCall s K C D S R n) :
    Runs Impl.AesGcm.RISCV64.ctrCall s (Kept c s) :=
  Runs.of_wp (WP.mono (Proof.AesGcm.RISCV64.ctr_call h) fun _ U => kept_saved E U.rd U.wr U.sp U.saved)

theorem gh_runs {c : Cx} {s : State} {H Y D S : Addr} {n : Nat} (E : Env c s) (h : GhCall s H Y D S n) :
    Runs Impl.AesGcm.RISCV64.ghCall s (Kept c s) :=
  Runs.of_wp (WP.mono (Proof.AesGcm.RISCV64.gh_call h) fun _ U => kept_saved E U.rd U.wr U.sp U.saved)

theorem key_runs {c : Cx} {s : State} {K : Addr} {kl : Nat} {C S : Addr} (E : Env c s) (h : KeyCall s K kl C S) :
    Runs Impl.AesGcm.RISCV64.keyCall s (Kept c s) :=
  Runs.of_wp (WP.mono (Proof.AesGcm.RISCV64.key_call h) fun _ U => kept_saved E U.rd U.wr U.sp U.saved)

end VG.Proof.AesGcmSiv.RISCV64
