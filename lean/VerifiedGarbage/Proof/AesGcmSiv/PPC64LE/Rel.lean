module

import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Wp
import VerifiedGarbage.Proof.AesCcm.PPC64LE.CallArgs
public import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Rel
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Callee
public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Impl.AesGcm.PPC64LE

/-!
# AES-GCM-SIV on PPC64LE: relating two runs

Untrusted: everything here is checked by Lean. As for AES-CCM
(`Proof/AesCcm/PPC64LE/Rel.lean`, whose relations of runs this uses): the
code between calls is related by the taint analysis, from the registers the
environment pins to the same public values in both runs and those the
correctness proofs pin (`rel_env`); each call by its callee's proof
(`rel_ctr`, `rel_gh`, `rel_key`). What the next piece needs of each run holds
after every run of the previous one: by its correctness proof, or, for the
registers code without calls does not write, by its instructions alone
(`Runs.kept`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE

open VG VG.PPC64LE
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_taint)
open VG.Proof.AesCcm.PPC64LE (Runs Runs.of_wp Runs.keep)
open VG.Proof.AesGcm.PPC64LE (CtrCall GhCall KeyCall)

/-- The registers the environment pins. -/
abbrev envRegs : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22]

/-- Two runs in the same environment agree on its registers. -/
theorem Env.agree {c : Cx} {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) :
    ∀ r ∈ envRegs, σ₁.gpr r = σ₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [E₁.r14, E₂.r14]
  · rw [E₁.r15, E₂.r15]
  · rw [E₁.r16, E₂.r16]
  · rw [E₁.r17, E₂.r17]
  · rw [E₁.r18, E₂.r18]
  · rw [E₁.r19, E₂.r19]
  · rw [E₁.r20, E₂.r20]
  · rw [E₁.r21, E₂.r21]
  · rw [E₁.r22, E₂.r22]

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
  Env c s' ∧ s'.sp = s.sp ∧ ∀ r ∈ [Reg.r23, .r24, .r25], s'.gpr r = s.gpr r

theorem Kept.trans {c : Cx} {s t u : State} (h₁ : Kept c s t) (h₂ : Kept c t u) : Kept c s u :=
  ⟨h₂.1, h₂.2.1.trans h₁.2.1, fun r hr => (h₂.2.2 r hr).trans (h₁.2.2 r hr)⟩

/-- Code without calls that writes none of the environment's registers, nor
`r23`–`r25`. -/
theorem Runs.kept {c : Cx} {code : Prog isa} {s : State} (E : Env c s) (rs : List Reg)
    (hc : writesOnly rs code = true)
    (hd : ∀ r ∈ keepRegs ++ ([.r23, .r24, .r25] : List Reg), r ∉ rs := by decide)
    (hn : code.noCalls = true := by decide +kernel) : Runs code s (Kept c s) :=
  (Runs.keep rs hc hn).mono fun _ ⟨k, sp⟩ =>
    ⟨E.of_pk (PK.ofKeep k sp fun r hr => hd r (List.mem_append_left _ hr)), sp, fun r hr =>
      k.gpr (hd r (List.mem_append_right _ hr))⟩

/-- What a call leaves: the environment, the stack pointer and `r23`–`r25`. -/
theorem kept_saved {c : Cx} {s s' : State} (E : Env c s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hs : ∀ r ∈ preserved, s'.gpr r = s.gpr r) : Kept c s s' :=
  ⟨E.of_pk (PK.ofSaved hrd hwr hsp hs), hsp, fun r hr => hs r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)⟩

/-! ## The calls -/

theorem rel_ctr {σ₁ σ₂ : State} {K C D S : Addr} {R n : Nat} (h₁ : CtrCall σ₁ K C D S R n)
    (h₂ : CtrCall σ₂ K C D S R n) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) Impl.AesGcm.PPC64LE.ctrCall TT :=
  Proof.AesGcm.PPC64LE.ctr_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, C, D, S, R, n, h₁, h₂, hsp⟩

theorem rel_gh {σ₁ σ₂ : State} {H Y D S : Addr} {n : Nat} (h₁ : GhCall σ₁ H Y D S n) (h₂ : GhCall σ₂ H Y D S n)
    (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) Impl.AesGcm.PPC64LE.ghCall TT :=
  Proof.AesGcm.PPC64LE.gh_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨H, Y, D, S, n, h₁, h₂, hsp⟩

theorem rel_key {σ₁ σ₂ : State} {K : Addr} {kl : Nat} {C S : Addr} (h₁ : KeyCall σ₁ K kl C S)
    (h₂ : KeyCall σ₂ K kl C S) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) Impl.AesGcm.PPC64LE.keyCall TT :=
  Proof.AesGcm.PPC64LE.key_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, kl, C, S, h₁, h₂, hsp⟩

theorem ctr_runs {c : Cx} {s : State} {K C D S : Addr} {R n : Nat} (E : Env c s) (h : CtrCall s K C D S R n) :
    Runs Impl.AesGcm.PPC64LE.ctrCall s (Kept c s) :=
  Runs.of_wp (WP.mono (Proof.AesGcm.PPC64LE.ctr_call h) fun _ U => kept_saved E U.rd U.wr U.sp U.saved)

theorem gh_runs {c : Cx} {s : State} {H Y D S : Addr} {n : Nat} (E : Env c s) (h : GhCall s H Y D S n) :
    Runs Impl.AesGcm.PPC64LE.ghCall s (Kept c s) :=
  Runs.of_wp (WP.mono (Proof.AesGcm.PPC64LE.gh_call h) fun _ U => kept_saved E U.rd U.wr U.sp U.saved)

theorem key_runs {c : Cx} {s : State} {K : Addr} {kl : Nat} {C S : Addr} (E : Env c s) (h : KeyCall s K kl C S) :
    Runs Impl.AesGcm.PPC64LE.keyCall s (Kept c s) :=
  Runs.of_wp (WP.mono (Proof.AesGcm.PPC64LE.key_call h) fun _ U => kept_saved E U.rd U.wr U.sp U.saved)

end VG.Proof.AesGcmSiv.PPC64LE
