module

public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenTo.Fn
public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenTo.CT
import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig

/-!
# AES-GCM decryption out of place, by a copy, RISC-V: `Verified`

Untrusted: everything here is checked by Lean. The shared contract of
`vg_aes_gcm_open_to`, with the 4672 bytes of stack below the stack pointer
that its frame and its call use (`Proof.AesGcm.openToRoundsContract`),
implies the one the proof is written against (`toK`, `to_implies`), and so
the code, calling `vg_aes_gcm_open` by its shared contract (`open_framed`),
is `Verified` against it (`openTo_verified`). As on PPC64LE
(`Proof/AesGcm/PPC64LE/OpenTo/Verified.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.RISCV64.OpenTo

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64.OpenTo

theorem openTo_correct (hv : OpenOk) (s : State) (hs : toK.pre s) :
    ∃ t s', Exec isa openTo s t s' ∧ abiPreserved s s' ∧ toK.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := openTo_wp hv hs
  exact ⟨t, s', he, ha, hp⟩

theorem toPre_of_spec {s : State} (h : (Proof.AesGcm.openToRoundsContract RISCV64.abi 4672).pre s) : ToPre s := by
  sig_pre [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToPre, RISCV64.abi, RISCV64.argRegs,
    List.getD, List.range, List.range.loop] at h
  obtain ⟨al, w₁, w₂, rd, wr, kd, nd, ad, sd, dt, da, bk, bn, ba, bs, bd, bt, barg, ok, on, oa, os, od, ot, hR, dl,
    ca⟩ := h
  rw [dl] at wr kd nd ad sd dt da bd od
  exact ⟨al, w₁, w₂, rd, wr, kd, nd, ad, sd, dt, da, bk, bn, ba, bs, bd, bt, barg, ok, on, oa, os, od, ot, hR, dl,
    ca⟩

theorem toPost_of {s s' : State} (h : toPost s s') :
    (Proof.AesGcm.openToRoundsContract RISCV64.abi 4672).post s s' := by
  sig_post [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Proof.AesGcm.openToRoundsPost, RISCV64.abi,
    RISCV64.argRegs, List.range, List.range.loop]
  intro _
  exact h

theorem toPub_of {s₁ s₂ : State} (hp : (Proof.AesGcm.openToRoundsContract RISCV64.abi 4672).pub s₁ s₂) :
    toPub s₁ s₂ := by
  sig_pub [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToLeak, RISCV64.abi,
    RISCV64.argRegs, List.range, List.range.loop] at hp
  obtain ⟨qsp, ql, q3, q4, q5, q6, q7, q8, q9, q10, a0, a1, a2, a3⟩ := hp
  refine ⟨qsp, ql, q3, q4, q5, q6, q7, q8, q9, q10, fun i hi => ?_⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3]

/-- A state satisfying the precondition of `vg_aes_gcm_open_to`: no nonce,
additional data, text or tag, and all four stack arguments 0. -/
def toSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a4 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0, 0⟩, ⟨0x9000, 32⟩]
  wr := [⟨0, 0⟩]

theorem toSat_pre : ∃ s, (Proof.AesGcm.openToRoundsContract RISCV64.abi 4672).pre s := by
  implies_sat [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToPre,
    Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr,
    List.getD, List.range, List.range.loop]
    [toSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using toSat

theorem to_implies : toK.Implies (Proof.AesGcm.openToRoundsContract RISCV64.abi 4672) :=
  ⟨fun _ h => toPre_of_spec h, fun _ _ _ h => toPost_of h, fun _ _ _ _ h => toPub_of h, toSat_pre⟩

/-- `vg_aes_gcm_open_to`, calling `vg_aes_gcm_open` by its shared contract
(`open_framed`). -/
theorem openTo_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target openTo (Proof.AesGcm.openToRoundsContract RISCV64.abi 4672) :=
  Verified.of_correct (k := toK) (openTo_correct open_framed.1) (openTo_ct open_framed.1 open_framed.2.1)
    to_implies

end VG.Proof.AesGcm.RISCV64.OpenTo
