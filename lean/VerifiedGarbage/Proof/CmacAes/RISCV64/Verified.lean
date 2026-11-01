module

public import VerifiedGarbage.Impl.CmacAes.RISCV64
public import VerifiedGarbage.Spec.Cmac.Contract
public import VerifiedGarbage.Proof.Cmac.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.CmacAes.RISCV64.Contract
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Chain
import VerifiedGarbage.Proof.CmacAes.RISCV64.CT
import VerifiedGarbage.Proof.CmacAes.RISCV64.Subkeys
import VerifiedGarbage.Proof.CmacAes.RISCV64.Finalize
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-CMAC on RISC-V: `Verified`

Correctness and constant time (of `update` from the chain's, `wrap_wp` and
`wrap_ct`, `Proof/AesCbc/RISCV64/Chain.lean`: the blocks chained into the
state), a state satisfying each precondition, and the shared contracts of
`Spec/Cmac/Contract.lean` (with no stack: a call stores
nothing in memory, and each function saves the return address in the
scratch buffer).
-/

@[expose] public section

namespace VG.Proof.CmacAes.RISCV64

open VG VG.RISCV64 VG.Impl.CmacAes.RISCV64

theorem subkeys_correct (s : State) (hs : subkeysRISCV64.pre s) :
    ∃ t s', Exec isa subkeys s t s' ∧ abiPreserved s s' ∧ subkeysRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ := subkeys_wp hs
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

/-- `update`'s precondition, the chain's (with the scratch buffer of 2176 bytes). -/
theorem update_wpre {s : State} (hs : updateRISCV64.pre s) : Proof.AesCbc.RISCV64.WPre false s :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k⟩ := hs
  ⟨a, b, c, d, e, f, g, h, i, j, k⟩

theorem update_correct (s : State) (hs : updateRISCV64.pre s) :
    ∃ t s', Exec isa update s t s' ∧ abiPreserved s s' ∧ updateRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp, -⟩ :=
    Proof.AesCbc.RISCV64.wrap_wp (name := "vg_aes_mac_chain") (update_wpre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

theorem update_ct : ConstantTime isa updateRISCV64.pre updateRISCV64.pub update :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    Proof.AesCbc.RISCV64.wrap_ct "vg_aes_mac_chain" false _ _ _ _ _ _ (update_wpre h₁) (update_wpre h₂) hq e₁ e₂

theorem finalize_correct (s : State) (hs : finalizeRISCV64.pre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ finalizeRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ := finalize_wp hs
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

/-- A state satisfying `vg_cmac_aes_subkeys`'s precondition. -/
def subSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 32⟩, ⟨0x4000, 2176⟩]

theorem subkeys_verified : Verified RISCV64.target subkeys (Proof.Cmac.aesSubkeysContract RISCV64.abi) :=
  Verified.of_correct subkeys_correct subkeys_ct (by
    sig_implies [Proof.Cmac.aesSubkeysContract, Proof.Cmac.aesSubkeysSig, subkeysRISCV64, RISCV64.abi,
      RISCV64.argRegs] [subSat] using subSat)

/-- A state satisfying `vg_cmac_aes_update`'s precondition (with no blocks). -/
def updSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a3 => 0x3000 | .a5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2176⟩]

theorem update_verified : Verified RISCV64.target update (Proof.Cmac.aesUpdateContract RISCV64.abi) :=
  Verified.of_correct update_correct update_ct (by
    sig_implies [Proof.Cmac.aesUpdateContract, Proof.Cmac.aesUpdateSig, updateRISCV64, RISCV64.abi,
      RISCV64.argRegs] [updSat] using updSat)

/-- A state satisfying `vg_cmac_aes_finalize`'s precondition (with no last bytes). -/
def finSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a3 => 0x3000 | .a5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2176⟩]

theorem finalize_verified : Verified RISCV64.target finalize (Proof.Cmac.aesFinalizeContract RISCV64.abi) :=
  Verified.of_correct finalize_correct finalize_ct (by
    sig_implies [Proof.Cmac.aesFinalizeContract, Proof.Cmac.aesFinalizeSig, finalizeRISCV64, RISCV64.abi,
      RISCV64.argRegs] [finSat] using finSat)

end VG.Proof.CmacAes.RISCV64
