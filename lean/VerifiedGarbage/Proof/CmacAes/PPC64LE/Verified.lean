module

public import VerifiedGarbage.Impl.CmacAes.PPC64LE
public import VerifiedGarbage.Spec.Cmac.Contract
public import VerifiedGarbage.Proof.Cmac.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.CmacAes.PPC64LE.Contract
import VerifiedGarbage.Proof.CmacAes.PPC64LE.CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.CmacAes.PPC64LE.Finalize
import VerifiedGarbage.Proof.CmacAes.PPC64LE.Subkeys

/-!
# AES-CMAC on PPC64LE: `Verified`

Correctness and constant time, a state satisfying each precondition, and the
shared contracts of `Spec/Cmac/Contract.lean` (with no stack: a call stores
nothing in memory, and each function saves the return address in the
scratch buffer).
-/

@[expose] public section

namespace VG.Proof.CmacAes.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.PPC64LE

theorem subkeys_correct (s : State) (hs : subkeysPPC64LE.pre s) :
    ∃ t s', Exec isa subkeys s t s' ∧ abiPreserved s s' ∧ subkeysPPC64LE.post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := subkeys_wp hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem update_correct (s : State) (hs : updatePPC64LE.pre s) :
    ∃ t s', Exec isa update s t s' ∧ abiPreserved s s' ∧ updatePPC64LE.post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := update_wp hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem finalize_correct (s : State) (hs : finalizePPC64LE.pre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ finalizePPC64LE.post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := finalize_wp hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

/-- A state satisfying `vg_cmac_aes_subkeys`'s precondition. -/
def subSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 32⟩, ⟨0x4000, 2176⟩]

theorem subkeys_verified : Verified PPC64LE.target subkeys (Proof.Cmac.aesSubkeysContract PPC64LE.abi) :=
  Verified.of_correct subkeys_correct subkeys_ct (by
    sig_implies [Proof.Cmac.aesSubkeysContract, Proof.Cmac.aesSubkeysSig, subkeysPPC64LE, PPC64LE.abi,
      PPC64LE.argRegs] [subSat] using subSat)

/-- A state satisfying `vg_cmac_aes_update`'s precondition (with no blocks). -/
def updSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r6 => 0x3000 | .r8 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2176⟩]

theorem update_verified : Verified PPC64LE.target update (Proof.Cmac.aesUpdateContract PPC64LE.abi) :=
  Verified.of_correct update_correct update_ct (by
    sig_implies [Proof.Cmac.aesUpdateContract, Proof.Cmac.aesUpdateSig, updatePPC64LE, PPC64LE.abi,
      PPC64LE.argRegs] [updSat] using updSat)

/-- A state satisfying `vg_cmac_aes_finalize`'s precondition (with no last bytes). -/
def finSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r6 => 0x3000 | .r8 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2176⟩]

theorem finalize_verified : Verified PPC64LE.target finalize (Proof.Cmac.aesFinalizeContract PPC64LE.abi) :=
  Verified.of_correct finalize_correct finalize_ct (by
    sig_implies [Proof.Cmac.aesFinalizeContract, Proof.Cmac.aesFinalizeSig, finalizePPC64LE, PPC64LE.abi,
      PPC64LE.argRegs] [finSat] using finSat)

end VG.Proof.CmacAes.PPC64LE
