module

public import VerifiedGarbage.Impl.CmacAes.PPC64LE
public import VerifiedGarbage.Spec.Cmac.Contract
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

end VG.Proof.CmacAes.PPC64LE
