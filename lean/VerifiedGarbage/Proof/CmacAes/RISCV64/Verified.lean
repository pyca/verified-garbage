module

public import VerifiedGarbage.Impl.CmacAes.RISCV64
public import VerifiedGarbage.Spec.Cmac.Contract
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
theorem update_wpre {s : State} (hs : updateRISCV64.pre s) :
    Proof.AesCbc.RISCV64.WPre false (16 * ·) s :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k⟩ := hs
  ⟨a, b, c, d, e, f, g, h, i, j, k⟩

theorem update_correct (s : State) (hs : updateRISCV64.pre s) :
    ∃ t s', Exec isa update s t s' ∧ abiPreserved s s' ∧ updateRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp, -⟩ :=
    Proof.AesCbc.RISCV64.wrap_wp (Proof.AesCbc.RISCV64.chain_k false) (name := "vg_aes_mac_chain")
      (update_wpre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

theorem update_ct : ConstantTime isa updateRISCV64.pre updateRISCV64.pub update :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    Proof.AesCbc.RISCV64.wrap_ct (Proof.AesCbc.RISCV64.chain_k false) "vg_aes_mac_chain" _ _ _ _ _ _
      (update_wpre h₁) (update_wpre h₂) hq e₁ e₂

theorem finalize_correct (s : State) (hs : finalizeRISCV64.pre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ finalizeRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ := finalize_wp hs
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

end VG.Proof.CmacAes.RISCV64
