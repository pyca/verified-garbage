module

public import VerifiedGarbage.Impl.Idea.Arm
public import VerifiedGarbage.Impl.Idea.Arm.Modes
public import VerifiedGarbage.Impl.Idea.Arm.FbFinal
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Residue.Arm
public import VerifiedGarbage.Impl.Residue.ArmSel

/-!
# IDEA on ARMv7, as emitted

Each function's code followed by its cleanup (`Impl/Residue/Arm.lean`): for
key expansion, which has no frame, the registers a callee may change set to
constants (`scrub`); for key inversion and ECB, first the stack their
contracts reserve, where their frames were, zeroed (`scrubF`); for the modes,
which wipe their own working space, first only the words of that stack that
the residue analysis (`Arm.rtaint`) finds may differ between two runs
(`Impl/Residue/ArmSel.lean`, `scrubSel`, `modeWords`, offsets in words from
its lowest address). None returns a value.
`Proof/Idea/Arm/Scrub.lean` states that each returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.Idea.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm VG.Impl.StackScratch.Arm

/-- `vg_idea_expand_key`. -/
def expandKey : Prog isa := scrub 0 Impl.Idea.Arm.expandKey

/-- `vg_idea_invert_key`. -/
def invertKey : Prog isa := scrubF 0 24 (withRegScratch 24 .r2 Impl.Idea.Arm.invertKey)

/-- `vg_idea_ecb`. -/
def ecb : Prog isa := scrubF 0 32 Impl.Idea.Arm.ecbCode

/-- The words the modes leave secret. -/
def modeWords : List Nat := List.range' 0 10

/-- `vg_idea_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := scrubSel 0 96 modeWords (withStackScratchWiped 64 0 14 Impl.Idea.Arm.cbcEncryptChained)

/-- `vg_idea_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := scrubSel 0 96 modeWords (withStackScratchWiped 64 0 14 Impl.Idea.Arm.cbcDecryptChained)

/-- `vg_idea_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := scrubSel 0 96 modeWords (withStackScratchWiped 64 0 14 Impl.Idea.Arm.cfbEncrypt)

/-- `vg_idea_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := scrubSel 0 96 modeWords (withStackScratchWiped 64 0 14 Impl.Idea.Arm.cfbDecrypt)

/-- `vg_idea_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := scrubSel 0 96 modeWords (withStackScratchWiped 64 0 14 Impl.Idea.Arm.cfbEncryptFinal)

/-- `vg_idea_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := scrubSel 0 96 modeWords (withStackScratchWiped 64 0 14 Impl.Idea.Arm.cfbDecryptFinal)

/-- `vg_idea_ofb`. -/
def ofb : Prog isa := scrubSel 0 96 modeWords (withStackScratchWiped 64 0 14 Impl.Idea.Arm.ofb)

/-- `vg_idea_ofb_final`. -/
def ofbFinal : Prog isa := scrubSel 0 96 modeWords (withStackScratchWiped 64 0 14 Impl.Idea.Arm.ofbFinal)

end VG.Impl.Idea.Arm.Fn
