module

public import VerifiedGarbage.Impl.Camellia.Arm.ExpandKey
public import VerifiedGarbage.Impl.Camellia.Arm.Cbc
public import VerifiedGarbage.Impl.Camellia.Arm.Fb
public import VerifiedGarbage.Impl.Camellia.Arm.FbFinal
public import VerifiedGarbage.Impl.Camellia.Arm.CtrFinal
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Scrub.Arm.Sel

/-!
# Camellia on ARMv7, as emitted

Each function's code followed by its cleanup (`Impl/Scrub/Arm/Sel.lean`,
`scrubSel`): of the stack its contract reserves, where its frames were, only
the words that the residue analysis (`Arm.rtaint`) finds may differ between
two runs zeroed (`…Words`, offsets in words from the lowest address of that
stack), and the registers a callee may change, but its result, set to
constants. The code wipes its own working space; what is left is the stack
arguments and buffer address it copies into its frame and its innermost
frames. `Proof/Camellia/Arm/Scrub.lean` states that each returns without
secret residue.
-/

@[expose] public section

namespace VG.Impl.Camellia.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- The words the key expansion leaves secret: none. -/
def expandKeyWords : List Nat := []

/-- The words the modes one block at a time leave secret. -/
def seqWords : List Nat := List.range' 2 5 ++ List.range' 705 3

/-- The words the modes in groups of blocks leave secret. -/
def wideWords : List Nat := [2, 3, 34, 35] ++ List.range' 684 22 ++ List.range' 716 25 ++ [759]

/-- The words the modes over a message's last piece leave secret. -/
def finalWords : List Nat := [2, 3] ++ List.range' 684 25 ++ [727]

/-- The words CTR over a message's last piece leaves secret. -/
def ctrFinalWords : List Nat := wideWords ++ List.range' 760 5 ++ [779]

/-- `vg_camellia_expand_key`. -/
def expandKey : Prog isa := scrubSel 0 2720 expandKeyWords (Impl.StackScratch.Arm.withRegScratchWiped 2720 .r3 680 Impl.Camellia.Arm.expandKey)

-- `vg_camellia_ecb_encrypt` and `vg_camellia_ecb_decrypt` (`ecbEncrypt`,
-- `ecbDecrypt`, with `ecbWords`) are in `Cbc.lean`, as the modes call them.

/-- `vg_camellia_cbc_encrypt_chained`. -/
def cbcEncrypt : Prog isa := scrubSel 0 2832 seqWords (Impl.StackScratch.Arm.withStackScratchWiped 2816 1 698 Impl.Camellia.Arm.cbcEncryptChained)

/-- `vg_camellia_cbc_decrypt_chained`. -/
def cbcDecrypt : Prog isa := scrubSel 0 3040 wideWords (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cbcDecryptChained)

/-- `vg_camellia_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := scrubSel 0 2832 seqWords (Impl.StackScratch.Arm.withStackScratchWiped 2816 1 698 Impl.Camellia.Arm.cfbEncrypt)

/-- `vg_camellia_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := scrubSel 0 3040 wideWords (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbDecrypt)

/-- `vg_camellia_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := scrubSel 0 2912 finalWords (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbEncryptFinal)

/-- `vg_camellia_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := scrubSel 0 2912 finalWords (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbDecryptFinal)

/-- `vg_camellia_ctr`. -/
def ctr : Prog isa := scrubSel 0 3040 wideWords Impl.Camellia.Arm.ctrFramed

/-- `vg_camellia_ctr_final`. -/
def ctrFinal : Prog isa := scrubSel 0 3120 ctrFinalWords (Impl.StackScratch.Arm.withStackScratchWiped 72 1 14 Impl.Camellia.Arm.ctrFinal)

/-- `vg_camellia_ofb`. -/
def ofb : Prog isa := scrubSel 0 2832 seqWords (Impl.StackScratch.Arm.withStackScratchWiped 2816 1 698 Impl.Camellia.Arm.ofb)

/-- `vg_camellia_ofb_final`. -/
def ofbFinal : Prog isa := scrubSel 0 2912 finalWords (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.ofbFinal)

end VG.Impl.Camellia.Arm.Fn
