module

public import VerifiedGarbage.Impl.Seed.X86.ExpandKey
public import VerifiedGarbage.Impl.Seed.X86.FbFinal
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-!
# SEED on x86 (32-bit): the functions as emitted

Each function runs with its working space in a frame on the stack, wiped
before it returns (`withStackScratchWiped`), and is followed by its cleanup
(`Impl.Scrub.X86.scrubF 0 W`): the `W` bytes of stack below `esp` that its
contract reserves zeroed, and the registers a callee may change cleared, so
that it returns without secret residue. None returns a result.
-/

@[expose] public section

namespace VG.Impl.Seed.X86.Fn

open VG.X86
open Impl.StackScratch.X86 (withStackScratchWiped)

/-- `vg_seed_expand_key`, as emitted. -/
def expandKey : Prog isa := Impl.Scrub.X86.scrubF 0 840 (withStackScratchWiped 840 2 206 Seed.X86.expandKey)

/-- `vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt`, as emitted. -/
def ecb (d : Spec.Seed.Direction) : Prog isa :=
  Impl.Scrub.X86.scrubF 0 1132 (withStackScratchWiped 1108 3 272 (Seed.X86.ecbCall d))

/-- `vg_seed_cbc_encrypt_chained`, as emitted. -/
def cbcEncryptChained : Prog isa :=
  Impl.Scrub.X86.scrubF 0 1188 (withStackScratchWiped 1168 4 286 Seed.X86.cbcEncryptChained)

/-- `vg_seed_cbc_decrypt_chained`, as emitted. -/
def cbcDecryptChained : Prog isa :=
  Impl.Scrub.X86.scrubF 0 1188 (withStackScratchWiped 1168 4 286 Seed.X86.cbcDecryptChained)

/-- `vg_seed_cfb128_encrypt`, as emitted. -/
def cfbEncrypt : Prog isa := Impl.Scrub.X86.scrubF 0 1188 (withStackScratchWiped 1168 4 286 Seed.X86.cfbEncrypt)

/-- `vg_seed_cfb128_decrypt`, as emitted. -/
def cfbDecrypt : Prog isa := Impl.Scrub.X86.scrubF 0 1188 (withStackScratchWiped 1168 4 286 Seed.X86.cfbDecrypt)

/-- `vg_seed_cfb128_encrypt_final`, as emitted. -/
def cfbEncryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubF 0 1188 (withStackScratchWiped 1168 4 286 Seed.X86.cfbEncryptFinal)

/-- `vg_seed_cfb128_decrypt_final`, as emitted. -/
def cfbDecryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubF 0 1188 (withStackScratchWiped 1168 4 286 Seed.X86.cfbDecryptFinal)

/-- `vg_seed_ofb`, as emitted. -/
def ofb : Prog isa := Impl.Scrub.X86.scrubF 0 1188 (withStackScratchWiped 1168 4 286 Seed.X86.ofb)

/-- `vg_seed_ofb_final`, as emitted. -/
def ofbFinal : Prog isa := Impl.Scrub.X86.scrubF 0 1188 (withStackScratchWiped 1168 4 286 Seed.X86.ofbFinal)

end VG.Impl.Seed.X86.Fn
