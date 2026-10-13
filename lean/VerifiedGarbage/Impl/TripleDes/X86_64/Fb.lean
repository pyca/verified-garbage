module

public import VerifiedGarbage.Impl.TripleDes.X86_64.Cbc
public import VerifiedGarbage.Impl.Modes.X86_64.Cfb8

/-!
# Triple DES-OFB, -CFB64 and -CFB8 on x86-64

`ofb`, `cfbEncrypt`, `cfbDecrypt`, `cfb8Encrypt` and `cfb8Decrypt`
(schedule = rdi, iv = rsi, data = rdx, n = rcx, scratch = r8): the modes'
generic OFB, CFB and CFB8 (`Impl/Modes/X86_64/Fb.lean`, `Cfb8.lean`) over
CBC encryption's core (`callCore .encrypt`, calling the scalar block function, one
8-byte block at a time), with the working space in the scratch buffer, which
the artifact allocates on the stack.
-/

@[expose] public section

namespace VG.Impl.TripleDes.X86_64

open VG.X86_64
open VG.Impl.Modes (FbMode)

/-- The registers of the arguments. -/
def fbRegs : Impl.Modes.X86_64.CtrRegs := ⟨.rsi, .rdx, .rcx, .r8⟩

/-- `vg_triple_des_ofb`. -/
def ofb : Prog isa := (callCore .encrypt).fb .ofb fbRegs

/-- `ofb` with the block function inlined. -/
def ofbI : Prog isa := (dirCore .encrypt).fb .ofb fbRegs

/-- `vg_triple_des_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := (callCore .encrypt).fb .cfbEnc fbRegs

/-- `cfbEncrypt` with the block function inlined. -/
def cfbEncryptI : Prog isa := (dirCore .encrypt).fb .cfbEnc fbRegs

/-- `vg_triple_des_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := (callCore .encrypt).fb .cfbDec fbRegs

/-- `cfbDecrypt` with the block function inlined. -/
def cfbDecryptI : Prog isa := (dirCore .encrypt).fb .cfbDec fbRegs

/-- `vg_triple_des_cfb8_encrypt`. -/
def cfb8Encrypt : Prog isa := (callCore .encrypt).cfb8 true fbRegs

/-- `cfb8Encrypt` with the block function inlined. -/
def cfb8EncryptI : Prog isa := (dirCore .encrypt).cfb8 true fbRegs

/-- `vg_triple_des_cfb8_decrypt`. -/
def cfb8Decrypt : Prog isa := (callCore .encrypt).cfb8 false fbRegs

/-- `cfb8Decrypt` with the block function inlined. -/
def cfb8DecryptI : Prog isa := (dirCore .encrypt).cfb8 false fbRegs

end VG.Impl.TripleDes.X86_64
