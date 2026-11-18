module

public import VerifiedGarbage.Impl.TripleDes.X86.Modes

/-!
# Triple DES-OFB, -CFB64 and -CFB8 on x86 (32-bit)

The modes' OFB, CFB and CFB8 (`Impl/Modes/X86/Seq.lean`) over Triple DES's
core in the encryption direction (`Modes.lean`), with the scratch buffer as
the fifth argument. CFB64 decryption, whose blocks can be deciphered
independently, takes them in groups on the bitsliced core (`wideCore`,
`Impl/Modes/X86/Wide.lean`); the others call the block function once a
block.
-/

@[expose] public section

namespace VG.Impl.TripleDes.X86

open VG.X86

/-- `vg_triple_des_ofb`. -/
def ofb : Prog isa := (dirCore .encrypt).seq (Modes.Mode.ofb 2)

/-- `vg_triple_des_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbEnc 2)

/-- `vg_triple_des_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa :=
  (wideCore .encrypt).seqLevels (Modes.Mode.cfbDecWide 2) levels (Modes.Mode.cfbDecEarly 2)

/-- `vg_triple_des_cfb8_encrypt`. -/
def cfb8Encrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfb8Enc 2)

/-- `vg_triple_des_cfb8_decrypt`. -/
def cfb8Decrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfb8Dec 2)

end VG.Impl.TripleDes.X86
