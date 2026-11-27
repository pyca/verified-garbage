module

public import VerifiedGarbage.Impl.Sm4.X86.Modes

/-!
# SM4-OFB and SM4-CFB128 on x86 (32-bit)

The modes' OFB and CFB (`Impl/Modes/X86/Seq.lean`) over SM4's core in the
encryption direction (`Modes.lean`), with the scratch buffer as the fifth
argument. CFB128 decryption takes the blocks in groups (`levels`,
`Impl/Modes/X86/Wide.lean`).
-/

@[expose] public section

namespace VG.Impl.Sm4.X86

open VG.X86

/-- `vg_sm4_ofb`. -/
def ofb : Prog isa := (dirCore .encrypt).seq (Modes.Mode.ofb 4)

/-- `vg_sm4_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbEnc 4)

/-- `vg_sm4_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa :=
  (dirCore .encrypt).seqLevels (Modes.Mode.cfbDecWide 4) levels (Modes.Mode.cfbDecEarly 4)

end VG.Impl.Sm4.X86
