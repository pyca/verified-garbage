module

public import VerifiedGarbage.Proof.Cast5.AArch64.TblEcbVerified
public meta import VerifiedGarbage.Proof.Cast5.AArch64.TblEcbVerified
public import VerifiedGarbage.Proof.Cast5.Rounds
public meta import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Impl.Residue.AArch64
public meta import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Framework.AArch64.ResidueCT
meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueCT
import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
meta import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

-- separate module: only the registration needs it, and it imports the proof of ECB, which the residue analysis would otherwise be built with

/-!
# CAST5-ECB on AArch64 returns without secret residue

`ecbEncryptCleared` and `ecbDecryptCleared` are `ecbEncrypt` and
`ecbDecrypt`, then what they leave secret cleared: the registers that held
the halves of the block and the S-box lookups, the vector registers the
calling convention does not preserve, the high halves of `v8`–`v15`, whose
low halves they restore, from `x6`, zeroed first, and the flags, from `x6`.
The residue analysis for two runs that leak the same
(`RTaintCT.noResidue_of_verified`) proves they leave nothing secret.
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64.Tbl

open VG VG.AArch64

/-- `c`, then the clears of what both directions leave. -/
abbrev ecbCleared (c : Prog isa) : Prog isa :=
  Impl.Residue.AArch64.withClearsHi [.x6, .x9, .x10, .x13, .x15]
    [.v0, .v1, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v27] (some .x6) .x6 [.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15] c

abbrev ecbEncryptCleared : Prog isa := ecbCleared Impl.Cast5.AArch64.Tbl.ecbEncrypt
abbrev ecbDecryptCleared : Prog isa := ecbCleared Impl.Cast5.AArch64.Tbl.ecbDecrypt

theorem ecbEncryptCleared_verified :
    Verified AArch64.target ecbEncryptCleared (Spec.Cast5.ecbEncryptContract AArch64.abi) :=
  Proof.Cast5.ecbEncrypt_keyed (show Verified AArch64.target ecbEncryptCleared
    (Proof.Cast5.ecbRoundsContract AArch64.abi .encrypt) from
    Clears.Verified.withClears (sig := Spec.Cast5.ecbSig) ecbEncrypt_verified (by decide))

theorem ecbDecryptCleared_verified :
    Verified AArch64.target ecbDecryptCleared (Spec.Cast5.ecbDecryptContract AArch64.abi) :=
  Proof.Cast5.ecbDecrypt_keyed (show Verified AArch64.target ecbDecryptCleared
    (Proof.Cast5.ecbRoundsContract AArch64.abi .decrypt) from
    Clears.Verified.withClears (sig := Spec.Cast5.ecbSig) ecbDecrypt_verified (by decide))

theorem ecbEncryptCleared_noResidue :
    NoResidue ecbEncryptCleared (Spec.Cast5.ecbEncryptContract AArch64.abi) 0 :=
  RTaintCT.noResidue_of_verified ecbEncryptCleared_verified ⟨_, by taint_decide_ct⟩

theorem ecbDecryptCleared_noResidue :
    NoResidue ecbDecryptCleared (Spec.Cast5.ecbDecryptContract AArch64.abi) 0 :=
  RTaintCT.noResidue_of_verified ecbDecryptCleared_verified ⟨_, by taint_decide_ct⟩

end VG.Proof.Cast5.AArch64.Tbl
