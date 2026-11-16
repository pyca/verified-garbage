module

public import VerifiedGarbage.Proof.Seed.AArch64.Lit
public import VerifiedGarbage.Impl.Seed.AArch64.Modes
import VerifiedGarbage.Proof.Seed.SboxLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Seed.SboxLit
meta import VerifiedGarbage.Proof.Seed.AArch64.Lit
meta import VerifiedGarbage.Impl.Seed.AArch64.Modes
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # SEED-CBC, -OFB and -CFB128's AArch64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG.AArch64 VG.Impl.Tbl.AArch64

/-! The serial core loads `S0` by immediates (`Serial.setup`), a lookup in
the specification's vector for each of its 256 bytes, which flattens its
rows and walks to the entry every time, and in both directions' code. The
code that loads it is evaluated once here, its bytes read from the packed
table (`Proof/Seed/SboxLit.lean`), and is the literal of the code the two
functions contain (`s0Load.lit_eq`). -/

/-- The code that loads `S0`, its bytes from the packed table. -/
private def s0Packed : List Instr := loadTable (fun k => BitVec.ofNat 8 (Proof.Seed.sNat false k))

materialize_value s0Packed

/-- The literal of the code that loads `S0` (private: only this module's
literals contain that code outside a literal). -/
private noncomputable abbrev s0Load.lit : List Instr := s0Packed.lit

private theorem s0Load.lit_eq : loadTable (fun k => Spec.Seed.s0.getD k 0) = s0Load.lit :=
  (congrArg loadTable (funext fun k => Proof.Seed.sTable_getD false k)).trans s0Packed.lit_eq

end VG.Proof.Seed.AArch64

namespace VG

materialize_code Impl.Seed.AArch64.serialCrypt
materialize_code Impl.Seed.AArch64.serialDecrypt
materialize_code Impl.Seed.AArch64.ecbEncrypt
materialize_code Impl.Seed.AArch64.ecbDecrypt
materialize_code Impl.Seed.AArch64.cbcEncryptChained
materialize_code Impl.Seed.AArch64.cbcDecryptChained
materialize_code Impl.Seed.AArch64.ofb
materialize_code Impl.Seed.AArch64.cfbEncrypt
materialize_code Impl.Seed.AArch64.cfbDecrypt

end VG
