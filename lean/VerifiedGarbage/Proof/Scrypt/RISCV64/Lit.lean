module

public import VerifiedGarbage.Impl.Scrypt.RISCV64.RoMix
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Scrypt.RISCV64.RoMix
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-!
# scrypt on RISC-V: the code as literals
-/

@[expose] public section

namespace VG

materialize_code salsaW := Impl.Scrypt.RISCV64.salsa true
materialize_code salsaB := Impl.Scrypt.RISCV64.salsa false
materialize_code blockMixW := Impl.Scrypt.RISCV64.blockMix true
materialize_code blockMixB := Impl.Scrypt.RISCV64.blockMix false
materialize_code roMixW := Impl.Scrypt.RISCV64.roMix true
materialize_code roMixB := Impl.Scrypt.RISCV64.roMix false

end VG
