module

public import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
public import VerifiedGarbage.Impl.P256.EcdhAllocatedCode

/-! The field inversion of P-256's ECDH, in constant time: ten batches of the generic packed divsteps
(`Weierstrass/AArch64/Inv.lean`), each batch's update of `(f, g, a, b)` register-allocated. The
scheduler is untrusted; its output is certified against the generic update, `updateRaw`. -/

@[expose] public section

namespace VG.Impl.P256.EcdhInverse
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64

def cfg : InvCfg := p256.invP

def updateRaw : List Instr := .movz .x .x12 0 0 :: cfg.fgUpdate ++ cfg.abUpdate

def update : List Instr := EcdhAllocatedCode.inverseUpdate

/-- The registers the allocation uses that the inversion's caller expects kept. -/
def extra : List (Reg × Nat) :=
  [(.x21,7800),(.x22,7808),(.x23,7816),(.x24,7824),(.x25,7832),(.x26,7840),(.x27,7848),(.x28,7856),(.x30,7864)]
def saveExtra : List Instr := extra.map fun (r,off) => st r off
def restoreExtra : List Instr := extra.map fun (r,off) => ld r off

def batch : Prog isa :=
  .seq (.block cfg.batchStart) (.seq (.block pwords) (.block update))

def body : Prog isa :=
  .seq (.block cfg.init) (.seq (.loop batch (.nonzero .x .x19)) (.block cfg.finish))

def inverse : Prog isa :=
  .seq (.block saveExtra) (.seq body (.block restoreExtra))

end VG.Impl.P256.EcdhInverse
