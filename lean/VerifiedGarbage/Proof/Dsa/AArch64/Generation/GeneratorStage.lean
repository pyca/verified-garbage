module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.ABI
public import VerifiedGarbage.Proof.Framework.AArch64.Depth

/-! # The generator stages parameter generation calls

`vg_dsa_generator_{bits}` for each width of p: each one's name, its code, its
proof, and the stack its frames use. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64

structure GeneratorStage where
  name : Nat → String
  code : Nat → Prog isa
  verified : ∀ pLen, Generator.Supported pLen → Verified target (code pLen) (Generator.contract pLen)
  depth : ∀ pLen, 16 * (code pLen).aarch64Depth ≤ 272

/-- The call of the stage for a p of `pLen` bytes. -/
def GeneratorStage.run (G : GeneratorStage) (pLen : Nat) : Prog isa := .call (G.name pLen) (G.code pLen)

end VG.Proof.Dsa.AArch64.Generation
