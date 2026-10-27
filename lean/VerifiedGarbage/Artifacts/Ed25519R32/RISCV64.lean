module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's point addition, in radix `2^32`, on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed25519R32.RISCV64

open VG.Spec.Ed25519.Point32 VG.Impl.Ed25519.RISCV64 VG.Proof.Ed25519.RISCV64

/-- How the function works. -/
def notes : List String := ["Uses baseline integer instructions, only caller-saved registers \
  and no stack. The function runs the complete addition formula: nine products of eight-word \
  field elements, by X25519's RISC-V product inlined (row by row, with `mul`, then `lo + 38 hi` \
  and the carry folded in), and additions and subtractions (`a - b + 4p`, so that every word is \
  a natural number), with the temporaries in bytes 320 to 575."]

def artifacts : List Artifact := [
  addApi.artifact RISCV64.target {
    notes := notes
    code := addFn
    verified := addFn_verified }]

end VG.Artifacts.Ed25519R32.RISCV64
