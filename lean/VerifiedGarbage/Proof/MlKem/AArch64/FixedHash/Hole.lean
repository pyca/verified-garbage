module

public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashCallers
public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHash
import VerifiedGarbage.Proof.Framework.CallFill

/-!
# The fixed hash over any single-state permutation, and over a hole

ML-KEM's paired path hashes with the fixed hash (`fixedHash c`), which calls a
Keccak backend's single-state permutation `c`. Its checks are decided once,
on the code built with the permutation's calls erased (`hole`, whose body is
empty), and hold of the code for every `c`, which is that code with its holes
filled (`Code.fillHoles c.name c.code`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.FixedHash

open VG VG.AArch64

/-- A callee with an empty body: its calls are the holes of `Code.fillHoles`. -/
def hole : Impl.Sha3.AArch64.Callee where
  name := ""
  code := .block []
  suffix := ""

/-- The fixed hash, calling the permutation `c`. -/
abbrev fixedHash (c : Impl.Sha3.AArch64.Callee) : Impl.MlKem.AArch64.FixedHashCallers.HashFn :=
  Impl.MlKem.AArch64.FixedHash.code c

end VG.Proof.MlKem.AArch64.FixedHash
