import VerifiedGarbage.Impl.RsaPss.X86_64
import VerifiedGarbage.Proof.RsaPss.X86_64.CtBase

/-!
# RSASSA-PSS on x86-64: the taint checks of each hash function

The pieces of the code between its calls whose instructions depend on the
hash function (its sizes, as immediates) are checked by the taint analysis
once for each hash function (`by taint_decide`, in its file under
`Proof/Pbkdf2/Md/X86_64/Hashes/`): `PssChecks P D`, for the parameters `P`
of its streaming code and its digest size `D`. The code of a hash function
`H` is that of `ckH H.P H.D`, by definition.
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Impl.MdStream.X86_64 (Params)

/-- A hash function with the parameters `P` and the digest size `D`, and no
functions to call. -/
def ckH (P : Params) (D : Nat) : Hash := ⟨P, D, 0, "", .block [], "", .block [], "", "", "", "", ""⟩

/-- The pieces of `ctHash` and `mgfXor`, with `n` writable regions after the
frame. -/
structure HashChecks (P : Params) (D : Nat) (n : Nat) : Prop where
  pad80 : ∃ hc, (taint.check (pT n [21, 28] []) (pad80 (ckH P D)) hc).isSome = true
  lenField : ∃ hc, (taint.check (pT n [21] []) (.block (lenField (ckH P D))) hc).isSome = true
  lenLoop : ∃ hc, (taint.check (pT n [21, 28] []) (lenLoop (ckH P D)) hc).isSome = true
  compArgs : ∃ hc, (taint.check (pT n [21, 29] []) (.block (compArgs (ckH P D))) hc).isSome = true
  select : ∃ hc, (taint.check (pT n [21, 29] []) (select (ckH P D)) hc).isSome = true
  digestOut : ∃ hc, (taint.check (pT n [21] []) (.block (digestOut (ckH P D))) hc).isSome = true
  clearCopyH : ∃ hc, (taint.check (pT n [21, 23, 24] []) (.seq (clearBlock (ckH P D)) (copyH (ckH P D))) hc).isSome
    = true
  counter : ∃ hc, (taint.check (pT n [31] [.rcx]) (.block (counter (ckH P D))) hc).isSome = true
  xorOut : ∃ hc, (taint.check (pT n [21, 23, 24, 32] []) (xorOut (ckH P D)) hc).isSome = true
  nextCtr : ∃ hc, (taint.check (pT n [24, 31, 32] []) (.block (nextCtr (ckH P D))) hc).isSome = true
  digestState : ∃ hc, (taint.check (pT n [21] []) (.block (digestAt (ckH P D) oSt)) hc).isSome = true
  fixedPad80 : ∃ hc, (taint.check (pT n [21, 28] []) (fixedPad80 (D + 4)) hc).isSome = true

/-- The pieces of verification. -/
structure VerifyChecks (P : Params) (D : Nat) : Prop where
  emLen : ∃ hc, (taint.check (pT 1 [17] [.rax]) (.seq (.block smear) (emLen (ckH P D))) hc).isSome = true
  salt : ∃ hc, (taint.check (pT 1 [17, 26] [.rdx]) (.block ([.mov .rax (.mem (sp sK)), .mov .r8 (.mem (sp sLo)),
    .alu .sub .rax (.reg .r8)] ++ saltFits (ckH P D))) hc).isSome = true
  posCheck : ∃ hc, (taint.check (pT 1 [24, 35, 36] []) (posCheck (ckH P D)) hc).isSome = true
  copyDigest : ∃ hc, (taint.check (pT 1 [21, 37] []) (.seq clearY (copyDigest (ckH P D))) hc).isSome = true
  copyFixedSalt : ∃ hc, (taint.check (pT 1 [23, 24, 36] [.rcx])
    (copyFixedSalt (ckH P D)) hc).isSome = true
  fixedSaltLen : ∃ hc, (taint.check (pT 1 [36] [])
    (.block (hashSaltLen (ckH P D) 36)) hc).isSome = true
  copyDb : ∃ hc, (taint.check (pT 1 [23, 24] [.rcx]) (copyDb (ckH P D)) hc).isSome = true
  shiftPass : ∃ hc, (taint.check (pT 1 [21, 24, 46] []) (shiftPass (ckH P D)) hc).isSome = true
  verifyNb : ∃ hc, (taint.check (pT 1 [24] []) (.block (verifyNb (ckH P D))) hc).isSome = true
  cmpH : ∃ hc, (taint.check (pT 1 [21, 23, 24] []) (cmpH (ckH P D)) hc).isSome = true

/-- The pieces of signing. -/
structure SignChecks (P : Params) (D : Nat) : Prop where
  emLen : ∃ hc, (taint.check (pT 2 [17] [.rax]) (.seq (.block smear) (emLen (ckH P D))) hc).isSome = true
  salt : ∃ hc, (taint.check (pT 2 [40] [.rax]) (.block ([.mov .rdx (.mem (sp sSaltLen))] ++ saltFits (ckH P D))) hc).isSome
    = true
  copyDigest : ∃ hc, (taint.check (pT 2 [21, 37] []) (.seq clearY (copyDigest (ckH P D))) hc).isSome = true
  copySaltY : ∃ hc, (taint.check (pT 2 [39, 40] [.rcx]) (copySaltY (ckH P D)) hc).isSome = true
  signLen : ∃ hc, (taint.check (pT 2 [40] []) (.block (signLen (ckH P D))) hc).isSome = true
  /-- `putH`'s copy of `H` (the rest reloads its words). -/
  putH : ∃ hc, (taint.check (pT 2 [21, 23, 24] [])
    (.seq (.block ([.mov .rdi (.mem (sp sEb)), .mov .rax (.mem (sp sDb)), .alu .add .rdi (.reg .rax)] ++
      scr .rsi oDig ++ [.mov32 .r8 (.imm 0)]))
      (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rdi .r8) .rax] (.imm (BitVec.ofNat 32 (ckH P D).D)))) hc).isSome
    = true

/-- All of them, for one hash function. -/
structure PssChecks (P : Params) (D : Nat) : Prop where
  hash1 : HashChecks P D 1
  hash2 : HashChecks P D 2
  verify : VerifyChecks P D
  sign : SignChecks P D

end VG.Proof.RsaPss.X86_64
