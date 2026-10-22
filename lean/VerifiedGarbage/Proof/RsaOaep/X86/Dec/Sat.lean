module

public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Base
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-OAEP decryption on x86: the contract is satisfiable

A state that meets `decryptContract` (`dec_sat`), whatever the hash
functions: a modulus of 64 bytes, `e`, `p`, `q`, `dP`, `dQ` and `qInv` of
one byte, an empty label, the working space it needs, and the arguments above
`esp = 0x20000`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes)

/-- The state. -/
def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 131077 then 0x10 else if a = 131080 then 0x40 else if a = 131085 then 0x11 else if a = 131089 then 0x20 else if a = 131092 then 0x40 else if a = 131097 then 0x21 else if a = 131100 then 0x1 else if a = 131105 then 0x31 else if a = 131108 then 0x1 else if a = 131113 then 0x32 else if a = 131116 then 0x1 else if a = 131121 then 0x33 else if a = 131124 then 0x1 else if a = 131129 then 0x34 else if a = 131132 then 0x1 else if a = 131137 then 0x35 else if a = 131140 then 0x1 else if a = 131145 then 0x36 else if a = 131153 then 0x37 else if a = 131156 then 0x40 else if a = 131162 then 0x1 else if a = 131164 then 0x20 else if a = 131165 then 0x8 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x3300, 1⟩, ⟨0x3400, 1⟩, ⟨0x3500, 1⟩,
    ⟨0x3600, 0⟩, ⟨0x3700, 64⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 8⟩, ⟨0x10000, 2080 * 8⟩, ⟨0x20004, 92⟩]

theorem dec_sat (H G : Spec.Mgf1.Hash) : ∃ s, (spec H G).pre s := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 0x1100 := by decide
  have a3 : arg satState 3 = 0x2000 := by decide
  have a4 : arg satState 4 = 64 := by decide
  have a5 : arg satState 5 = 0x2100 := by decide
  have a6 : arg satState 6 = 1 := by decide
  have a7 : arg satState 7 = 0x3100 := by decide
  have a8 : arg satState 8 = 1 := by decide
  have a9 : arg satState 9 = 0x3200 := by decide
  have a10 : arg satState 10 = 1 := by decide
  have a11 : arg satState 11 = 0x3300 := by decide
  have a12 : arg satState 12 = 1 := by decide
  have a13 : arg satState 13 = 0x3400 := by decide
  have a14 : arg satState 14 = 1 := by decide
  have a15 : arg satState 15 = 0x3500 := by decide
  have a16 : arg satState 16 = 1 := by decide
  have a17 : arg satState 17 = 0x3600 := by decide
  have a18 : arg satState 18 = 0 := by decide
  have a19 : arg satState 19 = 0x3700 := by decide
  have a20 : arg satState 20 = 64 := by decide
  have a21 : arg satState 21 = 0x10000 := by decide
  have a22 : arg satState 22 = 0x820 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argSlots, argVal, argBytes,
    stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, e, esp, satState, stackBytes, frameBytes, Spec.Rsa.lenValid, Spec.RsaPss.scratchWords,
      Spec.Rsa.scratchWords] using satState

end VG.Proof.RsaOaep.X86.Dec
