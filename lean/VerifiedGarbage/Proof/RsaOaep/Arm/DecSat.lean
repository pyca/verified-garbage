module

public import VerifiedGarbage.Proof.RsaOaep.Arm.DecBase
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-OAEP decryption on ARMv7: the contract is satisfiable

A state that meets `decryptContract` (`dec_sat`), whatever the hash
functions: a modulus of 64 bytes, `e`, `p`, `q`, `dP`, `dQ` and `qInv` of
one byte, an empty label, the working space it needs, and the stack
arguments at `0x8000`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm

/-- The state. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x1100 | .r3 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 0x40 else
    if a = 0x8005 then 0x21 else
    if a = 0x8008 then 1 else
    if a = 0x800d then 0x31 else
    if a = 0x8010 then 1 else
    if a = 0x8015 then 0x32 else
    if a = 0x8018 then 1 else
    if a = 0x801d then 0x33 else
    if a = 0x8020 then 1 else
    if a = 0x8025 then 0x34 else
    if a = 0x8028 then 1 else
    if a = 0x802d then 0x35 else
    if a = 0x8030 then 1 else
    if a = 0x8035 then 0x36 else
    if a = 0x803d then 0x37 else
    if a = 0x8040 then 0x40 else
    if a = 0x8046 then 1 else
    if a = 0x8048 then 0x20 else
    if a = 0x8049 then 8 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x3300, 1⟩, ⟨0x3400, 1⟩, ⟨0x3500, 1⟩,
    ⟨0x3600, 0⟩, ⟨0x3700, 64⟩, ⟨0x8000, 76⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 8⟩, ⟨0x10000, 2080 * 8⟩]

theorem dec_sat (h g : OHash) : ∃ s, (spec h g).pre s := by
  sig_implies_sat [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] using satState

end VG.Proof.RsaOaep.Arm.Dec
