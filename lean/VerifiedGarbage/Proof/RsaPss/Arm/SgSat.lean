module

public import VerifiedGarbage.Proof.RsaPss.Arm.SgBase
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS signing on ARMv7: the contract is satisfiable

A state that meets `signContract` (`sign_sat`), for each hash function
ARMv7 registers RSASSA-PSS with: a modulus of 64 bytes, `e`, `p`, `q`,
`dP`, `dQ` and `qInv` of one byte, an empty salt, the working space it needs,
and the stack arguments at `0x8000`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Sg

open VG VG.Arm

/-- The state, for a digest of `D` bytes. -/
def satState (D : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x21 else
    if a = 0x8004 then 1 else
    if a = 0x8009 then 0x31 else
    if a = 0x800c then 1 else
    if a = 0x8011 then 0x32 else
    if a = 0x8014 then 1 else
    if a = 0x8019 then 0x33 else
    if a = 0x801c then 1 else
    if a = 0x8021 then 0x34 else
    if a = 0x8024 then 1 else
    if a = 0x8029 then 0x35 else
    if a = 0x802c then 1 else
    if a = 0x8031 then 0x30 else
    if a = 0x8035 then 0x36 else
    if a = 0x803e then 1 else
    if a = 0x8040 then 0x20 else
    if a = 0x8041 then 8 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x3300, 1⟩, ⟨0x3400, 1⟩, ⟨0x3500, 1⟩,
    ⟨0x3000, D⟩, ⟨0x3600, 0⟩, ⟨0x8000, 68⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x10000, 2080 * 8⟩]

theorem sign_sat_md5 : ∃ s, (spec Spec.Mgf1.md5).pre s := by
  sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] using satState 16

theorem sign_sat_sha1 : ∃ s, (spec Spec.Mgf1.sha1).pre s := by
  sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] using satState 20

theorem sign_sat_sha224 : ∃ s, (spec Spec.Mgf1.sha224).pre s := by
  sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] using satState 28

theorem sign_sat_sha256 : ∃ s, (spec Spec.Mgf1.sha256).pre s := by
  sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] using satState 32

theorem sign_sat_sha384 : ∃ s, (spec Spec.Mgf1.sha384).pre s := by
  sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] using satState 48

theorem sign_sat_sha512 : ∃ s, (spec Spec.Mgf1.sha512).pre s := by
  sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] using satState 64

theorem sign_sat_sha512_224 : ∃ s, (spec Spec.Mgf1.sha512_224).pre s := by
  sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] using satState 28

theorem sign_sat_sha512_256 : ∃ s, (spec Spec.Mgf1.sha512_256).pre s := by
  sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] using satState 32

end VG.Proof.RsaPss.Arm.Sg
