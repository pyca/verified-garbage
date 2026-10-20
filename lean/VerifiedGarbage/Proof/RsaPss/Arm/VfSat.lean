module

public import VerifiedGarbage.Proof.RsaPss.Arm.VfBase
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the contract is satisfiable

A state that meets `verifyPrecomputedContract` (`verify_sat_<hash>`), for
each hash function ARMv7 registers RSASSA-PSS with: a modulus of 64 bytes,
`e` of one byte, a signature of 64 bytes, the working space it needs, the
precomputed values' 16 words, and the stack arguments at `0x8000`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm

/-- The state, for a digest of `D` bytes. -/
def satState (D : Nat) : State where
  gpr r := match r with
    | .r0 => 0x2000 | .r1 => 64 | .r2 => 0x2100 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x30 else
    if a = 0x8005 then 0x31 else
    if a = 0x8008 then 0x40 else
    if a = 0x8016 then 1 else
    if a = 0x8018 then 0x20 else
    if a = 0x8019 then 8 else
    if a = 0x801d then 0x70 else
    if a = 0x8020 then 0x10 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, D⟩, ⟨0x3100, 64⟩, ⟨0x7000, 128⟩, ⟨0x8000, 36⟩]
  wr := [⟨0x10000, 2080 * 8⟩]

theorem verify_sat_md5 : ∃ s, (spec Spec.Mgf1.md5).pre s := by
  sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
    using satState 16

theorem verify_sat_sha1 : ∃ s, (spec Spec.Mgf1.sha1).pre s := by
  sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
    using satState 20

theorem verify_sat_sha224 : ∃ s, (spec Spec.Mgf1.sha224).pre s := by
  sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
    using satState 28

theorem verify_sat_sha256 : ∃ s, (spec Spec.Mgf1.sha256).pre s := by
  sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
    using satState 32

theorem verify_sat_sha384 : ∃ s, (spec Spec.Mgf1.sha384).pre s := by
  sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
    using satState 48

theorem verify_sat_sha512 : ∃ s, (spec Spec.Mgf1.sha512).pre s := by
  sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
    using satState 64

theorem verify_sat_sha512_224 : ∃ s, (spec Spec.Mgf1.sha512_224).pre s := by
  sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
    using satState 28

theorem verify_sat_sha512_256 : ∃ s, (spec Spec.Mgf1.sha512_256).pre s := by
  sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
    using satState 32

end VG.Proof.RsaPss.Arm.Vf
