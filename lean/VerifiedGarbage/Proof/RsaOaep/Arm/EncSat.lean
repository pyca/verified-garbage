module

public import VerifiedGarbage.Proof.RsaOaep.Arm.EncBase
import all Init.Data.Nat.Bitwise.Basic

/-!
# RSAES-OAEP encryption with a precomputed public key on ARMv7: the contract is satisfiable

A state that meets `encryptPrecomputedContract` (`encrypt_sat_<hash>`, for
any MGF1 hash function), for each hash function ARMv7 registers RSAES-OAEP
with: a modulus of 64 bytes, `e` of one byte, an empty label and message,
the seed, the working space it needs, the precomputed values' 16 words, and
the stack arguments at `0x8000`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Enc

open VG VG.Arm

/-- The state, for a seed of `D` bytes. -/
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
    if a = 0x8009 then 0x30 else
    if a = 0x8011 then 0x31 else
    if a = 0x8019 then 0x32 else
    if a = 0x801e then 1 else
    if a = 0x8020 then 0x20 else
    if a = 0x8021 then 8 else
    if a = 0x8025 then 0x70 else
    if a = 0x8028 then 0x10 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, D⟩, ⟨0x7000, 128⟩, ⟨0x8000, 44⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x10000, 2080 * 8⟩]

theorem encrypt_sat_sha1 (G : Spec.Mgf1.Hash) : ∃ s, (spec Spec.Mgf1.sha1 G).pre s := by
  sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
    using satState 20

theorem encrypt_sat_sha224 (G : Spec.Mgf1.Hash) : ∃ s, (spec Spec.Mgf1.sha224 G).pre s := by
  sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
    using satState 28

theorem encrypt_sat_sha256 (G : Spec.Mgf1.Hash) : ∃ s, (spec Spec.Mgf1.sha256 G).pre s := by
  sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
    using satState 32

theorem encrypt_sat_sha384 (G : Spec.Mgf1.Hash) : ∃ s, (spec Spec.Mgf1.sha384 G).pre s := by
  sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
    using satState 48

theorem encrypt_sat_sha512 (G : Spec.Mgf1.Hash) : ∃ s, (spec Spec.Mgf1.sha512 G).pre s := by
  sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
    using satState 64

theorem encrypt_sat_sha512_224 (G : Spec.Mgf1.Hash) : ∃ s, (spec Spec.Mgf1.sha512_224 G).pre s := by
  sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
    using satState 28

theorem encrypt_sat_sha512_256 (G : Spec.Mgf1.Hash) : ∃ s, (spec Spec.Mgf1.sha512_256 G).pre s := by
  sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
    Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
    using satState 32

end VG.Proof.RsaOaep.Arm.Enc
