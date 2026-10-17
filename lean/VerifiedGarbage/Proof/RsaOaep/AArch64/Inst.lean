module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncVerified
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Callees
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Sha512.Word64
import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# RSAES-OAEP on AArch64: the instances emitted

The CPU features of an instance (`features`): its tier's and its RSA
operation's; and states meeting both contracts, for the registration files.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (Tier)

namespace Inst

/-- The CPU features of the tier `t` and of an RSA operation's, each once. -/
def features (t : Tier) (cf : List String) : List String := t.features ++ cf.filter (!t.features.contains ·)

end Inst

/-! ## States meeting the contracts -/

theorem stackArgs_ten (s : State) :
    List.map (stackArg s) (List.range 10) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9] := rfl

/-- A state meeting encryption's contract: a 512-bit modulus, a one-byte
`e`, an empty label and message, SHA-256 (3) for both hash functions and
its 32-byte seed, a working space of 2080 words, 16 words of `pre` at
`0x5000`, and the stack arguments at `0x10000`. -/
def encSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x3000 | .x5 => 1 | .x6 => 0x4000
    | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10001 then 0x41 else bif Nat.beq a.toNat 0x10011 then 0x42
    else bif Nat.beq a.toNat 0x10018 then 32 else bif Nat.beq a.toNat 0x10022 then 0x02
    else bif Nat.beq a.toNat 0x10028 then 0x20 else bif Nat.beq a.toNat 0x10029 then 0x08
    else bif Nat.beq a.toNat 0x10031 then 0x50 else bif Nat.beq a.toNat 0x10038 then 16
    else bif Nat.beq a.toNat 0x10040 then 3 else bif Nat.beq a.toNat 0x10048 then 3 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x4100, 0⟩, ⟨0x4200, 32⟩, ⟨0x5000, 128⟩, ⟨0x10000, 80⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 16640⟩]

theorem enc_sat (v : Proof.Rsa.AArch64.PublicImpl) :
    ∃ s, (Spec.RsaOaep.encryptAnyContract AArch64.abi (Enc.encStack (RsaPkcs1Sig.AArch64.pdOf v))).pre s := by
  sig_implies_sat [Spec.RsaOaep.encryptAnyContract, Spec.RsaOaep.encryptAnySig, AArch64.abi,
      AArch64.argRegs, Enc.encStack, Enc.encP, RsaPkcs1Sig.AArch64.pdOf, stackArgs_ten, List.append_eq,
      Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords,
      Spec.Rsa.precomputedWords, Spec.RsaOaep.hashIds, Spec.HashId.mgf1, Spec.Mgf1.hashes]
      [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState

theorem stackArgs_seventeen (s : State) :
    List.map (stackArg s) (List.range 17) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16] := rfl

/-- A state meeting decryption's contract: a 512-bit modulus, one-byte `e`,
primes, exponents and `qInv`, an empty label, SHA-256 (3) for both hash
functions, a working space of 2048 words, and the stack arguments at
`0x10000`. -/
def decSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x1800 | .x3 => 0x2000 | .x4 => 64 | .x5 => 0x3000 | .x6 => 1
    | .x7 => 0x4200 | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10070 then 0x20
    else bif Nat.beq a.toNat 0x10000 then 1 else bif Nat.beq a.toNat 0x10009 then 0x43
    else bif Nat.beq a.toNat 0x10010 then 1 else bif Nat.beq a.toNat 0x10019 then 0x44
    else bif Nat.beq a.toNat 0x10020 then 1 else bif Nat.beq a.toNat 0x10029 then 0x45
    else bif Nat.beq a.toNat 0x10030 then 1 else bif Nat.beq a.toNat 0x10039 then 0x46
    else bif Nat.beq a.toNat 0x10040 then 1 else bif Nat.beq a.toNat 0x10049 then 0x47
    else bif Nat.beq a.toNat 0x10059 then 0x41 else bif Nat.beq a.toNat 0x10060 then 64
    else bif Nat.beq a.toNat 0x1006A then 0x02 else bif Nat.beq a.toNat 0x10071 then 0x08
    else bif Nat.beq a.toNat 0x10078 then 3 else bif Nat.beq a.toNat 0x10080 then 3 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x4600, 1⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x10000, 136⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

theorem dec_sat (c : Proof.Rsa.AArch64.CrtImpl) :
    ∃ s, (Spec.RsaOaep.decryptAnyContract AArch64.abi (Dec.decStack (RsaPkcs1Enc.AArch64.privOf c))).pre s := by
  refine ⟨decSatState, ?_⟩
  -- The precondition does not depend on the implementation: with the stack
  -- literal, `sig_sat_check` decides it in the kernel.
  change (Spec.RsaOaep.decryptAnyContract AArch64.abi 3536).pre decSatState
  sig_sat_check [Spec.RsaOaep.decryptAnyContract, Spec.RsaOaep.decryptAnySig, AArch64.abi, AArch64.argRegs,
    stackArgs_seventeen, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords,
    Spec.RsaOaep.hashIds]

end VG.Proof.RsaOaep.AArch64
