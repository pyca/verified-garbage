module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecVerified
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivVerified
public import VerifiedGarbage.Impl.Rsa.AArch64
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Rsa.AArch64.PubChecked
import Mathlib.Data.List.Basic
public import VerifiedGarbage.Proof.Rsa.Contract

/-!
# `vg_rsa_private_checked` as decryption's callee on AArch64

For each implementation `c` of `vg_rsa_private_crt`
(a variant of `RsaPrivateCrt`), `vg_rsa_private_checked` calling it, the
internal function the padding functions call, is a `PrivImpl`
(`privOf`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64

open VG VG.AArch64

/-- `vg_rsa_private_checked` calling `c`, as decryption's callee. -/
def privOf (c : Proof.Rsa.AArch64.CrtImpl) : PrivImpl where
  name := Proof.Rsa.AArch64.privName c
  code := Proof.Rsa.AArch64.privCode c
  stack := Proof.Rsa.AArch64.stackBytes
  verified := Proof.Rsa.AArch64.code_verified c
  pos := by decide
  depth := by rw [Proof.Rsa.AArch64.privCode_depth]; decide
  spSafe := Code.all_of_forall (fun _ => rfl) _

theorem stackArgs_fifteen (s : State) :
    List.map (stackArg s) (List.range 15) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14] := rfl

/-- A state meeting decryption's contract with `privOf c`: a 512-bit modulus,
one-byte `e`, `d`, primes, exponents and `qInv`, and the stack arguments at
`0x10000`. -/
def decSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x1800 | .x3 => 0x2000 | .x4 => 64 | .x5 => 0x3000 | .x6 => 1
    | .x7 => 0x4000 | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10070 then 0x20
    else bif Nat.beq a.toNat 0x10000 then 1 else bif Nat.beq a.toNat 0x10009 then 0x41
    else bif Nat.beq a.toNat 0x10010 then 64 else bif Nat.beq a.toNat 0x10019 then 0x42
    else bif Nat.beq a.toNat 0x10020 then 1 else bif Nat.beq a.toNat 0x10029 then 0x43
    else bif Nat.beq a.toNat 0x10030 then 1 else bif Nat.beq a.toNat 0x10039 then 0x44
    else bif Nat.beq a.toNat 0x10040 then 1 else bif Nat.beq a.toNat 0x10049 then 0x45
    else bif Nat.beq a.toNat 0x10050 then 1 else bif Nat.beq a.toNat 0x10059 then 0x46
    else bif Nat.beq a.toNat 0x10060 then 1 else bif Nat.beq a.toNat 0x1006A then 0x02
    else bif Nat.beq a.toNat 0x10071 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x4100, 64⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x4500, 1⟩, ⟨0x4600, 1⟩, ⟨0x10000, 120⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 8448⟩]

theorem dec_sat (c : Proof.Rsa.AArch64.CrtImpl) :
    ∃ s, (Spec.RsaPkcs1Enc.decryptContract AArch64.abi (Dec.decStack (privOf c))).pre s := by
  -- A literal stack lets `sig_sat_check` decide the precondition in the kernel.
  rw [show Dec.decStack (privOf c) = 3472 from rfl]
  sig_implies_sat [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs,
    stackArgs_fifteen, List.append_eq, Spec.Rsa.lenValid] [decSatState] using decSatState

end VG.Proof.RsaPkcs1Enc.AArch64
