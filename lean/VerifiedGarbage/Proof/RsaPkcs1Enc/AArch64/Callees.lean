import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecVerified
import VerifiedGarbage.Proof.Rsa.AArch64.PrivVerified
import VerifiedGarbage.Proof.Rsa.AArch64.PubChecked

/-!
# `vg_rsa_public_checked` as encryption's callee on AArch64

`vg_rsa_public_checked` uses no stack, so the shared contract with none
implies it with any (`public_stack`): the stack is only in the
precondition, which asks less of the caller with less. With one byte, it is
a `PubImpl` (`pubImpl`). For each implementation `c` of `vg_rsa_private_crt`
(a variant of `RsaPrivateCrt`), `vg_rsa_private_checked` calling it, as
`Generic/RsaPrivateCrt/AArch64/Rsa.lean` emits it, is a `PrivImpl`
(`privOf`).
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64

open VG VG.AArch64

theorem public_stack (n : Nat) (hsat : ∃ s, (Spec.Rsa.publicCheckedContract AArch64.abi n).pre s) :
    (Spec.Rsa.publicCheckedContract AArch64.abi).Implies (Spec.Rsa.publicCheckedContract AArch64.abi n) where
  pre := by
    intro s h
    sig_pre [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, AArch64.abi, AArch64.argRegs,
      Proof.Rsa.AArch64.stackArgs_two, List.append_eq] at h
    sig_pre [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, AArch64.abi, AArch64.argRegs,
      Proof.Rsa.AArch64.stackArgs_two, List.append_eq]
    obtain ⟨-, a, b, c, d, e, f, -, rest⟩ := h
    exact ⟨a, b, c, d, e, f, rest⟩
  post _ _ _ h := h
  pub _ _ _ _ h := h
  sat := hsat

theorem public_sat : ∃ s, (Spec.Rsa.publicCheckedContract AArch64.abi 1).pre s := by
  sig_implies_sat [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, AArch64.abi, AArch64.argRegs,
    Proof.Rsa.AArch64.stackArgs_two, List.append_eq] [Proof.Rsa.AArch64.pubSatState, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using Proof.Rsa.AArch64.pubSatState

/-- `vg_rsa_public_checked`, as encryption's callee. -/
def pubImpl : PubImpl where
  name := Spec.Rsa.publicCheckedApi.name
  code := Impl.Rsa.AArch64.Checked.publicChecked
  stack := 1
  verified := Verified.of_implies Proof.Rsa.AArch64.publicChecked_verified (public_stack 1 public_sat)
  pos := by decide
  depth := by decide +kernel
  spSafe := Code.all_of_forall (fun _ => rfl) _

theorem stackArgs_four (s : State) :
    List.map (stackArg s) (List.range 4) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

/-- A state meeting encryption's contract with `pubImpl`: a 512-bit modulus, a
one-byte `e`, an empty message, a padding string of 61 bytes, and the stack
arguments at `0x10000`. -/
def encSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x3000 | .x5 => 1 | .x6 => 0x4000
    | _ => 0
  sp := 0x10000
  mem a := if a = 0x10001 then 0x41 else if a = 0x10008 then 61 else if a = 0x10012 then 0x02
    else if a = 0x10019 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x4100, 61⟩, ⟨0x10000, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 8192⟩]

theorem enc_sat : ∃ s, (Spec.RsaPkcs1Enc.encryptContract AArch64.abi (Enc.encStack pubImpl)).pre s := by
  sig_implies_sat [Spec.RsaPkcs1Enc.encryptContract, Spec.RsaPkcs1Enc.encryptSig, AArch64.abi, AArch64.argRegs,
    Enc.encStack, pubImpl, stackArgs_four, List.append_eq] [encSatState, stackArg, stackArgAddr, Mem.readW,
    Mem.read] using encSatState

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
  mem a := if a = 0x10000 then 1 else if a = 0x10009 then 0x41 else if a = 0x10010 then 64
    else if a = 0x10019 then 0x42 else if a = 0x10020 then 1 else if a = 0x10029 then 0x43
    else if a = 0x10030 then 1 else if a = 0x10039 then 0x44 else if a = 0x10040 then 1
    else if a = 0x10049 then 0x45 else if a = 0x10050 then 1 else if a = 0x10059 then 0x46
    else if a = 0x10060 then 1 else if a = 0x1006A then 0x02 else if a = 0x10071 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x4100, 64⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x4500, 1⟩, ⟨0x4600, 1⟩, ⟨0x10000, 120⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 8192⟩]

theorem dec_sat (c : Proof.Rsa.AArch64.CrtImpl) :
    ∃ s, (Spec.RsaPkcs1Enc.decryptContract AArch64.abi (Dec.decStack (privOf c))).pre s := by
  -- A literal stack lets `sig_sat_check` decide the precondition in the kernel.
  rw [show Dec.decStack (privOf c) = 3472 from rfl]
  sig_implies_sat [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs,
    stackArgs_fifteen, List.append_eq, Spec.Rsa.lenValid] [decSatState] using decSatState

end VG.Proof.RsaPkcs1Enc.AArch64
