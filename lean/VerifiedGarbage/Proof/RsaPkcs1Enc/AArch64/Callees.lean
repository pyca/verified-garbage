import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
import VerifiedGarbage.Proof.Rsa.AArch64.PubChecked

/-!
# `vg_rsa_public_checked` as encryption's callee on AArch64

`vg_rsa_public_checked` uses no stack, so the shared contract with none
implies it with any (`public_stack`): the stack is only in the
precondition, which asks less of the caller with less. With one byte, it is
a `PubImpl` (`pubImpl`).
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

end VG.Proof.RsaPkcs1Enc.AArch64
