module

public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCtx
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
public import VerifiedGarbage.Spec.RsaOaep.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSAES-OAEP encryption on x86-64: the contract on the registers

`encK H G` states the postcondition and the public data of
`Spec.RsaOaep.encryptAnyContract` for the hash functions `H` and `G` (with
the stack the frame and the calls use, `encStack`) on the registers and the
stack, which `vg_rsa_oaep_encrypt_precomputed` meets when `pre` holds the
values for `n` (`PcContract`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The stack below the stack pointer: the frame of 360 bytes, and the 16
bytes below it that the calls of the streaming hash functions use (the
public operation only its return address). -/
def encStack : Nat := 360 + 16

theorem stackArgs_twelve (s : State) :
    List.map (stackArg s) (List.range 12) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11] := rfl

/-- Entry states agreeing on the registers holding arguments, the stack
arguments (`label = [rsp + 8]`, …, `mgf1_hash = [rsp + 96]`), `n` and `e`. -/
def encPub (s₁ s₂ : State) : Prop :=
  (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
    (List.range 12).map (stackArg s₁) = (List.range 12).map (stackArg s₂) ∧
    Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
      Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
    Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
      Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat

variable (H G : Spec.Mgf1.Hash)

/-- What encryption's pieces are proven against, for the label's hash
function `H` and MGF1's `G`: its result written to `out` (`post`), from
entry states agreeing as `encPub` says (`pub`). -/
def encK : Contract isa where
  pre _ := True
  post s s' :=
    Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.RsaOaep.encrypt H G (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) H.len))
  pub := encPub

end VG.Proof.RsaOaep.X86_64
