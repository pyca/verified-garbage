import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# AES-OCB on ARMv7: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ocb/Contract.lean`, which imply these
(`Verified.lean`), with a 2560-byte `work` buffer appended
(`Proof/AesOcb/Scratch.lean`). `seal` and `open` call
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` in frames that push
their stack argument below the stack pointer: so the 8 bytes below the stack
pointer (`bel`) may not overlap any buffer.
-/

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (ctxCiph ctxInv ctxLstar encryptWith decryptWith lengthsOk zeros)

/-- The 8 bytes below the stack pointer, which the calls use. -/
abbrev bel (s : State) : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 32 := stackArg s i

/-- The arguments on the stack, `n` words of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 4 * n⟩

abbrev roundsOk (s : State) : Prop :=
  (s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14

/-- What `vg_aes_ocb_seal` and `vg_aes_ocb_open` both need, but for the
permissions: `(ctx = r0, rounds = r1, nonce = r2, nonce_len = r3,
aad = [sp], aad_len = [sp + 4], data = [sp + 8], len = [sp + 12],
tag = [sp + 16], tag_len = [sp + 20], work = [sp + 24])`. -/
def oneLay (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (arg s 0), (arg s 1).toNat⟩
  let data : Region := ⟨State.addr (arg s 2), (arg s 3).toNat⟩
  let tag : Region := ⟨State.addr (arg s 4), (arg s 5).toNat⟩
  let work : Region := ⟨State.addr (arg s 6), 2560⟩
  ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s 7) ∧ work.Disjoint (args s 7) ∧
    (bel s).Disjoint ctx ∧ (bel s).Disjoint nonce ∧ (bel s).Disjoint aad ∧ (bel s).Disjoint data ∧
    (bel s).Disjoint work ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
    (arg s 6).toNat + 2560 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧ s.sp.toNat + 28 ≤ 2 ^ 32 ∧ roundsOk s ∧
    lengthsOk (arg s 5).toNat (s.gpr .r3).toNat = true ∧
    tag.Disjoint data ∧ tag.Disjoint work ∧ (bel s).Disjoint tag ∧ (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32

/-- What `vg_aes_ocb_seal` needs: `oneLay`, with `tag` the `tag_len` bytes to
write. -/
def sealPre (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (arg s 0), (arg s 1).toNat⟩
  let data : Region := ⟨State.addr (arg s 2), (arg s 3).toNat⟩
  let tag : Region := ⟨State.addr (arg s 4), (arg s 5).toNat⟩
  let work : Region := ⟨State.addr (arg s 6), 2560⟩
  s.rd = [ctx, nonce, aad, args s 7] ∧ s.wr = [data, tag, work] ∧ oneLay s ∧ tag.Disjoint (args s 7)

/-- What `vg_aes_ocb_open` needs: `oneLay`, with the received tag the
`tag_len` bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (arg s 0), (arg s 1).toNat⟩
  let data : Region := ⟨State.addr (arg s 2), (arg s 3).toNat⟩
  let tag : Region := ⟨State.addr (arg s 4), (arg s 5).toNat⟩
  let work : Region := ⟨State.addr (arg s 6), 2560⟩
  s.rd = [ctx, nonce, aad, tag, args s 7] ∧ s.wr = [data, work] ∧ oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < 7, arg s₁ i = arg s₂ i

/-- The cipher of the key context. -/
abbrev ciph (s : State) : Spec.Ocb.Cipher := ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat

/-- The inverse cipher of the key context. -/
abbrev inv (s : State) : Spec.Ocb.Cipher := ctxInv s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat

/-- `L_*` of the key context. -/
abbrev lstar (s : State) : Spec.Ocb.Block := ctxLstar s.mem (State.addr (s.gpr .r0))

/-- `vg_aes_ocb_seal`. -/
def sealArm : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ciph s) (lstar s) (arg s 5).toNat
        (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
        (bytesAt s.mem (State.addr (arg s 0)) (arg s 1).toNat)
        (bytesAt s.mem (State.addr (arg s 2)) (arg s 3).toNat) =
      (bytesAt s'.mem (State.addr (arg s 2)) (arg s 3).toNat, bytesAt s'.mem (State.addr (arg s 4)) (arg s 5).toNat)
  pub := onePub

/-- What `vg_aes_ocb_open` computes, in a state. -/
abbrev openRes (s : State) : Option (List Byte) :=
  decryptWith (ciph s) (inv s) (lstar s) (arg s 5).toNat
    (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    (bytesAt s.mem (State.addr (arg s 0)) (arg s 1).toNat)
    (bytesAt s.mem (State.addr (arg s 2)) (arg s 3).toNat)
    (bytesAt s.mem (State.addr (arg s 4)) (arg s 5).toNat)

/-- What `vg_aes_ocb_open` may leak (`Spec.Ocb.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬roundsOk s then [] else [if (openRes s).isSome then 1 else 0]

/-- `vg_aes_ocb_open`. -/
def openArm : Contract isa where
  pre := openPre
  post s s' :=
    match openRes s with
    | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr (arg s 2)) (arg s 3).toNat = pt
    | none => s'.gpr .r0 = 0 ∧ bytesAt s'.mem (State.addr (arg s 2)) (arg s 3).toNat = zeros (arg s 3).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ openLeak s₁ = openLeak s₂

end VG.Proof.AesOcb.Arm
