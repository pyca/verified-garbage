module

public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# DSA on 32-bit ARM: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The facts of
`Spec.Dsa.signContract` and `Spec.Dsa.verifyContract` for 32-bit ARM, by
name. `vg_dsa_sign(out, out_len, key, key_len, p_len, nonce, q_len, digest,
digest_len, scratch, scratch_len)` has its first four arguments in `r0`–`r3`
and the others on the stack (`arg`, AAPCS); `vg_dsa_verify(key, key_len,
p_len, q_len, signature, signature_len, digest, digest_len, scratch,
scratch_len)` likewise. The result is in `r0` (the low word of `r1:r0`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 32 := stackArg s i

/-! ## Signing -/

/-- What `vg_dsa_sign` needs: `(out = r0, out_len = r1, key = r2, key_len = r3,
p_len = [sp], nonce = [sp + 4], q_len = [sp + 8], digest = [sp + 12],
digest_len = [sp + 16], scratch = [sp + 20], scratch_len = [sp + 24])`. -/
def signPre (s : State) : Prop :=
  let out : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
  let key : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let nonce : Region := ⟨State.addr (arg s 1), (arg s 2).toNat⟩
  let digest : Region := ⟨State.addr (arg s 3), (arg s 4).toNat⟩
  let scratch : Region := ⟨State.addr (arg s 5), (arg s 6).toNat * 8⟩
  let args : Region := ⟨State.addr s.sp, 28⟩
  s.sp.toNat + 28 ≤ 2 ^ 32 ∧ s.rd = [key, nonce, digest, args] ∧ s.wr = [out, scratch] ∧
    out.Disjoint key ∧ out.Disjoint nonce ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧ out.Disjoint args ∧
    key.Disjoint scratch ∧ nonce.Disjoint scratch ∧ digest.Disjoint scratch ∧ scratch.Disjoint args ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + (arg s 6).toNat * 8 ≤ 2 ^ 32 ∧
    Spec.Dsa.lengthsValid (arg s 0).toNat (arg s 2).toNat ∧ (s.gpr .r1).toNat = 2 * (arg s 2).toNat ∧
    (s.gpr .r3).toNat = 3 * (arg s 0).toNat + 2 * (arg s 2).toNat ∧
    Spec.Dsa.scratchWords (arg s 0).toNat ≤ (arg s 6).toNat

/-- The result of a signing attempt in a state. -/
abbrev signRes (s : State) : Option (List Byte) :=
  Spec.Dsa.signBytes (arg s 0).toNat (arg s 2).toNat
    (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    (Spec.Rsa.bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (State.addr (arg s 3)) (arg s 4).toNat)

/-- What signing may leak: the public bytes of the key and whether it succeeds. -/
abbrev signLeak (s : State) : List Nat :=
  Spec.Dsa.publicBytesLeak (arg s 0).toNat (arg s 2).toNat
      (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) ++
    [Spec.Dsa.signStatus (signRes s)]

def signArm : Contract isa where
  pre := signPre
  post s s' := (BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0)).toNat = Spec.Dsa.signStatus (signRes s) ∧
    Spec.Rsa.bytesAt s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat =
      (signRes s).getD (List.replicate (s.gpr .r1).toNat 0)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ signLeak s₁ = signLeak s₂ ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧
    s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < 7, arg s₁ i = arg s₂ i

/-! ## Verification -/

/-- What `vg_dsa_verify` needs: `(key = r0, key_len = r1, p_len = r2,
q_len = r3, signature = [sp], signature_len = [sp + 4], digest = [sp + 8],
digest_len = [sp + 12], scratch = [sp + 16], scratch_len = [sp + 20])`. -/
def verifyPre (s : State) : Prop :=
  let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
  let sig : Region := ⟨State.addr (arg s 0), (arg s 1).toNat⟩
  let digest : Region := ⟨State.addr (arg s 2), (arg s 3).toNat⟩
  let scratch : Region := ⟨State.addr (arg s 4), (arg s 5).toNat * 8⟩
  let args : Region := ⟨State.addr s.sp, 24⟩
  s.sp.toNat + 24 ≤ 2 ^ 32 ∧ s.rd = [key, sig, digest, args] ∧ s.wr = [scratch] ∧
    key.Disjoint scratch ∧ sig.Disjoint scratch ∧ digest.Disjoint scratch ∧ scratch.Disjoint args ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + (arg s 5).toNat * 8 ≤ 2 ^ 32 ∧
    Spec.Dsa.lengthsValid (s.gpr .r2).toNat (s.gpr .r3).toNat ∧
    (s.gpr .r1).toNat = 3 * (s.gpr .r2).toNat + (s.gpr .r3).toNat ∧ (arg s 1).toNat = 2 * (s.gpr .r3).toNat ∧
    Spec.Dsa.scratchWords (s.gpr .r2).toNat ≤ (arg s 5).toNat

/-- The result of a verification in a state. -/
abbrev verifyRes (s : State) : Bool :=
  Spec.Dsa.verifyBytes (s.gpr .r2).toNat (s.gpr .r3).toNat
    (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
    (Spec.Rsa.bytesAt s.mem (State.addr (arg s 0)) (arg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (State.addr (arg s 2)) (arg s 3).toNat)

/-- What verification may leak: the public key's bytes and the result. -/
abbrev verifyLeak (s : State) : List Nat :=
  Spec.Dsa.publicBytesLeak (s.gpr .r2).toNat (s.gpr .r3).toNat
      (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) ++
    [if verifyRes s then 1 else 0]

def verifyArm : Contract isa where
  pre := verifyPre
  post s s' := (BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0)).toNat = if verifyRes s then 1 else 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ verifyLeak s₁ = verifyLeak s₂ ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧
    s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < 6, arg s₁ i = arg s₂ i

end VG.Proof.Dsa.Arm
