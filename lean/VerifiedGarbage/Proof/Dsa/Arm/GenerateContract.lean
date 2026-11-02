module

public import VerifiedGarbage.Proof.Dsa.Arm.Contract
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.Contract

/-!
# DSA domain checks and key derivation on 32-bit ARM: the contracts

Untrusted: everything here is checked by Lean. The facts of
`Proof.Dsa.checkParametersContract` and `Spec.Dsa.deriveKeyContract` for
32-bit ARM, by name. `vg_dsa_check_parameters(params, params_len, p_len,
q_len, scratch, scratch_len)` has its first four arguments in `r0`–`r3`
and the others on the stack; `vg_dsa_derive_key(out, out_len, params,
params_len, p_len, x, q_len, scratch, scratch_len)` likewise.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm

/-! ## Checking a domain -/

/-- What `vg_dsa_check_parameters` needs: `(params = r0, params_len = r1,
p_len = r2, q_len = r3, scratch = [sp], scratch_len = [sp + 4])`. -/
def checkPre (s : State) : Prop :=
  let params : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
  let scratch : Region := ⟨State.addr (arg s 0), (arg s 1).toNat * 8⟩
  let args : Region := ⟨State.addr s.sp, 8⟩
  s.sp.toNat + 8 ≤ 2 ^ 32 ∧ s.rd = [params, args] ∧ s.wr = [scratch] ∧
    params.Disjoint scratch ∧ scratch.Disjoint args ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (arg s 0).toNat + (arg s 1).toNat * 8 ≤ 2 ^ 32 ∧
    Spec.Dsa.lengthsValid (s.gpr .r2).toNat (s.gpr .r3).toNat ∧
    (s.gpr .r1).toNat = 2 * (s.gpr .r2).toNat + (s.gpr .r3).toNat ∧
    Spec.Dsa.scratchWords (s.gpr .r2).toNat ≤ (arg s 1).toNat

/-- The bytes of the domain. -/
abbrev checkParams (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat

/-- The result of the check in a state. -/
abbrev checkRes (s : State) : Bool :=
  Spec.Dsa.checkParametersBytes (s.gpr .r2).toNat (s.gpr .r3).toNat (checkParams s)

def checkArm : Contract isa where
  pre := checkPre
  post s s' := (BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0)).toNat = if checkRes s then 1 else 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ (checkParams s₁).map (·.toNat) = (checkParams s₂).map (·.toNat) ∧
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < 2, arg s₁ i = arg s₂ i

/-! ## Deriving a key -/

/-- What `vg_dsa_derive_key` needs: `(out = r0, out_len = r1, params = r2,
params_len = r3, p_len = [sp], x = [sp + 4], q_len = [sp + 8],
scratch = [sp + 12], scratch_len = [sp + 16])`. -/
def derivePre (s : State) : Prop :=
  let out : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
  let params : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let x : Region := ⟨State.addr (arg s 1), (arg s 2).toNat⟩
  let scratch : Region := ⟨State.addr (arg s 3), (arg s 4).toNat * 8⟩
  let args : Region := ⟨State.addr s.sp, 20⟩
  s.sp.toNat + 20 ≤ 2 ^ 32 ∧ s.rd = [params, x, args] ∧ s.wr = [out, scratch] ∧
    out.Disjoint params ∧ out.Disjoint x ∧ out.Disjoint scratch ∧ out.Disjoint args ∧
    params.Disjoint scratch ∧ x.Disjoint scratch ∧ scratch.Disjoint args ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat * 8 ≤ 2 ^ 32 ∧
    Spec.Dsa.lengthsValid (arg s 0).toNat (arg s 2).toNat ∧
    (s.gpr .r1).toNat = 3 * (arg s 0).toNat + 2 * (arg s 2).toNat ∧
    (s.gpr .r3).toNat = 2 * (arg s 0).toNat + (arg s 2).toNat ∧
    Spec.Dsa.scratchWords (arg s 0).toNat ≤ (arg s 4).toNat

/-- The bytes of the domain and of x. -/
abbrev deriveParams (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
abbrev deriveX (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat

/-- The result of the derivation in a state. -/
abbrev deriveRes (s : State) : Option (List Byte) :=
  Spec.Dsa.deriveKeyBytes (arg s 0).toNat (arg s 2).toNat (deriveParams s) (deriveX s)

/-- What derivation may leak: the domain and whether it succeeds. -/
abbrev deriveLeak (s : State) : List Nat :=
  (deriveParams s).map (·.toNat) ++ [Spec.Dsa.signStatus (deriveRes s)]

def deriveArm : Contract isa where
  pre := derivePre
  post s s' := (BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0)).toNat = Spec.Dsa.signStatus (deriveRes s) ∧
    Spec.Rsa.bytesAt s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat =
      (deriveRes s).getD (List.replicate (s.gpr .r1).toNat 0)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ deriveLeak s₁ = deriveLeak s₂ ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧
    s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < 5, arg s₁ i = arg s₂ i

end VG.Proof.Dsa.Arm
