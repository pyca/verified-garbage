import VerifiedGarbage.Spec.RsaKeyGen.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# An RSA key from its primes on AArch64: the contract the proofs use

Untrusted: everything here is checked by Lean. `keyA` states
`Spec.RsaKeyGen.keyContract` on the registers and the stack:
`vg_rsa_keygen_key(n = x0, n_len = x1, d = x2, d_len = x3, p = x4,
p_len = x5, q = x6, q_len = x7, dp = [sp], dp_len = [sp + 8],
dq = [sp + 16], dq_len = [sp + 24], qinv = [sp + 32], qinv_len = [sp + 40],
e = [sp + 48], e_len = [sp + 56], scratch = [sp + 64],
scratch_len = [sp + 72])`. The shared contract implies it (`Implies.lean`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64
open VG.Spec.Rsa (bytesAt)
open VG.Spec.RsaKeyGen (keyOp keyStatus primeLenValid)

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 64 := stackArg s i

/-- The arguments on the stack. -/
abbrev args (s : State) : Region := ⟨stackArgAddr s 0, 80⟩

/-- The precondition. -/
def keyPre (s : State) : Prop :=
  let n : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  let d : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let p : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let q : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let dp : Region := ⟨arg s 0, (arg s 1).toNat⟩
  let dq : Region := ⟨arg s 2, (arg s 3).toNat⟩
  let qi : Region := ⟨arg s 4, (arg s 5).toNat⟩
  let e : Region := ⟨arg s 6, (arg s 7).toNat⟩
  let scr : Region := ⟨arg s 8, (arg s 9).toNat * 8⟩
  s.sp.toNat + 80 ≤ 2 ^ 64 ∧
    s.rd = [e, args s] ∧ s.wr = [n, d, p, q, dp, dq, qi, scr] ∧
    n.Disjoint d ∧ n.Disjoint p ∧ n.Disjoint q ∧ n.Disjoint dp ∧ n.Disjoint dq ∧ n.Disjoint qi ∧ n.Disjoint e ∧
    n.Disjoint scr ∧ n.Disjoint (args s) ∧
    d.Disjoint p ∧ d.Disjoint q ∧ d.Disjoint dp ∧ d.Disjoint dq ∧ d.Disjoint qi ∧ d.Disjoint e ∧ d.Disjoint scr ∧
    d.Disjoint (args s) ∧
    p.Disjoint q ∧ p.Disjoint dp ∧ p.Disjoint dq ∧ p.Disjoint qi ∧ p.Disjoint e ∧ p.Disjoint scr ∧
    p.Disjoint (args s) ∧
    q.Disjoint dp ∧ q.Disjoint dq ∧ q.Disjoint qi ∧ q.Disjoint e ∧ q.Disjoint scr ∧ q.Disjoint (args s) ∧
    dp.Disjoint dq ∧ dp.Disjoint qi ∧ dp.Disjoint e ∧ dp.Disjoint scr ∧ dp.Disjoint (args s) ∧
    dq.Disjoint qi ∧ dq.Disjoint e ∧ dq.Disjoint scr ∧ dq.Disjoint (args s) ∧
    qi.Disjoint e ∧ qi.Disjoint scr ∧ qi.Disjoint (args s) ∧
    e.Disjoint scr ∧ scr.Disjoint (args s) ∧
    (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 64 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 64 ∧
    (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 64 ∧ (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 64 ∧
    (arg s 8).toNat + (arg s 9).toNat * 8 ≤ 2 ^ 64 ∧
    primeLenValid (s.gpr .x5).toNat ∧ (s.gpr .x1).toNat = 2 * (s.gpr .x5).toNat ∧
    (s.gpr .x3).toNat = (s.gpr .x1).toNat ∧ (s.gpr .x7).toNat = (s.gpr .x5).toNat ∧
    (arg s 1).toNat = (s.gpr .x5).toNat ∧ (arg s 3).toNat = (s.gpr .x5).toNat ∧
    (arg s 5).toNat = (s.gpr .x5).toNat ∧ 1 ≤ (arg s 7).toNat ∧ (arg s 7).toNat ≤ 8 ∧
    Spec.Rsa.scratchWords (s.gpr .x1).toNat ≤ (arg s 9).toNat

/-- The specification's result, from the state on entry. -/
def keyRes (s : State) : Except Spec.RsaKeyGen.Failure (List (List Byte)) ⊕ Unit :=
  keyOp (s.gpr .x5).toNat (bytesAt s.mem (arg s 6) (arg s 7).toNat) (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
    (bytesAt s.mem (s.gpr .x6) (s.gpr .x5).toNat)

/-- The outputs: `n`, `d`, `p`, `q`, `dp`, `dq` and `qinv`. -/
def keyOuts (s : State) : List (Addr × Nat) :=
  [(s.gpr .x0, (s.gpr .x1).toNat), (s.gpr .x2, (s.gpr .x1).toNat), (s.gpr .x4, (s.gpr .x5).toNat),
    (s.gpr .x6, (s.gpr .x5).toNat), (arg s 0, (s.gpr .x5).toNat), (arg s 2, (s.gpr .x5).toNat),
    (arg s 4, (s.gpr .x5).toNat)]

/-- The postcondition. -/
def keyPost (s s' : State) : Prop :=
  ((s'.gpr .x0).setWidth 32).toNat = keyStatus (keyRes s) ∧
    match keyRes s with
    | .inl (.ok ys) => (keyOuts s).map (fun o => bytesAt s'.mem o.1 o.2) = ys
    | _ => ∀ o ∈ keyOuts s, bytesAt s'.mem o.1 o.2 = List.replicate o.2 0

/-- What timing may depend on, beyond the arguments: `e` and the status. -/
def keyLeak (s : State) : List Nat :=
  (bytesAt s.mem (arg s 6) (arg s 7).toNat).map (·.toNat) ++ [keyStatus (keyRes s)]

/-- The arguments agree, and so does the leak. -/
def keyPub (s₁ s₂ : State) : Prop :=
  (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧ (∀ i < 10, arg s₁ i = arg s₂ i) ∧
    keyLeak s₁ = keyLeak s₂

/-- `vg_rsa_keygen_key`. -/
def keyA : Contract isa where
  pre := keyPre
  post := keyPost
  pub := keyPub

end VG.Proof.RsaKeyGen.AArch64.Key
