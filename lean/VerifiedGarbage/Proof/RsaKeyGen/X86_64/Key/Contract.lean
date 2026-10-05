import VerifiedGarbage.Spec.RsaKeyGen.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# An RSA key from its primes on x86-64: the contract the proofs use

Untrusted: everything here is checked by Lean. `keyCtr` states
`Spec.RsaKeyGen.keyContract` on the registers and the stack:
`vg_rsa_keygen_key(n = rdi, n_len = rsi, d = rdx, d_len = rcx, p = r8,
p_len = r9, q = [rsp + 8], q_len = [rsp + 16], dp = [rsp + 24],
dp_len = [rsp + 32], dq = [rsp + 40], dq_len = [rsp + 48],
qinv = [rsp + 56], qinv_len = [rsp + 64], e = [rsp + 72],
e_len = [rsp + 80], scratch = [rsp + 88], scratch_len = [rsp + 96])`. The
shared contract implies it (`Implies.lean`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64
open VG.Spec.Rsa (bytesAt)
open VG.Spec.RsaKeyGen (keyOp keyStatus primeLenValid)

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 64 := stackArg s i

/-- The arguments on the stack. -/
abbrev args (s : State) : Region := ⟨stackArgAddr s 0, 96⟩

/-- The return address. -/
abbrev ret (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- The precondition. -/
def keyPre (s : State) : Prop :=
  let n : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  let d : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let p : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let q : Region := ⟨arg s 0, (arg s 1).toNat⟩
  let dp : Region := ⟨arg s 2, (arg s 3).toNat⟩
  let dq : Region := ⟨arg s 4, (arg s 5).toNat⟩
  let qi : Region := ⟨arg s 6, (arg s 7).toNat⟩
  let e : Region := ⟨arg s 8, (arg s 9).toNat⟩
  let scr : Region := ⟨arg s 10, (arg s 11).toNat * 8⟩
  (s.gpr .rsp).toNat + 104 ≤ 2 ^ 64 ∧
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
    (ret s).Disjoint n ∧ (ret s).Disjoint d ∧ (ret s).Disjoint p ∧ (ret s).Disjoint q ∧ (ret s).Disjoint dp ∧
    (ret s).Disjoint dq ∧ (ret s).Disjoint qi ∧ (ret s).Disjoint e ∧ (ret s).Disjoint scr ∧
    (ret s).Disjoint (args s) ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 64 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 64 ∧ (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 64 ∧
    (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 64 ∧ (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 64 ∧
    (arg s 10).toNat + (arg s 11).toNat * 8 ≤ 2 ^ 64 ∧
    primeLenValid (s.gpr .r9).toNat ∧ (s.gpr .rsi).toNat = 2 * (s.gpr .r9).toNat ∧
    (s.gpr .rcx).toNat = (s.gpr .rsi).toNat ∧ (arg s 1).toNat = (s.gpr .r9).toNat ∧
    (arg s 3).toNat = (s.gpr .r9).toNat ∧ (arg s 5).toNat = (s.gpr .r9).toNat ∧
    (arg s 7).toNat = (s.gpr .r9).toNat ∧ 1 ≤ (arg s 9).toNat ∧ (arg s 9).toNat ≤ 8 ∧
    Spec.Rsa.scratchWords (s.gpr .rsi).toNat ≤ (arg s 11).toNat

/-- The specification's result, from the state on entry. -/
def keyRes (s : State) : Except Spec.RsaKeyGen.Failure (List (List Byte)) ⊕ Unit :=
  keyOp (s.gpr .r9).toNat (bytesAt s.mem (arg s 8) (arg s 9).toNat) (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
    (bytesAt s.mem (arg s 0) (s.gpr .r9).toNat)

/-- The outputs: `n`, `d`, `p`, `q`, `dp`, `dq` and `qinv`. -/
def keyOuts (s : State) : List (Addr × Nat) :=
  [(s.gpr .rdi, (s.gpr .rsi).toNat), (s.gpr .rdx, (s.gpr .rsi).toNat), (s.gpr .r8, (s.gpr .r9).toNat),
    (arg s 0, (s.gpr .r9).toNat), (arg s 2, (s.gpr .r9).toNat), (arg s 4, (s.gpr .r9).toNat),
    (arg s 6, (s.gpr .r9).toNat)]

/-- The postcondition. -/
def keyPost (s s' : State) : Prop :=
  ((s'.gpr .rax).setWidth 32).toNat = keyStatus (keyRes s) ∧
    match keyRes s with
    | .inl (.ok ys) => (keyOuts s).map (fun o => bytesAt s'.mem o.1 o.2) = ys
    | _ => ∀ o ∈ keyOuts s, bytesAt s'.mem o.1 o.2 = List.replicate o.2 0

/-- What timing may depend on, beyond the arguments: `e` and the status. -/
def keyLeak (s : State) : List Nat :=
  (bytesAt s.mem (arg s 8) (arg s 9).toNat).map (·.toNat) ++ [keyStatus (keyRes s)]

/-- The arguments agree, and so does the leak. -/
def keyPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (∀ i < 12, arg s₁ i = arg s₂ i) ∧ keyLeak s₁ = keyLeak s₂

/-- `vg_rsa_keygen_key`. -/
def keyCtr : Contract isa where
  pre := keyPre
  post := keyPost
  pub := keyPub

end VG.Proof.RsaKeyGen.X86_64.Key
