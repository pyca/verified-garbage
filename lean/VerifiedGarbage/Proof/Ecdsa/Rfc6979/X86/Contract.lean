module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Instance
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.Contract

/-!
# Deterministic ECDSA on x86 (32-bit): the contract the proof is written against

The facts of the contract for an instance `I` of a curve of `len`-byte
scalars with a hash of `I.hashLen` bytes, for x86 and `N` bytes of stack, by
name, as on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Contract.lean`):
`vg_ecdsa_<curve>_sign(out, d, digest, digest_len, scratch, hmac)`, whose
arguments are on the stack (cdecl) and writable (the shared contract's
`writeArgs`), the table `hmac` (24 bytes, read-only, with what `TabFacts`
says of it), the result in `eax`, and the tables of constants `cs` that
`vg_ecdsa_<curve>_sign_k` reads, at their statics; the public data include
the addresses of the functions `ns`, those of the tables. `Table.lean` shows
`TableInstance.signContract` gives it for the hash function of the table.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 Spec.Weierstrass Spec.Ecdsa

/-- Static constants are held, fit the 32-bit address space, and miss every
writable or reserved region. -/
def TblsOk (cs : List (String × List (BitVec 64))) (s : State) (wr : List Region) : Prop :=
  Abi.constsHeld s.mem (fun n => (s.syms n).setWidth 64) cs ∧
    ∀ t ∈ Abi.constRegions (fun n => (s.syms n).setWidth 64) cs,
      t.base.toNat + t.len ≤ 2 ^ 32 ∧ ∀ r ∈ wr, t.Disjoint r

/-- RFC 6979's signature of the arguments, and the number of candidates tried. -/
abbrev result (I : Proof.Ecdsa.Rfc6979.Instance) (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  I.result m d digest

def rfcX86 (cs : List (String × List (BitVec 64))) (I : Proof.Ecdsa.Rfc6979.Instance) (N : Nat)
    (TabFacts : State → Prop) (ns : List String) : Contract X86.isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 2 * I.ecdsa.curve.len⟩
    let d : Region := ⟨(arg s 1).setWidth 64, I.ecdsa.curve.len⟩
    let digest : Region := ⟨(arg s 2).setWidth 64, I.hashLen⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let tab : Region := ⟨(arg s 5).setWidth 64, 24⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 N, N⟩
    N ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
    s.rd = [d, digest, tab] ++ Abi.constRegions (fun n => (s.syms n).setWidth 64) cs ∧
      s.wr = [out, scratch, args] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧
      args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      stack.Disjoint out ∧ stack.Disjoint d ∧ stack.Disjoint digest ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 2 * I.ecdsa.curve.len ≤ 2 ^ 32 ∧ (arg s 1).toNat + I.ecdsa.curve.len ≤ 2 ^ 32 ∧
      (arg s 2).toNat + I.hashLen ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧
      TblsOk cs s [out, scratch, ret, stack] ∧
      (arg s 5).toNat + 24 ≤ 2 ^ 32 ∧ tab.Disjoint out ∧ tab.Disjoint scratch ∧ tab.Disjoint args ∧
      tab.Disjoint ret ∧ tab.Disjoint stack ∧ TabFacts s
  post s s' :=
    match (result I s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64)).1 with
    | some rs => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧
      bytesAt s'.mem ((arg s 0).setWidth 64) (2 * I.ecdsa.curve.len) = encode I.ecdsa.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧
      bytesAt s'.mem ((arg s 0).setWidth 64) (2 * I.ecdsa.curve.len) = List.replicate (2 * I.ecdsa.curve.len) 0
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 6, arg s₁ i = arg s₂ i) ∧
    (result I s₁.mem ((arg s₁ 1).setWidth 64) ((arg s₁ 2).setWidth 64)).2 =
      (result I s₂.mem ((arg s₂ 1).setWidth 64) ((arg s₂ 2).setWidth 64)).2 ∧
    (∀ c ∈ cs, s₁.syms c.1 = s₂.syms c.1) ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

end VG.Proof.Ecdsa.Rfc6979.X86
