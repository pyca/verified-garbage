module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Instance
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call

/-!
# Deterministic ECDSA on PPC64LE: the contract the proof is written against

The facts of the contract for an instance `I` of a curve of `len`-byte
scalars with a hash of `I.hashLen` bytes, for PPC64LE and `N` bytes of
stack, by name, as the code for that hash function sees them on entry:
`vg_ecdsa_<curve>_sign(out = r3, d = r4, digest = r5, digest_len = r6,
scratch = r7, hmac = r8)` (the table, 48 bytes, read-only, with what
`TabFacts` says of it), the result in `r3` (ELFv2); the public data include
the addresses of the functions `ns`, those of the tables. `Table.lean` shows
`TableInstance.signContract` gives it for the hash function of the table.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE Spec.Weierstrass Spec.Ecdsa

/-- RFC 6979's signature of the arguments, and the number of candidates tried. -/
abbrev result (I : Proof.Ecdsa.Rfc6979.Instance) (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  I.result m d digest

def rfcPPC (I : Proof.Ecdsa.Rfc6979.Instance) (N : Nat) (TabFacts : State → Prop) (ns : List String) :
    Contract PPC64LE.isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 2 * I.ecdsa.curve.len⟩
    let d : Region := ⟨s.gpr .r4, I.ecdsa.curve.len⟩
    let digest : Region := ⟨s.gpr .r5, I.hashLen⟩
    let scratch : Region := ⟨s.gpr .r7, 8192⟩
    let tab : Region := ⟨s.gpr .r8, 48⟩
    let stk : Region := below s.sp N
    s.rd = [d, digest, tab] ∧ s.wr = [out, scratch] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧
      stk.Disjoint out ∧ stk.Disjoint d ∧ stk.Disjoint digest ∧ stk.Disjoint scratch ∧
      (s.gpr .r3).toNat + 2 * I.ecdsa.curve.len ≤ 2 ^ 64 ∧
      (s.gpr .r4).toNat + I.ecdsa.curve.len ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + I.hashLen ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + 8192 ≤ 2 ^ 64 ∧ N ≤ s.sp.toNat ∧
      (s.gpr .r8).toNat + 48 ≤ 2 ^ 64 ∧ tab.Disjoint out ∧ tab.Disjoint scratch ∧ stk.Disjoint tab ∧
      TabFacts s
  post s s' :=
    match (result I s.mem (s.gpr .r4) (s.gpr .r5)).1 with
    | some rs => (s'.gpr .r3).setWidth 32 = 1 ∧
        bytesAt s'.mem (s.gpr .r3) (2 * I.ecdsa.curve.len) = encode I.ecdsa.curve rs
    | none => (s'.gpr .r3).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .r3) (2 * I.ecdsa.curve.len) = List.replicate (2 * I.ecdsa.curve.len) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    (result I s₁.mem (s₁.gpr .r4) (s₁.gpr .r5)).2 = (result I s₂.mem (s₂.gpr .r4) (s₂.gpr .r5)).2 ∧
    ∀ n ∈ ns, s₁.syms n = s₂.syms n

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
