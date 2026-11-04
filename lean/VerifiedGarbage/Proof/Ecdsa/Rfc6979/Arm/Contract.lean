module

public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# Deterministic ECDSA on 32-bit ARM: the contract the proof is written against

The facts of the contract for an instance `I` of a curve of `len`-byte
scalars with a hash of `I.hashLen` bytes, for 32-bit ARM and `N` bytes of
stack, by name, as the code for that hash function sees them (`rfcArm`),
the result in `r0` (the low word of `r1:r0`). `Table.lean` shows
`TableInstance.signContract` gives it for the hash function of the table.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm Spec.Weierstrass Spec.Ecdsa

/-- RFC 6979's signature of the arguments, and the number of candidates tried. -/
abbrev result (I : Spec.Ecdsa.Rfc6979.Instance) (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  I.result m d digest

/-- The `N` bytes of stack below `sp`. -/
abbrev stkR (sp : BitVec 32) (N : Nat) : Region := ⟨State.addr sp - BitVec.ofNat 64 N, N⟩

/-- Static tables are readable, held in memory, and apart from every write region. -/
def TablesOk (cs : List (String × List (BitVec 64))) (sy : String → BitVec 32) (m : Mem)
    (writes : List Region) : Prop :=
  ∀ c∈cs,(∀ i<c.2.length,m.readW (State.addr (sy c.1)+BitVec.ofNat 64 (8*i)) 64=c.2.getD i 0) ∧
    (sy c.1).toNat+8*c.2.length≤2^32 ∧
    (∀ r∈writes,Region.Disjoint ⟨State.addr (sy c.1),8*c.2.length⟩ r) ∧
    (State.addr (sy c.1)).toNat%64=0

/-- The table of the hash function, stack argument 1. -/
abbrev tabR (s : State) : Region := ⟨State.addr (stackArg s 1), 20⟩

/-- The stack arguments. -/
abbrev argsR (s : State) : Region := ⟨stackArgAddr s 0, 8⟩

/-- The contract the code for one hash function is written against, as the
code sees it on entry (`signT`'s comparisons change only `r12` and the
flags): `out = r0`, `d = r1`, `digest = r2` (`I.hashLen` bytes) and, on the
stack, `scratch` and the table of the hash function `hash` (20 bytes,
read-only, with what `TabFacts` says of it); the public data include the
addresses of the functions `ns`, those of the tables. -/
def rfcArm (I : Spec.Ecdsa.Rfc6979.Instance) (N : Nat) (cs : List (String × List (BitVec 64)))
    (TabFacts : State → Prop) (ns : List String) : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 2 * I.ecdsa.curve.len⟩
    let d : Region := ⟨State.addr (s.gpr .r1), I.ecdsa.curve.len⟩
    let digest : Region := ⟨State.addr (s.gpr .r2), I.hashLen⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 8192⟩
    let stk : Region := stkR s.sp N
    s.rd = [d, digest, tabR s, argsR s] ++ Abi.constRegions (fun n => State.addr (s.syms n)) cs ∧
      s.wr = [out, scratch] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧ out.Disjoint (tabR s) ∧
      out.Disjoint (argsR s) ∧ d.Disjoint scratch ∧ digest.Disjoint scratch ∧ scratch.Disjoint (tabR s) ∧
      scratch.Disjoint (argsR s) ∧
      stk.Disjoint out ∧ stk.Disjoint d ∧ stk.Disjoint digest ∧ stk.Disjoint scratch ∧ stk.Disjoint (tabR s) ∧
      stk.Disjoint (argsR s) ∧
      (s.gpr .r0).toNat + 2 * I.ecdsa.curve.len ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + I.ecdsa.curve.len ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + I.hashLen ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 8192 ≤ 2 ^ 32 ∧
      (stackArg s 1).toNat + 20 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧ N ≤ s.sp.toNat ∧
      TablesOk cs s.syms s.mem [out, scratch, stk] ∧ TabFacts s
  post s s' :=
    match (result I s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2))).1 with
    | some rs => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
        bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * I.ecdsa.curve.len) = encode I.ecdsa.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
        bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * I.ecdsa.curve.len) = List.replicate (2 * I.ecdsa.curve.len) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    (result I s₁.mem (State.addr (s₁.gpr .r1)) (State.addr (s₁.gpr .r2))).2 =
      (result I s₂.mem (State.addr (s₂.gpr .r1)) (State.addr (s₂.gpr .r2))).2 ∧
    (∀ c ∈ cs, s₁.syms c.1 = s₂.syms c.1) ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

end VG.Proof.Ecdsa.Rfc6979.Arm
