module

public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# Deterministic ECDSA on 32-bit ARM: the contract the proof is written against

The facts of the contract for an instance `I` of a curve of `len`-byte
scalars with a hash of `I.hashLen` bytes, for 32-bit ARM and `N` bytes of
stack, by name, as the code for that hash function sees them:
`vg_ecdsa_<curve>_sign(out = r0, d = r1, digest = r2, digest_len = r3,
scratch = [sp], hmac = [sp + 4])` (the table, 24 bytes, read-only, with what
`TabFacts` says of it), the result in `r0` (the low word of `r1:r0`), and
the tables of constants `cs` that `vg_ecdsa_<curve>_sign_k` reads
(`TablesOk`), at their statics; the public data include the addresses of
the functions `ns`, those of the tables. `Table.lean` shows
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

def rfcArm (I : Spec.Ecdsa.Rfc6979.Instance) (N : Nat) (cs : List (String × List (BitVec 64)))
    (TabFacts : State → Prop) (ns : List String) : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 2 * I.ecdsa.curve.len⟩
    let d : Region := ⟨State.addr (s.gpr .r1), I.ecdsa.curve.len⟩
    let digest : Region := ⟨State.addr (s.gpr .r2), I.hashLen⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 8192⟩
    let tab : Region := ⟨State.addr (stackArg s 1), 24⟩
    let args : Region := ⟨State.addr s.sp, 8⟩
    let stk : Region := stkR s.sp N
    s.rd = [d, digest, tab, args] ++ Abi.constRegions (fun n => State.addr (s.syms n)) cs ∧
      s.wr = [out, scratch] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧
      stk.Disjoint out ∧ stk.Disjoint d ∧ stk.Disjoint digest ∧ stk.Disjoint scratch ∧
      (s.gpr .r0).toNat + 2 * I.ecdsa.curve.len ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + I.ecdsa.curve.len ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + I.hashLen ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 8192 ≤ 2 ^ 32 ∧ N ≤ s.sp.toNat ∧
      s.sp.toNat + 8 ≤ 2 ^ 32 ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      (stackArg s 1).toNat + 24 ≤ 2 ^ 32 ∧ tab.Disjoint out ∧ tab.Disjoint scratch ∧ tab.Disjoint stk ∧
      TablesOk cs s.syms s.mem [out,scratch,stk] ∧ TabFacts s
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
    (∀ c∈cs,s₁.syms c.1=s₂.syms c.1) ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

end VG.Proof.Ecdsa.Rfc6979.Arm
