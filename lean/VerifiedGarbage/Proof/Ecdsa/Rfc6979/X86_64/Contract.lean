module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Instance
public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# Deterministic ECDSA on x86-64: the contract the proof is written against

The facts of the contract for an instance `I` of a curve of `len`-byte
scalars with a hash of `I.hashLen` bytes, for x86-64 and `S` bytes of stack,
by name, as the code for that hash function sees them after `signT`'s
entry: `out = rdi`, `d = rsi`, `digest = rdx`, `scratch = rcx` and the
table `hmac = r9` (48 bytes, read-only, with what
`TabFacts` says of it), the result in `eax`, and the tables of constants
`cs` that `vg_ecdsa_<curve>_sign_k` reads (the comb's,
`Abi.withConsts E.combConsts`; `TblsOk`), at their statics; the public
data include the addresses of the functions `ns`, those of the tables.
`Table.lean` shows `TableInstance.signContract` gives it for the hash
function of the table.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa

/-- The tables `cs`, at the addresses of their statics, held, not wrapping
around, and apart from the regions `wr` (as `Abi.withConsts` says). -/
def TblsOk (cs : List (String × List (BitVec 64))) (s : State) (wr : List Region) : Prop :=
  Abi.constsHeld s.mem (fun n => s.syms n) cs ∧
    ∀ t ∈ Abi.constRegions (fun n => s.syms n) cs, t.base.toNat + t.len ≤ 2 ^ 64 ∧ ∀ r ∈ wr, t.Disjoint r

/-- RFC 6979's signature of the arguments, and the number of candidates tried. -/
abbrev result (I : Proof.Ecdsa.Rfc6979.Instance) (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  I.result m d digest

def rfcX86_64 (cs : List (String × List (BitVec 64))) (I : Proof.Ecdsa.Rfc6979.Instance) (S : Nat)
    (TabFacts : State → Prop) (ns : List String) : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 2 * I.ecdsa.curve.len⟩
    let d : Region := ⟨s.gpr .rsi, I.ecdsa.curve.len⟩
    let digest : Region := ⟨s.gpr .rdx, I.hashLen⟩
    let scratch : Region := ⟨s.gpr .rcx, 8192⟩
    let tab : Region := ⟨s.gpr .r9, 48⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 S, S⟩
    S ≤ (s.gpr .rsp).toNat ∧ s.rd = [d, digest, tab] ++ Abi.constRegions (fun n => s.syms n) cs ∧
      s.wr = [out, scratch] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint d ∧ ret.Disjoint digest ∧ ret.Disjoint scratch ∧
      stk.Disjoint out ∧ stk.Disjoint d ∧ stk.Disjoint digest ∧ stk.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 2 * I.ecdsa.curve.len ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + I.ecdsa.curve.len ≤ 2 ^ 64 ∧
      (s.gpr .rdx).toNat + I.hashLen ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64 ∧
      TblsOk cs s [out, scratch, ret, stk] ∧
      (s.gpr .r9).toNat + 48 ≤ 2 ^ 64 ∧ tab.Disjoint out ∧ tab.Disjoint scratch ∧ tab.Disjoint ret ∧
      tab.Disjoint stk ∧ TabFacts s
  post s s' :=
    match (result I s.mem (s.gpr .rsi) (s.gpr .rdx)).1 with
    | some rs => (s'.gpr .rax).setWidth 32 = 1 ∧
        bytesAt s'.mem (s.gpr .rdi) (2 * I.ecdsa.curve.len) = encode I.ecdsa.curve rs
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .rdi) (2 * I.ecdsa.curve.len) = List.replicate (2 * I.ecdsa.curve.len) 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    (result I s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx)).2 = (result I s₂.mem (s₂.gpr .rsi) (s₂.gpr .rdx)).2 ∧
    (∀ c ∈ cs, s₁.syms c.1 = s₂.syms c.1) ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

end VG.Proof.Ecdsa.Rfc6979.X86_64
