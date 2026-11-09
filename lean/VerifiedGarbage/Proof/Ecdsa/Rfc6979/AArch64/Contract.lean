module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Instance
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Impl.Ecdsa.AArch64

/-!
# Deterministic ECDSA on AArch64: the contract the proof is written against

The facts of the contract for an instance `I` of a curve of `len`-byte
scalars with a hash of `I.hashLen` bytes, for AArch64 and `N` bytes of stack,
by name, as the code for that hash function sees them after `signCode`'s
entry: `out = x0`, `d = x1`, `digest = x2`, `scratch = x4` and the table
`hmac = x5` (48 bytes, read-only, with what `TabFacts` says of it), the
result in `w0`, and the comb's tables of the curve `E` at the static
`E.tsym`, which `vg_ecdsa_<curve>_sign_k` reads (`Abi.withConsts
E.combConsts`; `TblOk`, as `Proof.Ecdsa.AArch64.TblHeld` for P-256); the
public data include the addresses of the functions `ns`, those of the
tables. `TableSpec.lean` shows `TableInstance.signContract` gives it for the
hash function of the table.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 Spec.Weierstrass Spec.Ecdsa

/-- An absent table needs neither a symbol nor a readable region. -/
def tableAddr (E : Impl.Ecdsa.AArch64.Cfg) (syms : String → Addr) : Addr :=
  if E.tbl.isEmpty then 0 else syms E.tsym

def tableRegions (E : Impl.Ecdsa.AArch64.Cfg) (addr : Addr) : List Region :=
  if E.tbl.isEmpty then [] else [⟨addr, 8 * E.combWords.length⟩]

/-- The comb's tables of `E` at the static `E.tsym`, held, not wrapping
around, and apart from the regions `wr`. -/
def TblOk (E : Impl.Ecdsa.AArch64.Cfg) (s : State) (wr : List Region) : Prop :=
  (∀ i < E.combWords.length,
    s.mem.readW (tableAddr E s.syms + BitVec.ofNat 64 (8 * i)) 64 = E.combWords.getD i 0) ∧
  (tableAddr E s.syms).toNat + 8 * E.combWords.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨tableAddr E s.syms, 8 * E.combWords.length⟩ r

/-- RFC 6979's signature of the arguments, and the number of candidates tried. -/
abbrev result (I : Proof.Ecdsa.Rfc6979.Instance) (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  I.result m d digest

def rfcAArch64 (E : Impl.Ecdsa.AArch64.Cfg) (I : Proof.Ecdsa.Rfc6979.Instance) (N : Nat)
    (TabFacts : State → Prop) (ns : List String) : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 2 * I.ecdsa.curve.len⟩
    let d : Region := ⟨s.gpr .x1, I.ecdsa.curve.len⟩
    let digest : Region := ⟨s.gpr .x2, I.hashLen⟩
    let scratch : Region := ⟨s.gpr .x4, 8192⟩
    let tab : Region := ⟨s.gpr .x5, 48⟩
    let stk : Region := below s.sp N
    s.rd = [d, digest, tab] ++ tableRegions E (tableAddr E s.syms) ∧ s.wr = [out, scratch] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧
      stk.Disjoint out ∧ stk.Disjoint d ∧ stk.Disjoint digest ∧ stk.Disjoint scratch ∧
      (s.gpr .x0).toNat + 2 * I.ecdsa.curve.len ≤ 2 ^ 64 ∧
      (s.gpr .x1).toNat + I.ecdsa.curve.len ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + I.hashLen ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64 ∧ N ≤ s.sp.toNat ∧
      TblOk E s [out, scratch, stk] ∧
      (s.gpr .x5).toNat + 48 ≤ 2 ^ 64 ∧ tab.Disjoint out ∧ tab.Disjoint scratch ∧ tab.Disjoint stk ∧
      TabFacts s
  post s s' :=
    match (result I s.mem (s.gpr .x1) (s.gpr .x2)).1 with
    | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧
        bytesAt s'.mem (s.gpr .x0) (2 * I.ecdsa.curve.len) = encode I.ecdsa.curve rs
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .x0) (2 * I.ecdsa.curve.len) = List.replicate (2 * I.ecdsa.curve.len) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    (result I s₁.mem (s₁.gpr .x1) (s₁.gpr .x2)).2 = (result I s₂.mem (s₂.gpr .x1) (s₂.gpr .x2)).2 ∧
    tableAddr E s₁.syms = tableAddr E s₂.syms ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

end VG.Proof.Ecdsa.Rfc6979.AArch64
