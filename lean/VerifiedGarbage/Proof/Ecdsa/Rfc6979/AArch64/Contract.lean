import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Impl.Ecdsa.AArch64

/-!
# Deterministic ECDSA on AArch64: the contract the proof is written against

The facts of `I.signContract` for an instance `I` of a curve of `len`-byte
scalars with a hash of `I.hashLen` bytes, for AArch64 and `N` bytes of stack,
by name: `vg_ecdsa_<curve>_<hash>_sign(out = x0, d = x1, digest = x2, scratch = x3)`,
the result in `w0`, and the comb's tables of the curve `E` at the static
`E.tsym`, which `vg_ecdsa_<curve>_sign` reads (`Abi.withConsts E.combConsts`;
`TblOk`, as `Proof.Ecdsa.AArch64.TblHeld` for P-256). Each instance's file
shows `I.signContract` implies it.
-/

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
abbrev result (I : Spec.Ecdsa.Rfc6979.Instance) (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  I.result m d digest

def rfcAArch64 (E : Impl.Ecdsa.AArch64.Cfg) (I : Spec.Ecdsa.Rfc6979.Instance) (N : Nat) : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 2 * I.ecdsa.curve.len⟩
    let d : Region := ⟨s.gpr .x1, I.ecdsa.curve.len⟩
    let digest : Region := ⟨s.gpr .x2, I.hashLen⟩
    let scratch : Region := ⟨s.gpr .x3, 8192⟩
    let stk : Region := below s.sp N
    s.rd = [d, digest] ++ tableRegions E (tableAddr E s.syms) ∧ s.wr = [out, scratch] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧
      stk.Disjoint out ∧ stk.Disjoint d ∧ stk.Disjoint digest ∧ stk.Disjoint scratch ∧
      (s.gpr .x0).toNat + 2 * I.ecdsa.curve.len ≤ 2 ^ 64 ∧
      (s.gpr .x1).toNat + I.ecdsa.curve.len ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + I.hashLen ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64 ∧ N ≤ s.sp.toNat ∧
      TblOk E s [out, scratch, stk]
  post s s' :=
    match (result I s.mem (s.gpr .x1) (s.gpr .x2)).1 with
    | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧
        bytesAt s'.mem (s.gpr .x0) (2 * I.ecdsa.curve.len) = encode I.ecdsa.curve rs
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .x0) (2 * I.ecdsa.curve.len) = List.replicate (2 * I.ecdsa.curve.len) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    (result I s₁.mem (s₁.gpr .x1) (s₁.gpr .x2)).2 = (result I s₂.mem (s₂.gpr .x1) (s₂.gpr .x2)).2 ∧
    tableAddr E s₁.syms = tableAddr E s₂.syms

/-- A state satisfying the precondition, for scalars of `Q` bytes and a
digest of `D` bytes, with the memory `m` holding the comb's tables (of `TB`
bytes) at `0x100000`. -/
def satState (Q D : Nat) (m : Mem) (TB : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x8000 | _ => 0
  sp := 0x20000
  mem := m
  rd := [⟨0x2000, Q⟩, ⟨0x3000, D⟩, ⟨0x100000, TB⟩]
  wr := [⟨0x1000, 2 * Q⟩, ⟨0x8000, 8192⟩]
  syms _ := 0x100000

end VG.Proof.Ecdsa.Rfc6979.AArch64
