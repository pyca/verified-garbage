module

public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.AnyHash
import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Impl.Ecdsa.AArch64
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs

/-!
# Deterministic ECDSA on AArch64: the contract the proof is written against

The facts of `J.signAnyContract` for the instance `J` of a curve of
`len`-byte scalars, for AArch64 and `N` bytes of stack, by name:
`vg_ecdsa_<curve>_rfc6979_sign(out = x0, d = x1, digest = x2, digest_len = x3,
scratch = x4, hash = w5)`, the result in `w0`, and the comb's tables of the
curve `E` at the static `E.tsym`, which `vg_ecdsa_<curve>_sign` reads
(`Abi.withConsts E.combConsts`; `TblOk`, as `Proof.Ecdsa.AArch64.TblHeld` for
P-256). Each curve's file shows `J.signAnyContract` implies it.
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

/-- The hash function's number: `hash` (`x5`). -/
abbrev selOf (s : State) : Nat := (s.gpr .x5).toNat

/-- RFC 6979's signature of the arguments with the hash function `h` names,
and the number of candidates tried; `none` if it names none. -/
abbrev anyResult (J : Spec.Ecdsa.Rfc6979.Instance) (m : Mem) (d digest : Addr) (D h : Nat) :
    Option (Option (Nat × Nat) × Nat) :=
  J.anyResult m d digest D h

def rfcAArch64 (E : Impl.Ecdsa.AArch64.Cfg) (J : Spec.Ecdsa.Rfc6979.Instance) (N : Nat) : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 2 * J.ecdsa.curve.len⟩
    let d : Region := ⟨s.gpr .x1, J.ecdsa.curve.len⟩
    let digest : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 8192⟩
    let stk : Region := below s.sp N
    selOf s ∈ Spec.Ecdsa.Rfc6979.hashIds ∧
      (∀ G, Spec.HashId.mgf1 (selOf s) = some G → (s.gpr .x3).toNat = G.len) ∧
      s.rd = [d, digest] ++ tableRegions E (tableAddr E s.syms) ∧ s.wr = [out, scratch] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧
      stk.Disjoint out ∧ stk.Disjoint d ∧ stk.Disjoint digest ∧ stk.Disjoint scratch ∧
      (s.gpr .x0).toNat + 2 * J.ecdsa.curve.len ≤ 2 ^ 64 ∧
      (s.gpr .x1).toNat + J.ecdsa.curve.len ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64 ∧ N ≤ s.sp.toNat ∧
      TblOk E s [out, scratch, stk]
  post s s' :=
    match anyResult J s.mem (s.gpr .x1) (s.gpr .x2) (s.gpr .x3).toNat (selOf s) with
    | some (some rs, _) => (s'.gpr .x0).setWidth 32 = 1 ∧
        bytesAt s'.mem (s.gpr .x0) (2 * J.ecdsa.curve.len) = encode J.ecdsa.curve rs
    | _ => (s'.gpr .x0).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .x0) (2 * J.ecdsa.curve.len) = List.replicate (2 * J.ecdsa.curve.len) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ selOf s₁ = selOf s₂ ∧
    ((anyResult J s₁.mem (s₁.gpr .x1) (s₁.gpr .x2) (s₁.gpr .x3).toNat (selOf s₁)).map (·.2)).getD 0 =
      ((anyResult J s₂.mem (s₂.gpr .x1) (s₂.gpr .x2) (s₂.gpr .x3).toNat (selOf s₂)).map (·.2)).getD 0 ∧
    tableAddr E s₁.syms = tableAddr E s₂.syms

/-- RFC 6979's signature of the arguments with the instance's hash function, and
the number of candidates tried. -/
abbrev result (I : Spec.Ecdsa.Rfc6979.Instance) (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  I.result m d digest

/-- A state satisfying the precondition, for scalars of `Q` bytes and a
SHA-256 digest (`hash` 3), with the memory `m` holding the comb's tables (of
`TB` bytes) at `0x100000`. -/
def satState (Q : Nat) (m : Mem) (TB : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 32 | .x4 => 0x8000 | .x5 => 3 | _ => 0
  sp := 0x20000
  mem := m
  rd := [⟨0x2000, Q⟩, ⟨0x3000, 32⟩, ⟨0x100000, TB⟩]
  wr := [⟨0x1000, 2 * Q⟩, ⟨0x8000, 8192⟩]
  syms _ := 0x100000

end VG.Proof.Ecdsa.Rfc6979.AArch64
