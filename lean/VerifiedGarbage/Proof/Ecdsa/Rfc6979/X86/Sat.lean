module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Verified
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Deterministic ECDSA on x86 (32-bit): the shared contract is satisfiable

A state that satisfies `I₀.signAnyContract`'s precondition (`anySat`), for
scalars of up to 66 bytes, SHA-256 (`hash = 3`), and the arguments
`0x1000, 0x2000, 0x3000, 32, 0x8000, 3` at `0x20004`, over the memory `m`
(the comb's tables, for P-256).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

/-- The arguments' bytes at `0x20004`, over `m`. -/
def anyMem (m : Mem) : Mem := fun a =>
  if a = 0x20005 then 0x10 else if a = 0x20009 then 0x20 else if a = 0x2000d then 0x30 else
  if a = 0x20010 then 0x20 else if a = 0x20015 then 0x80 else if a = 0x20018 then 3 else
  if (a - 0x20004).toNat < 24 then 0 else m a

/-- The state, for scalars of `Q` bytes and the tables `tbl` at the symbols `sy`. -/
def anySat (m : Mem) (sy : String → BitVec 32) (Q : Nat) (tbl : List Region) : State where
  gpr r := match r with
    | .esp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := anyMem m
  rd := [⟨0x2000, Q⟩, ⟨0x3000, 32⟩] ++ tbl
  wr := [⟨0x1000, 2 * Q⟩, ⟨0x8000, 8192⟩, ⟨0x20004, 24⟩]
  syms := sy

variable (m : Mem) (sy : String → BitVec 32) (Q : Nat) (tbl : List Region)

theorem anySat_arg (i : Nat) (hi : i < 6) :
    arg (anySat m sy Q tbl) i = arg (anySat (fun _ => 0) (fun _ => 0) 0 []) i := by
  unfold arg
  apply Mem.readW_congr
  intro j hj
  have h : ((argAddr (anySat (fun _ => 0) (fun _ => 0) 0 []) i + BitVec.ofNat 64 j) - 0x20004).toNat < 24 := by
    match i, hi, j, hj with
    | 0, _, 0, _ | 0, _, 1, _ | 0, _, 2, _ | 0, _, 3, _ | 1, _, 0, _ | 1, _, 1, _ | 1, _, 2, _ | 1, _, 3, _
    | 2, _, 0, _ | 2, _, 1, _ | 2, _, 2, _ | 2, _, 3, _ | 3, _, 0, _ | 3, _, 1, _ | 3, _, 2, _ | 3, _, 3, _
    | 4, _, 0, _ | 4, _, 1, _ | 4, _, 2, _ | 4, _, 3, _ | 5, _, 0, _ | 5, _, 1, _ | 5, _, 2, _ | 5, _, 3, _ => decide
  show anyMem m _ = anyMem (fun _ => 0) _
  unfold anyMem
  simp only [show argAddr (anySat m sy Q tbl) i = argAddr (anySat (fun _ => 0) (fun _ => 0) 0 []) i from rfl, h,
    ite_true]

theorem anySat_args : arg (anySat m sy Q tbl) 0 = 0x1000 ∧ arg (anySat m sy Q tbl) 1 = 0x2000 ∧
    arg (anySat m sy Q tbl) 2 = 0x3000 ∧ arg (anySat m sy Q tbl) 3 = 32 ∧ arg (anySat m sy Q tbl) 4 = 0x8000 ∧
    arg (anySat m sy Q tbl) 5 = 3 := by
  simp only [anySat_arg m sy Q tbl _ (show 0 < 6 by decide), anySat_arg m sy Q tbl _ (show 1 < 6 by decide),
    anySat_arg m sy Q tbl _ (show 2 < 6 by decide), anySat_arg m sy Q tbl _ (show 3 < 6 by decide),
    anySat_arg m sy Q tbl _ (show 4 < 6 by decide), anySat_arg m sy Q tbl _ (show 5 < 6 by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem sat_nil (I₀ : Spec.Ecdsa.Rfc6979.Instance) (hS : I₀.scratchWords = 1024) (hQ : I₀.ecdsa.curve.len ≤ 66) :
    ∃ s, (I₀.signAnyContract (X86.abi.withConsts []) 536).pre s := by
  refine ⟨anySat (fun _ => 0) (fun _ => 0) I₀.ecdsa.curve.len [], ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := anySat_args (fun _ => 0) (fun _ => 0) I₀.ecdsa.curve.len []
  have aa : argAddr (anySat (fun _ => 0) (fun _ => 0) I₀.ecdsa.curve.len []) 0 = 0x20004 := rfl
  sig_pre [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  simp only [a0, a1, a2, a3, a4, a5, aa, hS]
  repeat' apply And.intro
  all_goals first
    | decide
    | rfl
    | exact Region.disjoint_of_sep (by decide)
    | exact Region.disjoint_of_sep (by simp only [Region.sep]; simp; omega)
    | (intro H h; simp only [Spec.HashId.mgf1] at h; cases h; rfl)
    | (show 4096 + 2 * I₀.ecdsa.curve.len ≤ 2 ^ 32; omega)
    | (show 8192 + I₀.ecdsa.curve.len ≤ 2 ^ 32; omega)


end VG.Proof.Ecdsa.Rfc6979.X86
