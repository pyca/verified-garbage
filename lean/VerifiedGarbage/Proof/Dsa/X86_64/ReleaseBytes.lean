module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Spec.Rsa.Contract

import Mathlib.Tactic.Set
import VerifiedGarbage.TCB.X86_64.State

/-! # Byte-string postconditions for masked DSA signature release -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64

theorem bytesAt_split (mem : Mem) (ptr : Addr) (n k : Nat) :
    Spec.Rsa.bytesAt mem ptr (n + k) = Spec.Rsa.bytesAt mem ptr n ++
      Spec.Rsa.bytesAt mem (ptr + BitVec.ofNat 64 n) k := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map, Function.comp_def,
    BitVec.ofNat_add, BitVec.add_assoc]

theorem bytesAt_masked {mem mem' : Mem} {src dst : Addr} {n : Nat} {valid : Bool}
    (h : ∀ i < n, mem' (dst + BitVec.ofNat 64 i) = if valid then mem (src + BitVec.ofNat 64 i) else 0) :
    Spec.Rsa.bytesAt mem' dst n = if valid then Spec.Rsa.bytesAt mem src n else List.replicate n 0 := by
  cases valid
  · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact h i (List.mem_range.mp hi)
  · simp only [↓reduceIte] at h ⊢
    exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

end VG.Proof.Dsa.X86_64
