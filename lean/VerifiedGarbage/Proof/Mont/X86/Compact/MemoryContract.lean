module

import VerifiedGarbage.Proof.Mont.X86.Compact.EntryMemory
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Compact.Layout
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.X86.Compact.Entry
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame

/-! # Compact writes satisfy the public prepared workspace frame -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Proof.Mont VG.Proof.Rsa.Mont

theorem Entry.pushed_byte {s : State} (A : Entry s) {i : Nat} (index : i < lenOf s) :
    (entered s).mem (wsOf s + BitVec.ofNat 64 i) = s.mem (wsOf s + BitVec.ofNat 64 i) := by
  have saved := pushed_frame (rs := savedRegisters) (s := s) (by decide) A.stackFit
  exact saved _ fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    intro hc
    exact A.savedSeparate' _ hc (Offset.contains_base _ (by omega) (by have := A.bound; omega))

theorem Entry.keeps {s : State} (A : Entry s) {m : Mem}
    (O : Outs (wsOf s)
      [(arrAt (wOf s.mem (wsOf s)) 2, 8 * (2 * wOf s.mem (wsOf s)) + 28),
       (arrAt (wOf s.mem (wsOf s)) (arg s 2).toNat, 4 * (2 * wOf s.mem (wsOf s)))]
      (entered s).mem m) :
    Proof.Rsa.Mont.Keeps (wsOf s) (arg s 1).toNat (wOf s.mem (wsOf s)) (arg s 2).toNat s.mem m := by
  intro i index far
  have two := far 2 (by change 2 ∈ [2, 3, (arg s 2).toNat]; simp)
  have three := far 3 (by change 3 ∈ [2, 3, (arg s 2).toNat]; simp)
  have output := far (arg s 2).toNat (by change (arg s 2).toNat ∈ [2, 3, (arg s 2).toNat]; simp)
  have product := product_fits (wOf s.mem (wsOf s))
  have acc : VG.Impl.Mont.X86.Compact.accOff = 24 := rfl
  have keep := O (wsOf s + BitVec.ofNat 64 i) (by
    intro r hr
    rw [ofs_off0 (wsOf s) (by have := A.bound; omega)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · dsimp only
      unfold arrAt hdrBytes at two three product ⊢
      omega
    · dsimp only
      omega)
  exact keep.trans (A.pushed_byte (by unfold lenOf; omega))

end VG.Proof.Mont.X86.Compact
