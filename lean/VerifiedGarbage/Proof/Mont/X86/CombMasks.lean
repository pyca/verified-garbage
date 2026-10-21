module

import VerifiedGarbage.Impl.Mont.X86.CombTable
import VerifiedGarbage.Proof.Mont.X86.WindowSelect
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Mont.X86.Window
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! The comb's equality masks occupy a fixed, otherwise unused scratch range. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86

/-- Prepare all equality masks, preserving the table, window index and every
byte outside the mask range. -/
theorem combMasks_ok {s : State} {base : Addr} {size mask : Nat}
    (hs : Scr s base size) (hmask : 8 ≤ mask) (hw : w32 s.mem base 4 < 32) :
    ∀ k, k ≤ 32 → mask + 4*k ≤ size →
    WP isa (.block ((List.range k).flatMap fun j =>
      VG.Impl.Mont.X86.Dynamic.windowMask j ++ ([.store (sc (mask+4*j)) .ecx] : List Instr))) s fun t =>
      Outside base mask (4*k) s.mem t.mem ∧
      (∀ j < k, t.mem.readW (off base (mask+4*j)) 32 =
        if w32 s.mem base 4 = j then BitVec.allOnes 32 else 0) ∧
      Keeps [.eax, .ecx] s t
  | 0, _, _ => WP.block_nil ⟨Outside.refl _ _ _ _, by omega, Keeps.refl _ _⟩
  | k+1, hk, hz => by
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    refine WP.block_append (WP.mono (combMasks_ok hs hmask hw k (by omega) (by omega))
      fun u ⟨O, V, K⟩ => ?_)
    have hu := hs.of_keeps K (by decide)
    have win : w32 u.mem base 4 = w32 s.mem base 4 := O.w32 (by omega) (by omega)
    refine WP.block_append (WP.mono (windowMask_ok hu (by omega) (by rw [win]; exact hw) (by omega))
      fun v ⟨M, C, K'⟩ => ?_)
    have hv := hu.of_keeps K' (by decide)
    refine wp_storeS (hv.ea (d := mask+4*k) (by omega))
      (hv.write (d := mask+4*k) (n := 4) (by omega)) fun t W => WP.block_nil ?_
    have nw := hs.nowrap
    have F : Outside base (mask+4*k) 4 u.mem t.mem := by
      rw [W.mem, M]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨(O.mono (Nat.le_refl _) (by omega)).trans (F.mono (by omega) (by omega)), ?_,
      (K.trans K').trans (W.keeps _)⟩
    intro j hj
    by_cases eq : j = k
    · subst j
      rw [W.mem, Mem.readW_writeW_self32, C, win]
    · have jl : j < k := by omega
      have same := F.w32 (d := mask+4*j) (by omega) (by omega)
      apply BitVec.eq_of_toNat_eq
      change w32 t.mem base (mask+4*j) = _
      rw [same]
      exact congrArg BitVec.toNat (V j jl)

end VG.Proof.Mont.X86.Dynamic
