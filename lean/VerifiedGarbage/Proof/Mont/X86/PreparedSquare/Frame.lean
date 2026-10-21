module

public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Args

import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.RawArgs
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.ArgWs

/-! # Four public cached values in the square's fixed stack frame -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Mont.X86

def cacheRegisters : List Reg := [.ebx, .esi, .ebp, .eax]
def entered (s : State) : State := pushed cacheRegisters s

theorem entered_fit {s : State} (fit : 16 ≤ (s.gpr .esp).toNat) :
    ((entered s).gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
  rw [entered, pushed_esp, show 4 * cacheRegisters.length = 16 from rfl, sub_toNat fit]
  have := (s.gpr .esp).isLt
  omega

theorem entered_region (s : State) :
    below (s.gpr .esp) 16 = ⟨((entered s).gpr .esp).setWidth 64, 16⟩ := by
  unfold entered
  rw [pushed_esp]
  rfl

theorem entered_word {s : State} (fit : 16 ≤ (s.gpr .esp).toNat) {i : Nat} (index : i < 4) :
    readSrc (entered s) (.mem (at_ .esp (4 * i))) =
      some (s.gpr (cacheRegisters[3 - i]'(by change 3 - i < 4; omega))) := by
  have access : InRegions ((entered s).rd ++ (entered s).wr)
      (addr ((entered s).gpr .esp) (4 * i)) 4 := by
    rw [entered, pushed_wr]
    refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ List.mem_cons_self, ?_⟩
    change (below (s.gpr .esp) 16).Contains (addr ((entered s).gpr .esp) (4 * i)) 4
    rw [entered_region, addr_eq (by have := entered_fit fit; omega)]
    exact Offset.contains_base _ (by omega) (by omega)
  change (entered s).load32 (addr ((entered s).gpr .esp) (4 * i)) = _
  rw [State.load32, ite_eq_left access]
  exact congrArg some (pushed_word (rs := cacheRegisters) (by decide) fit index)

theorem entered_far {s : State} {W : Addr} {L : Nat}
    (fit : 16 ≤ (s.gpr .esp).toNat)
    (apart : (below (s.gpr .esp) 16).Disjoint ⟨W, L⟩) {i : Nat} (index : i < 4) :
    Dynamic.ArgFar (entered s) W L (at_ .esp (4 * i)) := by
  intro j byte
  apply Dynamic.ofs_far
  intro hc
  apply apart _ ?_ hc
  rw [entered_region]
  change (⟨((entered s).gpr .esp).setWidth 64, 16⟩ : Region).Contains
    (addr ((entered s).gpr .esp) (4 * i) + BitVec.ofNat 64 j) 1
  rw [addr_eq (by have := entered_fit fit; omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  exact Offset.contains_base _ (by omega) (by omega)

theorem entered_args {s : State} {W : Addr} {L : Nat} {C : Nat → BitVec 32}
    (fit : 16 ≤ (s.gpr .esp).toNat)
    (apart : (below (s.gpr .esp) 16).Disjoint ⟨W, L⟩)
    (eax : s.gpr .eax = C 0) (ebx : s.gpr .ebx = C 2)
    (ebp : s.gpr .ebp = C 0 + C 3) (esi : s.gpr .esi = C 0 + C 7)
    (inv : C 4 = BitVec.ofNat 32 56) (modulus : C 3 = BitVec.ofNat 32 256) :
    Args (entered s) W L C := by
  refine ⟨?_, ?_, inv, modulus⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · simpa [cacheArg, cacheValue, cacheRegisters] using
        (entered_word fit (i := 0) (by decide)).trans (congrArg some eax)
    · simpa [cacheArg, cacheValue, cacheRegisters] using
        (entered_word fit (i := 3) (by decide)).trans (congrArg some ebx)
    · simpa [cacheArg, cacheValue, cacheRegisters] using
        (entered_word fit (i := 1) (by decide)).trans (congrArg some ebp)
    · simpa [cacheArg, cacheValue, cacheRegisters] using
        (entered_word fit (i := 2) (by decide)).trans (congrArg some esi)
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact entered_far fit apart (i := 0) (by decide)
    · exact entered_far fit apart (i := 3) (by decide)
    · exact entered_far fit apart (i := 1) (by decide)
    · exact entered_far fit apart (i := 2) (by decide)

end VG.Proof.Mont.X86.PreparedSquare
