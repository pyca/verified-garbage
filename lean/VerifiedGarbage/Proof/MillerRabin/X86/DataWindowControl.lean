module

public import VerifiedGarbage.Proof.MillerRabin.X86.Data
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.WindowControl
import VerifiedGarbage.Proof.MillerRabin.X86.DataSlots

/-! # One exponent-window update retains exact known values -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

def windowSlots (V : Nat → BitVec 32) (q : Nat) (E1 E2 F : Bool) : Nat → BitVec 32 :=
  setAt (setAt (setAt V sFlag (BitVec.ofNat 32
      (if (V sValue >>> 28).toNat = 0 then F else E1 || E2).toNat))
    sValue (V sValue <<< 4)) sWindows (BitVec.ofNat 32 (q - 1))

theorem Data.windowEnd {g : Geometry} (v : g.Valid) {A : Nat → Nat} {Js : List Nat}
    {V : Nat → BitVec 32} {Ds : List Nat} {s : State} (D : Data g A Js V Ds s)
    (q : Nat) (positive : 0 < q) (bound : q < 2 ^ 32) (E1 E2 F : Bool)
    (known : ∀ d ∈ [sEq1, sEq2, sFlag, sValue, sWindows], d ∈ Ds)
    (eq1 : V sEq1 = BitVec.ofNat 32 E1.toNat) (eq2 : V sEq2 = BitVec.ofNat 32 E2.toNat)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) (count : V sWindows = BitVec.ofNat 32 q) :
    WP isa (.block windowEnd) s fun t =>
      Data g A Js (windowSlots V q E1 E2 F) ([sFlag, sValue, sWindows] ++ Ds) t ∧
      t.zf = some (decide (q = 1)) ∧ Outs g.W windowWrites s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx] s t := by
  have read (d : Nat) (mem : d ∈ [sEq1, sEq2, sFlag, sValue, sWindows]) := (D.slotValues d (known d mem)).2
  refine WP.mono (windowEnd_ok v D.context q positive bound E1 E2 F
    ((read _ (by simp)).trans eq1) ((read _ (by simp)).trans eq2)
    ((read _ (by simp)).trans flag) ((read _ (by simp)).trans count))
    fun t ⟨Flag, Value, Count, Z, O, K, C⟩ => ?_
  rw [read sValue (by simp)] at Flag Value
  have flagWord : t.mem.readW (off g.W sFlag) 32 = BitVec.ofNat 32
      (if (V sValue >>> 28).toNat = 0 then F else E1 || E2).toNat := by
    apply BitVec.eq_of_toNat_eq
    change w32 t.mem g.W sFlag = _
    rw [Flag]
    cases (if (V sValue >>> 28).toNat = 0 then F else E1 || E2) <;> rfl
  have countWord : t.mem.readW (off g.W sWindows) 32 = BitVec.ofNat 32 (q - 1) := by
    apply BitVec.eq_of_toNat_eq
    change w32 t.mem g.W sWindows = _
    rw [Count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨D.afterSlots v C [sFlag, sValue, sWindows] ?_ ?_ O, Z, O, K⟩
  · intro d mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · refine ⟨by unfold scratchWord sFlag; simp, ?_⟩
      change t.mem.readW (off g.W sFlag) 32 = BitVec.ofNat 32
        (if (V sValue >>> 28).toNat = 0 then F else E1 || E2).toNat
      exact flagWord
    · refine ⟨by unfold scratchWord sValue; simp, ?_⟩
      change t.mem.readW (off g.W sValue) 32 = V sValue <<< 4
      exact Value
    · refine ⟨by unfold scratchWord sWindows; simp, ?_⟩
      change t.mem.readW (off g.W sWindows) 32 = BitVec.ofNat 32 (q - 1)
      exact countWord
  · intro d _ none
    have nf : d ≠ sFlag := fun eq => none (by simp [eq])
    have nv : d ≠ sValue := fun eq => none (by simp [eq])
    have nw : d ≠ sWindows := fun eq => none (by simp [eq])
    exact ((setAt_other _ _ nw).trans (setAt_other _ _ nv)).trans (setAt_other _ _ nf)

end VG.Proof.MillerRabin.X86
