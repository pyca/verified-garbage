module

public import VerifiedGarbage.Proof.MillerRabin.X86.Data
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
import VerifiedGarbage.Proof.MillerRabin.X86.DataSlots
import VerifiedGarbage.Proof.MillerRabin.X86.SquareControl

/-! # A square's flag update as a known-value transition -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

def squareSlots (V : Nat → BitVec 32) (q r : Nat) (E F : Bool) : Nat → BitVec 32 :=
  setAt (setAt V sFlag (BitVec.ofNat 32 (F || (E && decide (r < q))).toNat))
    sSquares (BitVec.ofNat 32 (q - 1))

theorem Data.squareFlag {g : Geometry} (v : g.Valid) {A : Nat → Nat} {Js : List Nat}
    {V : Nat → BitVec 32} {Ds : List Nat} {s : State} (D : Data g A Js V Ds s)
    {q r : Nat} (positive : 0 < q) (qBound : q < 2 ^ 31) (rBound : r < 2 ^ 31) (E F : Bool)
    (known : ∀ d ∈ [sSquares, sThreshold, sEq2, sFlag], d ∈ Ds)
    (count : V sSquares = BitVec.ofNat 32 q) (threshold : V sThreshold = BitVec.ofNat 32 r)
    (eqBit : V sEq2 = BitVec.ofNat 32 E.toNat) (flag : V sFlag = BitVec.ofNat 32 F.toNat) :
    WP isa (.block squareFlag) s fun t =>
      Data g A Js (squareSlots V q r E F) ([sFlag, sSquares] ++ Ds) t ∧
      t.zf = some (decide (q = 1)) ∧
      Outs g.W [(sFlag, 4), (sSquares, 4)] s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  have read (d : Nat) (mem : d ∈ [sSquares, sThreshold, sEq2, sFlag]) := (D.slotValues d (known d mem)).2
  refine WP.mono (squareFlag_ok v D.context positive qBound rBound E F
    ((read _ (by simp)).trans count) ((read _ (by simp)).trans threshold)
    ((read _ (by simp)).trans eqBit) ((read _ (by simp)).trans flag))
    fun t ⟨Flag, Count, Z, O, K, C⟩ => ?_
  have flagWord : t.mem.readW (off g.W sFlag) 32 =
      BitVec.ofNat 32 (F || (E && decide (r < q))).toNat := by
    apply BitVec.eq_of_toNat_eq
    change w32 t.mem g.W sFlag = _
    rw [Flag]
    cases F || (E && decide (r < q)) <;> rfl
  have countWord : t.mem.readW (off g.W sSquares) 32 = BitVec.ofNat 32 (q - 1) := by
    apply BitVec.eq_of_toNat_eq
    change w32 t.mem g.W sSquares = _
    rw [Count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨D.afterSlots v C [sFlag, sSquares] ?_ ?_ O, Z, O, K⟩
  · intro d mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · refine ⟨by unfold scratchWord sFlag; simp, ?_⟩
      change t.mem.readW (off g.W sFlag) 32 = BitVec.ofNat 32 (F || (E && decide (r < q))).toNat
      exact flagWord
    · refine ⟨by unfold scratchWord sSquares; simp, ?_⟩
      change t.mem.readW (off g.W sSquares) 32 = BitVec.ofNat 32 (q - 1)
      exact countWord
  · intro d _ none
    have nf : d ≠ sFlag := fun eq => none (by simp [eq])
    have ns : d ≠ sSquares := fun eq => none (by simp [eq])
    exact (setAt_other _ _ ns).trans (setAt_other _ _ nf)

end VG.Proof.MillerRabin.X86
