module

public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame

import VerifiedGarbage.Proof.Mont.X86.Compact.EntryMemory

public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingContext
public import VerifiedGarbage.Proof.Mont.X86.Compact.Entry
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryArgs
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryValues
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingEntry
import VerifiedGarbage.Proof.Mont.X86.Compact.Prepared
import VerifiedGarbage.Proof.Mont.X86.Compact.Layout

/-! # Public cdecl inputs determine the prepared multiplication's geometry -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.Mont

/-- Values outside the five arguments are irrelevant and fixed at zero. -/
def args5 (s : State) (i : Nat) : BitVec 32 := if i < 5 then arg s i else 0

def geometry (s : State) : Geometry :=
  let w := wOf s.mem (wsOf s)
  { W := wsOf s, L := lenOf s, A := args5 s, N := 2 * w, S := arrAt w 2, mo := arrAt w 0,
    a := arrAt w (arg s 3).toNat, b := arrAt w (arg s 4).toNat, o := arrAt w (arg s 2).toNat }

theorem Entry.geometry_valid {s : State} (A : Entry s) : (geometry s).Valid := by
  have fit : arrAt (wOf s.mem (wsOf s)) 8 ≤ lenOf s := by
    simpa only [lenOf, Nat.mul_comm] using A.layout.2.2.1
  have lay := layout_bounds fit A.left A.right
  have outFit := array_fit fit A.output.1
  have apart := operand_apart (w := wOf s.mem (wsOf s)) A.output
  have product := product_fits (wOf s.mem (wsOf s))
  have acc : VG.Impl.Mont.X86.Compact.accOff = 24 := rfl
  have bound : (wsOf s).toNat + lenOf s ≤ 2 ^ 32 := by rw [A.ws_toNat]; exact A.bound
  constructor
  · exact A.ws_toNat.symm
  · exact lay
  · have := A.layout.1; change 0 < 2 * wOf s.mem (wsOf s); omega
  · change 4 * (2 * wOf s.mem (wsOf s)) < 2 ^ 32
    have := lay.scr; omega
  · exact A.output.1
  · change 128 ≤ arrAt (wOf s.mem (wsOf s)) (arg s 2).toNat
    unfold arrAt hdrBytes; omega
  · change arrAt (wOf s.mem (wsOf s)) (arg s 2).toNat + 4 * (2 * wOf s.mem (wsOf s)) ≤ lenOf s
    omega
  · change arrAt (wOf s.mem (wsOf s)) (arg s 2).toNat + 4 * (2 * wOf s.mem (wsOf s)) ≤
        arrAt (wOf s.mem (wsOf s)) 2 ∨
      arrAt (wOf s.mem (wsOf s)) 2 + 8 * (2 * wOf s.mem (wsOf s)) + 28 ≤
        arrAt (wOf s.mem (wsOf s)) (arg s 2).toNat
    omega
  · change arrAt (wOf s.mem (wsOf s)) (arg s 2).toNat = arrAt (wOf s.mem (wsOf s)) 0 ∨
        arrAt (wOf s.mem (wsOf s)) (arg s 2).toNat + 4 * (2 * wOf s.mem (wsOf s)) ≤ arrAt (wOf s.mem (wsOf s)) 0 ∨
        arrAt (wOf s.mem (wsOf s)) 0 + 4 * (2 * wOf s.mem (wsOf s)) ≤ arrAt (wOf s.mem (wsOf s)) (arg s 2).toNat
    by_cases zero : (arg s 2).toNat = 0
    · exact Or.inl (by rw [zero])
    · have := array_mono (wOf s.mem (wsOf s)) (i := 0) (j := (arg s 2).toNat) (by omega)
      exact Or.inr (Or.inr (by omega))

theorem Entry.context {s : State} (A : Entry s) : Context (geometry s) (entered s) := by
  refine ⟨A.pushed_ws, ?_, ?_, A.output_ptr, A.timing_wf⟩
  · constructor
    · intro i index
      change readSrc (entered s) (.mem (VG.Impl.Mont.X86.Compact.arg i)) = some (if i < 5 then arg s i else 0)
      rw [ite_eq_left index]
      exact A.pushed_args.read i index
    · exact A.pushed_args.far
  · have M := A.metadata
    exact ⟨M.width, M.aIndex, M.bIndex, M.scratch, M.modulus, M.left, M.right⟩

theorem geometry_eq {s t : State} (args : ∀ i < 5, arg s i = arg t i)
    (width : wOf s.mem (wsOf s) = wOf t.mem (wsOf t)) : geometry s = geometry t := by
  have a0 := args 0 (by decide)
  have a1 := args 1 (by decide)
  have a2 := args 2 (by decide)
  have a3 := args 3 (by decide)
  have a4 := args 4 (by decide)
  have all : args5 s = args5 t := by
    funext i
    unfold args5
    split
    · exact args i (by assumption)
    · rfl
  unfold geometry
  rw [width, wsOf, wsOf, lenOf, lenOf, a0, a1, a2, a3, a4, all]

end VG.Proof.Mont.X86.Compact
