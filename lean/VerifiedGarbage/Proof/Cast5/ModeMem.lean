module

public import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Cast5.Tables
public import VerifiedGarbage.Spec.Cast5
import VerifiedGarbage.Proof.Framework.Offset

/-!
# CAST5's subkeys and table under writes elsewhere, on any target

The subkeys (`scheduleAt_frame`) and the table of S-boxes (`held_frame`)
read the same after code that writes memory only apart from them, as the
modes' cores need.
-/

@[expose] public section

namespace VG.Proof.Cast5

open VG

theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 128⟩ r) : Spec.Cast5.scheduleAt m' p = Spec.Cast5.scheduleAt m p := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Cast5.scheduleAt, Vector.getElem_ofFn]
  have hb := fun j (hj : j < 128) => hf.bytes (R := ⟨p, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) hj
  rw [hb _ (by omega), hb _ (by omega), hb _ (by omega), hb _ (by omega)]

theorem s1234_length : Impl.Cast5.s1234.length = 512 := table_length _ _ _ _

theorem held_frame {rs : List Region} {m m' : Mem} {T : Addr} (h : Held m T Impl.Cast5.s1234)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨T, 4096⟩ r) : Held m' T Impl.Cast5.s1234 := by
  intro i hi
  rw [s1234_length] at hi
  rw [← h i (by rw [s1234_length]; exact hi)]
  exact hf.readW (r := ⟨T, 4096⟩) (Offset.contains_base _ (by omega) (by omega)) hd (by decide)

end VG.Proof.Cast5
