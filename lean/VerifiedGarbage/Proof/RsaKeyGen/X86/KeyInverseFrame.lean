module

public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

/-! # A compact frame for inversions at any native word width

Only the small inverse bank and its scalar slots can change. In
particular, the key-generation arguments and persistent arrays survive.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot

def inverseRanges (n : Nat) (slots : List Nat) : List (Nat × Nat) :=
  (hdr, 4 * (15 * (n + 2))) :: slots.map (fun d => (d, 4))

theorem inverse_frame {m m' : Mem} {B : Addr} {n : Nat} {js ds : List Nat}
    (indices : ∀ j ∈ js, j < 15) (changed : Keep B n js ds m m') :
    Outs B (inverseRanges n ds) m m' := by
  intro x hx
  apply changed x
  intro r hr
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨d, hd, rfl⟩
  · have outside := hx (hdr, 4 * (15 * (n + 2))) (List.mem_cons_self ..)
    have lower : hdr ≤ arr n j := Nat.le_add_right ..
    have upper := arr_end (w := n) (indices j hj)
    have endEq : arr n 15 = hdr + 4 * (15 * (n + 2)) := by unfold arr S; omega
    rw [endEq] at upper
    simp only at outside ⊢
    omega
  · exact hx _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨d, hd, rfl⟩))

theorem inverse_frame_slots {m m' : Mem} {B : Addr} {n : Nat} {js ds : List Nat}
    (indices : ∀ j ∈ js, j < 15) (changed : Keep B n js [] m m') :
    Outs B (inverseRanges n ds) m m' := by
  have O := inverse_frame indices changed
  refine O.mono ?_
  intro r hr
  simp only [inverseRanges, List.map_nil, List.mem_singleton] at hr
  subst r
  exact List.mem_cons_self ..

theorem inverse_frame_clear {m m' : Mem} {B : Addr} {n : Nat} (ds : List Nat)
    (changed : Outside B hdr (4 * (15 * (n + 2))) m m') :
    Outs B (inverseRanges n ds) m m' :=
  Outs.of_outside changed (List.mem_cons_self ..)

end VG.Proof.RsaKeyGen.X86.Key
