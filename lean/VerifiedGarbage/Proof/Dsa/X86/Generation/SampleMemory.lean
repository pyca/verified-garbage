module
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.Words32

/-! # Exact scratch-array frames preserve the witness buffer and Montgomery constants -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.Proof.Mont

theorem sampleOutside_frame {base : Addr} {d len : Nat} {s t : Mem}
    (O : Outside base d len s t) (fit : d + len ≤ 2 ^ 64) : Frame [⟨off base d, len⟩] s t := by
  intro x hx
  have h := hx ⟨off base d, len⟩ (by simp)
  change ¬ ((x - (base + BitVec.ofNat 64 d)).toNat + 1 ≤ len) at h
  rw [← Nat.lt_iff_add_one_le, Offset.lt_iff x base fit] at h
  exact O x (by unfold ofs; omega)

theorem sampleOuts_frame {base : Addr} {rs : List (Nat × Nat)} {s t : Mem}
    (O : Outs base rs s t) (fit : ∀ r ∈ rs, r.1 + r.2 ≤ 2 ^ 64) :
    Frame (rs.map fun r => ⟨off base r.1, r.2⟩) s t := by
  intro x hx
  apply O x
  intro r hr
  have h := hx ⟨off base r.1, r.2⟩ (List.mem_map.mpr ⟨r, hr, rfl⟩)
  change ¬ ((x - (base + BitVec.ofNat 64 r.1)).toNat + 1 ≤ r.2) at h
  rw [← Nat.lt_iff_add_one_le, Offset.lt_iff x base (fit r hr)] at h
  unfold ofs
  omega

theorem sampleFrame_words {base : Addr} {d n : Nat} {rs : List Region} {s t : Mem}
    (O : Frame rs s t) (apart : ∀ r ∈ rs, Region.Disjoint ⟨off base d, 8 * n⟩ r)
    (fit : d + 8 * n ≤ 2 ^ 64) : wordsVal t base d n = wordsVal s base d n := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  apply val32_congr
  intro j hj
  apply congrArg BitVec.toNat
  apply O.readW (r := ⟨off base d, 8 * n⟩) ?_ apart (by decide)
  have h := Offset.contains_base (off base d) (by omega : 4 * j + 4 ≤ 8 * n) (by omega : 4 * j < 2 ^ 64)
  simpa only [off, Offset.add_add, Nat.add_comm d] using h
end VG.Proof.Dsa.X86.Generation
