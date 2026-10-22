module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageKeeps
public import VerifiedGarbage.Proof.MillerRabin.X86.RestoreProtected
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Restoring the borrowed prefixes recovers exactly the shared preservation contract -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Spec.Rsa.Mont (arrAt)

theorem read_bytes {m m' : Mem} {base : Addr} {d n i : Nat}
    (e : m'.read (off base d) n = m.read (off base d) n) (hi : i < n) :
    m' (off base (d + i)) = m (off base (d + i)) := by
  have x := congrArg (fun v : BitVec (8 * n) => v.extractLsb' (8 * i) 8) e
  rw [Mem.extractLsb'_read _ _ hi, Mem.extractLsb'_read _ _ hi, Offset.add_add] at x
  exact x

theorem restored_frame_keeps {σ s : State} {m' : Mem} {base : Addr} {bytes w len : Nat}
    (h : Stage base bytes w σ s) (size : bytes = 8 * len) (fit : arrAt w 28 ≤ bytes)
    (F : Frame [⟨off base (scratch w), 32⟩, ⟨off base (arrAt w 4), 8 * w⟩] s.mem m')
    (tail : m'.read (off base (scratch w)) 32 = σ.mem.read (off base (scratch w)) 32)
    (array : m'.read (off base (arrAt w 4)) (8 * w) = σ.mem.read (off base (arrAt w 4)) (8 * w)) :
    Spec.MillerRabin.Keeps Spec.MillerRabin.compact base len w σ.mem m' := by
  have tailBytes : ∀ i < 32, m' (off base (scratch w + i)) = σ.mem (off base (scratch w + i)) :=
    fun _ hi => read_bytes tail hi
  have arrayBytes : ∀ i < 8 * w, m' (off base (arrAt w 4 + i)) = σ.mem (off base (arrAt w 4 + i)) :=
    fun _ hi => read_bytes array hi
  refine restored_keeps ?_ tailBytes arrayBytes
  intro i hi outside
  by_cases arrayHit : arrAt w 4 ≤ i ∧ i < arrAt w 4 + 8 * w
  · simpa only [Nat.add_sub_of_le arrayHit.1] using arrayBytes (i - arrAt w 4) (by omega)
  have core := h.workspace_keeps size fit i hi outside
  have nw := h.context.ws.nowrap
  have arrayFit := array_fits_bytes fit (show 4 < 28 by decide)
  have tailFit : scratch w + 32 ≤ bytes := by
    have := scratch_start w
    have := array_monotone w (show 2 ≤ 28 by decide)
    omega
  have temp := outside (scratch w, Spec.Rsa.MontMul.scratchBytes w) (by simp [workingRanges])
  have tailOut : i + 1 ≤ scratch w ∨ scratch w + 32 ≤ i := by
    simp only [Spec.Rsa.MontMul.scratchBytes] at temp
    omega
  have finalEq : m' (off base i) = s.mem (off base i) := by
    apply F
    intro r hr hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (Offset.disjoint base tailOut (by omega) (by omega)) _ (Region.contains_self _ _) hc
    · have apart : i + 1 ≤ arrAt w 4 ∨ arrAt w 4 + 8 * w ≤ i := by omega
      exact (Offset.disjoint base apart (by omega) (by omega)) _ (Region.contains_self _ _) hc
  exact finalEq.trans core

end VG.Proof.MillerRabin.X86
