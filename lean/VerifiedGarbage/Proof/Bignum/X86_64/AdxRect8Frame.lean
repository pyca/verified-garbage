import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Counter
import VerifiedGarbage.Proof.Bignum.X86_64.OpAt

namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

/-- The tile's temporary header words do not overlap the Montgomery header. -/
theorem frame_hdr {m m' : Mem} {B : Addr} {w e n : Nat} {mi : BitVec 64}
    (hh : Hdr m B w mi) (he : hdrBytes ≤ e)
    (hf : Frm B [(e,n),(carryOffset,8),(8*sFn 13,8)] m m') : Hdr m' B w mi := by
  have low (k : Nat) (hk : k < 16) : word m' B (8*k) = word m B (8*k) := by
    apply hf.word_eq
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [] <;>
        unfold carryOffset sFn hdrBytes at * <;> omega
    · omega
  exact ⟨(low sW (by decide)).trans hh.hw,(low sMinv (by decide)).trans hh.hminv,
    fun k hk => (low (sArr k) (by unfold sArr; omega)).trans (hh.harr k hk)⟩

/-- Nor the slots of the operands' bases. -/
theorem frame_ops {m m' : Mem} {B : Addr} {w e n : Nat} {ps : List (Nat × Nat)}
    (hv : Ops m B w ps) (he : hdrBytes ≤ e)
    (hf : Frm B [(e,n),(carryOffset,8),(8*sFn 13,8)] m m') : Ops m' B w ps :=
  hv.of_frm hf fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [] <;> unfold carryOffset sFn hdrBytes at * <;> omega

/-- Two adjacent scratch arrays contain every rectangular tile. -/
theorem tile_ranges {w i j a : Nat} (hi : i+8 ≤ w) (hj : j+8 ≤ w)
    (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) :
    slot w a+8*i+64 ≤ slot w 8 ∧
    slot w aAcc+16+8*(i+j)+128 ≤ slot w 8 ∧
    (slot w a+8*i+64 ≤ slot w aAcc+16+8*(i+j) ∨
      slot w aAcc+16+8*(i+j)+128 ≤ slot w a+8*i) := by
  have sa := slot_le (w := w) ha
  have st := slot_le (w := w) (show aTmp < 8 by decide)
  have s1 := slot_sep (w := w) ha1
  have s2 := slot_sep (w := w) ha2
  unfold slot aAcc aTmp at *
  omega

end VG.Proof.Bignum.X86_64.AdxRect8
