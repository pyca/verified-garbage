module

public import VerifiedGarbage.Proof.MillerRabin.X86.TableTransfer
public import VerifiedGarbage.Proof.MillerRabin.X86.TableEnd
public import VerifiedGarbage.Proof.MillerRabin.X86.OperandFrame

/-! # Append one power, retaining all preceding table entries -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem table_store {σ s : State} {base : Addr} {bytes w j k : Nat}
    (h : Stage base bytes w σ s) (hw : 4 ≤ w) (hu : w ≤ 128)
    (hf : arrAt w 28 ≤ bytes) (hj : 13 ≤ j ∧ j < 27) (hk : 0 < k ∧ k < 2 ^ 32)
    (width : σ.mem.readW (off base 48) 32 = BitVec.ofNat 32 w)
    (cursor : s.mem.readW (off (byteAddr (σ.gpr .esp)) tableCursor) 32 = ptr32 base (arrAt w j))
    (count : s.mem.readW (off base sK) 32 = BitVec.ofNat 32 k) :
    WP isa tabStore s fun t =>
      Stage base bytes w σ t ∧ w32 t.mem base sK = k - 1 ∧ t.zf = some (decide (k = 1)) ∧
      t.mem.readW (off (byteAddr (σ.gpr .esp)) tableCursor) 32 = ptr32 base (arrAt w (j + 1)) ∧
      numAt t.mem base w j = numAt s.mem base w 6 ∧
      (∀ a, a < 28 → a ≠ j → numAt t.mem base w a = numAt s.mem base w a) := by
  unfold tabStore
  refine WP.seq (WP.mono (table_transfer h hw hu hf hj width cursor) ?_)
  rintro u ⟨huStage, result⟩
  have ao : byteAddr (ptr32 base (arrAt w j)) = off base (arrAt w j) := by
    apply ptr32_addr
    have := h.context.ws.nowrap
    have := array_fits_bytes hf (show j < 28 by omega)
    omega
  have aa : byteAddr (ptr32 base (arrAt w 6)) = off base (arrAt w 6) := by
    apply ptr32_addr
    have := h.context.ws.nowrap
    have := array_fits_bytes hf (show 6 < 28 by decide)
    omega
  have F := result.frame
  rw [ao] at F
  have countU : u.mem.readW (off base sK) 32 = BitVec.ofNat 32 k :=
    (array_frame_header h.context.ws.nowrap hf (by omega) (by decide : sK + 4 ≤ 256) F).trans count
  refine WP.mono (table_end huStage hf hk result.dest countU) ?_
  rintro t ⟨ht, countT, zero, cursorT, tail⟩
  have tail' : Frame [⟨off (byteAddr (u.gpr .esp)) tableCursor, 4⟩, ⟨off base sK, 4⟩] u.mem t.mem := by
    rw [huStage.stack]
    exact tail
  have same := fun a ha => stack_header_frame_num huStage.context hf (a := a) ha
    (by decide : sK + 4 ≤ 256) tail'
  have value := congrArg BitVec.toNat result.value
  rw [aa, ao] at value
  refine ⟨ht, countT, zero, cursorT, (same j (by omega)).trans value, ?_⟩
  intro a ha hne
  exact (same a ha).trans (array_frame_num h.context.ws.nowrap hf ha (by omega) hne F)

end VG.Proof.MillerRabin.X86
