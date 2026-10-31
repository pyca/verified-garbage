module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Loops
public import VerifiedGarbage.Proof.Aes.PPC64LE.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: ECB contracts instantiate the shared batch and tail loops.
/-! # POWER8 AES ECB correctness -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE
open VG.Proof.Aes.Memory
open VG.Impl.Aes.PPC64LE.Crypto (mask byteMask)

def blockGprs : List Reg := [.r0, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem blocks_ok (inverse : Bool) (s : State)
    (hs : (Proof.Aes.blocksPPC64LE (result inverse)).pre s) :
    WP isa (Impl.Aes.PPC64LE.Crypto.blocks inverse) s fun t =>
      Keep blockGprs s t ∧ (Proof.Aes.blocksPPC64LE (result inverse)).post s t := by
  obtain ⟨hrd, hwr, hsep, _, _, hbound, hnr⟩ := hs
  let n := (s.gpr .r6).toNat
  let nr := (s.gpr .r4).toNat
  let D := s.gpr .r5
  have hnrlt : nr < 15 := by rcases hnr with h | h | h <;> omega
  have hnrmin : 1 < nr := by rcases hnr with h | h | h <;> omega
  have hsize : 16*n ≤ 2^64 := by omega
  rw [Impl.Aes.PPC64LE.Crypto.blocks]
  by_cases hz : s.gpr .r6 = 0
  · refine WP.ite true (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hz]; rfl)
      (fun _ => WP.block_nil ?_) (by simp)
    refine ⟨Keep.refl _ _, ?_⟩
    simp only [Proof.Aes.blocksPPC64LE, hz, show (0 : BitVec 64).toNat = 0 from rfl,
      Spec.Aes.statesAt, List.range_zero, List.map_nil]
  · refine WP.ite false (by simpa only [eval, State.read, Size.bits, BitVec.setWidth_eq, Option.some.injEq, beq_eq_false_iff_ne] using hz)
      (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (blocks_setup_ok s) fun base ⟨hp, hl, hzero, hm, he⟩ => ?_)
    have hc : LoopConfig inverse false base nr n D := by
      refine ⟨⟨hzero, hm, ?_, hnrmin, hnrlt, ?_⟩, hsize, ?_, ?_, by simp⟩
      · rw [he.keep.gpr (by decide)]
        simp only [nr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · intro j hj
        rw [he.keep.2.1, he.keep.2.2, he.keep.gpr (by decide), hrd, hwr]
        exact ⟨⟨s.gpr .r3, 240⟩, by simp,
          Offset.contains_base _ (d := 16*j) (n := 16) (k := 240) (by omega) (by omega)⟩
      · rw [he.keep.2.2, hwr]
        exact List.mem_cons_self
      · rw [he.keep.gpr (by decide)]
        exact hsep
    have hi : LoopInv inverse false base nr n D 0 0 base := by
      refine ⟨by omega, Keep.refl _ _, ?_, ?_, Processed.refl _ _ _ _, Frame.refl _ _, hm,
        by simp, by simp, by simp⟩
      · simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hp
      · simpa only [Nat.sub_zero, n, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hl
    refine WP.mono (batches_ok hc hi) fun t ht => ⟨?_, ?_⟩
    · exact (he.keep.trans ht.keep).mono (by simp [blockGprs, loopGprs])
    · have hstates := ht.processed.statesAt
      have hsched : schedule nr base = schedule nr s := by
        rw [schedule, he.mem, he.keep.gpr (by decide)]
      rw [hsched, he.mem] at hstates
      change Spec.Aes.statesAt t.mem D n = (List.range n).map
        (fun i => result inverse nr (schedule nr s) (Spec.Aes.stateAt s.mem (D + BitVec.ofNat 64 (16*i)))) at hstates
      simpa only [Proof.Aes.blocksPPC64LE, Spec.Aes.statesAt, List.map_map, Function.comp_def] using hstates

end VG.Proof.Aes.PPC64LE.Crypto
