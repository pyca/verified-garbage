module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Loops
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.CtrSetup
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.CtrFinish
public import VerifiedGarbage.Proof.Aes.PPC64LE.Base
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: CTR's contract permits a final counter store after the shared data loops.
/-! # POWER8 AES CTR correctness

`ctr32_wp`: the setup (`ctr_setup_ok`), the data loops (`batches_ok`) in
place, and the counter block stored back. -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE
open VG.Proof.Aes.Memory
open VG.Impl.Aes.PPC64LE.Crypto (counterBase counterStep counterOne mask byteMask)

def ctrGprs : List Reg := [.r0, .r8, .r6, .r7, .r9, .r10, .r11, .r12]

theorem read_write_self16 (m : Mem) (a : Addr) (v : BitVec 128) : (m.write a 16 v).read a 16 = v :=
  Mem.read_eq_of_bytes fun i hi => by
    simp only [Mem.write, Mem.sub_ofNat_toNat a (show i < 2 ^ 64 by omega_using [hi]), hi, ite_true]

/-- `ctr32`: the `n = r7` blocks at `r6` XORed with the keystream, in place,
and the counter block advanced by `n`. -/
theorem ctr32_wp (s : State) (hK : (⟨s.gpr .r3, 240⟩ : Region) ∈ s.rd ++ s.wr)
    (hC : (⟨s.gpr .r5, 16⟩ : Region) ∈ s.wr)
    (hw : (⟨s.gpr .r6, 16 * (s.gpr .r7).toNat⟩ : Region) ∈ s.wr)
    (hr : (⟨s.gpr .r6, 16 * (s.gpr .r7).toNat⟩ : Region) ∈ s.rd ++ s.wr)
    (hsep : (⟨s.gpr .r3, 240⟩ : Region).Disjoint ⟨s.gpr .r6, 16 * (s.gpr .r7).toNat⟩)
    (hcd : (⟨s.gpr .r5, 16⟩ : Region).Disjoint ⟨s.gpr .r6, 16 * (s.gpr .r7).toNat⟩)
    (hsize : 16 * (s.gpr .r7).toNat ≤ 2 ^ 64)
    (hnr : (s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14) :
    WP isa Impl.Aes.PPC64LE.Crypto.ctr32 s fun t => Keep ctrGprs s t ∧
      Spec.Gcm.blocksAt t.mem (s.gpr .r6) (s.gpr .r7).toNat =
        Spec.Gcm.ctr32 (Spec.Gcm.aesWith (s.gpr .r4).toNat
          (Spec.Aes.bytesAt s.mem (s.gpr .r3) (16 * ((s.gpr .r4).toNat + 1))))
          (Spec.Gcm.blockAt s.mem (s.gpr .r5)) (Spec.Gcm.blocksAt s.mem (s.gpr .r6) (s.gpr .r7).toNat) ∧
      Spec.Gcm.blockAt t.mem (s.gpr .r5) =
        Nat.repeat Spec.Gcm.inc32 (s.gpr .r7).toNat (Spec.Gcm.blockAt s.mem (s.gpr .r5)) := by
  let n := (s.gpr .r7).toNat
  let nr := (s.gpr .r4).toNat
  let D := s.gpr .r6
  let E := s.gpr .r6
  let C := s.gpr .r5
  let icb := Spec.Gcm.blockAt s.mem C
  have hnrlt : nr < 15 := by rcases hnr with h | h | h <;> omega
  have hnrmin : 1 < nr := by rcases hnr with h | h | h <;> omega
  rw [Impl.Aes.PPC64LE.Crypto.ctr32]
  by_cases hz : s.gpr .r7 = 0
  · refine WP.ite true (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hz]; rfl)
      (fun _ => WP.block_nil ?_) (by simp)
    refine ⟨Keep.refl _ _, ?_⟩
    simp only [hz, show (0 : BitVec 64).toNat = 0 from rfl, Spec.Gcm.blocksAt, List.range_zero, List.map_nil,
      Spec.Gcm.ctr32, Spec.Gcm.keystream, List.length_nil, List.zipWith_nil_left, Nat.repeat, and_self]
  · refine WP.ite false (by simpa only [eval, State.read, Size.bits, BitVec.setWidth_eq,
        Option.some.injEq, beq_eq_false_iff_ne] using hz) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (ctr_setup_ok s (List.mem_append_right _ hC)) fun base hb => ?_)
    have e := hb.effects
    have hc : LoopConfig false true .r0 base nr n D E := by
      refine ⟨⟨hb.zero, hb.mask, ?_, hnrmin, hnrlt, ?_⟩, hsize, ?_, ?_, fun _ => rfl, ?_,
        by rw [hb.zero, BitVec.sub_self]; rfl, by decide, .inl rfl⟩
      · rw [e.keep.gpr (by decide)]
        simp only [nr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · intro j hj
        rw [e.keep.2.1, e.keep.2.2, e.keep.gpr (by decide)]
        exact ⟨_, hK, Offset.contains_base _ (d := 16*j) (n := 16) (k := 240) (by omega_using [hnrlt, hj]) (by omega_using [hnrlt, hj])⟩
      · rw [e.keep.2.2]; exact hw
      · rw [e.keep.gpr (by decide)]; exact hsep
      · rw [e.keep.2.1, e.keep.2.2]; exact hr
    have hi : LoopInv false true base nr n D E icb 0 base := by
      refine ⟨by omega_using [], Keep.refl _ _, ?_, ?_, Processed.refl _ _ _ _, Frame.refl _ _, hb.mask,
        fun _ => hb.control, ?_⟩
      · rw [e.keep.gpr (by decide)]
        simp only [Nat.mul_zero, BitVec.add_zero]; rfl
      · rw [e.keep.gpr (by decide)]
        simp only [Nat.sub_zero, n, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · intro _; rw [hb.baseValue, ctrAdd_zero]
    refine WP.seq (WP.mono (batches_ok hc hi) fun u hu => ?_)
    have hC5 : u.gpr .r5 = C := (hu.keep.gpr (by decide)).trans (e.keep.gpr (by decide))
    -- the counter block, `n` further on, stored back
    have hwv : InRegions u.wr (u.gpr .r5) 16 := by
      rw [hu.keep.2.2, e.keep.2.2, hC5]
      exact ⟨⟨C, 16⟩, hC, Region.contains_self _ _⟩
    refine WP.mono (store_ok counterBase .r5 u (by decide) ((hu.keep.gpr (by decide)).trans hb.zero) hu.mask hwv)
      fun t ht => ?_
    subst t
    have hf : Frame [⟨C, 16⟩] u.mem (u.mem.write C 16 (rev128 (u.vpr counterBase))) :=
      (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hp := hu.processed.frame hf (by simpa only [List.mem_singleton, forall_eq] using hcd.symm) hsize
    have hbm : base.mem = s.mem := e.mem
    have hsched : schedule nr base = schedule nr s := by
      rw [schedule, hbm, e.keep.gpr (by decide)]
    rw [hsched, hbm] at hp
    refine ⟨(e.keep.trans hu.keep).mono (by simp [ctrGprs, loopGprs]), ?_, ?_⟩
    · show Spec.Gcm.blocksAt (u.mem.write (u.gpr .r5) 16 (rev128 (u.vpr counterBase))) E n = _
      rw [hC5]
      exact ctr_processed hp
    · show Spec.Gcm.blockAt (u.mem.write (u.gpr .r5) 16 (rev128 (u.vpr counterBase))) C = _
      rw [hC5, ← read_blockAt, read_write_self16, rev128_rev128, hu.counter rfl, ctrAdd_repeat]

theorem ctr32_ok (s : State) (hs : Proof.Aes.ctr32PPC64LE.pre s) :
    WP isa Impl.Aes.PPC64LE.Crypto.ctr32 s fun t => Keep ctrGprs s t ∧ Proof.Aes.ctr32PPC64LE.post s t := by
  obtain ⟨hrd, hwr, _, hsep, _, hcd, _, _, hbound, hnr⟩ := hs
  exact ctr32_wp s (by rw [hrd]; simp) (by rw [hwr]; simp) (by rw [hwr]; simp)
    (by rw [hrd, hwr]; simp) hsep hcd (by omega_using [hbound]) hnr

end VG.Proof.Aes.PPC64LE.Crypto
