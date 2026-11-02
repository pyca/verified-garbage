module

import VerifiedGarbage.Proof.MillerRabin.Arm.Run
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.MillerRabin.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-! # The Miller–Rabin round on ARMv7 is verified

Against its own contract (`round_verified_lite`), which implies the shared
one (`round_implies`, `round_verified`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Impl.MillerRabin.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt)

/-- A four-limb prepared working space for the candidate 3. -/
def satWord (i : Nat) : BitVec 64 :=
  if i = 6 then 4 else if i = 7 then 0x5555555555555555 else
    if 8 ≤ i ∧ i < 16 then BitVec.ofNat 64 (0x1100 + 48 * (i - 8)) else
    if i = 28 then 48 else if i = 32 then 3 else if i = 62 then 2 else
    if i = 86 then 1 else if i = 92 then 2 else if i = 194 then 1 else if i = 198 then 2 else 0

def satMem : Mem := fun x =>
  let i := (x - 0x1000).toNat
  if i < 2048 then (satWord (i / 8)).extractLsb' (8 * (i % 8)) 8 else 0

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 256 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem := satMem
  rd := []
  wr := [⟨0x1000, 2048⟩]

theorem sat_layout : Proof.MillerRabin.Round.Layout Proof.MillerRabin.Round.compact satMem 0x1000 256 := by
  simp only [Proof.MillerRabin.Round.Layout, Proof.MillerRabin.Round.compact, Proof.Rsa.Mont.Layout,
    Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
  decide +kernel

theorem sat_prepared : Proof.MillerRabin.Round.Prepared Proof.MillerRabin.Round.compact satMem 0x1000 := by
  have hw : wOf satMem 0x1000 = 4 := by decide +kernel
  have hc : numAt satMem 0x1000 4 0 = 3 := by decide +kernel
  have h5 : numAt satMem 0x1000 4 5 = 2 := by decide +kernel
  have h9 : numAt satMem 0x1000 4 9 = 1 := by decide +kernel
  have h10 : numAt satMem 0x1000 4 10 = 2 := by decide +kernel
  have h27 : numAt satMem 0x1000 4 27 = 1 := by decide +kernel
  simp only [Proof.MillerRabin.Round.Prepared, Proof.MillerRabin.Round.compact, hw, hc, h5, h9, h10, h27]
  decide +kernel

theorem round_implies : roundContract.Implies
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 56) where
  pre := by
    intro s h
    sig_pre [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, abi, argRegs, reduceClassify, Loc.val,
      State.addr] at h
    obtain ⟨spLo, _, rd, wr, disj, fit, lay, prep⟩ := h
    obtain ⟨_, mont, w4, w128, fits, _⟩ := lay
    have fits' : arrAt (wOf s.mem (State.addr (s.gpr .r0))) 28 ≤ 8 * (s.gpr .r1).toNat := fits
    refine ⟨rd, by rw [wr]; simp [State.addr, Nat.mul_comm], by omega_arith, spLo, ?_, ⟨mont, w4, w128, ?_⟩, ?_⟩
    · show (⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ : Region).Disjoint _
      rw [FrameStack.addr_sub' spLo]
      simpa [State.addr, Nat.mul_comm] using disj
    · have : arrAt (wOf s.mem (State.addr (s.gpr .r0))) nArr ≤ arrAt (wOf s.mem (State.addr (s.gpr .r0))) 28 := by
        simp only [arrAt, nArr]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by decide)) _
      exact Nat.le_trans this fits'
    · exact prep
  post := by
    intro s t _ h
    sig_post [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, abi, argRegs, reduceClassify, Loc.val,
      State.addr]
    obtain ⟨hr, hk⟩ := h
    refine ⟨fun b hb => ?_, fun i hi hfl harr htab => hk i hi (fun k hk' => hfl k ?_) (fun j hj => ?_)⟩
    · rw [BitVec.setWidth_append_eq_right]; exact hr b hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk' ⊢
      simp only [Proof.MillerRabin.Round.compact]
      omega_arith
    · have ht : i < arrAt (wOf s.mem (State.addr (s.gpr .r0))) 11 ∨
          arrAt (wOf s.mem (State.addr (s.gpr .r0))) 27 ≤ i := htab
      by_cases hs : j ∈ [2, 3, 5, 6, 8]
      · exact harr j (by simpa only [Proof.MillerRabin.Round.compact] using hs)
      · have hj' : 11 ≤ j ∧ j ≤ 26 := by
          simp only [wJs, aX, aY, aM1, List.mem_cons, List.not_mem_nil, or_false] at hj hs; omega_arith
        generalize wOf s.mem (State.addr (s.gpr .r0)) = w at ht ⊢
        have a := Nat.mul_le_mul_right (8 * (w + 2)) hj'.1
        have b := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ 27 by omega_arith)
        rw [Nat.add_mul, Nat.one_mul] at b
        simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at ht ⊢
        generalize 8 * (w + 2) = S at *
        omega_arith
  pub := by
    rintro s t - - h
    sig_pub [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, abi, argRegs, reduceClassify, Loc.val,
      State.addr] at h
    obtain ⟨sp, hw, h0, h1⟩ := h
    exact ⟨sp, h0, h1, List.singleton_inj.mp hw⟩
  sat := by
    refine ⟨satState, ?_⟩
    sig_pre [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, abi, argRegs, reduceClassify, Loc.val,
      State.addr]
    exact ⟨by decide, by decide, by decide, Region.disjoint_of_le (by decide) (by decide) (by decide), by decide,
      sat_layout, sat_prepared⟩

theorem round_correct (s : State) (h : roundContract.pre s) (fios : Bool := false) :
    ∃ tr t, Exec isa (code (fios := fios)) s tr t ∧ abiPreserved s t ∧ roundContract.post s t :=
  round_ok (fios := fios) h

theorem round_ct' (fios : Bool := false) : ConstantTime isa roundContract.pre roundContract.pub (code (fios := fios)) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨sp, h0, h1, hw⟩ := hp
  have hP : mkP s = mkP t := by
    simp only [mkP]; rw [sp, h1, hw, h0]
  exact (round_ct (fios := fios) s t tr1 tr2 u v ⟨hs, ht, sp, hP⟩ e1 e2).1

/-- `vg_miller_rabin_round` against the contract its callers use. -/
theorem round_verified_lite (fios : Bool := false) : Verified Arm.target (code (fios := fios)) roundContract :=
  ⟨(round_correct (fios := fios)), (round_ct' (fios := fios)), round_implies.sat_left⟩

/-- `vg_miller_rabin_round`. -/
theorem round_verified (fios : Bool := false) : Verified Arm.target (code (fios := fios))
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 56) :=
  (round_verified_lite (fios := fios)).of_implies round_implies

end VG.Proof.MillerRabin.Arm
