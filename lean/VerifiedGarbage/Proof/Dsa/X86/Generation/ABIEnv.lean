module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ABI
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Env
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ABIEntry
import VerifiedGarbage.Proof.Framework.Offset

/-! # The precondition gives a valid environment -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

/-- The environment of a call, from its arguments: the seeds and the `h`
candidates are those of each seed's own environment (`Env.atSeed`,
`Env.window`). -/
def callEnv (s : State) : Env where
  pLen := pLenOf s
  qLen := Spec.Dsa.generationQLen (pLenOf s)
  base := (arg s 5).setWidth 64
  size := (arg s 6).toNat * 8
  out := (arg s 0).setWidth 64
  usedP := (arg s 2).setWidth 64
  stP := (arg s 7).setWidth 64
  k0 := (s.mem.readW ((arg s 7).setWidth 64) 64).toNat
  seedsOff := 0
  seedsLen := 0
  hsOff := 0
  hsLen := 0
  wit := (arg s 3).setWidth 64
  witLen := (arg s 4).toNat
  sp := s.gpr .esp - BitVec.ofNat 32 16
  table := (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64
  witT := Spec.Rsa.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat

theorem disjoint_nat {a b : Addr} {n k : Nat}
    (_an : a.toNat + n ≤ 2 ^ 64) (_bk : b.toNat + k ≤ 2 ^ 64) (np : 0 < n) (kp : 0 < k)
    (D : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat := by
  by_contra bad
  have overlap : a.toNat < b.toNat + k ∧ b.toNat < a.toNat + n := by omega
  by_cases order : a.toNat ≤ b.toNat
  · apply D b
    · change (b - a).toNat + 1 ≤ n
      rw [BitVec.toNat_sub]
      omega
    · change (b - b).toNat + 1 ≤ k
      rw [BitVec.sub_self]; change 0 + 1 ≤ k; omega
  · apply D a
    · change (a - a).toNat + 1 ≤ n
      rw [BitVec.sub_self]; change 0 + 1 ≤ n; omega
    · change (a - b).toNat + 1 ≤ k
      rw [BitVec.toNat_sub]
      omega

theorem CallFacts.tableRegion {s : State} (F : CallFacts s) :
    let t : Region := ⟨(s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64, 8192⟩
    t.base.toNat + 8192 ≤ 2 ^ 32 ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
      t.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ∧ t.Disjoint (reservedRegion s) :=
  F.tableFar _ (by rw [ProbablePrime.table_regions]; exact List.mem_cons_self)

theorem CallFacts.rd {s : State} (F : CallFacts s) :
    s.rd = [⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩, (callEnv s).tableRegion] := by
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, F.rdPrefix, F.rdTable, ProbablePrime.table_regions]
  rfl

theorem CallFacts.pLens {s : State} (F : CallFacts s) : pLenOf s = 128 ∨ pLenOf s = 256 ∨ pLenOf s = 384 := by
  have := F.pValid
  simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at this
  omega

theorem CallFacts.lengths {s : State} (F : CallFacts s) :
    Spec.Dsa.generationLengthsValid (pLenOf s) (Spec.Dsa.generationQLen (pLenOf s)) := by
  rcases F.pLens with h | h | h <;> simp [Spec.Dsa.generationLengthsValid, Spec.Dsa.generationQLen, h]

theorem CallFacts.reserved {s : State} (F : CallFacts s) : reservedRegion s = below (s.gpr .esp) 216 := by
  unfold reservedRegion below
  rw [Taint.sub_setWidth F.low]

theorem CallFacts.stackSub {s : State} (F : CallFacts s) : (callEnv s).stackRegion.Sub (reservedRegion s) := by
  rw [F.reserved]
  exact below_inner (by decide) F.low

theorem CallFacts.spNat {s : State} (F : CallFacts s) : (callEnv s).sp.toNat = (s.gpr .esp).toNat - 16 :=
  sub_toNat (by have := F.low; omega)

theorem CallFacts.reservedNat {s : State} (F : CallFacts s) :
    ((s.gpr .esp).setWidth 64 - 216#64).toNat = (s.gpr .esp).toNat - 216 := by
  change (reservedRegion s).base.toNat = _
  rw [F.reserved]
  change ((s.gpr .esp - BitVec.ofNat 32 216).setWidth 64).toNat = _
  rw [toNat_wide, sub_toNat F.low]

/-- `scratch` lies below the reserved stack or above the return address. -/
theorem CallFacts.scratchNat {s : State} (F : CallFacts s) :
    (arg s 5).toNat + (arg s 6).toNat * 8 ≤ (s.gpr .esp).toNat - 216 ∨
      (s.gpr .esp).toNat + 4 ≤ (arg s 5).toNat := by
  have room := F.room
  unfold Spec.Dsa.generationScratchWords at room
  have fit := F.scrFit
  have esp := (s.gpr .esp).isLt
  have low := F.low
  have b₁ := disjoint_nat (by rw [toNat_wide]; omega) (by rw [F.reservedNat]; omega) (by omega) (by decide)
    F.stackScr.symm
  have b₂ := disjoint_nat (by rw [toNat_wide]; omega) (by rw [toNat_wide]; omega) (by omega) (by decide)
    F.retScr.symm
  rw [toNat_wide, F.reservedNat] at b₁
  rw [toNat_wide, toNat_wide] at b₂
  omega

/-- `out` lies below the reserved stack or above the return address. -/
theorem CallFacts.outNat {s : State} (F : CallFacts s) :
    (arg s 0).toNat + (arg s 1).toNat ≤ (s.gpr .esp).toNat - 216 ∨
      (s.gpr .esp).toNat + 4 ≤ (arg s 0).toNat := by
  have pos : 0 < (arg s 1).toNat := by
    rw [F.outLen]; rcases F.pLens with h | h | h <;> omega
  have fit := F.outFit
  have esp := (s.gpr .esp).isLt
  have low := F.low
  have b₁ := disjoint_nat (by rw [toNat_wide]; omega) (by rw [F.reservedNat]; omega) pos (by decide)
    F.stackOut.symm
  have b₂ := disjoint_nat (by rw [toNat_wide]; omega) (by rw [toNat_wide]; omega) pos (by decide)
    F.retOut.symm
  rw [toNat_wide, F.reservedNat] at b₁
  rw [toNat_wide, toNat_wide] at b₂
  omega

/-- `state` lies below the reserved stack or above the return address. -/
theorem CallFacts.stNat {s : State} (F : CallFacts s) :
    (arg s 7).toNat + 32 ≤ (s.gpr .esp).toNat - 216 ∨ (s.gpr .esp).toNat + 4 ≤ (arg s 7).toNat := by
  have fit := F.stFit
  have esp := (s.gpr .esp).isLt
  have low := F.low
  have b₁ := disjoint_nat (by rw [toNat_wide]; omega) (by rw [F.reservedNat]; omega) (by decide) (by decide)
    F.stackSt.symm
  have b₂ := disjoint_nat (by rw [toNat_wide]; omega) (by rw [toNat_wide]; omega) (by decide) (by decide)
    F.retSt.symm
  rw [toNat_wide, F.reservedNat] at b₁
  rw [toNat_wide, toNat_wide] at b₂
  omega

/-- `used` lies below the reserved stack or above the return address. -/
theorem CallFacts.usedNat {s : State} (F : CallFacts s) :
    (arg s 2).toNat + 8 ≤ (s.gpr .esp).toNat - 216 ∨ (s.gpr .esp).toNat + 4 ≤ (arg s 2).toNat := by
  have fit := F.usedFit
  have esp := (s.gpr .esp).isLt
  have low := F.low
  have b₁ := disjoint_nat (by rw [toNat_wide]; omega) (by rw [F.reservedNat]; omega) (by decide) (by decide)
    F.stackUsed.symm
  have b₂ := disjoint_nat (by rw [toNat_wide]; omega) (by rw [toNat_wide]; omega) (by decide) (by decide)
    F.retUsed.symm
  rw [toNat_wide, F.reservedNat] at b₁
  rw [toNat_wide, toNat_wide] at b₂
  omega

theorem CallFacts.outLenEq {s : State} (F : CallFacts s) : (callEnv s).outLen = (arg s 1).toNat := by
  simp only [Env.outLen, callEnv, F.outLen]

theorem CallFacts.outRegion {s : State} (F : CallFacts s) :
    (callEnv s).outRegion = ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ := by
  simp only [Env.outRegion, F.outLenEq]; rfl

/-- A region of the arguments' memory, apart from the stack the calls use. -/
theorem CallFacts.far {s : State} (F : CallFacts s) {r : Region} (h : (reservedRegion s).Disjoint r) :
    r.Disjoint (callEnv s).stackRegion := h.symm.sub_right F.stackSub

theorem CallFacts.valid {s : State} (F : CallFacts s) : (callEnv s).Valid := by
  have room := F.room
  unfold Spec.Dsa.generationScratchWords at room
  have T := F.tableRegion
  have scratchNat := F.scratchNat
  have spNat := F.spNat
  have low := F.low
  have ws : (callEnv s).scratchRegion = ⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩ := rfl
  have wW : (callEnv s).witRegion = ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩ := rfl
  have uR : (callEnv s).usedRegion = ⟨(arg s 2).setWidth 64, 8⟩ := rfl
  have sR : (callEnv s).stRegion = ⟨(arg s 7).setWidth 64, 32⟩ := rfl
  have tW : ∀ r ∈ s.wr, (callEnv s).tableRegion.Disjoint r := T.2.1
  refine ⟨F.lengths, by change 512 * pLenOf s + 8192 ≤ (arg s 6).toNat * 8; omega,
    by change ((arg s 5).setWidth 64).toNat + _ ≤ _; rw [toNat_wide]; exact F.scrFit,
    by rw [F.outLenEq]; change ((arg s 0).setWidth 64).toNat + _ ≤ _; rw [toNat_wide]; exact F.outFit,
    by change ((arg s 3).setWidth 64).toNat + _ ≤ _; rw [toNat_wide]; exact F.randFit,
    by simp [callEnv], by simp [callEnv], by rw [spNat]; omega, ?_, by rw [ws, F.outRegion]; exact F.outScr,
    ⟨by rw [wW, ws]; exact F.randScr, by rw [wW, F.outRegion]; exact F.outRand.symm,
      by rw [wW]; exact F.far F.stackRand⟩,
    by rw [F.outRegion]; exact F.far F.stackOut,
    by rw [ws]; exact F.far F.stackScr, T.1, (toNat_wide _).symm ▸ (arg s 0).isLt,
    (toNat_wide _).symm ▸ (arg s 3).isLt, (arg s 4).isLt, ⟨T.2.1 _ ?_, ?_, T.2.2.2.sub_right F.stackSub⟩, ?_,
    by change ((arg s 2).setWidth 64).toNat + 8 ≤ _; rw [toNat_wide]; exact F.usedFit,
    by change ((arg s 7).setWidth 64).toNat + 32 ≤ _; rw [toNat_wide]; exact F.stFit, ?_, ?_, F.seeds⟩
  · change (callEnv s).sp.toNat ≤ ((arg s 5).setWidth 64).toNat ∨
      ((arg s 5).setWidth 64).toNat + (arg s 6).toNat * 8 + 200 ≤ (callEnv s).sp.toNat
    rw [spNat, toNat_wide]
    omega
  · rw [F.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rw [F.outRegion]; exact T.2.1 _ (by rw [F.wr]; exact List.mem_cons_self)
  · exact F.tableAligned _ (by rw [ProbablePrime.table_regions]; exact List.mem_cons_self)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [uR, ws]; exact F.usedScr
    · rw [uR, F.outRegion]; exact F.outUsed.symm
    · rw [uR]; exact F.far F.stackUsed
    · rw [uR, sR]; exact F.usedSt
    · rw [uR, wW]; exact F.usedRand
    · exact (tW _ (by rw [F.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self)).symm
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [sR, ws]; exact F.scrSt.symm
    · rw [sR, F.outRegion]; exact F.outSt.symm
    · rw [sR]; exact F.far F.stackSt
    · rw [sR, wW]; exact F.randSt.symm
    · exact (tW _ (by rw [F.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))).symm

end VG.Proof.Dsa.X86.Generation
