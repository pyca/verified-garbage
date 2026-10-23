module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ABI
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Env
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ABIEntry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The precondition gives a valid environment -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

/-- The environment of a call, from its arguments. -/
def callEnv (s : State) : Env where
  pLen := (arg s 2).toNat
  qLen := (arg s 3).toNat
  base := (arg s 10).setWidth 64
  size := (arg s 11).toNat * 8
  out := (arg s 0).setWidth 64
  seeds := (arg s 4).setWidth 64
  seedsLen := (arg s 5).toNat
  hs := (arg s 6).setWidth 64
  hsLen := (arg s 7).toNat
  wit := (arg s 8).setWidth 64
  witLen := (arg s 9).toNat
  sp := s.gpr .esp - BitVec.ofNat 32 16
  table := (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64
  seedT := Spec.Rsa.bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat
  hT := Spec.Rsa.bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat
  witT := Spec.Rsa.bytesAt s.mem ((arg s 8).setWidth 64) (arg s 9).toNat

theorem toNat_wide (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

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
    s.rd = [⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩, ⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩,
      ⟨(arg s 8).setWidth 64, (arg s 9).toNat⟩, (callEnv s).tableRegion] := by
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, F.rdPrefix, F.rdTable, ProbablePrime.table_regions]
  rfl

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
    (arg s 10).toNat + (arg s 11).toNat * 8 ≤ (s.gpr .esp).toNat - 216 ∨
      (s.gpr .esp).toNat + 4 ≤ (arg s 10).toNat := by
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
    rw [F.outLen]; rcases F.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
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

theorem CallFacts.outLenEq {s : State} (F : CallFacts s) : (callEnv s).outLen = (arg s 1).toNat := by
  simp only [Env.outLen, callEnv, F.outLen]

theorem CallFacts.outRegion {s : State} (F : CallFacts s) :
    (callEnv s).outRegion = ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ := by
  simp only [Env.outRegion, F.outLenEq]; rfl

theorem CallFacts.valid {s : State} (F : CallFacts s) : (callEnv s).Valid := by
  have room := F.room
  unfold Spec.Dsa.generationScratchWords at room
  have T := F.tableRegion
  have scratchNat := F.scratchNat
  have spNat := F.spNat
  have low := F.low
  have ws : (callEnv s).scratchRegion = ⟨(arg s 10).setWidth 64, (arg s 11).toNat * 8⟩ := rfl
  have tapes : ∀ r ∈ [(callEnv s).seedsRegion, (callEnv s).hsRegion, (callEnv s).witRegion],
      r.Disjoint (callEnv s).scratchRegion ∧ r.Disjoint (callEnv s).outRegion ∧ r.Disjoint (reservedRegion s) := by
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rw [ws, F.outRegion]
    rcases mem with rfl | rfl | rfl
    · exact ⟨F.seedsScr, F.outSeeds.symm, F.stackSeeds.symm⟩
    · exact ⟨F.hsScr, F.outHs.symm, F.stackHs.symm⟩
    · exact ⟨F.witScr, F.outWit.symm, F.stackWit.symm⟩
  refine ⟨F.lengths, by change 512 * (arg s 2).toNat + 8192 ≤ (arg s 11).toNat * 8; omega,
    by change ((arg s 10).setWidth 64).toNat + _ ≤ _; rw [toNat_wide]; exact F.scrFit,
    by rw [F.outLenEq]; change ((arg s 0).setWidth 64).toNat + _ ≤ _; rw [toNat_wide]; exact F.outFit,
    by change ((arg s 4).setWidth 64).toNat + _ ≤ _; rw [toNat_wide]; exact F.seedsFit,
    by change ((arg s 6).setWidth 64).toNat + _ ≤ _; rw [toNat_wide]; exact F.hsFit,
    by change ((arg s 8).setWidth 64).toNat + _ ≤ _; rw [toNat_wide]; exact F.witFit,
    F.seedsWhole, F.hsWhole, by rw [spNat]; omega, ?_, by rw [ws, F.outRegion]; exact F.outScr,
    fun r mem => ⟨(tapes r mem).1, (tapes r mem).2.1, (tapes r mem).2.2.sub_right F.stackSub⟩,
    by rw [F.outRegion]; exact F.stackOut.symm.sub_right F.stackSub,
    by rw [ws]; exact F.stackScr.symm.sub_right F.stackSub, ?_, ?_, ?_, ?_⟩
  · change (callEnv s).sp.toNat ≤ ((arg s 10).setWidth 64).toNat ∨
      ((arg s 10).setWidth 64).toNat + (arg s 11).toNat * 8 + 200 ≤ (callEnv s).sp.toNat
    rw [spNat, toNat_wide]
    omega
  · have := T.1
    exact this
  · refine ⟨?_, ?_, ?_, ?_⟩ <;>
      first
      | exact Nat.lt_of_lt_of_eq (arg s _).isLt (toNat_wide _).symm
      | exact (toNat_wide _).symm ▸ (arg s _).isLt
  · exact ⟨(arg s 5).isLt, (arg s 7).isLt, (arg s 9).isLt⟩
  · refine ⟨T.2.1 _ ?_, ?_, ?_⟩
    · rw [F.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [F.outRegion]; exact T.2.1 _ (by rw [F.wr]; exact List.mem_cons_self)
    · exact T.2.2.2.sub_right F.stackSub

end VG.Proof.Dsa.X86.Generation
