module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateTest
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrepareInput
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2Timing
import VerifiedGarbage.Proof.RsaKeyGen.X86.ConstantsTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2
import VerifiedGarbage.Impl.RsaKeyGen.X86.LowPair
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Impl.RsaKeyGen.X86.LowBit
import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentMarker
import VerifiedGarbage.Impl.RsaKeyGen.X86.SigMask
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentShift
public import VerifiedGarbage.Impl.RsaKeyGen.X86.HalfPass
import VerifiedGarbage.Impl.RsaKeyGen.X86.Exponent
import VerifiedGarbage.Impl.RsaKeyGen.X86.Prepare
public import VerifiedGarbage.Impl.RsaKeyGen.X86.PrepareHeader
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
public import VerifiedGarbage.Proof.RsaKeyGen.CandLeak
public import VerifiedGarbage.Impl.RsaKeyGen.X86.MillerRabinLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinInit
import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessChecks
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinStep
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessAvailable
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessStep
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessAdvance
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessRound
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedDataGap
import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessMont
import VerifiedGarbage.Proof.MillerRabin.X86.TimingMultiply
import VerifiedGarbage.Proof.MillerRabin.X86.TimingCopy
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.CallReturn
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFrame
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessCount
import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessStatus
public import VerifiedGarbage.Impl.RsaKeyGen.X86.HeaderRt
import VerifiedGarbage.Impl.RsaKeyGen.X86.Header
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Impl.RsaKeyGen.X86.MontInverse
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessLoad
import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessLower
import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessUniform
import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessFallback
import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessSample
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ImportEntry
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Import

/-! ### `RsaKeyGen.X86.WitnessLoadTiming`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.ImportTiming`, which this module and modules that import it used -/

section

/-! # The import's address trace depends only on pointers and the public word count -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Import
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Import

def publicState : VG.X86.Taint.T := τr [.esp, .edi, .esi, .ebx, .ecx]

theorem code_trace : RelCT isa (VG.X86.Taint.Agree publicState) code (VG.X86.Taint.Agree publicState) :=
  checkedProgramChange (τ' := { publicState with flags := true })
    (hint := VG.Taint.hintOf taint publicState code) (by kernel_rfl) (by kernel_rfl)

end VG.Proof.RsaKeyGen.X86.Import

end

end

/-! ### `RsaKeyGen.X86.ImportLoadTiming`, which this module and modules that import it used -/

section

/-! # Complete native import timing depends only on public input and workspace pointers -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Import
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Import

theorem args_trace (count out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .esi])) (.block (args count out))
      (VG.X86.Taint.Agree publicState) :=
  erased_relCT (.block (args count out)) (.block (args 0 0)) (.block [])
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem load_trace (count out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .esi])) (load count out)
      (VG.X86.Taint.Agree publicState) :=
  RelCT.seq (args_trace count out) code_trace

end VG.Proof.RsaKeyGen.X86.Import

end

end

/-! # Import and sampling reveal the entropy pointer and width, but no random bytes -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/WitnessLowerTiming.lean`, which only this module imported.
section

/-! # The witness lower-bound scan has fixed public length and addresses -/

section
namespace VG.Proof.RsaKeyGen.X86.WitnessLower
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.WitnessLower

theorem code_trace (n src : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (code n src)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (code n src) (code 2 0)
    (VG.Taint.hintOf taint (roundTaint [.edi]) (Code.erase (code 2 0)))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.WitnessLower
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/WitnessUniformTiming.lean`, which only this module imported.
section

/-! # Uniform-witness classification scans the same addresses for every input -/

section
namespace VG.Proof.RsaKeyGen.X86.WitnessUniform
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.WitnessUniform

theorem mark_trace (src : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (VG.Impl.RsaKeyGen.X86.WitnessOdd.mark src))
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (.block (VG.Impl.RsaKeyGen.X86.WitnessOdd.mark src))
    (.block (VG.Impl.RsaKeyGen.X86.WitnessOdd.mark 0)) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem restore_trace (src : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (VG.Impl.RsaKeyGen.X86.WitnessOdd.restore src))
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (.block (VG.Impl.RsaKeyGen.X86.WitnessOdd.restore src))
    (.block (VG.Impl.RsaKeyGen.X86.WitnessOdd.restore 0)) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem less_trace (w src modulus : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (VG.Impl.Dsa.X86.lessThan w src modulus)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (VG.Impl.Dsa.X86.lessThan w src modulus) (VG.Impl.Dsa.X86.lessThan 1 0 0)
    (.seq (roundTaint [.edi]) (.block [])
      (.seq (roundTaint [.edi])
        (.seq (roundTaint [.edi, .ebp]) (.block []) (.loop (roundTaint [.edi, .ebp]) (.block []))) (.block [])))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem code_trace (w src modulus : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (code w src modulus)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq (WitnessLower.code_trace (2 * w) src) (RelCT.seq (mark_trace src)
    (RelCT.seq (less_trace w src modulus) (RelCT.seq (restore_trace src) (checkedBlockInvariant rfl rfl))))

end VG.Proof.RsaKeyGen.X86.WitnessUniform
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/WitnessFallbackTiming.lean`, which only this module imported.
section

/-! # Both fallback choices execute identical native updates -/

section
namespace VG.Proof.RsaKeyGen.X86.WitnessFallback
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.WitnessFallback

theorem codeAt_trace (k src : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (codeAt k src))
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (.block (codeAt k src)) (.block (codeAt 2 0)) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.WitnessFallback
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/WitnessSampleTiming.lean`, which only this module imported.
section

/-! # Complete witness sampling has a secret-independent trace -/

section
namespace VG.Proof.RsaKeyGen.X86.WitnessSample
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.WitnessSample

theorem codeAt_trace (k w src modulus : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (codeAt k w src modulus)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq (WitnessUniform.code_trace w src modulus) (WitnessFallback.codeAt_trace k src)

end VG.Proof.RsaKeyGen.X86.WitnessSample
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessLoad
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86 VG.Proof.Dsa.X86

theorem zeros_trace (o n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (VG.Impl.RsaKeyGen.X86.WitnessLoad.zeros o n))
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessLoad.zeros
  apply blockFlatMap_relCT
  intro j
  exact erased_relCT _ (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc 0) .eax])
    (.block []) rfl rfl rfl rfl

theorem codeAt_trace (D k w : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi, .esi])) (VG.Impl.RsaKeyGen.X86.WitnessLoad.codeAt D k w)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessLoad.codeAt VG.Impl.RsaKeyGen.X86.WitnessLoad.zeroTail
  refine RelCT.seq (Import.load_trace (D / 4) (VG.Impl.Bignum.X86.PublicContext.slot w 6)) ?_
  exact RelCT.seq ((zeros_trace _ _).mono (fun _ _ H => taint.le_sound (by decide +kernel) H) (fun _ _ H => H))
    (WitnessSample.codeAt_trace _ w _ _)

end VG.Proof.RsaKeyGen.X86.WitnessLoad

end

end

/-! ### `RsaKeyGen.X86.PrepareHeaderTiming`, which this module and modules that import it used -/

section

/-! # Header and inverse preparation have a candidate-independent trace -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/HeaderTiming.lean`, which only this module imported.
section

/-! # Prepared metadata initialization has no secret-dependent address -/

section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Header

theorem code_trace (w : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (code w))
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  erased_relCT (.block (code w)) (.block (code 0)) (.block [])
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.Header
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/MontInverseTiming.lean`, which only this module imported.
section

/-! # Full inverse setup uses a fixed native multiplication schedule -/

section
namespace VG.Proof.RsaKeyGen.X86.MontInverse
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.MontInverse

theorem code_trace (modulus inverse : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (code modulus inverse)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (code modulus inverse) (code 0 0)
    (.seq (roundTaint [.edi]) (.block []) (.block [])) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.MontInverse
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PrepareHeader
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.PrepareHeader

theorem code_trace (w : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (code w)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq (Header.code_trace w) (MontInverse.code_trace (VG.Impl.Bignum.X86.PublicContext.slot w 0) 56)

theorem prepareRt_trace :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) VG.Impl.RsaKeyGen.X86.HeaderRt.prepare
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq (VG.Proof.Dsa.X86.erased_relCT _ (.block VG.Impl.RsaKeyGen.X86.HeaderRt.code) (.block [])
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)) (MontInverse.code_trace 256 56)

end VG.Proof.RsaKeyGen.X86.PrepareHeader

end

end

/-! ### `RsaKeyGen.X86.MillerRabinTiming`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.MillerRabinTimingStep`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.MillerRabinTimingState`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.WitnessStepTiming`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.WitnessCountTiming`, which this module and modules that import it used -/

section

/-! # Counting uniform samples and choosing status use no secret branch -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/WitnessStatusTiming.lean`, which only this module imported.
section

/-! # Masked witness-count status does not reveal the test or sampling result -/

section
namespace VG.Proof.RsaKeyGen.X86.WitnessStatus
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

theorem code_trace : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block VG.Impl.RsaKeyGen.X86.WitnessStatus.code) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  checkedBlockInvariant rfl rfl

end VG.Proof.RsaKeyGen.X86.WitnessStatus
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessCount
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.WitnessCount

theorem next_trace : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block next) (VG.X86.Taint.Agree (roundTaint [.edi])) := checkedBlockInvariant rfl rfl

theorem store_trace : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block [.store (VG.Impl.Mont.X86.sc statusOffset) .ecx]) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  checkedBlockInvariant rfl rfl

theorem code_trace : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) code
    (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq next_trace (RelCT.seq WitnessStatus.code_trace store_trace)

end VG.Proof.RsaKeyGen.X86.WitnessCount

end

end

/-! ### `RsaKeyGen.X86.WitnessRoundTiming`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.RoundTiming`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.RoundTimingPre`, which only this module used -/

section

/-! # A shared round exposes only the workspace pointer, capacity and width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.RoundCall
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.RoundCall

def Input (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c b, Prepare.Data g c capacity p s ∧ c % 2 = 1 ∧ 3 ≤ c ∧
    val32 s.mem g.W (g.array 5) g.words = b % c * 2 ^ (64 * g.w) % c

def Ready (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  Input g capacity p s ∧ Arguments g capacity s

theorem Ready.sp {g : Geometry} {capacity : Nat} {p : BitVec 32} {s : State}
    (S : Ready g capacity p s) : s.gpr .esp = p := by
  obtain ⟨c, b, D, _, _, _⟩ := S.1
  exact D.ready.caller.sp

theorem Ready.entry_eq {g : Geometry} {capacity : Nat} {p : BitVec 32} {s : State}
    (S : Ready g capacity p s) :
    (pushed args s).callEntry.withRegions [below p 8] [⟨g.W, g.L⟩] = entry g s := by
  unfold entry
  rw [callEntry_argAddr0, S.sp]
  rfl

theorem Ready.callPre {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {s : State}
    (R : Ready g capacity p s) (length : g.L = 8 * capacity)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108)) :
    CallPre (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96) args [below p 8] [⟨g.W, g.L⟩] s := by
  obtain ⟨c, b, S, odd, large, witness⟩ := R.1
  refine ⟨?_, ?_, ?_⟩
  · rw [R.entry_eq]
    exact entry_pre v length S R.2 odd large witness (by rw [R.sp]; exact fit) (by rw [R.sp]; exact far)
  · rw [← R.sp]
    apply Covers.of_mem
    intro r mem
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact List.mem_append_right _ (List.mem_cons_self ..)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ S.ready.context.ws.wr)
  · apply Covers.of_mem
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact List.mem_cons_of_mem _ S.ready.context.ws.wr

theorem Ready.width {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {s : State}
    (R : Ready g capacity p s) (fit : 108 ≤ p.toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108)) :
    Proof.Rsa.Mont.wOf (entry g s).mem g.W = g.w := by
  obtain ⟨c, b, S, _, _, _⟩ := R.1
  have F := entry_frame (by rw [R.sp]; omega_using [fit]) S.ready.scratch.nowrap
    (by rw [R.sp]; exact far.sub_right (below_sub (by decide : 12 ≤ 108) fit))
  exact (S.ready.modulus.keep v F (by simp) (by simp)).width

theorem Ready.publicInputs {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {s t : State}
    (S : Ready g capacity p s) (T : Ready g capacity p t) (fit : 108 ≤ p.toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108)) :
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).pub (entry g s) (entry g t) := by
  have sa := fun {i} (hi : i < 2) => entry_arg S.2 (by rw [S.sp]; omega_using [fit]) hi
  have ta := fun {i} (hi : i < 2) => entry_arg T.2 (by rw [T.sp]; omega_using [fit]) hi
  obtain ⟨c, b, D, _, _, _⟩ := S.1
  have bound : g.W.toNat < 2 ^ 32 := by have := D.ready.scratch.nowrap; have := v.headerFit; omega_arith
  have ptr : (BitVec.ofNat 32 g.W.toNat).setWidth 64 = g.W := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt (Nat.lt_trans bound (by decide))]
  have sp : (entry g s).gpr .esp = (entry g t).gpr .esp := by
    change (pushed args s).callEntry.gpr .esp = (pushed args t).callEntry.gpr .esp
    rw [callEntry_esp', callEntry_esp', S.sp, T.sp]
  have width : [Proof.Rsa.Mont.wOf (entry g s).mem g.W] = [Proof.Rsa.Mont.wOf (entry g t).mem g.W] := by
    rw [S.width v fit far, T.width v fit far]
  sig_pub [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, abi, argSlots, argVal, argBytes]
  simp only [sa (by decide : 0 < 2), sa (by decide : 1 < 2), ta (by decide : 0 < 2), ta (by decide : 1 < 2), ↓reduceIte, ptr]
  exact ⟨sp, width, trivial, trivial⟩

end VG.Proof.RsaKeyGen.X86.RoundCall

end

end


/-! # A callable round reveals no candidate, witness, exponent or result -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.RoundCall
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.RoundCall VG.Impl.Mont.X86

theorem call_trace {round : Prog isa} {name : String}
    (verified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (fit : 108 ≤ p.toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108)) :
    RelCT isa (fun s t => Ready g capacity p s ∧ Ready g capacity p t) (call name round) (fun _ _ => True) := by
  refine VG.X86.RelCT.callWithReturn verified.1 verified.2.1 [below p 8] [⟨g.W, g.L⟩] ?_
  intro s t ⟨S, T⟩
  refine ⟨S.callPre v length fit far, T.callPre v length fit far, S.sp.trans T.sp.symm, ?_⟩
  rw [S.entry_eq, T.entry_eq]
  exact S.publicInputs v T fit far

theorem setup_raw : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block [.mov .edx (.mem (at_ .esp 24))]) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  checkedBlockInvariant rfl rfl

theorem setup_ready {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {s : State}
    (I : Input g capacity p s) :
    WP isa (.block [.mov .edx (.mem (at_ .esp 24))]) s (Ready g capacity p) := by
  obtain ⟨c, b, S, odd, large, witness⟩ := I
  refine wp_movS S.ready.caller.readLen fun a A _ => WP.block_nil ?_
  have Da := WitnessMont.data_outside v S
    (show Outside g.W (g.array 6) (4 * g.words) s.mem a.mem from by rw [A.mem]; exact Outside.refl _ _ _ _)
    A.keeps (by decide) (by decide)
  refine ⟨⟨c, b, Da, odd, large, by rw [A.mem]; exact witness⟩, ?_, A.gpr⟩
  apply BitVec.eq_of_toNat_eq
  rw [A.other .edi (by decide), S.ready.scratch.edi_toNat, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (by have := S.ready.scratch.nowrap; have := v.headerFit; omega_arith)).symm

def InputPair (g : Geometry) (capacity : Nat) (p : BitVec 32) (s t : State) : Prop :=
  Pair g [.edi] s t ∧ Input g capacity p s ∧ Input g capacity p t

theorem code_trace {round : Prog isa} {name : String}
    (verified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (noSp : NoSp round) (stack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (fit : 108 ≤ p.toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    RelCT isa (InputPair g capacity p) (code name round) (Pair g [.edi]) := by
  have raw : RelCT isa (InputPair g capacity p) (code name round) (fun _ _ => True) := by
    unfold code
    refine RelCT.seq (Q := fun _ _ => True) ?_ (call_trace verified v length fit far)
    intro s t tr ur u z H E G
    obtain ⟨trace, _⟩ := setup_raw _ _ _ _ _ _ H.1.2.2 E G
    exact ⟨trace, wp_result (setup_ready v H.2.1) E, wp_result (setup_ready v H.2.2) G⟩
  intro s t tr ur u z H E G
  have trace := (raw _ _ _ _ _ _ H E G).1
  have post {a : State} (I : Input g capacity p a) :
      WP isa (code name round) a fun t => Context g t ∧ Keeps [.eax, .ecx, .edx] a t := by
    obtain ⟨c, b, S, odd, large, witness⟩ := I
    exact WP.mono (code_ok (b := b) verified noSp stack v length S odd large witness fit far lengthFar)
      fun _ ⟨D, _, _, _, K⟩ => ⟨D.ready.context, K⟩
  obtain ⟨Cu, Ku⟩ := wp_result (post H.2.1) E
  obtain ⟨Cz, Kz⟩ := wp_result (post H.2.2) G
  exact ⟨trace, pair_of_keeps H.1 Cu Cz Ku Kz (by decide) (by decide)⟩

end VG.Proof.RsaKeyGen.X86.RoundCall

end

end

/-! # A complete sampled witness iteration has a secret-independent trace -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/WitnessMontTiming.lean`, which only this module imported.
section

/-! # Witness conversion has a trace independent of the sampled value -/

section
namespace VG.Proof.RsaKeyGen.X86.WitnessMont
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def Input (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c, Prepare.Data g c capacity p s ∧ c % 2 = 1 ∧ 0 < c

def InputPair (g : Geometry) (capacity : Nat) (p : BitVec 32) (s t : State) : Prop :=
  Pair g [.edi] s t ∧ Input g capacity p s ∧ Input g capacity p t

theorem input_mul {g : Geometry} {capacity : Nat} {p : BitVec 32} {s : State}
    (S : Input g capacity p s) : MulInput g capacity 4 p s := by
  obtain ⟨c, A, odd, positive⟩ := S
  exact ⟨A.ready.context, ⟨c, A.ready.modulus, odd, by rw [A.r2]; exact Nat.mod_lt _ positive⟩, A.ready.caller⟩

theorem code_raw {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (InputPair g capacity p) (VG.Impl.RsaKeyGen.X86.WitnessMont.code name mont)
      (Pair g [.edi]) := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessMont.code
  refine RelCT.seq ?_ (copy_relCT v 5 6 (by decide) (by decide))
  exact (mulY_relCT (p := p) (b := 4) verified noSp stack v length
    (by unfold Proof.Rsa.Mont.Operand; decide)).mono
    (fun _ _ H => ⟨H.1, input_mul H.2.1, input_mul H.2.2⟩) (fun _ _ H => H)

end VG.Proof.RsaKeyGen.X86.WitnessMont
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessRound
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.WitnessRound

/-- A candidate of `32 k` bits, the full width for RSA. -/
def Initial (g : Geometry) (capacity : Nat) (p : BitVec 32) (input : Import.Geometry) (s : State)
    (k : Nat := 2 * g.w) : Prop :=
  ∃ c, Prepare.Data g c capacity p s ∧ c % 2 = 1 ∧ 3 ≤ c ∧
    Spec.RsaKeyGen.bitLength (c - 1) = 32 * k ∧ Import.Context input s ∧
    s.gpr .esi = input.src ∧ s.gpr .edi + BitVec.ofNat 32 (g.array 6) = input.dst

def Work (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c, Prepare.Data g c capacity p s ∧ c % 2 = 1 ∧ 3 ≤ c

def WorkPair (g : Geometry) (capacity : Nat) (p : BitVec 32) (s t : State) : Prop :=
  Pair g [.edi] s t ∧ Work g capacity p s ∧ Work g capacity p t

def InitialPair (g : Geometry) (capacity : Nat) (p : BitVec 32) (input : Import.Geometry) (s t : State)
    (k : Nat := 2 * g.w) : Prop :=
  Pair g [.edi, .esi] s t ∧ Initial g capacity p input s k ∧ Initial g capacity p input t k

theorem load_pairAt {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {input : Import.Geometry}
    {draw k : Nat} (width : 4 * input.count = draw) (two : 2 ≤ k) (narrow : k ≤ input.count)
    (wide : input.count ≤ g.words) :
    RelCT isa (fun s t => InitialPair g capacity p input s t k) (VG.Impl.RsaKeyGen.X86.WitnessLoad.codeAt draw k g.w)
      (WorkPair g capacity p) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := WitnessLoad.codeAt_trace draw k g.w _ _ _ _ _ _ H.1.2.2 E G
  have post {a : State} (I : Initial g capacity p input a k) :
      WP isa (VG.Impl.RsaKeyGen.X86.WitnessLoad.codeAt draw k g.w) a (Work g capacity p) := by
    obtain ⟨c, S, odd, large, shape, C, source, destination⟩ := I
    exact WP.mono (WitnessLoad.codeAt_ok v S C width two narrow wide source destination odd shape)
      fun _ ⟨D, _, _, _, _⟩ => ⟨c, D, odd, large⟩
  have U := wp_result (post H.2.1) E
  have Z := wp_result (post H.2.2) G
  obtain ⟨cu, Du, ou, lu⟩ := U
  obtain ⟨cz, Dz, oz, lz⟩ := Z
  exact ⟨trace, ⟨Du.ready.context, Dz.ready.context, agree⟩, ⟨cu, Du, ou, lu⟩, ⟨cz, Dz, oz, lz⟩⟩

theorem store_pair {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (WorkPair g capacity p) (.block [.store (VG.Impl.Mont.X86.sc uniformOffset) .eax]) (WorkPair g capacity p) := by
  have raw : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
      (.block [.store (VG.Impl.Mont.X86.sc uniformOffset) .eax]) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
    checkedBlockInvariant rfl rfl
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := raw _ _ _ _ _ _ H.1.2.2 E G
  have post {a : State} (I : Work g capacity p a) :
      WP isa (.block [.store (VG.Impl.Mont.X86.sc uniformOffset) .eax]) a (Work g capacity p) := by
    obtain ⟨c, S, odd, large⟩ := I
    exact WP.mono (Prepare.storeGap_ok v S (by decide) (by decide)) fun _ ⟨D, _, _, _⟩ => ⟨c, D, odd, large⟩
  have U := wp_result (post H.2.1) E
  have Z := wp_result (post H.2.2) G
  obtain ⟨cu, Du, ou, lu⟩ := U
  obtain ⟨cz, Dz, oz, lz⟩ := Z
  exact ⟨trace, ⟨Du.ready.context, Dz.ready.context, agree⟩, ⟨cu, Du, ou, lu⟩, ⟨cz, Dz, oz, lz⟩⟩

theorem convert_pair {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (WorkPair g capacity p) (VG.Impl.RsaKeyGen.X86.WitnessMont.code name mont) (RoundCall.InputPair g capacity p) := by
  intro s t tr ur u z H E G
  have input {a : State} (I : Work g capacity p a) : WitnessMont.Input g capacity p a := by
    obtain ⟨c, S, odd, large⟩ := I
    exact ⟨c, S, odd, by omega_using [odd]⟩
  obtain ⟨trace, pair⟩ := WitnessMont.code_raw verified noSp stack v length _ _ _ _ _ _
    ⟨H.1, input H.2.1, input H.2.2⟩ E G
  have post {a : State} (I : Work g capacity p a) :
      WP isa (VG.Impl.RsaKeyGen.X86.WitnessMont.code name mont) a (RoundCall.Input g capacity p) := by
    obtain ⟨c, S, odd, large⟩ := I
    refine WP.mono (WitnessMont.code_ok verified noSp stack v length S odd (by omega_using [odd])) fun b ⟨D, value, _, _, _⟩ => ?_
    exact ⟨c, val32 a.mem g.W (g.array 6) g.words, D, odd, large, by rw [Nat.mod_mul_mod]; exact value⟩
  exact ⟨trace, pair, wp_result (post H.2.1) E, wp_result (post H.2.2) G⟩

theorem codeAt_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {input : Import.Geometry}
    {draw k : Nat} (width : 4 * input.count = draw) (two : 2 ≤ k) (narrow : k ≤ input.count)
    (wide : input.count ≤ g.words) (length : g.L = 8 * capacity) (fit : 108 ≤ p.toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    RelCT isa (fun s t => InitialPair g capacity p input s t k) (codeAt draw k g.w montName mont roundName round)
      (Pair g [.edi]) := by
  unfold codeAt
  exact RelCT.seq (load_pairAt v width two narrow wide) (RelCT.seq (store_pair v)
    (RelCT.seq (convert_pair montVerified montNoSp montStack v length)
      (RoundCall.code_trace roundVerified roundNoSp roundStack v length fit far lengthFar)))

end VG.Proof.RsaKeyGen.X86.WitnessRound

end

end

/-! ### `RsaKeyGen.X86.WitnessAdvanceTiming`, which this module and modules that import it used -/

section

/-! # Entropy cursor arithmetic uses only fixed header addresses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

theorem WitnessAdvance.codeAt_trace (D : Nat) : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block (VG.Impl.RsaKeyGen.X86.WitnessAdvance.codeAt D)) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT _ (.block (VG.Impl.RsaKeyGen.X86.WitnessAdvance.codeAt 0)) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem WitnessAvailable.codeAt_trace (D : Nat) : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block (VG.Impl.RsaKeyGen.X86.WitnessAvailable.codeAt D)) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT _ (.block (VG.Impl.RsaKeyGen.X86.WitnessAvailable.codeAt 0)) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

end VG.Proof.RsaKeyGen.X86

end

end

/-! # Consuming, testing and counting a witness reveals no sampled bytes or test result -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessStep
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.WitnessStep

/-- A candidate of `32 k` bits, the full width for RSA. -/
def Initial (g : Geometry) (capacity : Nat) (p rand : BitVec 32) (used randLen : Nat) (s : State)
    (k : Nat := 2 * g.w) : Prop :=
  ∃ c, Prepare.Data g c capacity p s ∧ s.mem.readW (off g.W 28) 32 = rand ∧ w32 s.mem g.W 152 = used ∧
    c % 2 = 1 ∧ 3 ≤ c ∧ Spec.RsaKeyGen.bitLength (c - 1) = 32 * k ∧
    w32 s.mem g.W 176 + 1 < 2 ^ 32 ∧ w32 s.mem g.W 192 + 1 < 2 ^ 32 ∧
    InRegions (s.rd ++ s.wr) (rand.setWidth 64) randLen

def InitialPair (g : Geometry) (capacity : Nat) (p rand : BitVec 32) (used randLen : Nat) (s t : State)
    (k : Nat := 2 * g.w) : Prop :=
  Pair g [.edi] s t ∧ Initial g capacity p rand used randLen s k ∧ Initial g capacity p rand used randLen t k

theorem advance_pairAt {g : Geometry} (v : g.Valid) {capacity used randLen draw k : Nat} {p rand : BitVec 32}
    (two : 2 ≤ k) (narrow : 4 * k ≤ draw) (wide : draw ≤ 8 * g.w) (four : draw % 4 = 0)
    (randFit : rand.toNat + randLen ≤ 2 ^ 32) (randLenFit : randLen < 2 ^ 32)
    (enough : used + draw ≤ randLen)
    (separate : (⟨rand.setWidth 64, randLen⟩ : Region).Disjoint ⟨g.W, g.L⟩) :
    RelCT isa (fun s t => InitialPair g capacity p rand used randLen s t k)
      (.block (VG.Impl.RsaKeyGen.X86.WitnessAdvance.codeAt draw))
      (fun s t => WitnessRound.InitialPair g capacity p (WitnessInput.geometryAt g rand used (draw / 4)) s t k) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := WitnessAdvance.codeAt_trace draw _ _ _ _ _ _ H.1.2.2 E G
  have post {a : State} (I : Initial g capacity p rand used randLen a k) :
      WP isa (.block (VG.Impl.RsaKeyGen.X86.WitnessAdvance.codeAt draw)) a fun b =>
        WitnessRound.Initial g capacity p (WitnessInput.geometryAt g rand used (draw / 4)) b k ∧
        b.gpr .esi = rand + BitVec.ofNat 32 used := by
    obtain ⟨c, S, source, consumed, odd, large, shape, _, _, readable⟩ := I
    refine WP.mono (WitnessAdvance.codeAt_ok (step := draw) v S source consumed (by omega))
      fun b ⟨B, ptr, _, _, K⟩ => ?_
    have readB : InRegions (b.rd ++ b.wr) (rand.setWidth 64) randLen := by
      rw [K.2.1, K.2.2]; exact readable
    exact ⟨⟨c, B, odd, large, shape, WitnessInput.context_okAt (used := used) (count := draw / 4) v B.ready.scratch
      randFit (by omega_using [two, narrow]) (by unfold Geometry.words; omega_using [wide]) (by omega_using [enough]) readB separate,
      ptr, (WitnessInput.destination_pointer v B.ready.scratch).symm⟩, ptr⟩
  obtain ⟨U, sourceU⟩ := wp_result (post H.2.1) E
  obtain ⟨Z, sourceZ⟩ := wp_result (post H.2.2) G
  obtain ⟨cu, Du, ou, lu, hu, Cu, su, du⟩ := U
  obtain ⟨cz, Dz, oz, lz, hz, Cz, sz, dz⟩ := Z
  have registers : ∀ r ∈ ([.edi, .esi] : List Reg), u.gpr r = z.gpr r := by
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact round_regs agree (by decide)
    · rw [sourceU, sourceZ]
  exact ⟨trace, ⟨Du.ready.context, Dz.ready.context, round_add_regs (round_forget agree) registers⟩,
    ⟨cu, Du, ou, lu, hu, Cu, su, du⟩, ⟨cz, Dz, oz, lz, hz, Cz, sz, dz⟩⟩

theorem codeAt_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {capacity used randLen draw k : Nat} {p rand : BitVec 32}
    (two : 2 ≤ k) (narrow : 4 * k ≤ draw) (wide : draw ≤ 8 * g.w) (four : draw % 4 = 0)
    (length : g.L = 8 * capacity)
    (randFit : rand.toNat + randLen ≤ 2 ^ 32) (randLenFit : randLen < 2 ^ 32)
    (enough : used + draw ≤ randLen)
    (separate : (⟨rand.setWidth 64, randLen⟩ : Region).Disjoint ⟨g.W, g.L⟩)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    RelCT isa (fun s t => InitialPair g capacity p rand used randLen s t k)
      (codeAt draw k g.w montName mont roundName round) (Pair g [.edi]) := by
  have raw : RelCT isa (fun s t => InitialPair g capacity p rand used randLen s t k)
      (codeAt draw k g.w montName mont roundName round) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
    unfold codeAt
    refine RelCT.seq (advance_pairAt v two narrow wide four randFit randLenFit enough separate) (RelCT.seq
      (WitnessRound.codeAt_trace (input := WitnessInput.geometryAt g rand used (draw / 4)) montVerified montNoSp
        montStack roundVerified roundNoSp roundStack v (by change 4 * (draw / 4) = draw; omega_using [four]) two
        (by change k ≤ draw / 4; omega_using [narrow]) (by change draw / 4 ≤ g.words; unfold Geometry.words; omega_using [wide])
        length fit far lengthFar) ?_)
    exact WitnessCount.code_trace.mono (fun _ _ H => H.2.2) (fun _ _ H => H)
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := raw _ _ _ _ _ _ H E G
  have post {a : State} (I : Initial g capacity p rand used randLen a k) :
      WP isa (codeAt draw k g.w montName mont roundName round) a (Context g) := by
    obtain ⟨c, S, source, consumed, odd, large, shape, roundsFit, uniformFit, readable⟩ := I
    exact WP.mono (codeAt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v two narrow wide four
      length S source consumed randFit randLenFit enough readable separate odd large shape roundsFit uniformFit
      fit far lengthFar) fun _ R => R.1.ready.context
  exact ⟨trace, wp_result (post H.2.1) E, wp_result (post H.2.2) G, agree⟩

end VG.Proof.RsaKeyGen.X86.WitnessStep

end

end

/-! # The blinded loop's public pointers and shared number of remaining iterations -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen VG.Proof.Dsa.X86

def Parameters.withSecret (P : Parameters) (c : Nat) (r : Spec.RsaKeyGen.Rand) : Parameters :=
  { P with candidate := c, entropy := r }

def LoopPair (P : Parameters) (other : Nat) (entropy : Spec.RsaKeyGen.Rand) (k n : Nat) (s t : State) : Prop :=
  Pair P.g [.edi] s t ∧ StateAt P k n s ∧ StateAt (P.withSecret other entropy) k n t

theorem StateAt.stepInitial {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s) :
    WitnessStep.Initial P.g P.capacity P.p P.rand (P.start + P.bytes * k) P.randLen s P.words :=
  ⟨P.candidate, S.prepared, S.randPtr, S.used, v.odd, by have := v.large; omega_using [this], v.shape,
    (S.countFit v).1, (S.countFit v).2, S.readable⟩

theorem StateAt.available {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s) :
    WP isa (.block (VG.Impl.RsaKeyGen.X86.WitnessAvailable.codeAt P.bytes)) s fun t =>
      StateAt P k n t ∧ isa.eval .b t = some (decide (P.randLen - (P.start + P.bytes * k) < P.bytes)) := by
  have usedBound : P.start + P.bytes * k ≤ P.randLen := by
    have := S.atLoop.used; rw [v.entropyLength] at this; exact this
  refine WP.mono (WitnessAvailable.codeAt_ok (D := P.bytes) S.prepared.ready.scratch v.geometry.headerFit
    (by have := v.geometry.maxWidth; have := v.wide; omega_arith) S.randLength S.used usedBound) fun t ⟨CF, mem, K⟩ => ?_
  exact ⟨S.keepMem v mem K (by decide) (by decide), CF⟩

def AvailablePair (P : Parameters) (other : Nat) (entropy : Spec.RsaKeyGen.Rand) (k n : Nat) (s t : State) : Prop :=
  LoopPair P other entropy k n s t ∧
    isa.eval .b s = some (decide (P.randLen - (P.start + P.bytes * k) < P.bytes)) ∧
    isa.eval .b t = some (decide (P.randLen - (P.start + P.bytes * k) < P.bytes))

theorem available_pair {P : Parameters} (v : P.Valid) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (LoopPair P other entropy k n) (.block (VG.Impl.RsaKeyGen.X86.WitnessAvailable.codeAt P.bytes))
      (AvailablePair P other entropy k n) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := WitnessAvailable.codeAt_trace P.bytes _ _ _ _ _ _ H.1.2.2 E G
  obtain ⟨U, Cu⟩ := wp_result (H.2.1.available v) E
  obtain ⟨Z, Cz⟩ := wp_result (H.2.2.available w) G
  exact ⟨trace, ⟨⟨U.prepared.ready.context, Z.prepared.ready.context, agree⟩, U, Z⟩, Cu, Cz⟩

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop

end

end

/-! # One blinded-loop step has the same trace for equal public entropy offsets -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

theorem exhausted_raw : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block exhausted)
    (VG.X86.Taint.Agree (roundTaint [.edi])) := checkedBlockInvariant rfl rfl

theorem again_raw : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block again)
    (VG.X86.Taint.Agree (roundTaint [.edi])) := checkedBlockInvariant rfl rfl

theorem branch_raw {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (AvailablePair P other entropy k n)
      (.ite .b (.block exhausted) (VG.Impl.RsaKeyGen.X86.WitnessStep.codeAt P.bytes P.words P.g.w montName mont roundName round))
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  refine VG.RelCT.ite (fun _ _ H => H.2.1.trans H.2.2.symm)
    (exhausted_raw.mono (fun _ _ H => H.1.1.1.2.2) (fun _ _ H => H)) ?_
  intro s t tr ur u z H E G
  have enough : P.start + P.bytes * k + P.bytes ≤ P.randLen := by
    by_contra short
    have bound := H.1.1.2.1.atLoop.used
    rw [v.entropyLength] at bound
    have small : P.randLen - (P.start + P.bytes * k) < P.bytes := by omega_using [short, bound]
    have condition := H.1.2.1
    rw [H.2, decide_eq_true small] at condition
    cases condition
  have pre : WitnessStep.InitialPair P.g P.capacity P.p P.rand (P.start + P.bytes * k) P.randLen s t P.words :=
    ⟨H.1.1.1, H.1.1.2.1.stepInitial v, H.1.1.2.2.stepInitial w⟩
  obtain ⟨trace, pair⟩ := WitnessStep.codeAt_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack
    v.geometry v.two v.narrow v.wide v.four
    v.length v.randFit v.randLenFit enough v.randSeparate v.low v.stackFar v.lengthFar _ _ _ _ _ _ pre E G
  exact ⟨trace, pair.2.2⟩

theorem step_raw {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (LoopPair P other entropy k n) (stepAt P.bytes P.words P.g.w montName mont roundName round)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold stepAt
  exact RelCT.seq (available_pair v w k n)
    (RelCT.seq (branch_raw montVerified montNoSp montStack roundVerified roundNoSp roundStack v w k n) again_raw)

theorem step_pair {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (LoopPair P other entropy k n) (stepAt P.bytes P.words P.g.w montName mont roundName round)
      (fun s t => Pair P.g [.edi] s t ∧ Outcome P k n s ∧ Outcome (P.withSecret other entropy) k n t) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := step_raw montVerified montNoSp montStack roundVerified roundNoSp roundStack v w k n _ _ _ _ _ _ H E G
  obtain ⟨U, Ou, _, _, _⟩ := wp_result
    (step_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v H.2.1) E
  obtain ⟨Z, Oz, _, _, _⟩ := wp_result
    (step_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack w H.2.2) G
  exact ⟨trace, ⟨U.ready.context, Z.ready.context, agree⟩, Ou, Oz⟩

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop

end

end

/-! # The complete prepared primality loop reveals only its consumed entropy length -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/MillerRabinTimingLoop.lean`, which only this module imported.
section

/-! # Equal specified witness counts give equal traces across the complete blinded loop -/

section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

theorem loop_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (LoopPair P other entropy k n) (.loop (stepAt P.bytes P.words P.g.w montName mont roundName round) .e) (Pair P.g [.edi]) := by
  let Inv : Nat → State → State → Prop := fun q s t => ∃ k n, q = n + 1 ∧ LoopPair P other entropy k n s t
  have run : RelCT isa (Inv (n + 1)) (.loop (stepAt P.bytes P.words P.g.w montName mont roundName round) .e) (Pair P.g [.edi]) := by
    refine RelCT.loop (M := isa) Inv ?_ (n + 1)
    rintro q s t tr ur u z ⟨i, j, rfl, H⟩ E G
    obtain ⟨trace, pair, Ou, Oz⟩ := step_pair montVerified montNoSp montStack roundVerified roundNoSp roundStack v w i j _ _ _ _ _ _ H E G
    rcases Ou with ⟨Eu, zeroU, _⟩ | ⟨Eu, positiveU, U⟩ <;>
      rcases Oz with ⟨Ez, zeroZ, _⟩ | ⟨Ez, positiveZ, Z⟩
    · refine ⟨trace, Eu.trans Ez.symm, fun _ => pair, ?_⟩
      intro continuing
      rw [Eu] at continuing
      cases continuing
    · omega
    · omega
    · refine ⟨trace, Eu.trans Ez.symm, ?_, ?_⟩
      · intro done
        rw [Eu] at done
        cases done
      · intro _
        exact ⟨j, by omega, i + 1, j - 1, by omega, pair, U, Z⟩
  exact run.mono (fun _ _ H => ⟨k, n, rfl, H⟩) (fun _ _ H => H)

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/WitnessChecksTiming.lean`, which only this module imported.
section

/-! # Initializing the witness policy has a width-only trace -/

section
namespace VG.Proof.RsaKeyGen.X86.WitnessChecks
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

theorem codeOf_trace (checks : Nat) : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block (VG.Impl.RsaKeyGen.X86.WitnessChecks.codeOf checks)) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT _ (.block (VG.Impl.RsaKeyGen.X86.WitnessChecks.codeOf 0)) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

end VG.Proof.RsaKeyGen.X86.WitnessChecks
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

def Parameters.iterations (P : Parameters) : Nat :=
  itersOf P.bytes P.entropy.length (shapeOf P.test) P.start - 1

def Initial (P : Parameters) (s : State) : Prop :=
  Prepare.Data P.g P.candidate P.capacity P.p s ∧
    InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen ∧
    Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy ∧
    s.mem.readW (off P.g.W 28) 32 = P.rand ∧ w32 s.mem P.g.W 32 = P.randLen ∧
    w32 s.mem P.g.W 152 = P.start

def InitialPair (P : Parameters) (other : Nat) (entropy : Spec.RsaKeyGen.Rand) (s t : State) : Prop :=
  Pair P.g [.edi] s t ∧ Initial P s ∧ Initial (P.withSecret other entropy) t ∧
    P.iterations = (P.withSecret other entropy).iterations

theorem init_pair {P : Parameters} (v : P.Valid) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (enough : P.start ≤ P.randLen) :
    RelCT isa (InitialPair P other entropy) (.block (VG.Impl.RsaKeyGen.X86.WitnessChecks.codeOf P.checks))
      (LoopPair P other entropy 0 P.iterations) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := WitnessChecks.codeOf_trace P.checks _ _ _ _ _ _ H.1.2.2 E G
  obtain ⟨S, readS, bytesS, ptrS, lenS, usedS⟩ := H.2.1
  obtain ⟨T, readT, bytesT, ptrT, lenT, usedT⟩ := H.2.2.1
  obtain ⟨U, _, _, _⟩ := wp_result (init_ok v S readS bytesS ptrS lenS usedS enough) E
  obtain ⟨Z, _, _, _⟩ := wp_result (init_ok w T readT bytesT ptrT lenT usedT enough) G
  have iters := H.2.2.2
  change P.iterations = (P.withSecret other entropy).iterations at iters
  change StateAt (P.withSecret other entropy) 0 (P.withSecret other entropy).iterations z at Z
  rw [← iters] at Z
  exact ⟨trace, ⟨U.prepared.ready.context, Z.prepared.ready.context, agree⟩, U, Z⟩

theorem code_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (enough : P.start ≤ P.randLen) :
    RelCT isa (InitialPair P other entropy) (codeWith P.checks P.bytes P.words P.g.w montName mont roundName round) (Pair P.g [.edi]) := by
  unfold codeWith
  exact RelCT.seq (init_pair v w enough)
    (loop_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v w 0 P.iterations)

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop

end

end

/-! ### `RsaKeyGen.X86.HalfPassTiming`, which only this module used -/

section

/-! # A masked exponent halving always visits every native word -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.HalfPass
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.HalfPass

theorem code_trace (n src out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (code n src out)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (code n src out) (code 1 0 0)
    (VG.Taint.hintOf taint (roundTaint [.edi]) (Code.erase (code 1 0 0)))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.HalfPass

end

end

/-! ### `RsaKeyGen.X86.PrepareTimingHeader`, which only this module used -/

section

/-! # Fresh candidates acquire identical public prepared metadata -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Prepare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

def Initial (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) (e : Nat := 64 * g.w - 1) : Prop :=
  ∃ c, Input g c capacity p s e

def InitialPair (g : Geometry) (capacity : Nat) (p : BitVec 32) (s t : State) (e : Nat := 64 * g.w - 1) : Prop :=
  VG.X86.Taint.Agree (roundTaint [.edi]) s t ∧ Initial g capacity p s e ∧ Initial g capacity p t e

theorem header_pair {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) {e : Nat} :
    RelCT isa (fun s t => InitialPair g capacity p s t e) (VG.Impl.RsaKeyGen.X86.PrepareHeader.code g.w)
      (fun s t => PreparedR2.InputPair g capacity p s t e) := by
  intro s t tr ur u z ⟨H, S, T⟩ E G
  obtain ⟨trace, agree⟩ := PrepareHeader.code_trace g.w _ _ _ _ _ _ H E G
  have post {a : State} (I : Initial g capacity p a e) :
      WP isa (VG.Impl.RsaKeyGen.X86.PrepareHeader.code g.w) a (fun t => PreparedR2.Input g capacity p t e) := by
    obtain ⟨c, I⟩ := I
    exact WP.mono (PrepareHeader.code_ok v I.scratch I.caller length I.candidate I.odd)
      fun _ ⟨R, _, _, _⟩ => ⟨c, R, I.odd, I.top⟩
  obtain ⟨cu, Cu, ou, tu⟩ := wp_result (post S) E
  obtain ⟨cz, Cz, oz, tz⟩ := wp_result (post T) G
  exact ⟨trace, ⟨Cu.context, Cz.context, agree⟩, ⟨cu, Cu, ou, tu⟩, ⟨cz, Cz, oz, tz⟩⟩

end VG.Proof.RsaKeyGen.X86.Prepare

end

end

/-! # Preparation and all witness rounds share only the specified public iteration count -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/PrepareTimingR2.lean`, which only this module imported.
section

/-! # The short R² phase feeds the prepared constant conversion without leaking residues -/

section
namespace VG.Proof.RsaKeyGen.X86.Prepare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

theorem r2_pairAt {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (bound : g.w ≤ 64) {e : Nat} (positive : 1 ≤ e) (eLt : e < 64 * g.w) :
    RelCT isa (fun s t => PreparedR2.InputPair g capacity p s t e) (VG.Impl.RsaKeyGen.X86.PreparedR2.codeAt e g.w name mont)
      (Constants.InputPair g capacity p) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, pair⟩ := PreparedR2.code_traceAt (p := p) verified noSp stack v length bound positive eLt
    _ _ _ _ _ _ H E G
  have post {a : State} (I : PreparedR2.Input g capacity p a e) :
      WP isa (VG.Impl.RsaKeyGen.X86.PreparedR2.codeAt e g.w name mont) a (Constants.Input g capacity p) := by
    obtain ⟨c, A, odd, top⟩ := I
    have two : 2 ≤ 2 ^ e := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) positive; simpa using this
    exact WP.mono (PreparedR2.code_okAt verified noSp stack v length A bound odd positive eLt top)
      fun _ ⟨R, r2, _, _, _⟩ => ⟨c, R, odd, by omega, r2⟩
  exact ⟨trace, pair, wp_result (post H.2.1) E, wp_result (post H.2.2) G⟩

end VG.Proof.RsaKeyGen.X86.Prepare
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/LowPairTiming.lean`, which only this module imported.
section

/-! # The lowest-word scan visits every public pair without secret control flow -/

section
namespace VG.Proof.RsaKeyGen.X86.LowPair
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.LowPair

theorem step_trace (src index : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (step src index))
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (.block (step src index)) (.block (step 0 0)) (.block [])
    rfl rfl rfl (by decide +kernel)

theorem steps_trace (src start count : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (steps src start count)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  induction count generalizing start with
  | zero => exact RelCT.block_nil (fun _ _ h => h)
  | succ count ih => exact RelCT.seq (step_trace src start) (ih (start + 1))

theorem scan_trace (src count : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (scan src count)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq (checkedBlockInvariant (τ' := roundTaint [.edi, .ebx, .esi]) rfl rfl) (steps_trace src 0 count)

end VG.Proof.RsaKeyGen.X86.LowPair
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/LowBitTiming.lean`, which only this module imported.
section

/-! # The native paired low-bit operation has a fixed instruction trace -/

section
namespace VG.Proof.RsaKeyGen.X86.LowBit
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.LowBit

theorem code_trace : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block code)
    (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  checkedBlockInvariant rfl rfl

end VG.Proof.RsaKeyGen.X86.LowBit
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentMarkerTiming.lean`, which only this module imported.
section

/-! # The secret exponent alignment is prepared without secret-dependent leakage -/

section
namespace VG.Proof.RsaKeyGen.X86.ExponentMarker
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.ExponentMarker

theorem code_trace (src count : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (code src count)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq (LowPair.scan_trace src count) LowBit.code_trace

end VG.Proof.RsaKeyGen.X86.ExponentMarker
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/SigMaskTiming.lean`, which only this module imported.
section

/-! # Alignment masks use fixed addresses and no secret-dependent branches -/

section
namespace VG.Proof.RsaKeyGen.X86.SigMask
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.SigMask

theorem code_trace (marker j : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (code marker j))
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (.block (code marker j)) (.block (code 0 0)) (.block [])
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.SigMask
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentShiftTiming.lean`, which only this module imported.
section

/-! # Every alignment pass executes independently of the secret shift -/

section
namespace VG.Proof.RsaKeyGen.X86.ExponentShift
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.ExponentShift

theorem halfIf_trace (n marker out j : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (halfIf n marker out j)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq (SigMask.code_trace marker j) (HalfPass.code_trace n out out)

theorem passes_trace (n marker out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (passes n marker out)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq (halfIf_trace n marker out 1) (RelCT.seq (halfIf_trace n marker out 2) (halfIf_trace n marker out 3))

end VG.Proof.RsaKeyGen.X86.ExponentShift
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentTiming.lean`, which only this module imported.
section

/-! # Complete exponent preparation is independent of the candidate and its trailing zeros -/

section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.Exponent

theorem clearTops_trace (n src out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (clearTops n src out))
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (.block (clearTops n src out)) (.block (clearTops 0 0 0)) (.block [])
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem finish_trace (n out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (finish n out))
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (.block (finish n out)) (.block (finish 0 0)) (.block [])
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem code_trace (w minusOne src out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (code w minusOne src out)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq (ExponentMarker.code_trace minusOne w)
    (RelCT.seq (checkedBlockInvariant rfl rfl)
      (RelCT.seq (RelCT.seq (clearTops_trace (2 * w) src out) (HalfPass.code_trace (2 * w) src out))
        (RelCT.seq (ExponentShift.passes_trace (2 * w) markerOffset out) (finish_trace (2 * w) out))))

end VG.Proof.RsaKeyGen.X86.Exponent
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/PrepareTiming.lean`, which only this module imported.
section

/-! # Complete reusable candidate preparation has a candidate-independent trace -/

section
namespace VG.Proof.RsaKeyGen.X86.Prepare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

theorem code_rawAt {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (bound : g.w ≤ 64) {e : Nat} (positive : 1 ≤ e) (eLt : e < 64 * g.w) :
    RelCT isa (fun s t => InitialPair g capacity p s t e) (VG.Impl.RsaKeyGen.X86.Prepare.codeAt e g.w name mont)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold VG.Impl.RsaKeyGen.X86.Prepare.codeAt
  rw [Prepared.slot_eq, Prepared.slot_eq, Prepared.slot_eq]
  refine RelCT.seq (header_pair v length) (RelCT.seq (r2_pairAt verified noSp stack v length bound positive eLt)
    (RelCT.seq (Constants.code_trace verified noSp stack v length) ?_))
  exact (Exponent.code_trace g.w (g.array 5) (g.array 0) (g.array 27)).mono
    (fun _ _ H => H.2.2) (fun _ _ H => H)

end VG.Proof.RsaKeyGen.X86.Prepare
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateTest
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen VG.Proof.Dsa.X86

def CorePair (P : MillerRabinLoop.Parameters) (other : Nat) (entropy : Spec.RsaKeyGen.Rand) (s t : State) : Prop :=
  VG.X86.Taint.Agree (roundTaint [.edi]) s t ∧ CandidatePrepare.Input P s ∧
    CandidatePrepare.Input (P.withSecret other entropy) t ∧
    P.iterations = (P.withSecret other entropy).iterations

theorem prepare_pair {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (bound : P.g.w ≤ 64)
    {other : Nat} {entropy : Spec.RsaKeyGen.Rand} (w : (P.withSecret other entropy).Valid) :
    RelCT isa (CorePair P other entropy) (VG.Impl.RsaKeyGen.X86.Prepare.codeAt P.seed P.g.w name mont)
      (MillerRabinLoop.InitialPair P other entropy) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := Prepare.code_rawAt verified noSp stack v.geometry v.length bound v.seedPos v.seedLt
    _ _ _ _ _ _ ⟨H.1, ⟨P.candidate, H.2.1.prepare⟩, ⟨other, H.2.2.1.prepare⟩⟩ E G
  obtain ⟨U, _, _, _⟩ := wp_result (CandidatePrepare.code_ok verified noSp stack v bound H.2.1) E
  obtain ⟨Z, _, _, _⟩ := wp_result (CandidatePrepare.code_ok verified noSp stack w bound H.2.2.1) G
  exact ⟨trace, ⟨U.prepared.ready.context, Z.prepared.ready.context, agree⟩,
    ⟨U.prepared, U.readable, U.entropy, U.randPtr, U.randLength, U.used⟩,
    ⟨Z.prepared, Z.readable, Z.entropy, Z.randPtr, Z.randLength, Z.used⟩, H.2.2.2⟩

theorem core_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (bound : P.g.w ≤ 64)
    {other : Nat} {entropy : Spec.RsaKeyGen.Rand} (w : (P.withSecret other entropy).Valid)
    (enough : P.start ≤ P.randLen) :
    RelCT isa (CorePair P other entropy) (VG.Impl.RsaKeyGen.X86.CandidateTest.coreWith P.seed P.checks P.bytes P.words P.g.w montName mont roundName round)
      (Pair P.g [.edi]) := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateTest.coreWith
  exact RelCT.seq (prepare_pair montVerified montNoSp montStack v bound w)
    (MillerRabinLoop.code_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v w enough)

end VG.Proof.RsaKeyGen.X86.CandidateTest
