module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateTest
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrepareInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinTiming

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2Timing
import VerifiedGarbage.Proof.RsaKeyGen.X86.ConstantsTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2
import VerifiedGarbage.Impl.RsaKeyGen.X86.LowPair
import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Impl.RsaKeyGen.X86.LowBit
import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentMarker
import VerifiedGarbage.Impl.RsaKeyGen.X86.SigMask
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentShift
import VerifiedGarbage.Proof.RsaKeyGen.X86.HalfPassTiming
import VerifiedGarbage.Impl.RsaKeyGen.X86.Exponent
import VerifiedGarbage.Impl.RsaKeyGen.X86.Prepare
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareTimingHeader
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.Prepare
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

theorem r2_pair {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (bound : g.w ≤ 64) :
    RelCT isa (PreparedR2.InputPair g capacity p) (VG.Impl.RsaKeyGen.X86.PreparedR2.code g.w name mont)
      (Constants.InputPair g capacity p) :=
  r2_pairAt verified noSp stack v length bound (e := 64 * g.w - 1)
    (by have := v.minWidth; omega) (by have := v.minWidth; omega)

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

theorem code_raw {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (bound : g.w ≤ 64) :
    RelCT isa (InitialPair g capacity p) (VG.Impl.RsaKeyGen.X86.Prepare.code g.w name mont)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  code_rawAt verified noSp stack v length bound (e := 64 * g.w - 1)
    (by have := v.minWidth; omega) (by have := v.minWidth; omega)

theorem code_traceAt {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (bound : g.w ≤ 64) {e : Nat} (positive : 1 ≤ e) (eLt : e < 64 * g.w) :
    RelCT isa (fun s t => InitialPair g capacity p s t e) (VG.Impl.RsaKeyGen.X86.Prepare.codeAt e g.w name mont)
      (Pair g [.edi]) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := code_rawAt (p := p) verified noSp stack v length bound positive eLt _ _ _ _ _ _ H E G
  have post {a : State} (I : Initial g capacity p a e) :
      WP isa (VG.Impl.RsaKeyGen.X86.Prepare.codeAt e g.w name mont) a (Context g) := by
    obtain ⟨c, I⟩ := I
    exact WP.mono (code_okAt verified noSp stack v bound length I positive eLt) fun _ R => R.1.ready.context
  exact ⟨trace, wp_result (post H.2.1) E, wp_result (post H.2.2) G, agree⟩

theorem code_trace {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (bound : g.w ≤ 64) :
    RelCT isa (InitialPair g capacity p) (VG.Impl.RsaKeyGen.X86.Prepare.code g.w name mont) (Pair g [.edi]) :=
  code_traceAt verified noSp stack v length bound (e := 64 * g.w - 1)
    (by have := v.minWidth; omega) (by have := v.minWidth; omega)

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
