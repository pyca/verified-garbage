module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessRound
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86.RoundTiming

import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessLoadTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedDataGap
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessMont
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessMont
import VerifiedGarbage.Proof.MillerRabin.X86.TimingMultiply
import VerifiedGarbage.Proof.MillerRabin.X86.TimingCopy
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
    exact ⟨c, S, odd, by omega⟩
  obtain ⟨trace, pair⟩ := WitnessMont.code_raw verified noSp stack v length _ _ _ _ _ _
    ⟨H.1, input H.2.1, input H.2.2⟩ E G
  have post {a : State} (I : Work g capacity p a) :
      WP isa (VG.Impl.RsaKeyGen.X86.WitnessMont.code name mont) a (RoundCall.Input g capacity p) := by
    obtain ⟨c, S, odd, large⟩ := I
    refine WP.mono (WitnessMont.code_ok verified noSp stack v length S odd (by omega)) fun b ⟨D, value, _, _, _⟩ => ?_
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

theorem code_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {input : Import.Geometry}
    (width : input.count = g.words) (length : g.L = 8 * capacity) (fit : 108 ≤ p.toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    RelCT isa (InitialPair g capacity p input) (code g.w montName mont roundName round) (Pair g [.edi]) :=
  codeAt_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v
    (by rw [width]; unfold Geometry.words; omega) (by have := v.minWidth; omega)
    (by rw [width]; unfold Geometry.words; omega) (by rw [width]) length fit far lengthFar

end VG.Proof.RsaKeyGen.X86.WitnessRound
