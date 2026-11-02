module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessStep
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStep
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessAdvance
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessAdvanceTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRoundTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessCountTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

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
      randFit (by omega) (by unfold Geometry.words; omega) (by omega) readB separate,
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
        montStack roundVerified roundNoSp roundStack v (by change 4 * (draw / 4) = draw; omega) two
        (by change k ≤ draw / 4; omega) (by change draw / 4 ≤ g.words; unfold Geometry.words; omega)
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

theorem code_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {capacity used randLen : Nat} {p rand : BitVec 32}
    (length : g.L = 8 * capacity)
    (randFit : rand.toNat + randLen ≤ 2 ^ 32) (randLenFit : randLen < 2 ^ 32)
    (enough : used + 8 * g.w ≤ randLen)
    (separate : (⟨rand.setWidth 64, randLen⟩ : Region).Disjoint ⟨g.W, g.L⟩)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    RelCT isa (InitialPair g capacity p rand used randLen) (code g.w montName mont roundName round) (Pair g [.edi]) :=
  codeAt_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v
    (by have := v.minWidth; omega) (by omega) (by omega) (by omega) length randFit randLenFit enough separate
    fit far lengthFar

end VG.Proof.RsaKeyGen.X86.WitnessStep
