module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeFrameInputs
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeInputArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeTapeValues
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleMemory
import VerifiedGarbage.Proof.Dsa.X86.Bytes
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeInputs
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeTapeArguments

/-! # Load the candidate and restore its independently threaded witness tape -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

theorem primeSetupFromFrame_ok {G : PrimeConfig} {frame : Addr} {words : Nat → BitVec 32} {used : Nat} {s : State}
    (R : PrimeFrameInputs G frame words used s) :
    WP isa (primeSetupFromFrame G.len) s fun t => PrimeInputs G t ∧ SearchFrame t frame ∧
      FrameWords t.mem frame words ∧ t.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 used ∧
      Frame [⟨G.base, G.size⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  have width := G.width
  have room : primeWitness + 4 ≤ G.size := by have := G.room; unfold primeWitness primeExponent at *; omega
  have modRoom : slot G.n 0 + 8 * G.n ≤ G.size := by
    have := G.room
    simp only [slot, stride, primeExponent] at *
    omega
  unfold primeSetupFromFrame
  change WP isa (.seq (.block primeInputArgs) (.seq (VG.Impl.Dsa.X86.loadComponent G.len G.n (slot G.n 0)) (.block primeTapeArgs))) s _
  refine WP.seq (WP.mono (primeInputArgs_ok R.search R.slots) fun a ⟨di, si, ma, Ka⟩ => ?_)
  have Sa : Scr a G.base G.size := ⟨by rw [di]; exact R.base,
    by rw [Ka.2.2]; exact R.write, R.nowrap, by rw [Ka.1 _ (by decide)]; exact R.stack⟩
  have Fa := R.search.keeps Ka (by decide)
  have Wa : FrameWords a.mem frame words := by rw [ma]; exact R.slots
  refine WP.seq (WP.mono (loadComponent_ok Sa modRoom (by rw [si]; exact R.candidateFit)
    G.lenMin (by unfold PrimeConfig.n; omega) G.lenWords
    (by intro d hd; rw [si, Ka.2.1, Ka.2.2]; exact R.candidateRead d hd)
    (by rw [si]; exact R.candidateScratch.sub_right (Offset.sub_base _ modRoom))) fun b ⟨modulus, Kb, Ob⟩ => ?_)
  rw [si, ma, R.candidate] at modulus
  have Sb := Sa.of_keeps Kb (by decide)
  have Fb := Fa.keeps Kb (by decide)
  have Fload : Frame [⟨off G.base (slot G.n 0), 8 * G.n⟩] a.mem b.mem :=
    sampleOuts_frame (Outs.of_outside Ob (rs := [(slot G.n 0, 8 * G.n)]) (by simp)) (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr; have := R.nowrap; omega)
  have Wb := Wa.keep Fload (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact R.frameScratch.sub_right (Offset.sub_base _ modRoom))
  refine WP.mono (primeTapeArgs_ok Fb Sb Wb room R.frameScratch) fun t ⟨Ft, St, Wt, mt, Ot, Kt⟩ => ?_
  have headers := primeTapeValues mt
  have K : Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t :=
    ((Ka.mono (by decide)).trans (Kb.mono (by decide))).trans (Kt.mono (by decide))
  have modT : wordsVal t.mem G.base (slot G.n 0) G.n = G.modulus := by
    rw [Ot.wordsVal (.inl (by simp only [slot, stride, primeUsed]; omega))
      (by have := R.nowrap; omega), modulus]
  have inputs : PrimeInputs G t := ⟨St, R.odd, R.gtOne, modT,
    headers.1.trans R.tape, headers.2.1.trans R.tapeLen, headers.2.2.2.trans R.witness,
    by intro i hi; rw [K.2.1, K.2.2]; exact R.tapeRead i hi,
    by intro d hd; rw [K.2.1, K.2.2]; exact R.witnessRead d hd,
    by intro i hi; rw [K.2.1, K.2.2]; exact R.witnessReadByte i hi,
    by intro i hi; rw [K.2.2]; exact R.witnessWrite i hi⟩
  have Fheader : Frame [⟨off G.base primeUsed, 24⟩] b.mem t.mem :=
    sampleOuts_frame (Outs.of_outside Ot (rs := [(primeUsed, 24)]) (by simp)) (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr; decide)
  have loadAll : Frame [⟨G.base, G.size⟩] s.mem b.mem := by
    rw [ma] at Fload
    apply Fload.sub
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨G.base, G.size⟩, by simp, Offset.sub_base _ modRoom⟩
  refine ⟨inputs, Ft, Wt, headers.2.2.1.trans R.usedValue, loadAll.trans (Fheader.sub ?_), K⟩
  intro r hr; obtain rfl := List.mem_singleton.mp hr
  exact ⟨⟨G.base, G.size⟩, by simp, Offset.sub_base _ (by unfold primeUsed primeWitness at *; omega)⟩
end VG.Proof.Dsa.X86.Generation
