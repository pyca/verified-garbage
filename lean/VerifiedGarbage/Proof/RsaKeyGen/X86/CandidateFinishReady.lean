module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinish
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateArrays
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestCore
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrepareInput
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.X86.ExportBE
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateFinish
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

/-! ### `RsaKeyGen.X86.CandidateFinishInput`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.CandidatePrime`, which this module and modules that import it used -/

section

/-! # Accepted candidates export their prime and exact entropy consumption -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateFinish
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Bignum.X86.PublicContext

structure PrimeInput (base : Addr) (size w candidate : Nat) (out usedPtr count : BitVec 32) (s : State) : Prop where
  scratch : Scr s base size
  positive : 0 < w
  space : slot w 0 + 8 * w ≤ size
  header : 156 ≤ size
  outEq : s.mem.readW (off base 0) 32 = out
  lengthEq : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w)
  usedEq : s.mem.readW (off base 44) 32 = usedPtr
  countEq : s.mem.readW (off base 152) 32 = count
  candidateEq : val32 s.mem base (slot w 0) (2 * w) = candidate
  outFit : out.toNat + 8 * w ≤ 2 ^ 32
  outWrite : InRegions s.wr (out.setWidth 64) (8 * w)
  usedWrite : Ws s (usedPtr.setWidth 64) 8
  workspaceFar : (⟨base, size⟩ : Region).Disjoint ⟨out.setWidth 64, 8 * w⟩
  usedFar : (⟨out.setWidth 64, 8 * w⟩ : Region).Disjoint ⟨usedPtr.setWidth 64, 8⟩

theorem prime_ok {s : State} {base : Addr} {size w candidate : Nat} {out usedPtr count : BitVec 32}
    (S : PrimeInput base size w candidate out usedPtr count s) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateFinish.prime w) s fun t =>
      t.gpr .eax = 1#32 ∧ Spec.Rsa.bytesAt t.mem (out.setWidth 64) (8 * w) = Spec.Rsa.i2osp candidate (8 * w) ∧
      t.mem.readW (usedPtr.setWidth 64) 64 = BitVec.ofNat 64 count.toNat ∧
      Frame [⟨out.setWidth 64, 8 * w⟩, ⟨usedPtr.setWidth 64, 8⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateFinish.prime
  refine WP.seq (wp_movS (readSrc_sc S.scratch (d := 0) (by have := S.header; omega_using [this])) fun a A _ =>
    wp_movS (readSrc_sc (S.scratch.of_keeps A.keeps (by decide)) (d := 4) (by have := S.header; omega_using [this])) fun b B _ => WP.block_nil ?_)
  have Kb : Keeps [.ebx, .ecx] s b := (A.keeps.mono (by decide)).widen B.keeps
  have Mb : b.mem = s.mem := B.mem.trans A.mem
  have outB : b.gpr .ebx = out := by rw [B.other .ebx (by decide), A.gpr, S.outEq]
  have lenB : b.gpr .ecx = BitVec.ofNat 32 (8 * w) := by rw [B.gpr, A.mem, S.lengthEq]
  have valueB : wordsVal b.mem base (slot w 0) w = candidate := by
    rw [wordsVal_eq_val32, Mb]; exact S.candidateEq
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.storeBE_ok (S.scratch.of_keeps Kb (by decide))
    (by have := S.positive; omega_using [this]) (by rfl) S.space lenB
    (by rw [wordsVal_eq_val32, show 8 * (8 * w) = 32 * (2 * w) by omega_using []]; exact val32_lt _ _ _ _)
    (by rw [outB]; exact S.outFit) (by rw [Kb.2.2, outB]; exact S.outWrite)
    (by
      rw [outB]
      exact Region.Disjoint.sub_left S.workspaceFar (Offset.sub_base base S.space)))
    fun c ⟨bytesC, Fc, Kc⟩ => ?_)
  rw [outB, valueB] at bytesC
  rw [outB, Mb] at Fc
  have Ksc : Keeps [.eax, .ebx, .ecx, .esi] s c := (Kb.mono (by decide)).widen Kc
  have readHeader (d : Nat) (fit : d + 4 ≤ size) : c.mem.readW (off base d) 32 = s.mem.readW (off base d) 32 :=
    Fc.readW (r := ⟨base, size⟩) (Offset.contains_base _ fit (by have := S.scratch.nowrap; omega_using [fit, this]))
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact S.workspaceFar) (by decide)
  refine WP.mono (used_ok (status := 1) (S.scratch.of_keeps Ksc (by decide)) S.header
    (S.usedWrite.of_keeps Ksc) ((readHeader 44 (by have := S.header; omega_using [this])).trans S.usedEq)
    ((readHeader 152 (by have := S.header; omega_using [this])).trans S.countEq)) fun t ⟨result, memory, O, Kt⟩ => ?_
  have Ft : Frame [⟨usedPtr.setWidth 64, 8⟩] c.mem t.mem := by
    simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using
      VG.Proof.Bignum.outside_frame O (by decide)
  refine ⟨result, ?_, ?_, ?_, (Ksc.mono (by decide)).trans (Kt.mono (by decide))⟩
  · rw [VG.Proof.RsaKeyGen.frame_bytesAt Ft (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact S.usedFar)
      (by have := S.outFit; omega_using [this])]
    exact bytesC
  · rw [memory, Mem.readW_writeW_self64]
  · exact (Fc.mono (fun _ mem => by obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_self)).trans
      (Ft.mono (fun _ mem => List.mem_cons_of_mem _ mem))

end VG.Proof.RsaKeyGen.X86.CandidateFinish

end

end

/-! ### `RsaKeyGen.X86.CandidateTestMetadata`, which only this module used -/

section

/-! # Prepared testing retains the output pointers required by every finish branch -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateTest
open VG VG.Proof.Mont VG.Proof.MillerRabin.X86

def protectedHeader (d bytes : Nat) : Prop := d + bytes ≤ 8 ∨ 16 ≤ d ∧ d + bytes ≤ 48

theorem ranges_apart {g : Geometry} {d bytes : Nat} (safe : protectedHeader d bytes)
    {r : Nat × Nat} (mem : r ∈ ranges g) : d + bytes ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  rcases List.mem_append.mp mem with mem | mem
  · exact Prepare.ranges_apart (by unfold protectedHeader at safe; left; omega_using [safe]) mem
  · refine (?_ : ∀ r ∈ MillerRabinLoop.ranges g, d + bytes ≤ r.1 ∨ r.1 + r.2 ≤ d) r mem
    unfold protectedHeader at safe
    simp only [MillerRabinLoop.ranges, WitnessChecks.ranges, WitnessStep.ranges,
      WitnessRound.ranges, WitnessMont.ranges, montWrites, roundWrites,
      WitnessCount.ranges, WitnessCount.nextRanges, List.forall_mem_append, List.forall_mem_cons,
      List.not_mem_nil, false_imp_iff, implies_true, and_true,
      Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
      VG.Impl.RsaKeyGen.X86.WitnessRound.uniformOffset,
      VG.Impl.RsaKeyGen.X86.WitnessCount.statusOffset,
      VG.Impl.RsaKeyGen.X86.WitnessCount.roundsOffset,
      VG.Impl.RsaKeyGen.X86.WitnessCount.uniformOffset]
    omega_using [safe]

theorem metadata32 {g : Geometry} (v : g.Valid) {m m' : Mem}
    (W : WorkspaceFrame g (ranges g) m m') {d : Nat} (safe : protectedHeader d 4) :
    m'.readW (off g.W d) 32 = m.readW (off g.W d) 32 := by
  apply W.read32 (by have := v.headerFit; unfold protectedHeader at safe; omega_using [safe, this])
  exact fun _ mem => ranges_apart safe mem

end VG.Proof.RsaKeyGen.X86.CandidateTest

end

end


/-! # Live candidate state supplies every pointer and permission needed by the finish paths -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

def FinishReady (E : Environment) (c : Nat) (s : State) : Prop :=
  CandidateFinish.PrimeInput E.base E.size E.width c E.out E.used (s.mem.readW (off E.base 152) 32) s ∧
  Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0

theorem finish_ready {E : Environment} (v : E.Valid) {c : Nat} {s : State}
    (S : Scr s E.base E.size)
    (out : s.mem.readW (off E.base 0) 32 = E.out)
    (length : s.mem.readW (off E.base 4) 32 = BitVec.ofNat 32 E.length)
    (used : s.mem.readW (off E.base 44) 32 = E.used)
    (outWrite : InRegions s.wr (E.out.setWidth 64) E.length)
    (usedWrite : VG.Proof.Mont.X86.Rt.Ws s (E.used.setWidth 64) 8)
    (value : val32 s.mem E.base (slot E.width 0) (2 * E.width) = c)
    (zeros : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0) : FinishReady E c s := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  refine ⟨⟨S, by have := v.width_bounds.1; omega_using [this], v.slotFit (by decide), by omega_using [space],
    out, ?_, used, rfl, value, ?_, ?_, usedWrite, ?_, ?_⟩, zeros⟩
  · rw [v.length_eq]; exact length
  · rw [v.length_eq]; exact v.outFit
  · rw [v.length_eq]; exact outWrite
  · rw [v.length_eq]; exact v.outWorkspace.symm
  · rw [v.length_eq]; exact v.outUsed

theorem Drawn.finishReady {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) : FinishReady E (candidateValue E entropy) s :=
  finish_ready v D.input.scratch D.input.out_eq (D.input.header 1 (by decide)) D.input.usedPointer
    D.input.outWrite D.input.usedWrite D.candidate D.zeros

theorem Drawn.finishReady_after_test {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s t : State}
    (D : Drawn E eBytes pBytes entropy s)
    (value : val32 t.mem E.base (slot E.width 0) (2 * E.width) = candidateValue E entropy)
    (W : WorkspaceFrame E.geometry (CandidateTest.ranges E.geometry) s.mem t.mem)
    (F : WorkFrame E s.mem t.mem) (K : Keeps WitnessStep.clob s t) :
    FinishReady E (candidateValue E entropy) t := by
  have out := CandidateTest.metadata32 v.geometry W (d := 0) (by left; decide)
  have length := CandidateTest.metadata32 v.geometry W (d := 4) (by left; decide)
  have used := CandidateTest.metadata32 v.geometry W (d := 44) (by right; constructor <;> decide)
  exact finish_ready v (D.input.scratch.of_keeps K (by unfold WitnessStep.clob; decide))
    (out.trans D.input.out_eq) (length.trans (D.input.header 1 (by decide))) (used.trans D.input.usedPointer)
    (by rw [K.2.2]; exact D.input.outWrite) (D.input.usedWrite.of_keeps K) value ((F.output v).trans D.zeros)

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! # The native finish paths expose exact status, output bytes, and entropy consumption -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def Outputs (E : Environment) (status count : Nat) (bytes : List Byte) (s : State) : Prop :=
  s.gpr .eax = BitVec.ofNat 32 status ∧ Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = bytes ∧
  s.mem.readW (E.used.setWidth 64) 64 = BitVec.ofNat 64 count

theorem FinishReady.keepMem {E : Environment} {c : Nat} {s t : State} (S : FinishReady E c s)
    (M : t.mem = s.mem) {regs : List Reg} (K : Keeps regs s t) (base : .edi ∉ regs) (sp : .esp ∉ regs) :
    FinishReady E c t := by
  obtain ⟨S, zeros⟩ := S
  refine ⟨⟨S.scratch.of_keeps K base sp, S.positive, S.space, S.header, ?_, ?_, ?_, rfl, ?_, S.outFit, ?_,
    S.usedWrite.of_keeps K, S.workspaceFar, S.usedFar⟩, ?_⟩
  · rw [M]; exact S.outEq
  · rw [M]; exact S.lengthEq
  · rw [M]; exact S.usedEq
  · rw [M]; exact S.candidateEq
  · rw [K.2.2]; exact S.outWrite
  · rw [M]; exact zeros

theorem used_frame {E : Environment} {m m' : Mem} (O : Outside (E.used.setWidth 64) 0 8 m m') :
    MutableFrame E m m' := by
  have F := VG.Proof.Bignum.outside_frame O (by decide)
  change Frame [⟨off (E.used.setWidth 64) 0, 8⟩] m m' at F
  have base : off (E.used.setWidth 64) 0 = E.used.setWidth 64 := by rw [off, BitVec.add_zero]
  rw [base] at F
  exact F.mono (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem finish_used_ok {E : Environment} (v : E.Valid) {c status : Nat} {s : State} (S : FinishReady E c s) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateFinish.used status) s fun t =>
      Outputs E status (w32 s.mem E.base 152) (List.replicate E.length 0) t ∧
      MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  refine WP.mono (CandidateFinish.used_ok S.1.scratch S.1.header S.1.usedWrite S.1.usedEq rfl)
    fun t ⟨statusEq, memory, O, K⟩ => ?_
  refine ⟨⟨statusEq, ?_, ?_⟩, used_frame O, K.mono (by unfold WitnessStep.clob; decide)⟩
  · exact (VG.Proof.Bignum.scratch_bytes O (by have := v.outFit; omega_using [this]) v.outUsed).trans S.2
  · rw [memory, Mem.readW_writeW_self64]

theorem finish_none_ok {E : Environment} (v : E.Valid) {c : Nat} {s : State} (S : FinishReady E c s) :
    WP isa VG.Impl.RsaKeyGen.X86.CandidateFinish.none s fun t =>
      Outputs E 0 0 (List.replicate E.length 0) t ∧
      MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  refine WP.mono (CandidateFinish.none_ok S.1.scratch (by have := S.1.header; omega_using [this]) S.1.usedWrite S.1.usedEq)
    fun t ⟨statusEq, memory, O, K⟩ => ?_
  refine ⟨⟨statusEq, ?_, ?_⟩, used_frame O, K.mono (by unfold WitnessStep.clob; decide)⟩
  · exact (VG.Proof.Bignum.scratch_bytes O (by have := v.outFit; omega_using [this]) v.outUsed).trans S.2
  · rw [memory, Mem.readW_writeW_self64]

theorem finish_prime_ok {E : Environment} (v : E.Valid) {c : Nat} {s : State} (S : FinishReady E c s) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateFinish.prime E.width) s fun t =>
      Outputs E 1 (w32 s.mem E.base 152) (Spec.Rsa.i2osp c E.length) t ∧
      MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  refine WP.mono (CandidateFinish.prime_ok S.1) fun t ⟨statusEq, bytes, used, F, K⟩ => ?_
  rw [v.length_eq] at bytes F
  refine ⟨⟨statusEq, bytes, used⟩, F.mono ?_, K.mono (by unfold WitnessStep.clob; decide)⟩
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact List.mem_append_left _ List.mem_cons_self
  · exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)

end VG.Proof.RsaKeyGen.X86.Candidate
