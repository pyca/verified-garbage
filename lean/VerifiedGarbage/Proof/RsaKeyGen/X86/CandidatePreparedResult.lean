module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinStep
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishReady
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Pointer
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateStack
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrepareInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.MrExponentRt.Prepared
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Loop
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateShape
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Array
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! ### `RsaKeyGen.X86.CandidateTestInput`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.CandidateNoSpCode`, which this module and modules that import it used -/

section

/-! # The complete native candidate dispatcher preserves ESP inside its frames -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateNoSp
open VG VG.X86 VG.Impl.RsaKeyGen.X86
open VG.Impl.Bignum.X86.PublicContext

theorem general : NoSp ExponentRt.general := by
  apply NoSp.of_all
  simp only [ExponentRt.general, Code.allInstrs, checked VG.Proof.RsaKeyGen.X86.ExponentRt.array_noSp]
  rfl

theorem exponentRt : NoSp ExponentRt.code := by
  apply NoSp.of_all
  simp only [ExponentRt.code, ExponentRt.filter, Code.allInstrs, checked general]
  rfl

theorem mrExponent : NoSp MrExponentRt.code := NoSp.of_all (by rfl)

theorem r2Rt {mont : Prog isa} (Hm : NoSp mont) (montName : String) :
    NoSp (PrepareRt.r2 montName mont) := by
  unfold PrepareRt.r2
  refine sequence (sequence (NoSp.of_all (by rfl)) (sequence (NoSp.of_all (by rfl)) ?_)) (NoSp.of_all (by rfl))
  have H := mulY Hm montName 6
  change NoSp (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ _)))))
  exact sequence H (sequence H (sequence H (sequence H (sequence H H))))

theorem constantsRt {mont : Prog isa} (Hm : NoSp mont) (montName : String) :
    NoSp (PrepareRt.constants montName mont) := by
  unfold PrepareRt.constants
  exact sequence (NoSp.of_all (by rfl))
    (sequence (mulY Hm montName 4) (sequence (NoSp.of_all (by rfl)) (NoSp.of_all (by rfl))))

theorem prepareHead {mont : Prog isa} (Hm : NoSp mont) (montName : String) :
    NoSp (Candidate.prepareHead montName mont) :=
  sequence (r2Rt Hm montName) (constantsRt Hm montName)

theorem prepared {mont : Prog isa} (Hm : NoSp mont) (montName : String) :
    NoSp (Candidate.prepared montName mont) :=
  sequence (NoSp.of_all (by rfl)) (sequence (prepareHead Hm montName) mrExponent)

theorem witnessRound {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round) (montName roundName : String) :
    NoSp (WitnessRt.round montName mont roundName round) := by
  unfold WitnessRt.round WitnessMont.code
  exact sequence (NoSp.of_all (by rfl)) (sequence (NoSp.of_all (by rfl))
    (sequence (sequence (mulY Hm montName 4) (NoSp.of_all (by rfl))) (roundCall Hr roundName)))

theorem witnessBody {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round) (montName roundName : String) :
    NoSp (WitnessRt.body montName mont roundName round) := by
  unfold WitnessRt.body
  exact sequence (NoSp.of_all (by rfl)) (sequence (witnessRound Hm Hr montName roundName) (NoSp.of_all (by rfl)))

theorem witnesses {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round) (montName roundName : String) :
    NoSp (WitnessRt.code montName mont roundName round) := by
  apply NoSp.of_all
  simp only [WitnessRt.code, WitnessRt.step, Code.allInstrs, checked (witnessBody Hm Hr montName roundName)]
  rfl

theorem testBody {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round) (montName roundName : String) :
    NoSp (Candidate.testBody montName mont roundName round) :=
  sequence (prepared Hm montName) (witnesses Hm Hr montName roundName)

theorem tested {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round) (montName roundName : String) :
    NoSp (Candidate.tested montName mont roundName round) := by
  apply NoSp.of_all
  simp only [Candidate.tested, CandidateFrame.code, Code.allInstrs, checked (testBody Hm Hr montName roundName)]
  rfl

theorem exponentCheck {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (montName roundName : String) : NoSp (Candidate.exponentCheck montName mont roundName round) := by
  apply NoSp.of_all
  simp only [Candidate.exponentCheck, Code.allInstrs, checked exponentRt, checked (tested Hm Hr montName roundName)]
  rfl

theorem front : NoSp VG.Impl.RsaKeyGen.X86.FrontRt.code := by
  apply NoSp.of_all
  rfl

theorem available {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (montName roundName : String) : NoSp (Candidate.available montName mont roundName round) := by
  apply NoSp.of_all
  simp only [Candidate.available, Code.allInstrs, checked front,
    checked (exponentCheck Hm Hr montName roundName)]
  rfl

theorem body {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (montName roundName : String) : NoSp (Candidate.body montName mont roundName round) := by
  apply NoSp.of_all
  simp only [Candidate.body, Code.allInstrs, checked (available Hm Hr montName roundName)]
  rfl

theorem code {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (montName roundName : String) : NoSp (Candidate.code montName mont roundName round) := by
  apply NoSp.of_all
  simp only [Candidate.code, Code.allInstrs, checked (body Hm Hr montName roundName)]
  rfl

end VG.Proof.RsaKeyGen.X86.CandidateNoSp

end

end

/-! ### `RsaKeyGen.X86.MrExponentRt.Test`, which only this module used -/

section

/-! # Preparation with the run-time exponent, then the witnesses, in the shared private frame -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MrExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen

/-- Preparation and the witnesses: `CandidateTest.core_ok` with the exponent
at the run-time width. -/
theorem body_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (width : 4 ≤ P.g.w) (bound : P.g.w ≤ 64)
    (seed : P.seed = 64 * P.g.w - 1) (checks : P.checks = VG.Impl.RsaKeyGen.X86.WitnessChecks.checks P.g.w)
    (bytes : P.bytes = 8 * P.g.w) (words : P.words = 2 * P.g.w) {s : State}
    (S : Prepare.Input P.g P.candidate P.capacity P.p s P.seed)
    (readable : InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen)
    (entropy : Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy)
    (randPtr : s.mem.readW (off P.g.W 28) 32 = P.rand)
    (randLength : w32 s.mem P.g.W 32 = P.randLen)
    (used : w32 s.mem P.g.W 152 = P.start) (enough : P.start ≤ P.randLen)
    (len : s.mem.readW (off P.g.W 4) 32 = BitVec.ofNat 32 (8 * P.g.w)) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.testBody montName mont roundName round) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ MillerRabinLoop.Result P t ∧
      WorkspaceFrame P.g (CandidateTest.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.testBody
  refine WP.seq (WP.mono (prepared_ok montVerified montNoSp montStack v width bound seed
    ⟨S, readable, entropy, randPtr, randLength, used⟩ len) fun a ⟨A, Wa, Fa, Ka⟩ => ?_)
  refine WP.mono (WitnessRt.codeRt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack
    v ⟨bytes, words, checks⟩ A.prepared A.readable A.entropy A.randPtr A.randLength A.used enough)
    fun t ⟨T, result, Wt, Ft, Kt⟩ => ?_
  refine ⟨T, result, ?_, (VG.X86.Frame.below_mono Fa (by decide) v.low).trans Ft, ?_⟩
  · exact (Wa.mono (fun _ mem => List.mem_append_left _ mem)).trans
      (Wt.mono (fun _ mem => List.mem_append_right _ mem))
  · exact (Ka.mono (by unfold Prepare.clob WitnessStep.clob; decide)).trans Kt

theorem tested_frame_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (width : 4 ≤ P.g.w) (bound : P.g.w ≤ 64)
    (seed : P.seed = 64 * P.g.w - 1) (checks : P.checks = VG.Impl.RsaKeyGen.X86.WitnessChecks.checks P.g.w)
    (bytes : P.bytes = 8 * P.g.w) (words : P.words = 2 * P.g.w) {s : State}
    (S : Scr s P.g.W P.g.L) (capacity : w32 s.mem P.g.W 40 = P.capacity)
    (privateEq : P.p = CandidateFrame.privateSp s)
    (candidate : val32 s.mem P.g.W (P.g.array 0) P.g.words = P.candidate)
    (minusOne : val32 s.mem P.g.W (P.g.array 5) P.g.words = P.candidate - 1)
    (top : 2 ^ P.seed ≤ P.candidate)
    (readable : InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen)
    (entropy : Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy)
    (randPtr : s.mem.readW (off P.g.W 28) 32 = P.rand)
    (randLength : w32 s.mem P.g.W 32 = P.randLen)
    (used : w32 s.mem P.g.W 152 = P.start) (enough : P.start ≤ P.randLen)
    (len : s.mem.readW (off P.g.W 4) 32 = BitVec.ofNat 32 (8 * P.g.w))
    (fit : 136 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ P.g.W.toNat ∨ P.g.W.toNat + P.g.L + 136 ≤ (s.gpr .esp).toNat)
    (randPrivateFar : (⟨P.rand.setWidth 64, P.randLen⟩ : Region).Disjoint (below (s.gpr .esp) 28)) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateFrame.code
      (VG.Impl.RsaKeyGen.X86.Candidate.testBody montName mont roundName round)) s fun t =>
      val32 t.mem P.g.W (P.g.array 0) P.g.words = P.candidate ∧ MillerRabinLoop.Result P t ∧
      WorkspaceFrame P.g (CandidateTest.ranges P.g) s.mem t.mem ∧
      Frame [⟨P.g.W, P.g.L⟩, below (s.gpr .esp) 136] s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  refine CandidateFrame.code_full_ok (CandidateNoSp.testBody montNoSp roundNoSp montName roundName) S
    v.geometry.headerFit capacity fit separate ?_
  intro a Sa Ca _ Fa Ka
  have workspaceFar : (⟨P.g.W, P.g.L⟩ : Region).Disjoint (below (s.gpr .esp) 28) :=
    FilterStack.allocated_apart (by omega_using [fit]) S.nowrap
      (by rcases separate with h | h; exact Or.inl h; exact Or.inr (by omega_using [h]))
  have Wa : WorkspaceFrame P.g [] s.mem a.mem := by
    intro i index _
    exact Fa.bytes (R := ⟨P.g.W, P.g.L⟩)
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact workspaceFar)
      (by change P.g.L ≤ 2 ^ 64; have := S.nowrap; omega_using [this]) index
  have I : Prepare.Input P.g P.candidate P.capacity P.p a P.seed := by
    refine ⟨Sa, ?_, ?_, ?_, v.odd, by have := v.large; omega_using [this], top⟩
    · rw [privateEq]; exact Ca
    · rw [Wa.val32 (v.geometry.arrayFit (by decide)) (by intro r mem; nomatch mem)]; exact candidate
    · rw [Wa.val32 (v.geometry.arrayFit (by decide)) (by intro r mem; nomatch mem)]; exact minusOne
  have entropyA : Spec.Rsa.bytesAt a.mem (P.rand.setWidth 64) P.randLen = P.entropy := by
    rw [frame_bytesAt Fa (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact randPrivateFar)
      (by have := v.randLenFit; omega_using [this])]
    exact entropy
  refine WP.mono (body_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v width bound seed checks
    bytes words I
    (by
      rw [Ka.2.1, Ka.2.2]
      obtain ⟨r, mem, contains⟩ := readable
      refine ⟨r, ?_, contains⟩
      rcases List.mem_append.mp mem with mem | mem
      · exact List.mem_append_left _ mem
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ mem)) entropyA
    (by rw [Wa.read32 (by have := v.geometry.headerFit; omega_using [this]) (by intro r mem; nomatch mem)]; exact randPtr)
    (by rw [w32, Wa.read32 (by have := v.geometry.headerFit; omega_using [this]) (by intro r mem; nomatch mem)]; exact randLength)
    (by rw [w32, Wa.read32 (by have := v.geometry.headerFit; omega_using [this]) (by intro r mem; nomatch mem)]; exact used) enough
    (by rw [Wa.read32 (by have := v.geometry.headerFit; omega_using [this]) (by intro r mem; nomatch mem)]; exact len))
    fun t ⟨T, result, Wt, Ft, Kt⟩ => ?_
  have outerFrame : Frame [⟨P.g.W, P.g.L⟩, below (s.gpr .esp) 136] s.mem t.mem := by
    have first : Frame [⟨P.g.W, P.g.L⟩, below (s.gpr .esp) 136] s.mem a.mem :=
      Fa.sub (by
        intro r mem; obtain rfl := List.mem_singleton.mp mem
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), below_sub (by decide) fit⟩)
    have second : Frame [⟨P.g.W, P.g.L⟩, below (s.gpr .esp) 136] a.mem t.mem :=
      Ft.sub (by
        intro r mem
        simp only [List.mem_append, List.mem_singleton] at mem
        rcases mem with rfl | rfl
        · exact ⟨_, List.mem_cons_self, fun _ H => H⟩
        · refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
          rw [privateEq]
          exact below_inner (by decide) fit)
    exact first.trans second
  refine ⟨T.ready.modulus.candidate, ?_, (Wa.mono (by intro r mem; nomatch mem)).trans Wt,
    outerFrame, FilterStack.freed_keeps ((Ka.mono (by unfold WitnessStep.clob; decide)).trans Kt) (by unfold WitnessStep.clob; decide)⟩
  change MillerRabinLoop.Result P t
  exact result

end VG.Proof.RsaKeyGen.X86.MrExponentRt

end

end


/-! # A drawn candidate enters the complete prepared test with its original entropy snapshot -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

theorem test_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s)
    (minusOne : val32 s.mem E.base (slot E.width 5) (2 * E.width) = candidateValue E entropy - 1)
    (enough : E.length ≤ E.randLength) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateFrame.code
      (VG.Impl.RsaKeyGen.X86.Candidate.testBody montName mont roundName round)) s fun t =>
      val32 t.mem E.base (slot E.width 0) (2 * E.width) = candidateValue E entropy ∧
      MillerRabinLoop.Result (E.parameters entropy) t ∧
      WorkspaceFrame E.geometry (CandidateTest.ranges E.geometry) s.mem t.mem ∧
      WorkFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  have top : 2 ^ (64 * E.width - 1) ≤ candidateValue E entropy := by
    have lower := (candidate_shape v entropy).2.1
    have width := v.width_bounds.1
    have eqPower : 2 ^ (64 * E.width - 1) = 2 ^ (64 * E.width - 2) * 2 := by
      rw [← Nat.pow_succ]
      congr 1
      omega_using [width]
    rw [eqPower]
    omega_using [lower]
  refine WP.mono (MrExponentRt.tested_frame_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack
    (v.parameters_valid entropy D.input.memory.entropyLength) v.width_bounds.1 v.width_bounds.2 rfl rfl rfl rfl
    D.input.scratch (D.input.capacity_eq v)
    (by change E.p - 28#32 = s.gpr .esp - 28#32; rw [D.input.stack])
    (by rw [← Prepared.slot_eq]; exact D.candidate) (by rw [← Prepared.slot_eq]; exact minusOne)
    top D.input.memory.randRead D.input.memory.entropy D.input.rand_eq (D.input.randLength_eq v)
    (by change w32 s.mem E.base 152 = 8 * E.width; rw [D.used, v.length_eq])
    (by change 8 * E.width ≤ E.randLength; rw [v.length_eq]; exact enough)
    (by
      change s.mem.readW (off E.base (4 * 1)) 32 = BitVec.ofNat 32 (8 * E.width)
      rw [D.input.header 1 (by decide)]
      change BitVec.ofNat 32 E.length = _
      rw [v.length_eq])
    (by rw [D.input.stack]; exact v.low) (by rw [D.input.stack]; exact v.workspaceStack)
    (by
      rw [D.input.stack]
      exact (v.stackFar E.randRegion (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))).sub_right (below_sub (by decide) v.low)))
    fun t ⟨value, result, W, F, K⟩ => ?_
  rw [D.input.stack] at F
  refine ⟨?_, result, W, F, K⟩
  rw [← Prepared.slot_eq] at value
  exact value

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! # Prepared testing and finish implement exactly the complete primality result -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateFinishResult.lean`, which only this module imported.
section

/-! # The prepared status selects exactly the matching native finish path -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86

def ResultOutputs (E : Environment) (c tag count : Nat) (s : State) : Prop :=
  Outputs E tag (if tag = 0 then 0 else count)
    (if tag = 1 then Spec.Rsa.i2osp c E.length else List.replicate E.length 0) s

theorem finish_result_ok {E : Environment} (v : E.Valid) {c tag : Nat} {s : State}
    (S : FinishReady E c s) (tags : tag = 0 ∨ tag = 1 ∨ tag = 3)
    (status : w32 s.mem E.base 168 = tag) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateFinish.mrResult E.width) s fun t =>
      ResultOutputs E c tag (w32 s.mem E.base 152) t ∧ MutableFrame E s.mem t.mem ∧
      Keeps WitnessStep.clob s t := by
  have tagBound : tag < 2 ^ 32 := by omega_using [tags]
  have statusWord : s.mem.readW (off E.base 168) 32 = BitVec.ofNat 32 tag := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt tagBound]
    exact status
  have header : 172 ≤ E.size := by have := S.1.header; have := v.geometry.headerFit; change 256 ≤ E.size at this; omega_using [this]
  unfold VG.Impl.RsaKeyGen.X86.CandidateFinish.mrResult
  refine WP.seq (wp_movS (readSrc_sc S.1.scratch (d := 168) (by omega_using [header])) fun a A _ =>
    wp_cmpS rfl fun b B Z => WP.block_nil ?_)
  have M : b.mem = s.mem := B.mem.trans A.mem
  have K : Keeps [.eax] s b := A.keeps.widen (B.keeps [])
  have Sb := S.keepMem M K (by decide) (by decide)
  have value : b.gpr .eax = BitVec.ofNat 32 tag := by rw [(B.keeps []).1 .eax (by decide), A.gpr, statusWord]
  have condition : isa.eval .e b = some (decide (tag = 1)) := by
    change b.zf = _
    rw [Z, A.gpr, statusWord]
    rcases tags with rfl | rfl | rfl <;> decide
  by_cases accepted : tag = 1
  · rw [accepted]
    refine WP.ite true (by rw [condition, decide_eq_true accepted]) (fun _ => ?_) (fun bad => nomatch bad)
    refine WP.mono (finish_prime_ok v Sb) fun t ⟨output, F, Kt⟩ => ?_
    rw [M] at output F
    exact ⟨output, F, (K.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩
  · refine WP.ite false (by rw [condition, decide_eq_false accepted]) (fun bad => nomatch bad) (fun _ => ?_)
    refine WP.seq (wp_cmpS rfl fun d D Z0 => WP.block_nil ?_)
    have Md : d.mem = s.mem := D.mem.trans M
    have Kd : Keeps [.eax] s d := K.widen (D.keeps [])
    have Sd := S.keepMem Md Kd (by decide) (by decide)
    have condition0 : isa.eval .e d = some (decide (tag = 0)) := by
      change d.zf = _
      rw [Z0, value]
      rcases tags with rfl | rfl | rfl <;> decide
    by_cases exhausted : tag = 0
    · rw [exhausted]
      refine WP.ite true (by rw [condition0, decide_eq_true exhausted]) (fun _ => ?_) (fun bad => nomatch bad)
      refine WP.mono (finish_none_ok v Sd) fun t ⟨output, F, Kt⟩ => ?_
      rw [Md] at F
      exact ⟨output, F, (Kd.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩
    · have rejected : tag = 3 := by omega_using [tags, accepted, exhausted]
      rw [rejected]
      refine WP.ite false (by rw [condition0, decide_eq_false exhausted]) (fun bad => nomatch bad) (fun _ => ?_)
      refine WP.mono (finish_used_ok (status := 3) v Sd) fun t ⟨output, F, Kt⟩ => ?_
      rw [Md] at output F
      exact ⟨output, F, (Kd.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

def PrimalityOutputs (E : Environment) (c : Nat) (entropy : List Byte) (s : State) : Prop :=
  match Spec.RsaKeyGen.primalityTest c (entropy.drop E.length) with
  | none => Outputs E 0 0 (List.replicate E.length 0) s
  | some (prime, rest) => Outputs E (if prime then 1 else 3) (entropy.length - rest.length)
      (if prime then Spec.Rsa.i2osp c E.length else List.replicate E.length 0) s

/-- Miller–Rabin's result is the same code at every width. -/
theorem mrResult_zero (w : Nat) :
    VG.Impl.RsaKeyGen.X86.CandidateFinish.mrResult 0 = VG.Impl.RsaKeyGen.X86.CandidateFinish.mrResult w := by
  simp only [VG.Impl.RsaKeyGen.X86.CandidateFinish.mrResult, VG.Impl.RsaKeyGen.X86.CandidateFinish.prime,
    VG.Proof.RsaKeyGen.X86.ExponentRt.slot0_eq]

/-- Preparation with the exponent at the run-time width, the witnesses, and
the result. -/
theorem tested_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s)
    (minusOne : val32 s.mem E.base (slot E.width 5) (2 * E.width) = candidateValue E entropy - 1)
    (enough : E.length ≤ E.randLength) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.tested montName mont roundName round) s fun t =>
      PrimalityOutputs E (candidateValue E entropy) entropy t ∧ MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.tested
  rw [mrResult_zero E.width]
  refine WP.seq (WP.mono (test_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v D minusOne enough)
    fun a ⟨value, result, W, F, K⟩ => ?_)
  have ready := D.finishReady_after_test v value W F K
  have frame : MutableFrame E s.mem a.mem := F.mutable
  rw [MillerRabinLoop.Result, v.test_eq] at result
  change (match Spec.RsaKeyGen.primalityTest (candidateValue E entropy) (entropy.drop (8 * E.width)) with
    | none => w32 a.mem E.base 168 = 0
    | some (prime, rest) => w32 a.mem E.base 168 = (if prime then 1 else 3) ∧
        w32 a.mem E.base 152 = entropy.length - rest.length) at result
  rw [v.length_eq] at result
  cases test : Spec.RsaKeyGen.primalityTest (candidateValue E entropy) (entropy.drop E.length) with
  | none =>
    rw [test] at result
    refine WP.mono (finish_result_ok v ready (Or.inl rfl) result) fun t ⟨output, Ft, Kt⟩ => ?_
    exact ⟨by simpa [PrimalityOutputs, test, ResultOutputs] using output, frame.trans Ft, K.trans Kt⟩
  | some pr =>
    obtain ⟨prime, rest⟩ := pr
    rw [test] at result
    cases prime
    · refine WP.mono (finish_result_ok v ready (Or.inr (Or.inr rfl)) result.1) fun t ⟨output, Ft, Kt⟩ => ?_
      rw [ResultOutputs, result.2] at output
      exact ⟨by simpa [PrimalityOutputs, test, ResultOutputs] using output, frame.trans Ft, K.trans Kt⟩
    · refine WP.mono (finish_result_ok v ready (Or.inr (Or.inl rfl)) result.1) fun t ⟨output, Ft, Kt⟩ => ?_
      rw [ResultOutputs, result.2] at output
      exact ⟨by simpa [PrimalityOutputs, test, ResultOutputs] using output, frame.trans Ft, K.trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Candidate
