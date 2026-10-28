module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSizedResult
public import VerifiedGarbage.Impl.RsaKeyGen.X86.FrontRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Pointer
public import VerifiedGarbage.Proof.RsaKeyGen.X86.NearScalar
public import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Load
public import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Other
public import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Sieve
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateCloseInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishReady
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateArrays
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateShape
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.RsaKeyGen.FrameOutside
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.Offset

/-! # The candidate drawn, compared with `p` and sieved at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

theorem Input.space {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : FrontRt.Space E.base E.size E.width s := by
  have five := v.slotFit (j := 5) (by decide)
  refine ⟨I.scratch, v.width_bounds.1, v.width_bounds.2, by omega, ?_⟩
  rw [I.header 1 (by decide), v.length_eq]
  rfl

theorem Environment.Valid.stackApart {E : Environment} (v : E.Valid) :
    E.p.toNat ≤ E.base.toNat ∨ E.base.toNat + E.size + 40 ≤ E.p.toNat := by
  rcases v.workspaceStack with h | h <;> omega

theorem Input.loadIn {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) (enough : E.length ≤ E.randLength) :
    FrontRt.LoadIn E.base E.size E.width E.p E.rand s := by
  have length := v.length_eq
  refine ⟨⟨I.space v, I.stack⟩, I.rand_eq, by have := v.randFit; omega, ?_, ?_⟩
  · obtain ⟨r, mem, contains⟩ := I.memory.randRead
    refine ⟨r, mem, ?_⟩
    change (E.rand.setWidth 64 - r.base).toNat + 8 * E.width ≤ r.len
    change (E.rand.setWidth 64 - r.base).toNat + E.randLength ≤ r.len at contains
    omega
  · exact (v.readWorkspace (r := E.randRegion) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))).sub_left
      (Region.sub_prefix (by omega))

theorem load_rt_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s)
    (zeros : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0)
    (enough : E.length ≤ E.randLength) :
    WP isa VG.Impl.RsaKeyGen.X86.FrontRt.load s fun t =>
      Drawn E eBytes pBytes entropy t ∧ WorkFrame E s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx, .edx] s t := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  have outFit := v.slotFit (j := 0) (by decide)
  have length := v.length_eq
  have L := I.loadIn v enough
  have firstBytes : Spec.Rsa.bytesAt s.mem (E.rand.setWidth 64) E.length = entropy.take E.length := by
    have first := VG.Proof.RsaKeyGen.seg_bytesAt s.mem (E.rand.setWidth 64) (a := 0) (n := E.length) (k := E.randLength) (by omega)
    rw [I.memory.entropy] at first
    simpa only [VG.Proof.RsaKeyGen.seg, List.drop_zero, show BitVec.ofNat 64 0 = 0#64 from rfl,
      BitVec.add_zero] using first.symm
  refine WP.mono_syms (FrontRt.load_ok L.base.1 L.sourceFit L.source L.readable L.separate)
    fun t ⟨value, count, F, K⟩ syms => ?_
  have O : Outs E.base [(slot E.width 0, 8 * E.width), (152, 8)] s.mem t.mem :=
    VG.Proof.RsaKeyGen.frame_outs F (by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> change _ ≤ 2 ^ 64 <;> have := I.scratch.nowrap <;> omega)
  have W : WorkspaceFrame E.geometry [(slot E.width 0, 8 * E.width), (152, 8)] s.mem t.mem :=
    WorkspaceFrame.of_outs I.scratch.nowrap O
  have frame : WorkFrame E s.mem t.mem := F.sub (by
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact ⟨E.workspaceRegion, List.mem_cons_self, Offset.sub_base E.base outFit⟩
    · exact ⟨E.workspaceRegion, List.mem_cons_self, Offset.sub_base E.base (by change 152 + 8 ≤ E.size; omega)⟩)
  have J := I.keepWorkspace v K (by decide) (by decide) frame W (by
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact Nat.le_trans (by decide) (E.slotHeader 0)
    · decide) (by rw [syms])
  refine ⟨⟨J, ?_, ?_, (frame.output v).trans zeros⟩, frame, K⟩
  · rw [show 64 * E.width = 8 * E.length by omega, length, firstBytes] at value
    exact value
  · rw [length] at count
    exact count_low v count

theorem Drawn.closeIn {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) :
    FrontRt.CloseIn E.base E.size E.width E.p E.other (BitVec.ofNat 32 E.otherLength) s := by
  have length := v.length_eq
  refine ⟨⟨D.input.space v, D.input.stack⟩, D.input.other_eq, D.input.header 6 (by decide), ?_⟩
  intro nonzero
  have positive : E.otherLength ≠ 0 := by intro zero; apply nonzero; rw [zero]
  have eqLength := v.otherLength.resolve_left positive
  refine ⟨by have := v.otherFit; omega, ?_, ?_⟩
  · have read := D.input.memory.otherRead
    rw [eqLength, ← length] at read
    exact read
  · have far := v.readWorkspace (r := E.otherRegion) (List.mem_cons_of_mem _ List.mem_cons_self)
    change (⟨E.other.setWidth 64, E.otherLength⟩ : Region).Disjoint E.workspaceRegion at far
    rw [eqLength, ← length] at far
    exact far

theorem close_rt_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) :
    WP isa VG.Impl.RsaKeyGen.X86.FrontRt.close s fun t =>
      Drawn E eBytes pBytes entropy t ∧
      t.gpr .eax = Near.bit (Spec.RsaKeyGen.tooClose (8 * E.length)
        (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy)) ∧
      WorkFrame E s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  have length := v.length_eq
  have fit : 40 ≤ (s.gpr .esp).toNat := by rw [D.input.stack]; have := v.low; omega
  have C := D.closeIn v
  refine WP.mono_syms (FrontRt.close_ok C.base.1 fit (by rw [D.input.stack]; exact v.stackApart)
    C.pointer C.length C.source) fun t ⟨result, F, W, K⟩ syms => ?_
  · change t.gpr .eax = Near.bit (Spec.RsaKeyGen.tooClose (64 * E.width)
      (if BitVec.ofNat 32 E.otherLength = 0#32 then none else
        some (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (E.other.setWidth 64) (8 * E.width))))
      (val32 s.mem E.base (slot E.width 0) (2 * E.width))) at result
    rw [D.input.memory.other_choice v, show 64 * E.width = 8 * E.length by omega, D.candidate] at result
    rw [D.input.stack] at F
    have frame : WorkFrame E s.mem t.mem := VG.X86.Frame.below_mono (wr := [E.workspaceRegion]) (a := 20) F (by decide) v.low
    have headerFar : ∀ r ∈ [(slot E.width 4, 8 * E.width), (slot E.width 2, 8 * E.width), (slot E.width 3, 8 * E.width)], 256 ≤ r.1 := by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · exact E.slotHeader 4
      · exact E.slotHeader 2
      · exact E.slotHeader 3
    have I := D.input.keepWorkspace v K (by decide) (by decide) frame W
      (fun r mem => Nat.le_trans (by decide) (headerFar r mem)) (by rw [syms])
    refine ⟨⟨I, ?_, ?_, (frame.output v).trans D.zeros⟩, result, frame, K⟩
    · have same := W.val32 (d := slot E.width 0) (n := 2 * E.width) (by change slot E.width 0 + 4 * (2 * E.width) ≤ E.size; have := v.slotFit (j := 0) (by decide); omega) (by
        intro r mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl
        · exact Or.inl (by have := E.slotBefore (i := 0) (j := 4) (by decide); omega)
        · exact Or.inl (by have := E.slotBefore (i := 0) (j := 2) (by decide); omega)
        · exact Or.inl (by have := E.slotBefore (i := 0) (j := 3) (by decide); omega))
      exact same.trans D.candidate
    · have same := W.read32 (d := 152) (by change 152 + 4 ≤ E.size; omega)
        (fun r mem => Or.inl (by have := headerFar r mem; omega))
      exact (congrArg BitVec.toNat same).trans D.used

theorem Drawn.sieveIn {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) :
    FrontRt.SieveIn E.sieveGeometry (candidateValue E entropy) (allocFrame 20 s) := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  have stackFit : 40 ≤ (s.gpr .esp).toNat := by rw [D.input.stack]; have := v.low; omega
  have Sa : Scr (allocFrame 20 s) E.base E.size :=
    FilterStack.allocated_scratch D.input.scratch stackFit (by rw [D.input.stack]; exact v.stackApart)
  refine ⟨sieve_context v D, ?_, D.input.memory.symbol, ?_⟩
  · rw [allocFrame_gpr _ _ (by decide)]
    change s.gpr .edi + 256#32 = E.workspace + 256#32
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [D.input.scratch.edi_toNat]
    change (E.workspace.setWidth 64).toNat = E.workspace.toNat
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans E.workspace.isLt (by decide))]
  rw [readSrc_sc Sa (d := 4) (by omega), allocFrame_mem, (D.input.space v).len]
  rfl

theorem sieve_rt_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) :
    WP isa VG.Impl.RsaKeyGen.X86.FrontRt.sieve s fun t =>
      Drawn E eBytes pBytes entropy t ∧
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy)).toNat ∧
      WorkFrame E s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  have privateSub : (below E.sieveGeometry.sp 4).Sub (below E.p 136) := below_inner (by decide) v.low
  have workspaceFar : E.workspaceRegion.Disjoint (below E.p 136) :=
    v.stackFar E.workspaceRegion (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have tableFar : E.tableRegion.Disjoint (below E.p 136) :=
    v.stackFar E.tableRegion (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  have pointer : s.gpr .edi = E.workspace := by
    apply BitVec.eq_of_toNat_eq
    have H := D.input.scratch.edi_toNat
    change (s.gpr .edi).toNat = (E.workspace.setWidth 64).toNat at H
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans E.workspace.isLt (by decide))] at H
    exact H
  have stackFit : 40 ≤ (s.gpr .esp).toNat := by rw [D.input.stack]; have := v.low; omega
  have Sa : Scr (allocFrame 20 s) E.base E.size :=
    FilterStack.allocated_scratch D.input.scratch stackFit (by rw [D.input.stack]; exact v.stackApart)
  have lenRead : readSrc (allocFrame 20 s) (.mem (VG.Impl.Mont.X86.sc 4)) =
      some (BitVec.ofNat 32 (8 * E.sieveGeometry.w)) := by
    rw [readSrc_sc Sa (d := 4) (by omega), allocFrame_mem, (D.input.space v).len]
    rfl
  refine WP.mono_syms (FrontRt.sieve_ok v.sieve_valid (sieve_context v D)
    (by omega) lenRead (by change s.gpr .edi + 256#32 = E.workspace + 256#32; rw [pointer])
    rfl D.input.memory.symbol (by change 4 ≤ (E.p - 20#32).toNat; rw [sub_toNat (by have := v.low; omega)]; have := v.low; omega)
    ((workspaceFar.sub_left v.sieveCandidateSub).sub_right privateSub) (tableFar.sub_right privateSub)
    (candidate_large v entropy)) fun t ⟨result, F, K⟩ syms => ?_
  change t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * E.width) (candidateValue E entropy)).toNat at result
  rw [show 64 * E.width = 8 * E.length by have := v.length_eq; omega] at result
  have stackFrame : Frame [below E.p 136] s.mem t.mem := F.sub (by
    intro r mem
    simp only [Sieve.setupWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, v.sieveStackSub⟩
    · exact ⟨_, List.mem_singleton_self _, privateSub⟩)
  have frame : WorkFrame E s.mem t.mem := stackFrame.mono (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have W : WorkspaceFrame E.geometry [] s.mem t.mem := workspace_of_frame stackFrame D.input.scratch.nowrap
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact workspaceFar)
  have I := D.input.keepWorkspace v K (by decide) (by decide) frame W (by intro r mem; cases mem) (by rw [syms])
  have value := W.val32 (d := slot E.width 0) (n := 2 * E.width)
    (by have := v.slotFit (j := 0) (by decide); change slot E.width 0 + 4 * (2 * E.width) ≤ E.size; omega)
    (by intro r mem; cases mem)
  have used := W.read32 (d := 152) (by change 152 + 4 ≤ E.size; omega) (by intro r mem; cases mem)
  exact ⟨⟨I, value.trans D.candidate, (congrArg BitVec.toNat used).trans D.used, (frame.output v).trans D.zeros⟩,
    result, frame, K⟩

theorem front_rt_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s)
    (zeros : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0)
    (enough : E.length ≤ E.randLength) :
    WP isa VG.Impl.RsaKeyGen.X86.FrontRt.code s fun t =>
      FrontOutputs E eBytes pBytes entropy t ∧ MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.FrontRt.code
  refine WP.seq (WP.mono (load_rt_ok v I zeros enough) fun a ⟨D, F₀, K₀⟩ => ?_)
  have F₀' : MutableFrame E s.mem a.mem := F₀.mutable
  have K₀' : Keeps WitnessStep.clob s a := K₀.mono (by unfold WitnessStep.clob; decide)
  refine WP.seq (WP.mono (close_rt_ok v D) fun a' ⟨Da, flag, F, K⟩ => ?_)
  refine WP.seq (WP.mono (cmp_bool flag) fun b ⟨B, _, cond⟩ => ?_)
  have Db := Da.keepMem v B.mem (B.keeps []) (by decide) (by decide) B.syms
  have Fb : MutableFrame E s.mem b.mem := by rw [B.mem]; exact F₀'.trans F.mutable
  have Kb : Keeps WitnessStep.clob s b :=
    (K₀'.trans (K.mono (by unfold WitnessStep.clob; decide))).widen (B.keeps [])
  cases close : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy)
  · refine WP.ite false (by rw [cond, close]) (fun bad => nomatch bad) (fun _ => ?_)
    refine WP.seq (WP.mono (sieve_rt_ok v Db) fun c ⟨Dc, flag', F', K'⟩ => ?_)
    refine WP.seq (WP.mono (cmp_bool flag') fun d ⟨Bd, _, cond'⟩ => ?_)
    have Dd := Dc.keepMem v Bd.mem (Bd.keeps []) (by decide) (by decide) Bd.syms
    have Fd : MutableFrame E s.mem d.mem := by rw [Bd.mem]; exact Fb.trans F'.mutable
    have Kd : Keeps WitnessStep.clob s d := (Kb.trans (K'.mono (by unfold WitnessStep.clob; decide))).widen (Bd.keeps [])
    cases composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy)
    · refine WP.ite false (by rw [cond', composite]) (fun bad => nomatch bad) (fun _ => ?_)
      refine wp_movS rfl fun t T _ => WP.block_nil ?_
      refine ⟨?_, by rw [T.mem]; exact Fd, Kd.widen T.keeps⟩
      simp only [FrontOutputs, close, composite, Bool.false_eq_true, ↓reduceIte]
      exact ⟨Dd.keepMem v T.mem T.keeps (by decide) (by decide) T.syms, T.gpr⟩
    · refine WP.ite true (by rw [cond', composite]) (fun _ => ?_) (fun bad => nomatch bad)
      refine WP.mono (finish_used_ok (status := 3) v (Dd.finishReady v)) fun t ⟨output, Ft, Kt⟩ => ?_
      rw [Dd.used] at output
      exact ⟨by simpa only [FrontOutputs, close, composite, Bool.false_eq_true, ↓reduceIte] using output,
        Fd.trans Ft, Kd.trans Kt⟩
  · refine WP.ite true (by rw [cond, close]) (fun _ => ?_) (fun bad => nomatch bad)
    refine WP.mono (finish_used_ok (status := 2) v (Db.finishReady v)) fun t ⟨output, Ft, Kt⟩ => ?_
    rw [Db.used] at output
    exact ⟨by simpa only [FrontOutputs, close, ↓reduceIte] using output, Fb.trans Ft, Kb.trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Candidate
