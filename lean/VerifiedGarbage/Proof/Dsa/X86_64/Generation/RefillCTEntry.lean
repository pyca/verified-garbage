module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCTLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillEntry
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillFinish
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.Layout
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCTLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillEntry
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillFinish
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryState
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
meta import VerifiedGarbage.Proof.Dsa.Generation.Memory
meta import VerifiedGarbage.Proof.Dsa.Generation.Layout
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.Registration

/-! # Timing of the refillable-tape search's entry

The controller's public state on entry (`loopPublic`) is a function of the
arguments, the stack pointer, `rand` and `state[0]`, which the contract
makes public; the entry's stores are at fixed offsets of the stack pointer
and at `state`, a public argument. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Impl.Bignum.X86_64 (at0)
open Refill (RefillABI inOut inUsed inRand inScr inState inArgs low refillBase refillGeometry refillContext randTape)

/-- The writable regions in the attempts' frame. -/
def refillWs (s : State) : List Region := Refill.ctlRegion (refillBase s) :: ⟨off (low s) 520, 48⟩ :: s.wr

def refillWr (s : State) : List Region := ⟨refillBase s, frameBytes⟩ :: refillWs s

section
variable {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀)
include h

theorem refillWr_eq : refillWr s₀ = [⟨refillBase s₀, frameBytes⟩, Refill.ctlRegion (refillBase s₀),
    ⟨off (low s₀) 520, 48⟩, inOut s₀, inUsed s₀, inScr s₀, inState s₀] := by
  simp only [refillWr, refillWs, h.wr]

theorem refillWr_pairwise : (refillWr s₀).Pairwise Region.Disjoint := by
  rw [refillWr_eq h]
  have fs : (⟨refillBase s₀, frameBytes⟩ : Region).Disjoint ⟨off (low s₀) 520, 48⟩ :=
    Offset.disjoint (low s₀) (d := 192) (n := 296) (e := 520) (k := 48) (by decide) (by decide) (by
      have := Refill.low_toNat h; have := (s₀.gpr .rsp).isLt; have : 568 ≤ (s₀.gpr .rsp).toNat := h.stackLower
      omega)
  have cs : (Refill.ctlRegion (refillBase s₀)).Disjoint ⟨off (low s₀) 520, 48⟩ := by
    rw [Refill.ctlRegion_eq]
    exact Offset.disjoint (low s₀) (d := 488) (n := 32) (e := 520) (k := 48) (by decide) (by decide) (by
      have := Refill.low_toNat h; have := (s₀.gpr .rsp).isLt; have : 568 ≤ (s₀.gpr .rsp).toNat := h.stackLower
      omega)
  have ab := fun {r : Region} (hr : r = inOut s₀ ∨ r = inUsed s₀ ∨ r = inRand s₀ ∨ r = inScr s₀ ∨ r = inState s₀ ∨
      r = inArgs s₀) => h.frame_disjoint hr
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true]
  refine ⟨⟨(Refill.ctl_frame _).symm, fs, (ab (by simp) _ (by simp)).symm, (ab (by simp) _ (by simp)).symm,
    (ab (by simp) _ (by simp)).symm, (ab (by simp) _ (by simp)).symm⟩,
    ⟨cs, (ab (by simp) _ (by simp)).symm, (ab (by simp) _ (by simp)).symm, (ab (by simp) _ (by simp)).symm,
      (ab (by simp) _ (by simp)).symm⟩,
    ⟨(ab (by simp) _ (by simp)).symm, (ab (by simp) _ (by simp)).symm, (ab (by simp) _ (by simp)).symm,
      (ab (by simp) _ (by simp)).symm⟩,
    ⟨h.outUsed, h.outScr, h.outState⟩, ⟨h.usedScr, h.usedState⟩, h.scrState, fun _ hh => hh.elim⟩

theorem refillWr_lengths : ∀ r ∈ refillWr s₀, r.len ≤ 2 ^ 64 := by
  rw [refillWr_eq h]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show 296 ≤ 2 ^ 64; decide
  · show 32 ≤ 2 ^ 64; decide
  · show 48 ≤ 2 ^ 64; decide
  · exact Nat.le_of_lt (s₀.gpr .rsi).isLt
  · show 8 ≤ 2 ^ 64; decide
  · show (stackArg s₀ 0).toNat * 8 ≤ 2 ^ 64
    have := h.scrBound; omega
  · show 32 ≤ 2 ^ 64; decide

theorem refill_header : PrimeHeaderLayout (refillGeometry h).B (refillWr s₀) := by
  refine Or.inr ⟨_, _, _, _, _, _, (stackArg s₀ 0).toNat * 8, refillWr_eq h, ?_, refillWr_pairwise h,
    refillWr_lengths h⟩
  have hs := h.scratchSize
  have hw : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384 := by
    have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega
  have : 28928 ≤ VG.Impl.Dsa.Generation.Layout.usedBytes pBytes := by
    rcases hw with rfl | rfl | rfl <;> decide
  omega

theorem refill_ctlOK : CtlOK (refillContext h) (s₀.gpr .rdx) (stackArg s₀ 1) :=
  ⟨Refill.ctl_changed h, Refill.rand_ctl h, Refill.rand_ctl h, h.ctl_hash, Refill.refillBase_bound h⟩

theorem refill_endOK : EndOK (refillContext h) (s₀.gpr .rdx) (stackArg s₀ 1) (refillWr s₀) := by
  have hrl : (⟨(randTape h).ptr, (randTape h).bytes.length⟩ : Region) = inRand s₀ := by
    simp only [randTape, bytesAt_length, inRand]
  have st := Refill.written_regions h (inState s₀) (by simp)
  have us := Refill.written_regions h (inUsed s₀) (by simp)
  have below : below (refillContext h).geo.F 192 = ⟨off (low s₀) 0, 192⟩ := by
    change below (refillBase s₀) 192 = _
    rw [Refill.refillBase_below]; simp [off]
  have changed : ∀ {r : Region}, (r = inUsed s₀ ∨ r = inState s₀) → r.Disjoint ⟨s₀.gpr .r9,
      VG.Impl.Dsa.Generation.Layout.usedBytes pBytes⟩ → ∀ q ∈ (refillContext h).changed, r.Disjoint q := by
    intro r hr ha q hq
    simp only [GenerationContext.changed, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact ha
    · exact h.frame_disjoint (r := r) (by rcases hr with rfl | rfl <;> simp) _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · rw [below]; exact h.stack_disjoint (d := 0) (n := 192) (by decide) (by rcases hr with rfl | rfl <;> simp) |>.symm
  refine
    { stIn := by rw [refillWr_eq h]; simp [inState]
      usIn := by rw [refillWr_eq h]; simp [inUsed]
      stBound := h.stateBound
      usBound := h.usedBound
      stChanged := changed (Or.inr rfl) st.2.2.2.2
      usChanged := changed (Or.inl rfl) us.2.2.2.2
      stRand := st.2.2.1.symm
      usRand := us.2.2.1.symm
      stSeeds := st.2.2.1.symm
      usSeeds := us.2.2.1.symm
      stHash := st.2.1
      usHash := us.2.1
      stCtl := st.2.2.2.1
      usCtl := us.2.2.2.1
      out := Refill.refillOutputPlan h
      outIn := ?_
      lenBound := ?_ }
  · have outLen : 2 * pBytes + Spec.Dsa.generationQLen pBytes = (s₀.gpr .rsi).toNat := by
      rw [h.outLength, h.width]
    change (⟨s₀.gpr .rdi, 2 * pBytes + Spec.Dsa.generationQLen pBytes⟩ : Region) ∈ refillWr s₀
    rw [outLen, refillWr_eq h]; simp [inOut]
  · change (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rcx) (s₀.gpr .r8).toNat).length < 2 ^ 32
    rw [bytesAt_length]
    have := h.randLength
    have hw : Refill.refillPLen s₀ ≤ 384 := by
      have := h.valid; unfold Spec.Dsa.generationPLenValid at this; simp at this; omega
    unfold Spec.Dsa.parameterEntropy at this
    omega

/-- The controller's public state on entry. -/
def loopPublic : LoopPublic where
  ctx := refillContext h
  hs := (refillContext h).hs
  start := 0
  left := (s₀.mem.readW (stackArg s₀ 1) 64).toNat
  c0 := s₀.gpr .rdx
  c1 := stackArg s₀ 1
  ws := refillWs s₀
  wr := refillWr s₀
  header := refill_header h
  startBound := Nat.zero_le _
  leftBound := h.seeds
  hsIn := by
    intro a ha
    simp [Region.Contains, refillContext, GenerationTape.slice] at ha
  ok := refill_ctlOK h
  ends := refill_endOK h

end

/-- A state the body starts from, with the controller's public state on entry `P`. -/
def RefillInit (pBytes : Nat) (P : LoopPublic) (u : State) : Prop :=
  ∃ (s₀ : State) (h : RefillABI pBytes s₀), Refill.RefillAllocated h u ∧ u.wr = refillWr s₀ ∧ loopPublic h = P

theorem entry_ready {pBytes qBytes : Nat} (hq : qBytes = Spec.Dsa.generationQLen pBytes) {P : LoopPublic}
    {u : State} (hi : RefillInit pBytes P u) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.Refill.entryHeader pBytes qBytes ++
      Impl.Dsa.X86_64.Generation.entryDerived)) u (LoopBefore 6 pBytes qBytes P) := by
  obtain ⟨s₀, h, a, hwr, rfl⟩ := hi
  refine WP.mono (Refill.entry_ok h a hq) fun v ⟨W, hm, h16, h10, c0, c1, c2, _, kV⟩ => ?_
  have wv : v.wr = refillWr s₀ := kV.2.2.trans hwr
  have hm' : GenerationMemory ((refillContext h).withHs (refillContext h).hs) W v := by
    rw [Refill.withHs_self]; exact hm
  refine ⟨⟨W, hm', by rw [h16]; rfl, h10⟩,
    ⟨c0, c1, ?_, kV.2.2 ▸ a.ctl⟩,
    ⟨(kV.gpr (by decide)).trans a.rsp, wv, ?_, refillWr_pairwise h,
      fun r hr => refillWr_lengths h r (List.mem_cons_of_mem _ hr)⟩, wv, rfl, hq.symm⟩
  · show Refill.ctlWord v.mem (refillBase s₀) 2 = BitVec.ofNat 64 (s₀.mem.readW (stackArg s₀ 1) 64).toNat
    rw [c2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · show (refillWs s₀).length = 6
    simp only [refillWs, h.wr, List.length_cons, List.length_nil]

def EntryLoaded (P : LoopPublic) (t : State) : Prop :=
  t.gpr .rsp = P.ctx.geo.F ∧ t.gpr .rax = P.c1

theorem entryFirst_ready {pBytes qBytes : Nat} {P : LoopPublic} {u : State} (hi : RefillInit pBytes P u)
    (hp : pBytes < 2 ^ 31) (hq : qBytes < 2 ^ 31) :
    WP isa (.block (Refill.headerA pBytes qBytes ++ ([.mov .rax (.mem (sp (Impl.Dsa.X86_64.Generation.Refill.frameBytes + 32 + 48 + 16))),
      .store (Impl.Dsa.X86_64.Generation.Refill.ctl 1) .rax] : List Instr))) u (EntryLoaded P) := by
  obtain ⟨s₀, h, a, _, rfl⟩ := hi
  have hb := Refill.refillBase_bound h
  apply WP.block_append
  refine WP.mono (Refill.headerA_ok a.rsp a.frame a.ctl hb hp hq) fun t ⟨hm, kt⟩ => ?_
  have fA : Frame [⟨refillBase s₀, frameBytes⟩, Refill.ctlRegion (refillBase s₀)] u.mem t.mem := by
    rw [hm]; exact Refill.chainA_frame _ _ _ _ _
  have argsC : (inArgs s₀).Contains (off (refillBase s₀) 392) 8 := by
    rw [Refill.refillBase_args]
    exact Offset.contains (s₀.gpr .rsp) (e := 8) (d := 16) (by decide) (by decide) (by decide)
  have hall : Frame [(⟨off (low s₀) 520, 48⟩ : Region), ⟨refillBase s₀, frameBytes⟩,
      Refill.ctlRegion (refillBase s₀)] s₀.mem t.mem :=
    (a.mem.mono (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact List.mem_cons_self ..)).trans
      (fA.mono fun r hr => List.mem_cons_of_mem _ hr)
  have hav : t.mem.readW (off (refillBase s₀) 392) 64 = stackArg s₀ 1 := by
    rw [hall.readW argsC (h.frame_disjoint (r := inArgs s₀) (by simp)) (by decide), Refill.refillBase_args]; rfl
  have ha : InRegions (t.rd ++ t.wr) (off (refillBase s₀) 392) 8 :=
    ⟨inArgs s₀, List.mem_append_left _ (by rw [kt.2.1, a.rd, h.rd]; simp), argsC⟩
  have hsp : t.gpr .rsp = refillBase s₀ := (kt.gpr (by decide)).trans a.rsp
  have cs : Scr t (off (refillBase s₀) 296) 32 := Scr.of_mem (by rw [kt.2.2]; exact a.ctl) (by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have c1 : InRegions t.wr (off (refillBase s₀) 304) 8 := by simpa [off_off] using cs.st (d := 8) (by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun v => v.gpr .rax = stackArg s₀ 1) ?_ rfl) fun v ⟨hv, kv⟩ =>
    ⟨(kv.gpr (by decide)).trans hsp, hv⟩
  xrun [Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes,
    ea_sp, hsp, ha, hav, c1]

theorem entry_ct (pBytes qBytes : Nat) (hp : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384)
    (hq : qBytes = Spec.Dsa.generationQLen pBytes) :
    RelCT isa (Two (RefillInit pBytes))
      (.block (Impl.Dsa.X86_64.Generation.Refill.entryHeader pBytes qBytes ++ Impl.Dsa.X86_64.Generation.entryDerived))
      (Two (LoopBefore 6 pBytes qBytes)) := by
  have t₁ : ∃ hc, (taint.check (Taint.ofRegs [.rsp])
      (.block (Refill.headerA pBytes qBytes ++ ([.mov .rax (.mem (sp (Impl.Dsa.X86_64.Generation.Refill.frameBytes + 32 + 48 + 16))),
      .store (Impl.Dsa.X86_64.Generation.Refill.ctl 1) .rax] : List Instr))) hc).isSome = true := by
    subst hq; rcases hp with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have p31 : pBytes < 2 ^ 31 := by omega
  have q31 : qBytes < 2 ^ 31 := by subst hq; rcases hp with rfl | rfl | rfl <;> decide
  refine two_post ?_ fun P u hi => entry_ready hq hi
  have e : Impl.Dsa.X86_64.Generation.Refill.entryHeader pBytes qBytes ++ Impl.Dsa.X86_64.Generation.entryDerived =
      (Refill.headerA pBytes qBytes ++ ([.mov .rax (.mem (sp (Impl.Dsa.X86_64.Generation.Refill.frameBytes + 32 + 48 + 16))),
      .store (Impl.Dsa.X86_64.Generation.Refill.ctl 1) .rax] : List Instr)) ++
        (([.mov .rax (.mem (at0 .rax)), .store (Impl.Dsa.X86_64.Generation.Refill.ctl 2) .rax] : List Instr) ++ Impl.Dsa.X86_64.Generation.entryDerived) := by
    simp only [Refill.entryHeader_eq, Refill.headerB, List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := EntryLoaded) [.rsp] ?_ t₁.choose_spec
    fun P u hi => entryFirst_ready hi p31 q31) (two_taint [.rsp, .rax] ?_ (by taint_decide)))
  · intro P s t ⟨s₀, h, a, _, e₀⟩ ⟨t₀, h', a', _, e₁⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [a.rsp, a'.rsp]
    have := congrArg (fun P : LoopPublic => P.ctx.geo.F) (e₀.trans e₁.symm)
    exact this
  · intro P s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.trans ht.1.symm
    · exact hs.2.trans ht.2.symm

end VG.Proof.Dsa.X86_64.Generation
