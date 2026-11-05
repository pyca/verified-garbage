module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCTEntry
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCTStep
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCTOutput
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillContract
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCorrect
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryInnerCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntrySetupCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntrySave
import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The refillable-tape search for one width is constant time

`refill_ct`: two runs from states whose public data agree (the arguments in
registers and on the stack, the stack pointer, `state`'s four words and the
whole tape `rand`) leak the same trace. The controller's public state on
entry is a function of that data (`loopPublic_eq`), and the entry, the
controller (`controller_ct`) and the end (`finish_ct`) keep their states
related. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.MillerRabin.X86_64
open Refill (RefillABI inOut inUsed inRand inScr inState inArgs low refillBase refillGeometry refillContext randTape)

variable {checkName : String}

/-! ## Public data -/

/-- What two runs' public data agree on. -/
structure RefillAgree (s t : State) : Prop where
  rsp : s.gpr .rsp = t.gpr .rsp
  regs : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9], s.gpr r = t.gpr r
  arg0 : stackArg s 0 = stackArg t 0
  arg1 : stackArg s 1 = stackArg t 1
  rand : Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .rcx) (t.gpr .r8).toNat
  seeds : s.mem.readW (stackArg s 1) 64 = t.mem.readW (stackArg t 1) 64

theorem refill_wordsAt_four (m : Mem) (p : Addr) : (Spec.Rsa.wordsAt m p 4).map (·.toNat) =
    [(m.readW (p + BitVec.ofNat 64 0) 64).toNat, (m.readW (p + 8) 64).toNat, (m.readW (p + 16) 64).toNat,
      (m.readW (p + 24) 64).toNat] := rfl

theorem refill_agree {pBytes S : Nat} {s t : State} (h : (Refill.contract pBytes abi S).pub s t) :
    RefillAgree s t := by
  sig_pub [Refill.contract, Spec.Dsa.parameterSearchSig, abi, argRegs, Refill.stackArgs_two] at h
  obtain ⟨hsp, hl, r1, r2, r3, r4, r5, r6, a0, a1⟩ := h
  rw [refill_wordsAt_four, refill_wordsAt_four] at hl
  have hp := List.append_inj hl rfl
  simp only [List.cons.injEq] at hp
  refine ⟨hsp, ?_, by simpa using a0, by simpa using a1, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · exact (List.map_inj_right fun a b e => BitVec.eq_of_toNat_eq e).mp hp.2
  · have := BitVec.eq_of_toNat_eq hp.1.1
    simpa only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] using this

theorem GenerationTape.heq_of {p q : GenerationGeometry} {a : GenerationTape p} {b : GenerationTape q}
    (hg : p = q) (hp : a.ptr = b.ptr) (hb : a.bytes = b.bytes) : HEq a b := by
  cases hg; cases a; cases b; cases hp; cases hb; rfl

theorem GenerationContext.ext' {a b : GenerationContext} (hg : a.geo = b.geo) (hs : HEq a.seeds b.seeds)
    (hh : HEq a.hs b.hs) (hr : HEq a.rand b.rand) (hw : a.saved = b.saved) : a = b := by
  cases a; cases b; cases hg; cases hs; cases hh; cases hr; cases hw; rfl

theorem LoopPublic.ext' {P Q : LoopPublic} (hc : P.ctx = Q.ctx) (hh : HEq P.hs Q.hs) (h1 : P.start = Q.start)
    (h2 : P.left = Q.left) (h3 : P.c0 = Q.c0) (h4 : P.c1 = Q.c1) (h5 : P.ws = Q.ws) (h6 : P.wr = Q.wr) :
    P = Q := by
  cases P; cases Q
  dsimp only at hc hh h1 h2 h3 h4 h5 h6
  subst hc; cases hh; subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; rfl

theorem RefillAgree.wr {pBytes : Nat} {s t : State} (hs : RefillABI pBytes s) (ht : RefillABI pBytes t)
    (a : RefillAgree s t) : s.wr = t.wr := by
  rw [hs.wr, ht.wr]
  simp only [inOut, inUsed, inScr, inState, a.regs .rdi (by simp), a.regs .rsi (by simp), a.regs .rdx (by simp),
    a.regs .r9 (by simp), a.arg0, a.arg1]

theorem refillContext_eq {pBytes : Nat} {s t : State} (hs : RefillABI pBytes s) (ht : RefillABI pBytes t)
    (a : RefillAgree s t) : refillContext hs = refillContext ht := by
  have base : refillBase s = refillBase t := by simp only [refillBase, low, a.rsp]
  have hg : refillGeometry hs = refillGeometry ht := by
    have ext : ∀ {x y : GenerationGeometry}, x.B = y.B → x.F = y.F → x.pLen = y.pLen → x.qLen = y.qLen → x = y := by
      intro x y hB hF hp hq
      cases x; cases y
      dsimp only at hB hF hp hq
      subst hB; subst hF; subst hp; subst hq; rfl
    exact ext (a.regs .r9 (by simp)) base rfl rfl
  have tape : HEq (randTape hs) (randTape ht) :=
    GenerationTape.heq_of hg (a.regs .rcx (by simp)) a.rand
  refine GenerationContext.ext' hg tape ?_ tape ?_
  · refine GenerationTape.heq_of hg ?_ ?_
    · show off (s.gpr .rcx) 0 = off (t.gpr .rcx) 0
      rw [a.regs .rcx (by simp)]
    · show ((randTape hs).bytes.drop 0).take 0 = ((randTape ht).bytes.drop 0).take 0
      simp only [List.take_zero]
  · funext k
    show Refill.refillWords pBytes s k = Refill.refillWords pBytes t k
    unfold Refill.refillWords
    split <;> simp only [a.regs .rdi (by simp), a.regs .rsi (by simp), a.regs .rcx (by simp),
      a.regs .r8 (by simp), a.regs .r9 (by simp)]

theorem loopPublic_eq {pBytes : Nat} {s t : State} (hs : RefillABI pBytes s) (ht : RefillABI pBytes t)
    (a : RefillAgree s t) : loopPublic hs = loopPublic ht := by
  have e := refillContext_eq hs ht a
  refine LoopPublic.ext' e (by change HEq (refillContext hs).hs (refillContext ht).hs; rw [e]) rfl ?_
    (a.regs .rdx (by simp)) a.arg1 ?_ ?_
  · change (s.mem.readW (stackArg s 1) 64).toNat = (t.mem.readW (stackArg t 1) 64).toNat
    rw [a.seeds]
  · change refillWs s = refillWs t
    simp only [refillWs, refillBase, low, a.rsp, a.wr hs ht]
  · change refillWr s = refillWr t
    simp only [refillWr, refillWs, refillBase, low, a.rsp, a.wr hs ht]

/-! ## The body -/

theorem body_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest) (pBytes qBytes : Nat)
    (hp : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384) (hq : qBytes = Spec.Dsa.generationQLen pBytes) :
    RelCT isa (Two (RefillInit pBytes))
      (Impl.Dsa.X86_64.Generation.Refill.body (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pBytes qBytes)
      (fun _ _ => True) := by
  have sizes : GenerationSizes pBytes qBytes := by
    subst hq; rcases hp with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  unfold Impl.Dsa.X86_64.Generation.Refill.body
  simp only [VG.Impl.Bignum.X86_64.seqs]
  exact RelCT.seq (entry_ct pBytes qBytes hp hq)
    (RelCT.seq (controller_ct (checkName := checkName) H M Sq T pBytes qBytes sizes) (finish_ct pBytes qBytes hp))

/-- The body's starting state, after the frames' allocation and the saved registers. -/
theorem refill_init {pBytes : Nat} {s₀ u : State} (h : RefillABI pBytes s₀)
    (hg : u.gpr = (allocState 48 s₀).gpr) (hr : u.rd = s₀.rd) (hw : u.wr = (allocState 48 s₀).wr)
    (hf : Frame [⟨(allocState 48 s₀).gpr .rsp, 48⟩] s₀.mem u.mem) :
    RefillInit pBytes (loopPublic h) (allocState 296 (allocState 32 u)) := by
  have lower : 568 ≤ (s₀.gpr .rsp).toNat := h.stackLower
  have ursp : u.gpr .rsp = s₀.gpr .rsp - BitVec.ofNat 64 48 := by rw [hg]; rfl
  have e : (allocState 296 (allocState 32 u)).gpr .rsp = refillBase s₀ := by
    change u.gpr .rsp - BitVec.ofNat 64 32 - BitVec.ofNat 64 296 = _
    rw [ursp, Refill.rsp_alloc]; rfl
  have ectl : u.gpr .rsp - BitVec.ofNat 64 32 = off (refillBase s₀) 296 := by
    rw [ursp, Refill.ctl_alloc]; rfl
  have wr : (allocState 296 (allocState 32 u)).wr = refillWr s₀ := by
    change ⟨(allocState 296 (allocState 32 u)).gpr .rsp, 296⟩ :: ⟨u.gpr .rsp - BitVec.ofNat 64 32, 32⟩ :: u.wr = _
    rw [e, ectl, hw]
    change _ :: _ :: ⟨s₀.gpr .rsp - BitVec.ofNat 64 48, 48⟩ :: s₀.wr = _
    rw [Refill.saved_alloc]; rfl
  refine ⟨s₀, h, ?_, wr, rfl⟩
  exact
    { rsp := e
      frame := by rw [wr]; exact List.mem_cons_self ..
      ctl := by rw [wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      wr := fun r hr => by rw [wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
      rd := hr
      regs := fun r hne => by simp only [allocState, State.setReg, hne, ↓reduceIte, hg]
      mem := by
        change Frame _ s₀.mem u.mem
        rw [show off (low s₀) 520 = (allocState 48 s₀).gpr .rsp from (Refill.saved_alloc _).symm]; exact hf }

theorem refill_post_of_exec {c : Prog isa} {s t : State} {trace : List Leak} {Q : State → Prop}
    (h : WP isa c s Q) (he : Exec isa c s trace t) : Q t := by
  obtain ⟨_, u, hu, hq⟩ := h
  obtain ⟨_, heq⟩ := Exec.det he hu
  rw [heq]
  exact hq

/-- The two inner frames and the body. -/
theorem refillInner_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest) (pBytes qBytes : Nat)
    (hp : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384) (hq : qBytes = Spec.Dsa.generationQLen pBytes)
    {s t a b u v : State} (hs : RefillABI pBytes s) (ht : RefillABI pBytes t) (agree : RefillAgree s t)
    (ga : a.gpr = (allocState 48 s).gpr) (ra : a.rd = s.rd) (wa : a.wr = (allocState 48 s).wr)
    (fa : Frame [⟨(allocState 48 s).gpr .rsp, 48⟩] s.mem a.mem)
    (gb : b.gpr = (allocState 48 t).gpr) (rb : b.rd = t.rd) (wb : b.wr = (allocState 48 t).wr)
    (fb : Frame [⟨(allocState 48 t).gpr .rsp, 48⟩] t.mem b.mem) {tsa tsb : List Leak}
    (ea : Exec isa (.frame (.alloc 32) (.frame (.alloc Impl.Dsa.X86_64.Generation.Refill.frameBytes)
        (Impl.Dsa.X86_64.Generation.Refill.body (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pBytes qBytes)
        (.free Impl.Dsa.X86_64.Generation.Refill.frameBytes)) (.free 32)) a tsa u)
    (eb : Exec isa (.frame (.alloc 32) (.frame (.alloc Impl.Dsa.X86_64.Generation.Refill.frameBytes)
        (Impl.Dsa.X86_64.Generation.Refill.body (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pBytes qBytes)
        (.free Impl.Dsa.X86_64.Generation.Refill.frameBytes)) (.free 32)) b tsb v) :
    tsa = tsb ∧ u.gpr .rsp = v.gpr .rsp := by
  have la : 568 ≤ (s.gpr .rsp).toNat := hs.stackLower
  have lb : 568 ≤ (t.gpr .rsp).toNat := ht.stackLower
  have arsp : (a.gpr .rsp).toNat = (s.gpr .rsp).toNat - 48 := by
    rw [ga]; exact Refill.toNat_sub_k (by omega)
  have brsp : (b.gpr .rsp).toNat = (t.gpr .rsp).toNat - 48 := by
    rw [gb]; exact Refill.toNat_sub_k (by omega)
  cases ea with
  | frame pa ia qa =>
    cases eb with
    | frame pb ib qb =>
      rw [generation_alloc (by decide) (by omega), Option.some.injEq] at pa
      rw [generation_alloc (by decide) (by omega), Option.some.injEq] at pb
      subst pa; subst pb
      cases ia with
      | frame pa' ba qa' =>
        cases ib with
        | frame pb' bb qb' =>
          rw [generation_alloc (by decide) (by
            change 296 ≤ (a.gpr .rsp - BitVec.ofNat 64 32).toNat
            rw [Refill.toNat_sub_k (by omega)]; omega), Option.some.injEq] at pa'
          rw [generation_alloc (by decide) (by
            change 296 ≤ (b.gpr .rsp - BitVec.ofNat 64 32).toNat
            rw [Refill.toNat_sub_k (by omega)]; omega), Option.some.injEq] at pb'
          subst pa'; subst pb'
          have ia := refill_init hs ga ra wa fa
          have ib := refill_init ht gb rb wb fb
          rw [← loopPublic_eq hs ht agree] at ib
          have traces := (body_ct (checkName := checkName) H M Sq T pBytes qBytes hp hq _ _ _ _ _ _
            ⟨loopPublic hs, ia, ib⟩ ba bb).1
          refine ⟨by simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using traces, ?_⟩
          rw [generation_free_rsp qa, generation_free_rsp qb, ga, gb]
          change s.gpr .rsp - BitVec.ofNat 64 48 = t.gpr .rsp - BitVec.ofNat 64 48
          rw [agree.rsp]

/-! ## The function -/

theorem refill_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest) (pBytes qBytes : Nat)
    (hp : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384) (hq : qBytes = Spec.Dsa.generationQLen pBytes) :
    ConstantTime isa (Refill.contract pBytes abi Refill.refillStack).pre
      (Refill.contract pBytes abi Refill.refillStack).pub
      (Impl.Dsa.X86_64.Generation.Refill.code (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run
        pBytes qBytes) := by
  intro s t tsa tsb u v hs ht hpub ea eb
  have hsa := Refill.refillABI_of hs
  have hta := Refill.refillABI_of ht
  have agree := refill_agree hpub
  have la : 568 ≤ (s.gpr .rsp).toNat := hsa.stackLower
  have lb : 568 ≤ (t.gpr .rsp).toNat := hta.stackLower
  unfold Impl.Dsa.X86_64.Generation.Refill.code at ea eb
  cases ea with
  | frame pa ba _ =>
    cases eb with
    | frame pb bb _ =>
      rw [generation_alloc (by decide) (by omega : 48 ≤ (s.gpr .rsp).toNat), Option.some.injEq] at pa
      rw [generation_alloc (by decide) (by omega : 48 ≤ (t.gpr .rsp).toNat), Option.some.injEq] at pb
      subst pa; subst pb
      cases ba with | seq sa restA => cases restA with | seq ia ra =>
      cases bb with | seq sb restB => cases restB with | seq ib rb =>
      have saveTrace := (entrySave_ct _ _ _ _ _ _ (by
        change s.gpr .rsp - BitVec.ofNat 64 48 = t.gpr .rsp - BitVec.ofNat 64 48
        rw [agree.rsp]) sa sb).1
      obtain ⟨ga, rda, wra, _, fa⟩ :=
        refill_post_of_exec (entrySave_ok (s := allocState 48 s) (List.mem_cons_self ..)) sa
      obtain ⟨gb, rdb, wrb, _, fb⟩ :=
        refill_post_of_exec (entrySave_ok (s := allocState 48 t) (List.mem_cons_self ..)) sb
      have inner := refillInner_ct (checkName := checkName) H M Sq T pBytes qBytes hp hq hsa hta agree
        ga rda wra fa gb rdb wrb fb ia ib
      have restoreTrace := (entryRestore_ct _ _ _ _ _ _ inner.2 ra rb).1
      simp only [addrs, List.map_nil, List.nil_append, List.append_nil]
      rw [saveTrace, inner.1, restoreTrace]

end VG.Proof.Dsa.X86_64.Generation
