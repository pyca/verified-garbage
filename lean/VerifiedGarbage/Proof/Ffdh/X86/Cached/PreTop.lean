module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.PreBody
public import VerifiedGarbage.Proof.Ffdh.X86.Entry
public import VerifiedGarbage.Proof.Ffdh.X86.ABI
public import VerifiedGarbage.Proof.Framework.X86.StackScratchConsts
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Table
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets

/-! # `vg_ffdh_generate_key_precompute` on i686 against its contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.CrtRt (In mw)
open VG.Proof.Ffdh.X86
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame)
open VG.Impl.Ffdh.X86.Cached

/-- The tables the precomputation reads. -/
abbrev pcConsts : List (String × List (BitVec 64)) := VG.Impl.Ffdh.X86.VettedValidation.tableConsts

/-- The precomputation's contract. -/
abbrev pcContract : Contract isa := Spec.Ffdh.generationPrecomputeContract (abi.withConsts pcConsts) stack

/-- What the contract gives `vg_ffdh_generate_key_precompute(ctx, ctx_len, domain, domain_len, p_len, scratch,
scratch_len)`, but the tables. -/
structure PreABI (s : State) : Prop where
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 28 ≤ 2 ^ 32
  rdIn : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region) ∈ s.rd
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat * 8⟩, ⟨argumentPointer s 5, (arg s 6).toNat * 8⟩,
    ⟨argAddr s 0, 28⟩]
  ctxDom : (⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  ctxScratch : (⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ : Region).Disjoint
    ⟨argumentPointer s 5, (arg s 6).toNat * 8⟩
  ctxArgs : (⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 28⟩
  domScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 5, (arg s 6).toNat * 8⟩
  domArgs : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 28⟩
  scratchArgs : (⟨argumentPointer s 5, (arg s 6).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 28⟩
  retCtx : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat * 8⟩
  retDom : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 5, (arg s 6).toNat * 8⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 28⟩
  belowCtx : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat * 8⟩
  belowDom : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint
    ⟨argumentPointer s 5, (arg s 6).toNat * 8⟩
  belowArgs : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argAddr s 0, 28⟩
  ctxBound : (arg s 0).toNat + (arg s 1).toNat * 8 ≤ 2 ^ 32
  domBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  scratchBound : (arg s 5).toNat + (arg s 6).toNat * 8 ≤ 2 ^ 32
  pLen : Spec.Ffdh.pLenValid (arg s 4).toNat
  dLen : Spec.Ffdh.domainLenValid (arg s 4).toNat (arg s 3).toNat
  ctxLen : (arg s 1).toNat = Spec.Ffdh.generationPrecomputedWords (arg s 4).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 4).toNat ≤ (arg s 6).toNat
  valid : Spec.Ffdh.domainValid (arg s 4).toNat (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat) = true

theorem preABI_plain {s : State} (h : (Spec.Ffdh.generationPrecomputeContract abi stack).pre s) : PreABI s := by
  sig_pre [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, abi,
    argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  have hrd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩] := by assumption
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (with_reducible assumption)
    | (rw [hrd]; exact List.mem_cons_self ..)

theorem preABI_of {s : State} (h : pcContract.pre s) : PreABI s ∧ ConstsOk pcConsts stack s := by
  obtain ⟨hp, hc⟩ := pre_consts.mp h
  have A := preABI_plain hp
  exact ⟨⟨A.stackLow, A.stackBound, stripConsts_rd_mem A.rdIn, A.wr, A.ctxDom, A.ctxScratch, A.ctxArgs,
    A.domScratch, A.domArgs, A.scratchArgs, A.retCtx, A.retDom, A.retScratch, A.retArgs, A.belowCtx, A.belowDom,
    A.belowScratch, A.belowArgs, A.ctxBound, A.domBound, A.scratchBound, A.pLen, A.dLen, A.ctxLen,
    A.scratchLength, A.valid⟩, hc⟩

abbrev pArgs : Impl.Ffdh.X86.Args := Impl.Ffdh.X86.Cached.Precompute.args

theorem wrapABI' {s : State} (A : PreABI s) : WrapABI pArgs 7 s where
  below := ⟨(fun _ h => by cases h), by decide, by decide, by decide, (fun _ h => by cases h),
    (fun _ h => by cases h), by decide, (fun _ h => by cases h; decide)⟩
  stackLow := A.stackLow
  stackBound := by have := A.stackBound; omega
  argsIn := by rw [A.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  wsIn := by rw [A.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  scratchArgs := A.scratchArgs
  retScratch := A.retScratch
  belowScratch := A.belowScratch
  scratchBound := A.scratchBound
  lower := A.pLen.1
  upper := A.pLen.2
  scratchLength := A.scratchLength

theorem pcFrameBody_all :
    (Code.seq (.block (Impl.Ffdh.X86.fill pArgs)) Impl.Ffdh.X86.Cached.Precompute.body :
      Prog isa).allInstrs VG.Proof.Mont.X86.StaticSquare.noSp = true := by
  rsa_stack_shape

/-- The bytes of the domain at entry. -/
abbrev pcDom (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat

/-- What the body may read: the domain and the table; and write: the context. -/
abbrev PRd (s : State) : List Region → List Region → Prop :=
  fun rd wr => InRegions (rd ++ wr) (argumentPointer s 2) (arg s 3).toNat ∧
    (⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ : Region) ∈ wr ∧
    InRegions (rd ++ wr) (symAddr s VG.Impl.Ffdh.X86.VettedValidation.tableSym) 17744

theorem pcWords_eq (k : Nat) : Spec.Ffdh.generationPrecomputedWords k = 3 + 34 * ((k + 7) / 8) := by
  simp only [Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords,
    Spec.Rsa.precomputedWords, Spec.Rsa.FixedBaseComb.entries, Spec.Rsa.FixedBaseComb.teeth, Spec.Rsa.modulusWords]
  omega

/-- The context's bytes. -/
theorem pcCtxBytes {s : State} (A : PreABI s) : (arg s 1).toNat * 8 = ctxBytes (pLenOf pArgs s) := by
  have := A.ctxLen
  rw [pcWords_eq] at this
  simp only [ctxBytes, CrtRt.bc, mw, Spec.Rsa.modulusWords]
  show _ = 24 + 8 * (((arg s 4).toNat + 7) / 8) * 34
  omega

/-- The table, and the 96 bytes below the frame and the frame, within the stack below the caller's. -/
theorem pc_subs {s : State} (A : PreABI s) {sp : BitVec 32} (espf : sp = s.gpr .esp - BitVec.ofNat 32 argsFrame) :
    Region.Sub (below sp 96) ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ ∧
      Region.Sub ⟨sp.setWidth 64, 76⟩ ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
  have fb : argsFrame = 76 := rfl
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega)
  have espN : sp.toNat = (s.gpr .esp).toNat - 76 := by rw [espf]; exact VG.X86.sub_toNat (by omega)
  refine ⟨?_, ?_⟩
  · simp only [below]
    rw [VG.X86.Taint.sub_setWidth (by rw [espN]; omega), espf,
      show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA,
      ← VG.Offset.sub_add_eq, show BitVec.ofNat 64 argsFrame + 96#64 = BitVec.ofNat 64 172 from rfl]
    exact Region.sub_prefix (by decide)
  · rw [espf, show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA]
    exact Offset.sub_below _ (by decide) (by decide)

/-- A table's region, apart from what the code writes. -/
theorem single_apart {name : String} {words : List (BitVec 64)} {s : State} {st : Nat}
    (h : ConstsOk [(name, words)] st s) :
    (symAddr s name).toNat + 8 * words.length ≤ 2 ^ 32 ∧
      (∀ r ∈ s.wr, Region.Disjoint ⟨symAddr s name, 8 * words.length⟩ r) ∧
      ∀ r ∈ abi.reserved st s, Region.Disjoint ⟨symAddr s name, 8 * words.length⟩ r :=
  h.2.2.1 ⟨symAddr s name, 8 * words.length⟩ List.mem_cons_self

/-- The tables' region, apart from what the code writes. -/
theorem table_apart {s : State} (hc : ConstsOk pcConsts stack s) :
    (symAddr s VG.Impl.Ffdh.X86.VettedValidation.tableSym).toNat + 17744 ≤ 2 ^ 32 ∧
      (∀ r ∈ s.wr, Region.Disjoint ⟨symAddr s VG.Impl.Ffdh.X86.VettedValidation.tableSym, 17744⟩ r) ∧
      Region.Disjoint ⟨symAddr s VG.Impl.Ffdh.X86.VettedValidation.tableSym, 17744⟩
        ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
  have T := single_apart (name := VG.Impl.Ffdh.X86.VettedValidation.tableSym)
    (words := VG.Impl.Ffdh.VettedGroups.tableWords) hc
  rw [VG.Proof.Ffdh.VettedTableFacts.tableWords_length] at T
  exact ⟨T.1, T.2.1, T.2.2 _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩

/-- The body, from the frame's state. -/
theorem pc_frame_ok {s : State} (A : PreABI s) (hc : ConstsOk pcConsts stack s) (f : State)
    (I : In (PRd s) (wsBase pArgs s) (wsSize pArgs s) (pLenOf pArgs s) (synth pArgs (arg s)) f)
    (espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame)
    (Ft : Frame [⟨wsBase pArgs s, wsSize pArgs s⟩, ⟨frameAt s, argsFrame⟩] s.mem f.mem) (hsy : f.syms = s.syms) :
    WP isa Impl.Ffdh.X86.Cached.Precompute.body f fun t =>
      (t.gpr .eax = 1 ∧ Spec.Rsa.wordsAt t.mem (argumentPointer s 0) (arg s 1).toNat =
        generationValues (pLenOf pArgs s) (pcDom s)) ∧
      Frame ([ctxR (synth pArgs (arg s)) (pLenOf pArgs s)] ++
        CrtRt.frameR (wsBase pArgs s) (f.gpr .esp) (fR (pLenOf pArgs s))) f.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f t := by
  obtain ⟨sub96, subF⟩ := pc_subs A espf
  obtain ⟨tfit, twr, t172⟩ := table_apart hc
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega)
  have frameSub : Region.Sub ⟨frameAt s, argsFrame⟩ ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
    rw [FA]; exact Offset.sub_below _ (by decide) (by decide)
  have ofn : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have cb := pcCtxBytes A
  have G : DomGeo (synth pArgs (arg s)) (wsBase pArgs s) (wsSize pArgs s) (pLenOf pArgs s) (arg s 3).toNat
      f.rd f.wr :=
    ⟨(ofn _).symm, (ofn _).symm, (ofn _).symm, rfl, rfl, (ofn _).symm, A.dLen, A.domBound, I.extra.1, A.domScratch,
      A.pLen.1, A.pLen.2⟩
  have hb40 : Region.Disjoint ⟨byteAddr (synth pArgs (arg s) 2), (arg s 3).toNat⟩ (below (f.gpr .esp) 96) :=
    (A.belowDom.sub_left sub96).symm
  have ctxE : ctxR (synth pArgs (arg s)) (pLenOf pArgs s) = ⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ := by
    rw [cb]; rfl
  have domC : Region.Disjoint ⟨byteAddr (synth pArgs (arg s) 2), (arg s 3).toNat⟩
      (ctxR (synth pArgs (arg s)) (pLenOf pArgs s)) := by rw [ctxE]; exact A.ctxDom.symm
  have C : CtxW (wsBase pArgs s) (wsSize pArgs s) (pLenOf pArgs s) (synth pArgs (arg s)) f := by
    have cfit : (argumentPointer s 0).toNat = (arg s 0).toNat := by
      simp only [argumentPointer, BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega)
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · show ctxR _ _ ∈ _; rw [ctxE]; exact I.extra.2.1
    · show (argumentPointer s 0).toNat + _ ≤ _; rw [← cb, cfit]; exact A.ctxBound
    · show Region.Disjoint (ctxR _ _) _; rw [ctxE]; exact A.ctxScratch
    · show Region.Disjoint _ (ctxR _ _); rw [ctxE]; exact (A.belowCtx.sub_left subF)
    · show Region.Disjoint (ctxR _ _) _; rw [ctxE]; exact (A.belowCtx.sub_left sub96).symm
  have tws : Region.Disjoint ⟨byteAddr (s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym), 17744⟩
      ⟨wsBase pArgs s, wsSize pArgs s⟩ := twr _ (by rw [A.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have tbytes : Spec.Rsa.bytesAt f.mem (byteAddr (s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym)) 17744 =
      VG.Impl.Ffdh.VettedGroups.tableBytes := by
    rw [frame_bytes Ft (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact tws
      · exact t172.sub_right frameSub) (by decide)]
    have := VettedValidation.consts_bytes hc
    rwa [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length] at this
  have dv : Spec.Ffdh.domainValid (pLenOf pArgs s) (KeyGen.domOf f.mem (synth pArgs (arg s)) (arg s 3).toNat) := by
    show Spec.Ffdh.domainValid _ (Spec.Rsa.bytesAt f.mem (argumentPointer s 2) _) = true
    rw [frame_bytes Ft (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact A.domScratch
      · exact (A.belowDom.sub_left frameSub).symm) (by have := A.domBound; omega)]
    exact A.valid
  have tfit' : (s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym).toNat + 17744 ≤ 2 ^ 32 := by
    have e : (symAddr s VG.Impl.Ffdh.X86.VettedValidation.tableSym).toNat =
        (s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym).toNat := by
      simp only [symAddr, BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by have := (s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym).isLt; omega)
    rw [e] at tfit; exact tfit
  refine WP.mono (pcBody_ok I G hb40 domC C (T := s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym)
    (by rw [hsy]) tfit' I.extra.2.2 tbytes tws
    (t172.sub_right sub96) dv) fun t ⟨E, F, K, W⟩ => ⟨⟨E, ?_⟩, by rw [List.singleton_append]; exact F, K⟩
  have dd : KeyGen.domOf f.mem (synth pArgs (arg s)) (arg s 3).toNat = pcDom s := by
    show Spec.Rsa.bytesAt f.mem (argumentPointer s 2) _ = _
    exact frame_bytes Ft (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact A.domScratch
      · exact (A.belowDom.sub_left frameSub).symm) (by have := A.domBound; omega)
  rw [dd] at W
  rw [A.ctxLen, pcWords_eq]
  exact W

theorem pc_operation_ok {s : State} (A : PreABI s) (hc : ConstsOk pcConsts stack s) :
    WP isa Impl.Ffdh.X86.Cached.Precompute.code s fun u =>
      (u.gpr .eax = 1 ∧ Spec.Rsa.wordsAt u.mem (argumentPointer s 0) (arg s 1).toNat =
        generationValues (pLenOf pArgs s) (pcDom s)) ∧ abiPreserved s u := by
  have tr := VettedValidation.consts_read hc
  rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length] at tr
  have hx : PRd s s.rd (⟨frameAt s, argsFrame⟩ :: s.wr) := by
    refine ⟨⟨_, List.mem_append_left _ A.rdIn, Region.contains_self _ _⟩, ?_, ?_⟩
    · rw [A.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
    · obtain ⟨r, hr, hcn⟩ := tr
      refine ⟨r, ?_, hcn⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have cb := pcCtxBytes A
  have ctxE : ctxR (synth pArgs (arg s)) (pLenOf pArgs s) = ⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ := by
    rw [cb]; rfl
  exact wrap_syms_ok (wrapABI' A) (NoSp.of_all pcFrameBody_all) hx (Out := [ctxR (synth pArgs (arg s)) (pLenOf pArgs s)])
    (fun r hr => by obtain rfl := List.mem_singleton.mp hr; rw [ctxE]; exact A.retCtx)
    (fun r hr => by obtain rfl := List.mem_singleton.mp hr; rw [ctxE]; exact A.ctxScratch.symm)
    (P := fun m e => e = 1 ∧ Spec.Rsa.wordsAt m (argumentPointer s 0) (arg s 1).toNat =
      generationValues (pLenOf pArgs s) (pcDom s))
    fun f I espf Ft hsy => pc_frame_ok A hc f I espf Ft hsy

theorem pc_correct (s : State) (h : pcContract.pre s) :
    ∃ trace t, Exec isa Impl.Ffdh.X86.Cached.Precompute.code s trace t ∧ abiPreserved s t ∧
      pcContract.post s t := by
  obtain ⟨A, hc⟩ := preABI_of h
  obtain ⟨trace, t, E, ⟨e1, W⟩, P⟩ := pc_operation_ok A hc
  refine ⟨trace, t, E, P, ?_⟩
  change (Spec.Ffdh.generationPrecomputeContract abi stack).post s t
  sig_post [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, abi,
    argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right, e1]
  refine ⟨rfl, ?_⟩
  have dl : (arg s 3).toNat = 2 * (arg s 4).toNat ∨ (arg s 3).toNat = 3 * (arg s 4).toNat := A.dLen
  have dlen : (arg s 4).toNat ≤ (pcDom s).length := by rw [VG.Proof.Bignum.bytesAt_length]; omega
  rw [VG.Proof.Ffdh.generationPrecompute_eq dlen (VG.Proof.Ffdh.domainValid_mod A.valid)]
  exact congrArg some W.symm

end VG.Proof.Ffdh.X86.Cached
