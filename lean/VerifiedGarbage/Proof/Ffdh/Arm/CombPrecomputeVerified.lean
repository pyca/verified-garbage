module

public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedBoundInstance
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMainCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSat
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableState
import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.GetElem
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInput
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputePrefix
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMontgomeryOut
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeBasis
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInitialStore
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableInit
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductState
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeBasisStore
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSamplePolicy
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputePre
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeEnvironment
import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
import Init.Core
import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCTState
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeEntry
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsEnvironment

/-! ### `Ffdh.Arm.CombPrecomputeTable`, which only this module used -/

section

/-! Four runtime basis rounds produce all thirty-two canonical table entries. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem table_loop_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32}
    (h : Core p sp s)
    (positive : 0<Spec.Rsa.FixedBaseComb.rows (bits p))
    (fits : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32)
    (power : Power5 p 1 s) (table : TablePrefix p 2 s.mem)
    (saved : s.mem.readW (off (State.addr sp) 36) 32=2) :
    WP isa (.loop (VG.Impl.Ffdh.Arm.CombPrecompute.basis
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) .ne) s fun t =>
      Core p sp t ∧ TablePrefix p 32 t.mem ∧
      WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  let I := fun k t => 0<k ∧ k≤4 ∧ Core p sp t ∧
    Power5 p (2^((4-k)*Spec.Rsa.FixedBaseComb.rows (bits p))) t ∧
    TablePrefix p (2^(5-k)) t.mem ∧
    t.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 (2^(5-k)) ∧
    WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
    Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t
  refine WP.loop (M:=isa) I ?_ 4 s ?_
  · intro k u hu
    obtain ⟨hk,bound,core,pow,tab,counter,header,frame,rest⟩ := hu
    have prev : 5-k-1=4-k := by omega_using []
    have pow' : Power5 p (2^((5-k-1)*Spec.Rsa.FixedBaseComb.rows (bits p))) u := by rw [prev];exact pow
    refine WP.mono (basis_ok backend u core (by omega_using [hk]) (by omega_using [bound]) positive fits pow' tab counter) ?_
    rintro t ⟨coreT,powT,tableT,countT,zero,headerT,frameT,restT⟩
    have headerAll : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem := by
      refine ⟨?_⟩
      intro d n hd
      exact (headerT.read d n hd).trans (header.read d n hd)
    by_cases last : k=1
    · left
      refine ⟨?_,coreT,?_,headerAll,frame.trans frameT,rest.trans restT⟩
      · change some (!t.z)=some false
        simp only [zero,last,decide_true,Bool.not_true]
      · simpa only [last] using tableT
    · right
      have ne : 5-k≠4 := by omega_using [last]
      refine ⟨?_,k-1,by omega_using [hk],by omega_using [hk, last],by omega_using [bound],coreT,?_,?_,?_,headerAll,frame.trans frameT,rest.trans restT⟩
      · change some (!t.z)=some true
        simp only [zero,ne,decide_false,Bool.not_false]
      · simpa only [show 4-(k-1)=5-k by omega_using [hk]] using powT
      · simpa only [show 5-(k-1)=5-k+1 by omega_using [hk, bound]] using tableT
      · simpa only [show 5-(k-1)=5-k+1 by omega_using [hk, bound]] using countT
  · refine ⟨by decide,by decide,h,?_,?_,?_,⟨fun _ _ _ => rfl⟩,Frame.refl _ _,Rest.refl _ _⟩
    · simpa only [Nat.sub_self,Nat.zero_mul,Nat.pow_zero] using power
    · exact table
    · exact saved


theorem table_ok (backend : MontBackend) (s : State) {p : Inputs} {sp : BitVec 32}
    (h : Memory p sp s)
    (modulus : Proof.Rsa.Mont.numAt s.mem (State.addr p.base) p.w 0=p.P)
    (r2 : Proof.Rsa.Mont.numAt s.mem (State.addr p.base) p.w 4=2^(128*p.w)%p.P)
    (odd : p.P%2=1) (positive : 0<Spec.Rsa.FixedBaseComb.rows (bits p))
    (fits : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32) :
    WP isa (VG.Impl.Ffdh.Arm.CombPrecompute.table
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      Core p sp t ∧ TablePrefix p 32 t.mem ∧
      WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem ∧
      Frame (productWrites p sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.CombPrecompute.table,WP.seq_iff]
  refine WP.mono (initial_ok backend s h modulus r2 odd) ?_
  rintro u ⟨memory,tab,value,one,modulusU,r2U,headerU,frameU,restU⟩
  have coreU : Core p sp u := ⟨memory,modulusU,odd,r2U,one⟩
  have power : Power5 p 1 u := by
    change _ = _
    rw [value,entryValue]
    have e := VG.Proof.Rsa.FixedBaseComb.exponent_tooth (bits p) 0 (by decide)
    simpa only [Nat.pow_zero,Nat.zero_mul] using congrArg
      (fun E => Spec.Rsa.powMod p.G E p.P * 2^(64*p.w)%p.P) e
  rw [WP.seq_iff]
  refine WP.mono (tableInit_state u coreU power) ?_
  rintro v ⟨coreV,powerV,savedV,frameV,restV⟩
  have ctxV := coreU.memory.controlContextEq (by decide) frameV
  have tableV : TablePrefix p 2 v.mem := by
    intro digit hd
    rw [ctxV.read (entryOffset p digit) (8*p.w) (entry_bound p (by omega_using [hd]))]
    exact tab digit hd
  refine WP.mono (table_loop_ok backend v coreV positive fits powerV tableV savedV) ?_
  rintro t ⟨coreT,tableT,headerT,frameT,restT⟩
  have header : WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem := by
    refine ⟨?_⟩
    intro d n hd
    exact (headerT.read d n hd).trans ((ctxV.read d n (by have := bytes_eq p;omega_using [hd, this])).trans (headerU.read d n hd))
  have wholeU : Frame (productWrites p sp) s.mem u.mem := frameU.mono (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl <;> simp [productWrites])
  have wholeV : Frame (productWrites p sp) u.mem v.mem := frameV.sub (by
    intro r hr
    have eq := List.mem_singleton.mp hr
    subst r
    exact ⟨⟨State.addr sp,72⟩,by simp [productWrites],Offset.sub_base _ (by decide)⟩)
  exact ⟨coreT,tableT,header,wholeU.trans (wholeV.trans frameT),restU.trans (restV.trans restT)⟩

end VG.Proof.Ffdh.Arm.CombBuilder

end

end

/-! ### `Ffdh.Arm.CombPrecomputeData`, which only this module used -/

section

/-! Package the reviewed public ABI arguments for the native writer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts)

theorem combPrecompute_data (s : State)
    (pre : (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts) 176).pre s) :
    ∃ p : Inputs, stackArg s 1 = p.base ∧ s.gpr .r0 = p.output ∧
      s.gpr .r2 = p.domain ∧ (stackArg s 0).toNat = p.k ∧
      (stackArg s 2).toNat = p.len ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r3).toNat = p.dom ∧
      (s.gpr .r1).toNat = Spec.Ffdh.generationPrecomputedWords p.k ∧
      p.privateValue=p.output ∧ p.publicValue=p.output ∧ p.entropy=p.output ∧
      CombPrecomputeFnInput p s := by
  have original := pre
  have plain := (pre_consts.mp pre).1
  sig_pre [Spec.Ffdh.generationPrecomputeContract,Spec.Ffdh.generationPrecomputeSig,
    abi,argRegs,reduceClassify,Loc.val,State.addr] at plain
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,bounds,domainLen,ctxLen,space,_⟩ := plain
  change Spec.Ffdh.pLenValid (stackArg s 0).toNat at bounds
  change Spec.Ffdh.domainLenValid (stackArg s 0).toNat (s.gpr .r3).toNat at domainLen
  change Spec.Rsa.scratchWords (stackArg s 0).toNat ≤ (stackArg s 2).toNat at space
  change (s.gpr .r1).toNat = Spec.Ffdh.generationPrecomputedWords (stackArg s 0).toNat at ctxLen
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
  have domLength : dom.length = (s.gpr .r3).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := stackArg s 1
    domain := s.gpr .r2
    publicValue := s.gpr .r0
    privateValue := s.gpr .r0
    output := s.gpr .r0
    entropy := s.gpr .r0
    len := (stackArg s 2).toNat
    k := (stackArg s 0).toNat
    privateLength := (stackArg s 0).toNat
    hasQ := decide ((s.gpr .r3).toNat = 3*(stackArg s 0).toNat)
    dom := dom
    minLength := bounds.1
    maxLength := bounds.2
    space := space
    domainLength := by
      rw [domLength]
      simp only [decide_eq_true_eq]
      split
      · assumption
      · rename_i different
        rcases domainLen with h | h
        · exact h
        · exact False.elim (different h) }
  have environment := combPrecompute_environment s original (p:=p) rfl rfl rfl rfl rfl rfl
  exact ⟨p,rfl,rfl,rfl,rfl,rfl,rfl,ctxLen,rfl,rfl,rfl,
    combPrecompute_input s original rfl rfl rfl rfl rfl rfl rfl rfl rfl environment⟩

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.CombPrecomputePost`, which only this module used -/

section

/-! The canonical native result has the reviewed public-precomputation postcondition. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem combPrecompute_post (s t : State) {p : Inputs}
    (output : s.gpr .r0=p.output) (domain : s.gpr .r2=p.domain)
    (count : (stackArg s 0).toNat=p.k)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r3).toNat=p.dom)
    (ctxLen : (s.gpr .r1).toNat=Spec.Ffdh.generationPrecomputedWords p.k)
    (status : t.gpr .r0=1)
    (result : Spec.Ffdh.generationPrecompute p.k p.dom=some
      (Spec.Rsa.wordsAt t.mem (State.addr p.output) (Spec.Ffdh.generationPrecomputedWords p.k))) :
    (Spec.Ffdh.generationPrecomputeContract abi 176).post s t := by
  sig_post [Spec.Ffdh.generationPrecomputeContract,Spec.Ffdh.generationPrecomputeSig,
    abi,argRegs,reduceClassify,Loc.val,State.addr]
  rw [BitVec.setWidth_append_eq_right]
  change t.gpr .r0=1 ∧ Spec.Ffdh.generationPrecompute (stackArg s 0).toNat
    (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)=
      some (Spec.Rsa.wordsAt t.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
  rw [status,count,domain,domainBytes,output,ctxLen]
  exact ⟨rfl,result⟩

end VG.Proof.Ffdh.Arm

end

end

/-! The complete public comb initializer meets its separately reviewed contract. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CombPrecomputeSerialization.lean`, which only this module imported.
section

/-! Native header, Montgomery prefix, and dense comb entries form the canonical context. -/
section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Bignum (wv read_eq_wv word_eq_ofNat)

private theorem wordsAt_add (m : Mem) (a : Addr) (n k : Nat) :
    Spec.Rsa.wordsAt m a (n+k)=Spec.Rsa.wordsAt m a n ++ Spec.Rsa.wordsAt m (off a (8*n)) k := by
  simp only [Spec.Rsa.wordsAt,List.range_add,List.map_append,List.map_map]
  apply congrArg (fun xs=>(List.range n).map (fun i=>m.readW (a+BitVec.ofNat 64 (8*i)) 64) ++ xs)
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply,off,Offset.add_add,Nat.mul_add]

private theorem wordsAt_read {m : Mem} {a : Addr} {w x : Nat}
    (value : (m.read a (8*w)).toNat=x) :
    Spec.Rsa.wordsAt m a w=Spec.Rsa.toWords x w := by
  have number : wv m a 0 w=x := by
    rw [←read_eq_wv]
    simpa only [off,BitVec.add_zero] using value
  apply List.ext_getElem
  · simp only [Spec.Rsa.wordsAt,Spec.Rsa.toWords,List.length_map,List.length_range]
  · intro i hi _
    have bound : i<w := by simpa only [Spec.Rsa.wordsAt,List.length_map,List.length_range] using hi
    have word := word_eq_ofNat m a 0 w bound
    rw [number] at word
    simpa only [Spec.Rsa.wordsAt,Spec.Rsa.toWords,List.getElem_map,List.getElem_range,Nat.zero_add] using word

private theorem table_words {p : Inputs} {m : Mem} (table : TablePrefix p 32 m) (n : Nat) (hn : n≤32) :
    Spec.Rsa.wordsAt m (off (State.addr p.output) (24+16*p.w)) (n*p.w)=
      (List.range n).flatMap (fun digit=>Spec.Rsa.toWords (entryValue p digit) p.w) := by
  induction n with
  | zero => simp [Spec.Rsa.wordsAt]
  | succ n ih =>
    conv_lhs => arg 3; rw [Nat.add_mul,Nat.one_mul]
    rw [wordsAt_add,ih (by omega),List.range_succ,List.flatMap_append]
    simp only [List.flatMap_singleton]
    congr 1
    have addr : off (off (State.addr p.output) (24+16*p.w)) (8*(n*p.w))=
        off (State.addr p.output) (entryOffset p n) := by
      unfold off
      rw [Offset.add_add]
      rw [show 24+16*p.w+8*(n*p.w)=entryOffset p n by unfold entryOffset;ring]
    rw [addr]
    exact wordsAt_read (table n (by omega))

theorem canonical_words {p : Inputs} {m : Mem}
    (header : Spec.Rsa.wordsAt m (State.addr p.output) 3=
      [BitVec.ofNat 64 (bits p),BitVec.ofNat 64 ((bits p+7)/8),
        BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows (bits p))])
    (montgomery : Spec.Rsa.wordsAt m (off (State.addr p.output) 24) (2*p.w)=
      Spec.Rsa.toWords p.P p.w ++ Spec.Rsa.toWords (2^(128*p.w)%p.P) p.w)
    (table : TablePrefix p 32 m) :
    Spec.Rsa.wordsAt m (State.addr p.output) (Spec.Ffdh.generationPrecomputedWords p.k)=
      VG.Proof.Ffdh.generationValues p.k p.dom := by
  have length : Spec.Ffdh.generationPrecomputedWords p.k=3+(2*p.w+32*p.w) := by
    simp only [Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,
      Spec.Rsa.precomputedWords,Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth,Inputs.w]
  rw [length,wordsAt_add]
  change Spec.Rsa.wordsAt m (State.addr p.output) 3 ++
    Spec.Rsa.wordsAt m (off (State.addr p.output) 24) (2*p.w+32*p.w)=_
  rw [wordsAt_add,header,montgomery]
  have addr : off (off (State.addr p.output) 24) (8*(2*p.w))=
      off (State.addr p.output) (24+16*p.w) := by
    unfold off
    rw [Offset.add_add]
    rw [show 24+8*(2*p.w)=24+16*p.w by omega]
  rw [addr,table_words table 32 (by omega)]
  simp only [VG.Proof.Ffdh.generationValues,Spec.Rsa.FixedBaseComb.table,
    Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth,entryValue,bits,Inputs.P,Inputs.G,Inputs.w,
    Spec.Ffdh.domainOf,List.append_assoc]

theorem canonical_precompute {p : Inputs} {m : Mem}
    (valid : Spec.Rsa.modulusValid p.P p.k=true)
    (header : Spec.Rsa.wordsAt m (State.addr p.output) 3=
      [BitVec.ofNat 64 (bits p),BitVec.ofNat 64 ((bits p+7)/8),
        BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows (bits p))])
    (montgomery : Spec.Rsa.wordsAt m (off (State.addr p.output) 24) (2*p.w)=
      Spec.Rsa.toWords p.P p.w ++ Spec.Rsa.toWords (2^(128*p.w)%p.P) p.w)
    (table : TablePrefix p 32 m) :
    Spec.Ffdh.generationPrecompute p.k p.dom=
      some (Spec.Rsa.wordsAt m (State.addr p.output) (Spec.Ffdh.generationPrecomputedWords p.k)) := by
  rw [canonical_words header montgomery table]
  apply VG.Proof.Ffdh.generationPrecompute_eq _ valid
  rw [p.domainLength]
  split <;> omega

end VG.Proof.Ffdh.Arm.CombBuilder
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CombPrecomputeWords.lean`, which only this module imported.
section

/-! Reuse exact byte preservation for packed context word lists. -/

section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Proof.Bignum.Arm VG.Proof.Mont

theorem wordsAt_eq {base : Addr} {size d count : Nat} {m m' : Mem}
    (h : WorkspaceEq base size m m') (bound : d+8*count≤size) :
    Spec.Rsa.wordsAt m' (off base d) count = Spec.Rsa.wordsAt m (off base d) count := by
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro i hi
  have hi' : i<count := List.mem_range.mp hi
  have read := h.word (d:=d+8*i) (bits:=64) (by omega)
  simpa only [off,BitVec.ofNat_add,←BitVec.add_assoc] using read

end VG.Proof.Ffdh.Arm.CombBuilder
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CombPrecomputeFn.lean`, which only this module imported.
section

/-! The complete callable native public-context initialization. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont CombBuilder
open VG.Proof.Rsa.Mont (numAt)

theorem combPrecomputeEntered_ok (backend : MontBackend) (s : State) {p : Inputs}
    (h : CombPrecomputeFnInput p s) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.CombPrecompute.entry)
      (VG.Impl.Ffdh.Arm.CombPrecompute.main
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VG.Proof.Ffdh.Arm.VettedBound.code))
      (entered s) fun t =>
      Frame (combPrecomputeWrites p (entered s)) (entered s).mem t.mem ∧ t.gpr .r0=1 ∧
      Spec.Ffdh.generationPrecompute p.k p.dom=
        some (Spec.Rsa.wordsAt t.mem (State.addr p.output) (Spec.Ffdh.generationPrecomputedWords p.k)) := by
  have valid := Proof.Ffdh.domainValid_mod h.valid
  change Spec.Rsa.modulusValid p.P p.k=true at valid
  have facts := Proof.Bignum.valid_facts valid p.minLength
  have params : Spec.Ffdh.parametersValid (Spec.Ffdh.domainOf p.k p.dom)=true := by
    have v := h.valid
    unfold Spec.Ffdh.domainValid at v
    simp only [Bool.and_eq_true] at v
    exact v.1
  have bitsPos : 0<bits p := CachedSample.generation_positive params
  have bitsBound : bits p≤8192 := CachedSample.bits_bound p
  have rowsPos : 0<Spec.Rsa.FixedBaseComb.rows (bits p) := by
    unfold Spec.Rsa.FixedBaseComb.rows Spec.Rsa.FixedBaseComb.teeth
    omega
  have rowsFit : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32 := by
    unfold Spec.Rsa.FixedBaseComb.rows Spec.Rsa.FixedBaseComb.teeth
    omega
  let op := VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul
  have grouped : WP isa (.seq
    (.seq (.block VG.Impl.Ffdh.Arm.CombPrecompute.entry) (prefixCode backend))
    (.seq VG.Impl.Ffdh.Arm.CombPrecompute.montgomeryOut
      (.seq (VG.Impl.Ffdh.Arm.CombPrecompute.table op) (VG.Impl.Ffdh.Arm.Domain.ret 1))))
      (entered s) (fun t => Frame (combPrecomputeWrites p (entered s)) (entered s).mem t.mem ∧ t.gpr .r0=1 ∧
        Spec.Ffdh.generationPrecompute p.k p.dom=
          some (Spec.Rsa.wordsAt t.mem (State.addr p.output) (Spec.Ffdh.generationPrecomputedWords p.k))) := by
    rw [WP.seq_iff]
    refine WP.mono (enteredPrefix_ok backend s h) ?_
    rintro u ⟨memory,header,modulus,r2,frameU⟩
    rw [WP.seq_iff]
    refine WP.mono (montgomeryOut_ok u memory) ?_
    rintro v ⟨memoryV,workspaceV,montgomery,frameV,headerV,restV⟩
    rw [modulus,r2] at montgomery
    have modulusV := (workspaceV.number (j:=0) (memory.ready.width ▸ memory.ready.layout.2.2.1) (by decide)).trans modulus
    have r2V := (workspaceV.number (j:=4) (memory.ready.width ▸ memory.ready.layout.2.2.1) (by decide)).trans r2
    have headersV : Spec.Rsa.wordsAt v.mem (State.addr p.output) 3=
        [BitVec.ofNat 64 (bits p),BitVec.ofNat 64 ((bits p+7)/8),BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows (bits p))] := by
      have preserved := wordsAt_eq (d:=0) (count:=3) headerV (by decide)
      simp only [off,BitVec.add_zero] at preserved
      exact preserved.trans header
    rw [WP.seq_iff]
    refine WP.mono (table_ok backend v memoryV modulusV r2V facts.1 rowsPos rowsFit) ?_
    rintro z ⟨coreZ,tableZ,headerZ,frameZ,restZ⟩
    have preservedZ := wordsAt_eq (d:=0) (count:=3) headerZ (by omega)
    simp only [off,BitVec.add_zero] at preservedZ
    have headersZ := preservedZ.trans headersV
    have montgomeryZ := (wordsAt_eq (d:=24) (count:=2*p.w) headerZ (by omega)).trans montgomery
    have serialized := canonical_precompute valid headersZ montgomeryZ tableZ
    refine WP.mono (ret_ok z 1 (by decide)) ?_
    rintro t ⟨⟨result,memT⟩,restT⟩
    have fullV : Frame (combPrecomputeWrites p (entered s)) u.mem v.mem := frameV.sub (by
      intro r hr
      have eq := List.mem_singleton.mp hr
      subst r
      exact ⟨⟨State.addr p.output,bytes p⟩,by simp [combPrecomputeWrites],Offset.sub_base _ (by have := bytes_eq p;omega)⟩)
    have fullZ : Frame (combPrecomputeWrites p (entered s)) v.mem z.mem := by
      simpa only [productWrites,combPrecomputeWrites] using frameZ
    rw [memT] at *
    exact ⟨frameU.trans (fullV.trans fullZ),result,serialized⟩
  obtain ⟨trace,t,exec,post⟩ := grouped
  cases exec with
  | seq hprefix htail =>
    cases hprefix with
    | seq hentry hprepared =>
      cases hprepared with
      | seq hprepare hboundmeta =>
        cases hboundmeta with
        | seq hbound hmetadata =>
          exact ⟨_,_,.seq hentry (.seq hprepare (.seq hbound (.seq hmetadata htail))),post⟩

theorem combPrecomputeFn_ok (backend : MontBackend) (s : State) {p : Inputs}
    (h : CombPrecomputeFnInput p s) :
    WP isa (VG.Impl.Ffdh.Arm.CombPrecompute.code
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VG.Proof.Ffdh.Arm.VettedBound.code) s fun t =>
      abiPreserved s t ∧ t.gpr .r0=1 ∧ Spec.Ffdh.generationPrecompute p.k p.dom=
        some (Spec.Rsa.wordsAt t.mem (State.addr p.output) (Spec.Ffdh.generationPrecomputedWords p.k)) := by
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.code
  refine framed_of_separate _ s (by have := h.stackFits;omega) (combPrecomputeWrites p (entered s))
    (fun mem status => status=1 ∧ Spec.Ffdh.generationPrecompute p.k p.dom=
      some (Spec.Rsa.wordsAt mem (State.addr p.output) (Spec.Ffdh.generationPrecomputedWords p.k))) h.saved ?_
  exact combPrecomputeEntered_ok backend s h

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CombPrecomputeCorrect.lean`, which only this module imported.
section

/-! Native public precomputation satisfies the reviewed immutable-context contract. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts)

theorem combPrecompute_correct (backend : MontBackend) (s : State)
    (pre : (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts) 176).pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.Arm.CombPrecompute.code
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VettedBound.code) s tr t ∧
      abiPreserved s t ∧
      (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts) 176).post s t := by
  obtain ⟨p,_base,output,domain,count,_capacity,domainBytes,ctxLen,_private,_public,_entropy,input⟩ :=
    combPrecompute_data s pre
  obtain ⟨tr,t,run,preserved,status,result⟩ := combPrecomputeFn_ok backend s input
  exact ⟨tr,t,run,preserved,post_consts.mpr
    (combPrecompute_post s t output domain count domainBytes ctxLen status result)⟩

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CombPrecomputeFnCT.lean`, which only this module imported.
section

/-! The public precompute frame and fixed argument stores preserve its timing policy. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem combPrecomputeFn_ct (backend : MontBackend) {p : Inputs}
    (mainTiming : ∀ {sp : BitVec 32},
      RelCT isa (fun s t=>CombBuilder.EnterInput p sp s ∧ CombBuilder.EnterInput p sp t ∧
        VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
        (VG.Impl.Ffdh.Arm.CombPrecompute.main
          (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VettedBound.code) (fun _ _=>True)) :
    RelCT isa (fun s t => CombPrecomputeFnInput p s ∧ CombPrecomputeFnInput p t ∧
      VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
      (VG.Impl.Ffdh.Arm.CombPrecompute.code
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VettedBound.code) (fun _ _=>True) := by
  let P := fun a : State => ∃s,CombPrecomputeFnInput p s ∧ a=entered s
  let Q := fun a : State => ∃sp,CombBuilder.EnterInput p sp a
  have wp (a : State) (h : P a) : WP isa (.block VG.Impl.Ffdh.Arm.CombPrecompute.entry) a Q := by
    obtain ⟨s,input,rfl⟩ := h
    refine WP.mono_syms (withAllRest (combEntry_ok (entered s) input.args input.incomingCount input.incomingBase
      input.outputReg input.domainReg input.domainLengthReg)) ?_
    rintro u ⟨⟨ctx,frame⟩,rest⟩ syms
    have context : Context p CombBuilder.slots u :=
      ⟨⟨ctx.workspace,ctx.locals,ctx.domain,ctx.domainStack,fun d hd=>
        ctx.saved d (by simp only [CombBuilder.slots,List.mem_cons,List.not_mem_nil,or_false] at hd ⊢; omega)⟩,ctx.ptr⟩
    have environment := VettedGroups.environment.stable input.environment
      (frame.mono (by simp [keyCallWrites,keyWrites])) rest syms
    exact ⟨(entered s).sp,context,environment,input.calls.after rest,input.output.after rest,
      input.workspaceSeparate,input.domainSeparate,input.localSeparate,input.callSeparate,rest.sp,input.valid⟩
  have entry : RelCT isa (fun s t=>P s ∧ P t ∧ VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
      (.block VG.Impl.Ffdh.Arm.CombPrecompute.entry)
      (fun s t=>VettedGroups.environment.publicRel s t ∧ s.sp=t.sp) := by
    intro s t tr1 tr2 u v h e1 e2
    have ct := relCT_keep_sp (combEntry_ct.mono (P' :=fun (s t : State)=>P s ∧ P t ∧ VettedGroups.environment.publicRel s t ∧ s.sp=t.sp) (fun _ _ k=>k.2.2.2) (fun _ _ _=>trivial))
      (fun _ _ k=>k.2.2.2)
    refine ⟨(ct s t tr1 tr2 u v h e1 e2).1,?_,(ct s t tr1 tr2 u v h e1 e2).2⟩
    change u.syms VG.Impl.Ffdh.Arm.VettedGroups.tableSym=v.syms VG.Impl.Ffdh.Arm.VettedGroups.tableSym
    rw [VG.Arm.Exec.syms e1,VG.Arm.Exec.syms e2]
    exact h.2.2.1
  have body : RelCT isa (fun s t=>P s ∧ P t ∧ VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
      (.seq (.block VG.Impl.Ffdh.Arm.CombPrecompute.entry)
        (VG.Impl.Ffdh.Arm.CombPrecompute.main
          (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VettedBound.code)) (fun _ _=>True) := by
    refine (entry.wp (fun s t h=>⟨wp s h.1,wp t h.2.1⟩)).seq ?_
    intro s t tr1 tr2 u v ⟨⟨pubEq,sp⟩,⟨sp1,h1⟩,⟨sp2,h2⟩⟩ e1 e2
    have eq : sp1=sp2 := h1.fixed.symm.trans (sp.trans h2.fixed)
    subst sp2
    exact mainTiming s t tr1 tr2 u v ⟨h1,h2,pubEq,sp⟩ e1 e2
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.code
  apply framed_ct (fun _ _ h=>⟨by have := h.1.stackFits; omega,by have := h.2.1.stackFits; omega⟩)
    (fun _ _ h=>h.2.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s,t,related,rfl,rfl⟩ := h
  exact body _ _ _ _ _ _ ⟨⟨s,related.1,rfl⟩,⟨t,related.2.1,rfl⟩,related.2.2.1,
    by rw [entered_sp,entered_sp,related.2.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CombPrecomputeContractCT.lean`, which only this module imported.
section

/-! The cached-context writer depends only on public domain bytes and addresses. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts tableSym tableWords)

theorem combPrecompute_contract_ct (backend : MontBackend)
    (mainTiming : ∀ {p : Inputs} {sp : BitVec 32}, Spec.Ffdh.domainValid p.k p.dom=true →
      RelCT isa (fun s t=>CombBuilder.EnterInput p sp s ∧ CombBuilder.EnterInput p sp t ∧
        VettedGroups.environment.publicRel s t ∧ s.sp=t.sp)
        (VG.Impl.Ffdh.Arm.CombPrecompute.main
          (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VettedBound.code) (fun _ _=>True)) :
    ConstantTime isa (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts) 176).pre
      (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts) 176).pub
      (VG.Impl.Ffdh.Arm.CombPrecompute.code
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VettedBound.code) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p,base,output,domain,count,capacity,domainBytes,_words,privateAlias,publicAlias,entropyAlias,inputS⟩ :=
    combPrecompute_data s hs
  have symbol := VettedGroups.consts_singleton_symEq (name:=tableSym) (words:=tableWords) (pub_consts.mp hp).2
  have hp := (pub_consts.mp hp).1
  sig_pub [Spec.Ffdh.generationPrecomputeContract,Spec.Ffdh.generationPrecomputeSig,
    abi,argRegs,reduceClassify,Loc.val,State.addr] at hp
  obtain ⟨sp,bytes,p0,_p1,p2,p3,p4,p5,p6⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map,Function.comp_def,BitVec.ofNat_toNat,BitVec.setWidth_eq,List.map_id'] at byteEq
  rw [←p2,←p3] at byteEq
  have environmentT := combPrecompute_environment t ht (p5.symm.trans base) (p0.symm.trans output)
    (by rw [←p6]; exact capacity) (by rw [←p4]; exact count) privateAlias publicAlias
  have inputT := combPrecompute_input t ht (p:=p) (p5.symm.trans base) (p0.symm.trans output)
    (p2.symm.trans domain) (by rw [←p4]; exact count) (by rw [←p6]; exact capacity)
    ?_ privateAlias publicAlias entropyAlias environmentT
  · exact (combPrecomputeFn_ct backend (mainTiming inputS.valid) s t tr1 tr2 u v ⟨inputS,inputT,symbol,sp⟩ e1 e2).1
  · rw [←p3,←domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r2)) (s.gpr .r3).toNat=p.dom
    rw [←byteEq,domain]
    exact domainBytes

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts)

theorem combPrecompute_verified (backend : MontBackend) :
    Verified target (VG.Impl.Ffdh.Arm.CombPrecompute.code
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VettedBound.code)
      (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts) 176) :=
  ⟨combPrecompute_correct backend,
    combPrecompute_contract_ct backend (CombBuilder.main_ct backend),combPrecompute_sat⟩

/-- The caller transform is part of the registered initializer. -/
def combPrecomputeCalledCode (backend : MontBackend) : Prog isa :=
  backend.caller.code (VG.Impl.Ffdh.Arm.CombPrecompute.code
    (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VettedBound.code)

theorem combPrecomputeCalled_verified (backend : MontBackend) :
    Verified target (combPrecomputeCalledCode backend)
      (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts) 176) :=
  backend.caller.verified (combPrecompute_verified backend)

end VG.Proof.Ffdh.Arm
