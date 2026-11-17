module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ImportPrefixTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SampleTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.InverseUnique
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ScalarRangeTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.OutputTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PublicRangeTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.CombTiming
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ImportFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceEncoding
public import VerifiedGarbage.Proof.Ffdh.Domain
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceSlices
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MemoryState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.OutputFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SampleMask
public import VerifiedGarbage.Proof.Ffdh.VettedPolicy
public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Cut
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
public import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Initial
import VerifiedGarbage.Proof.Mont.WordsCanonical
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ReadEnv
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Frame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.RangeFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Comb
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Finish
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Clear
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Bignum.Math

/-! ### `Ffdh.AArch64.Cached.GeneratePrepared`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.GenerateBody`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.KeyStatus`, which this module and modules that import it used -/

section

/-! Range predicates recover the complete reviewed key-status policy on checked domains. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG

theorem bit_decide (p : Prop) [Decidable p] :
 BitVec.ofNat 64 (decide p).toNat=(if p then 1#64 else 0#64) := by
 by_cases h : p
 · rw [decide_eq_true h,ite_eq_left h];rfl
 · rw [decide_eq_false h,ite_eq_right h];rfl

theorem keyStatus_ranges {a : Spec.Ffdh.Parameters} (valid : Spec.Ffdh.parametersValid a=true) (x : Nat) :
 Spec.Ffdh.keyStatus a x=
 if 0<x ∧ x<Spec.Ffdh.scalarBound a then
  if 1<Spec.Rsa.powMod a.g x a.p ∧ Spec.Rsa.powMod a.g x a.p<a.p-1 then 1 else 3
 else 2 := by
 have scalar : Spec.Ffdh.privateValid a x=false ↔ ¬(0<x ∧ x<Spec.Ffdh.scalarBound a) := by
  simp [Spec.Ffdh.privateValid,Spec.Ffdh.scalarBound]
 rw [VG.Proof.Ffdh.KeyScalar.keyStatus_eq valid]
 simp only [scalar,VG.Proof.Bignum.powMod_eq,VG.Proof.Ffdh.publicValid_power valid x]
 by_cases accepted : 0<x ∧ x<Spec.Ffdh.scalarBound a <;> simp [accepted]

theorem keyStatus_scalar_rejected {a : Spec.Ffdh.Parameters} (valid : Spec.Ffdh.parametersValid a=true) (x : Nat) :
 Spec.Ffdh.keyStatus a x=2 ↔ ¬(0<x ∧ x<Spec.Ffdh.scalarBound a) := by
 rw [keyStatus_ranges valid]
 split
 · split <;> simp_all
 · simp_all

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! The complete post-sampling operation has the reviewed scalar/key status and exact outputs. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/Fail.lean`, which only this module imported.
section

/-! A rejected scalar returns 2 and zeroes both complete outputs. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem fail_ok {s : State} {B xp yp : Addr} {Z k : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B) (positive : 0<k) (size : k<2^31)
 (x : word s.mem B (8*sX)=xp) (y : word s.mem B (8*sY)=yp) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (writeX : ∀ i<k,InRegions s.wr (xp+BitVec.ofNat 64 i) 1)
 (writeY : ∀ i<k,InRegions s.wr (yp+BitVec.ofNat 64 i) 1)
 (outsideX : ∀ i<k,Z≤ofs B (xp+BitVec.ofNat 64 i))
 (separate : ∀ i<k,k≤ofs yp (xp+BitVec.ofNat 64 i)) :
 WP isa Generate.fail s fun t =>
 t.gpr .x0=2#64 ∧ Spec.Rsa.bytesAt t.mem xp k=List.replicate k 0 ∧
 Spec.Rsa.bytesAt t.mem yp k=List.replicate k 0 ∧ Frame [⟨xp,k⟩,⟨yp,k⟩] s.mem t.mem ∧ Keep (.x0::mmRegs) s t := by
 unfold Generate.fail
 rw [WP.seq_iff]
 refine WP.mono (clear_ok scratch room base positive size (by decide : sX<32) x length writeX) ?_
 rintro a ⟨zeroX,frameX,restX⟩
 have sameScratch (q : Addr) (hq : ofs B q<Z) : a.mem q=s.mem q :=
  frameX q (Or.inr (by have sep : k≤ofs xp q := le_ofs_of_sep outsideX hq;omega_using [sep]))
 have sameHeader (i : Nat) (hi : i<32) : word a.mem B (8*i)=word s.mem B (8*i) :=
  workspace_word (by have := scratch.nowrap;omega_using [this]) sameScratch (by omega_using [room, hi])
 rw [WP.seq_iff]
 refine WP.mono (clear_ok (scratch.congr restX.wr) room ((restX.gpr .x0 (by decide)).trans base) positive size
  (by decide : sY<32) ((sameHeader sY (by decide)).trans y) ((sameHeader sLen (by decide)).trans length)
  (fun i hi =>by rw [restX.wr];exact writeY i hi)) ?_
 rintro b ⟨zeroY,frameY,restY⟩
 have xBytes : Spec.Rsa.bytesAt b.mem xp k=List.replicate k 0 := by
  rw [←zeroX]
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range]
  · intro i hi _
    have bound : i<k := by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi
    simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range]
    exact frameY _ (Or.inr (by have := separate i bound;omega_using [this]))
 have frame (ptr : Addr) {m m' : Mem} (h : Outside ptr 0 k m m')
  (member : (⟨ptr,k⟩ : Region)∈[⟨xp,k⟩,⟨yp,k⟩]) : Frame [⟨xp,k⟩,⟨yp,k⟩] m m' := by
  intro q hq
  apply h q
  right
  have no := hq ⟨ptr,k⟩ member
  change ¬ofs ptr q+1≤k at no
  omega_using [no]
 refine WP.mono (WP.keep [.x0] (Q:=fun t =>t.gpr .x0=2#64 ∧ t.mem=b.mem) ?_ rfl rfl rfl) ?_
 · brun
 · rintro t ⟨⟨status,mem⟩,rest⟩
   exact ⟨status,by rw [mem];exact xBytes,by rw [mem];exact zeroY,
    by rw [mem];exact (frame xp frameX (by simp)).trans (frame yp frameY (by simp)),
    ((restX.trans restY).trans rest).mono (by decide)⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

def generateBody (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
 .seq Generate.scalarRange (.ite (.zero .x .x9) Generate.fail
  (.seq (Comb.code mul) (.seq Generate.publicRange Generate.finish)))

theorem generateBody_ok (M : Mont) {p : Parameters} {s : State} {bs dom : List Byte} {dp yp : Addr} {dl : Nat}
 (start : Initial p bs s) (words : p.w=(p.k+7)/8) (positive : 0<p.k) (size : p.k<2^31)
 (shape : dl=2*p.k ∨ dl=3*p.k) (domLength : dom.length=dl)
 (valid : Spec.Ffdh.domainValid p.k dom=true)
 (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p) (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g)
 (domainSource : Src s p.B p.Z dp dom)
 (domain : word s.mem p.B (8*sDom)=dp) (domainLength : word s.mem p.B (8*sDL)=BitVec.ofNat 64 dl)
 (outputY : word s.mem p.B (8*sY)=yp)
 (bitsPositive : 0<p.N) (bitsBound : p.N≤8192) (scalarWidth : p.N≤8*p.k) (scalarBound : Spec.Rsa.os2ip bs<2^p.N)
 (table : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w))
 (writeX : ∀ i<p.k,InRegions s.wr (p.src+BitVec.ofNat 64 i) 1)
 (writeY : ∀ i<p.k,InRegions s.wr (yp+BitVec.ofNat 64 i) 1)
 (outsideY : ∀ i<p.k,p.Z≤ofs p.B (yp+BitVec.ofNat 64 i))
 (separate : ∀ i<p.k,p.k≤ofs yp (p.src+BitVec.ofNat 64 i)) :
 WP isa (generateBody M.mm) s fun t =>
 t.gpr .x0=BitVec.ofNat 64 (Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k dom) (Spec.Rsa.os2ip bs)) ∧
 (if Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k dom) (Spec.Rsa.os2ip bs)=1 then
  Spec.Rsa.bytesAt t.mem p.src p.k=Spec.Rsa.i2osp (Spec.Rsa.os2ip bs) p.k ∧
  Spec.Rsa.bytesAt t.mem yp p.k=Spec.Rsa.i2osp (Spec.Rsa.powMod p.G (Spec.Rsa.os2ip bs) p.P) p.k
 else Spec.Rsa.bytesAt t.mem p.src p.k=List.replicate p.k 0 ∧ Spec.Rsa.bytesAt t.mem yp p.k=List.replicate p.k 0) ∧
 Keep (.x0::mmRegs) s t := by
 let a := Spec.Ffdh.domainOf p.k dom
 let X := Spec.Rsa.os2ip bs
 have bsLength := start.reads.length
 have paramValid : Spec.Ffdh.parametersValid a=true := by
  have h := valid
  unfold Spec.Ffdh.domainValid at h
  simp only [Bool.and_eq_true] at h
  exact h.1
 have odd : p.P%2=1 := by
  have h := VG.Proof.Ffdh.domainValid_mod valid
  simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  rw [modulus]
  exact h.1.1.1
 have room256 : 256≤p.Z := by have := p.room;dsimp only [slot,hdrBytes] at this;omega_using [this]
 have outsideX (i : Nat) (hi : i<p.k) : p.Z≤ofs p.B (p.src+BitVec.ofNat 64 i) := start.reads.scalarOutside i (by omega_using [bsLength, hi])
 have length : word s.mem p.B (8*sLen)=BitVec.ofNat 64 p.k := bsLength ▸ start.controls.length
 have status := keyStatus_ranges paramValid X
 change Spec.Ffdh.keyStatus a X=(if 0<X ∧ X<Spec.Ffdh.scalarBound a then _ else 2) at status
 rw [←modulus,←generator] at status
 unfold generateBody
 rw [WP.seq_iff]
 refine WP.mono (scalarRange_ok start.good p.room words positive size shape domLength domainSource
  (source_src start.reads.source start.reads.scalarOutside) bsLength start.controls.source domain length domainLength
  (start.modulus.trans modulus) (by rw [←modulus];exact odd)) ?_
 rintro r ⟨goodR,_,flagR,frameR,restR⟩
 have startR := start.after_scalarRange goodR frameR restR
 have yR : word r.mem p.B (8*sY)=yp := (scalarFrame_header frameR (by decide) (by decide)).trans outputY
 have lenR : word r.mem p.B (8*sLen)=BitVec.ofNat 64 p.k := bsLength ▸ startR.controls.length
 by_cases accepted : 0<X ∧ X<Spec.Ffdh.scalarBound a
 · have condition : isa.eval (.zero .x .x9) r=some false := by
    rw [eval_zero,flagR,ite_eq_left accepted];decide
   have branch : WP isa (.seq (Comb.code M.mm) (.seq Generate.publicRange Generate.finish)) r fun t =>
    t.gpr .x0=BitVec.ofNat 64 (Spec.Ffdh.keyStatus a X) ∧
    (if Spec.Ffdh.keyStatus a X=1 then
     Spec.Rsa.bytesAt t.mem p.src p.k=Spec.Rsa.i2osp X p.k ∧
     Spec.Rsa.bytesAt t.mem yp p.k=Spec.Rsa.i2osp (Spec.Rsa.powMod p.G X p.P) p.k
    else Spec.Rsa.bytesAt t.mem p.src p.k=List.replicate p.k 0 ∧ Spec.Rsa.bytesAt t.mem yp p.k=List.replicate p.k 0) ∧
    Keep (.x0::mmRegs) s t := by
    rw [WP.seq_iff]
    refine WP.mono (comb_correct M startR bitsPositive bitsBound (bsLength ▸ size) (bsLength ▸ scalarWidth) scalarBound table) ?_
    rintro b ⟨stateB,valueB,controlsB,readsB,stableB,restB⟩
    have yB : word b.mem p.B (8*sY)=yp := (stableB sY (by decide) (by decide) (by decide) (by decide)).trans yR
    rw [WP.seq_iff]
    refine WP.mono (publicRange_ok stateB odd) ?_
    rintro c ⟨stateC,sameY,flagC,headerC,frameC,restC⟩
    let ok : Bool := decide (1<Spec.Rsa.powMod p.G X p.P ∧ Spec.Rsa.powMod p.G X p.P<p.P-1)
    have flag : word c.mem p.B (8*sTmp)=BitVec.ofNat 64 ok.toNat := by
     rw [headerC,flagC,valueB]
     exact (bit_decide (1<Spec.Rsa.powMod p.G X p.P ∧ Spec.Rsa.powMod p.G X p.P<p.P-1)).symm
    have readsC := readsB.after_inscr (InScr.of_frm frameC
     (fun r hr =>Nat.le_trans (publicRangeRanges_le _ r hr) p.room)) restC
    have xC : word c.mem p.B (8*sX)=p.src := (publicRangeFrame_header frameC (by decide) (by decide)).trans controlsB.source
    have yC : word c.mem p.B (8*sY)=yp := (publicRangeFrame_header frameC (by decide) (by decide)).trans yB
    have lenC : word c.mem p.B (8*sLen)=BitVec.ofNat 64 p.k :=
     (publicRangeFrame_header frameC (by decide) (by decide)).trans (bsLength ▸ controlsB.length)
    have sourceC := source_encoding readsC.source
    rw [bsLength] at sourceC
    have statusOk : Spec.Ffdh.keyStatus a X=(if ok then 1 else 3) := by
     rw [status,ite_eq_left accepted]
     simp only [ok,decide_eq_true_eq]
    have before := (restR.trans restB).trans restC
    refine WP.mono (finish_ok stateC.good p.room words positive size xC yC lenC flag
     (fun i hi =>by rw [before.wr];exact writeX i hi)
     (fun i hi =>by rw [before.wr];exact writeY i hi) outsideX outsideY separate) ?_
    rintro t ⟨ret,xT,yT,_,restT⟩
    rw [sourceC] at xT
    rw [sameY,valueB] at yT
    refine ⟨?_,?_,(before.trans restT).mono (by decide)⟩
    · rw [ret,statusOk]
      cases ok <;>rfl
    · rw [statusOk]
      cases h : ok
      · simpa only [h,ite_false,Bool.false_eq_true,show ¬(3:Nat)=1 by decide,i2osp_zero'] using And.intro xT yT
      · simpa only [h,ite_true] using And.intro xT yT
   obtain ⟨tr,t,run,post⟩ := branch
   exact ⟨_,t,.iteF condition run,post⟩
 · have condition : isa.eval (.zero .x .x9) r=some true := by
    rw [eval_zero,flagR,ite_eq_right accepted];decide
   have code := fail_ok goodR.scr room256 goodR.x0 positive size startR.controls.source yR lenR
    (fun i hi =>by rw [restR.wr];exact writeX i hi)
    (fun i hi =>by rw [restR.wr];exact writeY i hi) outsideX separate
   obtain ⟨tr,t,run,ret,xT,yT,_,restT⟩ := code
   refine ⟨_,t,.iteT condition run,?_,?_,(restR.trans restT).mono (by decide)⟩
   · rw [ret,status,ite_eq_right accepted]
   · rw [status,ite_eq_right accepted]
     exact ⟨xT,yT⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.GenerateFront`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.ContextView`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.Context`, which this module and modules that import it used -/

section

/-! Native 64-bit reads of the already reviewed, backend-independent context. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Proof.Bignum

theorem context_words {m : Mem} {ctx : Addr} {count k : Nat} {dom : List Byte}
 (length : k≤dom.length) (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (dom.take k)) k=true)
 (canonical : Spec.Ffdh.generationContextAt m ctx count k dom) :
 Spec.Rsa.wordsAt m ctx count=VG.Proof.Ffdh.generationValues k dom := by
 have equation := VG.Proof.Ffdh.generationPrecompute_eq length valid
 rw [canonical.2] at equation
 exact Option.some.inj equation

theorem context_words_count {m : Mem} {ctx : Addr} {count k : Nat} {dom : List Byte}
 (canonical : Spec.Ffdh.generationContextAt m ctx count k dom) :
 count=3+34*Spec.Rsa.modulusWords k := by
 rw [canonical.1]
 simp only [Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,
  Spec.Rsa.precomputedWords,Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth]
 omega_using []

theorem context_header {m : Mem} {ctx : Addr} {count k j : Nat} {dom : List Byte}
 (length : k≤dom.length) (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (dom.take k)) k=true)
 (canonical : Spec.Ffdh.generationContextAt m ctx count k dom) (hj : j<3) :
 m.readW (ctx+BitVec.ofNat 64 (8*j)) 64=
 ([BitVec.ofNat 64 (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom)),
  BitVec.ofNat 64 ((Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom)+7)/8),
  BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom)))] : List (BitVec 64)).getD j 0 := by
 have words := congrArg (fun xs : List (BitVec 64) => xs[j]?) (context_words length valid canonical)
 have count3 : 3≤count := by rw [context_words_count canonical];omega_using []
 simp only [Spec.Rsa.wordsAt,List.getElem?_map,List.getElem?_range (by omega_using [hj, count3] : j<count),Option.map_some] at words
 have heads := congrArg (fun xs : List (BitVec 64) => xs[j]?) (VG.Proof.Ffdh.generationValues_headers k dom)
 simp only [List.getElem?_take,ite_eq_left hj] at heads
 rw [heads] at words
 have cases : j=0 ∨ j=1 ∨ j=2 := by omega_using [hj]
 rcases cases with rfl | rfl | rfl <;> simpa using words

/-- Entry a is a complete reduced Montgomery residue with no backend pointers. -/
theorem context_table_entry {m : Mem} {ctx : Addr} {count k a : Nat} {dom : List Byte}
 (length : k≤dom.length) (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (dom.take k)) k=true)
 (canonical : Spec.Ffdh.generationContextAt m ctx count k dom) (ha : a<32) :
 let w := Spec.Rsa.modulusWords k
 let P := (Spec.Ffdh.domainOf k dom).p
 let G := (Spec.Ffdh.domainOf k dom).g
 let N := Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom)
 wv m ctx (24+16*w+8*w*a) w=
  Spec.Rsa.powMod G (Spec.Rsa.FixedBaseComb.exponent N a) P * 2^(64*w)%P := by
 dsimp only
 let w := Spec.Rsa.modulusWords k
 let E := Spec.Rsa.powMod (Spec.Ffdh.domainOf k dom).g
  (Spec.Rsa.FixedBaseComb.exponent (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom)) a)
  (Spec.Ffdh.domainOf k dom).p *2^(64*w)%(Spec.Ffdh.domainOf k dom).p
 have pBound : (Spec.Ffdh.domainOf k dom).p<2^(64*w) := by
  have bound := VG.Proof.Bignum.os2ip_lt (dom.take k)
  have len : (dom.take k).length=k := by simp only [List.length_take];omega_using [length]
  rw [len,VG.Proof.Bignum.pow256_eq] at bound
  exact Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (by dsimp [w,Spec.Rsa.modulusWords];omega_using []))
 have pPositive : 0<(Spec.Ffdh.domainOf k dom).p := by
  have facts := valid
  simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,decide_eq_true_eq] at facts
  change 0<Spec.Rsa.os2ip (dom.take k)
  omega
 have eBound : E<2^(64*w) := Nat.lt_trans (Nat.mod_lt _ pPositive) pBound
 change wv m ctx (24+16*w+8*w*a) w=E
 rw [←Nat.mod_eq_of_lt eBound]
 apply wv_of_words
 intro i hi
 let index := 3+(2+a)*w+i
 have indexFit : index<count := by
  have hcount := context_words_count canonical
  have aW := Nat.mul_le_mul_right w (show 2+a≤33 by omega_using [ha])
  dsimp [index,w] at *
  omega_using [hi, hcount, aW]
 have entry := congrArg (fun xs : List (BitVec 64) => xs[i]?) (VG.Proof.Ffdh.generationValues_entry k dom a ha)
 have hik : i<Spec.Rsa.modulusWords k := hi
 simp only [List.getElem?_take,ite_eq_left hik,List.getElem?_drop,Spec.Rsa.toWords,
  List.getElem?_map,List.getElem?_range hik,Option.map_some] at entry
 have read := congrArg (fun xs : List (BitVec 64) => xs[index]?) (context_words length valid canonical)
 simp only [Spec.Rsa.wordsAt,List.getElem?_map,List.getElem?_range indexFit,Option.map_some] at read
 change some (m.readW (off ctx (8*index)) 64)=_ at read
 dsimp only [index,w] at read
 rw [entry] at read
 have offset : 24+16*w+8*w*a+8*i=8*index := by dsimp [index];ring
 change (m.readW (off ctx (24+16*w+8*w*a+8*i)) 64).toNat=_
 rw [offset,Option.some.inj read,BitVec.toNat_ofNat]

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! The immutable canonical input survives scratch setup and output sampling. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/ContextReads.lean`, which only this module imported.
section

/-! The reviewed canonical context supplies all native comb reads and values. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum

theorem context_readEnv {p : Parameters} {s : State} {count : Nat} {dom bs : List Byte}
 (words : p.w=Spec.Rsa.modulusWords p.k) (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p)
 (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g) (policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom))
 (pointer : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w))
 (length : p.k≤dom.length) (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (dom.take p.k)) p.k=true)
 (canonical : Spec.Ffdh.generationContextAt s.mem p.ctx count p.k dom)
 (scalar : Source p.src bs s) (scalarLength : bs.length=p.k)
 (scalarOutside : ∀ i<bs.length,p.Z≤ofs p.B (p.src+BitVec.ofNat 64 i))
 (readable : ∀ i<count,InRegions (s.rd++s.wr) (p.ctx+BitVec.ofNat 64 (8*i)) 8)
 (outside : ∀ i<8*count,p.Z≤ofs p.B (p.ctx+BitVec.ofNat 64 i)) : ReadEnv p bs s := by
 have countEq : count=3+34*p.w := by rw [context_words_count canonical,words]
 have address (j i : Nat) : off p.table (8*p.w*j+8*i)=p.ctx+BitVec.ofNat 64 (8*(3+(2+j)*p.w+i)) := by
  rw [pointer]
  unfold off
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  congr 2
  ring
 have fit (j i : Nat) (hj : j<32) (hi : i<p.w) : 3+(2+j)*p.w+i<count := by
  have multiple := Nat.mul_le_mul_right p.w (show 2+j≤33 by omega_using [hj])
  rw [countEq]
  omega_using [hi, multiple]
 refine ⟨scalar,scalarLength,scalarOutside,?_,?_,?_⟩
 · intro j hj i hi
   rw [address]
   exact readable _ (fit j i hj hi)
 · intro j hj i hi b hb
   rw [address,BitVec.add_assoc,←BitVec.ofNat_add]
   exact outside _ (by have := fit j i hj hi;omega_using [hb, this])
 · intro j hj
   have entry := context_table_entry length valid canonical hj
   have equal : wv s.mem p.table (8*p.w*j) p.w=wv s.mem p.ctx (24+16*p.w+8*p.w*j) p.w := by
    apply wv_congr2
    intro i hi
    unfold word
    rw [address]
    congr 2
    ring
   rw [equal,words,modulus,generator,policy]
   exact entry

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

structure ContextView (B : Addr) (Z : Nat) (ctx : Addr) (count k : Nat) (dom : List Byte) (s : State) : Prop where
 canonical : Spec.Ffdh.generationContextAt s.mem ctx count k dom
 readable : ∀ i<count,InRegions (s.rd++s.wr) (ctx+BitVec.ofNat 64 (8*i)) 8
 outside : ∀ i<8*count,Z≤ofs B (ctx+BitVec.ofNat 64 i)

theorem ContextView.after_inscr {s t : State} {B ctx : Addr} {Z count k : Nat} {dom : List Byte} {rs : List Reg}
 (view : ContextView B Z ctx count k dom s) (frame : InScr B Z s.mem t.mem) (rest : Keep rs s t) :
 ContextView B Z ctx count k dom t := by
 have words : Spec.Rsa.wordsAt t.mem ctx count=Spec.Rsa.wordsAt s.mem ctx count := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.wordsAt,List.length_map,List.length_range]
  · intro i hi _
    have bound : i<count := by simpa only [Spec.Rsa.wordsAt,List.length_map,List.length_range] using hi
    simp only [Spec.Rsa.wordsAt,List.getElem_map,List.getElem_range]
    apply Mem.readW_congr
    intro j hj
    have outside := view.outside (8*i+j) (by omega_using [bound, hj])
    exact frame _ (by simpa only [BitVec.ofNat_add,BitVec.add_assoc] using outside)
 refine ⟨?_,?_,view.outside⟩
 · unfold Spec.Ffdh.generationContextAt
   rw [words]
   exact view.canonical
 · intro i hi;rw [rest.rd,rest.wr];exact view.readable i hi

theorem ContextView.after_output {s t : State} {B ctx out : Addr} {Z count k : Nat} {dom : List Byte} {rs : List Reg}
 (view : ContextView B Z ctx count k dom s) (frame : Frame [⟨B,Z⟩,⟨out,k⟩] s.mem t.mem) (rest : Keep rs s t)
 (outside : ∀ i<8*count,k≤ofs out (ctx+BitVec.ofNat 64 i)) : ContextView B Z ctx count k dom t := by
 have words : Spec.Rsa.wordsAt t.mem ctx count=Spec.Rsa.wordsAt s.mem ctx count := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.wordsAt,List.length_map,List.length_range]
  · intro i hi _
    have bound : i<count := by simpa only [Spec.Rsa.wordsAt,List.length_map,List.length_range] using hi
    simp only [Spec.Rsa.wordsAt,List.getElem_map,List.getElem_range]
    apply Mem.readW_congr
    intro j hj
    apply frame
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · have sep := view.outside (8*i+j) (by omega_using [bound, hj])
      have h : Z≤ofs B (ctx+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 j) :=
       by simpa only [BitVec.ofNat_add,BitVec.add_assoc] using sep
      change ¬ofs B (ctx+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 j)+1≤Z
      omega_using [h]
    · have sep := outside (8*i+j) (by omega_using [bound, hj])
      have h : k≤ofs out (ctx+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 j) :=
       by simpa only [BitVec.ofNat_add,BitVec.add_assoc] using sep
      change ¬ofs out (ctx+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 j)+1≤k
      omega_using [h]
 refine ⟨?_,?_,view.outside⟩
 · unfold Spec.Ffdh.generationContextAt
   rw [words]
   exact view.canonical
 · intro i hi;rw [rest.rd,rest.wr];exact view.readable i hi

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.Sample`, which only this module used -/

section

/-! The full native sampler applies the public policy to the complete entropy draw. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/SampleWidth.lean`, which only this module imported.
section

/-! The native mask and byte count encode exactly the reviewed sampler width. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG
open VG.Proof.Ffdh

theorem sample_width {N : Nat} (positive : 0<N) : ScalarWidth.width N=(N+7)/8 := by
 unfold ScalarWidth.width
 omega_using [positive]

theorem sample_headBits {N : Nat} (positive : 0<N) : ScalarWidth.headBits N=(N-1)%8+1 := by
 unfold ScalarWidth.headBits
 rw [sample_width positive]
 omega_using [positive]

theorem sample_mask {N : Nat} (positive : 0<N) : (sampleMask N).setWidth 8=ScalarWidth.mask N := by
 unfold sampleMask ScalarWidth.mask
 rw [sample_headBits positive]
 apply BitVec.eq_of_toNat_eq
 simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
 omega_using []

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/SampleDraw.lean`, which only this module imported.
section

/-! The existing constant-time byte-copy loop realizes the reviewed modular entropy cut. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Ffdh

theorem sampleDraw_bytes {s t : State} {rp xp : Addr} {rb : List Byte} {k ld : Nat} {msk : Addr}
 (inv : VG.Proof.Ffdh.AArch64.GenerateKey.CInv s rp xp rb ld msk k t)
 (length : rb.length=k) (inside : ld<k) :
 Spec.Rsa.bytesAt t.mem xp k=KeyScalar.cut rb ld (msk.setWidth 8) := by
 apply List.ext_getElem
 · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range,KeyScalar.cut_length _ (length ▸ inside)]
   exact length.symm
 · intro i hi _
   obtain bound : i<k := by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi
   simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range]
   rw [inv.bytes i bound,KeyScalar.cut_get _ (length ▸ inside) (by omega_using [length, bound] : i<rb.length)]
   unfold VG.Proof.Ffdh.AArch64.GenerateKey.cb
   simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by omega_using [length, bound] : i<rb.length),Option.getD_some]

theorem sampleDraw_ok {s : State} {rp xp : Addr} {rb : List Byte} {k N : Nat}
 (positive : 0<k) (size : k<2^31) (widthPositive : 0<N) (widthFit : N≤8*k) (length : rb.length=k)
 (random : s.gpr .x1=rp) (output : s.gpr .x2=xp) (index : s.gpr .x10=0#64)
 (skip : s.gpr .x11=BitVec.ofNat 64 (k-(N+7)/8)) (mask : s.gpr .x12=sampleMask N)
 (allOnes : s.gpr .x13=255#64) (zero : s.gpr .x7=0#64) (count : s.gpr .x14=BitVec.ofNat 64 k)
 (readable : ∀ i<k,InRegions (s.rd++s.wr) (rp+BitVec.ofNat 64 i) 1)
 (bytes : ∀ i<k,s.mem (rp+BitVec.ofNat 64 i)=rb.getD i 0)
 (writable : ∀ i<k,InRegions s.wr (xp+BitVec.ofNat 64 i) 1)
 (separate : ∀ i<k,∀ j<k,rp+BitVec.ofNat 64 i≠xp+BitVec.ofNat 64 j) :
 WP isa (countLoop .x14 VG.Impl.Ffdh.AArch64.Domain.GenerateKey.cutBody) s fun t =>
 Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem xp k)=Spec.Rsa.os2ip rb%2^N ∧
 VG.Proof.Ffdh.AArch64.GenerateKey.CInv s rp xp rb (k-(N+7)/8) (sampleMask N) k t := by
 obtain inside : k-(N+7)/8<k := by omega_using [positive, widthPositive]
 refine WP.mono (VG.Proof.Ffdh.AArch64.GenerateKey.cut_ok (by omega_using [positive]) size inside random output
  index skip mask allOnes zero count readable bytes writable separate) ?_
 intro t inv
 refine ⟨?_,inv⟩
 rw [sampleDraw_bytes inv length inside,sample_mask widthPositive]
 obtain width := sample_width widthPositive
 rw [←width]
 obtain cut := ScalarWidth.cut_value (bits:=N) (by omega_using [positive, length] : 0<rb.length) (by omega_using [widthFit, length] : N≤8*rb.length)
 rw [length] at cut
 exact cut

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem sample_ok {s : State} {B xp rp : Addr} {Z w k N : Nat} {mi : BitVec 64} {rb : List Byte}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<k) (size : k<2^31)
 (bitsPositive : 0<N) (bitsBound : N≤8192) (width : N≤8*k) (rbLength : rb.length=k)
 (bits : word s.mem B (8*sBits)=BitVec.ofNat 64 N) (bytes : word s.mem B (8*sBytes)=BitVec.ofNat 64 ((N+7)/8))
 (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k) (x : word s.mem B (8*sX)=xp) (random : word s.mem B (8*sRand)=rp)
 (source : Src s B Z rp rb) (writable : ∀ i<k,InRegions s.wr (xp+BitVec.ofNat 64 i) 1)
 (outside : ∀ i<k,Z≤ofs B (xp+BitVec.ofNat 64 i))
 (separate : ∀ i<k,∀ j<k,rp+BitVec.ofNat 64 i≠xp+BitVec.ofNat 64 j) :
 WP isa Generate.sample s fun t =>
 Good t B Z w mi ∧
 Spec.Rsa.bytesAt t.mem xp k=VG.Proof.Ffdh.KeyScalar.cut rb (k-(N+7)/8) ((sampleMask N).setWidth 8) ∧
 Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem xp k)=Spec.Rsa.os2ip rb%2^N ∧
 (∀ q,ofs B q<Z→t.mem q=(s.mem.writeW (off B (8*sMask)) (sampleMask N)) q) ∧
 Frame [⟨B,Z⟩,⟨xp,k⟩] s.mem t.mem ∧ Keep mmRegs s t := by
 obtain room256 : 256≤Z := by dsimp only [slot,hdrBytes] at room;omega_using [room]
 unfold Generate.sample
 rw [WP.seq_iff]
 refine WP.mono (sampleMask_ok good.scr room256 good.x0 bitsPositive bitsBound bits) ?_
 rintro a ⟨maskA,maskHeaderA,memA,frameA,restA⟩
 obtain goodA := good_after_header good (by decide) (by decide) frameA restA ((restA.gpr .x0 (by decide)).trans good.x0)
 obtain inscrA : InScr B Z s.mem a.mem := InScr.of_outside frameA (by have := hdr_lt_slot w 8 (show sMask<32 by decide);omega_using [room, this])
 rw [WP.seq_iff]
 have headerA (i : Nat) (hi : i<32) (different : i≠sMask) : word a.mem B (8*i)=word s.mem B (8*i) :=
  header_other frameA (by decide) hi different
 obtain subtract : BitVec.ofNat 64 k-BitVec.ofNat 64 ((N+7)/8)=BitVec.ofNat 64 (k-(N+7)/8) :=
  BitVec.ofNat_sub_ofNat_of_le k ((N+7)/8) (by omega_using [bitsBound]) (by omega_using [width])
 refine WP.mono (WP.keep [.x1,.x2,.x7,.x10,.x11,.x13,.x14] (Q:=fun b =>
  b.gpr .x1=rp ∧ b.gpr .x2=xp ∧ b.gpr .x10=0#64 ∧ b.gpr .x11=BitVec.ofNat 64 (k-(N+7)/8) ∧
  b.gpr .x13=255#64 ∧ b.gpr .x7=0#64 ∧ b.gpr .x14=BitVec.ofNat 64 k ∧ b.mem=a.mem) ?_ rfl rfl rfl) ?_
 · brun [goodA.x0,hdr_enc (show sLen<32 by decide),hdr_enc (show sBytes<32 by decide),hdr_enc (show sX<32 by decide),hdr_enc (show sRand<32 by decide),
    header_read goodA room (show sLen<32 by decide),header_read goodA room (show sBytes<32 by decide),
    header_read goodA room (show sX<32 by decide),header_read goodA room (show sRand<32 by decide),
    (headerA sLen (by decide) (by decide)).trans length,(headerA sBytes (by decide) (by decide)).trans bytes,
    (headerA sX (by decide) (by decide)).trans x,(headerA sRand (by decide) (by decide)).trans random,subtract]
 · rintro b ⟨⟨ptrB,outB,indexB,skipB,onesB,zeroB,countB,memB⟩,restB⟩
   obtain total := restA.trans restB
   obtain sourceB := (source.congrK inscrA restA).congrK (fun q _ =>by rw [memB]) restB
   refine WP.mono (sampleDraw_ok positive size bitsPositive width rbLength ptrB outB indexB skipB
    ((restB.gpr .x12 (by decide)).trans maskA) onesB zeroB countB
    (fun i hi =>sourceB.rd i (by omega_using [rbLength, hi])) (fun i hi =>(src_source sourceB).bytes i (by omega_using [rbLength, hi]))
    (fun i hi =>by rw [total.wr];exact writable i hi) separate) ?_
   rintro t ⟨valueT,inv⟩
   have sameScratch (q : Addr) (hq : ofs B q<Z) : t.mem q=a.mem q := by
    rw [inv.frame q ?_,memB]
    intro i hi eq
    obtain sep : k≤ofs xp q := le_ofs_of_sep outside hq
    rw [eq,show ofs xp (xp+BitVec.ofNat 64 i)=i from Mem.sub_ofNat_toNat _ (by omega_using [size, hi])] at sep
    omega_using [room, positive, size, bitsPositive, bitsBound, width, rbLength, bits, bytes, length, x, random, room256, maskA, maskHeaderA, subtract, ptrB, outB, indexB, skipB, onesB, zeroB, countB, valueT, hq, hi, sep]
   obtain rest : Keep mmRegs s t := (total.trans inv.keep).mono (by decide)
   obtain goodT : Good t B Z w mi :=
    ⟨good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,
     (workspace_word (by have := good.scr.nowrap;omega_using [this]) sameScratch (by have := hdr_lt_slot w 8 (show sW<32 by decide);omega_using [room, this])).trans goodA.hdr.hw,
     (workspace_word (by have := good.scr.nowrap;omega_using [this]) sameScratch (by have := hdr_lt_slot w 8 (show sMinv<32 by decide);omega_using [room, this])).trans goodA.hdr.hminv,
     fun i hi =>(workspace_word (by have := good.scr.nowrap;omega_using [this]) sameScratch (by have := hdr_lt_slot w 8 (show sArr i<32 by unfold sArr;omega_using [hi]);omega_using [room, this])).trans (goodA.hdr.harr i hi)⟩
   obtain outsideX : Outside xp 0 k b.mem t.mem := by
    intro q hq
    apply inv.frame q
    intro i hi eq
    subst q
    rw [show ofs xp (xp+BitVec.ofNat 64 i)=i from Mem.sub_ofNat_toNat _ (by omega_using [size, hi])] at hq
    omega_using [room, positive, size, bitsPositive, bitsBound, width, rbLength, bits, bytes, length, x, random, room256, maskA, maskHeaderA, subtract, ptrB, outB, indexB, skipB, onesB, zeroB, countB, valueT, hi, hq]
   obtain frameMask : Frame [⟨B,Z⟩,⟨xp,k⟩] s.mem a.mem := outside_frame_member (ptr:=B) (k:=Z)
    (fun q h =>inscrA q (by omega_using [h])) (by simp)
   obtain frameOutput : Frame [⟨B,Z⟩,⟨xp,k⟩] a.mem t.mem := by
    rw [←memB];exact outside_frame_member outsideX (by simp)
   exact ⟨goodT,sampleDraw_bytes inv rbLength (by omega_using [positive, bitsPositive]),valueT,
    fun q hq =>(sameScratch q hq).trans (by rw [memA]),frameMask.trans frameOutput,rest⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Connect immutable context import and policy sampling to the comb's initial state. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/ContextPrefix.lean`, which only this module imported.
section

/-! The canonical context contains exact, unreduced-width p and reduced R² limbs. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Proof.Bignum

theorem context_prefix {m : Mem} {ctx : Addr} {count k : Nat} {dom : List Byte}
 (length : k≤dom.length) (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (dom.take k)) k=true)
 (canonical : Spec.Ffdh.generationContextAt m ctx count k dom) :
 let w := Spec.Rsa.modulusWords k
 let P := (Spec.Ffdh.domainOf k dom).p
 wv m ctx 24 w=P ∧ wv m ctx (24+8*w) w=2^(128*w)%P := by
 dsimp only
 let w := Spec.Rsa.modulusWords k
 let P := (Spec.Ffdh.domainOf k dom).p
 obtain countEq : count=3+34*w := context_words_count canonical
 obtain bound : P<2^(64*w) := by
  obtain h := os2ip_lt (dom.take k)
  obtain len : (dom.take k).length=k := by simp only [List.length_take];omega_using [length]
  rw [len,pow256_eq] at h
  exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by dsimp [w,Spec.Rsa.modulusWords];omega_using []))
 obtain positive : 0<P := by
  have h := valid
  simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  change 0<Spec.Rsa.os2ip (dom.take k)
  omega_using [h]
 obtain prefixWords : Spec.Rsa.wordsAt m (off ctx 24) (2*w)=Spec.Rsa.toWords P w++Spec.Rsa.toWords (2^(128*w)%P) w := by
  obtain slice := VG.Proof.Mont.wordsAt_slice m ctx 0 count 3 (2*w) (by omega_using [countEq])
  obtain src := context_words length valid canonical
  simp only [VG.Proof.Mont.off,BitVec.add_zero,Nat.zero_add] at slice
  rw [src] at slice
  rw [VG.Proof.Ffdh.generationValues_montgomery] at slice
  exact slice.symm
 obtain values := pre_words prefixWords bound (Nat.lt_trans (Nat.mod_lt _ positive) bound)
 obtain zero : wv m (off ctx 24) 0 w=wv m ctx 24 w := by
  apply wv_congr2
  intro i hi
  simp only [word,off,BitVec.ofNat_add,BitVec.add_assoc,Nat.zero_add]
 obtain second : wv m (off ctx 24) (8*w) w=wv m ctx (24+8*w) w := by
  apply wv_congr2
  intro i hi
  simp only [word,off,BitVec.ofNat_add,BitVec.add_assoc,Nat.add_assoc]
 exact ⟨zero.symm.trans values.1,second.symm.trans values.2⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/SampleFrame.lean`, which only this module imported.
section

/-! Sampling modifies the private output and its dedicated mask control only. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem sampleFrame_header {p : Parameters} {s t : State} {N i : Nat}
 (scratch : Scr s p.B p.Z) (inside : i<32) (different : i≠sMask)
 (same : ∀ q,ofs p.B q<p.Z→t.mem q=(s.mem.writeW (off p.B (8*sMask)) (sampleMask N)) q) :
 word t.mem p.B (8*i)=word s.mem p.B (8*i) := by
 rw [workspace_word (by have := scratch.nowrap;omega_using [this]) same
  (by have := hdr_lt_slot p.w 8 inside;have := p.room;omega_arith)]
 exact header_other (writeW_outside _ _ _ (by decide : 8*sMask+8≤2^64)) (by decide) inside different

theorem FieldInitial.after_sample {p : Parameters} {s t : State} {N : Nat}
 (field : FieldInitial p s) (good : Good t p.B p.Z p.w p.mi)
 (same : ∀ q,ofs p.B q<p.Z→t.mem q=(s.mem.writeW (off p.B (8*sMask)) (sampleMask N)) q) : FieldInitial p t := by
 obtain nowrap : slot p.w 8≤2^64 := by have := field.good.scr.nowrap;have := p.room;omega_arith
 obtain masked := writeW_outside s.mem p.B (sampleMask N) (by decide : 8*sMask+8≤2^64)
 have arrays (a : Nat) (ha : a<8) : wv t.mem p.B (slot p.w a) p.w=wv s.mem p.B (slot p.w a) p.w := by
  obtain within := Nat.le_trans (slot_le (w:=p.w) ha) p.room
  apply Eq.trans _ (masked.wv (Or.inr (hdr_lt_slot p.w a (show sMask<32 by decide))) (by have := slot_le (w:=p.w) ha;omega_using [nowrap, this]))
  apply wv_congr
  intro i hi
  exact workspace_word (by have := field.good.scr.nowrap;omega_using [this]) same (by omega_using [within, hi])
 obtain wordSame : word t.mem p.B (slot p.w 0)=word s.mem p.B (slot p.w 0) := by
  rw [workspace_word (by have := field.good.scr.nowrap;omega_using [this]) same
   (by have := slot_le (w:=p.w) (show 0<8 by decide);have := p.room;have := p.positive;omega_arith)]
  exact masked.word (Or.inr (hdr_lt_slot p.w 0 (show sMask<32 by decide)))
   (by have := slot_le (w:=p.w) (show 0<8 by decide);have := p.positive;omega_arith)
 refine ⟨good,(arrays 0 (by decide)).trans field.modulus,?_,(arrays 4 (by decide)).trans field.r2⟩
 rw [wordSame]
 exact field.inverse

theorem Controls.after_sample {p : Parameters} {s t : State} {N k : Nat}
 (h : Controls p.B p.src p.ctx k p.N s) (scratch : Scr s p.B p.Z)
 (same : ∀ q,ofs p.B q<p.Z→t.mem q=(s.mem.writeW (off p.B (8*sMask)) (sampleMask N)) q) :
 Controls p.B p.src p.ctx k p.N t :=
 ⟨(sampleFrame_header scratch (by decide) (by decide) same).trans h.context,
  (sampleFrame_header scratch (by decide) (by decide) same).trans h.source,
  (sampleFrame_header scratch (by decide) (by decide) same).trans h.length,
  (sampleFrame_header scratch (by decide) (by decide) same).trans h.bits,
  (sampleFrame_header scratch (by decide) (by decide) same).trans h.rows⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem generateFront_ok {p : Parameters} {s : State} {dom rb : List Byte} {dp rp yp : Addr} {dl count : Nat}
 (scratch : Scr s p.B p.Z) (base : s.gpr .x0=p.B) (words : p.w=(p.k+7)/8)
 (positive : 0<p.k) (size : p.k<2^31) (shape : dl=2*p.k ∨ dl=3*p.k) (domLength : dom.length=dl)
 (valid : Spec.Ffdh.domainValid p.k dom=true)
 (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p) (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g)
 (policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom))
 (table : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w))
 (view : ContextView p.B p.Z p.ctx count p.k dom s)
 (domainSource : Src s p.B p.Z dp dom) (randomSource : Src s p.B p.Z rp rb) (rbLength : rb.length=p.k)
 (controls : Controls p.B p.src p.ctx p.k p.N s)
 (domain : word s.mem p.B (8*sDom)=dp) (domLen : word s.mem p.B (8*sDL)=BitVec.ofNat 64 dl)
 (y : word s.mem p.B (8*sY)=yp) (rand : word s.mem p.B (8*sRand)=rp)
 (bytes : word s.mem p.B (8*sBytes)=BitVec.ofNat 64 ((p.N+7)/8))
 (bitsPositive : 0<p.N) (bitsBound : p.N≤8192) (width : p.N≤8*p.k)
 (writeX : ∀ i<p.k,InRegions s.wr (p.src+BitVec.ofNat 64 i) 1)
 (outsideX : ∀ i<p.k,p.Z≤ofs p.B (p.src+BitVec.ofNat 64 i))
 (separateRand : ∀ i<p.k,∀ j<p.k,rp+BitVec.ofNat 64 i≠p.src+BitVec.ofNat 64 j)
 (separateDomain : ∀ i<dom.length,p.k≤ofs p.src (dp+BitVec.ofNat 64 i))
 (separateContext : ∀ i<8*count,p.k≤ofs p.src (p.ctx+BitVec.ofNat 64 i)) :
 WP isa (.seq importPrefix Generate.sample) s fun t =>
 ∃ mi,let q : Parameters := {p with mi:=mi}
 let bs := Spec.Rsa.bytesAt t.mem p.src p.k
 Initial q bs t ∧ Spec.Rsa.os2ip bs=Spec.Rsa.os2ip rb%2^p.N ∧
 Src t p.B p.Z dp dom ∧ word t.mem p.B (8*sDom)=dp ∧
 word t.mem p.B (8*sDL)=BitVec.ofNat 64 dl ∧ word t.mem p.B (8*sY)=yp ∧ Keep mmRegs s t := by
 obtain domSize : p.k≤dom.length := by omega_using [shape, domLength]
 obtain validMod := VG.Proof.Ffdh.domainValid_mod valid
 obtain prefixValues := context_prefix domSize validMod view.canonical
 have wEq : p.w=Spec.Rsa.modulusWords p.k := words
 rw [←wEq,←modulus] at prefixValues
 obtain countEq : count=3+34*p.w := by rw [context_words_count view.canonical,←wEq]
 obtain odd : p.P%2=1 := by
  have h := validMod
  simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  rw [modulus];exact h.1.1.1
 rw [WP.seq_iff]
 refine WP.mono (importPrefix_ok scratch base p.room words positive size controls.length controls.context
  (fun i hi =>by
   obtain h := view.readable (3+i) (by omega_using [countEq, hi])
   simpa only [off,Nat.mul_add] using h)
  (fun i hi =>by
   obtain h := view.outside (24+i) (by omega_using [countEq, hi])
   simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using h)
  prefixValues.1 prefixValues.2 odd) ?_
 rintro a ⟨mi,goodA,modulusA,inverseA,r2A,frameA,restA⟩
 let q : Parameters := {p with mi:=mi}
 obtain fieldA : FieldInitial q a := ⟨goodA,modulusA,inverseA,r2A⟩
 obtain inscrA : InScr p.B p.Z s.mem a.mem := InScr.of_frm frameA
  (fun r hr =>Nat.le_trans (importRanges_le _ r hr) p.room)
 obtain viewA := view.after_inscr inscrA restA
 obtain domainA := domainSource.congrK inscrA restA
 obtain randomA := randomSource.congrK inscrA restA
 have headerA (i : Nat) (lo : 16≤i) (hi : i<32) : word a.mem p.B (8*i)=word s.mem p.B (8*i) := importFrame_header frameA lo hi
 obtain controlsA : Controls q.B q.src q.ctx q.k q.N a :=
  ⟨(headerA sCtx (by decide) (by decide)).trans controls.context,
   (headerA sX (by decide) (by decide)).trans controls.source,
   (headerA sLen (by decide) (by decide)).trans controls.length,
   (headerA sBits (by decide) (by decide)).trans controls.bits,
   (headerA sRows (by decide) (by decide)).trans controls.rows⟩
 refine WP.mono (sample_ok goodA p.room positive size bitsPositive bitsBound width rbLength controlsA.bits
  ((headerA sBytes (by decide) (by decide)).trans bytes) controlsA.length controlsA.source
  ((headerA sRand (by decide) (by decide)).trans rand) randomA
  (fun i hi =>by rw [restA.wr];exact writeX i hi) outsideX separateRand) ?_
 rintro t ⟨goodT,_,valueT,sameT,frameT,restT⟩
 obtain total : Keep mmRegs s t := (restA.trans restT).mono (by decide)
 let bs := Spec.Rsa.bytesAt t.mem p.src p.k
 obtain bsLength : bs.length=p.k := by simp only [bs,Spec.Rsa.bytesAt,List.length_map,List.length_range]
 obtain fieldT := fieldA.after_sample goodT sameT
 obtain controlsT := controlsA.after_sample goodA.scr sameT
 obtain viewT := viewA.after_output frameT restT separateContext
 obtain domainT := src_after_output domainA frameT restT separateDomain
 obtain actual : Source q.src bs t := source_of_bytesAt t p.src p.k (fun i hi =>by
  obtain ⟨r,hr,contains⟩ := writeX i hi
  exact ⟨r,List.mem_append_right _ (by rw [total.wr];exact hr),contains⟩)
 obtain readsT : ReadEnv q bs t := context_readEnv wEq modulus generator policy table domSize validMod viewT.canonical
  actual bsLength (fun i hi =>outsideX i (by omega_using [bsLength, hi])) viewT.readable viewT.outside
 have headerT (i : Nat) (lo : 16≤i) (hi : i<32) (different : i≠sMask) : word t.mem p.B (8*i)=word s.mem p.B (8*i) :=
  (sampleFrame_header (p:=q) goodA.scr hi different sameT).trans (headerA i lo hi)
 refine ⟨mi,⟨fieldT,?_,readsT⟩,valueT,domainT,?_,?_,?_,total⟩
 · change Controls q.B q.src q.ctx bs.length q.N t
   rw [bsLength]
   exact controlsT
 · exact (headerT sDom (by decide) (by decide) (by decide)).trans domain
 · exact (headerT sDL (by decide) (by decide) (by decide)).trans domLen
 · exact (headerT sY (by decide) (by decide) (by decide)).trans y

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Context import, the exact vetted entropy policy, and the complete cached operation compose. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def generatePrepared (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
 .seq importPrefix (.seq Generate.sample (generateBody mul))

theorem generatePrepared_ok (M : Mont) {p : Parameters} {s : State} {dom rb : List Byte} {dp rp yp : Addr} {dl count : Nat}
 (scratch : Scr s p.B p.Z) (base : s.gpr .x0=p.B) (words : p.w=(p.k+7)/8)
 (positive : 0<p.k) (size : p.k<2^31) (shape : dl=2*p.k ∨ dl=3*p.k) (domLength : dom.length=dl)
 (valid : Spec.Ffdh.domainValid p.k dom=true)
 (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p) (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g)
 (policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom))
 (table : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w))
 (view : ContextView p.B p.Z p.ctx count p.k dom s)
 (domainSource : Src s p.B p.Z dp dom) (randomSource : Src s p.B p.Z rp rb) (rbLength : rb.length=p.k)
 (controls : Controls p.B p.src p.ctx p.k p.N s)
 (domain : word s.mem p.B (8*sDom)=dp) (domLen : word s.mem p.B (8*sDL)=BitVec.ofNat 64 dl)
 (y : word s.mem p.B (8*sY)=yp) (rand : word s.mem p.B (8*sRand)=rp)
 (bytes : word s.mem p.B (8*sBytes)=BitVec.ofNat 64 ((p.N+7)/8))
 (bitsPositive : 0<p.N) (bitsBound : p.N≤8192) (width : p.N≤8*p.k)
 (writeX : ∀ i<p.k,InRegions s.wr (p.src+BitVec.ofNat 64 i) 1)
 (writeY : ∀ i<p.k,InRegions s.wr (yp+BitVec.ofNat 64 i) 1)
 (outsideX : ∀ i<p.k,p.Z≤ofs p.B (p.src+BitVec.ofNat 64 i))
 (outsideY : ∀ i<p.k,p.Z≤ofs p.B (yp+BitVec.ofNat 64 i))
 (separateRand : ∀ i<p.k,∀ j<p.k,rp+BitVec.ofNat 64 i≠p.src+BitVec.ofNat 64 j)
 (separateDomain : ∀ i<dom.length,p.k≤ofs p.src (dp+BitVec.ofNat 64 i))
 (separateContext : ∀ i<8*count,p.k≤ofs p.src (p.ctx+BitVec.ofNat 64 i))
 (separateOutputs : ∀ i<p.k,p.k≤ofs yp (p.src+BitVec.ofNat 64 i)) :
 WP isa (generatePrepared M.mm) s fun t =>
 let a := Spec.Ffdh.domainOf p.k dom
 let x := Spec.Ffdh.vettedScalarOfOctets a rb
 t.gpr .x0=BitVec.ofNat 64 (Spec.Ffdh.keyStatus a x) ∧
 (if Spec.Ffdh.keyStatus a x=1 then
  Spec.Rsa.bytesAt t.mem p.src p.k=Spec.Rsa.i2osp x p.k ∧
  Spec.Rsa.bytesAt t.mem yp p.k=Spec.Rsa.i2osp (Spec.Rsa.powMod a.g x a.p) p.k
 else Spec.Rsa.bytesAt t.mem p.src p.k=List.replicate p.k 0 ∧ Spec.Rsa.bytesAt t.mem yp p.k=List.replicate p.k 0) ∧
 Keep (.x0::mmRegs) s t := by
 unfold generatePrepared
 apply WP.assoc
 rw [WP.seq_iff]
 refine WP.mono (generateFront_ok scratch base words positive size shape domLength valid modulus generator policy table view
  domainSource randomSource rbLength controls domain domLen y rand bytes bitsPositive bitsBound width
  writeX outsideX separateRand separateDomain separateContext) ?_
 rintro u ⟨mi,start,value,sourceU,domainU,lenU,yU,restU⟩
 let q : Parameters := {p with mi:=mi}
 let bs := Spec.Rsa.bytesAt u.mem p.src p.k
 have valueU : Spec.Rsa.os2ip bs=Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf p.k dom) rb := by
  unfold Spec.Ffdh.vettedScalarOfOctets
  rw [←policy]
  exact value
 have bound : Spec.Rsa.os2ip bs<2^q.N := by
  rw [value]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)
 refine WP.mono (generateBody_ok M start words positive size shape domLength valid modulus generator sourceU domainU lenU yU
  bitsPositive bitsBound width bound table
  (fun i hi =>by rw [restU.wr];exact writeX i hi)
  (fun i hi =>by rw [restU.wr];exact writeY i hi) outsideY separateOutputs) ?_
 rintro t ⟨status,outputs,restT⟩
 refine ⟨?_,?_,(restU.trans restT).mono (by decide)⟩
 · rw [valueU] at status
   exact status
 · rw [valueU] at outputs
   simpa only [q,generator,modulus] using outputs

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.GenerateEntry`, which this module and modules that import it used -/

section

/-! Complete cached-attempt entry with its original argument ordering. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/GenerateEntrySave.lean`, which only this module imported.
section

/-! Save the cached attempt's register and stack arguments in public scratch controls. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def generationSaveMemory (m : Mem) (B xp yp dp dl k rp ctx : Addr) : Mem :=
 ((((((m.writeW (off B (8*sX)) xp).writeW (off B (8*sY)) yp).writeW (off B (8*sDom)) dp).writeW
 (off B (8*sDL)) dl).writeW (off B (8*sLen)) k).writeW (off B (8*sRand)) rp).writeW (off B (8*sCtx)) ctx

theorem generationSave_range (m : Mem) (B xp yp dp dl k rp ctx : Addr) :
 Outside B 128 80 m (generationSaveMemory m B xp yp dp dl k rp ctx) := by
 intro q hq
 have store (m : Mem) (i : Nat) (low : 16≤i) (high : i<26) (v : Addr) :
  (m.writeW (off B (8*i)) v) q=m q := writeW_outside m B v (by omega_using [high]) q (by omega_using [hq, low, high])
 unfold generationSaveMemory
 rw [store _ sCtx (by decide) (by decide),store _ sRand (by decide) (by decide),store _ sLen (by decide) (by decide),
  store _ sDL (by decide) (by decide),store _ sDom (by decide) (by decide),
  store _ sY (by decide) (by decide),store _ sX (by decide) (by decide)]

theorem generateEntrySave_ok {s : State} {B ctx : Addr} {Z : Nat}
 (scratch : Scr s B Z) (room : 256≤Z)
 (readB : s.mem.readW (s.sp+8#64) 64=B) (readCtx : s.mem.readW (s.sp+24#64) 64=ctx)
 (stackB : InRegions (s.rd++s.wr) (s.sp+8#64) 8) (stackCtx : InRegions (s.rd++s.wr) (s.sp+24#64) 8) :
 WP isa (.block (Generate.entry.take 10)) s fun t =>
 (t.gpr .x0=B ∧ t.gpr .x9=ctx ∧
 t.mem=generationSaveMemory s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) ctx) ∧
 Keep [.x0,.x8,.x9] s t := by
 refine WP.keep [.x0,.x8,.x9] ?_ rfl rfl rfl
 unfold Generate.entry generationSaveMemory
 dsimp only [List.take]
 brun [exec_ldrSp_x' _ (show 8%8=0 ∧ 8<32768 by decide) stackB,
  exec_ldrSp_x' (s.write .x .x8 B) (show 24%8=0 ∧ 24<32768 by decide)
   (by simpa only [RegUpd.rd_write,RegUpd.wr_write,RegUpd.sp_write] using stackCtx),readB,readCtx,st,
  hdr_enc (show sX<32 by decide),hdr_enc (show sY<32 by decide),hdr_enc (show sDom<32 by decide),
  hdr_enc (show sDL<32 by decide),hdr_enc (show sLen<32 by decide),hdr_enc (show sRand<32 by decide),hdr_enc (show sCtx<32 by decide),
  scratch.st (d:=8*sX) (by unfold sX;omega_using [room]),scratch.st (d:=8*sY) (by unfold sY;omega_using [room]),
  scratch.st (d:=8*sDom) (by unfold sDom;omega_using [room]),scratch.st (d:=8*sDL) (by unfold sDL;omega_using [room]),
  scratch.st (d:=8*sLen) (by unfold sLen;omega_using [room]),scratch.st (d:=8*sRand) (by unfold sRand;omega_using [room]),scratch.st (d:=8*sCtx) (by unfold sCtx;omega_using [room])]

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/GenerateEntryMetadata.lean`, which only this module imported.
section

/-! Copy the three canonical public metadata words into native controls. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def generationMetadataMemory (m : Mem) (B N bytes rows : Addr) : Mem :=
 ((m.writeW (off B (8*sBits)) N).writeW (off B (8*sBytes)) bytes).writeW (off B (8*sRows)) rows

theorem generationMetadata_range (m : Mem) (B N bytes rows : Addr) :
 Outside B 128 80 m (generationMetadataMemory m B N bytes rows) := by
 intro q hq
 have store (m : Mem) (i : Nat) (low : 16≤i) (high : i<26) (v : Addr) :
  (m.writeW (off B (8*i)) v) q=m q := writeW_outside m B v (by omega_using [high]) q (by omega_using [hq, low, high])
 unfold generationMetadataMemory
 rw [store _ sRows (by decide) (by decide),store _ sBytes (by decide) (by decide),store _ sBits (by decide) (by decide)]

theorem generateEntryMetadata_ok {s : State} {B ctx N bytes rows : Addr} {Z : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B) (context : s.gpr .x9=ctx)
 (read0 : InRegions (s.rd++s.wr) ctx 8) (read8 : InRegions (s.rd++s.wr) (off ctx 8) 8)
 (read16 : InRegions (s.rd++s.wr) (off ctx 16) 8)
 (value0 : word s.mem ctx 0=N) (value8 : word s.mem ctx 8=bytes) (value16 : word s.mem ctx 16=rows) :
 WP isa (.block (Generate.entry.drop 10)) s fun t =>
 t.mem=generationMetadataMemory s.mem B N bytes rows ∧ Keep [.x10,.x11,.x12] s t := by
 refine WP.keep [.x10,.x11,.x12] ?_ rfl rfl rfl
 unfold Generate.entry generationMetadataMemory
 dsimp only [List.drop]
 have v0 : s.mem.readW ctx 64=N := by simpa only [word,off,BitVec.add_zero] using value0
 brun [base,context,read0,read8,read16,v0,value8,value16,
  hdr_enc (show sBits<32 by decide),hdr_enc (show sBytes<32 by decide),hdr_enc (show sRows<32 by decide),
  scratch.st (d:=8*sBits) (by unfold sBits;omega_using [room]),scratch.st (d:=8*sBytes) (by unfold sBytes;omega_using [room]),
  scratch.st (d:=8*sRows) (by unfold sRows;omega_using [room])]

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem generationEntry_headers (m : Mem) (B xp yp dp dl k rp ctx N bytes rows : Addr) :
 let t := generationMetadataMemory (generationSaveMemory m B xp yp dp dl k rp ctx) B N bytes rows
 word t B (8*sCtx)=ctx ∧ word t B (8*sDom)=dp ∧ word t B (8*sLen)=k ∧ word t B (8*sDL)=dl ∧
 word t B (8*sX)=xp ∧ word t B (8*sY)=yp ∧ word t B (8*sRand)=rp ∧
 word t B (8*sBits)=N ∧ word t B (8*sBytes)=bytes ∧ word t B (8*sRows)=rows := by
 simp (disch:=decide) only [generationMetadataMemory,generationSaveMemory,hdrStore_hdr,word_writeW_self]
 decide

theorem generateEntry_ok {s : State} {B ctx N bytes rows : Addr} {Z : Nat}
 (scratch : Scr s B Z) (room : 256≤Z)
 (readB : s.mem.readW (s.sp+8#64) 64=B) (readCtx : s.mem.readW (s.sp+24#64) 64=ctx)
 (stackB : InRegions (s.rd++s.wr) (s.sp+8#64) 8) (stackCtx : InRegions (s.rd++s.wr) (s.sp+24#64) 8)
 (readable : ∀ i<3,InRegions (s.rd++s.wr) (ctx+BitVec.ofNat 64 (8*i)) 8)
 (outside : ∀ i<24,Z≤ofs B (ctx+BitVec.ofNat 64 i))
 (value0 : word s.mem ctx 0=N) (value8 : word s.mem ctx 8=bytes) (value16 : word s.mem ctx 16=rows) :
 WP isa (.block Generate.entry) s fun t =>
 t.gpr .x0=B ∧
 t.mem=generationMetadataMemory (generationSaveMemory s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) ctx) B N bytes rows ∧
 Outside B 128 80 s.mem t.mem ∧ Keep (.x0::mmRegs) s t := by
 change WP isa (.block ((Generate.entry.take 10)++(Generate.entry.drop 10))) s _
 rw [WP.block_append_iff]
 refine WP.mono (generateEntrySave_ok scratch room readB readCtx stackB stackCtx) ?_
 rintro a ⟨⟨baseA,ctxA,memA⟩,restA⟩
 have frameA : Outside B 128 80 s.mem a.mem := by rw [memA];exact generationSave_range _ _ _ _ _ _ _ _ _
 have inscrA : InScr B Z s.mem a.mem := InScr.of_outside frameA (by omega_using [room])
 have same (i : Nat) (hi : i<3) : word a.mem ctx (8*i)=word s.mem ctx (8*i) := by
  apply Mem.readW_congr
  intro j hj
  have sep := outside (8*i+j) (by omega_using [hi, hj])
  exact inscrA _ (by simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using sep)
 refine WP.mono (generateEntryMetadata_ok (scratch.congr restA.wr) room baseA ctxA
  (by rw [restA.rd,restA.wr];simpa only [Nat.mul_zero,show BitVec.ofNat 64 0=0#64 from rfl,BitVec.add_zero] using readable 0 (by decide))
  (by rw [restA.rd,restA.wr];exact readable 1 (by decide))
  (by rw [restA.rd,restA.wr];exact readable 2 (by decide))
  ((same 0 (by decide)).trans value0) ((same 1 (by decide)).trans value8) ((same 2 (by decide)).trans value16)) ?_
 rintro t ⟨memT,restT⟩
 have frameT : Outside B 128 80 a.mem t.mem := by rw [memT];exact generationMetadata_range _ _ _ _ _
 exact ⟨(restT.gpr .x0 (by decide)).trans baseA,by rw [memT,memA],frameA.trans frameT,
  (restA.trans restT).mono (by decide)⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.FrontTimingState`, which only this module used -/

section

/-! Public and secret inputs of the context-import and entropy-sampling front end. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/BodyTimingState.lean`, which only this module imported.
section

/-! Attempt timing fixes only the reviewed public status, with independent secret draws. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure BodyPublic where
 scalar : ScalarPublic
 yp : Addr
 status : Nat
 bitsPositive : 0<scalar.p.N
 bitsBound : scalar.p.N≤8192
 width : scalar.p.N≤8*scalar.p.k
 table : scalar.p.table=scalar.p.ctx+BitVec.ofNat 64 (24+16*scalar.p.w)
 valid : Spec.Ffdh.parametersValid (Spec.Ffdh.domainOf scalar.p.k scalar.dom)=true
 outsideX : ∀ i<scalar.p.k,scalar.p.Z≤ofs scalar.p.B (scalar.p.src+BitVec.ofNat 64 i)

structure BodyState (q : BodyPublic) (bs : List Byte) (s : State) : Prop where
 scalar : ScalarState q.scalar bs s
 bound : Spec.Rsa.os2ip bs<2^q.scalar.p.N
 status : Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf q.scalar.p.k q.scalar.dom) (Spec.Rsa.os2ip bs)=q.status
 y : word s.mem q.scalar.p.B (8*sY)=q.yp
 write : ∀ i<q.scalar.p.k,InRegions s.wr (q.scalar.p.src+BitVec.ofNat 64 i) 1

def BodyReady (q : BodyPublic) (s : State) : Prop := ∃ bs,BodyState q bs s

def bodyOutput (q : BodyPublic) : OutputPublic :=
 ⟨q.scalar.p,q.yp,q.scalar.words,q.scalar.positive,q.scalar.size,q.outsideX⟩

def bodyComb (q : BodyPublic) : CombPublic :=
 ⟨⟨q.scalar.p,q.bitsPositive,q.bitsBound,q.scalar.size,q.width⟩,q.table⟩

theorem bodyReady_output {q : BodyPublic} {s : State} (h : BodyReady q s) : OutputReady (bodyOutput q) s := by
 obtain ⟨bs,h⟩:=h
 exact ⟨h.scalar.initial.good,h.scalar.initial.controls.source,h.y,h.scalar.length ▸ h.scalar.initial.controls.length,h.write⟩

def BodyRangeDone (q : BodyPublic) (s : State) : Prop :=
 BodyReady q s ∧ s.gpr .x9=(if q.status=2 then 0#64 else 1#64)

theorem bodyRangeDone_ok {q : BodyPublic} {s : State} (h : BodyReady q s) :
 WP isa Generate.scalarRange s (BodyRangeDone q) := by
 obtain ⟨bs,h⟩:=h
 have init :=h.scalar.initial
 refine WP.mono (scalarRange_ok init.good q.scalar.p.room q.scalar.words q.scalar.positive q.scalar.size q.scalar.shape q.scalar.domLength
  h.scalar.source (source_src init.reads.source init.reads.scalarOutside) h.scalar.length init.controls.source h.scalar.domain
  (h.scalar.length ▸ init.controls.length) h.scalar.domainLength (init.modulus.trans q.scalar.modulus)
  (by rw [←q.scalar.modulus];exact q.scalar.odd)) ?_
 rintro t ⟨good,_,flag,frame,rest⟩
 have state : BodyState q bs t :=
  ⟨h.scalar.after good frame rest,h.bound,h.status,(scalarFrame_header frame (by decide) (by decide)).trans h.y,
   fun i hi =>by rw [rest.wr];exact h.write i hi⟩
 refine ⟨⟨bs,state⟩,?_⟩
 have rejected := keyStatus_scalar_rejected q.valid (Spec.Rsa.os2ip bs)
 rw [h.status] at rejected
 by_cases scalar : 0<Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs<Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf q.scalar.p.k q.scalar.dom)
 · rw [ite_eq_left scalar] at flag
   rw [ite_eq_right (fun eq =>rejected.mp eq scalar)]
   exact flag
 · rw [ite_eq_right scalar] at flag
   rw [ite_eq_left (rejected.mpr scalar)]
   exact flag

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/GenerateBodyTiming.lean`, which only this module imported.
section

/-! Complete attempt-body timing is governed by public geometry and the reviewed returned status. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)

def TailReady (q : BodyPublic) (s : State) : Prop :=
 ModState q.scalar.p s ∧ OutputReady (bodyOutput q) s

def bodyRangePublic (q : BodyPublic) : RangePublic :=
 ⟨scalarWs q.scalar,by change 0<q.scalar.p.w;have :=q.scalar.p.positive;omega_using [this],q.scalar.p.width⟩

theorem bodyComb_output (M : Mont) {q : BodyPublic} {s : State} (h : BodyReady q s) :
 WP isa (Comb.code M.mm) s (TailReady q) := by
 obtain ⟨bs,h⟩ :=h
 have length :=h.scalar.length
 refine WP.mono (comb_correct M h.scalar.initial q.bitsPositive q.bitsBound
  (length ▸ q.scalar.size) (length ▸ q.width) h.bound q.table) ?_
 rintro t ⟨state,_,controls,_,stable,rest⟩
 exact ⟨state,state.good,controls.source,
  (stable sY (by decide) (by decide) (by decide) (by decide)).trans h.y,
  length ▸ controls.length,fun i hi =>by rw [rest.wr];exact h.write i hi⟩

theorem bodyRange_finish {q : BodyPublic} {s : State} (h : TailReady q s) :
 WP isa Generate.publicRange s (FinishReady (bodyOutput q)) := by
 obtain ⟨state,good,x,y,len,write⟩ :=h
 refine WP.mono (publicRange_ok state q.scalar.odd) ?_
 rintro t ⟨stateT,_,flag,header,frame,rest⟩
 refine ⟨⟨stateT.good,(publicRangeFrame_header frame (by decide) (by decide)).trans x,
  (publicRangeFrame_header frame (by decide) (by decide)).trans y,
  (publicRangeFrame_header frame (by decide) (by decide)).trans len,
  fun i hi =>by rw [rest.wr];exact write i hi⟩,?_,?_⟩
 · exact decide (1<wv s.mem q.scalar.p.B (slot q.scalar.p.w 6) q.scalar.p.w ∧
    wv s.mem q.scalar.p.B (slot q.scalar.p.w 6) q.scalar.p.w<q.scalar.p.P-1)
 · change word t.mem q.scalar.p.B (8*sTmp)=_
   rw [header,flag]
   exact (bit_decide _).symm

theorem acceptedBody_ct (M : Mont) : RelCT isa (Two BodyReady)
 (.seq (Comb.code M.mm) (.seq Generate.publicRange Generate.finish)) (fun _ _ =>True) := by
 refine RelCT.seq (two_post (Ψ:=TailReady)
  (two_map bodyComb (fun q s h =>by obtain ⟨bs,h⟩:=h;exact ⟨bs,h.scalar.initial,h.bound⟩) (comb_ct M))
  (fun _ _ h =>bodyComb_output M h)) ?_
 exact RelCT.seq (two_post (Ψ:=fun q s =>FinishReady (bodyOutput q) s)
  (two_map bodyRangePublic (fun q s h =>⟨q.scalar.p.mi,h.1.good,q.scalar.p.room⟩) publicRange_ct)
  (fun _ _ h =>bodyRange_finish h)) (two_map bodyOutput (fun _ _ h =>h) finish_ct)

theorem generateBody_ct (M : Mont) : RelCT isa (Two BodyReady) (generateBody M.mm) (fun _ _ =>True) := by
 unfold generateBody
 refine RelCT.seq (two_post (Ψ:=BodyRangeDone)
  (two_map BodyPublic.scalar (fun _ _ h =>by obtain ⟨bs,h⟩:=h;exact ⟨bs,h.scalar⟩) scalarRange_ct)
  (fun _ _ h =>bodyRangeDone_ok h)) ?_
 refine RelCT.ite ?_ ?_ ?_
 · rintro s t ⟨q,hs,ht,_⟩
   rw [eval_zero,eval_zero,hs.2,ht.2]
 · exact (two_map bodyOutput (fun _ _ h =>bodyReady_output h) fail_ct).mono
    (fun _ _ h =>by rcases h.1 with ⟨q,hs,ht,sp⟩;exact ⟨q,hs.1,ht.1,sp⟩) (fun _ _ h =>h)
 · exact (acceptedBody_ct M).mono
    (fun _ _ h =>by rcases h.1 with ⟨q,hs,ht,sp⟩;exact ⟨q,hs.1,ht.1,sp⟩) (fun _ _ h =>h)

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure FrontPublic where
 body : BodyPublic
 rp : Addr
 count : Nat
 checked : Spec.Ffdh.domainValid body.scalar.p.k body.scalar.dom=true
 generator : body.scalar.p.G=(Spec.Ffdh.domainOf body.scalar.p.k body.scalar.dom).g
 policy : body.scalar.p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf body.scalar.p.k body.scalar.dom)
 separateRand : ∀ i<body.scalar.p.k,∀ j<body.scalar.p.k,rp+BitVec.ofNat 64 i≠body.scalar.p.src+BitVec.ofNat 64 j
 separateDomain : ∀ i<body.scalar.dom.length,body.scalar.p.k≤ofs body.scalar.p.src (body.scalar.dp+BitVec.ofNat 64 i)
 separateContext : ∀ i<8*count,body.scalar.p.k≤ofs body.scalar.p.src (body.scalar.p.ctx+BitVec.ofNat 64 i)

structure FrontState (q : FrontPublic) (rb : List Byte) (s : State) : Prop where
 scratch : Scr s q.body.scalar.p.B q.body.scalar.p.Z
 base : s.gpr .x0=q.body.scalar.p.B
 view : ContextView q.body.scalar.p.B q.body.scalar.p.Z q.body.scalar.p.ctx q.count q.body.scalar.p.k q.body.scalar.dom s
 domainSource : Src s q.body.scalar.p.B q.body.scalar.p.Z q.body.scalar.dp q.body.scalar.dom
 randomSource : Src s q.body.scalar.p.B q.body.scalar.p.Z q.rp rb
 rbLength : rb.length=q.body.scalar.p.k
 controls : Controls q.body.scalar.p.B q.body.scalar.p.src q.body.scalar.p.ctx q.body.scalar.p.k q.body.scalar.p.N s
 domain : word s.mem q.body.scalar.p.B (8*sDom)=q.body.scalar.dp
 domainLength : word s.mem q.body.scalar.p.B (8*sDL)=BitVec.ofNat 64 q.body.scalar.dl
 y : word s.mem q.body.scalar.p.B (8*sY)=q.body.yp
 random : word s.mem q.body.scalar.p.B (8*sRand)=q.rp
 bytes : word s.mem q.body.scalar.p.B (8*sBytes)=BitVec.ofNat 64 ((q.body.scalar.p.N+7)/8)
 write : ∀ i<q.body.scalar.p.k,InRegions s.wr (q.body.scalar.p.src+BitVec.ofNat 64 i) 1
 status : Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf q.body.scalar.p.k q.body.scalar.dom)
  (Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf q.body.scalar.p.k q.body.scalar.dom) rb)=q.body.status

def FrontReady (q : FrontPublic) (s : State) : Prop := ∃ rb,FrontState q rb s

def frontImport (q : FrontPublic) : ImportPublic :=
 ⟨scalarWs q.body.scalar,q.body.scalar.p.k,q.body.scalar.p.ctx,q.body.scalar.p.room,
  q.body.scalar.words,q.body.scalar.positive,q.body.scalar.size⟩

def frontSample (q : FrontPublic) : SamplePublic :=
 ⟨scalarWs q.body.scalar,q.body.scalar.p.room,q.body.scalar.p.k,q.body.scalar.p.N,
  q.body.scalar.p.src,q.rp,q.body.bitsPositive,q.body.bitsBound⟩

def frontBody (q : FrontPublic) (mi : BitVec 64) : BodyPublic :=
 {q.body with scalar:={q.body.scalar with p:={q.body.scalar.p with mi:=mi}}}

theorem frontReady_import {q : FrontPublic} {s : State} (h : FrontReady q s) : ImportReady (frontImport q) s := by
 obtain ⟨rb,h⟩:=h
 exact ⟨h.scratch,h.base,h.controls.length,h.controls.context,
  fun i hi =>by
   change i<2*q.body.scalar.p.w at hi
   change InRegions (s.rd++s.wr) (off q.body.scalar.p.ctx (24+8*i)) 8
   have count :=context_words_count h.view.canonical
   have readable :=h.view.readable (3+i) (by change 3+i<q.count;rw [count];change _<3+34*((q.body.scalar.p.k+7)/8);rw [←q.body.scalar.words];omega_using [hi])
   simpa only [off,Nat.mul_add,Nat.reduceMul] using readable,
  fun i hi =>by
   change i<16*q.body.scalar.p.w at hi
   change q.body.scalar.p.Z≤ofs q.body.scalar.p.B (off q.body.scalar.p.ctx 24+BitVec.ofNat 64 i)
   have count :=context_words_count h.view.canonical
   have outside :=h.view.outside (24+i) (by rw [count];change _<8*(3+34*((q.body.scalar.p.k+7)/8));rw [←q.body.scalar.words];omega_using [hi])
   simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using outside⟩

theorem frontImport_sample {q : FrontPublic} {s : State} (h : FrontReady q s) :
 WP isa importPrefix s (SampleReady (frontSample q)) := by
 obtain ⟨rb,h⟩:=h
 have ready :=frontReady_import (q:=q) ⟨rb,h⟩
 have domSize : q.body.scalar.p.k≤q.body.scalar.dom.length := by have :=q.body.scalar.shape;have :=q.body.scalar.domLength;omega_arith
 have values :=context_prefix domSize (VG.Proof.Ffdh.domainValid_mod q.checked) h.view.canonical
 have wEq : q.body.scalar.p.w=Spec.Rsa.modulusWords q.body.scalar.p.k :=q.body.scalar.words
 rw [←wEq,←q.body.scalar.modulus] at values
 refine WP.mono (importPrefix_ok h.scratch h.base q.body.scalar.p.room q.body.scalar.words q.body.scalar.positive q.body.scalar.size
  h.controls.length h.controls.context ready.readable ready.outside values.1 values.2 q.body.scalar.odd) ?_
 rintro t ⟨mi,good,_,_,_,frame,_⟩
 have same (i : Nat) (lo : 16≤i) (hi : i<32) :=importFrame_header frame lo hi
 exact ⟨⟨mi,good,q.body.scalar.p.room⟩,(same sBits (by decide) (by decide)).trans h.controls.bits,
  (same sBytes (by decide) (by decide)).trans h.bytes,(same sLen (by decide) (by decide)).trans h.controls.length,
  (same sX (by decide) (by decide)).trans h.controls.source,(same sRand (by decide) (by decide)).trans h.random⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! The cached attempt's public calling convention and immutable input geometry. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/GenerateFrontTiming.lean`, which only this module imported.
section

/-! Relate independent entropy draws through context import, sampling, and the complete attempt. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

/-- The inverse is reconstructed; no prior scratch value is assumed. -/
def FrontDone (q : FrontPublic) (s : State) : Prop := ∃ mi,BodyReady (frontBody q mi) s

theorem generateFront_ct : RelCT isa (Two FrontReady) (.seq importPrefix Generate.sample) (fun _ _ =>True) :=
 RelCT.seq (two_post (Ψ:=fun q s =>SampleReady (frontSample q) s)
  (two_map frontImport (fun _ _ h =>frontReady_import h) importPrefix_ct)
  (fun _ _ h =>frontImport_sample h)) (two_map frontSample (fun _ _ h =>h) sample_ct)

theorem front_done_ok {q : FrontPublic} {s : State} (h : FrontReady q s) :
 WP isa (.seq importPrefix Generate.sample) s (FrontDone q) := by
 obtain ⟨rb,h⟩:=h
 refine WP.mono (generateFront_ok h.scratch h.base q.body.scalar.words q.body.scalar.positive q.body.scalar.size q.body.scalar.shape
  q.body.scalar.domLength q.checked q.body.scalar.modulus q.generator q.policy q.body.table h.view h.domainSource h.randomSource h.rbLength
  h.controls h.domain h.domainLength h.y h.random h.bytes q.body.bitsPositive q.body.bitsBound q.body.width
  h.write q.body.outsideX q.separateRand q.separateDomain q.separateContext) ?_
 rintro t ⟨mi,initial,value,domainSource,domain,domainLength,y,rest⟩
 let bs:=Spec.Rsa.bytesAt t.mem q.body.scalar.p.src q.body.scalar.p.k
 refine ⟨mi,bs,⟨initial,initial.reads.length,domainSource,domain,domainLength⟩,?_,?_,y,?_⟩
 · change Spec.Rsa.os2ip bs<2^q.body.scalar.p.N
   rw [value]
   exact Nat.mod_lt _ (Nat.two_pow_pos _)
 · have scalar : Spec.Rsa.os2ip bs=Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf q.body.scalar.p.k q.body.scalar.dom) rb := by
    unfold Spec.Ffdh.vettedScalarOfOctets
    rw [←q.policy]
    exact value
   change Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf q.body.scalar.p.k q.body.scalar.dom) (Spec.Rsa.os2ip bs)=q.body.status
   rw [scalar];exact h.status
 · intro i hi;rw [rest.wr];exact h.write i hi

theorem front_done_two {s t : State} (h : Two FrontDone s t) :
 Two BodyReady s t := by
 obtain ⟨q,⟨a,bs,hs⟩,⟨b,bt,ht⟩,sp⟩:=h
 have same : a=b := imported_inverse_unique (p:=q.body.scalar.p)
  hs.scalar.initial.toFieldInitial ht.scalar.initial.toFieldInitial q.body.scalar.odd
 subst b
 exact ⟨frontBody q a,⟨bs,hs⟩,⟨bt,ht⟩,sp⟩

theorem generatePrepared_ct (M : Mont) :
 RelCT isa (Two FrontReady) (generatePrepared M.mm) (fun _ _ =>True) := by
 unfold generatePrepared
 apply RelCT.assoc
 exact RelCT.seq (two_post generateFront_ct (fun _ _ h =>front_done_ok h))
  ((generateBody_ct M).mono (fun _ _ h =>front_done_two h) (fun _ _ h =>h))

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure NativeState (q : FrontPublic) (rb : List Byte) (s : State) : Prop where
 scratch : Scr s q.body.scalar.p.B q.body.scalar.p.Z
 view : ContextView q.body.scalar.p.B q.body.scalar.p.Z q.body.scalar.p.ctx q.count q.body.scalar.p.k q.body.scalar.dom s
 domainSource : Src s q.body.scalar.p.B q.body.scalar.p.Z q.body.scalar.dp q.body.scalar.dom
 randomSource : Src s q.body.scalar.p.B q.body.scalar.p.Z q.rp rb
 rbLength : rb.length=q.body.scalar.p.k
 xArg : s.gpr .x0=q.body.scalar.p.src
 yArg : s.gpr .x2=q.body.yp
 domArg : s.gpr .x4=q.body.scalar.dp
 dlArg : s.gpr .x5=BitVec.ofNat 64 q.body.scalar.dl
 lenArg : s.gpr .x6=BitVec.ofNat 64 q.body.scalar.p.k
 randArg : s.gpr .x7=q.rp
 readB : s.mem.readW (s.sp+8#64) 64=q.body.scalar.p.B
 readCtx : s.mem.readW (s.sp+24#64) 64=q.body.scalar.p.ctx
 stackB : InRegions (s.rd++s.wr) (s.sp+8#64) 8
 stackCtx : InRegions (s.rd++s.wr) (s.sp+24#64) 8
 write : ∀ i<q.body.scalar.p.k,InRegions s.wr (q.body.scalar.p.src+BitVec.ofNat 64 i) 1
 status : Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf q.body.scalar.p.k q.body.scalar.dom)
  (Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf q.body.scalar.p.k q.body.scalar.dom) rb)=q.body.status

def NativeReady (q : FrontPublic) (s : State) : Prop := ∃ rb,NativeState q rb s

theorem native_front_ok {q : FrontPublic} {s : State} (h : NativeReady q s) :
 WP isa (.block Generate.entry) s (FrontReady q) := by
 obtain ⟨rb,h⟩:=h
 let p:=q.body.scalar.p
 have room : 256≤p.Z := by have :=p.room;dsimp only [slot,hdrBytes] at this;omega_using [this]
 have count3 : 3≤q.count := by rw [context_words_count h.view.canonical];omega_using []
 have domSize : p.k≤q.body.scalar.dom.length := by have :=q.body.scalar.shape;have :=q.body.scalar.domLength;dsimp only [p];omega_arith
 have head (i : Nat) (hi : i<3) := context_header domSize (VG.Proof.Ffdh.domainValid_mod q.checked) h.view.canonical hi
 have head0 : word s.mem p.ctx 0=BitVec.ofNat 64 p.N := by simpa [word,off,p,q.policy] using head 0 (by decide)
 have head1 : word s.mem p.ctx 8=BitVec.ofNat 64 ((p.N+7)/8) := by simpa [word,off,p,q.policy] using head 1 (by decide)
 have head2 : word s.mem p.ctx 16=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N) := by simpa [word,off,p,q.policy] using head 2 (by decide)
 refine WP.mono (generateEntry_ok h.scratch room h.readB h.readCtx h.stackB h.stackCtx
  (fun i hi =>h.view.readable i (by omega_using [count3, hi])) (fun i hi =>h.view.outside i (by omega_using [count3, hi])) head0 head1 head2) ?_
 rintro t ⟨base,mem,frame,rest⟩
 have inscr : InScr p.B p.Z s.mem t.mem := InScr.of_outside frame (by omega_using [room])
 simp only [h.xArg,h.yArg,h.domArg,h.dlArg,h.lenArg,h.randArg] at mem
 have headers :=generationEntry_headers s.mem p.B p.src q.body.yp q.body.scalar.dp (BitVec.ofNat 64 q.body.scalar.dl)
  (BitVec.ofNat 64 p.k) q.rp p.ctx (BitVec.ofNat 64 p.N) (BitVec.ofNat 64 ((p.N+7)/8)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N))
 change t.mem=generationMetadataMemory (generationSaveMemory s.mem p.B p.src q.body.yp q.body.scalar.dp
  (BitVec.ofNat 64 q.body.scalar.dl) (BitVec.ofNat 64 p.k) q.rp p.ctx) p.B (BitVec.ofNat 64 p.N)
  (BitVec.ofNat 64 ((p.N+7)/8)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N)) at mem
 rw [←mem] at headers
 obtain ⟨ctx,domain,len,dl,x,y,rng,bits,bytes,rows⟩:=headers
 exact ⟨rb,h.scratch.congr rest.wr,base,h.view.after_inscr inscr rest,
  h.domainSource.congrK inscr rest,h.randomSource.congrK inscr rest,h.rbLength,
  ⟨ctx,x,len,bits,rows⟩,domain,dl,y,rng,bytes,
  fun i hi =>by rw [rest.wr];exact h.write i hi,h.status⟩

end VG.Proof.Ffdh.AArch64.Cached
