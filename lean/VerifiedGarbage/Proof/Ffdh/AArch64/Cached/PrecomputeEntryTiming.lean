module

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Ffdh.CachedGenerateKeyContract
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SatWitness
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyConsts
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratchConsts
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeTailTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ContextBuild
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BuildFrame
public import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Source
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeInitial
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Bit
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState
public import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.InverseUnique
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.DomainFacts
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
public import VerifiedGarbage.Impl.Rsa.AArch64
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BitMath
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyLoopTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyLoop
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyScan
import Mathlib.Tactic.SplitIfs

/-! ### `Ffdh.AArch64.Cached.PrecomputeTimingState`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.PolicyRecognizeTiming`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.PolicyRecognizeTimingState`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.PolicyBoundTiming`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.PolicyScanTiming`, which only this module used -/

section

/-! Leading-zero scanning depends only on the complete public bound encoding. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)

structure PolicyScanPublic where
 src : Addr
 bs : List Byte
 L : Nat
 size : bs.length<2^31
 inside : L<bs.length
 zeros : ∀ i<L,bs.getD i 0=0#8
 nonzero : bs.getD L 0≠0#8

structure PolicyScanReady (q : PolicyScanPublic) (i : Nat) (s : State) : Prop where
 source : Source q.src q.bs s
 pointer : s.gpr .x1=off q.src i
 remaining : s.gpr .x2=BitVec.ofNat 64 (q.bs.length-i)

private theorem publicByteZero : ∀ b : Byte,
 (BitVec.ofNat 64 b.toNat==0#64)=decide (b=0#8) := by decide +kernel

theorem policyScan_ct : RelCT isa (Two fun q s =>PolicyScanReady q 0 s)
 (.loop (.block Policy.scanStep) (.zero .x .x3)) (fun _ _ =>True) := by
 have stepCt : RelCT isa (Two fun (q : PolicyScanPublic × Nat) s =>q.2<q.1.L+1 ∧ PolicyScanReady q.1 q.2 s)
  (.block Policy.scanStep) (fun _ _ =>True) :=
  two_taint [.x1] (fun q s t hs ht r hr =>by
   have eq : r= .x1 := by simpa using hr
   subst r;exact hs.2.pointer.trans ht.2.pointer.symm) (by taint_decide)
 have loop:=two_loop (cond:= .zero .x .x3) (Φ:=PolicyScanReady) (Ψ:=fun _ _ =>True)
  (fun q =>q.L+1) stepCt (by
   intro q i s hi h
   refine WP.mono (policyScanStep h.source q.size (by have :=q.inside;omega_using [hi, this]) h.pointer h.remaining) ?_
   rintro t ⟨⟨ptr,count,byte,mem⟩,rest⟩
   refine ⟨?_,fun _ =>⟨h.source.of_mem mem rest,ptr,count⟩,fun _ =>trivial⟩
   rw [eval_zero,byte]
   change some (BitVec.ofNat 64 (q.bs.getD i 0).toNat==0#64)=_
   rw [publicByteZero]
   by_cases more : i<q.L
   · rw [q.zeros i more,decide_eq_true (show i+1<q.L+1 by omega_using [more])]
     rfl
   · have last : i=q.L :=by omega_using [hi, more]
     rw [last,decide_eq_false q.nonzero,decide_eq_false (show ¬q.L+1<q.L+1 by omega_using [])])
 exact loop.mono (fun _ _ ⟨q,hs,ht,sp⟩ =>⟨q,⟨by have :=q.inside;omega_using [],hs⟩,⟨by have :=q.inside;omega_using [],ht⟩,sp⟩)
  (fun _ _ _ =>trivial)

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.PolicyBound`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.PolicySource`, which only this module used -/

section

/-! Select q's public bytes when present, otherwise p's public bytes. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem exec_cselc_x (s : State) (d n m : Reg) (cond : CondCode) :
 exec (.cselc .x d n m cond) s=some (s.write .x d (if cond.holds s then s.gpr n else s.gpr m)) := rfl
private theorem zeroFlag (s : State) (d : Reg) (a b : BitVec 64) (c : Bool) :
 (s.addWithCarry .x d a b c).zf=decide (a+b+BitVec.ofNat 64 c.toNat=0#64) := rfl

private theorem publicSub (k dl : Nat) (size : k<2^31) (shape : dl=2*k ∨ dl=3*k) :
 BitVec.ofNat 64 dl+ ~~~BitVec.ofNat 64 (2*k)+1#64=BitVec.ofNat 64 (dl-2*k) := by
 rw [BitVec.add_assoc,←BitVec.neg_eq_not_add,←BitVec.sub_eq_add_neg]
 exact BitVec.ofNat_sub_ofNat_of_le dl (2*k) (by omega_using [size]) (by omega_using [shape])

theorem policySource_ok {s : State} {B dom : Addr} {Z k dl : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (positive : 0<k) (size : k<2^31) (shape : dl=2*k ∨ dl=3*k)
 (pointer : word s.mem B (8*sDom)=dom) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (domainLength : word s.mem B (8*sDL)=BitVec.ofNat 64 dl) :
 WP isa (.block (Policy.boundSource++[movi .x10 0])) s fun t =>
 (t.gpr .x1=(if dl=2*k then dom else off dom (2*k)) ∧
 t.gpr .x2=BitVec.ofNat 64 k ∧ t.gpr .x10=0#64 ∧ t.mem=s.mem) ∧ Keep [.x1,.x2,.x3,.x4,.x10] s t := by
 have shift : BitVec.ofNat 64 k <<< 1=BitVec.ofNat 64 (2*k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
  omega_using []
 have choose : (if decide (BitVec.ofNat 64 (dl-2*k)=0#64) then dom else dom+BitVec.ofNat 64 (2*k))=
  (if dl=2*k then dom else off dom (2*k)) := by
  rcases shape with eq | eq
  · subst dl
    simp
  · subst dl
    have ne : BitVec.ofNat 64 (3*k-2*k)≠0#64 := by
     intro zero
     have := congrArg BitVec.toNat zero
     simp only [BitVec.toNat_ofNat] at this
     omega_using [positive, size, this]
    simp only [ne,decide_false,ite_false,show ¬3*k=2*k by omega_using [positive]]
    rfl
 refine WP.keep [.x1,.x2,.x3,.x4,.x10] ?_ rfl rfl rfl
 unfold Policy.boundSource
 brun [base,hdr_enc (show sDom<32 by decide),hdr_enc (show sLen<32 by decide),hdr_enc (show sDL<32 by decide),
  scratch.ld (d:=8*sDom) (by unfold sDom;omega_using [room]),scratch.ld (d:=8*sLen) (by unfold sLen;omega_using [room]),
  scratch.ld (d:=8*sDL) (by unfold sDL;omega_using [room]),pointer,length,domainLength,shift,
  exec_cselc_x,CondCode.holds,RegUpd.zf_write,zeroFlag,Bool.toNat_true,publicSub k dl size shape,choose]

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.PolicyCount`, which only this module used -/

section

/-! Count the significant bits of the public first nonzero bound byte. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero)
open VG.Spec.RsaKeyGen (bitLength)

private theorem byteLengths : ∀ n<256, 0<n →
 0<bitLength n ∧ bitLength n≤8 ∧ bitLength (n/2)+1=bitLength n := by decide +kernel

theorem policyCountStep (s : State) {n j : Nat} (size : n<256)
 (byte : s.gpr .x3=BitVec.ofNat 64 n) (count : s.gpr .x10=BitVec.ofNat 64 j) :
 WP isa (.block Policy.countStep) s fun t =>
 (t.gpr .x3=BitVec.ofNat 64 (n/2) ∧ t.gpr .x10=BitVec.ofNat 64 (j+1) ∧ t.mem=s.mem) ∧
 Keep [.x3,.x10] s t := by
 have shift : BitVec.ofNat 64 n >>> 1=BitVec.ofNat 64 (n/2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  omega_using [size]
 refine WP.keep [.x3,.x10] ?_ rfl rfl rfl
 unfold Policy.countStep
 brun [byte,count,shift]
 exact (BitVec.ofNat_add _ _).symm

theorem policyCount_ok (s : State) {b : Nat} (size : b<256) (positive : 0<b)
 (byte : s.gpr .x3=BitVec.ofNat 64 b) (count : s.gpr .x10=0#64) :
 WP isa (.loop (.block Policy.countStep) (.nonzero .x .x3)) s fun t =>
 t.gpr .x3=0#64 ∧ t.gpr .x10=BitVec.ofNat 64 (bitLength b) ∧ t.mem=s.mem ∧ Keep [.x3,.x10] s t := by
 let I := fun n t => 0<n ∧ n≤b ∧ t.gpr .x3=BitVec.ofNat 64 n ∧
  t.gpr .x10=BitVec.ofNat 64 (bitLength b-bitLength n) ∧ t.mem=s.mem ∧ Keep [.x3,.x10] s t
 have monotone (n : Nat) (hn : n≤b) : bitLength n≤bitLength b := by
  unfold bitLength
  split_ifs <;> try omega
  have lower := Nat.log2_self_le (show n≠0 by assumption)
  have order := (Nat.le_log2 (show b≠0 by omega_using [positive])).mpr (Nat.le_trans lower hn)
  omega_using [order]
 refine WP.loop (M:=isa) I ?_ b s ?_
 · intro n t h
   obtain ⟨posN,leN,byteT,countT,memT,restT⟩ := h
   have lengths := byteLengths n (by omega_using [size, leN]) posN
   have countNext : bitLength b-bitLength n+1=bitLength b-bitLength (n/2) := by
    have := monotone n leN
    omega_using [lengths, this]
   refine WP.mono (policyCountStep t (by omega_using [size, leN]) byteT countT) ?_
   rintro u ⟨⟨byteU,countU,memU⟩,restU⟩
   by_cases last : n=1
   · left
     refine ⟨?_,?_,?_,memU.trans memT,(restT.trans restU).mono (by decide)⟩
     · rw [eval_nonzero,byteU,last]
       decide
     · rw [byteU,last]
     · rw [countU,countNext,last]
       simp only [show 1/2=0 from rfl,bitLength,ite_true,Nat.sub_zero]
   · right
     refine ⟨?_,n/2,by omega_using [posN],by omega_using [posN, last],by omega_using [leN],byteU,?_,memU.trans memT,(restT.trans restU).mono (by decide)⟩
     · rw [eval_nonzero,byteU]
       change some (BitVec.ofNat 64 (n/2) != 0#64)=some true
       rw [ofNat_nonzero (by omega_using [size, leN]),decide_eq_true (by omega_using [posN, last] : 0<n/2)]
     · rw [countU,countNext]
 · refine ⟨positive,Nat.le_refl _,byte,?_,rfl,Keep.refl _ _⟩
   simpa only [Nat.sub_self] using count

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! The uncapped public scalar width is the significant bit length of the bound. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.RsaKeyGen (bitLength)

theorem policyBound_ok {s : State} {B dom : Addr} {Z k dl L : Nat} {bs : List Byte}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (positive : 0<k) (size : k<2^31) (shape : dl=2*k ∨ dl=3*k)
 (pointer : word s.mem B (8*sDom)=dom) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (domainLength : word s.mem B (8*sDL)=BitVec.ofNat 64 dl)
 (source : Source (if dl=2*k then dom else off dom (2*k)) bs s) (bsLength : bs.length=k)
 (inside : L<bs.length) (zeros : ∀ i<L,bs.getD i 0=0#8) (nonzero : bs.getD L 0≠0#8) :
 WP isa Policy.boundBits s fun t =>
 t.mem=s.mem.writeW (off B (8*sBits))
  (BitVec.ofNat 64 (8*(bs.length-L-1)+bitLength (bs.getD L 0).toNat)) ∧
 Keep [.x1,.x2,.x3,.x4,.x10] s t := by
 have bytePositive : 0<(bs.getD L 0).toNat := by
  have : (bs.getD L 0).toNat≠0 := fun eq => nonzero (BitVec.eq_of_toNat_eq eq)
  omega_using [this]
 have byteSize := (bs.getD L 0).isLt
 unfold Policy.boundBits
 rw [WP.seq_iff]
 refine WP.mono (policySource_ok scratch room base positive size shape pointer length domainLength) ?_
 rintro a ⟨⟨ptrA,lenA,zeroA,memA⟩,restA⟩
 rw [WP.seq_iff]
 refine WP.mono (policyScan_ok a (source.of_mem memA restA) (by omega_using [size, bsLength]) inside zeros nonzero ptrA (bsLength ▸ lenA)) ?_
 rintro b ⟨_,lenB,byteB,memB,restB⟩
 rw [WP.seq_iff]
 have shift : BitVec.ofNat 64 (bs.length-(L+1)) <<< 3=BitVec.ofNat 64 (8*(bs.length-L-1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
  omega_using []
 refine WP.mono (WP.keep [.x2] (Q:=fun c =>
  c.gpr .x2=BitVec.ofNat 64 (8*(bs.length-L-1)) ∧ c.mem=b.mem) ?_ rfl rfl rfl) ?_
 · brun [lenB,shift]
 · rintro c ⟨⟨lenC,memC⟩,restC⟩
   rw [WP.seq_iff]
   have zeroC : c.gpr .x10=0#64 :=
    (restC.gpr .x10 (by decide)).trans ((restB.gpr .x10 (by decide)).trans zeroA)
   refine WP.mono (policyCount_ok c byteSize bytePositive
    ((restC.gpr .x3 (by decide)).trans byteB) zeroC) ?_
   rintro d ⟨_,countD,memD,restD⟩
   have rest := ((restA.trans restB).trans restC).trans restD
   have mem : d.mem=s.mem := ((memD.trans memC).trans memB).trans memA
   have value : d.gpr .x10+d.gpr .x2=
    BitVec.ofNat 64 (8*(bs.length-L-1)+bitLength (bs.getD L 0).toNat) := by
    rw [countD,restD.gpr .x2 (by decide),lenC,←BitVec.ofNat_add]
    congr 1
    omega_using []
   refine WP.mono (WP.keep [.x10] (Q:=fun t =>
    t.mem=d.mem.writeW (off B (8*sBits)) (BitVec.ofNat 64 (8*(bs.length-L-1)+bitLength (bs.getD L 0).toNat)))
    ?_ rfl rfl rfl) ?_
   · brun [(rest.gpr .x0 (by decide)).trans base,hdr_enc (show sBits<32 by decide),value,
      (scratch.congr rest.wr).st (d:=8*sBits) (by unfold sBits;omega_using [room])]
   · rintro t ⟨memT,restT⟩
     exact ⟨by rw [memT,mem],(rest.trans restT).mono (by decide)⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Conservative policy width derives solely from public p or q bytes. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure PolicyBoundPublic where
 B : Addr
 Z : Nat
 dom : Addr
 k : Nat
 dl : Nat
 bs : List Byte
 L : Nat
 room : 256≤Z
 positive : 0<k
 size : k<2^31
 shape : dl=2*k ∨ dl=3*k
 length : bs.length=k
 inside : L<bs.length
 zeros : ∀ i<L,bs.getD i 0=0#8
 nonzero : bs.getD L 0≠0#8

def boundPointer (q : PolicyBoundPublic) : Addr :=if q.dl=2*q.k then q.dom else off q.dom (2*q.k)

def boundScan (q : PolicyBoundPublic) : PolicyScanPublic :=
 ⟨boundPointer q,q.bs,q.L,by rw [q.length];exact q.size,q.inside,q.zeros,q.nonzero⟩

structure PolicyBoundReady (q : PolicyBoundPublic) (s : State) : Prop where
 scratch : Scr s q.B q.Z
 base : s.gpr .x0=q.B
 pointer : word s.mem q.B (8*sDom)=q.dom
 length : word s.mem q.B (8*sLen)=BitVec.ofNat 64 q.k
 domainLength : word s.mem q.B (8*sDL)=BitVec.ofNat 64 q.dl
 source : Source (boundPointer q) q.bs s

def BoundScanReady (q : PolicyBoundPublic) (s : State) : Prop :=
 PolicyScanReady (boundScan q) 0 s ∧ s.gpr .x0=q.B

theorem policyBound_ct : RelCT isa (Two PolicyBoundReady) Policy.boundBits (fun _ _ =>True) := by
 unfold Policy.boundBits
 refine RelCT.seq (two_piece (Ψ:=BoundScanReady) [.x0] (fun _ s t hs ht r hr =>by
  have eq : r= .x0 := by simpa using hr
  subst r;exact hs.base.trans ht.base.symm) (by taint_decide) ?_) ?_
 · intro q s h
   refine WP.mono (policySource_ok h.scratch q.room h.base q.positive q.size q.shape h.pointer h.length h.domainLength) ?_
   rintro t ⟨⟨ptr,count,_,mem⟩,rest⟩
   exact ⟨⟨h.source.of_mem mem rest,by change t.gpr .x1=off (boundPointer q) 0;simpa [off,boundPointer] using ptr,
    by change t.gpr .x2=BitVec.ofNat 64 (q.bs.length-0);simpa only [Nat.sub_zero,q.length] using count⟩,(rest.gpr .x0 (by decide)).trans h.base⟩
 · refine RelCT.seq (two_post (Ψ:=fun q s =>s.gpr .x0=q.B ∧ s.gpr .x3=BitVec.ofNat 64 (q.bs.getD q.L 0).toNat)
    (two_map boundScan (fun _ _ h =>h.1) policyScan_ct) ?_)
    (two_taint [.x0,.x3] (fun _ s t hs ht r hr =>by
     simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl|rfl
     · exact hs.1.trans ht.1.symm
     · exact hs.2.trans ht.2.symm) (by taint_decide))
   rintro q s ⟨scan,base⟩
   refine WP.mono (policyScan_ok s scan.source (by change q.bs.length<2^31;rw [q.length];exact q.size) q.inside q.zeros q.nonzero
    (by simpa only [off,BitVec.add_zero] using scan.pointer)
    (by simpa only [Nat.sub_zero] using scan.remaining)) ?_
   rintro t ⟨_,_,byte,_,rest⟩
   exact ⟨(rest.gpr .x0 (by decide)).trans base,byte⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.PolicyRecognize`, which this module and modules that import it used -/

section

/-! Full native exact-group recognition, including the conservative general bound. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.RsaKeyGen (bitLength)

private theorem exec_adrSym (s : State) (r : Reg) (sym : String) :
 exec (.adrSym r sym) s=some (s.write .x r (s.syms sym)) := rfl

private theorem byteCount_bound : ∀ b : Byte,bitLength b.toNat≤8 := by decide +kernel

theorem policyRecognize_ok {s : State} {B domPtr : Addr} {Z k dl L : Nat} {dom bs : List Byte}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (positive : 0<k) (size : k<2^28) (shape : dl=2*k ∨ dl=3*k) (domLength : dom.length=dl)
 (pointer : word s.mem B (8*sDom)=domPtr) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (domainLength : word s.mem B (8*sDL)=BitVec.ofNat 64 dl)
 (domainSource : Source domPtr dom s)
 (domainOutside : ∀ i<dom.length,8*sBits+8≤ofs B (domPtr+BitVec.ofNat 64 i))
 (source : Source (if dl=2*k then domPtr else off domPtr (2*k)) bs s) (bsLength : bs.length=k)
 (inside : L<bs.length) (zeros : ∀ i<L,bs.getD i 0=0#8) (nonzero : bs.getD L 0≠0#8)
 (records : PolicyTableAt B (s.syms Policy.tableSym) Policy.groups s) :
 WP isa Policy.recognize s fun t =>
 word t.mem B (8*sBits)=BitVec.ofNat 64
  (policyWidth (8*(bs.length-L-1)+bitLength (bs.getD L 0).toNat) k dom Policy.groups) ∧
 Outside B (8*sBits) 8 s.mem t.mem ∧ Keep recordClobbers s t := by
 let N := 8*(bs.length-L-1)+bitLength (bs.getD L 0).toNat
 unfold Policy.recognize
 rw [WP.seq_iff]
 refine WP.mono_syms (policyBound_ok scratch room base positive (by omega_using [size]) shape pointer length domainLength
  source bsLength inside zeros nonzero) ?_
 rintro a ⟨memA,restA⟩ symsA
 have frameA : Outside B (8*sBits) 8 s.mem a.mem := by rw [memA];exact writeW_outside _ _ _ (by decide)
 have headerA (i : Nat) (hi : i<32) (different : i≠sBits) : word a.mem B (8*i)=word s.mem B (8*i) :=
  header_other frameA (by decide) hi different
 have sourceA := domainSource.after_outside frameA restA domainOutside
 have recordsA := records.after_header frameA restA
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x4,.x7] (Q:=fun b =>
  b.gpr .x4=s.syms Policy.tableSym ∧ b.gpr .x7=BitVec.ofNat 64 Policy.groups.length ∧ b.mem=a.mem) ?_ rfl rfl rfl) ?_
 · brun [exec_adrSym,symsA,show Policy.groups.length=10 from rfl]
 · rintro b ⟨⟨ptrB,countB,memB⟩,restB⟩
   have rest := restA.trans restB
   have cap : word b.mem B (8*sBits)=BitVec.ofNat 64 N := by rw [memB,memA,word_writeW_self]
   refine WP.mono (policyLoop_ok (scratch.congr rest.wr) room ((rest.gpr .x0 (by decide)).trans base)
    (sourceA.of_mem memB restB) (recordsA.after_mem memB restB) (by omega_using [shape, domLength]) positive size
    (by rw [memB,headerA sDom (by decide) (by decide)];exact pointer)
    (by rw [memB,headerA sDL (by decide) (by decide),domainLength,domLength])
    (by rw [memB,headerA sLen (by decide) (by decide)];exact length) cap
    (by have h := byteCount_bound (bs.getD L 0#8);dsimp [N];omega_using [size, bsLength, h]) ptrB countB (by decide) (by decide)) ?_
   rintro t ⟨widthT,frameT,restT⟩
   refine ⟨widthT,?_,(rest.trans restT).mono (by simp [recordClobbers])⟩
   have frameB : Outside B (8*sBits) 8 s.mem b.mem := by rw [memB];exact frameA
   exact frameB.trans frameT

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Public inputs and phase boundaries of the complete vetted-group recognizer. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure RecognizePublic extends PolicyBoundPublic where
 domBytes : List Byte
 table : Addr
 domLength : domBytes.length=dl
 small : k<2^28

def initialPolicyWidth (q : RecognizePublic) : Nat :=
 8*(q.bs.length-q.L-1)+Spec.RsaKeyGen.bitLength (q.bs.getD q.L 0).toNat

private theorem byteBits : ∀ b : Byte,Spec.RsaKeyGen.bitLength b.toNat≤8 := by decide +kernel

def recognizedLoop (q : RecognizePublic) : PolicyLoopPublic :=
 ⟨⟨q.B,q.Z,q.dom,q.table,q.domBytes,⟨256,225,Spec.Ffdh.modp2048Prime⟩,q.k,q.room,
   by have :=q.domLength;have :=q.shape;omega_arith,q.positive,q.small⟩,
  Policy.groups.tail,initialPolicyWidth q,
  by have :=byteBits (q.bs.getD q.L 0);have :=q.inside;have :=q.size;have :=q.length;unfold initialPolicyWidth;omega_arith,
  by decide⟩

structure RecognizeReady (q : RecognizePublic) (s : State) : Prop extends PolicyBoundReady q.toPolicyBoundPublic s where
 domainSource : Source q.dom q.domBytes s
 domainOutside : ∀ i<q.domBytes.length,8*sBits+8≤ofs q.B (q.dom+BitVec.ofNat 64 i)
 records : PolicyTableAt q.B q.table Policy.groups s
 symbol : s.syms Policy.tableSym=q.table

structure RecognizeBound (q : RecognizePublic) (s : State) : Prop where
 scratch : Scr s q.B q.Z
 base : s.gpr .x0=q.B
 source : Source q.dom q.domBytes s
 records : PolicyTableAt q.B q.table Policy.groups s
 domain : word s.mem q.B (8*sDom)=q.dom
 length : word s.mem q.B (8*sDL)=BitVec.ofNat 64 q.domBytes.length
 keyLength : word s.mem q.B (8*sLen)=BitVec.ofNat 64 q.k
 width : word s.mem q.B (8*sBits)=BitVec.ofNat 64 (initialPolicyWidth q)
 symbol : s.syms Policy.tableSym=q.table

theorem recognize_bound_ok {q : RecognizePublic} {s : State} (h : RecognizeReady q s) :
 WP isa Policy.boundBits s (RecognizeBound q) := by
 refine WP.mono_syms (policyBound_ok h.scratch q.room h.base q.positive q.size q.shape h.pointer h.length h.domainLength
  h.source q.length q.inside q.zeros q.nonzero) ?_
 rintro t ⟨mem,rest⟩ syms
 have frame : Outside q.B (8*sBits) 8 s.mem t.mem :=by rw [mem];exact writeW_outside _ _ _ (by decide)
 have header (i : Nat) (hi : i<32) (ne : i≠sBits) :=header_other frame (by decide) hi ne
 exact ⟨h.scratch.congr rest.wr,(rest.gpr .x0 (by decide)).trans h.base,
  h.domainSource.after_outside frame rest h.domainOutside,h.records.after_header frame rest,
  (header sDom (by decide) (by decide)).trans h.pointer,
  by rw [header sDL (by decide) (by decide),h.domainLength,q.domLength],
  (header sLen (by decide) (by decide)).trans h.length,
  by rw [mem,word_writeW_self];rfl,(congrFun syms Policy.tableSym).trans h.symbol⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Full group recognition reveals only the public domain, never private entropy. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem execAdr (s : State) (r : Reg) (sym : String) :
 exec (.adrSym r sym) s=some (s.write .x r (s.syms sym)) :=rfl

theorem policyRecognize_ct : RelCT isa (Two RecognizeReady) Policy.recognize (fun _ _ =>True) := by
 unfold Policy.recognize
 refine RelCT.seq (two_post (Ψ:=RecognizeBound)
  (two_map RecognizePublic.toPolicyBoundPublic (fun _ _ h =>h.toPolicyBoundReady) policyBound_ct)
  (fun _ _ h =>recognize_bound_ok h)) ?_
 refine RelCT.seq (two_piece (Ψ:=fun q s =>PolicyLoopReady (recognizedLoop q) s) []
  (fun _ _ _ _ _ r hr =>by simp at hr) (by taint_decide) ?_)
  (two_map recognizedLoop (fun _ _ h =>h) policyLoop_ct)
 intro q s h
 refine WP.mono (WP.keep [.x4,.x7] (Q:=fun t =>t.gpr .x4=q.table ∧
  t.gpr .x7=BitVec.ofNat 64 10 ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [execAdr,h.symbol]
 · rintro t ⟨⟨ptr,count,mem⟩,rest⟩
   have records :=h.records.after_mem mem rest
   exact ⟨⟨h.scratch.congr rest.wr,(rest.gpr .x0 (by decide)).trans h.base,h.source.of_mem mem rest,records.1,
    mem ▸ h.domain,mem ▸ h.length,mem ▸ h.keyLength,mem ▸ h.width,ptr⟩,records,count⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.MetadataTiming`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.Metadata`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.MetadataRows`, which only this module used -/

section

/-! The public subtraction loop computes exactly ceil(N/5). -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

theorem metadataRowStep (s : State) {L j : Nat} (positive : 5≤L) (fit : L<2^63)
 (remaining : s.gpr .x12=BitVec.ofNat 64 L) (count : s.gpr .x13=BitVec.ofNat 64 j) :
 WP isa (.block Policy.rowStep) s fun t =>
 (t.gpr .x12=BitVec.ofNat 64 (L-5) ∧ t.gpr .x13=BitVec.ofNat 64 (j+1) ∧
 t.gpr .x14=(if L-5<5 then 1#64 else 0#64) ∧ t.mem=s.mem) ∧ Keep [.x12,.x13,.x14] s t := by
 have sub : BitVec.ofNat 64 L-5#64=BitVec.ofNat 64 (L-5) :=
  BitVec.ofNat_sub_ofNat_of_le L 5 (by decide) positive
 refine WP.keep [.x12,.x13,.x14] ?_ rfl rfl rfl
 unfold Policy.rowStep
 brun [remaining,count,sub,sign_sub (a:=L-5) (b:=5) (by omega_using [fit]) (by decide)]
 constructor
 · exact (BitVec.ofNat_add _ _).symm
 · change ((BitVec.ofNat 64 (L-5)+ ~~~5#64+1#64) >>> 63)=_
   rw [BitVec.add_assoc,←BitVec.neg_eq_not_add,←BitVec.sub_eq_add_neg]
   exact sign_sub (by omega_using [fit]) (by decide)

theorem metadataRows_ok (s : State) {N : Nat} (positive : 0<N) (bound : N≤8192)
 (remaining : s.gpr .x12=BitVec.ofNat 64 (N+4)) (count : s.gpr .x13=0#64) :
 WP isa (.loop (.block Policy.rowStep) (.zero .x .x14)) s fun t =>
 t.gpr .x13=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N) ∧ t.mem=s.mem ∧ Keep [.x12,.x13,.x14] s t := by
 let d := (N+4)/5
 have dPositive : 0<d := by dsimp [d];omega_using [positive]
 let I := fun n t => ∃ j, n=d-j ∧ j<d ∧
  t.gpr .x12=BitVec.ofNat 64 (N+4-5*j) ∧ t.gpr .x13=BitVec.ofNat 64 j ∧
  t.mem=s.mem ∧ Keep [.x12,.x13,.x14] s t
 refine WP.loop (M:=isa) I ?_ d s ?_
 · intro n t h
   obtain ⟨j,rem,hj,left,countT,mem,keep⟩ := h
   have enough : 5≤N+4-5*j := by dsimp [d] at hj;omega_using [hj]
   refine WP.mono (metadataRowStep t enough (by omega_using [bound]) left countT) ?_
   rintro u ⟨⟨leftU,countU,flagU,memU⟩,keepU⟩
   have same : N+4-5*j-5=N+4-5*(j+1) := by omega_using []
   have flag : (N+4-5*j-5<5) ↔ ¬j+1<d := by dsimp [d];omega_using []
   by_cases more : j+1<d
   · right
     refine ⟨?_,d-(j+1),by omega_using [rem, hj],j+1,rfl,more,?_,countU,memU.trans mem,(keep.trans keepU).mono (by decide)⟩
     · rw [eval_zero,flagU,ite_eq_right (by rw [flag];exact not_not_intro more)]
       decide
     · rw [leftU,same]
   · left
     have last : j+1=d := by omega_using [hj, more]
     refine ⟨?_,?_,memU.trans mem,(keep.trans keepU).mono (by decide)⟩
     · rw [eval_zero,flagU,ite_eq_left (flag.mpr more)]
       decide
     · rw [countU,last]
       rfl
 · refine ⟨0,by omega_using [],dPositive,?_,count,rfl,Keep.refl _ _⟩
   simpa using remaining

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Exact serialization of the reviewed sampling width and comb row count. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/MetadataHead.lean`, which only this module imported.
section

/-! Public scalar width metadata is computed without assuming initialized arithmetic arrays. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem metadataHead_ok {s : State} {B : Addr} {Z N : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B) (bound : N≤8192)
 (bits : word s.mem B (8*sBits)=BitVec.ofNat 64 N) :
 WP isa (.block Policy.metadataHead) s fun t =>
 (t.gpr .x10=BitVec.ofNat 64 N ∧ t.gpr .x11=BitVec.ofNat 64 ((N+7)/8) ∧
 t.gpr .x12=BitVec.ofNat 64 (N+4) ∧ t.gpr .x13=0#64 ∧
 t.mem=s.mem.writeW (off B (8*sBytes)) (BitVec.ofNat 64 ((N+7)/8))) ∧
 Keep [.x10,.x11,.x12,.x13] s t := by
 have shift : (BitVec.ofNat 64 N+7#64) >>> 3=BitVec.ofNat 64 ((N+7)/8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_add,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  omega_using [bound]
 refine WP.keep [.x10,.x11,.x12,.x13] ?_ rfl rfl rfl
 unfold Policy.metadataHead
 brun [base,hdr_enc (show sBits<32 by decide),hdr_enc (show sBytes<32 by decide),
  scratch.ld (d:=8*sBits) (by unfold sBits;omega_using [room]),scratch.st (d:=8*sBytes) (by unfold sBytes;omega_using [room]),bits,shift]
 exact (BitVec.ofNat_add _ _).symm

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/MetadataTail.lean`, which only this module imported.
section

/-! Serialize the public metadata into the immutable canonical context. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem metadataTail_ok {s : State} {B ctx : Addr} {Z N bytes rows : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (output : Scr s ctx 24)
 (base : s.gpr .x0=B) (context : word s.mem B (8*sCtx)=ctx)
 (bits : s.gpr .x10=BitVec.ofNat 64 N) (width : s.gpr .x11=BitVec.ofNat 64 bytes)
 (count : s.gpr .x13=BitVec.ofNat 64 rows) :
 WP isa (.block Policy.metadataTail) s fun t =>
 t.mem=(((s.mem.writeW (off B (8*sRows)) (BitVec.ofNat 64 rows)).writeW
  ctx (BitVec.ofNat 64 N)).writeW (off ctx 8) (BitVec.ofNat 64 bytes)).writeW
  (off ctx 16) (BitVec.ofNat 64 rows) ∧ Keep [.x8] s t := by
 have frame : Outside B (8*sRows) 8 s.mem (s.mem.writeW (off B (8*sRows)) (BitVec.ofNat 64 rows)) :=
  writeW_outside _ _ _ (by decide)
 have pointer : word (s.mem.writeW (off B (8*sRows)) (BitVec.ofNat 64 rows)) B (8*sCtx)=ctx :=
  (frame.word (Or.inl (by decide : 8*sCtx+8≤8*sRows)) (by decide)).trans context
 refine WP.keep [.x8] ?_ rfl rfl rfl
 unfold Policy.metadataTail
 brun [base,hdr_enc (show sRows<32 by decide),hdr_enc (show sCtx<32 by decide),
  scratch.ld (d:=8*sCtx) (by unfold sCtx;omega_using [room]),scratch.st (d:=8*sRows) (by unfold sRows;omega_using [room]),
  pointer,bits,width,count,
  (show InRegions s.wr ctx 8 by simpa [off] using output.st (d:=0) (by decide)),output.st (d:=8) (by decide),output.st (d:=16) (by decide)]

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def metadataMemory (m : Mem) (B ctx : Addr) (N : Nat) : Mem :=
 let m1 := m.writeW (off B (8*sBytes)) (BitVec.ofNat 64 ((N+7)/8))
 let m2 := m1.writeW (off B (8*sRows)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N))
 ((m2.writeW ctx (BitVec.ofNat 64 N)).writeW (off ctx 8) (BitVec.ofNat 64 ((N+7)/8))).writeW
  (off ctx 16) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N))

theorem metadata_ok {s : State} {B ctx : Addr} {Z N : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (output : Scr s ctx 24)
 (base : s.gpr .x0=B) (context : word s.mem B (8*sCtx)=ctx)
 (bits : word s.mem B (8*sBits)=BitVec.ofNat 64 N) (positive : 0<N) (bound : N≤8192) :
 WP isa Policy.metadata s fun t => t.mem=metadataMemory s.mem B ctx N ∧
 Keep [.x8,.x10,.x11,.x12,.x13,.x14] s t := by
 unfold Policy.metadata
 rw [WP.seq_iff]
 refine WP.mono (metadataHead_ok scratch room base bound bits) ?_
 rintro u ⟨⟨bitsU,widthU,leftU,countU,memU⟩,restU⟩
 rw [WP.seq_iff]
 refine WP.mono (metadataRows_ok u positive bound leftU countU) ?_
 rintro v ⟨countV,memV,restV⟩
 have rest := restU.trans restV
 have frame : Outside B (8*sBytes) 8 s.mem u.mem := by
  rw [memU];exact writeW_outside _ _ _ (by decide)
 have ctxV : word v.mem B (8*sCtx)=ctx := by
  rw [memV]
  exact (frame.word (Or.inl (by decide : 8*sCtx+8≤8*sBytes)) (by decide)).trans context
 refine WP.mono (metadataTail_ok (scratch.congr rest.wr) room (output.congr rest.wr)
  ((rest.gpr .x0 (by decide)).trans base) ctxV
  ((restV.gpr .x10 (by decide)).trans bitsU) ((restV.gpr .x11 (by decide)).trans widthU) countV) ?_
 rintro t ⟨memT,restT⟩
 refine ⟨?_,(rest.trans restT).mono (by decide)⟩
 rw [memV,memU] at memT
 exact memT

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Public metadata uses a public row count and fixed context addresses. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure MetadataPublic where
 B : Addr
 Z : Nat
 ctx : Addr
 N : Nat
 room : 256≤Z
 positive : 0<N
 bound : N≤8192

structure MetadataReady (q : MetadataPublic) (s : State) : Prop where
 scratch : Scr s q.B q.Z
 base : s.gpr .x0=q.B
 context : word s.mem q.B (8*sCtx)=q.ctx
 bits : word s.mem q.B (8*sBits)=BitVec.ofNat 64 q.N

structure MetadataHeadReady (q : MetadataPublic) (s : State) : Prop where
 scratch : Scr s q.B q.Z
 base : s.gpr .x0=q.B
 context : word s.mem q.B (8*sCtx)=q.ctx
 remaining : s.gpr .x12=BitVec.ofNat 64 (q.N+4)
 count : s.gpr .x13=0#64

structure MetadataTailReady (q : MetadataPublic) (s : State) : Prop where
 scratch : Scr s q.B q.Z
 base : s.gpr .x0=q.B
 context : word s.mem q.B (8*sCtx)=q.ctx

theorem metadataTail_ct : RelCT isa (Two MetadataTailReady) (.block Policy.metadataTail) (fun _ _ =>True) := by
 change RelCT isa (Two MetadataTailReady) (.block ([sth .x13 sRows,ldh .x8 sCtx]++[st .x10 .x8 0,st .x11 .x8 8,st .x13 .x8 16])) _
 apply RelCT.block_append
 refine RelCT.seq (two_piece (Ψ:=fun q s =>s.gpr .x8=q.ctx) [.x0] (fun _ s t hs ht r hr =>by
  have eq : r= .x0 := by simpa using hr
  subst r;exact hs.base.trans ht.base.symm) (by taint_decide) ?_)
  (two_taint [.x8] (fun _ s t hs ht r hr =>by
   have eq : r= .x8 := by simpa using hr
   subst r;exact hs.trans ht.symm) (by taint_decide))
 intro q s h
 have frame :=writeW_outside s.mem q.B (d:=8*sRows) (s.gpr .x13) (by decide : 8*sRows+8≤2^64)
 have pointer :=(frame.word (Or.inl (by decide : 8*sCtx+8≤8*sRows)) (by decide)).trans h.context
 brun [h.base,hdr_enc (show sRows<32 by decide),hdr_enc (show sCtx<32 by decide),
  h.scratch.st (d:=8*sRows) (by have :=q.room;unfold sRows;omega_using [this]),
  h.scratch.ld (d:=8*sCtx) (by have :=q.room;unfold sCtx;omega_using [this]),pointer]

theorem metadata_ct : RelCT isa (Two MetadataReady) Policy.metadata (fun _ _ =>True) := by
 unfold Policy.metadata
 refine RelCT.seq (two_piece (Ψ:=MetadataHeadReady) [.x0] (fun _ s t hs ht r hr =>by
  have eq : r= .x0 := by simpa using hr
  subst r;exact hs.base.trans ht.base.symm) (by taint_decide) ?_) ?_
 · intro q s h
   refine WP.mono (metadataHead_ok h.scratch q.room h.base q.bound h.bits) ?_
   rintro t ⟨⟨_,_,remaining,count,mem⟩,rest⟩
   have frame : Outside q.B (8*sBytes) 8 s.mem t.mem :=by rw [mem];exact writeW_outside _ _ _ (by decide)
   exact ⟨h.scratch.congr rest.wr,(rest.gpr .x0 (by decide)).trans h.base,
    (header_other frame (by decide) (by decide) (by decide)).trans h.context,remaining,count⟩
 · refine RelCT.seq (two_post (Ψ:=MetadataTailReady)
    (two_taint [.x12,.x13] (fun _ s t hs ht r hr =>by
     simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl|rfl
     · exact hs.remaining.trans ht.remaining.symm
     · exact hs.count.trans ht.count.symm) (by taint_decide)) ?_) metadataTail_ct
   intro q s h
   refine WP.mono (metadataRows_ok s q.positive q.bound h.remaining h.count) ?_
   rintro t ⟨_,mem,rest⟩
   exact ⟨h.scratch.congr rest.wr,(rest.gpr .x0 (by decide)).trans h.base,mem ▸ h.context⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.PrecomputeFieldFrame`, which only this module used -/

section

/-! Modulus setup preserves the cached-generation controls in the upper header. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PrecomputeField.lean`, which only this module imported.
section

/-! Context creation reuses the verified public modulus loading and R² construction. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem precomputeField_ok (M : Mont) {s : State} {B np : Addr} {Z k : Nat} {nb : List Byte}
 (scratch : Scr s B Z) (base : s.gpr .x0=B) (room : slot ((k+7)/8) 8≤Z)
 (positive : 9≤k) (size : k<2^31)
 (length : word s.mem B (8*Public.sK)=BitVec.ofNat 64 k) (modulusPtr : word s.mem B (8*Public.sN)=np)
 (source : Src s B Z np nb) (span : InRegions (s.rd++s.wr) np k) (byteLength : nb.length=k)
 (odd : Spec.Rsa.os2ip nb%2=1) (normalized : 2^(64*((k+7)/8-1))≤Spec.Rsa.os2ip nb) :
 WP isa (seqs (pcLoadW++r2StepsPub M.mm)) s fun t =>
 ∃ mi, Good t B Z ((k+7)/8) mi ∧
 wv t.mem B (slot ((k+7)/8) 0) ((k+7)/8)=Spec.Rsa.os2ip nb ∧
 ((word t.mem B (slot ((k+7)/8) 0)).toNat*mi.toNat+1)%2^64=0 ∧
 wv t.mem B (slot ((k+7)/8) 4) ((k+7)/8)=2^(128*((k+7)/8))%Spec.Rsa.os2ip nb ∧
 Frm B (pcLoadRanges ((k+7)/8)++r2Ranges ((k+7)/8)) s.mem t.mem ∧ Keep mmRegs s t := by
 refine wp_seqs_append (by simp [pcLoadW,pcLoadWith]) (by simp [r2StepsPub]) ?_
 refine WP.mono (pcLoadW_ok scratch base room positive size length modulusPtr source span byteLength odd) ?_
 rintro u ⟨mi,good,modulus,inverse,frame,rest⟩
 refine WP.mono (r2Pub_ok M good room (by omega_using [positive]) (by omega_using [size]) modulus inverse odd normalized) ?_
 rintro t ⟨goodT,boundT,valueT,frameT,restT⟩
 have nowrap : B.toNat+slot ((k+7)/8) 8≤2^64 := by have := scratch.nowrap;omega_using [room, this]
 have sameMod : wv t.mem B (slot ((k+7)/8) 0) ((k+7)/8)=Spec.Rsa.os2ip nb :=
  (frameT.r2_wv nowrap (by decide) (by decide) (by decide) (by decide)).trans modulus
 have sameInverse : ((word t.mem B (slot ((k+7)/8) 0)).toNat*mi.toNat+1)%2^64=0 := by
  rw [frameT.r2_word nowrap (by decide) (by decide) (by decide) (by decide)]
  exact inverse
 have value : wv t.mem B (slot ((k+7)/8) 4) ((k+7)/8)=2^(128*((k+7)/8))%Spec.Rsa.os2ip nb := by
  rw [Nat.mod_eq_of_lt boundT] at valueT
  rw [←Nat.pow_add] at valueT
  have exponent : 64*((k+7)/8)+64*((k+7)/8)=128*((k+7)/8) := by omega_using []
  rw [exponent] at valueT
  exact valueT
 exact ⟨mi,goodT,sameMod,sameInverse,value,
  (frame.mono (fun r hr => List.mem_append_left _ hr)).trans
   (frameT.mono (fun r hr => List.mem_append_right _ hr)),(rest.trans restT).mono (by simp)⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum
open VG.Impl.Bignum.Public

theorem precomputeField_header {B : Addr} {w i : Nat} {m m' : Mem}
 (frame : Frm B (pcLoadRanges w++r2Ranges w) m m')
 (lower : 16≤i) (upper : i<32) (counter : i≠sCnt) :
 word m' B (8*i)=word m B (8*i) := by
 apply frame.word_eq _ (by omega_using [upper])
 intro r hr
 have belowN := hdr_lt_slot w aN upper
 have belowAcc := hdr_lt_slot w aAcc upper
 have belowTmp := hdr_lt_slot w aTmp upper
 have belowR2 := hdr_lt_slot w aR2 upper
 simp only [List.mem_append,pcLoadRanges,r2Ranges,List.mem_cons,List.not_mem_nil,or_false] at hr
 rcases hr with (rfl|rfl|rfl|rfl) | (rfl|rfl|rfl|rfl)
 all_goals simp only [sW,sArr,sMinv] at *
 all_goals omega_arith

theorem precomputeField_inscr {B : Addr} {w Z : Nat} {m m' : Mem}
 (frame : Frm B (pcLoadRanges w++r2Ranges w) m m') (room : slot w 8≤Z) : InScr B Z m m' := by
 intro x hx
 apply frame x
 intro r hr
 have inside : r.1+r.2≤slot w 8 := by
  rcases List.mem_append.mp hr with load | square
  · exact pcLoadRanges_le w r load
  · have two := slot_le (w:=w) (show Public.aAcc<8 by decide)
    have three := slot_le (w:=w) (show Public.aTmp<8 by decide)
    have four := slot_le (w:=w) (show Public.aR2<8 by decide)
    have count := hdr_lt_slot w 8 (show sCnt<32 by decide)
    simp only [r2Ranges,List.mem_cons,List.not_mem_nil,or_false] at square
    rcases square with rfl|rfl|rfl|rfl <;> omega_arith
 exact Or.inr (by omega_using [room, hx, inside])

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.PublicFrame`, which only this module used -/

section

/-! Public precomputation may write only its scratch buffer and output context. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Proof.Bignum

def publicWrites (p : Parameters) : List Region := [⟨p.B,p.Z⟩,⟨p.ctx,8*(3+34*p.w)⟩]

abbrev PublicFrame (p : Parameters) := Frame (publicWrites p)

theorem PublicFrame.of_inscr {p : Parameters} {m m' : Mem} (h : InScr p.B p.Z m m') : PublicFrame p m m' := by
 intro x hx
 apply h
 have no := hx ⟨p.B,p.Z⟩ (by simp [publicWrites])
 change ¬ofs p.B x+1≤p.Z at no
 omega_using [no]

theorem PublicFrame.of_build {p : Parameters} {m m' : Mem} (h : BuildFrame p m m') : PublicFrame p m m' := by
 apply h.sub
 intro r hr
 simp only [buildWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
 rcases hr with rfl | rfl
 · exact ⟨⟨p.B,p.Z⟩,by simp [publicWrites],fun _ h => h⟩
 · exact ⟨⟨p.ctx,8*(3+34*p.w)⟩,by simp [publicWrites],Offset.sub_base p.ctx (by unfold tableStart;omega_using [])⟩

theorem PublicFrame.of_context {p : Parameters} {m m' : Mem} {d n : Nat}
 (h : Outside p.ctx d n m m') (fit : d+n≤8*(3+34*p.w)) : PublicFrame p m m' := by
 have limit : 8*(3+34*p.w)<2^64 := by have := p.width;omega_using [this]
 have frame := outside_to_array (by omega_using [fit, limit]) (by omega_using [fit, limit]) h
 intro x hx
 apply frame x
 right
 have no := hx ⟨p.ctx,8*(3+34*p.w)⟩ (by simp [publicWrites])
 have sub := Offset.sub_base p.ctx (d:=d) (n:=n) fit
 have notInside : ¬(⟨off p.ctx d,n⟩ : Region).Contains x 1 := fun hi => no (sub x hi)
 change ¬ofs (off p.ctx d) x+1≤n at notInside
 omega_using [notInside]

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.PolicyDomain`, which only this module used -/

section

/-! Checked domains provide every bound-scan premise, including its nonzero leading byte. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh (lead lead_lt lead_zero lead_nonzero)
open VG.Proof.Ffdh.KeyScalar (bnd)

theorem checked_bound_bits {k : Nat} {dom : List Byte} (positive : 0<k)
 (shape : dom.length=2*k ∨ dom.length=3*k) (valid : Spec.Ffdh.domainValid k dom=true) :
 Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom))=
 8*((bnd k dom).length-lead (bnd k dom)-1)+
 Spec.RsaKeyGen.bitLength ((bnd k dom).getD (lead (bnd k dom)) 0).toNat := by
 have length := VG.Proof.Ffdh.KeyScalar.bnd_length shape
 have nonempty : bnd k dom≠[] := by intro h;rw [h] at length;simp at length;omega_using [positive, length]
 have modulus := VG.Proof.Ffdh.domainValid_mod valid
 simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at modulus
 dsimp only [Spec.Ffdh.domainOf] at modulus
 have bound := VG.Proof.Ffdh.KeyScalar.bound_bits (by omega_using [positive] : 1≤k) shape (fun _ => ⟨modulus.1.1.1,by omega_using [modulus]⟩)
 rw [length,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (lead_lt nonempty),Option.getD_some]
 exact bound

theorem checked_bound_lead {k : Nat} {dom : List Byte} (positive : 0<k)
 (shape : dom.length=2*k ∨ dom.length=3*k) (valid : Spec.Ffdh.domainValid k dom=true) :
 let bs := bnd k dom
 lead bs<bs.length ∧ (∀ i<lead bs,bs.getD i 0=0#8) ∧ bs.getD (lead bs) 0≠0#8 := by
 dsimp only
 have length := VG.Proof.Ffdh.KeyScalar.bnd_length shape
 have nonempty : bnd k dom≠[] := by intro h;rw [h] at length;simp at length;omega_using [positive, length]
 have inside := lead_lt nonempty
 refine ⟨inside,?_,?_⟩
 · intro i hi
   obtain ⟨bound,zero⟩ := lead_zero (bs:=bnd k dom) i hi
   change (bnd k dom)[i]=0#8 at zero
   simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some] using zero
 · intro zero
   have last : ¬lead (bnd k dom)+1<(bnd k dom).length := by
    intro before
    have nz := lead_nonzero nonempty before
    have same : (bnd k dom).getD (lead (bnd k dom)) 0=(bnd k dom)[lead (bnd k dom)] := by
     simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inside,Option.getD_some]
    exact nz (same.symm.trans zero)
   have bits := checked_bound_bits positive shape valid
   rw [zero] at bits
   have pos := scalarBound_positive valid
   have lengthPos : 0<Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom)) := by
    unfold Spec.RsaKeyGen.bitLength
    rw [ite_eq_right (by omega_using [pos] : Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom)≠0)]
    omega_using []
   have tail : (bnd k dom).length-lead (bnd k dom)-1=0 := by omega_using [last]
   rw [tail] at bits
   change Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom))=0 at bits
   omega_using [lengthPos, bits]

theorem Source.bound {s : State} {domPtr : Addr} {dom : List Byte} {k dl : Nat}
 (source : Source domPtr dom s) (positive : 0<k) (length : dom.length=dl) (shape : dl=2*k ∨ dl=3*k) :
 Source (if dl=2*k then domPtr else off domPtr (2*k)) (bnd k dom) s := by
 unfold bnd
 by_cases three : dl=3*k
 · rw [ite_eq_left (by omega_using [length, three] : dom.length=3*k),ite_eq_right (by omega_using [positive, three] : ¬dl=2*k)]
   exact (source.drop (2*k)).take k
 · rw [ite_eq_right (by omega_using [length, three] : ¬dom.length=3*k),ite_eq_left (by omega_using [shape, three] : dl=2*k)]
   exact source.take k

theorem policyDomain_ok {s : State} {B domPtr : Addr} {Z k dl : Nat} {dom : List Byte}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (positive : 0<k) (size : k≤1024) (shape : dl=2*k ∨ dl=3*k) (domLength : dom.length=dl)
 (valid : Spec.Ffdh.domainValid k dom=true)
 (pointer : word s.mem B (8*sDom)=domPtr) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (domainLength : word s.mem B (8*sDL)=BitVec.ofNat 64 dl)
 (source : Source domPtr dom s)
 (outside : ∀ i<dom.length,8*sBits+8≤ofs B (domPtr+BitVec.ofNat 64 i))
 (records : PolicyTableAt B (s.syms Policy.tableSym) Policy.groups s) :
 WP isa Policy.recognize s fun t =>
 word t.mem B (8*sBits)=BitVec.ofNat 64 (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom)) ∧
 Outside B (8*sBits) 8 s.mem t.mem ∧ Keep recordClobbers s t := by
 have shapeDom : dom.length=2*k ∨ dom.length=3*k := by omega_using [shape, domLength]
 have leadFacts := checked_bound_lead positive shapeDom valid
 have bits := checked_bound_bits positive shapeDom valid
 refine WP.mono (policyRecognize_ok scratch room base positive (by omega_using [size]) shape domLength pointer length domainLength
  source outside (source.bound positive domLength shape) (VG.Proof.Ffdh.KeyScalar.bnd_length shapeDom)
  leadFacts.1 leadFacts.2.1 leadFacts.2.2 records) ?_
 rintro t ⟨width,frame,rest⟩
 rw [←bits,policyWidth_spec positive shapeDom (domain_normalized positive valid)] at width
 exact ⟨width,frame,rest⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.PrecomputeNative`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.PrecomputeArithmetic`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.PrecomputeFinish`, which only this module used -/

section

/-! Compose prefix storage and the entire table into a canonical context. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/Serialization.lean`, which only this module imported.
section

/-! Native header, Montgomery prefix and table values form the reviewed canonical context. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Proof.Bignum

private theorem wordsAt_add (m : Mem) (a : Addr) (n k : Nat) :
 Spec.Rsa.wordsAt m a (n+k)=Spec.Rsa.wordsAt m a n++Spec.Rsa.wordsAt m (off a (8*n)) k := by
 simp only [Spec.Rsa.wordsAt,List.range_add,List.map_append,List.map_map]
 apply congrArg (fun xs => (List.range n).map (fun i => m.readW (a+BitVec.ofNat 64 (8*i)) 64)++xs)
 apply List.map_congr_left
 intro i _
 simp only [Function.comp_apply,off,BitVec.add_assoc,BitVec.ofNat_add,Nat.mul_add]

theorem wordsAt_of_wv {m : Mem} {a : Addr} {d w x : Nat} (value : wv m a d w=x) :
 Spec.Rsa.wordsAt m (off a d) w=Spec.Rsa.toWords x w := by
 apply List.ext_getElem
 · simp only [Spec.Rsa.wordsAt,Spec.Rsa.toWords,List.length_map,List.length_range]
 · intro i hi _
   obtain bound : i<w := by simpa only [Spec.Rsa.wordsAt,List.length_map,List.length_range] using hi
   obtain word := word_eq_ofNat m a d w bound
   rw [value] at word
   simpa only [Spec.Rsa.wordsAt,Spec.Rsa.toWords,List.getElem_map,List.getElem_range,VG.Proof.Bignum.word,
    off,BitVec.add_assoc,BitVec.ofNat_add] using word

theorem table_words {p : Parameters} {s : State} (table : TablePrefix p 32 s) (n : Nat) (hn : n≤32) :
 Spec.Rsa.wordsAt s.mem (off p.ctx (tableStart p.w)) (n*p.w)=
 (List.range n).flatMap (fun j => Spec.Rsa.toWords (entryValue p j) p.w) := by
 induction n with
 | zero => simp [Spec.Rsa.wordsAt]
 | succ n ih =>
   conv_lhs => arg 3;rw [Nat.add_mul,Nat.one_mul]
   rw [wordsAt_add,ih (by omega_using [hn]),List.range_succ,List.flatMap_append]
   simp only [List.flatMap_singleton]
   congr 1
   obtain addr : off (off p.ctx (tableStart p.w)) (8*(n*p.w))=off p.ctx (entryOffset p.w n) := by
    unfold off
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    congr 2
    unfold tableStart entryOffset
    ring
   rw [addr]
   exact wordsAt_of_wv (table n (by omega_using [hn]))

theorem canonical_words {p : Parameters} {s : State} {dom : List Byte}
 (words : p.w=Spec.Rsa.modulusWords p.k) (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p)
 (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g) (policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom))
 (header : Spec.Rsa.wordsAt s.mem p.ctx 3=
  [BitVec.ofNat 64 p.N,BitVec.ofNat 64 ((p.N+7)/8),BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N)])
 (first : wv s.mem p.ctx 24 p.w=p.P) (second : wv s.mem p.ctx (24+8*p.w) p.w=2^(128*p.w)%p.P)
 (table : TablePrefix p 32 s) :
 Spec.Rsa.wordsAt s.mem p.ctx (Spec.Ffdh.generationPrecomputedWords p.k)=VG.Proof.Ffdh.generationValues p.k dom := by
 obtain length : Spec.Ffdh.generationPrecomputedWords p.k=3+(2*p.w+32*p.w) := by
  simp only [Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,
   Spec.Rsa.precomputedWords,Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth,←words]
 rw [length,wordsAt_add]
 change Spec.Rsa.wordsAt s.mem p.ctx 3++Spec.Rsa.wordsAt s.mem (off p.ctx 24) (2*p.w+32*p.w)=_
 rw [wordsAt_add,header]
 obtain addr : off (off p.ctx 24) (8*(2*p.w))=off p.ctx (tableStart p.w) := by
  unfold off tableStart
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  congr 2
  omega_using []
 rw [addr,table_words table 32 (by omega_using [])]
 obtain mont : Spec.Rsa.wordsAt s.mem (off p.ctx 24) (2*p.w)=
   Spec.Rsa.toWords p.P p.w++Spec.Rsa.toWords (2^(128*p.w)%p.P) p.w := by
  rw [show 2*p.w=p.w+p.w by omega_using [],wordsAt_add,wordsAt_of_wv first]
  obtain addr2 : off (off p.ctx 24) (8*p.w)=off p.ctx (24+8*p.w) := by
   simp only [off,BitVec.add_assoc,BitVec.ofNat_add]
  rw [addr2,wordsAt_of_wv second]
 rw [mont]
 simp only [VG.Proof.Ffdh.generationValues,Spec.Rsa.FixedBaseComb.table,Spec.Rsa.FixedBaseComb.entries,
  Spec.Rsa.FixedBaseComb.teeth,entryValue,words,modulus,generator,policy,List.append_assoc]

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem prefixWords_unchanged {p : Parameters} {s t : State} {n : Nat}
 (_space : ContextSpace p s) (same : ∀ i<8*n,t.mem (p.ctx+BitVec.ofNat 64 i)=s.mem (p.ctx+BitVec.ofNat 64 i)) :
 Spec.Rsa.wordsAt t.mem p.ctx n=Spec.Rsa.wordsAt s.mem p.ctx n := by
 apply List.ext_getElem
 · simp only [Spec.Rsa.wordsAt,List.length_map,List.length_range]
 · intro i hi _
   obtain index : i<n := by simpa only [Spec.Rsa.wordsAt,List.length_map,List.length_range] using hi
   simp only [Spec.Rsa.wordsAt,List.getElem_map,List.getElem_range]
   apply Mem.readW_congr
   intro b hb
   simpa only [BitVec.ofNat_add,BitVec.add_assoc] using same (8*i+b) (by omega_using [index, hb])

theorem precomputeFinish_ok (M : Mont) {s : State} {p : Parameters} {domPtr : Addr} {dom bs : List Byte}
 (field : FieldInitial p s) (space : ContextSpace p s)
 (source : GeneratorSource p (domPtr+BitVec.ofNat 64 p.k) bs s)
 (words : p.w=(p.k+7)/8) (positive : 0<p.k) (size : p.k<2^31) (reduced : p.G<p.P)
 (bits : 0<p.N ∧ p.N≤8192)
 (context : word s.mem p.B (8*sCtx)=p.ctx) (domain : word s.mem p.B (8*sDom)=domPtr)
 (length : word s.mem p.B (8*sLen)=BitVec.ofNat 64 p.k)
 (rows : word s.mem p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N))
 (header : Spec.Rsa.wordsAt s.mem p.ctx 3=
  [BitVec.ofNat 64 p.N,BitVec.ofNat 64 ((p.N+7)/8),BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N)])
 (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p) (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g)
 (policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom)) :
 WP isa (.seq Precompute.storePrefix (.seq (Precompute.table M.mm) (.block [movi .x0 1]))) s fun t =>
 t.gpr .x0=1#64 ∧
 Spec.Rsa.wordsAt t.mem p.ctx (Spec.Ffdh.generationPrecomputedWords p.k)=VG.Proof.Ffdh.generationValues p.k dom ∧
 PublicFrame p s.mem t.mem ∧ Keep (.x0::mmRegs) s t := by
 rw [WP.seq_iff]
 refine WP.mono (storePrefix_ok field space context) ?_
 rintro a ⟨fieldA,firstA,secondA,frameA,sameA,restA⟩
 obtain spaceA := space.after restA
 obtain headerA : Spec.Rsa.wordsAt a.mem p.ctx 3=Spec.Rsa.wordsAt s.mem p.ctx 3 := by
  apply prefixWords_unchanged space
  intro i hi
  exact frameA _ (Or.inl (by rw [show ofs p.ctx (p.ctx+BitVec.ofNat 64 i)=i from Mem.sub_ofNat_toNat _ (by omega_using [hi])];omega_using [hi]))
 obtain sourceA : GeneratorSource p (domPtr+BitVec.ofNat 64 p.k) bs a := by
  refine ⟨⟨?_,?_,source.source.out⟩,source.length,source.value,source.separate⟩
  · intro i hi;rw [restA.rd,restA.wr];exact source.source.rd i hi
  · intro i hi
    exact (frameA _ (Or.inr (by have := source.separate i hi;omega_using [this]))).trans (source.source.val i hi)
 have sameHeader (i : Nat) (hi : i<32) : word a.mem p.B (8*i)=word s.mem p.B (8*i) :=
  workspace_header field.good sameA hi
 rw [WP.seq_iff]
 refine WP.mono (precomputeTable_ok M fieldA spaceA sourceA words positive size reduced bits
  ((sameHeader sCtx (by decide)).trans context) ((sameHeader sDom (by decide)).trans domain)
  ((sameHeader sLen (by decide)).trans length) ((sameHeader sRows (by decide)).trans rows)) ?_
 rintro b ⟨basisB,frameB,restB⟩
 obtain canonical : Spec.Rsa.wordsAt b.mem p.ctx (Spec.Ffdh.generationPrecomputedWords p.k)=VG.Proof.Ffdh.generationValues p.k dom := by
  apply canonical_words (by simpa only [Spec.Rsa.modulusWords] using words) modulus generator policy
  · rw [prefixWords_unchanged spaceA (fun i hi => frameB.prefix spaceA (by unfold tableStart;omega_using [hi])),headerA,header]
  · apply Eq.trans _ firstA
    apply wv_congr
    intro i hi
    apply Mem.readW_congr
    intro j hj
    obtain same := frameB.prefix spaceA (i:=24+8*i+j) (by unfold tableStart;omega_using [hi, hj])
    simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using same
  · apply Eq.trans _ secondA
    apply wv_congr
    intro i hi
    apply Mem.readW_congr
    intro j hj
    obtain same := frameB.prefix spaceA (i:=24+8*p.w+8*i+j) (by unfold tableStart;omega_using [hi, hj])
    simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using same
  · exact basisB.table
 refine WP.mono (WP.keep [.x0] (Q:=fun t =>t.gpr .x0=1#64 ∧ t.mem=b.mem) ?_ rfl rfl rfl) ?_
 · brun
 · rintro t ⟨⟨status,mem⟩,rest⟩
   exact ⟨status,by rw [mem];exact canonical,
    by rw [mem];exact (PublicFrame.of_context frameA (by omega_using [])).trans (PublicFrame.of_build frameB),
    ((restA.trans restB).trans rest).mono (by decide)⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! All arithmetic after public metadata: modulus loading, R², prefix and table. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem precomputeArithmetic_ok (M : Mont) {s : State} {p : Parameters} {domPtr : Addr} {dom nb gb : List Byte}
 (scratch : Scr s p.B p.Z) (base : s.gpr .x0=p.B) (space : ContextSpace p s)
 (modulusSource : Src s p.B p.Z domPtr nb) (modulusSpan : InRegions (s.rd++s.wr) domPtr p.k)
 (nbLength : nb.length=p.k) (nbValue : Spec.Rsa.os2ip nb=p.P)
 (odd : p.P%2=1) (normalized : 2^(64*(p.w-1))≤p.P)
 (source : GeneratorSource p (domPtr+BitVec.ofNat 64 p.k) gb s)
 (words : p.w=(p.k+7)/8) (positive : 9≤p.k) (size : p.k<2^31) (reduced : p.G<p.P)
 (bits : 0<p.N ∧ p.N≤8192)
 (context : word s.mem p.B (8*sCtx)=p.ctx) (domain : word s.mem p.B (8*sDom)=domPtr)
 (length : word s.mem p.B (8*sLen)=BitVec.ofNat 64 p.k)
 (rows : word s.mem p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N))
 (header : Spec.Rsa.wordsAt s.mem p.ctx 3=
  [BitVec.ofNat 64 p.N,BitVec.ofNat 64 ((p.N+7)/8),BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N)])
 (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p) (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g)
 (policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom)) :
 WP isa (.seq (seqs (pcLoadW++r2StepsPub M.mm))
  (.seq Precompute.storePrefix (.seq (Precompute.table M.mm) (.block [movi .x0 1])))) s fun t =>
 t.gpr .x0=1#64 ∧
 Spec.Rsa.wordsAt t.mem p.ctx (Spec.Ffdh.generationPrecomputedWords p.k)=VG.Proof.Ffdh.generationValues p.k dom ∧
 PublicFrame p s.mem t.mem ∧ Keep (.x0::mmRegs) s t := by
 rw [WP.seq_iff]
 obtain room : slot ((p.k+7)/8) 8≤p.Z := by rw [←words];exact p.room
 refine WP.mono (precomputeField_ok M scratch base room positive size length domain modulusSource modulusSpan nbLength
  (by rw [nbValue];exact odd) (by rw [nbValue,←words];exact normalized)) ?_
 rintro a ⟨mi,goodA,modulusA,inverseA,r2A,frameA,restA⟩
 let q : Parameters := {p with mi:=mi}
 obtain fieldA : FieldInitial q a := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [q,words] using goodA
  · simpa only [q,words,nbValue] using modulusA
  · simpa only [q,words] using inverseA
  · simpa only [q,words,nbValue] using r2A
 obtain inscr : InScr p.B p.Z s.mem a.mem := by
  apply precomputeField_inscr (w:=p.w) _ p.room
  simpa only [words] using frameA
 have frame (i : Nat) (hi : 16≤i) (hi' : i<32) (counter : i≠Public.sCnt) :
  word a.mem p.B (8*i)=word s.mem p.B (8*i) := precomputeField_header frameA hi hi' counter
 obtain spaceA : ContextSpace q a := ⟨(space.after restA).writable,space.outside⟩
 obtain sourceAP := source.after_inscr inscr restA
 obtain sourceA : GeneratorSource q (domPtr+BitVec.ofNat 64 q.k) gb a :=
  ⟨sourceAP.source,source.length,source.value,source.separate⟩
 obtain headerA : Spec.Rsa.wordsAt a.mem p.ctx 3=Spec.Rsa.wordsAt s.mem p.ctx 3 := by
  apply prefixWords_unchanged (n:=3) space
  intro i hi
  exact inscr _ (space.outside i (by omega_using [hi]))
 refine WP.mono (precomputeFinish_ok M fieldA spaceA sourceA words (by change 0<p.k;omega_using [positive]) size reduced bits
  ((frame sCtx (by decide) (by decide) (by decide)).trans context)
  ((frame sDom (by decide) (by decide) (by decide)).trans domain)
  ((frame sLen (by decide) (by decide) (by decide)).trans length)
  ((frame sRows (by decide) (by decide) (by decide)).trans rows)
  (headerA.trans header) modulus generator policy) ?_
 rintro t ⟨status,canonical,frameT,restT⟩
 exact ⟨status,canonical,(PublicFrame.of_inscr inscr).trans frameT,
  (restA.trans restT).mono (by decide)⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Functional composition of the complete native public precomputation routine. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PrecomputeEntry.lean`, which only this module imported.
section

/-! The native entry saves only public arguments in the scratch header. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def entryMemory (m : Mem) (B ctx dom dl k : Addr) : Mem :=
 (((m.writeW (off B (8*sCtx)) ctx).writeW (off B (8*sDom)) dom).writeW
 (off B (8*sDL)) dl).writeW (off B (8*sLen)) k

theorem precomputeEntry_ok {s : State} {B : Addr} {Z : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x5=B) :
 WP isa (.block Precompute.entry) s fun t =>
 (t.gpr .x0=B ∧ t.mem=entryMemory s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4)) ∧
 Keep [.x0] s t := by
 refine WP.keep [.x0] (Q:=fun t => t.gpr .x0=B ∧ t.mem=entryMemory s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4)) ?_ rfl rfl rfl
 unfold Precompute.entry entryMemory
 brun [base,st,hdr_enc (show sCtx<32 by decide),hdr_enc (show sDom<32 by decide),
  hdr_enc (show sDL<32 by decide),hdr_enc (show sLen<32 by decide),
  scratch.st (d:=8*sCtx) (by unfold sCtx;omega_using [room]),
  scratch.st (d:=8*sDom) (by unfold sDom;omega_using [room]),
  scratch.st (d:=8*sDL) (by unfold sDL;omega_using [room]),
  scratch.st (d:=8*sLen) (by unfold sLen;omega_using [room])]

theorem entryMemory_header (m : Mem) (B ctx dom dl k : Addr) :
 word (entryMemory m B ctx dom dl k) B (8*sCtx)=ctx ∧
 word (entryMemory m B ctx dom dl k) B (8*sDom)=dom ∧
 word (entryMemory m B ctx dom dl k) B (8*sDL)=dl ∧
 word (entryMemory m B ctx dom dl k) B (8*sLen)=k := by
 have separate (m : Mem) (i j : Nat) (hi : i<32) (hj : j<32) (different : i≠j) (v : Addr) :
  word (m.writeW (off B (8*i)) v) B (8*j)=word m B (8*j) :=
  Mem.readW_writeW_sep (Offset.sep B (by omega_using [different]) (by omega_using [hj]) (by omega_using [hi])) (by decide)
 unfold entryMemory
 rw [separate _ sLen sCtx (by decide) (by decide) (by decide) _,
  separate _ sDL sCtx (by decide) (by decide) (by decide) _,
  separate _ sDom sCtx (by decide) (by decide) (by decide) _,word_writeW_self,
  separate _ sLen sDom (by decide) (by decide) (by decide) _,
  separate _ sDL sDom (by decide) (by decide) (by decide) _,word_writeW_self,
  separate _ sLen sDL (by decide) (by decide) (by decide) _,word_writeW_self,word_writeW_self]
 exact ⟨rfl,rfl,rfl,rfl⟩

theorem entryMemory_range (m : Mem) (B ctx dom dl k : Addr) :
 Outside B 128 32 m (entryMemory m B ctx dom dl k) := by
 intro x hx
 have store (m : Mem) (i : Nat) (low : 16≤i) (high : i<20) (v : Addr) :
  (m.writeW (off B (8*i)) v) x=m x :=
  writeW_outside m B v (by omega_using [high]) x (by omega_using [hx, low, high])
 unfold entryMemory
 rw [store _ sLen (by decide) (by decide),store _ sDL (by decide) (by decide),
  store _ sDom (by decide) (by decide),store _ sCtx (by decide) (by decide)]

theorem entryMemory_frame (m : Mem) (B ctx dom dl k : Addr) (Z : Nat) (room : 256≤Z) :
 InScr B Z m (entryMemory m B ctx dom dl k) := by
 obtain frame := (Frame.refl [⟨B,Z⟩] m).writeW (r:=⟨B,Z⟩) (b:=off B (8*sCtx)) (by simp) ctx
  (Offset.contains_base _ (by unfold sCtx;omega_using [room]) (by decide))
 obtain frame := frame.writeW (r:=⟨B,Z⟩) (b:=off B (8*sDom)) (by simp) dom
  (Offset.contains_base _ (by unfold sDom;omega_using [room]) (by decide))
 obtain frame := frame.writeW (r:=⟨B,Z⟩) (b:=off B (8*sDL)) (by simp) dl
  (Offset.contains_base _ (by unfold sDL;omega_using [room]) (by decide))
 obtain frame := frame.writeW (r:=⟨B,Z⟩) (b:=off B (8*sLen)) (by simp) k
  (Offset.contains_base _ (by unfold sLen;omega_using [room]) (by decide))
 intro x hx
 exact frame x (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr;subst r;change ¬ofs B x+1≤Z;omega_using [hx])

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/MetadataMemory.lean`, which only this module imported.
section

/-! The metadata writer produces exactly the three reviewed header words. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum

theorem threeHeaderWords (m : Mem) (a : Addr) (N bytes rows : Nat) :
 Spec.Rsa.wordsAt (((m.writeW (off a 0) (BitVec.ofNat 64 N)).writeW
  (off a 8) (BitVec.ofNat 64 bytes)).writeW (off a 16) (BitVec.ofNat 64 rows)) a 3=
 [BitVec.ofNat 64 N,BitVec.ofNat 64 bytes,BitVec.ofNat 64 rows] := by
 change [_,_,_]=_
 dsimp only
 rw [List.cons.injEq]
 constructor
 · rw [Mem.readW_writeW_sep (Offset.sep a (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (Offset.sep a (by decide) (by decide) (by decide)) (by decide)]
   exact Mem.readW_writeW_self64 _ _ _
 · rw [List.cons.injEq]
   constructor
   · rw [Mem.readW_writeW_sep (Offset.sep a (by decide) (by decide) (by decide)) (by decide)]
     exact Mem.readW_writeW_self64 _ _ _
   · exact congrArg (fun x => [x]) (Mem.readW_writeW_self64 _ _ _)

theorem metadataMemory_header (m : Mem) (B ctx : Addr) (N : Nat) :
 Spec.Rsa.wordsAt (metadataMemory m B ctx N) ctx 3=
 [BitVec.ofNat 64 N,BitVec.ofNat 64 ((N+7)/8),BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N)] := by
 simpa only [metadataMemory,off,BitVec.add_zero] using
  threeHeaderWords ((m.writeW (off B (8*sBytes)) (BitVec.ofNat 64 ((N+7)/8))).writeW
   (off B (8*sRows)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N))) ctx N ((N+7)/8) (Spec.Rsa.FixedBaseComb.rows N)

theorem metadataMemory_frame (m : Mem) (p : Parameters) (N : Nat) : PublicFrame p m (metadataMemory m p.B p.ctx N) := by
 obtain bytes := (Frame.refl (publicWrites p) m).writeW (r:=⟨p.B,p.Z⟩) (b:=off p.B (8*sBytes)) (by simp [publicWrites])
  (BitVec.ofNat 64 ((N+7)/8)) (Offset.contains_base _ (by have := p.room;have := VG.Proof.Bignum.hdr_lt_slot p.w 8 (show sBytes<32 by decide);omega_arith) (by decide))
 obtain rows := bytes.writeW (r:=⟨p.B,p.Z⟩) (b:=off p.B (8*sRows)) (by simp [publicWrites])
  (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N)) (Offset.contains_base _ (by have := p.room;have := VG.Proof.Bignum.hdr_lt_slot p.w 8 (show sRows<32 by decide);omega_arith) (by decide))
 obtain bitHeader := rows.writeW (r:=⟨p.ctx,8*(3+34*p.w)⟩) (b:=p.ctx) (by simp [publicWrites])
  (BitVec.ofNat 64 N) (by change (p.ctx-p.ctx).toNat+8≤8*(3+34*p.w);simp;omega_using [])
 obtain byteHeader := bitHeader.writeW (r:=⟨p.ctx,8*(3+34*p.w)⟩) (b:=off p.ctx 8) (by simp [publicWrites])
  (BitVec.ofNat 64 ((N+7)/8)) (Offset.contains_base _ (by omega_using []) (by decide))
 exact byteHeader.writeW (r:=⟨p.ctx,8*(3+34*p.w)⟩) (b:=off p.ctx 16) (by simp [publicWrites])
  (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N)) (Offset.contains_base _ (by omega_using []) (by decide))

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/MetadataWorkspace.lean`, which only this module imported.
section

/-! Context metadata stores cannot overwrite the separate scratch controls. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

private theorem contextStore_workspace {p : Parameters} {s : State} (space : ContextSpace p s)
 (m : Mem) {d : Nat} (inside : d+8≤8*(3+34*p.w)) (value : Addr) :
 ∀ x,ofs p.B x<p.Z→(m.writeW (off p.ctx d) value) x=m x := by
 intro x hx
 obtain fit : d+8≤2^64 := by have := p.width;omega_using [inside, this]
 have outside (i : Nat) (hi : i<8) : p.Z≤ofs p.B (off p.ctx d+BitVec.ofNat 64 i) := by
  simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using space.outside (d+i) (by omega_using [inside, hi])
 apply writeW_outside m p.ctx value fit x
 exact (outside_shift_iff p.ctx x (by omega_using [fit]) fit).mpr (le_ofs_of_sep outside hx)

theorem metadataMemory_workspace {p : Parameters} {s : State} (space : ContextSpace p s) (N : Nat) :
 ∀ x,ofs p.B x<p.Z→metadataMemory s.mem p.B p.ctx N x=
 ((s.mem.writeW (off p.B (8*sBytes)) (BitVec.ofNat 64 ((N+7)/8))).writeW
  (off p.B (8*sRows)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N))) x := by
 intro x hx
 unfold metadataMemory
 rw [contextStore_workspace space _ (d:=16) (by omega_using []) _ x hx,
  contextStore_workspace space _ (d:=8) (by omega_using []) _ x hx]
 simpa only [off,BitVec.add_zero] using contextStore_workspace space _ (d:=0) (by omega_using []) _ x hx

theorem metadataMemory_controls {p : Parameters} {s : State} (space : ContextSpace p s)
 (scratch : Scr s p.B p.Z) (N : Nat) :
 word (metadataMemory s.mem p.B p.ctx N) p.B (8*sBytes)=BitVec.ofNat 64 ((N+7)/8) ∧
 word (metadataMemory s.mem p.B p.ctx N) p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N) ∧
 (∀ i<32,i≠sBytes→i≠sRows→word (metadataMemory s.mem p.B p.ctx N) p.B (8*i)=word s.mem p.B (8*i)) := by
 let m := (s.mem.writeW (off p.B (8*sBytes)) (BitVec.ofNat 64 ((N+7)/8))).writeW
  (off p.B (8*sRows)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N))
 have same (i : Nat) (hi : i<32) : word (metadataMemory s.mem p.B p.ctx N) p.B (8*i)=word m p.B (8*i) :=
  workspace_word (by have := scratch.nowrap;omega_using [this]) (metadataMemory_workspace space N)
   (by have := hdr_lt_slot p.w 8 hi;have := p.room;omega_arith)
 constructor
 · rw [same sBytes (by decide)]
   exact ((writeW_outside _ _ _ (by decide : 8*sRows+8≤2^64)).word
    (Or.inl (by decide : 8*sBytes+8≤8*sRows)) (by decide)).trans (word_writeW_self _ _ _ _)
 constructor
 · rw [same sRows (by decide)]
   exact word_writeW_self _ _ _ _
 · intro i hi notBytes notRows
   rw [same i hi]
   have separate {j : Nat} (hj : j<32) (different : i≠j) (m : Mem) (v : Addr) :
    word (m.writeW (off p.B (8*j)) v) p.B (8*i)=word m p.B (8*i) :=
    (writeW_outside _ _ _ (by omega_using [hj])).word (by omega_using [different]) (by omega_using [hi])
   exact (separate (by decide) notRows _ _).trans (separate (by decide) notBytes _ _)

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PublicSource.lean`, which only this module imported.
section

/-! Checked domain bytes are immutable throughout context creation. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure PublicSource (p : Parameters) (ptr : Addr) (bs : List Byte) (s : State) : Prop extends Source ptr bs s where
 scratchOutside : ∀ i<bs.length,p.Z≤ofs p.B (ptr+BitVec.ofNat 64 i)
 contextOutside : ∀ i<bs.length,8*(3+34*p.w)≤ofs p.ctx (ptr+BitVec.ofNat 64 i)

theorem PublicSource.after {p : Parameters} {ptr : Addr} {bs : List Byte} {s t : State} {rs : List Reg}
 (source : PublicSource p ptr bs s) (frame : PublicFrame p s.mem t.mem) (rest : Keep rs s t) : PublicSource p ptr bs t := by
 refine ⟨⟨?_,?_⟩,source.scratchOutside,source.contextOutside⟩
 · intro i hi;rw [rest.rd,rest.wr];exact source.readable i hi
 · intro i hi
   apply Eq.trans (frame _ ?_) (source.bytes i hi)
   intro r hr
   simp only [publicWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl
   · have out := source.scratchOutside i hi
     change ¬ofs p.B (ptr+BitVec.ofNat 64 i)+1≤p.Z
     omega_using [out]
   · have out := source.contextOutside i hi
     change ¬ofs p.ctx (ptr+BitVec.ofNat 64 i)+1≤8*(3+34*p.w)
     omega_using [out]

theorem PublicSource.toSrc {p : Parameters} {ptr : Addr} {bs : List Byte} {s : State}
 (source : PublicSource p ptr bs s) : Src s p.B p.Z ptr bs := by
 refine ⟨source.readable,?_,source.scratchOutside⟩
 intro i hi
 simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using source.bytes i hi

theorem PublicSource.take {p : Parameters} {ptr : Addr} {bs : List Byte} {s : State}
 (source : PublicSource p ptr bs s) (n : Nat) : PublicSource p ptr (bs.take n) s := by
 refine ⟨source.toSource.take n,?_,?_⟩
 all_goals intro i hi;have bound : i<bs.length := by rw [List.length_take] at hi;omega_using [hi]
 · exact source.scratchOutside i bound
 · exact source.contextOutside i bound

theorem PublicSource.drop {p : Parameters} {ptr : Addr} {bs : List Byte} {s : State}
 (source : PublicSource p ptr bs s) (n : Nat) : PublicSource p (ptr+BitVec.ofNat 64 n) (bs.drop n) s := by
 refine ⟨source.toSource.drop n,?_,?_⟩
 all_goals intro i hi;have bound : n+i<bs.length := by rw [List.length_drop] at hi;omega_using [hi]
 · simpa only [BitVec.ofNat_add,BitVec.add_assoc] using source.scratchOutside (n+i) bound
 · simpa only [BitVec.ofNat_add,BitVec.add_assoc] using source.contextOutside (n+i) bound

theorem PublicSource.generator {p : Parameters} {ptr : Addr} {dom : List Byte} {s : State}
 (source : PublicSource p ptr dom s) (length : 2*p.k≤dom.length)
 (value : p.G=(Spec.Ffdh.domainOf p.k dom).g) :
 GeneratorSource p (ptr+BitVec.ofNat 64 p.k) ((dom.drop p.k).take p.k) s := by
 obtain bytes := (source.drop p.k).take p.k
 refine ⟨bytes.toSrc,?_,?_,bytes.contextOutside⟩
 · simp only [List.length_take,List.length_drop];omega_using [length]
 · exact value.symm

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem precomputeNative_ok (M : Mont) {s : State} {p : Parameters} {domPtr : Addr} {dom : List Byte} {dl : Nat}
 (scratch : Scr s p.B p.Z) (space : ContextSpace p s) (output : Scr s p.ctx 24)
 (source : PublicSource p domPtr dom s) (span : InRegions (s.rd++s.wr) domPtr p.k)
 (words : p.w=(p.k+7)/8) (small : 64≤p.k) (large : p.k≤1024)
 (shape : dl=2*p.k ∨ dl=3*p.k) (domLength : dom.length=dl)
 (valid : Spec.Ffdh.domainValid p.k dom=true)
 (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p) (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g)
 (policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom))
 (context : s.gpr .x0=p.ctx) (domain : s.gpr .x2=domPtr) (domainLength : s.gpr .x3=BitVec.ofNat 64 dl)
 (length : s.gpr .x4=BitVec.ofNat 64 p.k) (base : s.gpr .x5=p.B)
 (records : PolicyTableAt p.B (s.syms Policy.tableSym) Policy.groups s) :
 WP isa (Precompute.code M.mm) s fun t =>
 t.gpr .x0=1#64 ∧
 Spec.Rsa.wordsAt t.mem p.ctx (Spec.Ffdh.generationPrecomputedWords p.k)=VG.Proof.Ffdh.generationValues p.k dom ∧
 PublicFrame p s.mem t.mem ∧ Keep (.x0::mmRegs) s t := by
 obtain room : 256≤p.Z := by have := p.room;unfold slot at this;omega_using [words, small, this]
 obtain positive : 0<p.k := by omega_using [small]
 obtain shapeDom : dom.length=2*p.k ∨ dom.length=3*p.k := by omega_using [shape, domLength]
 obtain bits : 0<p.N ∧ p.N≤8192 := by
  rw [policy]
  exact ⟨generation_bits_positive valid,generation_bits_bound positive large⟩
 obtain facts := (VG.Proof.Ffdh.domainValid_iff p.k dom).mp valid
 have modFacts := facts.1
 simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at modFacts
 unfold Precompute.code
 rw [WP.seq_iff]
 refine WP.mono_syms (precomputeEntry_ok scratch room base) ?_
 rintro a ⟨⟨baseA,memA⟩,restA⟩ symsA
 obtain entry : a.mem=entryMemory s.mem p.B p.ctx domPtr (BitVec.ofNat 64 dl) (BitVec.ofNat 64 p.k) := by
  rw [memA,context,domain,domainLength,length]
 obtain headers := entryMemory_header s.mem p.B p.ctx domPtr (BitVec.ofNat 64 dl) (BitVec.ofNat 64 p.k)
 rw [←entry] at headers
 obtain inscrA : InScr p.B p.Z s.mem a.mem := by
  rw [entry];exact entryMemory_frame _ _ _ _ _ _ _ room
 obtain frameA : PublicFrame p s.mem a.mem := PublicFrame.of_inscr inscrA
 obtain sourceA := source.after frameA restA
 obtain recordFrame : Outside p.B 128 32 s.mem a.mem := by rw [entry];exact entryMemory_range _ _ _ _ _ _
 obtain recordsA : PolicyTableAt p.B (a.syms Policy.tableSym) Policy.groups a := by
  rw [symsA]
  exact records.after_belowBits recordFrame restA (by decide)
 rw [WP.seq_iff]
 refine WP.mono (policyDomain_ok (scratch.congr restA.wr) room baseA positive large shape domLength valid
  headers.2.1 headers.2.2.2 headers.2.2.1 sourceA.toSource
  (fun i hi => Nat.le_trans (by unfold sBits;omega_using [room] : 8*sBits+8≤p.Z) (source.scratchOutside i hi)) recordsA) ?_
 rintro b ⟨bitsB,frameB,restB⟩
 obtain inscrB : InScr p.B p.Z a.mem b.mem :=
  InScr.of_outside frameB (by unfold sBits;omega_using [room])
 obtain publicB := PublicFrame.of_inscr (p:=p) inscrB
 obtain sourceB := sourceA.after publicB restB
 have headersB (i : Nat) (hi : i<32) (different : i≠sBits) : word b.mem p.B (8*i)=word a.mem p.B (8*i) :=
  header_other frameB (by decide) hi different
 rw [WP.seq_iff]
 obtain before := restA.trans restB
 refine WP.mono (metadata_ok (scratch.congr before.wr) room (output.congr before.wr)
  ((restB.gpr .x0 (by decide)).trans baseA)
  ((headersB sCtx (by decide) (by decide)).trans headers.1)
  (by rw [policy];exact bitsB) bits.1 bits.2) ?_
 rintro c ⟨memC,restC⟩
 obtain spaceB := space.after before
 obtain publicC : PublicFrame p b.mem c.mem := by rw [memC];exact metadataMemory_frame _ p _
 obtain sourceC := sourceB.after publicC restC
 obtain total := before.trans restC
 obtain controls := metadataMemory_controls spaceB (scratch.congr before.wr) p.N
 rw [←memC] at controls
 obtain headerC := metadataMemory_header b.mem p.B p.ctx p.N
 rw [←memC] at headerC
 have sameHeader (i : Nat) (hi : i<32) (different : i≠sBits) (notBytes : i≠sBytes) (notRows : i≠sRows) :
  word c.mem p.B (8*i)=word a.mem p.B (8*i) :=
  (controls.2.2 i hi notBytes notRows).trans (headersB i hi different)
 obtain odd : p.P%2=1 := by rw [modulus];exact modFacts.1.1.1
 obtain normalized : 2^(64*(p.w-1))≤p.P := by rw [modulus,words];exact domain_normalized positive valid
 obtain nbLength : (dom.take p.k).length=p.k := by simp only [List.length_take];omega_using [shape, domLength]
 obtain sourceMod := (sourceC.take p.k).toSrc
 obtain spanC : InRegions (c.rd++c.wr) domPtr p.k := by rw [total.rd,total.wr];exact span
 refine WP.mono (precomputeArithmetic_ok M (scratch.congr total.wr)
  (((restB.trans restC).gpr .x0 (by simp [recordClobbers])).trans baseA)
  (space.after total) sourceMod spanC nbLength modulus.symm odd normalized
  (sourceC.generator (by omega_using [shape, domLength]) generator) words (by omega_using [small]) (by omega_using [large])
  (by rw [generator,modulus];have := facts.2.1;omega_using [this]) bits
  ((sameHeader sCtx (by decide) (by decide) (by decide) (by decide)).trans headers.1)
  ((sameHeader sDom (by decide) (by decide) (by decide) (by decide)).trans headers.2.1)
  ((sameHeader sLen (by decide) (by decide) (by decide) (by decide)).trans headers.2.2.2)
  controls.2.1 headerC modulus generator policy) ?_
 rintro t ⟨status,canonical,frameT,restT⟩
 exact ⟨status,canonical,((frameA.trans publicB).trans publicC).trans frameT,
  (total.trans restT).mono (by decide)⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Public inputs and staging predicates for the complete context initializer. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PolicyDomainTiming.lean`, which only this module imported.
section

/-! Checked public domains discharge all leading-zero and recognition timing premises. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Ffdh (lead)
open VG.Proof.Ffdh.KeyScalar (bnd)

structure DomainPolicyPublic where
 B : Addr
 Z : Nat
 src : Addr
 dom : List Byte
 k : Nat
 dl : Nat
 table : Addr
 room : 256≤Z
 positive : 0<k
 size : k≤1024
 shape : dl=2*k ∨ dl=3*k
 domLength : dom.length=dl
 checked : Spec.Ffdh.domainValid k dom=true

structure DomainPolicyReady (q : DomainPolicyPublic) (s : State) : Prop where
 scratch : Scr s q.B q.Z
 base : s.gpr .x0=q.B
 pointer : word s.mem q.B (8*sDom)=q.src
 length : word s.mem q.B (8*sLen)=BitVec.ofNat 64 q.k
 domainLength : word s.mem q.B (8*sDL)=BitVec.ofNat 64 q.dl
 source : Source q.src q.dom s
 outside : ∀ i<q.dom.length,8*sBits+8≤ofs q.B (q.src+BitVec.ofNat 64 i)
 records : PolicyTableAt q.B q.table Policy.groups s
 symbol : s.syms Policy.tableSym=q.table

def domainRecognize (q : DomainPolicyPublic) : RecognizePublic := by
 obtain shape : q.dom.length=2*q.k ∨ q.dom.length=3*q.k :=by have :=q.domLength;have :=q.shape;omega_arith
 have leadFacts:=checked_bound_lead q.positive shape q.checked
 exact {
  B:=q.B,Z:=q.Z,dom:=q.src,k:=q.k,dl:=q.dl,bs:=bnd q.k q.dom,L:=lead (bnd q.k q.dom),room:=q.room,
  positive:=q.positive,size:=by have :=q.size;omega_using [this],shape:=q.shape,length:=VG.Proof.Ffdh.KeyScalar.bnd_length shape,
  inside:=leadFacts.1,zeros:=leadFacts.2.1,nonzero:=leadFacts.2.2,
  domBytes:=q.dom,table:=q.table,domLength:=q.domLength,small:=by have :=q.size;omega_using [this]}

theorem domainRecognize_ready {q : DomainPolicyPublic} {s : State} (h : DomainPolicyReady q s) :
 RecognizeReady (domainRecognize q) s := by
 refine ⟨⟨h.scratch,h.base,h.pointer,h.length,h.domainLength,?_⟩,h.source,h.outside,h.records,h.symbol⟩
 change Source (if q.dl=2*q.k then q.src else off q.src (2*q.k)) (bnd q.k q.dom) s
 exact h.source.bound q.positive q.domLength q.shape

theorem policyDomain_ct : RelCT isa (Two DomainPolicyReady) Policy.recognize (fun _ _ =>True) :=
 two_map domainRecognize (fun _ _ h =>domainRecognize_ready h) policyRecognize_ct

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PrecomputeFieldTiming.lean`, which only this module imported.
section

/-! Reuse the existing public modulus-load and R-squared timing proofs. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem precomputeField_ct (M : Mont) : RelCT isa (Two PcM)
 (VG.Impl.Bignum.AArch64.seqs (pcLoadW++r2StepsPub M.mm)) (fun _ _ =>True) := by
 refine RelCT.seqs_append (by simp [pcLoadW,pcLoadWith]) (by simp [r2StepsPub]) (RelCT.seq
  (two_post (Ψ:=Pc3) (pcLoadW_ct.mono (fun _ _ h =>two_mono (fun _ _ h =>PcM.loadW h) h) (fun _ _ _ =>trivial)) ?_)
  ((pcR2_ct M).mono (fun _ _ h =>h) (fun _ _ _ =>trivial)))
 intro p s h
 have h':=h
 obtain ⟨scratch,base,room,small,large,_,length,modulus,source,nbLength,valid,_,_,span⟩:=h'
 exact WP.mono (pcLoadW_r2 scratch base room small large length modulus source span nbLength valid)
  (fun t ⟨mi,r2,frame,rest⟩ =>⟨mi,h.congr frame (fun r hr =>Nat.le_trans (pcLoadRanges_le _ r hr) room)
   (pcLoadRanges_fixed _) rest (by decide),r2⟩)

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/ArithmeticTimingState.lean`, which only this module imported.
section

/-! Public modulus setup establishes the table builder's field without assuming prior scratch contents. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure ArithmeticPublic where
 table : TablePublic
 nb : List Byte
 value : Spec.Rsa.os2ip nb=table.p.P
 odd : table.p.P%2=1

def arithmeticPc (q : ArithmeticPublic) : PcPub :=
 ⟨q.table.p.B,q.table.p.Z,q.table.p.k,q.table.p.ctx,q.table.dom,q.nb⟩

def arithmeticTable (q : ArithmeticPublic) (mi : BitVec 64) : TablePublic :=
 {q.table with p:={q.table.p with mi:=mi}}

structure ArithmeticReady (q : ArithmeticPublic) (s : State) : Prop where
 pc : PcM (arithmeticPc q) s
 space : ContextSpace q.table.p s
 generator : GeneratorSource q.table.p (q.table.dom+BitVec.ofNat 64 q.table.p.k) q.table.bs s
 rows : word s.mem q.table.p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows q.table.p.N)

def ArithmeticDone (q : ArithmeticPublic) (s : State) : Prop :=∃ mi,TableReady (arithmeticTable q mi) s

theorem arithmeticField_done (M : Mont) {q : ArithmeticPublic} {s : State} (h : ArithmeticReady q s) :
 WP isa (seqs (VG.Impl.Rsa.AArch64.pcLoadW++VG.Impl.Rsa.AArch64.r2StepsPub M.mm)) s (ArithmeticDone q) := by
 obtain ⟨scratch,base,room,small,large,ctx,len,dom,source,nbLength,valid,_,_,span⟩:=h.pc
 dsimp only [arithmeticPc,PcPub.w,PcPub.N] at *
 obtain normalized :=(valid_facts valid small).2.2
 refine WP.mono (precomputeField_ok M scratch base room (by change 9≤q.table.p.k;change 64≤q.table.p.k at small;omega_using [small])
  q.table.size len dom source span nbLength (by rw [q.value];exact q.odd) normalized) ?_
 rintro t ⟨mi,good,modulus,inverse,r2,frame,rest⟩
 obtain field : FieldInitial (arithmeticTable q mi).p t :=by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [arithmeticTable,q.table.words] using good
  · simpa only [arithmeticTable,q.table.words,q.value] using modulus
  · simpa only [arithmeticTable,q.table.words] using inverse
  · simpa only [arithmeticTable,q.table.words,q.value] using r2
 obtain inscr : InScr q.table.p.B q.table.p.Z s.mem t.mem :=by
  apply precomputeField_inscr (w:=q.table.p.w) _ q.table.p.room
  simpa only [q.table.words] using frame
 have sourceT:=h.generator.after_inscr inscr rest
 have header (i : Nat) (lo : 16≤i) (hi : i<32) (different : i≠Public.sCnt) :=precomputeField_header frame lo hi different
 exact ⟨mi,⟨field,⟨(h.space.after rest).writable,h.space.outside⟩,
  ⟨sourceT.source,sourceT.length,sourceT.value,sourceT.separate⟩,
  (header sCtx (by decide) (by decide) (by decide)).trans ctx,
  (header sDom (by decide) (by decide) (by decide)).trans dom,
  (header sLen (by decide) (by decide) (by decide)).trans len⟩,
  (header sRows (by decide) (by decide) (by decide)).trans h.rows⟩

theorem arithmeticDone_two {s t : State} (h : Two ArithmeticDone s t) : Two TableReady s t := by
 obtain ⟨q,⟨a,hs⟩,⟨b,ht⟩,sp⟩:=h
 obtain same : a=b := imported_inverse_unique (p:=q.table.p) hs.field ht.field q.odd
 subst b
 exact ⟨arithmeticTable q a,hs,ht,sp⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/ArithmeticTiming.lean`, which only this module imported.
section

/-! Compose public field setup with context serialization and the complete fixed-base table. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64

theorem precomputeArithmetic_ct (M : Mont) : RelCT isa (Two ArithmeticReady)
 (.seq (seqs (VG.Impl.Rsa.AArch64.pcLoadW++VG.Impl.Rsa.AArch64.r2StepsPub M.mm))
  (.seq Precompute.storePrefix (.seq (Precompute.table M.mm) (.block [movi .x0 1])))) (fun _ _ =>True) :=
 RelCT.seq (two_post (two_map arithmeticPc (fun _ _ h =>h.pc) (precomputeField_ct M))
  (fun _ _ h =>arithmeticField_done M h))
  ((precomputeTail_ct M).mono (fun _ _ h =>arithmeticDone_two h) (fun _ _ h =>h))

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure PrecomputePublic where
 p : Parameters
 domPtr : Addr
 dom : List Byte
 dl : Nat
 table : Addr
 words : p.w=(p.k+7)/8
 small : 64≤p.k
 large : p.k≤1024
 shape : dl=2*p.k ∨ dl=3*p.k
 domLength : dom.length=dl
 checked : Spec.Ffdh.domainValid p.k dom=true
 modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p
 generator : p.G=(Spec.Ffdh.domainOf p.k dom).g
 policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom)

theorem precomputeBits (q : PrecomputePublic) : 0<q.p.N ∧ q.p.N≤8192 :=by
 rw [q.policy]
 exact ⟨generation_bits_positive q.checked,generation_bits_bound (by have :=q.small;omega_using [this]) q.large⟩

def precomputeDomainPolicy (q : PrecomputePublic) : DomainPolicyPublic :=
 ⟨q.p.B,q.p.Z,q.domPtr,q.dom,q.p.k,q.dl,q.table,
  by have :=q.p.room;dsimp only [slot,hdrBytes] at this;omega_using [this],by have :=q.small;omega_using [this],q.large,q.shape,q.domLength,q.checked⟩

def precomputeMetadata (q : PrecomputePublic) : MetadataPublic :=
 ⟨q.p.B,q.p.Z,q.p.ctx,q.p.N,(precomputeDomainPolicy q).room,(precomputeBits q).1,(precomputeBits q).2⟩

def precomputeArithmetic (q : PrecomputePublic) : ArithmeticPublic :=by
 obtain facts :=(VG.Proof.Ffdh.domainValid_iff q.p.k q.dom).mp q.checked
 obtain reduced : q.p.G<q.p.P :=by rw [q.generator,q.modulus];have :=facts.2.1;omega_using [this]
 obtain odd : q.p.P%2=1 :=by
  have mod:=VG.Proof.Ffdh.domainValid_mod q.checked
  simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at mod
  rw [q.modulus];exact mod.1.1.1
 exact ⟨⟨⟨q.p,q.domPtr,(q.dom.drop q.p.k).take q.p.k,q.words,by have :=q.small;omega_using [this],
  by have :=q.large;omega_using [this],reduced⟩,precomputeBits q⟩,q.dom.take q.p.k,q.modulus.symm,odd⟩

structure PrecomputeReady (q : PrecomputePublic) (s : State) : Prop where
 scratch : Scr s q.p.B q.p.Z
 space : ContextSpace q.p s
 output : Scr s q.p.ctx 24
 source : PublicSource q.p q.domPtr q.dom s
 span : InRegions (s.rd++s.wr) q.domPtr q.p.k
 context : s.gpr .x0=q.p.ctx
 domain : s.gpr .x2=q.domPtr
 domainLength : s.gpr .x3=BitVec.ofNat 64 q.dl
 length : s.gpr .x4=BitVec.ofNat 64 q.p.k
 base : s.gpr .x5=q.p.B
 records : PolicyTableAt q.p.B q.table Policy.groups s
 symbol : s.syms Policy.tableSym=q.table

structure PrecomputeSetup (q : PrecomputePublic) (s : State) : Prop where
 scratch : Scr s q.p.B q.p.Z
 space : ContextSpace q.p s
 output : Scr s q.p.ctx 24
 source : PublicSource q.p q.domPtr q.dom s
 span : InRegions (s.rd++s.wr) q.domPtr q.p.k
 base : s.gpr .x0=q.p.B
 context : word s.mem q.p.B (8*sCtx)=q.p.ctx
 domain : word s.mem q.p.B (8*sDom)=q.domPtr
 domainLength : word s.mem q.p.B (8*sDL)=BitVec.ofNat 64 q.dl
 length : word s.mem q.p.B (8*sLen)=BitVec.ofNat 64 q.p.k

structure PrecomputeEntered (q : PrecomputePublic) (s : State) : Prop extends PrecomputeSetup q s where
 records : PolicyTableAt q.p.B q.table Policy.groups s
 symbol : s.syms Policy.tableSym=q.table

structure PrecomputePolicyDone (q : PrecomputePublic) (s : State) : Prop extends PrecomputeSetup q s where
 bits : word s.mem q.p.B (8*sBits)=BitVec.ofNat 64 q.p.N

theorem precomputeEntered_policy {q : PrecomputePublic} {s : State} (h : PrecomputeEntered q s) :
 DomainPolicyReady (precomputeDomainPolicy q) s :=
 ⟨h.scratch,h.base,h.domain,h.length,h.domainLength,h.source.toSource,
  fun i hi =>Nat.le_trans (by have :=q.p.room;dsimp only [slot,hdrBytes,sBits] at *;omega_using [this]) (h.source.scratchOutside i hi),h.records,h.symbol⟩

theorem precomputePolicyDone_metadata {q : PrecomputePublic} {s : State} (h : PrecomputePolicyDone q s) :
 MetadataReady (precomputeMetadata q) s :=⟨h.scratch,h.base,h.context,h.bits⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.PrecomputeSat`, which the modules that import this one used -/

section

/-! ### `Ffdh.AArch64.Cached.PrecomputeContract`, which this module and modules that import it used -/

section

/-! The reviewed initializer ABI, with its existing public constant-table convention. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Spec.Ffdh

abbrev precomputeDomain (s : State) : List Byte :=Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat

def precomputePlainPre (s : State) : Prop :=
 let ctx : Region:=⟨s.gpr .x0,(s.gpr .x1).toNat*8⟩
 let dom : Region:=⟨s.gpr .x2,(s.gpr .x3).toNat⟩
 let scr : Region:=⟨s.gpr .x5,(s.gpr .x6).toNat*8⟩
 s.rd=[dom] ∧ s.wr=[ctx,scr] ∧ ctx.Disjoint dom ∧ ctx.Disjoint scr ∧ dom.Disjoint scr ∧
 (s.gpr .x0).toNat+(s.gpr .x1).toNat*8≤2^64 ∧ (s.gpr .x2).toNat+(s.gpr .x3).toNat≤2^64 ∧
 (s.gpr .x5).toNat+(s.gpr .x6).toNat*8≤2^64 ∧
 pLenValid (s.gpr .x4).toNat ∧ domainLenValid (s.gpr .x4).toNat (s.gpr .x3).toNat ∧
 (s.gpr .x1).toNat=generationPrecomputedWords (s.gpr .x4).toNat ∧
 Spec.Rsa.scratchWords (s.gpr .x4).toNat≤(s.gpr .x6).toNat ∧
 domainValid (s.gpr .x4).toNat (precomputeDomain s)

def precomputePre (s : State) : Prop :=
 precomputePlainPre (stripConsts Policy.tableConsts s) ∧ ConstsOk Policy.tableConsts 0 s

def precomputePost (s t : State) : Prop :=
 (t.gpr .x0).setWidth 32=1#32 ∧
 generationPrecompute (s.gpr .x4).toNat (precomputeDomain s)=
  some (Spec.Rsa.wordsAt t.mem (s.gpr .x0) (s.gpr .x1).toNat)

def precomputePub (s t : State) : Prop :=
 s.sp=t.sp ∧ (precomputeDomain s).map (·.toNat)=(precomputeDomain t).map (·.toNat) ∧
 s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧ s.gpr .x2=t.gpr .x2 ∧ s.gpr .x3=t.gpr .x3 ∧
 s.gpr .x4=t.gpr .x4 ∧ s.gpr .x5=t.gpr .x5 ∧ s.gpr .x6=t.gpr .x6 ∧ s.syms Policy.tableSym=t.syms Policy.tableSym

def precomputeContract : Contract isa where
 pre:=precomputePre
 post:=precomputePost
 pub:=precomputePub

theorem precompute_shared_plain_pre {s : State} (h : (generationPrecomputeContract abi).pre s) : precomputePlainPre s :=by
 sig_pre [generationPrecomputeContract,generationPrecomputeSig,abi,argRegs,precomputePlainPre,pLenValid,domainLenValid] at h
 sig_pre [generationPrecomputeContract,generationPrecomputeSig,abi,argRegs,precomputePlainPre,pLenValid,domainLenValid] at h
 sig_split h
 sig_reduce [generationPrecomputeContract,generationPrecomputeSig,abi,argRegs,precomputePlainPre,pLenValid,domainLenValid]
 sig_and_intros
 sig_close
 all_goals with_reducible assumption

theorem precompute_shared_pre {s : State} (h : (generationPrecomputeContract (abi.withConsts Policy.tableConsts)).pre s) : precomputePre s :=by
 obtain ⟨plain,constants⟩:=pre_consts.mp h
 exact ⟨precompute_shared_plain_pre plain,constants⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! A concrete valid domain and public constant table witness the initializer ABI. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached

private def precomputeBase : State where
 gpr r:=match r with
  | .x0=>0x100000 | .x1=>275 | .x2=>0x3000 | .x3=>128 | .x4=>64 | .x5=>0x9000 | .x6=>1056 | _=>0
 sp:=0x8000
 mem:=Sat.domainMem
 rd:=[⟨0x3000,128⟩]
 wr:=[⟨0x100000,2200⟩,⟨0x9000,8448⟩]

@[irreducible] private def precomputeMem (W : List (BitVec 64)) : Mem :=fun a=>
 if (a-0x200000).toNat<17744 then constMem 0x200000 W a else Sat.domainMem a

private def precomputeSat (W : List (BitVec 64)) : State :=
 {precomputeBase with mem:=precomputeMem W,rd:=precomputeBase.rd++[⟨0x200000,17744⟩],syms:=fun _=>0x200000}

private theorem precomputeMem_held (W : List (BitVec 64)) (length : W.length=2218) (i : Nat) (hi : i<W.length) :
 (precomputeMem W).readW (0x200000+BitVec.ofNat 64 (8*i)) 64=W.getD i 0 :=by
 rw [←constMem_held 0x200000 W (by rw [length];decide) i hi]
 apply Mem.readW_congr
 intro j hj
 unfold precomputeMem
 refine ite_eq_left ?_
 rw [BitVec.add_assoc,BitVec.ofNat_add_ofNat,Offset.add_sub_cancel_left,BitVec.toNat_ofNat]
 rw [length] at hi
 omega_using [hi, hj]

private theorem precomputeSat_domain (W : List (BitVec 64)) : Spec.Rsa.bytesAt (precomputeMem W) 0x3000 128=Sat.domain :=by
 unfold Sat.domain Spec.Rsa.bytesAt
 apply List.map_congr_left
 intro i hi
 unfold precomputeMem
 apply ite_eq_right
 have small : ∀ i<128,¬((0x3000 : Addr)+BitVec.ofNat 64 i-0x200000).toNat<17744 :=by decide
 exact small i (List.mem_range.mp hi)

private theorem precomputeSat_aux (W : List (BitVec 64)) (length : W.length=2218) :
 ∃s,(Spec.Ffdh.generationPrecomputeContract (abi.withConsts [(Policy.tableSym,W)])).pre s :=by
 refine ⟨precomputeSat W,pre_consts.mpr ⟨?_,?_⟩⟩
 · sig_pre [Spec.Ffdh.generationPrecomputeContract,Spec.Ffdh.generationPrecomputeSig,Spec.Ffdh.pLenValid,
    Spec.Ffdh.domainLenValid,Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,
    Spec.Rsa.modulusWords,Spec.Rsa.scratchWords,abi,argRegs]
   repeat' apply And.intro
   all_goals first
    | rfl
    | decide +kernel
    | (apply Region.disjoint_of_sep;decide +kernel)
    | (change Spec.Ffdh.domainValid 64 (Spec.Rsa.bytesAt (precomputeMem W) 0x3000 128)=true
       rw [precomputeSat_domain W];exact Sat.domain_valid)
 · refine ⟨?_,?_,?_,?_⟩
   · simp only [precomputeSat,precomputeBase,constRegs,Abi.constRegions,List.map_cons,List.map_nil,length]
     rfl
   · intro c hc i hi
     simp only [List.mem_singleton] at hc
     subst c
     exact precomputeMem_held W length i hi
   · intro r hr
     simp only [constRegs,Abi.constRegions,List.mem_map,List.mem_singleton] at hr
     obtain ⟨c,rfl,rfl⟩:=hr
     rw [length]
     dsimp only [precomputeSat]
     refine ⟨by decide,?_,?_⟩
     · intro q hq
       change q∈([⟨0x100000,2200⟩,⟨0x9000,8448⟩] : List Region) at hq
       simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
       rcases hq with rfl|rfl
       all_goals apply Region.disjoint_of_sep;decide
     · intro q hq
       simp only [abi,stackBelow,List.not_mem_nil] at hq
   · intro r hr
     simp only [constRegs,Abi.constRegions,List.mem_map,List.mem_singleton] at hr
     obtain ⟨c,rfl,rfl⟩:=hr
     dsimp only [precomputeSat]
     decide

theorem precompute_shared_sat : ∃s,(Spec.Ffdh.generationPrecomputeContract (abi.withConsts Policy.tableConsts)).pre s :=
 precomputeSat_aux Policy.tableWords Policy.tableWords_length

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.AttemptSat`, which the modules that import this one used -/

section

/-! A real canonical public context witnesses satisfiability of the native cached ABI. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64

private def attemptBase : State where
 gpr r:=match r with
  | .x0=>0x1000 | .x1=>64 | .x2=>0x2000 | .x3=>64 | .x4=>0x3000 | .x5=>128 | .x6=>64 | .x7=>0x7000 | _=>0
 sp:=0x8000
 mem a:=if a=0x8000 then 0x40 else if a=0x8009 then 0x90 else if a=0x8010 then 0x20 else if a=0x8011 then 4
  else if a=0x801a then 0x10 else if a=0x8020 then 0x13 else if a=0x8021 then 1 else Sat.domainMem a
 rd:=[⟨0x3000,128⟩,⟨0x7000,64⟩,⟨0x100000,2200⟩,⟨0x8000,40⟩]
 wr:=[⟨0x1000,64⟩,⟨0x2000,64⟩,⟨0x9000,8448⟩]

private def attemptSat : State :={attemptBase with mem:=Sat.withContext attemptBase.mem}

private theorem attempt_arg (i : Nat) (hi : i<5) : stackArg attemptSat i=stackArg attemptBase i :=by
 apply Sat.readW_outside
 have small : ∀ i<5,(stackArgAddr attemptBase i).toNat+8≤0x100000 :=by decide
 exact small i hi

private theorem attempt_domain : Spec.Rsa.bytesAt attemptSat.mem 0x3000 128=Sat.domain :=by
 rw [show attemptSat.mem=Sat.withContext attemptBase.mem from rfl,Sat.domain_unchanged]
 unfold Sat.domain
 decide +kernel

theorem attempt_shared_sat : ∃ s,(Proof.Ffdh.cachedGenerateKeyContract abi).pre s :=by
 refine ⟨attemptSat,?_⟩
 sig_pre [Proof.Ffdh.cachedGenerateKeyContract,Proof.Ffdh.cachedGenerateKeySig,Spec.Ffdh.generateKeySig,
  Spec.Ffdh.pLenValid,Spec.Ffdh.domainLenValid,abi,argRegs]
 simp only [attempt_arg 0 (by decide),attempt_arg 1 (by decide),attempt_arg 2 (by decide),attempt_arg 3 (by decide),attempt_arg 4 (by decide)]
 have a0 : stackArg attemptBase 0=64 :=by decide
 have a1 : stackArg attemptBase 1=0x9000 :=by decide
 have a2 : stackArg attemptBase 2=1056 :=by decide
 have a3 : stackArg attemptBase 3=0x100000 :=by decide
 have a4 : stackArg attemptBase 4=275 :=by decide
 rw [a0,a1,a2,a3,a4]
 dsimp only [attemptSat,attemptBase]
 repeat' apply And.intro
 all_goals first
  | (change Spec.Ffdh.domainValid 64 (Spec.Rsa.bytesAt attemptSat.mem 0x3000 128)=true
     rw [attempt_domain];exact Sat.domain_valid)
  | (change Spec.Ffdh.generationPrecompute 64 (Spec.Rsa.bytesAt attemptSat.mem 0x3000 128)=some (Spec.Rsa.wordsAt attemptSat.mem 0x100000 275)
     rw [attempt_domain];exact (Sat.canonical _).2)
  | decide +kernel
  | (apply Region.disjoint_of_sep;decide +kernel)

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! The public initializer's entry and policy phases establish exact metadata inputs. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem precomputeEntry_ct : RelCT isa (Two PrecomputeReady) (.block Precompute.entry) (fun _ _ =>True) :=
 two_taint [.x5] (fun _ s t hs ht r hr =>by
  have eq : r= .x5 :=by simpa using hr
  subst r;exact hs.base.trans ht.base.symm) (by taint_decide)

theorem precomputeEntry_entered {q : PrecomputePublic} {s : State} (h : PrecomputeReady q s) :
 WP isa (.block Precompute.entry) s (PrecomputeEntered q) := by
 have room : 256≤q.p.Z :=(precomputeDomainPolicy q).room
 refine WP.mono_syms (precomputeEntry_ok h.scratch room h.base) ?_
 rintro t ⟨⟨base,mem⟩,rest⟩ syms
 have entry : t.mem=entryMemory s.mem q.p.B q.p.ctx q.domPtr (BitVec.ofNat 64 q.dl) (BitVec.ofNat 64 q.p.k) :=by
  rw [mem,h.context,h.domain,h.domainLength,h.length]
 have headers :=entryMemory_header s.mem q.p.B q.p.ctx q.domPtr (BitVec.ofNat 64 q.dl) (BitVec.ofNat 64 q.p.k)
 rw [←entry] at headers
 have inscr : InScr q.p.B q.p.Z s.mem t.mem :=by rw [entry];exact entryMemory_frame _ _ _ _ _ _ _ room
 have publicFrame : PublicFrame q.p s.mem t.mem :=PublicFrame.of_inscr inscr
 have range : Outside q.p.B 128 32 s.mem t.mem :=by rw [entry];exact entryMemory_range _ _ _ _ _ _
 exact ⟨⟨h.scratch.congr rest.wr,h.space.after rest,h.output.congr rest.wr,h.source.after publicFrame rest,
  by rw [rest.rd,rest.wr];exact h.span,base,headers.1,headers.2.1,headers.2.2.1,headers.2.2.2⟩,
  h.records.after_belowBits range rest (by decide),(congrFun syms Policy.tableSym).trans h.symbol⟩

theorem precomputePolicy_metadata {q : PrecomputePublic} {s : State} (h : PrecomputeEntered q s) :
 WP isa Policy.recognize s (PrecomputePolicyDone q) := by
 have room : 256≤q.p.Z :=(precomputeDomainPolicy q).room
 have records : PolicyTableAt q.p.B (s.syms Policy.tableSym) Policy.groups s :=by rw [h.symbol];exact h.records
 refine WP.mono (policyDomain_ok h.scratch room h.base (by have :=q.small;omega_using [this]) q.large q.shape q.domLength q.checked
  h.domain h.length h.domainLength h.source.toSource
  (fun i hi =>Nat.le_trans (by change 8*sBits+8≤q.p.Z;have :=room;unfold sBits;omega_using [room]) (h.source.scratchOutside i hi)) records) ?_
 rintro t ⟨bits,frame,rest⟩
 have inscr : InScr q.p.B q.p.Z s.mem t.mem :=InScr.of_outside frame (by change 8*sBits+8≤q.p.Z;have :=room;unfold sBits;omega_using [room])
 have header (i : Nat) (hi : i<32) (ne : i≠sBits) :=header_other frame (by decide) hi ne
 exact ⟨⟨h.scratch.congr rest.wr,h.space.after rest,h.output.congr rest.wr,h.source.after (PublicFrame.of_inscr inscr) rest,
  by rw [rest.rd,rest.wr];exact h.span,(rest.gpr .x0 (by simp [recordClobbers])).trans h.base,
  (header sCtx (by decide) (by decide)).trans h.context,(header sDom (by decide) (by decide)).trans h.domain,
  (header sDL (by decide) (by decide)).trans h.domainLength,(header sLen (by decide) (by decide)).trans h.length⟩,
  by rw [q.policy];exact bits⟩

end VG.Proof.Ffdh.AArch64.Cached
