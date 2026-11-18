module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyBoundTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyLoopTiming
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyBound
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyLoop
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

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
