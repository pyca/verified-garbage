module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyRecognize
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyBoundTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyLoopTiming
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Omega

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
   by have :=q.domLength;have :=q.shape;omega,q.positive,q.small⟩,
  Policy.groups.tail,initialPolicyWidth q,
  by have :=byteBits (q.bs.getD q.L 0);have :=q.inside;have :=q.size;have :=q.length;unfold initialPolicyWidth;omega,
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
