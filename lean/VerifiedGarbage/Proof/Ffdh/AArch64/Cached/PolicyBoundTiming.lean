module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyBound
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyScanTiming
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

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
