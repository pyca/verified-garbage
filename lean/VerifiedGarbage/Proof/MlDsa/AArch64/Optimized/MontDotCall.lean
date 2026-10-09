import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.MontDot (dot)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem callee (S : Nat) {count : Nat} (hc : count=4∨count=5∨count=7) : CalleeOk S (dot count) (montDotContract abi count) :=
  ⟨(verified hc).1,(verified hc).2.1,Nat.zero_le _⟩

abbrev args (out a b : Ptr) : List (Reg × Arg) :=
  [(.x0,.ptr out),(.x1,.ptr a),(.x2,.ptr b)]

def family (p : Addr) (n : Nat) : Region := ⟨p,1024*n⟩

structure Ready (count : Nat) (out a b : Ptr) (s : State) : Prop where
  outFit : (pa s out).toNat+1024≤2^64
  aFit : (pa s a).toNat+1024*count≤2^64
  bFit : (pa s b).toNat+1024*count≤2^64
  outA : (polyRegion (pa s out)).Disjoint (family (pa s a) count)
  outB : (polyRegion (pa s out)).Disjoint (family (pa s b) count)
  positiveA : ∀j<count,PositiveReduced s.mem (pa s a+BitVec.ofNat 64 (1024*j))
  positiveB : ∀j<count,PositiveReduced s.mem (pa s b+BitVec.ofNat 64 (1024*j))
  readable : Covers [family (pa s a) count,family (pa s b) count,polyRegion (pa s out)] (s.rd++s.wr)
  writable : Covers [polyRegion (pa s out)] s.wr

theorem at_pre {s s1 : State} {count : Nat} {out a b : Ptr}
    (h : Ready count out a b s) (h1 : Args (args out a b) s s1) :
    (montDotContract abi count).pre
      (s1.callEntry.withRegions [family (pa s a) count,family (pa s b) count] [polyRegion (pa s out)]) := by
  sig_pre [montProductContract,montDotSig,abi,argRegs]
  simp only [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1,Arg.val]
  have he : 256*count*4=1024*count := by omega
  rw [he]
  exact ⟨rfl,trivial,h.outA,h.outB,h.outFit,h.aFit,h.bFit,h.positiveA,h.positiveB⟩

theorem args_ok {out a b : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) :
    ∀x∈args out a b,x.2.Ok ∧ x.1∈argRegs := by
  simp only [args,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨ho,by simp⟩
  · exact ⟨ha,by simp⟩
  · exact ⟨hb,by simp⟩

theorem at_ok {S : Nat} (hS : S<2^64) {count : Nat} (hc : count=4∨count=5∨count=7) {nm : String} {s : State} {out a b : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok)
    (h : Ready count out a b s) :
    WP isa (callAt nm (dot count) (args out a b)) s fun t =>
      Post S s t [polyRegion (pa s out)] ∧
      PolyIs t.mem (pa s out) ((dotNTT (fun j=>polyAt s.mem (pa s a+BitVec.ofNat 64 (1024*j)))
        (fun j=>polyAt s.mem (pa s b+BitVec.ofNat 64 (1024*j))) count).map (·*montgomeryRInv)) := by
  refine WP.mono (callAtSyms_ok hS (callee S hc) (args_ok ho ha hb) (by simp)
    (fun s1 h1 _=>at_pre h h1) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  sig_post [montProductContract,montDotSig,abi,argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1] at hq
  exact hq
end VG.Proof.MlDsa.AArch64.Optimized.MontDot
