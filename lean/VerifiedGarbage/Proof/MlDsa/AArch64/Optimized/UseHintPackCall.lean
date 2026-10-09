import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.UseHintPack (prog)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem callee (S : Nat) {g : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g) : CalleeOk S prog (useHintPackContract g abi) :=
  ⟨(pack_verified hg).1,(pack_verified hg).2.1,Nat.zero_le _⟩

abbrev args (out a b : Ptr) (g : Nat) : List (Reg × Arg) :=
  [(.x0,.ptr out),(.x1,.ptr a),(.x2,.ptr b),(.x3,.imm g)]

abbrev packLen (g : Nat) := 32*bitlen ((q-1)/(2*g)-1)

structure CallReady (out a b : Ptr) (g : Nat) (s : State) : Prop where
  outFit : (pa s out).toNat+packLen g≤2^64
  aFit : (pa s a).toNat+1024≤2^64
  bFit : (pa s b).toNat+1024≤2^64
  outA : (⟨pa s out,packLen g⟩ : Region).Disjoint (polyRegion (pa s a))
  outB : (⟨pa s out,packLen g⟩ : Region).Disjoint (polyRegion (pa s b))
  gamma : VG.Proof.MlDsa.AArch64.Round.IsG g
  canonical : Reduced s.mem (pa s b)
  readable : Covers [polyRegion (pa s a),polyRegion (pa s b),⟨pa s out,packLen g⟩] (s.rd++s.wr)
  writable : Covers [⟨pa s out,packLen g⟩] s.wr

theorem at_pre {s s1 : State} {out a b : Ptr} {g : Nat}
    (h : CallReady out a b g s) (h1 : Args (args out a b g) s s1) :
    (useHintPackContract g abi).pre
      (s1.callEntry.withRegions [polyRegion (pa s a),polyRegion (pa s b)] [⟨pa s out,packLen g⟩]) := by
  sig_pre [useHintPackContract,useHintPackSig,abi,argRegs]
  simp only [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,Args.mem h1,Arg.val]
  have hg : ((BitVec.ofNat 64 g).setWidth 32).toNat=g := by
    rcases h.gamma with rfl|rfl <;> decide
  rw [hg]
  exact ⟨trivial,trivial,h.outA,h.outB,h.outFit,h.aFit,h.bFit,rfl,
    VG.Proof.MlDsa.AArch64.Round.mem_of_isG h.gamma,h.canonical⟩

theorem args_ok {out a b : Ptr} {g : Nat}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) :
    ∀x∈args out a b g,x.2.Ok ∧ x.1∈argRegs := by
  simp only [args,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨ho,by simp⟩
  · exact ⟨ha,by simp⟩
  · exact ⟨hb,by simp⟩
  · exact ⟨trivial,by simp⟩

theorem at_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State} {out a b : Ptr} {g : Nat}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok)
    (h : CallReady out a b g s) :
    WP isa (callAt nm prog (args out a b g)) s fun t =>
      VG.Proof.MlDsa.AArch64.Post S s t [⟨pa s out,packLen g⟩] ∧
      Spec.Sha3.bytesAt t.mem (pa s out) (packLen g)=
        simpleBitPack (Vector.zipWith (fun hj wj=>(useHint g hj wj).toNat)
          ((hintAt s.mem (pa s a) 1).headD (Vector.replicate n false)) (polyAt s.mem (pa s b)))
          ((q-1)/(2*g)-1) := by
  refine WP.mono (callAtSyms_ok hS (callee S h.gamma) (args_ok ho ha hb) (by simp)
    (fun s1 h1 _=>at_pre h h1) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  sig_post [useHintPackContract,useHintPackSig,abi,argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1] at hq
  exact hq
end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
