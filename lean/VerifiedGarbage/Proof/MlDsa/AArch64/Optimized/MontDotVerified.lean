import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotContract

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.MontDot (dot)

def sat (n : Nat) : State where
  gpr r := if r=.x0 then 4096 else if r=.x1 then 16384 else if r=.x2 then 32768 else 0
  sp := 131072
  mem := fun _=>0
  rd := [⟨16384,1024*n⟩,⟨32768,1024*n⟩]
  wr := [⟨4096,1024⟩]

theorem sat_pre {n : Nat} (hn : n≤7) : (montDotContract abi n).pre (sat n) := by
  sig_pre [montDotContract,montDotSig,abi,argRegs,stackBelow,sat]
  have he : 256*n*4=1024*n := by omega
  rw [he]
  refine ⟨rfl,?_,?_,by decide,?_,?_,?_,?_⟩
  · exact Region.disjoint_of_sep (by simp [Region.sep];omega)
  · exact Region.disjoint_of_sep (by simp [Region.sep];omega)
  · simp;omega
  · simp;omega
  all_goals intro j hj i hi; simp [coeffAt,Mem.readW,Mem.read,VG.Spec.MlDsa.q]

theorem pub {n : Nat} {s t : State} (h : (montDotContract abi n).pub s t) : (contract n).pub s t := by
  sig_pub [montDotContract,montDotSig,abi,argRegs] at h
  refine ⟨?_,h.1⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem ct {n : Nat} (hc : n=4∨n=5∨n=7) : ConstantTime isa (contract n).pre (contract n).pub (dot n) := by
  rcases hc with rfl|rfl|rfl
  all_goals
    exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x1,.x2])
      (fun _ _ _ _ h=>VG.Proof.MlKem.AArch64.agree_of h.2 h.1) (by taint_decide)

theorem verified {n : Nat} (hc : n=4∨n=5∨n=7) : Verified target (dot n) (montDotContract abi n) := by
  refine Verified.of_correct (correct hc) (ct hc)
    {pre:=fun _ h=>pre (by omega) h,post:=?_,pub:=fun _ _ _ _ h=>pub h,sat:=⟨sat n,sat_pre (by omega)⟩}
  intro s t _ h
  sig_post [montDotContract,montDotSig,abi,argRegs]
  exact h
end VG.Proof.MlDsa.AArch64.Optimized.MontDot
