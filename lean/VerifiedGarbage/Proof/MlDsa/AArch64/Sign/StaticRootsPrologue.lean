import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsEntry
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsFrame

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- The existing save prologue establishes the optimized invariant without
changing code or requiring an additional scratch region. -/
theorem rooted_prologue {p : Params} {S : Nat} {σ : State} (h3 : Ok3 p)
    (hp : (signK p S).pre σ) (hr : StaticRoots S σ) :
    WP isa (.block pro) σ fun s => RootedSt p S σ s ∧ s.gpr .x24=1 := by
  have hc := fChk_ok h3
  simp only [fChk,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨_,_,_,_,hlen⟩ := hc
  have hw : InRegions σ.wr (σ.gpr .x4+BitVec.ofNat 64 oSV) 56 := by
    refine ⟨⟨σ.gpr .x4,scrLen p⟩,?_,Offset.contains_base _ hlen (by decide)⟩
    rw [hp.2.1]
    simp
  refine WP.mono_syms (pro_ok (pro_in h3 hp)) fun s hs hy => ?_
  obtain ⟨ht,hflag,hframe⟩ := hs
  have rf := hr.forward.frame hframe (fun r hm => by
    obtain rfl := List.mem_singleton.mp hm
    exact hr.forward.apart_write hw) ht.rd ht.wr ht.sp hy
  have ri := hr.inverse.frame hframe (fun r hm => by
    obtain rfl := List.mem_singleton.mp hm
    exact hr.inverse.apart_write hw) ht.rd ht.wr ht.sp hy
  exact ⟨⟨entry_st h3 hp ht hframe,⟨rf,ri⟩⟩,hflag⟩

/-- Shared artifact preconditions enter the same optimized signing state. -/
theorem rooted_prologue_contract {p : Params} {S : Nat} {σ : State}
    (hS : 0<S) (h3 : Ok3 p)
    (hp : (signContractT p (abi.withConsts signRootConsts) S).pre σ) :
    WP isa (.block pro) σ fun s => RootedSt p S σ s ∧ s.gpr .x24=1 := by
  have h := staticRoots_entry hS hp
  exact rooted_prologue h3 h.1 h.2

end VG.Proof.MlDsa.AArch64.Sign
