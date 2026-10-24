module

public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Restore
public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Fallback
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Facts

/-! Recognized domains satisfy the original contract; every miss uses its original validator. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero)

private theorem abi_trans {s t u : State} (a : abiPreserved s t) (b : abiPreserved t u) : abiPreserved s u :=
  ⟨fun r hr =>(b.1 r hr).trans (a.1 r hr),b.2.1.trans a.2.1,
    fun r hr =>(b.2.2 r hr).trans (a.2.2 r hr)⟩

theorem result_eval {s t : State} (h : Result s t) :
    isa.eval (.nonzero .x .x10) t=some (decide (width s≠4095)) := by
  rw [eval_nonzero,h.test]
  change some (!(BitVec.ofNat 64 (width s)-BitVec.ofNat 64 4095==0#64))=_
  rw [Cached.sub_zero_iff (by have :=width_le s;omega) (by decide)]
  simp

theorem correct (W : Window) (M : Mont) (S : Selector) {s : State} (hs : pre s) :
    WP isa (VG.Impl.Ffdh.AArch64.VettedValidation.code W.code S.code M.mm) s
      (fun t =>abiPreserved s t ∧ CheckDomain.cdPost s t) := by
  have g:=geometry hs
  unfold VG.Impl.Ffdh.AArch64.VettedValidation.code
  rw [WP.seq_iff]
  refine WP.mono (recognize_ok g) ?_
  intro t h
  by_cases hit : width s≠4095
  · refine WP.ite true (by rw [result_eval h,decide_eq_true hit]) (fun _ =>?_) (fun bad =>Bool.noConfusion bad)
    have valid : Spec.Ffdh.domainValid (s.gpr .x2).toNat (CheckDomain.cdDom s)=true :=
      VG.Proof.Ffdh.AArch64.VettedValidation.policyWidth_valid (fun _ hg =>hg)
        (by simpa only [CheckDomain.cdDom,Spec.Rsa.bytesAt,List.length_map,List.length_range] using g.shape) hit
    refine WP.mono (WP.keep [.x0] (Q:=fun u =>u.gpr .x0=1#64) ?_ rfl rfl rfl) ?_
    · brun []
    · rintro u ⟨value,rest⟩
      have keep :=(h.keep.trans rest).mono (rs':=clobbers) (by
        intro r hr
        rcases List.mem_append.mp hr with hr|hr
        · exact hr
        · have eq : r= .x0 := by simpa using hr
          subst r
          decide)
      refine ⟨⟨fun r hr =>keep.gpr r (by revert r;decide),keep.sp,keep.vcs⟩,?_⟩
      unfold CheckDomain.cdPost
      rw [value,valid]
      rfl
  · refine WP.ite false (by rw [result_eval h,decide_eq_false hit]) (fun bad =>Bool.noConfusion bad) (fun _ =>?_)
    rw [WP.seq_iff]
    refine WP.mono (restore_ok g h) ?_
    intro u hu
    obtain ⟨trace,v,run,preserved,post⟩:=fallback_run W M S (hu.pre hs)
    refine ⟨trace,v,run,abi_trans hu.abi preserved,?_⟩
    unfold CheckDomain.cdPost at post ⊢
    rw [hu.args.2.2.1,hu.domain] at post
    exact post

end VG.Proof.Ffdh.AArch64.VettedValidation
