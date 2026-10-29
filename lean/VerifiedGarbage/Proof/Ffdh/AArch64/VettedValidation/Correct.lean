module

public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Recognize
public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Contract

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Correct
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Facts
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyTable
import VerifiedGarbage.Impl.Ffdh.VettedGroups
/-! Recognized domains satisfy the original contract; every miss uses its original validator. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/VettedValidation/Restore.lean`, which only this module imported.
section

/-! A recognition miss restores exactly the original general-validator arguments. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure Restored (s t : State) : Prop where
  args : t.gpr .x0=s.gpr .x0 ∧ t.gpr .x1=s.gpr .x1 ∧ t.gpr .x2=s.gpr .x2 ∧
    t.gpr .x3=s.gpr .x3 ∧ t.gpr .x4=s.gpr .x4
  domain : CheckDomain.cdDom t=CheckDomain.cdDom s
  keep : Keep clobbers s t

theorem restore_ok {s t : State} (g : Geometry s) (h : Result s t) :
    WP isa (.block VG.Impl.Ffdh.AArch64.VettedValidation.restore) t (Restored s) := by
  refine WP.mono (WP.keep [.x0,.x1,.x2,.x3,.x4] (Q:=fun u =>
    (u.gpr .x0=s.gpr .x0 ∧ u.gpr .x1=s.gpr .x1 ∧ u.gpr .x2=s.gpr .x2 ∧
     u.gpr .x3=s.gpr .x3 ∧ u.gpr .x4=s.gpr .x4) ∧ u.mem=t.mem) ?_ rfl rfl rfl) ?_
  · unfold VG.Impl.Ffdh.AArch64.VettedValidation.restore
    brun [h.base,hdr_enc (show sDom<32 by decide),hdr_enc (show sDL<32 by decide),
      hdr_enc (show sLen<32 by decide),hdr_enc (show sCtx<32 by decide),
      (g.scratch.congr h.keep.wr).ld (d:=8*sDom) (by unfold sDom;have :=g.room;omega),
      (g.scratch.congr h.keep.wr).ld (d:=8*sDL) (by unfold sDL;have :=g.room;omega),
      (g.scratch.congr h.keep.wr).ld (d:=8*sLen) (by unfold sLen;have :=g.room;omega),
      (g.scratch.congr h.keep.wr).ld (d:=8*sCtx) (by unfold sCtx;have :=g.room;omega),
      h.savedDomain,h.savedLength,h.savedKeyLength,h.savedWords]
  · rintro u ⟨⟨args,mem⟩,rest⟩
    refine ⟨args,?_,(h.keep.trans rest).mono (by
      intro r hr
      rcases List.mem_append.mp hr with hr|hr
      · exact hr
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)⟩
    unfold CheckDomain.cdDom
    rw [args.1,args.2.1,mem]
    unfold Spec.Rsa.bytesAt
    apply List.map_congr_left
    intro i hi
    exact h.frame _ (Or.inr (g.outside i (by simpa only [CheckDomain.cdDom,Spec.Rsa.bytesAt,List.length_map,List.length_range] using List.mem_range.mp hi)))

theorem Restored.pre {s t : State} (h : Restored s t) (hs : pre s) : CheckDomain.cdPre (plain t) := by
  obtain ⟨hp,_⟩:=hs
  simp only [CheckDomain.cdPre,stripConsts_gpr,stripConsts_wr] at hp ⊢
  rw [h.args.1,h.args.2.1,h.args.2.2.1,h.args.2.2.2.1,h.args.2.2.2.2]
  change t.rd.take (t.rd.length-Policy.tableConsts.length)=_ ∧ _
  rw [h.keep.rd,h.keep.wr]
  exact hp

theorem Restored.abi {s t : State} (h : Restored s t) : abiPreserved s t :=
  ⟨fun r hr =>h.keep.gpr r (by revert r;decide),h.keep.sp,h.keep.vcs⟩

end VG.Proof.Ffdh.AArch64.VettedValidation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/CheckDomain/Verified.lean`, which only this module imported.
section

/-!
# `vg_ffdh_check_domain` on AArch64: verified

Correct (`cd_correct`) and constant time (`cd_constantTime`) against
`cdContract`, which the shared contract implies (`cd_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckDomain

open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive

theorem cd_verified (W : Window) (M : Mont) (S : Selector) :
    Verified target (VG.Impl.Ffdh.AArch64.Domain.CheckDomain.code W.code S.code M.mm)
      (Spec.Ffdh.checkDomainContract abi) :=
  Verified.of_correct (cd_correct W M S) (cd_constantTime W M S) cd_implies

end VG.Proof.Ffdh.AArch64.CheckDomain
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/VettedValidation/Fallback.lean`, which only this module imported.
section

/-! Extra read-only recognition constants do not change the general validator's behavior. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open CheckDomain VG.Proof.Bignum.AArch64.WindowFive

theorem plain_covers (s : State) : Covers ((plain s).rd++(plain s).wr) (s.rd++s.wr) :=
  (Covers.of_mem (fun _ h =>List.mem_of_mem_take h)).append (Covers.refl _)

theorem fallback_run (W : Window) (M : Mont) (S : Selector) {s : State} (h : cdPre (plain s)) :
    ∃ trace t, Exec isa (VG.Impl.Ffdh.AArch64.Domain.CheckDomain.code W.code S.code M.mm) s trace t ∧
      abiPreserved s t ∧ cdPost s t := by
  obtain ⟨trace,t,run,abi,post⟩:=cd_correct W M S (plain s) h
  have wide:=VG.AArch64.Exec.widen run (rd:=s.rd) (wr:=s.wr) (plain_covers s) (Covers.refl _)
  refine ⟨trace,t.withRegions s.rd s.wr,?_,abi,post⟩
  simpa only [plain,stripConsts,State.withRegions_withRegions,State.withRegions_self] using wide

theorem fallback_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (fun s t =>cdPre (plain s) ∧ cdPre (plain t) ∧ cdPub s t)
      (VG.Impl.Ffdh.AArch64.Domain.CheckDomain.code W.code S.code M.mm) (fun _ _ =>True) := by
  intro s t ts tt u v ⟨hs,ht,hp⟩ es et
  obtain ⟨ts',u',eu,au,pu⟩:=cd_correct W M S (plain s) hs
  obtain ⟨tt',v',ev,av,pv⟩:=cd_correct W M S (plain t) ht
  have eus:=VG.AArch64.Exec.widen eu (rd:=s.rd) (wr:=s.wr) (plain_covers s) (Covers.refl _)
  have evt:=VG.AArch64.Exec.widen ev (rd:=t.rd) (wr:=t.wr) (plain_covers t) (Covers.refl _)
  have eus' : Exec isa (VG.Impl.Ffdh.AArch64.Domain.CheckDomain.code W.code S.code M.mm)
      s ts' (u'.withRegions s.rd s.wr) := by
    simpa only [plain,stripConsts,State.withRegions_withRegions,State.withRegions_self] using eus
  have evt' : Exec isa (VG.Impl.Ffdh.AArch64.Domain.CheckDomain.code W.code S.code M.mm)
      t tt' (v'.withRegions t.rd t.wr) := by
    simpa only [plain,stripConsts,State.withRegions_withRegions,State.withRegions_self] using evt
  have sameS:ts=ts':=(Exec.det es eus').1
  have sameT:tt=tt':=(Exec.det et evt').1
  refine ⟨?_,True.intro⟩
  rw [sameS,sameT]
  exact cd_constantTime W M S _ _ _ _ _ _ hs ht hp eu ev

end VG.Proof.Ffdh.AArch64.VettedValidation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/VettedValidation/Facts.lean`, which only this module imported.
section

/-! The AArch64 cap sentinel is non-default only for an algebraically valid domain. -/
section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG
open VG.Impl.Ffdh.AArch64.Cached

theorem policyWidth_valid {gs : List Policy.Group} (members : ∀ g∈gs,g∈Policy.groups)
    {k : Nat} {dom : List Byte} (shape : dom.length=2*k ∨ dom.length=3*k)
    (hit : VG.Proof.Ffdh.AArch64.Cached.policyWidth 4095 k dom gs≠4095) : Spec.Ffdh.domainValid k dom=true := by
  induction gs with
  | nil => exact False.elim (hit rfl)
  | cons g gs ih =>
    unfold VG.Proof.Ffdh.AArch64.Cached.policyWidth at hit
    by_cases same : k=g.len ∧ dom=g.domain.take dom.length
    · exact VG.Proof.Ffdh.VettedValidation.matched_domain_valid (members g (by simp)) shape same
    · rw [ite_eq_right same] at hit
      exact ih (fun a h =>members a (by simp [h])) hit

end VG.Proof.Ffdh.AArch64.VettedValidation
end

end

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
