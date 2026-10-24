module

public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Verified
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Correct
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
import VerifiedGarbage.Proof.Framework.Covers

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
