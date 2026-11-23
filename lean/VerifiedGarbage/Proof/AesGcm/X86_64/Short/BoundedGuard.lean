module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.BoundedDescriptor
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Open
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Impl.AesGcm.X86_64.BoundedGather

/-! The short-record and descriptor-count guards depend only on public lengths. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather.Layout
open VG VG.X86_64 VG.X86_64.RegUpd Gather Short VG.Impl.AesGcm.X86_64.DirectGather
open VG.Impl.AesGcm.X86_64.Short (cond)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
variable {M : CtxMode} {s t u : State}

abbrev HasPair (s : State) := Cnt s=1 ∨ Cnt s=2
abbrev ShortRecord (s : State) := IsShort (NL s) (AL s).toNat (L s)
abbrev Eligible (s : State) := ShortRecord s ∧ HasPair s
abbrev Probe (s u : State) (Q : Prop) [Decidable Q] := Initial s u ∧ u.zf = some (decide ¬Q)

theorem subTest (s : State) : (stackArg s 1-1#64).toNat < (2#64).toNat ↔ HasPair s := by
  constructor
  · intro h
    have nz : (stackArg s 1).toNat ≠ 0 := cnt_ne_of h
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)] at h
    simp at h
    change (stackArg s 1).toNat=1 ∨ (stackArg s 1).toNat=2
    omega
  · rintro (one|two)
    · have w : stackArg s 1=1#64 := BitVec.eq_of_toNat_eq one
      rw [w]; decide
    · have w : stackArg s 1=2#64 := BitVec.eq_of_toNat_eq two
      rw [w]; decide

theorem testCount (p : Layout M s) (e : Initial s u) : WP isa (.block countTest) u (fun v => Probe s v (HasPair s)) := by
  obtain ⟨count,pr⟩ := p.countWord e
  by_cases accept : HasPair s
  · have b := (subTest s).2 accept
    refine WP.of_runBlock ⟨_,by unfold countTest; xrun [e.rsp,count,pr,b],?_,?_⟩
    · refine OneEntry.keep (p.oneCtx M.ge).lay e ?_ rfl rfl (Frame.refl _ _)
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    · simp [accept,gpr_setReg]
  · have b : ¬(stackArg s 1-1#64).toNat < (2#64).toNat := fun h => accept ((subTest s).1 h)
    refine WP.of_runBlock ⟨_,by unfold countTest; xrun [e.rsp,count,pr,b],?_,?_⟩
    · refine OneEntry.keep (p.oneCtx M.ge).lay e ?_ rfl rfl (Frame.refl _ _)
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    · simp [accept,gpr_setReg]

theorem testShort (p : Layout M s) (e : Initial s u) : WP isa cond u fun v => Probe s v (ShortRecord s) :=
  WP.mono (condE_ok (p.oneCtx M.ge) e rfl rfl) fun _ h => ⟨h.2.1,h.1⟩

abbrev probeCode : Prog isa := .seq cond (.ite .e (.block []) (.block countTest))

theorem testBoth (p : Layout M s) (e : Initial s u) : WP isa probeCode u fun v => Probe s v (Eligible s) := by
  refine WP.seq (WP.mono (p.testShort e) fun v hp => WP.ite (decide ¬ShortRecord s)
    (by simp only [eval,hp.2]) (fun long => ?_) (fun short => ?_))
  · have n := of_decide_eq_true long
    exact WP.block_nil ⟨hp.1,by simpa [Eligible,n] using hp.2⟩
  · have sh := Classical.not_not.mp (of_decide_eq_false short)
    exact WP.mono (p.testCount hp.1) fun _ h => ⟨h.1,by simpa [Eligible,sh] using h.2⟩

theorem pubShort (pb : Pub s t) : ShortRecord t ↔ ShortRecord s := by
  simp only [ShortRecord,NL,AL,pb.rcx,pb.r9,pb.eL]

theorem pubEligible (pb : Pub s t) : Eligible t ↔ Eligible s := by
  simp only [Eligible,pubShort pb,HasPair,pb.cnt]

theorem testBoth_rel (p : Layout M s) (q : Layout M t) (pb : Pub s t) :
    RelCT isa (fun a b => Initial s a ∧ Initial t b) probeCode fun _ _ => True := by
  have ct := cond_rel (fun _ (h : Initial s _) => condS_of (nl:=NL s) (al:=(AL s).toNat) h rfl rfl)
    (fun _ (h : Initial t _) => by
      simpa only [NL,AL,pb.rcx,pb.r9,pb.eL,pb.w] using (condS_of (nl:=NL t) (al:=(AL t).toNat) h rfl rfl))
    (s.gpr .rcx).isLt (AL s).isLt (stackArg s 3).isLt
  refine RelCT.seq (rel_next ct (fun _ h => p.testShort h) (fun _ h => q.testShort h))
    (rel_ite_e (fun _ _ h => by simp only [h.1.2,h.2.2,pubShort pb]) (rel_taint [] (by simp) ⟨_,by taint_decide⟩)
      (rel_taint [.rsp] (fun _ _ h r hr => by
        rw [List.mem_singleton.mp hr,h.1.1.1.rsp,h.1.2.1.rsp]; exact pb.rsp.symm) ⟨_,by taint_decide⟩))

end VG.Proof.AesGcm.X86_64.DirectGather.Layout
