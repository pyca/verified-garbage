import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedEntryAccess
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlDsa.AArch64.Round

structure WordPublic (s t : State) : Prop where
  sp : s.sp=t.sp
  args : ∀r∈([.x0,.x1,.x2,.x3,.x4] : List Reg),s.gpr r=t.gpr r
  gamma : (s.gpr .x5).setWidth 32=(t.gpr .x5).setWidth 32
  table : s.syms "VG_MLDSA_INV_PAIR"=t.syms "VG_MLDSA_INV_PAIR"

def bodyPublicRegs : List Reg := [.x0,.x1,.x13,.x14,.x15,.x16]

structure BodyPublic (s t : State) : Prop where
  sp : s.sp=t.sp
  regs : ∀r∈bodyPublicRegs,s.gpr r=t.gpr r
  gamma : (s.gpr .x17).setWidth 32=(t.gpr .x17).setWidth 32

theorem body_word_ct : ConstantTime isa (fun _ => True) BodyPublic
    (VG.Impl.MlDsa.AArch64.Round.zext .x17
      (VG.Impl.MlDsa.AArch64.Round.onGamma .x17 .x7 kernelPaired)) := by
  apply zext_ct (τ := Taint.ofRegs (.x17::bodyPublicRegs)) ?_ (by taint_decide)
  intro s t hp
  have h := agree_zext (gr := .x17) (rs := bodyPublicRegs) hp.sp hp.gamma hp.regs
  exact ⟨h.1,fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩

theorem prolog_ct : ConstantTime isa (fun _ => True)
    (Taint.AgreeS ["VG_MLDSA_INV_PAIR"] (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4])) (.block pro) :=
  VG.Taint.constantTime (A := taintS ["VG_MLDSA_INV_PAIR"])
    (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4]) (fun _ _ _ _ h => h) (by taint_decide)

/-- Only the low32 bits of gamma are public under the u32 ABI. -/
theorem r0_word_ct : ConstantTime isa EntryAccess WordPublic (selected .r0) := by
  intro s t tr₁ tr₂ s' t' hs ht hp he₁ he₂
  change Exec isa (.seq (.block pro) _) s tr₁ s' at he₁
  change Exec isa (.seq (.block pro) _) t tr₂ t' at he₂
  cases he₁ with
  | seq e₁ f₁ =>
    cases he₂ with
    | seq e₂ f₂ =>
      obtain ⟨_,a,ea,hka,arga,ta,_,_,_⟩ := prolog_ok s hs.save
      obtain ⟨_,b,eb,hkb,argb,tb,_,_,_⟩ := prolog_ok t ht.save
      obtain ⟨_,hstate₁⟩ := Exec.det e₁ ea
      rw [hstate₁] at f₁
      obtain ⟨_,hstate₂⟩ := Exec.det e₂ eb
      rw [hstate₂] at f₂
      have hp₁ := prolog_ct _ _ _ _ _ _ trivial trivial
        (show Taint.AgreeS ["VG_MLDSA_INV_PAIR"] (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4]) s t from
          ⟨VG.Proof.MlKem.AArch64.agree_of hp.sp hp.args,by
            intro name hn
            have he : name="VG_MLDSA_INV_PAIR" := by simpa only [List.mem_singleton] using hn
            subst name; exact hp.table⟩) e₁ e₂
      have hbody : BodyPublic a b := by
        refine ⟨hka.sp.trans (hp.sp.trans hkb.sp.symm),?_,?_⟩
        · intro r hr
          simp only [bodyPublicRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
          · rw [arga.work,argb.work]; exact hp.args .x4 (by decide)
          · rw [ta,tb]; exact hp.table
          · rw [arga.common,argb.common]; exact hp.args .x0 (by decide)
          · rw [arga.secret,argb.secret]; exact hp.args .x1 (by decide)
          · rw [arga.data,argb.data]; exact hp.args .x2 (by decide)
          · rw [arga.aux,argb.aux]; exact hp.args .x3 (by decide)
        · rw [arga.gamma,argb.gamma]; exact hp.gamma
      have hp₂ := body_word_ct _ _ _ _ _ _ trivial trivial hbody f₁ f₂
      rw [hp₁,hp₂]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
