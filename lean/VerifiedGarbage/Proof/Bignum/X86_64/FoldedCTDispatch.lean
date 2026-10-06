import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTCode
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedChecked

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.MlKem.X86_64

theorem test_same (s : State) :
    WP isa (.block [.alu .cmp .r11 (.imm 65537)]) s fun t =>
      Same s t ∧ t.zf = some (s.gpr .r11 - BitVec.signExtend 64 (65537 : BitVec 32) == 0) := by
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.mem = s.mem ∧
    t.zf = some (s.gpr .r11 - BitVec.signExtend 64 (65537 : BitVec 32) == 0))
    (by xrun) rfl) fun t ⟨⟨hm,hz⟩,hk⟩ => ⟨Same.of_keep (hk.mono (by simp)) hm,hz⟩

theorem dispatch_ct (M : Mont)
    (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) :
    ConstantTime isa pdContract.pre
      (fun s t => pdContract.pub s t ∧ s.gpr .r11 = t.gpr .r11) (Folded.dispatch M.mm) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold Folded.dispatch
  have headCT := (RelCT.taint (A := taint) (c := .block [.alu .cmp .r11 (.imm 65537)]) (Taint.ofRegs [.r11])
    (P := fun s t => pdContract.pre s ∧ pdContract.pre t ∧
      pdContract.pub s t ∧ s.gpr .r11 = t.gpr .r11)
    (fun s t h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact h.2.2.2)
    (by taint_decide)).wpDep
    (F := fun (s t : State) => Same s t ∧
      t.zf = some (s.gpr .r11 - BitVec.signExtend 64 (65537 : BitVec 32) == 0))
    (fun s t _ => ⟨test_same s,test_same t⟩)
  refine RelCT.seq headCT (RelCT.ite ?_ ?_ ?_)
  · rintro a b ⟨_,s,t,h,⟨_,za⟩,⟨_,zb⟩⟩
    simp only [eval,za,zb,h.2.2.2]
  · refine (relCT_of_ct (code_constantTime M hfinal)).mono ?_ (fun _ _ _ => trivial)
    rintro a b ⟨⟨_,s,t,⟨ps,pt,pub,_⟩,⟨sa,_⟩,⟨sb,_⟩⟩,_⟩
    exact ⟨(pdPre_same sa).symm ▸ ps,(pdPre_same sb).symm ▸ pt,pdPub_same sa sb pub⟩
  · refine (relCT_of_ct (pdCode_constantTime (M := M))).mono ?_ (fun _ _ _ => trivial)
    rintro a b ⟨⟨_,s,t,⟨ps,pt,pub,_⟩,⟨sa,_⟩,⟨sb,_⟩⟩,_⟩
    exact ⟨(pdPre_same sa).symm ▸ ps,(pdPre_same sb).symm ▸ pt,pdPub_same sa sb pub⟩

end VG.Proof.Bignum.X86_64.FoldedPublic
