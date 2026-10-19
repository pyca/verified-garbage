module
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Stages

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.R2CT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Body
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Stages
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.R2CT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Body
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH public-key validation on x86-64: constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh VG.Proof.MlKem.X86_64

private theorem pins_nil {α : Type} (Φ : α → State → Prop) : Pins Φ [] :=
  fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

private theorem rangeXm_ct : RelCT isa (Two GoodW1) (seqs (rangeTest aXm)) fun _ _ => True := by
  unfold rangeTest
  refine RelCT.seqs_append (by simp [range, gt1, ltArr, cmpArr]) (by simp)
    (RelCT.seq (R := Two fun (_ : Unit) (_ : State) => True)
      ((range_ct (a := aXm) (by decide) (by decide) (by taint_decide) (by taint_decide)
        (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => ⟨(), trivial, trivial⟩)) ?_)
  exact two_taint [] (pins_nil _) (by taint_decide)

private theorem main_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckPublic.main M.mm E.code (.seq (.block r2Head) R.code) =
      seqs ((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++
        (Crt.loadArr aXm sY sK ++ (rangeTest aXm ++
          ([.ite .e (retInner 0) (.seq (.block (leave :: qTest))
            (.ite .e (VG.Impl.Ffdh.X86_64.Domain.ret 1)
              (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.subgroup M.mm E.code (.seq (.block r2Head) R.code)))))] : List (Prog isa))))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckPublic.main, List.append_assoc]

private theorem subgroup_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckPublic.subgroup M.mm E.code (.seq (.block r2Head) R.code) =
      scan sQ ++ (.block [enter] :: (.seq (.block r2Head) R.code ::
        (pow M.mm E.code sY sK sEp sEl ++ (isOne aY ++ ([.block [leave]] : List (Prog isa)))))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckPublic.subgroup, List.append_assoc, List.cons_append, List.nil_append]

theorem subgroup_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    RelCT isa (Two fun p s => C4 p s ∧ isa.eval .e s = some false)
      (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.subgroup M.mm E.code (.seq (.block r2Head) R.code)))
      fun _ _ => True := by
  rw [subgroup_eq]
  refine RelCT.seqs_append (by simp [scan]) (by simp) (RelCT.seq (R := Two C5)
    (two_post (two_map CpP.qs (fun p s h => c4_scan p s h.1 h.2)
      (scan_ct (by taint_decide) (by taint_decide))) (fun p s h => c4_c5 p s h.1 h.2)) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two C6)
    (two_piece [.rdi] (pins_rdiB CpP.B fun _ _ h => c5_x0 h) (by taint_decide) c5_c6) ?_)
  refine seqs_cons_ct (by simp [pow]) (RelCT.seq (R := Two C7)
    (two_post (c6_r2_ct M R) (c6_c7 M R)) ?_)
  refine RelCT.seqs_append (by simp [pow]) (by simp [isOne, eqArr]) (RelCT.seq (R := Two C8)
    (two_post (two_map CpP.pw c7_ps0
      (pow_ct M E (loadArr_ct (by decide) (by taint_decide) (by taint_decide)) hE
        (by taint_decide) (by taint_decide) (by taint_decide))) (c7_c8 M E)) ?_)
  refine RelCT.seqs_append (by simp [isOne, eqArr]) (by simp) (RelCT.seq (R := Two C8)
    (two_post (two_map CpP.ws (fun _ _ h => h.1) (eqArr_ct (by decide) (by decide) (by taint_decide)))
      fun p s h => ?_) ?_)
  · obtain ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ := h
    exact WP.mono (eqArr_ok hg hZ hw hw' (show aY < 8 by decide) (show aOne < 8 by decide))
      fun t ⟨_, hm, k⟩ => GoodW1.keep ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ hm (k.gpr (by decide)) k.2.2
  exact two_map CpP.ws (fun _ _ h => h) (two_taint [.rdi] pins_goodW1 (by taint_decide))

theorem main_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    RelCT isa (Two fun p s => CE p s ∧ isa.eval .ne s = some false)
      (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.main M.mm E.code (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp [pSetup]) (by simp [Crt.loadArr]) (RelCT.seq (R := Two C1)
    (two_post (two_map CpP.d (fun p s h => ce_setupP p s h.1 h.2) setup_ct)
      fun p s h => ce_c1 p s h.1 h.2) ?_)
  refine RelCT.seqs_append (by simp [Crt.loadArr]) (by simp) (RelCT.seq (R := Two C2)
    (two_post (two_map CpP.yl c1_lpre (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) c1_c2) ?_)
  refine RelCT.seqs_append (by simp [rangeTest, range, gt1, ltArr, cmpArr]) (by simp) (RelCT.seq (R := Two C3)
    (two_post (two_map CpP.ws c2_goodW1 rangeXm_ct) c2_c3) ?_)
  simp only [seqs]
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [c3_eval h₁, c3_eval h₂])
    (two_taint [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
      fun _ _ ⟨⟨_, ⟨_, hc, _⟩, _⟩, _⟩ => hc.rdi) (by taint_decide)) ?_
  refine RelCT.seq (R := Two C4) (RelCT.block_append (RelCT.seq
    (two_piece (Ψ := fun (p : CpP) t => t.gpr .rdi = p.B ∧ WP isa (.block qTest) t (C4 p)) [.rdi]
      (pins_rdiB (fun p => off p.B (inner p.w)) fun _ _ ⟨⟨_, ⟨_, hc, _⟩, _⟩, _⟩ => hc.rdi)
      (by taint_decide) fun p s h => WP.and (c3_leave p s h.1) (WP.block_append_iff.mp (c3_c4 p s h.1)))
    (two_piece [.rdi] (pins_rdiB CpP.B fun _ _ h => h.1) (by taint_decide) fun _ _ h => h.2))) ?_
  exact two_ite (fun p s₁ s₂ h₁ h₂ => by rw [c4_eval h₁, c4_eval h₂])
    (two_taint [] (pins_nil _) (by taint_decide)) (subgroup_ct M E R hE)

theorem cp_body_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    RelCT isa (Two CR) (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.body M.mm E.code (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckPublic.body
  refine RelCT.seq (R := Two CE) (RelCT.block_append (RelCT.seq
    (two_piece (Ψ := E1) [.rdi, .rsi, .rdx, .rcx, .r9] (pins_of entryRegs cr_regs) (by taint_decide) cr_e1)
    (two_post (two_map CpP.d e1_dhp domHead_ct) e1_ce))) ?_
  exact two_ite (fun p s₁ s₂ h₁ h₂ => by rw [ce_eval h₁, ce_eval h₂])
    (two_taint [] (pins_nil _) (by taint_decide)) (main_ct M E R hE)

theorem cp_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    RelCT isa (Two CR) (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code M.mm E.code (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code
  refine RelCT.seq (R := Two fun (p : CpP) s => s.gpr .rdi = p.B)
    (two_post (cp_body_ct M E R hE) fun p s h =>
      WP.mono (cp_body_ok M E R (cpCtx_of h.1)) fun _ ⟨_, hdi, _⟩ => hdi.trans h.2.2.1)
    (two_taint [.rdi] (pins_rdiB CpP.B fun _ _ h => h) (by taint_decide))

def cpOf (s : State) : CpP :=
  ⟨s.gpr .r9, (scrLen s).toNat * 8, (s.gpr .rdx).toNat, (s.gpr .rsi).toNat, s.gpr .rdi, s.gpr .rcx, cpDom s,
    Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat, s.gpr .rsp⟩

theorem cp_constantTime (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    ConstantTime isa cpContract.pre cpContract.pub
      (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code M.mm E.code (.seq (.block r2Head) R.code)) := by
  refine RelCT.constantTime ((cp_ct M E R hE).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨cpOf s₁, ?_, ?_⟩) fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6⟩ := hp
    unfold cpLeak at hl
    obtain ⟨hd, hy⟩ := List.append_inj hl (by simp [cpDom, Spec.Rsa.bytesAt, r1])
    refine ⟨h₂, hsp.symm, r5.symm, by rw [← r6]; rfl, by rw [← r2]; rfl, by rw [← r1]; rfl,
      r0.symm, r3.symm, ?_, ?_⟩
    · exact ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hd).symm
    · exact ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hy).symm

end VG.Proof.Ffdh.X86_64.CheckPublic
