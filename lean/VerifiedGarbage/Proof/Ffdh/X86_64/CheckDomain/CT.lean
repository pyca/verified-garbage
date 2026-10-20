module
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.StagesCT

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.OptionalCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Body
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.OptionalCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Body
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH domain validation on x86-64: full constant-time proof -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave loadArr)

private theorem main_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.main M.mm E.code (.seq (.block r2Head) R.code) =
      seqs (((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++
        (loadArr aXm sG sK ++ rangeTest aXm)) ++
        ([.ite .e (retInner 0) (.seq (.block (leave :: qTest))
          (.ite .e (ret 1) (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ M.mm E.code (.seq (.block r2Head) R.code)))))] : List (Prog isa))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.main, List.append_assoc]

private theorem checked_leave (p : CdP) (s : State)
    (h : GeneratorChecked p s ∧ isa.eval .e s = some false) :
    WP isa (.block [leave]) s fun t => t.gpr .rdi = p.B ∧ WP isa (.block qTest) t (Optional p) := by
  obtain ⟨mi, hw, hd, _⟩ := h.1.1
  exact WP.and (WP.mono (leave_ok (hw.mem.ctx hd)) fun _ ⟨hdi, _⟩ => hdi)
    (WP.block_append_iff.mp (checked_optional p s h))

private theorem checked_optional_ct :
    RelCT isa (Two fun p s => GeneratorChecked p s ∧ isa.eval .e s = some false)
      (.block (leave :: qTest)) (Two Optional) := by
  simpa only [List.singleton_append] using RelCT.block_append (RelCT.seq
    (two_piece [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
      fun _ _ h => h.1.1.choose_spec.2.1) (by taint_decide) checked_leave)
    (two_piece [.rdi] (pins_rdiB CdP.B fun _ _ h => h.1) (by taint_decide) fun _ _ h => h.2))

theorem main_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    RelCT isa (Two fun p s => CE p s ∧ isa.eval .ne s = some false)
      (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.main M.mm E.code (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp [pSetup, loadArr]) (by simp)
    (RelCT.seq (R := Two GeneratorChecked) front_ct ?_)
  simp only [seqs]
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2])
    (two_taint [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
      fun _ _ h => h.1.1.choose_spec.2.1) (by taint_decide)) ?_
  refine RelCT.seq (R := Two Optional) checked_optional_ct ?_
  exact two_ite (fun p s₁ s₂ h₁ h₂ => by
    obtain ⟨_, _, _, _, hz₁⟩ := h₁
    obtain ⟨_, _, _, _, hz₂⟩ := h₂
    simp only [eval, hz₁, hz₂])
    (two_taint [] (pins_nil _) (by taint_decide)) (optional_ct M E R hE)

theorem body_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    RelCT isa (Two CR) (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.body M.mm E.code (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckDomain.body
  refine RelCT.seq (R := Two CE) (RelCT.block_append (RelCT.seq entry_ct
    (two_post (two_map CdP.d e1_dhp domHead_ct) e1_ce))) ?_
  exact two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2.1, h₂.2.1])
    (two_taint [] (pins_nil _) (by taint_decide)) (main_ct M E R hE)

theorem code_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    RelCT isa (Two CR) (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.code M.mm E.code (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckDomain.code
  refine RelCT.seq (R := Two fun (p : CdP) s => s.gpr .rdi = p.B)
    (two_post (body_ct M E R hE) fun p s h =>
      WP.mono (cd_body_ok M E R (cdCtx_of h.1)) fun _ ⟨_, hd, _⟩ => by rw [h.2] at hd; exact hd)
    (two_taint [.rdi] (pins_rdiB CdP.B fun _ _ h => h) (by taint_decide))

theorem cd_constantTime (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    ConstantTime isa cdContract.pre cdContract.pub
      (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.code M.mm E.code (.seq (.block r2Head) R.code)) := by
  refine RelCT.constantTime ((code_ct M E R hE).mono
    (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨cdOf s₁, ⟨h₁, rfl⟩, h₂, ?_⟩) fun _ _ h => h)
  obtain ⟨hsp, hl, r0, r1, r2, r3, r4⟩ := hp
  have hdom := ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl)
  simp only [cdOf, r0, r1, r2, r3, r4, hsp, hdom]

end VG.Proof.Ffdh.X86_64.CheckDomain
