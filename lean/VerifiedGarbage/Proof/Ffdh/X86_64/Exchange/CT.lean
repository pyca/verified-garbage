module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.StagesCT

import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.R2CT
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.OutputCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Correct
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.R2CT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.OutputCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Correct
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH exchange on x86-64: constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Exchange

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)

private theorem main_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.Exchange.main M.mm E.code (.seq (.block r2Head) R.code) =
      seqs ((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++
        (([.seq (.block r2Head) R.code] : List (Prog isa)) ++
          (pow M.mm E.code sY sK sX sXl ++ (range aY ++
            ([.block VG.Impl.Ffdh.X86_64.Domain.Exchange.finBlk, storeBE,
              .block [.mov .rax (.mem (hdr sF)), leave]] : List (Prog isa)))))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.Exchange.main, List.append_assoc]

theorem main_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    RelCT isa (Two fun p s => CE p s ∧ isa.eval .ne s = some false)
      (VG.Impl.Ffdh.X86_64.Domain.Exchange.main M.mm E.code (.seq (.block r2Head) R.code)) fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp [pSetup]) (by simp) (RelCT.seq (R := Two C1)
    (two_post (two_map ExP.d ce_setup setup_ct) ce_c1) ?_)
  refine seqs_cons_ct (by simp [pow]) (RelCT.seq (r2_ct M R) ?_)
  refine RelCT.seqs_append (a := pow M.mm E.code sY sK sX sXl) (by simp [pow]) (by simp [range, gt1, ltArr, cmpArr])
    (RelCT.seq (R := Two C3)
      (two_post (two_map ExP.pw c2_ps0 (pow_ct M E (loadArr_ct (by decide) (by taint_decide) (by taint_decide))
        hE (by taint_decide) (by taint_decide) (by taint_decide))) (c2_c3 M E)) ?_)
  exact RelCT.seqs_append (by simp [range, gt1, ltArr, cmpArr]) (by simp) (RelCT.seq
    (two_post (two_map ExP.ws c3_good (range_ct (by decide) (by decide) (by taint_decide) (by taint_decide)
      (by taint_decide))) c3_c4) output_ct)

theorem body_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    RelCT isa (Two CR) (VG.Impl.Ffdh.X86_64.Domain.Exchange.body M.mm E.code (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Domain.Exchange.body
  refine RelCT.seq (R := Two CE) (RelCT.block_append (RelCT.seq entry_ct
    (two_post (two_map ExP.d e1_dhp domHead_ct) e1_ce))) ?_
  exact two_ite (fun _ _ _ h₁ h₂ => by rw [ce_eval h₁, ce_eval h₂])
    (two_taint [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)) (main_ct M E R hE)

theorem code_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    RelCT isa (Two CR) (VG.Impl.Ffdh.X86_64.Domain.Exchange.code M.mm E.code (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Domain.Exchange.code
  refine RelCT.seq (R := Two fun (p : ExP) s => s.gpr .rdi = p.B)
    (two_post (body_ct M E R hE) fun p s h =>
      WP.mono (body_ok M E R h.1) fun t ⟨_, hd, _⟩ => by rw [h.2] at hd; exact hd)
    (two_taint [.rdi] (pins_rdiB ExP.B fun _ _ h => h) (by taint_decide))

theorem ex_constantTime (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    ConstantTime isa exContract.pre exContract.pub
      (VG.Impl.Ffdh.X86_64.Domain.Exchange.code M.mm E.code (.seq (.block r2Head) R.code)) := by
  refine RelCT.constantTime ((code_ct M E R hE).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨exOf s₁, ⟨h₁, rfl⟩, h₂, ?_⟩)
    fun _ _ h => h)
  obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, a0, a1, a2, a3, a4⟩ := hp
  unfold exLeak at hl
  obtain ⟨hdy, _⟩ := List.append_inj hl (by simp [exDom, exY, Spec.Rsa.bytesAt, r3, a2])
  obtain ⟨hd, hy⟩ := List.append_inj hdy (by simp [exDom, Spec.Rsa.bytesAt, r3])
  have hdom := ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hd)
  have hyb := ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hy)
  simp only [exOf, r0, r2, r3, r4, r5, a0, a1, a3, a4, hsp, hdom, hyb]

end VG.Proof.Ffdh.X86_64.Exchange
