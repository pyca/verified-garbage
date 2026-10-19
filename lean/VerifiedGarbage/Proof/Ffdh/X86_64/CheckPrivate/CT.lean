module
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.StagesCT

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.TailCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.TailCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Correct
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Math
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp5
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Entry
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Main
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarBound
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarLess
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
import VerifiedGarbage.Proof.Ffdh.X86_64.SetupWsCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp5
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Correct
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Entry
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Main
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Math
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarBound
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarLess
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
meta import VerifiedGarbage.Proof.Ffdh.X86_64.R2
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupWsCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # FFDH private-key validation on x86-64: constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private theorem pins_nil {α : Type} (Φ : α → State → Prop) : Pins Φ [] :=
  fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

def CScalar (p : KpP) (s : State) : Prop := Inner p s ∧ s.gpr .rax = bit (p.sv = true)
def CBranch (p : KpP) (s : State) : Prop := Inner p s ∧ s.zf = some (!decide (p.sv = true))

private theorem scalar_stage (p : KpP) (s : State) (h : Inner p s) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange) s (CScalar p) := by
  obtain ⟨xb, mi, hw, hd, hm⟩ := h
  exact WP.mono (scalar_ok hw hd (valid_facts hm hw.base.k1).1)
    fun t ⟨⟨hw', hd', ha⟩, _⟩ => ⟨⟨xb, mi, hw', hd', hm⟩, ha⟩

private theorem test_stage (p : KpP) (s : State) (h : CScalar p s) :
    WP isa (.block [.alu .test .rax (.reg .rax)]) s (CBranch p) := by
  obtain ⟨⟨xb, mi, hw, hd, hm⟩, ha⟩ := h
  exact WP.mono (test_bit_ok ha) fun t ⟨hz, hmem, k⟩ =>
    ⟨⟨xb, mi, hw.keep hmem k, (k.gpr (by decide)).trans hd, hm⟩, hz⟩

private theorem branch_eval {p : KpP} {s : State} (h : CBranch p s) :
    isa.eval .e s = some (!decide (p.sv = true)) := by simp [eval, h.2]

private theorem main_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.main M.mm E.code (.seq (.block r2Head) R.code) =
      seqs (((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++
        VG.Impl.Rsa.X86_64.Crt.loadArr aXm sX sXl) ++
          (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange ++
            ([.block [.alu .test .rax (.reg .rax)], .ite .e (retInner 2)
              (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.tail M.mm E.code (.seq (.block r2Head) R.code)))] :
              List (Prog isa)))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.main, List.append_assoc]

theorem main_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    RelCT isa (Two fun p s => CE p s ∧ isa.eval .ne s = some false)
      (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.main M.mm E.code (.seq (.block r2Head) R.code)) fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp [pSetup, VG.Impl.Rsa.X86_64.Crt.loadArr]) (by simp)
    (RelCT.seq (R := Two Inner) ?_ ?_)
  · exact RelCT.seqs_append (by simp [pSetup]) (by simp [VG.Impl.Rsa.X86_64.Crt.loadArr])
      (RelCT.seq (R := Two BeforeX) (two_post (two_map KpP.d ce_setup setup_ct) ce_beforeX)
        (two_post (two_map KpP.xlPub beforeX_load (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) beforeX_inner))
  refine RelCT.seqs_append (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange, isNonzero, geArr, cmpArr])
    (by simp) (RelCT.seq (R := Two CScalar) (two_post scalar_ct scalar_stage) ?_)
  simp only [seqs]
  refine RelCT.seq (R := Two CBranch) (two_piece [] (pins_nil _) (by taint_decide) test_stage) ?_
  exact two_ite (fun _ _ _ h₁ h₂ => by rw [branch_eval h₁, branch_eval h₂])
    (two_taint [.rdi] (pins_rdiB (fun p => off p.B (inner p.w)) fun _ _ h => by
      obtain ⟨_, _, _, hd, _⟩ := h.1.1; exact hd) (by taint_decide))
    (two_map id (fun _ _ h => h.1.1) (tail_ct M E R hE))

theorem body_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    RelCT isa (Two CR) (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.body M.mm E.code (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.body
  refine RelCT.seq (R := Two CE) (RelCT.block_append (RelCT.seq entry_ct
    (two_post (two_map KpP.d e1_dhp domHead_ct) e1_ce))) ?_
  exact two_ite (fun _ _ _ h₁ h₂ => by rw [ce_eval h₁, ce_eval h₂])
    (two_taint [] (pins_nil _) (by taint_decide)) (main_ct M E R hE)

theorem code_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    RelCT isa (Two CR) (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code M.mm E.code (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code
  refine RelCT.seq (R := Two fun (p : KpP) s => s.gpr .rdi = p.B)
    (two_post (body_ct M E R hE) fun p s h =>
      WP.mono (body_ok M E R h.1) fun t ⟨_, hd, _⟩ => by rw [h.2] at hd; exact hd)
    (two_taint [.rdi] (pins_rdiB KpP.B fun _ _ h => h) (by taint_decide))

theorem kp_constantTime (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    ConstantTime isa kpContract.pre kpContract.pub
      (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code M.mm E.code (.seq (.block r2Head) R.code)) := by
  refine RelCT.constantTime ((code_ct M E R hE).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨kpOf s₁, ⟨h₁, rfl⟩, h₂, ?_⟩)
    fun _ _ h => h)
  obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, a0, a1, a2⟩ := hp
  unfold kpLeak at hl
  obtain ⟨hdy, hstatus⟩ := List.append_inj hl (by simp [kpDom, kpY, Spec.Rsa.bytesAt, r1, r4])
  obtain ⟨hd, hy⟩ := List.append_inj hdy (by simp [kpDom, Spec.Rsa.bytesAt, r1])
  have hdom := ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hd)
  have hyb := ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hy)
  have hs := (List.cons.inj hstatus).1
  have hfalse : ((kpOf s₁).sv = false) ↔ ((kpOf s₂).sv = false) := by
    change (Spec.Ffdh.privateValid (Spec.Ffdh.domainOf (s₁.gpr .rdx).toNat (kpDom s₁)) (Spec.Rsa.os2ip (kpX s₁)) = false) ↔
      (Spec.Ffdh.privateValid (Spec.Ffdh.domainOf (s₂.gpr .rdx).toNat (kpDom s₂)) (Spec.Rsa.os2ip (kpX s₂)) = false)
    rw [← privateStatus_scalar _ (Spec.Rsa.os2ip (kpY s₁)) _, ← privateStatus_scalar _ (Spec.Rsa.os2ip (kpY s₂)) _, hs]
  have hsv : (kpOf s₁).sv = (kpOf s₂).sv := by
    cases h₁ : (kpOf s₁).sv <;> cases h₂ : (kpOf s₂).sv <;> simp_all
  simp only [kpOf, r0, r1, r2, r3, r5, a0, a1, a2, hsp, hdom, hyb]
  congr 1
  simpa only [kpOf, r0, r1, r2, r3, r5, a0, a1, a2, hsp, hdom, hyb] using hsv.symm

end VG.Proof.Ffdh.X86_64.CheckPrivate
