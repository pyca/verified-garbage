module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.StagesCT
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Math
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Correct
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Math
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Correct
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH key generation on x86-64: constant time under the shared contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem code_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    RelCT isa (Two CR)
      (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.code M.mm E.code (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Domain.GenerateKey.code
  refine RelCT.seq (R := Two fun (p : GkP) s => s.gpr .rdi = p.B)
    (two_post (body_ct M E R hE) fun p s h =>
      WP.mono (body_ok M E R h.1) fun t ⟨_, hd, _⟩ => by rw [h.2] at hd; exact hd)
    (two_taint [.rdi] (pins_rdiB GkP.B fun _ _ h => h) (by taint_decide))

theorem gk_constantTime (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    ConstantTime isa gkContract.pre gkContract.pub
      (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.code M.mm E.code (.seq (.block r2Head) R.code)) := by
  refine RelCT.constantTime ((code_ct M E R hE).mono
    (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨gkOf s₁, ⟨h₁, rfl⟩, h₂, ?_⟩) fun _ _ h => h)
  obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, a0, a1, a2, a3, a4⟩ := hp
  unfold gkLeak at hl
  obtain ⟨hd, hstatus⟩ := List.append_inj hl (by simp [gkDom, Spec.Rsa.bytesAt, r5])
  have hdom := ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hd)
  have hs := (List.cons.inj hstatus).1
  have hfalse : ((gkOf s₁).sv = false) ↔ ((gkOf s₂).sv = false) := by
    change (Spec.Ffdh.privateValid (gkA s₁) (gkS s₁) = false) ↔
      (Spec.Ffdh.privateValid (gkA s₂) (gkS s₂) = false)
    rw [← keyStatus_scalar _ _, ← keyStatus_scalar _ _, hs]
  have hsv : (gkOf s₁).sv = (gkOf s₂).sv := by
    cases h₁ : (gkOf s₁).sv <;> cases h₂ : (gkOf s₂).sv <;> simp_all
  simp only [gkOf, r0, r2, r4, r5, a0, a1, a3, a4, hsp, hdom]
  congr 1
  simpa only [gkOf, r0, r1, r2, r3, r4, r5, a0, a1, a2, a3, a4, hsp, hdom] using hsv.symm

end VG.Proof.Ffdh.X86_64.GenerateKey
