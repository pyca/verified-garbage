module

public import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain

/-! Reuse the existing public modulus-load and R-squared timing proofs. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem precomputeField_ct (M : Mont) : RelCT isa (Two PcM)
 (VG.Impl.Bignum.AArch64.seqs (pcLoadW++r2StepsPub M.mm)) (fun _ _ =>True) := by
 refine RelCT.seqs_append (by simp [pcLoadW,pcLoadWith]) (by simp [r2StepsPub]) (RelCT.seq
  (two_post (Ψ:=Pc3) (pcLoadW_ct.mono (fun _ _ h =>two_mono (fun _ _ h =>PcM.loadW h) h) (fun _ _ _ =>trivial)) ?_)
  ((pcR2_ct M).mono (fun _ _ h =>h) (fun _ _ _ =>trivial)))
 intro p s h
 have h':=h
 obtain ⟨scratch,base,room,small,large,_,length,modulus,source,nbLength,valid,_,_,span⟩:=h'
 exact WP.mono (pcLoadW_r2 scratch base room small large length modulus source span nbLength valid)
  (fun t ⟨mi,r2,frame,rest⟩ =>⟨mi,h.congr frame (fun r hr =>Nat.le_trans (pcLoadRanges_le _ r hr) room)
   (pcLoadRanges_fixed _) rest (by decide),r2⟩)

end VG.Proof.Ffdh.AArch64.Cached
