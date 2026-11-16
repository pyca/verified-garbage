module
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Layer

import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedLayer
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.AddSub
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (Tab)
open VG.Spec.MlDsa (Poly)
open VG.Proof.MlDsa (PolyIs)

private theorem lens_cases {len : Nat} (hl : len ∈ nttLens) :
    len = 128 ∨ len = 64 ∨ len = 32 ∨ len = 16 ∨ len = 8 ∨ len = 4 ∨ len = 2 ∨ len = 1 := by
  simpa only [nttLens,List.mem_cons,List.not_mem_nil,or_false] using hl

set_option linter.unusedSimpArgs false

theorem layer_fwd_ok {fP zP : Addr} {len : Nat} (hlen : len ∈ nttLens)
    {F : Poly} {s : State} (h0 : s.gpr .x0 = fP) (h1 : s.gpr .x1 = zP)
    (hc : VConsts s) (hP : PolyIs s.mem fP F) (ht : Tab zetaTab s.mem zP 256)
    (hw : pR fP ∈ s.wr) (hzp : pR zP ∈ s.rd++s.wr) (hd : (pR zP).Disjoint (pR fP)) :
    WP isa (layer bfly len true) s fun s' => PolyIs s'.mem fP (nttLayer F len) ∧ BInv fP s s' := by
  have hl := lens_cases hlen
  by_cases hsmall : len < 4
  · have hp : len = 1 ∨ len = 2 := by omega_using [hl, hsmall]
    exact layer_packed_ok bfly_spec nttBlk_ok hp zetaTab_eq true
      (fun c => 128/len+c) (fun u => 128/len+(4/len)*u)
      (by simp [firstZ])
      (by intro u hu e he; simp only [ite_true]; omega_using [])
      (by intro u hu h; contradiction)
      (by intro u hu; rcases hp with rfl | rfl <;> simp only [baseZ,ite_true,Nat.reduceDiv] <;> omega_using [hu])
      (by intro u hu; simp only [ite_true,Nat.mul_add,Nat.mul_one]; omega_using []) h0 h1 hc hP ht hw hzp hd
  · have hl' : len ∈ [4,8,16,32,64,128] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false]; omega_using [hl, hsmall]
    exact layer_large_ok bfly_spec nttBlk_ok hl' zetaTab_eq true (fun c => 128/len+c)
      (by simp [firstZ])
      (by intro c hc; rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [Nat.reduceDiv] at * <;> omega_using [hc])
      (by intro c hc; simp only [ite_true]; exact VG.Proof.MlDsa.AArch64.Arith.coeffAddr_next _ _)
      h0 h1 hc hP ht hw hzp hd

end VG.Proof.MlDsa.AArch64.Arith.Neon
