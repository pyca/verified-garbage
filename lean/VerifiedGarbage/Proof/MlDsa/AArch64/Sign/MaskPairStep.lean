module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCBase
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskAt
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-! ## From `MaskSeedWords.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlKem.AArch64 (Keep Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem maskSeedHalf_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s)
    {src dst : Nat} (hs : src%8=0) (hsb : src+32≤32768) (hsrc : inB (rbs++wbs) (sc src) 32 = true)
    (hdst : inB wbs (sc dst) 32 = true)
    (hsep : sepB rbs wbs (sc src) 32 (sc dst) 32 = true) :
    WP isa (.block (maskSeedHalf src dst)) s fun t =>
      PPostB S s t [(sc dst,32)] ∧ Keep [.x9,.x10] s t ∧
        bytesAt t.mem (pa s (sc dst)) 32 = bytesAt s.mem (pa s (sc src)) 32 := by
  unfold maskSeedHalf
  refine lea_ok (by decide) _ fun s1 h1 e1 => ?_
  have eD : s1.gpr .x10 = pa s (sc dst) := e1
  have hin : Covers [⟨s.gpr .x28+BitVec.ofNat 64 src,32⟩] (s1.rd++s1.wr) := by
    rw [h1.rd,h1.wr]
    change Covers [⟨pa s (sc src),32⟩] (s.rd++s.wr)
    exact L.cR hsrc
  have hout : Covers [⟨pa s (sc dst)+BitVec.ofNat 64 0,32⟩] s1.wr := by
    rw [h1.wr,VG.Proof.MlKem.AArch64.ptr_zero]
    exact L.cW hdst
  refine WP.mono (Proof.MlKem.AArch64.KeyGen.copy_ok (S := s.gpr .x28)
    (D := pa s (sc dst)) (sb := .x28) (db := .x10) (so := src) (dO := 0) (by decide) (by decide) ⟨hs,hsb⟩ (by decide)
    (by
      rw [VG.Proof.MlKem.AArch64.ptr_zero]
      change (⟨pa s (sc src),32⟩ : Region).Disjoint ⟨pa s (sc dst),32⟩
      exact L.disj hsep)
    (h1.get .x28) eD hin hout) fun t ⟨h2,hf,hb⟩ => ?_
  rw [VG.Proof.MlKem.AArch64.ptr_zero] at hf hb
  have ht : Keep [.x9,.x10] s t := (h1.keep.trans h2).mono (by simp)
  refine ⟨postB_of_keep ht (by decide) ?_,ht,?_⟩
  · rw [← h1.mem]; exact hf
  · rw [hb,h1.mem]

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `MaskSeedNonce.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
open VG.Proof.MlKem.AArch64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem maskPairNonce_run (r j : Nat) (hr : r+j < 4096) (hj : j<2) (s : State)
    (h1 : InRegions (s.rd ++ s.wr) (pa s (sc oKAP)) 8) (h2 : InRegions s.wr (pa s (sc (oMP+66*j+64))) 1)
    (h3 : InRegions s.wr (pa s (sc (oMP+66*j+65))) 1) :
    WP isa (.block (maskPairNonce r j)) s fun s' =>
      s'.mem = (s.mem.writeW (pa s (sc (oMP+66*j+64)))
        ((s.mem.readW (pa s (sc oKAP)) 64 + BitVec.ofNat 64 (r+j)).setWidth 8)).writeW
        (pa s (sc (oMP+66*j+65))) (((s.mem.readW (pa s (sc oKAP)) 64 + BitVec.ofNat 64 (r+j)) >>> 8).setWidth 8) ∧
        Keep [.x9] s s' := by
  refine wp_ldrx (a := pa s (sc oKAP)) (by decide) rfl h1 fun s₁ h₁ e₁ => wp_addImm hr fun s₂ h₂ e₂ =>
    wp_strb (a := pa s (sc (oMP+66*j+64))) (by dsimp only [oMP]; omega_arith) (by rw [h₂.get .x28, h₁.get .x28]) (by rw [h₂.wr, h₁.wr]; exact h2)
      fun s₃ h₃ => wp_lsr (by decide) fun s₄ h₄ e₄ =>
        wp_strb (a := pa s (sc (oMP+66*j+65))) (by dsimp only [oMP]; omega_arith) (by rw [h₄.get .x28, show s₃.gpr .x28 = s₂.gpr .x28 by
          rw [h₃.gpr], h₂.get .x28, h₁.get .x28]) (by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr]; exact h3)
          fun s₅ h₅ => wp_nil ⟨?_, ((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).mono
            (by simp)⟩
  rw [h₅.mem, e₄, h₄.mem, h₃.mem, show s₃.gpr .x9 = s₂.gpr .x9 by rw [h₃.gpr], e₂, e₁, h₂.mem, h₁.mem]

theorem maskPairNonce_okB {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s) {r j x : Nat} (hj : j<2)
    (hr : r+j < 4096) (hx : x + (r+j) < 2 ^ 16) (h1 : inB (rbs ++ wbs) (sc oKAP) 8 = true)
    (h2 : inB wbs (sc (oMP+66*j+64)) 2 = true) (hk : s.mem.readW (pa s (sc oKAP)) 64 = BitVec.ofNat 64 x) :
    WP isa (.block (maskPairNonce r j)) s fun s' => PPostB D s s' [(sc (oMP+66*j+64), 2)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (pa s (sc (oMP+66*j+64))) 2 = integerToBytes (x + (r+j)) 2 := by
  have e65 : pa s (sc (oMP+66*j+65)) = pa s (sc (oMP+66*j+64)) + 1 := (pa_sc_add s (oMP+66*j+64) 1).symm
  have w2 := L.inW h2
  have c0 : (⟨pa s (sc (oMP+66*j+64)), 2⟩ : Region).Contains (pa s (sc (oMP+66*j+64))) 1 := by
    have := Offset.contains_base (pa s (sc (oMP+66*j+64))) (d := 0) (n := 1) (k := 2) (by omega_arith) (by decide)
    rwa [BitVec.add_zero] at this
  have c1 : (⟨pa s (sc (oMP+66*j+64)), 2⟩ : Region).Contains (pa s (sc (oMP+66*j+65))) 1 := by
    rw [e65]; exact Offset.contains_base _ (d := 1) (by omega_arith) (by decide)
  have i0 : InRegions s.wr (pa s (sc (oMP+66*j+64))) 1 := by
    have := inRegions_sub (off := 0) (l := 1) w2 (by omega_arith) (by decide)
    rwa [BitVec.add_zero] at this
  have i1 : InRegions s.wr (pa s (sc (oMP+66*j+65))) 1 := by
    rw [e65]; exact inRegions_sub (off := 1) (l := 1) w2 (by omega_arith) (by decide)
  refine WP.mono (maskPairNonce_run r j hr hj s (L.inR h1) i0 i1) fun s' ⟨hm, k⟩ => ?_
  have hf : Frame [⟨pa s (sc (oMP+66*j+64)), 2⟩] s.mem s'.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1
  refine ⟨postB_of_keep k (by decide) hf, k.get .x24, ?_⟩
  rw [hm, e65, bytes2_write, hk, ofNat64_add, kappa_bytes hx]

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `MaskPairSeed.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.Sign VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

def pairSeedWrites (j : Nat) : List (Ptr × Nat) :=
  [(sc (oMP+66*j),32),(sc (oMP+66*j+32),32),(sc (oMP+66*j+64),2)]

def pairSeedChk (p : Params) (r j : Nat) : Bool :=
  inB (sgB p) (sc oMS) 32 && inB (sgW p) (sc (oMP+66*j)) 32 &&
  sepB (sgR p) (sgW p) (sc oMS) 32 (sc (oMP+66*j)) 32 &&
  icmChk p [(sc (oMP+66*j),32)] r &&
  inB (sgB p) (sc (oMS+32)) 32 && inB (sgW p) (sc (oMP+66*j+32)) 32 &&
  sepB (sgR p) (sgW p) (sc (oMS+32)) 32 (sc (oMP+66*j+32)) 32 &&
  icmChk p [(sc (oMP+66*j+32),32)] r &&
  keepB (sgR p) (sgW p) [(sc (oMP+66*j+32),32)] (sc (oMP+66*j)) 32 &&
  inB (sgB p) (sc oKAP) 8 && inB (sgW p) (sc (oMP+66*j+64)) 2 &&
  icmChk p [(sc (oMP+66*j+64),2)] r &&
  keepB (sgR p) (sgW p) [(sc (oMP+66*j+64),2)] (sc (oMP+66*j)) 64 &&
  decide (p.ℓ*813+r+j<2^16) && decide (r+j<4096) && decide (j<2)

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `MaskPairFinish.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.Sign VG.Spec.MlDsa

def maskFinishChk (p : Params) (n r : Nat) : Bool :=
  let y := pS (yBase p+r)
  let yh := pS (yhBase p+r)
  copyChk (sgR p) (sgW p) yh y 1024 &&
  icmChk p [(yh,1024)] r && famChk (sgR p) (sgW p) [(yh,1024)] (yBase p) n &&
  ipChkS (sgR p) (sgW p) yh && icmChk p [(yh,1024),(sc oPS,1024)] r &&
  famChk (sgR p) (sgW p) [(yh,1024),(sc oPS,1024)] (yBase p) n

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `MaskPairStep.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.Sign VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

def maskPairStepChk (p : Params) (r : Nat) : Bool :=
  pairSeedChk p r 0 && pairSeedChk p r 1 &&
  keepB (sgR p) (sgW p) (pairSeedWrites 1) (sc oMP) 66 &&
  maskPairChk (sgR p) (sgW p) (sc oMP) (yP p r) (yP p (r+1)) (sc (oR4 p)) &&
  icmChk p [(yP p r,1024),(yP p (r+1),1024),(sc (oR4 p),8192)] r &&
  maskFinishChk p (r+2) r && maskFinishChk p (r+2) (r+1) &&
  decide (p.γ₁=2^17 ∨ p.γ₁=2^19)

end VG.Proof.MlDsa.AArch64.Sign

end
