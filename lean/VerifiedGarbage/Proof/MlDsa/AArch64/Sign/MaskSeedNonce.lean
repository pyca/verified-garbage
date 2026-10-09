import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskSeedWords

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
    wp_strb (a := pa s (sc (oMP+66*j+64))) (by dsimp only [oMP]; omega) (by rw [h₂.get .x28, h₁.get .x28]) (by rw [h₂.wr, h₁.wr]; exact h2)
      fun s₃ h₃ => wp_lsr (by decide) fun s₄ h₄ e₄ =>
        wp_strb (a := pa s (sc (oMP+66*j+65))) (by dsimp only [oMP]; omega) (by rw [h₄.get .x28, show s₃.gpr .x28 = s₂.gpr .x28 by
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
    have := Offset.contains_base (pa s (sc (oMP+66*j+64))) (d := 0) (n := 1) (k := 2) (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have c1 : (⟨pa s (sc (oMP+66*j+64)), 2⟩ : Region).Contains (pa s (sc (oMP+66*j+65))) 1 := by
    rw [e65]; exact Offset.contains_base _ (d := 1) (by omega) (by decide)
  have i0 : InRegions s.wr (pa s (sc (oMP+66*j+64))) 1 := by
    have := inRegions_sub (off := 0) (l := 1) w2 (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have i1 : InRegions s.wr (pa s (sc (oMP+66*j+65))) 1 := by
    rw [e65]; exact inRegions_sub (off := 1) (l := 1) w2 (by omega) (by decide)
  refine WP.mono (maskPairNonce_run r j hr hj s (L.inR h1) i0 i1) fun s' ⟨hm, k⟩ => ?_
  have hf : Frame [⟨pa s (sc (oMP+66*j+64)), 2⟩] s.mem s'.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1
  refine ⟨postB_of_keep k (by decide) hf, k.get .x24, ?_⟩
  rw [hm, e65, bytes2_write, hk, ofNat64_add, kappa_bytes hx]

theorem maskPairNonce_post {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s) {r j : Nat} (hj : j<2)
    (hr : r+j < 4096) (h1 : inB (rbs ++ wbs) (sc oKAP) 8 = true) (h2 : inB wbs (sc (oMP+66*j+64)) 2 = true) :
    WP isa (.block (maskPairNonce r j)) s fun s' => ∃ W, PostB D s s' W := by
  have e65 : pa s (sc (oMP+66*j+65)) = pa s (sc (oMP+66*j+64)) + 1 := (pa_sc_add s (oMP+66*j+64) 1).symm
  have w2 := L.inW h2
  have c0 : (⟨pa s (sc (oMP+66*j+64)), 2⟩ : Region).Contains (pa s (sc (oMP+66*j+64))) 1 := by
    have := Offset.contains_base (pa s (sc (oMP+66*j+64))) (d := 0) (n := 1) (k := 2) (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have c1 : (⟨pa s (sc (oMP+66*j+64)), 2⟩ : Region).Contains (pa s (sc (oMP+66*j+65))) 1 := by
    rw [e65]; exact Offset.contains_base _ (d := 1) (by omega) (by decide)
  have i0 : InRegions s.wr (pa s (sc (oMP+66*j+64))) 1 := by
    have := inRegions_sub (off := 0) (l := 1) w2 (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have i1 : InRegions s.wr (pa s (sc (oMP+66*j+65))) 1 := by
    rw [e65]; exact inRegions_sub (off := 1) (l := 1) w2 (by omega) (by decide)
  refine WP.mono (maskPairNonce_run r j hr hj s (L.inR h1) i0 i1) fun s' ⟨hm, k⟩ => ⟨_, (postB_of_keep k (by decide)
    (W := [⟨pa s (sc (oMP+66*j+64)), 2⟩]) ?_)⟩
  rw [hm]
  exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1

end VG.Proof.MlDsa.AArch64.Sign
