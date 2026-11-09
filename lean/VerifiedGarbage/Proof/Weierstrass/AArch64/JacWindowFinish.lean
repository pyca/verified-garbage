module
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowInvariant

import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombOut

/-! Convert the final Jacobian result, reusing the comb's conversion proof. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

def jacFinishCfg (K : WinCfg) : TCombCfg :=
  ⟨K.M,K.S,K.R,K.E,K.D,K.neg,K.zero,K.bits,260,"",5,52,(0,0),K.one⟩

/-- Conversion uses the same working slots as the fixed-base comb. -/
theorem jacFinishLayout {K : WinCfg} {size : Nat} (hL : JacWinLay K size) (hJ : K.J=52)
    (hBits : K.bits+5≤4096) : CombLay (jacFinishCfg K).toComb size := by
  have old := hL.toWinLay hJ
  have sub : ∀ x ∈ combSlots (jacFinishCfg K).toComb, x ∈ jacWinSlots K := by
    intro x hx; apply hL.old_slots x
    simp only [combSlots,jacFinishCfg,TCombCfg.toComb,winSlots,winRo,winOther,rcbW,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  refine { lay := { le := fun x hx => hL.lay.le x (sub x hx)
                    mo := fun x hx => hL.lay.mo x (sub x hx)
                    tmp := fun x hx => hL.lay.tmp x (sub x hx)
                    apart := fun x y hx hy hxy => hL.lay.apart x y (sub x hx) (sub y hy) hxy }
           add := old.rcbApart_D (Or.inr rfl)
           ro := ?_, nodup := hL.nodup, J := ?_, bits := ?_, bits4 := ?_, bits_w := ?_ }
  · intro x hx
    apply hL.ro x
    simp only [combRo,jacFinishCfg,TCombCfg.toComb,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [winRo]
  · rw [TCombCfg.toComb_J]; change 1≤52 ∧ 52≤4096; decide
  · rw [TCombCfg.toComb_J]
    change K.bits+4*52≤size
    have := hL.bits; omega
  · change K.bits+3<4096; omega
  · intro w hw
    change w ∈ jacLoopWrites K at hw
    rw [TCombCfg.toComb_J]
    change K.bits+4*52≤w.1 ∨ w.1+w.2≤K.bits
    simp only [jacLoopWrites,List.mem_append,List.mem_map,List.mem_singleton] at hw
    rcases hw with ⟨y,hy,rfl⟩ | rfl
    · have ht := hL.bits_w y (List.mem_append_left _ hy)
      dsimp only; rw [hL.n]; omega
    · have ht := hL.bits_tmp
      dsimp only; rw [hL.n]; omega

end VG.Proof.Weierstrass.AArch64
