import VerifiedGarbage.Proof.Weierstrass.WinLay
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog

namespace VG.Proof.Weierstrass.X86
open VG VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass

/-- The functions of `F`, with their own working space at `wk` above all
window slots, and the table of bits apart from it. -/
structure WinWk (K : WinCfg) (F : Spec.Weierstrass.Mont.Modulus) (m size wk : Nat) : Prop where
  acc : WkOk F K.M m size wk (· ∈ winSlots K)
  bits : K.bits + 4 * K.J ≤ wk ∨ wk + 64 * K.M.n ≤ K.bits

def winWX (K : WinCfg) (wk : Nat) : List (Nat × Nat) :=
  (winWs K).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n), (wk, 64 * K.M.n), Mont.outW]
def loopW (K : WinCfg) : List (Nat × Nat) :=
  (winOther K).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)]
def loopWX (K : WinCfg) (wk : Nat) : List (Nat × Nat) :=
  (winOther K).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n), (wk, 64 * K.M.n), Mont.outW]

/-- The functions' own working space is below byte 4096. -/
theorem WinWk.wk_le {K : WinCfg} {F : Spec.Weierstrass.Mont.Modulus} {m size wk : Nat}
    (hW : WinWk K F m size wk) : wk + 64 * K.M.n = 4096 :=
  hW.acc.toCallCfg.own_le

theorem winRo_apart {K : WinCfg} {F : Spec.Weierstrass.Mont.Modulus} {m size wk : Nat}
    (hL : WinLay K size) (hW : WinWk K F m size wk)
    {x : Nat} (hx : x ∈ winRo K) :
    ∀ w ∈ winWX K wk, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro w hw
  change w ∈ winW K ++ [(wk, 64 * K.M.n), Mont.outW] at hw
  have h1 := hW.acc.sl _ (winRo_slots K _ hx)
  have h2 := hW.wk_le
  rcases List.mem_append.mp hw with hw | hw
  · exact hL.ro_w hx w hw
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl h1
    · exact Or.inl (by dsimp only [Mont.outW]; omega)

theorem winWX_bits {K : WinCfg} {F : Spec.Weierstrass.Mont.Modulus} {m size wk : Nat}
    (hL : WinLay K size) (hAcc : WinWk K F m size wk) :
    ∀ w ∈ winWX K wk, K.bits + 4 * K.J ≤ w.1 ∨ w.1 + w.2 ≤ K.bits := by
  intro w hw
  change w ∈ winW K ++ [(wk, 64 * K.M.n), Mont.outW] at hw
  have h1 := hL.bits
  have h2 := hAcc.acc.size
  rcases List.mem_append.mp hw with hw | hw
  · exact hL.bits_w w hw
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hAcc.bits
    · exact Or.inl (by dsimp only [Mont.outW]; omega)

end VG.Proof.Weierstrass.X86
