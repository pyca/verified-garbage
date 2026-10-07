import VerifiedGarbage.Proof.Weierstrass.WinLay
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog

namespace VG.Proof.Weierstrass.X86
open VG VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass

/-- The multiplication accumulator is above all window slots and bits. -/
structure WinWk (K : WinCfg) (size wk : Nat) : Prop where
  acc : WkOk K.M size wk (· ∈ winSlots K)
  bits : K.bits + 4 * K.J ≤ wk

def winWX (K : WinCfg) (wk : Nat) : List (Nat × Nat) :=
  (winWs K).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n), (wk, accLen K.M)]
def loopW (K : WinCfg) : List (Nat × Nat) :=
  (winOther K).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)]
def loopWX (K : WinCfg) (wk : Nat) : List (Nat × Nat) :=
  (winOther K).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n), (wk, accLen K.M)]

theorem winRo_apart {K : WinCfg} {size wk : Nat} (hL : WinLay K size) (hW : WinWk K size wk)
    {x : Nat} (hx : x ∈ winRo K) :
    ∀ w ∈ winWX K wk, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro w hw
  change w ∈ winW K ++ [(wk, accLen K.M)] at hw
  rcases List.mem_append.mp hw with hw | hw
  · exact hL.ro_w hx w hw
  · rw [List.mem_singleton.mp hw]
    exact Or.inl (hW.acc.sl _ (winRo_slots K _ hx))

theorem winWX_bits {K : WinCfg} {size wk : Nat} (hL : WinLay K size) (hAcc : WinWk K size wk) :
    ∀ w ∈ winWX K wk, K.bits + 4 * K.J ≤ w.1 ∨ w.1 + w.2 ≤ K.bits := by
  intro w hw
  change w ∈ winW K ++ [(wk, accLen K.M)] at hw
  rcases List.mem_append.mp hw with hw | hw
  · exact hL.bits_w w hw
  · rw [List.mem_singleton.mp hw]; exact Or.inl hAcc.bits

end VG.Proof.Weierstrass.X86
