module
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Cache

import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad

/-!
# The public NAF multiplication

After the table (`table_ok`) and the `Z²` and `Z³` of its entries
(`cacheTo_ok`): `D = O` and the count of the digits after the top one
(`head_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- `D = O` and the count of the digits after the top one. -/
theorem head_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hone_lt : K.one < C.p) {P : Point C} {s₀ s₁ : State} (hF : NafFixed K C base s₀ P k)
    (S₁ : NSt K C base size P s₀ s₁) (hc : CacheOk K C base s₁) (hk : k < 2 ^ (64 * K.M.n)) :
    WP isa (.block (Jacobian.infinity K K.D ++
        ([.movz .x .x19 (BitVec.ofNat 16 (64 * K.M.n)) 0] : List Instr))) s₁ fun s₃ =>
      NSt K C base size P s₀ s₃ ∧ CacheOk K C base s₃ ∧ s₃.gpr .x19 = BitVec.ofNat 64 (64 * K.M.n) ∧
      (∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₃.mem base x K.M.n < C.p) ∧
      InvJ C (tmv C K.M.n base s₃ K.D.x) (tmv C K.M.n base s₃ K.D.y)
        (tmv C K.M.n base s₃ K.D.z) (mul (2 * Naf5.residual k (64 * K.M.n + 1)) P) := by
  have hW := hL.win
  have h6 := hL.n6
  rw [WP.block_append_iff]
  have hDs : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ winSlots K := fun x hx => winOther_mem (D_other K x hx)
  refine WP.mono (infinityPoint_ok hW.lay hL.al.al hDs
    (inv_of S₁.scr S₁.mod (V := winRo K) (winRo_slots K) (S₁.ro hW hF).1) hone_lt) fun s₂ h₂ => ?_
  obtain ⟨sc₂, k₂, U₂, M₂, Dl, DJ, -, -⟩ := jacPost_frame hW S₁.scr S₁.mod (Or.inr (Or.inl rfl)) h₂
  have S₂ := S₁.next hW sc₂ (k₂.mono clob_nafClob) U₂
  refine WP.mono (setCounter_ok s₂ (j := 64 * K.M.n) (by omega_arith)) fun s₃ ⟨x₃, k₃⟩ => ?_
  have S₃ := S₂.regs hW k₃ (fun r hr => nafClob_mem (by
    simp only [List.mem_singleton] at hr; subst hr; simp)) (by decide)
  have t₃ : ∀ x, tmv C K.M.n base s₃ x = tmv C K.M.n base s₂ x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [k₃.mem]
  have Dl₃ : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₃.mem base x K.M.n < C.p := by
    rw [k₃.mem]; exact Dl
  have hz : Naf5.residual k (64 * K.M.n + 1) = 0 := Naf5.residual_zero_top hk
  have DJ₃ : InvJ C (tmv C K.M.n base s₃ K.D.x) (tmv C K.M.n base s₃ K.D.y)
      (tmv C K.M.n base s₃ K.D.z) (mul (2 * Naf5.residual k (64 * K.M.n + 1)) P) := by
    rw [t₃, t₃, t₃, hz, Nat.mul_zero, show mul 0 P = .infinity by rw [Spec.Weierstrass.mul]; simp]
    exact DJ
  exact ⟨S₃, CacheUpTo.ofMem k₃.mem (CacheOk.unch hW hL.cache hc U₂ S₁.scr.nowrap), x₃, Dl₃, DJ₃⟩

end VG.Proof.Weierstrass.AArch64.PubNaf
