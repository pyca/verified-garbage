module
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Add
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.PubNaf
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass
open VG.Impl.Weierstrass.AArch64.Jacobian
/-- The shared double preserves both digit arrays and the cached peer table. -/
structure JointDoublePost (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ s : State)
    (j : Nat) (A : Point C) : Prop where
  st : NSt K C base size P s₀ s
  x19 : s.gpr .x19=BitVec.ofNat 64 j
  dlt : ∀x∈[K.D.x,K.D.y,K.D.z],wordsVal s.mem base x K.M.n<C.p
  d : InvJ C (tmv C K.M.n base s K.D.x) (tmv C K.M.n base s K.D.y) (tmv C K.M.n base s K.D.z) A
  cache : CacheOk K C base s
theorem jointDouble_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    {P : Point C} {s₀ s : State} (hF : NafFixed K C base s₀ P k) {A : Point C} (hA : onCurve C A=true) {j : Nat}
    (hj : j < 64 * K.M.n + 1) (h : JointDigitPost K C base size P s₀ s (j + 1) A) :
    WP isa (.seq (.block [decCounter]) (fprogB K.M (dblJ K.S K.R K.D))) s fun t => JointDoublePost K C base size P s₀ t j (Spec.Weierstrass.add A A) := by
  have hW := hL.win
  refine WP.seq (WP.mono (decCounter_ok s (by omega) (by have := hL.n6; omega) h.x19)
    fun s₁ ⟨x₁, k₁⟩ => ?_)
  have S₁ := h.st.regs hW k₁ (fun r hr => nafClob_mem (by
    simp only [List.mem_singleton] at hr; subst hr; simp)) (by decide)
  have t₁ : ∀ x, tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [k₁.mem]
  obtain ⟨-, -, -, -, a5, -, -, -⟩ := rcbApart_naf hW
  have sR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winRo K ++ winOther K :=
    fun x hx => List.mem_append_right _ (R_other K x hx)
  have sl := winJ_sl (o := K.D) (p := K.R) (q := K.R) (D_other K) sR sR
  let V := winRo K ++ [K.R.x, K.R.y, K.R.z]
  have hVs : ∀ x ∈ V, x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact winRo_slots K x hx
    · exact winOther_mem (R_other K x hx)
  have hVl : ∀ x ∈ V, wordsVal s₁.mem base x K.M.n < C.p := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (S₁.ro hW hF).1 x hx
    · rw [k₁.mem]; exact h.rlt x hx
  have hRV : ∀ x ∈ rcbR K.S K.R K.R, x ∈ V := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h' | h' | h' | h' | h' | h' | h' | h' <;> subst h' <;> simp [V, winRo]
  have RJ₁ : InvJ C (tmv C K.M.n base s₁ K.R.x) (tmv C K.M.n base s₁ K.R.y) (tmv C K.M.n base s₁ K.R.z)
      A := by rw [t₁, t₁, t₁]; exact h.r
  have hd := dblB_ok false hW.lay hL.al.al hp hC hM3 a5 sl.1 (hL.al.low sl.2.2)
    (inv_of S₁.scr S₁.mod hVs hVl) hRV hA RJ₁
  simp only [Bool.false_eq_true, ite_false] at hd
  refine WP.mono hd fun s₂ h₂ => ?_
  obtain ⟨sc₂, k₂, U₂, M₂, dl, dJ, -, -⟩ := jacPost_frame hW S₁.scr S₁.mod (Or.inr (Or.inl rfl)) h₂
  have S₂ := S₁.next hW sc₂ (k₂.mono clob_nafClob) U₂
  have x₂ : s₂.gpr .x19 = BitVec.ofNat 64 j := by
    rw [k₂.gpr _ (x19_not_clob _), x₁, Nat.add_sub_cancel]
  exact ⟨S₂,x₂,dl,dJ,CacheOk.unch hW hL.cache (CacheUpTo.ofMem k₁.mem h.cache) U₂ sc₂.nowrap⟩
end VG.Proof.Weierstrass.AArch64.PubNaf
