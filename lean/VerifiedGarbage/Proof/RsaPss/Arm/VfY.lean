module

public import VerifiedGarbage.Proof.RsaPss.Arm.VfTail
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.YDig
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the start of both paths

`Y` cleared and `mHash` after its 8 zero bytes (`yDig_vf`), keeping `K2`
through writes away from what it reads (`Away2`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable (h : PssHash)

theorem away2_scr {L : Lay} {scr : BitVec 32} (hg : Geo L scr) {o n : Nat} (ho : o + n ≤ oRsa)
    (he : oEm + 1024 ≤ o ∨ o + n ≤ oEm) : Away2 L scr (sR scr o n) := by
  obtain ⟨σ', ok⟩ := hg.ok
  exact ⟨hg.slot ok ho (by rw [hg.F]; decide), hg.slot ok ho (by rw [hg.F]; decide),
    hg.slot ok ho (by rw [hg.F]; decide), hg.slot ok ho (by rw [hg.F]; decide),
    hg.slot ok ho (by rw [hg.F]; decide), hg.slot ok ho (by rw [hg.F]; decide),
    Geo.sep (by omega) (by decide) ho⟩

theorem away2_slot {L : Lay} {scr : BitVec 32} (hg : Geo L scr) {d : Nat} (hd : d + 4 ≤ frameBytes)
    (h₁ : d + 4 ≤ sC ∨ sC + 4 ≤ d) (h₂ : d + 4 ≤ sLo ∨ sLo + 4 ≤ d) (h₃ : d + 4 ≤ sDb ∨ sDb + 4 ≤ d)
    (h₄ : d + 4 ≤ sAny ∨ sAny + 4 ≤ d) (h₅ : d + 4 ≤ sPos ∨ sPos + 4 ≤ d) (h₆ : d + 4 ≤ sAcc ∨ sAcc + 4 ≤ d) :
    Away2 L scr (slotR L d) := by
  obtain ⟨σ', ok⟩ := hg.ok
  exact ⟨slotSep (by decide) hd (by omega), slotSep (by decide) hd (by omega), slotSep (by decide) hd (by omega),
    slotSep (by decide) hd (by omega), slotSep (by decide) hd (by omega), slotSep (by decide) hd (by omega),
    (hg.slot ok (o := oEm) (n := 1024) (by decide) (by rw [hg.F]; omega)).symm⟩

theorem dig_buf {P : EP} (hP : ∃ σ, In h.D P σ) : RBuf (P.lay h.D) P.dig h.D := by
  obtain ⟨σ, hi⟩ := hP
  have hf := hi.ok.fits (P.DIG h.D) (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  exact ⟨hf, by omega, ⟨P.DIG h.D, by simp, Region.contains_self _ _⟩⟩

/-- `Y`: 8 zero bytes and `mHash`. -/
abbrev Y1 (P : EP) (τ : State) (m : Mem) : Prop :=
  ∀ i < 2048, m (sa P.scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ digB h P τ).getD i 0

/-- `Y` cleared and `mHash` after its 8 zero bytes. -/
theorem yDig_vf (P : EP) (hP : ∃ σ, In h.D P σ) (Q : Prop) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧ Q) (yDig h.H 4)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ Q) ∧ Y1 h P τ s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  refine (yDig_vp h hg (j := 4) (dgP := P.dig) (by decide) (by simp) rfl (dig_buf h ⟨σ₀, hi₀⟩)
    (fun o n hon => (hg.ro ok hon (R := P.DIG h.D) (by simp)).symm) (dl := digB h P)
    (fun σ => RsaPkcs1Sig.Arm.bytesAt_length _ _ _) (fun σ s hc i hi => ?_) (X := fun τ m => K2 h P τ m ∧ Q)
    fun σ m m' ⟨hk, hq⟩ hf => ⟨K2.keep h hk hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact away2_scr hg (by decide) (by decide), hq⟩).mono
    (fun σ s ⟨hc, hk, hq⟩ => ⟨hc, hk, hq⟩) fun σ s h' => h'
  have e : Spec.Rsa.bytesAt s.mem (State.addr P.dig) h.D = Spec.Rsa.bytesAt σ.mem (State.addr P.dig) h.D :=
    hc.st.ro (R := P.DIG h.D) (by simp)
  show s.mem (State.addr P.dig + BitVec.ofNat 64 i) = (Spec.Rsa.bytesAt σ.mem (State.addr P.dig) h.D).getD i 0
  rw [← e, RsaPkcs1Sig.Arm.bytesAt_getD hi]

end VG.Proof.RsaPss.Arm.Vf
