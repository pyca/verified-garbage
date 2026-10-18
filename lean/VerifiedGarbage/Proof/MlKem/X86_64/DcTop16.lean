module

public import VerifiedGarbage.Proof.MlKem.X86_64.Dc16Dec
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes

/-!
# ML-KEM on x86-64: decapsulation with 16-bit polynomials

`m'` by `vg_mlkem*_kpke_decrypt` (`Dc16Dec.lean`), the hashes as with
polynomials of `u32`s, the re-encryption with 16-bit polynomials
(`Enc16.lean`) writing `c'` to `oCT16`, and the choice of the key
(`kemDecaps16_correct`, `kemDecaps16_ct`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Decaps16

open Decaps

/-- The end of the re-encryption. -/
abbrev EncO16 {K : Kem16} (W : Dc16Wf K) (σ s : State) : Prop :=
  Enc16.EOut16 K (dcX W.toDcWfB σ) (sc oCT16) (dcEk K.L σ) (dcM' K.L σ) (dcG K.L σ).2 s

theorem EncO16.sel {K : Kem16} {W : Dc16Wf K} {σ s : State} (h : EncO16 W σ s) : SelIn K.L oCT16 σ s :=
  ⟨h.out.1, h.out.2, h.r15, h.ct⟩

end Decaps16

open Decaps Decaps16 in
theorem kemDecaps16_correct {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (W : Dc16Wf K) {n : String}
    {c : Prog isa} (hs : v.callee.s16 = some (n, c)) (hctl : ctlOk (kemDecaps16 K v.callee (n, c)) = true)
    (σ : State) (hp : (decapsK K.L).pre σ) :
    ∃ t s', Exec isa (kemDecaps16 K v.callee (n, c)) σ t s' ∧ abiPreserved σ s' ∧ (decapsK K.L).post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok W.toDcWfB hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (dec_ok hK W hp h₁ h15) fun s₂ h₂ =>
      WP.seq (WP.mono (hashes_ok W.toDcWfB hp h₂) fun s₃ h₃ =>
        WP.seq (WP.mono (Enc16.encrypt_ok hK v hs (C := dcX W.toDcWfB σ) (show Reg.rbp ∉ argRegs by decide) (by decide) W.k.2 W.enc W.tl
            h₃.1 h₃.2) fun s₄ h₄ =>
          WP.seq (WP.mono (select_okD W.toDcWfB (EncO16.sel (W := W) h₄)) fun s₅ h₅ =>
            WP.mono (topEpi_ok h₅.dc.top (h₅.hin W.toDcWfB hp)) fun s₆ ⟨hr, hg, hm⟩ =>
              (⟨hg, post_of W.toDcWfB h₅ hr hm⟩ : gprPreserved σ s₆ ∧ (decapsK K.L).post σ s₆))))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

namespace Decaps16

open Decaps

theorem encrypt_tr {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (W : Dc16Wf K) {n : String} {c : Prog isa}
    (hs : v.callee.s16 = some (n, c)) :
    RelCT isa (R K.L (EncI W.toDcWfB)) (Top16.encrypt K v.callee (n, c) (.rbp, 384 * K.L.k) (sc oCT16))
      fun _ _ => True := by
  obtain ⟨_, rhoT⟩ := W.rhoT
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (dcR K.L) (dcW K.L) x y ∧
      Enc.EIρ K.L (dcXA W.toDcWfB) (.rbp, 384 * K.L.k) ρ x ∧ Enc.EIρ K.L (dcXA W.toDcWfB) (.rbp, 384 * K.L.k) ρ y)
      (Q := fun _ _ => True)
      fun ρ => RelCT.mono (Enc16.encrypt_tr hK v hs (C := dcXA W.toDcWfB) (show Reg.rbp ∉ argRegs by decide) (by decide) W.k.2 W.enc W.tl
        W.ijT rhoT (ρ := ρ)) (fun _ _ h => h) fun _ _ _ => trivial) ?_ fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  have i₁ : Enc.EIρ K.L (dcXA W.toDcWfB) (.rbp, 384 * K.L.k) (Enc.rhoE K.L (dcEk K.L σ₁)) x :=
    ⟨_, _, _, rfl, EIn.any h₁.1, h₁.2⟩
  have i₂ : Enc.EIρ K.L (dcXA W.toDcWfB) (.rbp, 384 * K.L.k) (Enc.rhoE K.L (dcEk K.L σ₁)) y :=
    ⟨_, _, _, (rho_pub pub).symm, EIn.any h₂.1, h₂.2⟩
  exact ⟨Enc.rhoE K.L (dcEk K.L σ₁), dc_lrel W.toDcWfB p₁ p₂ pub h₁.1.out.2.dc h₂.1.out.2.dc, i₁, i₂⟩

end Decaps16

open Decaps Decaps16 in
theorem kemDecaps16_ct {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (W : Dc16Wf K) {n : String}
    {c : Prog isa} (hs : v.callee.s16 = some (n, c)) :
    ConstantTime isa (decapsK K.L).pre (decapsK K.L).pub (kemDecaps16 K v.callee (n, c)) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemDecaps16
  refine RelCT.seq (relInv (I' := fun σ s => DC K.L σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact pro_ok W.toDcWfB hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := DM K.L) (fun σ s hp hs => dec_ok hK W hp hs.1 hs.2) (dec_tr hK W)) ?_
  refine RelCT.seq (relInv (I' := EncI W.toDcWfB) (fun σ s hp hs => hashes_ok W.toDcWfB hp hs)
    (hashes_tr W.toDcWfB)) ?_
  refine RelCT.seq (relInv (I' := EncO16 W) (fun σ s _ hi =>
      Enc16.encrypt_ok hK v hs (C := dcX W.toDcWfB σ) (show Reg.rbp ∉ argRegs by decide) (by decide) W.k.2 W.enc W.tl
        hi.1 hi.2)
    (encrypt_tr hK v W hs)) ?_
  refine RelCT.seq (relInv (I' := DEnd K.L) (fun σ s _ hs => select_okD W.toDcWfB hs.sel)
    (RelCT.mono (select_tr W.toDcWfB) (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, pub, h₁.sel, h₂.sel⟩) fun _ _ h => h)) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64
