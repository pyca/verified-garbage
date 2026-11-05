module

public import VerifiedGarbage.Proof.RsaPss.AArch64.EncCTBase
public import VerifiedGarbage.Proof.RsaPss.AArch64.EncTop
public import VerifiedGarbage.Proof.RsaPss.AArch64.Checks
import VerifiedGarbage.Proof.RsaPss.AArch64.EncCT

/-!
# EMSA-PSS's encoding on AArch64, as a callee

`encK T Hs Gs`: what `encode` (for the functions `T` the tables name, and
the hash functions `Hs` and `Gs` they compute) does, which its callers
need: from `PreE` and the tables (`Tabs.At`), the encoding with `Hs` and
MGF1 with `Gs` (`enc_correct`), in constant time for entry states with the
same public data and the same addresses of the tables' functions
(`enc_constantTime`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (PssChecks)

/-- `encode`'s contract, for the tables' functions `T`. -/
def encK (T : Tabs) (Hs Gs : Spec.Mgf1.Hash) : Contract isa where
  pre s := PreE T.H.D T.tsH T.tsG s ∧ T.At s
  post s s' := OutOk T.H.D Hs Gs s s'.mem (s'.gpr .x0)
  pub s₁ s₂ := PubE s₁ s₂ ∧ ∀ n ∈ T.names, s₂.syms n = s₁.syms n

section
variable {T : Tabs} (hH : HashOK T.H) (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK T.G)
  {Hs Gs : Spec.Mgf1.Hash} (hHs : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = T.H.D)
  (hHv : Proof.Mgf1.Valid Hs) (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = T.G.D)
  (hGv : Proof.Mgf1.Valid Gs) (hc : PssChecks T.H.P T.H.D) (hdo : DigOK T.H.P)

include hH hHs hHl hHv hGh hGl hGv hdo in
theorem enc_correct (s : State) (h : (encK T Hs Gs).pre s) :
    ∃ t s', Exec isa (encode T.f T.H T.g) s t s' ∧ abiPreserved s s' ∧ (encK T Hs Gs).post s s' :=
  let ⟨t, s', he, habi, hr⟩ := code_ok hH hGm hHs hHl hHv hGh hGl hGv hdo h.1 h.2
  ⟨t, s', he, habi, hr⟩

include hH hHs hGh hGl hGv hc hdo in
theorem enc_constantTime : ConstantTime isa (encK T Hs Gs).pre (encK T Hs Gs).pub (encode T.f T.H T.g) :=
  RelCT.constantTime ((code_ct hH hGm hHs hGh hGl hGv hc hdo).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨h₁.1, PubE.refl s₁, h₁.2, fun _ _ => rfl⟩, h₂.1, hp.1, h₂.2, hp.2⟩) fun _ _ h => h)

end

end VG.Proof.RsaPss.AArch64.Enc
