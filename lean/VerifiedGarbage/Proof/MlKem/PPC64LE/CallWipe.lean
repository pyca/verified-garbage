module

public import VerifiedGarbage.Impl.MlKem.PPC64LE.Wipe
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallWipe
public import VerifiedGarbage.Proof.Zeroize.PPC64LE
public import VerifiedGarbage.Proof.MlKem.PPC64LE.KeyGenCT
public import VerifiedGarbage.Proof.MlKem.PPC64LE.EncapsCT
public import VerifiedGarbage.Proof.MlKem.PPC64LE.DecapsCT
public import VerifiedGarbage.Proof.MlKem.Scrubbed
public import VerifiedGarbage.Impl.MlKem1024.PPC64LE.Top
public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Proof.MlKem.PPC64LE.KeyGen
import VerifiedGarbage.Proof.MlKem1024.PPC64LE.Calls
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Encaps
import VerifiedGarbage.Proof.MlKem.EncapsHSat
public import VerifiedGarbage.Spec.MlKem.EncapsH
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Decaps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-! ### `MlKem1024.PPC64LE.KeyGenCT`, which only this module used -/

section

/-!
# ML-KEM-1024 on PPC64LE: `vg_mlkem1024_keygen`, `Verified`

The function of `Proof/MlKem/PPC64LE/KeyGenCT.lean` for `kl1024`: its
precondition from the contract's, and the contract's postcondition from what it
shows.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.PPC64LE.KeyGen

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE VG.Impl.MlKem1024.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.PPC64LE VG.Proof.MlKem1024.PPC64LE
open VG.Proof.MlKem.PPC64LE.Enc
open VG.Proof.MlKem.PPC64LE.KeyGen hiding pre_of post_of satState verified

theorem pre_of {s : State} (h : (Proof.MlKem.Scrubbed.keyGen1024BodyContract PPC64LE.abi 48).pre s) : Pre kl1024 s := by
  sig_pre [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4⟩ := h
  exact ⟨kl1024_wf, kl1024_calls, h0, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4⟩

theorem post_of {s₀ s : State} (h3 : s.gpr .r3 = if okK kl1024 s₀ kl1024.k then 1 else 0)
    (hek : bytesAt s.mem (pEk s₀) 1568 = EK kl1024 s₀)
    (hdk : bytesAt s.mem (pDk s₀) 3168 = DK kl1024 s₀) :
    (Proof.MlKem.Scrubbed.keyGen1024BodyContract PPC64LE.abi 48).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, PPC64LE.abi, PPC64LE.argRegs]
  have e : BitVec.setWidth 32 (if okK kl1024 s₀ kl1024.k then (1 : BitVec 64) else 0) =
      if okK kl1024 s₀ kl1024.k then 1 else 0 := by
    cases okK kl1024 s₀ kl1024.k <;> rfl
  rw [h3, hek, hdk, e]
  exact outcome kl1024_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x10000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1568⟩, ⟨0x3000, 3168⟩, ⟨0x10000, 49152⟩]

theorem verified :
    Verified PPC64LE.target Impl.MlKem1024.PPC64LE.keygen1024 (Proof.MlKem.Scrubbed.keyGen1024BodyContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hek, hdk⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp, hlr⟩, post_of h3 hek hdk⟩
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6⟩ := hpub
    have hr : ρ₀ kl1024 s₁ = ρ₀ kl1024 s₂ :=
      (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨hp₁, hp₂, hsp, g3, g4, g5, g6, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlKem1024.PPC64LE.KeyGen

end

end

/-! ### `MlKem1024.PPC64LE.EncapsCT`, which only this module used -/

section

/-!
# ML-KEM-1024 on PPC64LE: `vg_mlkem1024_encaps`, `Verified`

The function of `Proof/MlKem/PPC64LE/EncapsCT.lean` for `kl1024`: its
precondition from the contract's, and the contract's postcondition from what it
shows.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.PPC64LE.Encaps

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE VG.Impl.MlKem1024.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.PPC64LE VG.Proof.MlKem1024.PPC64LE
open VG.Proof.MlKem.PPC64LE.Enc
open VG.Proof.MlKem.PPC64LE.Encaps hiding pre_of post_of satState verified pre_ofH post_ofH verifiedH

theorem pre_of {s : State} (h : (Proof.MlKem.Scrubbed.encaps1024BodyContract PPC64LE.abi 48).pre s) : Pre kl1024 s := by
  sig_pre [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4, b5,
    f1, f2, f3, f4, f5⟩ := h
  exact ⟨kl1024_wf, kl1024_calls, h0, by rw [h1]; exact .head _, by rw [h1]; exact .tail _ (.head _), h2, d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4,
    b5, f1, f2, f3, f4, f5⟩

theorem post_of {s₀ s : State}
    (h3 : s.gpr .r3 = if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 s₀)) kl1024.k then 1 else 0)
    (hkey : bytesAt s.mem (pKey s₀) 32 = KK kl1024 s₀)
    (hct : bytesAt s.mem (pCt s₀) 1568 = VG.Proof.MlKem.KPke.ct kl1024.p
      (aEnc (ekRho kl1024.p (EK kl1024 s₀)) (RR kl1024 s₀)) (EK kl1024 s₀) (M kl1024 s₀) (RR kl1024 s₀)) :
    (Proof.MlKem.Scrubbed.encaps1024BodyContract PPC64LE.abi 48).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, PPC64LE.abi, PPC64LE.argRegs]
  have e : BitVec.setWidth 32
      (if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 s₀)) kl1024.k then (1 : BitVec 64) else 0) =
      if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 s₀)) kl1024.k then 1 else 0 := by
    cases okEnc kl1024.k (ekRho kl1024.p (EK kl1024 s₀)) kl1024.k <;> rfl
  have e0 : bytesAt s₀.mem (s₀.gpr .r3) 1568 = EK kl1024 s₀ := (EK_eq kl1024 s₀).symm
  have e1 : bytesAt s₀.mem (s₀.gpr .r4) 32 = M kl1024 s₀ := (M_eq kl1024 s₀).symm
  rw [h3, e, hkey, hct, e0, e1]
  exact outcome kl1024_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x4000 | .r7 => 0x10000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1568⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1568⟩, ⟨0x10000, 49152⟩]

theorem verified :
    Verified PPC64LE.target Impl.MlKem1024.PPC64LE.encaps1024 (Proof.MlKem.Scrubbed.encaps1024BodyContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hkey, hct⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp, hlr⟩, post_of h3 hkey hct⟩
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6, g7⟩ := hpub
    have hr : ekRho kl1024.p (EK kl1024 s₁) = ekRho kl1024.p (EK kl1024 s₂) := by
      rw [EK_eq, EK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨hp₁, hp₂, hsp, g3, g4, g5, g6, g7, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

/-! ## `encapsH` -/

theorem pre_ofH {s : State} (h : (Proof.MlKem.Scrubbed.encapsH1024BodyContract PPC64LE.abi 48).pre s) : PreH kl1024 s := by
  sig_pre [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, PPC64LE.abi,
    PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, d1, d2, d3, dh1, dh2, dh3, d4, d5, d6, d7, d8, d9, b1, bh, b2, b3, b4, b5,
    f1, fh, f2, f3, f4, f5, hh⟩ := h
  have r : (args s).rd = _ := h1
  exact ⟨⟨kl1024_wf, kl1024_calls, h0, by rw [r]; exact .head _, by rw [r]; exact .tail _ (.tail _ (.head _)),
    h2, d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4, b5, f1, f2, f3, f4, f5⟩,
    by rw [h1]; exact .tail _ (.head _), dh3, bh, fh, by rw [EK_eq]; exact hh⟩

/-- `post_of` for `encapsH`, whose arguments after `ek` are one register later. -/
theorem post_ofH {s₀ s : State}
    (h3 : s.gpr .r3 = if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 (args s₀))) kl1024.k then 1 else 0)
    (hkey : bytesAt s.mem (pKey (args s₀)) 32 = KK kl1024 (args s₀))
    (hct : bytesAt s.mem (pCt (args s₀)) 1568 = VG.Proof.MlKem.KPke.ct kl1024.p
      (aEnc (ekRho kl1024.p (EK kl1024 (args s₀))) (RR kl1024 (args s₀))) (EK kl1024 (args s₀)) (M kl1024 (args s₀))
      (RR kl1024 (args s₀))) :
    (Proof.MlKem.Scrubbed.encapsH1024BodyContract PPC64LE.abi 48).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, PPC64LE.abi,
    PPC64LE.argRegs]
  have e : BitVec.setWidth 32
      (if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 (args s₀))) kl1024.k then (1 : BitVec 64) else 0) =
      if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 (args s₀))) kl1024.k then 1 else 0 := by
    cases okEnc kl1024.k (ekRho kl1024.p (EK kl1024 (args s₀))) kl1024.k <;> rfl
  have e0 : bytesAt s₀.mem (s₀.gpr .r3) 1568 = EK kl1024 (args s₀) := (EK_eq kl1024 (args s₀)).symm
  have e1 : bytesAt s₀.mem (s₀.gpr .r5) 32 = M kl1024 (args s₀) := (M_eq kl1024 (args s₀)).symm
  have hkey' : bytesAt s.mem (s₀.gpr .r6) 32 = KK kl1024 (args s₀) := hkey
  have hct' : bytesAt s.mem (s₀.gpr .r7) 1568 = _ := hct
  rw [h3, e, hkey', hct', e0, e1]
  exact outcome kl1024_wf (args s₀)

theorem verifiedH :
    Verified PPC64LE.target Impl.MlKem1024.PPC64LE.encapsH1024 (Proof.MlKem.Scrubbed.encapsH1024BodyContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hkey, hct⟩ := correctH (pre_ofH hs)
    exact ⟨t, s', he, ⟨fun r hr => (hpres r hr).trans (args_preserved s r hr), hsp, hlr⟩, post_ofH h3 hkey hct⟩
  · have hq₁ := pre_ofH h₁
    have hq₂ := pre_ofH h₂
    sig_pub [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, PPC64LE.abi,
      PPC64LE.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6, g7, g8⟩ := hpub
    have hr : ekRho kl1024.p (EK kl1024 (args s₁)) = ekRho kl1024.p (EK kl1024 (args s₂)) := by
      rw [EK_eq, EK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ctH ⟨hq₁, hq₂, hsp, g3, g4, g5, g6, g7, g8, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨VG.Proof.MlKem.PPC64LE.Encaps.satStateH 1568 1568 49152, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, PPC64LE.abi,
        PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | exact VG.Proof.MlKem.hMem_h (by decide)
        | trivial
        | decide +kernel

end VG.Proof.MlKem1024.PPC64LE.Encaps

end

end

/-! ### `MlKem1024.PPC64LE.DecapsCT`, which only this module used -/

section

/-!
# ML-KEM-1024 on PPC64LE: `vg_mlkem1024_decaps`, `Verified`

The function of `Proof/MlKem/PPC64LE/DecapsCT.lean` for `kl1024`: its
precondition from the contract's, and the contract's postcondition from what it
shows.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.PPC64LE.Decaps

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE VG.Impl.MlKem1024.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.PPC64LE VG.Proof.MlKem1024.PPC64LE
open VG.Proof.MlKem.PPC64LE.Enc
open VG.Proof.MlKem.PPC64LE.Decaps hiding pre_of post_of satState verified

theorem pre_of {s : State} (h : (Proof.MlKem.Scrubbed.decaps1024BodyContract PPC64LE.abi 48).pre s) : Pre kl1024 s := by
  sig_pre [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, d1, d2, d3, d4, d5, b1, b2, b3, b4, f1, f2, f3, f4⟩ := h
  exact ⟨kl1024_wf, kl1024_calls, h0, h1, h2, d1, d2, d3, d4, d5, b1, b2, b3, b4, f1, f2, f3, f4⟩

theorem post_of {s₀ s : State}
    (h3 : s.gpr .r3 = if okEnc kl1024.k (ρD kl1024 s₀) kl1024.k then 1 else 0)
    (hkey : bytesAt s.mem (pKey s₀) 32 =
      if CT kl1024 s₀ = C2 kl1024 s₀ then K1 kl1024 s₀ else KB kl1024 s₀) :
    (Proof.MlKem.Scrubbed.decaps1024BodyContract PPC64LE.abi 48).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, PPC64LE.abi, PPC64LE.argRegs]
  have e : BitVec.setWidth 32
      (if okEnc kl1024.k (ρD kl1024 s₀) kl1024.k then (1 : BitVec 64) else 0) =
      if okEnc kl1024.k (ρD kl1024 s₀) kl1024.k then 1 else 0 := by
    cases okEnc kl1024.k (ρD kl1024 s₀) kl1024.k <;> rfl
  have e0 : bytesAt s₀.mem (s₀.gpr .r3) 3168 = DK kl1024 s₀ := (DK_eq kl1024 s₀).symm
  have e1 : bytesAt s₀.mem (s₀.gpr .r4) 1568 = CT kl1024 s₀ := (CT_eq kl1024 s₀).symm
  rw [h3, e, hkey, e0, e1]
  exact outcome kl1024_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x10000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 3168⟩, ⟨0x2000, 1568⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 49152⟩]

theorem verified :
    Verified PPC64LE.target Impl.MlKem1024.PPC64LE.decaps1024 (Proof.MlKem.Scrubbed.decaps1024BodyContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hkey⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp, hlr⟩, post_of h3 hkey⟩
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6⟩ := hpub
    have hr : ρD kl1024 s₁ = ρD kl1024 s₂ := by
      rw [rhoD_eq, rhoD_eq, DK_eq, DK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨hp₁, hp₂, hsp, g3, g4, g5, g6, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlKem1024.PPC64LE.Decaps

end

end


/-!
# ML-KEM on PPC64LE: the functions that wipe their working space

Each of ML-KEM-768's and ML-KEM-1024's functions taking `scratch` is
`callWipe` (`Impl/CallWipe/PPC64LE.lean`) of its code, which zeroes all of
`scratch` with `vg_zeroize` once that code returns, and is verified against
the same contract with 48 more bytes of stack and `scratch` left scrubbed
(`Verified.callWipe'`; `*_scrubbed`, the contracts of
`Proof/MlKem/Scrubbed.lean`), since every byte of it is zero
(`Scrubbed.keyGen_wiped`, …). `*_verified` state them as the contracts of
`Spec/MlKem/`.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.Wipe

open VG VG.PPC64LE

/-- `vg_zeroize` has no frames. -/
theorem zeroize_sdepth : sdepth Impl.Zeroize.PPC64LE.zeroize ≤ 0 := by decide

/-! ## What the contracts read of the memory -/

/-- Memories agreeing on the region of `k` bytes at `p` agree on the `n`
bytes at offset `o` within it. -/
theorem bytesAt_agree {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ a, Region.Contains ⟨p, k⟩ a 1 → m₁ a = m₂ a) (hk : k < 2 ^ 64) {o n : Nat} (hn : o + n ≤ k) :
    Spec.Sha3.bytesAt m₁ (p + BitVec.ofNat 64 o) n = Spec.Sha3.bytesAt m₂ (p + BitVec.ofNat 64 o) n := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  rw [Offset.add_add]
  exact h _ (Offset.contains_base _ (by omega_using [hn, hi]) (by omega_using [hk, hn, hi]))

/-- `bytesAt_agree` at offset 0. -/
theorem bytesAt_agree0 {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ a, Region.Contains ⟨p, k⟩ a 1 → m₁ a = m₂ a) (hk : k < 2 ^ 64) {n : Nat} (hn : n ≤ k) :
    Spec.Sha3.bytesAt m₁ p n = Spec.Sha3.bytesAt m₂ p n := by
  have := bytesAt_agree h hk (o := 0) (n := n) (by omega_using [hn])
  rwa [show p + BitVec.ofNat 64 0 = p from BitVec.add_zero p] at this

theorem vs4 {vs : List (BitVec 64)} (h : vs.length = 4) : ∃ a b c d, vs = [a, b, c, d] :=
  match vs, h with | [a, b, c, d], _ => ⟨a, b, c, d, rfl⟩

theorem vs5 {vs : List (BitVec 64)} (h : vs.length = 5) : ∃ a b c d e, vs = [a, b, c, d, e] :=
  match vs, h with | [a, b, c, d, e], _ => ⟨a, b, c, d, e, rfl⟩

theorem vs6 {vs : List (BitVec 64)} (h : vs.length = 6) : ∃ a b c d e f, vs = [a, b, c, d, e, f] :=
  match vs, h with | [a, b, c, d, e, f], _ => ⟨a, b, c, d, e, f, rfl⟩

/-- Two buffers of a contract, one of them writable, lie apart. -/
theorem pw_disj {l : List (Region × Bool)} (h : l.Pairwise (fun a b => (a.2 || b.2) = true → a.1.Disjoint b.1))
    {i j : Nat} (hij : i < j) (hj : j < l.length) (hw : (l[i].2 || l[j].2) = true) : l[i].1.Disjoint l[j].1 :=
  List.pairwise_iff_getElem.mp h i j (by omega_using [hij, hj]) hj hij hw

/-! ## The functions, with any code verified against their contracts -/

/-- `vg_mlkem768_keygen`. -/
theorem keyGen_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.keyGenBodyContract abi st))
    (hd : sdepth body ≤ st) (hst : st + 48 < 2 ^ 64)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.keyGenBodyContract abi (st + 48)).pre s) :
    Verified target (Impl.MlKem.PPC64LE.Wipe.wiped .r6 32768 "vg_mlkem768_keygen" body) (Scrubbed.keyGenContract abi (st + 48)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.keyGenSig.params.dropLast) (ps₂ := []) (i := 3) h Proof.Zeroize.PPC64LE.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hst hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide),
        show a + 32 = a + BitVec.ofNat 64 32 from rfl,
        ← bytesAt_agree hb.1 (by decide) (o := 32) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.1 (pw_disj hpw (i := 1) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1184) (by decide),
        ← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 2400) (by decide)]
      exact h)
    (Scrubbed.keyGen_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide)])

/-- `vg_mlkem768_encaps_h`. -/
theorem encapsH_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsHBodyContract abi st))
    (hd : sdepth body ≤ st) (hst : st + 48 < 2 ^ 64)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsHBodyContract abi (st + 48)).pre s) :
    Verified target (Impl.MlKem.PPC64LE.Wipe.wiped .r8 32768 "vg_mlkem768_encaps_h" body) (Scrubbed.encapsHContract abi (st + 48)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.encapsHSig.params.dropLast) (ps₂ := []) (i := 5) h Proof.Zeroize.PPC64LE.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hst hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ at h
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide),
        ← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)]
      exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide),
        ← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.2.1 (pw_disj hpw (i := 4) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1088) (by decide)]
      exact h)
    (Scrubbed.encapsH_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)])

/-- `vg_mlkem768_encaps`. -/
theorem encaps_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsBodyContract abi st))
    (hd : sdepth body ≤ st) (hst : st + 48 < 2 ^ 64)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsBodyContract abi (st + 48)).pre s) :
    Verified target (Impl.MlKem.PPC64LE.Wipe.wiped .r7 32768 "vg_mlkem768_encaps" body) (Scrubbed.encapsContract abi (st + 48)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.encapsSig.params.dropLast) (ps₂ := []) (i := 4) h Proof.Zeroize.PPC64LE.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hst hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1088) (by decide)]
      exact h)
    (Scrubbed.encaps_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)])

/-- `vg_mlkem768_decaps`. -/
theorem decaps_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.decapsBodyContract abi st))
    (hd : sdepth body ≤ st) (hst : st + 48 < 2 ^ 64)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.decapsBodyContract abi (st + 48)).pre s) :
    Verified target (Impl.MlKem.PPC64LE.Wipe.wiped .r6 32768 "vg_mlkem768_decaps" body) (Scrubbed.decapsContract abi (st + 48)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.decapsSig.params.dropLast) (ps₂ := []) (i := 3) h Proof.Zeroize.PPC64LE.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hst hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 2400) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 1088) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide)]
      exact h)
    (Scrubbed.decaps_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 2400) (by decide)])

/-- `vg_mlkem1024_keygen`. -/
theorem keyGen1024_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi st))
    (hd : sdepth body ≤ st) (hst : st + 48 < 2 ^ 64)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi (st + 48)).pre s) :
    Verified target (Impl.MlKem.PPC64LE.Wipe.wiped .r6 49152 "vg_mlkem1024_keygen" body) (Scrubbed.keyGen1024Contract abi (st + 48)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem1024.keyGenSig.params.dropLast) (ps₂ := []) (i := 3) h Proof.Zeroize.PPC64LE.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hst hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide),
        show a + 32 = a + BitVec.ofNat 64 32 from rfl,
        ← bytesAt_agree hb.1 (by decide) (o := 32) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.1 (pw_disj hpw (i := 1) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1568) (by decide),
        ← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 3168) (by decide)]
      exact h)
    (Scrubbed.keyGen1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide)])

/-- `vg_mlkem1024_encaps_h`. -/
theorem encapsH1024_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi st))
    (hd : sdepth body ≤ st) (hst : st + 48 < 2 ^ 64)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi (st + 48)).pre s) :
    Verified target (Impl.MlKem.PPC64LE.Wipe.wiped .r8 49152 "vg_mlkem1024_encaps_h" body) (Scrubbed.encapsH1024Contract abi (st + 48)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem1024.encapsHSig.params.dropLast) (ps₂ := []) (i := 5) h Proof.Zeroize.PPC64LE.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hst hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ at h
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide),
        ← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)]
      exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide),
        ← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.2.1 (pw_disj hpw (i := 4) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1568) (by decide)]
      exact h)
    (Scrubbed.encapsH1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)])

/-- `vg_mlkem1024_encaps`. -/
theorem encaps1024_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.encaps1024BodyContract abi st))
    (hd : sdepth body ≤ st) (hst : st + 48 < 2 ^ 64)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encaps1024BodyContract abi (st + 48)).pre s) :
    Verified target (Impl.MlKem.PPC64LE.Wipe.wiped .r7 49152 "vg_mlkem1024_encaps" body) (Scrubbed.encaps1024Contract abi (st + 48)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem1024.encapsSig.params.dropLast) (ps₂ := []) (i := 4) h Proof.Zeroize.PPC64LE.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hst hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1568) (by decide)]
      exact h)
    (Scrubbed.encaps1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)])

/-- `vg_mlkem1024_decaps`. -/
theorem decaps1024_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.decaps1024BodyContract abi st))
    (hd : sdepth body ≤ st) (hst : st + 48 < 2 ^ 64)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.decaps1024BodyContract abi (st + 48)).pre s) :
    Verified target (Impl.MlKem.PPC64LE.Wipe.wiped .r6 49152 "vg_mlkem1024_decaps" body) (Scrubbed.decaps1024Contract abi (st + 48)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem1024.decapsSig.params.dropLast) (ps₂ := []) (i := 3) h Proof.Zeroize.PPC64LE.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hst hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 3168) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 1568) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide)]
      exact h)
    (Scrubbed.decaps1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 3168) (by decide)])

/-! ## The stack the functions use: their callees' frames, at most 48 bytes -/

theorem keyGen_sdepth : sdepth Impl.MlKem.PPC64LE.keygen ≤ 48 := by lit_decide
theorem encapsH_sdepth : sdepth Impl.MlKem.PPC64LE.encapsH ≤ 48 := by lit_decide
theorem encaps_sdepth : sdepth Impl.MlKem.PPC64LE.encaps ≤ 48 := by lit_decide
theorem decaps_sdepth : sdepth Impl.MlKem.PPC64LE.decaps ≤ 48 := by lit_decide
theorem keyGen1024_sdepth : sdepth Impl.MlKem1024.PPC64LE.keygen1024 ≤ 48 := by lit_decide
theorem encapsH1024_sdepth : sdepth Impl.MlKem1024.PPC64LE.encapsH1024 ≤ 48 := by lit_decide
theorem encaps1024_sdepth : sdepth Impl.MlKem1024.PPC64LE.encaps1024 ≤ 48 := by lit_decide
theorem decaps1024_sdepth : sdepth Impl.MlKem1024.PPC64LE.decaps1024 ≤ 48 := by lit_decide

/-! ## The states satisfying the preconditions, with the frame's 48 more bytes of stack -/

/-- A state satisfying a precondition built with `Sig.contract`, after
`sig_apply_check`. -/
macro "wipe_sat " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (sig_apply_check
   · decide +kernel
   · sig_reduce [$ls,*]
     sig_and_intros
     all_goals first
       | exact VG.Proof.MlKem.hMem_h (by decide)
       | trivial
       | decide +kernel))

theorem keyGen_sat : ∃ s, (Proof.MlKem.Scrubbed.keyGenBodyContract abi 96).pre s := by
  refine ⟨Proof.MlKem.PPC64LE.KeyGen.satState, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.keyGenBodyContract, Spec.MlKem.keyGenSig, PPC64LE.abi, PPC64LE.argRegs]

theorem encaps_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsBodyContract abi 96).pre s := by
  refine ⟨Proof.MlKem.PPC64LE.Encaps.satState, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.encapsBodyContract, Spec.MlKem.encapsSig, PPC64LE.abi, PPC64LE.argRegs]

theorem encapsH_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsHBodyContract abi 96).pre s := by
  refine ⟨Proof.MlKem.PPC64LE.Encaps.satStateH 1184 1088 32768, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, PPC64LE.abi,
    PPC64LE.argRegs]

theorem decaps_sat : ∃ s, (Proof.MlKem.Scrubbed.decapsBodyContract abi 96).pre s := by
  refine ⟨Proof.MlKem.PPC64LE.Decaps.satState, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.decapsBodyContract, Spec.MlKem.decapsSig, PPC64LE.abi, PPC64LE.argRegs]

theorem keyGen1024_sat : ∃ s, (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi 96).pre s := by
  refine ⟨Proof.MlKem1024.PPC64LE.KeyGen.satState, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, PPC64LE.abi, PPC64LE.argRegs]

theorem encaps1024_sat : ∃ s, (Proof.MlKem.Scrubbed.encaps1024BodyContract abi 96).pre s := by
  refine ⟨Proof.MlKem1024.PPC64LE.Encaps.satState, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, PPC64LE.abi, PPC64LE.argRegs]

theorem encapsH1024_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi 96).pre s := by
  refine ⟨Proof.MlKem.PPC64LE.Encaps.satStateH 1568 1568 49152, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, PPC64LE.abi,
    PPC64LE.argRegs]

theorem decaps1024_sat : ∃ s, (Proof.MlKem.Scrubbed.decaps1024BodyContract abi 96).pre s := by
  refine ⟨Proof.MlKem1024.PPC64LE.Decaps.satState, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, PPC64LE.abi, PPC64LE.argRegs]

/-! ## The functions, with 96 bytes of stack -/

theorem keyGen_scrubbed : Verified target Impl.MlKem.PPC64LE.Wipe.keyGen (Scrubbed.keyGenContract abi 96) :=
  keyGen_wipe Proof.MlKem.PPC64LE.KeyGen.verified keyGen_sdepth (by decide) keyGen_sat

theorem keyGen_verified : Verified target Impl.MlKem.PPC64LE.Wipe.keyGen (Spec.MlKem.keyGenContract abi 96) :=
  keyGen_scrubbed

theorem encapsH_scrubbed : Verified target Impl.MlKem.PPC64LE.Wipe.encapsH (Scrubbed.encapsHContract abi 96) :=
  encapsH_wipe Proof.MlKem.PPC64LE.Encaps.verifiedH encapsH_sdepth (by decide) encapsH_sat

theorem encapsH_verified : Verified target Impl.MlKem.PPC64LE.Wipe.encapsH (Spec.MlKem.encapsHContract abi 96) :=
  encapsH_scrubbed

theorem encaps_scrubbed : Verified target Impl.MlKem.PPC64LE.Wipe.encaps (Scrubbed.encapsContract abi 96) :=
  encaps_wipe Proof.MlKem.PPC64LE.Encaps.verified encaps_sdepth (by decide) encaps_sat

theorem encaps_verified : Verified target Impl.MlKem.PPC64LE.Wipe.encaps (Spec.MlKem.encapsContract abi 96) :=
  encaps_scrubbed

theorem decaps_scrubbed : Verified target Impl.MlKem.PPC64LE.Wipe.decaps (Scrubbed.decapsContract abi 96) :=
  decaps_wipe Proof.MlKem.PPC64LE.Decaps.verified decaps_sdepth (by decide) decaps_sat

theorem decaps_verified : Verified target Impl.MlKem.PPC64LE.Wipe.decaps (Spec.MlKem.decapsContract abi 96) :=
  decaps_scrubbed

theorem keyGen1024_scrubbed :
    Verified target Impl.MlKem.PPC64LE.Wipe.keyGen1024 (Scrubbed.keyGen1024Contract abi 96) :=
  keyGen1024_wipe Proof.MlKem1024.PPC64LE.KeyGen.verified keyGen1024_sdepth (by decide) keyGen1024_sat

theorem keyGen1024_verified :
    Verified target Impl.MlKem.PPC64LE.Wipe.keyGen1024 (Spec.MlKem1024.keyGenContract abi 96) :=
  keyGen1024_scrubbed

theorem encapsH1024_scrubbed :
    Verified target Impl.MlKem.PPC64LE.Wipe.encapsH1024 (Scrubbed.encapsH1024Contract abi 96) :=
  encapsH1024_wipe Proof.MlKem1024.PPC64LE.Encaps.verifiedH encapsH1024_sdepth (by decide) encapsH1024_sat

theorem encapsH1024_verified :
    Verified target Impl.MlKem.PPC64LE.Wipe.encapsH1024 (Spec.MlKem1024.encapsHContract abi 96) :=
  encapsH1024_scrubbed

theorem encaps1024_scrubbed :
    Verified target Impl.MlKem.PPC64LE.Wipe.encaps1024 (Scrubbed.encaps1024Contract abi 96) :=
  encaps1024_wipe Proof.MlKem1024.PPC64LE.Encaps.verified encaps1024_sdepth (by decide) encaps1024_sat

theorem encaps1024_verified :
    Verified target Impl.MlKem.PPC64LE.Wipe.encaps1024 (Spec.MlKem1024.encapsContract abi 96) :=
  encaps1024_scrubbed

theorem decaps1024_scrubbed :
    Verified target Impl.MlKem.PPC64LE.Wipe.decaps1024 (Scrubbed.decaps1024Contract abi 96) :=
  decaps1024_wipe Proof.MlKem1024.PPC64LE.Decaps.verified decaps1024_sdepth (by decide) decaps1024_sat

theorem decaps1024_verified :
    Verified target Impl.MlKem.PPC64LE.Wipe.decaps1024 (Spec.MlKem1024.decapsContract abi 96) :=
  decaps1024_scrubbed

end VG.Proof.MlKem.PPC64LE.Wipe
