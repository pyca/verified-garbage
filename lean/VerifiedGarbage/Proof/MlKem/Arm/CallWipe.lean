module

public import VerifiedGarbage.Impl.MlKem.Arm.Wipe
public import VerifiedGarbage.Proof.Framework.Arm.CallWipe
public import VerifiedGarbage.Proof.Framework.Arm.CallWipeStack
public import VerifiedGarbage.Proof.Zeroize.Arm
public import VerifiedGarbage.Proof.MlKem.Arm.KeyGenCT
public import VerifiedGarbage.Proof.MlKem.Arm.EncapsCT
public import VerifiedGarbage.Proof.MlKem.Arm.DecapsCT
public import VerifiedGarbage.Proof.MlKem.Scrubbed
public import VerifiedGarbage.Impl.MlKem1024.Arm.Top
public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Proof.MlKem.Arm.KeyGen
import VerifiedGarbage.Proof.MlKem1024.Arm.Calls
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.Arm.Encaps
import VerifiedGarbage.Proof.MlKem.EncapsHSat
public import VerifiedGarbage.Spec.MlKem.EncapsH
public import VerifiedGarbage.Proof.MlKem.Arm.Decaps
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `MlKem1024.Arm.KeyGenCT`, which only this module used -/

section

/-!
# ML-KEM-1024 on 32-bit ARM: `vg_mlkem1024_keygen`, `Verified`

The key generation of `Proof/MlKem/Arm/KeyGenCT.lean` for `kl1024`: its precondition
from the contract's, and the contract's postcondition from what it shows.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.Arm.KeyGen

open VG VG.Arm VG.Impl.MlKem.Arm VG.Impl.MlKem1024.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.Arm VG.Proof.MlKem1024.Arm
open VG.Proof.MlKem.Arm.Enc
open VG.Proof.MlKem.Arm.KeyGen hiding pre_of post_of satState verified

theorem pre_of {s : State} (h : (Proof.MlKem.Scrubbed.keyGen1024BodyContract Arm.abi 8).pre s) : Pre kl1024 s := by
  sig_pre [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, -, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4⟩ := h
  exact ⟨kl1024_wf, kl1024_calls, h0, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4⟩

theorem post_of {s₀ s : State} (h0 : s.gpr .r0 = if okK kl1024 s₀ kl1024.k then 1 else 0)
    (hek : bytesAt s.mem (State.addr (pEk s₀)) 1568 = EK kl1024 s₀)
    (hdk : bytesAt s.mem (State.addr (pDk s₀)) 3168 = DK kl1024 s₀) :
    (Proof.MlKem.Scrubbed.keyGen1024BodyContract Arm.abi 8).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  rw [setWidth_append32, h0]
  have e1 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r1)) 1568 = EK kl1024 s₀ := hek
  have e2 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r2)) 3168 = DK kl1024 s₀ := hdk
  have eD : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0)) 32 = D s₀ := rfl
  have eZ : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0) + 32) 32 = Z s₀ := rfl
  rw [e1, e2, eD, eZ]
  exact outcome kl1024_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x10000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1568⟩, ⟨0x3000, 3168⟩, ⟨0x10000, 49152⟩]

theorem verified :
    Verified Arm.target Impl.MlKem1024.Arm.keygen1024 (Proof.MlKem.Scrubbed.keyGen1024BodyContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h0, hek, hdk⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp⟩, post_of h0 hek hdk⟩
  · sig_pub [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := hpub
    have hr : ρ₀ kl1024 s₁ = ρ₀ kl1024 s₂ :=
      (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨pre_of h₁, pre_of h₂, hsp, h0, h1, h2, h3, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_sat_check [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlKem1024.Arm.KeyGen

end

end

/-! ### `MlKem1024.Arm.EncapsCT`, which only this module used -/

section

/-!
# ML-KEM-1024 on 32-bit ARM: `vg_mlkem1024_encaps`, `Verified`

The encapsulation of `Proof/MlKem/Arm/EncapsCT.lean` for `kl1024`: its precondition
from the contract's, and the contract's postcondition from what it shows.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.Arm.Encaps

open VG VG.Arm VG.Impl.MlKem.Arm VG.Impl.MlKem1024.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.Arm VG.Proof.MlKem1024.Arm
open VG.Proof.MlKem.Arm.Enc
open VG.Proof.MlKem.Arm.Encaps hiding pre_of post_of satState verified pre_ofH post_ofH verifiedH

theorem pre_of {s : State} (h : (Proof.MlKem.Scrubbed.encaps1024BodyContract Arm.abi 8).pre s) :
    Pre kl1024 (withR12 s (stackArg s 0)) ∧ InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4 := by
  sig_pre [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, -, h2, h3, d1, d2, d3, d4, d5, d6, d7, d8, -, d10, -, -, b1, b2, b3, b4, b5, -,
    f1, f2, f3, f4, f5⟩ := h
  exact ⟨⟨kl1024_wf, kl1024_calls, h0, by show _ ∈ s.rd; rw [h2]; exact .head _,
    by show _ ∈ s.rd; rw [h2]; exact .tail _ (.head _), h3, d1, d2, d3, d4, d5, d6, d7, d8, d10, b1, b2, b3, b4, b5,
    f1, f2, f3, f4, f5⟩, ⟨_, List.mem_append_left _ (by rw [h2]; exact .tail _ (.tail _ (.head _))),
      Region.contains_self _ _⟩⟩

theorem post_of {s₀ s : State}
    (h0 : s.gpr .r0 = if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 s₀)) kl1024.k then 1 else 0)
    (hkey : bytesAt s.mem (State.addr (pKey s₀)) 32 = KK kl1024 s₀)
    (hct : bytesAt s.mem (State.addr (pCt s₀)) 1568 = VG.Proof.MlKem.KPke.ct kl1024.p
      (aEnc (ekRho kl1024.p (EK kl1024 s₀)) (RR kl1024 s₀)) (EK kl1024 s₀) (M kl1024 s₀) (RR kl1024 s₀)) :
    (Proof.MlKem.Scrubbed.encaps1024BodyContract Arm.abi 8).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  rw [setWidth_append32, h0]
  have e0 : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0)) 1568 = EK kl1024 s₀ := (EK_eq kl1024 s₀).symm
  have e1 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r2)) 32 = KK kl1024 s₀ := hkey
  have e2 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r3)) 1568 = VG.Proof.MlKem.KPke.ct kl1024.p
      (aEnc (ekRho kl1024.p (EK kl1024 s₀)) (RR kl1024 s₀)) (EK kl1024 s₀) (M kl1024 s₀) (RR kl1024 s₀) := hct
  rw [e0, ← M_eq, e1, e2]
  exact outcome kl1024_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 0 else if a = 0x8001 then 0 else if a = 0x8002 then 1 else 0
  rd := [⟨0x1000, 1568⟩, ⟨0x2000, 32⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1568⟩, ⟨0x10000, 49152⟩]

theorem verified :
    Verified Arm.target Impl.MlKem1024.Arm.encaps1024 (Proof.MlKem.Scrubbed.encaps1024BodyContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h0, hkey, hct⟩ := entry_correct (pre_of hs).1 (pre_of hs).2
    exact ⟨t, s', he, ⟨preserved_withR12 hpres, hsp⟩, post_of h0 hkey hct⟩
  · sig_pub [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3, hs⟩ := hpub
    have hr : ekRho kl1024.p (EK kl1024 s₁) = ekRho kl1024.p (EK kl1024 s₂) := by
      rw [EK_eq, EK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (entry_ct ⟨(pre_of h₁).1, (pre_of h₂).1, hsp, h0, h1, h2, h3, hs, hr⟩ (pre_of h₁).2 (pre_of h₂).2
      s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_sat_check [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

/-! ## `encapsH` -/

theorem pre_ofH {s : State} (h : (Proof.MlKem.Scrubbed.encapsH1024BodyContract Arm.abi 8).pre s) : PreH kl1024 s := by
  sig_pre [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h0, h1, h2, h3, d1, d2, d3, -, -, dh3, d4, d5, d6, d7, d8, -, d10, -, d12, b1, bh, b2, b3, b4, b5, -,
    f1, fh, f2, f3, f4, f5, hh⟩ := h
  have hc : ∀ k ≤ 4, Region.Contains ⟨stackArgAddr s 0, 8⟩ (State.addr (s.sp + BitVec.ofNat 32 k)) 4 := by
    intro k hk
    simp only [Region.Contains, stackArgAddr, State.addr]
    bv_omega
  have ra : (⟨stackArgAddr s 0, 8⟩ : Region) ∈ s.rd ++ s.wr := by
    rw [h2]; exact List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.head _))))
  exact ⟨⟨kl1024_wf, kl1024_calls, h0, by show _ ∈ s.rd; rw [h2]; exact .head _,
    by show _ ∈ s.rd; rw [h2]; exact .tail _ (.tail _ (.head _)), h3, d1, d2, d3, d4, d5, d6, d7, d8, d10,
    b1, b2, b3, b4, b5, f1, f2, f3, f4, f5⟩, by rw [h2]; exact .tail _ (.head _), dh3, bh, fh,
    by rw [EK_eq]; exact hh, ⟨_, ra, hc 0 (by decide)⟩, ⟨_, ra, hc 4 (by decide)⟩,
    d12.symm.sub_left (Region.sub_prefix (by decide))⟩

/-- `post_of` for `encapsH`, whose `m` and `key` are one register later and `ct` on the stack. -/
theorem post_ofH {s₀ s : State}
    (h0 : s.gpr .r0 = if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 (args s₀))) kl1024.k then 1 else 0)
    (hkey : bytesAt s.mem (State.addr (pKey (args s₀))) 32 = KK kl1024 (args s₀))
    (hct : bytesAt s.mem (State.addr (pCt (args s₀))) 1568 = VG.Proof.MlKem.KPke.ct kl1024.p
      (aEnc (ekRho kl1024.p (EK kl1024 (args s₀))) (RR kl1024 (args s₀))) (EK kl1024 (args s₀)) (M kl1024 (args s₀))
      (RR kl1024 (args s₀))) :
    (Proof.MlKem.Scrubbed.encapsH1024BodyContract Arm.abi 8).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]
  rw [setWidth_append32, h0]
  have e0 : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0)) 1568 = EK kl1024 (args s₀) :=
    (EK_eq kl1024 (args s₀)).symm
  have e1 : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r2)) 32 = M kl1024 (args s₀) := (M_eq kl1024 (args s₀)).symm
  have e2 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r3)) 32 = KK kl1024 (args s₀) := hkey
  have e3 : bytesAt s.mem (BitVec.setWidth 64 (stackArg s₀ 0)) 1568 = VG.Proof.MlKem.KPke.ct kl1024.p
      (aEnc (ekRho kl1024.p (EK kl1024 (args s₀))) (RR kl1024 (args s₀))) (EK kl1024 (args s₀)) (M kl1024 (args s₀))
      (RR kl1024 (args s₀)) := hct
  rw [e0, e1, e2, e3]
  exact outcome kl1024_wf (args s₀)

theorem verifiedH : Verified Arm.target Impl.MlKem1024.Arm.encapsH1024 (Proof.MlKem.Scrubbed.encapsH1024BodyContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h0, hkey, hct⟩ := entryH_correct (pre_ofH hs)
    exact ⟨t, s', he, ⟨fun r hr => (hpres r hr).trans (args_preserved s r hr), hsp⟩, post_ofH h0 hkey hct⟩
  · sig_pub [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, g0, g1, g2, g3, gc, gs⟩ := hpub
    have hr : ekRho kl1024.p (EK kl1024 (args s₁)) = ekRho kl1024.p (EK kl1024 (args s₂)) := by
      rw [EK_eq, EK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (entryH_ct ⟨pre_ofH h₁, pre_ofH h₂, hsp, g0, g1, g2, g3, gc, gs, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩
      e₁ e₂).1
  · refine ⟨VG.Proof.MlKem.Arm.Encaps.satStateH 1568 1568 49152, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | (show bytesAt (VG.Proof.MlKem.Arm.Encaps.satStateH 1568 1568 49152).mem (0x2000 : BitVec 64) 32 =
              VG.Spec.MlKem.H (bytesAt (VG.Proof.MlKem.Arm.Encaps.satStateH 1568 1568 49152).mem (0x1000 : BitVec 64) 1568)
           exact VG.Proof.MlKem.hMem_h_of (by decide) VG.Proof.MlKem.Arm.Encaps.satStateH_mem)
        | (fail_if_success show bytesAt _ _ _ = _
           decide +kernel)

end VG.Proof.MlKem1024.Arm.Encaps

end

end

/-! ### `MlKem1024.Arm.DecapsCT`, which only this module used -/

section

/-!
# ML-KEM-1024 on 32-bit ARM: `vg_mlkem1024_decaps`, `Verified`

The decapsulation of `Proof/MlKem/Arm/DecapsCT.lean` for `kl1024`: its precondition
from the contract's, and the contract's postcondition from what it shows.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.Arm.Decaps

open VG VG.Arm VG.Impl.MlKem.Arm VG.Impl.MlKem1024.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.Arm VG.Proof.MlKem1024.Arm
open VG.Proof.MlKem.Arm.Enc
open VG.Proof.MlKem.Arm.Decaps hiding pre_of post_of satState verified

theorem pre_of {s : State} (h : (Proof.MlKem.Scrubbed.decaps1024BodyContract Arm.abi 8).pre s) : Pre kl1024 s := by
  sig_pre [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, h1, h2, h3, d1, d2, d3, d4, d5, b1, b2, b3, b4, f1, f2, f3, f4⟩ := h
  exact ⟨kl1024_wf, kl1024_calls, h0, h1, h2, h3, d1, d2, d3, d4, d5, b1, b2, b3, b4, f1, f2, f3, f4⟩

theorem post_of {s₀ s : State} (h0 : s.gpr .r0 = if okEnc kl1024.k (ρD kl1024 s₀) kl1024.k then 1 else 0)
    (hkey : bytesAt s.mem (State.addr (pKey s₀)) 32 =
      if CT kl1024 s₀ = C2 kl1024 s₀ then K1 kl1024 s₀ else KB kl1024 s₀) :
    (Proof.MlKem.Scrubbed.decaps1024BodyContract Arm.abi 8).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  have e0 : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0)) 3168 = DK kl1024 s₀ := (DK_eq kl1024 s₀).symm
  have e1 : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r1)) 1568 = CT kl1024 s₀ := (CT_eq kl1024 s₀).symm
  have e2 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r2)) 32 =
      if CT kl1024 s₀ = C2 kl1024 s₀ then K1 kl1024 s₀ else KB kl1024 s₀ := hkey
  rw [setWidth_append32, h0, e0, e1, e2]
  exact outcome kl1024_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x10000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 3168⟩, ⟨0x2000, 1568⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 49152⟩]

theorem verified :
    Verified Arm.target Impl.MlKem1024.Arm.decaps1024 (Proof.MlKem.Scrubbed.decaps1024BodyContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h0, hkey⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp⟩, post_of h0 hkey⟩
  · sig_pub [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := hpub
    have hr : ρD kl1024 s₁ = ρD kl1024 s₂ := by
      rw [ρD_eq, ρD_eq, DK_eq, DK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨pre_of h₁, pre_of h₂, hsp, h0, h1, h2, h3, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_sat_check [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlKem1024.Arm.Decaps

end

end


/-!
# ML-KEM on 32-bit ARM: the functions that wipe their working space

Each of ML-KEM-768's and ML-KEM-1024's functions taking `scratch` is
`callWipe` (`Impl/CallWipe/Arm.lean`) of its code, for key generation and
decapsulation, which get `scratch` in `r3`, or `callWipeStack`
(`Impl/CallWipe/ArmStack.lean`), for encapsulation, which gets it on the
stack, and zeroes all of `scratch` with `vg_zeroize` once that code returns.
It is verified against the same contract with 16 more bytes of stack, 24
(`Verified.callWipe'`), or 24 more, 32 (`Verified.callWipeStack'`: its frame
and the copy of the stack arguments, 8 bytes for one word or two), with
`scratch` left scrubbed (`*_scrubbed`, the contracts of
`Proof/MlKem/Scrubbed.lean`), since every byte of it is zero
(`Scrubbed.keyGen_wiped`, …). `*_verified` state them as the contracts of
`Spec/MlKem/`.
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm.Wipe

open VG VG.Arm VG.Arm.FrameStack

/-- `vg_zeroize` has no frames. -/
theorem zeroize_stack : armStack Impl.Zeroize.Arm.zeroize ≤ 0 := by decide

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
theorem keyGen_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.keyGenBodyContract abi 8))
    (hd : armStack body ≤ 8)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.keyGenBodyContract abi 24).pre s) :
    Verified target (Impl.MlKem.Arm.Wipe.wiped .r3 32768 "vg_mlkem768_keygen" body) (Scrubbed.keyGenContract abi 24) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.keyGenSig.params.dropLast) (ps₂ := []) (i := 3) (stack := 8) h Proof.Zeroize.Arm.verified
    (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) hd zeroize_stack (Nat.zero_le _)
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
theorem encapsH_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsHBodyContract abi 8))
    (hd : armStack body ≤ 8)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsHBodyContract abi 32).pre s) :
    Verified target (Impl.MlKem.Arm.Wipe.wipedStack 2 4 32768 "vg_mlkem768_encaps_h" body) (Scrubbed.encapsHContract abi 32) :=
  Verified.callWipeStack' (ps₁ := Spec.MlKem.encapsHSig.params.dropLast) (ps₂ := []) (i := 5) (k := 2) (off := 4) (stack := 8) h
    Proof.Zeroize.Arm.verified (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide)
    (by decide) hd zeroize_stack (Nat.zero_le _)
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
theorem encaps_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsBodyContract abi 8))
    (hd : armStack body ≤ 8)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsBodyContract abi 32).pre s) :
    Verified target (Impl.MlKem.Arm.Wipe.wipedStack 1 0 32768 "vg_mlkem768_encaps" body) (Scrubbed.encapsContract abi 32) :=
  Verified.callWipeStack' (ps₁ := Spec.MlKem.encapsSig.params.dropLast) (ps₂ := []) (i := 4) (k := 1) (off := 0) (stack := 8) h
    Proof.Zeroize.Arm.verified (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide)
    (by decide) hd zeroize_stack (Nat.zero_le _)
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
theorem decaps_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.decapsBodyContract abi 8))
    (hd : armStack body ≤ 8)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.decapsBodyContract abi 24).pre s) :
    Verified target (Impl.MlKem.Arm.Wipe.wiped .r3 32768 "vg_mlkem768_decaps" body) (Scrubbed.decapsContract abi 24) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.decapsSig.params.dropLast) (ps₂ := []) (i := 3) (stack := 8) h Proof.Zeroize.Arm.verified
    (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) hd zeroize_stack (Nat.zero_le _)
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
theorem keyGen1024_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi 8))
    (hd : armStack body ≤ 8)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi 24).pre s) :
    Verified target (Impl.MlKem.Arm.Wipe.wiped .r3 49152 "vg_mlkem1024_keygen" body) (Scrubbed.keyGen1024Contract abi 24) :=
  Verified.callWipe' (ps₁ := Spec.MlKem1024.keyGenSig.params.dropLast) (ps₂ := []) (i := 3) (stack := 8) h Proof.Zeroize.Arm.verified
    (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) hd zeroize_stack (Nat.zero_le _)
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
theorem encapsH1024_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi 8))
    (hd : armStack body ≤ 8)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi 32).pre s) :
    Verified target (Impl.MlKem.Arm.Wipe.wipedStack 2 4 49152 "vg_mlkem1024_encaps_h" body) (Scrubbed.encapsH1024Contract abi 32) :=
  Verified.callWipeStack' (ps₁ := Spec.MlKem1024.encapsHSig.params.dropLast) (ps₂ := []) (i := 5) (k := 2) (off := 4) (stack := 8) h
    Proof.Zeroize.Arm.verified (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide)
    (by decide) hd zeroize_stack (Nat.zero_le _)
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
theorem encaps1024_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.encaps1024BodyContract abi 8))
    (hd : armStack body ≤ 8)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encaps1024BodyContract abi 32).pre s) :
    Verified target (Impl.MlKem.Arm.Wipe.wipedStack 1 0 49152 "vg_mlkem1024_encaps" body) (Scrubbed.encaps1024Contract abi 32) :=
  Verified.callWipeStack' (ps₁ := Spec.MlKem1024.encapsSig.params.dropLast) (ps₂ := []) (i := 4) (k := 1) (off := 0) (stack := 8) h
    Proof.Zeroize.Arm.verified (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide)
    (by decide) hd zeroize_stack (Nat.zero_le _)
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
theorem decaps1024_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.decaps1024BodyContract abi 8))
    (hd : armStack body ≤ 8)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.decaps1024BodyContract abi 24).pre s) :
    Verified target (Impl.MlKem.Arm.Wipe.wiped .r3 49152 "vg_mlkem1024_decaps" body) (Scrubbed.decaps1024Contract abi 24) :=
  Verified.callWipe' (ps₁ := Spec.MlKem1024.decapsSig.params.dropLast) (ps₂ := []) (i := 3) (stack := 8) h Proof.Zeroize.Arm.verified
    (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) hd zeroize_stack (Nat.zero_le _)
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

/-! ## The stack the functions use: their callees' frames, at most 8 bytes -/

theorem keyGen_stack : armStack Impl.MlKem.Arm.keygen ≤ 8 := by decide
theorem encapsH_stack : armStack Impl.MlKem.Arm.encapsH ≤ 8 := by decide
theorem encaps_stack : armStack Impl.MlKem.Arm.encaps ≤ 8 := by decide
theorem decaps_stack : armStack Impl.MlKem.Arm.decaps ≤ 8 := by decide
theorem keyGen1024_stack : armStack Impl.MlKem1024.Arm.keygen1024 ≤ 8 := by decide
theorem encapsH1024_stack : armStack Impl.MlKem1024.Arm.encapsH1024 ≤ 8 := by decide
theorem encaps1024_stack : armStack Impl.MlKem1024.Arm.encaps1024 ≤ 8 := by decide
theorem decaps1024_stack : armStack Impl.MlKem1024.Arm.decaps1024 ≤ 8 := by decide

/-! ## The states satisfying the preconditions, with the frames' bytes of stack -/

theorem keyGen_sat : ∃ s, (Proof.MlKem.Scrubbed.keyGenBodyContract abi 24).pre s := by
  refine ⟨Proof.MlKem.Arm.KeyGen.satState, ?_⟩
  sig_sat_check [Proof.MlKem.Scrubbed.keyGenBodyContract, Spec.MlKem.keyGenSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]

theorem encaps_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsBodyContract abi 32).pre s := by
  refine ⟨Proof.MlKem.Arm.Encaps.satState, ?_⟩
  sig_sat_check [Proof.MlKem.Scrubbed.encapsBodyContract, Spec.MlKem.encapsSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]

/-- The state `w`, `satStateH n ctLen scr`, satisfies `encapsH`'s
precondition, after `sig_apply_check`: `H(ek)` is at `h` (`hMem_h_of`). -/
macro "wipe_satH " w:term:max n:num " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (sig_apply_check
   · decide +kernel
   · sig_reduce [$ls,*]
     sig_and_intros
     all_goals first
       | (show Spec.Sha3.bytesAt ($w).mem (0x2000 : BitVec 64) 32 =
             Spec.MlKem.H (Spec.Sha3.bytesAt ($w).mem (0x1000 : BitVec 64) $n)
          exact VG.Proof.MlKem.hMem_h_of (by decide) Proof.MlKem.Arm.Encaps.satStateH_mem)
       | (fail_if_success show Spec.Sha3.bytesAt _ _ _ = _
          decide +kernel)))

theorem encapsH_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsHBodyContract abi 32).pre s := by
  refine ⟨Proof.MlKem.Arm.Encaps.satStateH 1184 1088 32768, ?_⟩
  wipe_satH (Proof.MlKem.Arm.Encaps.satStateH 1184 1088 32768) 1184 [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]

theorem decaps_sat : ∃ s, (Proof.MlKem.Scrubbed.decapsBodyContract abi 24).pre s := by
  refine ⟨Proof.MlKem.Arm.Decaps.satState, ?_⟩
  sig_sat_check [Proof.MlKem.Scrubbed.decapsBodyContract, Spec.MlKem.decapsSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]

theorem keyGen1024_sat : ∃ s, (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi 24).pre s := by
  refine ⟨Proof.MlKem1024.Arm.KeyGen.satState, ?_⟩
  sig_sat_check [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]

theorem encaps1024_sat : ∃ s, (Proof.MlKem.Scrubbed.encaps1024BodyContract abi 32).pre s := by
  refine ⟨Proof.MlKem1024.Arm.Encaps.satState, ?_⟩
  sig_sat_check [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]

theorem encapsH1024_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi 32).pre s := by
  refine ⟨Proof.MlKem.Arm.Encaps.satStateH 1568 1568 49152, ?_⟩
  wipe_satH (Proof.MlKem.Arm.Encaps.satStateH 1568 1568 49152) 1568 [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]

theorem decaps1024_sat : ∃ s, (Proof.MlKem.Scrubbed.decaps1024BodyContract abi 24).pre s := by
  refine ⟨Proof.MlKem1024.Arm.Decaps.satState, ?_⟩
  sig_sat_check [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]

/-! ## The functions -/

theorem keyGen_scrubbed : Verified target Impl.MlKem.Arm.Wipe.keyGen (Scrubbed.keyGenContract abi 24) :=
  keyGen_wipe Proof.MlKem.Arm.KeyGen.verified keyGen_stack keyGen_sat

theorem keyGen_verified : Verified target Impl.MlKem.Arm.Wipe.keyGen (Spec.MlKem.keyGenContract abi 24) :=
  keyGen_scrubbed

theorem encapsH_scrubbed : Verified target Impl.MlKem.Arm.Wipe.encapsH (Scrubbed.encapsHContract abi 32) :=
  encapsH_wipe Proof.MlKem.Arm.Encaps.verifiedH encapsH_stack encapsH_sat

theorem encapsH_verified : Verified target Impl.MlKem.Arm.Wipe.encapsH (Spec.MlKem.encapsHContract abi 32) :=
  encapsH_scrubbed

theorem encaps_scrubbed : Verified target Impl.MlKem.Arm.Wipe.encaps (Scrubbed.encapsContract abi 32) :=
  encaps_wipe Proof.MlKem.Arm.Encaps.verified encaps_stack encaps_sat

theorem encaps_verified : Verified target Impl.MlKem.Arm.Wipe.encaps (Spec.MlKem.encapsContract abi 32) :=
  encaps_scrubbed

theorem decaps_scrubbed : Verified target Impl.MlKem.Arm.Wipe.decaps (Scrubbed.decapsContract abi 24) :=
  decaps_wipe Proof.MlKem.Arm.Decaps.verified decaps_stack decaps_sat

theorem decaps_verified : Verified target Impl.MlKem.Arm.Wipe.decaps (Spec.MlKem.decapsContract abi 24) :=
  decaps_scrubbed

theorem keyGen1024_scrubbed :
    Verified target Impl.MlKem.Arm.Wipe.keyGen1024 (Scrubbed.keyGen1024Contract abi 24) :=
  keyGen1024_wipe Proof.MlKem1024.Arm.KeyGen.verified keyGen1024_stack keyGen1024_sat

theorem keyGen1024_verified :
    Verified target Impl.MlKem.Arm.Wipe.keyGen1024 (Spec.MlKem1024.keyGenContract abi 24) :=
  keyGen1024_scrubbed

theorem encapsH1024_scrubbed :
    Verified target Impl.MlKem.Arm.Wipe.encapsH1024 (Scrubbed.encapsH1024Contract abi 32) :=
  encapsH1024_wipe Proof.MlKem1024.Arm.Encaps.verifiedH encapsH1024_stack encapsH1024_sat

theorem encapsH1024_verified :
    Verified target Impl.MlKem.Arm.Wipe.encapsH1024 (Spec.MlKem1024.encapsHContract abi 32) :=
  encapsH1024_scrubbed

theorem encaps1024_scrubbed :
    Verified target Impl.MlKem.Arm.Wipe.encaps1024 (Scrubbed.encaps1024Contract abi 32) :=
  encaps1024_wipe Proof.MlKem1024.Arm.Encaps.verified encaps1024_stack encaps1024_sat

theorem encaps1024_verified :
    Verified target Impl.MlKem.Arm.Wipe.encaps1024 (Spec.MlKem1024.encapsContract abi 32) :=
  encaps1024_scrubbed

theorem decaps1024_scrubbed :
    Verified target Impl.MlKem.Arm.Wipe.decaps1024 (Scrubbed.decaps1024Contract abi 24) :=
  decaps1024_wipe Proof.MlKem1024.Arm.Decaps.verified decaps1024_stack decaps1024_sat

theorem decaps1024_verified :
    Verified target Impl.MlKem.Arm.Wipe.decaps1024 (Spec.MlKem1024.decapsContract abi 24) :=
  decaps1024_scrubbed

end VG.Proof.MlKem.Arm.Wipe
