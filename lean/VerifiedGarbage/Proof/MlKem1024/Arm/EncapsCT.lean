module
public import VerifiedGarbage.Proof.MlKem.Scrubbed
public import VerifiedGarbage.Proof.MlKem.Arm.Encaps
public import VerifiedGarbage.Impl.MlKem1024.Arm.Top
public import VerifiedGarbage.Spec.MlKem.Contract1024

import VerifiedGarbage.Proof.MlKem.Arm.EncapsCT
import VerifiedGarbage.Proof.MlKem.EncapsHSat
public import VerifiedGarbage.Spec.MlKem.EncapsH
import VerifiedGarbage.Proof.MlKem1024.Arm.Calls
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

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
