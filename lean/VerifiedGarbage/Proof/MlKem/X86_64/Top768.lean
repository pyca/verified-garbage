module

import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
public import VerifiedGarbage.Proof.MlKem.X86_64.EcTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.EcTop
public import VerifiedGarbage.Proof.MlKem.X86_64.DcTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.DcTop
public import VerifiedGarbage.Spec.MlKem.EncapsH
meta import VerifiedGarbage.Spec.MlKem.EncapsH
public import VerifiedGarbage.Proof.MlKem.X86_64.EkTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkTop
public import VerifiedGarbage.Proof.MlKem.X86_64.Sel16
public import VerifiedGarbage.Proof.MlKem.X86_64.EkSel16
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkSel16
public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeOk
public import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
meta import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
meta import Mathlib.Tactic.Conv
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes

/-!
# ML-KEM-768 on x86-64: `vg_mlkem768_keygen`, `vg_mlkem768_encaps_h` and `vg_mlkem768_decaps`

The proofs for any parameter set (`KgTop.lean`, `EcTop.lean`, `DcTop.lean`)
for ML-KEM-768 (`kem768`): its layout passes their checks, evaluated here,
it calls `vg_mlkem_compress_encode` and `vg_mlkem_decode_decompress` for its
widths, and the shared contracts imply the contracts the proofs are written
against.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem kemWf768 : KemWf kem768 := by kem_wf

theorem kgWf768 : KeyGen.KgWf kem768 := by kem_wf kemWf768
theorem ecWf768 : Encaps.EcWf kem768 := by kem_wf kemWf768
theorem dcWf768 : Decaps.DcWf kem768 := by kem_wf kemWf768
theorem kpke768 : KpkeOk kem768w.L := KpkeOk.k768
theorem kg16Wf768 : KeyGen16.Kg16Wf kem768w := by kem_wf kemWf768
theorem ec16Wf768 : Encaps16.Ec16Wf kem768w := by kem_wf kemWf768
theorem dc16Wf768 : Decaps16.Dc16Wf kem768w := by kem_wf kemWf768
theorem ekWf768 : Ek.EkWf kem768 := by kem_wf ecWf768

theorem ek16FWf768 : EkF16.Ek16FWf kem768w := by kem_wf ec16Wf768.toEcWfB
theorem ek16HWf768 : EkF16.Ek16HWf kem768w := by kem_wf ek16FWf768

/-- The taint checks of the fused encapsulation's pieces, with 16-bit polynomials. -/
theorem ekt16Wf768 : EkF16.EkT16Wf kem768w where
  rT := ⟨_, by taint_decide⟩
  zT := ⟨_, by taint_decide⟩
  hT := by
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 := by rw [show Encaps.nb kem768w.L = 3 by decide] at hi; omega
    rcases this with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  hcT := ⟨_, by taint_decide⟩
  ij := by decide +kernel

/-- The compressions it calls. -/
theorem calls768 : KemCalls kem768 compressWidths compressWidths := ⟨Codecs.ceI, Codecs.ddI, by decide, by decide⟩

/-- States satisfying the shared contracts' preconditions. -/
def keyGenSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x10000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1184⟩, ⟨0x3000, 2400⟩, ⟨0x10000, 32768⟩]

def decapsSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x10000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 2400⟩, ⟨0x2000, 1088⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 32768⟩]

/-- The shared contract of `keyGen`, from the contract its proofs are written against. -/
theorem keyGenImp768 : (keyGenK kem768).Implies (Spec.MlKem.keyGenContract X86_64.abi 32) :=
    { pre := by sig_implies_pre [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, keyGenK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      post := by sig_implies_post [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, keyGenK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, keyGenK, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, keyGenK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768] [keyGenSat]
        using keyGenSat }

theorem keyGen_verified (v : Sample4Impl) :
    Verified X86_64.target (Impl.MlKem.X86_64.keyGen v.callee) (Spec.MlKem.keyGenContract X86_64.abi 32) :=
  keyGenSel_verified (n := kem768.scr) (Nat.le_refl _) kpke768 v kg16Wf768 kgWf768 keyGenImp768
    (fun _ c S => by s16_ctl v c S kpke768) (by s4_ctl v)

/-- The shared contract of `encapsH`, from the contract its proofs are written against. -/
theorem encapsHImp768 : (encapsK kem768).Implies (Spec.MlKem.encapsHContract X86_64.abi 32) :=
    { pre := by sig_implies_pre [Spec.MlKem.encapsHContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, encapsK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      post := by sig_implies_post [Spec.MlKem.encapsHContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, encapsK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem.encapsHContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, encapsK, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx, h8, h9⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp, map_toNat_inj hb⟩
      sat := by
        refine ⟨encapsHSat 1184 1088 32768, ?_⟩
        sig_pre [Spec.MlKem.encapsHContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, encapsK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
        sig_and_intros
        all_goals first
          | exact encapsHSat_h (ekLen := 1184) (ctLen := 1088) (scr := 32768) (by decide)
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide) }

theorem encapsH_verified (v : Sample4Impl) :
    Verified X86_64.target (Impl.MlKem.X86_64.encapsH v.callee) (Spec.MlKem.encapsHContract X86_64.abi 32) :=
  encapsHSel_verified (n := kem768.scr) (Nat.le_refl _) kpke768 v ec16Wf768 ecWf768 calls768 encapsHImp768
    (fun _ c S => by s16_ctl v c S kpke768) (by s4_ctl v)

theorem encaps_ctl (v : Sample4Impl) : ctlOk (kemEncaps kem768 v.callee) = true := by
  s4_ctl v

/-- The shared contract of `encaps`, from the contract its proofs are written against. -/
theorem encapsImp768 : (encK kem768).Implies (Spec.MlKem.encapsContract X86_64.abi 32) :=
    { pre := by sig_implies_pre [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, encK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      post := by sig_implies_post [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, encK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, encK, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx, h8⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, h8, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, encK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768] [encapsSat]
        using encapsSat 1184 1088 32768 }

theorem encaps_verified (v : Sample4Impl) :
    Verified X86_64.target (Impl.MlKem.X86_64.encaps v.callee) (Spec.MlKem.encapsContract X86_64.abi 32) :=
  encapsSel_verified (n := kem768.scr) (Nat.le_refl _) kpke768 v ek16HWf768 ekt16Wf768 ekWf768 calls768 encapsImp768
    (fun _ c b S B => by ek16_ctl v c b S B kpke768) (encaps_ctl v)

/-- The shared contract of `decaps`, from the contract its proofs are written against. -/
theorem decapsImp768 : (decapsK kem768).Implies (Spec.MlKem.decapsContract X86_64.abi 32) :=
    { pre := by sig_implies_pre [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, decapsK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      post := by sig_implies_post [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, decapsK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, decapsK, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, decapsK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768] [decapsSat]
        using decapsSat }

theorem decaps_verified (v : Sample4Impl) :
    Verified X86_64.target (Impl.MlKem.X86_64.decaps v.callee) (Spec.MlKem.decapsContract X86_64.abi 32) :=
  decapsSel_verified (n := kem768.scr) (Nat.le_refl _) kpke768 v dc16Wf768 dcWf768 calls768 decapsImp768
    (fun _ c S => by s16_ctl v c S kpke768) (by s4_ctl v)

end VG.Proof.MlKem.X86_64
