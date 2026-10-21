module

public import VerifiedGarbage.Spec.MlKem.EncapsH
public import VerifiedGarbage.Proof.MlKem.X86_64.EkFusedCT16
public import VerifiedGarbage.Proof.MlKem.X86_64.Dc16Dec
public import VerifiedGarbage.Proof.MlKem.X86_64.EcTop16
import VerifiedGarbage.Proof.MlKem.X86_64.EkTop
import VerifiedGarbage.Proof.MlKem.X86_64.Sel16
import VerifiedGarbage.Proof.MlKem.X86_64.EkSel16
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeOk
import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA16
public import VerifiedGarbage.Proof.MlKem.X86_64.KgH16Sel
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgH16Sel
import VerifiedGarbage.Proof.MlKem.X86_64.KgNttV
import VerifiedGarbage.Proof.MlKem.X86_64.KgRowV
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
meta import VerifiedGarbage.Spec.MlKem.EncapsH
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkFusedCT16
meta import VerifiedGarbage.Proof.MlKem.X86_64.Dc16Dec
meta import VerifiedGarbage.Proof.MlKem.X86_64.EcTop16
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.Sel16
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkSel16
import VerifiedGarbage.Proof.MlKem.X86_64.DjSel16
public import VerifiedGarbage.Proof.MlKem.X86_64.DjFusedCT16
meta import VerifiedGarbage.Proof.MlKem.X86_64.DjFrag16
meta import VerifiedGarbage.Proof.MlKem.X86_64.DjFused16
meta import VerifiedGarbage.Proof.MlKem.X86_64.DjFusedCT16
meta import VerifiedGarbage.Proof.MlKem.X86_64.DjSel16
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeOk
public import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeOk
meta import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA16
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgH16Base

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
theorem djFWf768 : DjF16.DjFWf kem768w := by kem_wf dc16Wf768
theorem djHWf768 : DjF16.DjHWf kem768w := by kem_wf djFWf768

/-- The taint checks of the pieces of the decapsulation hashing `z ‖ c` in the fragments. -/
theorem djtWf768 : DjF16.DjTWf kem768w where
  rbpIn := by decide
  zT := ⟨_, by taint_decide⟩
  jT := by
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 := by rw [show Encaps.nb kem768w.L = 3 by decide] at hi; omega
    rcases this with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  kT := ⟨_, by taint_decide⟩
  ij := by decide +kernel

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

/-- The halves of K-PKE key generation of ML-KEM-768, safe to call. -/
theorem kgRows768 : KgRowsOk kem768w.L where
  ntt := ⟨kgNtt768_correct, kgNtt768_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩
  row := ⟨kgRow768_correct, kgRow768_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩

theorem kgH16Wf768 : KeyGenH.KgH16Wf kem768w :=
  { kgWf768.toKgWfB with
    k3 := by decide, ek := by decide, pr := by decide +kernel, se := by decide +kernel, nt := by decide +kernel,
    hz := by decide +kernel, c0 := by decide +kernel, sd0 := by decide +kernel, sm0 := by decide +kernel,
    cP := by decide +kernel, cp := by decide +kernel, sd := by decide +kernel, sm := by decide +kernel,
    rw := by decide +kernel, flg := by decide +kernel, tS := by decide +kernel, tC := by decide +kernel,
    tH := by decide +kernel }

/-- The taint checks of the pieces of key generation hashing `ek` in the rows. -/
theorem kgH16T768 : KeyGenH.KgH16T kem768w where
  zT := ⟨_, by taint_decide⟩
  cT := by
    intro i hi h0
    have : i = 1 ∨ i = 2 := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · exact absurd rfl h0
      · exact .inl rfl
      · exact .inr rfl
    rcases this with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  sT := ⟨_, by taint_decide⟩
  pT := ⟨_, by taint_decide⟩

theorem keyGen_verified (v : Sample4Impl) :
    Verified X86_64.target (Impl.MlKem.X86_64.keyGen v.callee) (Spec.MlKem.keyGenContract X86_64.abi 32) :=
  keyGenHSel_verified kgRows768 v kgH16Wf768 kgH16T768 kpke768 kg16Wf768 kgWf768 keyGenImp768
    (fun b p B P => by kgh_ctl v b p B P kgRows768) (fun _ c S => by s16_ctl v c S kpke768) (by s4_ctl v)

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
  decapsSel_verified (n := kem768.scr) (Nat.le_refl _) kpke768 v djHWf768 djtWf768 dcWf768 calls768 decapsImp768
    (fun _ c b S B => by ek16_ctl v c b S B kpke768) (by s4_ctl v)

end VG.Proof.MlKem.X86_64
