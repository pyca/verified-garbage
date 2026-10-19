module

import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
public import VerifiedGarbage.Proof.MlKem.X86_64.EcTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.EcTop
public import VerifiedGarbage.Proof.MlKem.X86_64.DcTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.DcTop
import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncode
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncodeAvx2
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncodeAvx2
public import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompressAvx2
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompressAvx2
public import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem
public import VerifiedGarbage.Proof.MlKem1024.X86_64.Calls
meta import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.Calls
public import VerifiedGarbage.Spec.MlKem.Contract1024
meta import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Spec.MlKem.EncapsH
meta import VerifiedGarbage.Spec.MlKem.EncapsH
public import VerifiedGarbage.Proof.MlKem.X86_64.EkTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkTop
public import VerifiedGarbage.Proof.MlKem.X86_64.Sel16
public import VerifiedGarbage.Proof.MlKem.X86_64.EkSel16
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkSel16
public import VerifiedGarbage.Proof.MlKem1024.X86_64.KpkeOk
public import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
meta import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
meta import Mathlib.Tactic.Conv
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_keygen`, `vg_mlkem1024_encaps_h` and `vg_mlkem1024_decaps`

The proofs for any parameter set (`Proof/MlKem/X86_64/KgTop.lean`,
`EcTop.lean`, `DcTop.lean`) for ML-KEM-1024 (`kem1024`): its layout passes
their checks, evaluated here, it calls `vg_mlkem1024_compress_encode` and
`vg_mlkem1024_decode_decompress` for its widths (or their AVX2
implementations, with the codecs `Codecs.avx2` of its other primitives), and
the shared contracts imply the contracts the proofs are written against.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem

theorem kemWf1024 : KemWf kem1024 := by kem_wf

theorem kgWf1024 : KeyGen.KgWf kem1024 := by kem_wf kemWf1024
theorem ecWf1024 : Encaps.EcWf kem1024 := by kem_wf kemWf1024
theorem dcWf1024 : Decaps.DcWf kem1024 := by kem_wf kemWf1024
theorem kpke1024 : KpkeOk kem1024w.L := KpkeOk.k1024
theorem kg16Wf1024 : KeyGen16.Kg16Wf kem1024w := by kem_wf kemWf1024
theorem ec16Wf1024 : Encaps16.Ec16Wf kem1024w := by kem_wf kemWf1024
theorem dc16Wf1024 : Decaps16.Dc16Wf kem1024w := by kem_wf kemWf1024
theorem ekWf1024 : Ek.EkWf kem1024 := by kem_wf ecWf1024

theorem ek16FWf1024 : EkF16.Ek16FWf kem1024w := by kem_wf ec16Wf1024.toEcWfB
theorem ek16HWf1024 : EkF16.Ek16HWf kem1024w := by kem_wf ek16FWf1024

/-- The taint checks of the fused encapsulation's pieces, with 16-bit polynomials. -/
theorem ekt16Wf1024 : EkF16.EkT16Wf kem1024w where
  rT := ⟨_, by taint_decide⟩
  zT := ⟨_, by taint_decide⟩
  hT := by
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by rw [show Encaps.nb kem1024w.L = 4 by decide] at hi; omega
    rcases this with rfl | rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  hcT := ⟨_, by taint_decide⟩
  ij := by decide +kernel

theorem ce1024_ctl : ∀ cs : Codecs, ctlOk (ce1024 cs) = true
  | .base => by decide +kernel
  | .avx2 => by decide +kernel

theorem dd1024_ctl : ∀ cs : Codecs, ctlOk (dd1024 cs) = true
  | .base => by decide +kernel
  | .avx2 => by decide +kernel

theorem ce1024_sp : ∀ cs : Codecs, (ce1024 cs).all (fun i => !isa.writesSp i) = true
  | .base => Code.all_of_allInstrs (by decide +kernel)
  | .avx2 => Code.all_of_allInstrs (by decide +kernel)

theorem dd1024_sp : ∀ cs : Codecs, (dd1024 cs).all (fun i => !isa.writesSp i) = true
  | .base => Code.all_of_allInstrs (by decide +kernel)
  | .avx2 => Code.all_of_allInstrs (by decide +kernel)

/-- States satisfying the shared contracts' preconditions. -/
def keyGen1024Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x10000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1568⟩, ⟨0x3000, 3168⟩, ⟨0x10000, 49152⟩]

def decaps1024Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x10000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 3168⟩, ⟨0x2000, 1568⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 49152⟩]

/-- The shared contract of `keyGen1024`, from the contract its proofs are written against. -/
theorem keyGenImp1024 : (keyGenK kem1024).Implies (Spec.MlKem1024.keyGenContract X86_64.abi 32) :=
    { pre := by sig_implies_pre [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, keyGenK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024]
      post := by sig_implies_post [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, keyGenK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, keyGenK, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, keyGenK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024] [keyGen1024Sat]
        using keyGen1024Sat }

theorem keyGen1024_verified (v : Sample4Impl) :
    Verified X86_64.target (keyGen1024 v.callee) (Spec.MlKem1024.keyGenContract X86_64.abi 32) :=
  keyGenSel_verified kpke1024 v kg16Wf1024 kgWf1024 keyGenImp1024
    (fun _ c S => by s16_ctl v c S kpke1024)
    (by s4_ctl v; all_goals first | exact ce1024_ctl _ | exact dd1024_ctl _)

/-- The shared contract of `encapsH1024`, from the contract its proofs are written against. -/
theorem encapsHImp1024 : (encapsK kem1024).Implies (Spec.MlKem1024.encapsHContract X86_64.abi 32) :=
    { pre := by sig_implies_pre [Spec.MlKem1024.encapsHContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, encapsK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024]
      post := by sig_implies_post [Spec.MlKem1024.encapsHContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, encapsK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem1024.encapsHContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, encapsK, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx, h8, h9⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp, map_toNat_inj hb⟩
      sat := by
        refine ⟨encapsHSat 1568 1568 49152, ?_⟩
        sig_pre [Spec.MlKem1024.encapsHContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, encapsK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024]
        sig_and_intros
        all_goals first
          | exact encapsHSat_h (ekLen := 1568) (ctLen := 1568) (scr := 49152) (by decide)
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide) }

theorem encapsH1024_verified (v : Sample4Impl) :
    Verified X86_64.target (encapsH1024 v.callee) (Spec.MlKem1024.encapsHContract X86_64.abi 32) :=
  encapsHSel_verified kpke1024 v ec16Wf1024 ecWf1024 calls1024 encapsHImp1024
    (fun _ c S => by s16_ctl v c S kpke1024)
    (by s4_ctl v; all_goals first | exact ce1024_ctl _ | exact dd1024_ctl _)

theorem encaps1024_ctl (v : Sample4Impl) : ctlOk (kemEncaps kem1024 v.callee) = true := by
  s4_ctl v
  all_goals first | exact ce1024_ctl _ | exact dd1024_ctl _

/-- The shared contract of `encaps1024`, from the contract its proofs are written against. -/
theorem encapsImp1024 : (encK kem1024).Implies (Spec.MlKem1024.encapsContract X86_64.abi 32) :=
    { pre := by sig_implies_pre [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, encK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024]
      post := by sig_implies_post [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, encK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, encK, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx, h8⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, h8, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, encK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024] [encapsSat]
        using encapsSat 1568 1568 49152 }

theorem encaps1024_verified (v : Sample4Impl) :
    Verified X86_64.target (encaps1024 v.callee) (Spec.MlKem1024.encapsContract X86_64.abi 32) :=
  encapsSel_verified kpke1024 v ek16HWf1024 ekt16Wf1024 ekWf1024 calls1024 encapsImp1024
    (fun _ c b S B => by ek16_ctl v c b S B kpke1024) (encaps1024_ctl v)

/-- The shared contract of `decaps1024`, from the contract its proofs are written against. -/
theorem decapsImp1024 : (decapsK kem1024).Implies (Spec.MlKem1024.decapsContract X86_64.abi 32) :=
    { pre := by sig_implies_pre [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, decapsK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024]
      post := by sig_implies_post [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, decapsK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, decapsK, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, decapsK, X86_64.abi, VG.X86_64.argRegs, kem1024, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem1024] [decaps1024Sat]
        using decaps1024Sat }

theorem decaps1024_verified (v : Sample4Impl) :
    Verified X86_64.target (decaps1024 v.callee) (Spec.MlKem1024.decapsContract X86_64.abi 32) :=
  decapsSel_verified kpke1024 v dc16Wf1024 dcWf1024 calls1024 decapsImp1024
    (fun _ c S => by s16_ctl v c S kpke1024)
    (by s4_ctl v; all_goals first | exact ce1024_ctl _ | exact dd1024_ctl _)

end VG.Proof.MlKem1024.X86_64
