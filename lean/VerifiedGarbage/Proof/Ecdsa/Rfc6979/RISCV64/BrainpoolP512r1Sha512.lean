module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.CT
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP512r1
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512
public import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Common
import VerifiedGarbage.Proof.Weierstrass.RISCV64.BrainpoolP512r1Order.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.CT
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP512r1
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.BrainpoolP512r1Order.Lit

/-!
# Deterministic ECDSA over brainpoolP512r1 with HMAC-SHA-512 on RISC-V

The instance for the generic proof (`pack`, with brainpoolP512r1's group law `hL`,
which the registration file supplies), the taint checks of its pieces
(`checks`), which the kernel evaluates, and the shared contract's implying
`rfcR` (`implies`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP512r1Sha512

open VG VG.RISCV64 VG.Impl.Ecdsa.Rfc6979.RISCV64

/-- The code's configuration. -/
def cfg : Cfg where
  H := Proof.Hmac.Stream.RISCV64.Sha512.hash
  hiN := Spec.Hmac.sha512I.initAnyKeyApi.name
  hfN := Spec.Hmac.sha512I.finalizeApi.name
  FN := Impl.Ecdsa.RISCV64.brainpoolp512r1Order
  coreN := "vg_ecdsa_brainpoolp512r1_sign"
  coreC := Impl.Ecdsa.RISCV64.signBrainpoolP512r1
  tries := 128
  nw := 8

/-- The instance, for brainpoolP512r1's group law `hL`. -/
def pack (hL : VG.Proof.Weierstrass.Law Spec.BrainpoolP512r1.curve) : Rfc where
  c := cfg
  hH := Proof.Hmac.Stream.RISCV64.Sha512.ok
  hiCt := Proof.Hmac.Stream.RISCV64.Sha512.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Sha512.fin_ct
  I := Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst
  kit := BrainpoolP512r1.kit hL
  hE := rfl
  hHash := rfl
  hD := rfl
  hnw := rfl
  hQ := rfl
  hG := rfl
  hsh := fun _ => rfl
  hQD := (by decide : 64 ≤ cfg.H.D + 8)
  hD64 := by decide
  hS := by decide
  hct := rfl
  hT := by decide
  hT' := by decide
  hFN := rfl
  hcC := rfl

theorem checks : Checks cfg := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, trivial⟩, ⟨?_, trivial⟩, ⟨?_, trivial⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ⟨?_, trivial⟩, ?_⟩ <;> refine ⟨?_, ?_⟩
  taint_decide_all

/-- The stack the function uses: its frame and its callees'. -/
theorem stack_eq (hL : VG.Proof.Weierstrass.Law Spec.BrainpoolP512r1.curve) : (pack hL).N = 784 := by
  simp only [Rfc.N, Rfc.X, pack, cfg, Cfg.frB, Proof.Hmac.Stream.RISCV64.Sha512.hash,
    Proof.Hmac.Stream.RISCV64.Sha512Family.hash, Impl.Hmac.Stream.RISCV64.Hash.ibytes,
    Impl.Hmac.Stream.RISCV64.Hash.fbytes, Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso,
    Impl.Hmac.Stream.RISCV64.Hash.S, Impl.Hmac.Stream.RISCV64.Hash.B, Cfg.fH, Nat.reduceLT, ↓reduceIte]
  decide

theorem implies :
    (rfcR Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst 784).Implies
      (Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst.signContract RISCV64.abi 784) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.BrainpoolP512r1.inst, Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords,
          RISCV64.abi, RISCV64.argRegs, rfcR]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.BrainpoolP512r1.inst, Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords,
          RISCV64.abi, RISCV64.argRegs, rfcR]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.BrainpoolP512r1.inst, Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords,
          RISCV64.abi, RISCV64.argRegs, rfcR] at h
        obtain ⟨hsp, hl, h3, h4, h5, h6⟩ := h
        exact ⟨hsp, h3, h4, h5, h6, (List.cons.inj hl).1⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.BrainpoolP512r1.inst, Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords,
          RISCV64.abi, RISCV64.argRegs, rfcR] [satState 64 64] using satState 64 64 }

theorem sign_verified (hL : VG.Proof.Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified RISCV64.target (pack hL).c.sign (Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst.signContract RISCV64.abi 784) :=
  RISCV64.sign_verified (P := pack hL) checks (stack_eq hL) (rfcR0_implies implies)

end VG.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP512r1Sha512
