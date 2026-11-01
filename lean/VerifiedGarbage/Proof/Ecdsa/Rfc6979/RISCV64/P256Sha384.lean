module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.CT
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha384
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha384
public import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Common
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Order.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.CT
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha384
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha384
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Order.Lit

/-!
# Deterministic ECDSA over P-256 with HMAC-SHA-384 on RISC-V

The instance for the generic proof (`pack`, with P-256's group law `hL`,
which the registration file supplies), the taint checks of its pieces
(`checks`), which the kernel evaluates, and the shared contract's implying
`rfcR` (`implies`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64.P256Sha384

open VG VG.RISCV64 VG.Impl.Ecdsa.Rfc6979.RISCV64

/-- The code's configuration. -/
def cfg : Cfg where
  H := Proof.Hmac.Stream.RISCV64.Sha384.hash
  hiN := Spec.Hmac.sha384I.initAnyKeyApi.name
  hfN := Spec.Hmac.sha384I.finalizeApi.name
  FN := Impl.Ecdsa.RISCV64.p256Order
  coreN := Spec.Ecdsa.P256.signApi.name
  coreC := Impl.Ecdsa.RISCV64.Sign.signP256
  tries := 8

/-- The instance, for P-256's group law `hL`. -/
def pack (hL : VG.Proof.Weierstrass.Law Spec.P256.curve) : Rfc where
  c := cfg
  hH := Proof.Hmac.Stream.RISCV64.Sha384.ok
  hiCt := Proof.Hmac.Stream.RISCV64.Sha384.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Sha384.fin_ct
  I := Spec.Ecdsa.Rfc6979.P256Sha384.inst
  hE := rfl
  hHash := rfl
  hD := rfl
  hD32 := by decide
  hD48 := by decide
  hS := by decide
  hct := rfl
  hT := by decide
  hT' := by decide
  hFN := rfl
  hcC := rfl
  law := hL

theorem checks : Checks cfg := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, trivial⟩, ⟨?_, trivial⟩, ⟨?_, trivial⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩ <;> refine ⟨?_, ?_⟩
  taint_decide_all

/-- The stack the function uses: its frame and its callees'. -/
theorem stack_eq (hL : VG.Proof.Weierstrass.Law Spec.P256.curve) : (pack hL).N = 720 := by
  simp only [Rfc.N, Rfc.X, pack, cfg, Proof.Hmac.Stream.RISCV64.Sha384.hash,
    Proof.Hmac.Stream.RISCV64.Sha512Family.hash, Impl.Hmac.Stream.RISCV64.Hash.ibytes,
    Impl.Hmac.Stream.RISCV64.Hash.fbytes, Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso,
    Impl.Hmac.Stream.RISCV64.Hash.S, Impl.Hmac.Stream.RISCV64.Hash.B, frB]
  decide

theorem implies :
    (rfcR Spec.Ecdsa.Rfc6979.P256Sha384.inst 720).Implies
      (Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract RISCV64.abi 720) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          RISCV64.abi, RISCV64.argRegs, rfcR]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          RISCV64.abi, RISCV64.argRegs, rfcR]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          RISCV64.abi, RISCV64.argRegs, rfcR] at h
        obtain ⟨hsp, hl, h3, h4, h5, h6⟩ := h
        exact ⟨hsp, h3, h4, h5, h6, (List.cons.inj hl).1⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          RISCV64.abi, RISCV64.argRegs, rfcR] [satState 32 48] using satState 32 48 }

theorem sign_verified (hL : VG.Proof.Weierstrass.Law Spec.P256.curve) :
    Verified RISCV64.target (pack hL).c.sign (Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract RISCV64.abi 720) :=
  RISCV64.sign_verified (P := pack hL) checks (stack_eq hL) implies

end VG.Proof.Ecdsa.Rfc6979.RISCV64.P256Sha384
