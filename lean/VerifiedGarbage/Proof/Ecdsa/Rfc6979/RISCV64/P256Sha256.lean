module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.CT
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P256
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha256
public import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Common
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Order.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.CT
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P256
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha256
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Order.Lit

/-!
# Deterministic ECDSA over P-256 with HMAC-SHA-256 on RISC-V

The instance for the generic proof (`pack`, with P-256's group law `hL`,
which the registration file supplies), the taint checks of its pieces
(`checks`), which the kernel evaluates, and the shared contract's implying
`rfcR` (`implies`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64.P256Sha256

open VG VG.RISCV64 VG.Impl.Ecdsa.Rfc6979.RISCV64
open VG.Proof.Hmac.Stream.RISCV64.Sha256Family (hash256 ok256)

/-- The code's configuration. -/
def cfg : Cfg where
  H := hash256
  hiN := Spec.Hmac.sha256I.initAnyKeyApi.name
  hfN := Spec.Hmac.sha256I.finalizeApi.name
  FN := Impl.Ecdsa.RISCV64.p256Order
  coreN := "vg_ecdsa_p256_sign"
  coreC := Impl.Ecdsa.RISCV64.Sign.signP256
  tries := 8
  nw := 4

/-- The instance, for P-256's group law `hL`. -/
def pack (hL : VG.Proof.Weierstrass.Law Spec.P256.curve) : Rfc where
  c := cfg
  hH := ok256
  hiCt := Proof.Hmac.Stream.RISCV64.Sha256.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Sha256.fin_ct
  I := Spec.Ecdsa.Rfc6979.P256Sha256.inst
  kit := P256.kit hL
  hE := rfl
  hHash := rfl
  hD := rfl
  hnw := rfl
  hDQ := (by decide : 8 * 4 ≤ cfg.H.D)
  hD48 := by decide
  hS := by decide
  hct := rfl
  hT := by decide
  hT' := by decide
  hFN := rfl
  hcC := rfl

theorem checks : Checks cfg := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, trivial⟩, ⟨?_, trivial⟩, ⟨?_, trivial⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩ <;> refine ⟨?_, ?_⟩
  taint_decide_all

/-- The stack the function uses: its frame and its callees'. -/
theorem stack_eq (hL : VG.Proof.Weierstrass.Law Spec.P256.curve) : (pack hL).N = 544 := by
  simp only [Rfc.N, Rfc.X, pack, cfg, Cfg.frB, Cfg.Q, hash256, Impl.Hmac.Stream.RISCV64.Hash.ibytes,
    Impl.Hmac.Stream.RISCV64.Hash.fbytes, Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso,
    Impl.Hmac.Stream.RISCV64.Hash.S, Impl.Hmac.Stream.RISCV64.Hash.B, fH]
  decide

theorem implies :
    (rfcR Spec.Ecdsa.Rfc6979.P256Sha256.inst 544).Implies
      (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract RISCV64.abi 544) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          RISCV64.abi, RISCV64.argRegs, rfcR]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          RISCV64.abi, RISCV64.argRegs, rfcR]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          RISCV64.abi, RISCV64.argRegs, rfcR] at h
        obtain ⟨hsp, hl, h3, h4, h5, h6⟩ := h
        exact ⟨hsp, h3, h4, h5, h6, (List.cons.inj hl).1⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          RISCV64.abi, RISCV64.argRegs, rfcR] [satState 32 32] using satState 32 32 }

/-- A state satisfying the precondition with the comb's table. -/
def satC : State :=
  { (satState 32 32) with
    mem := VG.Proof.Ecdsa.RISCV64.Comb.combSatMem
    rd := (satState 32 32).rd ++ [⟨0x100000, 151552⟩]
    syms := fun _ => 0x100000 }

theorem sat : (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.p256CombConsts) 544).pre satC := by
  have hl := VG.Proof.Ecdsa.RISCV64.Comb.combWords_length
  have held := VG.Proof.Ecdsa.RISCV64.Comb.combSatMem_held
  rw [show Impl.Ecdsa.RISCV64.Comb.p256CombConsts =
    [(Impl.Ecdsa.RISCV64.Comb.p256Sym, Impl.Ecdsa.RISCV64.Comb.p256CombWords)] from rfl]
  generalize Impl.Ecdsa.RISCV64.Comb.p256CombWords = W' at hl held ⊢
  generalize e : satC = s
  sig_pre [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
    Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
    RISCV64.abi, RISCV64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | (intro r hr
       change r ∈ [⟨0x1000, 2 * 32⟩, ⟨0x8000, 8192⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

theorem sign_verified (hL : VG.Proof.Weierstrass.Law Spec.P256.curve) :
    Verified RISCV64.target (pack hL).c.sign (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.p256CombConsts) 544) :=
  RISCV64.sign_verified (P := pack hL) checks (stack_eq hL) (rfcRC_implies implies ⟨satC, sat⟩)

end VG.Proof.Ecdsa.Rfc6979.RISCV64.P256Sha256
