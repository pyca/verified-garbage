module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.CT
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P224
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha224
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P224Sha224
public import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Common
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P224Field.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.CT
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P224
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha224
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P224Sha224
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P224Field.Lit

/-!
# Deterministic ECDSA over P-224 with HMAC-SHA-224 on RISC-V

The instance for the generic proof (`pack`, with P-224's group law `hL`,
which the registration file supplies), the taint checks of its pieces
(`checks`), which the kernel evaluates, and the shared contract's implying
`rfcR` (`implies`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64.P224Sha224

open VG VG.RISCV64 VG.Impl.Ecdsa.Rfc6979.RISCV64
open VG.Proof.Hmac.Stream.RISCV64.Sha256Family (hash224 ok224)

/-- The code's configuration. -/
def cfg : Cfg where
  H := hash224
  hiN := Spec.Hmac.sha224I.initAnyKeyApi.name
  hfN := Spec.Hmac.sha224I.finalizeApi.name
  FN := Impl.Ecdsa.RISCV64.p224Order
  coreN := "vg_ecdsa_p224_sign"
  coreC := Impl.Ecdsa.RISCV64.P224.signP224
  tries := 8
  nw := 4
  Q := 28

/-- The instance, for P-224's group law `hL`. -/
def pack (hL : VG.Proof.Weierstrass.Law Spec.P224.curve) : Rfc where
  c := cfg
  hH := ok224
  hiCt := Proof.Hmac.Stream.RISCV64.Sha224.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Sha224.fin_ct
  I := Spec.Ecdsa.Rfc6979.P224Sha224.inst
  kit := P224.kit hL
  hE := rfl
  hHash := rfl
  hD := rfl
  hnw := rfl
  hQ := rfl
  hDQ := (by decide : 28 ≤ cfg.H.D)
  hD64 := by decide
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
theorem stack_eq (hL : VG.Proof.Weierstrass.Law Spec.P224.curve) : (pack hL).N = 544 := by
  simp only [Rfc.N, Rfc.X, pack, cfg, Cfg.frB, hash224, Impl.Hmac.Stream.RISCV64.Hash.ibytes,
    Impl.Hmac.Stream.RISCV64.Hash.fbytes, Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso,
    Impl.Hmac.Stream.RISCV64.Hash.S, Impl.Hmac.Stream.RISCV64.Hash.B, Cfg.fH, Nat.reduceLT, ↓reduceIte]
  decide

theorem implies :
    (rfcR Spec.Ecdsa.Rfc6979.P224Sha224.inst 544).Implies
      (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract RISCV64.abi 544) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          RISCV64.abi, RISCV64.argRegs, rfcR]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          RISCV64.abi, RISCV64.argRegs, rfcR]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          RISCV64.abi, RISCV64.argRegs, rfcR] at h
        obtain ⟨hsp, hl, h3, h4, h5, h6⟩ := h
        exact ⟨hsp, h3, h4, h5, h6, (List.cons.inj hl).1⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          RISCV64.abi, RISCV64.argRegs, rfcR] [satState 28 28] using satState 28 28 }

/-- A state satisfying the precondition with the comb's table. -/
def satC : State :=
  { (satState 28 28) with
    mem := VG.Proof.Ecdsa.RISCV64.P224.Comb.combSatMem
    rd := (satState 28 28).rd ++ [⟨0x100000, 151552⟩]
    syms := fun _ => 0x100000 }

theorem sat : (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract
    (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.p224CombConsts) 544).pre satC := by
  have hl := VG.Proof.Ecdsa.RISCV64.P224.Comb.combWords_length
  have held := VG.Proof.Ecdsa.RISCV64.P224.Comb.combSatMem_held
  rw [show Impl.Ecdsa.RISCV64.Comb.p224CombConsts =
    [(Impl.Ecdsa.RISCV64.Comb.p224Sym, Impl.Ecdsa.RISCV64.Comb.p224CombWords)] from rfl]
  generalize Impl.Ecdsa.RISCV64.Comb.p224CombWords = W' at hl held ⊢
  generalize e : satC = s
  sig_pre [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
    Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
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
       change r ∈ [⟨0x1000, 2 * 28⟩, ⟨0x8000, 8192⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

theorem sign_verified (hL : VG.Proof.Weierstrass.Law Spec.P224.curve) :
    Verified RISCV64.target (pack hL).c.sign (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract
      (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.p224CombConsts) 544) :=
  RISCV64.sign_verified (P := pack hL) checks (stack_eq hL) (rfcRC_implies implies ⟨satC, sat⟩)

end VG.Proof.Ecdsa.Rfc6979.RISCV64.P224Sha224
