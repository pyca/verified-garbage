module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Common
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.Sign
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.SignVerified
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSpec
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSat
import VerifiedGarbage.Proof.Weierstrass.RISCV64.BrainpoolP512r1Order.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Common
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.Sign
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.SignLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.SignVerified
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSpec
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSat
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.BrainpoolP512r1Order.Lit

/-!
# Deterministic ECDSA on RISC-V: brainpoolp512r1's kit

brainpoolP512r1's scalars, the functions of its order, and `vg_ecdsa_brainpoolp512r1_sign`, which
reads no table: its calls against `signRV` (`WP.call`, since it pushes no
frames), from what `CoreArgs` gives.
-/

@[expose] public section

-- `2³⁸⁴ < 2n` is evaluated.
set_option exponentiation.threshold 1024

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP512r1

open VG VG.RISCV64
open VG.Proof.Ecdsa.Rfc6979.RISCV64
open VG.Proof.Ecdsa.RISCV64.BrainpoolP512r1 (signRV sign_rv sign_ct sg)

theorem nBits_brainpoolp512r1 : Spec.Ecdsa.nBits Spec.BrainpoolP512r1.curve = 512 := by
  show Spec.BrainpoolP512r1.curve.n.log2 + 1 = 512
  have h₁ : 511 ≤ Spec.BrainpoolP512r1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP512r1.curve.n.log2 < 512 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

theorem coreArgs_pre {s : State} {o d g k w : Addr} (h : CoreArgs 64 [] s o d g k w) :
    signRV.pre (s.callEntry.withRegions [⟨d, 64⟩, ⟨g, 64⟩, ⟨k, 64⟩] [⟨o, 128⟩, ⟨w, 8192⟩]) := by
  simp only [signRV, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, h.a4]
  exact ⟨trivial, trivial, h.d_ow, h.d_dw, h.d_gw, h.d_kw, h.no, h.nd, h.ng, h.nk, h.nw, h.wa⟩

theorem cov {s : State} {o d g k w : Addr} (h : CoreArgs 64 [] s o d g k w) :
    RISCV64.Covers ([⟨d, 64⟩, ⟨g, 64⟩, ⟨k, 64⟩] ++ [⟨o, 128⟩, ⟨w, 8192⟩]) (s.rd ++ s.wr) := by
  have := h.hc
  simpa [constRegs, Abi.constRegions] using this

theorem core_call {nm : String} {s : State} {o d g k w : Addr}
    (hL : VG.Proof.Weierstrass.Law Spec.BrainpoolP512r1.curve) (h : CoreArgs 64 [] s o d g k w) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨o, 128⟩, ⟨w, 8192⟩] s' →
      (match sg s.mem d g k with
        | some rs => s'.gpr .a0 = 1 ∧ Spec.Sha256.bytesAt s'.mem o 128 = Spec.Ecdsa.encode Spec.BrainpoolP512r1.curve rs
        | none => s'.gpr .a0 = 0 ∧ Spec.Sha256.bytesAt s'.mem o 128 = List.replicate 128 0) → Q s') :
    WP isa (.call nm Impl.Ecdsa.RISCV64.signBrainpoolP512r1) s Q := by
  refine WP.call (k := signRV) (sign_rv hL) (rd := [⟨d, 64⟩, ⟨g, 64⟩, ⟨k, 64⟩]) (wr := [⟨o, 128⟩, ⟨w, 8192⟩])
    (coreArgs_pre h) (cov h) h.hw ?_ Impl.Ecdsa.RISCV64.signBrainpoolP512r1_noFrames
  intro s' hrd hwr hsp' hf hcs _ hpost
  simp only [signRV, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3] at hpost
  exact hQ s' ⟨hrd, hwr, hsp', hcs, hf⟩ hpost

theorem core_rel {nm : String} (hL : VG.Proof.Weierstrass.Law Spec.BrainpoolP512r1.curve) {Q : State → State → Prop}
    {o d g k w : Addr}
    (h : ∀ s s', Q s s' → CoreArgs 64 [] s o d g k w ∧ CoreArgs 64 [] s' o d g k w ∧ s.sp = s'.sp) :
    RelCT isa Q (.call nm Impl.Ecdsa.RISCV64.signBrainpoolP512r1) fun _ _ => True := by
  refine RelCT.call (sign_rv hL) sign_ct [⟨d, 64⟩, ⟨g, 64⟩, ⟨k, 64⟩] [⟨o, 128⟩, ⟨w, 8192⟩] fun s s' hp => ?_
  obtain ⟨a, a', e⟩ := h s s' hp
  refine ⟨coreArgs_pre a, coreArgs_pre a', ?_, cov a, a.hw, cov a', a'.hw⟩
  simp only [signRV, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a4 ∉ linkRegs),
    a.a0, a'.a0, a.a1, a'.a1, a.a2, a'.a2, a.a3, a'.a3, a.a4, a'.a4]
  simp only [and_true]
  exact e

/-- brainpoolp512r1's kit, for its group law `hL`. -/
def kit (hL : VG.Proof.Weierstrass.Law Spec.BrainpoolP512r1.curve) : Kit where
  nw := 8
  Q := 64
  E := Spec.Ecdsa.BrainpoolP512r1.inst
  FN := Impl.Ecdsa.RISCV64.brainpoolp512r1Order
  FNok := VG.Proof.Ecdsa.RISCV64.BrainpoolP512r1.order_ok
  FNk := rfl
  FNm := rfl
  len := rfl
  sh := 0
  nbits := (Nat.add_zero _).trans nBits_brainpoolp512r1
  sh8 := by decide
  two := fun _ => by decide
  nw9 := ⟨by decide, by decide⟩
  Qw := .inl rfl
  G := 64
  coreC := Impl.Ecdsa.RISCV64.signBrainpoolP512r1
  K := []
  core_call h _ hQ := core_call hL h hQ
  core_rel h := core_rel hL fun s s' hp => let ⟨a, a', e, _⟩ := h s s' hp; ⟨a, a', e⟩

/-! ## `vg_ecdsa_brainpoolp512r1_sign`, with the hash function as a table -/

/-- brainpoolP512r1, for its group law `hL`. -/
def brainpoolp512r1 (hL : VG.Proof.Weierstrass.Law Spec.BrainpoolP512r1.curve) : RfcCurve where
  kit := kit hL
  coreN := "vg_ecdsa_brainpoolp512r1_sign_k"
  hsh := .inl rfl
  hGQ := (by decide : (64 : Nat) ≤ 64)
  hG8 := hG8_of _ (by decide : 8 * 64 + 0 ≤ 8 * 64)
  hGD := .inl rfl

/-- The code for the digest length `D` and the block size `B`. -/
abbrev cfgP (D B : Nat) : Impl.Ecdsa.Rfc6979.RISCV64.Cfg :=
  cfgK Impl.Ecdsa.RISCV64.brainpoolp512r1Order "vg_ecdsa_brainpoolp512r1_sign_k" Impl.Ecdsa.RISCV64.signBrainpoolP512r1 8 64 0 64 Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries D B

theorem checks₀ : Checks (cfgP 16 64) := by checks_decide
theorem checks₁ : Checks (cfgP 20 64) := by checks_decide
theorem checks₂ : Checks (cfgP 28 64) := by checks_decide
theorem checks₃ : Checks (cfgP 32 64) := by checks_decide
theorem checks₄ : Checks (cfgP 48 128) := by checks_decide
theorem checks₅ : Checks (cfgP 64 128) := by checks_decide
theorem checks₆ : Checks (cfgP 28 128) := by checks_decide
theorem checks₇ : Checks (cfgP 32 128) := by checks_decide

/-- `vg_ecdsa_brainpoolp512r1_sign`, with the tables of `vs`. -/
theorem brainpoolp512r1T_verified (hL : VG.Proof.Weierstrass.Law Spec.BrainpoolP512r1.curve) (vs : List Proof.HashTable.RISCV64.TVar)
    (h : OK vs) :
    Verified RISCV64.target (signCode (brainpoolp512r1 hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vs) (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 (kit hL).K vs) := by
  exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h (checks_of checks₀ checks₁ checks₂ checks₃ checks₄ checks₅ checks₆ checks₇)
    (sat_nil (T := Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1) h (by decide) rfl)

end VG.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP512r1
