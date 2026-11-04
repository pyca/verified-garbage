module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Common
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.Sign
public import VerifiedGarbage.Spec.Ecdsa.P192
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.SignVerified
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSpec
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSat
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P192Field.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Common
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.Sign
meta import VerifiedGarbage.Spec.Ecdsa.P192
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.SignLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.SignVerified
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSpec
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSat
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P192Field.Lit

/-!
# Deterministic ECDSA on RISC-V: P-192's kit

P-192's scalars (24 bytes in four words), the functions of its order, and
`vg_ecdsa_p192_sign`, which reads no table: its calls against `signRV` (`WP.call`, since it pushes no
frames), from what `CoreArgs` gives.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64.P192

open VG VG.RISCV64
open VG.Proof.Ecdsa.Rfc6979.RISCV64
open VG.Proof.Ecdsa.RISCV64.P192 (signRV sign_rv sign_ct sg)

theorem coreArgs_pre {s : State} {o d g k w : Addr} (h : CoreArgs 24 [] s o d g k w) :
    signRV.pre (s.callEntry.withRegions [⟨d, 24⟩, ⟨g, 24⟩, ⟨k, 24⟩] [⟨o, 48⟩, ⟨w, 8192⟩]) := by
  simp only [signRV, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, h.a4]
  exact ⟨trivial, trivial, h.d_ow, h.d_dw, h.d_gw, h.d_kw, h.no, h.nd, h.ng, h.nk, h.nw, h.wa⟩

theorem cov {s : State} {o d g k w : Addr} (h : CoreArgs 24 [] s o d g k w) :
    RISCV64.Covers ([⟨d, 24⟩, ⟨g, 24⟩, ⟨k, 24⟩] ++ [⟨o, 48⟩, ⟨w, 8192⟩]) (s.rd ++ s.wr) := by
  have := h.hc
  simpa [constRegs, Abi.constRegions] using this

theorem core_call {nm : String} {s : State} {o d g k w : Addr}
    (hL : VG.Proof.Weierstrass.Law Spec.P192.curve) (h : CoreArgs 24 [] s o d g k w) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨o, 48⟩, ⟨w, 8192⟩] s' →
      (match sg s.mem d g k with
        | some rs => s'.gpr .a0 = 1 ∧ Spec.Sha256.bytesAt s'.mem o 48 = Spec.Ecdsa.encode Spec.P192.curve rs
        | none => s'.gpr .a0 = 0 ∧ Spec.Sha256.bytesAt s'.mem o 48 = List.replicate 48 0) → Q s') :
    WP isa (.call nm Impl.Ecdsa.RISCV64.P192.signP192) s Q := by
  refine WP.call (k := signRV) (sign_rv hL) (rd := [⟨d, 24⟩, ⟨g, 24⟩, ⟨k, 24⟩]) (wr := [⟨o, 48⟩, ⟨w, 8192⟩])
    (coreArgs_pre h) (cov h) h.hw ?_ Impl.Ecdsa.RISCV64.P192.signP192_noFrames
  intro s' hrd hwr hsp' hf hcs _ hpost
  simp only [signRV, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3] at hpost
  exact hQ s' ⟨hrd, hwr, hsp', hcs, hf⟩ hpost

theorem core_rel {nm : String} (hL : VG.Proof.Weierstrass.Law Spec.P192.curve) {Q : State → State → Prop}
    {o d g k w : Addr}
    (h : ∀ s s', Q s s' → CoreArgs 24 [] s o d g k w ∧ CoreArgs 24 [] s' o d g k w ∧ s.sp = s'.sp) :
    RelCT isa Q (.call nm Impl.Ecdsa.RISCV64.P192.signP192) fun _ _ => True := by
  refine RelCT.call (sign_rv hL) sign_ct [⟨d, 24⟩, ⟨g, 24⟩, ⟨k, 24⟩] [⟨o, 48⟩, ⟨w, 8192⟩] fun s s' hp => ?_
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

/-- P-192's kit, for its group law `hL`. -/
def kit (hL : VG.Proof.Weierstrass.Law Spec.P192.curve) : Kit where
  nw := 4
  Q := 24
  E := Spec.Ecdsa.P192.inst
  FN := Impl.Ecdsa.RISCV64.p192Order
  FNok := VG.Proof.Ecdsa.RISCV64.P192.order_ok
  FNk := rfl
  FNm := rfl
  len := rfl
  sh := 0
  nbits := by decide
  sh8 := by decide
  two := fun _ => by decide
  nw9 := ⟨by decide, by decide⟩
  Qw := .inr (.inr (.inl ⟨rfl, rfl⟩))
  coreC := Impl.Ecdsa.RISCV64.P192.signP192
  K := []
  core_call h _ hQ := core_call hL h hQ
  core_rel h := core_rel hL fun s s' hp => let ⟨a, a', e, _⟩ := h s s' hp; ⟨a, a', e⟩

/-! ## `vg_ecdsa_p192_sign`, with the hash function as a table -/

/-- P-192, for its group law `hL`. -/
def p192 (hL : VG.Proof.Weierstrass.Law Spec.P192.curve) : RfcCurve where
  kit := kit hL
  coreN := "vg_ecdsa_p192_sign_k"
  hsh := .inl rfl
  hGQ := (by decide : (24 : Nat) ≤ 24)
  hG8 := hG8_of _ (by decide : 8 * 24 + 0 ≤ 8 * 24)
  hGD := .inl rfl

/-- The code for the digest length `D` and the block size `B`. -/
abbrev cfgP (D B : Nat) : Impl.Ecdsa.Rfc6979.RISCV64.Cfg :=
  cfgK Impl.Ecdsa.RISCV64.p192Order "vg_ecdsa_p192_sign_k" Impl.Ecdsa.RISCV64.P192.signP192 4 24 0 24 Spec.Ecdsa.Rfc6979.Curves.p192.tries D B

theorem checks₀ : Checks (cfgP 16 64) := by checks_decide
theorem checks₁ : Checks (cfgP 20 64) := by checks_decide
theorem checks₂ : Checks (cfgP 28 64) := by checks_decide
theorem checks₃ : Checks (cfgP 32 64) := by checks_decide
theorem checks₄ : Checks (cfgP 48 128) := by checks_decide
theorem checks₅ : Checks (cfgP 64 128) := by checks_decide
theorem checks₆ : Checks (cfgP 28 128) := by checks_decide
theorem checks₇ : Checks (cfgP 32 128) := by checks_decide

/-- `vg_ecdsa_p192_sign`, with the tables of `vs`. -/
theorem p192T_verified (hL : VG.Proof.Weierstrass.Law Spec.P192.curve) (vs : List Proof.HashTable.RISCV64.TVar)
    (h : OK vs) :
    Verified RISCV64.target (signCode (p192 hL) Spec.Ecdsa.Rfc6979.Curves.p192.tries vs) (specK Spec.Ecdsa.Rfc6979.Curves.p192 (kit hL).K vs) := by
  exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h (checks_of checks₀ checks₁ checks₂ checks₃ checks₄ checks₅ checks₆ checks₇)
    (sat_nil (T := Spec.Ecdsa.Rfc6979.Curves.p192) h (by decide) rfl)

end VG.Proof.Ecdsa.Rfc6979.RISCV64.P192
