module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Common
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.Sign
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.SignVerified
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Weierstrass.RISCV64.BrainpoolP512r1Order.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Common
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.Sign
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.SignLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.SignVerified
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.BrainpoolP512r1Order.Lit

/-!
# Deterministic ECDSA on RISC-V: brainpoolp512r1's kit

brainpoolP512r1's scalars, the functions of its order, and `vg_ecdsa_brainpoolp512r1_sign_k` (the signature with a given `k`), which
reads no table: its calls against `signRV` (`WP.call`, since it pushes no
frames), from what `CoreArgs` gives.

Then `vg_ecdsa_brainpoolp512r1_sign`, with HMAC as a table: the curve for the body
(`curveT`), the taint checks of its pieces (`checksP`), which the kernel
evaluates, and its verification against `TableInstance.signContract` with
the tables of `vs` (`verifiedT`).
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

/-! ## `vg_ecdsa_brainpoolp512r1_sign`, with HMAC as a table -/

/-- brainpoolP512r1 as the body's curve, for its group law `hL`. -/
def curveT (hL : VG.Proof.Weierstrass.Law Spec.BrainpoolP512r1.curve) : CurveT where
  kit := kit hL
  coreN := "vg_ecdsa_brainpoolp512r1_sign_k"
  big := false
  hbig := (by decide : (false = true ↔ 64 < 64))
  hGv := rfl
  hsh := fun _ => rfl

/-- The body's configuration without the tables, which the taint checks see. -/
def cfgP : Impl.Ecdsa.Rfc6979.RISCV64.Cfg where
  f := Proof.HmacTable.RISCV64.fnsOf []
  FN := Impl.Ecdsa.RISCV64.brainpoolp512r1Order
  coreN := "vg_ecdsa_brainpoolp512r1_sign_k"
  coreC := Impl.Ecdsa.RISCV64.signBrainpoolP512r1
  tries := Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries
  nw := 8
  Q := 64
  big := false
  G := 64

theorem checksP : Checks cfgP := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, trivial⟩, ⟨?_, trivial⟩, ⟨?_, trivial⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem checksT (hL : VG.Proof.Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Checks (cfgT (curveT hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries []) := checksP

/-- `vg_ecdsa_brainpoolp512r1_sign`, with the tables of `vs`. -/
theorem verifiedT (hL : VG.Proof.Weierstrass.Law Spec.BrainpoolP512r1.curve) (vs : List Proof.HmacTable.RISCV64.HVar)
    (h : OK vs) :
    Verified RISCV64.target (signCodeT (curveT hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 (kit hL).K vs) := by
  exact signT_spec ⟨rfl, by decide, by decide⟩ (checksT hL) rfl h (sat_nil h (by decide) rfl)

end VG.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP512r1
