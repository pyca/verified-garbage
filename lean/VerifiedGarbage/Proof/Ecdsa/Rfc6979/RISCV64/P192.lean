module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Common
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.Sign
public import VerifiedGarbage.Spec.Ecdsa.P192
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.SignVerified
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P192Field.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Common
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.Sign
meta import VerifiedGarbage.Spec.Ecdsa.P192
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.SignLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.SignVerified
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P192Field.Lit

/-!
# Deterministic ECDSA on RISC-V: P-192's kit

P-192's scalars (24 bytes in four words), the functions of its order, and
`vg_ecdsa_p192_sign_k` (the signature with a given `k`), which reads no table: its calls against `signRV` (`WP.call`, since it pushes no
frames), from what `CoreArgs` gives.

Then `vg_ecdsa_p192_sign`, with HMAC as a table: the curve for the body
(`curveT`), the taint checks of its pieces (`checksP`), which the kernel
evaluates, and its verification against `TableInstance.signContract` with
the tables of `vs` (`verifiedT`).
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

/-! ## `vg_ecdsa_p192_sign`, with HMAC as a table -/

/-- P-192 as the body's curve, for its group law `hL`. -/
def curveT (hL : VG.Proof.Weierstrass.Law Spec.P192.curve) : CurveT where
  kit := kit hL
  coreN := "vg_ecdsa_p192_sign_k"
  big := false
  hbig := (by decide : (false = true ↔ 64 < 24))
  hGv := rfl
  hsh := fun _ => rfl

/-- The body's configuration without the tables, which the taint checks see. -/
def cfgP : Impl.Ecdsa.Rfc6979.RISCV64.Cfg where
  f := Proof.HmacTable.RISCV64.fnsOf []
  FN := Impl.Ecdsa.RISCV64.p192Order
  coreN := "vg_ecdsa_p192_sign_k"
  coreC := Impl.Ecdsa.RISCV64.P192.signP192
  tries := Spec.Ecdsa.Rfc6979.Curves.p192.tries
  nw := 4
  Q := 24
  big := false
  G := 24

theorem checksP : Checks cfgP := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, trivial⟩, ⟨?_, trivial⟩, ⟨?_, trivial⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem checksT (hL : VG.Proof.Weierstrass.Law Spec.P192.curve) :
    Checks (cfgT (curveT hL) Spec.Ecdsa.Rfc6979.Curves.p192.tries []) := checksP

/-- `vg_ecdsa_p192_sign`, with the tables of `vs`. -/
theorem verifiedT (hL : VG.Proof.Weierstrass.Law Spec.P192.curve) (vs : List Proof.HmacTable.RISCV64.HVar)
    (h : OK vs) :
    Verified RISCV64.target (signCodeT (curveT hL) Spec.Ecdsa.Rfc6979.Curves.p192.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p192 (kit hL).K vs) := by
  exact signT_spec ⟨rfl, by decide, by decide⟩ (checksT hL) rfl h (sat_nil h (by decide) rfl)

end VG.Proof.Ecdsa.Rfc6979.RISCV64.P192
