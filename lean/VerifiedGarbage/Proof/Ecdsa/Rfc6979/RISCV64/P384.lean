module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Common
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.Sign
public import VerifiedGarbage.Spec.Ecdsa.P384
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.SignVerified
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny

/-!
# Deterministic ECDSA on RISC-V: P-384's kit

P-384's scalars, the functions of its order, and `vg_ecdsa_p384_sign`, which
reads no table: its calls against `signRV` (`WP.call`, since it pushes no
frames), from what `CoreArgs` gives.
-/

@[expose] public section

-- `2³⁸⁴ < 2n` is evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64.P384

open VG VG.RISCV64
open VG.Proof.Ecdsa.Rfc6979.RISCV64
open VG.Proof.Ecdsa.RISCV64.P384 (signRV sign_rv sign_ct sg)

theorem nBits_p384 : Spec.Ecdsa.nBits Spec.P384.curve = 384 := by
  show Spec.P384.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.P384.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P384.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

theorem coreArgs_pre {s : State} {o d g k w : Addr} (h : CoreArgs 48 [] s o d g k w) :
    signRV.pre (s.callEntry.withRegions [⟨d, 48⟩, ⟨g, 48⟩, ⟨k, 48⟩] [⟨o, 96⟩, ⟨w, 8192⟩]) := by
  simp only [signRV, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, h.a4]
  exact ⟨trivial, trivial, h.d_ow, h.d_dw, h.d_gw, h.d_kw, h.no, h.nd, h.ng, h.nk, h.nw, h.wa⟩

theorem cov {s : State} {o d g k w : Addr} (h : CoreArgs 48 [] s o d g k w) :
    RISCV64.Covers ([⟨d, 48⟩, ⟨g, 48⟩, ⟨k, 48⟩] ++ [⟨o, 96⟩, ⟨w, 8192⟩]) (s.rd ++ s.wr) := by
  have := h.hc
  simpa [constRegs, Abi.constRegions] using this

theorem core_call {nm : String} {s : State} {o d g k w : Addr}
    (hL : VG.Proof.Weierstrass.Law Spec.P384.curve) (h : CoreArgs 48 [] s o d g k w) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨o, 96⟩, ⟨w, 8192⟩] s' →
      (match sg s.mem d g k with
        | some rs => s'.gpr .a0 = 1 ∧ Spec.Sha256.bytesAt s'.mem o 96 = Spec.Ecdsa.encode Spec.P384.curve rs
        | none => s'.gpr .a0 = 0 ∧ Spec.Sha256.bytesAt s'.mem o 96 = List.replicate 96 0) → Q s') :
    WP isa (.call nm Impl.Ecdsa.RISCV64.Sign.signP384) s Q := by
  refine WP.call (k := signRV) (sign_rv hL) (rd := [⟨d, 48⟩, ⟨g, 48⟩, ⟨k, 48⟩]) (wr := [⟨o, 96⟩, ⟨w, 8192⟩])
    (coreArgs_pre h) (cov h) h.hw ?_ Impl.Ecdsa.RISCV64.Sign.signP384_noFrames
  intro s' hrd hwr hsp' hf hcs _ hpost
  simp only [signRV, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3] at hpost
  exact hQ s' ⟨hrd, hwr, hsp', hcs, hf⟩ hpost

theorem core_rel {nm : String} (hL : VG.Proof.Weierstrass.Law Spec.P384.curve) {Q : State → State → Prop}
    {o d g k w : Addr}
    (h : ∀ s s', Q s s' → CoreArgs 48 [] s o d g k w ∧ CoreArgs 48 [] s' o d g k w ∧ s.sp = s'.sp) :
    RelCT isa Q (.call nm Impl.Ecdsa.RISCV64.Sign.signP384) fun _ _ => True := by
  refine RelCT.call (sign_rv hL) sign_ct [⟨d, 48⟩, ⟨g, 48⟩, ⟨k, 48⟩] [⟨o, 96⟩, ⟨w, 8192⟩] fun s s' hp => ?_
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

/-- P-384's kit, for its group law `hL`. -/
def kit (hL : VG.Proof.Weierstrass.Law Spec.P384.curve) : Kit where
  nw := 6
  E := Spec.Ecdsa.P384.inst
  FN := Impl.Ecdsa.RISCV64.p384Order
  FNok := VG.Proof.Ecdsa.RISCV64.P384.order_ok
  FNk := rfl
  FNm := rfl
  len := rfl
  nbits := nBits_p384
  two := by decide
  nw4 := .inr rfl
  coreC := Impl.Ecdsa.RISCV64.Sign.signP384
  K := []
  core_call h _ hQ := core_call hL h hQ
  core_rel h := core_rel hL fun s s' hp => let ⟨a, a', e, _⟩ := h s s' hp; ⟨a, a', e⟩

end VG.Proof.Ecdsa.Rfc6979.RISCV64.P384
