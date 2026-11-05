module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Common
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.Sign
public import VerifiedGarbage.Spec.Ecdsa.P521
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.SignVerified
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Order.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Common
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.Sign
meta import VerifiedGarbage.Spec.Ecdsa.P521
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.SignLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.SignVerified
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Order.Lit

/-!
# Deterministic ECDSA on RISC-V: P-521's kit

P-521's scalars (66 bytes in nine words, of which `n`'s 521 bits are the
leftmost), the functions of its order, and `vg_ecdsa_p521_sign_k` (the signature with a given `k`), which reads
SHA-512's 64-byte digest and no table: its calls against `signRV`
(`WP.call`, since it pushes no frames), from what `CoreArgsG` gives; the
candidate it reads as `k` is its 66 bytes' leftmost 521 bits (`hash_eq`).

Then `vg_ecdsa_p521_sign`, with HMAC as a table: the curve for the body
(`curveT`), the taint checks of its pieces (`checksP`), which the kernel
evaluates, and its verification against `TableInstance.signContract` with
the tables of `vs` (`verifiedT`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64.P521

open VG VG.RISCV64
open VG.Proof.Ecdsa.Rfc6979.RISCV64
open VG.Proof.Ecdsa.RISCV64.P521 (signRV sign_rv sign_ct sg)

theorem coreArgs_pre {s : State} {o d g k w : Addr} (h : CoreArgsG 66 64 [] s o d g k w) :
    signRV.pre (s.callEntry.withRegions [⟨d, 66⟩, ⟨g, 64⟩, ⟨k, 66⟩] [⟨o, 132⟩, ⟨w, 8192⟩]) := by
  simp only [signRV, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, h.a4]
  exact ⟨trivial, trivial, h.d_ow, h.d_dw, h.d_gw, h.d_kw, h.no, h.nd, h.ng, h.nk, h.nw, h.wa⟩

theorem cov {s : State} {o d g k w : Addr} (h : CoreArgsG 66 64 [] s o d g k w) :
    RISCV64.Covers ([⟨d, 66⟩, ⟨g, 64⟩, ⟨k, 66⟩] ++ [⟨o, 132⟩, ⟨w, 8192⟩]) (s.rd ++ s.wr) := by
  have := h.hc
  simpa [constRegs, Abi.constRegions] using this

theorem core_call {nm : String} {s : State} {o d g k w : Addr}
    (hL : VG.Proof.Weierstrass.Law Spec.P521.curve) (h : CoreArgsG 66 64 [] s o d g k w) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨o, 132⟩, ⟨w, 8192⟩] s' →
      (match sg s.mem d g k with
        | some rs => s'.gpr .a0 = 1 ∧ Spec.Sha256.bytesAt s'.mem o 132 = Spec.Ecdsa.encode Spec.P521.curve rs
        | none => s'.gpr .a0 = 0 ∧ Spec.Sha256.bytesAt s'.mem o 132 = List.replicate 132 0) → Q s') :
    WP isa (.call nm Impl.Ecdsa.RISCV64.P521.signP521) s Q := by
  refine WP.call (k := signRV) (sign_rv hL) (rd := [⟨d, 66⟩, ⟨g, 64⟩, ⟨k, 66⟩]) (wr := [⟨o, 132⟩, ⟨w, 8192⟩])
    (coreArgs_pre h) (cov h) h.hw ?_ Impl.Ecdsa.RISCV64.P521.signP521_noFrames
  intro s' hrd hwr hsp' hf hcs _ hpost
  simp only [signRV, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3] at hpost
  exact hQ s' ⟨hrd, hwr, hsp', hcs, hf⟩ hpost

theorem core_rel {nm : String} (hL : VG.Proof.Weierstrass.Law Spec.P521.curve) {Q : State → State → Prop}
    {o d g k w : Addr}
    (h : ∀ s s', Q s s' → CoreArgsG 66 64 [] s o d g k w ∧ CoreArgsG 66 64 [] s' o d g k w ∧ s.sp = s'.sp) :
    RelCT isa Q (.call nm Impl.Ecdsa.RISCV64.P521.signP521) fun _ _ => True := by
  refine RelCT.call (sign_rv hL) sign_ct [⟨d, 66⟩, ⟨g, 64⟩, ⟨k, 66⟩] [⟨o, 132⟩, ⟨w, 8192⟩] fun s s' hp => ?_
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

/-- P-521's kit, for its group law `hL`. -/
def kit (hL : VG.Proof.Weierstrass.Law Spec.P521.curve) : Kit where
  nw := 9
  Q := 66
  E := Spec.Ecdsa.P521.inst
  FN := Impl.Ecdsa.RISCV64.p521Order
  FNok := VG.Proof.Ecdsa.RISCV64.P521.order_ok
  FNk := rfl
  FNm := rfl
  len := rfl
  sh := 7
  nbits := by rw [show Spec.Ecdsa.P521.inst.curve = Spec.P521.curve from rfl, VG.Proof.Ecdsa.RISCV64.P521.nBits_eq]
  sh8 := by decide
  two := fun h => absurd h (by decide)
  nw9 := ⟨by decide, by decide⟩
  Qw := .inr (.inr (.inr ⟨rfl, rfl⟩))
  G := 64
  coreC := Impl.Ecdsa.RISCV64.P521.signP521
  K := []
  core_call {_ s _ d g k _} h _ hQ := core_call hL h fun s' a hp => hQ s' a (by
    rwa [show VG.Proof.Ecdsa.RISCV64.P521.sg s.mem d g k = sgOf Spec.Ecdsa.P521.inst 66 64 7 s.mem d g k by
      simp only [VG.Proof.Ecdsa.RISCV64.P521.sg, sgOf, VG.Proof.Ecdsa.RISCV64.P521.hash_eq]; rfl] at hp)
  core_rel h := core_rel hL fun s s' hp => let ⟨a, a', e, _⟩ := h s s' hp; ⟨a, a', e⟩

/-! ## `vg_ecdsa_p521_sign`, with HMAC as a table -/

/-- P-521 as the body's curve, for its group law `hL`. -/
def curveT (hL : VG.Proof.Weierstrass.Law Spec.P521.curve) : CurveT where
  kit := kit hL
  coreN := "vg_ecdsa_p521_sign_k"
  big := true
  hbig := (by decide : (true = true ↔ 64 < 66))
  hGv := rfl
  hsh := fun h => nomatch h

/-- The body's configuration without the tables, which the taint checks see. -/
def cfgP : Impl.Ecdsa.Rfc6979.RISCV64.Cfg where
  f := Proof.HmacTable.RISCV64.fnsOf []
  FN := Impl.Ecdsa.RISCV64.p521Order
  coreN := "vg_ecdsa_p521_sign_k"
  coreC := Impl.Ecdsa.RISCV64.P521.signP521
  tries := Spec.Ecdsa.Rfc6979.Curves.p521.tries
  nw := 9
  Q := 66
  big := true
  G := 64

theorem checksP : Checks cfgP := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, trivial⟩, ⟨?_, trivial⟩, ⟨?_, trivial⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem checksT (hL : VG.Proof.Weierstrass.Law Spec.P521.curve) :
    Checks (cfgT (curveT hL) Spec.Ecdsa.Rfc6979.Curves.p521.tries []) := checksP

/-- `vg_ecdsa_p521_sign`, with the tables of `vs`. -/
theorem verifiedT (hL : VG.Proof.Weierstrass.Law Spec.P521.curve) (vs : List Proof.HmacTable.RISCV64.HVar)
    (h : OK vs) :
    Verified RISCV64.target (signCodeT (curveT hL) Spec.Ecdsa.Rfc6979.Curves.p521.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p521 (kit hL).K vs) := by
  exact signT_spec ⟨rfl, by decide, by decide⟩ (checksT hL) rfl h (sat_nil h (by decide) rfl)

end VG.Proof.Ecdsa.Rfc6979.RISCV64.P521
