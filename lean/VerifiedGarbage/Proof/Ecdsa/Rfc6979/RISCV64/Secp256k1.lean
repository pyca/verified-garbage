module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Common
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.Sign
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.SignVerified
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Secp256k1Order.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Common
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.Sign
meta import VerifiedGarbage.Spec.Ecdsa.Secp256k1
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.SignLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.SignVerified
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.Secp256k1Order.Lit

/-!
# Deterministic ECDSA on RISC-V: secp256k1's kit

secp256k1's scalars, the functions of its order, and `vg_ecdsa_secp256k1_sign_k` (the signature with a given `k`), whose
`[k]G` reads the comb's table: its calls against `signRVC` (`WP.call`, since
it pushes no frames), from what `CoreArgs` gives.

Then `vg_ecdsa_secp256k1_sign`, with HMAC as a table: the curve for the body
(`curveT`), the taint checks of its pieces (`checksP`), which the kernel
evaluates, and its verification against `TableInstance.signContract` with
the tables of `vs` (`verifiedT`).
-/

@[expose] public section

-- `2³⁸⁴ < 2n` is evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64.Secp256k1

open VG VG.RISCV64
open VG.Proof.Ecdsa.Rfc6979.RISCV64
open VG.Proof.Ecdsa.RISCV64.Secp256k1 (signRV signRVC sign_rv sign_ct sg)

theorem nBits_secp256k1 : Spec.Ecdsa.nBits Spec.Secp256k1.curve = 256 := by
  show Spec.Secp256k1.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.Secp256k1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.Secp256k1.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- The callee's regions. -/
abbrev coreRd (s : State) (d g k : Addr) : List Region :=
  [⟨d, 32⟩, ⟨g, 32⟩, ⟨k, 32⟩] ++ constRegs Impl.Ecdsa.RISCV64.Comb.secp256k1CombConsts s

theorem coreArgs_pre {s : State} {o d g k w : Addr}
    (h : CoreArgs 32 Impl.Ecdsa.RISCV64.Comb.secp256k1CombConsts s o d g k w) :
    signRVC.pre (s.callEntry.withRegions (coreRd s d g k) [⟨o, 64⟩, ⟨w, 8192⟩]) := by
  refine ⟨?_, ?_⟩
  · simp only [signRV, stripConsts, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, h.a4]
    exact ⟨rfl, trivial, h.d_ow, h.d_dw, h.d_gw, h.d_kw, h.no, h.nd, h.ng, h.nk, h.nw, h.wa⟩
  · refine ⟨rfl, h.held, fun t ht => ?_, h.tal⟩
    refine ⟨h.tfit t ht, fun r hr => ?_, fun r hr => ?_⟩
    · simp only [State.withRegions_wr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.t_o t ht
      · exact h.t_w t ht
    · simp [RISCV64.abi, stackBelow] at hr

theorem core_call {nm : String} {s : State} {o d g k w : Addr}
    (hL : VG.Proof.Weierstrass.Law Spec.Secp256k1.curve)
    (h : CoreArgs 32 Impl.Ecdsa.RISCV64.Comb.secp256k1CombConsts s o d g k w) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨o, 64⟩, ⟨w, 8192⟩] s' →
      (match sg s.mem d g k with
        | some rs => s'.gpr .a0 = 1 ∧ Spec.Sha256.bytesAt s'.mem o 64 = Spec.Ecdsa.encode Spec.Secp256k1.curve rs
        | none => s'.gpr .a0 = 0 ∧ Spec.Sha256.bytesAt s'.mem o 64 = List.replicate 64 0) → Q s') :
    WP isa (.call nm Impl.Ecdsa.RISCV64.signSecp256k1) s Q := by
  refine WP.call (k := signRVC) (sign_rv hL) (rd := coreRd s d g k) (wr := [⟨o, 64⟩, ⟨w, 8192⟩])
    (coreArgs_pre h) h.hc h.hw ?_ Impl.Ecdsa.RISCV64.signSecp256k1_noFrames
  intro s' hrd hwr hsp' hf hcs _ hpost
  simp only [signRVC, signRV, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3] at hpost
  exact hQ s' ⟨hrd, hwr, hsp', hcs, hf⟩ hpost

theorem core_rel {nm : String} (hL : VG.Proof.Weierstrass.Law Spec.Secp256k1.curve) {Q : State → State → Prop}
    {o d g k w : Addr} {f : String → BitVec 64}
    (h : ∀ s s', Q s s' → CoreArgs 32 Impl.Ecdsa.RISCV64.Comb.secp256k1CombConsts s o d g k w ∧
      CoreArgs 32 Impl.Ecdsa.RISCV64.Comb.secp256k1CombConsts s' o d g k w ∧ s.sp = s'.sp ∧
      ∀ c ∈ Impl.Ecdsa.RISCV64.Comb.secp256k1CombConsts, s.syms c.1 = f c.1 ∧ s'.syms c.1 = f c.1) :
    RelCT isa Q (.call nm Impl.Ecdsa.RISCV64.signSecp256k1) fun _ _ => True := by
  have cr : ∀ {s : State}, s.syms Impl.Ecdsa.RISCV64.Comb.secp256k1Sym = f Impl.Ecdsa.RISCV64.Comb.secp256k1Sym →
      constRegs Impl.Ecdsa.RISCV64.Comb.secp256k1CombConsts s =
        [⟨f Impl.Ecdsa.RISCV64.Comb.secp256k1Sym, 8 * Impl.Ecdsa.RISCV64.Comb.secp256k1CombWords.length⟩] := fun hs => by
    simp only [constRegs, Abi.constRegions, Impl.Ecdsa.RISCV64.Comb.secp256k1CombConsts, List.map_cons, List.map_nil, hs]
  refine RelCT.call (sign_rv hL) sign_ct ([⟨d, 32⟩, ⟨g, 32⟩, ⟨k, 32⟩] ++
    [⟨f Impl.Ecdsa.RISCV64.Comb.secp256k1Sym, 8 * Impl.Ecdsa.RISCV64.Comb.secp256k1CombWords.length⟩])
    [⟨o, 64⟩, ⟨w, 8192⟩] fun s s' hp => ?_
  obtain ⟨a, a', e, ey⟩ := h s s' hp
  obtain ⟨y, y'⟩ := ey _ List.mem_cons_self
  have p := coreArgs_pre a
  have p' := coreArgs_pre a'
  have c := a.hc
  have c' := a'.hc
  simp only [coreRd] at p p'
  rw [cr y] at p c
  rw [cr y'] at p' c'
  refine ⟨p, p', ⟨?_, ?_⟩, c, a.hw, c', a'.hw⟩
  · simp only [signRV, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
      State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a1 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a2 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a4 ∉ linkRegs),
      a.a0, a'.a0, a.a1, a'.a1, a.a2, a'.a2, a.a3, a'.a3, a.a4, a'.a4]
    simp only [and_true]
    exact e
  · show s.syms _ = s'.syms _
    rw [y, y']

/-- secp256k1's kit, for its group law `hL`. -/
def kit (hL : VG.Proof.Weierstrass.Law Spec.Secp256k1.curve) : Kit where
  nw := 4
  Q := 32
  E := Spec.Ecdsa.Secp256k1.inst
  FN := Impl.Ecdsa.RISCV64.secp256k1Order
  FNok := VG.Proof.Ecdsa.RISCV64.Secp256k1.order_ok
  FNk := rfl
  FNm := rfl
  len := rfl
  sh := 0
  nbits := (Nat.add_zero _).trans nBits_secp256k1
  sh8 := by decide
  two := fun _ => by decide
  nw9 := ⟨by decide, by decide⟩
  Qw := .inl rfl
  G := 32
  coreC := Impl.Ecdsa.RISCV64.signSecp256k1
  K := Impl.Ecdsa.RISCV64.Comb.secp256k1CombConsts
  core_call h _ hQ := core_call hL h hQ
  core_rel h := core_rel hL h

/-! ## `vg_ecdsa_secp256k1_sign`, with HMAC as a table -/

/-- secp256k1 as the body's curve, for its group law `hL`. -/
def curveT (hL : VG.Proof.Weierstrass.Law Spec.Secp256k1.curve) : CurveT where
  kit := kit hL
  coreN := "vg_ecdsa_secp256k1_sign_k"
  big := false
  hbig := (by decide : (false = true ↔ 64 < 32))
  hGv := rfl
  hsh := fun _ => rfl

/-- The body's configuration without the tables, which the taint checks see. -/
def cfgP : Impl.Ecdsa.Rfc6979.RISCV64.Cfg where
  f := Proof.HmacTable.RISCV64.fnsOf []
  FN := Impl.Ecdsa.RISCV64.secp256k1Order
  coreN := "vg_ecdsa_secp256k1_sign_k"
  coreC := Impl.Ecdsa.RISCV64.signSecp256k1
  tries := Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries
  nw := 4
  Q := 32
  big := false
  G := 32

theorem checksP : Checks cfgP := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, trivial⟩, ⟨?_, trivial⟩, ⟨?_, trivial⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem checksT (hL : VG.Proof.Weierstrass.Law Spec.Secp256k1.curve) :
    Checks (cfgT (curveT hL) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries []) := checksP

/-- `vg_ecdsa_secp256k1_sign`, with the tables of `vs`. -/
theorem verifiedT (hL : VG.Proof.Weierstrass.Law Spec.Secp256k1.curve) (vs : List Proof.HmacTable.RISCV64.HVar)
    (h : OK vs ∧ Impl.Ecdsa.RISCV64.Comb.secp256k1Sym ∉ Proof.HmacTable.RISCV64.names vs) :
    Verified RISCV64.target (signCodeT (curveT hL) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.secp256k1 (kit hL).K vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.secp256k1) h.1 VG.Proof.Ecdsa.RISCV64.Secp256k1.Comb.combSatMem h.2
    (by rw [VG.Proof.Ecdsa.RISCV64.Secp256k1.Comb.combWords_length]; decide) VG.Proof.Ecdsa.RISCV64.Secp256k1.Comb.combSatMem_held (by decide) rfl
  exact signT_spec ⟨rfl, by decide, by decide⟩ (checksT hL) rfl h.1 hsat

end VG.Proof.Ecdsa.Rfc6979.RISCV64.Secp256k1
