module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Common
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.Sign
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.SignVerified
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny

/-!
# Deterministic ECDSA on RISC-V: P-256's kit

P-256's scalars, the functions of its order, and `vg_ecdsa_p256_sign`,
whose `[k]G` reads the comb's table: its calls against `signRVC`
(`WP.call`, since it pushes no frames), from what `CoreArgs` gives.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64.P256

open VG VG.RISCV64
open VG.Proof.Ecdsa.Rfc6979.RISCV64
open VG.Proof.Ecdsa.RISCV64.P256 (signRV signRVC sign_rv sign_ct sg)
open VG.Proof.Ecdsa.RISCV64.Comb (combWords_length)

/-- The callee's regions. -/
abbrev coreRd (s : State) (d g k : Addr) : List Region :=
  [⟨d, 32⟩, ⟨g, 32⟩, ⟨k, 32⟩] ++ constRegs Impl.Ecdsa.RISCV64.Comb.p256CombConsts s

theorem coreArgs_pre {s : State} {o d g k w : Addr}
    (h : CoreArgs 32 Impl.Ecdsa.RISCV64.Comb.p256CombConsts s o d g k w) :
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
    (hL : VG.Proof.Weierstrass.Law Spec.P256.curve)
    (h : CoreArgs 32 Impl.Ecdsa.RISCV64.Comb.p256CombConsts s o d g k w) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨o, 64⟩, ⟨w, 8192⟩] s' →
      (match sg s.mem d g k with
        | some rs => s'.gpr .a0 = 1 ∧ Spec.Sha256.bytesAt s'.mem o 64 = Spec.Ecdsa.encode Spec.P256.curve rs
        | none => s'.gpr .a0 = 0 ∧ Spec.Sha256.bytesAt s'.mem o 64 = List.replicate 64 0) → Q s') :
    WP isa (.call nm Impl.Ecdsa.RISCV64.Sign.signP256) s Q := by
  refine WP.call (k := signRVC) (sign_rv hL) (rd := coreRd s d g k) (wr := [⟨o, 64⟩, ⟨w, 8192⟩])
    (coreArgs_pre h) h.hc h.hw ?_ Impl.Ecdsa.RISCV64.Sign.signP256_noFrames
  intro s' hrd hwr hsp' hf hcs _ hpost
  simp only [signRVC, signRV, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3] at hpost
  exact hQ s' ⟨hrd, hwr, hsp', hcs, hf⟩ hpost

theorem core_rel {nm : String} (hL : VG.Proof.Weierstrass.Law Spec.P256.curve) {Q : State → State → Prop}
    {o d g k w : Addr} {f : String → BitVec 64}
    (h : ∀ s s', Q s s' → CoreArgs 32 Impl.Ecdsa.RISCV64.Comb.p256CombConsts s o d g k w ∧
      CoreArgs 32 Impl.Ecdsa.RISCV64.Comb.p256CombConsts s' o d g k w ∧ s.sp = s'.sp ∧
      ∀ c ∈ Impl.Ecdsa.RISCV64.Comb.p256CombConsts, s.syms c.1 = f c.1 ∧ s'.syms c.1 = f c.1) :
    RelCT isa Q (.call nm Impl.Ecdsa.RISCV64.Sign.signP256) fun _ _ => True := by
  have cr : ∀ {s : State}, s.syms Impl.Ecdsa.RISCV64.Comb.p256Sym = f Impl.Ecdsa.RISCV64.Comb.p256Sym →
      constRegs Impl.Ecdsa.RISCV64.Comb.p256CombConsts s =
        [⟨f Impl.Ecdsa.RISCV64.Comb.p256Sym, 8 * Impl.Ecdsa.RISCV64.Comb.p256CombWords.length⟩] := fun hs => by
    simp only [constRegs, Abi.constRegions, Impl.Ecdsa.RISCV64.Comb.p256CombConsts, List.map_cons, List.map_nil, hs]
  refine RelCT.call (sign_rv hL) sign_ct ([⟨d, 32⟩, ⟨g, 32⟩, ⟨k, 32⟩] ++
    [⟨f Impl.Ecdsa.RISCV64.Comb.p256Sym, 8 * Impl.Ecdsa.RISCV64.Comb.p256CombWords.length⟩])
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

/-- P-256's kit, for its group law `hL`. -/
def kit (hL : VG.Proof.Weierstrass.Law Spec.P256.curve) : Kit where
  nw := 4
  E := Spec.Ecdsa.P256.inst
  FN := Impl.Ecdsa.RISCV64.p256Order
  FNok := VG.Proof.Ecdsa.RISCV64.P256.order_ok
  FNk := rfl
  FNm := rfl
  len := rfl
  nbits := VG.Proof.Ecdsa.Rfc6979.nBits_p256
  two := by decide
  nw4 := .inl rfl
  coreC := Impl.Ecdsa.RISCV64.Sign.signP256
  K := Impl.Ecdsa.RISCV64.Comb.p256CombConsts
  core_call h _ hQ := core_call hL h hQ
  core_rel h := core_rel hL h

end VG.Proof.Ecdsa.Rfc6979.RISCV64.P256
