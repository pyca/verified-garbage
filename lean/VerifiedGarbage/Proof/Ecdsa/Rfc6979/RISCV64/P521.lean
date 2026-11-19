module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Common
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.SignVerified
public import VerifiedGarbage.Spec.Ecdsa.P521
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.SignLit
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Order.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Common
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.SignVerified
meta import VerifiedGarbage.Spec.Ecdsa.P521
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.SignLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Order.Lit

/-!
# Deterministic ECDSA on RISC-V: P-521's kit

P-521's scalars (66 bytes in nine words, of which `n`'s 521 bits are the
leftmost), the functions of its order, and `vg_ecdsa_p521_sign_k` (the signature with a given `k`), which reads
SHA-512's 64-byte digest, and whose `[k]G` reads the comb's table: its calls against `signRVC`
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
open VG.Proof.Ecdsa.RISCV64.P521 (signRV signRVC sign_rv sign_ct sg)
open VG.Proof.Ecdsa.RISCV64.P521.Comb (combWords_length)

/-- The callee's regions. -/
abbrev coreRd (s : State) (d g k : Addr) : List Region :=
  [⟨d, 66⟩, ⟨g, 64⟩, ⟨k, 66⟩] ++ constRegs Impl.Ecdsa.RISCV64.CombU.p521CombConsts s

theorem coreArgs_pre {s : State} {o d g k w : Addr}
    (h : CoreArgsG 66 64 Impl.Ecdsa.RISCV64.CombU.p521CombConsts s o d g k w) :
    signRVC.pre (s.callEntry.withRegions (coreRd s d g k) [⟨o, 132⟩, ⟨w, 8192⟩]) := by
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
    (hL : VG.Proof.Weierstrass.Law Spec.P521.curve)
    (h : CoreArgsG 66 64 Impl.Ecdsa.RISCV64.CombU.p521CombConsts s o d g k w) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨o, 132⟩, ⟨w, 8192⟩] s' →
      (match sg s.mem d g k with
        | some rs => s'.gpr .a0 = 1 ∧ Spec.Sha256.bytesAt s'.mem o 132 = Spec.Ecdsa.encode Spec.P521.curve rs
        | none => s'.gpr .a0 = 0 ∧ Spec.Sha256.bytesAt s'.mem o 132 = List.replicate 132 0) → Q s') :
    WP isa (.call nm Impl.Ecdsa.RISCV64.P521.signP521) s Q := by
  refine WP.call (k := signRVC) (sign_rv hL) (rd := coreRd s d g k) (wr := [⟨o, 132⟩, ⟨w, 8192⟩])
    (coreArgs_pre h) h.hc h.hw ?_ Impl.Ecdsa.RISCV64.P521.signP521_noFrames
  intro s' hrd hwr hsp' hf hcs _ hpost
  simp only [signRVC, signRV, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3] at hpost
  exact hQ s' ⟨hrd, hwr, hsp', hcs, hf⟩ hpost

theorem core_rel {nm : String} (hL : VG.Proof.Weierstrass.Law Spec.P521.curve) {Q : State → State → Prop}
    {o d g k w : Addr} {f : String → BitVec 64}
    (h : ∀ s s', Q s s' → CoreArgsG 66 64 Impl.Ecdsa.RISCV64.CombU.p521CombConsts s o d g k w ∧
      CoreArgsG 66 64 Impl.Ecdsa.RISCV64.CombU.p521CombConsts s' o d g k w ∧ s.sp = s'.sp ∧
      ∀ c ∈ Impl.Ecdsa.RISCV64.CombU.p521CombConsts, s.syms c.1 = f c.1 ∧ s'.syms c.1 = f c.1) :
    RelCT isa Q (.call nm Impl.Ecdsa.RISCV64.P521.signP521) fun _ _ => True := by
  have cr : ∀ {s : State}, s.syms Impl.Ecdsa.RISCV64.CombU.p521Sym = f Impl.Ecdsa.RISCV64.CombU.p521Sym →
      constRegs Impl.Ecdsa.RISCV64.CombU.p521CombConsts s =
        [⟨f Impl.Ecdsa.RISCV64.CombU.p521Sym, 8 * Impl.Ecdsa.RISCV64.CombU.p521CombWords.length⟩] := fun hs => by
    simp only [constRegs, Impl.Ecdsa.RISCV64.CombU.p521CombConsts, Abi.constRegions_cons, Abi.constRegions_nil, hs]
  refine RelCT.call (sign_rv hL) sign_ct ([⟨d, 66⟩, ⟨g, 64⟩, ⟨k, 66⟩] ++
    [⟨f Impl.Ecdsa.RISCV64.CombU.p521Sym, 8 * Impl.Ecdsa.RISCV64.CombU.p521CombWords.length⟩])
    [⟨o, 132⟩, ⟨w, 8192⟩] fun s s' hp => ?_
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
  K := Impl.Ecdsa.RISCV64.CombU.p521CombConsts
  core_call {_ s _ d g k _} h _ hQ := core_call hL h fun s' a hp => hQ s' a (by
    rwa [show VG.Proof.Ecdsa.RISCV64.P521.sg s.mem d g k = sgOf Spec.Ecdsa.P521.inst 66 64 7 s.mem d g k by
      simp only [VG.Proof.Ecdsa.RISCV64.P521.sg, sgOf, VG.Proof.Ecdsa.RISCV64.P521.hash_eq]; rfl] at hp)
  core_rel h := core_rel hL h

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
    (h : OK vs ∧ Impl.Ecdsa.RISCV64.CombU.p521Sym ∉ Proof.HmacTable.RISCV64.names vs) :
    Verified RISCV64.target (signCodeT (curveT hL) Spec.Ecdsa.Rfc6979.Curves.p521.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p521 (kit hL).K vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.p521) h.1 VG.Proof.Ecdsa.RISCV64.P521.Comb.combSatMem h.2
    (by rw [VG.Proof.Ecdsa.RISCV64.P521.Comb.combWords_length]; decide) VG.Proof.Ecdsa.RISCV64.P521.Comb.combSatMem_held (by decide) rfl
  exact signT_spec ⟨rfl, by decide, by decide⟩ (checksT hL) rfl h.1 hsat

end VG.Proof.Ecdsa.Rfc6979.RISCV64.P521
