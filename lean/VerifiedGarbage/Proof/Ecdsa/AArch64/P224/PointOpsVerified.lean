module

import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Verified
public import VerifiedGarbage.Proof.Weierstrass.PointFacts
public import VerifiedGarbage.Impl.Ecdsa.P224.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Batteries.Data.List.Lemmas
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Verified
meta import VerifiedGarbage.Proof.Weierstrass.PointFacts
meta import VerifiedGarbage.Impl.Ecdsa.P224.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Lit
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Batteries.Data.List.Lemmas
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
meta import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
meta import VerifiedGarbage.Proof.Weierstrass.InverseContract

/-!
# `vg_p224_proj_add` on AArch64: `Verified`

The facts of `Impl.Weierstrass.PointOps.p224`'s `projAddContract` for
AArch64, by name (`addK`): `ws` in `x0`, `p` at slot 0, `P`, `Q` and `b`
below it at their slots, which are P-224's ECDSA slots `RX`, `TX` and `EM`
(`sl`). The code is Algorithm 4 on those slots into `D` (`DX`, slot 17),
the formula's temporaries `T0`–`T5` (slots 23 to 28) and the products'
temporary area (`TMP`, slot 2): `rcb3_ok` gives its values, and that no other
byte changes (`keeps_of`). The contract decodes a coordinate `x` as
`x R^(p-2)`, the proofs as `x R⁻¹` (`toM`): they agree by Fermat's little
theorem, from the group law (`Point.dec_eq`). Constant time by taint
tracking, `x0` and `sp` public.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.P224.PointOps

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P224

/-- P-224's curve of `Proof/Weierstrass/PointOpsContract.lean`. -/
abbrev C : Impl.Weierstrass.PointOps.Curve := Impl.Weierstrass.PointOps.p224

/-- The coordinate at an offset below `2³²` is the number `wordsVal` reads. -/
theorem coordAt_eq (m : Mem) (ws : Addr) {o : Nat} (ho : o < 2 ^ 32) :
    C.coordAt m ws o = wordsVal m ws o 4 := by
  unfold Impl.Weierstrass.Point.Curve.coordAt Impl.Weierstrass.Mont.numAt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  exact read_eq_wordsVal m ws 4 o

/-- `vg_p224_proj_add`'s contract on AArch64, by name. -/
def addK : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .x0, 8192⟩] ∧ (s.gpr .x0).toNat + 8192 ≤ 2 ^ 64 ∧
    C.ModOk (s.gpr .x0) s.mem ∧ C.Below (C.pointAt s.mem (s.gpr .x0) C.pAt) ∧
    C.Below (C.pointAt s.mem (s.gpr .x0) C.qAt) ∧ C.CoordBelow (s.gpr .x0) s.mem C.bAt
  post s s' := let P := C.pt (s.gpr .x0) s.mem C.pAt
    let Q := C.pt (s.gpr .x0) s.mem C.qAt
    C.Result C.oAt (Impl.Weierstrass.PointOps.rcbAdd (C.el (s.gpr .x0) s.mem C.bAt) P.1 P.2.1 P.2.2
      Q.1 Q.2.1 Q.2.2) (s.gpr .x0) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.sp = s₂.sp

/-- The formula's slots: `b`, its temporaries, `D`, `P` and `Q`. -/
abbrev addI : List Nat := [EM, T0, T1, T2, T3, T4, T5, DX, DY, DZ, RX, RY, RZ, TX, TY, TZ]

/-- The slots it reads. -/
abbrev readI : List Nat := [EM, RX, RY, RZ, TX, TY, TZ]

/-- The code's slots, as the specification's offsets. -/
theorem sl_vals : p224.sl EM = C.bAt ∧ p224.sl RX = C.pAt ∧ p224.sl TX = C.qAt ∧ p224.sl DX = C.oAt ∧
    p224.sl MP = C.modAt ∧ p224.sl RY = C.pAt + 32 ∧ p224.sl RZ = C.pAt + 64 ∧
    p224.sl TY = C.qAt + 32 ∧ p224.sl TZ = C.qAt + 64 ∧ p224.sl DY = C.oAt + 32 ∧
    p224.sl DZ = C.oAt + 64 := by decide

/-- What the code writes, as offsets: `T0`–`T5`, `D`, and the temporary area. -/
theorem rcbW_eq : rcbW { p224.rcbSlots with a := p224.sl EM, b3 := p224.sl EM } (p224.pt DX DY DZ) =
    [800, 832, 864, 896, 928, 960, 608, 640, 672] := by decide

theorem tmp_eq : p224.MP'.tmp = 128 ∧ p224.MP'.n = 4 := by decide

theorem keeps_of {ws : Addr} {m m' : Mem}
    (h : ∀ x, (∀ w ∈ [800, 832, 864, 896, 928, 960, 608, 640, 672], ofs ws x < w ∨ w + 32 ≤ ofs ws x) →
      (ofs ws x < 128 ∨ 128 + 32 ≤ ofs ws x) → m' x = m x) :
    C.Keeps C.oAt ws m m' := by
  intro i hi hown ho
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine h _ (fun w hw => ?_) ?_
  all_goals
    show (ws + BitVec.ofNat 64 i - ws).toNat < _ ∨ _ ≤ (ws + BitVec.ofNat 64 i - ws).toNat
    rw [Mem.sub_ofNat_toNat ws (by omega)]
    simp only [Impl.Weierstrass.PointOps.Curve.Own, Impl.Weierstrass.PointOps.Curve.slot,
      Impl.Weierstrass.PointOps.Curve.tmpAt, Impl.Weierstrass.PointOps.Curve.oAt,
      Impl.Weierstrass.PointOps.Curve.ptBytes, C, Impl.Weierstrass.PointOps.p224,
      Impl.Weierstrass.Point.p224] at hown ho
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · omega

theorem correct (hFe : Point.Fermat C.p) (hI : InvSounds) (s : State) (hs : addK.pre s) :
    ∃ t s', Exec isa projAddP224 s t s' ∧ abiPreserved s s' ∧ addK.post s s' := by
  obtain ⟨-, hwr, hfit, hm, hP, hQ, hb⟩ := hs
  have hc := (p224_ok hI).toBaseCfgOk
  have h0 := hc.n0
  have ⟨eb, eP, eQ, eO, eM, eRY, eRZ, eTY, eTZ, eDY, eDZ⟩ := sl_vals
  set base := s.gpr .x0
  have hS : Scr s base size := ⟨rfl, by rw [hwr]; simp, hfit, by decide⟩
  have cv : ∀ i ∈ readI ++ [MP], C.coordAt s.mem base (p224.sl i) = wordsVal s.mem base (p224.sl i) 4 :=
    fun i hi => coordAt_eq _ _ (by
      have : ∀ i ∈ readI ++ [MP], p224.sl i < 2 ^ 32 := by decide
      exact this i hi)
  have hM : ModOkA p224.MP' size p224.C.p s.mem base := modP_of hc (by
    show wordsVal s.mem base (p224.sl MP) 4 = _
    rw [← cv MP (by simp), eM]; exact hm)
  -- What it reads is below `p`.
  have hlt : ∀ i ∈ readI, wordsVal s.mem base (p224.sl i) 4 < p224.C.p := by
    have b0 := hP.1
    have b1 := hP.2.1
    have b2 := hP.2.2
    have q0 := hQ.1
    have q1 := hQ.2.1
    have q2 := hQ.2.2
    have bb : C.coordAt s.mem base C.bAt < C.p := hb
    simp only [Impl.Weierstrass.Point.Curve.pointAt, Impl.Weierstrass.Point.elemBytes] at b0 b1 b2 q0 q1 q2
    intro i hi
    rw [← cv i (List.mem_append_left _ hi)]
    simp only [readI, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [eb]; exact bb
    · rw [eP]; exact b0
    · rw [eRY]; exact b1
    · rw [eRZ]; exact b2
    · rw [eQ]; exact q0
    · rw [eTY]; exact q1
    · rw [eTZ]; exact q2
  have hL : Lay p224.MP' size (· ∈ addI.map p224.sl) := lay_map hc rfl rfl rfl (by decide)
  have hAl : Aligned p224.MP' (· ∈ addI.map p224.sl) := ⟨fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact sl_mod8 p224 i, MP'_A p224,
    fun f m' h => (hc.call_p f m' h).2⟩
  have hA : RcbApart { p224.rcbSlots with a := p224.sl EM, b3 := p224.sl EM } (p224.pt RX RY RZ)
      (p224.pt TX TY TZ) (p224.pt DX DY DZ) :=
    rcbApart_of h0 (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ]) (lr := [EM, EM, RX, RY, RZ, TX, TY, TZ])
      rfl rfl (by decide) (by decide)
  let E := fun x => toM p224.C.p (2 ^ (64 * p224.n)) (wordsVal s.mem base x p224.n)
  have hInv : Inv p224.MP' base size p224.C.p (· ∈ addI.map p224.sl) (readI.map p224.sl) E s := by
    refine ⟨hS, hM, fun x hx => ?_, fun x hx => ?_, fun _ _ => rfl⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have sub : ∀ i ∈ readI, i ∈ addI := by decide
      exact List.mem_map_of_mem (sub i hi)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact hlt i hi
  have hpR := unitMod_pow_two hc.p_odd (64 * p224.n)
  obtain ⟨t, s', he, K, I', v'⟩ := rcb3_ok hL hAl hpR hA (fun x hx => by
      rw [show rcbW { p224.rcbSlots with a := p224.sl EM, b3 := p224.sl EM } (p224.pt DX DY DZ) ++
        rcbR { p224.rcbSlots with a := p224.sl EM, b3 := p224.sl EM } (p224.pt RX RY RZ) (p224.pt TX TY TZ) =
        ([T0, T1, T2, T3, T4, T5, DX, DY, DZ, EM, EM, RX, RY, RZ, TX, TY, TZ]).map p224.sl from rfl] at hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have sub : ∀ i ∈ [T0, T1, T2, T3, T4, T5, DX, DY, DZ, EM, EM, RX, RY, RZ, TX, TY, TZ], i ∈ addI := by
        decide
      exact List.mem_map_of_mem (sub i hi))
    (Low.small (by decide) _) hInv (fun x hx => by
      rw [show rcbR { p224.rcbSlots with a := p224.sl EM, b3 := p224.sl EM } (p224.pt RX RY RZ)
        (p224.pt TX TY TZ) = ([EM, EM, RX, RY, RZ, TX, TY, TZ]).map p224.sl from rfl] at hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have sub : ∀ i ∈ [EM, EM, RX, RY, RZ, TX, TY, TZ], i ∈ readI := by decide
      exact List.mem_map_of_mem (sub i hi))
  have hv : projAddP224.allInstrs keepsV = true := by lit_decide
  refine ⟨t, s', he, ⟨fun r hr => K.gpr r (by revert r; decide), K.sp, Exec.preservedV he hv⟩, ?_⟩
  -- The result.
  have dq := Point.dec_eq C.toCurve (by decide +kernel) hFe hpR
  have hD : ∀ i ∈ [DX, DY, DZ], p224.sl i ∈ [(p224.pt DX DY DZ).x, (p224.pt DX DY DZ).y,
      (p224.pt DX DY DZ).z] ++ readI.map p224.sl := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> simp [Cfg.pt]
  have cv' : ∀ i ∈ [DX, DY, DZ], C.coordAt s'.mem base (p224.sl i) = wordsVal s'.mem base (p224.sl i) 4 :=
    fun i hi => coordAt_eq _ _ (by
      have : ∀ i ∈ [DX, DY, DZ], p224.sl i < 2 ^ 32 := by decide
      exact this i hi)
  obtain ⟨tw, tt⟩ := tmp_eq
  refine ⟨⟨?_, ?_, ?_⟩, ?_, keeps_of fun x hx ht => K.mem x (by rw [rcbW_eq, tt]; exact hx)
    (by rw [tw, tt]; exact ht)⟩
  · show C.coordAt s'.mem base C.oAt < C.p
    rw [← eO, cv' DX (by simp)]; exact I'.lt _ (hD DX (by simp))
  · show C.coordAt s'.mem base (C.oAt + Impl.Weierstrass.Point.elemBytes C.k) < C.p
    rw [show C.oAt + Impl.Weierstrass.Point.elemBytes C.k = p224.sl DY by rw [eDY]; rfl,
      cv' DY (by simp)]; exact I'.lt _ (hD DY (by simp))
  · show C.coordAt s'.mem base (C.oAt + 2 * Impl.Weierstrass.Point.elemBytes C.k) < C.p
    rw [show C.oAt + 2 * Impl.Weierstrass.Point.elemBytes C.k = p224.sl DZ by rw [eDZ]; rfl,
      cv' DZ (by simp)]; exact I'.lt _ (hD DZ (by simp))
  · have el : ∀ i ∈ readI, C.dec (C.coordAt s.mem base (p224.sl i)) = E (p224.sl i) := fun i hi => by
      rw [cv i (List.mem_append_left _ hi), dq]; rfl
    have el' : ∀ i ∈ [DX, DY, DZ], C.dec (C.coordAt s'.mem base (p224.sl i)) =
        toM p224.C.p (2 ^ (64 * p224.n)) (wordsVal s'.mem base (p224.sl i) p224.n) := fun i hi => by
      rw [cv' i hi, dq]; rfl
    show (C.dec (C.coordAt s'.mem base C.oAt),
      C.dec (C.coordAt s'.mem base (C.oAt + Impl.Weierstrass.Point.elemBytes C.k)),
      C.dec (C.coordAt s'.mem base (C.oAt + 2 * Impl.Weierstrass.Point.elemBytes C.k))) =
      Impl.Weierstrass.PointOps.rcbAdd (C.dec (C.coordAt s.mem base C.bAt))
        (C.dec (C.coordAt s.mem base C.pAt))
        (C.dec (C.coordAt s.mem base (C.pAt + Impl.Weierstrass.Point.elemBytes C.k)))
        (C.dec (C.coordAt s.mem base (C.pAt + 2 * Impl.Weierstrass.Point.elemBytes C.k)))
        (C.dec (C.coordAt s.mem base C.qAt))
        (C.dec (C.coordAt s.mem base (C.qAt + Impl.Weierstrass.Point.elemBytes C.k)))
        (C.dec (C.coordAt s.mem base (C.qAt + 2 * Impl.Weierstrass.Point.elemBytes C.k)))
    have e32 : Impl.Weierstrass.Point.elemBytes C.k = 32 := rfl
    rw [e32, show 2 * 32 = 64 from rfl, ← eDY, ← eDZ, ← eO, ← eb, ← eRY, ← eRZ, ← eP, ← eTY, ← eTZ, ← eQ,
      el' DX (by simp), el' DY (by simp), el' DZ (by simp), el EM (by simp), el RX (by simp),
      el RY (by simp), el RZ (by simp), el TX (by simp), el TY (by simp), el TZ (by simp)]
    exact (congrArg₂ Prod.mk (I'.val _ (hD DX (by simp)))
      (congrArg₂ Prod.mk (I'.val _ (hD DY (by simp))) (I'.val _ (hD DZ (by simp))))).trans v'

theorem agree (s₁ s₂ : State) (_ : addK.pre s₁) (_ : addK.pre s₂) (h : addK.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x0]) s₁ s₂ :=
  ⟨h.2, fun r hr => by
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h.1⟩

/-- Constant time by taint tracking, `x0` and `sp` public. -/
theorem ct : ConstantTime isa addK.pre addK.pub projAddP224 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0]) agree (by taint_decide)

/-- The memory of `satState`: P-224's `p` at `ws + 64` for `ws = 0x1000`,
zeros elsewhere. -/
@[irreducible] def satMem : Mem := fun a =>
  if 0x1040 ≤ a.toNat ∧ a.toNat < 0x1060 then BitVec.ofNat 8 (Spec.P224.p >>> (8 * (a.toNat - 0x1040)))
  else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | _ => 0
  sp := 0x10000
  mem := satMem
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem sat_pre : C.ModOk 0x1000 satMem ∧ C.Below (C.pointAt satMem 0x1000 C.pAt) ∧
    C.Below (C.pointAt satMem 0x1000 C.qAt) ∧ C.CoordBelow 0x1000 satMem C.bAt :=
  ⟨by unfold Impl.Weierstrass.PointOps.Curve.ModOk; decide +kernel,
    by unfold Impl.Weierstrass.Point.Curve.Below; decide +kernel,
    by unfold Impl.Weierstrass.Point.Curve.Below; decide +kernel,
    by unfold Impl.Weierstrass.PointOps.Curve.CoordBelow; decide +kernel⟩

theorem implies : addK.Implies (C.projAddContract AArch64.abi) where
  pre s h := by
    sig_pre [Impl.Weierstrass.PointOps.Curve.projAddContract, Impl.Weierstrass.PointOps.sig,
      AArch64.abi, AArch64.argRegs, stackBelow] at h
    exact h
  post s s' _ h := by
    sig_post [Impl.Weierstrass.PointOps.Curve.projAddContract, Impl.Weierstrass.PointOps.sig,
      AArch64.abi, AArch64.argRegs]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Impl.Weierstrass.PointOps.Curve.projAddContract, Impl.Weierstrass.PointOps.sig,
      AArch64.abi, AArch64.argRegs] at h
    exact ⟨h.2, h.1⟩
  sat := ⟨satState, by
    sig_pre [Impl.Weierstrass.PointOps.Curve.projAddContract, Impl.Weierstrass.PointOps.sig,
      AArch64.abi, AArch64.argRegs, stackBelow]
    exact ⟨by decide, sat_pre⟩⟩

/-- `vg_p224_proj_add` on AArch64. -/
theorem verified (hL : Weierstrass.Law Spec.P224.curve) (hI : InvSounds) :
    Verified AArch64.target projAddP224 (C.projAddContract AArch64.abi) :=
  Verified.of_correct (correct (Point.fermat_of_law hL) hI) ct implies

end VG.Proof.Ecdsa.AArch64.P224.PointOps
