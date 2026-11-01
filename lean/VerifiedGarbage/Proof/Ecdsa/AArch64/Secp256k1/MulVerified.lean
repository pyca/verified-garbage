module

import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.GMul
import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Config
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Weierstrass.PointFacts
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.AArch64
public import VerifiedGarbage.Proof.Ecdsa.AArch64.MulFn
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Weierstrass.AArch64.Secp256k1Literals
import VerifiedGarbage.Proof.Secp256k1.Point
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Batteries.Data.List.Lemmas
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.CombLay
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.GMul
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Config
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Weierstrass.PointFacts
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.AArch64
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.MulFn
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Secp256k1Literals
meta import VerifiedGarbage.Proof.Secp256k1.Point
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Batteries.Data.List.Lemmas
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.CombLay
public import VerifiedGarbage.Proof.Weierstrass.MulContract
meta import VerifiedGarbage.Proof.Weierstrass.MulContract

/-!
# `vg_secp256k1_mul` on AArch64: `Verified`

The facts of `Impl.Weierstrass.Mul.secp256k1.mulContract` for AArch64, by name
(`mK`): `ws` in `x0`, `p`, zero and the constants at their slots, and the
point `Q` in `R`'s first two. `mulFn_ok` gives `[k]Q` in `R`'s slots, which
are `P`'s, `x19` restored, and every byte of `ws` kept but those of its slots
(`mulWF`), `R`'s and the own working space's. The coordinates the
specification decodes are the proofs' (`dq`, given Fermat's little theorem
from the group law), and `Represents` is `Rep`. Constant time by taint
tracking, `x0` and `sp` public.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.Secp256k1.Mul

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.Secp256k1

/-- secp256k1's curve of `Proof/Weierstrass/MulContract.lean`. -/
abbrev C : Impl.Weierstrass.Mul.Curve := Impl.Weierstrass.Mul.secp256k1

/-- The function's contract on AArch64. -/
def mK : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .x0, 8192⟩] ∧ (s.gpr .x0).toNat + 8192 ≤ 2 ^ 64 ∧
    C.ConstsOk (s.gpr .x0) s.mem ∧ C.PointOk (s.gpr .x0) s.mem
  post s s' := C.Result (mul (C.scalar (s.gpr .x0) s.mem) (C.point (s.gpr .x0) s.mem)) (s.gpr .x0) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.sp = s₂.sp

/-- The coordinate at an offset below `2³²` is the number `wordsVal` reads. -/
theorem coordAt_eq (P : Impl.Weierstrass.Point.Curve) (m : Mem) (ws : Addr) {o : Nat} (ho : o < 2 ^ 32) :
    P.coordAt m ws o = wordsVal m ws o P.k := by
  unfold Impl.Weierstrass.Point.Curve.coordAt Impl.Weierstrass.Mont.numAt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  exact read_eq_wordsVal m ws P.k o

/-- What the function writes, as offsets: `R`'s slots (`P`'s) and the own
working space. -/
theorem mulWF_eq : mulWF secp256k1 = [(512, 32), (544, 32), (576, 32), (992, 32), (1024, 32), (704, 32),
    (736, 32), (768, 32), (800, 32), (832, 32), (864, 32), (896, 32), (928, 32), (960, 32), (608, 32),
    (640, 32), (672, 32), (128, 32), (1504, 264)] := by decide

theorem keeps_of_unch {ws : Addr} {m m' : Mem} (hu : Unch ws (mulWF secp256k1) m m') :
    C.Keeps ws m m' := by
  intro i hi hown hp
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  show (ws + BitVec.ofNat 64 i - ws).toNat < _ ∨ _ ≤ (ws + BitVec.ofNat 64 i - ws).toNat
  rw [Mem.sub_ofNat_toNat ws (by omega)]
  simp only [Impl.Weierstrass.Mul.Curve.Own, Impl.Weierstrass.Mul.Curve.slot,
    Impl.Weierstrass.Mul.Curve.tmpAt, Impl.Weierstrass.Mul.Curve.bitsAt,
    Impl.Weierstrass.Mul.Curve.pAt, Impl.Weierstrass.Mul.Curve.ptBytes, C,
    Impl.Weierstrass.Mul.secp256k1] at hown hp
  rw [mulWF_eq] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

/-- The prime, as `C`'s points and the group law have it: equal without
evaluating it, which unifying the two would. -/
theorem toPoint_p : C.toPoint.p = Spec.Secp256k1.curve.p := by
  simp only [Impl.Weierstrass.Mul.Curve.toPoint]; rfl

theorem fermat_congr {p q : Nat} [NeZero p] [NeZero q] (h : p = q) (hf : Point.Fermat q) :
    Point.Fermat p := by
  subst h; exact hf

/-- `Represents` is the proofs' `Rep`. -/
theorem represents_of_rep {W : Spec.Weierstrass.Curve} {X Y Z : Fe W} {P : Point W}
    (h : Rep W X Y Z P) : Impl.Weierstrass.MulBase.Represents X Y Z P := by
  cases P <;> exact h

theorem ca (m : Mem) (ws : Addr) {o : Nat} (ho : o < 2 ^ 32) :
    C.toPoint.coordAt m ws o = wordsVal m ws o 4 := coordAt_eq _ _ _ ho

theorem sv_at {base : Addr} {s : State} {i o : Nat} (h : secp256k1.sl i = o) :
    sv secp256k1 base s i = wordsVal s.mem base o 4 := by
  show wordsVal s.mem base (secp256k1.sl i) secp256k1.n = _
  rw [h]; rfl

/-- Decoding is the proofs' `toM`, given the group law (Fermat's little
theorem). -/
theorem dq (hL : Law Spec.Secp256k1.curve) (x : Nat) : C.toPoint.dec x = toM C.toPoint.p C.toPoint.R x := by
  have hFe : Point.Fermat C.toPoint.p := fermat_congr toPoint_p (Point.fermat_of_law hL)
  have hodd : C.toPoint.p % 2 = 1 := by rw [toPoint_p]; decide +kernel
  have h1 : (1 : Fin C.toPoint.p) ≠ 0 := by decide +kernel
  exact Point.dec_eq C.toPoint h1 hFe (unitMod_pow_two hodd (64 * C.k)) x

theorem mul_correct (hL : Law Spec.Secp256k1.curve) (hI : InvSounds) (s : State) (hs : mK.pre s) :
    ∃ t s', Exec isa secp256k1.mulFn s t s' ∧ abiPreserved s s' ∧ mK.post s s' := by
  obtain ⟨-, hwr, hfit, ⟨hmp, hz, hone, ha, hb3⟩, ⟨hx, hy, hon⟩⟩ := hs
  have hc := secp256k1_ok hI
  have hS : Scr s (s.gpr .x0) size := ⟨rfl, by rw [hwr]; simp, hfit, by decide⟩
  have hmp' : sv secp256k1 (s.gpr .x0) s MP = secp256k1.C.p := (ca _ _ (by decide)).symm.trans hmp
  have hz' : sv secp256k1 (s.gpr .x0) s ZERO = 0 := (ca _ _ (by decide)).symm.trans hz
  have hone' : sv secp256k1 (s.gpr .x0) s ONEP = 2 ^ (64 * secp256k1.n) % secp256k1.C.p := by
    have h := (ca s.mem (s.gpr .x0) (o := 224) (by decide)).symm.trans hone
    simp only [Impl.Weierstrass.Mul.Curve.mont, Nat.one_mul] at h
    exact h
  have ha' : sv secp256k1 (s.gpr .x0) s AP = secp256k1.mont secp256k1.C.a :=
    (ca s.mem (s.gpr .x0) (o := 256) (by decide)).symm.trans ha
  have hb3' : sv secp256k1 (s.gpr .x0) s BM = secp256k1.mont (3 * secp256k1.C.b) :=
    (ca s.mem (s.gpr .x0) (o := 288) (by decide)).symm.trans hb3
  have qx : (C.qCoords (s.gpr .x0) s.mem).1 = sv secp256k1 (s.gpr .x0) s RX := by
    rw [sv_at (i := RX) (o := 512) rfl, ← ca _ _ (by decide)]; rfl
  have qy : (C.qCoords (s.gpr .x0) s.mem).2 = sv secp256k1 (s.gpr .x0) s RY := by
    rw [sv_at (i := RY) (o := 544) rfl, ← ca _ _ (by decide)]; rfl
  have hx' : sv secp256k1 (s.gpr .x0) s RX < secp256k1.C.p := qx ▸ hx
  have hy' : sv secp256k1 (s.gpr .x0) s RY < secp256k1.C.p := qy ▸ hy
  have eP : C.point (s.gpr .x0) s.mem = ptQ secp256k1 (s.gpr .x0) s := by
    unfold Impl.Weierstrass.Mul.Curve.point
    rw [qx, qy, dq hL, dq hL]
    rfl
  have hQ : onCurve secp256k1.C (ptQ secp256k1 (s.gpr .x0) s) = true := by rw [← eP]; exact hon
  obtain ⟨t, s', he, K', U', -, L', R'⟩ :=
    mulFn_ok hc (.inl rfl) (.inl (by decide)) ladLayM ladAM hL hS hmp' hz' hone' ha' hb3' hx' hy' hQ
  refine ⟨t, s', he, ⟨fun r hr => K'.gpr r (by revert r; decide), K'.sp, Exec.preservedV he
    (show secp256k1.mulFn.allInstrs keepsV = true by lit_decide)⟩, ?_⟩
  show C.Result (mul (C.scalar (s.gpr .x0) s.mem) (C.point (s.gpr .x0) s.mem)) (s.gpr .x0) s.mem s'.mem
  rw [eP, show C.scalar (s.gpr .x0) s.mem = sv secp256k1 (s.gpr .x0) s K from ca _ _ (by decide)]
  refine ⟨?_, ?_, keeps_of_unch U'⟩
  · show C.toPoint.coordAt s'.mem _ 512 < _ ∧ C.toPoint.coordAt s'.mem _ 544 < _ ∧
      C.toPoint.coordAt s'.mem _ 576 < _
    rw [ca _ _ (by decide), ca _ _ (by decide), ca _ _ (by decide)]
    exact ⟨L' _ (by decide), L' _ (by decide), L' _ (by decide)⟩
  · show Impl.Weierstrass.MulBase.Represents (C.toPoint.dec (C.toPoint.coordAt s'.mem _ 512))
      (C.toPoint.dec (C.toPoint.coordAt s'.mem _ 544)) (C.toPoint.dec (C.toPoint.coordAt s'.mem _ 576)) _
    rw [dq hL, dq hL, dq hL, ca _ _ (by decide), ca _ _ (by decide), ca _ _ (by decide)]
    exact represents_of_rep R'

theorem agree (s₁ s₂ : State) (_ : mK.pre s₁) (_ : mK.pre s₂) (h : mK.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x0]) s₁ s₂ :=
  ⟨h.2, fun r hr => by
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h.1⟩

/-- Constant time by taint tracking, `x0` and `sp` public. -/
theorem mul_ct : ConstantTime isa mK.pre mK.pub secp256k1.mulFn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0]) agree (by taint_decide)

/-- The memory of `satState`: `p`, one, `a` and `3 b` in Montgomery's form,
and `G`'s coordinates in Montgomery's form, at their slots for `ws = 0x1000`,
zeros elsewhere. -/
@[irreducible] def satMem : Mem := fun a =>
  if 0x1040 ≤ a.toNat ∧ a.toNat < 0x1060 then BitVec.ofNat 8 (Spec.Secp256k1.curve.p >>> (8 * (a.toNat - 0x1040)))
  else if 0x10e0 ≤ a.toNat ∧ a.toNat < 0x1100 then BitVec.ofNat 8 (C.mont 1 >>> (8 * (a.toNat - 0x10e0)))
  else if 0x1100 ≤ a.toNat ∧ a.toNat < 0x1120 then BitVec.ofNat 8 (C.mont C.W.a >>> (8 * (a.toNat - 0x1100)))
  else if 0x1120 ≤ a.toNat ∧ a.toNat < 0x1140 then BitVec.ofNat 8 (C.mont (3 * C.W.b) >>> (8 * (a.toNat - 0x1120)))
  else if 0x1200 ≤ a.toNat ∧ a.toNat < 0x1220 then BitVec.ofNat 8 (C.mont C.W.gx >>> (8 * (a.toNat - 0x1200)))
  else if 0x1220 ≤ a.toNat ∧ a.toNat < 0x1240 then BitVec.ofNat 8 (C.mont C.W.gy >>> (8 * (a.toNat - 0x1220)))
  else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | _ => 0
  sp := 0x10000
  mem := satMem
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem sat_consts : C.ConstsOk 0x1000 satMem := by
  unfold Impl.Weierstrass.Mul.Curve.ConstsOk
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem sat_point (hL : Law Spec.Secp256k1.curve) : C.PointOk 0x1000 satMem := by
  have ex' : C.toPoint.coordAt satMem 0x1000 512 = C.mont C.W.gx := by decide +kernel
  have ey' : C.toPoint.coordAt satMem 0x1000 544 = C.mont C.W.gy := by decide +kernel
  have ex : (C.qCoords 0x1000 satMem).1 = C.mont C.W.gx := ex'
  have ey : (C.qCoords 0x1000 satMem).2 = C.mont C.W.gy := ey'
  have hodd : C.toPoint.p % 2 = 1 := by rw [toPoint_p]; decide +kernel
  have hu : UnitMod C.toPoint.p (2 ^ (64 * C.k)) := unitMod_pow_two hodd (64 * C.k)
  refine ⟨by rw [ex]; decide +kernel, by rw [ey]; decide +kernel, ?_⟩
  have eG : C.point 0x1000 satMem = G C.W := by
    unfold Impl.Weierstrass.Mul.Curve.point
    rw [ex, ey, dq hL, dq hL]
    exact congrArg₂ Point.affine (toM_mont hu) (toM_mont hu)
  rw [eG]; exact Proof.Secp256k1.onCurve_G

theorem implies (hL : Law Spec.Secp256k1.curve) : mK.Implies (C.mulContract AArch64.abi) where
  pre s h := by
    sig_pre [Impl.Weierstrass.Mul.Curve.mulContract, Impl.Weierstrass.MulBase.sig, AArch64.abi,
      AArch64.argRegs, stackBelow] at h
    exact h
  post s s' _ h := by
    sig_post [Impl.Weierstrass.Mul.Curve.mulContract, Impl.Weierstrass.MulBase.sig, AArch64.abi,
      AArch64.argRegs]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Impl.Weierstrass.Mul.Curve.mulContract, Impl.Weierstrass.MulBase.sig, AArch64.abi,
      AArch64.argRegs] at h
    exact ⟨h.2, h.1⟩
  sat := ⟨satState, by
    sig_pre [Impl.Weierstrass.Mul.Curve.mulContract, Impl.Weierstrass.MulBase.sig, AArch64.abi,
      AArch64.argRegs, stackBelow]
    exact ⟨by decide, sat_consts, sat_point hL⟩⟩

/-- `vg_secp256k1_mul` on AArch64. -/
theorem mul_verified (hL : Law Spec.Secp256k1.curve) (hI : InvSounds) :
    Verified AArch64.target secp256k1.mulFn (C.mulContract AArch64.abi) :=
  Verified.of_correct (mul_correct hL hI) mul_ct (implies hL)

end VG.Proof.Ecdsa.AArch64.Secp256k1.Mul
