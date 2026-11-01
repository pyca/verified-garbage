module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.MulFn
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointContract
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Rep
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
public import VerifiedGarbage.Proof.Weierstrass.MulContract

/-!
# `vg_<curve>_mul` on PPC64LE: the contract

The facts of `Impl.Weierstrass.Mul.Curve.mulInRangeContract` on PPC64LE, by
register (`mulPPC`: `ws` in `r3`), for the curve of
`Proof/Weierstrass/MulContract.lean` that a configuration's code has (`mulCurve`: its
words, temporary slot `TMP`, `tail` and `inRange`), and `mulFn` meets them
(`mul_ppc`), given the group law: `mulFn_ok` for the invariant that `R`
represents `[k >>> j]Q` when `k` is below `2^(8 len)` (every `k` below `n`
is), which `R = O` has for `j = 8 len`. The coordinates the specification
decodes are the proofs' (`Point.dec_eq`, given Fermat's little theorem from
the group law), and `Represents` is `Rep`. What the function writes
(`mulFW`) is its own working space or the result's (`keeps_of_unch`). As on
32-bit ARM (`Proof/Ecdsa/Arm/MulVerified.lean`).

`mul_verified` combines it with the function's constant time and a state
satisfying the precondition, both proven for each curve.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Weierstrass.PPC64LE.Point VG.Spec.Weierstrass

variable {c : Cfg}

/-- The curve of `Proof/Weierstrass/MulContract.lean` that `c`'s code has: its words,
its temporary slot, with `tail` and `inRange`. -/
def mulCurve (c : Cfg) (curve desc : String) : Impl.Weierstrass.Mul.Curve :=
  { W := c.C, curve := curve, k := c.n, desc := desc, tmp := TMP, tail := true, inRange := true }

/-- `vg_<curve>_mul(ws = r3)`. -/
def mulPPC (C : Impl.Weierstrass.Mul.Curve) : Contract PPC64LE.isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .r3, 8192⟩] ∧ (s.gpr .r3).toNat + 8192 ≤ 2 ^ 64 ∧
    C.ConstsOk (s.gpr .r3) s.mem ∧ C.PointOk (s.gpr .r3) s.mem
  post s s' := C.ResultInRange (C.scalar (s.gpr .r3) s.mem) (C.point (s.gpr .r3) s.mem) (s.gpr .r3) s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3

/-- `Represents` is the proofs' `Rep`. -/
theorem represents_of_rep {W : Spec.Weierstrass.Curve} {X Y Z : Fe W} {P : Point W}
    (h : Rep W X Y Z P) : Impl.Weierstrass.MulBase.Represents X Y Z P := by
  cases P <;> exact h

section curve

variable {curve desc : String}

/-- What `mulFW` writes is the function's own working space or the result's. -/
theorem keeps_of_unch (h3 : 3 ≤ c.n) (h7 : c.n < 10) {ws : Addr} {m m' : Mem} (hu : Unch ws (mulFW c) m m') :
    (mulCurve c curve desc).Keeps ws m m' := by
  intro i hi hown hp
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  rw [show ws + BitVec.ofNat 64 i = off ws i from rfl, ofs_off0 ws (by omega)]
  have hown' := own_eq c.n
  simp only [Impl.Weierstrass.Mul.Curve.Own, Impl.Weierstrass.Mul.Curve.slot,
    Impl.Weierstrass.Mul.Curve.tmpAt, Impl.Weierstrass.Mul.Curve.bitsAt,
    Impl.Weierstrass.Mul.Curve.pAt, Impl.Weierstrass.Mul.Curve.ptBytes, mulCurve, TMP, true_and] at hown hp
  simp only [mulFW, mulBW, mulBX, List.mem_append, ladWp_eq, slW, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false] at hw
  rcases hw with ((((⟨j, hj, rfl⟩ | hw) | hw) | (⟨j, hj, rfl⟩ | hw)) | hw)
  · rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sl_eq, RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ, TMP] <;> omega
  · rw [hw]; dsimp only; omega
  · simp only [ptW] at hw
    split at hw
    · rw [List.mem_singleton.mp hw]
      have h1 := save_le_oAt (c := c) h3 ‹_›
      rw [sl_eq] at h1
      dsimp only; omega
    · simp at hw
  · rcases hj with rfl | rfl <;> simp only [sl_eq, ACC, PT] <;> omega
  · rw [hw, bitsAt_eq]; dsimp only; omega
  · rw [hw]; simp only [sl_eq, nslots]; omega

/-- The number at a slot is the coordinate the specification reads there. -/
theorem coord_sl (c : Cfg) (C : Impl.Weierstrass.Mul.Curve) (hk : C.k = c.n) (m : Mem) (ws : Addr)
    {i : Nat} (h7 : c.n < 10) (hi : i < 45) :
    C.toPoint.coordAt m ws (c.sl i) = wordsVal m ws (c.sl i) c.n := by
  rw [VG.Proof.Weierstrass.PPC64LE.Point.coordAt_eq C.toPoint m ws
    (by have := sl_le c h7 hi; omega)]
  show wordsVal m ws (c.sl i) C.k = _
  rw [hk]

/-- `vg_<curve>_mul` meets `mulPPC`, given the group law. -/
theorem mul_ppc (hc : CfgOk c) (h3 : 3 ≤ c.n) (hL : Law c.C) (s : State) (hs : (mulPPC (mulCurve c curve desc)).pre s) :
    ∃ t s', Exec isa c.mulFn s t s' ∧ abiPreserved s s' ∧ (mulPPC (mulCurve c curve desc)).post s s' := by
  obtain ⟨-, hwr, hfit, ⟨-, hz, hone, ha, hb3⟩, ⟨hx, hy, hon⟩⟩ := hs
  have h7 := hc.n10
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  generalize hb : s.gpr .r3 = base at hwr hfit hz hone ha hb3 hx hy hon ⊢
  have ca : ∀ {i}, i < 45 → (mulCurve c curve desc).toPoint.coordAt s.mem base (c.sl i) = sv c base s i :=
    fun hi => coord_sl c _ rfl s.mem base h7 hi
  have hz' : sv c base s ZERO = 0 := (ca (i := ZERO) (by decide)).symm.trans hz
  have hone' : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p := by
    have h := (ca (i := ONEP) (by decide)).symm.trans hone
    simp only [Impl.Weierstrass.Mul.Curve.mont, Nat.one_mul] at h
    exact h
  have ha' : sv c base s AP = c.mont c.C.a := (ca (i := AP) (by decide)).symm.trans ha
  have hb3' : sv c base s B3P = c.mont (3 * c.C.b) := (ca (i := B3P) (by decide)).symm.trans hb3
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have qx : ((mulCurve c curve desc).qCoords base s.mem).1 = sv c base s RX := ca (i := RX) (by decide)
  have qy : ((mulCurve c curve desc).qCoords base s.mem).2 = sv c base s RY := by
    rw [← ca (i := RY) (by decide)]
    show Impl.Weierstrass.Point.Curve.coordAt _ _ _ (64 + 8 * c.n * 14 + 8 * c.n) = _
    rw [show 64 + 8 * c.n * 14 + 8 * c.n = c.sl RY by rw [sl_eq]; simp only [RY]; omega]
  have dq : ∀ x, (mulCurve c curve desc).toPoint.dec x = toM c.C.p (2 ^ (64 * c.n)) x :=
    VG.Proof.Weierstrass.Point.dec_eq _ hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) hpR
  -- The point, and the invariant of the ladder.
  have eP : (mulCurve c curve desc).point base s.mem =
      .affine (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY)) := by
    unfold Impl.Weierstrass.Mul.Curve.point
    rw [qx, qy, dq, dq]
  have hQ : onCurve c.C (.affine (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))) = true := by
    have h := hon; rw [eP] at h; exact h
  have tone : tmv c.C c.n base s (c.sl ONEP) = 1 := by
    show toM _ _ (sv c base s ONEP) = 1; rw [hone']; exact toM_one hpR
  have hG : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
      (tmv c.C c.n base s (c.sl ONEP)) (.affine (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))) := by
    rw [tone]; exact rep_affine' hL _ _
  have st := step_rep (L := ladderAt c RX RY) (k := sv c base s K) hL hQ
    (by show toM _ _ (sv c base s AP) = _; rw [ha']; exact toM_cmont hc _)
    (by show toM _ _ (sv c base s B3P) = _; rw [hb3']; exact toM_cmont hc _) hG
  have W := mulFn_ok hc h3 hb hwr hfit (by rw [ha']; exact hmont _) (by rw [hb3']; exact hmont _)
    (by rw [hone']; exact Nat.mod_lt _ (by omega)) (by rw [hz']; omega) (qx ▸ hx) (qy ▸ hy)
    (Q := fun j X Y Z => sv c base s K < 2 ^ (8 * c.C.len) →
      Rep c.C X Y Z (mul (sv c base s K >>> j) (.affine (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY)))))
    (fun j hj X Y Z X2 Y2 Z2 X3 Y3 Z3 hq h2 h3' hk => st j hj X Y Z X2 Y2 Z2 X3 Y3 Z3 (hq hk) h2 h3')
    (fun hk => by
      show Rep c.C (toM _ _ (sv c base s ZERO)) (tmv c.C c.n base s (c.sl ONEP)) (toM _ _ (sv c base s ZERO)) _
      rw [hz', toM_zero, tone, show c.ladderCfg.nbits = 8 * c.C.len from rfl, Nat.shiftRight_eq_div_pow,
        Nat.div_eq_of_lt hk, mul_zero_pt]
      exact rep_infinity' hL)
  obtain ⟨t, s', he, A, -, -, -, U, L, R⟩ := W
  refine ⟨t, s', he, A, ?_⟩
  show (mulCurve c curve desc).ResultInRange _ _ (s.gpr .r3) s.mem s'.mem
  rw [hb, eP]
  refine ⟨fun h1 hn => ?_, keeps_of_unch h3 h7 U⟩
  have e : (mulCurve c curve desc).scalar base s.mem = sv c base s K := ca (i := K) (by decide)
  have hk : sv c base s K < 2 ^ (8 * c.C.len) := by
    have := hc.n_enc
    rw [e, show (mulCurve c curve desc).W.n = c.C.n from rfl] at hn; omega
  have cs : ∀ {i}, i < 45 → (mulCurve c curve desc).toPoint.coordAt s'.mem base (c.sl i) = sv c base s' i :=
    fun hi => coord_sl c _ rfl s'.mem base h7 hi
  have p1 : (mulCurve c curve desc).pAt + Impl.Weierstrass.Point.elemBytes (mulCurve c curve desc).toPoint.k
      = c.sl RY := by
    show 64 + 8 * c.n * 14 + Impl.Weierstrass.Point.elemBytes c.n = _
    rw [sl_eq]; simp only [RY, Impl.Weierstrass.Point.elemBytes]; omega
  have p2 : (mulCurve c curve desc).pAt + 2 * Impl.Weierstrass.Point.elemBytes (mulCurve c curve desc).toPoint.k
      = c.sl RZ := by
    show 64 + 8 * c.n * 14 + 2 * Impl.Weierstrass.Point.elemBytes c.n = _
    rw [sl_eq]; simp only [RZ, Impl.Weierstrass.Point.elemBytes]; omega
  have x0 : (mulCurve c curve desc).toPoint.coordAt s'.mem base (mulCurve c curve desc).pAt =
      sv c base s' RX := cs (i := RX) (by decide)
  have x1 : (mulCurve c curve desc).toPoint.coordAt s'.mem base
      ((mulCurve c curve desc).pAt + Impl.Weierstrass.Point.elemBytes (mulCurve c curve desc).toPoint.k) =
      sv c base s' RY := by rw [p1]; exact cs (by decide)
  have x2 : (mulCurve c curve desc).toPoint.coordAt s'.mem base
      ((mulCurve c curve desc).pAt + 2 * Impl.Weierstrass.Point.elemBytes (mulCurve c curve desc).toPoint.k) =
      sv c base s' RZ := by rw [p2]; exact cs (by decide)
  have hR := R hk
  rw [Nat.shiftRight_zero] at hR
  rw [e]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · show _ < c.C.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x0]; exact L _ (by simp)
  · show _ < c.C.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x1]; exact L _ (by simp)
  · show _ < c.C.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x2]; exact L _ (by simp)
  · rw [Impl.Weierstrass.Point.Curve.pointAt, x0, x1, x2, dq, dq, dq]
    exact represents_of_rep hR

/-- `vg_<curve>_mul` meets its contract, given the group law, its constant
time and a state satisfying the precondition. -/
theorem mul_verified (hc : CfgOk c) (h3 : 3 ≤ c.n) (hL : Law c.C)
    (hct : ConstantTime isa (mulPPC (mulCurve c curve desc)).pre (mulPPC (mulCurve c curve desc)).pub c.mulFn)
    (hsat : ∃ s, ((mulCurve c curve desc).mulInRangeContract PPC64LE.abi).pre s) :
    Verified PPC64LE.target c.mulFn ((mulCurve c curve desc).mulInRangeContract PPC64LE.abi) :=
  Verified.of_correct (mul_ppc hc h3 hL) hct
    { pre := fun s h => by
        sig_pre [Impl.Weierstrass.Mul.Curve.mulInRangeContract, Impl.Weierstrass.MulBase.sig, PPC64LE.abi,
          PPC64LE.argRegs] at h
        exact ⟨h.1, h.2⟩
      post := fun s s' _ h => by
        sig_post [Impl.Weierstrass.Mul.Curve.mulInRangeContract, Impl.Weierstrass.MulBase.sig, PPC64LE.abi,
          PPC64LE.argRegs]
        exact h
      pub := fun s₁ s₂ _ _ h => by
        sig_pub [Impl.Weierstrass.Mul.Curve.mulInRangeContract, Impl.Weierstrass.MulBase.sig, PPC64LE.abi,
          PPC64LE.argRegs] at h
        exact h
      sat := hsat }

/-! ## A state satisfying the precondition -/

/-- Byte `a` of the number `x` at slot `i` of a working space at `0x1000`,
if `a` is in that slot. -/
def mulSatByte (c : Cfg) (a : Addr) (i x : Nat) : Option (BitVec 8) :=
  if 0x1000 + c.sl i ≤ a.toNat ∧ a.toNat < 0x1000 + c.sl i + 8 * c.n then
    some (BitVec.ofNat 8 (x >>> (8 * (a.toNat - (0x1000 + c.sl i)))))
  else none

/-- The memory of `mulSatState`: `p`, and one, `a`, `3 b` and `G`'s
coordinates in Montgomery's form, at their slots for `ws = 0x1000`, zeros
elsewhere. -/
def mulSatMem (c : Cfg) : Mem := fun a =>
  ((mulSatByte c a MP c.C.p).orElse fun _ => (mulSatByte c a ONEP (c.mont 1)).orElse fun _ =>
    (mulSatByte c a AP (c.mont c.C.a)).orElse fun _ => (mulSatByte c a B3P (c.mont (3 * c.C.b))).orElse fun _ =>
    (mulSatByte c a RX (c.mont c.C.gx)).orElse fun _ => mulSatByte c a RY (c.mont c.C.gy)).getD 0

/-- A state satisfying the precondition. -/
def mulSatState (c : Cfg) : State where
  gpr r := match r with
    | .r3 => 0x1000 | _ => 0
  lr := 0
  sp := 0x10000
  mem := mulSatMem c
  rd := []
  wr := [⟨0x1000, 8192⟩]

/-- `mulSatMem` has `G` in `Q`'s place, given its coordinates there. -/
theorem mulSat_point (hc : CfgOk c) (hL : Law c.C)
    (hx : (mulCurve c curve desc).toPoint.coordAt (mulSatMem c) 0x1000 (c.sl RX) = c.mont c.C.gx)
    (hy : (mulCurve c curve desc).toPoint.coordAt (mulSatMem c) 0x1000 (c.sl RY) = c.mont c.C.gy) :
    (mulCurve c curve desc).PointOk 0x1000 (mulSatMem c) := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have ey : ((mulCurve c curve desc).qCoords 0x1000 (mulSatMem c)).2 = c.mont c.C.gy := by
    rw [← hy]
    show Impl.Weierstrass.Point.Curve.coordAt _ _ _ (64 + 8 * c.n * 14 + 8 * c.n) = _
    rw [show 64 + 8 * c.n * 14 + 8 * c.n = c.sl RY by rw [sl_eq]; simp only [RY]; omega]
  have ex : ((mulCurve c curve desc).qCoords 0x1000 (mulSatMem c)).1 = c.mont c.C.gx := hx
  have dq : ∀ x, (mulCurve c curve desc).toPoint.dec x = toM c.C.p (2 ^ (64 * c.n)) x :=
    VG.Proof.Weierstrass.Point.dec_eq _ hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) hpR
  refine ⟨by rw [ex]; exact Nat.mod_lt _ (by omega), by rw [ey]; exact Nat.mod_lt _ (by omega), ?_⟩
  have eG : (mulCurve c curve desc).point 0x1000 (mulSatMem c) = G c.C := by
    unfold Impl.Weierstrass.Mul.Curve.point
    rw [ex, ey, dq, dq]
    exact congrArg₂ Point.affine (toM_cmont hc _) (toM_cmont hc _)
  have h := hc.onG
  rw [← eG] at h
  exact h

end curve

end VG.Proof.Ecdsa.PPC64LE
