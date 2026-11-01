module

import VerifiedGarbage.Proof.Ecdsa.X86.QMul
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Weierstrass.MulContract
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Weierstrass.X86.PointContract
public import VerifiedGarbage.Proof.Weierstrass.X86.PointCurves
import VerifiedGarbage.Proof.Weierstrass.X86.Rep
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ecdsa.X86.Stages
public import VerifiedGarbage.Proof.Ecdsa.X86.MulFn

/-!
# `vg_<curve>_mul` on x86 (32-bit): the contract

The facts of `Impl.Weierstrass.Mul.Curve.mulInRangeContract` on x86, for
calls using 20 bytes of stack, by name (`mulX86`: `ws` the argument, the
argument, the return address and the 20 bytes below it apart from it, as
the point functions' `sumX86` has them), for the curve of
`Proof/Weierstrass/MulContract.lean` that a configuration's code has (`mulCurve`),
and `mulFn` meets them (`mul_x86`), given the group law: `mulFn_ok` for the
invariant that `R` represents `[k >>> j]Q` when `k` is below `2^(8 len)`
(every `k` below `n` is), which `R = O` has for `j = 8 len`. As on PPC64LE
(`Proof/Ecdsa/PPC64LE/MulVerified.lean`).

`mul_verified` combines it with the function's constant time and a state
satisfying the precondition, both proven for each curve; the constant time
starts from the point functions' taint (`VG.Proof.Weierstrass.X86.Point.τP`: the stack pointer and the
argument public).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- The curve of `Proof/Weierstrass/MulContract.lean` that `c`'s code has: its words,
its temporary slot, with `tail` and `inRange`. -/
def mulCurve (c : Cfg) (curve desc : String) : Impl.Weierstrass.Mul.Curve :=
  { W := c.C, curve := curve, k := c.n, desc := desc, tmp := TMP, tail := true, inRange := true }

/-- The working space, the argument. -/
abbrev mws (s : State) : Addr := (arg s 0).setWidth 64

/-- `vg_<curve>_mul(ws)`, for 20 bytes of stack. -/
def mulX86 (C : Impl.Weierstrass.Mul.Curve) : Contract isa where
  pre s := s.rd = [⟨argAddr s 0, 4⟩] ∧ s.wr = [⟨mws s, 8192⟩] ∧ (arg s 0).toNat + 8192 ≤ 2 ^ 32 ∧
    20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 8 ≤ 2 ^ 32 ∧
    Region.Disjoint ⟨argAddr s 0, 4⟩ ⟨mws s, 8192⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨mws s, 8192⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 20, 20⟩ ⟨mws s, 8192⟩ ∧
    C.ConstsOk (mws s) s.mem ∧ C.PointOk (mws s) s.mem
  post s s' := C.ResultInRange (C.scalar (mws s) s.mem) (C.point (mws s) s.mem) (mws s) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0

/-- `Represents` is the proofs' `Rep`. -/
theorem represents_of_rep {W : Spec.Weierstrass.Curve} {X Y Z : Fe W} {P : Point W}
    (h : Rep W X Y Z P) : Impl.Weierstrass.MulBase.Represents X Y Z P := by
  cases P <;> exact h

section curve

variable {curve desc : String}

/-- What `mulFW` writes is the function's own working space or the result's. -/
theorem keeps_of_unch (h7 : c.n < 10) {ws : Addr} {m m' : Mem} (hu : Unch ws (mulFW c) m m') :
    (mulCurve c curve desc).Keeps ws m m' := by
  intro i hi hown hp
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  rw [show ws + BitVec.ofNat 64 i = off ws i from rfl, ofs_off0 ws (by omega)]
  have hwk := wk_eq c
  simp only [Impl.Weierstrass.Mul.Curve.Own, Impl.Weierstrass.Mul.Curve.slot,
    Impl.Weierstrass.Mul.Curve.tmpAt, Impl.Weierstrass.Mul.Curve.bitsAt,
    Impl.Weierstrass.Mul.Curve.pAt, Impl.Weierstrass.Mul.Curve.ptBytes, mulCurve, TMP, true_and] at hown hp
  simp only [mulFW, mulBW, mulBX, mulLadder_eq, ladWx_at, wkW, List.mem_append, slW, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with (((⟨j, hj, rfl⟩ | hw | hw) | (⟨j, hj, rfl⟩ | hw)) | hw)
  · rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sl_eq, RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ, TMP] <;> omega
  · rw [hw]; dsimp only; omega
  · rw [hw]; dsimp only [Mont.outW]; omega
  · rcases hj with rfl | rfl <;> simp only [sl_eq, ACC, PT] <;> omega
  · rw [hw, bitsAt_eq]; dsimp only; omega
  · rw [hw]; simp only [sl_eq, nslots]; omega

/-- The number at a slot is the coordinate the specification reads there. -/
theorem coord_sl (c : Cfg) (C : Impl.Weierstrass.Mul.Curve) (hk : C.k = c.n) (m : Mem) (ws : Addr)
    {i : Nat} (h7 : c.n < 10) (hi : i < 45) :
    C.toPoint.coordAt m ws (c.sl i) = wordsVal m ws (c.sl i) c.n := by
  rw [VG.Proof.Weierstrass.X86.Point.coordAt_eq C.toPoint m ws
    (by have := sl_le c h7 hi; have : size = 8192 := rfl; omega)]
  show wordsVal m ws (c.sl i) C.k = _
  rw [hk]

/-- The precondition, as `mulFn_ok` has it. -/
theorem argP_of {C : Impl.Weierstrass.Mul.Curve} {s : State} (h : (mulX86 C).pre s) :
    Point.ArgP s (mws s) ∧ Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨mws s, 8192⟩ := by
  obtain ⟨hrd, hwr, hfit, h20, hsp, haw, hrw, hzw, -⟩ := h
  have hn : (mws s).toNat + 8192 ≤ 2 ^ 32 := by
    show ((arg s 0).setWidth 64).toNat + 8192 ≤ _
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hfit
  exact ⟨⟨rfl, by rw [hrd]; exact List.mem_singleton_self _, by rw [hwr]; exact List.mem_singleton_self _,
    hn, VG.Proof.Weierstrass.X86.stkOk_of (Nat.le_refl _) h20 hn (by decide) hzw, hsp, haw⟩, hrw⟩

/-- `vg_<curve>_mul` meets `mulX86`, given the group law. -/
theorem mul_x86 (hc : CfgOk c) (hL : Law c.C) (hsp : SpOk c.mulFn 20) (s : State)
    (hs : (mulX86 (mulCurve c curve desc)).pre s) :
    ∃ t s', Exec isa c.mulFn s t s' ∧ abiPreserved s s' ∧ (mulX86 (mulCurve c curve desc)).post s s' := by
  obtain ⟨hp, hret⟩ := argP_of hs
  obtain ⟨-, hwr, -, h20, -, -, -, -, ⟨hmp, hz, hone, ha, hb3⟩, ⟨hx, hy, hon⟩⟩ := hs
  have h7 := hc.n10
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  generalize hb : mws s = base at hp hret hwr hmp hz hone ha hb3 hx hy hon ⊢
  have ca : ∀ {i}, i < 45 → (mulCurve c curve desc).toPoint.coordAt s.mem base (c.sl i) = sv c base s i :=
    fun hi => coord_sl c _ rfl s.mem base h7 hi
  have hmp' : sv c base s MP = c.C.p := (ca (i := MP) (by decide)).symm.trans hmp
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
  have st := step_rep (L := ladAt c RX RY) (k := sv c base s K) hL hQ
    (by show toM _ _ (sv c base s AP) = _; rw [ha']; exact toM_cmont hc _)
    (by show toM _ _ (sv c base s B3P) = _; rw [hb3']; exact toM_cmont hc _) hG
  have W := WP.spFrame hsp h20 (mulFn_ok hc hp hmp' (by rw [ha']; exact hmont _) (by rw [hb3']; exact hmont _)
    (by rw [hone']; exact Nat.mod_lt _ (by omega)) (by rw [hz']; omega) (qx ▸ hx) (qy ▸ hy)
    (Q := fun j X Y Z =>
      Rep c.C X Y Z (mul (sv c base s K >>> j) (.affine (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY)))))
    st (by
      show Rep c.C (toM _ _ (sv c base s ZERO)) (tmv c.C c.n base s (c.sl ONEP)) (toM _ _ (sv c base s ZERO)) _
      rw [hz', toM_zero, tone, show c.ladderCfg.nbits = 64 * c.n from rfl,
        shiftRight_eq_zero (wordsVal_lt _ _ _ _), mul_zero_pt]
      exact rep_infinity' hL))
  obtain ⟨t, s', he, ⟨G, -, -, U, L, R⟩, F⟩ := W
  refine ⟨t, s', he, ⟨G, ?_⟩, ?_⟩
  · refine F.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rw [hwr] at hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hret
    · exact (below_disjoint_ret h20).symm
  show (mulCurve c curve desc).ResultInRange _ _ (mws s) s.mem s'.mem
  rw [hb, eP]
  refine ⟨fun h1 hn => ?_, keeps_of_unch h7 U⟩
  have e : (mulCurve c curve desc).scalar base s.mem = sv c base s K := ca (i := K) (by decide)
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
  have hR := R
  rw [Nat.shiftRight_zero] at hR
  rw [e]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · show _ < c.C.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x0]; exact L _ (by simp)
  · show _ < c.C.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x1]; exact L _ (by simp)
  · show _ < c.C.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x2]; exact L _ (by simp)
  · rw [Impl.Weierstrass.Point.Curve.pointAt, x0, x1, x2, dq, dq, dq]
    exact represents_of_rep hR

/-! ## A state satisfying the precondition -/

/-- Byte `a` of the number `x` at slot `i` of a working space at address 0,
if `a` is in that slot. -/
def mulSatByte (c : Cfg) (a : Addr) (i x : Nat) : Option (BitVec 8) :=
  if c.sl i ≤ a.toNat ∧ a.toNat < c.sl i + 8 * c.n then
    some (BitVec.ofNat 8 (x >>> (8 * (a.toNat - c.sl i))))
  else none

/-- The memory of `mulSatState`: `p`, and one, `a`, `3 b` and `G`'s
coordinates in Montgomery's form, at their slots for `ws = 0`, zeros
elsewhere (the argument, at `0x20004`, among them). -/
def mulSatMem (c : Cfg) : Mem := fun a =>
  ((mulSatByte c a MP c.C.p).orElse fun _ => (mulSatByte c a ONEP (c.mont 1)).orElse fun _ =>
    (mulSatByte c a AP (c.mont c.C.a)).orElse fun _ => (mulSatByte c a B3P (c.mont (3 * c.C.b))).orElse fun _ =>
    (mulSatByte c a RX (c.mont c.C.gx)).orElse fun _ => mulSatByte c a RY (c.mont c.C.gy)).getD 0

/-- A state satisfying the precondition: `ws` at address 0, the argument at
`0x20004`. -/
def mulSatState (c : Cfg) : State where
  gpr r := match r with
    | .esp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := mulSatMem c
  rd := [⟨0x20004, 4⟩]
  wr := [⟨0, 8192⟩]

/-- `mulSatMem` has `G` in `Q`'s place, given its coordinates there. -/
theorem mulSat_point (hc : CfgOk c) (hL : Law c.C)
    (hx : (mulCurve c curve desc).toPoint.coordAt (mulSatMem c) 0 (c.sl RX) = c.mont c.C.gx)
    (hy : (mulCurve c curve desc).toPoint.coordAt (mulSatMem c) 0 (c.sl RY) = c.mont c.C.gy) :
    (mulCurve c curve desc).PointOk 0 (mulSatMem c) := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have ey : ((mulCurve c curve desc).qCoords 0 (mulSatMem c)).2 = c.mont c.C.gy := by
    rw [← hy]
    show Impl.Weierstrass.Point.Curve.coordAt _ _ _ (64 + 8 * c.n * 14 + 8 * c.n) = _
    rw [show 64 + 8 * c.n * 14 + 8 * c.n = c.sl RY by rw [sl_eq]; simp only [RY]; omega]
  have ex : ((mulCurve c curve desc).qCoords 0 (mulSatMem c)).1 = c.mont c.C.gx := hx
  have dq : ∀ x, (mulCurve c curve desc).toPoint.dec x = toM c.C.p (2 ^ (64 * c.n)) x :=
    VG.Proof.Weierstrass.Point.dec_eq _ hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) hpR
  refine ⟨by rw [ex]; exact Nat.mod_lt _ (by omega), by rw [ey]; exact Nat.mod_lt _ (by omega), ?_⟩
  have eG : (mulCurve c curve desc).point 0 (mulSatMem c) = G c.C := by
    unfold Impl.Weierstrass.Mul.Curve.point
    rw [ex, ey, dq, dq]
    exact congrArg₂ Point.affine (toM_cmont hc _) (toM_cmont hc _)
  have h := hc.onG
  rw [← eG] at h
  exact h

/-! ## The constant time and `Verified` -/

theorem wfM {C : Impl.Weierstrass.Mul.Curve} {s : State} (h : (mulX86 C).pre s) :
    VG.X86.Taint.Wf VG.Proof.Weierstrass.X86.Point.τP s := by
  obtain ⟨hrd, hwr, hfit, h20, hsp, haw, hrw, hzw, -⟩ := h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hwr, VG.Proof.Weierstrass.X86.Point.τP], by simp [hwr], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [VG.Proof.Weierstrass.X86.Point.τP]; omega, ?_⟩, ?_⟩ fun _ => ⟨by simp only [VG.Proof.Weierstrass.X86.Point.τP]; omega, ?_⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; simp only [BitVec.toNat_setWidth]; omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 4) (by omega) hrw haw
  · intro p hp'
    simp only [VG.Proof.Weierstrass.X86.Point.τP, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    refine ⟨by decide, ?_⟩
    simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    exact hzw

theorem agreeM {C : Impl.Weierstrass.Mul.Curve} {s₁ s₂ : State} (h₁ : (mulX86 C).pre s₁) (h₂ : (mulX86 C).pre s₂)
    (hpub : (mulX86 C).pub s₁ s₂) : VG.X86.Taint.Agree VG.Proof.Weierstrass.X86.Point.τP s₁ s₂ := by
  obtain ⟨hesp, a0⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wfM h₁, wfM h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.Weierstrass.X86.Point.τP, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [h₁.2.1, h₂.2.1]; show [(⟨(arg s₁ 0).setWidth 64, 8192⟩ : Region)] = _; rw [a0]
  · simp only [VG.Proof.Weierstrass.X86.Point.τP] at hk
    rw [show VG.X86.Taint.depth VG.Proof.Weierstrass.X86.Point.τP.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := h₁.2.2.2.2.1; omega) h4 hk,
      VG.X86.Taint.argByte_eq (by have := h₂.2.2.2.2.1; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    have : (k - 4) / 4 = 0 := by omega
    rw [this]
    exact congrArg _ a0

/-- `vg_<curve>_mul` meets its contract, for calls using 20 bytes of stack,
given the group law, its constant time and a state satisfying the
precondition. -/
theorem mul_verified (hc : CfgOk c) (hL : Law c.C) (hsp : SpOk c.mulFn 20)
    (hct : ConstantTime isa (mulX86 (mulCurve c curve desc)).pre (mulX86 (mulCurve c curve desc)).pub c.mulFn)
    (hsat : ((mulCurve c curve desc).mulInRangeContract X86.abi 20).pre (mulSatState c)) :
    Verified X86.target c.mulFn ((mulCurve c curve desc).mulInRangeContract X86.abi 20) :=
  Verified.of_correct (mul_x86 hc hL hsp) hct
    { pre := fun s h => by
        sig_pre [Impl.Weierstrass.Mul.Curve.mulInRangeContract, Impl.Weierstrass.MulBase.sig,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
        obtain ⟨h20, hsp, hrd, hwr, haw, hrw, -, hzw, -, hfit, hco, hpo⟩ := h
        exact ⟨hrd, hwr, hfit, h20, hsp, haw.symm, hrw, hzw, hco, hpo⟩
      post := by sig_implies_post [Impl.Weierstrass.Mul.Curve.mulInRangeContract, Impl.Weierstrass.MulBase.sig,
        mulX86, mws, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      pub := by sig_implies_pub [Impl.Weierstrass.Mul.Curve.mulInRangeContract, Impl.Weierstrass.MulBase.sig,
        mulX86, mws, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sat := ⟨_, hsat⟩ }

end curve

end VG.Proof.Ecdsa.X86
