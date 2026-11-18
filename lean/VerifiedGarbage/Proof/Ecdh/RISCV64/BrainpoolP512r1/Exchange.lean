module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.ExchangeAll
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP512r1
public import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP512r1.CheckLit
import VerifiedGarbage.Proof.BrainpoolP512r1.Point
public import VerifiedGarbage.Proof.Ecdh.RISCV64.TailAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.MulFn
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.RISCV64
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.MulVerified
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.MulLit
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Ecdh.RISCV64.BrainpoolP512r1.Tail`, which this module and modules that import it used -/

section

/-! ### `Ecdh.RISCV64.BrainpoolP512r1.Check`, which only this module used -/

section

/-!
# `vg_brainpoolp512r1_check_point` on RISC-V: brainpoolP512r1's facts

The check (`Impl/Ecdh/RISCV64.lean`) is proven once for every curve in
`Proof/Ecdh/RISCV64/TailAll.lean` (`TKit.check_rv`), from what `tkit` says of
this one. Here are brainpoolP512r1's slots, and the facts about them that other proofs
name.
-/

@[expose] public section

-- `p`, below `2^512`, is evaluated.
set_option exponentiation.threshold 1024

namespace VG.Proof.Ecdh.RISCV64.BrainpoolP512r1

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.BrainpoolP512r1
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point)

/-- The flag's offset. -/
abbrev FL : Nat := 2880

theorem sl_FLAG : brainpoolp512r1.sl FLAG = FL := rfl

theorem sl_eq (i : Nat) : brainpoolp512r1.sl i = 64 + 64 * i := by simp only [Cfg.sl, slot, brainpoolp512r1]

/-- What the proofs shared by every curve (`TailAll.lean`) need of this one. -/
def tkit : TKit where
  c := brainpoolp512r1
  name := "brainpoolp512r1"
  cdesc := "brainpoolP512r1"
  mdesc := "brainpoolP512r1"
  n4 := by decide
  n9 := by decide
  p1 := by decide
  field_ok := field_ok
  FPk := rfl
  FPm := rfl
  unit := unit

/-- The flag `&=` the mask `a7`. -/
theorem andFlag_ok {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (Cfg.andFlag brainpoolp512r1)) s fun s' =>
      word s'.mem base FL = word s.mem base FL &&& s.gpr .a7 ∧ Rest [.t0] s s' ∧ Outside base FL 8 s.mem s'.mem :=
  TKit.andFlag_ok brainpoolp512r1 (by decide) hw

/-! ## Slots and masks -/

/-- A slot apart from what changed. -/
theorem sv_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (U : Unch base W m m') (i : Nat)
    (h : ∀ w ∈ W, brainpoolp512r1.sl i + 64 ≤ w.1 ∨ w.1 + w.2 ≤ brainpoolp512r1.sl i) (hi : i < 100 := by decide) :
    wordsVal m' base (brainpoolp512r1.sl i) 8 = wordsVal m base (brainpoolp512r1.sl i) 8 :=
  U.wordsVal h (by rw [sl_eq]; omega_using [hi])

theorem maskOf_and (a b : Bool) : maskOf a &&& maskOf b = maskOf (a && b) := by
  cases a <;> cases b <;> decide

/-- `toM` is injective on numbers below `m`. -/
theorem toM_inj {m R : Nat} [NeZero m] (hR : UnitMod m R) {x y : Nat} (hx : x < m) (hy : y < m)
    (h : toM m R x = toM m R y) : x = y :=
  Kit.toM_inj hR hx hy h

/-- A Montgomery multiplication by `R² mod p` gives `x R mod p`. -/
theorem mont_eq {r x : Nat} (hr : r < W.p) (h : r * 2 ^ 512 % W.p = x * (2 ^ 512 * 2 ^ 512 % W.p) % W.p) :
    r = x * 2 ^ 512 % W.p :=
  toM_inj unit hr (Nat.mod_lt _ (by decide)) ((toM_r2 unit h).trans (toM_mont unit).symm)

/-- brainpoolP512r1's check of `Proof/Weierstrass/CheckPointContract.lean`. -/
abbrev CC : Impl.Weierstrass.CheckPoint.Curve :=
  { Impl.Weierstrass.CheckPoint.brainpoolp512r1 with montOwn := 7680, montOwnEnd := 8192 }

end VG.Proof.Ecdh.RISCV64.BrainpoolP512r1

end

end


/-!
# ECDH and public keys over brainpoolP512r1 on RISC-V: the multiplication and after

What follows the point's setup in both functions (`tail`) is proven once for
every curve in `Proof/Ecdh/RISCV64/TailAll.lean` (`TKit.tail_ok`). Here is what
that proof needs of brainpoolP512r1, its chain of `p - 2` (`chainP_ok`) and its
multiplication's contract (`mulNF`, `mul_meets`), and that proof's statements
on brainpoolP512r1's slots that other proofs name.
-/

@[expose] public section

-- `p`, below `2^512`, is evaluated.
set_option exponentiation.threshold 1024

/-!
## ECDH and public keys over brainpoolP512r1 on RISC-V: the setup

The constants (`consts_ok`, by `TailAll.lean`'s), and what both functions'
setups share.
-/

namespace VG.Proof.Ecdh.RISCV64.BrainpoolP512r1

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.BrainpoolP512r1
open VG.Proof.X25519.RISCV64 (Rest)

/-- Constants to slots below 41, each its own. -/
theorem consts_ok : ∀ (L : List (Nat × Nat)) {s : State} {base : Addr}, WsReg s base → (∀ e ∈ L, e.1 < 41) →
    (L.map Prod.fst).Nodup →
    WP isa (.block (L.flatMap fun e => setConst 8 (brainpoolp512r1.sl e.1) e.2)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ Unch base (L.map fun e => (brainpoolp512r1.sl e.1, 64)) s.mem s'.mem ∧
      ∀ e ∈ L, sv base s' e.1 = e.2 % 2 ^ 512 :=
  fun L _ _ hw hlt hnd =>
    TKit.consts_ok brainpoolp512r1 (by decide) L hw (fun e he => Nat.le_trans (Nat.le_of_lt (hlt e he)) (by decide)) hnd

/-- The constants, as `consts_ok` takes them. -/
theorem constCode_eq : constCode brainpoolp512r1 = (consts brainpoolp512r1).flatMap fun e => setConst 8 (brainpoolp512r1.sl e.1) e.2 := rfl

/-- The constants' slots. -/
theorem consts_slots : ∀ e ∈ consts brainpoolp512r1, e.1 < 41 := by decide

theorem consts_nodup : ((consts brainpoolp512r1).map Prod.fst).Nodup := by decide

/-- The constants are below `2²⁵⁶`. -/
theorem consts_lt : ∀ e ∈ consts brainpoolp512r1, e.2 < 2 ^ 512 := by decide

/-- The saves, `s0 = s3 = r` and `s2 = a0`. -/
theorem save_ok {s : State} {r : Reg} {base : Addr} (h0 : s.gpr r = base)
    (hwr : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) (hal : base.toNat % 8 = 0) :
    WP isa (.block (saveCode r)) s fun s' => WsReg s' base ∧ s'.gpr .s3 = base ∧ s'.gpr .s2 = s.gpr .a0 ∧
      (∀ x, x ≠ .s0 → x ≠ .s2 → x ≠ .s3 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ Unch base [(0, 40)] s.mem s'.mem ∧
      word s'.mem base 0 = s.gpr .s0 ∧ word s'.mem base 8 = s.gpr .s1 ∧ word s'.mem base 16 = s.gpr .s2 ∧
      word s'.mem base 24 = s.gpr .ra ∧ word s'.mem base 32 = s.gpr .s3 :=
  TKit.save_ok h0 hwr hn hal

end VG.Proof.Ecdh.RISCV64.BrainpoolP512r1

namespace VG.Proof.Ecdh.RISCV64.BrainpoolP512r1

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.BrainpoolP512r1
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes)

/-- What `vg_brainpoolp512r1_mul` may write, as ranges of offsets. -/
abbrev mulKW : List (Nat × Nat) := [(960, 192), (1152, 896), (192, 64), (2624, 64), (2944, 2 ^ 64)]

/-- What `vg_brainpoolp512r1_check_point` may write, as ranges of offsets. -/
abbrev checkKW : List (Nat × Nat) :=
  [(192, 64), (2432, 64), (2688, 64), (2752, 64), (7680, 512), (2240, 64), (2304, 64), (2496, 64), (2816, 64),
    (FL, 8), (8192, 2 ^ 64)]

theorem not_mask (b : Bool) : maskOf b ^^^ BitVec.ofInt 64 (-1) = maskOf (!b) := by cases b <;> decide

/-- A slot below the flag's. -/
theorem sl_lt {i : Nat} (hi : i < 44) : brainpoolp512r1.sl i % 8 = 0 ∧ brainpoolp512r1.sl i + 8 * 8 ≤ 6144 ∧ brainpoolp512r1.sl i + 8 * 8 ≤ FL := by
  simp only [Cfg.sl, slot, show brainpoolp512r1.n = 8 from rfl, FL]; omega_using [hi]

/-- The masks of `x < n` and `x ≠ 0` into the flag, for `x` at slot `i`. -/
theorem rangeOf_ok {i : Nat} (hi : i < 41) {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (rangeOf brainpoolp512r1 i)) s fun s' =>
      Kp s s' ∧ Outside base FL 8 s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s i < sv base s MN)) &&&
        maskOf (!decide (sv base s i = 0)) :=
  TKit.rangeOf_ok brainpoolp512r1 (by decide) (Nat.lt_of_lt_of_le hi (by decide)) hw

/-- The constants `tail` reads. -/
structure TailConsts (base : Addr) (s : State) : Prop where
  mp : sv base s MP = W.p
  mn : sv base s MN = W.n
  zero : sv base s ZERO = 0
  one : sv base s ONE = 1
  onep : sv base s ONEP = 1 * 2 ^ 512 % W.p
  ap : sv base s AP = W.a * 2 ^ 512 % W.p
  b3p : sv base s B3P = 3 * W.b * 2 ^ 512 % W.p
  expp : sv base s EXPP = W.p - 2

theorem TailConsts.of_unch {base : Addr} {s s' : State} {W' : List (Nat × Nat)} (h : TailConsts base s)
    (U : Unch base W' s.mem s'.mem)
    (hW : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP], ∀ w ∈ W', brainpoolp512r1.sl i + 64 ≤ w.1 ∨ w.1 + w.2 ≤ brainpoolp512r1.sl i) :
    TailConsts base s' :=
  have g := TKit.Consts.of_unch (c := brainpoolp512r1) (by decide) ⟨h.mp, h.mn, h.zero, h.one, h.onep, h.ap, h.b3p, h.expp⟩ U hW
  ⟨g.mp, g.mn, g.zero, g.one, g.onep, g.ap, g.b3p, g.expp⟩

theorem chainLay : ChainLayR (chainP brainpoolp512r1) 8 :=
  TKit.chainLay brainpoolp512r1 (by decide) (by decide)

/-- The chain is `p - 2`'s. -/
theorem chainP_ok : ChainOkR (chainP brainpoolp512r1) (W.p - 2) := ChainOkR.of_check (by lit_decide)

/-- The coordinate `[o] = [a] Z^(p-2)` out of Montgomery's form, `Z^(p-2) R` in `ACC`. -/
theorem affine_ok {s : State} {base : Addr} (hw : WsReg s base) {t o a : Nat} (ht : t < 44) (ho : o < 44)
    (ha : a < 44) (htm : t ≠ ONE ∧ t ≠ ACC) (hacc : sv base s ACC < W.p) (hone : sv base s ONE = 1) :
    WP isa (affineCoord brainpoolp512r1 t o a) s fun s' =>
      Kp s s' ∧ Unch base [(brainpoolp512r1.sl t, 64), (own 8, 512), (brainpoolp512r1.sl o, 64), (own 8, 512)] s.mem s'.mem ∧
      sv base s' o < W.p ∧
      Fin.ofNat W.p (sv base s' o) = toM W.p (2 ^ 512) (sv base s a) * toM W.p (2 ^ 512) (sv base s ACC) :=
  tkit.affine_ok hw ht ho ha htm hacc hone

/-- What `tail` writes. -/
abbrev tailW : List (Nat × Nat) :=
  [(FL, 8)] ++ mulKW ++ chainWx (chainP brainpoolp512r1) 8 ++
    [(brainpoolp512r1.sl XM, 64), (own 8, 512), (brainpoolp512r1.sl XO, 64), (own 8, 512)]

/-- A byte of a region apart from the working space. -/
theorem out_of_disj {p base : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hn : p.toNat + n ≤ 2 ^ 64)
    {off i : Nat} (hi : off + i < n) : ¬ (⟨base, 8192⟩ : Region).Contains (p + BitVec.ofNat 64 (off + i)) 1 :=
  Kit.out_of_disj hd hn hi

/-- Eight bytes of a region. -/
theorem in_rd8 {rs : List Region} {p : Addr} {n : Nat} (hr : (⟨p, n⟩ : Region) ∈ rs) {off : Nat} (ho : off + 8 ≤ n)
    (hn : n ≤ 8192 := by decide) :
    InRegions rs (p + BitVec.ofNat 64 off) 8 :=
  Kit.in_rd8 hr ho hn

/-- Bytes apart from the working space survive changes within it. -/
theorem bytesAt_unch {base q : Addr} {W : List (Nat × Nat)} {n : Nat} {m m' : Mem} (U : Unch base W m m')
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ 8192)
    (hsep : ∀ i < n, ¬ (⟨base, 8192⟩ : Region).Contains (q + BitVec.ofNat 64 i) 1) :
    bytesAt m' q n = bytesAt m q n :=
  Kit.bytesAt_unch U hW hsep

/-- The value of a constant's slot. -/
theorem const_at {base : Addr} {s : State} (hc : ∀ e ∈ consts brainpoolp512r1, sv base s e.1 = e.2) (k : Nat)
    (hk : k < (consts brainpoolp512r1).length := by decide) : sv base s (consts brainpoolp512r1)[k].1 = (consts brainpoolp512r1)[k].2 :=
  hc _ (List.getElem_mem hk)

/-- The bytes just written. -/
theorem bytesAt_writeBytes (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length ≤ 2 ^ 64) :
    bytesAt (writeBytes m q xs) q xs.length = xs :=
  Kit.bytesAt_writeBytes m q xs h

theorem and_one (b : Bool) : maskOf b &&& BitVec.ofInt 64 1 = if b then 1 else 0 := by cases b <;> decide

/-- Bytes of a region apart from the working space, from an offset. -/
theorem sep_at' {p base : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hn : p.toNat + n ≤ 2 ^ 64)
    {off k : Nat} (hk : off + k ≤ n) :
    ∀ i < k, ¬ (⟨base, 8192⟩ : Region).Contains (p + BitVec.ofNat 64 off + BitVec.ofNat 64 i) 1 := fun i hi => by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact out_of_disj hd hn (by omega_using [hk, hi])

/-- The multiplication's code pushes no frames. -/
theorem mulNF : mulBrainpoolP512r1.noFrames = true :=
  Impl.Ecdsa.RISCV64.mulBrainpoolP512r1_noFrames

/-- The multiplication meets the contract `tail` calls it by. -/
theorem mul_meets (hL : VG.Proof.Weierstrass.Law tkit.c.C) : Meets mulBrainpoolP512r1 (TKit.mulRVc tkit.MC) :=
  mul_rv hL

/-- `tail` with `vg_brainpoolp512r1_mul`. -/
theorem tail_ok (hL : VG.Proof.Weierstrass.Law W) {s : State} {base : Addr} (hw : WsReg s base)
    (h3 : s.gpr .s3 = base) (hc : TailConsts base s) (hx : sv base s RX < W.p) (hy : sv base s RY < W.p)
    (hon : Spec.Weierstrass.onCurve W (.affine (toM W.p (2 ^ 512) (sv base s RX))
      (toM W.p (2 ^ 512) (sv base s RY))) = true) :
    WP isa (tail brainpoolp512r1 "vg_brainpoolp512r1_mul" mulBrainpoolP512r1) s fun s' =>
      Kc s s' ∧ Unch base tailW s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s K < W.n)) &&&
        maskOf (!decide (sv base s K = 0)) ∧
      (1 ≤ sv base s K → sv base s K < W.n →
        Rep W (toM W.p (2 ^ 512) (sv base s' RX)) (toM W.p (2 ^ 512) (sv base s' RY))
          (toM W.p (2 ^ 512) (sv base s' RZ))
          (Spec.Weierstrass.mul (sv base s K) (.affine (toM W.p (2 ^ 512) (sv base s RX))
            (toM W.p (2 ^ 512) (sv base s RY)))) ∧
        sv base s' RX < W.p ∧ sv base s' RY < W.p ∧ sv base s' RZ < W.p) ∧
      sv base s' XO < W.p ∧
      Fin.ofNat W.p (sv base s' XO) =
        toM W.p (2 ^ 512) (sv base s' RX) * toM W.p (2 ^ 512) (sv base s' RZ) ^ (W.p - 2) ∧
      sv base s' ACC < W.p ∧
      toM W.p (2 ^ 512) (sv base s' ACC) = toM W.p (2 ^ 512) (sv base s' RZ) ^ (W.p - 2) :=
  tkit.tail_ok chainP_ok mulNF (mul_meets hL) hL hw h3 ⟨hc.mp, hc.mn, hc.zero, hc.one, hc.onep, hc.ap, hc.b3p, hc.expp⟩ hx hy hon

end VG.Proof.Ecdh.RISCV64.BrainpoolP512r1

end

end

/-!
# ECDH over brainpoolP512r1 on RISC-V: correctness

The curve's kit for `Proof/Ecdh/RISCV64/ExchangeAll.lean`, and what that
proof gives of `vg_ecdh_brainpoolp512r1`: it meets its contract by register (`ecdhRV`), given
the group law (`ecdh_rv`); the peer's point read to the check's slots
(`peerLoad_ok`) and its check (`check_ok`), which verification and the
compressed keys use too.
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.BrainpoolP512r1

-- `p`, below `2^512`, is evaluated.
set_option exponentiation.threshold 1024

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.BrainpoolP512r1
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes)

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange Spec.BrainpoolP512r1.curve (ofBytes (bytesAt m d 64)) (bytesAt m peer 129)

def ecdhRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 64⟩
    let d : Region := ⟨s.gpr .a1, 64⟩
    let peer : Region := ⟨s.gpr .a2, 129⟩
    let scratch : Region := ⟨s.gpr .a3, 8192⟩
    s.rd = [d, peer] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      peer.Disjoint scratch ∧ (s.gpr .a0).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 64 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat + 129 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 8192 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat % 8 = 0
  post s s' :=
    match ex s.mem (s.gpr .a1) (s.gpr .a2) with
    | some z => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 64 = z
    | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 64 = List.replicate 64 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3

theorem onG : Spec.Weierstrass.onCurve W (Spec.Weierstrass.G W) = true := VG.Proof.BrainpoolP512r1.onCurve_G

theorem checkNF : checkBrainpoolP512r1.noFrames = true := checkBrainpoolP512r1_noFrames

/-- The curve's kit. -/
def kit : Kit where
  toTKit := tkit
  L := 64
  len := rfl
  Ln := by decide
  onG := onG
  load := loadNum 8
  store := storeNum 8
  load_ok := Kit.loadNum_kit (c := brainpoolp512r1) (by decide)
  store_ok := Kit.storeNum_kit (c := brainpoolp512r1) (by decide)
  checkN := "vg_brainpoolp512r1_check_point"
  checkNF := checkNF
  mulN := "vg_brainpoolp512r1_mul"
  mulC := mulBrainpoolP512r1
  mulNF := mulNF
  mul_rv := mul_meets
  chainP_ok := chainP_ok
  consts_lt := consts_lt

/-- What the contract gives, by register. -/
abbrev EPre (s : State) : Prop := kit.EPre s

/-- The peer's point read from `[q]` (`x` and `y` to the check's slots), the
flag set to the mask of its first byte being `04`, and the constants. -/
theorem peerLoad_ok {s : State} {base : Addr} {q : Reg} (hw : WsReg s base) (hq : q ∉ [Reg.t0, .t1, .a7])
    (hrd : (⟨s.gpr q, 129⟩ : Region) ∈ s.rd ++ s.wr) (hdis : (⟨s.gpr q, 129⟩ : Region).Disjoint ⟨base, 8192⟩)
    (hfit : (s.gpr q).toNat + 129 ≤ 2 ^ 64) :
    WP isa (.block (loadNum brainpoolp512r1.n (brainpoolp512r1.sl CX) q 1 ++ loadNum brainpoolp512r1.n (brainpoolp512r1.sl CY) q (1 + 8 * brainpoolp512r1.n) ++
      leadMask q ++ sdAt .a7 wb (brainpoolp512r1.sl FLAG) ++ constCode brainpoolp512r1)) s fun s' =>
      WsReg s' base ∧ Rest [.t0, .t1, .a7] s s' ∧
      Unch base ([(brainpoolp512r1.sl CX, 8 * 8)] ++ [(brainpoolp512r1.sl CY, 8 * 8)] ++ [(FL, 8)] ++
        (consts brainpoolp512r1).map fun e => (brainpoolp512r1.sl e.1, 64)) s.mem s'.mem ∧
      sv base s' CX = ofBytes (bytesAt s.mem (s.gpr q + BitVec.ofNat 64 1) 64) ∧
      sv base s' CY = ofBytes (bytesAt s.mem (s.gpr q + BitVec.ofNat 64 65) 64) ∧
      word s'.mem base FL = maskOf (decide (s.mem (s.gpr q) = 4)) ∧
      ∀ e ∈ consts brainpoolp512r1, sv base s' e.1 = e.2 :=
  kit.peerLoad_ok hw hq hrd hdis hfit

/-- The check of the peer's point, by its call. -/
theorem check_ok {s : State} {base : Addr} (hw : WsReg s base) (h3 : s.gpr .s3 = base) (hc : ∀ e ∈ consts brainpoolp512r1, sv base s e.1 = e.2)
    (hf : word s.mem base FL = 0 ∨ word s.mem base FL = BitVec.allOnes 64) :
    WP isa (wsCall "vg_brainpoolp512r1_check_point" checkBrainpoolP512r1) s fun s' =>
      Kp s s' ∧ Unch base checkKW s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&&
        Impl.Weierstrass.CheckPoint.Curve.mask (CC.Valid (sv base s CX) (sv base s CY)) ∧
      sv base s' CPX = (if word s'.mem base FL = 0 then sv base s GX else sv base s CX * 2 ^ 512 % W.p) ∧
      sv base s' CPY = (if word s'.mem base FL = 0 then sv base s GY else sv base s CY * 2 ^ 512 % W.p) :=
  kit.check_ok hw h3 hc hf

/-- The peer's key: `04`, `x` and `y`. -/
theorem peer_bytes (m : Mem) (p : Addr) (L : Nat) :
    bytesAt m p (1 + 2 * L) = m p :: (bytesAt m (p + BitVec.ofNat 64 1) L ++
      bytesAt m (p + BitVec.ofNat 64 (1 + L)) L) :=
  Kit.peer_bytes m p L

theorem mask_eq (P : Prop) [Decidable P] : Impl.Weierstrass.CheckPoint.Curve.mask P = maskOf (decide P) :=
  Kit.mask_eq P

/-- The check's validity is the specification's, but for the first byte. -/
theorem valid_iff (x y : Nat) :
    CC.Valid x y ↔ x < W.p ∧ y < W.p ∧ VG.Proof.Ecdh.OnCurveF W x y :=
  Kit.valid_iff_of rfl x y

theorem ecdh_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : ecdhRV.pre s) :
    ∃ t s', Exec isa ecdhBrainpoolP512r1 s t s' ∧ abiPreserved s s' ∧ ecdhRV.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hs
  obtain ⟨t, s', he, h⟩ := kit.ecdh_ok hL ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  exact ⟨t, s', he, h⟩

end VG.Proof.Ecdh.RISCV64.BrainpoolP512r1
