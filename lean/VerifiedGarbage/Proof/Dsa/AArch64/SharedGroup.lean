module
public import VerifiedGarbage.Impl.Dsa.AArch64.SharedPower
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
public import VerifiedGarbage.Proof.Dsa.SharedPower
import VerifiedGarbage.Proof.Dsa.AArch64.SharedBucket
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The exponents' bytes, three at a time from the end

`group` takes the last bytes not yet taken of both exponents, three unless
fewer are left: their values go to `sV` and `sMaskX`, and the count of their
three-bit digits to `sBit`. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.SharedPower VG.Proof.Dsa.Shared

/-- The branch on a number in a register. -/
theorem eval_zero_reg {s : State} {r : Reg} {a : Nat} (h : s.gpr r = BitVec.ofNat 64 a) (ha : a < 2 ^ 64) :
    isa.eval (.zero .x r) s = some (decide (a = 0)) := by
  rw [eval_zero, h, eq_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

/-- A byte shifted up into the clear bits of a value. -/
theorem or_shl {a b sh : Nat} (ha : a < 2 ^ sh) (hb : b < 256) (hsh : sh + 8 ≤ 64) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 b <<< sh = BitVec.ofNat 64 (a + 2 ^ sh * b) := by
  have hp : 2 ^ sh * 256 ≤ 2 ^ 64 := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) hsh
  have hb' : 2 ^ sh * b + 2 ^ sh ≤ 2 ^ sh * 256 := by
    have := Nat.mul_le_mul_left (2 ^ sh) (show b + 1 ≤ 256 by omega_arith)
    rwa [Nat.mul_add, Nat.mul_one] at this
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega_arith),
    Nat.shiftLeft_eq, Nat.mul_comm b, Nat.mod_eq_of_lt (show 2 ^ sh * b < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show a + 2 ^ sh * b < 2 ^ 64 by omega_arith), Nat.or_comm, Nat.mul_comm, ← Nat.shiftLeft_eq,
    ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.add_comm]

/-- The registers between the group's bytes: `c` bytes left, the pointers
at the bytes just read, and the values so far. -/
structure GroupRegs (s : State) (xp qp : Addr) (c a a' n : Nat) (t : State) : Prop where
  x4 : t.gpr .x4 = BitVec.ofNat 64 c
  x1 : t.gpr .x1 = xp + BitVec.ofNat 64 c
  x2 : t.gpr .x2 = qp + BitVec.ofNat 64 c
  x5 : t.gpr .x5 = BitVec.ofNat 64 a
  x6 : t.gpr .x6 = BitVec.ofNat 64 a'
  x3 : t.gpr .x3 = BitVec.ofNat 64 n
  mem : t.mem = s.mem
  keep : Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7] s t

theorem groupHead_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc r : Nat} {xp qp : Addr}
    {xb qb : List Byte} (hc : CExpCtx s P wx minv N Xc) (hr1 : 1 ≤ r) (hrx : r ≤ xb.length)
    (hrq : r ≤ qb.length)
    (hI : word s.mem P (8 * Crt.sI) = BitVec.ofNat 64 r) (hE : word s.mem P (8 * Crt.sExp) = xp)
    (hS : word s.mem P (8 * Crt.sSrc) = qp)
    (hxrd : ∀ i < xb.length, InRegions (s.rd ++ s.wr) (xp + BitVec.ofNat 64 i) 1)
    (hxv : ∀ i (h : i < xb.length), s.mem (xp + BitVec.ofNat 64 i) = xb[i])
    (hqrd : ∀ i < qb.length, InRegions (s.rd ++ s.wr) (qp + BitVec.ofNat 64 i) 1)
    (hqv : ∀ i (h : i < qb.length), s.mem (qp + BitVec.ofNat 64 i) = qb[i]) :
    WP isa (.block groupHead) s
      (GroupRegs s xp qp (r - 1) (xb[r - 1]'(by omega_arith)).toNat (qb[r - 1]'(by omega_arith)).toNat 3) := by
  refine WP.mono (WP.keep [.x1, .x2, .x3, .x4, .x5, .x6] (Q := fun t =>
    t.gpr .x4 = BitVec.ofNat 64 (r - 1) ∧ t.gpr .x1 = xp + BitVec.ofNat 64 (r - 1) ∧
    t.gpr .x2 = qp + BitVec.ofNat 64 (r - 1) ∧
    t.gpr .x5 = BitVec.ofNat 64 (xb[r - 1]'(by omega_arith)).toNat ∧
    t.gpr .x6 = BitVec.ofNat 64 (qb[r - 1]'(by omega_arith)).toNat ∧
    t.gpr .x3 = BitVec.ofNat 64 3 ∧ t.mem = s.mem) ?_ rfl rfl rfl) fun t ⟨⟨h4, h1, h2, h5, h6, h3, hm⟩, k⟩ =>
      ⟨h4, h1, h2, h5, h6, h3, hm, k.mono (by decide)⟩
  have e1 : (1 : BitVec 64) = BitVec.ofNat 64 1 := rfl
  brun [groupHead, hc.good.x0, hdr_enc (show Crt.sI < 32 by decide), hdr_enc (show Crt.sExp < 32 by decide),
    hdr_enc (show Crt.sSrc < 32 by decide), hc.ld (i := Crt.sI) (by decide), hc.ld (i := Crt.sExp) (by decide),
    hc.ld (i := Crt.sSrc) (by decide), hI, hE, hS, e1, VG.Offset.ofNat_sub_ofNat hr1,
    hxrd (r - 1) (by omega_arith), hqrd (r - 1) (by omega_arith), zext_byte, hxv (r - 1) (by omega_arith),
    hqv (r - 1) (by omega_arith)]

/-- The next byte down of each exponent, `sh` bits up. -/
theorem groupMore_ok {s u : State} {xp qp : Addr} {xb qb : List Byte} {c a a' n sh cnt : Nat}
    (hg : GroupRegs s xp qp c a a' n u) (hc1 : 1 ≤ c) (hcx : c ≤ xb.length) (hcq : c ≤ qb.length)
    (ha : a < 2 ^ sh) (ha' : a' < 2 ^ sh) (hsc : (sh = 8 ∧ cnt = 6) ∨ (sh = 16 ∧ cnt = 8))
    (hxrd : ∀ i < xb.length, InRegions (s.rd ++ s.wr) (xp + BitVec.ofNat 64 i) 1)
    (hxv : ∀ i (h : i < xb.length), s.mem (xp + BitVec.ofNat 64 i) = xb[i])
    (hqrd : ∀ i < qb.length, InRegions (s.rd ++ s.wr) (qp + BitVec.ofNat 64 i) 1)
    (hqv : ∀ i (h : i < qb.length), s.mem (qp + BitVec.ofNat 64 i) = qb[i]) :
    WP isa (.block (groupMore sh cnt)) u
      (GroupRegs s xp qp (c - 1) (a + 2 ^ sh * (xb[c - 1]'(by omega_arith)).toNat)
        (a' + 2 ^ sh * (qb[c - 1]'(by omega_arith)).toNat) cnt) := by
  have e1 : (1 : BitVec 64) = BitVec.ofNat 64 1 := rfl
  have hsh : sh + 8 ≤ 64 := by omega_using [hsc]
  have p (z : Addr) : z + BitVec.ofNat 64 c - BitVec.ofNat 64 1 = z + BitVec.ofNat 64 (c - 1) := by
    rw [show z + BitVec.ofNat 64 c = z + BitVec.ofNat 64 (c - 1) + BitVec.ofNat 64 1 by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.sub_add_cancel hc1], BitVec.add_sub_cancel]
  refine WP.mono (WP.keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7] (Q := fun t =>
    t.gpr .x4 = BitVec.ofNat 64 (c - 1) ∧ t.gpr .x1 = xp + BitVec.ofNat 64 (c - 1) ∧
    t.gpr .x2 = qp + BitVec.ofNat 64 (c - 1) ∧
    t.gpr .x5 = BitVec.ofNat 64 a ||| BitVec.ofNat 64 (xb[c - 1]'(by omega_arith)).toNat <<< sh ∧
    t.gpr .x6 = BitVec.ofNat 64 a' ||| BitVec.ofNat 64 (qb[c - 1]'(by omega_arith)).toNat <<< sh ∧
    t.gpr .x3 = BitVec.ofNat 64 cnt ∧ t.mem = u.mem) ?_ rfl rfl rfl) fun t ⟨⟨h4, h1, h2, h5, h6, h3, hm⟩, k⟩ =>
      ⟨h4, h1, h2, by rw [h5, or_shl ha (xb[c - 1]'(by omega_arith)).isLt hsh],
        by rw [h6, or_shl ha' (qb[c - 1]'(by omega_arith)).isLt hsh], h3, hm.trans hg.mem,
        (hg.keep.trans k).mono (by decide)⟩
  rcases hsc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  brun [groupMore, hg.x4, hg.x1, hg.x2, hg.x5, hg.x6, e1, VG.Offset.ofNat_sub_ofNat hc1, p,
    hg.keep.rd, hg.keep.wr, hg.mem, hxrd (c - 1) (by omega_arith), hqrd (c - 1) (by omega_arith), zext_byte,
    hxv (c - 1) (by omega_arith), hqv (c - 1) (by omega_arith)]

theorem groupEnd_ok {s u : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc c a a' n : Nat} {xp qp : Addr}
    (hc : CExpCtx s P wx minv N Xc) (hg : GroupRegs s xp qp c a a' n u) :
    WP isa (.block groupEnd) u fun t =>
      t.mem = (((s.mem.writeW (off P (8 * Crt.sI)) (BitVec.ofNat 64 c)).writeW (off P (8 * Crt.sV))
        (BitVec.ofNat 64 a)).writeW (off P (8 * Crt.sMaskX)) (BitVec.ofNat 64 a')).writeW
          (off P (8 * Crt.sBit)) (BitVec.ofNat 64 n) ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7] s t := by
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = (((s.mem.writeW (off P (8 * Crt.sI))
      (BitVec.ofNat 64 c)).writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 a)).writeW (off P (8 * Crt.sMaskX))
        (BitVec.ofNat 64 a')).writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 n)) ?_ rfl rfl rfl)
    fun t ⟨hm, k⟩ => ⟨hm, (hg.keep.trans k).mono (by decide)⟩
  have h0 : u.gpr .x0 = P := (hg.keep.gpr .x0 (by decide)).trans hc.good.x0
  brun [groupEnd, h0, hdr_enc (show Crt.sI < 32 by decide), hdr_enc (show Crt.sV < 32 by decide),
    hdr_enc (show Crt.sMaskX < 32 by decide), hdr_enc (show Crt.sBit < 32 by decide), hg.keep.wr,
    hc.st (i := Crt.sI) (by decide), hc.st (i := Crt.sV) (by decide), hc.st (i := Crt.sMaskX) (by decide),
    hc.st (i := Crt.sBit) (by decide), hg.x4, hg.x5, hg.x6, hg.x3, hg.mem]

/-- The group of the bytes below `r`, of which `sI` says `r` are left:
`r - 3` are then left, the group's values are in `sV` and `sMaskX`, and its
digits' count in `sBit`. -/
theorem group_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc r : Nat} {xp qp : Addr}
    {xb qb : List Byte} (hc : CExpCtx s P wx minv N Xc) (hr1 : 1 ≤ r) (hrx : r ≤ xb.length)
    (hrq : r ≤ qb.length) (hr64 : r < 2 ^ 64)
    (hI : word s.mem P (8 * Crt.sI) = BitVec.ofNat 64 r) (hE : word s.mem P (8 * Crt.sExp) = xp)
    (hS : word s.mem P (8 * Crt.sSrc) = qp)
    (hxrd : ∀ i < xb.length, InRegions (s.rd ++ s.wr) (xp + BitVec.ofNat 64 i) 1)
    (hxv : ∀ i (h : i < xb.length), s.mem (xp + BitVec.ofNat 64 i) = xb[i])
    (hqrd : ∀ i < qb.length, InRegions (s.rd ++ s.wr) (qp + BitVec.ofNat 64 i) 1)
    (hqv : ∀ i (h : i < qb.length), s.mem (qp + BitVec.ofNat 64 i) = qb[i]) :
    WP isa group s fun t =>
      t.mem = (((s.mem.writeW (off P (8 * Crt.sI)) (BitVec.ofNat 64 (r - 3))).writeW (off P (8 * Crt.sV))
        (BitVec.ofNat 64 (gval xb r))).writeW (off P (8 * Crt.sMaskX)) (BitVec.ofNat 64 (gval qb r))).writeW
          (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (gcount r)) ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7] s t := by
  unfold group
  refine WP.seq (WP.mono (groupHead_ok hc hr1 hrx hrq hI hE hS hxrd hxv hqrd hqv) fun u hu => ?_)
  refine WP.seq ?_
  by_cases h1 : r - 1 = 0
  · refine WP.ite true (by rw [eval_zero_reg hu.x4 (by omega_arith), decide_eq_true h1]) (fun _ => ?_) (by simp)
    refine WP.block_nil (WP.mono (groupEnd_ok hc hu) fun t ⟨hm, k⟩ => ⟨?_, k⟩)
    have hr : r = 1 := by omega_arith
    rw [hm, (gval_one xb hr hrx).1, (gval_one qb hr hrq).1, (gval_one xb hr hrx).2,
      show r - 3 = r - 1 by omega_arith]
  · refine WP.ite false (by rw [eval_zero_reg hu.x4 (by omega_arith), decide_eq_false h1]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (groupMore_ok (sh := 8) (cnt := 6) hu (by omega_arith) (by omega_arith)
      (by omega_arith) (xb[r - 1]'(by omega_arith)).isLt (qb[r - 1]'(by omega_arith)).isLt (Or.inl ⟨rfl, rfl⟩)
      hxrd hxv hqrd hqv) fun v hv => ?_)
    by_cases h2 : r - 1 - 1 = 0
    · refine WP.ite true (by rw [eval_zero_reg hv.x4 (by omega_arith), decide_eq_true h2]) (fun _ => ?_) (by simp)
      refine WP.block_nil (WP.mono (groupEnd_ok hc hv) fun t ⟨hm, k⟩ => ⟨?_, k⟩)
      have hr : r = 2 := by omega_arith
      rw [hm, (gval_two xb hr hrx).1, (gval_two qb hr hrq).1, (gval_two xb hr hrx).2,
        show r - 3 = r - 1 - 1 by omega_arith]
    · refine WP.ite false (by rw [eval_zero_reg hv.x4 (by omega_arith), decide_eq_false h2]) (by simp)
        (fun _ => ?_)
      have b1 := (xb[r - 1]'(by omega_arith)).isLt
      have b2 := (xb[r - 1 - 1]'(by omega_arith)).isLt
      have c1 := (qb[r - 1]'(by omega_arith)).isLt
      have c2 := (qb[r - 1 - 1]'(by omega_arith)).isLt
      refine WP.mono (groupMore_ok (sh := 16) (cnt := 8) hv (by omega_arith) (by omega_arith)
        (by omega_arith) (by omega_arith) (by omega_arith) (Or.inr ⟨rfl, rfl⟩) hxrd hxv hqrd hqv) fun z hz => ?_
      refine WP.mono (groupEnd_ok hc hz) fun t ⟨hm, k⟩ => ⟨?_, k⟩
      have hr : 3 ≤ r := by omega_arith
      rw [hm, (gval_three xb hr hrx).1, (gval_three qb hr hrq).1, (gval_three xb hr hrx).2,
        show r - 3 = r - 1 - 1 - 1 by omega_arith]

end VG.Proof.Dsa.AArch64.SharedPower
