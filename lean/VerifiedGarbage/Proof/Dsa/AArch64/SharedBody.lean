module
public import VerifiedGarbage.Impl.Dsa.AArch64.SharedPower
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
public import VerifiedGarbage.Proof.Dsa.AArch64.Frame
public import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.AArch64.SharedBucket
import VerifiedGarbage.Proof.Dsa.AArch64.SharedCombine
import VerifiedGarbage.Proof.Dsa.AArch64.SharedDigits
import VerifiedGarbage.Proof.Dsa.AArch64.SharedTable
import VerifiedGarbage.Proof.Dsa.AArch64.OneScan
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.EncodePower
import VerifiedGarbage.Proof.Dsa.AArch64.Load
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtRedc
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # g^x and the mask of g^q = 1, in the prime's workspace -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Impl.Dsa.AArch64.SharedPower VG.Proof.Dsa.Shared

/-- The mask of `[aT] = 1` into `sMaskX`: nothing else of the table or the
header changes. -/
theorem orderCheck_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) :
    WP isa orderCheck s fun t => CExpCtx t P wx minv N Xc ∧
      word t.mem P (8 * Crt.sMaskX) = mask (decide (wv s.mem P (slot wx Crt.aT) wx = 1)) ∧
      (∀ j < 16, wv t.mem P (slot wx (8 + j)) wx = wv s.mem P (slot wx (8 + j)) wx) ∧
      (∀ j < 8, j ≠ aX → wv t.mem P (slot wx j) wx = wv s.mem P (slot wx j) wx) ∧
      (∀ i < 32, i ≠ Crt.sMaskX → word t.mem P (8 * i) = word s.mem P (8 * i)) ∧
      Frm P (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.scrT.nowrap
  have hnZ : P.toNat + slot wx 8 ≤ 2 ^ 64 := by omega_arith
  unfold orderCheck
  refine wp_seqs_append (by simp [Crt.copyArr]) (by simp) (WP.mono (copyArr_ok hc.good (Nat.le_refl _)
    (by omega_arith) (by omega_arith) (o := aX) (a := Crt.aT) (by decide) (by decide) (by decide))
    fun u ⟨hX, ou, ku⟩ => ?_)
  have au : Arrays P wx [aX] s.mem u.mem :=
    Arrays.of_outside (List.mem_singleton_self _) ou (Nat.le_refl _) (by omega_arith)
  have hcu := ctx_of_arrays hc au (by decide) (by decide) ku.wr (ku.gpr .x0 (by decide))
  simp only [seqs]
  refine WP.seq (WP.mono (oneScan_ok hcu.good (Nat.le_refl _) hw (by omega_arith)) fun v ⟨h15, hmv, kv⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (zeroMask_ok .x15 false) fun z ⟨h3, hmz, kz⟩ => ?_
  have h0 : z.gpr .x0 = P := (kz.gpr .x0 (by decide)).trans ((kv.gpr .x0 (by decide)).trans hcu.good.x0)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = z.mem.writeW (off P (8 * Crt.sMaskX)) (z.gpr .x3))
    (by
      brun [h0, hdr_enc (show Crt.sMaskX < 32 by decide), kz.wr, kv.wr, hcu.st (i := Crt.sMaskX) (by decide)])
    rfl rfl rfl) fun t ⟨hmt, kt⟩ => ?_
  have hmt' : t.mem = u.mem.writeW (off P (8 * Crt.sMaskX)) (z.gpr .x3) := by rw [hmt, hmz, hmv]
  have ot : Outside P 136 120 u.mem t.mem := by rw [hmt']; exact fn_outside _ P _ (by decide) (by decide)
  have kall : Keep mmRegs s t := (((ku.trans kv).trans (kz.mono (rs' := mmRegs) (by decide))).trans kt).mono
    (by decide)
  have kut : Keep mmRegs u t := ((kv.trans (kz.mono (rs' := mmRegs) (by decide))).trans kt).mono (by decide)
  refine ⟨ctx_of_fn hcu ot kut.wr (kut.gpr .x0 (by decide)), ?_, fun j hj => ?_, fun j hj hjx => ?_,
    fun i hi h => ?_, (arrays_work au (by decide)).trans (fn_work ot), kall⟩
  · rw [hmt', word_writeW_self, h3]
    simp only [Bool.false_eq_true, ↓reduceIte]
    congr 1
    rw [← hX]
    exact decide_eq_decide.mpr h15
  · rw [fn_ent ot hn hj, arr_ent au (by decide) hn hj]
  · rw [fn_arr ot hn hj, au.wv_of_not_mem hj (by simpa using hjx) hnZ]
  · rw [hmt', hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h), au.hslot hi]

/-- A word of the parent's workspace through a store to a slot of the child's header. -/
theorem child_store_parent {t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx t B Z o w wx minv) (m : Mem) {i d : Nat} (v : BitVec 64) (hi : i < 32) (hd : d + 8 ≤ o) :
    word (m.writeW (off B (o + 8 * i)) v) B d = word m B d := by
  have hn := hc.scr.nowrap
  have hhi := hc.hi
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  rw [store_off]
  exact (Frm.of_outside (rs := [(8 * i, 8)]) (writeW_outside m (off B o) (d := 8 * i) v (by omega_arith))
    (by simp)).word_below (L := slot wx 8)
    (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_arith) (by omega_arith) (by omega_arith) hd

/-- The exponents' pointers and their length, from the parent's header. -/
theorem expInit_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) {xp qp : Addr} {L : Nat}
    (he : word s.mem B (8 * arg2) = xp) (hel : word s.mem B (8 * arg2Len) = BitVec.ofNat 64 L)
    (hq : word s.mem B Field.q.offset = qp) :
    WP isa (.block expInit) s fun t =>
      t.mem = ((s.mem.writeW (off (off B o) (8 * Crt.sExp)) xp).writeW (off (off B o) (8 * Crt.sSrc)) qp).writeW
        (off (off B o) (8 * Crt.sI)) (BitVec.ofNat 64 L) ∧ Keep [.x3, .x5] s t := by
  have hlo := hc.lo
  have hhi := hc.hi
  have h384 : 384 ≤ slot w 8 := by unfold slot hdrBytes; omega_arith
  have hqo : Field.q.offset = 264 := rfl
  have hq₁ : (s.mem.writeW (off B (o + 8 * Crt.sExp)) xp).readW (off B Field.q.offset) 64 = qp :=
    (child_store_parent hc s.mem xp (by decide) (by omega_arith)).trans hq
  have hl₂ : ((s.mem.writeW (off B (o + 8 * Crt.sExp)) xp).writeW (off B (o + 8 * Crt.sSrc)) qp).readW
      (off B (8 * arg2Len)) 64 = BitVec.ofNat 64 L :=
    ((child_store_parent hc _ qp (by decide) (by unfold arg2Len; omega_arith)).trans
      (child_store_parent hc s.mem xp (by decide) (by unfold arg2Len; omega_arith))).trans hel
  refine WP.keep _ ?_ rfl rfl rfl
  brun [SharedPower.expInit, Crt.ldw, hc.x0, hdr_enc (show Crt.sLink < 32 by decide), hdr_enc (show arg2 < 32 by decide),
    hdr_enc (show arg2Len < 32 by decide), field_enc .q, fieldAddress,
    hdr_enc (show Crt.sExp < 32 by decide), hdr_enc (show Crt.sSrc < 32 by decide),
    hdr_enc (show Crt.sI < 32 by decide), hc.ld' (show Crt.sLink < 32 by decide), hc.link',
    hc.ldn (show arg2 < 32 by decide), he, hc.st' (show Crt.sExp < 32 by decide),
    hc.scr.ld (d := Field.q.offset) (by omega_arith), hq₁,
    hc.st' (show Crt.sSrc < 32 by decide), hc.ldn (show arg2Len < 32 by decide), hl₂,
    hc.st' (show Crt.sI < 32 by decide), off_off]

theorem power_eq (mul : Nat → Nat → Nat → Prog isa) : power mul =
    seqs (([Arithmetic.constants mul, Arithmetic.load aX arg argLen, Arithmetic.encodePower mul] : List (Prog isa)) ++
      (tableInit ++ (([.block SharedPower.expInit, digits mul, combine mul 8, orderCheck,
        combine mul 0] : List (Prog isa)) ++ Crt.copyArr aY Crt.aT))) := rfl

/-- A source outside the scratch space, as the child's workspace sees it. -/
theorem src_out {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    {p : Addr} {bs : List Byte} (hs : Src s B Z p bs) :
    ∀ i < bs.length, slot wx 8 + tabBytes wx ≤ ofs (off B o) (p + BitVec.ofNat 64 i) := fun i hi' => by
  have hi := hc.hi
  have hBn := hc.scr.nowrap
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  have := hs.out i hi'
  rcases ofs_rebase B (p + BitVec.ofNat 64 i) (o := o) (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩
  · omega_arith
  · omega_arith

end VG.Proof.Dsa.AArch64.SharedPower
