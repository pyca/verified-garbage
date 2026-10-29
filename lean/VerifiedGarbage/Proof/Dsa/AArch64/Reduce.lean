module

public import VerifiedGarbage.Proof.Dsa.AArch64.Frame
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.AArch64.ReduceInit
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceSetup
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceByte
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.Contract
/-! # Complete streaming modular reduction for DSA -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/ReduceLoop.lean`, which only this module imported.
section

/-! # The nonempty streaming reduction loop -/

section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- The loop consumes the entire source and computes its Horner reduction.
The measure is the public remaining-byte count; its invariant includes all
memory and register frames needed to return to the parent workspace. -/
theorem reduceLoop_ok (M : Mont) {s : State} {B p : Addr} {Z o w wx m acc : Nat}
    {minv : BitVec 64} {bytes : List Byte}
    (h : ReduceState s B Z o w wx m minv p bytes acc)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 31) (hm : 255 < m) (hodd : m % 2 = 1)
    (hnonempty : 0 < bytes.length) (hlen : bytes.length < 2 ^ 64) :
    WP isa (.loop (Arithmetic.reduceByte M.mm) (.nonzero .x .x3)) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aY) wx = VG.Proof.Dsa.reduceBytes m acc bytes ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  let target := VG.Proof.Dsa.reduceBytes m acc bytes
  let Inv := fun n t => ∃ (ptr : Addr) (bs : List Byte) (a : Nat),
    bs.length = n ∧ 0 < n ∧ n < 2 ^ 64 ∧ ReduceState t B Z o w wx m minv ptr bs a ∧
    VG.Proof.Dsa.reduceBytes m a bs = target ∧
    Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t
  refine WP.loop (M := isa) (body := Arithmetic.reduceByte M.mm) (c := (.nonzero .x .x3)) Inv ?_ bytes.length s ?_
  · intro n u ⟨ptr, bs, a, hlen', hpos, hbound, hu, htarget, hfu, hku⟩
    cases bs with
    | nil => simp only [List.length_nil] at hlen'; omega
    | cons b bs =>
      refine WP.mono (reduceByte_ok M hu hw hw' hm hodd (by omega))
        fun t ⟨ht, hz, hft, hkt⟩ => ?_
      have hf := hfu.trans hft
      have hk := (hku.trans hkt).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
      have htval : VG.Proof.Dsa.reduceBytes m ((256 * a + b.toNat) % m) bs = target := htarget
      by_cases he : bs.length = 0
      · left
        refine ⟨?_, ht.ctx, ht.modulus, ?_, hf, hk⟩
        · change some (t.gpr .x3 != (0#64)) = some false
          rw [hz, he]
          rfl
        · have hempty := List.length_eq_zero_iff.mp he
          rw [hempty] at htval
          simp only [VG.Proof.Dsa.reduceBytes, List.foldl_nil, Nat.mod_eq_of_lt ht.reduced] at htval
          exact ht.value.trans htval
      · right
        refine ⟨?_, bs.length, by simp only [List.length_cons] at hlen'; omega,
          ptr + 1, bs, _, rfl, by omega, by simp only [List.length_cons] at hlen'; omega,
          ht, htval, hf, hk⟩
        change some (t.gpr .x3 != (0#64)) = some true
        rw [hz]
        have hnz : BitVec.ofNat 64 bs.length ≠ (0#64) := by
          intro eq
          have val := congrArg BitVec.toNat eq
          change bs.length % 2 ^ 64 = 0 at val
          have bound : bs.length < 2 ^ 64 := by simp only [List.length_cons] at hlen'; omega
          rw [Nat.mod_eq_of_lt bound] at val
          exact he val
        simp [hnz]

  · exact ⟨p, bytes, acc, rfl, hnonempty, hlen, h, rfl,
      fun _ _ => rfl, Keep.refl _ _⟩

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- Reduce an arbitrary big-endian byte string, including the empty string,
modulo an odd integer greater than 255. No primality or divisibility relation
between the source and destination moduli is required. -/
theorem reduce_ok (M : Mont) {s : State} {B p : Addr} {Z o w wx m : Nat}
    {minv : BitVec 64} {bytes : List Byte} {sp sl : Nat}
    (hc : SubCtx s B Z o w wx minv) (hw : 2 ≤ wx) (hw48 : wx ≤ 48)
    (hm : 255 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hsp : sp < 32) (hsl : sl < 32)
    (hp : word s.mem B (8 * sp) = p)
    (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bytes.length)
    (hs : Src s B Z p bytes) (hlen : bytes.length < 2 ^ 64) :
    WP isa (Arithmetic.reduce M.mm sp sl) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aY) wx = Spec.Dsa.decodeBE bytes % m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Arithmetic.reduce seqs
  refine WP.seq (WP.mono (reduceSetup_ok M hc hw hw48 (by omega) hodd hn hinv)
    fun u ⟨hcu, hmu, hur, huy, hux, hfu, hku⟩ => ?_)
  refine WP.seq (WP.mono (reduceInit_ok hcu hmu hsp hsl
    ((work_parent hc hfu hsp).trans hp) ((work_parent hc hfu hsl).trans hl) hlen)
    fun v ⟨hcv, hmv, harr, hvp, hvl, hvz, hfv, hkv⟩ => ?_)
  have hf := hfu.trans hfv
  have hk := (hku.trans hkv).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
  have hvy := (harr aY (by decide)).trans huy
  have hvx := (harr aX (by decide)).trans hux
  have hv : ReduceState v B Z o w wx m minv p bytes 0 :=
    ⟨hcv, hmv, (harr aXm (by decide)).trans hur,
      fun i hi _ => (wv_eq_zero_iff _ _ _ _).mp hvx i hi,
      hvy, by omega, hvp, hvl, work_source hc hf hk hs⟩
  by_cases he : bytes.length = 0
  · refine WP.ite true ?_ (fun _ => WP.block_nil ?_) (fun h => Bool.noConfusion h)
    · change some (v.gpr .x3 == (0#64)) = some true
      rw [hvz, he]
      rfl
    · refine ⟨hcv, hmv, ?_, hf, hk⟩
      rw [List.length_eq_zero_iff.mp he]
      exact hvy
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
    · change some (v.gpr .x3 == (0#64)) = some false
      rw [hvz]
      have hnz : BitVec.ofNat 64 bytes.length ≠ (0#64) := by
        intro eq
        have val := congrArg BitVec.toNat eq
        change bytes.length % 2 ^ 64 = 0 at val
        rw [Nat.mod_eq_of_lt hlen] at val
        exact he val
      simp [hnz]

    · refine WP.mono (reduceLoop_ok M hv hw (by omega) hm hodd (by omega) hlen)
        fun t ⟨hct, hmt, htval, hft, hkt⟩ => ?_
      rw [VG.Proof.Dsa.reduceBytes_eq] at htval
      exact ⟨hct, hmt, htval, hf.trans hft, (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
