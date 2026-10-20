module

public import VerifiedGarbage.Proof.Dsa.AArch64.ReduceByte
public import VerifiedGarbage.Proof.Dsa.Arithmetic
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! # The nonempty streaming reduction loop -/

@[expose] public section

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
