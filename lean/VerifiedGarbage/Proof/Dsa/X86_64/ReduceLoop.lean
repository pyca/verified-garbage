module

public import VerifiedGarbage.Proof.Dsa.X86_64.ReduceByte
public import VerifiedGarbage.Proof.Dsa.Arithmetic
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core

/-! # The nonempty streaming reduction loop -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- The loop consumes the entire source and computes its Horner reduction.
The measure is the public remaining-byte count; its invariant includes all
memory and register frames needed to return to the parent workspace. -/
theorem reduceLoop_ok (M : Mont) {s : State} {B p : Addr} {Z o w wx m acc : Nat}
    {minv : BitVec 64} {bytes : List Byte}
    (h : ReduceState s B Z o w wx m minv p bytes acc)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 31) (hm : 255 < m) (hodd : m % 2 = 1)
    (hnonempty : 0 < bytes.length) (hlen : bytes.length < 2 ^ 64) :
    WP isa (.loop (Arithmetic.reduceByte M.mm) .ne) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aY) wx = VG.Proof.Dsa.reduceBytes m acc bytes ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  let target := VG.Proof.Dsa.reduceBytes m acc bytes
  let Inv := fun n t => ∃ (ptr : Addr) (bs : List Byte) (a : Nat),
    bs.length = n ∧ 0 < n ∧ n < 2 ^ 64 ∧ ReduceState t B Z o w wx m minv ptr bs a ∧
    VG.Proof.Dsa.reduceBytes m a bs = target ∧
    Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t
  refine WP.loop (M := isa) (body := Arithmetic.reduceByte M.mm) (c := .ne) Inv ?_ bytes.length s ?_
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
        · change VG.X86_64.eval .ne t = some false
          simp only [VG.X86_64.eval, hz, he, decide_true, Option.map_some, Bool.not_true]
        · have hempty := List.length_eq_zero_iff.mp he
          rw [hempty] at htval
          simp only [VG.Proof.Dsa.reduceBytes, List.foldl_nil, Nat.mod_eq_of_lt ht.reduced] at htval
          exact ht.value.trans htval
      · right
        refine ⟨?_, bs.length, by simp only [List.length_cons] at hlen'; omega,
          ptr + 1, bs, _, rfl, by omega, by simp only [List.length_cons] at hlen'; omega,
          ht, htval, hf, hk⟩
        change VG.X86_64.eval .ne t = some true
        simp only [VG.X86_64.eval, hz, he, decide_false, Option.map_some, Bool.not_false]
  · exact ⟨p, bytes, acc, rfl, hnonempty, hlen, h, rfl,
      fun _ _ => rfl, Keep.refl _ _⟩

end VG.Proof.Dsa.X86_64
