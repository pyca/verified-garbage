module

public import VerifiedGarbage.Impl.Dsa.AArch64.Random
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! Correctness and memory framing of random-tape suffix copying. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.WriteBytes (writeW8_apply)

structure RandomCopyInv (s : State) (src out : Addr) (n j : Nat) (t : State) : Prop where
  keep : Keep [.x0, .x12, .x2, .x9] s t
  rsi : t.gpr .x12 = src + BitVec.ofNat 64 j
  rdx : t.gpr .x2 = out + BitVec.ofNat 64 j
  rcx : t.gpr .x9 = BitVec.ofNat 64 (n - j)
  bytes : ∀ i < j, t.mem (out + BitVec.ofNat 64 i) = s.mem (src + BitVec.ofNat 64 i)
  frame : ∀ x, (∀ i < j, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x

theorem random_copyLoop_ok {s : State} {src out : Addr} {n : Nat}
    (hsi : s.gpr .x12 = src) (hdx : s.gpr .x2 = out) (hcx : s.gpr .x9 = BitVec.ofNat 64 n)
    (h1 : 0 < n) (h64 : n < 2 ^ 64)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ j < n, src + BitVec.ofNat 64 i ≠ out + BitVec.ofNat 64 j) :
    WP isa (.loop (.block VG.Impl.Dsa.AArch64.Random.copyByte) (.nonzero .x .x9)) s fun t =>
      (∀ i < n, t.mem (out + BitVec.ofNat 64 i) = s.mem (src + BitVec.ofNat 64 i)) ∧
      (∀ x, (∀ i < n, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.x0, .x12, .x2, .x9] s t := by
  refine WP.mono (wp_countdown (N := n) h64 h1 (fun j t => RandomCopyInv s src out n j t)
    ?_ ⟨Keep.refl _ _, by simpa using hsi, by simpa using hdx, by simpa using hcx,
      fun i hi => absurd hi (by omega), fun x _ => rfl⟩ hcx)
    fun t ht => ⟨ht.bytes, ht.frame, ht.keep⟩
  intro j hj t ht hcount
  have hrd : InRegions (t.rd ++ t.wr) (src + BitVec.ofNat 64 j) 1 := by
    rw [ht.keep.rd, ht.keep.wr]; exact hr j hj
  have hwr : InRegions t.wr (out + BitVec.ofNat 64 j) 1 := by
    rw [ht.keep.wr]; exact hw j hj
  have hval := ht.frame (src + BitVec.ofNat 64 j) (fun i hi => hsep j hj i (by omega))
  refine WP.mono (WP.keep [.x0, .x12, .x2, .x9] (Q := fun u =>
    u.mem = t.mem.writeW (out + BitVec.ofNat 64 j) (s.mem (src + BitVec.ofNat 64 j)) ∧
    u.gpr .x12 = src + BitVec.ofNat 64 (j + 1) ∧ u.gpr .x2 = out + BitVec.ofNat 64 (j + 1) ∧
    u.gpr .x9 = BitVec.ofNat 64 (n - (j + 1))) ?_ rfl rfl rfl)
    fun u ⟨⟨hum, husi, hudx, hucx⟩, hku⟩ => ?_
  · unfold VG.Impl.Dsa.AArch64.Random.copyByte
    have hp : BitVec.ofNat 64 (n - j) - (1#64) = BitVec.ofNat 64 (n - (j + 1)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    brun [ht.rsi, ht.rdx, ht.rcx, hrd, hwr, read_one, hval,
      BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide), BitVec.setWidth_eq,
      hp, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
      BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide), BitVec.setWidth_eq]
    rfl
  · refine ⟨⟨(ht.keep.trans hku).mono (by decide), husi, hudx, hucx, ?_, ?_⟩, ?_⟩
    · intro i hi
      rw [hum, writeW8_apply]
      by_cases hij : i = j
      · subst i; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
        exact ht.bytes i (by omega)
    · intro x hx
      rw [hum, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
      exact ht.frame x fun i hi => hx i (by omega)

    · rw [hucx, hcount]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega

/-- An empty suffix does not touch memory. -/
theorem random_copyRest_ok {s : State} {src out : Addr} {n : Nat}
    (hp : s.gpr .x12 = src) (hd : s.gpr .x2 = out) (hn : s.gpr .x9 = BitVec.ofNat 64 n)
    (hbound : n < 2 ^ 64)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ j < n, src + BitVec.ofNat 64 i ≠ out + BitVec.ofNat 64 j) :
    WP isa VG.Impl.Dsa.AArch64.Random.copyRest s fun t =>
      (∀ i < n, t.mem (out + BitVec.ofNat 64 i) = s.mem (src + BitVec.ofNat 64 i)) ∧
      (∀ x, (∀ i < n, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.x0, .x12, .x2, .x9] s t := by
  unfold VG.Impl.Dsa.AArch64.Random.copyRest
  by_cases h0 : n = 0
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => WP.block_nil ?_)
    · simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hn, h0]
      rfl
    · exact ⟨fun i hi => False.elim (by omega), fun _ _ => rfl, Keep.refl _ _⟩
  · refine WP.ite true ?_ (fun _ => random_copyLoop_ok hp hd hn (by omega) hbound hr hw hsep)
      (fun h => Bool.noConfusion h)
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hn]
    have hz : BitVec.ofNat 64 n ≠ (0#64) := by
      intro he
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound] at this
      exact h0 this
    change some (!(BitVec.ofNat 64 n == (0#64))) = some true
    rw [beq_eq_false_iff_ne.mpr hz]
    rfl

end VG.Proof.Dsa.AArch64
