module

public import VerifiedGarbage.Impl.Dsa.X86_64.Random
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.WriteBytes
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Words

/-! # Correctness and memory framing of the random-tape copy loop -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.WriteBytes (writeW8_apply)

structure RandomCopyInv (s : State) (src out : Addr) (n j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .r10, .rdx, .r11] s t
  r10 : t.gpr .r10 = src + BitVec.ofNat 64 j
  rdx : t.gpr .rdx = out + BitVec.ofNat 64 j
  r11 : t.gpr .r11 = BitVec.ofNat 64 (n - j)
  bytes : ∀ i < j, t.mem (out + BitVec.ofNat 64 i) = s.mem (src + BitVec.ofNat 64 i)
  frame : ∀ x, (∀ i < j, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x

theorem random_copyLoop_ok {s : State} {src out : Addr} {n : Nat}
    (hsi : s.gpr .r10 = src) (hdx : s.gpr .rdx = out) (hcx : s.gpr .r11 = BitVec.ofNat 64 n)
    (h1 : 0 < n) (h64 : n < 2 ^ 64)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ j < n, src + BitVec.ofNat 64 i ≠ out + BitVec.ofNat 64 j) :
    WP isa (.loop (.block VG.Impl.Dsa.X86_64.Random.copyByte) .ne) s fun t =>
      (∀ i < n, t.mem (out + BitVec.ofNat 64 i) = s.mem (src + BitVec.ofNat 64 i)) ∧
      (∀ x, (∀ i < n, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.rax, .r10, .rdx, .r11] s t := by
  refine WP.mono (wp_upto (a := 0) (N := n) h1 (RandomCopyInv s src out n ·) ?_ (fun t h => h)
    ⟨Keep.refl _ _, by simpa using hsi, by simpa using hdx, by simpa using hcx,
      fun i hi => absurd hi (by omega), fun x _ => rfl⟩)
    fun t ht => ⟨ht.bytes, ht.frame, ht.keep⟩
  intro j _ hj t ht
  have hrd : InRegions (t.rd ++ t.wr) (src + BitVec.ofNat 64 j) 1 := by
    rw [ht.keep.2.1, ht.keep.2.2]; exact hr j hj
  have hwr : InRegions t.wr (out + BitVec.ofNat 64 j) 1 := by
    rw [ht.keep.2.2]; exact hw j hj
  have hval := ht.frame (src + BitVec.ofNat 64 j) (fun i hi => hsep j hj i (by omega))
  refine WP.mono (WP.keep [.rax, .r10, .rdx, .r11] (Q := fun u =>
    u.mem = t.mem.writeW (out + BitVec.ofNat 64 j) (s.mem (src + BitVec.ofNat 64 j)) ∧
    u.gpr .r10 = src + BitVec.ofNat 64 (j + 1) ∧ u.gpr .rdx = out + BitVec.ofNat 64 (j + 1) ∧
    u.gpr .r11 = BitVec.ofNat 64 (n - (j + 1)) ∧ u.zf = some (decide (j + 1 = n))) ?_ rfl)
    fun u ⟨⟨hum, husi, hudx, hucx, huz⟩, hku⟩ => ?_
  · unfold VG.Impl.Dsa.X86_64.Random.copyByte
    xrun [State.ea, ht.r10, ht.rdx, ht.r11,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hrd, hwr, hval,
      ofNat64_pred (show 1 ≤ n - j by omega) (by omega), BitVec.add_assoc, ofNat_add_one,
      ofNat64_beq_zero (show n - j - 1 < 2 ^ 64 by omega)]
    refine ⟨?_, by rw [show n - j - 1 = n - (j + 1) by omega], decide_eq_decide.mpr (by omega)⟩
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  · refine ⟨huz, (ht.keep.trans hku).mono (by decide), husi, hudx, hucx, ?_, ?_⟩
    · intro i hi
      rw [hum, writeW8_apply]
      by_cases hij : i = j
      · subst i; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
        exact ht.bytes i (by omega)
    · intro x hx
      rw [hum, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
      exact ht.frame x fun i hi => hx i (by omega)

/-- The suffix copy also accepts an empty suffix without touching memory. -/
theorem random_copyRest_ok {s : State} {src out : Addr} {n : Nat}
    (hp : s.gpr .r10 = src) (hd : s.gpr .rdx = out) (hn : s.gpr .r11 = BitVec.ofNat 64 n)
    (hz : s.zf = some (decide (n = 0))) (hbound : n < 2 ^ 64)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ j < n, src + BitVec.ofNat 64 i ≠ out + BitVec.ofNat 64 j) :
    WP isa VG.Impl.Dsa.X86_64.Random.copyRest s fun t =>
      (∀ i < n, t.mem (out + BitVec.ofNat 64 i) = s.mem (src + BitVec.ofNat 64 i)) ∧
      (∀ x, (∀ i < n, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.rax, .r10, .rdx, .r11] s t := by
  unfold VG.Impl.Dsa.X86_64.Random.copyRest
  by_cases h0 : n = 0
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => WP.block_nil ?_)
    · simp only [eval, hz, h0, decide_true, Option.map_some, Bool.not_true]
    · exact ⟨fun i hi => False.elim (by omega), fun _ _ => rfl, Keep.refl _ _⟩
  · refine WP.ite true ?_ (fun _ => random_copyLoop_ok hp hd hn (by omega) hbound hr hw hsep)
      (fun h => Bool.noConfusion h)
    simp only [eval, hz, h0, decide_false, Option.map_some, Bool.not_false]

end VG.Proof.Dsa.X86_64
