module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Candidate
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Framework.Block

/-!
# A candidate on PPC64LE: sequences and the arrays' offsets

`wp_seqs`: a sequence, one piece at a time. `slot_lin`: an array's offset,
linear in `w`, which is how `omega` should see it (its preprocessing of
`j * (8 * (w + 2))` for larger `j` exceeds the recursion limit).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (seqs)
open VG.Proof.Bignum (slot)

theorem wp_seqs {c : Prog isa} {l : List (Prog isa)} (hl : l ≠ []) {s : State} {Q : State → Prop} :
    WP isa (seqs (c :: l)) s Q ↔ WP isa c s (fun t => WP isa (seqs l) t Q) := by
  match l, hl with
  | _ :: _, _ => exact WP.seq_iff

theorem slot_le {w j k : Nat} (h : j ≤ k) : slot w j ≤ slot w k := by
  unfold slot; have := Nat.mul_le_mul_right (8 * (w + 2)) h; omega

theorem slot0 {w : Nat} : slot w 0 = 256 := by simp [slot, VG.Impl.Bignum.hdrBytes]

/-- An array's offset, linear in `w`. -/
theorem slot_lin (w j : Nat) : slot w j = 256 + j * (8 * w) + j * 16 := by
  show VG.Impl.Bignum.hdrBytes + j * (8 * (w + 2)) = _
  rw [Nat.mul_add 8 w 2, Nat.mul_add, ← Nat.add_assoc]; rfl

end VG.Proof.RsaKeyGen.PPC64LE.Cand
