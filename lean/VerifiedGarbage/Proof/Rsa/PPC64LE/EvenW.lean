module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Rsa.PPC64LE.WordLoops
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# The choice between words and digits

`evenW_ok`: `evenW even odd` runs `even` for an even `w` and `odd` for an
odd one, having changed only `r0`. For an even `w = 2 m`, `num` is the value
of `m` words (`num_words`) and arrays apart are apart as words (`aheadW`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Loops
open VG.Impl.Rsa.PPC64LE.Keys (evenW)
open VG.Proof.Rsa.KeyWorkspace (arr S num)

theorem and_one_ofNat {w : Nat} (hw : w < 2 ^ 64) :
    BitVec.ofNat 64 w &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (w % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw,
    Nat.and_one_is_mod]
  omega

theorem lsr1_ofNat {w : Nat} (hw : w < 2 ^ 64) : BitVec.ofNat 64 w >>> 1 = BitVec.ofNat 64 (w / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt (by omega)]

/-- `evenW`: the words for an even `w`, the digits for an odd one. -/
theorem evenW_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) {even odd : Prog isa}
    {Q : State → Prop}
    (he : w % 2 = 0 → ∀ t : State, t.mem = s.mem → Keep [.r0] s t → WP isa even t Q)
    (ho : w % 2 = 1 → ∀ t : State, t.mem = s.mem → Keep [.r0] s t → WP isa odd t Q) :
    WP isa (evenW even odd) s Q := by
  have hw : w < 2 ^ 64 := by have := h.wle; omega
  rw [evenW, WP.seq_iff]
  refine WP.mono (WP.keep [.r0] (Q := fun x => x.gpr .r0 = BitVec.ofNat 64 (w % 2) ∧ x.mem = s.mem) ?_
    (by decide)) fun t ⟨⟨a0, mt⟩, kt⟩ => ?_
  · prun [h.r29, and_one_ofNat hw]
  · refine WP.ite (decide (w % 2 = 0)) (eval_zero_ofNat t .r0 (by omega) a0) (fun e => he (of_decide_eq_true e) t mt kt)
      (fun e => ho (by have := of_decide_eq_false e; omega) t mt kt)

/-- An even number of digits is half as many words. -/
theorem num_words (m : Mem) (B : Addr) {w : Nat} (hw : w % 2 = 0) (j : Nat) :
    num m B w j = wordsVal m B (arr w j) (w / 2) := by
  rw [wordsVal_eq_val32, show 2 * (w / 2) = w by omega]

theorem aheadW {dO dA w : Nat} (hw : w % 2 = 0) (h : Ahead dO dA w) : AheadW dO dA (w / 2) := by
  unfold Ahead at h; unfold AheadW; omega

end VG.Proof.Rsa.PPC64LE.Keys
