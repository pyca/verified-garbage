import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.BoundedFour
import VerifiedGarbage.Proof.MlDsa.Sample.HalfByte

/-! The bounded sampler's vector groups preserve the standard nibble order.
Only the accepted prefix is meaningful while the parser is running; a failed
whole polynomial is cleared by the final mask. -/
namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (acceptedIndices)

/-- The four low-to-high half-bytes consumed by one vector iteration. -/
def nibbles (a b : Byte) : List Nat :=
 [a.toNat % 16, a.toNat / 16, b.toNat % 16, b.toNat / 16]

/-- Values accepted by a bounded sampler from a list of half-bytes. -/
def accepted (η : Nat) (bs : List Nat) : List Zq :=
 (bs.filter (fun b => b < rbB η)).map (fun b => ofInt (rbC η b))

theorem fold_hbTry (η : Nat) (hη : η=2 ∨ η=4) (a : List Zq) (bs : List Nat) :
    bs.foldl (hbTry η) a = a ++ accepted η bs := by
  induction bs generalizing a with
  | nil => simp [accepted]
  | cons b bs ih =>
    simp only [List.foldl_cons, ih, hbTry_eq hη]
    by_cases h : b < rbB η
    · simp [accepted, h, List.append_assoc]
    · simp [accepted, h]

theorem rbStep_two {η : Nat} {a : List Zq} (ha : a.length≤254) (b : Byte) :
    rbStep η a b = hbTry η (hbTry η a (b.toNat%16)) (b.toNat/16) := by
  have h1 := halfByteOk_le η (b.toNat%16)
  simp only [rbStep, n]
  rw [ifT (by omega), ifT (by rw [hbTry_length]; omega)]

theorem twoBytes_values {η : Nat} (hη : η=2 ∨ η=4) {a : List Zq}
    (ha : a.length≤252) (b c : Byte) :
    rbFold η a [b,c] = a ++ accepted η (nibbles b c) := by
  have h1 := halfByteOk_le η (b.toNat%16)
  have h2 := halfByteOk_le η (b.toNat/16)
  have hlen : (hbTry η (hbTry η a (b.toNat%16)) (b.toNat/16)).length≤254 := by
    simp only [hbTry_length]; omega
  rw [rbFold, rbStep_two (by omega), rbFold, rbStep_two hlen]
  simpa only [nibbles, List.foldl_cons, List.foldl_nil, rbFold] using
    fold_hbTry η hη a (nibbles b c)

theorem accepted_length (η : Nat) (bs : List Nat) : (accepted η bs).length≤bs.length := by
  simpa only [accepted, List.length_map] using List.length_filter_le (fun b => b < rbB η) bs

theorem twoBytes_length {η : Nat} (hη : η=2 ∨ η=4) {a : List Zq}
    (ha : a.length≤252) (b c : Byte) :
    (rbFold η a [b,c]).length=a.length+(accepted η (nibbles b c)).length := by
  rw [twoBytes_values hη ha, List.length_append]

/-- The fourth lane of the three-polynomial tail duplicates its first lane.
Consequently the aggregate failure test has exactly the original three inputs. -/
theorem duplicate_failure (a b c : Nat) :
    (a=0 ∧ b=0 ∧ c=0 ∧ a=0) ↔ (a=0 ∧ b=0 ∧ c=0) := by
  constructor
  · rintro ⟨ha,hb,hc,_⟩; exact ⟨ha,hb,hc⟩
  · rintro ⟨ha,hb,hc⟩; exact ⟨ha,hb,hc,ha⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
