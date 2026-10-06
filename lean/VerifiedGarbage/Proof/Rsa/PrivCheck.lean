import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Spec.Rsa.Contract

/-!
# The checked RSA private-key operation: the check's logic, on every target

What BoringSSL's check of the private-key operation computes from the values
the CRT and the public operation return and write, as every target's
`vg_rsa_private_checked` computes it without branches: the mask of the
release (`relMask`), the result (`result`, `checkResult`), whether `M` is
released (`released`), and that this is `privateChecked`'s outcome
(`outcome_eq`) and releases only a result that passes the check
(`checkResult_sound`).
-/

namespace VG.Proof.Rsa

open VG

/-- `r₂ & r₁ & r₃ & 1`. -/
def gOf (r₂ r₁ r₃ : BitVec 64) : BitVec 64 := r₂ &&& r₁ &&& r₃ &&& 1

theorem gOf_cases (r₂ r₁ r₃ : BitVec 64) : gOf r₂ r₁ r₃ = 0 ∨ gOf r₂ r₁ r₃ = 1 := by
  unfold gOf
  generalize r₂ &&& r₁ &&& r₃ = x
  have h : (x &&& 1).toNat = x.toNat % 2 := by
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h0 | h1
  · exact .inl (BitVec.eq_of_toNat_eq (by rw [h, h0]; rfl))
  · exact .inr (BitVec.eq_of_toNat_eq (by rw [h, h1]; rfl))

theorem zext_xor_eq_zero (a b : Byte) : (BitVec.setWidth 64 a ^^^ BitVec.setWidth 64 b = 0) ↔ a = b := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    have := congrArg (BitVec.setWidth 8) h
    simpa using this
  · rintro rfl; rfl

/-- The release mask and the result. -/
def relMask (g : BitVec 64) (eq : Bool) : BitVec 64 := if g = 1 ∧ eq = true then BitVec.allOnes 64 else 0
def result (g : BitVec 64) (eq : Bool) : BitVec 64 := if g = 1 then (if eq then 1 else 2) else 0

theorem low_and_mask (b : Byte) (g : BitVec 64) (eq : Bool) :
    (BitVec.setWidth 64 b &&& relMask g eq).setWidth 8 = if g = 1 ∧ eq = true then b else 0 := by
  unfold relMask
  split
  · rw [BitVec.and_allOnes]; simp
  · rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.and_zero]; rfl

theorem bytesAt_eq_iff (m : Mem) (a b : Addr) (k : Nat) :
    Spec.Rsa.bytesAt m a k = Spec.Rsa.bytesAt m b k ↔
      ∀ i < k, m (a + BitVec.ofNat 64 i) = m (b + BitVec.ofNat 64 i) := by
  simp only [Spec.Rsa.bytesAt]
  constructor
  · intro h i hi
    have := congrArg (fun l => l[i]?) h
    simpa [hi] using this
  · intro h
    exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-! ## Bits -/

theorem and1_toNat (x : BitVec 64) : (x &&& 1).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem and1_eq_one (x : BitVec 64) : x &&& 1 = 1 ↔ x.toNat % 2 = 1 := by
  rw [← BitVec.toNat_inj, and1_toNat]; rfl

theorem gOf_eq_one (a b c : BitVec 64) : gOf a b c = 1 ↔ a &&& 1 = 1 ∧ b &&& 1 = 1 ∧ c &&& 1 = 1 := by
  have key : ∀ x : Nat, x % 2 = 1 ↔ x.testBit 0 = true := fun x => by
    rw [Nat.testBit_zero]; simp
  simp only [gOf, and1_eq_one, BitVec.toNat_and, key, Nat.testBit_and, Bool.and_eq_true, and_assoc]

theorem and1_of_setWidth_one {x : BitVec 64} (h : x.setWidth 32 = 1) : x &&& 1 = 1 := by
  rw [and1_eq_one]
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth] at this
  have h2 : x.toNat % 2 = x.toNat % 2 ^ 32 % 2 := (Nat.mod_mod_of_dvd _ (by decide)).symm
  rw [h2, this]; rfl

theorem and1_of_setWidth_zero {x : BitVec 64} (h : x.setWidth 32 = 0) : x &&& 1 ≠ 1 := by
  rw [Ne, and1_eq_one]
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth] at this
  have h2 : x.toNat % 2 = x.toNat % 2 ^ 32 % 2 := (Nat.mod_mod_of_dvd _ (by decide)).symm
  rw [h2, this]; decide

/-! ## The check -/

/-- Whether `M` is released: `r₁` odd, `n` a valid modulus, and the public
operation of `M` (within BoringSSL's limits on `e`) the input. -/
def released (r₁ : BitVec 64) (nB eB xB mB : List Byte) : Prop :=
  r₁ &&& 1 = 1 ∧ Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) nB.length ∧ Spec.Rsa.publicOpChecked nB eB mB = some xB

instance (r₁ : BitVec 64) (nB eB xB mB : List Byte) : Decidable (released r₁ nB eB xB mB) := by
  unfold released; infer_instance

/-- What the check returns: 1 if it releases `M`, 2 if `r₁` is odd, `n`
valid and the public operation of `M` succeeds but is not the input, 0
otherwise. -/
def checkResult (r₁ : BitVec 64) (nB eB xB mB : List Byte) : BitVec 64 :=
  if r₁ &&& 1 = 1 ∧ Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) nB.length = true ∧
      (Spec.Rsa.publicOpChecked nB eB mB).isSome = true then
    (if Spec.Rsa.publicOpChecked nB eB mB = some xB then 1 else 2)
  else 0

theorem bytesAt_length' (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

theorem precompute_isSome (nB : List Byte) :
    (Spec.Rsa.publicPrecompute nB).isSome = Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) nB.length := by
  simp only [Spec.Rsa.publicPrecompute]
  split <;> simp_all

/-- The check's logic: what it returns and whether it releases `M`, from
what the calls returned (`r₂` and `r₃`) and wrote (`outB`). -/
theorem check_logic {r₁ r₂ r₃ : BitVec 64} {nB eB xB mB outB : List Byte}
    (h3 : match Spec.Rsa.publicPrecompute nB with
      | some _ => r₃.setWidth 32 = 1
      | none => r₃.setWidth 32 = 0)
    (h2 : (Spec.Rsa.publicPrecompute nB).isSome = true →
      match Spec.Rsa.publicOpChecked nB eB mB with
      | some y => r₂.setWidth 32 = 1 ∧ outB = y
      | none => r₂.setWidth 32 = 0) :
    result (gOf r₂ r₁ r₃) (decide (outB = xB)) = checkResult r₁ nB eB xB mB ∧
      ((gOf r₂ r₁ r₃ = 1 ∧ outB = xB) ↔ released r₁ nB eB xB mB) := by
  unfold checkResult released result
  rw [← precompute_isSome]
  cases hpc : Spec.Rsa.publicPrecompute nB with
  | none =>
    simp only [hpc] at h3
    have hg : gOf r₂ r₁ r₃ ≠ 1 := fun h => and1_of_setWidth_zero h3 ((gOf_eq_one _ _ _).mp h).2.2
    have hg' : ¬ gOf r₂ r₁ r₃ = 1#64 := hg
    simp [hg']
  | some ws =>
    simp only [hpc] at h3
    have h2 := h2 (by simp [hpc])
    cases hpo : Spec.Rsa.publicOpChecked nB eB mB with
    | none =>
      simp only [hpo] at h2
      have hg : gOf r₂ r₁ r₃ ≠ 1 := fun h => and1_of_setWidth_zero h2 ((gOf_eq_one _ _ _).mp h).1
      have hg' : ¬ gOf r₂ r₁ r₃ = 1#64 := hg
      simp [hg']
    | some y =>
      simp only [hpo] at h2
      obtain ⟨h2, rfl⟩ := h2
      have hg : gOf r₂ r₁ r₃ = 1 ↔ r₁ &&& 1 = 1 := by
        rw [gOf_eq_one]; exact ⟨fun h => h.2.1, fun h => ⟨and1_of_setWidth_one h2, h, and1_of_setWidth_one h3⟩⟩
      by_cases h1 : r₁ &&& 1 = 1
      · have hg1 : gOf r₂ r₁ r₃ = 1#64 := hg.mpr h1
        have h1' : r₁ &&& 1#64 = 1#64 := h1
        simp [hg1, h1']
      · have hg1 : ¬ gOf r₂ r₁ r₃ = 1#64 := fun h => h1 (hg.mp h)
        have h1' : ¬ r₁ &&& 1#64 = 1#64 := h1
        simp [hg1, h1']

/-- The CRT's result `mB` (returning `rc`), and the check's of it (returning
`r` and writing `outB`), are the checked private operation's. -/
theorem outcome_eq {m m' : Mem} {M out : Addr} {k : Nat} {rc r : BitVec 64}
    {nB eB xB pB qB dPB dQB qInvB : List Byte} (hn : nB.length = k) (hx : xB.length = k)
    (hcrt : Spec.Rsa.written m M k (rc.setWidth 32) (Spec.Rsa.privateCrt nB xB pB qB dPB dQB qInvB))
    (hr : r = checkResult rc nB eB xB (Spec.Rsa.bytesAt m M k))
    (hout : Spec.Rsa.bytesAt m' out k =
      if released rc nB eB xB (Spec.Rsa.bytesAt m M k) then Spec.Rsa.bytesAt m M k else List.replicate k 0) :
    Spec.Rsa.writtenOutcome m' out k (r.setWidth 32) (Spec.Rsa.privateChecked nB eB xB pB qB dPB dQB qInvB) := by
  rw [Proof.Rsa.privateChecked_of_crt (hx.trans hn.symm)]
  cases hc : Spec.Rsa.privateCrt nB xB pB qB dPB dQB qInvB with
  | none =>
    rw [hc] at hcrt
    have h1 := and1_of_setWidth_zero hcrt.1
    have hrel : ¬ released rc nB eB xB (Spec.Rsa.bytesAt m M k) := fun h => h1 h.1
    simp only [checkResult, h1, false_and, ↓reduceIte] at hr
    simp only [hrel, ↓reduceIte] at hout
    exact ⟨by rw [hr]; rfl, hout⟩
  | some y =>
    rw [hc] at hcrt
    obtain ⟨hr1, hy⟩ := hcrt
    obtain ⟨hm, hs⟩ := Proof.Rsa.privateCrt_some hc
    have h1 := and1_of_setWidth_one hr1
    rw [hy] at hr hout
    by_cases he : Spec.Rsa.exponentValid (Spec.Rsa.os2ip eB) = true
    · have hsome := hs eB he
      by_cases hp : Spec.Rsa.publicOpChecked nB eB y = some xB
      · have hrel : released rc nB eB xB y := ⟨h1, hm, hp⟩
        simp only [checkResult, h1, hm, hp, ↓reduceIte] at hr
        simp only [hrel, ↓reduceIte] at hout
        simp only [he, hp, ↓reduceIte]
        exact ⟨by rw [hr]; rfl, hout⟩
      · have hrel : ¬ released rc nB eB xB y := fun h => hp h.2.2
        simp only [checkResult, h1, hm, hsome, hp, and_self, ↓reduceIte] at hr
        simp only [hrel, ↓reduceIte] at hout
        simp only [he, hp, ↓reduceIte]
        exact ⟨by rw [hr]; rfl, hout⟩
    · have hnone : Spec.Rsa.publicOpChecked nB eB y = none := by
        simp only [Spec.Rsa.publicOpChecked, he]; rfl
      have hrel : ¬ released rc nB eB xB y := fun h => by
        have := h.2.2; rw [hnone] at this; cases this
      simp only [checkResult, hnone, Option.isSome_none, Bool.false_eq_true, and_false, ↓reduceIte] at hr
      simp only [hrel, ↓reduceIte] at hout
      simp only [he, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by rw [hr]; rfl, hout⟩

/-- What the check releases passes it: a result 1 means `mB` (of `k` octets)
is below `n` and `mB^e mod n` is the input. -/
theorem checkResult_sound {r₁ : BitVec 64} {nB eB xB mB : List Byte} (hx : xB.length = nB.length)
    (h : checkResult r₁ nB eB xB mB = 1) :
    released r₁ nB eB xB mB ∧ Spec.Rsa.os2ip mB < Spec.Rsa.os2ip nB ∧
      Spec.Rsa.os2ip mB ^ Spec.Rsa.os2ip eB % Spec.Rsa.os2ip nB = Spec.Rsa.os2ip xB := by
  simp only [checkResult] at h
  split at h
  · rename_i hc
    split at h
    · rename_i hp
      exact ⟨⟨hc.1, hc.2.1, hp⟩, Proof.Rsa.publicOpChecked_sound hx hp⟩
    · cases h
  · cases h

end VG.Proof.Rsa
