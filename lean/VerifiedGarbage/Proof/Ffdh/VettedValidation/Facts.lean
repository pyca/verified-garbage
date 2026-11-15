module

public import VerifiedGarbage.Proof.Ffdh.VettedGroupFacts
public import VerifiedGarbage.Spec.Ffdh.VettedGroups
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega

/-! ### One evaluation of a whole exponent -/

namespace VG.Proof.Ffdh.VettedValidation

/-- Append the low `8 * n` bits of `b` to a binary exponent whose residue is `a`, a byte at a
time: eight squarings and a shift for the byte's power of two in a step, which the kernel
evaluates several times faster than a step for each bit. -/
private def powerBytes (p a b : Nat) : Nat → Nat
  | 0 => a % p
  | n + 1 =>
    ((((((((powerBytes p a (b / 256) n
      ^ 2 % p) ^ 2 % p) ^ 2 % p) ^ 2 % p) ^ 2 % p) ^ 2 % p) ^ 2 % p) ^ 2 <<< (b % 256)) % p

private theorem sq_mod (x p : Nat) : (x % p) ^ 2 % p = x ^ 2 % p := (Nat.pow_mod x 2 p).symm

private theorem powerBytes_correct (p a b n : Nat) :
    powerBytes p a b n = a ^ (256 ^ n) * 2 ^ (b % 256 ^ n) % p := by
  induction n generalizing b with
  | zero => simp only [powerBytes, Nat.pow_zero, Nat.pow_one, Nat.mod_one, Nat.mul_one]
  | succ n ih =>
    have bits : b % 256 ^ (n + 1) = (b / 256 % 256 ^ n) * 256 + b % 256 := by
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]
      omega_using []
    have exps : 256 ^ (n + 1) = 256 ^ n * 256 := Nat.pow_succ 256 n
    rw [powerBytes, ih, Nat.shiftLeft_eq, Nat.mul_mod]
    simp only [sq_mod]
    rw [← Nat.mul_mod, bits, exps, Nat.pow_add, Nat.pow_mul a, Nat.pow_mul 2,
      ← Nat.mul_assoc, ← Nat.mul_pow]
    simp only [← Nat.pow_mul, Nat.reduceMul]

/-- One kernel evaluation checks that 2 to the power `(p - 1) / 2`, an exponent of at most
`8 * n` bits, is 1 modulo `p`: no intermediate residue is stated. -/
private theorem subgroup_of_powerBytes {p : Nat} (n : Nat)
    (ok : (decide ((p - 1) / 2 < 256 ^ n) && powerBytes p 1 ((p - 1) / 2) n == 1) = true) :
    2 ^ ((p - 1) / 2) % p = 1 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ok
  have result := ok.2
  rw [powerBytes_correct, Nat.mod_eq_of_lt ok.1, Nat.one_pow, Nat.one_mul] at result
  exact result

end VG.Proof.Ffdh.VettedValidation

/-! ### `Ffdh.VettedValidation.Modp2048`, which only this module used -/

section

/-! Kernel-checked binary-power certificate for the published modp2048 parameters:
`powerBytes` runs over the 256 bytes of the exponent in one evaluation. -/
@[expose] public section
namespace VG.Proof.Ffdh.VettedValidation.Modp2048

open VG.Proof.Ffdh.VettedValidation

theorem subgroup : 2 ^ ((Spec.Ffdh.modp2048Prime - 1) / 2) % Spec.Ffdh.modp2048Prime = 1 :=
  subgroup_of_powerBytes 256 (by decide +kernel)

end VG.Proof.Ffdh.VettedValidation.Modp2048

end

end

/-! ### `Ffdh.VettedValidation.Ffdhe2048`, which only this module used -/

section

/-! Kernel-checked binary-power certificate for the published ffdhe2048 parameters:
`powerBytes` runs over the 256 bytes of the exponent in one evaluation. -/
@[expose] public section
namespace VG.Proof.Ffdh.VettedValidation.Ffdhe2048

open VG.Proof.Ffdh.VettedValidation

theorem subgroup : 2 ^ ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) % Spec.Ffdh.ffdhe2048Prime = 1 :=
  subgroup_of_powerBytes 256 (by decide +kernel)

end VG.Proof.Ffdh.VettedValidation.Ffdhe2048

end

end

/-! ### `Ffdh.VettedValidation.Modp3072`, which only this module used -/

section

/-! Kernel-checked binary-power certificate for the published modp3072 parameters:
`powerBytes` runs over the 384 bytes of the exponent in one evaluation. -/
@[expose] public section
namespace VG.Proof.Ffdh.VettedValidation.Modp3072

open VG.Proof.Ffdh.VettedValidation

theorem subgroup : 2 ^ ((Spec.Ffdh.modp3072Prime - 1) / 2) % Spec.Ffdh.modp3072Prime = 1 :=
  subgroup_of_powerBytes 384 (by decide +kernel)

end VG.Proof.Ffdh.VettedValidation.Modp3072

end

end

/-! ### `Ffdh.VettedValidation.Ffdhe3072`, which only this module used -/

section

/-! Kernel-checked binary-power certificate for the published ffdhe3072 parameters:
`powerBytes` runs over the 384 bytes of the exponent in one evaluation. -/
@[expose] public section
namespace VG.Proof.Ffdh.VettedValidation.Ffdhe3072

open VG.Proof.Ffdh.VettedValidation

theorem subgroup : 2 ^ ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) % Spec.Ffdh.ffdhe3072Prime = 1 :=
  subgroup_of_powerBytes 384 (by decide +kernel)

end VG.Proof.Ffdh.VettedValidation.Ffdhe3072

end

end

/-! ### `Ffdh.VettedValidation.Modp4096`, which only this module used -/

section

/-! Kernel-checked binary-power certificate for the published modp4096 parameters:
`powerBytes` runs over the 512 bytes of the exponent in one evaluation. -/
@[expose] public section
namespace VG.Proof.Ffdh.VettedValidation.Modp4096

open VG.Proof.Ffdh.VettedValidation

theorem subgroup : 2 ^ ((Spec.Ffdh.modp4096Prime - 1) / 2) % Spec.Ffdh.modp4096Prime = 1 :=
  subgroup_of_powerBytes 512 (by decide +kernel)

end VG.Proof.Ffdh.VettedValidation.Modp4096

end

end

/-! ### `Ffdh.VettedValidation.Ffdhe4096`, which only this module used -/

section

/-! Kernel-checked binary-power certificate for the published ffdhe4096 parameters:
`powerBytes` runs over the 512 bytes of the exponent in one evaluation. -/
@[expose] public section
namespace VG.Proof.Ffdh.VettedValidation.Ffdhe4096

open VG.Proof.Ffdh.VettedValidation

theorem subgroup : 2 ^ ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) % Spec.Ffdh.ffdhe4096Prime = 1 :=
  subgroup_of_powerBytes 512 (by decide +kernel)

end VG.Proof.Ffdh.VettedValidation.Ffdhe4096

end

end

/-! ### `Ffdh.VettedValidation.Modp6144`, which only this module used -/

section

/-! Kernel-checked binary-power certificate for the published modp6144 parameters:
`powerBytes` runs over the 768 bytes of the exponent in one evaluation. -/
@[expose] public section
namespace VG.Proof.Ffdh.VettedValidation.Modp6144

open VG.Proof.Ffdh.VettedValidation

theorem subgroup : 2 ^ ((Spec.Ffdh.modp6144Prime - 1) / 2) % Spec.Ffdh.modp6144Prime = 1 :=
  subgroup_of_powerBytes 768 (by decide +kernel)

end VG.Proof.Ffdh.VettedValidation.Modp6144

end

end

/-! ### `Ffdh.VettedValidation.Ffdhe6144`, which only this module used -/

section

/-! Kernel-checked binary-power certificate for the published ffdhe6144 parameters:
`powerBytes` runs over the 768 bytes of the exponent in one evaluation. -/
@[expose] public section
namespace VG.Proof.Ffdh.VettedValidation.Ffdhe6144

open VG.Proof.Ffdh.VettedValidation

theorem subgroup : 2 ^ ((Spec.Ffdh.ffdhe6144Prime - 1) / 2) % Spec.Ffdh.ffdhe6144Prime = 1 :=
  subgroup_of_powerBytes 768 (by decide +kernel)

end VG.Proof.Ffdh.VettedValidation.Ffdhe6144

end

end

/-! ### `Ffdh.VettedValidation.Modp8192`, which only this module used -/

section

/-! Kernel-checked binary-power certificate for the published modp8192 parameters:
`powerBytes` runs over the 1024 bytes of the exponent in one evaluation. -/
@[expose] public section
namespace VG.Proof.Ffdh.VettedValidation.Modp8192

open VG.Proof.Ffdh.VettedValidation

theorem subgroup : 2 ^ ((Spec.Ffdh.modp8192Prime - 1) / 2) % Spec.Ffdh.modp8192Prime = 1 :=
  subgroup_of_powerBytes 1024 (by decide +kernel)

end VG.Proof.Ffdh.VettedValidation.Modp8192

end

end

/-! ### `Ffdh.VettedValidation.Ffdhe8192`, which only this module used -/

section

/-! Kernel-checked binary-power certificate for the published ffdhe8192 parameters:
`powerBytes` runs over the 1024 bytes of the exponent in one evaluation. -/
@[expose] public section
namespace VG.Proof.Ffdh.VettedValidation.Ffdhe8192

open VG.Proof.Ffdh.VettedValidation

theorem subgroup : 2 ^ ((Spec.Ffdh.ffdhe8192Prime - 1) / 2) % Spec.Ffdh.ffdhe8192Prime = 1 :=
  subgroup_of_powerBytes 1024 (by decide +kernel)

end VG.Proof.Ffdh.VettedValidation.Ffdhe8192

end

end


/-! The fixed standard groups satisfy the existing algebraic import contract. -/
@[expose] public section
namespace VG.Proof.Ffdh.VettedValidation
open VG
open VG.Impl.Ffdh

private theorem prime_facts (g : VettedGroups.Group) (member : g∈VettedGroups.groups) :
  512≤Spec.RsaKeyGen.bitLength g.prime ∧ Spec.RsaKeyGen.bitLength g.prime≤8192 ∧
  g.prime % 2=1 ∧ 2<g.prime-1 ∧ 2<(g.prime-1)/2 ∧ ((g.prime-1)/2)%2=1 ∧
  (g.prime-1)/2<g.prime-1 ∧ (g.prime-1)%((g.prime-1)/2)=0 := by
  simp only [VettedGroups.groups,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

theorem group_subgroup (g : VettedGroups.Group) (member : g∈VettedGroups.groups) :
  2 ^ ((g.prime-1)/2) % g.prime=1 := by
  have primes : g.prime=Spec.Ffdh.modp2048Prime ∨ g.prime=Spec.Ffdh.ffdhe2048Prime ∨ g.prime=Spec.Ffdh.modp3072Prime ∨ g.prime=Spec.Ffdh.ffdhe3072Prime ∨ g.prime=Spec.Ffdh.modp4096Prime ∨ g.prime=Spec.Ffdh.ffdhe4096Prime ∨ g.prime=Spec.Ffdh.modp6144Prime ∨ g.prime=Spec.Ffdh.ffdhe6144Prime ∨ g.prime=Spec.Ffdh.modp8192Prime ∨ g.prime=Spec.Ffdh.ffdhe8192Prime := by
    simp only [VettedGroups.groups,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  rcases primes with h|h|h|h|h|h|h|h|h|h
  · rw [h]; exact Modp2048.subgroup
  · rw [h]; exact Ffdhe2048.subgroup
  · rw [h]; exact Modp3072.subgroup
  · rw [h]; exact Ffdhe3072.subgroup
  · rw [h]; exact Modp4096.subgroup
  · rw [h]; exact Ffdhe4096.subgroup
  · rw [h]; exact Modp6144.subgroup
  · rw [h]; exact Ffdhe6144.subgroup
  · rw [h]; exact Modp8192.subgroup
  · rw [h]; exact Ffdhe8192.subgroup

theorem group_parameters_valid (g : VettedGroups.Group) (member : g∈VettedGroups.groups) (q : Option Nat)
    (order : q=none ∨ q=some ((g.prime-1)/2)) :
    Spec.Ffdh.parametersValid ⟨g.prime,2,q⟩=true := by
  obtain ⟨lo,hi,odd,gen,qlo,qodd,qhi,divides⟩ := prime_facts g member
  rcases order with rfl|rfl
  · simp only [Spec.Ffdh.parametersValid,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
    exact ⟨⟨⟨⟨⟨lo,hi⟩,odd⟩,by decide⟩,gen⟩,True.intro⟩
  · simp only [Spec.Ffdh.parametersValid,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,
      VG.Proof.Bignum.powMod_eq]
    exact ⟨⟨⟨⟨⟨lo,hi⟩,odd⟩,by decide⟩,gen⟩,⟨⟨⟨⟨qlo,qodd⟩,qhi⟩,divides⟩,group_subgroup g member⟩⟩

theorem matched_domain_valid {g : VettedGroups.Group} (member : g∈VettedGroups.groups)
    {k : Nat} {dom : List Byte} (shape : dom.length=2*k ∨ dom.length=3*k)
    (matched : k=g.len ∧ dom=g.domain.take dom.length) : Spec.Ffdh.domainValid k dom=true := by
  obtain ⟨rfl,matched⟩:=matched
  have params := VG.Proof.Ffdh.VettedGroupFacts.group_parameters g member shape
  have domain := congrArg (Spec.Ffdh.domainOf g.len) matched
  rw [params] at domain
  unfold Spec.Ffdh.domainValid
  rw [domain]
  rw [Bool.and_eq_true]
  refine ⟨group_parameters_valid g member _ ?_,?_⟩
  · split <;> simp
  · exact decide_eq_true (VG.Proof.Ffdh.VettedGroupFacts.group_bounds g member).2.1

/-- Any exact-table recognition success establishes the unchanged validation predicate.
No assumption about the input modulus is needed before recognition. -/
theorem recognized_domain_valid (gs : List VettedGroups.Group)
    (members : ∀ g ∈ gs, g ∈ VettedGroups.groups)
    {k : Nat} {dom : List Byte} (shape : dom.length = 2 * k ∨ dom.length = 3 * k)
    (hit : VettedGroups.recognizeList gs k dom ≠ 0) :
    Spec.Ffdh.domainValid k dom = true := by
  induction gs with
  | nil => simp only [VettedGroups.recognizeList] at hit; exact False.elim (hit rfl)
  | cons g gs ih =>
    by_cases matched : g.len = k ∧ dom = g.domain.take dom.length
    · exact matched_domain_valid (members g (by simp)) shape ⟨matched.1.symm, matched.2⟩
    · apply ih (fun x hx => members x (by simp [hx]))
      simpa only [VettedGroups.recognizeList, ite_eq_right matched] using hit


end VG.Proof.Ffdh.VettedValidation
