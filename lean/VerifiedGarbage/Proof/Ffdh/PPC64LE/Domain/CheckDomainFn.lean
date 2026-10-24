module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.DomainBody
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_check_domain` on PPC64LE: the function

`vg_ffdh_check_domain(domain = r3, domain_len = r4, p_len = r5, scratch = r6,
scratch_len = r7)` (`cdContract`): `checkDomain` saves the nonvolatile
registers in the working space's header, sets up the registers, loads and
checks p (`loadP_ok`), checks q and g (`domainBody_ok`) and restores the
registers (`cd_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot slot_sep bytesAt_length)

/-- The working space, `scratch_len` words at `r6`. -/
abbrev scrR6 (s : State) : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat * 8⟩

/-- `vg_ffdh_check_domain`, on the registers. -/
def cdContract : Contract isa where
  pre s :=
    s.rd = [domR s] ∧ s.wr = [scrR6 s] ∧ (domR s).Disjoint (scrR6 s) ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + (s.gpr .r7).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Ffdh.pLenValid (s.gpr .r5).toNat ∧ Spec.Ffdh.domainLenValid (s.gpr .r5).toNat (s.gpr .r4).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r5).toNat ≤ (s.gpr .r7).toNat
  post s t :=
    ((t.gpr .r3).setWidth 32).toNat =
      if Spec.Ffdh.domainValid (s.gpr .r5).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) then 1
      else 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r3) (s₁.gpr .r4).toNat).map (·.toNat) =
        (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r3) (s₂.gpr .r4).toNat).map (·.toNat)

/-- The registers `setup` writes. -/
def setup0Regs : List Reg := [.r10, .r11, .r21, .r27, .r28, .r29, .r31]

/-- `setup`, the working space at `r23`. -/
theorem setup0_ok {s : State} {S D : Addr} {k L : Nat} (h3 : s.gpr .r3 = D)
    (h4 : s.gpr .r4 = BitVec.ofNat 64 L) (h5 : s.gpr .r5 = BitVec.ofNat 64 k)
    (h23 : s.gpr .r23 = S) (hk : k ≤ 1024) :
    WP isa (.block setup) s fun t =>
      (t.gpr .r21 = D ∧ t.gpr .r27 = BitVec.ofNat 64 L ∧ t.gpr .r28 = BitVec.ofNat 64 k ∧
        t.gpr .r11 = BitVec.ofNat 64 (2 * ((k + 7) / 8)) ∧ t.gpr .r29 = BitVec.ofNat 64 (8 * ((k + 7) / 8 + 2)) ∧
        t.gpr .r10 = off S (slot ((k + 7) / 8) 0) ∧ t.gpr .r31 = S ∧ t.mem = s.mem) ∧
      Keep setup0Regs s t := by
  refine WP.keep _ ?_ (by decide)
  unfold setup
  prun [h3, h4, h5, h23, BitVec.add_zero, Pub.ofNat_add7_shr3 k (by omega), Pub.ofNat_shl3, Pub.ofNat_shl1,
    hdrBytes]
  refine ⟨?_, by simp [off, slot, hdrBytes]⟩
  rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, BitVec.ofNat_add_ofNat]
  congr 1

theorem cd_pres_not_written : ∀ r ∈ preserved, (∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i) →
    r ∉ ([.r23] : List Reg) ++ setup0Regs ++ ([.r0, .r6, .r12, .r14, .r15, .r16, .r17, .r18] : List Reg) ++
      (domainBodyRegs ++ ([.r3] : List Reg)) := by
  decide

theorem mod_one_iff {p q : Nat} (hq : 2 ≤ q) (hp : 1 ≤ p) : p % q = 1 ↔ (p - 1) % q = 0 := by
  have e := Nat.div_add_mod p q
  constructor
  · intro h
    rw [h] at e
    rw [show p - 1 = q * (p / q) by omega, Nat.mul_mod_right]
  · intro h
    have e' := Nat.div_add_mod (p - 1) q
    rw [h, Nat.add_zero] at e'
    rw [show p = q * ((p - 1) / q) + 1 by omega, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hq

/-- `domainValid`, as `checkDomain` computes it. -/
theorem domainValid_body (m : Mem) (D : Addr) {k L : Nat} (hk : 1 ≤ k) (hL : L = 2 * k ∨ L = 3 * k) :
    Spec.Ffdh.domainValid k (Spec.Rsa.bytesAt m D L) = true ↔
      Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k)) k = true ∧
        bodyCond L k (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off D (2 * k)) k)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off D k) k)) := by
  rw [Proof.Ffdh.domainValid_iff, Proof.Ffdh.domainOf_p _ _ (by omega), Proof.Ffdh.domainOf_g _ _ (by omega)]
  rcases hL with rfl | rfl
  · rw [Proof.Ffdh.domainOf_q2 _ _ (by omega)]
    simp only [bodyCond, show ¬ 2 * k = 3 * k by omega, ↓reduceIte, reduceCtorEq, false_imp_iff, imp_true_iff,
      and_true]
  · rw [Proof.Ffdh.domainOf_q3]
    simp only [bodyCond, ↓reduceIte, Option.some.injEq, forall_eq', qConds]
    constructor
    · rintro ⟨hv, hg, ⟨hq1, hq2, hq3⟩, hd, hgq⟩
      have := modulus_facts hv
      exact ⟨hv, ⟨⟨hq2, hq3⟩, hq1⟩, ⟨hg, (mod_one_iff hq2 (by omega)).mpr hd⟩, hgq⟩
    · rintro ⟨hv, ⟨⟨hq2, hq3⟩, hq1⟩, ⟨hg, hd⟩, hgq⟩
      have := modulus_facts hv
      exact ⟨hv, hg, ⟨hq1, hq2, hq3⟩, (mod_one_iff hq2 (by omega)).mp hd, hgq⟩

end VG.Proof.Ffdh.PPC64LE.Domain
