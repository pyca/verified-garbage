module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Fn
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Safety
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Verified
public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Safety
public import VerifiedGarbage.Proof.Ffdh.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFillG
import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
import VerifiedGarbage.Proof.Framework.Lit

/-!
# FFDH's domain operations on x86-64, without secret residue

Each of `vg_ffdh_check_public`, `vg_ffdh_exchange`, `vg_ffdh_check_private`,
`vg_ffdh_derive_public` and `vg_ffdh_check_domain` as emitted
(`Impl.Ffdh.X86_64.Fn`), over any implementation of the arithmetic
(`RoundImpl`) and of the exponentiation (`ExpImpl`), with its whole stack
wiped by its cleanup at the higher of their levels. Its code is its code over
stubs of the multiplication and of the exponentiation, with the
implementations' code where it runs them (`FillG`, `fill_gen`, the
exponentiation's code spliced into its sequences, `FillG.seqs_append`): the
kernel evaluates what the cleanup needs of the stub once, and the
implementations what they need of theirs where they are defined
(`RoundImpl.mmSide`, `ExpImpl.side`).
-/

-- separate module: the kernel's evaluation of the cleanup's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.DomainScrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)

/-- A stub of the Montgomery multiplication. -/
abbrev stubMM : Nat → Nat → Nat → Prog isa := fun _ _ _ => .call "mm" (.block [])

/-- A stub of the exponentiation. -/
abbrev stubEx : Nat → Nat → List (Prog isa) := fun _ _ => [.call "exp" (.block [])]

/-- The stub's `R² mod p`. -/
abbrev stubR2 : Prog isa := Impl.Ffdh.X86_64.Fn.r2 stubMM

/-- The level of the cleanup over `v` and `e`. -/
def level (v : RoundImpl) (e : ExpImpl) : VecLevel := v.level.join e.level

theorem mm_side (v : RoundImpl) (e : ExpImpl) : ∀ o a b, calleeSide (v.mm o a b) (level v e).level 8 = true :=
  fun o a b => calleeSide_mono (level_join_left _ _) (Nat.le_refl _) (v.mmSide o a b)

theorem ex_side (v : RoundImpl) (e : ExpImpl) {sp sl : Nat} (hs : ExpSlots sp sl) :
    ∀ c ∈ e.code v.mm sp sl, calleeSide c (level v e).level 8 = true :=
  e.side v.mm _ (level_join_right _ _) (mm_side v e) sp sl hs

/-- The stack the multiplication and the exponentiation need. -/
def stubStack : String → Nat := fun _ => 8

theorem public_stub : stubSideG (Impl.Ffdh.X86_64.Domain.CheckPublic.code stubMM stubEx stubR2) VecLevel.sse.level stubStack 8 [] = true := by lit_decide

theorem public_fill (v : RoundImpl) (e : ExpImpl) :
    FillG (level v e).level stubStack (Impl.Ffdh.X86_64.Domain.CheckPublic.code stubMM stubEx stubR2) (CheckPublic.publicCode v e) := by
  have hm := mm_side v e
  have hx := ex_side v e (Or.inl ⟨rfl, rfl⟩)
  have he := ex_side v e (Or.inr ⟨rfl, rfl⟩)
  unfold CheckPublic.publicCode
  simp only [Impl.Ffdh.X86_64.Domain.CheckPublic.code, Impl.Ffdh.X86_64.Domain.CheckPublic.body, Impl.Ffdh.X86_64.Domain.CheckPublic.main, Impl.Ffdh.X86_64.Domain.CheckPublic.subgroup, Impl.Ffdh.X86_64.Domain.pow, List.append_assoc, List.cons_append, List.nil_append]
  fill_gen

/-- `Spec.Ffdh.checkPublicApi`'s function as emitted over `v` and `e` meets its contract in
constant time and returns without secret residue. -/
theorem public_scrubbed (v : RoundImpl) (e : ExpImpl) :
    VerifiedScrubbed target (Impl.Ffdh.X86_64.Fn.checkPublic (level v e) v.mm (e.code v.mm))
      (Spec.Ffdh.checkPublicApi.contract X86_64.abi 8) 32 :=
  verifiedScrubbedAllFillG (api := Spec.Ffdh.checkPublicApi)
    { code := CheckPublic.publicCode v e
      verified := CheckPublic.publicCode_verified v e
      spSafe := CheckPublic.publicCode_sp v e } _ (Proof.Ffdh.X86_64.Scrub.checkPublicOut _)
    (public_fill v e) (Nat.zero_le _) (Nat.le_refl _) (ha := public_stub)

theorem public_spSafe (v : RoundImpl) (e : ExpImpl) :
    (Impl.Ffdh.X86_64.Fn.checkPublic (level v e) v.mm (e.code v.mm)).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (CheckPublic.publicCode_sp v e)

theorem exchange_stub : stubSideG (Impl.Ffdh.X86_64.Domain.Exchange.code stubMM stubEx stubR2) VecLevel.sse.level stubStack 8 [] = true := by lit_decide

theorem exchange_fill (v : RoundImpl) (e : ExpImpl) :
    FillG (level v e).level stubStack (Impl.Ffdh.X86_64.Domain.Exchange.code stubMM stubEx stubR2) (Exchange.exchangeCode v e) := by
  have hm := mm_side v e
  have hx := ex_side v e (Or.inl ⟨rfl, rfl⟩)
  have he := ex_side v e (Or.inr ⟨rfl, rfl⟩)
  unfold Exchange.exchangeCode
  simp only [Impl.Ffdh.X86_64.Domain.Exchange.code, Impl.Ffdh.X86_64.Domain.Exchange.body, Impl.Ffdh.X86_64.Domain.Exchange.main, Impl.Ffdh.X86_64.Domain.pow, List.append_assoc, List.cons_append, List.nil_append]
  fill_gen

/-- `Spec.Ffdh.exchangeApi`'s function as emitted over `v` and `e` meets its contract in
constant time and returns without secret residue. -/
theorem exchange_scrubbed (v : RoundImpl) (e : ExpImpl) :
    VerifiedScrubbed target (Impl.Ffdh.X86_64.Fn.exchange (level v e) v.mm (e.code v.mm))
      (Spec.Ffdh.exchangeApi.contract X86_64.abi 8) 32 :=
  verifiedScrubbedAllFillG (api := Spec.Ffdh.exchangeApi)
    { code := Exchange.exchangeCode v e
      verified := Exchange.exchangeCode_verified v e
      spSafe := Exchange.exchangeCode_sp v e } _ (Proof.Ffdh.X86_64.Scrub.exchangeOut _)
    (exchange_fill v e) (Nat.zero_le _) (Nat.le_refl _) (ha := exchange_stub)

theorem exchange_spSafe (v : RoundImpl) (e : ExpImpl) :
    (Impl.Ffdh.X86_64.Fn.exchange (level v e) v.mm (e.code v.mm)).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Exchange.exchangeCode_sp v e)

theorem private_stub : stubSideG (Impl.Ffdh.X86_64.Domain.CheckPrivate.code stubMM stubEx stubR2) VecLevel.sse.level stubStack 8 [] = true := by lit_decide

theorem private_fill (v : RoundImpl) (e : ExpImpl) :
    FillG (level v e).level stubStack (Impl.Ffdh.X86_64.Domain.CheckPrivate.code stubMM stubEx stubR2) (CheckPrivate.privateCode v e) := by
  have hm := mm_side v e
  have hx := ex_side v e (Or.inl ⟨rfl, rfl⟩)
  have he := ex_side v e (Or.inr ⟨rfl, rfl⟩)
  unfold CheckPrivate.privateCode
  simp only [Impl.Ffdh.X86_64.Domain.CheckPrivate.code, Impl.Ffdh.X86_64.Domain.CheckPrivate.body, Impl.Ffdh.X86_64.Domain.CheckPrivate.main, Impl.Ffdh.X86_64.Domain.CheckPrivate.tail, Impl.Ffdh.X86_64.Domain.pow, List.append_assoc, List.cons_append, List.nil_append]
  fill_gen

/-- `Spec.Ffdh.checkPrivateApi`'s function as emitted over `v` and `e` meets its contract in
constant time and returns without secret residue. -/
theorem private_scrubbed (v : RoundImpl) (e : ExpImpl) :
    VerifiedScrubbed target (Impl.Ffdh.X86_64.Fn.checkPrivate (level v e) v.mm (e.code v.mm))
      (Spec.Ffdh.checkPrivateApi.contract X86_64.abi 8) 32 :=
  verifiedScrubbedAllFillG (api := Spec.Ffdh.checkPrivateApi)
    { code := CheckPrivate.privateCode v e
      verified := CheckPrivate.privateCode_verified v e
      spSafe := CheckPrivate.privateCode_sp v e } _ (Proof.Ffdh.X86_64.Scrub.checkPrivateOut _)
    (private_fill v e) (Nat.zero_le _) (Nat.le_refl _) (ha := private_stub)

theorem private_spSafe (v : RoundImpl) (e : ExpImpl) :
    (Impl.Ffdh.X86_64.Fn.checkPrivate (level v e) v.mm (e.code v.mm)).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (CheckPrivate.privateCode_sp v e)

theorem derive_stub : stubSideG (Impl.Ffdh.X86_64.Domain.DerivePublic.code stubMM stubEx stubR2) VecLevel.sse.level stubStack 8 [] = true := by lit_decide

theorem derive_fill (v : RoundImpl) (e : ExpImpl) :
    FillG (level v e).level stubStack (Impl.Ffdh.X86_64.Domain.DerivePublic.code stubMM stubEx stubR2) (DerivePublic.deriveCode v e) := by
  have hm := mm_side v e
  have hx := ex_side v e (Or.inl ⟨rfl, rfl⟩)
  have he := ex_side v e (Or.inr ⟨rfl, rfl⟩)
  unfold DerivePublic.deriveCode
  simp only [Impl.Ffdh.X86_64.Domain.DerivePublic.code, Impl.Ffdh.X86_64.Domain.DerivePublic.body, Impl.Ffdh.X86_64.Domain.DerivePublic.main, Impl.Ffdh.X86_64.Domain.DerivePublic.tail, Impl.Ffdh.X86_64.Domain.pow, List.append_assoc, List.cons_append, List.nil_append]
  fill_gen

/-- `Spec.Ffdh.derivePublicApi`'s function as emitted over `v` and `e` meets its contract in
constant time and returns without secret residue. -/
theorem derive_scrubbed (v : RoundImpl) (e : ExpImpl) :
    VerifiedScrubbed target (Impl.Ffdh.X86_64.Fn.derivePublic (level v e) v.mm (e.code v.mm))
      (Spec.Ffdh.derivePublicApi.contract X86_64.abi 8) 32 :=
  verifiedScrubbedAllFillG (api := Spec.Ffdh.derivePublicApi)
    { code := DerivePublic.deriveCode v e
      verified := DerivePublic.deriveCode_verified v e
      spSafe := DerivePublic.deriveCode_sp v e } _ (Proof.Ffdh.X86_64.Scrub.derivePublicOut _)
    (derive_fill v e) (Nat.zero_le _) (Nat.le_refl _) (ha := derive_stub)

theorem derive_spSafe (v : RoundImpl) (e : ExpImpl) :
    (Impl.Ffdh.X86_64.Fn.derivePublic (level v e) v.mm (e.code v.mm)).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (DerivePublic.deriveCode_sp v e)

theorem domain_stub : stubSideG (Impl.Ffdh.X86_64.VettedValidation.code (Impl.Ffdh.X86_64.Domain.CheckDomain.code stubMM stubEx stubR2)) VecLevel.sse.level stubStack 8 [] = true := by lit_decide

theorem domain_fill (v : RoundImpl) (e : ExpImpl) :
    FillG (level v e).level stubStack (Impl.Ffdh.X86_64.VettedValidation.code (Impl.Ffdh.X86_64.Domain.CheckDomain.code stubMM stubEx stubR2)) (VettedValidation.emittedCode v e) := by
  have hm := mm_side v e
  have hx := ex_side v e (Or.inl ⟨rfl, rfl⟩)
  have he := ex_side v e (Or.inr ⟨rfl, rfl⟩)
  unfold VettedValidation.emittedCode CheckDomain.domainCode
  simp only [Impl.Ffdh.X86_64.VettedValidation.code, Impl.Ffdh.X86_64.Domain.CheckDomain.code, Impl.Ffdh.X86_64.Domain.CheckDomain.body, Impl.Ffdh.X86_64.Domain.CheckDomain.main, Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup, Impl.Ffdh.X86_64.Domain.CheckDomain.divides, Impl.Ffdh.X86_64.Domain.CheckDomain.withQ, Impl.Ffdh.X86_64.Domain.pow, List.append_assoc, List.cons_append, List.nil_append]
  fill_gen

/-- `Spec.Ffdh.checkDomainApi`'s function as emitted over `v` and `e` meets its contract in
constant time and returns without secret residue. -/
theorem domain_scrubbed (v : RoundImpl) (e : ExpImpl) :
    VerifiedScrubbed target (Impl.Ffdh.X86_64.Fn.checkDomain (level v e) v.mm (e.code v.mm))
      (Spec.Ffdh.checkDomainApi.contract (X86_64.abi.withConsts Impl.Ffdh.X86_64.VettedValidation.tableConsts) 8) 32 :=
  verifiedScrubbedAllFillG (api := Spec.Ffdh.checkDomainApi)
    { code := VettedValidation.emittedCode v e
      verified := VettedValidation.verified v e
      spSafe := VettedValidation.sp_safe v e } _ (Proof.Ffdh.X86_64.Scrub.checkDomainOut 8 Impl.Ffdh.X86_64.VettedValidation.tableConsts)
    (domain_fill v e) (Nat.zero_le _) (Nat.le_refl _) (ha := domain_stub)

theorem domain_spSafe (v : RoundImpl) (e : ExpImpl) :
    (Impl.Ffdh.X86_64.Fn.checkDomain (level v e) v.mm (e.code v.mm)).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (VettedValidation.sp_safe v e)

end VG.Proof.Ffdh.X86_64.DomainScrub
