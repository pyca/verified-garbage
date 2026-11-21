module

public import VerifiedGarbage.Impl.MlDsa.X86_64.Fn
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Inst
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Prims
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.Prepare
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.Scrub
public import VerifiedGarbage.Proof.MlDsa.X86_64.PkTr
public import VerifiedGarbage.Proof.MlDsa.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFillG
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# ML-DSA on x86-64, without secret residue

Each function as emitted (`Impl.MlDsa.X86_64.Fn`), over any implementation
of the polynomial arithmetic (`ArithImpl`), with its whole stack wiped by its
cleanup at the implementation's level. Its code is its code over a backend
whose functions' code is empty (`stub`), with the implementation's where it
calls them (`FillG`, `fill_gen`): the kernel evaluates what the cleanup needs
of the stub once, and the implementation what it needs of its functions where
it is defined (`ArithImpl.sides`).
-/

-- separate module: the kernel's evaluation of the cleanup's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.FnScrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64
open VG.Proof.MlDsa.X86_64 (ArithImpl)

/-- A backend whose functions' code is empty. -/
abbrev stub : Impl.MlDsa.X86_64.Arith.Backend := .empty

/-- The stack the backend's functions (called) need. -/
def stubStack : String → Nat := fun _ => 32

/-- The backend `B`'s functions, by the names the stub's code calls them by:
each with the name the code over `B` calls it by. -/
def table (B : Impl.MlDsa.X86_64.Arith.Backend) : List (String × String × Prog isa) := [
  ("vg_mldsa_ntt", "vg_mldsa_ntt" ++ B.asfx, B.ntt),
  ("vg_mldsa_inv_ntt", (if B.montgomery then "vg_mldsa_montgomery_inv_ntt" else "vg_mldsa_inv_ntt") ++ B.asfx, B.invNtt),
  ("vg_mldsa_multiply_ntt", (if B.montgomery then "vg_mldsa_montgomery_multiply_ntt" else "vg_mldsa_multiply_ntt") ++ B.asfx, B.mul),
  ("vg_mldsa_multiply_add_ntt", (if B.montgomery then "vg_mldsa_montgomery_multiply_add_ntt" else "vg_mldsa_multiply_add_ntt") ++ B.asfx, B.mulAdd),
  ("vg_mldsa_add", "vg_mldsa_add" ++ B.asfx, B.add),
  ("vg_mldsa_sub", "vg_mldsa_sub" ++ B.asfx, B.sub),
  ("vg_mldsa_high_bits", "vg_mldsa_high_bits" ++ B.asfx, B.highBits),
  ("vg_mldsa_low_bits", "vg_mldsa_low_bits" ++ B.asfx, B.lowBits),
  ("vg_mldsa_norm_lt", "vg_mldsa_norm_lt" ++ B.asfx, B.normLt),
  ("vg_mldsa_make_hint", "vg_mldsa_make_hint" ++ B.asfx, B.makeHint),
  ("vg_mldsa_use_hint", "vg_mldsa_use_hint" ++ B.asfx, B.useHint),
  ("vg_mldsa_rej_ntt_poly4", "vg_mldsa_rej_ntt_poly4" ++ B.sfx, B.rej4),
  ("vg_mldsa_expand_mask_poly4", "vg_mldsa_expand_mask_poly4" ++ B.sfx, B.expandMask4),
  (Impl.MlDsa.X86_64.Sign.dotInvName 4, Impl.MlDsa.X86_64.Sign.dotInvName 4 ++ B.asfx, B.dotInv4),
  (Impl.MlDsa.X86_64.Sign.dotInvName 5, Impl.MlDsa.X86_64.Sign.dotInvName 5 ++ B.asfx, B.dotInv5),
  (Impl.MlDsa.X86_64.Sign.dotInvName 7, Impl.MlDsa.X86_64.Sign.dotInvName 7 ++ B.asfx, B.dotInv7)]

/-- The backend `B`'s functions, by the names the stub's code calls them by (`table`). -/
def sigma (B : Impl.MlDsa.X86_64.Arith.Backend) (f : String) : Option (String × Prog isa) := (table B).lookup f

theorem mem_of_lookup {f : String} {p : String × Prog isa} :
    ∀ {l : List (String × String × Prog isa)}, l.lookup f = some p → p ∈ l.map Prod.snd
  | [], h => by simp at h
  | (a, b) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · exact List.mem_cons.mpr (.inl (Option.some.inj h).symm)
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem sigma_side (v : ArithImpl) :
    ∀ f g d, sigma v.code f = some (g, d) → calleeSide (.call g d) v.level.level (stubStack f) = true := by
  intro f g d h
  have hm := mem_of_lookup h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := v.sides
  simp only [table, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact FillG.calleeSide_call _ (by assumption)

theorem keyGen44_eq (v : ArithImpl) :
    Impl.MlDsa.X86_64.KeyGen.keyGen (Impl.MlDsa.X86_64.KeyGen.primsWith v.code) Spec.MlDsa.mlDsa44 =
      fillCallsG (sigma v.code) (Impl.MlDsa.X86_64.KeyGen.keyGen (Impl.MlDsa.X86_64.KeyGen.primsWith stub) Spec.MlDsa.mlDsa44) := by
  kernel_rfl

theorem keyGen44_stub : stubSideG (Impl.MlDsa.X86_64.KeyGen.keyGen (Impl.MlDsa.X86_64.KeyGen.primsWith stub) Spec.MlDsa.mlDsa44) VecLevel.sse.level stubStack 32 [] = true := by decide +kernel

/-- `Spec.MlDsa.keyGen44Api`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem keyGen44_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.keyGen v.level v.code Spec.MlDsa.mlDsa44)
      ((Spec.MlDsa.keyGen44Api).contract X86_64.abi 32) 32 :=
  verifiedScrubbedAllFillG (api := Spec.MlDsa.keyGen44Api)
    { code := Impl.MlDsa.X86_64.KeyGen.keyGen (Impl.MlDsa.X86_64.KeyGen.primsWith v.code) Spec.MlDsa.mlDsa44
      verified := Proof.MlDsa.X86_64.KeyGen.keyGen_verifiedWith v (.inl rfl)
      spSafe := Proof.MlDsa.X86_64.KeyGen.keyGen_spSafe v (.inl rfl) } _
    (VG.Proof.MlDsa.X86_64.Scrub.keyGenOut Spec.MlDsa.mlDsa44 _)
    ((keyGen44_eq v) ▸ fillG_of (sigma_side v) _)
    (Nat.zero_le _) (Nat.le_refl _) (ha := keyGen44_stub)

theorem keyGen44_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.keyGen v.level v.code Spec.MlDsa.mlDsa44).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.KeyGen.keyGen_spSafe v (.inl rfl))

theorem signBody44_eq (v : ArithImpl) :
    Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa44 = fillCallsG (sigma v.code) (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith stub) Spec.MlDsa.mlDsa44) := by
  kernel_rfl

/-- The signing over `v` is its code over the stub with `v`'s functions. -/
theorem signBody44_fill (v : ArithImpl) :
    FillG v.level.level stubStack (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith stub) Spec.MlDsa.mlDsa44) (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa44) :=
  (signBody44_eq v) ▸ fillG_of (sigma_side v) _

theorem verifyBody44_eq (v : ArithImpl) :
    Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44 = fillCallsG (sigma v.code) (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa44) := by
  kernel_rfl

/-- The verification over `v` is its code over the stub with `v`'s functions. -/
theorem verifyBody44_fill (v : ArithImpl) :
    FillG v.level.level stubStack (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa44) (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44) :=
  (verifyBody44_eq v) ▸ fillG_of (sigma_side v) _

theorem preparePublic44_eq (v : ArithImpl) :
    Impl.MlDsa.X86_64.PreparedKey.preparePublic (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44 = fillCallsG (sigma v.code) (Impl.MlDsa.X86_64.PreparedKey.preparePublic (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa44) := by
  kernel_rfl

theorem preparePublic44_stub : stubSideG (Impl.MlDsa.X86_64.PreparedKey.preparePublic (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa44) VecLevel.sse.level stubStack 32 [] = true := by decide +kernel

/-- `Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44"`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparePublic44_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.preparePublic v.level (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44)
      ((Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").contract X86_64.abi 32) 0 :=
  verifiedScrubbedAllFillG (api := Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")
    { code := Impl.MlDsa.X86_64.PreparedKey.preparePublic (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44
      verified := Proof.MlDsa.X86_64.Verify.Prepare.preparePublic_verified (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_self ..)
      spSafe := Proof.MlDsa.X86_64.Verify.Prepare.preparePublic_spSafe (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_self ..) } _
    (Proof.MlDsa.X86_64.PreparedKey.Scrub.pubOut (List.mem_cons_self ..))
    (((preparePublic44_eq v) ▸ fillG_of (sigma_side v) _))
    (Nat.zero_le _) (Nat.le_refl _) (ha := preparePublic44_stub)

theorem preparePublic44_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.preparePublic v.level (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Verify.Prepare.preparePublic_spSafe (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_self ..))

theorem prepareSecret44_eq (v : ArithImpl) :
    Impl.MlDsa.X86_64.PreparedKey.prepareSecret (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44 = fillCallsG (sigma v.code) (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa44) := by
  kernel_rfl

theorem prepareSecret44_stub : stubSideG (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa44) VecLevel.sse.level stubStack 32 [] = true := by decide +kernel

/-- `Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44"`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem prepareSecret44_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.prepareSecret v.level (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44)
      ((Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").contract X86_64.abi 32) 0 :=
  verifiedScrubbedAllFillG (api := Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")
    { code := Impl.MlDsa.X86_64.PreparedKey.prepareSecret (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44
      verified := Proof.MlDsa.X86_64.Verify.Prepare.prepareSecret_verified (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_self ..)
      spSafe := Proof.MlDsa.X86_64.Verify.Prepare.prepareSecret_spSafe (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_self ..) } _
    (Proof.MlDsa.X86_64.PreparedKey.Scrub.secOut (List.mem_cons_self ..))
    (((prepareSecret44_eq v) ▸ fillG_of (sigma_side v) _))
    (Nat.zero_le _) (Nat.le_refl _) (ha := prepareSecret44_stub)

theorem prepareSecret44_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.prepareSecret v.level (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Verify.Prepare.prepareSecret_spSafe (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_self ..))

theorem pkTr44_codeSp : (Impl.MlDsa.X86_64.PkTr.pkTr Spec.MlDsa.mlDsa44).all (fun i => !isa.writesSp i) = true := by sp_safe

/-- `Spec.MlDsa.pkTr44Api`'s function as emitted meets its contract in constant time and
returns without secret residue. -/
theorem pkTr44_scrubbed :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.pkTr Spec.MlDsa.mlDsa44) (Spec.MlDsa.pkTr44Api.contract X86_64.abi 32) 0 :=
  verifiedScrubbedAll (api := Spec.MlDsa.pkTr44Api)
    { code := Impl.MlDsa.X86_64.PkTr.pkTr Spec.MlDsa.mlDsa44
      verified := Proof.MlDsa.X86_64.PkTr.pkTr44_verified
      spSafe := pkTr44_codeSp } .sse (VG.Proof.MlDsa.X86_64.Scrub.pkTrOut Spec.MlDsa.mlDsa44 _) (hs := by decide +kernel)

theorem pkTr44_spSafe : (Impl.MlDsa.X86_64.Fn.pkTr Spec.MlDsa.mlDsa44).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe pkTr44_codeSp

theorem keyGen65_eq (v : ArithImpl) :
    Impl.MlDsa.X86_64.KeyGen.keyGen (Impl.MlDsa.X86_64.KeyGen.primsWith v.code) Spec.MlDsa.mlDsa65 =
      fillCallsG (sigma v.code) (Impl.MlDsa.X86_64.KeyGen.keyGen (Impl.MlDsa.X86_64.KeyGen.primsWith stub) Spec.MlDsa.mlDsa65) := by
  kernel_rfl

theorem keyGen65_stub : stubSideG (Impl.MlDsa.X86_64.KeyGen.keyGen (Impl.MlDsa.X86_64.KeyGen.primsWith stub) Spec.MlDsa.mlDsa65) VecLevel.sse.level stubStack 32 [] = true := by decide +kernel

/-- `Spec.MlDsa.keyGen65Api`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem keyGen65_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.keyGen v.level v.code Spec.MlDsa.mlDsa65)
      ((Spec.MlDsa.keyGen65Api).contract X86_64.abi 32) 32 :=
  verifiedScrubbedAllFillG (api := Spec.MlDsa.keyGen65Api)
    { code := Impl.MlDsa.X86_64.KeyGen.keyGen (Impl.MlDsa.X86_64.KeyGen.primsWith v.code) Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.X86_64.KeyGen.keyGen_verifiedWith v (.inr (.inl rfl))
      spSafe := Proof.MlDsa.X86_64.KeyGen.keyGen_spSafe v (.inr (.inl rfl)) } _
    (VG.Proof.MlDsa.X86_64.Scrub.keyGenOut Spec.MlDsa.mlDsa65 _)
    ((keyGen65_eq v) ▸ fillG_of (sigma_side v) _)
    (Nat.zero_le _) (Nat.le_refl _) (ha := keyGen65_stub)

theorem keyGen65_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.keyGen v.level v.code Spec.MlDsa.mlDsa65).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.KeyGen.keyGen_spSafe v (.inr (.inl rfl)))

theorem signBody65_eq (v : ArithImpl) :
    Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa65 = fillCallsG (sigma v.code) (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith stub) Spec.MlDsa.mlDsa65) := by
  kernel_rfl

/-- The signing over `v` is its code over the stub with `v`'s functions. -/
theorem signBody65_fill (v : ArithImpl) :
    FillG v.level.level stubStack (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith stub) Spec.MlDsa.mlDsa65) (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa65) :=
  (signBody65_eq v) ▸ fillG_of (sigma_side v) _

theorem verifyBody65_eq (v : ArithImpl) :
    Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65 = fillCallsG (sigma v.code) (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa65) := by
  kernel_rfl

/-- The verification over `v` is its code over the stub with `v`'s functions. -/
theorem verifyBody65_fill (v : ArithImpl) :
    FillG v.level.level stubStack (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa65) (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65) :=
  (verifyBody65_eq v) ▸ fillG_of (sigma_side v) _

theorem preparePublic65_eq (v : ArithImpl) :
    Impl.MlDsa.X86_64.PreparedKey.preparePublic (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65 = fillCallsG (sigma v.code) (Impl.MlDsa.X86_64.PreparedKey.preparePublic (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa65) := by
  kernel_rfl

theorem preparePublic65_stub : stubSideG (Impl.MlDsa.X86_64.PreparedKey.preparePublic (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa65) VecLevel.sse.level stubStack 32 [] = true := by decide +kernel

/-- `Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65"`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparePublic65_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.preparePublic v.level (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65)
      ((Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").contract X86_64.abi 32) 0 :=
  verifiedScrubbedAllFillG (api := Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")
    { code := Impl.MlDsa.X86_64.PreparedKey.preparePublic (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.X86_64.Verify.Prepare.preparePublic_verified (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      spSafe := Proof.MlDsa.X86_64.Verify.Prepare.preparePublic_spSafe (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) } _
    (Proof.MlDsa.X86_64.PreparedKey.Scrub.pubOut (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (((preparePublic65_eq v) ▸ fillG_of (sigma_side v) _))
    (Nat.zero_le _) (Nat.le_refl _) (ha := preparePublic65_stub)

theorem preparePublic65_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.preparePublic v.level (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Verify.Prepare.preparePublic_spSafe (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem prepareSecret65_eq (v : ArithImpl) :
    Impl.MlDsa.X86_64.PreparedKey.prepareSecret (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65 = fillCallsG (sigma v.code) (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa65) := by
  kernel_rfl

theorem prepareSecret65_stub : stubSideG (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa65) VecLevel.sse.level stubStack 32 [] = true := by decide +kernel

/-- `Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65"`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem prepareSecret65_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.prepareSecret v.level (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65)
      ((Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").contract X86_64.abi 32) 0 :=
  verifiedScrubbedAllFillG (api := Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")
    { code := Impl.MlDsa.X86_64.PreparedKey.prepareSecret (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.X86_64.Verify.Prepare.prepareSecret_verified (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      spSafe := Proof.MlDsa.X86_64.Verify.Prepare.prepareSecret_spSafe (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) } _
    (Proof.MlDsa.X86_64.PreparedKey.Scrub.secOut (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (((prepareSecret65_eq v) ▸ fillG_of (sigma_side v) _))
    (Nat.zero_le _) (Nat.le_refl _) (ha := prepareSecret65_stub)

theorem prepareSecret65_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.prepareSecret v.level (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Verify.Prepare.prepareSecret_spSafe (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem pkTr65_codeSp : (Impl.MlDsa.X86_64.PkTr.pkTr Spec.MlDsa.mlDsa65).all (fun i => !isa.writesSp i) = true := by sp_safe

/-- `Spec.MlDsa.pkTr65Api`'s function as emitted meets its contract in constant time and
returns without secret residue. -/
theorem pkTr65_scrubbed :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.pkTr Spec.MlDsa.mlDsa65) (Spec.MlDsa.pkTr65Api.contract X86_64.abi 32) 0 :=
  verifiedScrubbedAll (api := Spec.MlDsa.pkTr65Api)
    { code := Impl.MlDsa.X86_64.PkTr.pkTr Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.X86_64.PkTr.pkTr65_verified
      spSafe := pkTr65_codeSp } .sse (VG.Proof.MlDsa.X86_64.Scrub.pkTrOut Spec.MlDsa.mlDsa65 _) (hs := by decide +kernel)

theorem pkTr65_spSafe : (Impl.MlDsa.X86_64.Fn.pkTr Spec.MlDsa.mlDsa65).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe pkTr65_codeSp

theorem keyGen87_eq (v : ArithImpl) :
    Impl.MlDsa.X86_64.KeyGen.keyGen (Impl.MlDsa.X86_64.KeyGen.primsWith v.code) Spec.MlDsa.mlDsa87 =
      fillCallsG (sigma v.code) (Impl.MlDsa.X86_64.KeyGen.keyGen (Impl.MlDsa.X86_64.KeyGen.primsWith stub) Spec.MlDsa.mlDsa87) := by
  kernel_rfl

theorem keyGen87_stub : stubSideG (Impl.MlDsa.X86_64.KeyGen.keyGen (Impl.MlDsa.X86_64.KeyGen.primsWith stub) Spec.MlDsa.mlDsa87) VecLevel.sse.level stubStack 32 [] = true := by decide +kernel

/-- `Spec.MlDsa.keyGen87Api`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem keyGen87_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.keyGen v.level v.code Spec.MlDsa.mlDsa87)
      ((Spec.MlDsa.keyGen87Api).contract X86_64.abi 32) 32 :=
  verifiedScrubbedAllFillG (api := Spec.MlDsa.keyGen87Api)
    { code := Impl.MlDsa.X86_64.KeyGen.keyGen (Impl.MlDsa.X86_64.KeyGen.primsWith v.code) Spec.MlDsa.mlDsa87
      verified := Proof.MlDsa.X86_64.KeyGen.keyGen_verifiedWith v (.inr (.inr rfl))
      spSafe := Proof.MlDsa.X86_64.KeyGen.keyGen_spSafe v (.inr (.inr rfl)) } _
    (VG.Proof.MlDsa.X86_64.Scrub.keyGenOut Spec.MlDsa.mlDsa87 _)
    ((keyGen87_eq v) ▸ fillG_of (sigma_side v) _)
    (Nat.zero_le _) (Nat.le_refl _) (ha := keyGen87_stub)

theorem keyGen87_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.keyGen v.level v.code Spec.MlDsa.mlDsa87).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.KeyGen.keyGen_spSafe v (.inr (.inr rfl)))

theorem signBody87_eq (v : ArithImpl) :
    Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa87 = fillCallsG (sigma v.code) (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith stub) Spec.MlDsa.mlDsa87) := by
  kernel_rfl

/-- The signing over `v` is its code over the stub with `v`'s functions. -/
theorem signBody87_fill (v : ArithImpl) :
    FillG v.level.level stubStack (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith stub) Spec.MlDsa.mlDsa87) (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa87) :=
  (signBody87_eq v) ▸ fillG_of (sigma_side v) _

theorem verifyBody87_eq (v : ArithImpl) :
    Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87 = fillCallsG (sigma v.code) (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa87) := by
  kernel_rfl

/-- The verification over `v` is its code over the stub with `v`'s functions. -/
theorem verifyBody87_fill (v : ArithImpl) :
    FillG v.level.level stubStack (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa87) (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87) :=
  (verifyBody87_eq v) ▸ fillG_of (sigma_side v) _

theorem preparePublic87_eq (v : ArithImpl) :
    Impl.MlDsa.X86_64.PreparedKey.preparePublic (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87 = fillCallsG (sigma v.code) (Impl.MlDsa.X86_64.PreparedKey.preparePublic (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa87) := by
  kernel_rfl

theorem preparePublic87_stub : stubSideG (Impl.MlDsa.X86_64.PreparedKey.preparePublic (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa87) VecLevel.sse.level stubStack 32 [] = true := by decide +kernel

/-- `Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87"`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparePublic87_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.preparePublic v.level (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87)
      ((Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").contract X86_64.abi 32) 0 :=
  verifiedScrubbedAllFillG (api := Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")
    { code := Impl.MlDsa.X86_64.PreparedKey.preparePublic (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87
      verified := Proof.MlDsa.X86_64.Verify.Prepare.preparePublic_verified (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      spSafe := Proof.MlDsa.X86_64.Verify.Prepare.preparePublic_spSafe (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) } _
    (Proof.MlDsa.X86_64.PreparedKey.Scrub.pubOut (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    (((preparePublic87_eq v) ▸ fillG_of (sigma_side v) _))
    (Nat.zero_le _) (Nat.le_refl _) (ha := preparePublic87_stub)

theorem preparePublic87_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.preparePublic v.level (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Verify.Prepare.preparePublic_spSafe (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem prepareSecret87_eq (v : ArithImpl) :
    Impl.MlDsa.X86_64.PreparedKey.prepareSecret (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87 = fillCallsG (sigma v.code) (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa87) := by
  kernel_rfl

theorem prepareSecret87_stub : stubSideG (Impl.MlDsa.X86_64.PreparedKey.prepareSecret (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa87) VecLevel.sse.level stubStack 32 [] = true := by decide +kernel

/-- `Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87"`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem prepareSecret87_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.prepareSecret v.level (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87)
      ((Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").contract X86_64.abi 32) 0 :=
  verifiedScrubbedAllFillG (api := Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")
    { code := Impl.MlDsa.X86_64.PreparedKey.prepareSecret (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87
      verified := Proof.MlDsa.X86_64.Verify.Prepare.prepareSecret_verified (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      spSafe := Proof.MlDsa.X86_64.Verify.Prepare.prepareSecret_spSafe (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) } _
    (Proof.MlDsa.X86_64.PreparedKey.Scrub.secOut (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    (((prepareSecret87_eq v) ▸ fillG_of (sigma_side v) _))
    (Nat.zero_le _) (Nat.le_refl _) (ha := prepareSecret87_stub)

theorem prepareSecret87_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.prepareSecret v.level (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Verify.Prepare.prepareSecret_spSafe (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem pkTr87_codeSp : (Impl.MlDsa.X86_64.PkTr.pkTr Spec.MlDsa.mlDsa87).all (fun i => !isa.writesSp i) = true := by sp_safe

/-- `Spec.MlDsa.pkTr87Api`'s function as emitted meets its contract in constant time and
returns without secret residue. -/
theorem pkTr87_scrubbed :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.pkTr Spec.MlDsa.mlDsa87) (Spec.MlDsa.pkTr87Api.contract X86_64.abi 32) 0 :=
  verifiedScrubbedAll (api := Spec.MlDsa.pkTr87Api)
    { code := Impl.MlDsa.X86_64.PkTr.pkTr Spec.MlDsa.mlDsa87
      verified := Proof.MlDsa.X86_64.PkTr.pkTr87_verified
      spSafe := pkTr87_codeSp } .sse (VG.Proof.MlDsa.X86_64.Scrub.pkTrOut Spec.MlDsa.mlDsa87 _) (hs := by decide +kernel)

theorem pkTr87_spSafe : (Impl.MlDsa.X86_64.Fn.pkTr Spec.MlDsa.mlDsa87).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe pkTr87_codeSp

end VG.Proof.MlDsa.X86_64.FnScrub
