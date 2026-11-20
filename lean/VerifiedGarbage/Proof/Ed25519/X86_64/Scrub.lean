module

public import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed
public import VerifiedGarbage.Impl.Ed25519.X86_64.KeyPair
public import VerifiedGarbage.Impl.Ed25519.X86_64.SignCached
public import VerifiedGarbage.Proof.Ed25519.X86_64.KeyPair
public import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Expanded
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLit
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyLit
public import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyIfma
public import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyMessage
public import VerifiedGarbage.Proof.Sha512.X86_64.Variant
public import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.FillRefl
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Spec.Ed25519.ExpandedSign
public import VerifiedGarbage.Spec.Ed25519.KeyPair
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Ed25519.WholeLocal

/-!
# Ed25519 on x86-64, without secret residue

The postconditions of `vg_ed25519_key_pair` and `vg_ed25519_sign_expanded`
read the memory on return only within their outputs, and that of
`vg_ed25519_verify` not at all (`X86_64.Scrub.PostOut`), whatever tables of
constants their code takes: each implementation returns with its whole stack
wiped (`X86_64.Scrub.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub
open VG.Proof.Ed25519.WholeLocal (bytesAt_congr)

variable (cs : List (String × List (BitVec 64))) (stack : Nat)

theorem keyPairOut :
    PostOut (Spec.Ed25519.keyPairContract (X86_64.abi.withConsts cs) stack) (Spec.Ed25519.keyPairSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, ex, sd, sc], _ =>
      simp only [Spec.Ed25519.keyPairSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Ed25519.bytesAt m₂ ex 64 = _ ∧ Spec.Ed25519.bytesAt m₂ o 32 = _
      rw [bytesAt_congr hb.2.1, bytesAt_congr hb.1]
      exact h

theorem signExpandedOut :
    PostOut (Spec.Ed25519.signExpandedContract (X86_64.abi.withConsts cs) stack)
      (Spec.Ed25519.signExpandedSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, ex, pk, msg, len, sc], _ =>
      simp only [Spec.Ed25519.signExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      show ∀ seed : List Byte, _ → _ → Spec.Ed25519.bytesAt m₂ o 64 = _
      rw [bytesAt_congr hb.1]
      exact h

theorem verifyOut :
    PostOut (Spec.Ed25519.verifyContract (X86_64.abi.withConsts cs) stack) (Spec.Ed25519.verifySig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _], _ => exact h


/-! ## The functions as emitted

Each is generic over the SHA-512 compression function it calls (a variant,
`Proof.Sha512.X86_64.Compress`): its code with a stub in the compression
function's place (`stubC`, of the same scratch space), which the kernel
evaluates once for each scratch space a compression function may have
(`VerifyStub`, `SignStub`, `KeyPairStub`), and what the compression
function proves of its own code where it is defined (`Compress.side`) give
the cleanup's side conditions (`verifiedScrubbedAllFill`). The cleanup's
level is the compression function's joined with that of the function's own
instructions (`lv`). -/

/-- A stub of a SHA-512 compression function, with the scratch space `so`. -/
def stubC (so : Nat) : Impl.Sha512.X86_64.Stream.Callee := ⟨"vg_sha512_compress", .block [], so⟩

theorem updateOwn_fill {k : Nat} {so : Nat} {nm : String} {cd : Prog isa}
    (hd : calleeSide cd k 0 = true) :
    Fill k (fun _ => 0) (Impl.Sha512.X86_64.Stream.updateOwn (stubC so))
      (Impl.Sha512.X86_64.Stream.updateOwn ⟨nm, cd, so⟩) := by
  unfold Impl.Sha512.X86_64.Stream.updateOwn Impl.MdStream.X86_64.update
  fill_calls

theorem finalizeOwn_fill {k : Nat} {so : Nat} {nm : String} {cd : Prog isa}
    (hd : calleeSide cd k 0 = true) :
    Fill k (fun _ => 0) (Impl.Sha512.X86_64.Stream.finalizeOwn (stubC so))
      (Impl.Sha512.X86_64.Stream.finalizeOwn ⟨nm, cd, so⟩) := by
  unfold Impl.Sha512.X86_64.Stream.finalizeOwn Impl.MdStream.X86_64.finalize
  fill_calls

section
variable {fld : Impl.Ed25519.X86_64.Arith} {win : Prog isa} {fs : String}

theorem verify_fill {k so : Nat} {nm sfx : String} {cd : Prog isa} (hd : calleeSide cd k 0 = true) :
    Fill k (fun _ => 0) (Impl.Ed25519.X86_64.VerifyMessage.code fld win fs (stubC so) "")
      (Impl.Ed25519.X86_64.VerifyMessage.code fld win fs ⟨nm, cd, so⟩ sfx) := by
  refine Fill.frame _ _ (Fill.seq ?_ (Fill.refl _))
  unfold Impl.Ed25519.X86_64.VerifyMessage.hash Impl.Ed25519.X86_64.callWith
  exact .seq (Fill.refl _) (.seq (.seq (Fill.refl _) (.call _ _ (updateOwn_fill hd)))
    (.seq (.seq (Fill.refl _) (.call _ _ (updateOwn_fill hd)))
    (.seq (.seq (Fill.refl _) (.call _ _ (updateOwn_fill hd)))
      (.seq (Fill.refl _) (.call _ _ (finalizeOwn_fill hd))))))

/-- What the cleanup of `vg_ed25519_verify` with the field arithmetic `fld`
and the windows `win` needs of its code with a stub for each scratch space a
compression function may have, at the level `lv` of its own instructions. -/
def VerifyStub (lv : Impl.Scrub.X86_64.VecLevel) (fld : Impl.Ed25519.X86_64.Arith) (win : Prog isa)
    (fs : String) : Prop :=
  ∀ so, so = 0 ∨ so = 192 ∨ so = 1328 →
    stubSide (Impl.Ed25519.X86_64.VerifyMessage.code fld win fs (stubC so) "") lv.level (fun _ => 0) 184 [] = true

/-- `vg_ed25519_verify` with the SHA-512 compression function `c`, as emitted
(`Impl.Ed25519.X86_64.VerifyMessage.Fn.verify`), its cleanup included, meets
its contract in constant time and returns without secret residue. -/
theorem verify_scrubbed [Proof.Ed25519.X86_64.EdArith fld] (c : Proof.Sha512.X86_64.Compress)
    (hq : Proof.Ed25519.X86_64.VerifyMessage.EqCode fld win) (lv : Impl.Scrub.X86_64.VecLevel)
    (hs : VerifyStub lv fld win fs) :
    VerifiedScrubbed X86_64.target
      (Impl.Ed25519.X86_64.VerifyMessage.Fn.verify (c.level.join lv) fld win fs c.callee c.suffix)
      (Spec.Ed25519.verifyApi.contract (X86_64.abi.withConsts Impl.Ed25519.X86_64.baseOddConsts) 184) 32 := by
  have hv := Proof.Ed25519.X86_64.VerifyMessage.verified (fs := fs) hq c
  have hsp := Proof.Ed25519.X86_64.VerifyMessage.spSafe (fs := fs) hq c
  have hd := calleeSide_mono (level_join_left c.level lv) (Nat.le_refl 0) c.side
  have hso := c.hso
  generalize c.callee = f at hv hsp hd hso ⊢
  obtain ⟨nm, cd, so⟩ := f
  exact verifiedScrubbedAllFill (api := Spec.Ed25519.verifyApi)
    (a := Impl.Ed25519.X86_64.VerifyMessage.code fld win fs (stubC so) "") (ks := lv.level) (n := fun _ => 0)
    { code := Impl.Ed25519.X86_64.VerifyMessage.code fld win fs ⟨nm, cd, so⟩ c.suffix
      stack := 184
      verified := hv
      spSafe := hsp } (c.level.join lv) (verifyOut Impl.Ed25519.X86_64.baseOddConsts 184)
    (verify_fill hd) (level_join_right _ _) (Nat.le_refl _) (ha := hs so hso)

theorem verify_spSafe (c : Proof.Sha512.X86_64.Compress) (hq : Proof.Ed25519.X86_64.VerifyMessage.EqCode fld win)
    (lv : Impl.Scrub.X86_64.VecLevel) :
    (Impl.Ed25519.X86_64.VerifyMessage.Fn.verify lv fld win fs c.callee c.suffix).all
      (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.Ed25519.X86_64.VerifyMessage.spSafe (fs := fs) hq c)

end

theorem verify_stub_ifma :
    VerifyStub .avx Impl.X25519.X86_64.adx Impl.Ed25519.X86_64.Ifma.windows "_ifma" := by
  rintro so (rfl | rfl | rfl) <;> lit_decide


theorem verify_stub_adx :
    VerifyStub .sse Impl.X25519.X86_64.adx (Impl.Ed25519.X86_64.windows Impl.X25519.X86_64.adx) "_adx" := by
  rintro so (rfl | rfl | rfl) <;> lit_decide

theorem verify_stub_baseline :
    VerifyStub .sse Impl.X25519.X86_64.baseline (Impl.Ed25519.X86_64.windows Impl.X25519.X86_64.baseline) "" := by
  rintro so (rfl | rfl | rfl) <;> lit_decide

section
variable {bs : Prog isa} {fs : String}

theorem update_fill {k so : Nat} {nm sfx : String} {cd : Prog isa} (hd : calleeSide cd k 0 = true)
    (args : List Instr) :
    Fill k (fun _ => 0) (Impl.Ed25519.X86_64.SignCached.update (stubC so) "" args)
      (Impl.Ed25519.X86_64.SignCached.update ⟨nm, cd, so⟩ sfx args) :=
  .seq (Fill.refl _) (.call _ _ (updateOwn_fill hd))

theorem finalize_fill {k so : Nat} {nm sfx : String} {cd : Prog isa} (hd : calleeSide cd k 0 = true)
    (n : Nat) (w : Bool) :
    Fill k (fun _ => 0) (Impl.Ed25519.X86_64.SignCached.finalize (stubC so) "" n w)
      (Impl.Ed25519.X86_64.SignCached.finalize ⟨nm, cd, so⟩ sfx n w) :=
  .seq (Fill.refl _) (.call _ _ (finalizeOwn_fill hd))

theorem sign_fill {k so : Nat} {nm sfx : String} {cd : Prog isa} (hd : calleeSide cd k 0 = true) :
    Fill k (fun _ => 0) (Impl.Ed25519.X86_64.SignCached.codeExpanded bs fs (stubC so) "")
      (Impl.Ed25519.X86_64.SignCached.codeExpanded bs fs ⟨nm, cd, so⟩ sfx) :=
  .frame _ _ (.seq (Fill.refl _) (.seq (Fill.refl _)
    (.seq (.seq (Fill.refl _) (.seq (update_fill hd _) (.seq (update_fill hd _) (finalize_fill hd _ _))))
    (.seq (Fill.refl _) (.seq (Fill.refl _)
    (.seq (.seq (Fill.refl _) (.seq (update_fill hd _) (.seq (update_fill hd _)
      (.seq (update_fill hd _) (finalize_fill hd _ _)))))
    (Fill.refl _)))))))

/-- What the cleanup of `vg_ed25519_sign_expanded` with the base-point
multiplication `bs` needs of its code with a stub for each scratch space a
compression function may have, at the level `lv` of its own instructions. -/
def SignStub (lv : Impl.Scrub.X86_64.VecLevel) (bs : Prog isa) (fs : String) : Prop :=
  ∀ so, so = 0 ∨ so = 192 ∨ so = 1328 →
    stubSide (Impl.Ed25519.X86_64.SignCached.codeExpanded bs fs (stubC so) "") lv.level (fun _ => 0) 264 [] = true

/-- `vg_ed25519_sign_expanded` with the SHA-512 compression function `c`, as
emitted (`Impl.Ed25519.X86_64.SignCached.Fn.signExpanded`), its cleanup
included, meets its contract in constant time and returns without secret
residue. -/
theorem signExpanded_scrubbed [Proof.Ed25519.X86_64.EdBase bs] (c : Proof.Sha512.X86_64.Compress)
    (lv : Impl.Scrub.X86_64.VecLevel) (hs : SignStub lv bs fs) :
    VerifiedScrubbed X86_64.target
      (Impl.Ed25519.X86_64.SignCached.Fn.signExpanded (c.level.join lv) bs fs c.callee c.suffix)
      (Spec.Ed25519.signExpandedApi.contract (X86_64.abi.withConsts Impl.Ed25519.X86_64.combConsts) 264) 0 := by
  have hv := Proof.Ed25519.X86_64.SignCached.verifiedE (bs := bs) (fs := fs) c
  have hsp := Proof.Ed25519.X86_64.SignCached.spSafeE (bs := bs) (fs := fs) c
  have hd := calleeSide_mono (level_join_left c.level lv) (Nat.le_refl 0) c.side
  have hso := c.hso
  generalize c.callee = f at hv hsp hd hso ⊢
  obtain ⟨nm, cd, so⟩ := f
  exact verifiedScrubbedAllFill (api := Spec.Ed25519.signExpandedApi)
    (a := Impl.Ed25519.X86_64.SignCached.codeExpanded bs fs (stubC so) "") (ks := lv.level) (n := fun _ => 0)
    { code := Impl.Ed25519.X86_64.SignCached.codeExpanded bs fs ⟨nm, cd, so⟩ c.suffix
      stack := 264
      verified := hv
      spSafe := hsp } (c.level.join lv) (signExpandedOut Impl.Ed25519.X86_64.combConsts 264)
    (sign_fill hd) (level_join_right _ _) (Nat.le_refl _) (ha := hs so hso)

theorem signExpanded_spSafe [Proof.Ed25519.X86_64.EdBase bs] (c : Proof.Sha512.X86_64.Compress)
    (lv : Impl.Scrub.X86_64.VecLevel) :
    (Impl.Ed25519.X86_64.SignCached.Fn.signExpanded lv bs fs c.callee c.suffix).all
      (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.Ed25519.X86_64.SignCached.spSafeE (bs := bs) (fs := fs) c)

theorem dg_fill {k so : Nat} {nm : String} {cd : Prog isa} (hd : calleeSide cd k 0 = true) :
    Fill k (fun _ => 0) (Proof.Sha512.X86_64.OneShot.digest (Impl.MdStream.X86_64.out64 8) Spec.Sha512.H0_512 (stubC so))
      (Proof.Sha512.X86_64.OneShot.digest (Impl.MdStream.X86_64.out64 8) Spec.Sha512.H0_512 ⟨nm, cd, so⟩) := by
  fill_calls

/-- `vg_ed25519_key_pair`'s code with the digest of a stub compression
function of the scratch space `so`. -/
abbrev keyPairStub (bs : Prog isa) (fs : String) (so : Nat) : Prog isa :=
  Impl.Ed25519.X86_64.KeyPair.keyPair "vg_sha512_digest_core"
    (Proof.Sha512.X86_64.OneShot.digest (Impl.MdStream.X86_64.out64 8) Spec.Sha512.H0_512 (stubC so))
    ("vg_ed25519_public_key_expanded" ++ fs) (Impl.Ed25519.X86_64.publicKeyExpanded bs fs)

/-- What the cleanup of `vg_ed25519_key_pair` with the base-point
multiplication `bs` needs of its code with a stub for each scratch space a
compression function may have, at the level `lv` of its own instructions. -/
def KeyPairStub (lv : Impl.Scrub.X86_64.VecLevel) (bs : Prog isa) (fs : String) : Prop :=
  ∀ so, so = 0 ∨ so = 192 ∨ so = 1328 → stubSide (keyPairStub bs fs so) lv.level (fun _ => 0) 1632 [] = true

/-- `vg_ed25519_key_pair` with the SHA-512 compression function `c`, as
emitted (`Impl.Ed25519.X86_64.KeyPair.Fn.keyPair`), its cleanup included,
meets its contract in constant time and returns without secret residue. -/
theorem keyPair_scrubbed [Proof.Ed25519.X86_64.EdBase bs] (c : Proof.Sha512.X86_64.Compress)
    (lv : Impl.Scrub.X86_64.VecLevel) (hs : KeyPairStub lv bs fs) :
    VerifiedScrubbed X86_64.target
      (Impl.Ed25519.X86_64.KeyPair.Fn.keyPair (c.level.join lv)
        (Spec.Sha512.digest512Api.name ++ c.suffix ++ "_core") (Proof.Ed25519.X86_64.KeyPair.dgCode c)
        ("vg_ed25519_public_key_expanded" ++ fs) (Impl.Ed25519.X86_64.publicKeyExpanded bs fs))
      (Spec.Ed25519.keyPairApi.contract (X86_64.abi.withConsts Impl.Ed25519.X86_64.combConsts) 1632) 0 := by
  have hv := Proof.Ed25519.X86_64.KeyPair.verified c bs fs
    (dn := Spec.Sha512.digest512Api.name ++ c.suffix ++ "_core") (pn := "vg_ed25519_public_key_expanded" ++ fs)
  have hsp := Proof.Ed25519.X86_64.KeyPair.spSafe c bs fs
    (dn := Spec.Sha512.digest512Api.name ++ c.suffix ++ "_core") (pn := "vg_ed25519_public_key_expanded" ++ fs)
  have hd := calleeSide_mono (level_join_left c.level lv) (Nat.le_refl 0) c.side
  have hso := c.hso
  generalize Spec.Sha512.digest512Api.name ++ c.suffix ++ "_core" = dn at hv hsp ⊢
  unfold Proof.Ed25519.X86_64.KeyPair.dgCode at hv hsp ⊢
  generalize c.callee = f at hv hsp hd hso ⊢
  obtain ⟨nm, cd, so⟩ := f
  exact verifiedScrubbedAllFill (api := Spec.Ed25519.keyPairApi) (a := keyPairStub bs fs so) (ks := lv.level)
    (n := fun _ => 0)
    { code := Impl.Ed25519.X86_64.KeyPair.keyPair dn
        (Proof.Sha512.X86_64.OneShot.digest (Impl.MdStream.X86_64.out64 8) Spec.Sha512.H0_512 ⟨nm, cd, so⟩)
        ("vg_ed25519_public_key_expanded" ++ fs) (Impl.Ed25519.X86_64.publicKeyExpanded bs fs)
      stack := 1632
      verified := hv
      spSafe := hsp } (c.level.join lv) (keyPairOut Impl.Ed25519.X86_64.combConsts 1632)
    (.frame _ _ (.seq (Fill.refl _) (.seq (.call _ _ (dg_fill hd)) (Fill.refl _))))
    (level_join_right _ _) (Nat.le_refl _) (ha := hs so hso)

theorem keyPair_spSafe [Proof.Ed25519.X86_64.EdBase bs] (c : Proof.Sha512.X86_64.Compress)
    (lv : Impl.Scrub.X86_64.VecLevel) :
    (Impl.Ed25519.X86_64.KeyPair.Fn.keyPair lv (Spec.Sha512.digest512Api.name ++ c.suffix ++ "_core")
        (Proof.Ed25519.X86_64.KeyPair.dgCode c) ("vg_ed25519_public_key_expanded" ++ fs)
        (Impl.Ed25519.X86_64.publicKeyExpanded bs fs)).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.Ed25519.X86_64.KeyPair.spSafe c bs fs)

end

theorem sign_stub_ifma : SignStub .avx Impl.Ed25519.X86_64.scalarBase_ifma "_ifma" := by
  rintro so (rfl | rfl | rfl) <;> lit_decide

theorem sign_stub_adx : SignStub .avx Impl.Ed25519.X86_64.scalarBase_adx "_adx" := by
  rintro so (rfl | rfl | rfl) <;> lit_decide

theorem sign_stub_baseline :
    SignStub .sse (Impl.Ed25519.X86_64.scalarBase_precomputed Impl.X25519.X86_64.baseline) "" := by
  rintro so (rfl | rfl | rfl) <;> lit_decide

theorem keyPair_stub_ifma : KeyPairStub .avx Impl.Ed25519.X86_64.scalarBase_ifma "_ifma" := by
  rintro so (rfl | rfl | rfl) <;> lit_decide

theorem keyPair_stub_adx : KeyPairStub .avx Impl.Ed25519.X86_64.scalarBase_adx "_adx" := by
  rintro so (rfl | rfl | rfl) <;> lit_decide

theorem keyPair_stub_baseline :
    KeyPairStub .sse (Impl.Ed25519.X86_64.scalarBase_precomputed Impl.X25519.X86_64.baseline) "" := by
  rintro so (rfl | rfl | rfl) <;> lit_decide

end VG.Proof.Ed25519.X86_64.Scrub
