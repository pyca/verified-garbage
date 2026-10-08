import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Sha256.X86.Stream.Digest
import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# SHA-256 on x86: the scalar compression function

A variant of `Sha256` on x86 (see `TCB/Emit.lean`): `vg_sha256_compress`, in
the baseline ISA, the streaming `update` and `finalize` made with it, which
HMAC's and PBKDF2's functions call (`Generic/Sha256/X86/`), and SHA-224's
`finalize`.
-/
namespace VG.Variants.Sha256.X86.Scalar

open VG.X86
open VG.Proof.Pbkdf2.Stream.X86 (Sha256Stream)
open VG.Proof.Pbkdf2.Md.X86 (sha256M sha224M)
open VG.Proof.Sha256.X86.Variants (pbkdf2Fns pbkdf2Fns224)

/-- The streaming functions made with the scalar compression function. -/
def stream : Sha256Stream where
  suffix := ""
  upd := Impl.Sha256.X86.Stream.update
  fin := Impl.Sha256.X86.Stream.finalize
  updOK := Proof.Sha256.X86.Stream.Update.update_verified
  finOK := Proof.Sha256.X86.Stream.Finalize.finalize_verified
  updSp := NoSp.of_all (by lit_decide)
  finSp := NoSp.of_all (by lit_decide)
  updSU := by lit_decide
  finSU := by lit_decide

materialize_code sha256HInit := (sha256M stream "vg_sha256_compress" Impl.Sha256.X86.compress).hmacInit
materialize_code sha256HFinalize := (sha256M stream "vg_sha256_compress" Impl.Sha256.X86.compress).hmacFin
materialize_code sha256HIterate := (sha256M stream "vg_sha256_compress" Impl.Sha256.X86.compress).iterate
materialize_code sha256HPbkdf2 := (pbkdf2Fns stream "vg_sha256_compress" Impl.Sha256.X86.compress).pbkdf2
materialize_code sha224HInit := (sha224M stream "vg_sha256_compress" Impl.Sha256.X86.compress).hmacInit
materialize_code sha224HFinalize := (sha224M stream "vg_sha256_compress" Impl.Sha256.X86.compress).hmacFin
materialize_code sha224HIterate := (sha224M stream "vg_sha256_compress" Impl.Sha256.X86.compress).iterate
materialize_code sha224HPbkdf2 := (pbkdf2Fns224 stream "vg_sha256_compress" Impl.Sha256.X86.compress).pbkdf2

abbrev sha224Finalize := Impl.Sha256.X86.Stream.finalize224 "vg_sha256_compress" Impl.Sha256.X86.compress
materialize_code sha224Finalize

theorem finalize224_ct : ConstantTime isa
    (Proof.MdStream.X86.finKD (P := Impl.Sha256.X86.Stream.params224) Proof.Sha256.md 160 28).pre
    (Proof.MdStream.X86.finKD (P := Impl.Sha256.X86.Stream.params224) Proof.Sha256.md 160 28).pub sha224Finalize :=
  VG.Taint.constantTime (A := taint) (Proof.MdStream.X86.Finalize.τ₀D Impl.Sha256.X86.Stream.params224 160 28)
    (fun _ _ h₁ h₂ hp => Proof.MdStream.X86.Finalize.agree₀D Proof.Sha256.X86.Stream.dims224 (by decide) h₁ h₂ hp)
    (by taint_decide)

def variant : Proof.Sha256.X86.Variants.Backend where
  cmpN := "vg_sha256_compress"
  cmpC := Impl.Sha256.X86.compress
  cmp := Proof.Sha256.X86.compress_verified
  cmpSp := NoSp.of_all (by lit_decide)
  cmpStack := by lit_decide
  stream := stream
  features := []
  functions := [
    { api := Spec.Sha256.compressApi
      code := Impl.Sha256.X86.compress
      contract := Spec.Sha256.compressContract X86.abi
      verified := Proof.Sha256.X86.Shared.compress
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) },
    { api := Spec.Sha256.updateApi
      code := Impl.StackScratch.X86.withStackScratch 636 5 Impl.Sha256.X86.Stream.update
      contract := Spec.Sha256.updateContract X86.abi (20 + 636)
      stack := 20 + 636
      verified := Proof.Sha256.X86.Shared.update_frame Proof.Sha256.X86.Shared.updateScratch
        (by lit_decide) (by lit_decide)
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) },
    { api := Spec.Sha256.finalizeApi
      code := Impl.StackScratch.X86.withStackScratch 632 4 Impl.Sha256.X86.Stream.finalize
      contract := Spec.Sha256.finalizeContract X86.abi (20 + 632)
      stack := 20 + 632
      verified := Proof.Sha256.X86.Shared.finalize_frame Proof.Sha256.X86.Shared.finalizeScratch
        (by lit_decide) (by lit_decide)
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) },
    { api := Spec.Sha256.finalize224Api
      code := Impl.StackScratch.X86.withStackScratch 632 4 sha224Finalize
      contract := Spec.Sha256.finalize224Contract X86.abi (20 + 632)
      stack := 20 + 632
      verified := Proof.Sha256.X86.Shared.finalize224_frame
        (Proof.Sha256.X86.Shared.finalize224Scratch (Proof.Sha256.X86.Stream.finalize224_of Proof.Sha256.X86.Stream.callee finalize224_ct))
        (by lit_decide) (by lit_decide)
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) },
    { api := Spec.Sha256.updateScratchApi
      code := Impl.Sha256.X86.Stream.update
      contract := Spec.Sha256.updateScratchContract X86.abi 20
      stack := 20
      verified := Proof.Sha256.X86.Shared.updateScratch
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) },
    { api := Spec.Sha256.finalizeScratchApi
      code := Impl.Sha256.X86.Stream.finalize
      contract := Spec.Sha256.finalizeScratchContract X86.abi 20
      stack := 20
      verified := Proof.Sha256.X86.Shared.finalizeScratch
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) }]
  initSp := Code.all_of_allInstrs (by lit_decide)
  finSp := Code.all_of_allInstrs (by lit_decide)
  iterSp := Code.all_of_allInstrs (by lit_decide)
  pbkdf2Sp := Code.all_of_allInstrs (by lit_decide)
  initNoSp := NoSp.of_all (by lit_decide)
  initStack := by lit_decide
  finalizeNoSp := NoSp.of_all (by lit_decide)
  finalizeStack := by lit_decide
  iterNoSp := NoSp.of_all (by lit_decide)
  iterStack := by lit_decide
  init224Sp := Code.all_of_allInstrs (by lit_decide)
  fin224Sp := Code.all_of_allInstrs (by lit_decide)
  iter224Sp := Code.all_of_allInstrs (by lit_decide)
  pbkdf2_224Sp := Code.all_of_allInstrs (by lit_decide)
  init224NoSp := NoSp.of_all (by lit_decide)
  init224Stack := by lit_decide
  finalize224NoSp := NoSp.of_all (by lit_decide)
  finalize224Stack := by lit_decide
  iter224NoSp := NoSp.of_all (by lit_decide)
  iter224Stack := by lit_decide

end VG.Variants.Sha256.X86.Scalar
