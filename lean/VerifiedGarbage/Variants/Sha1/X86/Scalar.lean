import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
import VerifiedGarbage.Proof.Sha1.X86.Shared
import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# SHA-1 on x86: the scalar compression function

A variant of `Sha1` on x86 (see `TCB/Emit.lean`): `vg_sha1_compress`, in the
baseline ISA, and the streaming `update` and `finalize` made with it, which
HMAC's and PBKDF2's functions call (`Generic/Sha1/X86/`).
-/
namespace VG.Variants.Sha1.X86.Scalar

open VG.X86
open VG.Proof.Pbkdf2.Stream.X86 (Sha1Stream)
open VG.Proof.Pbkdf2.Md.X86 (sha1M)
open VG.Proof.Sha1.X86.Variants (pbkdf2Fns)

/-- The streaming functions made with the scalar compression function. -/
def stream : Sha1Stream where
  suffix := ""
  upd := Impl.Sha1.X86.Stream.update
  fin := Impl.Sha1.X86.Stream.finalize
  updOK := Proof.Sha1.X86.Stream.Update.update_verified
  finOK := Proof.Sha1.X86.Stream.Finalize.finalize_verified
  updSp := NoSp.of_all (by lit_decide)
  finSp := NoSp.of_all (by lit_decide)
  updSU := by lit_decide
  finSU := by lit_decide

materialize_code sha1HInit := (sha1M stream "vg_sha1_compress" Impl.Sha1.X86.compress).hmacInit
materialize_code sha1HFinalize := (sha1M stream "vg_sha1_compress" Impl.Sha1.X86.compress).hmacFin
materialize_code sha1HIterate := (sha1M stream "vg_sha1_compress" Impl.Sha1.X86.compress).iterate
materialize_code sha1HPbkdf2 := (pbkdf2Fns stream "vg_sha1_compress" Impl.Sha1.X86.compress).pbkdf2

def variant : Proof.Sha1.X86.Variants.Backend where
  cmpN := "vg_sha1_compress"
  cmpC := Impl.Sha1.X86.compress
  cmp := Proof.Sha1.X86.compress_verified
  cmpSp := NoSp.of_all (by lit_decide)
  cmpStack := by lit_decide
  stream := stream
  features := []
  functions := [
    { api := Spec.Sha1.compressApi
      code := Impl.Sha1.X86.compress
      contract := Spec.Sha1.compressContract X86.abi
      verified := Proof.Sha1.X86.Shared.compress
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) },
    { api := Spec.Sha1.updateApi
      code := Impl.StackScratch.X86.withStackScratch 188 5 Impl.Sha1.X86.Stream.update
      contract := Spec.Sha1.updateContract X86.abi (20 + 188)
      stack := 20 + 188
      verified := Proof.Sha1.X86.Shared.update
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) },
    { api := Spec.Sha1.finalizeApi
      code := Impl.StackScratch.X86.withStackScratch 184 4 Impl.Sha1.X86.Stream.finalize
      contract := Spec.Sha1.finalizeContract X86.abi (20 + 184)
      stack := 20 + 184
      verified := Proof.Sha1.X86.Shared.finalize
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) },
    { api := Spec.Sha1.updateScratchApi
      code := Impl.Sha1.X86.Stream.update
      contract := Spec.Sha1.updateScratchContract X86.abi 20
      stack := 20
      verified := Proof.Sha1.X86.Shared.updateScratch
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) },
    { api := Spec.Sha1.finalizeScratchApi
      code := Impl.Sha1.X86.Stream.finalize
      contract := Spec.Sha1.finalizeScratchContract X86.abi 20
      stack := 20
      verified := Proof.Sha1.X86.Shared.finalizeScratch
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

end VG.Variants.Sha1.X86.Scalar
