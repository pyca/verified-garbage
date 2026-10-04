import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
import VerifiedGarbage.Proof.Sha1.X86.Shared
import VerifiedGarbage.Proof.Sha1.X86.ShaNi.Compress

/-!
# SHA-1 on x86 with the SHA extensions

A variant of `Sha1` on x86 (see `TCB/Emit.lean`): `vg_sha1_compress_shani`,
which needs the SHA extensions and SSSE3, and the streaming `update` and
`finalize` made with it, which HMAC's and PBKDF2's functions call
(`Generic/Sha1/X86/`).
-/
namespace VG.Variants.Sha1.X86.ShaNi
open VG VG.X86
open VG.Proof.Sha1.X86.Stream (params dims)
open VG.Proof.Sha1 (md)
open VG.Proof.MdStream VG.Proof.MdStream.X86
open VG.Proof.Pbkdf2.Stream.X86 (Sha1Stream)
open VG.Proof.Pbkdf2.Md.X86 (sha1M)
open VG.Proof.Sha1.X86.Variants (pbkdf2Fns)

abbrev cmpN := "vg_sha1_compress_shani"
abbrev cmpC := Impl.Sha1.X86.ShaNi.compress

abbrev sha1Update := Impl.MdStream.X86.update params cmpN cmpC
materialize_code sha1Update
abbrev sha1Finalize := Impl.MdStream.X86.finalize params cmpN cmpC
materialize_code sha1Finalize

theorem callee : CalleeOk (P := params) md cmpC :=
  ⟨Proof.Sha1.X86.ShaNi.compress_verified.1, Proof.Sha1.X86.ShaNi.compress_nosp,
    Proof.Sha1.X86.ShaNi.compress_stack⟩

theorem update_ct : ConstantTime isa (updK (P := params) md 160).pre
    (updK (P := params) md 160).pub sha1Update :=
  VG.Taint.constantTime (A := sseTaint) (Proof.MdStream.X86.Update.τ₀ params 160)
    (fun _ _ h₁ h₂ hp => Proof.MdStream.X86.Update.agree₀ dims h₁ h₂ hp) (by taint_decide)

theorem finalize_ct : ConstantTime isa (finK (P := params) md 160).pre
    (finK (P := params) md 160).pub sha1Finalize :=
  VG.Taint.constantTime (A := sseTaint) (Proof.MdStream.X86.Finalize.τ₀ params 160)
    (fun _ _ h₁ h₂ hp => Proof.MdStream.X86.Finalize.agree₀ dims h₁ h₂ hp) (by taint_decide)

/-- The streaming functions made with the SHA-NI compression function. -/
def stream : Sha1Stream where
  suffix := "_shani"
  upd := sha1Update
  fin := sha1Finalize
  updOK := Proof.Sha1.X86.Stream.update_of callee update_ct
  finOK := Proof.Sha1.X86.Stream.finalize_of callee finalize_ct
  updSp := NoSp.of_all (by lit_decide)
  finSp := NoSp.of_all (by lit_decide)
  updSU := by lit_decide
  finSU := by lit_decide

theorem updateScratch_shared :
    Verified X86.target sha1Update (Spec.Sha1.updateScratchContract X86.abi 20) :=
  Proof.Sha1.X86.Shared.updateScratch_of stream.updOK

theorem finalizeScratch_shared :
    Verified X86.target sha1Finalize (Spec.Sha1.finalizeScratchContract X86.abi 20) :=
  Proof.Sha1.X86.Shared.finalizeScratch_of stream.finOK

materialize_code sha1HInit := (sha1M stream cmpN cmpC).hmacInit
materialize_code sha1HFinalize := (sha1M stream cmpN cmpC).hmacFin
materialize_code sha1HIterate := (sha1M stream cmpN cmpC).iterate
materialize_code sha1HPbkdf2 := (pbkdf2Fns stream cmpN cmpC).pbkdf2

def variant : Proof.Sha1.X86.Variants.Backend where
  cmpN := cmpN
  cmpC := cmpC
  cmp := Proof.Sha1.X86.ShaNi.compress_verified
  cmpSp := Proof.Sha1.X86.ShaNi.compress_nosp
  cmpStack := Proof.Sha1.X86.ShaNi.compress_stack
  stream := stream
  features := ["sha", "ssse3"]
  functions := [
    { api := Spec.Sha1.compressApi
      code := cmpC
      contract := Spec.Sha1.compressContract X86.abi
      verified := Proof.Sha1.X86.Shared.compress_of Proof.Sha1.X86.ShaNi.compress_verified
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) },
    { api := Spec.Sha1.updateApi
      code := Impl.StackScratch.X86.withStackScratch 188 5 sha1Update
      contract := Spec.Sha1.updateContract X86.abi (20 + 188)
      stack := 20 + 188
      verified := Proof.Sha1.X86.Shared.update_frame updateScratch_shared (by lit_decide) (by lit_decide)
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) },
    { api := Spec.Sha1.finalizeApi
      code := Impl.StackScratch.X86.withStackScratch 184 4 sha1Finalize
      contract := Spec.Sha1.finalizeContract X86.abi (20 + 184)
      stack := 20 + 184
      verified := Proof.Sha1.X86.Shared.finalize_frame finalizeScratch_shared (by lit_decide)
        (by lit_decide)
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) },
    { api := Spec.Sha1.updateScratchApi
      code := sha1Update
      contract := Spec.Sha1.updateScratchContract X86.abi 20
      stack := 20
      verified := updateScratch_shared
      ofSig := ⟨_, _, _, rfl⟩
      ofApi := rfl
      spSafe := Code.all_of_allInstrs (by lit_decide) },
    { api := Spec.Sha1.finalizeScratchApi
      code := sha1Finalize
      contract := Spec.Sha1.finalizeScratchContract X86.abi 20
      stack := 20
      verified := finalizeScratch_shared
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

end VG.Variants.Sha1.X86.ShaNi
