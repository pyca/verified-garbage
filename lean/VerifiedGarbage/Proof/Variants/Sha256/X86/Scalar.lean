module

public import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
meta import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Sha256.X86.Stream.Digest
meta import VerifiedGarbage.Proof.Sha256.X86.Stream.Digest
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Md5.X86.Compress
import VerifiedGarbage.Proof.MdStream.Prefix
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFin
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
import VerifiedGarbage.Proof.Pbkdf2.MdHmac
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Sha256.X86.Stream.Variant
import VerifiedGarbage.Proof.Sha512.Spec
import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Hmac.Common
meta import VerifiedGarbage.Proof.Md5.X86.Compress
meta import VerifiedGarbage.Proof.MdStream.Prefix
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFin
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
meta import VerifiedGarbage.Proof.Pbkdf2.MdHmac
meta import VerifiedGarbage.Proof.Pbkdf2.Memory
meta import VerifiedGarbage.Proof.Sha256.X86.Stream.Variant
meta import VerifiedGarbage.Proof.Sha512.Spec
meta import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
public import VerifiedGarbage.Proof.Sha256.X86.Stream.Digest
public import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.MdStream.Prefix
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFin
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
public import VerifiedGarbage.Proof.Sha256.X86.Stream.Variant

/-!
# SHA-256 on x86: the scalar compression function: the variant's code and proofs

The variant `VG.Variants.Sha256.X86.Scalar.variant`
(`Variants/Sha256/X86/Scalar.lean`), with the proofs its interface asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.Sha256.X86.Scalar

open VG.X86
open VG.Proof.Pbkdf2.Stream.X86 (Sha256Stream)
open VG.Proof.Pbkdf2.Md.X86 (sha256M sha224M)
open VG.Proof.Sha256.X86.Variants (pbkdf2Fns pbkdf2Fns224)

/-- The streaming functions made with the scalar compression function. Its checks of the
code are one kernel evaluation (`taint_decide_all`). -/
def stream : Sha256Stream := by
  refine {
    suffix := "",
    upd := Impl.Sha256.X86.Stream.update,
    fin := Impl.Sha256.X86.Stream.finalize,
    updOK := Proof.Sha256.X86.Stream.Update.update_verified,
    finOK := Proof.Sha256.X86.Stream.Finalize.finalize_verified,
    updSp := NoSp.of_all ?_,
    finSp := NoSp.of_all ?_,
    updSU := ?_,
    finSU := ?_ }
  taint_decide_all

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

/-- The backend: its checks of the code (`spSafe`, `NoSp`, the stack) evaluated in one
kernel evaluation (`taint_decide_all`), which evaluates the compression function they
all contain once. -/
def variant : Proof.Sha256.X86.Variants.Backend := by
  refine {
    cmpN := "vg_sha256_compress",
    cmpC := Impl.Sha256.X86.compress,
    cmp := Proof.Sha256.X86.compress_verified,
    cmpSp := NoSp.of_all ?_,
    cmpStack := ?_,
    stream := stream,
    features := [],
    functions := [
      { api := Spec.Sha256.updateApi
        code := Impl.StackScratch.X86.withStackScratch 636 5 Impl.Sha256.X86.Stream.update
        contract := Spec.Sha256.updateContract X86.abi (20 + 636)
        stack := 20 + 636
        verified := Proof.Sha256.X86.Shared.update_frame Proof.Sha256.X86.Shared.updateScratch
          ?_ ?_
        ofSig := ⟨_, _, _, rfl⟩
        ofApi := rfl
        spSafe := Code.all_of_allInstrs ?_ },
      { api := Spec.Sha256.finalizeApi
        code := Impl.StackScratch.X86.withStackScratch 632 4 Impl.Sha256.X86.Stream.finalize
        contract := Spec.Sha256.finalizeContract X86.abi (20 + 632)
        stack := 20 + 632
        verified := Proof.Sha256.X86.Shared.finalize_frame Proof.Sha256.X86.Shared.finalizeScratch
          ?_ ?_
        ofSig := ⟨_, _, _, rfl⟩
        ofApi := rfl
        spSafe := Code.all_of_allInstrs ?_ },
      { api := Spec.Sha256.finalize224Api
        code := Impl.StackScratch.X86.withStackScratch 632 4 sha224Finalize
        contract := Spec.Sha256.finalize224Contract X86.abi (20 + 632)
        stack := 20 + 632
        verified := Proof.Sha256.X86.Shared.finalize224_frame
          (Proof.Sha256.X86.Shared.finalize224Scratch (Proof.Sha256.X86.Stream.finalize224_of Proof.Sha256.X86.Stream.callee finalize224_ct))
          ?_ ?_
        ofSig := ⟨_, _, _, rfl⟩
        ofApi := rfl
        spSafe := Code.all_of_allInstrs ?_ }],
    initSp := Code.all_of_allInstrs ?_,
    finSp := Code.all_of_allInstrs ?_,
    iterSp := Code.all_of_allInstrs ?_,
    pbkdf2Sp := Code.all_of_allInstrs ?_,
    initNoSp := NoSp.of_all ?_,
    initStack := ?_,
    finalizeNoSp := NoSp.of_all ?_,
    finalizeStack := ?_,
    iterNoSp := NoSp.of_all ?_,
    iterStack := ?_,
    init224Sp := Code.all_of_allInstrs ?_,
    fin224Sp := Code.all_of_allInstrs ?_,
    iter224Sp := Code.all_of_allInstrs ?_,
    pbkdf2_224Sp := Code.all_of_allInstrs ?_,
    init224NoSp := NoSp.of_all ?_,
    init224Stack := ?_,
    finalize224NoSp := NoSp.of_all ?_,
    finalize224Stack := ?_,
    iter224NoSp := NoSp.of_all ?_,
    iter224Stack := ?_ }
  taint_decide_all

end VG.Proof.Variants.Sha256.X86.Scalar
