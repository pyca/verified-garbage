module

public import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
meta import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
public import VerifiedGarbage.Proof.Sha1.X86.Shared
public import VerifiedGarbage.Proof.Sha1.X86.Compress
meta import VerifiedGarbage.Proof.Sha1.X86.Shared
import VerifiedGarbage.Impl.Sha256.X86.Stream
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Md5.X86.Compress
import VerifiedGarbage.Proof.MdStream.X86.ArgWord
import VerifiedGarbage.Proof.MdStream.X86.Words
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFin
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
import VerifiedGarbage.Proof.Pbkdf2.MdHmac
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Sha1.Scratch
import VerifiedGarbage.Proof.Sha1.StateMem
import VerifiedGarbage.Proof.Sha1.X86.Stream.Variant
import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Proof.Sha256.X86.Compress
import VerifiedGarbage.Proof.Sha512.Spec
import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
meta import VerifiedGarbage.Impl.Sha256.X86.Stream
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
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
meta import VerifiedGarbage.Proof.Framework.X86.StackScratch
meta import VerifiedGarbage.Proof.Hmac.Common
meta import VerifiedGarbage.Proof.Md5.X86.Compress
meta import VerifiedGarbage.Proof.MdStream.X86.ArgWord
meta import VerifiedGarbage.Proof.MdStream.X86.Words
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFin
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
meta import VerifiedGarbage.Proof.Pbkdf2.MdHmac
meta import VerifiedGarbage.Proof.Pbkdf2.Memory
meta import VerifiedGarbage.Proof.Sha1.Scratch
meta import VerifiedGarbage.Proof.Sha1.StateMem
meta import VerifiedGarbage.Proof.Sha1.X86.Compress
meta import VerifiedGarbage.Proof.Sha1.X86.Stream.Variant
meta import VerifiedGarbage.Proof.Sha256.StateMem
meta import VerifiedGarbage.Proof.Sha256.X86.Compress
meta import VerifiedGarbage.Proof.Sha512.Spec
meta import VerifiedGarbage.Proof.Sha512.X86.Stream.Init

/-!
# SHA-1 on x86: the scalar compression function: the variant's code and proofs

The variant `VG.Variants.Sha1.X86.Scalar.variant`
(`Variants/Sha1/X86/Scalar.lean`), with the proofs its interface asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.Sha1.X86.Scalar

open VG.X86
open VG.Proof.Pbkdf2.Stream.X86 (Sha1Stream)
open VG.Proof.Pbkdf2.Md.X86 (sha1M)
open VG.Proof.Sha1.X86.Variants (pbkdf2Fns)

/-- The streaming functions made with the scalar compression function. Its checks of the
code are one kernel evaluation (`taint_decide_all`). -/
def stream : Sha1Stream := by
  refine {
    suffix := "",
    upd := Impl.Sha1.X86.Stream.update,
    fin := Impl.Sha1.X86.Stream.finalize,
    updOK := Proof.Sha1.X86.Stream.Update.update_verified,
    finOK := Proof.Sha1.X86.Stream.Finalize.finalize_verified,
    updSp := NoSp.of_all ?_,
    finSp := NoSp.of_all ?_,
    updSU := ?_,
    finSU := ?_ }
  taint_decide_all

materialize_code sha1HInit := (sha1M stream "vg_sha1_compress" Impl.Sha1.X86.compress).hmacInit
materialize_code sha1HFinalize := (sha1M stream "vg_sha1_compress" Impl.Sha1.X86.compress).hmacFin
materialize_code sha1HIterate := (sha1M stream "vg_sha1_compress" Impl.Sha1.X86.compress).iterate
materialize_code sha1HPbkdf2 := (pbkdf2Fns stream "vg_sha1_compress" Impl.Sha1.X86.compress).pbkdf2

/-- The backend. Its checks of the code (`spSafe`, `NoSp`, the stack) are one kernel
evaluation (`taint_decide_all`), which evaluates the compression function they all
contain once. -/
def variant : Proof.Sha1.X86.Variants.Backend := by
  refine {
    cmpN := "vg_sha1_compress",
    cmpC := Impl.Sha1.X86.compress,
    cmp := Proof.Sha1.X86.compress_verified,
    cmpSp := NoSp.of_all ?_,
    cmpStack := ?_,
    stream := stream,
    features := [],
    functions := [
      { api := Spec.Sha1.updateApi
        code := Impl.StackScratch.X86.withStackScratch 188 5 Impl.Sha1.X86.Stream.update
        contract := Spec.Sha1.updateContract X86.abi (20 + 188)
        stack := 20 + 188
        verified := Proof.Sha1.X86.Shared.update
        ofSig := ⟨_, _, _, rfl⟩
        ofApi := rfl
        spSafe := Code.all_of_allInstrs ?_ },
      { api := Spec.Sha1.finalizeApi
        code := Impl.StackScratch.X86.withStackScratch 184 4 Impl.Sha1.X86.Stream.finalize
        contract := Spec.Sha1.finalizeContract X86.abi (20 + 184)
        stack := 20 + 184
        verified := Proof.Sha1.X86.Shared.finalize
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
    iterStack := ?_ }
  taint_decide_all

end VG.Proof.Variants.Sha1.X86.Scalar
