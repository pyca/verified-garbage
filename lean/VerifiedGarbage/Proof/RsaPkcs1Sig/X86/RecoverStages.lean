module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverEncoding
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverPublicCall

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverCmpArgs
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverDigestArgs
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! # Intermediate verifier states used to compose independent executions -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Recover
open VG.Impl.RsaPkcs1Sig.X86.Verify (test0)

structure EncodeReady (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop where
  context : Context g bs s
  dst : s.gpr .edi = g.em2
  len : s.gpr .ecx = BitVec.ofNat 32 g.length
  hash : s.gpr .edx = g.hash
  src : s.gpr .esi = g.digest
  count : s.gpr .ebp = BitVec.ofNat 32 g.outputLength

structure EncodeDone (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop where
  context : Context g bs s
  encoded : Encoded g s

structure CompareReady (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop where
  context : Context g bs s
  src : s.gpr .esi = g.em1
  dst : s.gpr .edi = g.em2
  count : s.gpr .ecx = BitVec.ofNat 32 g.length

structure CallReady (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop where
  context : Context g bs s
  args : Arguments g (publicArgument g) 10 s

theorem encArgs_ready {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (.block encArgs) s (EncodeReady g bs) := by
  refine WP.mono (encArgs_ok h) ?_
  rintro t ⟨ht, _, _, dst, len, hash, count, src⟩
  exact ⟨ht, dst, len, hash, src, count⟩

theorem encode_done {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : EncodeReady g bs s) : WP isa VG.Impl.RsaPkcs1Sig.X86.encode s (EncodeDone g bs) := by
  refine WP.mono (encoding_ok h.context h.dst h.len h.hash h.src h.count) ?_
  rintro t ⟨ht, _, _, enc⟩
  exact ⟨ht, enc⟩

theorem cmpArgs_ready {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (.block cmpArgs) s (CompareReady g bs) := by
  refine WP.mono (cmpArgs_ok h) ?_
  rintro t ⟨ht, _, _, src, dst, cnt⟩
  exact ⟨ht, src, dst, cnt⟩

theorem compare_done {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : CompareReady g bs s) : WP isa VG.Impl.RsaPkcs1Sig.X86.compare s (Context g bs) := by
  refine WP.mono (compare_ok h.context h.src h.dst h.count) ?_
  rintro t ⟨ht, _, _, _⟩
  exact ht

theorem callArgs_ready {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (.block pubArgs) s (CallReady g bs) := by
  refine WP.mono (pubArgs_ok h) ?_
  rintro t ⟨ht, args, _, _⟩
  exact ⟨ht, args⟩

theorem publicCall_ready (v : PublicImpl) {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : CallReady g bs s) (len : g.signatureLength = g.length) :
    WP isa (.call v.name v.code) s (Context g bs) := by
  refine WP.mono (public_call v h.context h.args len) ?_
  rintro t ⟨ht, _, _, _⟩
  exact ht

theorem encoded_status {g : Geometry} {bs : Fin 4 → List Byte} {s t : State}
    (hs : EncodeDone g bs s) (ht : EncodeDone g bs t) : s.gpr .eax = t.gpr .eax := by
  have option : (encodeId g.hash (digestBytes g s) g.length).isSome =
      (encodeId g.hash (digestBytes g t) g.length).isSome := by
    unfold encodeId
    cases id : Spec.RsaPkcs1Sig.Hash.ofId g.hash.toNat with
    | none => rfl
    | some hv =>
      simp only [Option.bind_some, Spec.RsaPkcs1Sig.encode, Spec.RsaPkcs1Sig.digestInfo,
        List.length_append, digestBytes, Spec.Rsa.bytesAt, List.length_map, List.length_range]
      split <;> rfl
  have left := hs.encoded
  have right := ht.encoded
  unfold Encoded at left right
  cases e1 : encodeId g.hash (digestBytes g s) g.length <;>
    cases e2 : encodeId g.hash (digestBytes g t) g.length <;>
    simp only [e1, e2, Option.isSome_none, Option.isSome_some, Bool.false_eq_true, Bool.true_eq_false] at option left right
  · exact left.trans right.symm
  · exact left.1.trans right.1.symm

end VG.Proof.RsaPkcs1Sig.X86.Rcv
