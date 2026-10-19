module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignAfter
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignCallPublic

/-! # Intermediate signing states for relating independent secret digests -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Sign

structure EncodeReady (g : Geometry) (bs : Fin 8 → List Byte) (s : State) : Prop where
  context : Context g bs s
  dst : s.gpr .edi = g.temporary
  len : s.gpr .ecx = BitVec.ofNat 32 g.length
  hash : s.gpr .edx = g.hash
  src : s.gpr .esi = g.sources 2
  count : s.gpr .ebp = BitVec.ofNat 32 g.digestLength

structure EncodeDone (g : Geometry) (bs : Fin 8 → List Byte) (s : State) : Prop where
  context : Context g bs s
  encoded : Encoded g bs s

structure CallReady (g : Geometry) (bs : Fin 8 → List Byte) (s : State) : Prop where
  context : Context g bs s
  args : PrivateArgs g s

theorem encArgs_ready {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (.block encArgs) s (EncodeReady g bs) := by
  refine WP.mono (encArgs_ok h) ?_
  rintro t ⟨ht, _, _, dst, len, hash, src, count⟩
  exact ⟨ht, dst, len, hash, src, count⟩

theorem encode_done {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : EncodeReady g bs s) : WP isa VG.Impl.RsaPkcs1Sig.X86.encode s (EncodeDone g bs) := by
  refine WP.mono (encoding_ok h.context h.dst h.len h.hash h.src h.count) ?_
  rintro t ⟨ht, _, _, enc⟩
  exact ⟨ht, enc⟩

theorem callArgs_ready {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (.block callArgs) s (CallReady g bs) := by
  refine WP.mono (callArgs_ok h) ?_
  rintro t ⟨ht, args, _, _⟩
  exact ⟨ht, args⟩

theorem privateCall_ready (v : VG.Proof.Rsa.X86.PrivChecked.CrtImpl)
    {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : CallReady g bs s) :
    WP isa (.call (privName v) (VG.Proof.Rsa.X86.PrivChecked.privCode v)) s (Context g bs) := by
  refine WP.mono (private_call v h.context h.args rfl) ?_
  rintro t ⟨ht, _, _, _⟩
  exact ht

theorem encoded_status {g : Geometry} {bs1 bs2 : Fin 8 → List Byte} {s t : State}
    (hs : EncodeDone g bs1 s) (ht : EncodeDone g bs2 t) : s.gpr .eax = t.gpr .eax := by
  have lengths : (bs1 2).length = (bs2 2).length :=
    (hs.context.sources 2).length.trans (ht.context.sources 2).length.symm
  have option : (encodeId g.hash (bs1 2) g.length).isSome = (encodeId g.hash (bs2 2) g.length).isSome := by
    unfold encodeId
    cases id : Spec.RsaPkcs1Sig.Hash.ofId g.hash.toNat with
    | none => rfl
    | some hv =>
      simp only [Option.bind_some, Spec.RsaPkcs1Sig.encode, Spec.RsaPkcs1Sig.digestInfo,
        List.length_append, lengths]
      split <;> rfl
  have left := hs.encoded
  have right := ht.encoded
  unfold Encoded at left right
  cases e1 : encodeId g.hash (bs1 2) g.length <;>
    cases e2 : encodeId g.hash (bs2 2) g.length <;>
    simp only [e1, e2, Option.isSome_none, Option.isSome_some, Bool.false_eq_true, Bool.true_eq_false] at option left right
  · exact left.trans right.symm
  · exact left.1.trans right.1.symm

end VG.Proof.RsaPkcs1Sig.X86.Sgn
