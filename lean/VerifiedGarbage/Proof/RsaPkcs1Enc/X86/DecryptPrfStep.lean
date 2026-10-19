module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfInvariant

/-! # Extend the prefix of PRF output by one verified digest -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt
open VG.Proof.RsaPkcs1Enc

theorem prfInvariant_step (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s0 s : State} {R : PrfConfig} {key extra : List Byte} {i : Nat}
    (h : PrfInvariant g bs s0 R key extra i s) (bound : i < R.blocks)
    (messageOk : ∀ (a : State), Context g bs a → a.gpr .edi = g.workspace + BitVec.ofNat 32 sMsg →
      a.gpr .ebx = BitVec.ofNat 32 i → a.gpr .edx = BitVec.ofNat 32 g.length →
      WP isa (.block (msgBytes R.label R.lenCode)) a fun t => Context g bs t ∧
        Frame [g.scratch sMsg 16] a.mem t.mem ∧ Keeps [.eax, .ecx] a t ∧
        Spec.Rsa.bytesAt t.mem (g.scratch sMsg (R.label.length + 4)).base (R.label.length + 4) =
          prfMessage i (R.label.map (BitVec.ofNat 8)) R.length) :
    WP isa (prfBody (hashFns v) R.label R.lenCode R.dst) s fun t =>
      PrfInvariant g bs s0 R key extra (i + 1) t ∧
      t.zf = some (BitVec.ofNat 32 (i + 1) - BitVec.ofNat 32 R.blocks == 0) := by
  have dstHigh : R.dst + 32 * i + 32 ≤ sHash := by have := R.dstHigh; omega
  refine WP.mono (prfBody_ok v h.context R.label R.lenCode R.length R.dst i R.blocks
    h.counter h.blocks (by have := R.dstLow; omega) dstHigh R.labelBound h.keyBytes messageOk) ?_
  rintro t ⟨ht, F, K, digest, counter, blocks, zf⟩
  refine ⟨⟨ht, h.frame.trans (prfBodyFrame_rejection h.context dstHigh F), h.keep.trans K,
    counter, blocks, ?_, ?_, ?_⟩, zf⟩
  · exact (prfBody_bytes h.context (by decide : 208 ≤ sKDK) (by decide : sKDK + 32 ≤ sHash)
      dstHigh (Or.inl (by have := R.dstLow; unfold sKDK; omega)) F).trans h.keyBytes
  · exact (prfBody_bytes h.context R.extraLow R.extraHigh dstHigh (by
      rcases R.separate with before | after
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)) F).trans h.extraBytes
  · have earlier := (prfBody_bytes h.context (by have := R.dstLow; omega)
      (by omega : R.dst + 32 * i ≤ sHash) dstHigh (Or.inl (Nat.le_refl _)) F).trans h.prefixBytes
    change Spec.Rsa.bytesAt t.mem (byteAddr g.workspace + BitVec.ofNat 64 R.dst) (32 * (i + 1)) = _
    rw [show 32 * (i + 1) = 32 * i + 32 by omega, bytesAt_add]
    change Spec.Rsa.bytesAt t.mem (g.scratch R.dst (32 * i)).base (32 * i) ++
      Spec.Rsa.bytesAt t.mem ((byteAddr g.workspace + BitVec.ofNat 64 R.dst) + BitVec.ofNat 64 (32 * i)) 32 = _
    change Spec.Rsa.bytesAt t.mem (byteAddr g.workspace + BitVec.ofNat 64 (R.dst + 32 * i)) 32 = _ at digest
    rw [Offset.add_add, earlier, digest, List.range_succ, List.flatMap_append, List.flatMap_singleton]

end VG.Proof.RsaPkcs1Enc.X86.Dec
