module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMessageLength
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Bytes

/-! # The PRF scratch buffer contains the specified complete message -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt
open VG.Proof.RsaPkcs1Enc

theorem MessageWritten.complete {g : Geometry} {bs : Fin 9 → List Byte} {s0 s : State}
    {xs : List Byte} (h : MessageWritten g bs s0 xs xs.length s) :
    Spec.Rsa.bytesAt s.mem (g.scratch sMsg xs.length).base xs.length = xs := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  · intro j hj hxs
    have same := h.bytes j hxs
    rw [← List.getElem_eq_getD (h := hxs) 0] at same
    simpa only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, Geometry.scratch] using same

theorem clMessage_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {i : Nat}
    (h : Context g bs s) (ptr : s.gpr .edi = g.workspace + BitVec.ofNat 32 sMsg)
    (counter : s.gpr .ebx = BitVec.ofNat 32 i) (counterBound : i < 256) :
    WP isa (.block (msgBytes lengthLabel clLen)) s fun t => Context g bs t ∧
      Frame [g.scratch sMsg 16] s.mem t.mem ∧ Keeps [.eax, .ecx] s t ∧
      Spec.Rsa.bytesAt t.mem (g.scratch sMsg 10).base 10 =
        prfMessage i (lengthLabel.map (BitVec.ofNat 8)) 256 := by
  unfold msgBytes
  rw [WP.block_append_iff]
  refine WP.mono (messagePrefix_ok (L := 256) h lengthLabel ptr counter counterBound (by decide)) ?_
  intro a ha
  refine WP.mono (clLen_ok ptr (by decide : (lengthLabel.map (BitVec.ofNat 8)).length = 6) ha) ?_
  intro t ht
  exact ⟨ht.context, ht.frame, ht.keep, ht.complete⟩

theorem amMessage_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {i : Nat}
    (h : Context g bs s) (ptr : s.gpr .edi = g.workspace + BitVec.ofNat 32 sMsg)
    (counter : s.gpr .ebx = BitVec.ofNat 32 i) (counterBound : i < 256)
    (length : s.gpr .edx = BitVec.ofNat 32 g.length) :
    WP isa (.block (msgBytes messageLabel amLen)) s fun t => Context g bs t ∧
      Frame [g.scratch sMsg 16] s.mem t.mem ∧ Keeps [.eax, .ecx] s t ∧
      Spec.Rsa.bytesAt t.mem (g.scratch sMsg 11).base 11 =
        prfMessage i (messageLabel.map (BitVec.ofNat 8)) g.length := by
  unfold msgBytes
  rw [WP.block_append_iff]
  refine WP.mono (messagePrefix_ok (L := g.length) h messageLabel ptr counter counterBound (by decide)) ?_
  intro a ha
  refine WP.mono (amLen_ok ptr (by decide : (messageLabel.map (BitVec.ofNat 8)).length = 7) length ha) ?_
  intro t ht
  exact ⟨ht.context, ht.frame, ht.keep, ht.complete⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec
