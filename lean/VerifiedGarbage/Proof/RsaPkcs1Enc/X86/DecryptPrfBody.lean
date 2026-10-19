module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfBodyFrames
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfPointer
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfMac
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfIncrement
public import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # One complete IRPRF iteration writes the specified block -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt
open VG.Proof.RsaPkcs1Enc

theorem prfBody_ok (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {key : List Byte}
    (h : Context g bs s) (label : List Nat) (lenCode : List Instr) (L dst i nb : Nat)
    (counter : s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oI) 32 = BitVec.ofNat 32 i)
    (blocks : s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oNB) 32 = BitVec.ofNat 32 nb)
    (dstLow : 192 ≤ dst + 32 * i) (dstHigh : dst + 32 * i + 32 ≤ sHash)
    (lengthBound : label.length + 4 ≤ 16)
    (keyBytes : Spec.Rsa.bytesAt s.mem (g.scratch sKDK 32).base 32 = key)
    (messageOk : ∀ (a : State), Context g bs a → a.gpr .edi = g.workspace + BitVec.ofNat 32 sMsg →
      a.gpr .ebx = BitVec.ofNat 32 i → a.gpr .edx = BitVec.ofNat 32 g.length →
      WP isa (.block (msgBytes label lenCode)) a fun t => Context g bs t ∧
        Frame [g.scratch sMsg 16] a.mem t.mem ∧ Keeps [.eax, .ecx] a t ∧
        Spec.Rsa.bytesAt t.mem (g.scratch sMsg (label.length + 4)).base (label.length + 4) =
          prfMessage i (label.map (BitVec.ofNat 8)) L) :
    WP isa (prfBody (hashFns v) label lenCode dst) s fun t => Context g bs t ∧
      Frame (prfBodyWrites g (dst + 32 * i)) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebx, .edi] s t ∧
      Spec.Rsa.bytesAt t.mem (g.scratch (dst + 32 * i) 32).base 32 = prfBlock key (label.map (BitVec.ofNat 8)) L i ∧
      t.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oI) 32 = BitVec.ofNat 32 (i + 1) ∧
      t.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oNB) 32 = BitVec.ofNat 32 nb ∧
      t.zf = some (BitVec.ofNat 32 (i + 1) - BitVec.ofNat 32 nb == 0) := by
  unfold prfBody
  refine WP.seq (WP.mono (prfMsgPtr_ok h counter) ?_)
  rintro a ⟨ha, Ma, Ka, ptrA, counterA, lengthA⟩
  refine WP.seq (WP.mono (messageOk a ha ptrA counterA lengthA) ?_)
  rintro b ⟨hb, Fb, Kb, messageB⟩
  have FhashB := messageFrame_hash ha Fb
  have counterB : b.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oI) 32 = BitVec.ofNat 32 i := (hash_local ha FhashB (by decide : 80 ≤ oI)
    (by decide : oI + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes)).trans (by rw [Ma]; exact counter)
  have blocksB : b.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oNB) 32 = BitVec.ofNat 32 nb := (hash_local ha FhashB (by decide : 80 ≤ oNB)
    (by decide : oNB + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes)).trans (by rw [Ma]; exact blocks)
  have keyB : Spec.Rsa.bytesAt b.mem (g.scratch sKDK 32).base 32 = key := (messageFrame_key Fb).trans (by rw [Ma]; exact keyBytes)
  have rest : WP isa (.seq (prfMac (hashFns v) (label.length + 4) dst) (.block incr)) b
      (fun t => Context g bs t ∧ Frame (prfBodyWrites g (dst + 32 * i)) s.mem t.mem ∧
        Keeps [.eax, .ecx, .edx, .ebx, .edi] s t ∧
        Spec.Rsa.bytesAt t.mem (g.scratch (dst + 32 * i) 32).base 32 = prfBlock key (label.map (BitVec.ofNat 8)) L i ∧
        t.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oI) 32 = BitVec.ofNat 32 (i + 1) ∧
        t.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oNB) 32 = BitVec.ofNat 32 nb ∧
        t.zf = some (BitVec.ofNat 32 (i + 1) - BitVec.ofNat 32 nb == 0)) := by
    refine WP.seq (WP.mono (prfMac_ok v hb dst i (label.length + 4) counterB dstLow dstHigh
      lengthBound (by rw [prfMessage_length, List.length_map]) keyB messageB) ?_)
    rintro c ⟨hc, Fc, FfineC, Kc, digestC⟩
    have counterC := (hash_local hb Fc (by decide : 80 ≤ oI)
      (by decide : oI + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes)).trans counterB
    have blocksC := (hash_local hb Fc (by decide : 80 ≤ oNB)
      (by decide : oNB + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes)).trans blocksB
    refine WP.mono (prfIncr_ok hc counterC blocksC) ?_
    rintro t ⟨ht, F, K, ci, nbT, zf⟩
    refine ⟨ht, ?_, (Ka.mono (by decide)).trans ((Kb.mono (by decide)).trans ((Kc.mono (by decide)).trans (K.mono (by decide)))),
      ?_, ci, nbT, zf⟩
    · have Fbs : Frame (prfBodyWrites g (dst + 32 * i)) s.mem b.mem := by
        rw [← Ma]
        exact Fb.sub (by
          intro r hr
          obtain rfl := List.mem_singleton.mp hr
          exact ⟨_, by simp [prfBodyWrites], fun _ hx => hx⟩)
      exact Fbs.trans ((FfineC.sub (by
        intro r hr
        exact ⟨r, by simp only [prfBodyWrites, List.mem_cons]; exact Or.inr (Or.inr hr), fun _ hx => hx⟩)).trans
        (F.sub (by
          intro r hr
          obtain rfl := List.mem_singleton.mp hr
          exact ⟨_, by simp [prfBodyWrites], fun _ hx => hx⟩)))
    · exact (incrementFrame_scratch hc (by unfold sHash at dstHigh; omega) F).trans digestC
  unfold prfMac at rest
  have flat := WP.assoc rest
  exact WP.seq (WP.mono (WP.seq_iff.mp flat) fun _ hu => WP.assoc hu)

end VG.Proof.RsaPkcs1Enc.X86.Dec
