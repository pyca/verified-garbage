module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeCopy
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeDispatch
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeHead
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodePadding
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The encoder writes the complete EMSA-PKCS1-v1_5 byte string -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Bignum VG.Proof.Bignum.X86 VG.WriteBytes
open VG.Impl.RsaPkcs1Sig.X86 Spec.RsaPkcs1Sig

structure WPre (s0 : State) (x : BitVec 32) (h : Hash) (k : Nat) (s : State) : Prop where
  keep : Keeps [.eax, .ebx] s0 s
  mem : s.mem = s0.mem
  info : s.gpr .ebx = BitVec.ofNat 32 (h.prefix.length + h.len)
  digest : s0.gpr .ebp = BitVec.ofNat 32 h.len
  hash : s0.gpr .edx = x
  id : Hash.ofId x.toNat = some h
  length : s0.gpr .ecx = BitVec.ofNat 32 k
  room : h.prefix.length + h.len + 11 ≤ k
  bound : k ≤ 1024

theorem write_ok {s0 s : State} {x : BitVec 32} {h : Hash} {k : Nat} (buf : Buf s0 k)
    (pre : WPre s0 x h k s) (digest : Digest s0 k h.len) :
    WP isa write s fun t => t.gpr .eax = 1 ∧ W s0
      ([0x00, 0x01] ++ List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++
        [0x00] ++ h.prefix ++ Spec.Rsa.bytesAt s0.mem (byteAddr (s0.gpr .esi)) h.len) t := by
  have room := pre.room
  have bound := pre.bound
  have initial : W s0 [] s := by
    refine ⟨pre.keep.mono (by decide), ?_, ?_⟩
    · rw [writeBytes_nil]; exact pre.mem
    · change s.gpr .edi = s0.gpr .edi + 0#32
      rw [BitVec.add_zero]
      exact pre.keep.1 .edi (by decide)
  unfold write
  refine WP.seq (WP.mono (head_ok buf bound room initial
    ((pre.keep.1 .ecx (by decide)).trans pre.length) pre.info) fun s1 ⟨h1, ax, count, k1⟩ => ?_)
  refine WP.seq (WP.mono (psLoop_ok buf bound (by omega) (by simp; omega) 0xff h1 ax count)
    fun s2 ⟨h2, k2⟩ => ?_)
  refine WP.seq (WP.mono (putByte_ok buf (by simp; omega) 0x00 h2) fun s3 ⟨h3, k3⟩ => ?_)
  have kept : Keeps [.eax, .edi, .ebx] s s3 :=
    (k1.trans (k2.mono (by decide))).trans (k3.mono (by decide))
  have hash3 : s3.gpr .edx = x :=
    (kept.1 _ (by decide)).trans ((pre.keep.1 _ (by decide)).trans pre.hash)
  have case : ∀ j (hj : j < hashes.length), x.toNat = 0 + j → ∀ u, SameF s3 u →
      WP isa (prefixBytes hashes[j]) u fun t =>
        W s0 ([0x00, 0x01] ++ List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++ [0x00] ++ h.prefix) t ∧
        Keeps [.eax, .edi, .ebx] s t := by
    intro j hj eq u hu
    have same : hashes[j] = h := by
      have id := pre.id
      rw [eq, Nat.zero_add, ofId_hashes j hj] at id
      exact Option.some.inj id
    rw [same]
    refine WP.mono (putBytes_ok buf h.prefix (by simp; omega) (W_sameF h3 hu)) fun t ⟨ht, kt⟩ => ?_
    refine ⟨ht, ?_⟩
    exact kept.trans ⟨fun r hr => by rw [kt.1 r (by simp_all), hu.1],
      kt.2.1.trans hu.2.2.1, kt.2.2.trans hu.2.2.2⟩
  have default : (∀ j < hashes.length, x.toNat ≠ 0 + j) → ∀ u, SameF s3 u →
      WP isa (.block []) u fun t =>
        W s0 ([0x00, 0x01] ++ List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++ [0x00] ++ h.prefix) t ∧
        Keeps [.eax, .edi, .ebx] s t := by
    intro absent u _
    exfalso
    have member : x.toNat < hashes.length := by
      by_contra no
      have id := pre.id
      rw [ofId_ge (by omega)] at id
      cases id
    exact absent _ member (by omega)
  refine WP.seq (WP.mono (dispatch_ok (fun _ h => prefixBytes h) (.block []) x hash3 hashes 0
    (by decide) case default s3 ⟨rfl, rfl, rfl, rfl⟩) fun s4 ⟨h4, k4⟩ => ?_)
  refine WP.seq (WP.mono (copyLoop_ok buf bound digest (by cases h <;> decide)
    (by simp; omega) h4
    ((k4.1 _ (by decide)).trans (pre.keep.1 _ (by decide)))
    ((k4.1 _ (by decide)).trans ((pre.keep.1 _ (by decide)).trans pre.digest))) fun s5 h5 => ?_)
  refine VG.Proof.Mont.X86.wp_movS rfl fun t T _ => WP.block_nil ?_
  exact ⟨T.gpr, h5.after T.keeps (by decide) T.mem (T.other .edi (by decide))⟩

end VG.Proof.RsaPkcs1Sig.X86
