module
public import VerifiedGarbage.Proof.AesGcm.SealBuffers
public import VerifiedGarbage.Spec.Gcm.Contiguous
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Omega

/-! The contiguous seal postcondition stays true under changes outside its
declared buffers, including the single writable buffer of an in-place call. -/
@[expose] public section
namespace VG.Proof.AesGcm.SealBuffers
open VG VG.Spec.Gcm

abbrev sig := sealContiguousSig 129

theorem agreements {m₁ m₂ : Mem} {k r iv nl ad al src dst n tag : Addr}
    (h : ∀ b ∈ Sig.bufs sig.params [k,r,iv,nl,ad,al,src,dst,n,tag], Agree m₁ m₂ b.1.base b.1.len) :
    Agree m₁ m₂ k 1032 ∧ Agree m₁ m₂ iv nl.toNat ∧ Agree m₁ m₂ ad al.toNat ∧ Agree m₁ m₂ src n.toNat ∧
      Agree m₁ m₂ dst n.toNat ∧ Agree m₁ m₂ tag 16 := by
  by_cases eq : src=dst
  · subst src
    simp [sig, sealContiguousSig, Sig.bufs, Elem.size] at h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.1,h.2.2.2.2⟩
  · simpa [sig,sealContiguousSig,Sig.bufs,Elem.size,eq] using h

theorem postInputs (vs : List Addr) (m m' out : Mem) (r : BitVec 0) (hl : vs.length=(sig.words 64).length)
    (hb : ∀ b∈Sig.bufs sig.params vs, ∀ a,b.1.Contains a 1 → m a=m' a)
    (h : Curry.apply (sig.words 64) (sealContiguousPost 64) vs m out r) :
    Curry.apply (sig.words 64) (sealContiguousPost 64) vs m' out r := by
  match vs,hl with
  | [k,rounds,iv,nl,ad,al,src,dst,n,tag],_ =>
    obtain ⟨key,nonce,aad,pt,_⟩ := agreements hb
    intro sk hk
    have hₖ := keyRounds_local (m:=m') (m':=m) (fun a ha => (key a ((Region.sub_prefix (show 256≤1032 by decide)) _ ha)).symm) hk
    change Spec.Gcm.aesGcmEncrypt sk 16 (Spec.Aes.bytesAt m' iv nl.toNat) (Spec.Aes.bytesAt m' src n.toNat) (Spec.Aes.bytesAt m' ad al.toNat) = _
    rw [bytesAt_congr (agree_of nonce),bytesAt_congr (agree_of pt),bytesAt_congr (agree_of aad)]
    exact h sk hₖ

theorem postOutputs (vs : List Addr) (m out out' : Mem) (r : BitVec 0) (hl : vs.length=(sig.words 64).length)
    (hb : ∀ b∈Sig.bufs sig.params vs, ∀ a,b.1.Contains a 1 → out a=out' a)
    (h : Curry.apply (sig.words 64) (sealContiguousPost 64) vs m out r) :
    Curry.apply (sig.words 64) (sealContiguousPost 64) vs m out' r := by
  match vs,hl with
  | [k,rounds,iv,nl,ad,al,src,dst,n,tag],_ =>
    obtain ⟨_,_,_,_,d,t⟩ := agreements hb
    intro sk hk
    change _ = (Spec.Aes.bytesAt out' dst n.toNat,Spec.Aes.bytesAt out' tag 16)
    rw [bytesAt_congr (agree_of d),bytesAt_congr (agree_of t)]
    exact h sk hk

end VG.Proof.AesGcm.SealBuffers
