module
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Hash
public import VerifiedGarbage.Proof.RsaOaep.AArch64.CtBase
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Label

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT
import VerifiedGarbage.Impl.Bignum.AArch64
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashFrame
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.WordFrame
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Spec.RsaOaep
meta import VerifiedGarbage.Impl.Bignum.AArch64
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashFrame
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Generation.Memory
meta import VerifiedGarbage.Proof.Dsa.Generation.WordFrame
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mgf1.Bytes
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
meta import VerifiedGarbage.Spec.Pbkdf2.Generic
meta import VerifiedGarbage.Spec.RsaOaep

/-! # Seed hashing's trace depends only on its public location and width -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

theorem seedHash_ct {G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash}
    (h1 : Calls.StreamOK G1.stream) (h256 : Calls.StreamOK G256.stream)
    {F S rp : Addr} {len : Nat} (hlen : len < 2 ^ 64) :
    RelCT isa (LR F S (fun W s => LabAt s F S W rp len))
      (Impl.Dsa.AArch64.Generation.seedHash G1 G256) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.seedHash
  refine (lr_wp (X' := fun W s => LabAt s F S W rp len ∧ s.gpr .x0 = BitVec.ofNat 64 len - 20)
    (lr_taint [] (by taint_decide) nopin) ?_).seq ?_
  · intro s V W L R A
    exact WP.mono (hashTest_ok L R A.hll) fun t ⟨hx, hm, hk⟩ =>
      ⟨V, W, L.congr hk.sp hk.wr (by rw [hm]), hm ▸ R,
        A.congr hk.rd hk.wr rfl rfl, hx⟩
  · refine RelCT.ite ?_ ?_ ?_
    · intro a b h
      obtain ⟨⟨_, _, _, _, _, ha⟩, ⟨_, _, _, _, _, hb⟩⟩ := h
      simp only [eval, State.read, ha, hb]
    · apply (hashLabel_tr h1 hlen (Or.inl rfl) (X := fun W s => LabAt s F S W rp len)
        (fun _ _ h => h)).mono
      · intro a b h
        obtain ⟨⟨Va, Wa, La, Ra, Aa, _⟩, ⟨Vb, Wb, Lb, Rb, Ab, _⟩⟩ := h.1
        exact ⟨⟨Va, Wa, La, Ra, Aa⟩, ⟨Vb, Wb, Lb, Rb, Ab⟩⟩
      · intro _ _ _
        trivial
    · apply (hashLabel_tr h256 hlen (Or.inl rfl) (X := fun W s => LabAt s F S W rp len)
        (fun _ _ h => h)).mono
      · intro a b h
        obtain ⟨⟨Va, Wa, La, Ra, Aa, _⟩, ⟨Vb, Wb, Lb, Rb, Ab, _⟩⟩ := h.1
        exact ⟨⟨Va, Wa, La, Ra, Aa⟩, ⟨Vb, Wb, Lb, Rb, Ab⟩⟩
      · intro _ _ _
        trivial

end VG.Proof.Dsa.AArch64.Generation
