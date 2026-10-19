module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.AArch64.Run

/-! # Preserve the hash frame while writing an external candidate buffer -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64

/-- The candidate and wrapped-seed buffers are apart from the hash state
and its caller frame. Separation is stated bytewise, allowing callers to
place them in larger shared allocations. -/
structure HashBufferSeparate (F S op : Addr) (len : Nat) : Prop where
  frame : ∀ i < len, ∀ j < frameBytes, VG.Proof.Bignum.off op i ≠ VG.Proof.Bignum.off F j
  scratch : ∀ i < len, ∀ j < oRsa, VG.Proof.Bignum.off op i ≠ VG.Proof.Bignum.off S j

theorem rep_of_external_write {m m' : Mem} {F S op : Addr} {len : Nat}
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W)
    (hsep : HashBufferSeparate F S op len)
    (hf : ∀ a, (∀ i < len, a ≠ VG.Proof.Bignum.off op i) → m' a = m a) : Rep m' F S V W where
  scr j hj := by
    rw [hf _ (fun i hi => Ne.symm (hsep.scratch i hi j hj))]
    exact R.scr j hj
  fr k hk := by
    have he : VG.Proof.RsaOaep.AArch64.word m' F (8 * k) = VG.Proof.RsaOaep.AArch64.word m F (8 * k) := by
      apply Mem.readW_congr
      intro j hj
      change m' (VG.Proof.Bignum.off (VG.Proof.Bignum.off F (8 * k)) j) = m (VG.Proof.Bignum.off (VG.Proof.Bignum.off F (8 * k)) j)
      rw [VG.Proof.Bignum.off_off]
      exact hf _ (fun i hi => Ne.symm (hsep.frame i hi (8 * k + j) (by
        dsimp only [nW, frameBytes] at hk ⊢
        omega)))
    rw [he]
    exact R.fr k hk

theorem lay_of_rep {s t : State} {F S : Addr} {V V' : Nat → Byte}
    {W W' : Nat → BitVec 64} (L : Lay s F S) (R : Rep s.mem F S V W)
    (Rt : Rep t.mem F S V' W') (h12 : W' 12 = W 12)
    (hsp : t.sp = s.sp) (hwr : t.wr = s.wr) : Lay t F S := by
  refine L.congr hsp hwr ?_
  change VG.Proof.RsaOaep.AArch64.word t.mem F (8 * 12) = VG.Proof.RsaOaep.AArch64.word s.mem F (8 * 12)
  rw [Rt.fr 12 (by decide), R.fr 12 (by decide), h12]

/-- Arithmetic calls preserve the complete hash representation when their
workspace, draw buffer and call stack are disjoint from it. -/
theorem rep_of_disjoint_frame {m m' : Mem} {F S : Addr} {rs : List Region}
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W)
    (hf : Frame rs m m')
    (hF : ∀ r ∈ rs, (⟨F, frameBytes⟩ : Region).Disjoint r)
    (hS : ∀ r ∈ rs, (⟨S, oRsa⟩ : Region).Disjoint r) : Rep m' F S V W where
  scr o ho := by
    rw [hf _ (fun r hr hcontains => hS r hr _
      (Offset.contains_base S (by omega : o + 1 ≤ oRsa) (by unfold oRsa at ho; omega)) hcontains)]
    exact R.scr o ho
  fr k hk := by
    have sub : Region.Sub ⟨VG.Proof.Bignum.off F (8 * k), 8⟩ ⟨F, frameBytes⟩ :=
      Offset.sub_base F (by simp only [nW, frameBytes] at hk ⊢; omega)
    rw [VG.Proof.RsaOaep.AArch64.word, hf.readW (r := ⟨VG.Proof.Bignum.off F (8 * k), 8⟩)
      (Region.contains_self _ _)
      (fun r hr a ha hb => hF r hr a (sub a ha) hb) (by decide)]
    exact R.fr k hk

end VG.Proof.Dsa.AArch64.Generation
