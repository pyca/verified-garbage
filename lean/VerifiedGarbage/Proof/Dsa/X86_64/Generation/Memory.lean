module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.Framework.Omega

/-! # Preserve the hash frame while writing an external candidate buffer -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64

/-- The candidate and wrapped-seed buffers are apart from the hash state
and its caller frame. Separation is stated bytewise, allowing callers to
place them in larger shared allocations. -/
structure HashBufferSeparate (F S op : Addr) (len : Nat) : Prop where
  frame : ∀ i < len, ∀ j < frameBytes, off op i ≠ off F j
  scratch : ∀ i < len, ∀ j < oRsa, off op i ≠ off S j

theorem rep_of_external_write {m m' : Mem} {F S op : Addr} {len : Nat}
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W)
    (hsep : HashBufferSeparate F S op len)
    (hf : ∀ a, (∀ i < len, a ≠ off op i) → m' a = m a) : Rep m' F S V W where
  scr j hj := by
    rw [hf _ (fun i hi => Ne.symm (hsep.scratch i hi j hj))]
    exact R.scr j hj
  fr k hk := by
    have he : word m' F (8 * k) = word m F (8 * k) := by
      apply Mem.readW_congr
      intro j hj
      change m' (off (off F (8 * k)) j) = m (off (off F (8 * k)) j)
      rw [off_off]
      exact hf _ (fun i hi => Ne.symm (hsep.frame i hi (8 * k + j) (by
        dsimp only [nW, frameBytes] at hk ⊢
        omega)))
    rw [he]
    exact R.fr k hk

theorem lay_of_rep {s t : State} {F S : Addr} {V V' : Nat → Byte}
    {W W' : Nat → BitVec 64} (L : Lay s F S) (R : Rep s.mem F S V W)
    (Rt : Rep t.mem F S V' W') (h14 : W' 14 = W 14)
    (hsp : t.gpr .rsp = s.gpr .rsp) (hwr : t.wr = s.wr) : Lay t F S := by
  refine L.congr hsp hwr ?_
  change word t.mem F (8 * 14) = word s.mem F (8 * 14)
  rw [Rt.fr 14 (by decide), R.fr 14 (by decide), h14]

end VG.Proof.Dsa.X86_64.Generation
