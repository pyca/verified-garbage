module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Init
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Complete full-width signed recoding, framed to its 464-byte digit buffer. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr Keeps Outside off)

structure Digits (base : Addr) (wide : Bool) (k : Nat) (s₀ s : State) : Prop where
  scr : Scr s base
  keep : Keeps recClob s₀ s
  mem : Outside base BITS 464 s₀.mem s.mem
  digits : ∀ j<464,s.mem (off base (BITS+j))=Enc wide k j

theorem recodeBits_ok (wide : Bool) {s : State} {base : Addr} (hs : Scr s base)
    {k : Nat} (hk:k<VG.Impl.Ed448.WnafWide.scalarLimit)
    (hb:∀ j<456,s.mem (off base (BITS+j))=BitVec.ofNat 8 (WnafWide.bit k j)) :
    WP isa (recodeBits wide) s (Digits base wide k s) := by
  unfold recodeBits
  refine WP.seq (WP.mono (init_ok wide hs hk hb) fun u hu => ?_)
  refine WP.seq (WP.mono (recodeLoop_ok wide (by decide) hu) fun v hv => ?_)
  refine WP.mono (recodeTail_ok wide hk (by decide) (by decide) hv) fun t ht => ?_
  exact ⟨ht.scr,ht.keep,ht.mem,ht.digits⟩

end VG.Proof.Ed448.AArch64.Sparse
