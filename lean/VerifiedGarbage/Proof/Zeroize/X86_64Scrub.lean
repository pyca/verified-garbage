module

public import VerifiedGarbage.Spec.Zeroize.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Zeroize.X86_64Avx
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Spec.Zeroize.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Zeroize.X86_64Avx
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_zeroize` and `vg_zeroize_avx` on x86-64, without secret residue

Each followed by `Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`),
which clears the registers it writes. Their postcondition reads the memory
on return only within the buffer. The functions that call them (through
`Proof.Zeroize.X86_64.ZeroizeImpl`) call their code as the internal
`vg_zeroize_core` and `vg_zeroize_avx_core`, which clear what they leave
themselves.
-/

@[expose] public section

namespace VG.Proof.Zeroize.X86_64

open VG.Spec.Zeroize VG.X86_64 VG.X86_64.Scrub

theorem zeroizeOut : PostOut (zeroizeContract X86_64.abi) (zeroizeSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨p, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (Nat.succ.inj hlen)
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj (Nat.succ.inj hlen))
    simp only [zeroizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hb
    have e64 : ((ArgWord.int X86_64.abi.ptrBits).ofRaw ln).toNat = ln.toNat :=
      congrArg BitVec.toNat (BitVec.setWidth_eq ln)
    show bytesAt m₂ p _ = _
    refine Eq.trans ?_ h
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    exact (hb _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [e64, this]) (by omega_using [e64, this]))).symm

def zeroizeKs : List Nat := keep_for% Spec.Zeroize.zeroizeApi.sig 0 Impl.Zeroize.X86_64.zeroize []

theorem zeroizeOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Zeroize.zeroizeApi.sig 0 []) Impl.Zeroize.X86_64.zeroize
      h).any (RScrub.resOkB · 0 zeroizeKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of zeroizeKs (by taint_decide)

def zeroizeAvxKs : List Nat :=
  keep_for% Spec.Zeroize.zeroizeApi.sig 0 Impl.Zeroize.X86_64.zeroizeAvx []

theorem zeroizeAvxOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Zeroize.zeroizeApi.sig 0 []) Impl.Zeroize.X86_64.zeroizeAvx
      h).any (RScrub.resOkB · 0 zeroizeAvxKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of zeroizeAvxKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_zeroize`. -/
def zeroizeReg : Registration Spec.Zeroize.zeroizeApi X86_64.target :=
  withScrub { code := Impl.Zeroize.X86_64.zeroize, verified := verified } zeroizeOut []
    (pubOk_nil _) (some ⟨zeroizeKs, zeroizeOk⟩)

open VG.X86_64.RScrub in
/-- `vg_zeroize_avx`. -/
def zeroizeAvxReg : Registration Spec.Zeroize.zeroizeApi X86_64.target :=
  withScrub { suffix := "_avx", code := Impl.Zeroize.X86_64.zeroizeAvx, verified := verifiedAvx }
    zeroizeOut [] (pubOk_nil _) (some ⟨zeroizeAvxKs, zeroizeAvxOk⟩)

end VG.Proof.Zeroize.X86_64
