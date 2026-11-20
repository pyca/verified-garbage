module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
public import VerifiedGarbage.Impl.Zeroize.X86_64.Fn
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
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

/-! ## The functions as emitted -/

theorem zeroize_codeSp : (Impl.Zeroize.X86_64.zeroize).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Zeroize.zeroizeApi`'s function as emitted (`Impl.Zeroize.X86_64.Fn.zeroize`) meets its contract in
constant time and returns without secret residue. -/
theorem zeroize_scrubbed :
    VerifiedScrubbed target Impl.Zeroize.X86_64.Fn.zeroize (Spec.Zeroize.zeroizeApi.contract X86_64.abi 0) 0 :=
  verifiedScrubbedSel (api := Spec.Zeroize.zeroizeApi)
    { code := Impl.Zeroize.X86_64.zeroize
      verified := verified
      spSafe := zeroize_codeSp }
    .sse [] zeroizeOut (RScrub.pubOk_nil _) (by taint_decide)

theorem zeroize_spSafe : Impl.Zeroize.X86_64.Fn.zeroize.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe zeroize_codeSp

theorem zeroizeAvx_codeSp : (Impl.Zeroize.X86_64.zeroizeAvx).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Zeroize.zeroizeApi`'s function as emitted (`Impl.Zeroize.X86_64.Fn.zeroizeAvx`) meets its contract in
constant time and returns without secret residue. -/
theorem zeroizeAvx_scrubbed :
    VerifiedScrubbed target Impl.Zeroize.X86_64.Fn.zeroizeAvx (Spec.Zeroize.zeroizeApi.contract X86_64.abi 0) 0 :=
  verifiedScrubbedSel (api := Spec.Zeroize.zeroizeApi)
    { code := Impl.Zeroize.X86_64.zeroizeAvx
      verified := verifiedAvx
      suffix := "_avx"
      spSafe := zeroizeAvx_codeSp }
    .avx [] zeroizeOut (RScrub.pubOk_nil _) (by taint_decide)

theorem zeroizeAvx_spSafe : Impl.Zeroize.X86_64.Fn.zeroizeAvx.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe zeroizeAvx_codeSp
end VG.Proof.Zeroize.X86_64
