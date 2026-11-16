module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Avx2Lit
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyNtt
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YAddSub
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YMontgomery
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YMontgomeryInv
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YDot
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YBits
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YHint
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YNorm
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YUse
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt5
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.Sample.Rej4
public import VerifiedGarbage.Proof.Sha3.X86_64.Round
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Verified
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5CT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4CT

/-! ### `MlDsa.X86_64.Sample.Rej5Verified`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG VG.X86_64

theorem rejNTT4Avx2_verified {fast : Bool} : Verified X86_64.target (Impl.MlDsa.X86_64.Sample.Rej5.rejNTT4Avx2 fast)
    (Proof.MlDsa.rejNTT4Contract X86_64.abi 24) := rej4_verified _ (correct (fast := fast)) ct

theorem rejNTT4Avx2_ret {fast : Bool} {s s' : State} {t : List Leak} (h : (Proof.MlDsa.rejNTT4Contract X86_64.abi 24).pre s)
    (e : Exec isa (Impl.MlDsa.X86_64.Sample.Rej5.rejNTT4Avx2 fast) s t s') :
    (s'.gpr .rax).setWidth 32 = rej4Res s.mem (s.gpr .rdi) := rej4_ret (correct (fast := fast)) h e

end VG.Proof.MlDsa.X86_64.Rej4.Segment

end

end


/-!
# ML-DSA on x86-64: the polynomial arithmetic with AVX2, as an `ArithImpl`

The AVX2 code (`Impl/MlDsa/X86_64/Arith/Avx2.lean`) meets what the callers of
the polynomial arithmetic need of it (`FnOk`), and requires AVX and AVX2.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith

/-- The AVX2 code. -/
def ArithImpl.avx2 : ArithImpl where
  code := .avx2Combined
  ok :=
    { ntt := FnOk.of Arith.Lazy.verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      invNtt := FnOk.of Arith.MontgomeryInv.verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      mul := FnOk.of Arith.montMulY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      mulAdd := FnOk.of Arith.montMulAddY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      add := FnOk.of Arith.addY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      sub := FnOk.of Arith.subY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      highBits := FnOk.of Round.highBitsY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      lowBits := FnOk.of Round.lowBitsY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      normLt := FnOk.of Round.normLtY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      makeHint := FnOk.of Round.makeHintY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      useHint := FnOk.of Round.useHintY_verified (by lit_decide) (by lit_decide) (by lit_decide)
        (by lit_decide)
      rej4 :=
        have h := Proof.MlKem.X86_64.nospMx_of (c := Backend.avx2Combined.rej4) (by lit_decide)
        ⟨Rej4.Segment.rejNTT4Avx2_verified, h.1, h.2, by lit_decide,
          by lit_decide, Code.all_of_spTest (by lit_decide), fun _ _ _ => Rej4.Segment.rejNTT4Avx2_ret⟩
      expandMask4 :=
        have h := Proof.MlKem.X86_64.nospMx_of (c := Backend.avx2Combined.expandMask4) (by lit_decide)
        ⟨Mask4.expandMask4Avx2_verified, h.1, h.2,
          by lit_decide, by lit_decide, Code.all_of_spTest (by lit_decide)⟩
      dotInv := fun c hc => by
        rcases hc with rfl | rfl | rfl
        · exact FnOk.of Arith.YDot.verified4 (by lit_decide) (by lit_decide) (by lit_decide) (by lit_decide)
        · exact FnOk.of Arith.YDot.verified5 (by lit_decide) (by lit_decide) (by lit_decide) (by lit_decide)
        · exact FnOk.of Arith.YDot.verified7 (by lit_decide) (by lit_decide) (by lit_decide) (by lit_decide) }
  features := ["avx", "avx2"]

/-- AVX2 arithmetic with the AVX-512VL four-state permutation in both samplers: its other
functions are the AVX2 code's, which it calls by their names (`asfx`, `_avx2`), so that they
are emitted once, and the callers that call no sampler are not instantiated for it
(`Proof/Variants/MlDsaArith/X86_64.lean`, `samplerFreeVariants`). -/
def ArithImpl.avx512 : ArithImpl where
  code := { Backend.avx2Combined with
    rej4 := Impl.MlDsa.X86_64.Sample.Rej5.rejNTT4Avx2 true
    expandMask4 := Impl.MlDsa.X86_64.Sample.Mask4.expandMask4Avx2 true
    sfx := "_avx512" }
  ok := { ArithImpl.avx2.ok with
    rej4 :=
      have h := Proof.MlKem.X86_64.nospMx_of (c := Impl.MlDsa.X86_64.Sample.Rej5.rejNTT4Avx2 true) (by lit_decide)
      ⟨Rej4.Segment.rejNTT4Avx2_verified, h.1, h.2, by lit_decide,
        by lit_decide, Code.all_of_spTest (by lit_decide), fun _ _ _ => Rej4.Segment.rejNTT4Avx2_ret⟩
    expandMask4 :=
      have h := Proof.MlKem.X86_64.nospMx_of (c := Impl.MlDsa.X86_64.Sample.Mask4.expandMask4Avx2 true) (by lit_decide)
      ⟨Mask4.expandMask4Avx2_verified, h.1, h.2,
        by lit_decide, by lit_decide, Code.all_of_spTest (by lit_decide)⟩ }
  features := ["avx", "avx2", "avx512f", "avx512vl"]

end VG.Proof.MlDsa.X86_64
