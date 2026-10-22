module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Prepare
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareTimingHeader
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareTimingR2
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.Prepare
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Complete reusable candidate preparation has a candidate-independent trace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Prepare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

theorem code_rawAt {mont : Prog isa} {name : String}
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 16)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (bound : g.w ≤ 64) {e : Nat} (positive : 1 ≤ e) (eLt : e < 64 * g.w) :
    RelCT isa (fun s t => InitialPair g capacity p s t e) (VG.Impl.RsaKeyGen.X86.Prepare.codeAt e g.w name mont)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold VG.Impl.RsaKeyGen.X86.Prepare.codeAt
  rw [Prepared.slot_eq, Prepared.slot_eq, Prepared.slot_eq]
  refine RelCT.seq (header_pair v length) (RelCT.seq (r2_pairAt verified noSp stack v length bound positive eLt)
    (RelCT.seq (Constants.code_trace verified noSp stack v length) ?_))
  exact (Exponent.code_trace g.w (g.array 5) (g.array 0) (g.array 27)).mono
    (fun _ _ H => H.2.2) (fun _ _ H => H)

theorem code_raw {mont : Prog isa} {name : String}
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 16)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (bound : g.w ≤ 64) :
    RelCT isa (InitialPair g capacity p) (VG.Impl.RsaKeyGen.X86.Prepare.code g.w name mont)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  code_rawAt verified noSp stack v length bound (e := 64 * g.w - 1)
    (by have := v.minWidth; omega) (by have := v.minWidth; omega)

theorem code_traceAt {mont : Prog isa} {name : String}
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 16)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (bound : g.w ≤ 64) {e : Nat} (positive : 1 ≤ e) (eLt : e < 64 * g.w) :
    RelCT isa (fun s t => InitialPair g capacity p s t e) (VG.Impl.RsaKeyGen.X86.Prepare.codeAt e g.w name mont)
      (Pair g [.edi]) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := code_rawAt (p := p) verified noSp stack v length bound positive eLt _ _ _ _ _ _ H E G
  have post {a : State} (I : Initial g capacity p a e) :
      WP isa (VG.Impl.RsaKeyGen.X86.Prepare.codeAt e g.w name mont) a (Context g) := by
    obtain ⟨c, I⟩ := I
    exact WP.mono (code_okAt verified noSp stack v bound length I positive eLt) fun _ R => R.1.ready.context
  exact ⟨trace, wp_result (post H.2.1) E, wp_result (post H.2.2) G, agree⟩

theorem code_trace {mont : Prog isa} {name : String}
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 16)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (bound : g.w ≤ 64) :
    RelCT isa (InitialPair g capacity p) (VG.Impl.RsaKeyGen.X86.Prepare.code g.w name mont) (Pair g [.edi]) :=
  code_traceAt verified noSp stack v length bound (e := 64 * g.w - 1)
    (by have := v.minWidth; omega) (by have := v.minWidth; omega)

end VG.Proof.RsaKeyGen.X86.Prepare
