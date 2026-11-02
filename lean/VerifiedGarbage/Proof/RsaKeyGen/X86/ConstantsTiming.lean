module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Constants
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.ConstantsOne
import VerifiedGarbage.Proof.RsaKeyGen.X86.Constants
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingMultiply
import VerifiedGarbage.Proof.MillerRabin.X86.TimingCopy
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Montgomery constants reuse a prepared call with a candidate-independent trace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Constants
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86
open VG.Proof.RsaKeyGen.X86.PreparedR2

def Input (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c, Ready g c capacity p s ∧ c % 2 = 1 ∧ 0 < c ∧
    val32 s.mem g.W (g.array 4) g.words = 2 ^ (64 * g.w) * 2 ^ (64 * g.w) % c

def InputPair (g : Geometry) (capacity : Nat) (p : BitVec 32) (s t : State) : Prop :=
  Pair g [.edi] s t ∧ Input g capacity p s ∧ Input g capacity p t

theorem plainOne_raw (w out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (VG.Impl.Mont.X86.Dynamic.one w out)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (VG.Impl.Mont.X86.Dynamic.one w out) (VG.Impl.Mont.X86.Dynamic.one 1 0)
    (VG.Taint.hintOf taint (roundTaint [.edi]) (Code.erase (VG.Impl.Mont.X86.Dynamic.one 1 0)))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem subtract_raw (w : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (VG.Impl.RsaKeyGen.X86.Constants.subtract w)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (VG.Impl.RsaKeyGen.X86.Constants.subtract w) (VG.Impl.Mont.X86.Dynamic.chainW .sbb 1 0 0 0)
    (.seq (roundTaint [.edi]) (.block [])
      (.seq (roundTaint [.edi, .ebp]) (.block []) (.loop (roundTaint [.edi, .ebp]) (.block []))))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem plainOne_pair {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (InputPair g capacity p) (VG.Impl.Mont.X86.Dynamic.one g.w (g.array 6))
      (fun s t => Pair g [.edi] s t ∧ MulInput g capacity 4 p s ∧ MulInput g capacity 4 p t) := by
  intro s t tr ur u z ⟨H, S, T⟩ E G
  obtain ⟨trace, agree⟩ := plainOne_raw g.w (g.array 6) _ _ _ _ _ _ H.2.2 E G
  have post {a : State} (I : Input g capacity p a) :
      WP isa (VG.Impl.Mont.X86.Dynamic.one g.w (g.array 6)) a (MulInput g capacity 4 p) := by
    obtain ⟨c, A, odd, positive, r2⟩ := I
    refine WP.mono (plainOne_ok v A) fun b ⟨B, _, r2Same, _, _⟩ => ?_
    exact ⟨B.context, ⟨c, B.modulus, odd, by rw [r2Same, r2]; exact Nat.mod_lt _ positive⟩, B.caller⟩
  have U := wp_result (post S) E
  have Z := wp_result (post T) G
  exact ⟨trace, ⟨U.context, Z.context, agree⟩, U, Z⟩

theorem code_raw {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (InputPair g capacity p) (VG.Impl.RsaKeyGen.X86.Constants.code g.w name mont)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold VG.Impl.RsaKeyGen.X86.Constants.code
  rw [Prepared.slot_eq]
  refine RelCT.seq (plainOne_pair v) (RelCT.seq
    (mulY_relCT (p := p) (b := 4) verified noSp stack v length (by unfold Proof.Rsa.Mont.Operand; decide))
    (RelCT.seq (copy_relCT v 9 6 (by decide) (by decide)) ?_))
  exact (subtract_raw g.w).mono (fun _ _ H => H.2.2) (fun _ _ H => H)

theorem code_trace {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (InputPair g capacity p) (VG.Impl.RsaKeyGen.X86.Constants.code g.w name mont) (Pair g [.edi]) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := code_raw (p := p) verified noSp stack v length _ _ _ _ _ _ H E G
  have post {a : State} (I : Input g capacity p a) :
      WP isa (VG.Impl.RsaKeyGen.X86.Constants.code g.w name mont) a (Context g) := by
    obtain ⟨c, A, odd, positive, r2⟩ := I
    exact WP.mono (code_ok verified noSp stack v length A odd positive r2) fun _ R => R.1.context
  exact ⟨trace, wp_result (post H.2.1) E, wp_result (post H.2.2) G, agree⟩

end VG.Proof.RsaKeyGen.X86.Constants
