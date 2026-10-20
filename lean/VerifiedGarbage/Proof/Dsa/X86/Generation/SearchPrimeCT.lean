module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeArguments
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.X86.Generation.CheckPrimeCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryPrimeInputs
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryStack
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryTrial

/-! # Public search buffers instantiate the complete trial and Miller–Rabin timing proof -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

def SearchPrimeAt (P : SearchContextPlan) (len m used offset : Nat) (s : State) : Prop :=
  ∃ W, SearchContext P W s ∧ W 22 = P.geometry.pointer offset ∧ W 16 = BitVec.ofNat 32 used ∧
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off P.geometry.base offset) len) = m

theorem searchPrime_ct (P : SearchContextPlan) (len m used offset : Nat)
    (lo : 4 ≤ len) (hi : len ≤ 384) (words : len % 4 = 0)
    (bits : Spec.RsaKeyGen.bitLength m = 8 * len) (odd : m % 2 = 1)
    (room : offset + len ≤ usedBytes P.geometry.pLen) (before : offset + len ≤ arithmetic)
    (usedBound : used ≤ P.witnesses.bytes.length) :
    RelCT isa (Two fun (_ : Unit) => SearchPrimeAt P len m used offset) (checkPrime len) (fun _ _ => True) := by
  let C := P.geometry.prime P.witnesses len m lo hi words bits odd
  let F : PublicFrame := ⟨P.geometry.frameBase, frameUpdate P.saved 22 (P.geometry.pointer offset)⟩
  let Q : CheckPrimePublic C := ⟨⟨F, ⟨P.witnesses.bytes, used, usedBound⟩⟩,
    (P.geometry.frame - 16).setWidth 64, P.geometry.trial_frame_apart, P.witnesses.below (by decide)⟩
  have large : 8161 < m := by
    have bounds := (VG.Proof.Dsa.bitLength_iff_bounds (by omega : 0 < 8 * len)).mp bits
    have power := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 13 ≤ 8 * len - 1)
    have eight : (2 : Nat) ^ 13 = 8192 := by decide
    rw [eight] at power
    omega
  refine two_map (fun (_ : Unit) => Q) ?_ (checkPrime_ct C large)
  rintro _ s ⟨W, R, candidate, usedValue, value⟩
  have parent : W 5 = P.geometry.parent := (R.fixed 5 (by decide) (by decide)).trans P.parent
  have tape : W 13 = P.witnesses.pointer := (R.fixed 13 (by decide) (by decide)).trans P.witnessPointer
  have tapeLen : W 15 = BitVec.ofNat 32 P.witnesses.bytes.length :=
    (R.fixed 15 (by decide) (by decide)).trans P.witnessLength
  have inputs := generationPrimeInputs R.arena R.representation parent candidate lo hi words bits odd room before value
    tape tapeLen usedValue usedBound (by intro i hi; exact R.witnesses.read i 1 (by omega))
  have trial := generationTrialInputs R.arena (by omega : 2 ≤ len) (by omega : len % 2 = 0)
    (by omega : len < 2 ^ 32) (entries := if len ≤ 128 then 512 else 1024)
    (by split <;> decide) (by split <;> decide) room R.table
  have bridge : PrimeFromAt C Q.frame s := ⟨W, inputs, R.fixed 5 (by decide) (by decide), candidate, R.witnesses.value⟩
  refine ⟨bridge, bridge.frame, ?_, ?_, ?_⟩
  · rw [R.arena.frameReg]; have := P.geometry.stackSize; omega
  · change TrialInputs _ _ (P.geometry.pointer offset) (P.saved 5) len _
    rw [P.parent]
    exact trial
  · change trialValue s (P.geometry.pointer offset) len = m
    unfold trialValue
    rw [P.geometry.pointer_addr (by omega)]
    exact value
end VG.Proof.Dsa.X86.Generation
