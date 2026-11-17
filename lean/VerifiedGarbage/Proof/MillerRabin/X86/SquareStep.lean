module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Proof.MillerRabin.Word32
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.DataSquareControl
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.MillerRabin.X86.StageMultiply
import VerifiedGarbage.Proof.MillerRabin.X86.RoundScalarFrame
import VerifiedGarbage.Proof.MillerRabin.X86.RoundArrayFrame
import VerifiedGarbage.Proof.MillerRabin.X86.StageSlots
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
import VerifiedGarbage.Proof.MillerRabin.X86.ModulusKeep
import VerifiedGarbage.Proof.MillerRabin.X86.Data
import VerifiedGarbage.Proof.MillerRabin.X86.Equal
import VerifiedGarbage.Proof.MillerRabin.X86.DataScalar

/-! ### `MillerRabin.X86.StageEqual`, which this module and modules that import it used -/

section

/-! # Equality records a flag while retaining the prepared call invariants -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/DataEqual.lean`, which only this module imported.
section

/-! # A prepared-array comparison records its exact equality bit -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Data.equal {g : Geometry} (v : g.Valid) {A : Nat → Nat} {Js : List Nat}
    {V : Nat → BitVec 32} {Ds : List Nat} {s : State} (D : Data g A Js V Ds s)
    (d a b : Nat) (scratch : scratchWord d) (aKnown : a ∈ Js) (bKnown : b ∈ Js) :
    WP isa (equal d a b) s fun t =>
      Data g A Js (setAt V d (BitVec.ofNat 32 (decide (A a = A b)).toNat)) (d :: Ds) t ∧
      Outside g.W d 4 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have av := D.arrayValues a aKnown
  have bv := D.arrayValues b bKnown
  have bound := scratch_fit scratch
  refine WP.mono (equal_ok v D.context d a b (by have := v.headerFit; omega) av.1 bv.1)
    fun t ⟨Value, O, K⟩ => ?_
  have C := D.context.keepScalar K (by decide) O scratch
  rw [av.2, bv.2] at Value
  have stored : t.mem.readW (off g.W d) 32 = BitVec.ofNat 32 (decide (A a = A b)).toNat := by
    apply BitVec.eq_of_toNat_eq
    change w32 t.mem g.W d = _
    rw [Value]
    cases decide (A a = A b) <;> rfl
  exact ⟨D.afterScalar v C d scratch _ O stored, O, K⟩

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.equal {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s)
    (d a b : Nat) (scratch : scratchWord d) (aKnown : a ∈ Js) (bKnown : b ∈ Js) :
    WP isa (equal d a b) s fun t =>
      Stage g capacity c p A Js (setAt V d (BitVec.ofNat 32 (decide (A a = A b)).toNat)) (d :: Ds) t ∧
      Outside g.W d 4 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.mono (S.data.equal v d a b scratch aKnown bKnown) fun t ⟨D, O, K⟩ => ?_
  refine ⟨⟨D, S.modulus.keepScalar v S.data.context.ws.nowrap scratch O, ?_, S.noScratch⟩, O, K⟩
  exact S.caller.keepOuts K (by decide) (Outs.of_outside O (List.mem_singleton_self _)) (by
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact Nat.le_trans (scratch_fit scratch) v.headerFit)

end VG.Proof.MillerRabin.X86

end

end

/-! # One prepared square, equality check and masked flag update -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/StageSquareControl.lean`, which only this module imported.
section

/-! # A square's public countdown keeps the complete prepared stage usable -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.squareFlag {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s)
    {q r : Nat} (positive : 0 < q) (qBound : q < 2 ^ 31) (rBound : r < 2 ^ 31) (E F : Bool)
    (known : ∀ d ∈ [sSquares, sThreshold, sEq2, sFlag], d ∈ Ds)
    (count : V sSquares = BitVec.ofNat 32 q) (threshold : V sThreshold = BitVec.ofNat 32 r)
    (eqBit : V sEq2 = BitVec.ofNat 32 E.toNat) (flag : V sFlag = BitVec.ofNat 32 F.toNat) :
    WP isa (.block squareFlag) s fun t =>
      Stage g capacity c p A Js (squareSlots V q r E F) ([sFlag, sSquares] ++ Ds) t ∧
      t.zf = some (decide (q = 1)) ∧ WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx] s t := by
  have scratch : ∀ d ∈ [sFlag, sSquares], scratchWord d := by
    intro d mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · unfold scratchWord sFlag; simp
    · unfold scratchWord sSquares; simp
  refine WP.mono (S.data.squareFlag v positive qBound rBound E F known count threshold eqBit flag)
    fun t ⟨D, Z, O, K⟩ => ?_
  exact ⟨S.afterSlots v D [sFlag, sSquares] scratch O K (by decide), Z,
    scalar_roundFrame S.data.context.ws.nowrap scratch O, K⟩

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem squareStep_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c q r : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) (length : g.L = 8 * capacity)
    (odd : c % 2 = 1) (Ylt : A aY < c) (yKnown : aY ∈ Js) (minusKnown : aMinusOne ∈ Js)
    (positive : 0 < q) (qBound : q < 2 ^ 31) (rBound : r < 2 ^ 31) (F : Bool)
    (known : ∀ d ∈ [sSquares, sThreshold, sFlag], d ∈ Ds)
    (count : V sSquares = BitVec.ofNat 32 q) (threshold : V sThreshold = BitVec.ofNat 32 r)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) :
    let Y := Word32.mm c g.w (A aY) (A aY)
    let E := decide (Y = A aMinusOne)
    WP isa (squareStep name code) s fun t =>
      Stage g capacity c p (setAt A aY Y) Js
        (squareSlots (setAt V sEq2 (BitVec.ofNat 32 E.toNat)) q r E F)
        ([sFlag, sSquares] ++ sEq2 :: Ds) t ∧
      t.zf = some (decide (q = 1)) ∧ WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  dsimp only
  change WP isa (.seq (mulY name code aY)
    (.seq (equal sEq2 aY aMinusOne) (.block squareFlag))) s _
  refine WP.seq (WP.mono (S.multiply verified noSp stack v length aY
    (by change 6 < 8 ∧ 6 ≠ 2 ∧ 6 ≠ 3; decide) odd Ylt yKnown yKnown) fun a ⟨Sa, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (Sa.equal v sEq2 aY aMinusOne (by unfold scratchWord sEq2; simp)
    yKnown minusKnown) fun b ⟨Sb, Ob, Kb⟩ => ?_)
  refine WP.mono (Sb.squareFlag v positive qBound rBound
    (decide (Word32.mm c g.w (A aY) (A aY) = A aMinusOne)) F ?_ ?_ ?_ ?_ ?_)
    fun t ⟨St, Z, Ot, Kt⟩ => ?_
  · intro d mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl
    · exact List.mem_cons_of_mem _ (known _ (by simp))
    · exact List.mem_cons_of_mem _ (known _ (by simp))
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (known _ (by simp))
  · exact count
  · exact threshold
  · rfl
  · exact flag
  · refine ⟨St, Z, ?_, ((Ka.mono (by decide)).trans Kb).trans (Kt.mono (by decide))⟩
    have EqFrame : WorkspaceFrame g (roundWrites g) a.mem b.mem :=
      scalar_roundFrame Sa.data.context.ws.nowrap (rs := [sEq2]) (by
        intro d mem
        obtain rfl := List.mem_singleton.mp mem
        unfold scratchWord sEq2; simp) (Outs.of_outside Ob (List.mem_singleton_self _))
    exact ((mont_roundFrame Oa).trans EqFrame).trans Ot

end VG.Proof.MillerRabin.X86
