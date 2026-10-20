module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterState
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterStable

/-! # Consume one complete seed and advance exactly the specification's outer attempt loop -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

theorem parameter_step {H : Hash} (Khash : HashOK H) (F : KeyRandom.CheckCall.CheckFn) {P : SearchContextPlan}
    (digest : H.D = P.geometry.qLen) (final : H.F = P.geometry.qLen)
    (hash : ∀ bs, Khash.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.geometry.qLen) bs)
    (hashSize : ∀ bs, (Spec.Dsa.seedHash (8 * P.geometry.qLen) bs).length = P.geometry.qLen)
    {expected : Option Spec.Dsa.Params} {initial : State} {used : Nat} {s t : State} {W : Nat → BitVec 32}
    (I : ParameterInvariant P expected initial used s) (room : used + P.geometry.qLen ≤ P.seeds.bytes.length)
    (rep : FrameWords s.mem P.geometry.frameBase W)
    (repT : FrameWords t.mem P.geometry.frameBase
      (frameUpdate (frameUpdate W 1 (W 8 + BitVec.ofNat 32 used)) 10 (BitVec.ofNat 32 (used + P.geometry.qLen))))
    (O : Outside P.geometry.frameBase 0 VG.Impl.Dsa.X86.Generation.frameBytes s.mem t.mem)
    (K : Keeps [.eax, .ecx] s t) :
    WP isa (parameterBody H P.geometry.pLen P.geometry.qLen (finishDomain F.name F.code P.geometry.pLen P.geometry.qLen)) t
      fun u => ∃ W', SearchFrame u P.geometry.frameBase ∧ FrameWords u.mem P.geometry.frameBase W' ∧
        (if W' 19 = 3 then ParameterInvariant P expected initial (used + P.geometry.qLen) u else ParameterFinished P expected initial u) := by
  obtain ⟨Wi, witnessUsed, Ri, _, cursor, bound, _, remaining, Oi, rd, wr⟩ := I
  have R := Ri.relabel rep
  let Wt := frameUpdate (frameUpdate W 1 (W 8 + BitVec.ofNat 32 used)) 10 (BitVec.ofNat 32 (used + P.geometry.qLen))
  have Ft := parameter_frame (P := P) O (Nat.le_refl _)
  have Rt : SearchContext P Wt t := R.frame repT (by
    intro i _ hx
    have i1 : i ≠ 1 := by intro h; subst i; exact hx (by decide)
    have i10 : i ≠ 10 := by intro h; subst i; exact hx (by decide)
    simp only [Wt, frameUpdate, ite_eq_right i10, ite_eq_right i1]) Ft K (by decide)
  have qw := P.geometry.qWidth
  have positive : 0 < P.geometry.qLen := by omega
  let T := P.seeds.slice used P.geometry.qLen room positive
  have len : T.bytes.length = P.geometry.qLen := by
    change ((P.seeds.bytes.drop used).take P.geometry.qLen).length = _
    simp only [List.length_take, List.length_drop]; omega
  have source : Wt 1 = T.pointer := by
    change W 8 + BitVec.ofNat 32 used = P.seeds.pointer + BitVec.ofNat 32 used
    rw [R.fixed 8 (by decide) (by decide), P.seedPointer]
  have ct : Wt 16 = BitVec.ofNat 32 witnessUsed :=
    ((rep 16 (by decide)).symm.trans (Ri.representation 16 (by decide))).trans cursor
  have seed := Rt.seeds.slice used P.geometry.qLen room positive
  refine WP.mono (parameterBody_ok Khash F Rt seed len source ct bound digest final hash hashSize)
    fun u ⟨Wu, nextUsed, Ru, seedCursor, nextCursor, nextBound, outcome, Ou, rdu, wru⟩ => ?_
  have whole := (Oi.trans Ft).trans Ou
  have allRd := rdu.trans (K.2.1.trans rd)
  have allWr := wru.trans (K.2.2.trans wr)
  rw [parameterRemaining_step P room] at remaining
  refine ⟨Wu, Ru.arena.frame, Ru.representation, ?_⟩
  rcases outcome with ⟨status, answer⟩ | ⟨status, answer⟩ | ⟨params, status, answer, bytes⟩
  · change seedExpected P ((P.seeds.bytes.drop used).take P.geometry.qLen) witnessUsed = _ at answer
    rw [ite_eq_right (by rw [status]; decide : Wu 19 ≠ 3)]
    have none : expected = none := by rw [answer] at remaining; exact remaining
    exact ⟨Wu, Ru, .inl ⟨.inl status, none⟩, whole, allRd, allWr⟩
  · change seedExpected P ((P.seeds.bytes.drop used).take P.geometry.qLen) witnessUsed = _ at answer
    rw [ite_eq_left status]
    have next : expected = parameterRemaining P (used + P.geometry.qLen) nextUsed := by
      rw [answer] at remaining
      exact remaining
    exact ⟨Wu, nextUsed, Ru, seedCursor, nextCursor, nextBound, room, next, whole, allRd, allWr⟩
  · change seedExpected P ((P.seeds.bytes.drop used).take P.geometry.qLen) witnessUsed = _ at answer
    rw [ite_eq_right (by rw [status]; decide : Wu 19 ≠ 3)]
    have found : expected = some params := by rw [answer] at remaining; exact remaining
    exact ⟨Wu, Ru, .inr ⟨params, status, found, bytes⟩, whole, allRd, allWr⟩
end VG.Proof.Dsa.X86.Generation
