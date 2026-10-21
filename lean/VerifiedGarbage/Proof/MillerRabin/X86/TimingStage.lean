module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingSquares

/-! # Functional round stages supply the guards of timing compositions -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Impl.MillerRabin.X86

theorem Stage.mulInput {g : Geometry} {capacity c b : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) (odd : c % 2 = 1) (known : b ∈ Js) (lt : A b < c) :
    MulInput g capacity b p s := by
  refine ⟨S.data.context, ⟨c, S.modulus, odd, ?_⟩, S.caller⟩
  rw [(S.data.arrayValues b known).2]
  exact lt

theorem Stage.squareInput {g : Geometry} {capacity c q r : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) (odd : c % 2 = 1) (lt : A aY < c)
    (y : aY ∈ Js) (minus : aMinusOne ∈ Js) (rBound : r < 2 ^ 31) (qBound : q < 2 ^ 31)
    (F : Bool) (known : ∀ d ∈ [sSquares, sThreshold, sFlag], d ∈ Ds)
    (count : V sSquares = BitVec.ofNat 32 q) (threshold : V sThreshold = BitVec.ofNat 32 r)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) : SquareInput g capacity p q s := by
  refine ⟨c, A, V, r, F, S.mono ?_ ?_, odd, lt, rBound, qBound, count, threshold, flag⟩
  · intro j mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact ⟨y, rfl⟩
    · exact ⟨minus, rfl⟩
  · exact fun d mem => ⟨known d mem, rfl⟩

end VG.Proof.MillerRabin.X86
