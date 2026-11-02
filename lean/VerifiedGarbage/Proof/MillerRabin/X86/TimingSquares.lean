module

import VerifiedGarbage.Proof.MillerRabin.X86.TimingSquareStep
public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
import VerifiedGarbage.Proof.MillerRabin.X86.SquareStep
import VerifiedGarbage.Proof.MillerRabin.X86.TimingPrivate
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingMultiply

/-! # A public square count controls the loop; the threshold remains secret -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

def SquareInput (g : Geometry) (capacity : Nat) (p : BitVec 32) (q : Nat) (s : State) : Prop :=
  ∃ c A V r, ∃ flag : Bool,
    Stage g capacity c p A [aY, aMinusOne] V [sSquares, sThreshold, sFlag] s ∧
    c % 2 = 1 ∧ A aY < c ∧ r < 2 ^ 31 ∧ q < 2 ^ 31 ∧
    V sSquares = BitVec.ofNat 32 q ∧ V sThreshold = BitVec.ofNat 32 r ∧ V sFlag = BitVec.ofNat 32 flag.toNat

theorem SquareInput.context {g : Geometry} {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : SquareInput g capacity p q s) : Context g s := by
  obtain ⟨_, _, _, _, _, S, _⟩ := I
  exact S.data.context

theorem SquareInput.mulInput {g : Geometry} {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : SquareInput g capacity p q s) : MulInput g capacity aY p s := by
  obtain ⟨c, A, V, r, F, S, odd, lt, _⟩ := I
  refine ⟨S.data.context, ⟨c, S.modulus, odd, ?_⟩, S.caller⟩
  rw [(S.data.arrayValues aY (by decide)).2]
  exact lt

theorem SquareInput.step {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : SquareInput g capacity p q s) (length : g.L = 8 * capacity) (positive : 0 < q) :
    WP isa (squareStep name code) s fun t => SquareInput g capacity p (q - 1) t ∧ t.zf = some (decide (q = 1)) := by
  obtain ⟨c, A, V, r, F, S, odd, lt, rBound, qBound, count, threshold, flag⟩ := I
  refine WP.mono (squareStep_ok verified noSp stack v S length odd lt (by decide) (by decide)
    positive qBound rBound F (by intro d mem; exact mem) count threshold flag) fun t ⟨St, Z, _, _⟩ => ?_
  let Y := Word32.mm c g.w (A aY) (A aY)
  let E := decide (Y = A aMinusOne)
  refine ⟨⟨c, setAt A aY Y, squareSlots (setAt V sEq2 (BitVec.ofNat 32 E.toNat)) q r E F,
    r, F || (decide (r < q) && E), ?_, odd, ?_, rBound, by omega, rfl, ?_, ?_⟩, Z⟩
  · exact St.mono (fun j mem => ⟨mem, rfl⟩) (by
      intro d mem
      refine ⟨?_, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem ⊢
      rcases mem with rfl | rfl | rfl <;> simp)
  · rw [setAt_self]
    exact Word32.mm_lt (by omega : 0 < c)
  · exact threshold
  · change BitVec.ofNat 32 (F || (E && decide (r < q))).toNat = _
    rw [Bool.and_comm]

end VG.Proof.MillerRabin.X86
