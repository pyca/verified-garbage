module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.WordState
public import VerifiedGarbage.Proof.MillerRabin.X86.StageLoadWord
public import VerifiedGarbage.Proof.MillerRabin.ExponentWords32
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.MillerRabin.X86.WordWindows
import VerifiedGarbage.Proof.MillerRabin.X86.StageCounter

/-! # A public word index loads and consumes exactly eight exponent windows -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

def wordEndSlots (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (x : BitVec 32) (F : Bool) (q : Nat) :
    Nat → BitVec 32 :=
  setAt (setAt V sFlag (BitVec.ofNat 32 (wordState A c w x F 8).2.toNat)) sWords (BitVec.ofNat 32 (q - 1))

theorem wordStep_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Spec.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c q : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A Js V wordFields s) (length : g.L = 8 * capacity)
    (odd : c % 2 = 1) (Ylt : A aY < c) (yKnown : aY ∈ Js)
    (oneKnown : aOne ∈ Js) (minusKnown : aMinusOne ∈ Js) (expKnown : aExponent ∈ Js) (xUnknown : aX ∉ Js)
    (tableKnown : ∀ j < 16, aTable + j ∈ Js) (one : A aTable = A aOne)
    (tableLt : ∀ j < 16, A (aTable + j) < c)
    (positive : 0 < q) (bound : q ≤ g.words) (F : Bool)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) (count : V sWords = BitVec.ofNat 32 q) :
    let x := exponentWord (A aExponent) (q - 1)
    WP isa (wordStep name code) s fun t =>
      Stage g capacity c p (wordValues A c g.w x F 8) Js (wordEndSlots V A c g.w x F q) wordFields t ∧
      t.zf = some (decide (q = 1)) ∧ WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  dsimp only
  change WP isa (.seq (.block loadWord) (.seq (.loop (window name code) .ne) (.block wordEnd))) s _
  have readWord := read_exponentWord (S.data.arrayValues aExponent expKnown).2 (by omega : q - 1 < g.words)
  refine WP.seq (WP.mono (S.loadWord v q positive bound count _ readWord) fun a ⟨Sa, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (wordWindows_ok verified noSp stack v Sa length odd Ylt yKnown oneKnown minusKnown
    xUnknown tableKnown one tableLt _ F rfl flag rfl) fun b ⟨Sb, Ob, Kb⟩ => ?_)
  have qBound : q < 2 ^ 32 := by have := v.maxWidth; unfold Geometry.words at bound; omega
  refine WP.mono (Sb.counterDown v sWords q (by unfold scratchWord sWords; simp) (by decide)
    positive qBound count) fun t ⟨St, Z, Ot, Kt⟩ => ?_
  refine ⟨St.mono (fun _ mem => ⟨mem, rfl⟩) ?_, Z, (Oa.trans Ob).trans Ot,
    ((Ka.mono (by decide)).trans Kb).trans (Kt.mono (by decide))⟩
  intro d mem
  have membership : d ∈ sWords :: windowFields := by
    change d ∈ [184, 232] at mem
    change d ∈ [232, 184, 208, 232, 240]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl <;> decide
  refine ⟨membership, ?_⟩
  change d ∈ [184, 232] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl <;> rfl

end VG.Proof.MillerRabin.X86
