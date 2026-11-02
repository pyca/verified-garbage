module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.WordState
public import VerifiedGarbage.Proof.MillerRabin.X86.StageLoadWord
public import VerifiedGarbage.Proof.MillerRabin.ExponentWords32
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call

import VerifiedGarbage.Proof.MillerRabin.X86.Window
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.MillerRabin.X86.Counter
import VerifiedGarbage.Proof.MillerRabin.X86.DataScalar
import VerifiedGarbage.Proof.MillerRabin.X86.StageSlots
import VerifiedGarbage.Proof.MillerRabin.X86.RoundScalarFrame
import VerifiedGarbage.Impl.MillerRabin.X86.Layout
/-! # A public word index loads and consumes exactly eight exponent windows -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/WordWindows.lean`, which only this module imported.
section

/-! # Eight fixed windows consume a complete native exponent word -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86.PublicRt (countLoop)

theorem wordWindows_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A Js V windowFields s) (length : g.L = 8 * capacity)
    (odd : c % 2 = 1) (Ylt : A aY < c) (yKnown : aY ∈ Js)
    (oneKnown : aOne ∈ Js) (minusKnown : aMinusOne ∈ Js) (xUnknown : aX ∉ Js)
    (tableKnown : ∀ j < 16, aTable + j ∈ Js) (one : A aTable = A aOne)
    (tableLt : ∀ j < 16, A (aTable + j) < c)
    (x : BitVec 32) (F : Bool) (value : V sValue = x)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) (count : V sWindows = 8#32) :
    WP isa (.loop (window name code) .ne) s fun t =>
      Stage g capacity c p (wordValues A c g.w x F 8) Js
        (wordCounters V A c g.w x F 8) windowFields t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  let I : Nat → State → Prop := fun i t =>
    Stage g capacity c p (wordValues A c g.w x F i) Js
      (wordCounters V A c g.w x F i) windowFields t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t
  have start : I 0 s := by
    refine ⟨?_, WorkspaceFrame.refl _ _ _, Keeps.refl _ _⟩
    rw [wordValues_initial, wordCounters_initial V A c g.w x F value count flag]
    exact S
  apply countLoop (by decide : 0 < 8) I ?_ start
  intro i t index H
  obtain ⟨St, Ot, Kt⟩ := H
  have yBound : wordValues A c g.w x F i aY < c := by
    rw [wordValues, setAt_self]
    exact wordState_lt A (by omega : 0 < c) g.w x F Ylt i
  have sameOne : wordValues A c g.w x F i aTable = wordValues A c g.w x F i aOne := by
    unfold wordValues
    rw [setAt_other _ _ (by decide : aTable ≠ aY), setAt_other _ _ (by decide : aOne ≠ aY)]
    exact one
  have powersLt : ∀ j < 16, wordValues A c g.w x F i (aTable + j) < c := by
    intro j bound
    rw [wordValues, setAt_other _ _ (by unfold aTable aY; omega)]
    exact tableLt j bound
  refine WP.mono (window_ok verified noSp stack v St length odd yBound yKnown oneKnown minusKnown
    xUnknown tableKnown sameOne powersLt (by omega : 0 < 8 - i) (by omega : 8 - i < 2 ^ 32)
    (wordState A c g.w x F i).2 rfl rfl) fun u ⟨Su, Z, Ou, Ku⟩ => ?_
  have Snext : Stage g capacity c p (wordValues A c g.w x F (i + 1)) Js
      (wordCounters V A c g.w x F (i + 1)) windowFields u := Su.mono
    (fun j mem => ⟨mem, congrFun (wordValues_next V A c g.w x F i) j⟩)
    (fun d mem => ⟨mem, wordCounters_next V A c g.w x F i mem⟩)
  refine ⟨⟨Snext, Ot.trans Ou, Kt.trans Ku⟩, ?_⟩
  rw [Z]
  congr 1
  exact decide_eq_decide.mpr (by omega)

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/StageCounter.lean`, which only this module imported.
section

/-! # A public countdown is a prepared-stage transition -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.counterDown {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) (d q : Nat) (scratch : scratchWord d) (known : d ∈ Ds)
    (positive : 0 < q) (bound : q < 2 ^ 32) (count : V d = BitVec.ofNat 32 q) :
    WP isa (.block [.mov .eax (.mem (slot d)), .alu .sub .eax (.imm 1), .store (slot d) .eax]) s fun t =>
      Stage g capacity c p A Js (setAt V d (BitVec.ofNat 32 (q - 1))) (d :: Ds) t ∧
      t.zf = some (decide (q = 1)) ∧ WorkspaceFrame g (roundWrites g) s.mem t.mem ∧ Keeps [.eax] s t := by
  have read := (S.data.slotValues d known).2.trans count
  refine WP.mono (counterDown_ok v S.data.context d q scratch positive bound read)
    fun t ⟨Count, Z, O, K, C⟩ => ?_
  have stored : t.mem.readW (off g.W d) 32 = BitVec.ofNat 32 (q - 1) := by
    apply BitVec.eq_of_toNat_eq
    change w32 t.mem g.W d = _
    rw [Count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have D := S.data.afterScalar v C d scratch _ O stored
  have scratchList : ∀ e ∈ [d], scratchWord e := by
    intro e mem
    obtain rfl := List.mem_singleton.mp mem
    exact scratch
  have outs := Outs.of_outside O (rs := slotWrites [d]) (List.mem_singleton_self _)
  exact ⟨S.afterSlots v D [d] scratchList outs K (by decide), Z,
    scalar_roundFrame S.data.context.ws.nowrap scratchList outs, K⟩

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

def wordEndSlots (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (x : BitVec 32) (F : Bool) (q : Nat) :
    Nat → BitVec 32 :=
  setAt (setAt V sFlag (BitVec.ofNat 32 (wordState A c w x F 8).2.toNat)) sWords (BitVec.ofNat 32 (q - 1))

theorem wordStep_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
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
