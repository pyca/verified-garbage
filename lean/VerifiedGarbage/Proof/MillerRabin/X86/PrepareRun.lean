module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.RunView
public import VerifiedGarbage.Proof.MillerRabin.X86.StageLoadWord
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call

import VerifiedGarbage.Proof.MillerRabin.X86.StageCopy
import VerifiedGarbage.Proof.MillerRabin.X86.RoundArrayFrame
import VerifiedGarbage.Proof.MillerRabin.X86.TableMath
import VerifiedGarbage.Proof.MillerRabin.X86.TableInit
import VerifiedGarbage.Proof.MillerRabin.X86.TableStep
import VerifiedGarbage.Proof.MillerRabin.X86.Sequences
import VerifiedGarbage.Proof.MillerRabin.X86.Scalar
import VerifiedGarbage.Proof.MillerRabin.X86.DataScalar
import VerifiedGarbage.Proof.MillerRabin.X86.StageSlots
import VerifiedGarbage.Proof.MillerRabin.X86.RoundScalarFrame
import VerifiedGarbage.Impl.MillerRabin.X86.Layout
import VerifiedGarbage.Proof.MillerRabin.X86.Copy
import VerifiedGarbage.Proof.MillerRabin.X86.StageLiteral
/-! # The table and initial Montgomery one are ready before exponent scanning -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/Table.lean`, which only this module imported.
section

/-! # Fourteen prepared products build the complete sixteen-entry power table -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem table_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A initialArrays V Ds s)
    (length : g.L = 8 * capacity) (odd : c % 2 = 1) (Xlt : A aX < c) :
    WP isa (table name code) s fun t =>
      Stage g capacity c p (tableValues A c g.w 14) (tableArrays 14) V Ds t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold table
  rw [seqs_append_iff]
  refine WP.mono (tableInit_ok v S) fun a ⟨Sa, Oa, Ka⟩ => ?_
  let P : Nat → State → Prop := fun k t =>
    Stage g capacity c p (tableValues A c g.w k) (tableArrays k) V Ds t ∧
      WorkspaceFrame g (roundWrites g) a.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] a t
  have start : P 0 a := ⟨Sa, WorkspaceFrame.refl _ _ _, Keeps.refl _ _⟩
  refine WP.mono (seqs_range_ok 14
    (fun j => .seq (mulY name code aX) (copy (aTable + j + 2) aY)) P ?_ a start)
    fun t ⟨St, Ot, Kt⟩ => ⟨St, Oa.trans Ot, (Ka.mono (by decide)).trans Kt⟩
  intro k index t H
  obtain ⟨St, Ot, Kt⟩ := H
  refine WP.mono (tableStep_ok verified noSp stack v St length odd Xlt index)
    fun u ⟨Su, Ou, Ku⟩ => ?_
  exact ⟨Su, Ot.trans Ou, Kt.trans Ku⟩

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/StageStore.lean`, which only this module imported.
section

/-! # Record a known register value in one permitted scratch word -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.storeRegister {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) (d : Nat) (scratch : scratchWord d) (r : Reg)
    (value : BitVec 32) (regValue : s.gpr r = value) :
    WP isa (.block [.store (slot d) r]) s fun t =>
      Stage g capacity c p A Js (setAt V d value) (d :: Ds) t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧ Keeps [] s t := by
  refine WP.mono (scalarStore_ok v S.data.context d scratch r) fun t ⟨Value, O, K, C⟩ => ?_
  rw [regValue] at Value
  have D := S.data.afterScalar v C d scratch value O Value
  have scratchList : ∀ e ∈ [d], scratchWord e := by
    intro e mem
    obtain rfl := List.mem_singleton.mp mem
    exact scratch
  have outs := Outs.of_outside O (rs := slotWrites [d]) (List.mem_singleton_self _)
  exact ⟨S.afterSlots v D [d] scratchList outs K (by decide),
    scalar_roundFrame S.data.context.ws.nowrap scratchList outs, K⟩

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/InitWindows.lean`, which only this module imported.
section

/-! # Initialize the public exponent length and the secret pass flag -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem initWindows_ok {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A Js V [] s) :
    WP isa (.block initWindows) s fun t =>
      Stage g capacity c p A Js (setAt (setAt V sWords (BitVec.ofNat 32 g.words)) sFlag 0#32) wordFields t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧ Keeps [.eax, .esi] s t := by
  unfold initWindows
  refine WP.block_append (WP.mono (words_ok v S.data.context) fun a ⟨Count, M, K⟩ => ?_)
  have Sa := S.keepMem K (by decide) (by decide) M
  have reg : a.gpr .esi = BitVec.ofNat 32 g.words := by
    apply BitVec.eq_of_toNat_eq
    rw [Count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := v.maxWidth; unfold Geometry.words; omega)]
  change WP isa (.block ([.store (slot sWords) .esi] ++ [.mov .eax (.imm 0), .store (slot sFlag) .eax])) a _
  refine WP.block_append (WP.mono (Sa.storeRegister v sWords (by unfold scratchWord sWords; simp) .esi _ reg)
    fun b ⟨Sb, Ob, Kb⟩ => ?_)
  refine WP.mono (Sb.literal v sFlag (by unfold scratchWord sFlag; simp) 0#32) fun t ⟨St, Ot, Kt⟩ => ?_
  rw [M] at Ob
  exact ⟨St, Ob.trans Ot, ((K.mono (by decide)).trans (Kb.mono (by decide))).trans (Kt.mono (by decide))⟩

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem prepareRun_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A initialArrays V [] s)
    (length : g.L = 8 * capacity) (odd : c % 2 = 1) (Xlt : A aX < c) :
    WP isa (.seq (table name code) (.seq (copy aY aOne) (.block initWindows))) s fun t =>
      Stage g capacity c p (runValues A c g.w) runArrays
        (setAt (setAt V sWords (BitVec.ofNat 32 g.words)) sFlag 0#32) wordFields t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.seq (WP.mono (table_ok verified noSp stack v S length odd Xlt) fun a ⟨Sa, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (Sa.copy v aY aOne (by decide) (by decide) (by decide)
    (by simp [tableArrays, initialArrays])) fun b ⟨Sb, Ob, Kb⟩ => ?_)
  change Stage g capacity c p (runValues A c g.w) (aY :: tableArrays 14) V [] b at Sb
  have Start : Stage g capacity c p (runValues A c g.w) runArrays V [] b :=
    Sb.mono (by
      intro j mem
      refine ⟨?_, rfl⟩
      rcases List.mem_append.mp mem with base | power
      · change j ∈ [6, 9, 10, 27, 0] at base
        simp only [List.mem_cons, List.not_mem_nil, or_false] at base
        rcases base with rfl | rfl | rfl | rfl | rfl <;> decide
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ power)))
      (fun _ mem => ⟨mem, rfl⟩)
  refine WP.mono (initWindows_ok v Start) fun t ⟨St, Ot, Kt⟩ => ?_
  exact ⟨St, (Oa.trans (array_roundFrame Sa.data.context.ws.nowrap
    (by unfold roundArray aY; simp) Ob)).trans Ot,
    (Ka.trans (Kb.mono (by decide))).trans (Kt.mono (by decide))⟩

end VG.Proof.MillerRabin.X86
