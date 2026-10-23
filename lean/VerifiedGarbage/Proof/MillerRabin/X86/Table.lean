module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.TableMath
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.MillerRabin.X86.TableInit
import VerifiedGarbage.Proof.MillerRabin.X86.TableStep
import VerifiedGarbage.Proof.MillerRabin.X86.Sequences

/-! # Fourteen prepared products build the complete sixteen-entry power table -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem table_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Spec.Rsa.Mont.mulContract abi 56))
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
