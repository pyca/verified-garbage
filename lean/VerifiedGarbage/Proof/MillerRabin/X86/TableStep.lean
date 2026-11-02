module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.TableMath
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.MillerRabin.X86.StageCopy
import VerifiedGarbage.Proof.MillerRabin.X86.StageMultiply
import VerifiedGarbage.Proof.MillerRabin.X86.RoundArrayFrame

/-! # Each table product writes its completed power once -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem tableStep_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c k : Nat} {p : BitVec 32}
    {A : Nat → Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p (tableValues A c g.w k) (tableArrays k) V Ds s)
    (length : g.L = 8 * capacity) (odd : c % 2 = 1) (Xlt : A aX < c) (index : k < 14) :
    WP isa (.seq (mulY name code aX) (copy (aTable + k + 2) aY)) s fun t =>
      Stage g capacity c p (tableValues A c g.w (k + 1)) (tableArrays (k + 1)) V Ds t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.seq (WP.mono (S.multiply verified noSp stack v length aX
    (by change 5 < 8 ∧ 5 ≠ 2 ∧ 5 ≠ 3; decide) odd (by rw [tableValues_x]; exact Xlt)
    (by simp [tableArrays, initialArrays]) (by exact List.mem_cons_self ..))
    fun a ⟨Sa, Oa, Ka⟩ => ?_)
  refine WP.mono (Sa.copy v (aTable + k + 2) aY (by unfold aTable; omega)
    (by unfold aTable; omega) (by unfold aTable; omega) (by exact List.mem_cons_self ..))
    fun t ⟨St, Ot, Kt⟩ => ?_
  have values : setAt (setAt (tableValues A c g.w k) aY
      (Word32.mm c g.w (tableValues A c g.w k aY) (tableValues A c g.w k aX)))
      (aTable + k + 2) ((setAt (tableValues A c g.w k) aY
        (Word32.mm c g.w (tableValues A c g.w k aY) (tableValues A c g.w k aX))) aY) =
      tableValues A c g.w (k + 1) := by
    rw [setAt_self]
    exact tableValues_next A c g.w k
  rw [values] at St
  refine ⟨St.mono ?_ (fun _ mem => ⟨mem, rfl⟩),
    (mont_roundFrame Oa).trans (array_roundFrame Sa.data.context.ws.nowrap
      (by unfold roundArray aTable; omega) Ot), (Ka.mono (by decide)).trans (Kt.mono (by decide))⟩
  intro j known
  exact ⟨List.mem_cons.mpr ((tableArrays_next k j).mp known), rfl⟩

end VG.Proof.MillerRabin.X86
