module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessChecks
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedDataGap
import Mathlib.Tactic.SplitIfs

/-! # Initialize the two counters and the width-selected number of uniform tests -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessChecks
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.WitnessChecks

def ranges : List (Nat × Nat) := [(176, 4), (192, 4), (200, 4)]

theorem checks_bound (w : Nat) : checks w < 2 ^ 32 := by
  unfold checks
  split_ifs <;> decide

theorem codeOf_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Prepare.Data g c capacity p s) {checks : Nat} (checksFit : checks < 2 ^ 32) :
    WP isa (.block (codeOf checks)) s fun t =>
      Prepare.Data g c capacity p t ∧ w32 t.mem g.W 176 = 0 ∧ w32 t.mem g.W 192 = 0 ∧
      w32 t.mem g.W 200 = checks ∧ Outs g.W ranges s.mem t.mem ∧ Keeps [.eax] s t := by
  have head := v.headerFit
  unfold codeOf
  refine wp_movS rfl fun a A _ => ?_
  have Sa := S.ready.scratch.of_keeps A.keeps (by decide)
  refine wp_storeS (Sa.ea (by omega)) (Sa.write (by omega)) fun b B => ?_
  have Kb := A.keeps.widen (B.keeps [])
  have Sb := S.ready.scratch.of_keeps Kb (by decide)
  refine wp_storeS (Sb.ea (by omega)) (Sb.write (by omega)) fun d D => wp_movS rfl fun e E _ => ?_
  have Ke := ((Kb.widen (D.keeps [])).trans E.keeps)
  have Se := S.ready.scratch.of_keeps Ke (by decide)
  refine wp_storeS (Se.ea (by omega)) (Se.write (by omega)) fun t T => WP.block_nil ?_
  have Ob : Outside g.W 176 4 s.mem b.mem := by
    rw [B.mem, A.mem]
    exact writeW32_outside _ _ _ (by decide)
  have Od : Outside g.W 192 4 b.mem d.mem := by
    rw [D.mem]
    exact writeW32_outside _ _ _ (by decide)
  have Ot : Outside g.W 200 4 d.mem t.mem := by
    rw [T.mem, E.mem]
    exact writeW32_outside _ _ _ (by decide)
  have gap : Outside g.W 128 96 s.mem t.mem :=
    ((Ob.mono (by decide) (by decide)).trans (Od.mono (by decide) (by decide))).trans (Ot.mono (by decide) (by decide))
  have K := Ke.widen (T.keeps [])
  refine ⟨S.keepHeader v (by decide) (by decide) gap K (by decide) (by decide), ?_, ?_, ?_, ?_, K⟩
  · rw [Ot.w32 (by decide) (by decide), Od.w32 (by decide) (by decide), B.mem, w32_write_self, A.gpr]
    rfl
  · rw [Ot.w32 (by decide) (by decide), D.mem, w32_write_self, B.gpr, A.gpr]
    rfl
  · rw [T.mem, w32_write_self, E.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt checksFit]
  · exact ((Outs.of_outside Ob (by simp [ranges])).trans
      (Outs.of_outside Od (by simp [ranges]))).trans (Outs.of_outside Ot (by simp [ranges]))

theorem code_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Prepare.Data g c capacity p s) :
    WP isa (.block (code g.w)) s fun t =>
      Prepare.Data g c capacity p t ∧ w32 t.mem g.W 176 = 0 ∧ w32 t.mem g.W 192 = 0 ∧
      w32 t.mem g.W 200 = checks g.w ∧ Outs g.W ranges s.mem t.mem ∧ Keeps [.eax] s t :=
  codeOf_ok v S (checks_bound g.w)

end VG.Proof.RsaKeyGen.X86.WitnessChecks
