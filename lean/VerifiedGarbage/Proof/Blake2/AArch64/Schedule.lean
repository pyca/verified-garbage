module

public import VerifiedGarbage.Impl.Blake2.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Interleave

/-!
# Four-way scalar BLAKE2 round scheduling

Each column/diagonal pass ends in exactly the state of four sequential Gs,
including the shared message temporary. The load and its consuming additions
stay adjacent; all other arithmetic operates on disjoint lanes. Prove the
state equality symbolically once per pass shape, for both operand widths.
The compression proof and constant-time analysis still check the actual code.
-/

@[expose] public section

namespace VG.Proof.Blake2.AArch64.Schedule

open VG VG.AArch64 VG.Impl.Blake2.AArch64

theorem sz_bits (z : Size) : sz z.bits = z := by cases z <;> rfl
theorem ws_bits (z : Size) : ws z.bits = z.bytes := by cases z <;> rfl

theorem load {z : Size} {s : State} {t : Reg} (j : Fin 16)
    (h : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (z.bytes * j)) z.bytes) :
    exec (.ldr z t .x1 (z.bytes * j)) s =
      some (s.write z t (s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (z.bytes * j)) z.bits)) := by
  have ho : z.bytes * j.val % z.bytes = 0 ∧ z.bytes * j.val < 4096 * z.bytes :=
    ⟨Nat.mul_mod_right _ _, by cases z <;> simp only [Size.bytes] <;> omega_arith⟩
  cases z
  · exact exec_ldr_w ho h
  · exact exec_ldr_x ho h

theorem rotate {z : Size} {s : State} {d n : Reg} {sh : Nat} (h : sh < z.bits) :
    exec (.ror z d n sh) s = some (s.write z d ((s.read z n).rotateRight sh)) := by
  simp [exec, h]

theorem state_eq {s t : State} (hg : s.gpr = t.gpr) (hs : s.sp = t.sp)
    (hc : s.c = t.c) (hn : s.nf = t.nf) (hz : s.zf = t.zf) (hvf : s.vf = t.vf)
    (hv : s.v = t.v) (hm : s.mem = t.mem) (hr : s.rd = t.rd) (hw : s.wr = t.wr)
    (hu : s.unknowns = t.unknowns) (hsy : s.syms = t.syms) : s = t := by
  cases s; cases t; cases hg; cases hs; cases hc; cases hn; cases hz
  cases hvf; cases hv; cases hm; cases hr; cases hw; cases hu; cases hsy
  rfl

theorem ext_trunc (z : Size) (v : BitVec z.bits) : (v.setWidth 64).setWidth z.bits = v := by
  cases z
  · rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  · simp only [Size.bits, BitVec.setWidth_eq]

theorem run_eq {z : Size} (P : Spec.Blake2.Params z.bits) (r : Nat) (diagonal : Bool) (s : State)
    (h1 : P.R1 < z.bits) (h2 : P.R2 < z.bits) (h3 : P.R3 < z.bits) (h4 : P.R4 < z.bits)
    (hm : ∀ j : Fin 16, InRegions (s.rd ++ s.wr)
      (s.gpr .x1 + BitVec.ofNat 64 (z.bytes * j)) z.bytes) :
    runBlock isa (passCode P r diagonal) s = runBlock isa (referencePass P r diagonal) s := by
  cases diagonal <;> simp only [passCode, referencePass, stage, slots, g,
    List.range_succ, List.range_zero, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
    List.cons_append, List.nil_append, List.append_nil, wreg, T,
    Nat.reduceMod, Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, Bool.false_eq_true,
    ↓reduceIte]
  all_goals simp only [sz_bits, ws_bits, runBlock_cons, runStep_some, runBlock_nil, exec_add,
    exec_logic, rotate h1, rotate h2, rotate h3, rotate h4, load, isa, State.read,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    reduceCtorEq, ite_true, ite_false, hm, ext_trunc]
  all_goals
    apply congrArg some
    apply state_eq <;> try rfl
    funext q
    cases q <;> simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]

theorem referencePass_false {w} (P : Spec.Blake2.Params w) (r : Nat) :
    referencePass P r false =
      g P (wreg 0) (wreg 4) (wreg 8) (wreg 12) (Spec.Blake2.sigmaAt r 0) (Spec.Blake2.sigmaAt r 1) ++
      g P (wreg 1) (wreg 5) (wreg 9) (wreg 13) (Spec.Blake2.sigmaAt r 2) (Spec.Blake2.sigmaAt r 3) ++
      g P (wreg 2) (wreg 6) (wreg 10) (wreg 14) (Spec.Blake2.sigmaAt r 4) (Spec.Blake2.sigmaAt r 5) ++
      g P (wreg 3) (wreg 7) (wreg 11) (wreg 15) (Spec.Blake2.sigmaAt r 6) (Spec.Blake2.sigmaAt r 7) := rfl

theorem referencePass_true {w} (P : Spec.Blake2.Params w) (r : Nat) :
    referencePass P r true =
      g P (wreg 0) (wreg 5) (wreg 10) (wreg 15) (Spec.Blake2.sigmaAt r 8) (Spec.Blake2.sigmaAt r 9) ++
      g P (wreg 1) (wreg 6) (wreg 11) (wreg 12) (Spec.Blake2.sigmaAt r 10) (Spec.Blake2.sigmaAt r 11) ++
      g P (wreg 2) (wreg 7) (wreg 8) (wreg 13) (Spec.Blake2.sigmaAt r 12) (Spec.Blake2.sigmaAt r 13) ++
      g P (wreg 3) (wreg 4) (wreg 9) (wreg 14) (Spec.Blake2.sigmaAt r 14) (Spec.Blake2.sigmaAt r 15) := rfl

theorem wp {z : Size} (P : Spec.Blake2.Params z.bits) (r : Nat) (diagonal : Bool)
    {s : State} {Q : State → Prop}
    (h1 : P.R1 < z.bits) (h2 : P.R2 < z.bits) (h3 : P.R3 < z.bits) (h4 : P.R4 < z.bits)
    (hm : ∀ j : Fin 16, InRegions (s.rd ++ s.wr)
      (s.gpr .x1 + BitVec.ofNat 64 (z.bytes * j)) z.bytes)
    (h : WP isa (.block (referencePass P r diagonal)) s Q) :
    WP isa (.block (passCode P r diagonal)) s Q := by
  obtain ⟨s', hr, hq⟩ := VG.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨s', (run_eq P r diagonal s h1 h2 h3 h4 hm).trans hr, hq⟩

end VG.Proof.Blake2.AArch64.Schedule
