module

import VerifiedGarbage.Proof.Ed448.PPC64LE.ScalarLoop
import VerifiedGarbage.Proof.Ed448.PPC64LE.Pack
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Ed448.PPC64LE.Scalar
public import VerifiedGarbage.Proof.Ed448.PPC64LE.ScalarBit
public import VerifiedGarbage.Proof.X448.PPC64LE.Field
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass

/-!
# `vg_ed448_scalar_reduce` on PPC64LE: correctness

The function saves the nonvolatile registers it uses at `SAVE` of `scratch`
(`saveList`, by `Spill`), reduces the 114 bytes of `wide` into `SR`
(`engine_ok`), writes `SR` to `out` as 57 bytes (`packScalar_ok`), and
restores the registers.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame
open VG.Spec.Ed448 (L decodeLE bytesAt)

/-! ## The saved registers -/

/-- The registers the scalar functions save, and their slots. -/
def saveList : List (Reg × Nat) := (List.range 12).map fun i => (savedRegs.getD i .r14, SAVE + 8 * i)

theorem scalarSave_eq (b : Reg) : scalarSave b = Spill.saveCode b saveList := by
  simp only [scalarSave, Spill.saveCode, saveList, List.map_map]; rfl

theorem scalarRestore_eq : scalarRestore = Spill.restoreCode .r6 saveList := by
  simp only [scalarRestore, Spill.restoreCode, saveList, List.map_map]; rfl

theorem saveList_fits : ∀ p ∈ saveList, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide

theorem saveList_in : ∀ p ∈ saveList, SAVE ≤ p.2 ∧ p.2 + 8 ≤ SAVE + 96 := by decide

theorem saveList_restorable : Spill.Restorable .r6 saveList := by decide

theorem saveList_regs : saveList.map Prod.fst = savedRegs := by decide

theorem SAVE_eq : SAVE = 1064 := rfl
theorem SR_eq : SR = 0 := rfl

theorem rem_SR : Rem SR := ⟨by decide, by decide⟩

/-- A byte of a region disjoint from the working space is in none of its parts. -/
theorem not_in_ws {x b : Addr} {d n : Nat} (hd : d + n ≤ 8192)
    (h : ¬ (⟨b, 8192⟩ : Region).Contains x 1) : ¬ (⟨b + BitVec.ofNat 64 d, n⟩ : Region).Contains x 1 :=
  fun hc => h (Offset.sub_base b hd x hc)

/-- The bytes of a buffer apart from the working space, through a frame in it. -/
theorem bytesAt_keep {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p b : Addr} {n : Nat}
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨b, 8192⟩) (hs : ∀ r ∈ rs, Region.Sub r ⟨b, 8192⟩)
    (hn : n < 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt, List.map_inj_left]
  intro i hi
  have hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) (hs r hr _ hc)

/-! ## The function -/

/-- The precondition, by register: `out` in `r3`, `wide` in `r4`, `scratch` in `r5`. -/
structure ReducePre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, 114⟩]
  wr : s.wr = [⟨s.gpr .r3, 57⟩, ⟨s.gpr .r5, 8192⟩]
  out_wide : (⟨s.gpr .r3, 57⟩ : Region).Disjoint ⟨s.gpr .r4, 114⟩
  out_ws : (⟨s.gpr .r3, 57⟩ : Region).Disjoint ⟨s.gpr .r5, 8192⟩
  wide_ws : (⟨s.gpr .r4, 114⟩ : Region).Disjoint ⟨s.gpr .r5, 8192⟩

section
variable {b : Addr}

/-- The remainder at `SR` to `out` (in `r27`), and the registers restored. -/
theorem finish_ok {s0 s : State} (hc : Ctx b s) {q : Addr} (h27 : s.gpr .r27 = q)
    (hw : (⟨q, 57⟩ : Region) ∈ s.wr) (hrd : s.rd = s0.rd) (hwr : s.wr = s0.wr)
    (hws : (⟨b, 8192⟩ : Region) ∈ s0.wr)
    (hd : (⟨q, 57⟩ : Region).Disjoint ⟨b, 8192⟩)
    (hsv : Spill.Saved b s0.gpr saveList s.mem)
    (hrest : ∀ r ∈ preserved, r ∉ savedRegs → s.gpr r = s0.gpr r) :
    WP isa (.block scalarFinish) s fun t =>
      (∀ r ∈ preserved, t.gpr r = s0.gpr r) ∧ t.sp = s.sp ∧
      bytesAt t.mem q 57 = Spec.Ed448.encodeLE 57 (V s.mem b SR) := by
  have hS := SR_eq
  have hV := SAVE_eq
  unfold scalarFinish
  rw [scalarRestore_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (by decide) (by decide) fun s6 u6 => ?_
  have e14' : s6.gpr .r14 = q := by rw [u6.gpr, h27, BitVec.add_zero]
  have hc6 : Ctx b s6 := hc.of_rest (u6.rest (ws := [.r14]) (by decide)) (by decide)
  refine WP.append (packScalar_ok hc6 e14' (a := SR) (by omega_arith) (by rw [u6.wr]; exact hw)
    (hd.sub_right (Offset.sub_base _ (by omega_arith)))) fun s7 ⟨hr7, hf7, hb7⟩ => ?_
  have hsv7 : Spill.Saved b s0.gpr saveList s7.mem := by
    rw [← u6.mem] at hsv
    refine hsv.frame_in (lo := SAVE) (n := 96) saveList_in hf7 fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact fun x h₁ h₂ => hd x h₂ (Offset.sub_base _ (by omega_arith) x h₁)
  refine Spill.restore_ok (b := .r6) (B := b) (by decide)
    (by rw [hr7.gpr _ (by decide), u6.other _ (by decide), hc.r6])
    saveList_fits saveList_restorable
    (fun p hpl => by
      rw [hr7.rd, hr7.wr, u6.rd, u6.wr, hrd, hwr]
      exact in_base (List.mem_append_right _ hws) (by have := saveList_in p hpl; omega_arith)
        (by have := saveList_in p hpl; omega_arith)) hsv7 fun s8 h8 => WP.block_nil ⟨fun r hr => ?_, ?_, ?_⟩
  · refine h8.gpr_of ?_
    by_cases hm : r ∈ saveList.map Prod.fst
    · exact .inl hm
    · refine .inr ?_
      rw [saveList_regs] at hm
      have h1 : r ∉ ([.r7] : List Reg) := by revert hr hm; cases r <;> decide
      have h2 : r ∉ ([.r14] : List Reg) := by revert hr hm; cases r <;> decide
      rw [hr7.gpr _ h1, u6.other _ (by simpa using h2)]
      exact hrest r hr hm
  · rw [h8.sp, hr7.sp, u6.sp]
  · rw [h8.mem, hb7, u6.mem]

end

theorem reduce_ok {s : State} (hp : ReducePre s) :
    WP isa scalarReduce s fun t =>
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧
      bytesAt t.mem (s.gpr .r3) 57 = Spec.Ed448.scalarReduce (bytesAt s.mem (s.gpr .r4) 114) := by
  have hS := SR_eq
  have hD := SD_eq
  have hV := SAVE_eq
  have hws : (⟨s.gpr .r5, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hout : (⟨s.gpr .r3, 57⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hwide : (⟨s.gpr .r4, 114⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  unfold scalarReduce scalarReduceSetup
  rw [scalarSave_eq]
  refine WP.seq (Spill.save_ok (b := .r5) (by decide) saveList_fits
    (fun p hpl => in_base hws (by have := saveList_in p hpl; omega_arith) (by have := saveList_in p hpl; omega_arith)) ?_)
  -- The state after the saves.
  let s1 : State := { s with mem := Spill.saveMem s.mem (s.gpr .r5) s.gpr saveList }
  have hsv : Spill.Saved (s.gpr .r5) s.gpr saveList s1.mem := Spill.saveMem_saved (by decide) _ _ _
  have hf1 : Frame [⟨s.gpr .r5, 8192⟩] s.mem s1.mem :=
    Spill.saveMem_frame_base (fun p hpl => by have := saveList_in p hpl; omega_arith) (by decide) _ _ _
  refine wp_addi (by decide) (by decide) fun s2 u2 => wp_addi (by decide) (by decide) fun s3 u3 =>
    wp_addi (by decide) (by decide) fun s4 u4 => WP.block_nil ?_
  have hr4 : Rest [.r6, .r14, .r27] s1 s4 :=
    (u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide)))
  have hm4 : s4.mem = s1.mem := by rw [u4.mem, u3.mem, u2.mem]
  have e6 : s4.gpr .r6 = s.gpr .r5 := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, BitVec.add_zero]
  have e27 : s4.gpr .r27 = s.gpr .r3 := by
    rw [u4.other _ (by decide), u3.gpr, u2.other _ (by decide), BitVec.add_zero]
  have e14 : s4.gpr .r14 = s.gpr .r4 := by
    rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), BitVec.add_zero]
  have hc4 : Ctx (s.gpr .r5) s4 := ⟨e6, 8192, by decide, by rw [hr4.wr]; exact hws⟩
  -- The bytes of `wide`, kept by the saves.
  have hwb : ∀ i < 114, ¬ (⟨s.gpr .r5, 8192⟩ : Region).Contains (s.gpr .r4 + BitVec.ofNat 64 i) 1 :=
    fun i hi => hp.wide_ws _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  have hb1 : bytesAt s4.mem (s.gpr .r4) 114 = bytesAt s.mem (s.gpr .r4) 114 := by
    rw [hm4]
    exact bytesAt_keep hf1 hp.wide_ws (fun r hr => by rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (Nat.le_refl _))
      (by decide)
  refine WP.seq (WP.mono (engine_ok rem_SR (N := 114) (by decide) (by decide) hc4 e14
    (fun i hi => by rw [hr4.rd, hr4.wr]; exact in_base (List.mem_append_left _ hwide) (by omega_arith) (by omega_arith))
    (fun i hi r hr => by
      simp only [RD, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact not_in_ws (by omega_arith) (hwb i hi))) fun s5 ⟨hr5, hf5, hv5⟩ => ?_)
  rw [hb1] at hv5
  have hc5 : Ctx (s.gpr .r5) s5 := hc4.of_rest hr5 (by decide)
  have hsv5 : Spill.Saved (s.gpr .r5) s.gpr saveList s5.mem := by
    rw [← hm4] at hsv
    refine hsv.frame_in (lo := SAVE) (n := 96) saveList_in hf5 fun r hr => ?_
    simp only [RD, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  refine WP.mono (finish_ok (s0 := s) hc5 (q := s.gpr .r3) (by rw [hr5.gpr _ (by decide), e27])
    (by rw [hr5.wr, hr4.wr]; exact hout) (by rw [hr5.rd, hr4.rd]) (by rw [hr5.wr, hr4.wr]) hws hp.out_ws hsv5
    fun r hr hm => ?_) fun t ⟨h1, h2, h3⟩ => ⟨h1, by rw [h2, hr5.sp, hr4.sp], by rw [h3, hv5]; rfl⟩
  have h3 : r ∉ ([.r5, .r7, .r8, .r11, .r15, .r16] : List Reg) := by revert hr hm; cases r <;> decide
  have h4 : r ∉ ([.r6, .r14, .r27] : List Reg) := by revert hr hm; cases r <;> decide
  rw [hr5.gpr _ h3, hr4.gpr _ h4]

end VG.Proof.Ed448.PPC64LE
