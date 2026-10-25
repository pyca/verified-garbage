module

import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarLoop
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Packed
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Ed25519.PPC64LE.SpecConv
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBit
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Scalar
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field
public import VerifiedGarbage.Spec.Ed25519

/-!
# `vg_ed25519_scalar_reduce` on PPC64LE: correctness

The function saves the nonvolatile registers it uses at `SAVE` of `scratch`
(`saveList`, by `Spill`), reduces the 64 bytes of `wide` into `SR`
(`engine_ok`), copies `SR`'s words to `out`, and restores the registers.
`SR`'s words are the scalar's 32 bytes, little-endian, so `out` holds
`scalarReduce wide` (`out_bytes`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (L decodeLE bytesAt)

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

theorem SAVE_eq : SAVE = 1024 := rfl

/-- The save slots, within the working space at `b`. -/
abbrev SV (b : Addr) : Region := ⟨b + BitVec.ofNat 64 SAVE, 96⟩

/-! ## The bytes of an element -/

/-- The 32 bytes at `q` whose words are an element's. -/
theorem bytes_of_words {m m₀ : Mem} {q b : Addr} {a : Nat} (h : ∀ j < 8, wd m q (4 * j) = limb m₀ b a j) :
    decodeLE (bytesAt m q 32) = V m₀ b a := by
  have e : decodeLE (bytesAt m q 32) = V m q 0 := by
    rw [Proof.Ed25519.decodeLE_eq]
    show Proof.X25519.leNum (Spec.X25519.bytesAt m q 32) = _
    rw [Proof.X25519.leNum_bytesAt_read, ← read_V, BitVec.add_zero]
  rw [e, V, V]
  exact val32_congr fun j hj => by rw [limb, Nat.zero_add]; exact h j hj

/-- The output, as `scalarReduce` encodes the remainder. -/
theorem out_bytes {m m₀ : Mem} {q b : Addr} {a : Nat} (h : ∀ j < 8, wd m q (4 * j) = limb m₀ b a j) {x : Nat}
    (hv : V m₀ b a = x) : bytesAt m q 32 = Spec.Ed25519.encodeLE 32 x := by
  rw [Proof.Ed25519.bytesAt_encodeLE, bytes_of_words h, hv]

/-! ## The function -/

/-- The precondition, by register: `out` in `r3`, `wide` in `r4`, `scratch` in `r5`. -/
structure ReducePre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, 64⟩]
  wr : s.wr = [⟨s.gpr .r3, 32⟩, ⟨s.gpr .r5, 8192⟩]
  out_wide : (⟨s.gpr .r3, 32⟩ : Region).Disjoint ⟨s.gpr .r4, 64⟩
  out_ws : (⟨s.gpr .r3, 32⟩ : Region).Disjoint ⟨s.gpr .r5, 8192⟩
  wide_ws : (⟨s.gpr .r4, 64⟩ : Region).Disjoint ⟨s.gpr .r5, 8192⟩

/-- A byte of a region disjoint from the working space is in none of its parts. -/
theorem not_in_ws {x b : Addr} {d n : Nat} (hd : d + n ≤ 8192)
    (h : ¬ (⟨b, 8192⟩ : Region).Contains x 1) : ¬ (⟨b + BitVec.ofNat 64 d, n⟩ : Region).Contains x 1 :=
  fun hc => h (Offset.sub_base b hd x hc)

theorem reduce_ok {s : State} (hp : ReducePre s) :
    WP isa scalarReduce s fun t =>
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧
      bytesAt t.mem (s.gpr .r3) 32 = Spec.Ed25519.scalarReduce (bytesAt s.mem (s.gpr .r4) 64) := by
  have hS := SR_eq
  have hV := SAVE_eq
  have hws : (⟨s.gpr .r5, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hout : (⟨s.gpr .r3, 32⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hwide : (⟨s.gpr .r4, 64⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
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
  have hwb : ∀ i < 64, ¬ (⟨s.gpr .r5, 8192⟩ : Region).Contains (s.gpr .r4 + BitVec.ofNat 64 i) 1 :=
    fun i hi => hp.wide_ws _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  have hb1 : bytesAt s4.mem (s.gpr .r4) 64 = bytesAt s.mem (s.gpr .r4) 64 := by
    rw [hm4]
    simp only [bytesAt, List.map_inj_left]
    intro i hi
    exact hf1 _ fun r hr => by rw [List.mem_singleton.mp hr]; exact hwb i (List.mem_range.mp hi)
  refine WP.seq (WP.mono (engine_ok hc4 e14
    (fun i hi => by rw [hr4.rd, hr4.wr]; exact in_base (List.mem_append_left _ hwide) (by omega_arith) (by omega_arith))
    (fun i hi => not_in_ws (by omega_arith) (hwb i hi))) fun s5 ⟨hr5, hf5, hv5⟩ => ?_)
  rw [hb1] at hv5
  have hc5 : Ctx (s.gpr .r5) s5 := hc4.of_rest hr5 (by decide)
  -- The copy to `out`, and the restores.
  unfold scalarFinish
  rw [scalarRestore_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (by decide) (by decide) fun s6 u6 => ?_
  have e14' : s6.gpr .r14 = s.gpr .r3 := by rw [u6.gpr, hr5.gpr _ (by decide), e27, BitVec.add_zero]
  have hc6 : Ctx (s.gpr .r5) s6 := hc5.of_rest (u6.rest (ws := [.r14]) (by decide)) (by decide)
  have hwr6 : s6.wr = s.wr := by rw [u6.wr, hr5.wr, hr4.wr]
  have hrd6 : s6.rd = s.rd := by rw [u6.rd, hr5.rd, hr4.rd]
  refine WP.append (packField_ok hc6 e14' (a := SR) (dst := 0) (by omega_arith) (by decide)
    (fun k hk => by rw [hwr6]; exact in_base hout (by omega_arith) (by omega_arith))
    (by rw [BitVec.add_zero]; exact hp.out_ws.sub_right (Offset.sub_base _ (by omega_arith))))
    fun s7 hp7 => ?_
  have hsv7 : Spill.Saved (s.gpr .r5) s.gpr saveList s7.mem := by
    have h5 : Spill.Saved (s.gpr .r5) s.gpr saveList s5.mem := by
      rw [← hm4] at hsv
      refine hsv.frame_in (lo := SAVE) (n := 96) saveList_in hf5 fun r hr => ?_
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    rw [← u6.mem] at h5
    refine h5.frame_in (lo := SAVE) (n := 96) saveList_in hp7.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr, BitVec.add_zero]
    exact fun x h₁ h₂ => hp.out_ws x h₂ (Offset.sub_base _ (by omega_arith) x h₁)
  refine Spill.restore_ok (b := .r6) (B := s.gpr .r5) (by decide)
    (by rw [hp7.rest.gpr _ (by decide), u6.other _ (by decide), hr5.gpr _ (by decide), e6])
    saveList_fits saveList_restorable
    (fun p hpl => by
      rw [hp7.rest.rd, hp7.rest.wr, hrd6, hwr6]
      exact in_base (List.mem_append_right _ hws) (by have := saveList_in p hpl; omega_arith)
        (by have := saveList_in p hpl; omega_arith)) hsv7 fun s8 h8 => WP.block_nil ⟨fun r hr => ?_, ?_, ?_⟩
  · refine h8.gpr_of ?_
    by_cases hm : r ∈ saveList.map Prod.fst
    · exact .inl hm
    · refine .inr ?_
      rw [saveList_regs] at hm
      have h1 : r ∉ ([.r7] : List Reg) := by revert hr hm; cases r <;> decide
      have h2 : r ∉ ([.r14] : List Reg) := by revert hr hm; cases r <;> decide
      have h3 : r ∉ ([.r5, .r7, .r8, .r11, .r15, .r16] : List Reg) := by revert hr hm; cases r <;> decide
      have h4 : r ∉ ([.r6, .r14, .r27] : List Reg) := by revert hr hm; cases r <;> decide
      rw [hp7.rest.gpr _ h1, u6.other _ (by simpa using h2), hr5.gpr _ h3, hr4.gpr _ h4]
  · rw [h8.sp, hp7.rest.sp, u6.sp, hr5.sp, hr4.sp]
  · rw [h8.mem]
    refine out_bytes (b := s.gpr .r5) (a := SR) (fun j hj => by rw [← Nat.zero_add (4 * j)]; exact hp7.outs j hj) ?_
    rw [u6.mem, hv5]

end VG.Proof.Ed25519.PPC64LE
