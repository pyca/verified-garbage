module

public import VerifiedGarbage.Spec.Argon2
public import VerifiedGarbage.Impl.Argon2.PPC64LE.HPrime
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Blake2.Stream
import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # H′ on PPC64LE: saving the caller, the return address and the length prefix -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Proof.MdStream.PPC64LE (Upd wp_mov wp_std wp_stw wp_ld)

/-- The memory after the setup: the saved registers, the return address at
880 and the length prefix at 832. -/
def setupMem (s : State) : Mem :=
  ((Spill.saveMem s.mem (s.gpr .r7) s.gpr saved).writeW (s.gpr .r7 + BitVec.ofNat 64 880) s.lr).writeW
    (s.gpr .r7 + BitVec.ofNat 64 832) ((s.gpr .r6).setWidth 32)

theorem saved_in : ∀ p ∈ saved, 832 ≤ p.2 ∧ p.2 + 8 ≤ 832 + 64 := by decide

theorem setupMem_frame (s : State) :
    Frame [⟨s.gpr .r7 + BitVec.ofNat 64 832, 64⟩] s.mem (setupMem s) :=
  ((Spill.saveMem_frame saved_in (by decide) _ _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains _ (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (Offset.contains _ (by decide) (by decide) (by decide))

theorem setupMem_prefix (s : State) :
    Spec.Blake2.bytesAt (setupMem s) (s.gpr .r7 + BitVec.ofNat 64 832) 4 =
      Spec.Argon2.le32 (s.gpr .r6).toNat := by
  rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (Or.inl rfl)]
  unfold setupMem
  rw [Mem.readW_writeW_self32]
  rfl

theorem saved_bounds : ∀ p ∈ saved, 840 ≤ p.2 ∧ p.2 + 8 ≤ 880 := by decide

theorem setupMem_saved (s : State) (r : Reg) (d : Nat) (hr : (r, d) ∈ saved) :
    (setupMem s).readW (s.gpr .r7 + BitVec.ofNat 64 d) 64 = s.gpr r := by
  have hd := saved_bounds (r, d) hr
  have h880 : d + 8 ≤ 880 := hd.2
  unfold setupMem
  rw [Mem.readW_writeW_sep (Offset.sep _ (Or.inr (by omega)) (by omega) (by decide)) (by decide),
    Mem.readW_writeW_sep (Offset.sep _ (Or.inl h880) (by omega) (by decide)) (by decide)]
  exact Spill.saveMem_saved (by decide) _ _ _ (r, d) hr

theorem setupMem_lr (s : State) :
    (setupMem s).readW (s.gpr .r7 + BitVec.ofNat 64 880) 64 = s.lr := by
  unfold setupMem
  rw [Mem.readW_writeW_sep (Offset.sep _ (Or.inr (by decide)) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self64]

structure Setup (s t : State) : Prop where
  workspace : t.gpr .r31 = s.gpr .r7
  input : t.gpr .r27 = s.gpr .r3
  length : t.gpr .r28 = s.gpr .r4
  output : t.gpr .r29 = s.gpr .r5
  remaining : t.gpr .r30 = s.gpr .r6
  other : ∀ r, r ≠ .r0 → r ≠ .r31 → r ≠ .r27 → r ≠ .r28 → r ≠ .r29 → r ≠ .r30 → t.gpr r = s.gpr r
  mem : t.mem = setupMem s
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem setup_ok (s : State) (hw : (⟨s.gpr .r7, 16384⟩ : Region) ∈ s.wr) :
    WP isa (.block setup) s (Setup s) := by
  have write (d n : Nat) (h : d + n ≤ 16384) :
      InRegions s.wr (s.gpr .r7 + BitVec.ofNat 64 d) n :=
    ⟨_, hw, Offset.contains_base _ h (by omega)⟩
  unfold setup
  rw [show saved.map (fun (r, d) => Instr.store .d r .r7 d) = Spill.saveCode .r7 saved from rfl]
  refine Spill.save_ok (by decide) (by decide) (fun p hp => write _ _ (by have := saved_in p hp; omega)) ?_
  refine MdStream.PPC64LE.WP.cons exec_mflr ?_
  have u₀ := Upd.write { s with mem := Spill.saveMem s.mem (s.gpr .r7) s.gpr saved } .r0 s.lr
  generalize { s with mem := Spill.saveMem s.mem (s.gpr .r7) s.gpr saved }.write .r0 s.lr = a at u₀
  refine wp_std (a := s.gpr .r7 + BitVec.ofNat 64 880) (by decide) (by rw [u₀.other _ (by decide)])
    (by rw [u₀.wr]; exact write 880 8 (by decide)) fun c hc => ?_
  refine wp_mov fun d hd => wp_mov fun e he => wp_mov fun f hf => wp_mov fun g hg =>
    wp_mov fun h hh => ?_
  refine wp_stw (a := s.gpr .r7 + BitVec.ofNat 64 832) (by decide)
    (by rw [hh.other _ (by decide), hg.other _ (by decide), hf.other _ (by decide),
      he.other _ (by decide), hd.gpr, hc.gpr, u₀.other _ (by decide)])
    (by rw [hh.wr, hg.wr, hf.wr, he.wr, hd.wr, hc.wr, u₀.wr]; exact write 832 4 (by decide))
    fun t ht => WP.block_nil ?_
  have o : ∀ r, r ≠ .r0 → r ≠ .r31 → r ≠ .r27 → r ≠ .r28 → r ≠ .r29 → r ≠ .r30 →
      t.gpr r = s.gpr r := fun r h0 h31 h27 h28 h29 h30 => by
    rw [ht.gpr, hh.other _ h30, hg.other _ h29, hf.other _ h28, he.other _ h27, hd.other _ h31,
      hc.gpr, u₀.other _ h0]
  refine ⟨?_, ?_, ?_, ?_, ?_, o, ?_, ?_, ?_, ?_⟩
  · rw [ht.gpr, hh.other _ (by decide), hg.other _ (by decide), hf.other _ (by decide),
      he.other _ (by decide), hd.gpr, hc.gpr, u₀.other _ (by decide)]
  · rw [ht.gpr, hh.other _ (by decide), hg.other _ (by decide), hf.other _ (by decide), he.gpr,
      hd.other _ (by decide), hc.gpr, u₀.other _ (by decide)]
  · rw [ht.gpr, hh.other _ (by decide), hg.other _ (by decide), hf.gpr, he.other _ (by decide),
      hd.other _ (by decide), hc.gpr, u₀.other _ (by decide)]
  · rw [ht.gpr, hh.other _ (by decide), hg.gpr, hf.other _ (by decide), he.other _ (by decide),
      hd.other _ (by decide), hc.gpr, u₀.other _ (by decide)]
  · rw [ht.gpr, hh.gpr, hg.other _ (by decide), hf.other _ (by decide), he.other _ (by decide),
      hd.other _ (by decide), hc.gpr, u₀.other _ (by decide)]
  · have r6 : h.gpr .r6 = s.gpr .r6 := by
      rw [hh.other _ (by decide), hg.other _ (by decide), hf.other _ (by decide),
        he.other _ (by decide), hd.other _ (by decide), hc.gpr, u₀.other _ (by decide)]
    rw [ht.mem, r6, hh.mem, hg.mem, hf.mem, he.mem, hd.mem, hc.mem, u₀.mem, u₀.gpr]
    rfl
  · rw [ht.rd, hh.rd, hg.rd, hf.rd, he.rd, hd.rd, hc.rd, u₀.rd]
  · rw [ht.wr, hh.wr, hg.wr, hf.wr, he.wr, hd.wr, hc.wr, u₀.wr]
  · rw [ht.sp, hh.sp, hg.sp, hf.sp, he.sp, hd.sp, hc.sp, u₀.sp]

/-- Restoring the return address and the caller's registers. -/
theorem restore_ok (original s : State) (base : s.gpr .r31 = original.gpr .r7)
    (extra : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → s.gpr r = original.gpr r)
    (readable : (⟨original.gpr .r7, 16384⟩ : Region) ∈ s.rd ++ s.wr)
    (values : ∀ r d, (r, d) ∈ saved →
      s.mem.readW (original.gpr .r7 + BitVec.ofNat 64 d) 64 = original.gpr r)
    (lrSlot : s.mem.readW (original.gpr .r7 + BitVec.ofNat 64 880) 64 = original.lr) :
    WP isa (.block restore) s fun t =>
      (∀ r ∈ preserved, t.gpr r = original.gpr r) ∧ t.lr = original.lr ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have read (d : Nat) (h : d + 8 ≤ 16384) :
      InRegions (s.rd ++ s.wr) (original.gpr .r7 + BitVec.ofNat 64 d) 8 :=
    ⟨_, readable, Offset.contains_base _ h (by omega)⟩
  rw [show restore = ([.load .d .r0 .r31 880, .mtlr .r0] : List Instr) ++ Spill.restoreCode .r31 saved
    from rfl, List.cons_append, List.cons_append, List.nil_append]
  refine wp_ld (a := original.gpr .r7 + BitVec.ofNat 64 880) (by decide) (by rw [base])
    (read 880 (by decide)) fun a ha => ?_
  refine MdStream.PPC64LE.WP.cons exec_mtlr ?_
  refine WP.mono (Spill.restore_wp (b := .r31) (B := original.gpr .r7) (g := original.gpr) (by decide)
    (by simp [ha.other _ (by decide : Reg.r31 ≠ .r0), base]) (by decide) (by decide)
    (fun p hp => by
      simp only [ha.rd, ha.wr]
      exact read _ (by have := saved_bounds p hp; omega))
    (fun p hp => by simp only [ha.mem]; exact values p.1 p.2 hp)) fun t ht => ?_
  refine ⟨fun r hr => ht.gpr_of ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hm : r ∈ saved.map Prod.fst
    · exact .inl hm
    · refine .inr ?_
      have h0 : r ≠ .r0 := fun h => by subst h; exact absurd hr (by decide)
      show a.gpr r = _
      rw [ha.other r h0, extra r hr hm]
  · rw [ht.lr]; show a.gpr .r0 = _; rw [ha.gpr, lrSlot]
  · rw [ht.mem]; exact ha.mem
  · rw [ht.rd]; exact ha.rd
  · rw [ht.wr]; exact ha.wr
  · rw [ht.sp]; exact ha.sp

end VG.Proof.Argon2.PPC64LE.HPrime
