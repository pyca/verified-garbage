module

public import VerifiedGarbage.Spec.Argon2
public import VerifiedGarbage.Impl.Argon2.RISCV64.HPrime
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Blake2.Stream
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # H′ on RISC-V: saving the caller's registers and the length prefix

The return address is a register like the callee-saved ones, saved at 880
with them. -/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.RISCV64.Steps (Upd Mupd wp_mv wp_sw)

/-- The memory after the setup: the saved registers and the length prefix
at 832. -/
def setupMem (s : State) : Mem :=
  (Spill.saveMem s.mem (s.gpr .a4) s.gpr saved).writeW
    (s.gpr .a4 + BitVec.ofNat 64 832) ((s.gpr .a3).setWidth 32)

theorem saved_in : ∀ p ∈ saved, 832 ≤ p.2 ∧ p.2 + 8 ≤ 832 + 64 := by decide

theorem saved_fits : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

theorem setupMem_frame (s : State) :
    Frame [⟨s.gpr .a4 + BitVec.ofNat 64 832, 64⟩] s.mem (setupMem s) :=
  (Spill.saveMem_frame saved_in (by decide) _ _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains _ (by decide) (by decide) (by decide))

theorem setupMem_prefix (s : State) :
    Spec.Blake2.bytesAt (setupMem s) (s.gpr .a4 + BitVec.ofNat 64 832) 4 =
      Spec.Argon2.le32 (s.gpr .a3).toNat := by
  rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (Or.inl rfl)]
  unfold setupMem
  rw [Mem.readW_writeW_self32]
  rfl

theorem saved_bounds : ∀ p ∈ saved, 840 ≤ p.2 ∧ p.2 + 8 ≤ 888 := by decide

theorem setupMem_saved (s : State) : Spill.Saved (s.gpr .a4) s.gpr saved (setupMem s) := by
  intro p hp
  have hd := saved_bounds p hp
  unfold setupMem
  rw [Mem.readW_writeW_sep (Offset.sep _ (Or.inr (by omega)) (by omega) (by decide)) (by decide)]
  exact Spill.saveMem_saved (by decide) _ _ _ p hp

structure Setup (s t : State) : Prop where
  workspace : t.gpr .s4 = s.gpr .a4
  input : t.gpr .s0 = s.gpr .a0
  length : t.gpr .s1 = s.gpr .a1
  output : t.gpr .s2 = s.gpr .a2
  remaining : t.gpr .s3 = s.gpr .a3
  other : ∀ r, r ≠ .s4 → r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → t.gpr r = s.gpr r
  mem : t.mem = setupMem s
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem setup_ok (s : State) (hw : (⟨s.gpr .a4, 16384⟩ : Region) ∈ s.wr)
    (hal : (s.gpr .a4).toNat % 8 = 0) :
    WP isa (.block setup) s (Setup s) := by
  have write (d n : Nat) (h : d + n ≤ 16384) :
      InRegions s.wr (s.gpr .a4 + BitVec.ofNat 64 d) n :=
    ⟨_, hw, Offset.contains_base _ h (by omega)⟩
  unfold setup
  rw [show saved.map (fun (r, d) => Instr.store .d r .a4 d) = Spill.saveCode .a4 saved from rfl]
  refine Spill.save_ok hal saved_fits (fun p hp => write _ _ (by have := saved_in p hp; omega)) ?_
  generalize hs₀ : ({ s with mem := Spill.saveMem s.mem (s.gpr .a4) s.gpr saved } : State) = s₀
  refine wp_mv fun d hd => wp_mv fun e he => wp_mv fun f hf => wp_mv fun g hg =>
    wp_mv fun h hh => ?_
  have g4 : s₀.gpr .a4 = s.gpr .a4 := by rw [← hs₀]
  refine wp_sw (a := s.gpr .a4 + BitVec.ofNat 64 832) (by decide)
    (by rw [hh.other _ (by decide), hg.other _ (by decide), hf.other _ (by decide),
      he.other _ (by decide), hd.gpr, g4])
    (by have h8 := Spill.al8 hal (d := 832) (by decide); omega)
    (by rw [hh.wr, hg.wr, hf.wr, he.wr, hd.wr, ← hs₀]; exact write 832 4 (by decide))
    fun t ht => WP.block_nil ?_
  have o : ∀ r, r ≠ .s4 → r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 →
      t.gpr r = s.gpr r := fun r h4 h0 h1 h2 h3 => by
    rw [ht.gpr, hh.other _ h3, hg.other _ h2, hf.other _ h1, he.other _ h0, hd.other _ h4, ← hs₀]
  have ga : ∀ r, r ≠ .s4 → r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s₀.gpr r = s.gpr r :=
    fun _ _ _ _ _ _ => by rw [← hs₀]
  refine ⟨?_, ?_, ?_, ?_, ?_, o, ?_, ?_, ?_, ?_⟩
  · rw [ht.gpr, hh.other _ (by decide), hg.other _ (by decide), hf.other _ (by decide),
      he.other _ (by decide), hd.gpr, g4]
  · rw [ht.gpr, hh.other _ (by decide), hg.other _ (by decide), hf.other _ (by decide), he.gpr,
      hd.other _ (by decide), ga _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [ht.gpr, hh.other _ (by decide), hg.other _ (by decide), hf.gpr, he.other _ (by decide),
      hd.other _ (by decide), ga _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [ht.gpr, hh.other _ (by decide), hg.gpr, hf.other _ (by decide), he.other _ (by decide),
      hd.other _ (by decide), ga _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [ht.gpr, hh.gpr, hg.other _ (by decide), hf.other _ (by decide), he.other _ (by decide),
      hd.other _ (by decide), ga _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · have a3 : h.gpr .a3 = s.gpr .a3 := by
      rw [hh.other _ (by decide), hg.other _ (by decide), hf.other _ (by decide),
        he.other _ (by decide), hd.other _ (by decide),
        ga _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    rw [ht.mem, a3, hh.mem, hg.mem, hf.mem, he.mem, hd.mem, ← hs₀]
    rfl
  · rw [ht.rd, hh.rd, hg.rd, hf.rd, he.rd, hd.rd, ← hs₀]
  · rw [ht.wr, hh.wr, hg.wr, hf.wr, he.wr, hd.wr, ← hs₀]
  · rw [ht.sp, hh.sp, hg.sp, hf.sp, he.sp, hd.sp, ← hs₀]

/-- Restoring the return address and the caller's registers. -/
theorem restore_ok (original s : State) (base : s.gpr .s4 = original.gpr .a4)
    (hal : (original.gpr .a4).toNat % 8 = 0)
    (extra : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → s.gpr r = original.gpr r)
    (readable : (⟨original.gpr .a4, 16384⟩ : Region) ∈ s.rd ++ s.wr)
    (values : Spill.Saved (original.gpr .a4) original.gpr saved s.mem) :
    WP isa (.block restore) s fun t =>
      (∀ r ∈ preserved, t.gpr r = original.gpr r) ∧ t.gpr .ra = original.gpr .ra ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have read (d : Nat) (h : d + 8 ≤ 16384) :
      InRegions (s.rd ++ s.wr) (original.gpr .a4 + BitVec.ofNat 64 d) 8 :=
    ⟨_, readable, Offset.contains_base _ h (by omega)⟩
  rw [show restore = Spill.restoreCode .s4 saved from rfl]
  refine WP.mono (Spill.restore_wp (b := .s4) hal base saved_fits (by decide)
    (fun p (hp : p ∈ saved) => read _ (by have := saved_bounds p hp; omega)) values) fun t ht => ?_
  refine ⟨fun r hr => ht.gpr_of ?_, ht.gpr (.ra, 880) (by decide), ht.mem, ht.rd, ht.wr, ht.sp⟩
  by_cases hm : r ∈ saved.map Prod.fst
  · exact .inl hm
  · exact .inr (extra r hr hm)

end VG.Proof.Argon2.RISCV64.HPrime
