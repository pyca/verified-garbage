import VerifiedGarbage.Proof.Blowfish.X86_64.Block
import VerifiedGarbage.Proof.Blowfish.KeyTable

/-!
# Key expansion: the initial schedule

`initSchedule_run`: the 521 quadwords of the initial schedule's image, as
immediates, into the schedule at `rdx`.
-/

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- The schedule at `S` is writable. -/
def SchedW (S : Addr) (t : State) : Prop := ∀ off n, off + n ≤ 4168 → InRegions t.wr (S + BitVec.ofNat 64 off) n

theorem SchedW.of_mem {S : Addr} {t : State} (h : (⟨S, 4168⟩ : Region) ∈ t.wr) : SchedW S t :=
  fun off n hon => ⟨_, h, Offset.contains_base S hon (by omega)⟩

theorem exec_store64 {s : State} {m : MemOp} {r : Reg} (h : InRegions s.wr (s.ea m) 8) :
    exec (.store m r) s = some { s with mem := s.mem.writeW (s.ea m) (s.gpr r) } := by
  simp only [exec, State.store64, h, ite_true]

/-- `u` is `t` with other registers and memory. -/
def GM (t u : State) : Prop := u = { t with gpr := u.gpr, mem := u.mem }

theorem GM.trans {t u v : State} (h₁ : u = { t with gpr := u.gpr, mem := u.mem })
    (h₂ : v = { u with gpr := v.gpr, mem := v.mem }) : v = { t with gpr := v.gpr, mem := v.mem } := by
  rw [h₂]; conv => lhs; rw [h₁]

/-- Quadword `i` of the initial schedule. -/
def initStep (i : Nat) : List Instr :=
  [.movImm64 .r11 (Impl.Blowfish.initWord i), .store (mem .rdx (8 * i)) .r11]

theorem initSchedule_eq : initSchedule = (List.range 521).flatMap initStep := rfl

theorem flatMap_range_succ {α : Type} (f : Nat → List α) (k : Nat) :
    (List.range (k + 1)).flatMap f = (List.range k).flatMap f ++ f k := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem initSteps_run {S : Addr} {t : State} (hS : t.gpr .rdx = S) (hW : SchedW S t) :
    ∀ k ≤ 521, ∃ t', runBlock isa ((List.range k).flatMap initStep) t = some t' ∧
      (∀ i < k, t'.mem.readW (S + BitVec.ofNat 64 (8 * i)) 64 = Impl.Blowfish.initWord i) ∧
      Frame [⟨S, 4168⟩] t.mem t'.mem ∧ (∀ g, g ≠ .r11 → t'.gpr g = t.gpr g) ∧
      t' = { t with gpr := t'.gpr, mem := t'.mem }
  | 0, _ => ⟨t, rfl, fun i hi => by omega, Frame.refl _ _, fun _ _ => rfl, rfl⟩
  | k + 1, hk => by
    obtain ⟨u, r, d, f, g, e⟩ := initSteps_run hS hW k (by omega)
    let u₁ := u.setReg .r11 (Impl.Blowfish.initWord k)
    have ea : u₁.ea (mem .rdx (8 * k)) = S + BitVec.ofNat 64 (8 * k) := by
      rw [ea_mem]; simp only [u₁, gpr_setReg_of_ne _ _ (show Reg.rdx ≠ Reg.r11 by decide)]
      rw [g .rdx (by decide), hS]
    have hw : InRegions u₁.wr (u₁.ea (mem .rdx (8 * k))) 8 := by
      rw [ea, show u₁.wr = t.wr by simp only [u₁, wr_setReg]; rw [e]]; exact hW _ _ (by omega)
    let u₂ : State := { u₁ with mem := u₁.mem.writeW (u₁.ea (mem .rdx (8 * k))) (u₁.gpr .r11) }
    have m₂ : u₂.mem = u.mem.writeW (S + BitVec.ofNat 64 (8 * k)) (Impl.Blowfish.initWord k) := by
      simp only [u₂, ea]; simp only [u₁, mem_setReg, gpr_setReg_self]
    refine ⟨u₂, ?_, fun i hi => ?_, ?_, fun g' h => ?_, ?_⟩
    · rw [flatMap_range_succ, runBlock_append_x r, initStep, runBlock_cons, exec_movImm64, runStep_some,
        runBlock_cons, exec_store64 hw, runStep_some, runBlock_nil]
    · rw [m₂]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [Mem.readW_writeW_sep (Offset.sep S (by omega) (by omega) (by omega)) (by decide)]
        exact d i hi
      · exact Mem.readW_writeW_self64 _ _ _
    · rw [m₂]
      exact f.writeW (List.mem_singleton_self _) _ (Offset.contains_base S (by omega) (by omega))
    · simp only [u₂, u₁, gpr_setReg_of_ne _ _ h]; exact g g' h
    · exact GM.trans e (by simp only [u₂, u₁, State.setReg])

end VG.Proof.Blowfish.X86_64
