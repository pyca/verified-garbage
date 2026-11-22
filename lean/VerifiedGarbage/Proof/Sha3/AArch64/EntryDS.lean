module

public import VerifiedGarbage.Proof.Sha3.AArch64.EntryS
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RelCT

/-!
# Calling a function with the addresses of several functions in registers (AArch64)

`Verified.entryDS`: `Verified.entryD8S` for a list `L` of functions and the
registers that hold their addresses. `entryDS L name k body` copies the
caller's `k` stack words into the bottom of its frame, saves the return
address above them, then, for each function `n` and register `v` of `L`,
saves `v`'s low 64 bits and puts `n`'s address there (`saveRegs`), calls
`body`, and restores them (`restoreRegs`). The registers are distinct, and
`body` writes none of them (`Contract.dL`).
-/

-- separate module: the entry for several functions' addresses, which only some callers need,
-- apart from `EntryS.lean`'s one.

@[expose] public section

namespace VG.Proof.Sha3.AArch64

open VG VG.AArch64 VG.Impl.Sha3.AArch64 VG.Impl.StackScratch.AArch64

/-! ## Saving and restoring the registers -/

/-- The state after `saveRegs o i [(n, v)]` from `w`. -/
def regStep (o i : Nat) (n : String) (v : VReg) (w : State) : State :=
  let w₁ := w.write .x .x16 (laneOf w v 0)
  let w₂ : State := { w₁ with mem := w₁.mem.write (w₁.sp + BitVec.ofNat 64 (o + 8 + 8 * i)) 8 (w₁.gpr .x16) }
  let w₃ := w₂.write .x .x16 (w₂.syms n)
  w₃.setV v (setLane (w₃.v v) 64 0 (w₃.gpr .x16))

/-- The state after `saveRegs o i L` from `w`. -/
def sRegs (o : Nat) : Nat → List (String × VReg) → State → State
  | _, [], w => w
  | i, (n, v) :: L, w => sRegs o (i + 1) L (regStep o i n v w)

/-- What `saveRegs o i L` leaks, from `sp = p`: the addresses of the saves. -/
def regsTrace (o : Nat) (p : Addr) : Nat → List (String × VReg) → List Leak
  | _, [] => []
  | i, _ :: L => .addr (p + BitVec.ofNat 64 (o + 8 + 8 * i)) :: regsTrace o p (i + 1) L

section
variable (o i : Nat) (n : String) (v : VReg) (w : State)

@[simp] theorem regStep_sp : (regStep o i n v w).sp = w.sp := rfl
@[simp] theorem regStep_rd : (regStep o i n v w).rd = w.rd := rfl
@[simp] theorem regStep_wr : (regStep o i n v w).wr = w.wr := rfl
@[simp] theorem regStep_syms : (regStep o i n v w).syms = w.syms := rfl
@[simp] theorem regStep_dit : (regStep o i n v w).dit = w.dit := rfl

theorem regStep_mem :
    (regStep o i n v w).mem = w.mem.write (w.sp + BitVec.ofNat 64 (o + 8 + 8 * i)) 8 (laneOf w v 0) := by
  show (w.write .x .x16 (laneOf w v 0)).mem.write _ 8 ((w.write .x .x16 (laneOf w v 0)).gpr .x16) = _
  rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]; rfl

theorem regStep_gpr {q : Reg} (h : q ≠ .x16) : (regStep o i n v w).gpr q = w.gpr q := by
  simp only [regStep, RegUpd.gpr_setV, RegUpd.gpr_write_of_ne _ _ _ h]

theorem regStep_v {q : VReg} (h : q ≠ v) : (regStep o i n v w).v q = w.v q := by
  simp only [regStep, RegUpd.v_setV_of_ne _ _ h, RegUpd.v_write]

theorem regStep_lane : ((regStep o i n v w).v v).extractLsb' 0 64 = w.syms n := by
  simp only [regStep, RegUpd.v_setV_self, RegUpd.gpr_write_self, BitVec.setWidth_eq]
  exact (extract_setLane64 _ _ (i := 0) (j := 0) (by decide) (by decide)).trans (ite_eq_left rfl)

end

theorem regStep_run {o i : Nat} {n : String} {v : VReg} {w : State}
    (ho : (o + 8 + 8 * i) % 8 = 0 ∧ o + 8 + 8 * i < 32768)
    (h : InRegions w.wr (w.sp + BitVec.ofNat 64 (o + 8 + 8 * i)) 8) :
    execBlock isa [.umov .x .x16 v 0, .strSp .x16 (o + 8 + 8 * i), .adrSym .x16 n, .vop (.ins .d2 v 0 .x16)] w =
      some (regStep o i n v w, [.addr (w.sp + BitVec.ofNat 64 (o + 8 + 8 * i))]) := by
  have e₀ : exec (.umov .x .x16 v 0) w = some (w.write .x .x16 (laneOf w v 0)) := exec_umov (by decide)
  have e₁ := exec_strSp' (s := w.write .x .x16 (laneOf w v 0)) (t := .x16) ho h
  have e₂ := exec_adrSym (s := { w.write .x .x16 (laneOf w v 0) with
    mem := (w.write .x .x16 (laneOf w v 0)).mem.write ((w.write .x .x16 (laneOf w v 0)).sp +
      BitVec.ofNat 64 (o + 8 + 8 * i)) 8 ((w.write .x .x16 (laneOf w v 0)).gpr .x16) }) (d := .x16) (name := n)
  have e₃ := exec_ins (s := ({ w.write .x .x16 (laneOf w v 0) with
    mem := (w.write .x .x16 (laneOf w v 0)).mem.write ((w.write .x .x16 (laneOf w v 0)).sp +
      BitVec.ofNat 64 (o + 8 + 8 * i)) 8 ((w.write .x .x16 (laneOf w v 0)).gpr .x16) } : State).write .x .x16
      (w.syms n)) (r := .x16) (v := v) (l := 0) (by decide)
  simp only [execBlock, isa, e₀, e₁, e₂, Option.map_some, addrs, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  rfl

theorem saveRegs_run {o : Nat} (hm : o % 8 = 0) : ∀ (L : List (String × VReg)) (i : Nat) (w : State),
    o + 8 + 8 * (i + L.length) ≤ 32768 →
    (∀ idx < L.length, InRegions w.wr (w.sp + BitVec.ofNat 64 (o + 8 + 8 * (i + idx))) 8) →
    execBlock isa (saveRegs o i L) w = some (sRegs o i L w, regsTrace o w.sp i L)
  | [], _, _, _, _ => rfl
  | (n, v) :: L, i, w, hb, hr => by
    simp only [List.length_cons] at hb
    rw [saveRegs, execBlock_append, regStep_run ⟨by omega, by omega⟩ (by simpa using hr 0 (by simp))]
    simp only [Option.bind_some]
    rw [saveRegs_run hm L (i + 1) (regStep o i n v w) (by omega) (fun idx h => by
      rw [regStep_wr, regStep_sp, show i + 1 + idx = i + (idx + 1) by omega]
      exact hr (idx + 1) (by simp; omega))]
    simp only [Option.map_some, regStep_sp, sRegs, regsTrace, List.singleton_append]

section
variable (o : Nat)

theorem sRegs_sp : ∀ (L : List (String × VReg)) (i : Nat) (w : State), (sRegs o i L w).sp = w.sp
  | [], _, _ => rfl
  | (n, v) :: L, i, w => (sRegs_sp L (i + 1) _).trans (regStep_sp o i n v w)
theorem sRegs_rd : ∀ (L : List (String × VReg)) (i : Nat) (w : State), (sRegs o i L w).rd = w.rd
  | [], _, _ => rfl
  | (n, v) :: L, i, w => (sRegs_rd L (i + 1) _).trans (regStep_rd o i n v w)
theorem sRegs_wr : ∀ (L : List (String × VReg)) (i : Nat) (w : State), (sRegs o i L w).wr = w.wr
  | [], _, _ => rfl
  | (n, v) :: L, i, w => (sRegs_wr L (i + 1) _).trans (regStep_wr o i n v w)
theorem sRegs_syms : ∀ (L : List (String × VReg)) (i : Nat) (w : State), (sRegs o i L w).syms = w.syms
  | [], _, _ => rfl
  | (n, v) :: L, i, w => (sRegs_syms L (i + 1) _).trans (regStep_syms o i n v w)
theorem sRegs_dit : ∀ (L : List (String × VReg)) (i : Nat) (w : State), (sRegs o i L w).dit = w.dit
  | [], _, _ => rfl
  | (n, v) :: L, i, w => (sRegs_dit L (i + 1) _).trans (regStep_dit o i n v w)

theorem sRegs_gpr {q : Reg} (h : q ≠ .x16) :
    ∀ (L : List (String × VReg)) (i : Nat) (w : State), (sRegs o i L w).gpr q = w.gpr q
  | [], _, _ => rfl
  | (n, v) :: L, i, w => (sRegs_gpr h L (i + 1) _).trans (regStep_gpr o i n v w h)

theorem sRegs_v {q : VReg} :
    ∀ (L : List (String × VReg)) (i : Nat) (w : State), (∀ p ∈ L, p.2 ≠ q) → (sRegs o i L w).v q = w.v q
  | [], _, _, _ => rfl
  | (n, v) :: L, i, w, h =>
    (sRegs_v L (i + 1) _ fun p hp => h p (List.mem_cons_of_mem _ hp)).trans
      (regStep_v o i n v w (h (n, v) (List.mem_cons_self ..)).symm)

/-- After the saves, each register holds the address of its function. -/
theorem sRegs_DL : ∀ (L : List (String × VReg)) (i : Nat) (w : State), (L.map (·.2)).Nodup →
    DL L (sRegs o i L w)
  | [], _, _, _ => fun _ h => absurd h List.not_mem_nil
  | (n, v) :: L, i, w, hn => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · show ((sRegs o (i + 1) L (regStep o i n v w)).v v).extractLsb' 0 64 =
        (sRegs o (i + 1) L (regStep o i n v w)).syms n
      rw [sRegs_v o L (i + 1) _ (fun q hq e => hn.1 ⟨q, hq, e⟩), sRegs_syms, regStep_lane, regStep_syms]
    · exact sRegs_DL L (i + 1) _ hn.2 p hp

/-- The saves write only their slots. -/
theorem sRegs_frame : ∀ (L : List (String × VReg)) (i : Nat) (w : State),
    o + 8 + 8 * (i + L.length) < 2 ^ 64 →
    Frame [⟨w.sp + BitVec.ofNat 64 (o + 8 + 8 * i), 8 * L.length⟩] w.mem (sRegs o i L w).mem
  | [], _, _, _ => Frame.refl _ _
  | (n, v) :: L, i, w, hb => by
    simp only [List.length_cons] at hb ⊢
    have f := sRegs_frame L (i + 1) (regStep o i n v w) (by omega)
    rw [regStep_sp] at f
    have h₀ : Frame [⟨w.sp + BitVec.ofNat 64 (o + 8 + 8 * i), 8 * (L.length + 1)⟩] w.mem
        (regStep o i n v w).mem := by
      rw [regStep_mem]
      exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _
        (Offset.contains _ (Nat.le_refl _) (by omega) (by omega))
    refine Frame.trans h₀ (Frame.sub f fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega) (by omega)⟩

/-- The slots hold the registers' low halves from before the saves. -/
theorem sRegs_read : ∀ (L : List (String × VReg)) (i : Nat) (w : State), (L.map (·.2)).Nodup →
    o + 8 + 8 * (i + L.length) < 2 ^ 64 → ∀ idx (h : idx < L.length),
    (sRegs o i L w).mem.read (w.sp + BitVec.ofNat 64 (o + 8 + 8 * (i + idx))) 8 = laneOf w (L[idx]).2 0
  | [], _, _, _, _, idx, h => absurd h (Nat.not_lt_zero _)
  | (n, v) :: L, i, w, hn, hb, idx, h => by
    simp only [List.length_cons] at hb h
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    cases idx with
    | zero =>
      have f := sRegs_frame o L (i + 1) (regStep o i n v w) (by omega)
      rw [regStep_sp] at f
      rw [show sRegs o i ((n, v) :: L) w = sRegs o (i + 1) L (regStep o i n v w) from rfl,
        f.read (r := ⟨w.sp + BitVec.ofNat 64 (o + 8 + 8 * (i + 0)), 8⟩) (Region.contains_self _ _)
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by decide),
        regStep_mem, Nat.add_zero i, read_write_self]
      rfl
    | succ idx =>
      have ih := sRegs_read L (i + 1) (regStep o i n v w) hn.2 (by omega) idx (by omega)
      rw [regStep_sp, show i + 1 + idx = i + (idx + 1) by omega] at ih
      rw [show sRegs o i ((n, v) :: L) w = sRegs o (i + 1) L (regStep o i n v w) from rfl, ih]
      have hne : (L[idx]).2 ≠ v := fun e => hn.1 ⟨L[idx], List.getElem_mem _, e⟩
      simp only [laneOf, regStep_v o i n v w hne, List.getElem_cons_succ]

/-! ### Restoring -/

/-- The state after `restoreRegs o i [(n, v)]` from `g`. -/
def rStep (o i : Nat) (v : VReg) (g : State) : State :=
  let g₁ := g.write .x .x16 (g.mem.read (g.sp + BitVec.ofNat 64 (o + 8 + 8 * i)) 8)
  g₁.setV v (setLane (g₁.v v) 64 0 (g₁.gpr .x16))

/-- The state after `restoreRegs o i L` from `g`. -/
def rRegs : Nat → List (String × VReg) → State → State
  | _, [], g => g
  | i, (_, v) :: L, g => rRegs (i + 1) L (rStep o i v g)

/-- What `restoreRegs o i L` leaks, from `sp = p`. -/
def rTrace (p : Addr) : Nat → List (String × VReg) → List Leak
  | _, [] => []
  | i, _ :: L => .addr (p + BitVec.ofNat 64 (o + 8 + 8 * i)) :: rTrace p (i + 1) L

theorem rStep_run {i : Nat} {v : VReg} {g : State} (ho : (o + 8 + 8 * i) % 8 = 0 ∧ o + 8 + 8 * i < 32768)
    (h : InRegions (g.rd ++ g.wr) (g.sp + BitVec.ofNat 64 (o + 8 + 8 * i)) 8) :
    execBlock isa [.ldrSp .x16 (o + 8 + 8 * i), .vop (.ins .d2 v 0 .x16)] g =
      some (rStep o i v g, [.addr (g.sp + BitVec.ofNat 64 (o + 8 + 8 * i))]) := by
  have e₁ := exec_ldrSp' (s := g) (t := .x16) ho h
  have e₂ := exec_ins (s := g.write .x .x16 (g.mem.read (g.sp + BitVec.ofNat 64 (o + 8 + 8 * i)) 8))
    (r := .x16) (v := v) (l := 0) (by decide)
  simp only [execBlock, isa, e₁, e₂, Option.map_some, addrs, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  rfl

theorem rStep_sp (i : Nat) (v : VReg) (g : State) : (rStep o i v g).sp = g.sp := rfl
theorem rStep_rd (i : Nat) (v : VReg) (g : State) : (rStep o i v g).rd = g.rd := rfl
theorem rStep_wr (i : Nat) (v : VReg) (g : State) : (rStep o i v g).wr = g.wr := rfl
theorem rStep_mem (i : Nat) (v : VReg) (g : State) : (rStep o i v g).mem = g.mem := rfl

theorem restoreRegs_run (hm : o % 8 = 0) : ∀ (L : List (String × VReg)) (i : Nat) (g : State),
    o + 8 + 8 * (i + L.length) ≤ 32768 →
    (∀ idx < L.length, InRegions (g.rd ++ g.wr) (g.sp + BitVec.ofNat 64 (o + 8 + 8 * (i + idx))) 8) →
    execBlock isa (restoreRegs o i L) g = some (rRegs o i L g, rTrace o g.sp i L)
  | [], _, _, _, _ => rfl
  | (n, v) :: L, i, g, hb, hr => by
    simp only [List.length_cons] at hb
    rw [restoreRegs, execBlock_append, rStep_run o ⟨by omega, by omega⟩ (by simpa using hr 0 (by simp))]
    simp only [Option.bind_some]
    rw [restoreRegs_run hm L (i + 1) (rStep o i v g) (by omega) (fun idx h => by
      rw [rStep_rd, rStep_wr, rStep_sp, show i + 1 + idx = i + (idx + 1) by omega]
      exact hr (idx + 1) (by simp; omega))]
    simp only [Option.map_some, rStep_sp, rRegs, rTrace, List.singleton_append]

theorem rRegs_sp : ∀ (L : List (String × VReg)) (i : Nat) (g : State), (rRegs o i L g).sp = g.sp
  | [], _, _ => rfl
  | (_, v) :: L, i, g => (rRegs_sp L (i + 1) _).trans (rStep_sp o i v g)

theorem rRegs_mem : ∀ (L : List (String × VReg)) (i : Nat) (g : State), (rRegs o i L g).mem = g.mem
  | [], _, _ => rfl
  | (_, v) :: L, i, g => (rRegs_mem L (i + 1) _).trans (rStep_mem o i v g)

theorem rRegs_gpr {q : Reg} (h : q ≠ .x16) :
    ∀ (L : List (String × VReg)) (i : Nat) (g : State), (rRegs o i L g).gpr q = g.gpr q
  | [], _, _ => rfl
  | (_, v) :: L, i, g => (rRegs_gpr h L (i + 1) _).trans (by
      simp only [rStep, RegUpd.gpr_setV, RegUpd.gpr_write_of_ne _ _ _ h])

theorem rRegs_v {q : VReg} :
    ∀ (L : List (String × VReg)) (i : Nat) (g : State), (∀ p ∈ L, p.2 ≠ q) → (rRegs o i L g).v q = g.v q
  | [], _, _, _ => rfl
  | (_, v) :: L, i, g, h =>
    (rRegs_v L (i + 1) _ fun p hp => h p (List.mem_cons_of_mem _ hp)).trans (by
      simp only [rStep, RegUpd.v_setV_of_ne _ _ (h (_, v) (List.mem_cons_self ..)).symm, RegUpd.v_write])

/-- After the restores, each register's low half is what its slot holds. -/
theorem rRegs_lane : ∀ (L : List (String × VReg)) (i : Nat) (g : State), (L.map (·.2)).Nodup →
    ∀ idx (h : idx < L.length),
    ((rRegs o i L g).v (L[idx]).2).extractLsb' 0 64 = g.mem.read (g.sp + BitVec.ofNat 64 (o + 8 + 8 * (i + idx))) 8
  | [], _, _, _, idx, h => absurd h (Nat.not_lt_zero _)
  | (n, v) :: L, i, g, hn, idx, h => by
    simp only [List.length_cons] at h
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    cases idx with
    | zero =>
      show ((rRegs o (i + 1) L (rStep o i v g)).v v).extractLsb' 0 64 = _
      rw [rRegs_v o L (i + 1) _ (fun q hq e => hn.1 ⟨q, hq, e⟩)]
      simp only [rStep, RegUpd.v_setV_self, RegUpd.gpr_write_self, BitVec.setWidth_eq, Nat.add_zero]
      exact (extract_setLane64 _ _ (i := 0) (j := 0) (by decide) (by decide)).trans (ite_eq_left rfl)
    | succ idx =>
      have ih := rRegs_lane L (i + 1) (rStep o i v g) hn.2 idx (by omega)
      rw [rStep_sp, rStep_mem, show i + 1 + idx = i + (idx + 1) by omega] at ih
      exact ih

end

end VG.Proof.Sha3.AArch64
