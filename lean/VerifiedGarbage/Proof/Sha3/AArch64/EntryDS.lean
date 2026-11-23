module

public import VerifiedGarbage.Proof.Sha3.AArch64.Entry
public import VerifiedGarbage.Impl.Sha3.AArch64.ViaD8
public import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
public import VerifiedGarbage.Proof.Sha3.AArch64.ViaD8At
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RelCT

/-!
# Calling a function with the addresses of several functions in registers (AArch64)

`Verified.entryDS`: `Verified.entryD8` for a function whose arguments need
not all fit the eight argument registers, and a list `L` of functions and the
registers that hold their addresses. `entryDS L name k body` copies the
caller's `k` stack words into the bottom of its frame, saves the return
address above them, then, for each function `n` and register `v` of `L`,
saves `v`'s low 64 bits and puts `n`'s address there (`saveRegs`), calls
`body`, and restores them (`restoreRegs`). The registers are distinct, and
`body` writes none of them (`Contract.dL`).
-/

-- separate module: the entry for functions with stack arguments or several functions' addresses,
-- which only some callers of `d8` functions need, apart from `Entry.lean`, which every one imports.

@[expose] public section

namespace VG.Proof.Sha3.AArch64

open VG VG.AArch64 VG.Impl.Sha3.AArch64 VG.Impl.StackScratch.AArch64

/-! ## Saving and restoring the registers -/

theorem copiedState_syms (b : Nat) (w : State) : ∀ m, (copiedState b w m).syms = w.syms
  | 0 => rfl
  | m + 1 => copiedState_syms b w m

theorem saveOff_ge (k : Nat) : 8 * k ≤ saveOff k := by unfold saveOff; omega

theorem saveOff_mod (k : Nat) : saveOff k % 8 = 0 := by unfold saveOff; omega

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

/-! ## The frame -/

section
variable (L : List (String × VReg)) (k : Nat) (s : State)

/-- The state after the frame's allocation and the copies of `k` stack words. -/
abbrev dCopied : State :=
  copiedState (frameDS k L.length) (baseState (allocated (frameDS k L.length) s)) k

/-- The state after the copies and the save of the return address. -/
abbrev dX : State :=
  { dCopied L k s with
    mem := (dCopied L k s).mem.write ((dCopied L k s).sp + BitVec.ofNat 64 (saveOff k)) 8 ((dCopied L k s).gpr .x30) }

/-- The state after the frame's allocation and `enterDS L k`. -/
def dSave : State := sRegs (saveOff k) 0 L (dX L k s)

/-- The address `off` bytes into the frame of `s`'s caller. -/
abbrev dslot (off : Nat) : Addr := s.sp - BitVec.ofNat 64 (frameDS k L.length) + BitVec.ofNat 64 off

theorem dCopied_sp : (dCopied L k s).sp = s.sp - BitVec.ofNat 64 (frameDS k L.length) := by
  rw [copiedState_sp]; rfl

theorem dX_sp : (dX L k s).sp = s.sp - BitVec.ofNat 64 (frameDS k L.length) := dCopied_sp L k s

@[simp] theorem dSave_sp : (dSave L k s).sp = s.sp - BitVec.ofNat 64 (frameDS k L.length) := by
  rw [dSave, sRegs_sp]; exact dX_sp L k s
@[simp] theorem dSave_rd : (dSave L k s).rd = s.rd := by
  rw [dSave, sRegs_rd]; show (dCopied L k s).rd = _; rw [copiedState_rd]; rfl
@[simp] theorem dSave_wr :
    (dSave L k s).wr = ⟨s.sp - BitVec.ofNat 64 (frameDS k L.length), frameDS k L.length⟩ :: s.wr := by
  rw [dSave, sRegs_wr]; show (dCopied L k s).wr = _; rw [copiedState_wr]; rfl
@[simp] theorem dSave_syms : (dSave L k s).syms = s.syms := by
  rw [dSave, sRegs_syms]; show (dCopied L k s).syms = _; rw [copiedState_syms]; rfl
@[simp] theorem dSave_dit : (dSave L k s).dit = s.dit := by
  rw [dSave, sRegs_dit]; show (dCopied L k s).dit = _; rw [copiedState_dit]; rfl

theorem dCopied_gpr {q : Reg} (h₁ : q ≠ .x16) (h₂ : q ≠ .x17) : (dCopied L k s).gpr q = s.gpr q := by
  rw [copiedState_gpr _ _ h₂, RegUpd.gpr_write_of_ne _ _ _ h₁]; rfl

theorem dSave_gpr {q : Reg} (h₁ : q ≠ .x16) (h₂ : q ≠ .x17) : (dSave L k s).gpr q = s.gpr q := by
  rw [dSave, sRegs_gpr _ h₁]; exact dCopied_gpr L k s h₁ h₂

theorem dCopied_v : (dCopied L k s).v = s.v := by rw [copiedState_v]; rfl

theorem dSave_v {q : VReg} (h : ∀ p ∈ L, p.2 ≠ q) : (dSave L k s).v q = s.v q := by
  rw [dSave, sRegs_v _ _ _ _ h]; show (dCopied L k s).v q = _; rw [dCopied_v]

theorem dSave_DL (hn : (L.map (·.2)).Nodup) : DL L (dSave L k s) := sRegs_DL _ L 0 _ hn

end

theorem saveOff_le_frameDS (k j : Nat) : saveOff k + 8 + 8 * j ≤ frameDS k j := by
  unfold frameDS; omega

theorem frameDS_mod16 (k j : Nat) : frameDS k j % 16 = 0 := by unfold frameDS saveOff; omega

theorem frameDS_mod (k j : Nat) : frameDS k j % 8 = 0 := by unfold frameDS saveOff; omega

theorem frameDS_pos (k j : Nat) : 0 < frameDS k j := by unfold frameDS; omega

theorem dslot_in (L : List (String × VReg)) (k : Nat) (s : State) {off : Nat}
    (h : off + 8 ≤ frameDS k L.length) (hE : frameDS k L.length < 4096) :
    InRegions (⟨s.sp - BitVec.ofNat 64 (frameDS k L.length), frameDS k L.length⟩ :: s.wr) (dslot L k s off) 8 :=
  ⟨_, List.mem_cons_self .., Offset.contains_base _ h (by omega)⟩

/-- A run of `enterDS L k` from the caller's state `s`, whose `k` stack
words are readable. -/
theorem enterDS_run (L : List (String × VReg)) (k : Nat) (s : State) (hE : frameDS k L.length < 4096)
    (hr : ∀ j < k, InRegions s.rd (stackArgAddr s j) 8) :
    execBlock isa (enterDS L k) (allocated (frameDS k L.length) s) =
      some (dSave L k s, copyTrace (frameDS k L.length) (s.sp - BitVec.ofNat 64 (frameDS k L.length)) k ++
        (.addr (dslot L k s (saveOff k)) ::
          regsTrace (saveOff k) (s.sp - BitVec.ofNat 64 (frameDS k L.length)) 0 L)) := by
  have hsk := saveOff_ge k
  have hle := saveOff_le_frameDS k L.length
  have hm := saveOff_mod k
  have e_add : exec (.addSp .x16 0) (allocated (frameDS k L.length) s) =
      some (baseState (allocated (frameDS k L.length) s)) := exec_addSp (by decide)
  have hc := copies_run (bytes := frameDS k L.length) (w := baseState (allocated (frameDS k L.length) s))
    (baseState_x16 _) (frameDS_mod k _) k (by omega)
    (fun j hj => by
      obtain ⟨R, hR, hcR⟩ := hr j hj
      refine ⟨R, List.mem_append_left _ hR, ?_⟩
      show R.Contains (s.sp - BitVec.ofNat 64 (frameDS k L.length) + BitVec.ofNat 64 (frameDS k L.length + 8 * j)) 8
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
      exact hcR)
    (fun j hj => dslot_in L k s (by omega) hE)
  have e_x30 : exec (.strSp .x30 (saveOff k)) (dCopied L k s) = some (dX L k s) :=
    exec_strSp' ⟨hm, by omega⟩ (by
      rw [copiedState_wr, dCopied_sp]; exact dslot_in L k s (by omega) hE)
  have hregs := saveRegs_run hm L 0 (dX L k s) (by omega) (fun idx h => by
    show InRegions (dCopied L k s).wr ((dX L k s).sp + _) 8
    rw [copiedState_wr, dX_sp]; exact dslot_in L k s (by omega) hE)
  rw [enterDS, execBlock_append, execBlock_cons_of e_add, hc]
  simp only [Option.map_some, Option.bind_some]
  rw [execBlock_cons_of e_x30, hregs]
  simp only [Option.map_some, addrs, List.map_cons, List.map_nil, List.nil_append, List.singleton_append,
    dCopied_sp]
  rfl

section
variable (L : List (String × VReg)) (k : Nat) (s : State)

theorem dslot_contains {off : Nat} (h : off + 8 ≤ frameDS k L.length) (hE : frameDS k L.length < 4096) :
    (below s.sp (frameDS k L.length)).Contains (dslot L k s off) 8 :=
  Offset.contains_base _ h (by omega)

theorem dX_mem : (dX L k s).mem = (dCopied L k s).mem.write (dslot L k s (saveOff k)) 8 (s.gpr .x30) := by
  show (dCopied L k s).mem.write ((dCopied L k s).sp + _) 8 ((dCopied L k s).gpr .x30) = _
  rw [dCopied_sp, dCopied_gpr L k s (by decide) (by decide)]

/-- The saves of the registers write only above the return address. -/
theorem dSave_regs_frame (hE : frameDS k L.length < 4096) :
    Frame [⟨dslot L k s (saveOff k + 8), 8 * L.length⟩] (dX L k s).mem (dSave L k s).mem := by
  have f := sRegs_frame (saveOff k) L 0 (dX L k s) (by have := saveOff_le_frameDS k L.length; omega)
  rw [dX_sp, Nat.mul_zero, Nat.add_zero] at f
  exact f

/-- The entry writes only its frame. -/
theorem dSave_frame (hE : frameDS k L.length < 4096) :
    Frame [below s.sp (frameDS k L.length)] s.mem (dSave L k s).mem := by
  have hsk := saveOff_ge k
  have hle := saveOff_le_frameDS k L.length
  obtain ⟨f, -⟩ := copiedState_mem (bytes := frameDS k L.length)
    (w := baseState (allocated (frameDS k L.length) s)) (baseState_x16 _) k (by omega) (by omega)
  have f₁ : Frame [below s.sp (frameDS k L.length)] s.mem (dX L k s).mem := by
    rw [dX_mem]
    refine Frame.write (Frame.sub f fun r hr => ?_) (List.mem_singleton_self _) _
      (dslot_contains L k s (by omega) hE)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
  refine Frame.trans f₁ (Frame.sub (dSave_regs_frame L k s hE) fun r hr => ?_)
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega)⟩

/-- The frame's bottom holds the caller's stack words. -/
theorem dSave_args (hE : frameDS k L.length < 4096) {j : Nat} (hj : j < k) :
    (dSave L k s).mem.readW (dslot L k s (8 * j)) 64 = s.mem.readW (stackArgAddr s j) 64 := by
  have hsk := saveOff_ge k
  have hle := saveOff_le_frameDS k L.length
  obtain ⟨-, hv⟩ := copiedState_mem (bytes := frameDS k L.length)
    (w := baseState (allocated (frameDS k L.length) s)) (baseState_x16 _) k (by omega) (by omega)
  rw [(dSave_regs_frame L k s hE).readW (r := ⟨dslot L k s (8 * j), 8⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
  rw [dX_mem]
  simp only [Mem.readW]
  rw [Mem.read_write_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
  have h := hv j hj
  simp only [Mem.readW] at h
  rw [show (baseState (allocated (frameDS k L.length) s)).sp = s.sp - BitVec.ofNat 64 (frameDS k L.length)
    from rfl] at h
  rw [h, stackArgAddr]
  show (s.mem.read _ (64 / 8)).setWidth 64 = _
  rw [show s.sp - BitVec.ofNat 64 (frameDS k L.length) + BitVec.ofNat 64 (frameDS k L.length + 8 * j) =
      s.sp + BitVec.ofNat 64 (8 * j) by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]]

theorem dSave_read_x30 (hE : frameDS k L.length < 4096) :
    (dSave L k s).mem.read (dslot L k s (saveOff k)) 8 = s.gpr .x30 := by
  have hle := saveOff_le_frameDS k L.length
  rw [(dSave_regs_frame L k s hE).read (r := ⟨dslot L k s (saveOff k), 8⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by decide),
    dX_mem, read_write_self]

theorem dSave_read_reg (hn : (L.map (·.2)).Nodup) (hE : frameDS k L.length < 4096) {idx : Nat}
    (h : idx < L.length) :
    (dSave L k s).mem.read (dslot L k s (saveOff k + 8 + 8 * idx)) 8 = laneOf s (L[idx]).2 0 := by
  have hle := saveOff_le_frameDS k L.length
  have r := sRegs_read (saveOff k) L 0 (dX L k s) hn (by omega) idx h
  rw [dX_sp, Nat.zero_add] at r
  rw [dSave, r]
  show ((dCopied L k s).v _).extractLsb' _ _ = _
  rw [dCopied_v]

end

/-- The state after `leaveDS L k`, from `g`. -/
def dRestore (L : List (String × VReg)) (k : Nat) (g : State) : State :=
  (rRegs (saveOff k) 0 L g).write .x .x30
    ((rRegs (saveOff k) 0 L g).mem.read ((rRegs (saveOff k) 0 L g).sp + BitVec.ofNat 64 (saveOff k)) 8)

theorem leaveDS_run {L : List (String × VReg)} {k : Nat} {g : State} (hE : frameDS k L.length < 4096)
    (hin : ∀ off, off + 8 ≤ frameDS k L.length → InRegions (g.rd ++ g.wr) (g.sp + BitVec.ofNat 64 off) 8) :
    execBlock isa (leaveDS L k) g =
      some (dRestore L k g, rTrace (saveOff k) g.sp 0 L ++ ([.addr (g.sp + BitVec.ofNat 64 (saveOff k))] : List Leak)) := by
  have hle := saveOff_le_frameDS k L.length
  have hm := saveOff_mod k
  have hr := restoreRegs_run (saveOff k) hm L 0 g (by omega) (fun idx h => hin _ (by omega))
  have hrd : (rRegs (saveOff k) 0 L g).rd ++ (rRegs (saveOff k) 0 L g).wr = g.rd ++ g.wr := by
    have : ∀ (L : List (String × VReg)) (i : Nat) (g : State),
        (rRegs (saveOff k) i L g).rd = g.rd ∧ (rRegs (saveOff k) i L g).wr = g.wr := by
      intro L
      induction L with
      | nil => intro i g; exact ⟨rfl, rfl⟩
      | cons p L ih => intro i g; exact ih (i + 1) _
    rw [(this L 0 g).1, (this L 0 g).2]
  have e := exec_ldrSp' (s := rRegs (saveOff k) 0 L g) (t := .x30) (off := saveOff k) ⟨hm, by omega⟩
    (by rw [hrd, rRegs_sp]; exact hin _ (by omega))
  rw [leaveDS, execBlock_append, hr]
  simp only [Option.bind_some]
  rw [execBlock_cons_of e]
  simp only [execBlock, Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil, rRegs_sp]
  rw [dRestore, rRegs_sp]

theorem dRestore_sp (L : List (String × VReg)) (k : Nat) (g : State) : (dRestore L k g).sp = g.sp :=
  rRegs_sp _ L 0 g

theorem dRestore_gpr {L : List (String × VReg)} {k : Nat} {g : State} {q : Reg} (h16 : q ≠ .x16)
    (h30 : q ≠ .x30) : (dRestore L k g).gpr q = g.gpr q := by
  rw [dRestore, RegUpd.gpr_write_of_ne _ _ _ h30, rRegs_gpr _ h16]

theorem dRestore_x30 (L : List (String × VReg)) (k : Nat) (g : State) :
    (dRestore L k g).gpr .x30 = g.mem.read (g.sp + BitVec.ofNat 64 (saveOff k)) 8 := by
  rw [dRestore, RegUpd.gpr_write_self, BitVec.setWidth_eq, rRegs_mem, rRegs_sp]

theorem dRestore_v {L : List (String × VReg)} {k : Nat} {g : State} {q : VReg} (h : ∀ p ∈ L, p.2 ≠ q) :
    (dRestore L k g).v q = g.v q := by
  rw [dRestore, RegUpd.v_write, rRegs_v _ _ _ _ h]

theorem dRestore_lane {L : List (String × VReg)} {k : Nat} {g : State} (hn : (L.map (·.2)).Nodup)
    {idx : Nat} (h : idx < L.length) :
    ((dRestore L k g).v (L[idx]).2).extractLsb' 0 64 =
      g.mem.read (g.sp + BitVec.ofNat 64 (saveOff k + 8 + 8 * idx)) 8 := by
  rw [dRestore, RegUpd.v_write, rRegs_lane _ L 0 g hn idx h, Nat.zero_add]

/-- The public data under `A.withFns ns`: that under `A`, and the functions'
addresses. -/
theorem pub_fnsL {sig : Sig} {A : Abi isa} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    {st : Nat} {f : String} {fs : List String} {s₁ s₂ : State}
    (h : (sig.contract (A.withFns (f :: fs)) pre post wa st leak).pub s₁ s₂) :
    (sig.contract A pre post wa st leak).pub s₁ s₂ ∧ ∀ g ∈ f :: fs, s₁.syms g = s₂.syms g := by
  simp only [Sig.contract, Abi.withFns] at h ⊢
  revert h
  split
  · exact fun h => h.elim
  · intro h
    cases leak with
    | none => exact ⟨⟨h.1.1, h.2⟩, h.1.2⟩
    | some g => exact ⟨⟨⟨h.1.1.1, h.1.2⟩, h.2⟩, h.1.1.2⟩

/-! ## The function's contract at its entry -/

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The state the function runs from, with the permissions of its contract:
after the call, with the caller's buffers and the copies of its stack words
in place of its argument area. -/
def eEntryDS (sig : Sig) (L : List (String × VReg)) (s : State) : State :=
  ((dSave L (nStack sig) s).callEntry).withRegions
    (((allRegions sig (dSave L (nStack sig) s).callEntry).filter (!·.2)).map (·.1))
    (((allRegions sig (dSave L (nStack sig) s).callEntry).filter (·.2)).map (·.1))

@[simp] theorem eEntryDS_sp (sig : Sig) (L : List (String × VReg)) (s : State) :
    (eEntryDS sig L s).sp = s.sp - BitVec.ofNat 64 (frameDS (nStack sig) L.length) := dSave_sp L _ s
@[simp] theorem eEntryDS_mem (sig : Sig) (L : List (String × VReg)) (s : State) :
    (eEntryDS sig L s).mem = (dSave L (nStack sig) s).mem := rfl
@[simp] theorem eEntryDS_syms (sig : Sig) (L : List (String × VReg)) (s : State) : (eEntryDS sig L s).syms = s.syms :=
  dSave_syms L _ s
@[simp] theorem eEntryDS_dit (sig : Sig) (L : List (String × VReg)) (s : State) : (eEntryDS sig L s).dit = s.dit :=
  dSave_dit L _ s

theorem eEntryDS_gpr (sig : Sig) (L : List (String × VReg)) (s : State) {q : Reg} (h : q ∉ linkRegs) :
    (eEntryDS sig L s).gpr q = s.gpr q := by
  rw [eEntryDS, State.withRegions_gpr, State.callEntry_gpr _ h]
  exact dSave_gpr L _ s (fun e => h (by rw [e]; decide)) (fun e => h (by rw [e]; decide))

theorem eEntryDS_DL (sig : Sig) (L : List (String × VReg)) (s : State) (hn : (L.map (·.2)).Nodup) :
    DL L (eEntryDS sig L s) := dSave_DL L _ s hn

theorem allRegions_eEntryDS (sig : Sig) (L : List (String × VReg)) (s : State) :
    allRegions sig (eEntryDS sig L s) = allRegions sig (dSave L (nStack sig) s).callEntry := rfl

/-- The function's arguments at its entry are the caller's. -/
theorem allArgs_eEntryDS (L : List (String × VReg)) (s : State) (hE : frameDS (nStack sig) L.length < 4096) :
    allArgs sig (eEntryDS sig L s) = allArgs sig s := by
  have h1 : (argRegs.take (sig.words abi.ptrBits).length).map (eEntryDS sig L s).gpr =
      (argRegs.take (sig.words abi.ptrBits).length).map s.gpr :=
    List.map_congr_left fun q hq => eEntryDS_gpr sig L s (argRegs_not_link q (List.mem_of_mem_take hq))
  have h2 : (List.range (nStack sig)).map (stackArg (eEntryDS sig L s)) =
      (List.range (nStack sig)).map (stackArg s) := List.map_congr_left fun j hj => by
    have hj' := List.mem_range.mp hj
    show (eEntryDS sig L s).mem.readW ((eEntryDS sig L s).sp + BitVec.ofNat 64 (8 * j)) 64 = _
    rw [eEntryDS_mem, eEntryDS_sp]
    exact dSave_args L _ s hE hj'
  rw [allArgs, allArgs, h1, h2]

/-- What the caller's precondition gives the entry. -/
theorem d_facts {L : List (String × VReg)} (hA : ArgsOk sig) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + frameDS (nStack sig) L.length) leak).pre s) :
    stack + frameDS (nStack sig) L.length ≤ s.sp.toNat ∧ s.sp.toNat + 8 * nStack sig ≤ 2 ^ 64 ∧
      (∀ j < nStack sig, InRegions s.rd (stackArgAddr s j) 8) ∧
      ∀ a ∈ allRegions sig s, (below s.sp (stack + frameDS (nStack sig) L.length)).Disjoint a.1 := by
  have hE := frameDS_pos (nStack sig) L.length
  rw [pre_args hA hl] at hs
  obtain ⟨⟨hst, hfit⟩, hrd, -, -, hres, -, -⟩ := hs
  have hsb : stack + frameDS (nStack sig) L.length ≤ s.sp.toNat := by rcases hst with h | h <;> omega
  refine ⟨hsb, hfit, fun j hj => ?_, fun a ha =>
    hres _ (by rw [stackBelow_pos _ (by omega)]; exact List.mem_singleton_self _) a ha⟩
  have h0 : nStack sig ≠ 0 := by omega
  have hmem : (⟨stackArgAddr s 0, 8 * nStack sig⟩, false) ∈ allRegions sig s := by
    simp [allRegions, argArea, h0]
  refine ⟨⟨stackArgAddr s 0, 8 * nStack sig⟩, ?_, ?_⟩
  · rw [hrd]; exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
  · simp only [stackArgAddr]
    exact Offset.contains _ (d := 8 * j) (n := 8) (e := 8 * 0) (k := 8 * nStack sig)
      (by omega) (by omega) (by omega)

/-- The function's regions at its entry: the caller's buffers, and the
copies. -/
theorem allRegions_eEntryDS' (L : List (String × VReg)) (s : State) (hE : frameDS (nStack sig) L.length < 4096) :
    allRegions sig (eEntryDS sig L s) = Sig.bufs sig.params (allArgs sig s) ++ argArea sig (eEntryDS sig L s) := by
  rw [allRegions, allArgs_eEntryDS L s hE]

/-- The copies lie in the stack below the caller's `sp` its contract reserves. -/
theorem argArea_eEntryDS_sub (L : List (String × VReg)) (s : State) :
    ∀ b ∈ argArea sig (eEntryDS sig L s), Region.Sub b.1 (below s.sp (stack + frameDS (nStack sig) L.length)) := by
  intro b hb
  unfold argArea at hb
  split at hb
  · cases hb
  · simp only [List.mem_singleton] at hb; subst hb
    have hsk := saveOff_ge (nStack sig)
    have hfs := saveOff_le_frameDS (nStack sig) L.length
    show Region.Sub ⟨stackArgAddr (eEntryDS sig L s) 0, 8 * nStack sig⟩ _
    rw [stackArgAddr, eEntryDS_sp, Nat.mul_zero, BitVec.add_zero]
    exact Offset.sub_below _ (by omega) (by omega)

/-- The caller's precondition gives the function's at its entry. -/
theorem d_bodyPre (hA : ArgsOk sig) (hl : Sig.noLists sig.params = true) {L : List (String × VReg)}
    (hE : frameDS (nStack sig) L.length < 4096)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + frameDS (nStack sig) L.length) leak).pre s) :
    (sig.contract abi pre post wa stack leak).pre (eEntryDS sig L s) := by
  obtain ⟨hsb, hfit, -, hout⟩ := d_facts hA hl hs
  have hF := frameDS_pos (nStack sig) L.length
  have hsk := saveOff_ge (nStack sig)
  have hfs := saveOff_le_frameDS (nStack sig) L.length
  rw [pre_args hA hl] at hs
  obtain ⟨-, -, -, hpw, -, hnw, hpr⟩ := hs
  have hbufs : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), (below s.sp (stack + frameDS (nStack sig) L.length)).Disjoint a.1 :=
    fun a ha => hout a (List.mem_append_left _ ha)
  refine (pre_args hA hl).mpr ⟨⟨.inr ?_, ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [eEntryDS_sp, toNat_sub_ofNat' (by omega)]; omega
  · rw [eEntryDS_sp, toNat_sub_ofNat' (by omega)]; omega
  · rw [allRegions_eEntryDS' L s hE]
    refine List.pairwise_append.mpr ⟨(List.pairwise_append.mp hpw).1, ?_, fun a ha b hb _ => ?_⟩
    · unfold argArea; split <;> simp
    · exact ((hbufs a ha).sub_left (argArea_eEntryDS_sub (stack := stack) L s b hb)).symm
  · intro r hr a ha
    rcases Nat.eq_zero_or_pos stack with h0 | h0
    · subst h0; simp [stackBelow] at hr
    rw [stackBelow_pos _ h0, List.mem_singleton] at hr; subst hr
    rw [allRegions_eEntryDS' L s hE] at ha
    rcases List.mem_append.mp ha with ha | ha
    · rw [eEntryDS_sp]
      exact (hbufs a ha).sub_left (by
        have := below_below s.sp (frameDS (nStack sig) L.length) stack
        exact this)
    · unfold argArea at ha
      split at ha
      · cases ha
      · simp only [List.mem_singleton] at ha; subst ha
        show (below (eEntryDS sig L s).sp stack).Disjoint ⟨stackArgAddr (eEntryDS sig L s) 0, 8 * nStack sig⟩
        rw [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
        exact (Offset.base_disjoint_below _ (by omega)).symm
  · rw [allArgs_eEntryDS L s hE]; exact hnw
  · rw [allArgs_eEntryDS L s hE, eEntryDS_mem]
    refine hpre _ _ _ (allArgs_length sig s) (fun b hb x hx => ?_) hpr
    refine (dSave_frame L _ s hE x fun R hR hc => ?_).symm
    simp only [List.mem_singleton] at hR; subst hR
    exact hbufs b hb x (below_sub (by omega) (by omega) x hc) hx

/-- The entry's memory is the caller's in the buffers. -/
theorem d_agree (hA : ArgsOk sig) (hl : Sig.noLists sig.params = true) (L : List (String × VReg))
    (hE : frameDS (nStack sig) L.length < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + frameDS (nStack sig) L.length) leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (allArgs sig s), ∀ x, b.1.Contains x 1 → (eEntryDS sig L s).mem x = s.mem x := by
  obtain ⟨hsb, -, -, hout⟩ := d_facts hA hl hs
  intro b hb x hx
  refine dSave_frame L _ s hE x fun R hR hc => ?_
  simp only [List.mem_singleton] at hR; subst hR
  exact hout b (List.mem_append_left _ hb) x (below_sub (by omega) (by omega) x hc) hx

/-- The caller's public data is the function's at its entry. -/
theorem d_bodyPub (hA : ArgsOk sig) (hl : Sig.noLists sig.params = true) (L : List (String × VReg))
    (hE : frameDS (nStack sig) L.length < 4096) {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + frameDS (nStack sig) L.length) leak).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + frameDS (nStack sig) L.length) leak).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + frameDS (nStack sig) L.length) leak).pub s₁ s₂)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak) :
    (sig.contract abi pre post wa stack leak).pub (eEntryDS sig L s₁) (eEntryDS sig L s₂) := by
  have ag₁ := d_agree hA hl L hE h₁
  have ag₂ := d_agree hA hl L hE h₂
  rw [pub_args hA hl] at hp ⊢
  obtain ⟨⟨⟨hsp, hdit⟩, hlk⟩, hpa⟩ := hp
  rw [allArgs_eEntryDS L s₁ hE, allArgs_eEntryDS L s₂ hE, eEntryDS_sp, eEntryDS_sp, hsp, eEntryDS_dit,
    eEntryDS_dit]
  refine ⟨⟨⟨rfl, hdit⟩, ?_⟩, hpa⟩
  cases leak with
  | none => trivial
  | some f =>
    show Curry.apply _ f (allArgs sig s₁) (eEntryDS sig L s₁).mem =
      Curry.apply _ f (allArgs sig s₂) (eEntryDS sig L s₂).mem
    rw [hleak _ _ _ (allArgs_length sig s₁) ag₁, hleak _ _ _ (allArgs_length sig s₂) ag₂]
    exact hlk

/-- What the run of the function leaves, from the caller's state `s`. -/
def AfterDS (sig : Sig) (L : List (String × VReg)) (post : sig.Post abi.ptrBits) (stack : Nat) (s c : State) :
    Prop :=
  c.wr = ⟨s.sp - BitVec.ofNat 64 (frameDS (nStack sig) L.length), frameDS (nStack sig) L.length⟩ :: s.wr ∧
  c.sp = s.sp - BitVec.ofNat 64 (frameDS (nStack sig) L.length) ∧
  (∀ q ∈ preserved, q ≠ .x30 → c.gpr q = s.gpr q) ∧
  (∀ q ∈ preservedV, (∀ p ∈ L, p.2 ≠ q) → (c.v q).extractLsb' 0 64 = (s.v q).extractLsb' 0 64) ∧
  c.mem.read (dslot L (nStack sig) s (saveOff (nStack sig))) 8 = s.gpr .x30 ∧
  (∀ idx (h : idx < L.length),
    c.mem.read (dslot L (nStack sig) s (saveOff (nStack sig) + 8 + 8 * idx)) 8 = laneOf s (L[idx]).2 0) ∧
  Frame (s.wr ++ [below s.sp (stack + frameDS (nStack sig) L.length)]) s.mem c.mem ∧
  Curry.apply (sig.words abi.ptrBits) post (allArgs sig s) s.mem c.mem ((c.gpr .x0).setWidth _)

/-- The function's regions at its entry are within the caller's and the frame. -/
theorem d_covers (hA : ArgsOk sig) (hl : Sig.noLists sig.params = true) (L : List (String × VReg))
    (hE : frameDS (nStack sig) L.length < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + frameDS (nStack sig) L.length) leak).pre s) :
    Covers (((allRegions sig (eEntryDS sig L s)).filter (!·.2)).map (·.1))
        (s.rd ++ ⟨s.sp - BitVec.ofNat 64 (frameDS (nStack sig) L.length), frameDS (nStack sig) L.length⟩ :: s.wr) ∧
      ∀ r ∈ ((allRegions sig (eEntryDS sig L s)).filter (·.2)).map (·.1), r ∈ s.wr := by
  have hsk := saveOff_ge (nStack sig)
  have hfs := saveOff_le_frameDS (nStack sig) L.length
  rw [pre_args hA hl] at hs
  obtain ⟨-, hrd, hwr, -, -, -, -⟩ := hs
  rw [allRegions_eEntryDS' L s hE]
  refine ⟨Covers.of_forall fun r hr => ?_, fun r hr => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf⟩ := List.mem_filter.mp ha
    rcases List.mem_append.mp ha with ha | ha
    · refine Covers.left (Covers.of_mem fun x hx => ?_)
      simp only [List.mem_singleton] at hx; subst hx
      rw [hrd]
      exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, hf⟩, rfl⟩
    · unfold argArea at ha
      split at ha
      · cases ha
      · simp only [List.mem_singleton] at ha; subst ha
        refine Covers.right (Covers.one ⟨_, List.mem_cons_self .., ?_⟩)
        show Region.Contains _ (stackArgAddr (eEntryDS sig L s) 0) _
        rw [stackArgAddr, eEntryDS_sp, Nat.mul_zero, BitVec.add_zero]
        exact Region.contains_self' (by omega)
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf⟩ := List.mem_filter.mp ha
    rcases List.mem_append.mp ha with ha | ha
    · rw [hwr]
      exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, hf⟩, rfl⟩
    · unfold argArea at ha
      split at ha
      · cases ha
      · simp only [List.mem_singleton] at ha; subst ha; simp at hf

/-- The call of the function, from a caller's state `s` whose precondition
holds, for code verified against a contract `kb` whose precondition holds at
its entry (`hentry`) and whose postcondition gives the function's (`hkb`). -/
theorem d_body_wpOf {L : List (String × VReg)} {name : String} {body : Prog isa} {kb : Contract isa}
    (hn : (L.map (·.2)).Nodup)
    (hv : ∀ s, kb.pre s → ∃ t s', Exec isa body s t s' ∧ abiPreserved s s' ∧ kb.post s s')
    (hkb : ∀ x y, kb.post x y → (sig.contract abi pre post wa stack leak).post x y)
    (hA : ArgsOk sig) (hl : Sig.noLists sig.params = true) (hE : frameDS (nStack sig) L.length < 4096)
    (hd : 16 * body.aarch64Depth ≤ stack)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    {s : State} (hs : (sig.contract abi pre post wa (stack + frameDS (nStack sig) L.length) leak).pre s)
    (hentry : kb.pre (eEntryDS sig L s)) :
    WP isa (.call name body) (dSave L (nStack sig) s) (AfterDS sig L post stack s) := by
  obtain ⟨hsb, hfit, -, hout⟩ := d_facts hA hl hs
  have hag := d_agree hA hl L hE hs
  obtain ⟨hcR, hcW⟩ := d_covers hA hl L hE hs
  have hF := frameDS_pos (nStack sig) L.length
  have hb := saveOff_le_frameDS (nStack sig) L.length
  have hsk := saveOff_ge (nStack sig)
  have hwrs : ∀ r ∈ ((allRegions sig (eEntryDS sig L s)).filter (·.2)).map (·.1),
      ∃ a ∈ allRegions sig s, a.1 = r := by
    intro r hr
    rw [pre_args hA hl] at hs
    have := hs.2.2.1 ▸ hcW r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp this
    exact ⟨a, (List.mem_filter.mp ha).1, rfl⟩
  -- The frame is apart from the writable buffers and the stack below it.
  have hap : ∀ x ∈ ((allRegions sig (eEntryDS sig L s)).filter (·.2)).map (·.1) ++
      [below (s.sp - BitVec.ofNat 64 (frameDS (nStack sig) L.length)) (16 * body.aarch64Depth)],
      (below s.sp (frameDS (nStack sig) L.length)).Disjoint x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨a, ha, rfl⟩ := hwrs x hx
      exact (hout a ha).sub_left (below_sub (by omega) (by omega))
    · simp only [List.mem_singleton] at hx; subst hx
      exact Offset.base_disjoint_below _ (by omega)
  refine WP.callFV (k := kb) hv (s := dSave L (nStack sig) s)
    (rd := ((allRegions sig (dSave L (nStack sig) s).callEntry).filter fun x : Region × Bool => !x.2).map
      fun x : Region × Bool => x.1)
    (wr := ((allRegions sig (dSave L (nStack sig) s).callEntry).filter fun x : Region × Bool => x.2).map
      fun x : Region × Bool => x.1) hentry
    (by rw [dSave_rd, dSave_wr]
        exact Covers.append_left hcR (Covers.right (Covers.of_mem fun x hx => List.mem_cons_of_mem _ (hcW x hx))))
    (by rw [dSave_wr]; exact Covers.of_mem fun x hx => List.mem_cons_of_mem _ (hcW x hx)) ?_ (by omega)
  intro c _ hwr hsp hfr hcs hvs hq
  rw [dSave_sp] at hfr hsp
  rw [dSave_wr] at hwr
  have hP : ∀ q ∈ preserved, q ≠ .x16 ∧ q ≠ .x17 := by decide
  refine ⟨hwr, hsp, fun q hq hq30 => (hcs q hq hq30).trans (dSave_gpr L _ s (hP q hq).1 (hP q hq).2),
    fun q hq hq8 => (hvs q hq).trans (by rw [dSave_v L _ s hq8]), ?_, ?_, ?_, ?_⟩
  · rw [hfr.read (dslot_contains L _ s (by omega) hE) hap (by decide), dSave_read_x30 L _ s hE]
  · intro idx hidx
    rw [hfr.read (dslot_contains L _ s (by omega) hE) hap (by decide), dSave_read_reg L _ s hn hE hidx]
  · refine Frame.trans (Frame.sub (dSave_frame L _ s hE) fun x hx => ?_) (Frame.sub hfr fun x hx => ?_)
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub (by omega) (by omega)⟩
    · rcases List.mem_append.mp hx with hx | hx
      · exact ⟨x, List.mem_append_left _ (hcW x hx), fun _ h => h⟩
      · simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
          fun y hy => below_sub (sp := s.sp) (a := 16 * body.aarch64Depth + frameDS (nStack sig) L.length)
            (b := stack + frameDS (nStack sig) L.length) (by omega) (by omega) y
            (below_below _ (frameDS (nStack sig) L.length) _ y hy)⟩
  · have hq' := hkb _ _ hq
    rw [post_args hA] at hq'
    rw [show (dSave L (nStack sig) s).callEntry.withRegions _ _ = eEntryDS sig L s from rfl,
      allArgs_eEntryDS L s hE, eEntryDS_mem, State.withRegions_mem, State.withRegions_gpr] at hq'
    exact hpost _ _ _ _ _ (allArgs_length sig s) (fun b hb x hx => hag b hb x hx) hq'

/-- A run of `entryDS L`, from the caller's state `s`, from the run of the
call of the function (`hb`): it keeps what the calling convention requires,
and its postcondition is the function's if that reads the memory on return
only within the buffers (`hout`). -/
theorem d_wp {L : List (String × VReg)} {name : String} {body : Prog isa} (hn : (L.map (·.2)).Nodup)
    (hA : ArgsOk sig) (hl : Sig.noLists sig.params = true)
    (hE : frameDS (nStack sig) L.length < 4096) {s : State}
    (hs : (sig.contract abi pre post wa (stack + frameDS (nStack sig) L.length) leak).pre s)
    (hb : WP isa (.call name body) (dSave L (nStack sig) s) (AfterDS sig L post stack s))
    (hout : ∀ m₁ m₂ x, (∀ b ∈ Sig.bufs sig.params (allArgs sig s), ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post (allArgs sig s) s.mem m₁ x →
        Curry.apply (sig.words abi.ptrBits) post (allArgs sig s) s.mem m₂ x) :
    WP isa (entryDS L name (nStack sig) body) s fun g =>
      abiPreserved s g ∧ (sig.contract abi pre post wa (stack + frameDS (nStack sig) L.length) leak).post s g := by
  obtain ⟨hsb, hfit, hr, hout'⟩ := d_facts hA hl hs
  have hF := frameDS_pos (nStack sig) L.length
  have hsk := saveOff_ge (nStack sig)
  have hfs := saveOff_le_frameDS (nStack sig) L.length
  refine WP.alloc ⟨hF, hE, frameDS_mod16 _ _⟩ (by omega) ?_
  refine WP.seq (WP.block ⟨_, enterDS_run L _ s hE hr, ?_⟩)
  refine WP.seq (WP.mono hb fun c hc => ?_)
  obtain ⟨hwrc, hspc, hcs, hvc, h0, h8, -, hq⟩ := hc
  have hin : ∀ off, off + 8 ≤ frameDS (nStack sig) L.length →
      InRegions (c.rd ++ c.wr) (c.sp + BitVec.ofNat 64 off) 8 := fun off h => by
    rw [hwrc, hspc]
    exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), Offset.contains_base _ h (by omega)⟩
  refine WP.block ⟨_, leaveDS_run hE hin, ?_⟩
  intro m u f
  refine ⟨⟨fun q hq => ?_, ?_, fun q hq => ?_⟩, ?_⟩
  · show (dRestore L (nStack sig) c).gpr q = s.gpr q
    by_cases hq30 : q = .x30
    · subst hq30; rw [dRestore_x30, hspc]; exact h0
    · rw [dRestore_gpr (fun e => by subst e; simp [preserved] at hq) hq30]
      exact hcs q hq hq30
  · show (dRestore L (nStack sig) c).sp + BitVec.ofNat 64 (frameDS (nStack sig) L.length) = s.sp
    rw [dRestore_sp, hspc, BitVec.sub_add_cancel]
  · show ((dRestore L (nStack sig) c).v q).extractLsb' 0 64 = (s.v q).extractLsb' 0 64
    by_cases hqL : ∃ p ∈ L, p.2 = q
    · obtain ⟨p, hp, rfl⟩ := hqL
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hp
      rw [dRestore_lane hn hidx, hspc]
      exact h8 idx hidx
    · rw [dRestore_v fun p hp e => hqL ⟨p, hp, e⟩]
      exact hvc q hq fun p hp e => hqL ⟨p, hp, e⟩
  · rw [post_args hA]
    show Curry.apply _ post (allArgs sig s) s.mem m (((dRestore L (nStack sig) c).gpr .x0).setWidth _)
    rw [dRestore_gpr (by decide) (by decide)]
    refine hout c.mem _ _ (fun b hb x hx => ?_) hq
    refine (congrFun (rRegs_mem _ L 0 c) x).symm.trans (f x fun R hR hc => ?_).symm
    simp only [List.mem_singleton] at hR; subst hR
    exact hout' b (List.mem_append_left _ hb) x (below_sub (by omega) (by omega) x hc) hx

/-- Two runs of the frame's body from callers' states `σ₁` and `σ₂` which
agree on `sp` leak the same, if the two calls of the function do (`hbody`). -/
theorem d_ct {L : List (String × VReg)} {name : String} {body : Prog isa} {σ₁ σ₂ : State} (hsp12 : σ₁.sp = σ₂.sp)
    (hE : frameDS (nStack sig) L.length < 4096)
    (hr₁ : ∀ j < nStack sig, InRegions σ₁.rd (stackArgAddr σ₁ j) 8)
    (hr₂ : ∀ j < nStack sig, InRegions σ₂.rd (stackArgAddr σ₂ j) 8)
    (hbody : RelCT isa (fun a b => a = dSave L (nStack sig) σ₁ ∧ b = dSave L (nStack sig) σ₂) (.call name body)
      fun c₁ c₂ => AfterDS sig L post stack σ₁ c₁ ∧ AfterDS sig L post stack σ₂ c₂) :
    RelCT isa (fun a b => a = allocated (frameDS (nStack sig) L.length) σ₁ ∧ b = allocated (frameDS (nStack sig) L.length) σ₂)
      (.seq (.block (enterDS L (nStack sig)))
        (.seq (.call name body) (.block (leaveDS L (nStack sig))))) fun _ _ => True := by
  have hsk := saveOff_ge (nStack sig)
  have hfs := saveOff_le_frameDS (nStack sig) L.length
  refine RelCT.seq (R := fun a b => a = dSave L (nStack sig) σ₁ ∧ b = dSave L (nStack sig) σ₂)
    (RelCT.block_of fun a b hab => ?_) ?_
  · obtain ⟨rfl, rfl⟩ := hab
    exact ⟨_, _, _, enterDS_run L _ σ₁ hE hr₁,
      by rw [enterDS_run L _ σ₂ hE hr₂]; simp only [dslot, hsp12], rfl, rfl⟩
  refine RelCT.seq (R := fun c₁ c₂ => AfterDS sig L post stack σ₁ c₁ ∧ AfterDS sig L post stack σ₂ c₂) hbody ?_
  refine RelCT.block_of fun g₁ g₂ hg => ?_
  obtain ⟨⟨hw₁, hs₁, -⟩, ⟨hw₂, hs₂, -⟩⟩ := hg
  have i₁ : ∀ off, off + 8 ≤ frameDS (nStack sig) L.length → InRegions (g₁.rd ++ g₁.wr) (g₁.sp + BitVec.ofNat 64 off) 8 :=
    fun off h => by
      rw [hw₁, hs₁]
      exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), Offset.contains_base _ h (by omega)⟩
  have i₂ : ∀ off, off + 8 ≤ frameDS (nStack sig) L.length → InRegions (g₂.rd ++ g₂.wr) (g₂.sp + BitVec.ofNat 64 off) 8 :=
    fun off h => by
      rw [hw₂, hs₂]
      exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), Offset.contains_base _ h (by omega)⟩
  refine ⟨_, dRestore L (nStack sig) g₂, _, leaveDS_run hE i₁, ?_, trivial⟩
  rw [leaveDS_run hE i₂, hs₁, hs₂, hsp12]

/-- **Code verified against `Contract.dL L` of a contract under `abi` with
`stack` bytes of stack, for a function with arguments on the stack, is
verified against the contract under `abi.withFns (L.map (·.1))` with `frameDS` more
bytes when called by `entryDS L`**: `Verified.entryD8` for any number of
arguments. -/
theorem Verified.entryDS {p₀ : String × VReg} {L' : List (String × VReg)} {name : String} {body : Prog isa}
    (h : Verified target body (Contract.dL (p₀ :: L') (sig.contract abi pre post wa stack leak)))
    (hn : ((p₀ :: L').map (·.2)).Nodup)
    (hl : Sig.noLists sig.params = true) (hE : frameDS (nStack sig) (p₀ :: L').length < 4096)
    (hd : 16 * body.aarch64Depth ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    (hpostR : ∀ vs m m₁ m₂ x, vs.length = (sig.words abi.ptrBits).length →
      (Sig.bufs sig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ x →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ x)
    (hsat : ∃ s, (sig.contract (abi.withFns ((p₀ :: L').map (·.1))) pre post wa (stack + frameDS (nStack sig) (p₀ :: L').length) leak).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (Impl.Sha3.AArch64.entryDS (p₀ :: L') name (nStack sig) body)
      (sig.contract (abi.withFns ((p₀ :: L').map (·.1))) pre post wa (stack + frameDS (nStack sig) (p₀ :: L').length) leak) := by
  have hA : ArgsOk sig := by
    obtain ⟨s, hs⟩ := hsat
    exact argsOk_of_pre (pre := pre) (post := post) (wa := wa) (leak := leak)
      (stack := stack + frameDS (nStack sig) (p₀ :: L').length) (s := s) hs
  have hout : ∀ s, (sig.contract abi pre post wa (stack + frameDS (nStack sig) (p₀ :: L').length) leak).pre s →
      ∀ m₁ m₂ x, (∀ b ∈ Sig.bufs sig.params (allArgs sig s), ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post (allArgs sig s) s.mem m₁ x →
        Curry.apply (sig.words abi.ptrBits) post (allArgs sig s) s.mem m₂ x := by
    intro s hs m₁ m₂ x hag hq
    have hpw := (List.pairwise_append.mp ((pre_args hA hl).mp hs).2.2.2.1).1
    exact hpostR _ _ _ _ _ (allArgs_length sig s) hpw hag hq
  have hbody : ∀ s, (sig.contract abi pre post wa (stack + frameDS (nStack sig) (p₀ :: L').length) leak).pre s →
      WP isa (.call name body) (dSave (p₀ :: L') (nStack sig) s) (AfterDS sig (p₀ :: L') post stack s) := fun s hs =>
    d_body_wpOf hn h.1 (fun _ _ h => h) hA hl hE hd hpost hs ⟨d_bodyPre hA hl hE hpre hs, eEntryDS_DL sig (p₀ :: L') s hn⟩
  refine ⟨fun s hs => ?_, ?_, hsat⟩
  · have hs' : (sig.contract abi pre post wa (stack + frameDS (nStack sig) (p₀ :: L').length) leak).pre s := hs
    obtain ⟨t, g, he, habi, hq⟩ := d_wp hn hA hl hE hs' (hbody s hs') (hout s hs')
    exact ⟨t, g, he, habi, hq⟩
  · refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.alloc (R := fun _ _ => True) ?_)
    refine RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => ?_
    by_cases hP0 :
        (sig.contract (abi.withFns ((p₀ :: L').map (·.1))) pre post wa (stack + frameDS (nStack sig) (p₀ :: L').length) leak).pre σ₁ ∧
        (sig.contract (abi.withFns ((p₀ :: L').map (·.1))) pre post wa (stack + frameDS (nStack sig) (p₀ :: L').length) leak).pre σ₂ ∧
        (sig.contract (abi.withFns ((p₀ :: L').map (·.1))) pre post wa (stack + frameDS (nStack sig) (p₀ :: L').length) leak).pub σ₁ σ₂
    swap
    · exact RelCT.of_false fun a b hab => hP0 hab.1
    obtain ⟨h₁, h₂, hp⟩ := hP0
    have h₁' : (sig.contract abi pre post wa (stack + frameDS (nStack sig) (p₀ :: L').length) leak).pre σ₁ := h₁
    have h₂' : (sig.contract abi pre post wa (stack + frameDS (nStack sig) (p₀ :: L').length) leak).pre σ₂ := h₂
    have hp₀ := (pub_fnsL hp).1
    have hsp12 : σ₁.sp = σ₂.sp := pub_args_sp hA hp₀
    obtain ⟨-, -, hr₁, -⟩ := d_facts hA hl h₁'
    obtain ⟨-, -, hr₂, -⟩ := d_facts hA hl h₂'
    refine RelCT.mono (P := fun a b => a = allocated (frameDS (nStack sig) (p₀ :: L').length) σ₁ ∧ b = allocated (frameDS (nStack sig) (p₀ :: L').length) σ₂)
      (d_ct (post := post) (stack := stack) hsp12 hE hr₁ hr₂ ?_) (fun a b hab => hab.2) (fun _ _ h => h)
    have hcov : ∀ σ : State, (sig.contract abi pre post wa (stack + frameDS (nStack sig) (p₀ :: L').length) leak).pre σ →
        Covers ((((allRegions sig (dSave (p₀ :: L') (nStack sig) σ).callEntry).filter fun x : Region × Bool => !x.2).map
            fun x : Region × Bool => x.1) ++
          (((allRegions sig (dSave (p₀ :: L') (nStack sig) σ).callEntry).filter fun x : Region × Bool => x.2).map
            fun x : Region × Bool => x.1))
          ((dSave (p₀ :: L') (nStack sig) σ).rd ++ (dSave (p₀ :: L') (nStack sig) σ).wr) ∧
        Covers (((allRegions sig (dSave (p₀ :: L') (nStack sig) σ).callEntry).filter fun x : Region × Bool => x.2).map
            fun x : Region × Bool => x.1) (dSave (p₀ :: L') (nStack sig) σ).wr := fun σ hσ => by
      obtain ⟨hcR, hcW⟩ := d_covers hA hl (p₀ :: L') hE hσ
      rw [dSave_rd, dSave_wr]
      exact ⟨Covers.append_left hcR (Covers.right (Covers.of_mem fun x hx => List.mem_cons_of_mem _ (hcW x hx))),
        Covers.of_mem fun x hx => List.mem_cons_of_mem _ (hcW x hx)⟩
    refine RelCT.mono (RelCT.wp (F₁ := AfterDS sig (p₀ :: L') post stack σ₁) (F₂ := AfterDS sig (p₀ :: L') post stack σ₂)
      (RelCT.callEx h.1 h.2.1 fun a b hab => ?_) fun a b hab => ?_) (fun _ _ h => h) (fun _ _ h => h.2)
    · obtain ⟨rfl, rfl⟩ := hab
      exact ⟨_, _, _, _, ⟨d_bodyPre hA hl hE hpre h₁', eEntryDS_DL sig (p₀ :: L') σ₁ hn⟩,
        ⟨d_bodyPre hA hl hE hpre h₂', eEntryDS_DL sig (p₀ :: L') σ₂ hn⟩,
        ⟨d_bodyPub hA hl (p₀ :: L') hE h₁' h₂' hp₀ hleak, by
          intro q hq
          show (eEntryDS sig (p₀ :: L') σ₁).syms q.1 = (eEntryDS sig (p₀ :: L') σ₂).syms q.1
          rw [eEntryDS_syms, eEntryDS_syms]; exact (pub_fnsL hp).2 q.1 (List.mem_map_of_mem hq)⟩,
        (hcov σ₁ h₁').1, (hcov σ₁ h₁').2, (hcov σ₂ h₂').1, (hcov σ₂ h₂').2⟩
    · obtain ⟨rfl, rfl⟩ := hab
      exact ⟨hbody σ₁ h₁', hbody σ₂ h₂'⟩

open VG.AArch64.Scrub VG.Impl.Scrub.AArch64 in
theorem keptG_clearDL (L : List (String × VReg)) : keptG (clearDL L) = [] :=
  (by decide : allGprs.filter (fun q => !allGprs.contains q) = [])

open VG.AArch64.Scrub VG.Impl.Scrub.AArch64 in
/-- `sideI` of the cleanup `clearDL L` holds of an instruction that writes no
vector register or PSTATE.DIT: `clearDL` clears every general-purpose
register. -/
theorem sideI_clearDL_of (L : List (String × VReg)) {i : Instr} (hd : vdstOf i = none)
    (hw : i.writesDit = false) :
    sideI (RegSet.ofList (keptG (clearDL L))) (RegSet.ofList (keptV (clearDL L))) i = true := by
  have hg := keptG_clearDL L
  simp only [sideI, hw, hg, keeps_ofList, List.all_nil, vkeeps, hd, Bool.not_false, Bool.and_self]

open VG.AArch64.Scrub VG.Impl.Scrub.AArch64 in
/-- `sideI` of the cleanup `clearDL L` holds of the write of the low half of a
register `L` gives: `clearDL` clears its high half. -/
theorem sideI_clearDL_ins {L : List (String × VReg)} {v : VReg} (hv : v ∈ L.map (·.2)) :
    sideI (RegSet.ofList (keptG (clearDL L))) (RegSet.ofList (keptV (clearDL L)))
      (.vop (.ins .d2 v 0 .x16)) = true := by
  have hg := keptG_clearDL L
  have hm : (RegSet.ofList (keptV (clearDL L))).mem v = false := by
    cases h : (RegSet.ofList (keptV (clearDL L))).mem v with
    | false => rfl
    | true =>
      have h' := RegSet.mem_ofList.mp h
      simp only [keptV, clearDL, List.mem_append, List.mem_filter, Bool.not_eq_true',
        List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq] at h'
      rcases h' with ⟨h1, h2⟩ | ⟨-, h2⟩
      · exact (h2 v h1 rfl).elim
      · exact (h2 v hv rfl).elim
  simp only [sideI, hg, keeps_ofList, List.all_nil, vkeeps, vdstOf, VOp.dst, hm, Bool.not_false,
    Bool.and_true]
  rfl

open VG.AArch64.Scrub VG.Impl.Scrub.AArch64 in
/-- `sideI` of the cleanup `clearDL L` holds of each instruction of
`saveRegs o i L'` for `L'` a part of `L`. -/
theorem sideI_saveRegs {L : List (String × VReg)} (o : Nat) :
    ∀ (i : Nat) (L' : List (String × VReg)), (∀ p ∈ L', p.2 ∈ L.map (·.2)) →
      ∀ x ∈ saveRegs o i L',
        sideI (RegSet.ofList (keptG (clearDL L))) (RegSet.ofList (keptV (clearDL L))) x = true
  | _, [], _, x, hx => by cases hx
  | i, (n, v) :: L', hL, x, hx => by
    simp only [saveRegs, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | rfl | hx
    · exact sideI_clearDL_of L rfl rfl
    · exact sideI_clearDL_of L rfl rfl
    · exact sideI_clearDL_of L rfl rfl
    · exact sideI_clearDL_ins (hL _ List.mem_cons_self)
    · exact sideI_saveRegs o (i + 1) L' (fun p hp => hL p (List.mem_cons_of_mem _ hp)) x hx

open VG.AArch64.Scrub VG.Impl.Scrub.AArch64 in
/-- `sideI` of the cleanup `clearDL L` holds of each instruction of
`restoreRegs o i L'` for `L'` a part of `L`. -/
theorem sideI_restoreRegs {L : List (String × VReg)} (o : Nat) :
    ∀ (i : Nat) (L' : List (String × VReg)), (∀ p ∈ L', p.2 ∈ L.map (·.2)) →
      ∀ x ∈ restoreRegs o i L',
        sideI (RegSet.ofList (keptG (clearDL L))) (RegSet.ofList (keptV (clearDL L))) x = true
  | _, [], _, x, hx => by cases hx
  | i, (n, v) :: L', hL, x, hx => by
    simp only [restoreRegs, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact sideI_clearDL_of L rfl rfl
    · exact sideI_clearDL_ins (hL _ List.mem_cons_self)
    · exact sideI_restoreRegs o (i + 1) L' (fun p hp => hL p (List.mem_cons_of_mem _ hp)) x hx

open VG.AArch64.Scrub VG.Impl.Scrub.AArch64 in
/-- `scrubSide` of a function with `k` stack words that calls `F`, made to
call each function `L` names by the register it pairs it with, by
`entryDS L`, with the cleanup `clearDL L` over `frameDS k L.length` more
bytes, from `F`'s with the cleanup that leaves the callee-saved halves: with
`L`'s functions those of a table. -/
theorem scrubSide_entryDS {L : List (String × VReg)} {core : String} {k : Nat} {F : Prog isa} {W rb : Nat}
    (hs : scrubSide F W rb ⟨allGprs, allVecs, []⟩ [] = true) (hW : 0 < W)
    (hW' : W + frameDS k L.length < 4096) (hwf : wfB (clearDL L) = true) :
    scrubSide (entryDS L core k (Code.viaDAt L F)) (W + frameDS k L.length) rb (clearDL L)
      [("", [⟨"", "", L.map (·.1), []⟩])] = true := by
  obtain ⟨hc, -⟩ := of_side hs hW
  have hWF : W + frameDS k L.length ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.add_pos_left hW _)
  have h16 := frameDS_mod16 k L.length
  have hLL : ∀ p ∈ L, p.2 ∈ L.map (·.2) := fun p hp => List.mem_map_of_mem hp
  simp only [scrubSide, Nat.pos_iff_ne_zero.mp hW, hWF, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hs ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨-, h2⟩, h3⟩, -⟩, h5⟩, -⟩, h7⟩, -⟩ := hs
  refine ⟨⟨⟨⟨⟨⟨⟨hW', by rw [Nat.add_mod, h2, h16]⟩, ?_⟩, ?_⟩, h5⟩, hwf⟩, ?_⟩, ?_⟩
  · simp only [entryDS, Code.aarch64Depth, depth_viaDAt, Instr.frameUnits, Nat.zero_max, Nat.max_zero]
    rw [Nat.mul_add, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h16)]
    exact Nat.add_le_add_right h3 _
  · unfold tablesCall
    rw [List.all_eq_true]
    intro f hf
    simp only [entryDS, inames, List.nil_append, List.append_nil] at hf
    have := inames_viaDAt (L := L) hc f hf
    simp [tableFns, this]
  · rw [Code.allInstrs_eq, List.all_eq_true] at h7 ⊢
    intro i hi
    simp only [entryDS, enterDS, leaveDS, instrs, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false, List.cons_append, or_assoc] at hi
    rcases hi with rfl | rfl | hi | rfl | hi | hi | hi | rfl | rfl
    · rfl
    · exact sideI_clearDL_of L rfl rfl
    · obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hi
      simp only [copyArg, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact sideI_clearDL_of L rfl rfl
      · exact sideI_clearDL_of L rfl rfl
    · exact sideI_clearDL_of L rfl rfl
    · exact sideI_saveRegs _ 0 L hLL i hi
    · rcases instrs_viaDAt L F hi with h | ⟨p, -, rfl⟩ | rfl
      · exact sideI_mono (fun q hq => hq) (fun w hw => by
          simp only [keptV, clearDL, List.mem_append, List.mem_filter] at hw ⊢
          rcases hw with ⟨h1, h2⟩ | ⟨h1, -⟩
          · exact .inl ⟨h1, h2⟩
          · exact .inr ⟨h1, rfl⟩) (h7 i h)
      · exact sideI_clearDL_of L rfl rfl
      · exact sideI_clearDL_of L rfl rfl
    · exact sideI_restoreRegs _ 0 L hLL i hi
    · exact sideI_clearDL_of L rfl rfl
    · rfl
  · rw [keptG_clearDL]; exact Bool.or_eq_true_iff.mpr (.inr (by decide))

end


end VG.Proof.Sha3.AArch64
