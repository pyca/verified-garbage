import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# Registers restored from a vector lane, on AArch64

A function that saves a register `r` in a 64-bit lane of a vector register
(`ins vd.d[l], r`) and restores it from there (`umov r, vd.d[l]`) keeps
`r`, whatever else it does to it in between, if nothing else writes `r`
before the save or after the restore, nor that lane in between
(`restores_ok`). `restores` checks it of a list of instructions by
evaluation, and `straight` gives the instructions of straight-line code, so
that a caller can check that the functions it calls keep the callee-saved
registers it does not save itself (`Proof/Ecdsa/AArch64/Abi.lean`).
-/

namespace VG.AArch64

/-- Whether `i` writes no register but those of `dstOf`, other than `r`. -/
def keepsReg (r : Reg) (i : Instr) : Bool := (dstOf i).all (· != r)

/-- Whether `i` keeps lane `l` (64 bits) of `v`: it writes another vector
register, or another lane of `v` by `ins`. -/
def keepsLane (v : VReg) (l : Nat) : Instr → Bool
  | .vop (.ins .d2 d l' _) => d != v || l' != l
  | i => (vdstOf i).all (· != v)

/-- After the save of `r` in lane `l` of `v`: the lane is kept until `r` is
restored from it, and `r` is kept after. -/
def restoresMid (r : Reg) (v : VReg) (l : Nat) : List Instr → Bool
  | [] => false
  | i :: is =>
    match i with
    | .umov .x r' v' l' =>
      if r' = r ∧ v' = v ∧ l' = l then is.all (keepsReg r) else keepsLane v l i && restoresMid r v l is
    | _ => keepsLane v l i && restoresMid r v l is

/-- Whether instructions keep `r`: it is kept until it is saved in a lane,
which is kept until `r` is restored from it, and `r` is kept after; or it is
kept throughout. -/
def restores (r : Reg) : List Instr → Bool
  | [] => true
  | i :: is =>
    match i with
    | .vop (.ins .d2 v l r') =>
      if r' = r ∧ l < 2 then restoresMid r v l is else restores r is
    | _ => keepsReg r i && restores r is

/-- The instructions of straight-line code (blocks one after the other). -/
def straight : Prog isa → Option (List Instr)
  | .block is => some is
  | .seq a b => (straight a).bind fun x => (straight b).map (x ++ ·)
  | _ => none

theorem straight_exec : ∀ {c : Prog isa} {is : List Instr}, straight c = some is →
    ∀ {s s' : State} {t : List Leak}, Exec isa c s t s' → ∃ t', execBlock isa is s = some (s', t')
  | .block is, is', h, s, s', t, e => by
    simp only [straight, Option.some.injEq] at h; subst h
    cases e with
    | block b => exact ⟨t, b⟩
  | .seq a b, is, h, s, s', t, e => by
    simp only [straight, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    cases e with
    | seq e₁ e₂ =>
      obtain ⟨t₁, b₁⟩ := straight_exec hx e₁
      obtain ⟨t₂, b₂⟩ := straight_exec hy e₂
      exact ⟨t₁ ++ t₂, by rw [execBlock_append, b₁]; simp [b₂]⟩
  | .ite _ _ _, _, h, _, _, _, _ => by simp [straight] at h
  | .loop _ _, _, h, _, _, _, _ => by simp [straight] at h
  | .call _ _, _, h, _, _, _, _ => by simp [straight] at h
  | .frame _ _ _, _, h, _, _, _, _ => by simp [straight] at h

/-- A run of instructions that keep `r` keeps it. -/
theorem keepsReg_ok {r : Reg} : ∀ {is : List Instr}, is.all (keepsReg r) = true →
    ∀ {s s' : State} {t : List Leak}, execBlock isa is s = some (s', t) → s'.gpr r = s.gpr r := by
  intro is h s s' t e
  refine execBlock_keep (fun s : State => s.gpr r) (ok := fun i => keepsReg r i = true)
    (fun hi he => exec_gpr ?_ he) (List.all_eq_true.mp h) e
  intro hd
  simp only [keepsReg, hd, Option.all_some, bne_self_eq_false] at hi
  exact absurd hi (by decide)

/-- The lane `l` of `v`. -/
abbrev laneOf (s : State) (v : VReg) (l : Nat) : BitVec 64 := (s.v v).extractLsb' (64 * l) 64

theorem extract_setLane64 (x : BitVec 128) (y : BitVec 64) {i j : Nat} (hi : i < 2) (hj : j < 2) :
    (setLane x 64 i y).extractLsb' (64 * j) 64 = if i = j then y else x.extractLsb' (64 * j) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;>
    simp only [setLane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
      hk, decide_true, Bool.true_and, ite_true, ite_false, Nat.mul_zero, Nat.mul_one,
      Nat.sub_zero, reduceCtorEq] <;>
    (have h1 : k < 128 := by omega
     have h2 : 64 + k < 128 := by omega
     have h3 : ¬ 64 + k < 64 := by omega
     simp [h1, h2, h3, hk])

/-- An instruction that keeps lane `l` of `v` keeps it. -/
theorem keepsLane_ok {v : VReg} {l : Nat} (hl : l < 2) {i : Instr} (h : keepsLane v l i = true)
    {s s' : State} (he : exec i s = some s') : laneOf s' v l = laneOf s v l := by
  unfold keepsLane at h
  split at h
  · rename_i d l' n
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at h
    simp only [exec, VOp.eval] at he
    split at he
    · rename_i hl'
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      by_cases hd : d = v
      · subst hd
        have hll : l' ≠ l := h.resolve_left (fun h' => h' rfl)
        simp only [laneOf, RegUpd.v_setV, ite_true]
        rw [extract_setLane64 _ _ hl' hl]; simp [hll]
      · simp only [laneOf, RegUpd.v_setV, Ne.symm hd, ite_false]
    · simp at he
  · rename_i hne
    have : vdstOf i ≠ some v := fun hd => by simp [hd] at h
    simp only [laneOf, exec_vec this he]

theorem restoresMid_ok {r : Reg} {v : VReg} {l : Nat} (hl : l < 2) :
    ∀ {is : List Instr}, restoresMid r v l is = true →
    ∀ {s s' : State} {t : List Leak}, execBlock isa is s = some (s', t) → s'.gpr r = laneOf s v l
  | [], h, _, _, _, _ => by simp [restoresMid] at h
  | i :: is, h, s, s', t, e => by
    simp only [execBlock] at e
    split at e <;> [cases e; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at e
    obtain ⟨⟨s₂, t₂⟩, e₂, heq⟩ := e
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    have mid : (keepsLane v l i && restoresMid r v l is) = true → s₂.gpr r = laneOf s v l := fun h' => by
      simp only [Bool.and_eq_true] at h'
      rw [restoresMid_ok hl h'.2 e₂, keepsLane_ok hl h'.1 he]
    unfold restoresMid at h
    split at h
    · rename_i r' v' l'
      split at h
      · rename_i hrvl
        obtain ⟨rfl, rfl, rfl⟩ := hrvl
        rw [keepsReg_ok h e₂]
        simp only [exec, Size.bits] at he
        split at he
        · simp only [Option.some.injEq] at he; subst he
          simp [State.write, laneOf, Nat.mul_comm]
        · cases he
      · exact mid h
    · exact mid h

/-- Instructions that `restores` accepts keep `r`. -/
theorem restores_ok {r : Reg} : ∀ {is : List Instr}, restores r is = true →
    ∀ {s s' : State} {t : List Leak}, execBlock isa is s = some (s', t) → s'.gpr r = s.gpr r
  | [], _, _, _, _, e => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e; rw [e.1]
  | i :: is, h, s, s', t, e => by
    simp only [execBlock] at e
    split at e <;> [cases e; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at e
    obtain ⟨⟨s₂, t₂⟩, e₂, heq⟩ := e
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    unfold restores at h
    split at h
    · rename_i v l r'
      split at h
      · rename_i hr
        obtain ⟨rfl, hl⟩ := hr
        rw [restoresMid_ok hl h e₂]
        simp only [exec, VOp.eval, hl, ite_true, Option.map_some, Option.some.injEq] at he
        subst he
        simp only [laneOf, RegUpd.v_setV, ite_true]
        rw [extract_setLane64 _ _ hl hl]; simp
      · rw [restores_ok h e₂, exec_gpr (by simp [dstOf]) he]
    · simp only [Bool.and_eq_true] at h
      rw [restores_ok h.2 e₂, exec_gpr ?_ he]
      intro hd
      simp only [keepsReg, hd, Option.all_some, bne_self_eq_false] at h
      exact absurd h.1 (by decide)

end VG.AArch64
