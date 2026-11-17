module

public import VerifiedGarbage.Proof.Camellia.Words
public import VerifiedGarbage.Proof.Camellia.Arm.Round
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Camellia.Arm.Fl`, which this module and modules that import it used -/

section

/-!
# FL and FLINV on ARMv7

The two steps of FL (`flRot`, `flOr`) AND and OR the planes with the
subkey's, so they are not linear, and are run symbolically: one plane's
instructions for any plane (`flRotStep_ok`, `flOrStep_ok`), composed by
induction over the planes. The left word is in the state registers
throughout; the right word stays in its slots.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 kp ldS stS eorR andR rorOp)

/-! ## Instructions on slots and the table -/

theorem slot_in {s : State} (hok : Ok layerCfg s) {k : Nat} (hk : k < keySlot) :
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr sb + BitVec.ofNat 32 (4 * k))) 4 := by
  obtain ⟨r, hr, hc⟩ := hok.slotIn k hk
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem exec_ldS {s : State} (hok : Ok layerCfg s) {r : Reg} {k : Nat} (hk : k < keySlot) :
    exec (ldS r k) s = some (s.setReg r (slotW s k)) :=
  exec_ldr (by simp [keySlot] at hk; omega_arith) (slot_in hok hk)

theorem exec_stS {s : State} (hok : Ok layerCfg s) {r : Reg} {k : Nat} (hk : k < keySlot) :
    exec (stS k r) s = some { s with mem := s.mem.writeW (wordAddr (s.gpr sb) k) (s.gpr r) } :=
  exec_str (by simp [keySlot] at hk; omega_arith) (hok.slotIn k hk)

theorem exec_ldK {s : State} (hok : Ok layerCfg s) {r : Reg} {w : Nat} (hw : w < 32) :
    exec (.ldr r kp (4 * w)) s = some (s.setReg r (keyW s w)) :=
  exec_ldr (by omega_arith) (hok.extIn w hw)

theorem exec_dp_reg {s : State} {op : DpOp} {d n m : Reg} :
    exec (.dp op d n (.reg m)) s = some (s.setReg d (match op with
      | .add => s.gpr n + s.gpr m | .sub => s.gpr n - s.gpr m | .and => s.gpr n &&& s.gpr m
      | .orr => s.gpr n ||| s.gpr m | .eor => s.gpr n ^^^ s.gpr m | .bic => s.gpr n &&& ~~~(s.gpr m))) := by
  cases op <;> rfl

theorem exec_eor_ror {s : State} {d n m : Reg} {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ 31) :
    exec (.dp .eor d n (rorOp m k)) s = some (s.setReg d (s.gpr n ^^^ (s.gpr m).rotateRight k)) := by
  simp only [exec, rorOp, Op2.eval, h1, h2, and_self, ite_true, Option.map_some]

/-- Ok survives a write of a register but `sb` and `kp`, and of memory. -/
theorem ok_setReg {s : State} (h : Ok layerCfg s) {r : Reg} (x : BitVec 32) (h1 : r ≠ sb) (h2 : r ≠ kp) :
    Ok layerCfg (s.setReg r x) :=
  h.congr (RegUpd.gpr_setReg_of_ne s x (Ne.symm h1)) (RegUpd.gpr_setReg_of_ne s x (Ne.symm h2)) rfl rfl

theorem ok_setMem {s : State} (h : Ok layerCfg s) (m : Mem) : Ok layerCfg { s with mem := m } :=
  h.congr rfl rfl rfl rfl

theorem slotW_setReg (s : State) {r : Reg} (x : BitVec 32) (h : r ≠ sb) (k : Nat) :
    slotW (s.setReg r x) k = slotW s k := by
  simp only [slotW, RegUpd.mem_setReg, RegUpd.gpr_setReg_of_ne s x (Ne.symm h)]

/-! Running a block one instruction at a time. -/

theorem run_ldS {u : State} (hu : Ok layerCfg u) {r : Reg} {k : Nat} (hk : k < keySlot) (is : List Instr) :
    runBlock isa (ldS r k :: is) u = runBlock isa is (u.setReg r (slotW u k)) := by
  rw [runBlock_cons, exec_ldS hu hk, runStep_some]

theorem run_ldK {u : State} (hu : Ok layerCfg u) {r : Reg} {w : Nat} (hw : w < 32) (is : List Instr) :
    runBlock isa (.ldr r kp (4 * w) :: is) u = runBlock isa is (u.setReg r (keyW u w)) := by
  rw [runBlock_cons, exec_ldK hu hw, runStep_some]

theorem run_stS {u : State} (hu : Ok layerCfg u) {r : Reg} {k : Nat} (hk : k < keySlot) (is : List Instr) :
    runBlock isa (stS k r :: is) u =
      runBlock isa is { u with mem := u.mem.writeW (wordAddr (u.gpr sb) k) (u.gpr r) } := by
  rw [runBlock_cons, exec_stS hu hk, runStep_some]

theorem run_and {u : State} {d n m : Reg} (is : List Instr) :
    runBlock isa (.dp .and d n (.reg m) :: is) u = runBlock isa is (u.setReg d (u.gpr n &&& u.gpr m)) := by
  rw [runBlock_cons, exec_dp_reg, runStep_some]

theorem run_orr {u : State} {d n m : Reg} (is : List Instr) :
    runBlock isa (.dp .orr d n (.reg m) :: is) u = runBlock isa is (u.setReg d (u.gpr n ||| u.gpr m)) := by
  rw [runBlock_cons, exec_dp_reg, runStep_some]

theorem run_eor {u : State} {d n m : Reg} (is : List Instr) :
    runBlock isa (.dp .eor d n (.reg m) :: is) u = runBlock isa is (u.setReg d (u.gpr n ^^^ u.gpr m)) := by
  rw [runBlock_cons, exec_dp_reg, runStep_some]

theorem run_eor_ror {u : State} {d n m : Reg} {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ 31) (is : List Instr) :
    runBlock isa (.dp .eor d n (rorOp m k) :: is) u =
      runBlock isa is (u.setReg d (u.gpr n ^^^ (u.gpr m).rotateRight k)) := by
  rw [runBlock_cons, exec_eor_ror h1 h2, runStep_some]

/-- A store to slot `k` keeps the other slots below the table. -/
theorem slot_writeW {s : State} (hok : Ok layerCfg s) {k k' : Nat} (hk : k < keySlot) (hk' : k' < keySlot)
    (hne : k' ≠ k) (v : BitVec 32) :
    (s.mem.writeW (wordAddr (s.gpr sb) k) v).readW (wordAddr (s.gpr sb) k') 32 = slotW s k' := by
  have := hok.slots
  simp only [layerCfg, keySlot] at this hk hk'
  exact Mem.readW_writeW_sep (slot_sep _ (by omega_arith) (by omega_arith) hne) (by decide)

theorem slot_writeW_self {s : State} (k : Nat) (v : BitVec 32) :
    (s.mem.writeW (wordAddr (s.gpr sb) k) v).readW (wordAddr (s.gpr sb) k) 32 = v :=
  Mem.readW_writeW_self32 _ _ _

/-- A store to slot `k` keeps the table's words at `kp`. -/
theorem key_writeW {s : State} (hok : Ok layerCfg s) {k w : Nat} (hk : k < keySlot) (hw : w < 32)
    (v : BitVec 32) :
    (s.mem.writeW (wordAddr (s.gpr sb) k) v).readW (wordAddr (s.gpr kp) w) 32 = keyW s w := by
  have h := hok.sep k hk w hw
  exact Mem.readW_writeW_sep (fun x h1 h2 => h x h2 h1) (by decide)

theorem exec_stS_frame {s : State} (hok : Ok layerCfg s) {k : Nat} (hk : k < keySlot) (v : BitVec 32) :
    Frame [slotRegion layerCfg s] s.mem (s.mem.writeW (wordAddr (s.gpr sb) k) v) := by
  have := hok.slots
  refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
  simp only [slotRegion, layerCfg]
  exact slot_contains _ hk this

/-! ## One plane of each step -/

/-- The rotation step's new right plane `j`: the AND of plane `j - 1` of the
left word and the subkey's, rotated by a byte for plane 0. -/
def rotV (L K : Nat → BitVec 32) (j : Nat) : BitVec 32 :=
  let v := K ((j + 7) % 8) &&& L ((j + 7) % 8)
  if j = 0 then v.rotateRight 8 else v

theorem q_ne (i : Nat) : q i ≠ t0 ∧ q i ≠ t1 ∧ q i ≠ sb ∧ q i ≠ kp := by
  unfold q; split <;> decide

theorem q_mem (i : Nat) : q i ∈ layerWrites := by unfold q; split <;> decide

theorem q_inj : ∀ i < 8, ∀ j < 8, q i = q j → i = j := by decide

theorem itePos {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a :=
  by simp only [h, ↓reduceIte]

theorem iteNeg {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b :=
  by simp only [h, ↓reduceIte]

/-- What a register write keeps. -/
structure Keeps (s s' : State) (d : Reg) : Prop where
  ok : Ok layerCfg s → Ok layerCfg s'
  gpr : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem keeps_setReg (s : State) {d : Reg} (x : BitVec 32) (h1 : d ≠ sb) (h2 : d ≠ kp) :
    Keeps s (s.setReg d x) d :=
  ⟨fun h => ok_setReg h x h1 h2, fun _ h => RegUpd.gpr_setReg_of_ne _ _ h, rfl, rfl, rfl, rfl⟩

theorem Keeps.slotW {s s' : State} {d : Reg} (h : Keeps s s' d) (hd : d ≠ sb) (k : Nat) :
    slotW s' k = slotW s k := by
  simp only [Arm.slotW, h.mem, h.gpr sb (Ne.symm hd)]

theorem flRotStep_ok {s : State} (hok : Ok layerCfg s) {d off j : Nat}
    (hk : d + 8 + j < keySlot) (hw : off + 8 ≤ 32) :
    ∃ s', runBlock isa (flRotStep d off j) s = some s' ∧ Ok layerCfg s' ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧
      (∀ k < keySlot, slotW s' k =
        if k = d + 8 + j then slotW s k ^^^ rotV (fun i => s.gpr (q i)) (fun i => keyW s (off + i)) j
        else slotW s k) ∧
      (∀ w < 32, keyW s' w = keyW s w) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [slotRegion layerCfg s] s.mem s'.mem := by
  have hi : (j + 7) % 8 < 8 := Nat.mod_lt _ (by decide)
  obtain ⟨n0, n1, -, -⟩ := q_ne _
  simp only [flRotStep, andR]
  rw [run_ldK hok (by omega_arith)]
  generalize e₁ : s.setReg t0 (keyW s (off + (j + 7) % 8)) = s₁
  have k₁ : Keeps s s₁ t0 := e₁ ▸ keeps_setReg _ _ (by decide) (by decide)
  have v₁ : s₁.gpr t0 = keyW s (off + (j + 7) % 8) := e₁ ▸ RegUpd.gpr_setReg_self _ _ _
  rw [run_and]
  generalize e₂ : s₁.setReg t0 (s₁.gpr t0 &&& s₁.gpr (q ((j + 7) % 8))) = s₂
  have k₂ : Keeps s₁ s₂ t0 := e₂ ▸ keeps_setReg _ _ (by decide) (by decide)
  have v₂ : s₂.gpr t0 = keyW s (off + (j + 7) % 8) &&& s.gpr (q ((j + 7) % 8)) := by
    rw [← e₂, RegUpd.gpr_setReg_self, v₁, k₁.gpr _ n0]
  have ok₂ := k₂.ok (k₁.ok hok)
  rw [run_ldS ok₂ hk]
  generalize e₃ : s₂.setReg t1 (slotW s₂ (d + 8 + j)) = s₃
  have k₃ : Keeps s₂ s₃ t1 := e₃ ▸ keeps_setReg _ _ (by decide) (by decide)
  have v₃ : s₃.gpr t1 = slotW s (d + 8 + j) := by
    rw [← e₃, RegUpd.gpr_setReg_self, k₂.slotW (by decide), k₁.slotW (by decide)]
  have u₃ : s₃.gpr t0 = s₂.gpr t0 := k₃.gpr _ (by decide)
  let V := rotV (fun i => s.gpr (q i)) (fun i => keyW s (off + i)) j
  have e₄ : ∀ is, runBlock isa (.dp .eor t1 t1 (if j = 0 then rorOp t0 8 else .reg t0) :: is) s₃ =
      runBlock isa is (s₃.setReg t1 (slotW s (d + 8 + j) ^^^ V)) := by
    intro is
    split
    · rename_i h
      rw [run_eor_ror (by decide) (by decide), v₃, u₃, v₂]
      simp only [V, rotV, h, ↓reduceIte]
    · rename_i h
      rw [run_eor, v₃, u₃, v₂]
      simp only [V, rotV, h, ↓reduceIte]
  rw [e₄]
  generalize e₅ : s₃.setReg t1 (slotW s (d + 8 + j) ^^^ V) = s₄
  have k₄ : Keeps s₃ s₄ t1 := e₅ ▸ keeps_setReg _ _ (by decide) (by decide)
  have v₄ : s₄.gpr t1 = slotW s (d + 8 + j) ^^^ V := e₅ ▸ RegUpd.gpr_setReg_self _ _ _
  have ok₄ := k₄.ok (k₃.ok ok₂)
  have b₄ : s₄.gpr sb = s.gpr sb := by
    rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  have kp₄ : s₄.gpr kp = s.gpr kp := by
    rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  have m₄ : s₄.mem = s.mem := by rw [k₄.mem, k₃.mem, k₂.mem, k₁.mem]
  rw [run_stS ok₄ hk, runBlock_nil]
  refine ⟨_, rfl, ok_setMem ok₄ _, fun r h1 h2 => ?_, fun k hk' => ?_, fun w hw' => ?_,
    by rw [k₄.rd, k₃.rd, k₂.rd, k₁.rd], by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr],
    by rw [k₄.sp, k₃.sp, k₂.sp, k₁.sp], ?_⟩
  · show s₄.gpr r = s.gpr r
    rw [k₄.gpr _ h2, k₃.gpr _ h2, k₂.gpr _ h1, k₁.gpr _ h1]
  · show (s₄.mem.writeW (wordAddr (s₄.gpr sb) (d + 8 + j)) (s₄.gpr t1)).readW (wordAddr (s₄.gpr sb) k) 32 = _
    rw [b₄, m₄, v₄]
    split
    · rename_i h; subst h; exact slot_writeW_self _ _
    · rename_i h; exact slot_writeW hok hk hk' h _
  · show (s₄.mem.writeW (wordAddr (s₄.gpr sb) (d + 8 + j)) (s₄.gpr t1)).readW (wordAddr (s₄.gpr kp) w) 32 = _
    rw [b₄, kp₄, m₄]
    exact key_writeW hok hk hw' _
  · show Frame _ s.mem (s₄.mem.writeW (wordAddr (s₄.gpr sb) (d + 8 + j)) (s₄.gpr t1))
    rw [b₄, m₄]
    exact exec_stS_frame hok hk _

theorem flOrStep_ok {s : State} (hok : Ok layerCfg s) {d off j : Nat} (hj : j < 8)
    (hk : d + 8 + j < keySlot) (hw : off + 16 ≤ 32) :
    ∃ s', runBlock isa (flOrStep d off j) s = some s' ∧ Ok layerCfg s' ∧
      s'.gpr (q j) = s.gpr (q j) ^^^ (keyW s (off + 8 + j) ||| slotW s (d + 8 + j)) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ q j → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨n0, n1, nsb, nkp⟩ := q_ne _
  simp only [flOrStep, eorR]
  rw [run_ldK hok (by omega_arith)]
  generalize e₁ : s.setReg t0 (keyW s (off + 8 + j)) = s₁
  have k₁ : Keeps s s₁ t0 := e₁ ▸ keeps_setReg _ _ (by decide) (by decide)
  have v₁ : s₁.gpr t0 = keyW s (off + 8 + j) := e₁ ▸ RegUpd.gpr_setReg_self _ _ _
  rw [run_ldS (k₁.ok hok) hk]
  generalize e₂ : s₁.setReg t1 (slotW s₁ (d + 8 + j)) = s₂
  have k₂ : Keeps s₁ s₂ t1 := e₂ ▸ keeps_setReg _ _ (by decide) (by decide)
  have v₂ : s₂.gpr t1 = slotW s (d + 8 + j) := by
    rw [← e₂, RegUpd.gpr_setReg_self, k₁.slotW (by decide)]
  rw [run_orr]
  generalize e₃ : s₂.setReg t0 (s₂.gpr t0 ||| s₂.gpr t1) = s₃
  have k₃ : Keeps s₂ s₃ t0 := e₃ ▸ keeps_setReg _ _ (by decide) (by decide)
  have v₃ : s₃.gpr t0 = keyW s (off + 8 + j) ||| slotW s (d + 8 + j) := by
    rw [← e₃, RegUpd.gpr_setReg_self, v₂, k₂.gpr _ (by decide), v₁]
  rw [run_eor]
  generalize e₄ : s₃.setReg (q j) (s₃.gpr (q j) ^^^ s₃.gpr t0) = s₄
  have k₄ : Keeps s₃ s₄ (q j) := e₄ ▸ keeps_setReg _ _ nsb nkp
  rw [runBlock_nil]
  refine ⟨_, rfl, k₄.ok (k₃.ok (k₂.ok (k₁.ok hok))), ?_, fun r h1 h2 h3 => ?_,
    by rw [k₄.mem, k₃.mem, k₂.mem, k₁.mem], by rw [k₄.rd, k₃.rd, k₂.rd, k₁.rd],
    by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr], by rw [k₄.sp, k₃.sp, k₂.sp, k₁.sp]⟩
  · rw [← e₄, RegUpd.gpr_setReg_self, v₃, k₃.gpr _ n0, k₂.gpr _ n1, k₁.gpr _ n0]
  · rw [k₄.gpr _ h3, k₃.gpr _ h1, k₂.gpr _ h2, k₁.gpr _ h1]

theorem runBlock_range_succ {f : Nat → List Instr} {n : Nat} {s : State} :
    runBlock isa ((List.range (n + 1)).flatMap f) s = (runBlock isa ((List.range n).flatMap f) s).bind
      (runBlock isa (f n)) := by
  rw [List.range_succ, List.flatMap_append, runBlock_app, List.flatMap_singleton]

/-- The rotation step on the half at slot `d`, the left word in the state. -/
theorem flRot_ok {s : State} (hok : Ok layerCfg s) {d off : Nat} (hd : d + 16 ≤ keySlot)
    (hw : off + 8 ≤ 32) : ∀ n ≤ 8,
    ∃ s', runBlock isa ((List.range n).flatMap (flRotStep d off)) s = some s' ∧ Ok layerCfg s' ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧
      (∀ k < keySlot, slotW s' k =
        if d + 8 ≤ k ∧ k < d + 8 + n then
          slotW s k ^^^ rotV (fun i => s.gpr (q i)) (fun i => keyW s (off + i)) (k - (d + 8))
        else slotW s k) ∧
      (∀ w < 32, keyW s' w = keyW s w) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [slotRegion layerCfg s] s.mem s'.mem
  | 0, _ => ⟨s, runBlock_nil, hok, fun _ _ _ => rfl, fun k _ => by simp only [show ¬ (d + 8 ≤ k ∧ k < d + 8 + 0) by omega_arith, ↓reduceIte],
      fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨s₁, h₁, ok₁, g₁, m₁, k₁, rd₁, wr₁, sp₁, f₁⟩ := flRot_ok hok hd hw n (by omega_arith)
    obtain ⟨s₂, h₂, ok₂, g₂, m₂, k₂, rd₂, wr₂, sp₂, f₂⟩ := flRotStep_ok ok₁ (d := d) (off := off) (j := n)
      (by omega_arith) hw
    have hq : ∀ i, s₁.gpr (q i) = s.gpr (q i) := fun i => g₁ _ (q_ne i).1 (q_ne i).2.1
    refine ⟨s₂, by rw [runBlock_range_succ, h₁, Option.bind_some, h₂], ok₂, fun r h1 h2 => (g₂ r h1 h2).trans (g₁ r h1 h2),
      fun k hk => ?_, fun w hw' => (k₂ w hw').trans (k₁ w hw'), rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_⟩
    · rw [m₂ k hk]
      have hrv : rotV (fun i => s₁.gpr (q i)) (fun i => keyW s₁ (off + i)) n =
          rotV (fun i => s.gpr (q i)) (fun i => keyW s (off + i)) n := by
        simp only [rotV, hq, k₁ _ (show off + (n + 7) % 8 < 32 by omega_arith)]
      split
      · rename_i h; subst h
        rw [m₁ _ hk, iteNeg (by omega_arith), hrv, itePos (by omega_arith), show d + 8 + n - (d + 8) = n by omega_arith]
      · rename_i h
        rw [m₁ _ hk]
        by_cases h' : d + 8 ≤ k ∧ k < d + 8 + n
        · rw [itePos h', itePos (by omega_arith)]
        · rw [iteNeg h', iteNeg (by omega_arith)]
    · have e : slotRegion layerCfg s₁ = slotRegion layerCfg s := by
        simp only [slotRegion, layerCfg, g₁ sb (by decide) (by decide)]
      exact f₁.trans (e ▸ f₂)

/-- The OR step: the left word, in the state, from the right word in its slots. -/
theorem flOr_ok {s : State} (hok : Ok layerCfg s) {d off : Nat} (hd : d + 16 ≤ keySlot)
    (hw : off + 16 ≤ 32) : ∀ n ≤ 8,
    ∃ s', runBlock isa ((List.range n).flatMap (flOrStep d off)) s = some s' ∧ Ok layerCfg s' ∧
      (∀ j < 8, s'.gpr (q j) = if j < n then s.gpr (q j) ^^^ (keyW s (off + 8 + j) ||| slotW s (d + 8 + j))
        else s.gpr (q j)) ∧
      (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp
  | 0, _ => ⟨s, runBlock_nil, hok, fun j _ => by simp only [show ¬ j < 0 by omega_arith, ↓reduceIte],
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | n + 1, hn => by
    obtain ⟨s₁, h₁, ok₁, g₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := flOr_ok hok hd hw n (by omega_arith)
    obtain ⟨s₂, h₂, ok₂, v₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := flOrStep_ok ok₁ (d := d) (off := off) (j := n)
      (by omega_arith) (by omega_arith) hw
    refine ⟨s₂, by rw [runBlock_range_succ, h₁, Option.bind_some, h₂], ok₂, fun j hj => ?_,
      fun r hr => ?_, m₂.trans m₁, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁⟩
    · have hs : slotW s₁ (d + 8 + n) = slotW s (d + 8 + n) := by
        simp only [slotW, m₁, (o₁ sb (by decide))]
      have hkw : keyW s₁ (off + 8 + n) = keyW s (off + 8 + n) := by
        simp only [keyW, m₁, (o₁ kp (by decide))]
      by_cases hjn : j = n
      · subst hjn
        rw [v₂, g₁ j hj, iteNeg (by omega_arith), itePos (by omega_arith), hs, hkw]
      · rw [o₂ _ (q_ne j).1 (q_ne j).2.1 (fun h => hjn (q_inj j hj n (by omega_arith) h)), g₁ j hj]
        by_cases hjn' : j < n
        · rw [itePos hjn', itePos (by omega_arith)]
        · rw [iteNeg hjn', iteNeg (by omega_arith)]
    · have h1 : r ≠ t0 := fun h => hr (h ▸ by decide)
      have h2 : r ≠ t1 := fun h => hr (h ▸ by decide)
      have h3 : r ≠ q n := fun h => hr (h ▸ q_mem n)
      rw [o₂ r h1 h2 h3, o₁ r hr]

theorem runBlock_map_succ {f : Nat → Instr} {n : Nat} {s : State} :
    runBlock isa ((List.range (n + 1)).map f) s = (runBlock isa ((List.range n).map f) s).bind
      (runBlock isa [f n]) := by
  rw [List.range_succ, List.map_append, runBlock_app, List.map_singleton]

theorem loadL_ok {s : State} (hok : Ok layerCfg s) {d : Nat} (hd : d + 8 ≤ keySlot) : ∀ n ≤ 8,
    ∃ s', runBlock isa ((List.range n).map fun j => ldS (q j) (d + j)) s = some s' ∧ Ok layerCfg s' ∧
      (∀ j < 8, s'.gpr (q j) = if j < n then slotW s (d + j) else s.gpr (q j)) ∧
      (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp
  | 0, _ => ⟨s, runBlock_nil, hok, fun j _ => by simp only [show ¬ j < 0 by omega_arith, ↓reduceIte],
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | n + 1, hn => by
    obtain ⟨s₁, h₁, ok₁, g₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := loadL_ok hok hd n (by omega_arith)
    obtain ⟨-, -, nsb, nkp⟩ := q_ne n
    have k₂ := keeps_setReg s₁ (slotW s₁ (d + n)) nsb nkp
    have hs : slotW s₁ (d + n) = slotW s (d + n) := by simp only [slotW, m₁, o₁ sb (by decide)]
    refine ⟨_, by rw [runBlock_map_succ, h₁, Option.bind_some, run_ldS ok₁ (by omega_arith), runBlock_nil],
      k₂.ok ok₁, fun j hj => ?_, fun r hr => ?_, m₁, rd₁, wr₁, sp₁⟩
    · by_cases hjn : j = n
      · subst hjn; rw [RegUpd.gpr_setReg_self, hs, itePos (by omega_arith)]
      · rw [k₂.gpr _ (fun h => hjn (q_inj j hj n (by omega_arith) h)), g₁ j hj]
        by_cases hjn' : j < n
        · rw [itePos hjn', itePos (by omega_arith)]
        · rw [iteNeg hjn', iteNeg (by omega_arith)]
    · rw [k₂.gpr _ (fun h => hr (by rw [h]; exact q_mem n)), o₁ r hr]

theorem storeL_ok {s : State} (hok : Ok layerCfg s) {d : Nat} (hd : d + 8 ≤ keySlot) : ∀ n ≤ 8,
    ∃ s', runBlock isa ((List.range n).map fun j => stS (d + j) (q j)) s = some s' ∧ Ok layerCfg s' ∧
      (∀ k < keySlot, slotW s' k = if d ≤ k ∧ k < d + n then s.gpr (q (k - d)) else slotW s k) ∧
      (∀ w < 32, keyW s' w = keyW s w) ∧ (∀ r, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [slotRegion layerCfg s] s.mem s'.mem
  | 0, _ => ⟨s, runBlock_nil, hok, fun k _ => by simp only [show ¬ (d ≤ k ∧ k < d + 0) by omega_arith, ↓reduceIte],
      fun _ _ => rfl, fun _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨s₁, h₁, ok₁, m₁, k₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := storeL_ok hok hd n (by omega_arith)
    have b₁ : s₁.gpr sb = s.gpr sb := g₁ sb
    refine ⟨{ s₁ with mem := s₁.mem.writeW (wordAddr (s₁.gpr sb) (d + n)) (s₁.gpr (q n)) },
      by rw [runBlock_map_succ, h₁, Option.bind_some, run_stS ok₁ (by omega_arith), runBlock_nil],
      ok_setMem ok₁ _, fun k hk => ?_, fun w hw => ?_, g₁, rd₁, wr₁, sp₁, ?_⟩
    · show (s₁.mem.writeW (wordAddr (s₁.gpr sb) (d + n)) (s₁.gpr (q n))).readW (wordAddr (s₁.gpr sb) k) 32 = _
      by_cases hkn : k = d + n
      · subst hkn
        rw [slot_writeW_self, itePos (by omega_arith), g₁, show d + n - d = n by omega_arith]
      · rw [slot_writeW ok₁ (by omega_arith) hk hkn]
        show slotW s₁ k = _
        rw [m₁ k hk]
        by_cases h' : d ≤ k ∧ k < d + n
        · rw [itePos h', itePos (by omega_arith)]
        · rw [iteNeg h', iteNeg (by omega_arith)]
    · show (s₁.mem.writeW (wordAddr (s₁.gpr sb) (d + n)) (s₁.gpr (q n))).readW (wordAddr (s₁.gpr kp) w) 32 = _
      rw [key_writeW ok₁ (by omega_arith) hw, k₁ w hw]
    · have e : slotRegion layerCfg s₁ = slotRegion layerCfg s := by simp only [slotRegion, layerCfg, b₁]
      exact f₁.trans (e ▸ exec_stS_frame ok₁ (by omega_arith) _)

theorem getLsbD_ror8 (x : BitVec 32) {p : Nat} (hp : p < 32) :
    (x.rotateRight 8).getLsbD p = x.getLsbD ((p + 8) % 32) := by
  rw [BitVec.getLsbD_rotateRight]
  split
  · congr 1; omega_arith
  · rename_i h; simp only [Nat.reduceMod, Nat.not_lt] at h; simp only [hp, decide_true, Bool.true_and]
    congr 1; omega_arith

theorem rotV_bit {L K : Nat → BitVec 32} {j p : Nat} (hp : p < 32) :
    (rotV L K j).getLsbD p =
      ((L ((j + 7) % 8)).getLsbD (W32.rotPos j p) && (K ((j + 7) % 8)).getLsbD (W32.rotPos j p)) := by
  simp only [rotV, W32.rotPos]
  split
  · rw [getLsbD_ror8 _ hp, BitVec.getLsbD_and, Bool.and_comm]
  · rw [BitVec.getLsbD_and, Bool.and_comm]

/-- The planes of a half: the left word in the state registers, the right in its slots. -/
def mixed (s : State) (d : Nat) : Nat → BitVec 32 := fun i => if i < 8 then s.gpr (q i) else slotW s (d + i)

/-- What FL and FLINV keep and change. -/
structure FlPost (s s' : State) (d : Nat) : Prop where
  ok : Ok layerCfg s'
  slots : ∀ k < keySlot, (k < d ∨ d + 16 ≤ k) → slotW s' k = slotW s k
  keys : ∀ w < 32, keyW s' w = keyW s w
  gpr : ∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [slotRegion layerCfg s] s.mem s'.mem

/-- The rotation step, as `W32.RotStep`, after the left word is loaded. -/
theorem flRot_step {s : State} (hok : Ok layerCfg s) {d off : Nat} (hd : d + 16 ≤ keySlot)
    (hw : off + 8 ≤ 32) :
    ∃ s', runBlock isa (flRot d off) s = some s' ∧
      W32.RotStep (mixed s d) (fun i => keyW s (off + i)) (mixed s' d) ∧ Ok layerCfg s' ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧
      (∀ k < keySlot, (k < d + 8 ∨ d + 16 ≤ k) → slotW s' k = slotW s k) ∧
      (∀ w < 32, keyW s' w = keyW s w) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [slotRegion layerCfg s] s.mem s'.mem := by
  obtain ⟨s', h, ok, g, m, k, rd, wr, sp, f⟩ := flRot_ok hok hd hw 8 (Nat.le_refl _)
  have hq : ∀ i, s'.gpr (q i) = s.gpr (q i) := fun i => g _ (q_ne i).1 (q_ne i).2.1
  refine ⟨s', h, ⟨fun j hj => ?_, fun j hj p hp => ?_⟩, ok, g, fun k' hk' h' => ?_, k, rd, wr, sp, f⟩
  · simp only [mixed, hj, ↓reduceIte, hq]
  · have hjj : (j + 7) % 8 < 8 := Nat.mod_lt _ (by decide)
    simp only [mixed, show ¬ 8 + j < 8 by omega_arith, ↓reduceIte, hjj]
    rw [m _ (by omega_arith), itePos (by omega_arith), BitVec.getLsbD_xor, rotV_bit hp,
      show d + (8 + j) - (d + 8) = j by omega_arith]
  · rw [m k' hk', iteNeg (by omega_arith)]

/-- The OR step, as `W32.OrStep`. -/
theorem flOr_step {s : State} (hok : Ok layerCfg s) {d off : Nat} (hd : d + 16 ≤ keySlot)
    (hw : off + 16 ≤ 32) :
    ∃ s', runBlock isa (flOr d off) s = some s' ∧
      W32.OrStep (mixed s d) (fun i => keyW s (off + i)) (mixed s' d) ∧ Ok layerCfg s' ∧
      (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s', h, ok, g, o, m, rd, wr, sp⟩ := flOr_ok hok hd hw 8 (Nat.le_refl _)
  have hs : ∀ k, slotW s' k = slotW s k := fun k => by simp only [slotW, m, o sb (by decide)]
  refine ⟨s', h, ⟨fun j hj => ?_, fun j hj p hp => ?_⟩, ok, o, m, rd, wr, sp⟩
  · simp only [mixed, show ¬ 8 + j < 8 by omega_arith, ↓reduceIte, hs]
  · simp only [mixed, hj, ↓reduceIte, show ¬ 8 + j < 8 by omega_arith]
    rw [g j hj, itePos hj, BitVec.getLsbD_xor, BitVec.getLsbD_or, Bool.or_comm,
      show d + (8 + j) = d + 8 + j by omega_arith, show off + (8 + j) = off + 8 + j by omega_arith]

theorem loadL_mixed {s : State} (hok : Ok layerCfg s) {d : Nat} (hd : d + 16 ≤ keySlot) :
    ∃ s', runBlock isa (loadL d) s = some s' ∧ Ok layerCfg s' ∧ (∀ i < 16, mixed s' d i = half s d i) ∧
      (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s', h, ok, g, o, m, rd, wr, sp⟩ := loadL_ok hok (d := d) (by omega_arith) 8 (Nat.le_refl _)
  refine ⟨s', h, ok, fun i hi => ?_, o, m, rd, wr, sp⟩
  simp only [mixed, half]
  split
  · rename_i h; rw [g i h, itePos h]
  · simp only [slotW, m, o sb (by decide)]

theorem storeL_mixed {s : State} (hok : Ok layerCfg s) {d : Nat} (hd : d + 16 ≤ keySlot) :
    ∃ s', runBlock isa (storeL d) s = some s' ∧ Ok layerCfg s' ∧ (∀ i < 16, half s' d i = mixed s d i) ∧
      (∀ k < keySlot, (k < d ∨ d + 8 ≤ k) → slotW s' k = slotW s k) ∧
      (∀ w < 32, keyW s' w = keyW s w) ∧ (∀ r, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [slotRegion layerCfg s] s.mem s'.mem := by
  obtain ⟨s', h, ok, m, k, g, rd, wr, sp, f⟩ := storeL_ok hok (d := d) (by omega_arith) 8 (Nat.le_refl _)
  refine ⟨s', h, ok, fun i hi => ?_, fun k' hk' h' => ?_, k, g, rd, wr, sp, f⟩
  · simp only [mixed, half]
    rw [m _ (by omega_arith)]
    split
    · rename_i h; rw [itePos (by omega_arith), show d + i - d = i by omega_arith]
    · rw [iteNeg (by omega_arith)]
  · rw [m _ hk', iteNeg (by omega_arith)]

theorem fl_ok {s : State} (hok : Ok layerCfg s) {d off : Nat} (hd : d + 16 ≤ keySlot) (hw : off + 16 ≤ 32)
    {x : Nat → BitVec 64} {k : BitVec 64} (hQ : W32.HalfRel (half s d) x)
    (hK : W32.HalfRel (fun i => keyW s (off + i)) fun _ => k) :
    ∃ s', runBlock isa (flCode d off) s = some s' ∧
      W32.HalfRel (half s' d) (fun b => Spec.Camellia.fl (x b) k) ∧ FlPost s s' d := by
  obtain ⟨s₁, h₁, ok₁, x₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := loadL_mixed hok hd
  have kw₁ : ∀ w, keyW s₁ w = keyW s w := fun w => by simp only [keyW, m₁, o₁ kp (by decide)]
  obtain ⟨s₂, h₂, r₂, ok₂, o₂, sl₂, kw₂, rd₂, wr₂, sp₂, f₂⟩ := flRot_step ok₁ hd (off := off) (by omega_arith)
  obtain ⟨s₃, h₃, r₃, ok₃, o₃, m₃, rd₃, wr₃, sp₃⟩ := flOr_step ok₂ hd hw
  obtain ⟨s₄, h₄, ok₄, x₄, sl₄, kw₄, o₄, rd₄, wr₄, sp₄, f₄⟩ := storeL_mixed ok₃ hd
  have hK₁ : W32.HalfRel (fun i => keyW s₁ (off + i)) fun _ => k := hK.congr fun i _ => kw₁ _
  have hK₂ : W32.HalfRel (fun i => keyW s₂ (off + i)) fun _ => k :=
    hK₁.congr fun i hi => kw₂ _ (by omega_arith)
  have hr := W32.fl_rel (hQ.congr fun i hi => x₁ i hi) hK₁ r₂
    ⟨r₃.1, fun j hj p hp => by rw [r₃.2 j hj p hp]; dsimp only; rw [kw₂ _ (by omega_arith)]⟩
  have b₂ : s₂.gpr sb = s.gpr sb := by rw [o₂ _ (by decide) (by decide), o₁ _ (by decide)]
  have s₃eq : ∀ k, slotW s₃ k = slotW s₂ k := fun k => by simp only [slotW, m₃, o₃ sb (by decide)]
  refine ⟨s₄, ?_, hr.congr fun i hi => x₄ i hi, ⟨ok₄, fun k' hk' h' => ?_, fun w hw' => ?_, fun r hr => ?_,
    by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁], by rw [sp₄, sp₃, sp₂, sp₁], ?_⟩⟩
  · rw [flCode, runBlock_app, runBlock_app, runBlock_app, h₁, Option.bind_some, h₂, Option.bind_some, h₃,
      Option.bind_some, h₄]
  · rw [sl₄ k' hk' (by omega_arith), s₃eq, sl₂ k' hk' (by omega_arith)]
    simp only [slotW, m₁, o₁ sb (by decide)]
  · rw [kw₄ w hw', show keyW s₃ w = keyW s₂ w by simp only [keyW, m₃, o₃ kp (by decide)], kw₂ w hw', kw₁]
  · have h1 : r ≠ t0 := fun h => hr (h ▸ by decide)
    have h2 : r ≠ t1 := fun h => hr (h ▸ by decide)
    rw [o₄, o₃ r hr, o₂ r h1 h2, o₁ r hr]
  · have e₂ : slotRegion layerCfg s₁ = slotRegion layerCfg s := by
      simp only [slotRegion, layerCfg, o₁ sb (by decide)]
    have e₃ : slotRegion layerCfg s₃ = slotRegion layerCfg s := by
      simp only [slotRegion, layerCfg, o₃ sb (by decide), b₂]
    have f₁ : Frame [slotRegion layerCfg s] s.mem s₁.mem := by rw [m₁]; exact Frame.refl _ _
    have f₃ : Frame [slotRegion layerCfg s] s₂.mem s₃.mem := by rw [m₃]; exact Frame.refl _ _
    exact f₁.trans ((e₂ ▸ f₂).trans (f₃.trans (e₃ ▸ f₄)))

theorem flinv_ok {s : State} (hok : Ok layerCfg s) {d off : Nat} (hd : d + 16 ≤ keySlot) (hw : off + 16 ≤ 32)
    {x : Nat → BitVec 64} {k : BitVec 64} (hQ : W32.HalfRel (half s d) x)
    (hK : W32.HalfRel (fun i => keyW s (off + i)) fun _ => k) :
    ∃ s', runBlock isa (flinvCode d off) s = some s' ∧
      W32.HalfRel (half s' d) (fun b => Spec.Camellia.flinv (x b) k) ∧ FlPost s s' d := by
  obtain ⟨s₁, h₁, ok₁, x₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := loadL_mixed hok hd
  have kw₁ : ∀ w, keyW s₁ w = keyW s w := fun w => by simp only [keyW, m₁, o₁ kp (by decide)]
  obtain ⟨s₂, h₂, r₂, ok₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := flOr_step ok₁ hd hw
  have kw₂ : ∀ w, keyW s₂ w = keyW s₁ w := fun w => by simp only [keyW, m₂, o₂ kp (by decide)]
  obtain ⟨s₃, h₃, r₃, ok₃, o₃, sl₃, kw₃, rd₃, wr₃, sp₃, f₃⟩ := flRot_step ok₂ hd (off := off) (by omega_arith)
  obtain ⟨s₄, h₄, ok₄, x₄, sl₄, kw₄, o₄, rd₄, wr₄, sp₄, f₄⟩ := storeL_mixed ok₃ hd
  have hK₁ : W32.HalfRel (fun i => keyW s₁ (off + i)) fun _ => k := hK.congr fun i _ => kw₁ _
  have hK₂ : W32.HalfRel (fun i => keyW s₂ (off + i)) fun _ => k := hK₁.congr fun i _ => kw₂ _
  have hr := W32.flinv_rel (hQ.congr fun i hi => x₁ i hi) hK₁ r₂ (by
    have : (fun i => keyW s₂ (off + i)) = fun i => keyW s₁ (off + i) := funext fun i => kw₂ _
    rw [this] at r₃; exact r₃)
  have b₂ : s₂.gpr sb = s.gpr sb := by rw [o₂ _ (by decide), o₁ _ (by decide)]
  refine ⟨s₄, ?_, hr.congr fun i hi => x₄ i hi, ⟨ok₄, fun k' hk' h' => ?_, fun w hw' => ?_, fun r hr => ?_,
    by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁], by rw [sp₄, sp₃, sp₂, sp₁], ?_⟩⟩
  · rw [flinvCode, runBlock_app, runBlock_app, runBlock_app, h₁, Option.bind_some, h₂, Option.bind_some, h₃,
      Option.bind_some, h₄]
  · rw [sl₄ k' hk' (by omega_arith), sl₃ k' hk' (by omega_arith)]
    simp only [slotW, m₂, m₁, o₂ sb (by decide), o₁ sb (by decide)]
  · rw [kw₄ w hw', kw₃ w hw', kw₂, kw₁]
  · have h1 : r ≠ t0 := fun h => hr (h ▸ by decide)
    have h2 : r ≠ t1 := fun h => hr (h ▸ by decide)
    rw [o₄, o₃ r h1 h2, o₂ r hr, o₁ r hr]
  · have e₂ : slotRegion layerCfg s₂ = slotRegion layerCfg s := by
      simp only [slotRegion, layerCfg, b₂]
    have e₃ : slotRegion layerCfg s₃ = slotRegion layerCfg s := by
      simp only [slotRegion, layerCfg, o₃ sb (by decide) (by decide), b₂]
    have f₂ : Frame [slotRegion layerCfg s] s.mem s₂.mem := by rw [m₂, m₁]; exact Frame.refl _ _
    exact f₂.trans ((e₂ ▸ f₃).trans (e₃ ▸ f₄))

end VG.Proof.Camellia.Arm

end

end

/-!
# Eight blocks of bitsliced Camellia on ARMv7: the rounds

With the table of bitsliced subkeys `E 0 … E (8 g + 1)` in the scratch
buffer (`CorePre`), the groups of rounds of `crypt8` take the halves in
their slots through `groups g E`. They write only the rounds' working space
below the table and the slot of the group's end (`Ctx`). The rounds are
`round_ok`, FL and FLINV `fl_ok` and `flinv_ok`; the pairs of rounds and the
groups of six are loops around them, whose invariants are the
specification's `pair` and `group` (`Proof/Camellia/Words.lean`).
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Camellia.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 kp ldS stS)
open VG.Proof.Camellia (pair group groups cryptWords pairsN pairsN_succ group_eq)
open VG.Proof.Sm4.Arm (linPostG)

theorem slots_eq : slots = 680 := rfl
theorem tailSlot_eq : tailSlot = 632 := rfl
theorem keySlot_eq : keySlot = 72 := rfl
theorem grpSlot_eq : grpSlot = 616 := rfl
theorem endSlot_eq : endSlot = 617 := rfl
theorem d1Slot_eq : d1Slot = 40 := rfl
theorem d2Slot_eq : d2Slot = 56 := rfl

/-- Word `j` of entry `i` of the table, in the scratch buffer at `b`. -/
def entryW (m : Mem) (b : BitVec 32) (i j : Nat) : BitVec 32 := m.readW (wordAddr b (keySlot + 16 * i + j)) 32

/-- The scratch buffer at `b` is writable in `s`, and does not wrap around. -/
structure Scr (s : State) (b : BitVec 32) : Prop where
  wr : (⟨State.addr b, 4 * slots⟩ : Region) ∈ s.wr
  fit : b.toNat + 4 * slots ≤ 2 ^ 32

/-- What the rounds need: the scratch buffer, writable, and a table of `nk`
subkeys. -/
structure KeyCtx (s₀ : State) (nk : Nat) (E : Nat → BitVec 64) : Prop where
  scr : Scr s₀ (s₀.gpr sb)
  nk34 : nk ≤ 34
  keys : ∀ i < nk, W32.HalfRel (entryW s₀.mem (s₀.gpr sb) i) fun _ => E i

/-- What the groups of rounds need: the table of `8 g + 2` subkeys, and the
address of its postwhitening entry in its slot. -/
structure CorePre (s₀ : State) (g : Nat) (E : Nat → BitVec 64) : Prop extends KeyCtx s₀ (8 * g + 2) E where
  hg : g = 3 ∨ g = 4
  bound : slotW s₀ endSlot = s₀.gpr sb + BitVec.ofNat 32 (4 * keySlot + 512 * g)

/-- What the rounds may write in the scratch buffer at `b`: their working
space, the slot of the group's end, and the tail buffer. -/
def ctxRegions (b : BitVec 32) : List Region :=
  [⟨State.addr b, 4 * keySlot⟩, ⟨State.addr (b + BitVec.ofNat 32 (4 * grpSlot)), 4⟩,
   ⟨State.addr (b + BitVec.ofNat 32 (4 * tailSlot)), 128⟩]

/-- What stays the same: the regions, `sb` and the registers outside the
layers', and the memory outside `ctxRegions`. -/
structure Ctx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ layerWrites → r ≠ kp → s.gpr r = s₀.gpr r
  frame : Frame (ctxRegions (s₀.gpr sb)) s₀.mem s.mem

theorem Ctx.refl (s₀ : State) : Ctx s₀ s₀ := ⟨rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _⟩

theorem Ctx.base {s₀ s : State} (hc : Ctx s₀ s) : s.gpr sb = s₀.gpr sb := hc.keep _ (by decide) (by decide)

/-- A step that writes only the layers' registers, `kp`, and the regions. -/
theorem Ctx.step {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ layerWrites → r ≠ kp → s'.gpr r = s.gpr r)
    (hf : Frame (ctxRegions (s₀.gpr sb)) s.mem s'.mem) : Ctx s₀ s' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, fun r h1 h2 => (hk r h1 h2).trans (hc.keep r h1 h2), hc.frame.trans hf⟩

/-- A step that writes only the rounds' working space. -/
theorem Ctx.stepL {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ layerWrites → r ≠ kp → s'.gpr r = s.gpr r)
    (hf : Frame [slotRegion layerCfg s] s.mem s'.mem) : Ctx s₀ s' :=
  hc.step hrd hwr hk (hf.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    simp [slotRegion, layerCfg, ctxRegions, hc.base])

/-! ## Addresses -/

/-- `kp` at entry `m` of the table. -/
def AtEntry (s : State) (b : BitVec 32) (m : Nat) : Prop := s.gpr kp = b + BitVec.ofNat 32 (4 * keySlot + 64 * m)

theorem wordAddr_entry {s : State} {b : BitVec 32} {m : Nat} (hk : AtEntry s b m) (j : Nat) :
    wordAddr (s.gpr kp) j = wordAddr b (keySlot + 16 * m + j) := by
  rw [wordAddr, wordAddr, hk, add_ofNat_ofNat,
    show 4 * keySlot + 64 * m + 4 * j = 4 * (keySlot + 16 * m + j) by omega_arith]

theorem keyW_entry {s : State} {b : BitVec 32} {m : Nat} (hk : AtEntry s b m) (e j : Nat) :
    keyW s (16 * e + j) = entryW s.mem b (m + e) j := by
  simp only [keyW, entryW, wordAddr_entry hk,
    show keySlot + 16 * m + (16 * e + j) = keySlot + 16 * (m + e) + j by omega_arith]

theorem Scr.slot_in {s : State} {b : BitVec 32} (h : Scr s b) {k : Nat} (hk : k < slots) :
    InRegions s.wr (wordAddr b k) 4 :=
  in_off h.wr h.fit (by omega_arith) (by omega_arith)

theorem ok_layer {s : State} {b : BitVec 32} {m : Nat} (hs : Scr s b) (hb : s.gpr sb = b)
    (hk : AtEntry s b m) (hm : m + 2 ≤ 34) : Ok layerCfg s where
  slotIn k hk' := by
    simp only [layerCfg, keySlot_eq] at hk'
    simp only [layerCfg, hb]; exact hs.slot_in (by rw [slots_eq]; omega_arith)
  extIn j hj := by
    simp only [layerCfg] at hj
    simp only [layerCfg, wordAddr_entry hk]
    obtain ⟨r, hr, hc⟩ := hs.slot_in (k := keySlot + 16 * m + j) (by rw [slots_eq, keySlot_eq]; omega_arith)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  slots := by have := hs.fit; simp only [layerCfg, hb]; rw [slots_eq] at this; rw [keySlot_eq]; omega_arith
  sep k hk' j hj := by
    have := hs.fit
    simp only [layerCfg, keySlot_eq] at hk' hj
    simp only [layerCfg, hb, wordAddr_entry hk]
    rw [slots_eq] at this
    exact slot_sep _ (by omega_arith) (by rw [keySlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith)

/-- A word of slot `k` outside a region at slots `a … a + n` of the scratch buffer. -/
theorem slot_disjoint {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {k a n : Nat}
    (hk : k < slots) (ha : a + n ≤ slots) (hn : 0 < n) (h : k + 1 ≤ a ∨ a + n ≤ k) :
    (⟨wordAddr b k, 4⟩ : Region).Disjoint ⟨State.addr (b + BitVec.ofNat 32 (4 * a)), 4 * n⟩ := by
  rw [slots_eq] at hfit hk ha
  rw [wordAddr, VG.Arm.addr_add (by omega_arith), VG.Arm.addr_add (by omega_arith)]
  exact VG.Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem slot_disjoint_base {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {k n : Nat}
    (hk : k < slots) (hn : n ≤ k) :
    (⟨wordAddr b k, 4⟩ : Region).Disjoint ⟨State.addr b, 4 * n⟩ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · intro x _ h; simp [Region.Contains] at h
  have := slot_disjoint hfit (a := 0) (n := n) hk (by rw [slots_eq] at hk ⊢; omega_arith) hn0 (.inr (by omega_arith))
  simpa using this

/-- Slots outside `ctxRegions` are kept. -/
theorem Ctx.slot {s₀ s : State} (hc : Ctx s₀ s) (hfit : (s₀.gpr sb).toNat + 4 * slots ≤ 2 ^ 32) {k : Nat}
    (hk : k < slots) (h1 : keySlot ≤ k) (h2 : k ≠ grpSlot) (h3 : k < tailSlot ∨ tailSlot + 32 ≤ k) :
    slotW s k = slotW s₀ k := by
  simp only [slotW, hc.base]
  refine hc.frame.readW (r := ⟨wordAddr (s₀.gpr sb) k, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact slot_disjoint_base hfit hk h1
  · have := slot_disjoint hfit (a := grpSlot) (n := 1) hk (by rw [slots_eq, grpSlot_eq]; omega_arith)
      (by decide) (by omega_arith)
    simpa using this
  · have := slot_disjoint hfit (a := tailSlot) (n := 32) hk (by rw [slots_eq, tailSlot_eq]; omega_arith)
      (by decide) (by omega_arith)
    simpa using this

theorem Ctx.entry {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {i j : Nat} (hi : i < 34) (hj : j < 16) :
    entryW s.mem (s₀.gpr sb) i j = entryW s₀.mem (s₀.gpr sb) i j := by
  have := hc.slot hp.scr.fit (k := keySlot + 16 * i + j) (by rw [slots_eq, keySlot_eq]; omega_arith)
    (by omega_arith) (by rw [grpSlot_eq, keySlot_eq]; omega_arith) (.inl (by rw [tailSlot_eq, keySlot_eq]; omega_arith))
  simp only [slotW, hc.base] at this
  exact this

theorem Ctx.keyRel {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m e : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hme : m + e < nk) :
    W32.HalfRel (fun j => keyW s (16 * e + j)) fun _ => E (m + e) := by
  have hg := hp.nk34
  refine (hp.keys _ hme).congr fun j hj => ?_
  rw [keyW_entry hk, hc.entry hp (by omega_arith) hj]

theorem Ctx.ok {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 2 ≤ 34) : Ok layerCfg s :=
  ok_layer ⟨by rw [hc.wr]; exact hp.scr.wr, hp.scr.fit⟩ hc.base hk hm

/-! ## Rounds -/

/-- The halves of the eight blocks, `(D1, D2)` of block `b` in `S b`, in their slots. -/
def Halves (s : State) (S : Nat → BitVec 64 × BitVec 64) : Prop :=
  W32.HalfRel (half s d1Slot) (fun b => (S b).1) ∧ W32.HalfRel (half s d2Slot) (fun b => (S b).2)

theorem Halves.congr {s s' : State} {S : Nat → BitVec 64 × BitVec 64} (h : Halves s S)
    (hs : ∀ k, d1Slot ≤ k → k < keySlot → slotW s' k = slotW s k) : Halves s' S :=
  ⟨h.1.congr fun i hi => hs _ (by omega_arith) (by rw [d1Slot_eq, keySlot_eq] at *; omega_arith),
   h.2.congr fun i hi => hs _ (by rw [d1Slot_eq, d2Slot_eq]; omega_arith) (by rw [d2Slot_eq, keySlot_eq]; omega_arith)⟩

theorem round_all (off src dst : Nat) (h : RoundCase off src dst) :
    (layerKeep.all fun r => (preL off src ++ midLR off src ++ postP dst).all fun i => !clobbers i r) = true := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide +kernel

/-- `add kp, kp, #n`, keeping all else. -/
theorem addKp_ok (s : State) (n : Nat) (he : encodable (BitVec.ofNat 32 n) = true) :
    runBlock isa [.dp .add kp kp (.imm (BitVec.ofNat 32 n))] s =
      some (s.setReg kp (s.gpr kp + BitVec.ofNat 32 n)) := by
  simp only [runBlock_cons, exec, Op2.eval, he, ↓reduceIte, Option.map_some, runStep_some, runBlock_nil]

/-- A round, under `Ctx`, with the subkey at entry `m + off / 16`. -/
theorem round_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {off src dst m : Nat}
    (hA : check (lanes 32 11) layerCfg (linExt 32) (preL off src) preEnv
      (linPostG 11 (qOuts (preG off src)) [] halvesSlots preEnv) = true)
    (hC : check (lanes 32 12) layerCfg (linExt 40) (midLR off src) midEnv
      (linPostG 12 (qOuts (midG off src)) ylOuts halvesSlots midEnv) = true)
    (hE : check (lanes 32 11) linCfg (linExt 48) (postP dst) postEnv
      (linPostG 11 [] (postOuts dst) (otherSlots dst) postEnv) = true)
    (hcase : RoundCase off src dst)
    (hk : AtEntry s (s₀.gpr sb) m) (hme : m + off / 16 < nk) (hm34 : m + 2 ≤ 34)
    {X Y : Nat → BitVec 64} (hQ : W32.HalfRel (half s src) X) (hR : W32.HalfRel (half s dst) Y) :
    ∃ s', runBlock isa (round off src dst) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      W32.HalfRel (half s' dst) (fun b => Y b ^^^ Spec.Camellia.f (X b) (E (m + off / 16))) ∧
      (∀ i < 16, slotW s' (src + i) = slotW s (src + i)) ∧
      (∀ k, keySlot ≤ k → k < slots → slotW s' k = slotW s k) := by
  have hK : W32.HalfRel (fun j => keyW s (off + j)) fun _ => E (m + off / 16) := by
    have := hc.keyRel hp hk (e := off / 16) hme
    rcases hcase with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact this
  have hok := hc.ok hp hk hm34
  obtain ⟨s', h', hD, hsrc, rd', wr', sp', o', f'⟩ :=
    round_ok hA hC hE (round_all off src dst hcase) hcase hok hQ hK hR
  have hfit := hp.scr.fit
  rw [slots_eq] at hfit
  refine ⟨s', h', hc.stepL rd' wr' (fun r h1 _ => o' r h1) f', o' _ (by decide), hD, hsrc, fun k h1 h2 => ?_⟩
  simp only [slotW, o' sb (by decide)]
  refine f'.readW (r := ⟨wordAddr (s.gpr sb) k, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  simp only [slotRegion, layerCfg]
  rw [hc.base]
  exact slot_disjoint_base (by rw [slots_eq]; omega_arith) h2 h1

theorem entry_beq (b : BitVec 32) {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (b + BitVec.ofNat 32 x - (b + BitVec.ofNat 32 y) == 0) = decide (x = y) := by
  rw [VG.Offset.add_sub_add_left, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

/-- `ldr t0, [sb, #4 grpSlot]; cmp kp, t0`. -/
theorem cmpSlot_ok {s : State} (hs : Scr s (s.gpr sb)) {k : Nat} (hk : k < slots) (hk4 : 4 * k < 4096) :
    runBlock isa [ldS t0 k, .cmp kp (.reg t0)] s =
      some (subFlags (s.setReg t0 (slotW s k)) (s.gpr kp) (slotW s k)) := by
  have hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr sb + BitVec.ofNat 32 (4 * k))) 4 := by
    obtain ⟨r, hr, hc⟩ := hs.slot_in hk; exact ⟨r, List.mem_append_right _ hr, hc⟩
  simp only [ldS, runBlock_cons, exec_ldr hk4 hin, runStep_some]
  rfl

theorem subFlags_gpr (s : State) (x y : BitVec 32) : (subFlags s x y).gpr = s.gpr := rfl
theorem subFlags_mem (s : State) (x y : BitVec 32) : (subFlags s x y).mem = s.mem := rfl
theorem subFlags_rd (s : State) (x y : BitVec 32) : (subFlags s x y).rd = s.rd := rfl
theorem subFlags_wr (s : State) (x y : BitVec 32) : (subFlags s x y).wr = s.wr := rfl
theorem subFlags_z (s : State) (x y : BitVec 32) : (subFlags s x y).z = (x - y == 0) := rfl

theorem encodable_128 : encodable (BitVec.ofNat 32 128) = true := by decide

/-- `kp` stepped by `n`, from entry `m`. -/
theorem AtEntry.add {s s' : State} {b : BitVec 32} {m n : Nat} (hk : AtEntry s b m)
    (h : s'.gpr kp = s.gpr kp + BitVec.ofNat 32 (64 * n)) : AtEntry s' b (m + n) := by
  rw [AtEntry, h, hk, add_ofNat_ofNat]; congr 2; omega_arith

/-- The two rounds of a pair, `kp += 128` and the comparison of `kp` with the
group's end. -/
theorem pair_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 1 < nk) (hm34 : m + 2 ≤ 34)
    {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    ∃ s', runBlock isa pairBody s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (m + 2) ∧
      Halves s' (fun b => pair (E m) (E (m + 1)) (S b)) ∧
      s'.z = (s'.gpr kp - slotW s grpSlot == 0) ∧
      (∀ k, keySlot ≤ k → k < slots → slotW s' k = slotW s k) := by
  obtain ⟨h1, h2⟩ := hS
  obtain ⟨s₁, e₁, c₁, k₁, d₁, o₁, a₁⟩ := round_step hp hc (off := 0) (src := d1Slot) (dst := d2Slot)
    preL0_check mid0_check post2_check (.inl ⟨rfl, rfl, rfl⟩) hk (by omega_arith) hm34 h1 h2
  have hk₁ : AtEntry s₁ (s₀.gpr sb) m := by rw [AtEntry, k₁]; exact hk
  have h1' : W32.HalfRel (half s₁ d1Slot) (fun b => (S b).1) := h1.congr fun i hi => o₁ i hi
  obtain ⟨s₂, e₂, c₂, k₂, d₂, o₂, a₂⟩ := round_step hp c₁ (off := 16) (src := d2Slot) (dst := d1Slot)
    preL16_check mid16_check post1_check (.inr ⟨rfl, rfl, rfl⟩) hk₁ (by omega_arith) hm34 d₁ h1'
  have d₂' : W32.HalfRel (half s₂ d2Slot) (fun b => (S b).2 ^^^ Spec.Camellia.f (S b).1 (E (m + 0 / 16))) :=
    d₁.congr fun i hi => o₂ i hi
  let s₃ := s₂.setReg kp (s₂.gpr kp + BitVec.ofNat 32 128)
  have ok₃ : Scr s₃ (s₃.gpr sb) := by
    have : s₃.gpr sb = s₀.gpr sb := (RegUpd.gpr_setReg_of_ne _ _ (by decide)).trans c₂.base
    rw [this]; exact ⟨by rw [show s₃.wr = s₂.wr from rfl, c₂.wr]; exact hp.scr.wr, hp.scr.fit⟩
  have hfit := hp.scr.fit
  rw [slots_eq] at hfit
  have hs₃ : ∀ k, slotW s₃ k = slotW s₂ k := fun k => slotW_setReg _ _ (by decide) k
  have g₄ : ∀ r, r ≠ t0 → r ≠ kp →
      (subFlags (s₃.setReg t0 (slotW s₃ grpSlot)) (s₃.gpr kp) (slotW s₃ grpSlot)).gpr r = s₂.gpr r :=
    fun r h1 h2 => by
      rw [subFlags_gpr, RegUpd.gpr_setReg_of_ne _ _ h1, RegUpd.gpr_setReg_of_ne _ _ h2]
  have hs₄ : ∀ k, slotW (subFlags (s₃.setReg t0 (slotW s₃ grpSlot)) (s₃.gpr kp) (slotW s₃ grpSlot)) k =
      slotW s₂ k := fun k => by
    simp only [slotW, subFlags_mem, RegUpd.mem_setReg, g₄ sb (by decide) (by decide)]
    rfl
  have kp₄ : (subFlags (s₃.setReg t0 (slotW s₃ grpSlot)) (s₃.gpr kp) (slotW s₃ grpSlot)).gpr kp =
      s.gpr kp + BitVec.ofNat 32 128 := by
    rw [subFlags_gpr, RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self, k₂, k₁]
  refine ⟨subFlags (s₃.setReg t0 (slotW s₃ grpSlot)) (s₃.gpr kp) (slotW s₃ grpSlot), ?_, ?_, ?_, ⟨?_, ?_⟩, ?_,
    fun k h1 h2 => ?_⟩
  · rw [pairBody, runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some,
      show ([.dp .add kp kp (.imm 128), ldS t0 grpSlot, .cmp kp (.reg t0)] : List Instr) =
        [.dp .add kp kp (.imm (BitVec.ofNat 32 128))] ++ [ldS t0 grpSlot, .cmp kp (.reg t0)] from rfl,
      runBlock_app, addKp_ok _ _ encodable_128, Option.bind_some,
      cmpSlot_ok ok₃ (by rw [grpSlot_eq, slots_eq]; decide) (by rw [grpSlot_eq]; decide)]
  · refine c₂.step rfl rfl (fun r h1 h2 => g₄ r (fun h => h1 (h ▸ by decide)) h2) (by exact Frame.refl _ _)
  · exact hk.add (n := 2) kp₄
  · exact d₂.congr fun i _ => hs₄ _
  · exact d₂'.congr fun i _ => hs₄ _
  · have : s₃.gpr kp = s.gpr kp + BitVec.ofNat 32 128 := by
      rw [RegUpd.gpr_setReg_self, k₂, k₁]
    rw [subFlags_z, kp₄, this, hs₃, a₂ _ (by rw [grpSlot_eq, keySlot_eq]; decide)
      (by rw [grpSlot_eq, slots_eq]; decide), a₁ _ (by rw [grpSlot_eq, keySlot_eq]; decide)
      (by rw [grpSlot_eq, slots_eq]; decide)]
  · rw [hs₄, a₂ k h1 h2, a₁ k h1 h2]

/-- A frame of the rounds' working space keeps the slots from the table on. -/
theorem slot_above_frame {s s' : State} (hfit : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32)
    (hb : s'.gpr sb = s.gpr sb) (hf : Frame [slotRegion layerCfg s] s.mem s'.mem) {k : Nat}
    (h1 : keySlot ≤ k) (h2 : k < slots) : slotW s' k = slotW s k := by
  simp only [slotW, hb]
  refine hf.readW (r := ⟨wordAddr (s.gpr sb) k, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact slot_disjoint_base hfit h2 h1

/-- The FL layer: FLINV on `D2` with entry `m + 1`, FL on `D1` with entry `m`. -/
theorem fl_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 1 < nk) (hm34 : m + 2 ≤ 34)
    {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    ∃ s', runBlock isa flLayer s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (m + 2) ∧
      Halves s' (fun b => (Spec.Camellia.fl (S b).1 (E m), Spec.Camellia.flinv (S b).2 (E (m + 1)))) ∧
      (∀ k, keySlot ≤ k → k < slots → slotW s' k = slotW s k) := by
  obtain ⟨h1, h2⟩ := hS
  have hok := hc.ok hp hk hm34
  have hfit : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32 := by rw [hc.base]; exact hp.scr.fit
  have hK1 : W32.HalfRel (fun j => keyW s (16 + j)) fun _ => E (m + 1) := by
    simpa using hc.keyRel hp hk (e := 1) (by omega_arith)
  obtain ⟨s₁, e₁, d₁, p₁⟩ := flinv_ok hok (d := d2Slot) (off := 16) (by decide) (by decide) h2 hK1
  have hK0 : W32.HalfRel (fun j => keyW s₁ (0 + j)) fun _ => E m := by
    have := hc.keyRel hp hk (e := 0) (by omega_arith)
    refine (this.congr fun j hj => ?_).congr_right fun _ _ => by simp
    rw [p₁.keys _ (by omega_arith)]
  have h1' : W32.HalfRel (half s₁ d1Slot) (fun b => (S b).1) :=
    h1.congr fun i hi => p₁.slots _ (by rw [d1Slot_eq, keySlot_eq]; omega_arith) (.inl (by rw [d1Slot_eq, d2Slot_eq]; omega_arith))
  obtain ⟨s₂, e₂, d₂, p₂⟩ := fl_ok p₁.ok (d := d1Slot) (off := 0) (by decide) (by decide) h1' hK0
  have b₁ : s₁.gpr sb = s.gpr sb := p₁.gpr _ (by decide)
  have b₂ : s₂.gpr sb = s.gpr sb := (p₂.gpr _ (by decide)).trans b₁
  have kp₂ : s₂.gpr kp = s.gpr kp := (p₂.gpr _ (by decide)).trans (p₁.gpr _ (by decide))
  have hs₃ : ∀ k, slotW (s₂.setReg kp (s₂.gpr kp + BitVec.ofNat 32 128)) k = slotW s₂ k :=
    fun k => slotW_setReg _ _ (by decide) k
  refine ⟨s₂.setReg kp (s₂.gpr kp + BitVec.ofNat 32 128), ?_, ?_, ?_, ⟨?_, ?_⟩, fun k k1 k2 => ?_⟩
  · rw [show flLayer = flinvCode d2Slot 16 ++ flCode d1Slot 0 ++
        [.dp .add kp kp (.imm (BitVec.ofNat 32 128))] from rfl,
      runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, addKp_ok _ _ encodable_128]
  · have c₁ := hc.stepL p₁.rd p₁.wr (fun r h1 _ => p₁.gpr r h1) p₁.frame
    have e : slotRegion layerCfg s₁ = slotRegion layerCfg s := by simp only [slotRegion, layerCfg, b₁]
    have c₂ := c₁.stepL p₂.rd p₂.wr (fun r h1 _ => p₂.gpr r h1) p₂.frame
    exact c₂.step rfl rfl (fun r _ h2 => RegUpd.gpr_setReg_of_ne _ _ h2) (Frame.refl _ _)
  · exact hk.add (n := 2) (by rw [RegUpd.gpr_setReg_self, kp₂])
  · exact d₂.congr fun i _ => by simp only [half]; rw [hs₃]
  · refine d₁.congr fun i hi => ?_
    simp only [half]
    rw [hs₃, p₂.slots _ (by rw [d2Slot_eq, keySlot_eq]; omega_arith) (.inr (by rw [d1Slot_eq, d2Slot_eq]; omega_arith))]
  · rw [hs₃, slot_above_frame (by rw [b₁]; exact hfit) (by rw [p₂.gpr _ (by decide)]) p₂.frame k1 k2,
      slot_above_frame hfit b₁ p₁.frame k1 k2]

/-! ## Groups of six rounds -/

theorem Ctx.scr {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s) :
    Scr s (s.gpr sb) := ⟨by rw [hc.wr, hc.base]; exact hp.scr.wr, by rw [hc.base]; exact hp.scr.fit⟩

theorem encodable_384 : encodable (BitVec.ofNat 32 384) = true := by decide

/-- `add t0, kp, #384; str t0, [sb, #4 grpSlot]`: the end of the group's pairs. -/
theorem setGrp_ok {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s) :
    ∃ s', runBlock isa [.dp .add t0 kp (.imm 384), stS grpSlot t0] s = some s' ∧ Ctx s₀ s' ∧
      s'.gpr kp = s.gpr kp ∧ slotW s' grpSlot = s.gpr kp + BitVec.ofNat 32 384 ∧
      (∀ k < slots, k ≠ grpSlot → slotW s' k = slotW s k) := by
  have hs := hc.scr hp
  have hfit := hs.fit
  rw [slots_eq] at hfit
  let s₁ := s.setReg t0 (s.gpr kp + BitVec.ofNat 32 384)
  have b₁ : s₁.gpr sb = s.gpr sb := RegUpd.gpr_setReg_of_ne _ _ (by decide)
  have hst : exec (stS grpSlot t0) s₁ =
      some { s₁ with mem := s₁.mem.writeW (wordAddr (s₁.gpr sb) grpSlot) (s₁.gpr t0) } :=
    exec_str (by rw [grpSlot_eq]; decide) (by rw [b₁]; exact hs.slot_in (by rw [grpSlot_eq, slots_eq]; decide))
  refine ⟨{ s₁ with mem := s₁.mem.writeW (wordAddr (s₁.gpr sb) grpSlot) (s₁.gpr t0) }, ?_, ?_, ?_, ?_, fun k hk hne => ?_⟩
  · have ha : exec (.dp .add t0 kp (.imm (BitVec.ofNat 32 384))) s = some s₁ := by
      simp only [exec, Op2.eval, encodable_384, ↓reduceIte, Option.map_some]; rfl
    rw [show ([.dp .add t0 kp (.imm 384), stS grpSlot t0] : List Instr) =
      [.dp .add t0 kp (.imm (BitVec.ofNat 32 384)), stS grpSlot t0] from rfl, runBlock_cons, ha, runStep_some,
      runBlock_cons, hst, runStep_some, runBlock_nil]
  · refine hc.step rfl rfl (fun r h1 h2 => RegUpd.gpr_setReg_of_ne _ _ (fun h => h1 (by rw [h]; decide))) ?_
    refine (Frame.refl _ _).writeW (r := ⟨State.addr (s₀.gpr sb + BitVec.ofNat 32 (4 * grpSlot)), 4⟩)
      (by simp [ctxRegions]) _ ?_
    rw [b₁, hc.base]; exact Region.contains_self _ _
  · exact RegUpd.gpr_setReg_of_ne (r := t0) (r' := kp) s (s.gpr kp + BitVec.ofNat 32 384) (by decide)
  · show (s₁.mem.writeW (wordAddr (s₁.gpr sb) grpSlot) (s₁.gpr t0)).readW (wordAddr (s₁.gpr sb) grpSlot) 32 = _
    rw [Mem.readW_writeW_self32]; exact RegUpd.gpr_setReg_self _ _ _
  · rw [slots_eq] at hk
    show (s₁.mem.writeW (wordAddr (s₁.gpr sb) grpSlot) (s₁.gpr t0)).readW (wordAddr (s₁.gpr sb) k) 32 = _
    rw [Mem.readW_writeW_sep (slot_sep _ (by rw [b₁]; omega_arith) (by rw [b₁, grpSlot_eq]; omega_arith) hne) (by decide), b₁]
    rfl

/-- `ldr t0, [sb, #4 endSlot]; cmp kp, t0`: whether `kp` is at the postwhitening's entry. -/
theorem atEnd_ok {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m ≤ 8 * g + 2) :
    ∃ s', runBlock isa atEnd s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) m ∧
      s'.z = decide (m = 8 * g) ∧ (∀ k, slotW s' k = slotW s k) := by
  have hs := hc.scr hp.toKeyCtx
  have hg4 : g ≤ 4 := by rcases hp.hg with h | h <;> omega_arith
  refine ⟨_, cmpSlot_ok hs (by rw [endSlot_eq, slots_eq]; decide) (by rw [endSlot_eq]; decide),
    hc.step rfl rfl (fun r h1 h2 => by rw [subFlags_gpr, RegUpd.gpr_setReg_of_ne _ _ (fun h => h1 (by rw [h]; decide))])
      (Frame.refl _ _), ?_, ?_, fun k => ?_⟩
  · rw [AtEntry, subFlags_gpr, RegUpd.gpr_setReg_of_ne _ _ (by decide)]; exact hk
  · rw [subFlags_z, hc.slot hp.scr.fit (by rw [endSlot_eq, slots_eq]; decide) (by rw [endSlot_eq, keySlot_eq]; decide)
      (by rw [endSlot_eq, grpSlot_eq]; decide) (.inl (by rw [endSlot_eq, tailSlot_eq]; decide)), hp.bound, hk,
      show 512 * g = 64 * (8 * g) by omega_arith, entry_beq _ (by rw [keySlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith)]
    simp only [decide_eq_decide]; omega_arith
  · simp only [slotW, subFlags_mem, subFlags_gpr, RegUpd.mem_setReg, RegUpd.gpr_setReg_of_ne _ _ (show sb ≠ t0 by decide)]

theorem eval_ne (s : State) : isa.eval .ne s = some !s.z := rfl

theorem eval_eq (s : State) : isa.eval .eq s = some s.z := rfl

/-- A group of six rounds, then FL and FLINV unless it is the last. -/
theorem group_wp {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {i : Nat} (hi : i < g) (hk : AtEntry s (s₀.gpr sb) (2 + 8 * i)) {S : Nat → BitVec 64 × BitVec 64}
    (hS : Halves s S) :
    WP isa groupBody s fun s' => Ctx s₀ s' ∧ Halves s' (fun b => group g E (S b) i) ∧
      AtEntry s' (s₀.gpr sb) (if i + 1 < g then 2 + 8 * (i + 1) else 8 * g) ∧
      s'.z = decide (i + 1 = g) := by
  have hg4 : g ≤ 4 := by rcases hp.hg with h | h <;> omega_arith
  let b := s₀.gpr sb
  -- The end of the pairs.
  obtain ⟨s₁, e₁, c₁, k₁, v₁, o₁⟩ := setGrp_ok hp.toKeyCtx hc
  have hk₁ : AtEntry s₁ b (2 + 8 * i) := by rw [AtEntry, k₁]; exact hk
  have hv₁ : slotW s₁ grpSlot = b + BitVec.ofNat 32 (4 * keySlot + 64 * (8 + 8 * i)) := by
    rw [v₁, hk, add_ofNat_ofNat]; congr 2; omega_arith
  have hS₁ : Halves s₁ S := hS.congr fun k h1 h2 =>
    o₁ k (by rw [slots_eq]; rw [keySlot_eq] at h2; omega_arith) (by rw [grpSlot_eq]; rw [keySlot_eq] at h2; omega_arith)
  unfold groupBody
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  -- The pairs.
  let Inv : Nat → State → Prop := fun n s' => ∃ p, n = 3 - p ∧ p < 3 ∧ Ctx s₀ s' ∧
    AtEntry s' b (2 + 8 * i + 2 * p) ∧ slotW s' grpSlot = slotW s₁ grpSlot ∧
    Halves s' (fun b => pairsN E i p (S b))
  let Mid : State → Prop := fun s' => Ctx s₀ s' ∧ AtEntry s' b (8 + 8 * i) ∧
    Halves s' (fun b => pairsN E i 3 (S b))
  refine WP.seq (WP.mono (Q := Mid) (WP.loop Inv (fun n s' hs' => ?_) 3 s₁
    ⟨0, rfl, by omega_arith, c₁, by simpa using hk₁, rfl, by simpa [pairsN] using hS₁⟩) fun s₂ h₂ => ?_)
  · obtain ⟨p, rfl, hp3, hc', hk', hg', hS'⟩ := hs'
    obtain ⟨s'', e'', c'', k'', S'', z'', a''⟩ := pair_step hp.toKeyCtx hc' hk' (by omega_arith) (by omega_arith) hS'
    refine WP.of_runBlock ⟨s'', e'', ?_⟩
    have hz : s''.z = decide (p + 1 = 3) := by
      rw [z'', show s''.gpr kp = _ from k'', hg', hv₁, entry_beq b (by rw [keySlot_eq]; omega_arith)
        (by rw [keySlot_eq]; omega_arith)]
      simp only [decide_eq_decide]; omega_arith
    have hS'' : Halves s'' (fun b => pairsN E i (p + 1) (S b)) := by
      simpa only [pairsN_succ, show 2 + 8 * i + 2 * p + 1 = 3 + 8 * i + 2 * p by omega_arith] using S''
    by_cases hp2 : p + 1 = 3
    · refine .inl ⟨(eval_ne s'').trans (by rw [hz]; simp [hp2]), c'', ?_, by rw [← hp2]; exact hS''⟩
      rw [AtEntry, show s''.gpr kp = _ from k'', show 2 + 8 * i + 2 * p + 2 = 8 + 8 * i by omega_arith]
    · refine .inr ⟨(eval_ne s'').trans (by rw [hz]; simp [hp2]), 3 - (p + 1), by omega_arith, p + 1, rfl, by omega_arith, c'',
        by rw [AtEntry, show s''.gpr kp = _ from k'', show 2 + 8 * i + 2 * p + 2 = 2 + 8 * i + 2 * (p + 1) by omega_arith],
        by rw [a'' _ (by rw [grpSlot_eq, keySlot_eq]; decide) (by rw [grpSlot_eq, slots_eq]; decide), hg'], hS''⟩
  · obtain ⟨hc₂, hk₂, hS₂⟩ := h₂
    obtain ⟨s₃, e₃, hc₃, hk₃, hz₃, sl₃⟩ := atEnd_ok hp hc₂ hk₂ (by omega_arith)
    have hS₃ : Halves s₃ (fun b => pairsN E i 3 (S b)) := hS₂.congr fun k _ _ => sl₃ k
    refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
    refine WP.seq (WP.ite (!decide (8 + 8 * i = 8 * g)) ((eval_ne s₃).trans (by rw [hz₃])) (fun ht => ?_)
      (fun hf => ?_))
    · have hlt : i + 1 < g := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at ht; omega_arith
      obtain ⟨s₄, e₄, c₄, k₄, S₄, -⟩ := fl_step hp.toKeyCtx hc₃ hk₃ (by omega_arith) (by omega_arith) hS₃
      refine WP.of_runBlock ⟨s₄, e₄, ?_⟩
      have hk₄ : AtEntry s₄ b (2 + 8 * (i + 1)) := by
        rw [AtEntry, show s₄.gpr kp = _ from k₄, show 8 + 8 * i + 2 = 2 + 8 * (i + 1) by omega_arith]
      obtain ⟨s₅, e₅, c₅, k₅, z₅, sl₅⟩ := atEnd_ok hp c₄ hk₄ (by omega_arith)
      refine WP.of_runBlock ⟨s₅, e₅, c₅, ?_, ?_, ?_⟩
      · have hG : (fun b => group g E (S b) i) = fun b =>
            (Spec.Camellia.fl (pairsN E i 3 (S b)).1 (E (8 + 8 * i)),
              Spec.Camellia.flinv (pairsN E i 3 (S b)).2 (E (8 + 8 * i + 1))) :=
          funext fun b => by
            rw [group_eq, show 8 + 8 * i + 1 = 9 + 8 * i by omega_arith]; simp only [hlt, ↓reduceIte]
        rw [hG]
        exact S₄.congr fun k _ _ => sl₅ k
      · simp only [hlt, ↓reduceIte]; exact k₅
      · rw [z₅]; simp only [decide_eq_decide]; omega_arith
    · have heq : i + 1 = g := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at hf; omega_arith
      refine WP.of_runBlock ⟨s₃, rfl, ?_⟩
      obtain ⟨s₅, e₅, c₅, k₅, z₅, sl₅⟩ := atEnd_ok hp hc₃ hk₃ (by omega_arith)
      refine WP.of_runBlock ⟨s₅, e₅, c₅, ?_, ?_, ?_⟩
      · have hG : (fun b => group g E (S b) i) = fun b => pairsN E i 3 (S b) :=
          funext fun b => by rw [group_eq]; simp only [show ¬ i + 1 < g by omega_arith, ↓reduceIte]
        rw [hG]
        exact hS₃.congr fun k _ _ => sl₅ k
      · simp only [show ¬ i + 1 < g by omega_arith, ↓reduceIte]
        rw [show 8 * g = 8 + 8 * i by omega_arith]; exact k₅
      · rw [z₅]; simp only [decide_eq_decide]; omega_arith

theorem WP.sp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h; exact ⟨t, s', he, hq, Exec.sp he⟩

theorem addr_toNat (b : BitVec 32) : (State.addr b).toNat = b.toNat := by
  have := b.isLt; simp [State.addr]; omega_arith
/-- The rounds' regions are in the scratch buffer. -/
theorem ctx_sub_scr {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) :
    ∀ r ∈ ctxRegions b, Region.Sub r ⟨State.addr b, 4 * slots⟩ := by
  have hb := addr_toNat b
  rw [slots_eq] at hfit
  intro r hr
  simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Region.sub_prefix (by rw [slots_eq, keySlot_eq] <;> omega_arith)
  · rw [VG.Arm.addr_add (by rw [grpSlot_eq] <;> omega_arith)]
    exact VG.Offset.sub_base _ (by rw [slots_eq, grpSlot_eq] <;> omega_arith)
  · rw [VG.Arm.addr_add (by rw [tailSlot_eq] <;> omega_arith)]
    exact VG.Offset.sub_base _ (by rw [slots_eq, tailSlot_eq] <;> omega_arith)

end VG.Proof.Camellia.Arm
