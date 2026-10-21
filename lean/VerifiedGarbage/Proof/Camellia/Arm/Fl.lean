module

public import VerifiedGarbage.Proof.Camellia.Arm.Round
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.PlainSimp

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
  exec_ldr (by simp [keySlot] at hk; omega) (slot_in hok hk)

theorem exec_stS {s : State} (hok : Ok layerCfg s) {r : Reg} {k : Nat} (hk : k < keySlot) :
    exec (stS k r) s = some { s with mem := s.mem.writeW (wordAddr (s.gpr sb) k) (s.gpr r) } :=
  exec_str (by simp [keySlot] at hk; omega) (hok.slotIn k hk)

theorem exec_ldK {s : State} (hok : Ok layerCfg s) {r : Reg} {w : Nat} (hw : w < 32) :
    exec (.ldr r kp (4 * w)) s = some (s.setReg r (keyW s w)) :=
  exec_ldr (by omega) (hok.extIn w hw)

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

theorem keyW_setReg (s : State) {r : Reg} (x : BitVec 32) (h : r ≠ kp) (k : Nat) :
    keyW (s.setReg r x) k = keyW s k := by
  simp only [keyW, RegUpd.mem_setReg, RegUpd.gpr_setReg_of_ne s x (Ne.symm h)]

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
  exact Mem.readW_writeW_sep (slot_sep _ (by omega) (by omega) hne) (by decide)

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

theorem Keeps.keyW {s s' : State} {d : Reg} (h : Keeps s s' d) (hd : d ≠ kp) (k : Nat) :
    keyW s' k = keyW s k := by
  simp only [Arm.keyW, h.mem, h.gpr kp (Ne.symm hd)]

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
  rw [run_ldK hok (by omega)]
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
  rw [run_ldK hok (by omega)]
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
  | 0, _ => ⟨s, runBlock_nil, hok, fun _ _ _ => rfl, fun k _ => by simp only [show ¬ (d + 8 ≤ k ∧ k < d + 8 + 0) by omega, ↓reduceIte],
      fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨s₁, h₁, ok₁, g₁, m₁, k₁, rd₁, wr₁, sp₁, f₁⟩ := flRot_ok hok hd hw n (by omega)
    obtain ⟨s₂, h₂, ok₂, g₂, m₂, k₂, rd₂, wr₂, sp₂, f₂⟩ := flRotStep_ok ok₁ (d := d) (off := off) (j := n)
      (by omega) hw
    have hq : ∀ i, s₁.gpr (q i) = s.gpr (q i) := fun i => g₁ _ (q_ne i).1 (q_ne i).2.1
    refine ⟨s₂, by rw [runBlock_range_succ, h₁, Option.bind_some, h₂], ok₂, fun r h1 h2 => (g₂ r h1 h2).trans (g₁ r h1 h2),
      fun k hk => ?_, fun w hw' => (k₂ w hw').trans (k₁ w hw'), rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_⟩
    · rw [m₂ k hk]
      have hrv : rotV (fun i => s₁.gpr (q i)) (fun i => keyW s₁ (off + i)) n =
          rotV (fun i => s.gpr (q i)) (fun i => keyW s (off + i)) n := by
        simp only [rotV, hq, k₁ _ (show off + (n + 7) % 8 < 32 by omega)]
      split
      · rename_i h; subst h
        rw [m₁ _ hk, iteNeg (by omega), hrv, itePos (by omega), show d + 8 + n - (d + 8) = n by omega]
      · rename_i h
        rw [m₁ _ hk]
        by_cases h' : d + 8 ≤ k ∧ k < d + 8 + n
        · rw [itePos h', itePos (by omega)]
        · rw [iteNeg h', iteNeg (by omega)]
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
  | 0, _ => ⟨s, runBlock_nil, hok, fun j _ => by simp only [show ¬ j < 0 by omega, ↓reduceIte],
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | n + 1, hn => by
    obtain ⟨s₁, h₁, ok₁, g₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := flOr_ok hok hd hw n (by omega)
    obtain ⟨s₂, h₂, ok₂, v₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := flOrStep_ok ok₁ (d := d) (off := off) (j := n)
      (by omega) (by omega) hw
    refine ⟨s₂, by rw [runBlock_range_succ, h₁, Option.bind_some, h₂], ok₂, fun j hj => ?_,
      fun r hr => ?_, m₂.trans m₁, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁⟩
    · have hs : slotW s₁ (d + 8 + n) = slotW s (d + 8 + n) := by
        simp only [slotW, m₁, (o₁ sb (by decide))]
      have hkw : keyW s₁ (off + 8 + n) = keyW s (off + 8 + n) := by
        simp only [keyW, m₁, (o₁ kp (by decide))]
      by_cases hjn : j = n
      · subst hjn
        rw [v₂, g₁ j hj, iteNeg (by omega), itePos (by omega), hs, hkw]
      · rw [o₂ _ (q_ne j).1 (q_ne j).2.1 (fun h => hjn (q_inj j hj n (by omega) h)), g₁ j hj]
        by_cases hjn' : j < n
        · rw [itePos hjn', itePos (by omega)]
        · rw [iteNeg hjn', iteNeg (by omega)]
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
  | 0, _ => ⟨s, runBlock_nil, hok, fun j _ => by simp only [show ¬ j < 0 by omega, ↓reduceIte],
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | n + 1, hn => by
    obtain ⟨s₁, h₁, ok₁, g₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := loadL_ok hok hd n (by omega)
    obtain ⟨-, -, nsb, nkp⟩ := q_ne n
    have k₂ := keeps_setReg s₁ (slotW s₁ (d + n)) nsb nkp
    have hs : slotW s₁ (d + n) = slotW s (d + n) := by simp only [slotW, m₁, o₁ sb (by decide)]
    refine ⟨_, by rw [runBlock_map_succ, h₁, Option.bind_some, run_ldS ok₁ (by omega), runBlock_nil],
      k₂.ok ok₁, fun j hj => ?_, fun r hr => ?_, m₁, rd₁, wr₁, sp₁⟩
    · by_cases hjn : j = n
      · subst hjn; rw [RegUpd.gpr_setReg_self, hs, itePos (by omega)]
      · rw [k₂.gpr _ (fun h => hjn (q_inj j hj n (by omega) h)), g₁ j hj]
        by_cases hjn' : j < n
        · rw [itePos hjn', itePos (by omega)]
        · rw [iteNeg hjn', iteNeg (by omega)]
    · rw [k₂.gpr _ (fun h => hr (by rw [h]; exact q_mem n)), o₁ r hr]

theorem storeL_ok {s : State} (hok : Ok layerCfg s) {d : Nat} (hd : d + 8 ≤ keySlot) : ∀ n ≤ 8,
    ∃ s', runBlock isa ((List.range n).map fun j => stS (d + j) (q j)) s = some s' ∧ Ok layerCfg s' ∧
      (∀ k < keySlot, slotW s' k = if d ≤ k ∧ k < d + n then s.gpr (q (k - d)) else slotW s k) ∧
      (∀ w < 32, keyW s' w = keyW s w) ∧ (∀ r, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [slotRegion layerCfg s] s.mem s'.mem
  | 0, _ => ⟨s, runBlock_nil, hok, fun k _ => by simp only [show ¬ (d ≤ k ∧ k < d + 0) by omega, ↓reduceIte],
      fun _ _ => rfl, fun _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨s₁, h₁, ok₁, m₁, k₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := storeL_ok hok hd n (by omega)
    have b₁ : s₁.gpr sb = s.gpr sb := g₁ sb
    refine ⟨{ s₁ with mem := s₁.mem.writeW (wordAddr (s₁.gpr sb) (d + n)) (s₁.gpr (q n)) },
      by rw [runBlock_map_succ, h₁, Option.bind_some, run_stS ok₁ (by omega), runBlock_nil],
      ok_setMem ok₁ _, fun k hk => ?_, fun w hw => ?_, g₁, rd₁, wr₁, sp₁, ?_⟩
    · show (s₁.mem.writeW (wordAddr (s₁.gpr sb) (d + n)) (s₁.gpr (q n))).readW (wordAddr (s₁.gpr sb) k) 32 = _
      by_cases hkn : k = d + n
      · subst hkn
        rw [slot_writeW_self, itePos (by omega), g₁, show d + n - d = n by omega]
      · rw [slot_writeW ok₁ (by omega) hk hkn]
        show slotW s₁ k = _
        rw [m₁ k hk]
        by_cases h' : d ≤ k ∧ k < d + n
        · rw [itePos h', itePos (by omega)]
        · rw [iteNeg h', iteNeg (by omega)]
    · show (s₁.mem.writeW (wordAddr (s₁.gpr sb) (d + n)) (s₁.gpr (q n))).readW (wordAddr (s₁.gpr kp) w) 32 = _
      rw [key_writeW ok₁ (by omega) hw, k₁ w hw]
    · have e : slotRegion layerCfg s₁ = slotRegion layerCfg s := by simp only [slotRegion, layerCfg, b₁]
      exact f₁.trans (e ▸ exec_stS_frame ok₁ (by omega) _)

theorem getLsbD_ror8 (x : BitVec 32) {p : Nat} (hp : p < 32) :
    (x.rotateRight 8).getLsbD p = x.getLsbD ((p + 8) % 32) := by
  rw [BitVec.getLsbD_rotateRight]
  split
  · congr 1; omega
  · rename_i h; simp only [Nat.reduceMod, Nat.not_lt] at h; simp only [hp, decide_true, Bool.true_and]
    congr 1; omega

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
    simp only [mixed, show ¬ 8 + j < 8 by omega, ↓reduceIte, hjj]
    rw [m _ (by omega), itePos (by omega), BitVec.getLsbD_xor, rotV_bit hp,
      show d + (8 + j) - (d + 8) = j by omega]
  · rw [m k' hk', iteNeg (by omega)]

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
  · simp only [mixed, show ¬ 8 + j < 8 by omega, ↓reduceIte, hs]
  · simp only [mixed, hj, ↓reduceIte, show ¬ 8 + j < 8 by omega]
    rw [g j hj, itePos hj, BitVec.getLsbD_xor, BitVec.getLsbD_or, Bool.or_comm,
      show d + (8 + j) = d + 8 + j by omega, show off + (8 + j) = off + 8 + j by omega]

theorem loadL_mixed {s : State} (hok : Ok layerCfg s) {d : Nat} (hd : d + 16 ≤ keySlot) :
    ∃ s', runBlock isa (loadL d) s = some s' ∧ Ok layerCfg s' ∧ (∀ i < 16, mixed s' d i = half s d i) ∧
      (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s', h, ok, g, o, m, rd, wr, sp⟩ := loadL_ok hok (d := d) (by omega) 8 (Nat.le_refl _)
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
  obtain ⟨s', h, ok, m, k, g, rd, wr, sp, f⟩ := storeL_ok hok (d := d) (by omega) 8 (Nat.le_refl _)
  refine ⟨s', h, ok, fun i hi => ?_, fun k' hk' h' => ?_, k, g, rd, wr, sp, f⟩
  · simp only [mixed, half]
    rw [m _ (by omega)]
    split
    · rename_i h; rw [itePos (by omega), show d + i - d = i by omega]
    · rw [iteNeg (by omega)]
  · rw [m _ hk', iteNeg (by omega)]

theorem fl_ok {s : State} (hok : Ok layerCfg s) {d off : Nat} (hd : d + 16 ≤ keySlot) (hw : off + 16 ≤ 32)
    {x : Nat → BitVec 64} {k : BitVec 64} (hQ : W32.HalfRel (half s d) x)
    (hK : W32.HalfRel (fun i => keyW s (off + i)) fun _ => k) :
    ∃ s', runBlock isa (flCode d off) s = some s' ∧
      W32.HalfRel (half s' d) (fun b => Spec.Camellia.fl (x b) k) ∧ FlPost s s' d := by
  obtain ⟨s₁, h₁, ok₁, x₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := loadL_mixed hok hd
  have kw₁ : ∀ w, keyW s₁ w = keyW s w := fun w => by simp only [keyW, m₁, o₁ kp (by decide)]
  obtain ⟨s₂, h₂, r₂, ok₂, o₂, sl₂, kw₂, rd₂, wr₂, sp₂, f₂⟩ := flRot_step ok₁ hd (off := off) (by omega)
  obtain ⟨s₃, h₃, r₃, ok₃, o₃, m₃, rd₃, wr₃, sp₃⟩ := flOr_step ok₂ hd hw
  obtain ⟨s₄, h₄, ok₄, x₄, sl₄, kw₄, o₄, rd₄, wr₄, sp₄, f₄⟩ := storeL_mixed ok₃ hd
  have hK₁ : W32.HalfRel (fun i => keyW s₁ (off + i)) fun _ => k := hK.congr fun i _ => kw₁ _
  have hK₂ : W32.HalfRel (fun i => keyW s₂ (off + i)) fun _ => k :=
    hK₁.congr fun i hi => kw₂ _ (by omega)
  have hr := W32.fl_rel (hQ.congr fun i hi => x₁ i hi) hK₁ r₂
    ⟨r₃.1, fun j hj p hp => by rw [r₃.2 j hj p hp]; dsimp only; rw [kw₂ _ (by omega)]⟩
  have b₂ : s₂.gpr sb = s.gpr sb := by rw [o₂ _ (by decide) (by decide), o₁ _ (by decide)]
  have s₃eq : ∀ k, slotW s₃ k = slotW s₂ k := fun k => by simp only [slotW, m₃, o₃ sb (by decide)]
  refine ⟨s₄, ?_, hr.congr fun i hi => x₄ i hi, ⟨ok₄, fun k' hk' h' => ?_, fun w hw' => ?_, fun r hr => ?_,
    by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁], by rw [sp₄, sp₃, sp₂, sp₁], ?_⟩⟩
  · rw [flCode, runBlock_app, runBlock_app, runBlock_app, h₁, Option.bind_some, h₂, Option.bind_some, h₃,
      Option.bind_some, h₄]
  · rw [sl₄ k' hk' (by omega), s₃eq, sl₂ k' hk' (by omega)]
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
  obtain ⟨s₃, h₃, r₃, ok₃, o₃, sl₃, kw₃, rd₃, wr₃, sp₃, f₃⟩ := flRot_step ok₂ hd (off := off) (by omega)
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
  · rw [sl₄ k' hk' (by omega), sl₃ k' hk' (by omega)]
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
