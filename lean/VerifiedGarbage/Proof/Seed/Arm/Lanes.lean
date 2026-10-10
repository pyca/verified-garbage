import VerifiedGarbage.Impl.Seed.Arm.Ecb
import VerifiedGarbage.Proof.Seed.Arm.G8
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The arrays of 32-bit words in the scratch buffer

As on AArch64 (`Proof/Seed/AArch64/Lanes.lean`): the ECB code keeps eight
lanes of each of its arrays (`G`'s words, `a`, `c`, `d` and the blocks'
words) in the scratch buffer at `r8`: lane `b` of the array at slot `k` is
slot `k + b` (`lv`). This file has the slots' loads and stores, and
`lanes_ok`, which runs a step written for one lane (`lanes8 f`, `f b`
touching only lane `b` of each array) on all eight.
-/

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Seed.Arm
open VG.Impl.Aes.Arm (sb t0 t1 u7 kp ldS stS eorR)
open VG.Arm.Straight (wordAddr slot_sep slot_contains)

theorem slots_eq : slots = 188 := rfl

/-- The scratch buffer. -/
def scratchR (s : State) : Region := ⟨State.addr (s.gpr sb), 4 * slots⟩

/-- The scratch buffer is writable, and does not wrap around. -/
structure Room (s : State) : Prop where
  mem : scratchR s ∈ s.wr
  fit : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32

theorem Room.congr {s s' : State} (h : Room s) (hb : s'.gpr sb = s.gpr sb) (hw : s'.wr = s.wr) :
    Room s' :=
  ⟨by unfold scratchR; rw [hb, hw]; exact h.mem, by rw [hb]; exact h.fit⟩

theorem toNat_addr (b : BitVec 32) : (State.addr b).toNat = b.toNat := by
  have := b.isLt; simp [State.addr]; omega

/-- Slot `k`, as a 64-bit offset from the base. -/
theorem slot_addr {b : BitVec 32} {k : Nat} (hfit : b.toNat + 4 * k + 4 ≤ 2 ^ 32) :
    wordAddr b k = State.addr b + BitVec.ofNat 64 (4 * k) := addr_add (by omega)

theorem slot_in {s : State} (h : Room s) {k : Nat} (hk : k < slots) :
    (scratchR s).Contains (wordAddr (s.gpr sb) k) 4 :=
  slot_contains (s.gpr sb) hk h.fit

theorem slot_off {k : Nat} (hk : k < slots) : 4 * k < 4096 := by rw [slots_eq] at hk; omega

/-- Slot `k` of the scratch buffer. -/
abbrev slotA (s : State) (k : Nat) : Addr := wordAddr (s.gpr sb) k

/-- `s` with the memory `m`. -/
def setMem (s : State) (m : Mem) : State := { s with mem := m }

theorem mem_setMem (s : State) (m : Mem) : (setMem s m).mem = m := rfl
theorem gpr_setMem (s : State) (m : Mem) : (setMem s m).gpr = s.gpr := rfl
theorem rd_setMem (s : State) (m : Mem) : (setMem s m).rd = s.rd := rfl
theorem wr_setMem (s : State) (m : Mem) : (setMem s m).wr = s.wr := rfl
theorem sp_setMem (s : State) (m : Mem) : (setMem s m).sp = s.sp := rfl

theorem exec_ldS {s : State} (h : Room s) {k : Nat} (hk : k < slots) (d : Reg) :
    exec (ldS d k) s = some (s.setReg d (slotW s k)) :=
  exec_ldr (slot_off hk) ⟨_, List.mem_append_right _ h.mem, slot_in h hk⟩

theorem exec_stS {s : State} (h : Room s) {k : Nat} (hk : k < slots) (r : Reg) :
    exec (stS k r) s = some (setMem s (s.mem.writeW (slotA s k) (s.gpr r))) :=
  exec_str (slot_off hk) ⟨_, h.mem, slot_in h hk⟩

theorem slotW_setMem_write {s : State} (h : Room s) {k j : Nat} (hk : k < slots) (hj : j < slots)
    (v : BitVec 32) :
    slotW (setMem s (s.mem.writeW (slotA s k) v)) j = if j = k then v else slotW s j := by
  have hf := h.fit
  rw [slots_eq] at hf hk hj
  show (s.mem.writeW (slotA s k) v).readW (slotA s j) 32 = _
  split
  · rename_i e; subst e; exact Mem.readW_writeW_self32 _ _ _
  · rename_i e; exact Mem.readW_writeW_sep (slot_sep _ (by omega) (by omega) e) (by decide)

theorem slotA_setReg (s : State) {r : Reg} (hr : r ≠ sb) (v : BitVec 32) (k : Nat) :
    slotA (s.setReg r v) k = slotA s k := by
  simp only [slotA, gpr_setReg_of_ne _ _ (Ne.symm hr)]

theorem slotA_setMem (s : State) (m : Mem) (k : Nat) : slotA (setMem s m) k = slotA s k := rfl

theorem slotW_setMem (s : State) (m : Mem) (k : Nat) : slotW (setMem s m) k = m.readW (slotA s k) 32 := rfl

theorem slotW_setReg (s : State) {r : Reg} (hr : r ≠ sb) (v : BitVec 32) (j : Nat) :
    slotW (s.setReg r v) j = slotW s j := by
  simp only [slotW, gpr_setReg_of_ne _ _ (Ne.symm hr), mem_setReg]

/-! ## The arrays -/

/-- Lane `b` of the array at slot `k`. -/
def lv (s : State) (k b : Nat) : BitVec 32 := slotW s (k + b)

/-- The arrays: their first slots. -/
def arrays : List Nat := [tSlot 0, aSlot, cSlot, dSlot, arrSlot 0, arrSlot 1, arrSlot 2, arrSlot 3]

theorem arrays_bound : ∀ k ∈ arrays, 40 ≤ k ∧ k + 8 ≤ 112 := by decide

theorem arrays_apart : ∀ k ∈ arrays, ∀ k' ∈ arrays, k ≠ k' → k + 8 ≤ k' ∨ k' + 8 ≤ k := by decide

/-- The arrays' slots, 40 to 111. -/
def arraysR (s : State) : Region := ⟨State.addr (s.gpr sb) + BitVec.ofNat 64 (4 * 40), 4 * 72⟩

/-- The working area: every slot below the tail buffer. -/
def workR (s : State) : Region := ⟨State.addr (s.gpr sb), 4 * tailSlot⟩

theorem lane_slot {k b : Nat} (hk : k ∈ arrays) (hb : b < 8) : k + b < slots := by
  have := arrays_bound k hk; rw [slots_eq]; omega

theorem lane_inArrays {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 8) :
    (arraysR s).Contains (slotA s (k + b)) 4 := by
  have := arrays_bound k hk
  have hf := h.fit; rw [slots_eq] at hf
  rw [slotA, slot_addr (by omega)]
  have := toNat_addr (s.gpr sb)
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem arraysR_sub_work (s : State) : Region.Sub (arraysR s) (workR s) :=
  Offset.sub_base _ (by simp [tailSlot])

theorem workR_sub_scratch (s : State) : Region.Sub (workR s) (scratchR s) :=
  Region.sub_prefix (by simp [tailSlot, slots_eq])

/-- Two different lanes do not overlap. -/
theorem lane_sep {s : State} (h : Room s) {k b k' b' : Nat} (hk : k ∈ arrays) (hb : b < 8)
    (hk' : k' ∈ arrays) (hb' : b' < 8) (hne : k ≠ k' ∨ b ≠ b') :
    Mem.Sep (slotA s (k + b)) 4 (slotA s (k' + b')) 4 := by
  have h1 := arrays_bound k hk
  have h2 := arrays_bound k' hk'
  have hf := h.fit; rw [slots_eq] at hf
  refine slot_sep _ (by omega) (by omega) ?_
  by_cases hkk : k = k'
  · subst hkk; have : b ≠ b' := by simpa using hne
    omega
  · have := arrays_apart k hk k' hk' hkk; omega

/-! ## Steps on every lane -/

/-- A step on one lane: for each array it writes (in order), the value it
writes to the lane, from the lane's old values `x k'` of the arrays `k'`. -/
abbrev LaneSpec := List (Nat × ((Nat → BitVec 32) → BitVec 32))

/-- The memory after the writes of `sp` to lane `b`, from `s`. -/
def laneWrites (s : State) (sp : LaneSpec) (b : Nat) : Mem :=
  sp.foldl (fun m kv => m.writeW (slotA s (kv.1 + b)) (kv.2 fun k' => lv s k' b)) s.mem

/-- The new value of the array `k` at a lane whose old values are `x`. -/
def newVal (sp : LaneSpec) (k : Nat) (x : Nat → BitVec 32) : BitVec 32 :=
  sp.foldl (fun v kv => if kv.1 = k then kv.2 x else v) (x k)

/-- The values of `sp` read only the arrays. -/
def ReadsArrays (sp : LaneSpec) : Prop :=
  ∀ kv ∈ sp, ∀ x y : Nat → BitVec 32, (∀ k ∈ arrays, x k = y k) → kv.2 x = kv.2 y

theorem newVal_congr {sp : LaneSpec} (hd : ReadsArrays sp) {k : Nat} (hk : k ∈ arrays)
    {x y : Nat → BitVec 32} (h : ∀ k ∈ arrays, x k = y k) : newVal sp k x = newVal sp k y := by
  unfold newVal
  rw [h k hk]
  generalize y k = v
  induction sp generalizing v with
  | nil => rfl
  | cons kv sp ih =>
    simp only [List.foldl_cons]
    rw [hd kv List.mem_cons_self x y h]
    exact ih (fun kv h' => hd kv (List.mem_cons_of_mem _ h')) _

/-- What a step on lane `b` does: its writes, and it writes no register but
`t0` and `t1`. -/
structure LaneOk (s s' : State) (sp : LaneSpec) (b : Nat) : Prop where
  mem : s'.mem = laneWrites s sp b
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  regs : ∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r

theorem readW_foldl_writes {s : State} (h : Room s) {sp : LaneSpec} (hsp : ∀ kv ∈ sp, kv.1 ∈ arrays)
    (x : Nat → BitVec 32) (m : Mem) {k b b' : Nat} (hk : k ∈ arrays) (hb : b < 8) (hb' : b' < 8) :
    (sp.foldl (fun m kv => m.writeW (slotA s (kv.1 + b')) (kv.2 x)) m).readW (slotA s (k + b)) 32 =
      if b = b' then sp.foldl (fun v kv => if kv.1 = k then kv.2 x else v) (m.readW (slotA s (k + b)) 32)
      else m.readW (slotA s (k + b)) 32 := by
  induction sp generalizing m with
  | nil => simp
  | cons kv sp ih =>
    simp only [List.foldl_cons]
    rw [ih (fun kv h => hsp kv (List.mem_cons_of_mem _ h))]
    have hkv := hsp kv List.mem_cons_self
    by_cases hbb : b = b'
    · subst hbb
      by_cases hkk : kv.1 = k
      · rw [← hkk, Mem.readW_writeW_self32]; simp [hkk]
      · rw [Mem.readW_writeW_sep (lane_sep h hk hb hkv hb (Or.inl (Ne.symm hkk))) (by decide)]
        simp [hkk]
    · rw [Mem.readW_writeW_sep (lane_sep h hk hb hkv hb' (Or.inr hbb)) (by decide)]
      simp [hbb]

theorem lv_laneWrites {s : State} (h : Room s) {sp : LaneSpec} (hsp : ∀ kv ∈ sp, kv.1 ∈ arrays)
    {k b b' : Nat} (hk : k ∈ arrays) (hb : b < 8) (hb' : b' < 8) :
    (laneWrites s sp b').readW (slotA s (k + b)) 32 =
      if b = b' then newVal sp k (fun k' => lv s k' b) else lv s k b := by
  rw [laneWrites, readW_foldl_writes h hsp _ s.mem hk hb hb']
  by_cases hbb : b = b'
  · subst hbb; simp [newVal, lv, slotW]
  · simp [hbb, lv, slotW]

theorem foldl_writes_frame {s : State} (h : Room s) {sp : LaneSpec} (hsp : ∀ kv ∈ sp, kv.1 ∈ arrays)
    {b : Nat} (hb : b < 8) (x : Nat → BitVec 32) {m : Mem} (h0 : Frame [arraysR s] s.mem m) :
    Frame [arraysR s] s.mem (sp.foldl (fun m kv => m.writeW (slotA s (kv.1 + b)) (kv.2 x)) m) := by
  induction sp generalizing m with
  | nil => exact h0
  | cons kv sp ih =>
    simp only [List.foldl_cons]
    exact ih (fun kv h' => hsp kv (List.mem_cons_of_mem _ h'))
      (h0.writeW List.mem_cons_self (kv.2 x) (lane_inArrays h (hsp kv List.mem_cons_self) hb))

theorem laneWrites_frame {s : State} (h : Room s) {sp : LaneSpec} (hsp : ∀ kv ∈ sp, kv.1 ∈ arrays)
    {b : Nat} (hb : b < 8) : Frame [arraysR s] s.mem (laneWrites s sp b) :=
  foldl_writes_frame h hsp hb _ (Frame.refl _ _)

/-- The step `f`, on lanes `0 … n - 1`. -/
theorem lanes_ok {f : Nat → List Instr} {sp : LaneSpec} (hsp : ∀ kv ∈ sp, kv.1 ∈ arrays)
    (hd : ReadsArrays sp) {P : State → Prop} (hP : ∀ b s s', P s → LaneOk s s' sp b → P s')
    (hR : ∀ s, P s → Room s)
    (hf : ∀ b < 8, ∀ s, P s → ∃ s', runBlock isa (f b) s = some s' ∧ LaneOk s s' sp b)
    {s₀ : State} (h₀ : P s₀) :
    ∀ n ≤ 8, ∃ s', runBlock isa ((List.range n).flatMap f) s₀ = some s' ∧ P s' ∧
      (∀ k ∈ arrays, ∀ b < 8,
        lv s' k b = if b < n then newVal sp k (fun k' => lv s₀ k' b) else lv s₀ k b) ∧
      Frame [arraysR s₀] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s₀.gpr r) := by
  intro n hn
  induction n with
  | zero => exact ⟨s₀, runBlock_nil, h₀, fun k _ b _ => by simp, Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨s, hs, hPs, hv, hfr, hrd, hwr, hsp', hregs⟩ := ih (by omega)
    obtain ⟨s', hs', hok⟩ := hf n (by omega) s hPs
    have hRs := hR s hPs
    have hsb : s.gpr sb = s₀.gpr sb := hregs _ (by decide) (by decide)
    have hsb' : s'.gpr sb = s.gpr sb := hok.regs _ (by decide) (by decide)
    refine ⟨s', ?_, hP n s s' hPs hok, fun k hk b hb => ?_, ?_, hok.rd.trans hrd, hok.wr.trans hwr,
      hok.sp.trans hsp', fun r h1 h2 => (hok.regs r h1 h2).trans (hregs r h1 h2)⟩
    · rw [List.range_succ, List.flatMap_append, runBlock_append, hs, Option.bind_some,
        List.flatMap_singleton, hs']
    · have hl : lv s' k b = (laneWrites s sp n).readW (slotA s (k + b)) 32 := by
        rw [lv, slotW, hsb', ← hok.mem]
      rw [hl, lv_laneWrites hRs hsp hk hb (by omega)]
      have hx : newVal sp k (fun k' => lv s k' n) = newVal sp k (fun k' => lv s₀ k' n) :=
        newVal_congr hd hk fun k' hk' => by rw [hv k' hk' n (by omega)]; simp
      by_cases hbn : b = n
      · subst hbn; simp [hx]
      · rw [ite_eq_right hbn, hv k hk b hb]
        by_cases hbl : b < n
        · simp [hbl, show b < n + 1 by omega]
        · simp [hbl, show ¬ b < n + 1 by omega]
    · have hfr' := laneWrites_frame hRs hsp (b := n) (by omega)
      rw [← hok.mem] at hfr'
      refine hfr.trans ?_
      simpa [arraysR, hsb] using hfr'

end VG.Proof.Seed.Arm
