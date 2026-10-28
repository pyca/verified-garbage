module

public import VerifiedGarbage.Impl.Seed.RISCV64.Ecb
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The arrays of 32-bit words in the scratch buffer

As on PPC64LE (`Proof/Seed/PPC64LE/Lanes.lean`): the ECB code keeps sixteen
lanes of each of its arrays (`G`'s words, `a`, `c`, `d` and the blocks'
words) in the scratch buffer at `a5`: lane `b` of the array at slot `k` is
the 32-bit word at `a5 + 8k + 4b` (`laneA`, `lv`). This file has the 32-bit
instructions' effects on them, and `lanes_ok`, which runs a step written for
one lane (`lanes16 f`, `f b` touching only lane `b` of each array) on all
sixteen.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64
open VG.Impl.Aes.RISCV64 (sb)

/-- Lane `b` of the array at slot `k`. -/
def laneA (s : State) (k b : Nat) : Addr := s.gpr sb + BitVec.ofNat 64 (8 * k + 4 * b)

def lv (s : State) (k b : Nat) : BitVec 32 := s.mem.readW (laneA s k b) 32

/-- The scratch buffer. -/
def scratchR (s : State) : Region := ⟨s.gpr sb, 8 * scratchSlots⟩

/-- The working area: the S-box's slots and the arrays (slots 0 to 103). -/
def workR (s : State) : Region := ⟨s.gpr sb, 8 * 104⟩

/-- The arrays' slots, 40 to 103. -/
def arraysR (s : State) : Region := ⟨s.gpr sb + BitVec.ofNat 64 (8 * 40), 8 * 64⟩

/-- The arrays: their first slots. -/
def arrays : List Nat := [tSlot 0, aSlot, cSlot, dSlot, arrSlot 0, arrSlot 1, arrSlot 2, arrSlot 3]

theorem arrays_bound : ∀ k ∈ arrays, 40 ≤ k ∧ k + 8 ≤ 104 := by decide

theorem arrays_apart : ∀ k ∈ arrays, ∀ k' ∈ arrays, k ≠ k' → k + 8 ≤ k' ∨ k' + 8 ≤ k := by decide

theorem lane_in {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) (s : State) :
    (scratchR s).Contains (laneA s k b) 4 := by
  have := arrays_bound k hk
  exact Offset.contains_base _ (by unfold scratchSlots; omega) (by omega)

theorem lane_inArrays {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) (s : State) :
    (arraysR s).Contains (laneA s k b) 4 := by
  have := arrays_bound k hk
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem arraysR_sub (s : State) : Region.Sub (arraysR s) (scratchR s) :=
  Offset.sub_base _ (by unfold scratchSlots; omega)

/-- Two different lanes do not overlap. -/
theorem lane_sep {k b k' b' : Nat} (hk : k ∈ arrays) (hb : b < 16) (hk' : k' ∈ arrays)
    (hb' : b' < 16) (h : k ≠ k' ∨ b ≠ b') (s : State) :
    Mem.Sep (laneA s k b) 4 (laneA s k' b') 4 := by
  have h1 := arrays_bound k hk
  have h2 := arrays_bound k' hk'
  by_cases hkk : k = k'
  · subst hkk
    have : b ≠ b' := by simpa using h
    exact Offset.sep _ (by omega) (by omega) (by omega)
  · have := arrays_apart k hk k' hk' hkk
    exact Offset.sep _ (by omega) (by omega) (by omega)

/-! ## Steps on every lane -/

/-- A step on one lane: for each array it writes (in order), the value it
writes to the lane, from the lane's old values `x k'` of the arrays `k'`. -/
abbrev LaneSpec := List (Nat × ((Nat → BitVec 32) → BitVec 32))

/-- The memory after the writes of `sp` to lane `b`, from `s`. -/
def laneWrites (s : State) (sp : LaneSpec) (b : Nat) : Mem :=
  sp.foldl (fun m kv => m.writeW (laneA s kv.1 b) (kv.2 fun k' => lv s k' b)) s.mem

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
  regs : ∀ r, r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r

theorem readW_foldl_writes {sp : LaneSpec} (hsp : ∀ kv ∈ sp, kv.1 ∈ arrays) (s : State)
    (x : Nat → BitVec 32) (m : Mem) {k b b' : Nat} (hk : k ∈ arrays) (hb : b < 16) (hb' : b' < 16) :
    (sp.foldl (fun m kv => m.writeW (laneA s kv.1 b') (kv.2 x)) m).readW (laneA s k b) 32 =
      if b = b' then sp.foldl (fun v kv => if kv.1 = k then kv.2 x else v) (m.readW (laneA s k b) 32)
      else m.readW (laneA s k b) 32 := by
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
      · rw [Mem.readW_writeW_sep (lane_sep hk hb hkv hb (Or.inl (Ne.symm hkk)) s) (by decide)]
        simp [hkk]
    · rw [Mem.readW_writeW_sep (lane_sep hk hb hkv hb' (Or.inr hbb) s) (by decide)]
      simp [hbb]

theorem lv_laneWrites {sp : LaneSpec} (hsp : ∀ kv ∈ sp, kv.1 ∈ arrays) (s : State) {k b b' : Nat}
    (hk : k ∈ arrays) (hb : b < 16) (hb' : b' < 16) :
    (laneWrites s sp b').readW (laneA s k b) 32 =
      if b = b' then newVal sp k (fun k' => lv s k' b) else lv s k b := by
  rw [laneWrites, readW_foldl_writes hsp s _ s.mem hk hb hb']
  by_cases h : b = b'
  · subst h; simp [newVal, lv]
  · simp [h, lv]

theorem foldl_writes_frame {sp : LaneSpec} (hsp : ∀ kv ∈ sp, kv.1 ∈ arrays) (s : State) {b : Nat}
    (hb : b < 16) (x : Nat → BitVec 32) {m : Mem} (h : Frame [arraysR s] s.mem m) :
    Frame [arraysR s] s.mem (sp.foldl (fun m kv => m.writeW (laneA s kv.1 b) (kv.2 x)) m) := by
  induction sp generalizing m with
  | nil => exact h
  | cons kv sp ih =>
    simp only [List.foldl_cons]
    exact ih (fun kv h => hsp kv (List.mem_cons_of_mem _ h))
      (h.writeW List.mem_cons_self _ (lane_inArrays (hsp kv List.mem_cons_self) hb s))

theorem laneWrites_frame {sp : LaneSpec} (hsp : ∀ kv ∈ sp, kv.1 ∈ arrays) (s : State) {b : Nat}
    (hb : b < 16) : Frame [arraysR s] s.mem (laneWrites s sp b) :=
  foldl_writes_frame hsp s hb _ (Frame.refl _ _)

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

/-- The step `f`, on lanes `0 … n - 1`. -/
theorem lanes_ok {f : Nat → List Instr} {sp : LaneSpec} (hsp : ∀ kv ∈ sp, kv.1 ∈ arrays)
    (hd : ReadsArrays sp) {P : State → Prop} (hP : ∀ b s s', P s → LaneOk s s' sp b → P s')
    (hf : ∀ b < 16, ∀ s, P s → ∃ s', runBlock isa (f b) s = some s' ∧ LaneOk s s' sp b)
    {s₀ : State} (h₀ : P s₀) :
    ∀ n ≤ 16, ∃ s', runBlock isa ((List.range n).flatMap f) s₀ = some s' ∧ P s' ∧
      (∀ k ∈ arrays, ∀ b < 16,
        lv s' k b = if b < n then newVal sp k (fun k' => lv s₀ k' b) else lv s₀ k b) ∧
      Frame [arraysR s₀] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → s'.gpr r = s₀.gpr r) := by
  intro n hn
  induction n with
  | zero =>
    exact ⟨s₀, runBlock_nil, h₀, fun k _ b _ => by simp, Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨s, hs, hPs, hv, hfr, hrd, hwr, hsp', hregs⟩ := ih (by omega)
    obtain ⟨s', hs', hok⟩ := hf n (by omega) s hPs
    have hsb : s.gpr sb = s₀.gpr sb := hregs _ (by decide) (by decide)
    have hsb' : s'.gpr sb = s.gpr sb := hok.regs _ (by decide) (by decide)
    refine ⟨s', ?_, hP n s s' hPs hok, fun k hk b hb => ?_, ?_, hok.rd.trans hrd, hok.wr.trans hwr,
      hok.sp.trans hsp', fun r h1 h2 => (hok.regs r h1 h2).trans (hregs r h1 h2)⟩
    · rw [List.range_succ, List.flatMap_append, runBlock_append, hs, Option.bind_some,
        List.flatMap_singleton, hs']
    · have hl : lv s' k b = (laneWrites s sp n).readW (laneA s k b) 32 := by
        rw [lv, laneA, hsb', ← hok.mem]; rfl
      rw [hl, lv_laneWrites hsp s hk hb (by omega)]
      have hx : newVal sp k (fun k' => lv s k' n) = newVal sp k (fun k' => lv s₀ k' n) :=
        newVal_congr hd hk fun k' hk' => by rw [hv k' hk' n (by omega)]; simp
      by_cases hbn : b = n
      · subst hbn; simp [hx]
      · rw [ite_eq_right hbn, hv k hk b hb]
        by_cases hbl : b < n
        · simp [hbl, show b < n + 1 by omega]
        · simp [hbl, show ¬ b < n + 1 by omega]
    · have hfr' := laneWrites_frame hsp s (b := n) (by omega)
      rw [← hok.mem] at hfr'
      refine hfr.trans ?_
      simpa [arraysR, hsb] using hfr'

/-! ## Register updates keep the lanes -/

theorem laneA_write (s : State) {r : Reg} (v : BitVec 64) (h : ¬sb = r) (k b : Nat) :
    laneA (s.write r v) k b = laneA s k b := by
  simp only [laneA, gpr_write_of_ne _ _ h]

theorem lv_write (s : State) {r : Reg} (v : BitVec 64) (h : ¬sb = r) (k b : Nat) :
    lv (s.write r v) k b = lv s k b := by
  simp only [lv, laneA_write _ _ h, mem_write]

/-- `s` with the memory `m`. -/
def setMem (s : State) (m : Mem) : State := { s with mem := m }

theorem laneA_setMem (s : State) (m : Mem) (k b : Nat) : laneA (setMem s m) k b = laneA s k b := rfl
theorem lv_setMem (s : State) (m : Mem) (k b : Nat) :
    lv (setMem s m) k b = m.readW (laneA s k b) 32 := rfl
theorem mem_setMem (s : State) (m : Mem) : (setMem s m).mem = m := rfl
theorem gpr_setMem (s : State) (m : Mem) : (setMem s m).gpr = s.gpr := rfl
theorem rd_setMem (s : State) (m : Mem) : (setMem s m).rd = s.rd := rfl
theorem wr_setMem (s : State) (m : Mem) : (setMem s m).wr = s.wr := rfl
theorem sp_setMem (s : State) (m : Mem) : (setMem s m).sp = s.sp := rfl

/-! ## Instructions on lanes -/

/-- The scratch buffer is writable and 8-byte aligned: a writable region at
`a5` holds it (and may hold more, such as the modes' slots after it). -/
def Room (s : State) : Prop :=
  (s.gpr sb).toNat % 8 = 0 ∧ ∃ n, 8 * scratchSlots ≤ n ∧ (⟨s.gpr sb, n⟩ : Region) ∈ s.wr

/-- What the scratch buffer contains is writable. -/
theorem Room.wr {s : State} (h : Room s) {a : Addr} {m : Nat} (hc : (scratchR s).Contains a m) :
    InRegions s.wr a m := by
  obtain ⟨_, n, hn, hm⟩ := h
  exact ⟨_, hm, by simp only [Region.Contains, scratchR] at hc ⊢; omega⟩

theorem Room.rw {s : State} (h : Room s) {a : Addr} {m : Nat} (hc : (scratchR s).Contains a m) :
    InRegions (s.rd ++ s.wr) a m :=
  let ⟨r, hr, hc'⟩ := h.wr hc; ⟨r, List.mem_append_right _ hr, hc'⟩

theorem lane_wr {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) :
    InRegions s.wr (laneA s k b) 4 := h.wr (lane_in hk hb s)

theorem lane_rw {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) :
    InRegions (s.rd ++ s.wr) (laneA s k b) 4 := h.rw (lane_in hk hb s)

theorem laneOff_ok {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) :
    laneOff k b % 4 = 0 ∧ laneOff k b < 2048 := by
  have := arrays_bound k hk
  unfold laneOff; omega

/-- An offset that is a multiple of 4 from an 8-byte aligned base. -/
theorem al4 {b : Addr} (hb : b.toNat % 8 = 0) {off : Nat} (ho : off % 4 = 0) (ho' : off < 2048) :
    (b + BitVec.ofNat 64 off).toNat % 4 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega)]
  have := b.isLt
  omega

theorem lane_al {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) :
    (laneA s k b).toNat % 4 = 0 :=
  al4 h.1 (laneOff_ok hk hb).1 (laneOff_ok hk hb).2

theorem exec_ldW_lane {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) (d : Reg) :
    exec (ldW d k b) s = some (s.write d ((lv s k b).setWidth 64)) :=
  exec_load_w (laneOff_ok hk hb).2 (lane_al h hk hb) (lane_rw h hk hb)

theorem exec_stW_lane {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16)
    (r : Reg) : exec (stW k b r) s =
      some (setMem s (s.mem.writeW (laneA s k b) ((s.gpr r).setWidth 32))) :=
  exec_store_w (laneOff_ok hk hb).2 (lane_al h hk hb) (lane_wr h hk hb)

theorem exec_xorR (s : State) (d n m : Reg) :
    exec (Impl.Aes.RISCV64.xorR d n m) s = some (s.write d (s.gpr n ^^^ s.gpr m)) := rfl

theorem exec_addW (s : State) (d n m : Reg) :
    exec (addW d n m) s = some (s.write d (s.gpr n + s.gpr m)) := rfl

end VG.Proof.Seed.RISCV64
