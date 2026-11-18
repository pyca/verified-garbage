module

import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Impl.Seed.RISCV64.Ecb
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Seed.RISCV64.Lanes`, which this module and modules that import it used -/

section

/-!
# The arrays of 32-bit words in the scratch buffer

As on PPC64LE (`Proof/Seed/PPC64LE/Steps.lean`): the ECB code keeps sixteen
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
  exact Offset.contains_base _ (by unfold scratchSlots; omega_using [hb, this]) (by omega_using [hb, this])

theorem lane_inArrays {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) (s : State) :
    (arraysR s).Contains (laneA s k b) 4 := by
  have := arrays_bound k hk
  exact Offset.contains _ (by omega_using [this]) (by omega_using [hb, this]) (by omega_using [])

theorem arraysR_sub (s : State) : Region.Sub (arraysR s) (scratchR s) :=
  Offset.sub_base _ (by unfold scratchSlots; omega_using [])

/-- Two different lanes do not overlap. -/
theorem lane_sep {k b k' b' : Nat} (hk : k ∈ arrays) (hb : b < 16) (hk' : k' ∈ arrays)
    (hb' : b' < 16) (h : k ≠ k' ∨ b ≠ b') (s : State) :
    Mem.Sep (laneA s k b) 4 (laneA s k' b') 4 := by
  have h1 := arrays_bound k hk
  have h2 := arrays_bound k' hk'
  by_cases hkk : k = k'
  · subst hkk
    have : b ≠ b' := by simpa using h
    exact Offset.sep _ (by omega_using [h]) (by omega_using [hb, h1]) (by omega_using [hb', h1])
  · have := arrays_apart k hk k' hk' hkk
    exact Offset.sep _ (by omega_using [hb, hb', this]) (by omega_using [hb, h1]) (by omega_using [hb', h2])

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
    obtain ⟨s, hs, hPs, hv, hfr, hrd, hwr, hsp', hregs⟩ := ih (by omega_using [hn])
    obtain ⟨s', hs', hok⟩ := hf n (by omega_using [hn]) s hPs
    have hsb : s.gpr sb = s₀.gpr sb := hregs _ (by decide) (by decide)
    have hsb' : s'.gpr sb = s.gpr sb := hok.regs _ (by decide) (by decide)
    refine ⟨s', ?_, hP n s s' hPs hok, fun k hk b hb => ?_, ?_, hok.rd.trans hrd, hok.wr.trans hwr,
      hok.sp.trans hsp', fun r h1 h2 => (hok.regs r h1 h2).trans (hregs r h1 h2)⟩
    · rw [List.range_succ, List.flatMap_append, runBlock_append, hs, Option.bind_some,
        List.flatMap_singleton, hs']
    · have hl : lv s' k b = (laneWrites s sp n).readW (laneA s k b) 32 := by
        rw [lv, laneA, hsb', ← hok.mem]; rfl
      rw [hl, lv_laneWrites hsp s hk hb (by omega_using [hn])]
      have hx : newVal sp k (fun k' => lv s k' n) = newVal sp k (fun k' => lv s₀ k' n) :=
        newVal_congr hd hk fun k' hk' => by rw [hv k' hk' n (by omega_using [hn])]; simp
      by_cases hbn : b = n
      · subst hbn; simp [hx]
      · rw [ite_eq_right hbn, hv k hk b hb]
        by_cases hbl : b < n
        · simp [hbl, show b < n + 1 by omega_using [hbl]]
        · simp [hbl, show ¬ b < n + 1 by omega_using [hbn, hbl]]
    · have hfr' := laneWrites_frame hsp s (b := n) (by omega_using [hn])
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
/-! ## Instructions on lanes -/

/-- The scratch buffer is writable and 8-byte aligned: a writable region
holds it (and may hold more, such as the modes' frame around it). -/
def Room (s : State) : Prop :=
  (s.gpr sb).toNat % 8 = 0 ∧ InRegions s.wr (s.gpr sb) (8 * scratchSlots)

/-- What a region contains within a part of another, the other contains. -/
theorem contains_trans {r : Region} {b a : Addr} {n m : Nat} (h₁ : (⟨b, n⟩ : Region).Contains a m)
    (h₂ : r.Contains b n) : r.Contains a m := by
  simp only [Region.Contains] at h₁ h₂ ⊢
  have e : a - r.base = (a - b) + (b - r.base) := by
    rw [Offset.sub_add_sub_cancel]
  rw [e, BitVec.toNat_add]
  have := Nat.mod_le ((a - b).toNat + (b - r.base).toNat) (2 ^ 64)
  omega_using [h₁, h₂]

/-- What the scratch buffer contains is writable. -/
theorem Room.wr {s : State} (h : Room s) {a : Addr} {m : Nat} (hc : (scratchR s).Contains a m) :
    InRegions s.wr a m := by
  obtain ⟨_, r, hr, hc'⟩ := h
  exact ⟨r, hr, contains_trans hc hc'⟩

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
  unfold laneOff; omega_using [hb, this]

/-- An offset that is a multiple of 4 from an 8-byte aligned base. -/
theorem al4 {b : Addr} (hb : b.toNat % 8 = 0) {off : Nat} (ho : off % 4 = 0) (ho' : off < 2048) :
    (b + BitVec.ofNat 64 off).toNat % 4 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega_using [ho'])]
  have := b.isLt
  omega_using [hb, ho]

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

end

end

/-!
# The steps of a round, lane by lane

As on PPC64LE (`Proof/Seed/PPC64LE/Steps.lean`): each step of the round (`step1` … `step4`) on one lane meets
its `LaneSpec` (`LaneOk`); `lanes_ok` then gives it on all sixteen.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64
open VG.Impl.Aes.RISCV64 (sb)

-- The steps share one set of rewrites, not all of which each step uses.
set_option linter.unusedSimpArgs false

theorem setWidth_setWidth_32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem mem_tA : tSlot 0 ∈ arrays := by decide
theorem mem_aA : aSlot ∈ arrays := by decide
theorem mem_cA : cSlot ∈ arrays := by decide
theorem mem_dA : dSlot ∈ arrays := by decide
theorem mem_L0 : arrSlot 0 ∈ arrays := by decide
theorem mem_L1 : arrSlot 1 ∈ arrays := by decide
theorem mem_R0 : arrSlot 2 ∈ arrays := by decide
theorem mem_R1 : arrSlot 3 ∈ arrays := by decide

theorem room_congr {s s' : State} (h : Room s) (hr : s'.gpr sb = s.gpr sb) (hw : s'.wr = s.wr) :
    Room s' := by
  unfold Room at *; rw [hr, hw]; exact h

/-- Reading a lane after a write to another. -/
theorem readW_writeW_lane {m : Mem} {s : State} {k b k' b' : Nat} (hk : k ∈ arrays) (hb : b < 16)
    (hk' : k' ∈ arrays) (hb' : b' < 16) (h : k ≠ k' ∨ b ≠ b') (v : BitVec 32) :
    (m.writeW (laneA s k' b') v).readW (laneA s k b) 32 = m.readW (laneA s k b) 32 :=
  Mem.readW_writeW_sep (lane_sep hk hb hk' hb' h s) (by decide)

theorem lv_eq (s : State) (k b : Nat) : s.mem.readW (laneA s k b) 32 = lv s k b := rfl

def sp1 (k0 k1 : BitVec 32) : LaneSpec :=
  [(aSlot, fun x => x (arrSlot 2) ^^^ k0),
   (tSlot 0, fun x => x (arrSlot 2) ^^^ k0 ^^^ x (arrSlot 3) ^^^ k1)]

def sp2 : LaneSpec := [(cSlot, fun x => x (tSlot 0)), (tSlot 0, fun x => x (tSlot 0) + x aSlot)]

def sp3 : LaneSpec := [(dSlot, fun x => x (tSlot 0)), (tSlot 0, fun x => x (tSlot 0) + x cSlot)]

def sp4 : LaneSpec :=
  [(arrSlot 1, fun x => x (arrSlot 1) ^^^ x (tSlot 0)),
   (arrSlot 0, fun x => (x (tSlot 0) + x dSlot) ^^^ x (arrSlot 0))]

/-- The round key's halves are in `t5` and `t6`. -/
def KeysIn (k0 k1 : BitVec 32) (s : State) : Prop :=
  Room s ∧ (s.gpr .t5).setWidth 32 = k0 ∧ (s.gpr .t6).setWidth 32 = k1

theorem step1_ok (k0 k1 : BitVec 32) {b : Nat} (hb : b < 16) (s : State) (h : KeysIn k0 k1 s) :
    ∃ s', runBlock isa (step1 b) s = some s' ∧ LaneOk s s' (sp1 k0 k1) b := by
  obtain ⟨h, hk0, hk1⟩ := h
  rw [step1, runBlock_cons, exec_ldW_lane h mem_R0 hb, runStep_some, runBlock_cons,
    exec_xorR, runStep_some, runBlock_cons, exec_stW_lane ?h1 mem_aA hb, runStep_some,
    runBlock_cons, exec_ldW_lane ?h2 mem_R1 hb, runStep_some, runBlock_cons, exec_xorR, runStep_some,
    runBlock_cons, exec_xorR, runStep_some, runBlock_cons, exec_stW_lane ?h3 mem_tA hb, runStep_some,
    runBlock_nil]
  case h1 | h2 | h3 => exact room_congr h rfl rfl
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp only [Impl.Aes.RISCV64.t0, Impl.Aes.RISCV64.t1, k0R, k1R, laneWrites, sp1, List.foldl_cons, List.foldl_nil, gpr_write,
      reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, BitVec.setWidth_xor, lo32_add, gpr_setMem, mem_write, mem_setMem, lv_setMem,
      laneA_setMem, hk0, hk1,
      laneA_write _ _ (show ¬ sb = .t0 by decide), lv_write _ _ (show ¬ sb = .t0 by decide),
      laneA_write _ _ (show ¬ sb = .t1 by decide), lv_write _ _ (show ¬ sb = .t1 by decide),
      lv_eq]
    rw [readW_writeW_lane mem_R1 hb mem_aA hb (Or.inl (by decide)), lv_eq]
  · simp only [Impl.Aes.RISCV64.t0, Impl.Aes.RISCV64.t1, gpr_write, gpr_setMem, h1, h2, ↓reduceIte]

theorem step2_ok {b : Nat} (hb : b < 16) (s : State) (h : Room s) :
    ∃ s', runBlock isa (step2 b) s = some s' ∧ LaneOk s s' sp2 b := by
  rw [step2, runBlock_cons, exec_ldW_lane h mem_tA hb, runStep_some, runBlock_cons,
    exec_stW_lane ?h1 mem_cA hb, runStep_some, runBlock_cons, exec_ldW_lane ?h2 mem_aA hb,
    runStep_some, runBlock_cons, exec_addW, runStep_some, runBlock_cons, exec_stW_lane ?h3 mem_tA hb,
    runStep_some, runBlock_nil]
  case h1 | h2 | h3 => exact room_congr h rfl rfl
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp only [Impl.Aes.RISCV64.t0, Impl.Aes.RISCV64.t1, k0R, k1R, laneWrites, sp2, List.foldl_cons, List.foldl_nil, gpr_write,
      reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, BitVec.setWidth_xor, lo32_add, gpr_setMem, mem_write, mem_setMem, lv_setMem,
      laneA_setMem,
      laneA_write _ _ (show ¬ sb = .t0 by decide), lv_write _ _ (show ¬ sb = .t0 by decide),
      laneA_write _ _ (show ¬ sb = .t1 by decide), lv_write _ _ (show ¬ sb = .t1 by decide),
      lv_eq]
    rw [readW_writeW_lane mem_aA hb mem_cA hb (Or.inl (by decide)), lv_eq]
  · simp only [Impl.Aes.RISCV64.t0, Impl.Aes.RISCV64.t1, gpr_write, gpr_setMem, h1, h2, ↓reduceIte]

theorem step3_ok {b : Nat} (hb : b < 16) (s : State) (h : Room s) :
    ∃ s', runBlock isa (step3 b) s = some s' ∧ LaneOk s s' sp3 b := by
  rw [step3, runBlock_cons, exec_ldW_lane h mem_tA hb, runStep_some, runBlock_cons,
    exec_stW_lane ?h1 mem_dA hb, runStep_some, runBlock_cons, exec_ldW_lane ?h2 mem_cA hb,
    runStep_some, runBlock_cons, exec_addW, runStep_some, runBlock_cons, exec_stW_lane ?h3 mem_tA hb,
    runStep_some, runBlock_nil]
  case h1 | h2 | h3 => exact room_congr h rfl rfl
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp only [Impl.Aes.RISCV64.t0, Impl.Aes.RISCV64.t1, k0R, k1R, laneWrites, sp3, List.foldl_cons, List.foldl_nil, gpr_write,
      reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, BitVec.setWidth_xor, lo32_add, gpr_setMem, mem_write, mem_setMem, lv_setMem,
      laneA_setMem,
      laneA_write _ _ (show ¬ sb = .t0 by decide), lv_write _ _ (show ¬ sb = .t0 by decide),
      laneA_write _ _ (show ¬ sb = .t1 by decide), lv_write _ _ (show ¬ sb = .t1 by decide),
      lv_eq]
    rw [readW_writeW_lane mem_cA hb mem_dA hb (Or.inl (by decide)), lv_eq]
  · simp only [Impl.Aes.RISCV64.t0, Impl.Aes.RISCV64.t1, gpr_write, gpr_setMem, h1, h2, ↓reduceIte]

theorem step4_ok {b : Nat} (hb : b < 16) (s : State) (h : Room s) :
    ∃ s', runBlock isa (step4 b) s = some s' ∧ LaneOk s s' sp4 b := by
  rw [step4, runBlock_cons, exec_ldW_lane h mem_tA hb, runStep_some, runBlock_cons,
    exec_ldW_lane ?h1 mem_L1 hb, runStep_some, runBlock_cons, exec_xorR, runStep_some,
    runBlock_cons, exec_stW_lane ?h2 mem_L1 hb, runStep_some, runBlock_cons,
    exec_ldW_lane ?h3 mem_dA hb, runStep_some, runBlock_cons, exec_addW, runStep_some,
    runBlock_cons, exec_ldW_lane ?h4 mem_L0 hb, runStep_some, runBlock_cons, exec_xorR, runStep_some,
    runBlock_cons, exec_stW_lane ?h5 mem_L0 hb, runStep_some, runBlock_nil]
  case h1 | h2 | h3 | h4 | h5 => exact room_congr h rfl rfl
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp only [Impl.Aes.RISCV64.t0, Impl.Aes.RISCV64.t1, k0R, k1R, laneWrites, sp4, List.foldl_cons, List.foldl_nil, gpr_write,
      reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, BitVec.setWidth_xor, lo32_add, gpr_setMem, mem_write, mem_setMem, lv_setMem,
      laneA_setMem,
      laneA_write _ _ (show ¬ sb = .t0 by decide), lv_write _ _ (show ¬ sb = .t0 by decide),
      laneA_write _ _ (show ¬ sb = .t1 by decide), lv_write _ _ (show ¬ sb = .t1 by decide),
      lv_eq]
    rw [readW_writeW_lane mem_dA hb mem_L1 hb (Or.inl (by decide)),
      readW_writeW_lane mem_L0 hb mem_L1 hb (Or.inl (by decide)), lv_eq, lv_eq]
  · simp only [Impl.Aes.RISCV64.t0, Impl.Aes.RISCV64.t1, gpr_write, gpr_setMem, h1, h2, ↓reduceIte]

end VG.Proof.Seed.RISCV64
