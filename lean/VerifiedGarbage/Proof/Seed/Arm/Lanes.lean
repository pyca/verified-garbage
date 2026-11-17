module

public import VerifiedGarbage.Impl.Seed.Arm.Ecb
public import VerifiedGarbage.Impl.Seed.Arm.G8
public import VerifiedGarbage.Proof.Seed.G8
public import VerifiedGarbage.Proof.Aes.Arm.Sbox
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Seed.Arm.G8`, which only this module used -/

section

/-!
# `g8` on ARMv7

`g8_ok`: `g8` replaces each of the eight words in `tSlot 0 … tSlot 7` with
`G` of it. As on AArch64 (`Proof/Seed/AArch64/Steps.lean`): its linear
layers, which build their masks with `movw` and `movt`, are checked by
evaluation over the lane domain (`g8In_check`, `g8Out_check`: the planes of
`M`, and the words from the S-box's planes, as `Proof/Seed/G8.lean` states
them), the S-box by AES's proof (`Proof.Aes.Arm.sbox_ok`), and `g8_words`
puts them together.
-/

@[expose] public section

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Bitslice VG.Impl.Seed VG.Impl.Seed.Arm
open VG.Arm.Straight (Cfg Env check of_check run Rel Ok slotRegion wordAddr)
open VG.Impl.Aes.Arm (q t0 t1 sb sboxCode)
open VG.Impl.Seed.W32 (gConst32)
open VG.Proof.Seed (l1w l2w g8_words)

open VG.Proof.Aes.Arm (layerWrites layerKeep writes_rest)

/-- The slots `g8` reads and writes: the S-box's, the copies, the words and
the mixing's constants. -/
def gCfg : Cfg := { base := sb, slots := 53, ext := sb, exts := 0 }

/-- Slot `k` of the scratch buffer. -/
def slotW (s : State) (k : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr sb) k) 32

/-! ## The checks -/

/-- The words as atoms (word `i` in `tSlot i`). -/
def env1 : Env (Nat × Nat) :=
  { reg := fun _ => none, slot := fun k => if 40 ≤ k ∧ k < 48 then some (inWordW 32 (k - 40)) else none }

def post1 (e : Env (Nat × Nat)) : Bool :=
  (List.range 8).all fun j =>
    e.reg (q j) == some (outWordW 32 (l1w j)) && (List.range 32).all fun p => (l1w j p).all (· < 2 ^ 8)

theorem g8In_check : check (lanes 32 8) gCfg (fun _ => none) g8In env1 post1 = true := by
  decide +kernel

/-- The S-box's planes as atoms (plane `j` in `q j`). -/
def env2 : Env (Nat × Nat) :=
  { reg := fun r => ((List.range 8).find? (fun j => q j == r)).map (inWordW 32), slot := fun _ => none }

def post2 (e : Env (Nat × Nat)) : Bool :=
  (List.range 8).all fun i =>
    e.slot (tSlot i) == some (gConst32.toNat, mk 32 (l2w i) 32) &&
      (List.range 32).all fun t => (l2w i t).all (· < 2 ^ 8)

theorem g8Out_check : check (lanes 32 8) gCfg (fun _ => none) g8Out env2 post2 = true := by
  decide +kernel

/-! ## Relating the checks to the machine -/

/-- An output word with the constant bits `c`. -/
theorem outWordC_rel {k : Nat} {W : Nat → BitVec 32} {g : Nat → List Nat} {c : Nat} {x : BitVec 32}
    (hg : ∀ p < 32, ∀ a ∈ g p, a < 2 ^ k) (h : LaneRel k (assign W (2 ^ k)) (c, mk 32 g 32) x) :
    ∀ p < 32, x.getLsbD p = (c.testBit p ^^ xorBits W (g p)) := by
  intro p hp
  rw [h.2 p hp, par_mk hp (Nat.le_refl _) _ (fun q hq => hg q hq), xorA_assign W (hg p hp)]
  simp [hp]

theorem g8_keeps : layerKeep.all (fun r => g8.all fun i => !clobbers i r) = true := by
  decide +kernel

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    rw [List.cons_append, runBlock_cons, runBlock_cons]
    cases exec i s with
    | none => rfl
    | some s' => rw [runStep_some, runStep_some]; exact ih s'

theorem dst_append (a b : List Instr) (r : Reg) :
    ((a ++ b).all fun i => !clobbers i r) =
      ((a.all fun i => !clobbers i r) && (b.all fun i => !clobbers i r)) := List.all_append

/-- `g8`: `G` of every word. -/
theorem g8_ok {s : State} (hok : Ok gCfg s) :
    ∃ s', runBlock isa g8 s = some s' ∧
      (∀ w < 8, slotW s' (tSlot w) = Spec.Seed.g (slotW s (tSlot w))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion gCfg s] s.mem s'.mem := by
  let In : Nat → BitVec 32 := fun i => slotW s (tSlot i)
  -- The input layer.
  have hrel1 : Rel (LaneRel 8 (assign In (2 ^ 8))) gCfg (fun _ => none) env1 s := by
    refine ⟨fun r a h => (by cases h), fun k a hk h => ?_, fun _ _ hk => (by cases hk),
      fun _ _ h => (by cases h)⟩
    simp only [env1] at h
    split at h
    · rename_i hk'
      simp only [Option.some.injEq] at h; subst h
      have := inWordW_rel In (w := 32) (i := k - 40) (k := 8) (by omega_using [hk'])
      simpa [In, slotW, tSlot, show 40 + (k - 40) = k by omega_using [hk'], gCfg] using this
    · cases h
  obtain ⟨e1, he1, hp1⟩ := of_check _ _ _ g8In_check
  obtain ⟨s1, hs1, p1⟩ := run lanes_sound hok hrel1 he1
  simp only [post1, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hp1
  let Pl : Nat → BitVec 32 := fun j => s1.gpr (q j)
  have h1 : ∀ j < 8, ∀ p < 32, (Pl j).getLsbD p = xorBits In (l1w j p) := by
    intro j hj
    have hj' := hp1 j hj
    simp only [decide_eq_true_eq] at hj'
    exact outWordW_rel (fun p hp a ha => hj'.2 p hp a ha) (p1.rel.reg _ _ hj'.1)
  -- The S-box.
  have hokS : Ok Proof.Aes.Arm.sboxCfg s1 :=
    ⟨fun k hk => p1.ok.slotIn k (by simp [Proof.Aes.Arm.sboxCfg, gCfg] at hk ⊢; omega_using [hk]),
      fun _ hk => (by cases hk), by have := p1.ok.slots; simp [Proof.Aes.Arm.sboxCfg, gCfg] at this ⊢; omega_using [this],
      fun _ _ _ hj => (by cases hj)⟩
  obtain ⟨s2, hs2, hS, rd2, wr2, sp2, oth2, fr2⟩ := Proof.Aes.Arm.sbox_ok hokS
  let S : Nat → BitVec 32 := fun j => s2.gpr (q j)
  have hsb2 : s2.gpr sb = s1.gpr sb := oth2 _ (by decide)
  -- The output layer.
  have hok2 : Ok gCfg s2 := p1.ok.congr hsb2 hsb2 rd2 wr2
  have hrel2 : Rel (LaneRel 8 (assign S (2 ^ 8))) gCfg (fun _ => none) env2 s2 := by
    refine ⟨fun r a h => ?_, fun k a _ h => (by cases h), fun _ _ hk => (by cases hk),
      fun _ _ h => (by cases h)⟩
    simp only [env2, Option.map_eq_some_iff] at h
    obtain ⟨j, hf, rfl⟩ := h
    have hr : q j = r := by simpa using List.find?_some hf
    have hj := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    subst hr
    exact inWordW_rel S (w := 32) (k := 8) (by omega_using [hj])
  obtain ⟨e2, he2, hp2⟩ := of_check _ _ _ g8Out_check
  obtain ⟨s3, hs3, p2⟩ := run lanes_sound hok2 hrel2 he2
  simp only [post2, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hp2
  have hb1 : s1.gpr sb = s.gpr sb := p1.base
  have hb2 : s2.gpr sb = s.gpr sb := hsb2.trans hb1
  let Out : Nat → BitVec 32 := fun i => slotW s3 (tSlot i)
  have h2 : ∀ i < 8, ∀ t < 32, (Out i).getLsbD t = (gConst32.getLsbD t ^^ xorBits S (l2w i t)) := by
    intro i hi
    have hi' := hp2 i hi
    simp only [decide_eq_true_eq] at hi'
    have hl : LaneRel 8 (assign S (2 ^ 8)) (gConst32.toNat, mk 32 (l2w i) 32) (Out i) := by
      have := p2.rel.slot _ _ (by simp [tSlot, gCfg]; omega_using [hi]) hi'.1
      simpa [Out, slotW, gCfg, p2.base, hb2] using this
    intro t ht
    rw [outWordC_rel (fun p hp a ha => hi'.2 p hp a ha) hl t ht, BitVec.testBit_toNat]
  refine ⟨s3, ?_, ?_, p2.rd.trans (rd2.trans p1.rd), p2.wr.trans (wr2.trans p1.wr),
    p2.sp.trans (sp2.trans p1.sp), fun r hr => ?_, ?_⟩
  · rw [g8, runBlock_append, runBlock_append, hs1, Option.bind_some, hs2, Option.bind_some, hs3]
  · have := g8_words h1 hS h2
    intro w hw
    have e := this w hw
    simpa [Out, In, slotW, p2.base, hb2] using e
  · have hk := writes_rest g8_keeps r hr
    simp only [g8, dst_append, Bool.and_eq_true] at hk
    rw [p2.other r (by simp [hk.2]), oth2 r hr, p1.other r (by simp [hk.1.1])]
  · refine p1.frame.trans (Frame.trans (Frame.sub fr2 ?_) ?_)
    · intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨slotRegion gCfg s, List.mem_singleton_self _, ?_⟩
      show Region.Sub ⟨State.addr (s1.gpr sb), 4 * 32⟩ ⟨State.addr (s.gpr sb), 4 * 53⟩
      rw [hb1]
      exact Region.sub_prefix (by omega_using [])
    · have := p2.frame
      simp only [slotRegion] at this ⊢
      rw [show s2.gpr gCfg.base = s.gpr gCfg.base from hb2] at this
      exact this

end VG.Proof.Seed.Arm

end

end


/-!
# The arrays of 32-bit words in the scratch buffer

As on AArch64 (`Proof/Seed/AArch64/Steps.lean`): the ECB code keeps eight
lanes of each of its arrays (`G`'s words, `a`, `c`, `d` and the blocks'
words) in the scratch buffer at `r8`: lane `b` of the array at slot `k` is
slot `k + b` (`lv`). This file has the slots' loads and stores, and
`lanes_ok`, which runs a step written for one lane (`lanes8 f`, `f b`
touching only lane `b` of each array) on all eight.
-/

@[expose] public section

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
  have := b.isLt; simp [State.addr]; omega_using []

/-- Slot `k`, as a 64-bit offset from the base. -/
theorem slot_addr {b : BitVec 32} {k : Nat} (hfit : b.toNat + 4 * k + 4 ≤ 2 ^ 32) :
    wordAddr b k = State.addr b + BitVec.ofNat 64 (4 * k) := addr_add (by omega_using [hfit])

theorem slot_in {s : State} (h : Room s) {k : Nat} (hk : k < slots) :
    (scratchR s).Contains (wordAddr (s.gpr sb) k) 4 :=
  slot_contains (s.gpr sb) hk h.fit

theorem slot_off {k : Nat} (hk : k < slots) : 4 * k < 4096 := by rw [slots_eq] at hk; omega_using [hk]

/-- Slot `k` of the scratch buffer. -/
abbrev slotA (s : State) (k : Nat) : Addr := wordAddr (s.gpr sb) k

/-- `s` with the memory `m`. -/
def setMem (s : State) (m : Mem) : State := { s with mem := m }

theorem mem_setMem (s : State) (m : Mem) : (setMem s m).mem = m := rfl
theorem gpr_setMem (s : State) (m : Mem) : (setMem s m).gpr = s.gpr := rfl
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
  · rename_i e; exact Mem.readW_writeW_sep (slot_sep _ (by omega_using [hj, hf]) (by omega_using [hk, hf]) e) (by decide)

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
  have := arrays_bound k hk; rw [slots_eq]; omega_using [hb, this]

theorem lane_inArrays {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 8) :
    (arraysR s).Contains (slotA s (k + b)) 4 := by
  have := arrays_bound k hk
  have hf := h.fit; rw [slots_eq] at hf
  rw [slotA, slot_addr (by omega_using [hb, this, hf])]
  have := toNat_addr (s.gpr sb)
  exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_using [])

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
  refine slot_sep _ (by omega_using [hb, h1, hf]) (by omega_using [hb', h2, hf]) ?_
  by_cases hkk : k = k'
  · subst hkk; have : b ≠ b' := by simpa using hne
    omega_using [hne]
  · have := arrays_apart k hk k' hk' hkk; omega_using [hb, hb', this]

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
    obtain ⟨s, hs, hPs, hv, hfr, hrd, hwr, hsp', hregs⟩ := ih (by omega_using [hn])
    obtain ⟨s', hs', hok⟩ := hf n (by omega_using [hn]) s hPs
    have hRs := hR s hPs
    have hsb : s.gpr sb = s₀.gpr sb := hregs _ (by decide) (by decide)
    have hsb' : s'.gpr sb = s.gpr sb := hok.regs _ (by decide) (by decide)
    refine ⟨s', ?_, hP n s s' hPs hok, fun k hk b hb => ?_, ?_, hok.rd.trans hrd, hok.wr.trans hwr,
      hok.sp.trans hsp', fun r h1 h2 => (hok.regs r h1 h2).trans (hregs r h1 h2)⟩
    · rw [List.range_succ, List.flatMap_append, runBlock_append, hs, Option.bind_some,
        List.flatMap_singleton, hs']
    · have hl : lv s' k b = (laneWrites s sp n).readW (slotA s (k + b)) 32 := by
        rw [lv, slotW, hsb', ← hok.mem]
      rw [hl, lv_laneWrites hRs hsp hk hb (by omega_using [hn])]
      have hx : newVal sp k (fun k' => lv s k' n) = newVal sp k (fun k' => lv s₀ k' n) :=
        newVal_congr hd hk fun k' hk' => by rw [hv k' hk' n (by omega_using [hn])]; simp
      by_cases hbn : b = n
      · subst hbn; simp [hx]
      · rw [ite_eq_right hbn, hv k hk b hb]
        by_cases hbl : b < n
        · simp [hbl, show b < n + 1 by omega_using [hbl]]
        · simp [hbl, show ¬ b < n + 1 by omega_using [hbn, hbl]]
    · have hfr' := laneWrites_frame hRs hsp (b := n) (by omega_using [hn])
      rw [← hok.mem] at hfr'
      refine hfr.trans ?_
      simpa [arraysR, hsb] using hfr'

end VG.Proof.Seed.Arm
