module

import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Seed.SboxLit
public import VerifiedGarbage.Impl.Seed.X86_64.Ecb
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Seed.X86_64.G16
public import VerifiedGarbage.Proof.Seed.G16
public import VerifiedGarbage.Proof.Seed.G16Lanes
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Aes.X86_64.Encrypt

/-! ### `Seed.X86_64.Lanes`, which this module and modules that import it used -/

section

/-! ### `Seed.X86_64.G16`, which this module and modules that import it used -/

section

/-!
# `g16` on x86-64

`g16_ok`: `g16` replaces each of the sixteen words in `tSlot 0 … tSlot 7`
with `G` of it, when the masks are in their slots (`MasksIn`), and keeps
them there. Its linear layers are checked by evaluation over the lane
domain (`g16In_check`, `g16Out_check`: the planes of `M`, and the words from
the S-box's planes, as `Proof/Seed/G16.lean` states them), the S-box by
AES's proof (`Proof.Aes.X86_64.sbox_ok`), and `g16_words` puts them together.
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Seed VG.Impl.Seed.X86_64
open VG.Impl.Aes.X86_64 (q t0 t1 sb sboxCode)
open VG.Proof.Seed (l1 l2 wordQ g16_words l2Lane l2_lt)

/-- The slots `g16` reads and writes: the S-box's, the masks and the words. -/
def gCfg : Cfg := { base := sb, slots := 69, ext := sb, exts := 0 }

/-- Slot `k` of the scratch buffer. -/
def slotW (s : State) (k : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr sb) k) 64

/-- The masks are in their slots. -/
def MasksIn (s : State) : Prop := ∀ kv ∈ maskSlots, slotW s kv.1 = kv.2

/-- The masks, as constants of the lane domain. -/
def maskEnv (k : Nat) : Option (Nat × Nat) := (maskSlots.find? (·.1 == k)).map fun kv => (kv.2.toNat, 0)

def masksKept (e : Env (Nat × Nat)) : Bool := maskSlots.all fun kv => e.slot kv.1 == some (kv.2.toNat, 0)

/-! ## The checks -/

/-- The words as atoms (word `i` in `tSlot i`), and the masks. -/
def env1 : Env (Nat × Nat) :=
  { reg := fun _ => none, slot := fun k => if 61 ≤ k ∧ k < 69 then some (inWord (k - 61)) else maskEnv k }

def post1 (e : Env (Nat × Nat)) : Bool :=
  masksKept e && (List.range 8).all fun j =>
    e.reg (q j) == some (outWord (l1 j)) && (List.range 64).all fun p => (l1 j p).all (· < 2 ^ 9)

theorem g16In_check : check (lanes 64 9) gCfg (fun _ => none) g16In env1 post1 = true := by
  decide +kernel

/-- The S-box's planes as atoms (plane `j` in `q j`), and the masks. -/
def env2 : Env (Nat × Nat) :=
  { reg := fun r => ((List.range 8).find? (fun j => q j == r)).map inWord, slot := maskEnv }

def post2 (e : Env (Nat × Nat)) : Bool :=
  masksKept e && (List.range 8).all fun i =>
    e.slot (tSlot i) == some (gConst.toNat, mk 64 (l2 i) 64) &&
      (List.range 64).all fun t => (l2 i t).all (· < 2 ^ 9)

/-- `post2`, against the table of the output layer's lanes (`Proof/Seed/G16Lanes.lean`): what the
kernel evaluates. -/
def post2K (e : Env (Nat × Nat)) : Bool :=
  masksKept e && (List.range 8).all fun i => e.slot (tSlot i) == some (gConst.toNat, l2Lane i)

theorem post2_of_K {e : Env (Nat × Nat)} (h : post2K e = true) : post2 e = true := by
  simp only [post2K, post2, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h ⊢
  exact ⟨h.1, fun i hi => ⟨h.2 i hi, fun t ht a ha => l2_lt hi ht a ha⟩⟩

theorem g16Out_check : check (lanes 64 9) gCfg (fun _ => none) g16Out env2 post2 = true := by
  obtain ⟨e, he, hp⟩ := of_check _ _ _ (show check (lanes 64 9) gCfg (fun _ => none) g16Out env2 post2K = true by lit_decide)
  unfold check
  rw [he]
  exact post2_of_K hp

/-! ## Relating the checks to the machine -/

theorem laneRel_const {k A : Nat} (v : BitVec 64) : LaneRel k A (v.toNat, 0) v :=
  ⟨v.isLt, fun q _ => by simp [par_zero, BitVec.testBit_toNat]⟩

/-- An output word with the constant bits `c`. -/
theorem outWordC_rel {k : Nat} {W : Nat → BitVec 64} {g : Nat → List Nat} {c : Nat} {x : BitVec 64}
    (hg : ∀ p < 64, ∀ a ∈ g p, a < 2 ^ k) (h : LaneRel k (assign W (2 ^ k)) (c, mk 64 g 64) x) :
    ∀ p < 64, x.getLsbD p = (c.testBit p ^^ xorBits W (g p)) := by
  intro p hp
  rw [h.2 p hp, par_mk hp (Nat.le_refl _) _ (fun q hq => hg q hq), xorA_assign W (hg p hp)]
  simp [hp]

theorem maskEnv_some {k : Nat} {a : Nat × Nat} (h : maskEnv k = some a) :
    ∃ v, (k, v) ∈ maskSlots ∧ a = (v.toNat, 0) := by
  simp only [maskEnv, Option.map_eq_some_iff] at h
  obtain ⟨kv, hv, rfl⟩ := h
  have hk : kv.1 = k := by simpa using List.find?_some hv
  exact ⟨kv.2, hk ▸ List.mem_of_find?_eq_some hv, rfl⟩

theorem masks_rel {k : Nat} {s : State} (hm : MasksIn s) {A : Nat} {a : Nat × Nat}
    (h : maskEnv k = some a) : LaneRel 9 A a (slotW s k) := by
  obtain ⟨v, hv, rfl⟩ := maskEnv_some h
  rw [hm _ hv]; exact laneRel_const v

theorem masksKept_in {e : Env (Nat × Nat)} (hk : masksKept e = true) {c : Cfg} {A : Nat}
    {s : State} (hb : c.base = sb) (hr : Rel (LaneRel 9 A) c (fun _ => none) e s)
    (hs : ∀ kv ∈ maskSlots, kv.1 < c.slots) : MasksIn s := by
  intro kv hkv
  have he : e.slot kv.1 = some (kv.2.toNat, 0) := by
    have := List.all_eq_true.mp hk kv hkv
    simpa using this
  have hl := hr.slot _ _ (hs kv hkv) he
  simp only [slotW, ← hb]
  apply BitVec.eq_of_getLsbD_eq
  intro q hq
  rw [hl.2 q hq]; simp [par_zero, BitVec.testBit_toNat]

theorem maskSlots_lt : ∀ kv ∈ maskSlots, kv.1 < 61 ∧ 48 ≤ kv.1 := by decide

/-- The registers `g16` writes: the S-box's. -/
def g16Writes : List Reg := [q 0, q 1, q 2, q 3, q 4, q 5, q 6, q 7, t0, t1]

theorem g16_writes_rest :
    [Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all
      (fun r => g16In.all (fun i => i.dst != some r) && g16Out.all (fun i => i.dst != some r)) =
      true := by
  decide +kernel

theorem not_g16Writes (r : Reg) (hr : r ∉ g16Writes) : r ∈ [Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9] := by
  revert hr; cases r <;> decide

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

/-- `g16`: `G` of every word, the masks kept. -/
theorem g16_ok {s : State} (hok : Ok gCfg s) (hm : MasksIn s) :
    ∃ s', runBlock isa g16 s = some s' ∧
      (∀ w < 16, wordQ (fun i => slotW s' (tSlot i)) w =
        Spec.Seed.g (wordQ (fun i => slotW s (tSlot i)) w)) ∧
      MasksIn s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ g16Writes → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion gCfg s] s.mem s'.mem := by
  let In : Nat → BitVec 64 := fun i => slotW s (tSlot i)
  -- The input layer.
  have hrel1 : Rel (LaneRel 9 (assign In (2 ^ 9))) gCfg (fun _ => none) env1 s := by
    refine ⟨fun r a h => (by cases h), fun k a hk h => ?_, fun _ _ hk => (by cases hk)⟩
    simp only [env1] at h
    split at h
    · rename_i hk'
      simp only [Option.some.injEq] at h; subst h
      have := inWord_rel In (i := k - 61) (k := 9) (by omega_using [hk'])
      simpa [In, slotW, tSlot, show 61 + (k - 61) = k by omega_using [hk'], gCfg] using this
    · exact masks_rel hm h
  obtain ⟨e1, he1, hp1⟩ := of_check _ _ _ g16In_check
  obtain ⟨s1, hs1, p1⟩ := run lanes_sound hok hrel1 he1
  simp only [post1, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hp1
  have hm1 : MasksIn s1 := masksKept_in (by simpa [masksKept] using hp1.1) rfl p1.rel
    fun kv h => Nat.lt_of_lt_of_le (maskSlots_lt kv h).1 (by decide)
  let Pl : Nat → BitVec 64 := fun j => s1.gpr (q j)
  have h1 : ∀ j < 8, ∀ p < 64, (Pl j).getLsbD p = xorBits In (l1 j p) := by
    intro j hj
    have hj' := hp1.2 j hj
    simp only [decide_eq_true_eq] at hj'
    exact outWord_rel (fun p hp a ha => hj'.2 p hp a ha) (p1.rel.reg _ _ hj'.1)
  -- The S-box.
  have hokS : Ok Proof.Aes.X86_64.sboxCfg s1 :=
    ⟨fun k hk => p1.ok.slotIn k (by simp [Proof.Aes.X86_64.sboxCfg, gCfg] at hk ⊢; omega_using [hk]),
      fun _ hk => (by cases hk), by decide, fun _ _ _ hj => (by cases hj)⟩
  obtain ⟨s2, hs2, hS, rd2, wr2, oth2, fr2⟩ := Proof.Aes.X86_64.sbox_ok hokS
  let S : Nat → BitVec 64 := fun j => s2.gpr (q j)
  have hsb2 : s2.gpr sb = s1.gpr sb := oth2 _ (by decide)
  have hm2 : MasksIn s2 := by
    intro kv hkv
    have hlt := maskSlots_lt kv hkv
    rw [← hm1 kv hkv]
    simp only [slotW, hsb2]
    refine fr2.readW (r := ⟨wordAddr (s1.gpr sb) kv.1, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base (s1.gpr sb) (d := 8 * kv.1) (n := 8) (k := 8 * 48)
      (by omega_using [hlt]) (by omega_using [hlt])
  -- The output layer.
  have hok2 : Ok gCfg s2 := p1.ok.congr hsb2 hsb2 rd2 wr2
  have hrel2 : Rel (LaneRel 9 (assign S (2 ^ 9))) gCfg (fun _ => none) env2 s2 := by
    refine ⟨fun r a h => ?_, fun k a _ h => masks_rel hm2 h, fun _ _ hk => (by cases hk)⟩
    simp only [env2, Option.map_eq_some_iff] at h
    obtain ⟨j, hf, rfl⟩ := h
    have hr : q j = r := by simpa using List.find?_some hf
    have hj := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    subst hr
    exact inWord_rel S (k := 9) (by omega_using [hj])
  obtain ⟨e2, he2, hp2⟩ := of_check _ _ _ g16Out_check
  obtain ⟨s3, hs3, p2⟩ := run lanes_sound hok2 hrel2 he2
  simp only [post2, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hp2
  have hm3 : MasksIn s3 := masksKept_in (by simpa [masksKept] using hp2.1) rfl p2.rel
    fun kv h => Nat.lt_of_lt_of_le (maskSlots_lt kv h).1 (by decide)
  have hb1 : s1.gpr sb = s.gpr sb := p1.base
  have hb2 : s2.gpr sb = s.gpr sb := hsb2.trans hb1
  let Out : Nat → BitVec 64 := fun i => slotW s3 (tSlot i)
  have h2 : ∀ i < 8, ∀ t < 64, (Out i).getLsbD t = (gConst.getLsbD t ^^ xorBits S (l2 i t)) := by
    intro i hi
    have hi' := hp2.2 i hi
    simp only [decide_eq_true_eq] at hi'
    have hl : LaneRel 9 (assign S (2 ^ 9)) _ (Out i) :=
      p2.rel.slot _ _ (by simp [tSlot, gCfg]; omega_using [hi]) hi'.1
    intro t ht
    rw [outWordC_rel (fun p hp a ha => hi'.2 p hp a ha) hl t ht, BitVec.testBit_toNat]
  refine ⟨s3, ?_, g16_words h1 hS h2, hm3, p2.rd.trans (rd2.trans p1.rd),
    p2.wr.trans (wr2.trans p1.wr), fun r hr => ?_, ?_⟩
  · rw [g16, runBlock_append, runBlock_append, hs1, Option.bind_some, hs2, Option.bind_some, hs3]
  · have hrest := List.all_eq_true.mp g16_writes_rest r (not_g16Writes r hr)
    simp only [Bool.and_eq_true] at hrest
    rw [p2.other r (by simp [hrest.2]), oth2 r (by simpa [Proof.Aes.X86_64.sboxWrites, g16Writes] using hr),
      p1.other r (by simp [hrest.1])]
  · refine p1.frame.trans (Frame.trans (Frame.sub fr2 ?_) ?_)
    · intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨slotRegion gCfg s, List.mem_singleton_self _, ?_⟩
      show Region.Sub ⟨s1.gpr sb, 8 * 48⟩ ⟨s.gpr sb, 8 * 69⟩
      rw [hb1]
      exact Region.sub_prefix (by omega_using [])
    · have := p2.frame
      simp only [slotRegion] at this ⊢
      rw [show s2.gpr gCfg.base = s.gpr gCfg.base from hb2] at this
      exact this

end VG.Proof.Seed.X86_64

end

end

/-!
# The arrays of 32-bit words in the scratch buffer

The ECB code keeps sixteen lanes of each of its arrays (`G`'s words, `a`, `c`,
`d` and the blocks' words) in the scratch buffer at `r9`: lane `b` of the
array at slot `k` is the 32-bit word at `r9 + 8k + 4b` (`laneA`, `lv`).
This file has the 32-bit instructions' effects on them, and `lanes16_ok`,
which runs a step written for one lane (`lanes16 f`, `f b` touching only
lane `b` of each array) on all sixteen.
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64

/-- Lane `b` of the array at slot `k`. -/
def laneA (s : State) (k b : Nat) : Addr := s.gpr .r9 + BitVec.ofNat 64 (8 * k + 4 * b)

def lv (s : State) (k b : Nat) : BitVec 32 := s.mem.readW (laneA s k b) 32

/-- The scratch buffer. -/
def scratchR (s : State) : Region := ⟨s.gpr .r9, 8 * scratchSlots⟩

/-- The working area: every slot but the saved registers' (slots 0 to 124). -/
def workR (s : State) : Region := ⟨s.gpr .r9, 8 * 125⟩

/-- The arrays' slots, 61 to 124. -/
def arraysR (s : State) : Region := ⟨s.gpr .r9 + BitVec.ofNat 64 (8 * 61), 8 * 64⟩

/-- The arrays: their first slots. -/
def arrays : List Nat := [tSlot 0, aSlot, cSlot, dSlot, arrSlot 0, arrSlot 1, arrSlot 2, arrSlot 3]

theorem arrays_bound : ∀ k ∈ arrays, 61 ≤ k ∧ k + 8 ≤ 125 := by decide

theorem arrays_apart : ∀ k ∈ arrays, ∀ k' ∈ arrays, k ≠ k' → k + 8 ≤ k' ∨ k' + 8 ≤ k := by decide

theorem lane_in {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) (s : State) :
    (scratchR s).Contains (laneA s k b) 4 := by
  have := arrays_bound k hk
  exact Offset.contains_base _ (by unfold scratchSlots; omega_using [hb, this]) (by omega_using [hb, this])

theorem lane_inArrays {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) (s : State) :
    (arraysR s).Contains (laneA s k b) 4 := by
  have := arrays_bound k hk
  exact Offset.contains _ (by omega_using [this]) (by omega_using [hb, this]) (by omega_using [])

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

theorem ea_lane (s : State) (base : Reg) (k b : Nat) :
    s.ea (lane base k b) = s.gpr base + BitVec.ofNat 64 (8 * k + 4 * b) := by
  show s.gpr base + BitVec.ofInt 64 ((8 * k + 4 * b : Nat) : Int) = _
  rw [BitVec.ofInt_natCast]

/-! ## 32-bit instructions -/

theorem exec_mov32_mem {s : State} {d : Reg} {m : MemOp} (h : InRegions (s.rd ++ s.wr) (s.ea m) 4) :
    exec (.mov32 d (.mem m)) s = some (s.setReg32 d (s.mem.readW (s.ea m) 32)) := by
  simp [exec, readSrc32, State.load32, h]

theorem exec_store32 {s : State} {r : Reg} {m : MemOp} (h : InRegions s.wr (s.ea m) 4) :
    exec (.store32 m r) s = some { s with mem := s.mem.writeW (s.ea m) ((s.gpr r).setWidth 32) } := by
  simp [exec, State.store32, h]

theorem exec_xor32_reg (s : State) (d r : Reg) :
    exec (.alu32 .xor d (.reg r)) s =
      some ((arithFlags s ((s.gpr d).setWidth 32 ^^^ (s.gpr r).setWidth 32) false false).setReg32 d
        ((s.gpr d).setWidth 32 ^^^ (s.gpr r).setWidth 32)) := rfl

theorem exec_xor32_mem {s : State} {d : Reg} {m : MemOp} (h : InRegions (s.rd ++ s.wr) (s.ea m) 4) :
    exec (.alu32 .xor d (.mem m)) s =
      some ((arithFlags s ((s.gpr d).setWidth 32 ^^^ s.mem.readW (s.ea m) 32) false false).setReg32 d
        ((s.gpr d).setWidth 32 ^^^ s.mem.readW (s.ea m) 32)) := by
  simp [exec, execAlu32, readSrc32, State.load32, h]

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
`rax` and `rcx` (and the flags). -/
structure LaneOk (s s' : State) (sp : LaneSpec) (b : Nat) : Prop where
  mem : s'.mem = laneWrites s sp b
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  regs : ∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r

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

/-- The step `f`, on lanes `0 … n - 1`. -/
theorem lanes_ok {f : Nat → List Instr} {sp : LaneSpec} (hsp : ∀ kv ∈ sp, kv.1 ∈ arrays)
    (hd : ReadsArrays sp) {P : State → Prop} (hP : ∀ b s s', P s → LaneOk s s' sp b → P s')
    (hf : ∀ b < 16, ∀ s, P s → ∃ s', runBlock isa (f b) s = some s' ∧ LaneOk s s' sp b)
    {s₀ : State} (h₀ : P s₀) :
    ∀ n ≤ 16, ∃ s', runBlock isa ((List.range n).flatMap f) s₀ = some s' ∧ P s' ∧
      (∀ k ∈ arrays, ∀ b < 16,
        lv s' k b = if b < n then newVal sp k (fun k' => lv s₀ k' b) else lv s₀ k b) ∧
      Frame [arraysR s₀] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s₀.gpr r) := by
  intro n hn
  induction n with
  | zero => exact ⟨s₀, runBlock_nil, h₀, fun k _ b _ => by simp, Frame.refl _ _, rfl, rfl, fun _ _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨s, hs, hPs, hv, hfr, hrd, hwr, hregs⟩ := ih (by omega_using [hn])
    obtain ⟨s', hs', hok⟩ := hf n (by omega_using [hn]) s hPs
    have hr9 : s.gpr .r9 = s₀.gpr .r9 := hregs _ (by decide) (by decide)
    have hr9' : s'.gpr .r9 = s.gpr .r9 := hok.regs _ (by decide) (by decide)
    refine ⟨s', ?_, hP n s s' hPs hok, fun k hk b hb => ?_, ?_, hok.rd.trans hrd, hok.wr.trans hwr,
      fun r h1 h2 => (hok.regs r h1 h2).trans (hregs r h1 h2)⟩
    · rw [List.range_succ, List.flatMap_append, runBlock_append, hs, Option.bind_some,
        List.flatMap_singleton, hs']
    · have hl : lv s' k b = (laneWrites s sp n).readW (laneA s k b) 32 := by
        rw [lv, laneA, hr9', ← hok.mem]; rfl
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
      simpa [arraysR, hr9] using hfr'

/-! ## Register updates keep the lanes -/

theorem laneA_setReg (s : State) {r : Reg} (v : BitVec 64) (h : ¬Reg.r9 = r) (k b : Nat) :
    laneA (s.setReg r v) k b = laneA s k b := by
  simp only [laneA, RegUpd.gpr_setReg_of_ne _ _ h]

theorem lv_setReg (s : State) {r : Reg} (v : BitVec 64) (h : ¬Reg.r9 = r) (k b : Nat) :
    lv (s.setReg r v) k b = lv s k b := by
  simp only [lv, laneA_setReg _ _ h, RegUpd.mem_setReg]

theorem laneA_arithFlags (s : State) {w : Nat} (x : BitVec w) (c o : Bool) (k b : Nat) :
    laneA (arithFlags s x c o) k b = laneA s k b := rfl

theorem lv_arithFlags (s : State) {w : Nat} (x : BitVec w) (c o : Bool) (k b : Nat) :
    lv (arithFlags s x c o) k b = lv s k b := rfl

/-- `s` with the memory `m`. -/
def setMem (s : State) (m : Mem) : State := { s with mem := m }

theorem laneA_setMem (s : State) (m : Mem) (k b : Nat) : laneA (setMem s m) k b = laneA s k b := rfl
theorem lv_setMem (s : State) (m : Mem) (k b : Nat) :
    lv (setMem s m) k b = m.readW (laneA s k b) 32 := rfl
theorem mem_setMem (s : State) (m : Mem) : (setMem s m).mem = m := rfl
theorem gpr_setMem (s : State) (m : Mem) : (setMem s m).gpr = s.gpr := rfl
/-! ## Instructions on lanes -/

/-- The scratch buffer is writable: it begins a writable region (which a
caller's larger working space may extend). -/
def Room (s : State) : Prop := ∃ n, 8 * scratchSlots ≤ n ∧ (⟨s.gpr .r9, n⟩ : Region) ∈ s.wr

/-- An access within the scratch buffer is writable. -/
theorem Room.wr {s : State} (h : Room s) {a : Addr} {k : Nat} (hc : (scratchR s).Contains a k) :
    InRegions s.wr a k := by
  obtain ⟨n, hn, hm⟩ := h
  refine ⟨_, hm, ?_⟩
  unfold scratchR Region.Contains at hc
  unfold Region.Contains
  simp only at hc ⊢
  omega_using [hc, hn]

/-- An access within the scratch buffer is readable. -/
theorem Room.rw {s : State} (h : Room s) {a : Addr} {k : Nat} (hc : (scratchR s).Contains a k) :
    InRegions (s.rd ++ s.wr) a k := by
  obtain ⟨r, hr, hc'⟩ := h.wr hc
  exact ⟨r, List.mem_append_right _ hr, hc'⟩

theorem lane_wr {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) :
    InRegions s.wr (laneA s k b) 4 := h.wr (lane_in hk hb s)

theorem lane_rw {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) :
    InRegions (s.rd ++ s.wr) (laneA s k b) 4 := h.rw (lane_in hk hb s)

theorem exec_mov32_lane {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) (d : Reg) :
    exec (.mov32 d (.mem (lane .r9 k b))) s = some (s.setReg32 d (lv s k b)) := by
  rw [exec_mov32_mem (by rw [ea_lane]; exact lane_rw h hk hb), ea_lane]; rfl

theorem exec_store32_lane {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16)
    (r : Reg) : exec (.store32 (lane .r9 k b) r) s =
      some (setMem s (s.mem.writeW (laneA s k b) ((s.gpr r).setWidth 32))) := by
  rw [exec_store32 (by rw [ea_lane]; exact lane_wr h hk hb), ea_lane]; rfl

theorem exec_xor32_lane {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16)
    (d : Reg) : exec (.alu32 .xor d (.mem (lane .r9 k b))) s =
      some ((arithFlags s ((s.gpr d).setWidth 32 ^^^ lv s k b) false false).setReg32 d
        ((s.gpr d).setWidth 32 ^^^ lv s k b)) := by
  rw [exec_xor32_mem (by rw [ea_lane]; exact lane_rw h hk hb), ea_lane]; rfl

theorem exec_add32_lane {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16)
    (d : Reg) : exec (.alu32 .add d (.mem (lane .r9 k b))) s =
      some ((arithFlags s ((s.gpr d).setWidth 32 + lv s k b)
        (decide (2 ^ 32 ≤ ((s.gpr d).setWidth 32).toNat + (lv s k b).toNat))
        (addOverflow ((s.gpr d).setWidth 32) (lv s k b) ((s.gpr d).setWidth 32 + lv s k b))).setReg32 d
        ((s.gpr d).setWidth 32 + lv s k b)) := by
  have hr := lane_rw h hk hb
  simp only [laneA] at hr
  simp only [exec, execAlu32, readSrc32, State.load32, ea_lane, hr, ite_true, Option.bind_some]
  rfl

end VG.Proof.Seed.X86_64

end

end

/-!
# The steps of a round, lane by lane

Each step of the round (`step1` … `step4`) on one lane meets its `LaneSpec`
(`LaneOk`); `lanes_ok` then gives it on all sixteen.
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64

-- The steps share one set of rewrites, not all of which each step uses.
set_option linter.unusedSimpArgs false

theorem mem_tA : tSlot 0 ∈ arrays := by decide
theorem mem_aA : aSlot ∈ arrays := by decide
theorem mem_cA : cSlot ∈ arrays := by decide
theorem mem_dA : dSlot ∈ arrays := by decide
theorem mem_L0 : arrSlot 0 ∈ arrays := by decide
theorem mem_L1 : arrSlot 1 ∈ arrays := by decide
theorem mem_R0 : arrSlot 2 ∈ arrays := by decide
theorem mem_R1 : arrSlot 3 ∈ arrays := by decide

theorem room_congr {s s' : State} (h : Room s) (hr : s'.gpr .r9 = s.gpr .r9) (hw : s'.wr = s.wr) :
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

/-- The round key's halves are in `r11` and `r12`. -/
def KeysIn (k0 k1 : BitVec 32) (s : State) : Prop :=
  Room s ∧ (s.gpr .r11).setWidth 32 = k0 ∧ (s.gpr .r12).setWidth 32 = k1

theorem step1_ok (k0 k1 : BitVec 32) {b : Nat} (hb : b < 16) (s : State) (h : KeysIn k0 k1 s) :
    ∃ s', runBlock isa (step1 b) s = some s' ∧ LaneOk s s' (sp1 k0 k1) b := by
  obtain ⟨h, hk0, hk1⟩ := h
  rw [step1, runBlock_cons, exec_mov32_lane h mem_R0 hb, runStep_some, runBlock_cons,
    exec_xor32_reg, runStep_some, runBlock_cons, exec_store32_lane ?h1 mem_aA hb, runStep_some,
    runBlock_cons, exec_xor32_lane ?h2 mem_R1 hb, runStep_some, runBlock_cons,
    exec_xor32_reg, runStep_some, runBlock_cons, exec_store32_lane ?h3 mem_tA hb, runStep_some,
    runBlock_nil]
  case h1 | h2 | h3 => exact room_congr h rfl rfl
  refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp only [laneWrites, sp1, List.foldl_cons, List.foldl_nil, State.setReg32, gpr_setReg,
      reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, gpr_arithFlags, gpr_setMem, mem_setReg,
      mem_arithFlags, mem_setMem, lv_setMem, laneA_setMem, laneA_arithFlags, hk0, hk1,
      laneA_setReg _ _ (show ¬ Reg.r9 = .rax by decide), lv_setReg _ _ (show ¬ Reg.r9 = .rax by decide),
      lv_arithFlags, lv_eq]
    rw [readW_writeW_lane mem_R1 hb mem_aA hb (Or.inl (by decide)), lv_eq]
  · simp only [State.setReg32, gpr_setReg, gpr_arithFlags, gpr_setMem, h1, ↓reduceIte]

theorem step2_ok {b : Nat} (hb : b < 16) (s : State) (h : Room s) :
    ∃ s', runBlock isa (step2 b) s = some s' ∧ LaneOk s s' sp2 b := by
  rw [step2, runBlock_cons, exec_mov32_lane h mem_tA hb, runStep_some, runBlock_cons,
    exec_store32_lane ?h1 mem_cA hb, runStep_some, runBlock_cons, exec_add32_lane ?h2 mem_aA hb,
    runStep_some, runBlock_cons, exec_store32_lane ?h3 mem_tA hb, runStep_some, runBlock_nil]
  case h1 | h2 | h3 => exact room_congr h rfl rfl
  refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp only [laneWrites, sp2, List.foldl_cons, List.foldl_nil, State.setReg32, gpr_setReg,
      reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, gpr_arithFlags, gpr_setMem, mem_setReg,
      mem_arithFlags, mem_setMem, lv_setMem, laneA_setMem, laneA_arithFlags,
      laneA_setReg _ _ (show ¬ Reg.r9 = .rax by decide), lv_setReg _ _ (show ¬ Reg.r9 = .rax by decide),
      lv_arithFlags, lv_eq]
    rw [readW_writeW_lane mem_aA hb mem_cA hb (Or.inl (by decide)), lv_eq]
  · simp only [State.setReg32, gpr_setReg, gpr_arithFlags, gpr_setMem, h1, ↓reduceIte]

theorem step3_ok {b : Nat} (hb : b < 16) (s : State) (h : Room s) :
    ∃ s', runBlock isa (step3 b) s = some s' ∧ LaneOk s s' sp3 b := by
  rw [step3, runBlock_cons, exec_mov32_lane h mem_tA hb, runStep_some, runBlock_cons,
    exec_store32_lane ?h1 mem_dA hb, runStep_some, runBlock_cons, exec_add32_lane ?h2 mem_cA hb,
    runStep_some, runBlock_cons, exec_store32_lane ?h3 mem_tA hb, runStep_some, runBlock_nil]
  case h1 | h2 | h3 => exact room_congr h rfl rfl
  refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp only [laneWrites, sp3, List.foldl_cons, List.foldl_nil, State.setReg32, gpr_setReg,
      reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, gpr_arithFlags, gpr_setMem, mem_setReg,
      mem_arithFlags, mem_setMem, lv_setMem, laneA_setMem, laneA_arithFlags,
      laneA_setReg _ _ (show ¬ Reg.r9 = .rax by decide), lv_setReg _ _ (show ¬ Reg.r9 = .rax by decide),
      lv_arithFlags, lv_eq]
    rw [readW_writeW_lane mem_cA hb mem_dA hb (Or.inl (by decide)), lv_eq]
  · simp only [State.setReg32, gpr_setReg, gpr_arithFlags, gpr_setMem, h1, ↓reduceIte]

theorem step4_ok {b : Nat} (hb : b < 16) (s : State) (h : Room s) :
    ∃ s', runBlock isa (step4 b) s = some s' ∧ LaneOk s s' sp4 b := by
  rw [step4, runBlock_cons, exec_mov32_lane h mem_tA hb, runStep_some, runBlock_cons,
    exec_mov32_lane ?h1 mem_L1 hb, runStep_some, runBlock_cons, exec_xor32_reg, runStep_some,
    runBlock_cons, exec_store32_lane ?h2 mem_L1 hb, runStep_some, runBlock_cons,
    exec_add32_lane ?h3 mem_dA hb, runStep_some, runBlock_cons, exec_xor32_lane ?h4 mem_L0 hb,
    runStep_some, runBlock_cons, exec_store32_lane ?h5 mem_L0 hb, runStep_some, runBlock_nil]
  case h1 | h2 | h3 | h4 | h5 => exact room_congr h rfl rfl
  refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp only [laneWrites, sp4, List.foldl_cons, List.foldl_nil, State.setReg32, gpr_setReg,
      reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, gpr_arithFlags, gpr_setMem, mem_setReg,
      mem_arithFlags, mem_setMem, lv_setMem, laneA_setMem, laneA_arithFlags,
      laneA_setReg _ _ (show ¬ Reg.r9 = .rax by decide), lv_setReg _ _ (show ¬ Reg.r9 = .rax by decide),
      laneA_setReg _ _ (show ¬ Reg.r9 = .rcx by decide), lv_setReg _ _ (show ¬ Reg.r9 = .rcx by decide),
      lv_arithFlags, lv_eq]
    rw [readW_writeW_lane mem_dA hb mem_L1 hb (Or.inl (by decide)),
      readW_writeW_lane mem_L0 hb mem_L1 hb (Or.inl (by decide)), lv_eq, lv_eq]
  · simp only [State.setReg32, gpr_setReg, gpr_arithFlags, gpr_setMem, h1, h2, ↓reduceIte]

end VG.Proof.Seed.X86_64
