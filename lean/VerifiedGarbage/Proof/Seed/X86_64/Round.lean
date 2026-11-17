module

public import VerifiedGarbage.Proof.Framework.Bitslice.Sym
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Seed.SboxLit
public import VerifiedGarbage.Impl.Seed.X86_64.Ecb
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Seed.X86_64.G16
public import VerifiedGarbage.Proof.Seed.G16
public import VerifiedGarbage.Proof.Seed.G16Lanes
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Aes.X86_64.Encrypt

/-! ### `Seed.X86_64.Steps`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Seed.X86_64.Swap`, which only this module used -/

section

/-!
# Lanes and slots; exchanging the halves

A lane is half of a 64-bit slot (`lv_slot`), so `g16`'s words are lanes of
`tSlot 0` (`wordQ_lv`). `swap_ok`: `swapHalves` exchanges the arrays of
`L` (`arrSlot 0`, `arrSlot 1`) with those of `R` (`arrSlot 2`, `arrSlot 3`),
checked by evaluating its moves over named words (`Bitslice.names`).
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Seed.X86_64

theorem lv_slot (s : State) (k b : Nat) :
    lv s k b = ((slotW s (k + b / 2)) >>> (32 * (b % 2))).setWidth 32 := by
  obtain ha : laneA s k b = wordAddr (s.gpr .r9) (k + b / 2) + BitVec.ofNat 64 (4 * (b % 2)) := by
    simp only [laneA, wordAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2; omega_using []
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · rw [lv, ha, h, show wordAddr (s.gpr .r9) (k + b / 2) + BitVec.ofNat 64 (4 * 0) =
      wordAddr (s.gpr .r9) (k + b / 2) by simp, Mem.readW_lo32 (a := wordAddr (s.gpr .r9) (k + b / 2)) (v := slotW s (k + b / 2)) rfl]
    simp
  · rw [lv, ha, h, show 4 * 1 = 4 from rfl, Mem.readW_hi32 (a := wordAddr (s.gpr .r9) (k + b / 2)) (v := slotW s (k + b / 2)) rfl]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi]

theorem wordQ_lv (s : State) (w : Nat) :
    Proof.Seed.wordQ (fun i => slotW s (tSlot i)) w = lv s (tSlot 0) w := by
  rw [lv_slot]; rfl

/-- The slots `swapHalves` moves, and those below them. -/
def swapCfg : Cfg := { base := .r9, slots := 125, ext := .r9, exts := 0 }

def swapEnv : Env Nat := { reg := fun _ => none, slot := fun k => if k < 125 then some k else none }

def swapPost (e : Env Nat) : Bool :=
  (List.range 16).all (fun k => e.slot (93 + k) == some (109 + k) && e.slot (109 + k) == some (93 + k)) &&
    (List.range 93).all fun j => e.slot j == some j

theorem swap_check : check (names 64) swapCfg (fun _ => none) swapHalves swapEnv swapPost = true := by
  decide +kernel

theorem ok_of_room {s : State} (h : Room s) {c : Cfg} (hb : c.base = .r9) (hs : c.slots ≤ 132)
    (he : c.exts = 0) : Ok c s :=
  ⟨fun k hk => h.wr (by
      rw [hb]; exact Offset.contains_base _ (by unfold scratchSlots; omega_using [hs, hk]) (by omega_using [hs, hk])),
    fun k hk => by omega, by omega_using [hs], fun _ _ j hj => by omega⟩

theorem swap_writes (r : Reg) (h1 : r ≠ .rax) (h2 : r ≠ .rcx) :
    (swapHalves.all fun i => i.dst != some r) = true := by
  cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | decide

theorem swap_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa swapHalves s = some s' ∧
      (∀ w < 4, ∀ b < 16, lv s' (arrSlot w) b = lv s (arrSlot ((w + 2) % 4)) b) ∧
      (∀ j < 93, slotW s' j = slotW s j) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ Frame [workR s] s.mem s'.mem := by
  obtain hok : Ok swapCfg s := ok_of_room h rfl (by decide) rfl
  obtain hrel : Rel (NameRel (fun k => slotW s k)) swapCfg (fun _ => none) swapEnv s := by
    refine ⟨fun _ _ h => (by cases h), fun k a hk h => ?_, fun _ _ hk => (by cases hk)⟩
    simp only [swapEnv, show k < 125 from hk, ite_true, Option.some.injEq] at h
    subst h; rfl
  obtain ⟨e, he, hp⟩ := of_check _ _ _ swap_check
  obtain ⟨s', hs', p⟩ := run (names_sound _) hok hrel he
  simp only [swapPost, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hp
  have hr9 : s'.gpr .r9 = s.gpr .r9 := p.base
  obtain hsl : ∀ k a, k < 125 → e.slot k = some a → slotW s' k = slotW s a := by
    intro k a hk hka
    exact p.rel.slot k a hk hka
  refine ⟨s', hs', fun w hw b hb => ?_, fun j hj => hsl j j (by omega_using [hj]) (hp.2 j hj), p.rd, p.wr,
    fun r h1 h2 => p.other r ?_, ?_⟩
  · rw [lv_slot, lv_slot]
    congr 2
    rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_using [hw]) with rfl | rfl | rfl | rfl
    · exact hsl _ _ (by simp [arrSlot]; omega_using [hb]) ((hp.1 (b / 2) (by omega_using [hb])).1)
    · rw [show arrSlot 1 + b / 2 = 93 + (8 + b / 2) by simp [arrSlot]; omega_using [],
        show arrSlot ((1 + 2) % 4) + b / 2 = 109 + (8 + b / 2) by simp [arrSlot]; omega_using []]
      exact hsl _ _ (by omega_using [hb]) ((hp.1 (8 + b / 2) (by omega_using [hb])).1)
    · rw [show arrSlot 2 + b / 2 = 109 + b / 2 by simp [arrSlot],
        show arrSlot ((2 + 2) % 4) + b / 2 = 93 + b / 2 by simp [arrSlot]]
      exact hsl _ _ (by omega_using [hb]) ((hp.1 (b / 2) (by omega_using [hb])).2)
    · rw [show arrSlot 3 + b / 2 = 109 + (8 + b / 2) by simp [arrSlot]; omega_using [],
        show arrSlot ((3 + 2) % 4) + b / 2 = 93 + (8 + b / 2) by simp [arrSlot]; omega_using []]
      exact hsl _ _ (by omega_using [hb]) ((hp.1 (8 + b / 2) (by omega_using [hb])).2)
  · rw [swap_writes r h1 h2]; decide
  · have := p.frame
    refine this.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s, List.mem_singleton_self _, Region.sub_prefix (by simp [swapCfg])⟩

end VG.Proof.Seed.X86_64

end

end


/-!
# A round on x86-64

`g16_lanes` restates `g16_ok` on the lanes of the arrays, and `round_ok`
puts the steps of a round together: on every lane, the round's code does
RFC 4269 §2's round (`Spec.Seed.round`) to the arrays of `L0`, `L1`, `R0`,
`R1`, with the round key at `rdi`.
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.Seed.X86_64

theorem room_ok_gCfg {s : State} (h : Room s) : Ok gCfg s := ok_of_room h rfl (by decide) rfl

/-- `g16` on the lanes: `G` of `G`'s words, the other arrays kept. -/
theorem g16_lanes {s : State} (h : Room s) (hm : MasksIn s) :
    ∃ s', runBlock isa g16 s = some s' ∧
      (∀ w < 16, lv s' (tSlot 0) w = Spec.Seed.g (lv s (tSlot 0) w)) ∧
      (∀ k ∈ arrays, k ≠ tSlot 0 → ∀ b < 16, lv s' k b = lv s k b) ∧
      MasksIn s' ∧ Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ g16Writes → s'.gpr r = s.gpr r) ∧ Frame [workR s] s.mem s'.mem := by
  obtain ⟨s', hs', hg, hm', hrd, hwr, hregs, hfr⟩ := g16_ok (room_ok_gCfg h) hm
  obtain hr9 : s'.gpr .r9 = s.gpr .r9 := hregs _ (by decide)
  refine ⟨s', hs', fun w hw => ?_, fun k hk hkt b hb => ?_, hm', room_congr h hr9 hwr, hrd, hwr,
    hregs, ?_⟩
  · rw [← wordQ_lv, ← wordQ_lv]; exact hg w hw
  · have hb' := arrays_bound k hk
    obtain hk69 : 69 ≤ k := by
      simp only [arrays, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hkt | decide
    simp only [lv, laneA, hr9]
    refine hfr.readW (r := ⟨s.gpr .r9 + BitVec.ofNat 64 (8 * k + 4 * b), 4⟩)
      (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base (s.gpr .r9) (d := 8 * k + 4 * b) (n := 4) (k := 8 * 69)
      (by omega_using [hk69]) (by omega_using [hb, hb'])
  · refine hfr.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s, List.mem_singleton_self _, Region.sub_prefix (by simp [gCfg])⟩

/-! ## The round -/

/-- Lane `b` of the blocks' state: `(L0, L1, R0, R1)`. -/
def quad (s : State) (b : Nat) : Spec.Seed.Word × Spec.Seed.Word × Spec.Seed.Word × Spec.Seed.Word :=
  (lv s (arrSlot 0) b, lv s (arrSlot 1) b, lv s (arrSlot 2) b, lv s (arrSlot 3) b)

theorem reads1 (k0 k1 : BitVec 32) : ReadsArrays (sp1 k0 k1) := by
  intro kv hkv x y h
  simp only [sp1, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ mem_R0, h _ mem_R1]

theorem reads2 : ReadsArrays sp2 := by
  intro kv hkv x y h
  simp only [sp2, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ mem_tA, h _ mem_aA]

theorem reads3 : ReadsArrays sp3 := by
  intro kv hkv x y h
  simp only [sp3, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ mem_tA, h _ mem_cA]

theorem reads4 : ReadsArrays sp4 := by
  intro kv hkv x y h
  simp only [sp4, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ mem_tA, h _ mem_dA, h _ mem_L0, h _ mem_L1]

theorem dests1 (k0 k1 : BitVec 32) : ∀ kv ∈ sp1 k0 k1, kv.1 ∈ arrays := by
  intro kv hkv; simp only [sp1, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl
  · exact mem_aA
  · exact mem_tA
theorem dests2 : ∀ kv ∈ sp2, kv.1 ∈ arrays := by
  intro kv hkv; simp only [sp2, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> decide
theorem dests3 : ∀ kv ∈ sp3, kv.1 ∈ arrays := by
  intro kv hkv; simp only [sp3, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> decide
theorem dests4 : ∀ kv ∈ sp4, kv.1 ∈ arrays := by
  intro kv hkv; simp only [sp4, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> decide

/-- A step on all sixteen lanes, from a state where the scratch buffer is writable. -/
theorem lanes16_room {f : Nat → List Instr} {sp : LaneSpec} (hsp : ∀ kv ∈ sp, kv.1 ∈ arrays)
    (hd : ReadsArrays sp) (hf : ∀ b < 16, ∀ s, Room s → ∃ s', runBlock isa (f b) s = some s' ∧ LaneOk s s' sp b)
    {s : State} (h : Room s) :
    ∃ s', runBlock isa (lanes16 f) s = some s' ∧ Room s' ∧
      (∀ k ∈ arrays, ∀ b < 16, lv s' k b = newVal sp k (fun k' => lv s k' b)) ∧
      Frame [arraysR s] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) := by
  obtain ⟨s', hs', hP, hv, rest⟩ := lanes_ok hsp hd (P := Room)
    (fun _ s s' hP hok => room_congr hP (hok.regs _ (by decide) (by decide)) hok.wr) hf h 16 (Nat.le_refl _)
  exact ⟨s', hs', hP, fun k hk b hb => by rw [hv k hk b hb, ite_eq_left hb], rest⟩

/-- The masks are outside the arrays. -/
theorem masks_of_arrays {s s' : State} (hm : MasksIn s) (hr9 : s'.gpr .r9 = s.gpr .r9)
    (hfr : Frame [arraysR s] s.mem s'.mem) : MasksIn s' := by
  intro kv hkv
  obtain hlt := maskSlots_lt kv hkv
  rw [← hm kv hkv]
  show s'.mem.readW (wordAddr (s'.gpr .r9) kv.1) 64 = s.mem.readW (wordAddr (s.gpr .r9) kv.1) 64
  rw [hr9]
  refine hfr.readW (r := ⟨wordAddr (s.gpr .r9) kv.1, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ (Or.inl (by omega_using [hlt])) (by omega_using [hlt]) (by omega_using [])

theorem scratch_of_arrays {s s' : State} (hfr : Frame [arraysR s] s.mem s'.mem) :
    Frame [workR s] s.mem s'.mem :=
  hfr.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s, List.mem_singleton_self _, Offset.sub_base _ (by omega_using [])⟩

theorem exec_add_imm (s : State) (d : Reg) (v : BitVec 32) :
    ∃ t, exec (.alu .add d (.imm v)) s = some t ∧ t.gpr d = s.gpr d + v.signExtend 64 ∧
      (∀ r, r ≠ d → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  ⟨_, rfl, by simp [gpr_setReg], fun r h => by simp [gpr_setReg, h, gpr_arithFlags], rfl, rfl, rfl⟩

theorem exec_sub_imm (s : State) (d : Reg) (v : BitVec 32) :
    ∃ t, exec (.alu .sub d (.imm v)) s = some t ∧ t.gpr d = s.gpr d - v.signExtend 64 ∧
      t.zf = some (s.gpr d - v.signExtend 64 == 0) ∧
      (∀ r, r ≠ d → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  ⟨_, rfl, by simp [gpr_setReg], rfl, fun r h => by simp [gpr_setReg, h, gpr_arithFlags], rfl, rfl, rfl⟩

theorem runBlock_trans {a b : List Instr} {s s' s'' : State} (h1 : runBlock isa a s = some s')
    (h2 : runBlock isa b s' = some s'') : runBlock isa (a ++ b) s = some s'' := by
  rw [runBlock_append, h1, Option.bind_some, h2]

theorem keepRegs : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .r8, .r9, .rsp],
    r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .r11 ∧ r ≠ .r12 := by decide

theorem notG16 : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .r8, .r9, .rsp], r ∉ g16Writes := by decide

theorem round_ok (d : Spec.Seed.Direction) {s : State} (h : Room s) (hm : MasksIn s)
    (hk0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 4)
    (hk1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + 4) 4) :
    ∃ s', runBlock isa (round d) s = some s' ∧
      (∀ b < 16, quad s' b =
        Spec.Seed.round (s.mem.readW (s.gpr .rdi) 32, s.mem.readW (s.gpr .rdi + 4) 32) (quad s b)) ∧
      MasksIn s' ∧ Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr .rdi = s.gpr .rdi + (BitVec.ofInt 32 (keyStep d)).signExtend 64 ∧
      s'.gpr .r8 = s.gpr .r8 - (1 : BitVec 32).signExtend 64 ∧
      s'.zf = some (s.gpr .r8 - (1 : BitVec 32).signExtend 64 == 0) ∧
      s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rdx = s.gpr .rdx ∧ s'.gpr .r9 = s.gpr .r9 ∧
      s'.gpr .rsp = s.gpr .rsp ∧ Frame [workR s] s.mem s'.mem := by
  let K0 := s.mem.readW (s.gpr .rdi) 32
  let K1 := s.mem.readW (s.gpr .rdi + 4) 32
  -- The round key.
  obtain ea0 : s.ea { base := .rdi, disp := 0 } = s.gpr .rdi := by simp [State.ea]
  obtain ea4 : (s.setReg32 .r11 K0).ea { base := .rdi, disp := 4 } = s.gpr .rdi + 4 := by
    simp [State.ea, State.setReg32, gpr_setReg]
  obtain e1 : exec (.mov32 .r11 (.mem { base := .rdi, disp := 0 })) s = some (s.setReg32 .r11 K0) := by
    rw [exec_mov32_mem (by rw [ea0]; exact hk0), ea0]
  obtain e2 : exec (.mov32 .r12 (.mem { base := .rdi, disp := 4 })) (s.setReg32 .r11 K0) =
      some ((s.setReg32 .r11 K0).setReg32 .r12 K1) := by
    rw [exec_mov32_mem (by rw [ea4]; exact hk1), ea4]; rfl
  let s2 := (s.setReg32 .r11 K0).setReg32 .r12 K1
  obtain hrun2 : runBlock isa [.mov32 .r11 (.mem { base := .rdi, disp := 0 }),
      .mov32 .r12 (.mem { base := .rdi, disp := 4 })] s = some s2 := by
    rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_nil]
  obtain hkeys : KeysIn K0 K1 s2 := by
    refine ⟨room_congr h rfl rfl, ?_, ?_⟩ <;>
      simp [s2, State.setReg32, gpr_setReg]
  obtain lv2 : ∀ k b, lv s2 k b = lv s k b := fun k b => by
    simp only [s2, State.setReg32, lv_setReg _ _ (show ¬ Reg.r9 = .r12 by decide),
      lv_setReg _ _ (show ¬ Reg.r9 = .r11 by decide)]
  obtain g2 : ∀ r, r ≠ .r11 → r ≠ .r12 → s2.gpr r = s.gpr r := fun r h1 h2 => by
    simp [s2, State.setReg32, gpr_setReg, h1, h2]
  -- The steps.
  obtain ⟨s3, hs3, hP3, hv3, fr3, rd3, wr3, rg3⟩ := lanes_ok (dests1 K0 K1) (reads1 K0 K1)
    (P := KeysIn K0 K1)
    (fun _ s s' hP hok => ⟨room_congr hP.1 (hok.regs _ (by decide) (by decide)) hok.wr,
      by rw [hok.regs _ (by decide) (by decide)]; exact hP.2.1,
      by rw [hok.regs _ (by decide) (by decide)]; exact hP.2.2⟩)
    (fun b hb s hs => step1_ok K0 K1 hb s hs) hkeys 16 (Nat.le_refl _)
  obtain r93 : s3.gpr .r9 = s2.gpr .r9 := rg3 _ (by decide) (by decide)
  obtain hm3 : MasksIn s3 := masks_of_arrays (masks_of_arrays hm rfl (Frame.refl _ _)) r93 fr3
  obtain ⟨s4, hs4, hg4, hk4, hm4, h4, rd4, wr4, rg4, fr4⟩ := g16_lanes hP3.1 hm3
  obtain ⟨s5, hs5, h5, hv5, fr5, rd5, wr5, rg5⟩ := lanes16_room dests2 reads2 (fun b hb s hs => step2_ok hb s hs) h4
  obtain hm5 : MasksIn s5 := masks_of_arrays hm4 (rg5 _ (by decide) (by decide)) fr5
  obtain ⟨s6, hs6, hg6, hk6, hm6, h6, rd6, wr6, rg6, fr6⟩ := g16_lanes h5 hm5
  obtain ⟨s7, hs7, h7, hv7, fr7, rd7, wr7, rg7⟩ := lanes16_room dests3 reads3 (fun b hb s hs => step3_ok hb s hs) h6
  obtain hm7 : MasksIn s7 := masks_of_arrays hm6 (rg7 _ (by decide) (by decide)) fr7
  obtain ⟨s8, hs8, hg8, hk8, hm8, h8, rd8, wr8, rg8, fr8⟩ := g16_lanes h7 hm7
  obtain ⟨s9, hs9, h9, hv9, fr9, rd9, wr9, rg9⟩ := lanes16_room dests4 reads4 (fun b hb s hs => step4_ok hb s hs) h8
  obtain hm9 : MasksIn s9 := masks_of_arrays hm8 (rg9 _ (by decide) (by decide)) fr9
  obtain ⟨s10, hs10, hsw, hlow, rd10, wr10, rg10, fr10⟩ := swap_ok h9
  obtain ⟨s11, e11, rdi11, rg11, mem11, rd11, wr11⟩ :=
    exec_add_imm s10 .rdi (BitVec.ofInt 32 (keyStep d))
  obtain ⟨s12, e12, r812, zf12, rg12, mem12, rd12, wr12⟩ := exec_sub_imm s11 .r8 1
  obtain hrun : runBlock isa [.alu .add .rdi (.imm (BitVec.ofInt 32 (keyStep d))), .alu .sub .r8 (.imm 1)]
      s10 = some s12 := by
    rw [runBlock_cons, e11, runStep_some, runBlock_cons, e12, runStep_some, runBlock_nil]
  -- Registers through the steps.
  obtain keep : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .r8, .r9, .rsp], s10.gpr r = s.gpr r := by
    intro r hr
    obtain hg := notG16 r hr
    obtain ⟨h1, h2, h3, h4⟩ := keepRegs r hr
    rw [rg10 r h1 h2, rg9 r h1 h2, rg8 r hg, rg7 r h1 h2, rg6 r hg, rg5 r h1 h2, rg4 r hg,
      rg3 r h1 h2, g2 r h3 h4]
  obtain r9_10 : s10.gpr .r9 = s.gpr .r9 := keep _ (by decide)
  obtain r9_12 : s12.gpr .r9 = s.gpr .r9 := by
    rw [rg12 _ (by decide), rg11 _ (by decide), r9_10]
  obtain lv12 : ∀ k b, lv s12 k b = lv s10 k b := fun k b => by
    simp only [lv, laneA, mem12, mem11, r9_12, r9_10]
  refine ⟨s12, ?_, fun b hb => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact runBlock_trans (runBlock_trans (runBlock_trans (runBlock_trans (runBlock_trans
      (runBlock_trans (runBlock_trans (runBlock_trans (runBlock_trans hrun2 hs3) hs4) hs5) hs6)
      hs7) hs8) hs9) hs10) hrun
  · -- The values, stage by stage.
    obtain ar : ∀ k ∈ arrays, k ∈ arrays := fun _ h => h
    obtain t3 : lv s3 (tSlot 0) b = (lv s (arrSlot 2) b ^^^ K0) ^^^ (lv s (arrSlot 3) b ^^^ K1) := by
      rw [hv3 _ mem_tA b hb, ite_eq_left hb]
      simp [newVal, sp1, lv2, tSlot, aSlot, arrSlot, BitVec.xor_assoc]
    obtain a3 : lv s3 aSlot b = lv s (arrSlot 2) b ^^^ K0 := by
      rw [hv3 _ mem_aA b hb, ite_eq_left hb]
      simp [newVal, sp1, lv2, tSlot, aSlot, arrSlot]
    obtain o3 : ∀ k ∈ [arrSlot 0, arrSlot 1, arrSlot 2, arrSlot 3], lv s3 k b = lv s k b := by
      intro k hk
      obtain hk' : k ∈ arrays := by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
      rw [hv3 _ hk' b hb, ite_eq_left hb]
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> simp [newVal, sp1, lv2, tSlot, aSlot, arrSlot]
    -- c
    obtain t4 : lv s4 (tSlot 0) b = Spec.Seed.g (lv s3 (tSlot 0) b) := hg4 b hb
    obtain k4 : ∀ k ∈ arrays, k ≠ tSlot 0 → lv s4 k b = lv s3 k b := fun k hk hkt => hk4 k hk hkt b hb
    obtain t5 : lv s5 (tSlot 0) b = lv s4 (tSlot 0) b + lv s4 aSlot b := by
      rw [hv5 _ mem_tA b hb]; simp [newVal, sp2, tSlot, aSlot, cSlot]
    obtain c5 : lv s5 cSlot b = lv s4 (tSlot 0) b := by
      rw [hv5 _ mem_cA b hb]; simp [newVal, sp2, tSlot, aSlot, cSlot]
    obtain o5 : ∀ k ∈ arrays, k ≠ tSlot 0 → k ≠ cSlot → lv s5 k b = lv s4 k b := by
      intro k hk h1 h2; rw [hv5 _ hk b hb]; simp [newVal, sp2, Ne.symm h1, Ne.symm h2]
    -- d
    obtain t6 : lv s6 (tSlot 0) b = Spec.Seed.g (lv s5 (tSlot 0) b) := hg6 b hb
    obtain k6 : ∀ k ∈ arrays, k ≠ tSlot 0 → lv s6 k b = lv s5 k b := fun k hk hkt => hk6 k hk hkt b hb
    obtain t7 : lv s7 (tSlot 0) b = lv s6 (tSlot 0) b + lv s6 cSlot b := by
      rw [hv7 _ mem_tA b hb]; simp [newVal, sp3, tSlot, dSlot, cSlot]
    obtain d7 : lv s7 dSlot b = lv s6 (tSlot 0) b := by
      rw [hv7 _ mem_dA b hb]; simp [newVal, sp3, tSlot, dSlot, cSlot]
    obtain o7 : ∀ k ∈ arrays, k ≠ tSlot 0 → k ≠ dSlot → lv s7 k b = lv s6 k b := by
      intro k hk h1 h2; rw [hv7 _ hk b hb]; simp [newVal, sp3, Ne.symm h1, Ne.symm h2]
    -- e
    obtain t8 : lv s8 (tSlot 0) b = Spec.Seed.g (lv s7 (tSlot 0) b) := hg8 b hb
    obtain k8 : ∀ k ∈ arrays, k ≠ tSlot 0 → lv s8 k b = lv s7 k b := fun k hk hkt => hk8 k hk hkt b hb
    obtain l0_9 : lv s9 (arrSlot 0) b = (lv s8 (tSlot 0) b + lv s8 dSlot b) ^^^ lv s8 (arrSlot 0) b := by
      rw [hv9 _ mem_L0 b hb]; simp [newVal, sp4, arrSlot]
    obtain l1_9 : lv s9 (arrSlot 1) b = lv s8 (arrSlot 1) b ^^^ lv s8 (tSlot 0) b := by
      rw [hv9 _ mem_L1 b hb]; simp [newVal, sp4, arrSlot]
    obtain r0_9 : lv s9 (arrSlot 2) b = lv s8 (arrSlot 2) b := by
      rw [hv9 _ mem_R0 b hb]; simp [newVal, sp4, arrSlot]
    obtain r1_9 : lv s9 (arrSlot 3) b = lv s8 (arrSlot 3) b := by
      rw [hv9 _ mem_R1 b hb]; simp [newVal, sp4, arrSlot]
    -- The arrays other than `G`'s words, through the `G`s and the steps that do not write them.
    obtain xs : ∀ k ∈ [arrSlot 0, arrSlot 1, arrSlot 2, arrSlot 3],
        lv s8 k b = lv s k b := by
      intro k hk
      obtain hk' : k ∈ arrays := by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
      obtain hkt : k ≠ tSlot 0 := by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
      obtain hkc : k ≠ cSlot := by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
      obtain hkd : k ≠ dSlot := by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
      rw [k8 k hk' hkt, o7 k hk' hkt hkd, k6 k hk' hkt, o5 k hk' hkt hkc, k4 k hk' hkt, o3 k hk]
    obtain a4 : lv s4 aSlot b = lv s3 aSlot b := k4 _ mem_aA (by decide)
    obtain c6 : lv s6 cSlot b = lv s5 cSlot b := k6 _ mem_cA (by decide)
    obtain d8 : lv s8 dSlot b = lv s7 dSlot b := k8 _ mem_dA (by decide)
    simp only [quad, lv12, hsw 0 (by decide) b hb, hsw 1 (by decide) b hb, hsw 2 (by decide) b hb,
      hsw 3 (by decide) b hb]
    simp only [show (0 + 2) % 4 = 2 from rfl, show (1 + 2) % 4 = 3 from rfl,
      show (2 + 2) % 4 = 0 from rfl, show (3 + 2) % 4 = 1 from rfl]
    simp only [r0_9, r1_9, l0_9, l1_9]
    simp only [xs (arrSlot 0) (by simp), xs (arrSlot 1) (by simp), xs (arrSlot 2) (by simp),
      xs (arrSlot 3) (by simp), d8, d7, t8, t7, c6, c5, t6, t5, t4, a4, a3, t3]
    simp only [Spec.Seed.round, Spec.Seed.f, K0, K1, BitVec.xor_comm (lv s (arrSlot 0) b),
      BitVec.xor_comm (lv s (arrSlot 1) b)]
  · intro kv hkv
    obtain hlt := maskSlots_lt kv hkv
    rw [← hm9 kv hkv]
    show s12.mem.readW (wordAddr (s12.gpr .r9) kv.1) 64 = s9.mem.readW (wordAddr (s9.gpr .r9) kv.1) 64
    rw [mem12, mem11, r9_12, ← r9_10]
    exact hlow kv.1 (by omega_using [hlt])
  · exact room_congr h r9_12 (by rw [wr12, wr11, wr10, wr9, wr8, wr7, wr6, wr5, wr4, wr3]; rfl)
  · rw [rd12, rd11, rd10, rd9, rd8, rd7, rd6, rd5, rd4, rd3]; rfl
  · rw [wr12, wr11, wr10, wr9, wr8, wr7, wr6, wr5, wr4, wr3]; rfl
  · rw [rg12 _ (by decide), rdi11, keep _ (by decide)]
  · rw [r812, rg11 _ (by decide), keep _ (by decide)]
  · rw [zf12, rg11 _ (by decide), keep _ (by decide)]
  · rw [rg12 _ (by decide), rg11 _ (by decide), keep _ (by decide)]
  · rw [rg12 _ (by decide), rg11 _ (by decide), keep _ (by decide)]
  · exact r9_12
  · rw [rg12 _ (by decide), rg11 _ (by decide), keep _ (by decide)]
  · -- The frames, all in the scratch buffer.
    obtain fc : ∀ {t : State} {m m' : Mem}, t.gpr .r9 = s.gpr .r9 → Frame [workR t] m m' →
        Frame [workR s] m m' := fun ht hf => by simpa [workR, ht] using hf
    rw [mem12, mem11]
    refine (fc rfl (scratch_of_arrays fr3)).trans ?_
    refine (fc (rg3 _ (by decide) (by decide)) fr4).trans ?_
    refine (fc ?_ (scratch_of_arrays fr5)).trans ?_
    · rw [rg4 _ (by decide), rg3 _ (by decide) (by decide)]; rfl
    refine (fc ?_ fr6).trans ?_
    · rw [rg5 _ (by decide) (by decide), rg4 _ (by decide), rg3 _ (by decide) (by decide)]; rfl
    refine (fc ?_ (scratch_of_arrays fr7)).trans ?_
    · rw [rg6 _ (by decide), rg5 _ (by decide) (by decide), rg4 _ (by decide),
        rg3 _ (by decide) (by decide)]; rfl
    refine (fc ?_ fr8).trans ?_
    · rw [rg7 _ (by decide) (by decide), rg6 _ (by decide), rg5 _ (by decide) (by decide),
        rg4 _ (by decide), rg3 _ (by decide) (by decide)]; rfl
    refine (fc ?_ (scratch_of_arrays fr9)).trans ?_
    · rw [rg8 _ (by decide), rg7 _ (by decide) (by decide), rg6 _ (by decide),
        rg5 _ (by decide) (by decide), rg4 _ (by decide), rg3 _ (by decide) (by decide)]; rfl
    refine fc ?_ fr10
    rw [rg9 _ (by decide) (by decide), rg8 _ (by decide), rg7 _ (by decide) (by decide),
      rg6 _ (by decide), rg5 _ (by decide) (by decide), rg4 _ (by decide),
      rg3 _ (by decide) (by decide)]; rfl

end VG.Proof.Seed.X86_64
