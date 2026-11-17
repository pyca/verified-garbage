module

public import VerifiedGarbage.Proof.Framework.Bitslice.Sym
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Seed.SboxLit
public import VerifiedGarbage.Impl.Seed.AArch64.Ecb
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Seed.AArch64.G16
public import VerifiedGarbage.Proof.Seed.G16
public import VerifiedGarbage.Proof.Seed.G16Lanes
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Aes.AArch64.Encrypt

/-! ### `Seed.AArch64.Steps`, which this module and modules that import it used -/

section

/-! ### `Seed.AArch64.Lanes`, which this module and modules that import it used -/

section

/-! ### `Seed.AArch64.G16`, which this module and modules that import it used -/

section

/-!
# `g16` on AArch64

`g16_ok`: `g16` replaces each of the sixteen words in `tSlot 0 … tSlot 7`
with `G` of it. Its linear layers, which build their masks with `movz` and
`movk`, are checked by evaluation over the lane domain (`g16In_check`,
`g16Out_check`: the planes of `M`, and the words from the S-box's planes, as
`Proof/Seed/G16.lean` states them), the S-box by AES's proof
(`Proof.Aes.AArch64.sbox_ok`), and `g16_words` puts them together.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Seed VG.Impl.Seed.AArch64
open VG.Impl.Aes.AArch64 (q t0 t1 sb sboxCode)
open VG.Proof.Seed (l1 l2 wordQ g16_words l2Lane l2_lt)
open VG.Proof.Aes.AArch64 (layerWrites layerKeep writes_rest)

/-- The slots `g16` reads and writes: the S-box's and the words. -/
def gCfg : Cfg := { base := sb, slots := 56, ext := sb, exts := 0 }

/-- Slot `k` of the scratch buffer. -/
def slotW (s : State) (k : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr sb) k) 64

/-! ## The checks -/

/-- The words as atoms (word `i` in `tSlot i`). -/
def env1 : Env (Nat × Nat) :=
  { reg := fun _ => none, slot := fun k => if 48 ≤ k ∧ k < 56 then some (inWord (k - 48)) else none }

def post1 (e : Env (Nat × Nat)) : Bool :=
  (List.range 8).all fun j =>
    e.reg (q j) == some (outWord (l1 j)) && (List.range 64).all fun p => (l1 j p).all (· < 2 ^ 9)

theorem g16In_check : check (lanes 64 9) gCfg (fun _ => none) g16In env1 post1 = true := by
  decide +kernel

/-- The S-box's planes as atoms (plane `j` in `q j`). -/
def env2 : Env (Nat × Nat) :=
  { reg := fun r => ((List.range 8).find? (fun j => q j == r)).map inWord, slot := fun _ => none }

def post2 (e : Env (Nat × Nat)) : Bool :=
  (List.range 8).all fun i =>
    e.slot (tSlot i) == some (gConst.toNat, mk 64 (l2 i) 64) &&
      (List.range 64).all fun t => (l2 i t).all (· < 2 ^ 9)

/-- `post2`, against the table of the output layer's lanes (`Proof/Seed/G16Lanes.lean`): what the
kernel evaluates. -/
def post2K (e : Env (Nat × Nat)) : Bool :=
  (List.range 8).all fun i => e.slot (tSlot i) == some (gConst.toNat, l2Lane i)

theorem post2_of_K {e : Env (Nat × Nat)} (h : post2K e = true) : post2 e = true := by
  simp only [post2K, post2, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h ⊢
  exact fun i hi => ⟨h i hi, fun t ht a ha => l2_lt hi ht a ha⟩

theorem g16Out_check : check (lanes 64 9) gCfg (fun _ => none) g16Out env2 post2 = true := by
  obtain ⟨e, he, hp⟩ := of_check _ _ _ (show check (lanes 64 9) gCfg (fun _ => none) g16Out env2 post2K = true by lit_decide)
  unfold check
  rw [he]
  exact post2_of_K hp

/-! ## Relating the checks to the machine -/

/-- An output word with the constant bits `c`. -/
theorem outWordC_rel {k : Nat} {W : Nat → BitVec 64} {g : Nat → List Nat} {c : Nat} {x : BitVec 64}
    (hg : ∀ p < 64, ∀ a ∈ g p, a < 2 ^ k) (h : LaneRel k (assign W (2 ^ k)) (c, mk 64 g 64) x) :
    ∀ p < 64, x.getLsbD p = (c.testBit p ^^ xorBits W (g p)) := by
  intro p hp
  rw [h.2 p hp, par_mk hp (Nat.le_refl _) _ (fun q hq => hg q hq), xorA_assign W (hg p hp)]
  simp [hp]

theorem g16_keeps : layerKeep.all (fun r => g16.all fun i => !clobbers i r) = true := by
  decide +kernel

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

theorem dst_append (a b : List Instr) (r : Reg) :
    ((a ++ b).all fun i => !clobbers i r) =
      ((a.all fun i => !clobbers i r) && (b.all fun i => !clobbers i r)) := List.all_append

/-- `g16`: `G` of every word. -/
theorem g16_ok {s : State} (hok : Ok gCfg s) :
    ∃ s', runBlock isa g16 s = some s' ∧
      (∀ w < 16, wordQ (fun i => slotW s' (tSlot i)) w =
        Spec.Seed.g (wordQ (fun i => slotW s (tSlot i)) w)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion gCfg s] s.mem s'.mem := by
  let In : Nat → BitVec 64 := fun i => slotW s (tSlot i)
  -- The input layer.
  have hrel1 : Rel (LaneRel 9 (assign In (2 ^ 9))) gCfg (fun _ => none) env1 s := by
    refine ⟨fun r a h => (by cases h), fun k a hk h => ?_, fun _ _ hk => (by cases hk),
      fun _ _ h => (by cases h)⟩
    simp only [env1] at h
    split at h
    · rename_i hk'
      simp only [Option.some.injEq] at h; subst h
      have := inWord_rel In (i := k - 48) (k := 9) (by omega_using [hk'])
      simpa [In, slotW, tSlot, show 48 + (k - 48) = k by omega_using [hk'], gCfg] using this
    · cases h
  obtain ⟨e1, he1, hp1⟩ := of_check _ _ _ g16In_check
  obtain ⟨s1, hs1, p1⟩ := run lanes_sound hok hrel1 he1
  simp only [post1, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hp1
  let Pl : Nat → BitVec 64 := fun j => s1.gpr (q j)
  have h1 : ∀ j < 8, ∀ p < 64, (Pl j).getLsbD p = xorBits In (l1 j p) := by
    intro j hj
    have hj' := hp1 j hj
    simp only [decide_eq_true_eq] at hj'
    exact outWord_rel (fun p hp a ha => hj'.2 p hp a ha) (p1.rel.reg _ _ hj'.1)
  -- The S-box.
  have hokS : Ok Proof.Aes.AArch64.sboxCfg s1 :=
    ⟨fun k hk => p1.ok.slotIn k (by simp [Proof.Aes.AArch64.sboxCfg, gCfg] at hk ⊢; omega_using [hk]),
      fun _ hk => (by cases hk), by decide, fun _ _ _ hj => (by cases hj)⟩
  obtain ⟨s2, hs2, hS, rd2, wr2, sp2, oth2, fr2⟩ := Proof.Aes.AArch64.sbox_ok hokS
  let S : Nat → BitVec 64 := fun j => s2.gpr (q j)
  have hsb2 : s2.gpr sb = s1.gpr sb := oth2 _ (by decide)
  -- The output layer.
  have hok2 : Ok gCfg s2 := p1.ok.congr hsb2 hsb2 rd2 wr2
  have hrel2 : Rel (LaneRel 9 (assign S (2 ^ 9))) gCfg (fun _ => none) env2 s2 := by
    refine ⟨fun r a h => ?_, fun k a _ h => (by cases h), fun _ _ hk => (by cases hk),
      fun _ _ h => (by cases h)⟩
    simp only [env2, Option.map_eq_some_iff] at h
    obtain ⟨j, hf, rfl⟩ := h
    have hr : q j = r := by simpa using List.find?_some hf
    have hj := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    subst hr
    exact inWord_rel S (k := 9) (by omega_using [hj])
  obtain ⟨e2, he2, hp2⟩ := of_check _ _ _ g16Out_check
  obtain ⟨s3, hs3, p2⟩ := run lanes_sound hok2 hrel2 he2
  simp only [post2, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hp2
  have hb1 : s1.gpr sb = s.gpr sb := p1.base
  have hb2 : s2.gpr sb = s.gpr sb := hsb2.trans hb1
  let Out : Nat → BitVec 64 := fun i => slotW s3 (tSlot i)
  have h2 : ∀ i < 8, ∀ t < 64, (Out i).getLsbD t = (gConst.getLsbD t ^^ xorBits S (l2 i t)) := by
    intro i hi
    have hi' := hp2 i hi
    simp only [decide_eq_true_eq] at hi'
    have hl : LaneRel 9 (assign S (2 ^ 9)) (gConst.toNat, mk 64 (l2 i) 64) (Out i) := by
      have := p2.rel.slot _ _ (by simp [tSlot, gCfg]; omega_using [hi]) hi'.1
      simpa [Out, slotW, gCfg, p2.base, hb2] using this
    intro t ht
    rw [outWordC_rel (fun p hp a ha => hi'.2 p hp a ha) hl t ht, BitVec.testBit_toNat]
  refine ⟨s3, ?_, ?_, p2.rd.trans (rd2.trans p1.rd), p2.wr.trans (wr2.trans p1.wr),
    p2.sp.trans (sp2.trans p1.sp), fun r hr => ?_, ?_⟩
  · rw [g16, runBlock_append, runBlock_append, hs1, Option.bind_some, hs2, Option.bind_some, hs3]
  · have := g16_words h1 hS h2
    intro w hw
    have e := this w hw
    simpa [Out, In, slotW, p2.base, hb2] using e
  · have hk := writes_rest g16_keeps r hr
    simp only [g16, dst_append, Bool.and_eq_true] at hk
    rw [p2.other r (by simp [hk.2]), oth2 r hr, p1.other r (by simp [hk.1.1])]
  · refine p1.frame.trans (Frame.trans (Frame.sub fr2 ?_) ?_)
    · intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨slotRegion gCfg s, List.mem_singleton_self _, ?_⟩
      show Region.Sub ⟨s1.gpr sb, 8 * 48⟩ ⟨s.gpr sb, 8 * 56⟩
      rw [hb1]
      exact Region.sub_prefix (by omega_using [])
    · have := p2.frame
      simp only [slotRegion] at this ⊢
      rw [show s2.gpr gCfg.base = s.gpr gCfg.base from hb2] at this
      exact this

end VG.Proof.Seed.AArch64

end

end

/-!
# The arrays of 32-bit words in the scratch buffer

As on x86-64 (`Proof/Seed/X86_64/Round.lean`): the ECB code keeps sixteen
lanes of each of its arrays (`G`'s words, `a`, `c`, `d` and the blocks'
words) in the scratch buffer at `x5`: lane `b` of the array at slot `k` is
the 32-bit word at `x5 + 8k + 4b` (`laneA`, `lv`). This file has the 32-bit
instructions' effects on them, and `lanes_ok`, which runs a step written for
one lane (`lanes16 f`, `f b` touching only lane `b` of each array) on all
sixteen.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Seed.AArch64
open VG.Impl.Aes.AArch64 (sb)

/-- Lane `b` of the array at slot `k`. -/
def laneA (s : State) (k b : Nat) : Addr := s.gpr .x5 + BitVec.ofNat 64 (8 * k + 4 * b)

def lv (s : State) (k b : Nat) : BitVec 32 := s.mem.readW (laneA s k b) 32

/-- The scratch buffer. -/
def scratchR (s : State) : Region := ⟨s.gpr .x5, 8 * scratchSlots⟩

/-- The working area: every slot but the saved registers' (slots 0 to 111). -/
def workR (s : State) : Region := ⟨s.gpr .x5, 8 * 112⟩

/-- The arrays' slots, 48 to 111. -/
def arraysR (s : State) : Region := ⟨s.gpr .x5 + BitVec.ofNat 64 (8 * 48), 8 * 64⟩

/-- The arrays: their first slots. -/
def arrays : List Nat := [tSlot 0, aSlot, cSlot, dSlot, arrSlot 0, arrSlot 1, arrSlot 2, arrSlot 3]

theorem arrays_bound : ∀ k ∈ arrays, 48 ≤ k ∧ k + 8 ≤ 112 := by decide

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
`x14` and `x15`. -/
structure LaneOk (s s' : State) (sp : LaneSpec) (b : Nat) : Prop where
  mem : s'.mem = laneWrites s sp b
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  regs : ∀ r, r ≠ .x14 → r ≠ .x15 → s'.gpr r = s.gpr r

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
      (∀ r, r ≠ .x14 → r ≠ .x15 → s'.gpr r = s₀.gpr r) := by
  intro n hn
  induction n with
  | zero => exact ⟨s₀, runBlock_nil, h₀, fun k _ b _ => by simp, Frame.refl _ _, rfl, rfl, fun _ _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨s, hs, hPs, hv, hfr, hrd, hwr, hregs⟩ := ih (by omega_using [hn])
    obtain ⟨s', hs', hok⟩ := hf n (by omega_using [hn]) s hPs
    have hr9 : s.gpr .x5 = s₀.gpr .x5 := hregs _ (by decide) (by decide)
    have hr9' : s'.gpr .x5 = s.gpr .x5 := hok.regs _ (by decide) (by decide)
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

theorem laneA_write (s : State) (sz : Size) {r : Reg} (v : BitVec sz.bits) (h : ¬Reg.x5 = r) (k b : Nat) :
    laneA (s.write sz r v) k b = laneA s k b := by
  simp only [laneA, gpr_write_of_ne _ _ _ h]

theorem lv_write (s : State) (sz : Size) {r : Reg} (v : BitVec sz.bits) (h : ¬Reg.x5 = r) (k b : Nat) :
    lv (s.write sz r v) k b = lv s k b := by
  simp only [lv, laneA_write _ _ _ h, mem_write]

/-- `s` with the memory `m`. -/
def setMem (s : State) (m : Mem) : State := { s with mem := m }

theorem laneA_setMem (s : State) (m : Mem) (k b : Nat) : laneA (setMem s m) k b = laneA s k b := rfl
theorem lv_setMem (s : State) (m : Mem) (k b : Nat) :
    lv (setMem s m) k b = m.readW (laneA s k b) 32 := rfl
theorem mem_setMem (s : State) (m : Mem) : (setMem s m).mem = m := rfl
theorem gpr_setMem (s : State) (m : Mem) : (setMem s m).gpr = s.gpr := rfl
/-! ## Instructions on lanes -/

/-- The scratch buffer is writable: a writable region at `x5` holds it (and
may hold more, such as the modes' slots after it). -/
def Room (s : State) : Prop := ∃ n, 8 * scratchSlots ≤ n ∧ (⟨s.gpr .x5, n⟩ : Region) ∈ s.wr

/-- What the scratch buffer contains is writable. -/
theorem Room.wr {s : State} (h : Room s) {a : Addr} {m : Nat} (hc : (scratchR s).Contains a m) :
    InRegions s.wr a m := by
  obtain ⟨n, hn, hm⟩ := h
  exact ⟨_, hm, by simp only [Region.Contains, scratchR] at hc ⊢; omega_using [hc, hn]⟩

theorem Room.rw {s : State} (h : Room s) {a : Addr} {m : Nat} (hc : (scratchR s).Contains a m) :
    InRegions (s.rd ++ s.wr) a m :=
  let ⟨r, hr, hc'⟩ := h.wr hc; ⟨r, List.mem_append_right _ hr, hc'⟩

/-- The scratch buffer is exactly a writable region. -/
theorem Room.of_mem {s : State} (h : scratchR s ∈ s.wr) : Room s := ⟨_, Nat.le_refl _, h⟩

theorem lane_wr {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) :
    InRegions s.wr (laneA s k b) 4 := h.wr (lane_in hk hb s)

theorem lane_rw {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) :
    InRegions (s.rd ++ s.wr) (laneA s k b) 4 := h.rw (lane_in hk hb s)

theorem laneOff_ok {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) :
    laneOff k b % 4 = 0 ∧ laneOff k b < 16384 := by
  have := arrays_bound k hk
  unfold laneOff; omega_using [hb, this]

theorem exec_ldW_lane {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) (d : Reg) :
    exec (ldW d k b) s = some (s.write .w d (lv s k b)) :=
  exec_ldr_w (laneOff_ok hk hb) (lane_rw h hk hb)

theorem exec_stW_lane {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16)
    (r : Reg) : exec (stW k b r) s =
      some (setMem s (s.mem.writeW (laneA s k b) ((s.gpr r).setWidth 32))) :=
  exec_str_w (laneOff_ok hk hb) (lane_wr h hk hb)

theorem exec_eorW (s : State) (d n m : Reg) :
    exec (eorW d n m) s = some (s.write .w d (s.read .w n ^^^ s.read .w m)) := rfl

theorem exec_addW (s : State) (d n m : Reg) :
    exec (addW d n m) s = some (s.write .w d (s.read .w n + s.read .w m)) := rfl

end VG.Proof.Seed.AArch64

end

end

/-!
# The steps of a round, lane by lane

As on x86-64: each step of the round (`step1` … `step4`) on one lane meets
its `LaneSpec` (`LaneOk`); `lanes_ok` then gives it on all sixteen.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Seed.AArch64

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

theorem room_congr {s s' : State} (h : Room s) (hr : s'.gpr .x5 = s.gpr .x5) (hw : s'.wr = s.wr) :
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

/-- The round key's halves are in `x16` and `x17`. -/
def KeysIn (k0 k1 : BitVec 32) (s : State) : Prop :=
  Room s ∧ (s.gpr .x16).setWidth 32 = k0 ∧ (s.gpr .x17).setWidth 32 = k1

theorem step1_ok (k0 k1 : BitVec 32) {b : Nat} (hb : b < 16) (s : State) (h : KeysIn k0 k1 s) :
    ∃ s', runBlock isa (step1 b) s = some s' ∧ LaneOk s s' (sp1 k0 k1) b := by
  obtain ⟨h, hk0, hk1⟩ := h
  rw [step1, runBlock_cons, exec_ldW_lane h mem_R0 hb, runStep_some, runBlock_cons,
    exec_eorW, runStep_some, runBlock_cons, exec_stW_lane ?h1 mem_aA hb, runStep_some,
    runBlock_cons, exec_ldW_lane ?h2 mem_R1 hb, runStep_some, runBlock_cons, exec_eorW, runStep_some,
    runBlock_cons, exec_eorW, runStep_some, runBlock_cons, exec_stW_lane ?h3 mem_tA hb, runStep_some,
    runBlock_nil]
  case h1 | h2 | h3 => exact room_congr h rfl rfl
  refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp only [laneWrites, sp1, List.foldl_cons, List.foldl_nil, State.read, gpr_write,
      reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, gpr_setMem, mem_write, mem_setMem, lv_setMem,
      laneA_setMem, hk0, hk1, Size.bits,
      laneA_write _ _ _ (show ¬ Reg.x5 = .x14 by decide), lv_write _ _ _ (show ¬ Reg.x5 = .x14 by decide),
      laneA_write _ _ _ (show ¬ Reg.x5 = .x15 by decide), lv_write _ _ _ (show ¬ Reg.x5 = .x15 by decide),
      lv_eq]
    rw [readW_writeW_lane mem_R1 hb mem_aA hb (Or.inl (by decide)), lv_eq]
  · simp only [gpr_write, gpr_setMem, h1, h2, ↓reduceIte]

theorem step2_ok {b : Nat} (hb : b < 16) (s : State) (h : Room s) :
    ∃ s', runBlock isa (step2 b) s = some s' ∧ LaneOk s s' sp2 b := by
  rw [step2, runBlock_cons, exec_ldW_lane h mem_tA hb, runStep_some, runBlock_cons,
    exec_stW_lane ?h1 mem_cA hb, runStep_some, runBlock_cons, exec_ldW_lane ?h2 mem_aA hb,
    runStep_some, runBlock_cons, exec_addW, runStep_some, runBlock_cons, exec_stW_lane ?h3 mem_tA hb,
    runStep_some, runBlock_nil]
  case h1 | h2 | h3 => exact room_congr h rfl rfl
  refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp only [laneWrites, sp2, List.foldl_cons, List.foldl_nil, State.read, gpr_write,
      reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, gpr_setMem, mem_write, mem_setMem, lv_setMem,
      laneA_setMem, Size.bits,
      laneA_write _ _ _ (show ¬ Reg.x5 = .x14 by decide), lv_write _ _ _ (show ¬ Reg.x5 = .x14 by decide),
      laneA_write _ _ _ (show ¬ Reg.x5 = .x15 by decide), lv_write _ _ _ (show ¬ Reg.x5 = .x15 by decide),
      lv_eq]
    rw [readW_writeW_lane mem_aA hb mem_cA hb (Or.inl (by decide)), lv_eq]
  · simp only [gpr_write, gpr_setMem, h1, h2, ↓reduceIte]

theorem step3_ok {b : Nat} (hb : b < 16) (s : State) (h : Room s) :
    ∃ s', runBlock isa (step3 b) s = some s' ∧ LaneOk s s' sp3 b := by
  rw [step3, runBlock_cons, exec_ldW_lane h mem_tA hb, runStep_some, runBlock_cons,
    exec_stW_lane ?h1 mem_dA hb, runStep_some, runBlock_cons, exec_ldW_lane ?h2 mem_cA hb,
    runStep_some, runBlock_cons, exec_addW, runStep_some, runBlock_cons, exec_stW_lane ?h3 mem_tA hb,
    runStep_some, runBlock_nil]
  case h1 | h2 | h3 => exact room_congr h rfl rfl
  refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp only [laneWrites, sp3, List.foldl_cons, List.foldl_nil, State.read, gpr_write,
      reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, gpr_setMem, mem_write, mem_setMem, lv_setMem,
      laneA_setMem, Size.bits,
      laneA_write _ _ _ (show ¬ Reg.x5 = .x14 by decide), lv_write _ _ _ (show ¬ Reg.x5 = .x14 by decide),
      laneA_write _ _ _ (show ¬ Reg.x5 = .x15 by decide), lv_write _ _ _ (show ¬ Reg.x5 = .x15 by decide),
      lv_eq]
    rw [readW_writeW_lane mem_cA hb mem_dA hb (Or.inl (by decide)), lv_eq]
  · simp only [gpr_write, gpr_setMem, h1, h2, ↓reduceIte]

theorem step4_ok {b : Nat} (hb : b < 16) (s : State) (h : Room s) :
    ∃ s', runBlock isa (step4 b) s = some s' ∧ LaneOk s s' sp4 b := by
  rw [step4, runBlock_cons, exec_ldW_lane h mem_tA hb, runStep_some, runBlock_cons,
    exec_ldW_lane ?h1 mem_L1 hb, runStep_some, runBlock_cons, exec_eorW, runStep_some,
    runBlock_cons, exec_stW_lane ?h2 mem_L1 hb, runStep_some, runBlock_cons,
    exec_ldW_lane ?h3 mem_dA hb, runStep_some, runBlock_cons, exec_addW, runStep_some,
    runBlock_cons, exec_ldW_lane ?h4 mem_L0 hb, runStep_some, runBlock_cons, exec_eorW, runStep_some,
    runBlock_cons, exec_stW_lane ?h5 mem_L0 hb, runStep_some, runBlock_nil]
  case h1 | h2 | h3 | h4 | h5 => exact room_congr h rfl rfl
  refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp only [laneWrites, sp4, List.foldl_cons, List.foldl_nil, State.read, gpr_write,
      reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, gpr_setMem, mem_write, mem_setMem, lv_setMem,
      laneA_setMem, Size.bits,
      laneA_write _ _ _ (show ¬ Reg.x5 = .x14 by decide), lv_write _ _ _ (show ¬ Reg.x5 = .x14 by decide),
      laneA_write _ _ _ (show ¬ Reg.x5 = .x15 by decide), lv_write _ _ _ (show ¬ Reg.x5 = .x15 by decide),
      lv_eq]
    rw [readW_writeW_lane mem_dA hb mem_L1 hb (Or.inl (by decide)),
      readW_writeW_lane mem_L0 hb mem_L1 hb (Or.inl (by decide)), lv_eq, lv_eq]
  · simp only [gpr_write, gpr_setMem, h1, h2, ↓reduceIte]

end VG.Proof.Seed.AArch64

end

end

/-! ### `Seed.AArch64.Swap`, which only this module used -/

section

/-!
# Lanes and slots; exchanging the halves

A lane is half of a 64-bit slot (`lv_slot`), so `g16`'s words are lanes of
`tSlot 0` (`wordQ_lv`). `swap_ok`: `swapHalves` exchanges the arrays of
`L` (`arrSlot 0`, `arrSlot 1`) with those of `R` (`arrSlot 2`, `arrSlot 3`),
checked by evaluating its moves over named words (`Bitslice.names`).
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Seed.AArch64

theorem lv_slot (s : State) (k b : Nat) :
    lv s k b = ((slotW s (k + b / 2)) >>> (32 * (b % 2))).setWidth 32 := by
  obtain ha : laneA s k b = wordAddr (s.gpr .x5) (k + b / 2) + BitVec.ofNat 64 (4 * (b % 2)) := by
    simp only [laneA, wordAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2; omega_using []
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · rw [lv, ha, h, show wordAddr (s.gpr .x5) (k + b / 2) + BitVec.ofNat 64 (4 * 0) =
      wordAddr (s.gpr .x5) (k + b / 2) by simp, Mem.readW_lo32 (a := wordAddr (s.gpr .x5) (k + b / 2)) (v := slotW s (k + b / 2)) rfl]
    simp
  · rw [lv, ha, h, show 4 * 1 = 4 from rfl, Mem.readW_hi32 (a := wordAddr (s.gpr .x5) (k + b / 2)) (v := slotW s (k + b / 2)) rfl]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi]

theorem wordQ_lv (s : State) (w : Nat) :
    Proof.Seed.wordQ (fun i => slotW s (tSlot i)) w = lv s (tSlot 0) w := by
  rw [lv_slot]; rfl

/-- The slots `swapHalves` moves, and those below them. -/
def swapCfg : Cfg := { base := .x5, slots := 112, ext := .x5, exts := 0 }

def swapEnv : Env Nat := { reg := fun _ => none, slot := fun k => if k < 112 then some k else none }

def swapPost (e : Env Nat) : Bool :=
  (List.range 16).all (fun k => e.slot (80 + k) == some (96 + k) && e.slot (96 + k) == some (80 + k)) &&
    (List.range 80).all fun j => e.slot j == some j

theorem swap_check : check (names 64) swapCfg (fun _ => none) swapHalves swapEnv swapPost = true := by
  decide +kernel

theorem ok_of_room {s : State} (h : Room s) {c : Cfg} (hb : c.base = .x5) (hs : c.slots ≤ 122)
    (he : c.exts = 0) : Ok c s :=
  ⟨fun k hk => h.wr (by
      rw [hb]; exact Offset.contains_base _ (by unfold scratchSlots; omega_using [hs, hk]) (by omega_using [hs, hk])),
    fun k hk => by omega, by omega_using [hs], fun _ _ j hj => by omega⟩

theorem swap_writes (r : Reg) (h1 : r ≠ .x14) (h2 : r ≠ .x15) :
    (swapHalves.all fun i => !clobbers i r) = true := by
  cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | decide

theorem swap_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa swapHalves s = some s' ∧
      (∀ w < 4, ∀ b < 16, lv s' (arrSlot w) b = lv s (arrSlot ((w + 2) % 4)) b) ∧
      (∀ j < 80, slotW s' j = slotW s j) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ (∀ r, r ≠ .x14 → r ≠ .x15 → s'.gpr r = s.gpr r) ∧ Frame [workR s] s.mem s'.mem := by
  obtain hok : Ok swapCfg s := ok_of_room h rfl (by decide) rfl
  obtain hrel : Rel (NameRel (fun k => slotW s k)) swapCfg (fun _ => none) swapEnv s := by
    refine ⟨fun _ _ h => (by cases h), fun k a hk h => ?_, fun _ _ hk => (by cases hk), fun _ _ h => (by cases h)⟩
    simp only [swapEnv, show k < 112 from hk, ite_true, Option.some.injEq] at h
    subst h; rfl
  obtain ⟨e, he, hp⟩ := of_check _ _ _ swap_check
  obtain ⟨s', hs', p⟩ := run (names_sound _) hok hrel he
  simp only [swapPost, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hp
  obtain hsl : ∀ k a, k < 112 → e.slot k = some a → slotW s' k = slotW s a := by
    intro k a hk hka
    exact p.rel.slot k a hk hka
  refine ⟨s', hs', fun w hw b hb => ?_, fun j hj => hsl j j (by omega_using [hj]) (hp.2 j hj), p.rd, p.wr, p.sp,
    fun r h1 h2 => p.other r ?_, ?_⟩
  · rw [lv_slot, lv_slot]
    refine congrArg (fun x : BitVec 64 => (x >>> (32 * (b % 2))).setWidth 32) ?_
    rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_using [hw]) with rfl | rfl | rfl | rfl
    · exact hsl _ _ (by simp [arrSlot]; omega_using [hb]) ((hp.1 (b / 2) (by omega_using [hb])).1)
    · rw [show arrSlot 1 + b / 2 = 80 + (8 + b / 2) by simp [arrSlot]; omega_using [],
        show arrSlot ((1 + 2) % 4) + b / 2 = 96 + (8 + b / 2) by simp [arrSlot]; omega_using []]
      exact hsl _ _ (by omega_using [hb]) ((hp.1 (8 + b / 2) (by omega_using [hb])).1)
    · rw [show arrSlot 2 + b / 2 = 96 + b / 2 by simp [arrSlot],
        show arrSlot ((2 + 2) % 4) + b / 2 = 80 + b / 2 by simp [arrSlot]]
      exact hsl _ _ (by omega_using [hb]) ((hp.1 (b / 2) (by omega_using [hb])).2)
    · rw [show arrSlot 3 + b / 2 = 96 + (8 + b / 2) by simp [arrSlot]; omega_using [],
        show arrSlot ((3 + 2) % 4) + b / 2 = 80 + (8 + b / 2) by simp [arrSlot]; omega_using []]
      exact hsl _ _ (by omega_using [hb]) ((hp.1 (8 + b / 2) (by omega_using [hb])).2)
  · rw [swap_writes r h1 h2]; decide
  · have := p.frame
    refine this.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s, List.mem_singleton_self _, Region.sub_prefix (by simp [swapCfg])⟩

end VG.Proof.Seed.AArch64

end

end


/-!
# A round on AArch64

`g16_lanes` restates `g16_ok` on the lanes of the arrays, and `round_ok`
puts the steps of a round together: on every lane, the round's code does
RFC 4269 §2's round (`Spec.Seed.round`) to the arrays of `L0`, `L1`, `R0`,
`R1`, with the round key at `x0`.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64
open VG.Proof.Aes.AArch64 (layerWrites)

theorem room_ok_gCfg {s : State} (h : Room s) : Ok gCfg s := ok_of_room h rfl (by decide) rfl

/-- `g16` on the lanes: `G` of `G`'s words, the other arrays kept. -/
theorem g16_lanes {s : State} (h : Room s) :
    ∃ s', runBlock isa g16 s = some s' ∧
      (∀ w < 16, lv s' (tSlot 0) w = Spec.Seed.g (lv s (tSlot 0) w)) ∧
      (∀ k ∈ arrays, k ≠ tSlot 0 → ∀ b < 16, lv s' k b = lv s k b) ∧
      Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧ Frame [workR s] s.mem s'.mem := by
  obtain ⟨s', hs', hg, hrd, hwr, hsp, hregs, hfr⟩ := g16_ok (room_ok_gCfg h)
  obtain hr9 : s'.gpr .x5 = s.gpr .x5 := hregs _ (by decide)
  refine ⟨s', hs', fun w hw => ?_, fun k hk hkt b hb => ?_, room_congr h hr9 hwr, hrd, hwr, hsp,
    hregs, ?_⟩
  · rw [← wordQ_lv, ← wordQ_lv]; exact hg w hw
  · have hb' := arrays_bound k hk
    obtain hk56 : 56 ≤ k := by
      simp only [arrays, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hkt | decide
    simp only [lv, laneA, hr9]
    refine hfr.readW (r := ⟨s.gpr .x5 + BitVec.ofNat 64 (8 * k + 4 * b), 4⟩)
      (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base (s.gpr .x5) (d := 8 * k + 4 * b) (n := 4) (k := 8 * 56)
      (by omega_using [hk56]) (by omega_using [hb, hb'])
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
      (∀ r, r ≠ .x14 → r ≠ .x15 → s'.gpr r = s.gpr r) := by
  obtain ⟨s', hs', hP, hv, rest⟩ := lanes_ok hsp hd (P := Room)
    (fun _ s s' hP hok => room_congr hP (hok.regs _ (by decide) (by decide)) hok.wr) hf h 16 (Nat.le_refl _)
  exact ⟨s', hs', hP, fun k hk b hb => by rw [hv k hk b hb, ite_eq_left hb], rest⟩

theorem scratch_of_arrays {s s' : State} (hfr : Frame [arraysR s] s.mem s'.mem) :
    Frame [workR s] s.mem s'.mem :=
  hfr.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s, List.mem_singleton_self _, Offset.sub_base _ (by omega_using [])⟩

/-- The step of the key pointer. -/
def stepW : Spec.Seed.Direction → BitVec 64
  | .encrypt => 8
  | .decrypt => -8

theorem exec_keyNext (d : Spec.Seed.Direction) (s : State) :
    exec (keyNext d) s = some (s.write .x .x0 (s.gpr .x0 + stepW d)) := by
  cases d
  · rw [keyNext, exec_addImm_x (by decide), read_x]; rfl
  · rw [keyNext, exec_subImm_x (by decide), read_x, BitVec.sub_eq_add_neg]; rfl

theorem exec_dec (s : State) (r : Reg) :
    exec (.subImm .x r r 1) s = some (s.write .x r (s.gpr r - 1)) := by
  rw [exec_subImm_x (by decide), read_x]; rfl

theorem runBlock_sp {is : List Instr} {s s' : State} (h : runBlock isa is s = some s') :
    s'.sp = s.sp := by
  induction is generalizing s with
  | nil => cases h; rfl
  | cons i is ih =>
    rw [runBlock_cons] at h
    cases h₁ : exec i s with
    | none => rw [h₁] at h; cases h
    | some s₁ =>
      rw [h₁, runStep_some] at h
      rw [ih h]; exact exec_sp h₁

theorem runBlock_trans {a b : List Instr} {s s' s'' : State} (h1 : runBlock isa a s = some s')
    (h2 : runBlock isa b s' = some s'') : runBlock isa (a ++ b) s = some s'' := by
  rw [runBlock_append, h1, Option.bind_some, h2]

theorem keepRegs : ∀ r ∈ [Reg.x0, .x1, .x2, .x4, .x5],
    r ≠ .x14 ∧ r ≠ .x15 ∧ r ≠ .x16 ∧ r ≠ .x17 := by decide

theorem notG16 : ∀ r ∈ [Reg.x0, .x1, .x2, .x4, .x5], r ∉ layerWrites := by decide

theorem round_ok (d : Spec.Seed.Direction) {s : State} (h : Room s)
    (hk0 : InRegions (s.rd ++ s.wr) (s.gpr .x0) 4)
    (hk1 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 4) 4) :
    ∃ s', runBlock isa (round d) s = some s' ∧
      (∀ b < 16, quad s' b =
        Spec.Seed.round (s.mem.readW (s.gpr .x0) 32, s.mem.readW (s.gpr .x0 + 4) 32) (quad s b)) ∧
      Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.gpr .x0 = s.gpr .x0 + stepW d ∧ s'.gpr .x4 = s.gpr .x4 - 1 ∧
      s'.gpr .x1 = s.gpr .x1 ∧ s'.gpr .x2 = s.gpr .x2 ∧ s'.gpr .x5 = s.gpr .x5 ∧
      Frame [workR s] s.mem s'.mem := by
  let K0 := s.mem.readW (s.gpr .x0) 32
  let K1 := s.mem.readW (s.gpr .x0 + 4) 32
  -- The round key.
  obtain e1 : exec (.ldr .w .x16 .x0 0) s = some (s.write .w .x16 K0) := by
    rw [exec_ldr_w (by decide) (by simpa using hk0)]; simp [K0]
  obtain e2 : exec (.ldr .w .x17 .x0 4) (s.write .w .x16 K0) =
      some ((s.write .w .x16 K0).write .w .x17 K1) := by
    rw [exec_ldr_w (by decide) (by rw [rd_write, wr_write, gpr_write_of_ne _ _ _ (by decide)]; exact hk1)]
    rw [gpr_write_of_ne _ _ _ (by decide), mem_write]; rfl
  let s2 := (s.write .w .x16 K0).write .w .x17 K1
  obtain hrun2 : runBlock isa [.ldr .w .x16 .x0 0, .ldr .w .x17 .x0 4] s = some s2 := by
    rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_nil]
  obtain hkeys : KeysIn K0 K1 s2 := by
    refine ⟨room_congr h rfl rfl, ?_, ?_⟩ <;>
      simp [s2, gpr_write]
  obtain lv2 : ∀ k b, lv s2 k b = lv s k b := fun k b => by
    simp only [s2, lv_write _ _ _ (show ¬ Reg.x5 = .x17 by decide),
      lv_write _ _ _ (show ¬ Reg.x5 = .x16 by decide)]
  obtain g2 : ∀ r, r ≠ .x16 → r ≠ .x17 → s2.gpr r = s.gpr r := fun r h1 h2 => by
    simp [s2, gpr_write, h1, h2]
  -- The steps.
  obtain ⟨s3, hs3, hP3, hv3, fr3, rd3, wr3, rg3⟩ := lanes_ok (dests1 K0 K1) (reads1 K0 K1)
    (P := KeysIn K0 K1)
    (fun _ s s' hP hok => ⟨room_congr hP.1 (hok.regs _ (by decide) (by decide)) hok.wr,
      by rw [hok.regs _ (by decide) (by decide)]; exact hP.2.1,
      by rw [hok.regs _ (by decide) (by decide)]; exact hP.2.2⟩)
    (fun b hb s hs => step1_ok K0 K1 hb s hs) hkeys 16 (Nat.le_refl _)
  obtain ⟨s4, hs4, hg4, hk4, h4, rd4, wr4, spp4, rg4, fr4⟩ := g16_lanes hP3.1
  obtain ⟨s5, hs5, h5, hv5, fr5, rd5, wr5, rg5⟩ := lanes16_room dests2 reads2 (fun b hb s hs => step2_ok hb s hs) h4
  obtain ⟨s6, hs6, hg6, hk6, h6, rd6, wr6, spp6, rg6, fr6⟩ := g16_lanes h5
  obtain ⟨s7, hs7, h7, hv7, fr7, rd7, wr7, rg7⟩ := lanes16_room dests3 reads3 (fun b hb s hs => step3_ok hb s hs) h6
  obtain ⟨s8, hs8, hg8, hk8, h8, rd8, wr8, spp8, rg8, fr8⟩ := g16_lanes h7
  obtain ⟨s9, hs9, h9, hv9, fr9, rd9, wr9, rg9⟩ := lanes16_room dests4 reads4 (fun b hb s hs => step4_ok hb s hs) h8
  obtain ⟨s10, hs10, hsw, hlow, rd10, wr10, spp10, rg10, fr10⟩ := swap_ok h9
  let s11 := s10.write .x .x0 (s10.gpr .x0 + stepW d)
  let s12 := s11.write .x .x4 (s11.gpr .x4 - 1)
  obtain hrun : runBlock isa [keyNext d, .subImm .x .x4 .x4 1] s10 = some s12 := by
    rw [runBlock_cons, exec_keyNext, runStep_some, runBlock_cons, exec_dec, runStep_some, runBlock_nil]
  -- Registers through the steps.
  obtain keep : ∀ r ∈ [Reg.x0, .x1, .x2, .x4, .x5], s10.gpr r = s.gpr r := by
    intro r hr
    obtain hg := notG16 r hr
    obtain ⟨h1, h2, h3, h4⟩ := keepRegs r hr
    rw [rg10 r h1 h2, rg9 r h1 h2, rg8 r hg, rg7 r h1 h2, rg6 r hg, rg5 r h1 h2, rg4 r hg,
      rg3 r h1 h2, g2 r h3 h4]
  obtain r9_10 : s10.gpr .x5 = s.gpr .x5 := keep _ (by decide)
  obtain g12 : ∀ r, r ≠ .x0 → r ≠ .x4 → s12.gpr r = s10.gpr r := fun r a b => by
    simp [s12, s11, gpr_write, a, b]
  obtain r9_12 : s12.gpr .x5 = s.gpr .x5 := by rw [g12 _ (by decide) (by decide), r9_10]
  obtain lv12 : ∀ k b, lv s12 k b = lv s10 k b := fun k b => by
    simp only [lv, laneA, s12, s11, mem_write, r9_12, r9_10]
  refine ⟨s12, ?_, fun b hb => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · exact room_congr h r9_12 (by simp only [s12, s11, wr_write, wr10, wr9, wr8, wr7, wr6, wr5, wr4, wr3]; rfl)
  · simp only [s12, s11, rd_write, rd10, rd9, rd8, rd7, rd6, rd5, rd4, rd3]; rfl
  · simp only [s12, s11, wr_write, wr10, wr9, wr8, wr7, wr6, wr5, wr4, wr3]; rfl
  · simp only [s12, s11, sp_write, spp10]
    rw [runBlock_sp hs9, spp8, runBlock_sp hs7, spp6, runBlock_sp hs5, spp4, runBlock_sp hs3,
      runBlock_sp hrun2]
  · simp [s12, s11, gpr_write, keep _ (show Reg.x0 ∈ [Reg.x0, .x1, .x2, .x4, .x5] by decide)]
  · simp [s12, s11, gpr_write, keep _ (show Reg.x4 ∈ [Reg.x0, .x1, .x2, .x4, .x5] by decide)]
  · rw [g12 _ (by decide) (by decide), keep _ (by decide)]
  · rw [g12 _ (by decide) (by decide), keep _ (by decide)]
  · exact r9_12
  · -- The frames, all in the scratch buffer.
    obtain fc : ∀ {t : State} {m m' : Mem}, t.gpr .x5 = s.gpr .x5 → Frame [workR t] m m' →
        Frame [workR s] m m' := fun ht hf => by simpa [workR, ht] using hf
    simp only [s12, s11, mem_write]
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

end VG.Proof.Seed.AArch64
