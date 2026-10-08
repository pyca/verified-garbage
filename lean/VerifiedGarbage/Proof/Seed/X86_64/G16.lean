import VerifiedGarbage.Impl.Seed.X86_64.G16
import VerifiedGarbage.Proof.Seed.G16
import VerifiedGarbage.Proof.Framework.X86_64.Linear
import VerifiedGarbage.Proof.Aes.X86_64.Encrypt

/-!
# `g16` on x86-64

`g16_ok`: `g16` replaces each of the sixteen words in `tSlot 0 … tSlot 7`
with `G` of it, when the masks are in their slots (`MasksIn`), and keeps
them there. Its linear layers are checked by evaluation over the lane
domain (`g16In_check`, `g16Out_check`: the planes of `M`, and the words from
the S-box's planes, as `Proof/Seed/G16.lean` states them), the S-box by
AES's proof (`Proof.Aes.X86_64.sbox_ok`), and `g16_words` puts them together.
-/

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Seed VG.Impl.Seed.X86_64
open VG.Impl.Aes.X86_64 (q t0 t1 sb sboxCode)
open VG.Proof.Seed (l1 l2 wordQ g16_words)

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

theorem g16Out_check : check (lanes 64 9) gCfg (fun _ => none) g16Out env2 post2 = true := by
  decide +kernel

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
      have := inWord_rel In (i := k - 61) (k := 9) (by omega)
      simpa [In, slotW, tSlot, show 61 + (k - 61) = k by omega, gCfg] using this
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
    ⟨fun k hk => p1.ok.slotIn k (by simp [Proof.Aes.X86_64.sboxCfg, gCfg] at hk ⊢; omega),
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
      (by omega) (by omega)
  -- The output layer.
  have hok2 : Ok gCfg s2 := p1.ok.congr hsb2 hsb2 rd2 wr2
  have hrel2 : Rel (LaneRel 9 (assign S (2 ^ 9))) gCfg (fun _ => none) env2 s2 := by
    refine ⟨fun r a h => ?_, fun k a _ h => masks_rel hm2 h, fun _ _ hk => (by cases hk)⟩
    simp only [env2, Option.map_eq_some_iff] at h
    obtain ⟨j, hf, rfl⟩ := h
    have hr : q j = r := by simpa using List.find?_some hf
    have hj := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    subst hr
    exact inWord_rel S (k := 9) (by omega)
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
      p2.rel.slot _ _ (by simp [tSlot, gCfg]; omega) hi'.1
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
      exact Region.sub_prefix (by omega)
    · have := p2.frame
      simp only [slotRegion] at this ⊢
      rw [show s2.gpr gCfg.base = s.gpr gCfg.base from hb2] at this
      exact this

end VG.Proof.Seed.X86_64
