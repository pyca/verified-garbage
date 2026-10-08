import VerifiedGarbage.Impl.Seed.AArch64.G16
import VerifiedGarbage.Proof.Seed.G16
import VerifiedGarbage.Proof.Framework.AArch64.Linear
import VerifiedGarbage.Proof.Aes.AArch64.Encrypt

/-!
# `g16` on AArch64

`g16_ok`: `g16` replaces each of the sixteen words in `tSlot 0 … tSlot 7`
with `G` of it. Its linear layers, which build their masks with `movz` and
`movk`, are checked by evaluation over the lane domain (`g16In_check`,
`g16Out_check`: the planes of `M`, and the words from the S-box's planes, as
`Proof/Seed/G16.lean` states them), the S-box by AES's proof
(`Proof.Aes.AArch64.sbox_ok`), and `g16_words` puts them together.
-/

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Seed VG.Impl.Seed.AArch64
open VG.Impl.Aes.AArch64 (q t0 t1 sb sboxCode)
open VG.Proof.Seed (l1 l2 wordQ g16_words)
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

theorem g16Out_check : check (lanes 64 9) gCfg (fun _ => none) g16Out env2 post2 = true := by
  decide +kernel

/-! ## Relating the checks to the machine -/

/-- An output word with the constant bits `c`. -/
theorem outWordC_rel {k : Nat} {W : Nat → BitVec 64} {g : Nat → List Nat} {c : Nat} {x : BitVec 64}
    (hg : ∀ p < 64, ∀ a ∈ g p, a < 2 ^ k) (h : LaneRel k (assign W (2 ^ k)) (c, mk 64 g 64) x) :
    ∀ p < 64, x.getLsbD p = (c.testBit p ^^ xorBits W (g p)) := by
  intro p hp
  rw [h.2 p hp, par_mk hp (Nat.le_refl _) _ (fun q hq => hg q hq), xorA_assign W (hg p hp)]
  simp [hp]

theorem g16_keeps : layerKeep.all (fun r => g16.all fun i => dstOf i != some r) = true := by
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
    ((a ++ b).all fun i => dstOf i != some r) =
      ((a.all fun i => dstOf i != some r) && (b.all fun i => dstOf i != some r)) := List.all_append

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
      have := inWord_rel In (i := k - 48) (k := 9) (by omega)
      simpa [In, slotW, tSlot, show 48 + (k - 48) = k by omega, gCfg] using this
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
    ⟨fun k hk => p1.ok.slotIn k (by simp [Proof.Aes.AArch64.sboxCfg, gCfg] at hk ⊢; omega),
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
    exact inWord_rel S (k := 9) (by omega)
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
      have := p2.rel.slot _ _ (by simp [tSlot, gCfg]; omega) hi'.1
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
      exact Region.sub_prefix (by omega)
    · have := p2.frame
      simp only [slotRegion] at this ⊢
      rw [show s2.gpr gCfg.base = s.gpr gCfg.base from hb2] at this
      exact this

end VG.Proof.Seed.AArch64
