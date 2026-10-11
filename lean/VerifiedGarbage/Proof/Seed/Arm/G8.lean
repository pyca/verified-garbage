import VerifiedGarbage.Impl.Seed.Arm.G8
import VerifiedGarbage.Proof.Seed.G8
import VerifiedGarbage.Proof.Framework.Arm.Linear
import VerifiedGarbage.Proof.Aes.Arm.Sbox

/-!
# `g8` on ARMv7

`g8_ok`: `g8` replaces each of the eight words in `tSlot 0 … tSlot 7` with
`G` of it. As on AArch64 (`Proof/Seed/AArch64/G16.lean`): its linear
layers, which build their masks with `movw` and `movt`, are checked by
evaluation over the lane domain (`g8In_check`, `g8Out_check`: the planes of
`M`, and the words from the S-box's planes, as `Proof/Seed/G8.lean` states
them), the S-box by AES's proof (`Proof.Aes.Arm.sbox_ok`), and `g8_words`
puts them together.
-/

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

theorem g8_keeps : layerKeep.all (fun r => g8.all fun i => dstOf i != some r) = true := by
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
    ((a ++ b).all fun i => dstOf i != some r) =
      ((a.all fun i => dstOf i != some r) && (b.all fun i => dstOf i != some r)) := List.all_append

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
      have := inWordW_rel In (w := 32) (i := k - 40) (k := 8) (by omega)
      simpa [In, slotW, tSlot, show 40 + (k - 40) = k by omega, gCfg] using this
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
    ⟨fun k hk => p1.ok.slotIn k (by simp [Proof.Aes.Arm.sboxCfg, gCfg] at hk ⊢; omega),
      fun _ hk => (by cases hk), by have := p1.ok.slots; simp [Proof.Aes.Arm.sboxCfg, gCfg] at this ⊢; omega,
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
    exact inWordW_rel S (w := 32) (k := 8) (by omega)
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
      have := p2.rel.slot _ _ (by simp [tSlot, gCfg]; omega) hi'.1
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
      exact Region.sub_prefix (by omega)
    · have := p2.frame
      simp only [slotRegion] at this ⊢
      rw [show s2.gpr gCfg.base = s.gpr gCfg.base from hb2] at this
      exact this

end VG.Proof.Seed.Arm
