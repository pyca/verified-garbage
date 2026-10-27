module

public import VerifiedGarbage.Impl.Seed.RISCV64.G16
public import VerifiedGarbage.Proof.Seed.G16
public import VerifiedGarbage.Proof.Aes.RISCV64.Layers
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `g16` on RISC-V

`g16_ok`: `g16` replaces each of the sixteen words in `tSlot 0 … tSlot 7`
with `G` of it. As on PPC64LE (`Proof/Seed/PPC64LE/G16.lean`): its linear
layers, which read their masks from the words at `kb` (`gKs`), are checked
by evaluation over the lane domain (`g16In_check`, `g16Out_check`: the
planes of `M`, and the words from the S-box's planes, as
`Proof/Seed/G16.lean` states them), the S-box by AES's proof
(`Proof.Aes.RISCV64.sbox_ok`), and `g16_words` puts them together.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Seed VG.Impl.Seed.RISCV64
open VG.Impl.Aes.RISCV64 (q t0 t1 sb sboxCode)
open VG.Proof.Seed (l1 l2 wordQ g16_words)
open VG.Proof.Aes.RISCV64 (sboxWrites)

/-- The memory `g16` uses: the slots it reads and writes (the S-box's and
the words), and the masks it reads. -/
def gCfg : Cfg := { base := sb, slots := 48, ext := kb, exts := 13 }

/-- Slot `k` of the scratch buffer. -/
def slotW (s : State) (k : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr sb) k) 64

/-- The masks are in the words at `kb`. -/
def KsAt (m : Mem) (b : Addr) : Prop := ∀ j v, (j, v) ∈ gKs → m.readW (wordAddr b j) 64 = v

/-! ## The checks -/

/-- The words as atoms (word `i` in `tSlot i`). -/
def env1 : Env (Nat × Nat) :=
  { reg := fun _ => none, slot := fun k => if 40 ≤ k ∧ k < 48 then some (inWord (k - 40)) else none }

def post1 (e : Env (Nat × Nat)) : Bool :=
  (List.range 8).all fun j =>
    word (e.reg (q j)) == some (outWord (l1 j)) && (List.range 64).all fun p => (l1 j p).all (· < 2 ^ 9)

theorem g16In_check : check (lanes 64 9) gCfg (kExt gKs) g16In env1 post1 = true := by
  decide +kernel

/-- The S-box's planes as atoms (plane `j` in `q j`). -/
def env2 : Env (Nat × Nat) :=
  { reg := fun r => ((List.range 8).find? (fun j => q j == r)).map fun j => .v (inWord j),
    slot := fun _ => none }

def post2 (e : Env (Nat × Nat)) : Bool :=
  (List.range 8).all fun i =>
    e.slot (tSlot i) == some (gConst.toNat, mk 64 (l2 i) 64) &&
      (List.range 64).all fun t => (l2 i t).all (· < 2 ^ 9)

theorem g16Out_check : check (lanes 64 9) gCfg (kExt gKs) g16Out env2 post2 = true := by
  decide +kernel

/-! ## Relating the checks to the machine -/

/-- An output word with the constant bits `c`. -/
theorem outWordC_rel {k : Nat} {W : Nat → BitVec 64} {g : Nat → List Nat} {c : Nat} {x : BitVec 64}
    (hg : ∀ p < 64, ∀ a ∈ g p, a < 2 ^ k) (h : LaneRel k (assign W (2 ^ k)) (c, mk 64 g 64) x) :
    ∀ p < 64, x.getLsbD p = (c.testBit p ^^ xorBits W (g p)) := by
  intro p hp
  rw [h.2 p hp, par_mk hp (Nat.le_refl _) _ (fun q hq => hg q hq), xorA_assign W (hg p hp)]
  simp [hp]

/-- The registers `g16` writes: the S-box's. -/
def g16Writes : List Reg := sboxWrites

/-- The registers outside `g16Writes`. -/
def g16Keep : List Reg := [.ra, .a0, .a1, .a2, .a3, .a4, .a5]

theorem not_g16Writes (r : Reg) (hr : r ∉ g16Writes) : r ∈ g16Keep :=
  Proof.Aes.RISCV64.not_sboxWrites r hr

theorem g16_keeps : g16Keep.all (fun r => g16.all fun i => dst i != some r) = true := by
  decide +kernel

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

theorem dst_append (a b : List Instr) (r : Reg) :
    ((a ++ b).all fun i => dst i != some r) =
      ((a.all fun i => dst i != some r) && (b.all fun i => dst i != some r)) := List.all_append

/-- The masks' words lie above the S-box's slots. -/
theorem ks_disjoint (S : Addr) {j : Nat} (hj : j < 13) :
    Region.Disjoint ⟨wordAddr (S + BitVec.ofNat 64 (8 * kSlot)) j, 8⟩ ⟨S, 8 * 40⟩ := by
  simp only [wordAddr]
  rw [Offset.add_add]
  exact Offset.disjoint_base _ (by unfold kSlot; omega) (by unfold kSlot; omega)

/-- A constant word. -/
theorem const_rel {k : Nat} (A : Nat) (v : BitVec 64) : LaneRel k A (v.toNat, 0) v := by
  refine ⟨v.isLt, fun q _ => ?_⟩
  simp [par_zero, BitVec.testBit_toNat]

theorem gKs_lt : ∀ p ∈ gKs, p.1 < 13 := by decide

theorem gKs_ext : ∀ p ∈ gKs, kExt gKs p.1 = some (p.2.toNat, 0) := by decide

theorem ks_rel {W : Nat → BitVec 64} {s : State} (hks : KsAt s.mem (s.gpr kb)) :
    ∀ j a, j < gCfg.exts → kExt gKs j = some a →
      LaneRel 9 (assign W (2 ^ 9)) a (s.mem.readW (wordAddr (s.gpr gCfg.ext) j) 64) :=
  kExt_rel fun j v h => hks j v h

/-- `g16`: `G` of every word. -/
theorem g16_ok {s : State} (hok : Ok gCfg s)
    (hkb : s.gpr kb = s.gpr sb + BitVec.ofNat 64 (8 * kSlot)) (hks : KsAt s.mem (s.gpr kb)) :
    ∃ s', runBlock isa g16 s = some s' ∧
      (∀ w < 16, wordQ (fun i => slotW s' (tSlot i)) w =
        Spec.Seed.g (wordQ (fun i => slotW s (tSlot i)) w)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ∉ g16Writes → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion gCfg s] s.mem s'.mem := by
  let In : Nat → BitVec 64 := fun i => slotW s (tSlot i)
  -- The input layer.
  have hrel1 : Rel (LaneRel 9 (assign In (2 ^ 9))) gCfg (kExt gKs) env1 s := by
    refine ⟨fun r a h => (by cases h), fun k a hk h => ?_, ks_rel hks⟩
    simp only [env1] at h
    split at h
    · rename_i hk'
      simp only [Option.some.injEq] at h; subst h
      have := inWord_rel In (i := k - 40) (k := 9) (by omega)
      simpa [In, slotW, tSlot, show 40 + (k - 40) = k by omega, gCfg] using this
    · cases h
  obtain ⟨e1, he1, hp1⟩ := of_check _ _ _ g16In_check
  obtain ⟨s1, hs1, p1⟩ := run lanes_sound laneRel_fun hok hrel1 he1
  simp only [post1, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hp1
  let Pl : Nat → BitVec 64 := fun j => s1.gpr (q j)
  have h1 : ∀ j < 8, ∀ p < 64, (Pl j).getLsbD p = xorBits In (l1 j p) := by
    intro j hj
    have hj' := hp1 j hj
    simp only [decide_eq_true_eq] at hj'
    cases hr : e1.reg (q j) with
    | none => rw [hr] at hj'; cases hj'.1
    | some v =>
      rw [hr] at hj'
      cases v with
      | v a =>
        simp only [word, Option.some.injEq] at hj'
        obtain ⟨rfl, hb⟩ := hj'
        exact outWord_rel (fun p hp a ha => hb p hp a ha) (p1.rel.reg _ _ hr)
      | shl _ _ => cases hj'.1
      | shr _ _ => cases hj'.1
  -- The S-box.
  have hokS : Ok Proof.Aes.RISCV64.sboxCfg s1 :=
    { slotIn := fun k hk => p1.ok.slotIn k (by simp [Proof.Aes.RISCV64.sboxCfg, gCfg] at hk ⊢; omega)
      extIn := fun _ hk => (by cases hk)
      baseAl := fun _ => p1.ok.baseAl (by decide)
      extAl := fun h => (by cases h)
      slots := by decide
      sep := fun _ _ _ hj => (by cases hj) }
  obtain ⟨s2, hs2, hS, rd2, wr2, sp2, oth2, fr2⟩ := Proof.Aes.RISCV64.sbox_ok hokS
  let S : Nat → BitVec 64 := fun j => s2.gpr (q j)
  have hsb2 : s2.gpr sb = s1.gpr sb := oth2 _ (by decide)
  have hkb2 : s2.gpr kb = s1.gpr kb := oth2 _ (by decide)
  have hb1 : s1.gpr sb = s.gpr sb := p1.base
  have hk1 : s1.gpr kb = s.gpr kb := p1.ext
  -- The masks, still in place.
  have hks1 : KsAt s1.mem (s1.gpr kb) := by
    intro j v hj
    have := p1.rel.ext j _ (gKs_lt _ hj) (gKs_ext _ hj)
    exact laneRel_fun _ _ _ this (const_rel _ v)
  have hks2 : KsAt s2.mem (s2.gpr kb) := by
    intro j v hj
    have hlt : j < 13 := gKs_lt _ hj
    rw [hkb2, fr2.readW (r := ⟨wordAddr (s1.gpr kb) j, 8⟩) (by simp [Region.Contains])
      (fun r hr => ?_) (by decide)]
    · exact hks1 j v hj
    · simp only [List.mem_singleton] at hr; subst hr
      show Region.Disjoint _ ⟨s1.gpr sb, 8 * 40⟩
      rw [hk1, hkb, hb1]
      exact ks_disjoint _ hlt
  -- The output layer.
  have hok2 : Ok gCfg s2 := p1.ok.congr hsb2 hkb2 rd2 wr2
  have hrel2 : Rel (LaneRel 9 (assign S (2 ^ 9))) gCfg (kExt gKs) env2 s2 := by
    refine ⟨fun r a h => ?_, fun k a _ h => (by cases h), ks_rel hks2⟩
    simp only [env2, Option.map_eq_some_iff] at h
    obtain ⟨j, hf, rfl⟩ := h
    have hr : q j = r := by simpa using List.find?_some hf
    have hj := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    subst hr
    exact inWord_rel S (k := 9) (by omega)
  obtain ⟨e2, he2, hp2⟩ := of_check _ _ _ g16Out_check
  obtain ⟨s3, hs3, p2⟩ := run lanes_sound laneRel_fun hok2 hrel2 he2
  simp only [post2, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hp2
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
  · have hk := List.all_eq_true.mp g16_keeps r (not_g16Writes r hr)
    simp only [g16, dst_append, Bool.and_eq_true] at hk
    rw [p2.other r (by simp [hk.2]), oth2 r hr, p1.other r (by simp [hk.1.1])]
  · refine p1.frame.trans (Frame.trans (Frame.sub fr2 ?_) ?_)
    · intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨slotRegion gCfg s, List.mem_singleton_self _, ?_⟩
      show Region.Sub ⟨s1.gpr sb, 8 * 40⟩ ⟨s.gpr sb, 8 * 48⟩
      rw [hb1]
      exact Region.sub_prefix (by omega)
    · have := p2.frame
      simp only [slotRegion] at this ⊢
      rw [show s2.gpr gCfg.base = s.gpr gCfg.base from hb2] at this
      exact this

end VG.Proof.Seed.RISCV64
