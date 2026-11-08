module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Spills
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.RoundLit
public import VerifiedGarbage.Proof.Framework.PPC64LE.Linear
public import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.TripleDes.Pieces
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# The round on PPC64LE

`feistel` is checked in three parts by evaluation, as on RISC-V
(`Proof/TripleDes/RISCV64/Feistel.lean`). Its first part (`feistelIn`) and
its last (`feistelOut`) are linear (the lane domain,
`Framework/PPC64LE/Linear.lean`, here with the words of constants as
constants, `kExt`): the first forms each lane's six input bits, bits of R
and of the round key, in `m 0`–`m 5`; the last XORs each output bit into L
at its destination under P. The middle part (`feistelTree`) is checked over
the position-table domain (`Framework/Bitslice/PosTable.lean`), on all 64
inputs of every lane at once: each lane's result is its table
(`laneTables`). The words of constants are external words of the scratch
buffer. `feistel_ok` composes them, and `roundBody_ok` adds the half swap.
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Bitslice VG.Impl.TripleDes.PPC64LE
open VG.Proof.TripleDes (inputTable roundChunk roundChunk_bit)

/-! ## Linear blocks with constant external words -/

/-- External word `j` is the constant `v` for each `(j, v)` of `ks`. -/
def kExt (ks : List (Nat × BitVec 64)) (j : Nat) : Option (Nat × Nat) :=
  (ks.find? (·.1 == j)).map fun p => (p.2.toNat, 0)

/-- A linear block that the evaluator accepts, on the machine, with any
external words. -/
theorem linearK_ok {k : Nat} {c : Cfg} {is : List Instr} {ins : List (Reg × Nat)}
    {ext : Nat → Option (Nat × Nat)} {outs : List (Reg × (Nat → List Nat))}
    (hchk : check (lanes 64 k) c ext is (linEnv ins) (linPost k outs) = true)
    {s : State} (hok : Ok c s) (W : Nat → BitVec 64)
    (hin : ∀ r i, (r, i) ∈ ins → 64 * i + 64 ≤ 2 ^ k ∧ W i = s.gpr r)
    (hext : ∀ j a, j < c.exts → ext j = some a →
      LaneRel k (assign W (2 ^ k)) a (s.mem.readW (wordAddr (s.gpr c.ext) j) 64)) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ r g, (r, g) ∈ outs → ∀ p < 64, (s'.gpr r).getLsbD p = xorBits W (g p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, (is.all fun i => dstOf i != some r) = true → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion c s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  have hrel : Rel (LaneRel k (assign W (2 ^ k))) c ext (linEnv ins) s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), hext, fun _ _ h => by cases h⟩
    simp only [linEnv, Option.map_eq_some_iff] at h
    obtain ⟨⟨r', i⟩, hf, rfl⟩ := h
    have hr : r' = r := by simpa using List.find?_some hf
    subst hr
    obtain ⟨h1, h2⟩ := hin r' i (List.mem_of_find?_eq_some hf)
    rw [← h2]; exact inWord_rel W h1
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  refine ⟨s', hs', fun r g hrg q hq => ?_, p.rd, p.wr, fun r hr => p.other r (by simp [hr]), p.frame⟩
  obtain ⟨h1, h2⟩ := outOkW_spec (List.all_eq_true.mp hpost (r, g) hrg)
  exact outWord_rel_of_lt h2 (p.rel.reg r _ h1) q hq

/-- External words that are constants. -/
theorem kExt_rel {k : Nat} {c : Cfg} {s : State} {W : Nat → BitVec 64} {ks : List (Nat × BitVec 64)}
    (hks : ∀ j v, (j, v) ∈ ks → s.mem.readW (wordAddr (s.gpr c.ext) j) 64 = v) :
    ∀ j a, j < c.exts → kExt ks j = some a →
      LaneRel k (assign W (2 ^ k)) a (s.mem.readW (wordAddr (s.gpr c.ext) j) 64) := by
  intro j a _ h
  simp only [kExt, Option.map_eq_some_iff] at h
  obtain ⟨⟨j', v⟩, hf, rfl⟩ := h
  have hj' : j' = j := by simpa using List.find?_some hf
  subst hj'
  rw [hks j' v (List.mem_of_find?_eq_some hf)]
  refine ⟨v.isLt, fun q _ => ?_⟩
  simp [par_zero, BitVec.testBit_toNat]

/-! ## The three checks -/

/-- The scratch buffer's first 62 words, read only: slots 15–61 hold the constants. -/
def feiCfg : Cfg := { base := .r5, slots := 0, ext := .r5, exts := 15 + 47 }

/-- External word `15 + c` is the constant `c`. -/
def constKs : List (Nat × BitVec 64) := (List.range 47).map fun c => (15 + c, roundConsts.getD c 0)

/-- R (input word 0) and the round key (input word 1). -/
def inRegs : List (Reg × Nat) := [(.r15, 0), (t4, 1)]

/-- Lane `p`'s input bit `k`: bits of R and of the round key, by E. -/
def maskBits (k p : Nat) : List Nat :=
  let n := 6 * (7 - p / 8) + 5 - k
  [32 - Spec.TripleDes.expansion.getD n 1, 64 + (47 - n)]

def maskOuts : List (Reg × (Nat → List Nat)) := (List.range 6).map fun k => (m k, maskBits k)

theorem feistelIn_check :
    check (lanes 64 7) feiCfg (kExt constKs) (instrs feistelIn.lit) (linEnv inRegs)
      (linPost 7 maskOuts) = true := by
  lit_decide

/-- The lanes' tables (input word 0) and L (input word 1). -/
def outRegs : List (Reg × Nat) := [(t0, 0), (.r14, 1)]

/-- The low lane of the output that P moves to bit `q < 32` of L. -/
def pSrc (q : Nat) : Nat :=
  let t := 32 - Spec.TripleDes.p.getD (31 - q) 1
  8 * (t / 4) + outLane (t / 4) (t % 4)

def outBits (q : Nat) : List Nat := [64 + q] ++ (if q < 32 then [pSrc q, pSrc q + 4] else [])

theorem feistelOut_check :
    check (lanes 64 7) feiCfg (kExt constKs) (instrs feistelOut.lit) (linEnv outRegs)
      (linPost 7 [(.r14, outBits)]) = true := by
  lit_decide

/-- The input bits, the same table at every position. -/
def treeEnv : Env Nat :=
  { reg := fun r => ((List.range 6).find? (fun k => m k == r)).map
      fun k => everywhere 64 64 (inputTable k),
    slot := fun _ => none }

def treeExt (j : Nat) : Option Nat :=
  if 15 ≤ j then some (spreadConst 64 64 (roundConsts.getD (j - 15) 0).toNat) else none

def treePost (e : Env Nat) : Bool := e.reg t0 == some laneTables

theorem feistelTree_check :
    check (posTables 64 64) feiCfg treeExt (instrs feistelTree.lit) treeEnv treePost = true := by
  lit_decide

/-! ## The three parts on the machine -/

theorem feiCfg_ok {s : State} (h : Ok scratchCfg s) : Ok feiCfg s where
  slotIn k hk := by simp [feiCfg] at hk
  extIn k hk := by
    obtain ⟨r, hr, hc⟩ := h.slotIn k (by simp only [feiCfg] at hk; simp only [scratchCfg]; omega)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  slots := by decide
  sep k hk := by simp [feiCfg] at hk

theorem constKs_rel {s : State} (h : ConstsAt s) :
    ∀ j v, (j, v) ∈ constKs → s.mem.readW (wordAddr (s.gpr feiCfg.ext) j) 64 = v := by
  intro j v hm
  simp only [constKs, List.mem_map, List.mem_range, Prod.mk.injEq] at hm
  obtain ⟨c, hc, rfl, rfl⟩ := hm
  exact h c hc

theorem mem_of_frame_fei {s s' : State} (h : Frame [slotRegion feiCfg s] s.mem s'.mem) :
    s'.mem = s.mem := by
  funext a
  apply h a
  intro r hr hc
  simp only [slotRegion, feiCfg, List.mem_singleton] at hr
  subst r
  simp [Region.Contains] at hc

/-- What the parts need: the scratch buffer, with the constants. -/
structure FeiReady (s : State) : Prop where
  ok : Ok scratchCfg s
  consts : ConstsAt s

theorem FeiReady.congr {s t : State} (h : FeiReady s) (hb : t.gpr .r5 = s.gpr .r5)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hm : t.mem = s.mem) : FeiReady t :=
  ⟨h.ok.congr hb hb hrd hwr, h.consts.congr hb hm⟩

/-- R and the round key, as input words. -/
def inWords (s : State) (i : Nat) : BitVec 64 := if i = 0 then s.gpr .r15 else s.gpr t4

theorem feistelIn_ok (s : State) (h : FeiReady s) :
    ∃ s', runBlock isa (ePart ++ kPart ++ maskPart) s = some s' ∧
      (∀ k < 6, ∀ p < 64, (s'.gpr (m k)).getLsbD p = xorBits (inWords s) (maskBits k p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((ePart ++ kPart ++ maskPart).all fun i => dstOf i != some r) = true →
        s'.gpr r = s.gpr r) := by
  have hchk := feistelIn_check
  rw [← feistelIn.lit_eq] at hchk
  obtain ⟨s', hs', out, rd, wr, keep, frame⟩ := linearK_ok hchk (feiCfg_ok h.ok) (inWords s)
    (fun r i hri => by
      simp only [inRegs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (kExt_rel (constKs_rel h.consts))
  exact ⟨s', hs', fun k hk p hp => out (m k) (maskBits k)
    (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩) p hp, rd, wr,
    mem_of_frame_fei frame, keep⟩

/-- Lane `p`'s six input bits. -/
def laneInput (s : State) (p : Nat) : BitVec 6 := ofBits 6 fun k => (s.gpr (m k)).getLsbD p

theorem testBit_laneTables {p c : Nat} (hp : p < 64) (hc : c < 64) :
    laneTables.testBit (64 * p + c) = laneBit p c := by
  rw [laneTables, testBit_blocks (fun p => tableOf_lt _ 64) 64 p c hc, testBit_tableOf]
  simp [hp, hc]

theorem feistelTree_ok (s : State) (h : FeiReady s) :
    ∃ s', runBlock isa treePart s = some s' ∧
      (∀ p < 64, (s'.gpr t0).getLsbD p = laneBit p (laneInput s p).toNat) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, (treePart.all fun i => dstOf i != some r) = true → s'.gpr r = s.gpr r) := by
  have hchk := feistelTree_check
  rw [← feistelTree.lit_eq] at hchk
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  let cs : Nat → Nat := fun p => (laneInput s p).toNat
  have hcs : ∀ p < 64, cs p < 64 := fun p _ => (laneInput s p).isLt
  have hrel : Rel (PosRel 64 cs) feiCfg treeExt treeEnv s := by
    refine ⟨fun r a hr => ?_, fun _ _ hk _ => by simp [feiCfg] at hk, fun j a hj hja => ?_,
      fun _ _ h => by cases h⟩
    · simp only [treeEnv, Option.map_eq_some_iff] at hr
      obtain ⟨k, hk, rfl⟩ := hr
      have hqr := List.find?_some hk
      have hk6 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
      simp only [beq_iff_eq] at hqr
      subst hqr
      intro p hp
      have hc : (ofBits 6 fun k => (s.gpr (m k)).getLsbD p).toNat < 64 := BitVec.isLt _
      rw [inputTable, testBit_everywhere (tableOf_lt _ 64) hp (hcs p hp), testBit_tableOf]
      simp only [cs, laneInput, hc, decide_true, Bool.true_and, BitVec.testBit_toNat,
        getLsbD_ofBits, hk6]
    · simp only [treeExt] at hja
      split at hja
      · cases hja
        intro p hp
        have hc : j - 15 < 47 := by simp only [feiCfg] at hj; omega
        have hw := h.consts (j - 15) hc
        rw [show 15 + (j - 15) = j by omega] at hw
        rw [testBit_spreadConst hp (hcs p hp), BitVec.testBit_toNat]
        exact congrArg (fun x : BitVec 64 => x.getLsbD p) hw.symm
      · cases hja
  obtain ⟨s', hs', p₀⟩ := run (posTables_sound hcs) (feiCfg_ok h.ok) hrel he
  have hout : e'.reg t0 = some laneTables := by
    simpa only [treePost, beq_iff_eq] using hpost
  refine ⟨s', hs', fun p hp => ?_, p₀.rd, p₀.wr, mem_of_frame_fei p₀.frame,
    fun r hr => p₀.other r (by
      intro hw
      rw [show instrs (Code.block treePart) = treePart from rfl, hr] at hw
      cases hw)⟩
  have hb := p₀.rel.reg t0 _ hout p hp
  rw [← hb, testBit_laneTables hp (hcs p hp)]

/-- The lanes' tables and L, as input words. -/
def outWords (s : State) (i : Nat) : BitVec 64 := if i = 0 then s.gpr t0 else s.gpr .r14

theorem feistelOut_ok (s : State) (h : FeiReady s) :
    ∃ s', runBlock isa pPart s = some s' ∧
      (∀ q < 64, (s'.gpr .r14).getLsbD q = xorBits (outWords s) (outBits q)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, (pPart.all fun i => dstOf i != some r) = true → s'.gpr r = s.gpr r) := by
  have hchk := feistelOut_check
  rw [← feistelOut.lit_eq] at hchk
  obtain ⟨s', hs', out, rd, wr, keep, frame⟩ := linearK_ok hchk (feiCfg_ok h.ok) (outWords s)
    (fun r i hri => by
      simp only [outRegs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (kExt_rel (constKs_rel h.consts))
  exact ⟨s', hs', fun q hq => out .r14 outBits (by simp) q hq, rd, wr,
    mem_of_frame_fei frame, keep⟩

/-! ## The round function -/

theorem bitOf_lo (W : Nat → BitVec 64) {a : Nat} (ha : a < 64) : bitOf W a = (W 0).getLsbD a := by
  simp only [bitOf, Nat.div_eq_of_lt ha, Nat.mod_eq_of_lt ha]

theorem bitOf_hi (W : Nat → BitVec 64) {a : Nat} (ha : a < 64) :
    bitOf W (64 + a) = (W 1).getLsbD a := by
  have hd : (64 + a) / 64 = 1 := by omega
  simp only [bitOf, hd, Nat.add_mod_left, Nat.mod_eq_of_lt ha]

theorem maskBits_bounds : ∀ p < 64, ∀ k < 6,
    32 - Spec.TripleDes.expansion.getD (6 * (7 - p / 8) + 5 - k) 1 < 64 ∧
    47 - (6 * (7 - p / 8) + 5 - k) < 64 := by
  intro p _ k _; omega

/-- Each lane's input bits are its S-box's six bits of E of R XORed with
the round key. -/
theorem laneInput_eq {s s' : State}
    (hm : ∀ k < 6, ∀ p < 64, (s'.gpr (m k)).getLsbD p = xorBits (inWords s) (maskBits k p))
    (p : Nat) (hp : p < 64) :
    laneInput s' p = roundChunk (7 - p / 8) ((s.gpr .r15).setWidth 32) ((s.gpr t4).setWidth 48) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [laneInput, getLsbD_ofBits, roundChunk_bit (7 - p / 8) k (by omega) hk, hm k hk p hp]
  obtain ⟨h1, h2⟩ := maskBits_bounds p hp k hk
  simp only [hk, decide_true, Bool.true_and, maskBits, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_lo _ h1, bitOf_hi _ h2, inWords, ite_true, show (1 : Nat) ≠ 0 by decide, ite_false]

/-- The two lanes of an output, in the two halves of its byte, XOR to the
output on every input. -/
theorem lane_pair (b l x : Nat) (hl : l < 4) (hx : x < 64) :
    (laneBit (8 * b + l) x ^^ laneBit (8 * b + l + 4) x) =
      (Spec.TripleDes.sBox (7 - b) (BitVec.ofNat 6 x)).getLsbD (laneOut b l) := by
  have h1 : (8 * b + l) / 8 = b := by omega
  have h2 : (8 * b + l) % 8 = l := by omega
  have h3 : (8 * b + l + 4) / 8 = b := by omega
  have h4 : (8 * b + l + 4) % 8 = l + 4 := by omega
  have h5 : laneOut b (l + 4) = laneOut b l := by
    simp only [laneOut, show (l + 4) % 4 = l % 4 by omega]
  simp only [laneBit, h1, h2, h3, h4, h5, show l / 4 = 0 by omega, show (l + 4) / 4 = 1 by omega]
  rcases (show x / 32 = 0 ∨ x / 32 = 1 by omega) with hx' | hx' <;> simp [hx']

theorem pSrc_shape : ∀ q < 32,
    let t := 32 - Spec.TripleDes.p.getD (31 - q) 1
    t / 4 < 8 ∧ outLane (t / 4) (t % 4) < 4 ∧ laneOut (t / 4) (outLane (t / 4) (t % 4)) = t % 4 := by
  decide +kernel

/-- The registers the round function keeps. -/
def feistelKept : List Reg :=
  [.r2, .r3, .r4, .r5, .r15, .r16, .r17, .r18, .r19, .r26, .r27, .r28, .r29, .r30, .r31]

theorem feistelIn_keeps : (.r14 :: feistelKept).all
    (fun r => (instrs feistelIn.lit).all fun i => dstOf i != some r) = true := by
  decide +kernel

theorem feistelTree_keeps : (.r14 :: feistelKept).all
    (fun r => (instrs feistelTree.lit).all fun i => dstOf i != some r) = true := by
  decide +kernel

theorem feistelOut_keeps : feistelKept.all
    (fun r => (instrs feistelOut.lit).all fun i => dstOf i != some r) = true := by
  decide +kernel

theorem feistelIn_keep {r : Reg} (hr : r ∈ .r14 :: feistelKept) :
    ((ePart ++ kPart ++ maskPart).all fun i => dstOf i != some r) = true := by
  have h := List.all_eq_true.mp feistelIn_keeps r hr
  rw [← feistelIn.lit_eq] at h
  exact h

theorem feistelTree_keep {r : Reg} (hr : r ∈ .r14 :: feistelKept) :
    (treePart.all fun i => dstOf i != some r) = true := by
  have h := List.all_eq_true.mp feistelTree_keeps r hr
  rw [← feistelTree.lit_eq] at h
  exact h

theorem feistelOut_keep {r : Reg} (hr : r ∈ feistelKept) :
    (pPart.all fun i => dstOf i != some r) = true := by
  have h := List.all_eq_true.mp feistelOut_keeps r hr
  rw [← feistelOut.lit_eq] at h
  exact h

/-- The round function: L XORed with the round function of R and the round
key at `r17`. -/
theorem feistel_ok (s : State) (h : FeiReady s) (l r : BitVec 32)
    (hl : s.gpr .r14 = l.setWidth 64) (hr : s.gpr .r15 = r.setWidth 64)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .r17) 8) :
    ∃ s', runBlock isa feistel s = some s' ∧
      s'.gpr .r14 = (l ^^^ Spec.TripleDes.roundFunction r
        ((s.mem.readW (s.gpr .r17) 64).setWidth 48)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ q ∈ feistelKept, s'.gpr q = s.gpr q) := by
  have ha : s.gpr .r17 + BitVec.ofNat 64 0 = s.gpr .r17 := BitVec.add_zero _
  let s₀ := s.write t4 (s.mem.readW (s.gpr .r17) 64)
  have run₀ : runBlock isa keyLoad s = some s₀ := by
    rw [keyLoad, runBlock_cons, exec_load_d (by decide) (by decide) (by rw [ha]; exact hread), ha,
      runStep_some, runBlock_nil]
  have hready₀ : FeiReady s₀ := h.congr (gpr_write_of_ne _ _ (by decide)) rfl rfl rfl
  obtain ⟨s₁, run₁, masks, rd₁, wr₁, mem₁, keep₁⟩ := feistelIn_ok s₀ hready₀
  have hready₁ := hready₀.congr (keep₁ .r5 (feistelIn_keep (by decide))) rd₁ wr₁ mem₁
  obtain ⟨s₂, run₂, tabs, rd₂, wr₂, mem₂, keep₂⟩ := feistelTree_ok s₁ hready₁
  have hready₂ := hready₁.congr (keep₂ .r5 (feistelTree_keep (by decide))) rd₂ wr₂ mem₂
  obtain ⟨s₃, run₃, outs, rd₃, wr₃, mem₃, keep₃⟩ := feistelOut_ok s₂ hready₂
  have hL₂ : s₂.gpr .r14 = l.setWidth 64 := by
    rw [keep₂ .r14 (feistelTree_keep (by decide)), keep₁ .r14 (feistelIn_keep (by decide)),
      gpr_write_of_ne _ _ (by decide), hl]
  have hR₀ : (s₀.gpr .r15).setWidth 32 = r := by
    rw [gpr_write_of_ne _ _ (by decide), hr]; simp
  have hK₀ : s₀.gpr t4 = s.mem.readW (s.gpr .r17) 64 := gpr_write_self _ _ _
  refine ⟨s₃, ?_, ?_, rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁),
    mem₃.trans (mem₂.trans mem₁), fun q hq => ?_⟩
  · rw [feistel, runBoxes_append, runBoxes_append, runBoxes_append, run₀, Option.bind_some,
      run₁, Option.bind_some, run₂, Option.bind_some, run₃]
  · apply BitVec.eq_of_getLsbD_eq
    intro q hq
    rw [outs q hq]
    have hLq : bitOf (outWords s₂) (64 + q) = (l.setWidth 64).getLsbD q := by
      rw [bitOf_hi _ hq]
      simp only [outWords, show (1 : Nat) ≠ 0 by decide, ite_false, hL₂]
    by_cases hq32 : q < 32
    · simp only [outBits, hq32, ite_true, List.cons_append, List.nil_append, xorBits_cons,
        xorBits_nil, Bool.xor_false, hLq]
      simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, hq, decide_true, Bool.true_and]
      rw [VG.Proof.TripleDes.roundFunction_bit _ _ q hq32]
      simp only []
      obtain ⟨hb, hll, hlo⟩ := pSrc_shape q hq32
      have hsrc : pSrc q = 8 * ((32 - Spec.TripleDes.p.getD (31 - q) 1) / 4) +
          outLane ((32 - Spec.TripleDes.p.getD (31 - q) 1) / 4)
            ((32 - Spec.TripleDes.p.getD (31 - q) 1) % 4) := rfl
      generalize 32 - Spec.TripleDes.p.getD (31 - q) 1 = t at hb hll hlo hsrc ⊢
      generalize hb' : t / 4 = b at hb hll hlo hsrc ⊢
      generalize hl' : outLane b (t % 4) = ll at hll hlo hsrc
      have hs64 : pSrc q < 64 := by omega
      have hs64' : pSrc q + 4 < 64 := by omega
      rw [bitOf_lo _ hs64, bitOf_lo _ hs64']
      simp only [outWords, ite_true]
      rw [tabs _ hs64, tabs _ hs64', laneInput_eq masks _ hs64, laneInput_eq masks _ hs64', hsrc,
        show (8 * b + ll + 4) / 8 = b by omega, show (8 * b + ll) / 8 = b by omega,
        lane_pair b ll _ hll (BitVec.isLt _), hlo, hR₀, hK₀, BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
      rfl
    · simp only [outBits, hq32, ite_false, List.append_nil, xorBits_cons, xorBits_nil,
        Bool.xor_false, hLq, BitVec.getLsbD_setWidth, BitVec.getLsbD_xor]
      rw [BitVec.getLsbD_of_ge l q (by omega),
        BitVec.getLsbD_of_ge (Spec.TripleDes.roundFunction _ _) q (by omega)]
      rfl
  · have hA : q ∈ .r14 :: feistelKept := List.mem_cons_of_mem _ hq
    have hne : q ≠ t4 := by revert hq; cases q <;> decide
    rw [keep₃ q (feistelOut_keep hq), keep₂ q (feistelTree_keep hA), keep₁ q (feistelIn_keep hA),
      gpr_write_of_ne _ _ hne]

/-! ## The round -/

/-- The registers the half swap keeps. -/
def roundOuterKept : List Reg := [.r2, .r3, .r4, .r5, .r16, .r17, .r18, .r19, .r29, .r30, .r31]

theorem swapHalves_ok (s : State) :
    ∃ s', runBlock isa swapHalves s = some s' ∧
      s'.gpr .r14 = s.gpr .r15 ∧ s'.gpr .r15 = s.gpr .r14 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ q ∈ roundOuterKept, s'.gpr q = s.gpr q) := by
  let s₁ := s.write .r6 (s.gpr .r14 ||| s.gpr .r14)
  let s₂ := s₁.write .r14 (s₁.gpr .r15 ||| s₁.gpr .r15)
  let s₃ := s₂.write .r15 (s₂.gpr .r6 ||| s₂.gpr .r6)
  refine ⟨s₃, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · rw [swapHalves, rr, rr, rr, runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_logic,
      runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_nil]
  · simp only [s₃, s₂, s₁, gpr_write, BitVec.or_self, reduceCtorEq, ite_true, ite_false]
  · simp only [s₃, s₂, s₁, gpr_write, BitVec.or_self, reduceCtorEq, ite_true, ite_false]
  · intro q hq
    have hne : q ≠ .r6 ∧ q ≠ .r14 ∧ q ≠ .r15 := by revert hq; cases q <;> decide
    simp only [s₃, s₂, s₁, gpr_write, hne.1, hne.2.1, hne.2.2, ite_false]

/-- One full Feistel round: the round function and the half swap. -/
theorem roundBody_ok (s : State) (l r : BitVec 32) (k : BitVec 64)
    (hl : s.gpr .r14 = l.setWidth 64) (hr : s.gpr .r15 = r.setWidth 64)
    (hk : s.mem.readW (s.gpr .r17) 64 = k) (hok : Ok scratchCfg s) (hc : ConstsAt s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .r17) 8) :
    ∃ s', runBlock isa roundBody s = some s' ∧
      s'.gpr .r14 = r.setWidth 64 ∧
      s'.gpr .r15 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ roundOuterKept, s'.gpr q = s.gpr q) ∧
      s'.mem = s.mem := by
  obtain ⟨s₁, run₁, value, rd₁, wr₁, mem₁, keep₁⟩ := feistel_ok s ⟨hok, hc⟩ l r hl hr hread
  obtain ⟨s₂, run₂, left, right, rd₂, wr₂, mem₂, keep₂⟩ := swapHalves_ok s₁
  refine ⟨s₂, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, ?_, mem₂.trans mem₁⟩
  · simp only [roundBody, runBoxes_append, run₁, Option.bind_some, run₂]
  · exact left.trans ((keep₁ .r15 (by decide)).trans hr)
  · rw [right, value, hk]
  · intro q hq
    have hq' : q ∈ feistelKept := by revert hq; cases q <;> decide
    exact (keep₂ q hq).trans (keep₁ q hq')

end VG.Proof.TripleDes.PPC64LE
