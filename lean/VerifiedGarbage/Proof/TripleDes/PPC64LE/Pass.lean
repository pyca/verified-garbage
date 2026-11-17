module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Spills
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Block
public import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.RoundLit
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.PPC64LE.Linear
public import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.TripleDes.Pieces
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `TripleDes.PPC64LE.RoundBody`, which only this module used -/

section

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
    obtain ⟨r, hr, hc⟩ := h.slotIn k (by simp only [feiCfg] at hk; simp only [scratchCfg]; omega_using [hk])
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
        have hc : j - 15 < 47 := by simp only [feiCfg] at hj; omega_using [hj]
        have hw := h.consts (j - 15) hc
        rw [show 15 + (j - 15) = j by omega_arith] at hw
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
  have hd : (64 + a) / 64 = 1 := by omega_using [ha]
  simp only [bitOf, hd, Nat.add_mod_left, Nat.mod_eq_of_lt ha]

theorem maskBits_bounds : ∀ p < 64, ∀ k < 6,
    32 - Spec.TripleDes.expansion.getD (6 * (7 - p / 8) + 5 - k) 1 < 64 ∧
    47 - (6 * (7 - p / 8) + 5 - k) < 64 := by
  intro p _ k _; omega_using []

/-- Each lane's input bits are its S-box's six bits of E of R XORed with
the round key. -/
theorem laneInput_eq {s s' : State}
    (hm : ∀ k < 6, ∀ p < 64, (s'.gpr (m k)).getLsbD p = xorBits (inWords s) (maskBits k p))
    (p : Nat) (hp : p < 64) :
    laneInput s' p = roundChunk (7 - p / 8) ((s.gpr .r15).setWidth 32) ((s.gpr t4).setWidth 48) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [laneInput, getLsbD_ofBits, roundChunk_bit (7 - p / 8) k (by omega_using []) hk, hm k hk p hp]
  obtain ⟨h1, h2⟩ := maskBits_bounds p hp k hk
  simp only [hk, decide_true, Bool.true_and, maskBits, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_lo _ h1, bitOf_hi _ h2, inWords, ite_true, show (1 : Nat) ≠ 0 by decide, ite_false]

/-- The two lanes of an output, in the two halves of its byte, XOR to the
output on every input. -/
theorem lane_pair (b l x : Nat) (hl : l < 4) (hx : x < 64) :
    (laneBit (8 * b + l) x ^^ laneBit (8 * b + l + 4) x) =
      (Spec.TripleDes.sBox (7 - b) (BitVec.ofNat 6 x)).getLsbD (laneOut b l) := by
  have h1 : (8 * b + l) / 8 = b := by omega_using [hl]
  have h2 : (8 * b + l) % 8 = l := by omega_using [hl]
  have h3 : (8 * b + l + 4) / 8 = b := by omega_using [hl]
  have h4 : (8 * b + l + 4) % 8 = l + 4 := by omega_using [hl]
  have h5 : laneOut b (l + 4) = laneOut b l := by
    simp only [laneOut, show (l + 4) % 4 = l % 4 by omega_using []]
  simp only [laneBit, h1, h2, h3, h4, h5, show l / 4 = 0 by omega_using [hl], show (l + 4) / 4 = 1 by omega_using [hl]]
  rcases (show x / 32 = 0 ∨ x / 32 = 1 by omega_using [hx]) with hx' | hx' <;> simp [hx']

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
      have hs64 : pSrc q < 64 := by omega_using [hb, hll, hsrc]
      have hs64' : pSrc q + 4 < 64 := by omega_using [hb, hll, hsrc]
      rw [bitOf_lo _ hs64, bitOf_lo _ hs64']
      simp only [outWords, ite_true]
      rw [tabs _ hs64, tabs _ hs64', laneInput_eq masks _ hs64, laneInput_eq masks _ hs64', hsrc,
        show (8 * b + ll + 4) / 8 = b by omega_using [hll], show (8 * b + ll) / 8 = b by omega_using [hll],
        lane_pair b ll _ hll (BitVec.isLt _), hlo, hR₀, hK₀, BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
      rfl
    · simp only [outBits, hq32, ite_false, List.append_nil, xorBits_cons, xorBits_nil,
        Bool.xor_false, hLq, BitVec.getLsbD_setWidth, BitVec.getLsbD_xor]
      rw [BitVec.getLsbD_of_ge l q (by omega_using [hq32]),
        BitVec.getLsbD_of_ge (Spec.TripleDes.roundFunction _ _) q (by omega_using [hq32])]
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

end

end

/-! ### `TripleDes.PPC64LE.PassStart`, which only this module used -/

section

/-! ### `TripleDes.PPC64LE.Loop`, which only this module used -/

section

/-! ### `TripleDes.PPC64LE.RoundStep`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE

/-- The registers a round and the step to the next keep. -/
def roundStepKept : List Reg := [.r2, .r3, .r4, .r5, .r18, .r19, .r29, .r30, .r31]

theorem countDown_rules : ∀ n < 17, 1 ≤ n →
    (BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1)) ∧
    ((BitVec.ofNat 64 n - 1) != 0) = decide (n ≠ 1) := by
  decide +kernel

theorem roundAdvance_ok (s : State) :
    ∃ s', runBlock isa roundAdvance s = some s' ∧
      s'.gpr .r17 = s.gpr .r17 + s.gpr .r18 ∧
      s'.gpr .r16 = s.gpr .r16 - 1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .r16 → r ≠ .r17 → s'.gpr r = s.gpr r) := by
  let s₁ := s.write .r17 (s.gpr .r17 + s.gpr .r18)
  let s₂ := s₁.write .r16 (s₁.gpr .r16 - BitVec.ofNat 64 1)
  refine ⟨s₂, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · rw [roundAdvance, runBlock_cons, exec_add, runStep_some, runBlock_cons,
      exec_subi (by decide) (by decide), runStep_some, runBlock_nil]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
    rfl
  · intro r h16 h17
    simp only [s₂, s₁, gpr_write, h16, h17, ite_false]

theorem roundStep_ok (s : State)
    (l r : BitVec 32) (k : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn' : n < 17)
    (hl : s.gpr .r14 = l.setWidth 64) (hr : s.gpr .r15 = r.setWidth 64)
    (hk : s.mem.readW (s.gpr .r17) 64 = k) (hok : Ok scratchCfg s) (hc : ConstsAt s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .r17) 8)
    (hcount : s.gpr .r16 = BitVec.ofNat 64 n) :
    ∃ s', runBlock isa (roundBody ++ roundAdvance) s = some s' ∧
      s'.gpr .r14 = r.setWidth 64 ∧
      s'.gpr .r15 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)).setWidth 64 ∧
      s'.gpr .r17 = s.gpr .r17 + s.gpr .r18 ∧
      s'.gpr .r16 = BitVec.ofNat 64 (n - 1) ∧
      isa.eval (.nonzero .d .r16) s' = some (decide (n ≠ 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ roundStepKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, left₁, right₁, rd₁, wr₁, keep₁, mem₁⟩ :=
    roundBody_ok s l r k hl hr hk hok hc hread
  obtain ⟨s₂, run₂, ptr₂, count₂, rd₂, wr₂, mem₂, keep₂⟩ := roundAdvance_ok s₁
  obtain ⟨hsub, hzero⟩ := countDown_rules n hn' hn
  have hcount₁ : s₁.gpr .r16 = BitVec.ofNat 64 n := (keep₁ .r16 (by decide)).trans hcount
  refine ⟨s₂, ?_, ?_, ?_, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, ?_, ?_⟩
  · simp only [runBoxes_append, run₁, Option.bind_some, run₂]
  · exact (keep₂ .r14 (by decide) (by decide)).trans left₁
  · exact (keep₂ .r15 (by decide) (by decide)).trans right₁
  · rw [ptr₂, keep₁ .r17 (by decide), keep₁ .r18 (by decide)]
  · rw [count₂, hcount₁, hsub]
  · change VG.PPC64LE.eval (.nonzero .d .r16) s₂ = _
    simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, count₂, hcount₁, hzero]
  · intro q hq
    have hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    have hneq : q ≠ .r16 ∧ q ≠ .r17 := by revert hq; cases q <;> decide
    exact (keep₂ q hneq.1 hneq.2).trans (keep₁ q hq')
  · rw [mem₂, mem₁]; exact Frame.refl _ _

end VG.Proof.TripleDes.PPC64LE

end

end


@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix feistelStep)

def keyAddr (base : Addr) (direction : Direction) (j : Nat) : Addr :=
  base + BitVec.ofNat 64 (8 * (if direction = .encrypt then j else 15 - j))

/-- The key step of a pass, in `r18`. -/
def stepVal (direction : Direction) : BitVec 64 := if direction = .encrypt then 8 else -8

theorem keyAddr_step (base : Addr) (direction : Direction) (j : Nat) (hj : j < 15) :
    keyAddr base direction j + stepVal direction = keyAddr base direction (j + 1) := by
  cases direction
  · change base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 8 =
      base + BitVec.ofNat 64 (8 * (j + 1))
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun i => base + BitVec.ofNat 64 i) (by omega_using [])
  · change base + BitVec.ofNat 64 (8 * (15 - j)) + -BitVec.ofNat 64 8 =
      base + BitVec.ofNat 64 (8 * (15 - (j + 1)))
    rw [← BitVec.sub_eq_add_neg, Offset.add_ofNat_sub _ (by omega_using [hj])]
    exact congrArg (fun i => base + BitVec.ofNat 64 i) (by omega_using [])

structure LoopInv (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32) (n : Nat) (s : State) : Prop where
  positive : 1 ≤ n
  bounded : n ≤ 16
  left : s.gpr .r14 = (roundPrefix keys direction (16 - n) v).1.setWidth 64
  right : s.gpr .r15 = (roundPrefix keys direction (16 - n) v).2.setWidth 64
  counter : s.gpr .r16 = BitVec.ofNat 64 n
  pointer : s.gpr .r17 = keyAddr base direction (16 - n)
  step : s.gpr .r18 = stepVal direction
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

structure LoopPost (keys : DesSchedule) (direction : Direction)
    (origin : State) (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .r14 = (roundPrefix keys direction 16 v).1.setWidth 64
  right : s.gpr .r15 = (roundPrefix keys direction 16 v).2.setWidth 64
  counter : s.gpr .r16 = 0
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

theorem loopStep (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok scratchCfg origin) (hc : ConstsAt origin)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (keyAddr base direction j) 8)
    (hsep : ∀ j < 16, (⟨keyAddr base direction j, 8⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j)
    (n : Nat) (s : State) (hs : LoopInv keys direction base origin v n s) :
    WP isa (.block (roundBody ++ roundAdvance)) s (fun s' =>
      (isa.eval (.nonzero .d .r16) s' = some false ∧ LoopPost keys direction origin v s') ∨
      (isa.eval (.nonzero .d .r16) s' = some true ∧ ∃ m < n, LoopInv keys direction base origin v m s')) := by
  have hj : 16 - n < 16 := by omega_using [hs.positive]
  have hwork : spillRegion s = spillRegion origin := by
    simp only [spillRegion, hs.regs .r5 (by decide)]
  have hokS : Ok scratchCfg s := hok.congr
    (hs.regs .r5 (by decide)) (hs.regs .r5 (by decide)) hs.rd hs.wr
  have hreadS : InRegions (s.rd ++ s.wr) (s.gpr .r17) 8 := by
    rw [hs.rd, hs.wr, hs.pointer]; exact hread _ hj
  have hcS : ConstsAt s := hc.of_frame (hs.regs .r5 (by decide)) hs.frame
  have hk : (s.mem.readW (s.gpr .r17) 64).setWidth 48 = roundKey keys direction (16 - n) := by
    rw [hs.pointer]
    have hmem := hs.frame.readW (a := keyAddr base direction (16 - n)) (w := 64)
      (r := ⟨keyAddr base direction (16 - n), 8⟩)
      (Region.contains_self _ _) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq
        exact hsep _ hj) (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hkeys _ hj)
  obtain ⟨s', run, left, right, ptr, count, flag, rd, wr, regs, frame⟩ :=
    roundStep_ok s _ _ (s.mem.readW (s.gpr .r17) 64) n hs.positive
      (by omega_using [hs.bounded]) hs.left hs.right rfl hokS hcS hreadS
      hs.counter
  have hidx : 16 - (n - 1) = 16 - n + 1 := by
    omega_using [hs.positive, hs.bounded]
  have hleft : s'.gpr .r14 = (roundPrefix keys direction (16 - (n - 1)) v).1.setWidth 64 := by
    rw [hidx]
    exact left.trans (congrArg (fun pair => pair.1.setWidth 64)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hright : s'.gpr .r15 = (roundPrefix keys direction (16 - (n - 1)) v).2.setWidth 64 := by
    rw [hidx]
    have hval := congrArg (fun key =>
      ((roundPrefix keys direction (16 - n) v).1 ^^^
        Spec.TripleDes.roundFunction (roundPrefix keys direction (16 - n) v).2 key).setWidth 64) hk
    exact (right.trans hval).trans (congrArg (fun pair => pair.2.setWidth 64)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hframe : Frame [spillRegion origin] origin.mem s'.mem := by
    rw [hwork] at frame
    exact hs.frame.trans frame
  have hregs : ∀ q ∈ roundStepKept, s'.gpr q = origin.gpr q :=
    fun q hq => (regs q hq).trans (hs.regs q hq)
  refine WP.of_runBlock ⟨s', run, ?_⟩
  by_cases hlast : n = 1
  · left
    refine ⟨?_, ?_⟩
    · simpa only [hlast, ne_eq, not_true_eq_false, decide_false] using flag
    · subst n
      exact ⟨hleft, hright, count, rd.trans hs.rd, wr.trans hs.wr, hregs, hframe⟩
  · right
    refine ⟨?_, n - 1, by omega_using [hs.positive], ?_⟩
    · simpa only [hlast, ne_eq, not_false_eq_true, decide_true] using flag
    · refine ⟨by omega_using [hs.positive, hlast], by omega_using [hs.bounded],
        hleft, hright, count, ?_, (regs .r18 (by decide)).trans hs.step,
        rd.trans hs.rd, wr.trans hs.wr, hregs, hframe⟩
      rw [ptr, hs.pointer, hs.step, keyAddr_step base direction (16 - n) (by
        omega_using [hs.positive, hlast]), ← hidx]

/-- The complete sixteen-round loop, in either key order. -/
theorem roundsLoop_ok (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok scratchCfg origin) (hc : ConstsAt origin)
    (hl : origin.gpr .r14 = v.1.setWidth 64) (hr : origin.gpr .r15 = v.2.setWidth 64)
    (hptr : origin.gpr .r17 = keyAddr base direction 0)
    (hcount : origin.gpr .r16 = BitVec.ofNat 64 16)
    (hstep : origin.gpr .r18 = stepVal direction)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (keyAddr base direction j) 8)
    (hsep : ∀ j < 16, (⟨keyAddr base direction j, 8⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j) :
    WP isa (.loop (.block (roundBody ++ roundAdvance)) (.nonzero .d .r16))
      origin (LoopPost keys direction origin v) := by
  apply WP.loop (M := isa) (body := .block (roundBody ++ roundAdvance))
    (c := .nonzero .d .r16) (Q := LoopPost keys direction origin v) (LoopInv keys direction base origin v)
    (loopStep keys direction base origin v hok hc hread hsep hkeys)
    16 origin
  exact ⟨by decide, by decide, hl, hr, hcount, hptr, hstep, rfl, rfl,
    fun _ _ => rfl, Frame.refl _ _⟩

end VG.Proof.TripleDes.PPC64LE

end

end


@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction)

def passOffset (component : Nat) (direction : Direction) : Nat :=
  128 * component + if direction = .encrypt then 0 else 120

theorem passOffset_bound : ∀ c < 3, ∀ d : Direction, passOffset c d < 2 ^ 15 := by
  intro c hc d
  cases d <;> simp only [passOffset, reduceCtorEq, ite_true, ite_false] <;> omega_using [hc]

theorem passStart_ok (component : Nat) (hc : component < 3) (direction : Direction)
    (s : State) :
    ∃ s', runBlock isa (passStart component direction) s = some s' ∧
      s'.gpr .r17 = s.gpr .r3 + BitVec.ofNat 64 (passOffset component direction) ∧
      s'.gpr .r16 = BitVec.ofNat 64 16 ∧ s'.mem = s.mem ∧
      s'.gpr .r18 = stepVal direction ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r16 → r ≠ .r17 → r ≠ .r18 → s'.gpr r = s.gpr r) := by
  have hb := passOffset_bound component hc direction
  let s₁ := s.write .r17 (s.gpr .r3 + BitVec.ofNat 64 (passOffset component direction))
  let s₂ := s₁.write .r16 (BitVec.ofNat 64 16)
  let s₃ := s₂.write .r18 (BitVec.ofNat 64 0)
  let s₄ := s₃.write .r18 (stepVal direction)
  have e₄ : exec (if direction = .encrypt then .addi .r18 .r18 8 else .subi .r18 .r18 8) s₃ =
      some s₄ := by
    cases direction
    · rw [ite_eq_left rfl, exec_addi (by decide) (by decide)]
      simp only [s₄, s₃, gpr_write, ite_true, stepVal]
      rfl
    · rw [ite_eq_right (by decide), exec_subi (by decide) (by decide)]
      simp only [s₄, s₃, gpr_write, ite_true, stepVal, reduceCtorEq, ite_false]
      rfl
  refine ⟨s₄, ?_, ?_, ?_, rfl, ?_, rfl, rfl, ?_⟩
  · rw [passStart, runBlock_cons, show (128 * component + if direction = .encrypt then 0 else 120)
        = passOffset component direction from rfl,
      exec_addi (by decide) hb, runStep_some, runBlock_cons, imm, exec_li (by decide),
      runStep_some, runBlock_cons, imm, exec_li (by decide), runStep_some, runBlock_cons, e₄,
      runStep_some, runBlock_nil]
  · simp only [s₄, s₃, s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [s₄, s₃, s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [s₄, gpr_write, ite_true]
  · intro r h16 h17 h18
    simp only [s₄, s₃, s₂, s₁, gpr_write, h16, h17, h18, ite_false]

end VG.Proof.TripleDes.PPC64LE

end

end


@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix)

/-- What choosing and starting the pass of component `c` and direction `d` leaves. -/
structure StartPost (c : Nat) (d : Direction) (s t : State) : Prop where
  ptr : t.gpr .r17 = s.gpr .r3 + BitVec.ofNat 64 (passOffset c d)
  count : t.gpr .r16 = BitVec.ofNat 64 16
  mem : t.mem = s.mem
  step : t.gpr .r18 = stepVal d
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  regs : ∀ r, r ≠ .r16 → r ≠ .r17 → r ≠ .r18 → r ≠ .r20 → t.gpr r = s.gpr r

theorem passOf_lt (d : Direction) (p : Nat) : (passOf d p).1 < 3 := by
  cases d <;> (rcases p with _ | _ | _ | _ | p) <;> simp [passOf]

theorem subi_zero (x : BitVec 64) (p k : Nat) (hx : x = BitVec.ofNat 64 p) (hp : 1 ≤ p ∧ p ≤ 3)
    (hk : k ≤ 3) : ((x - BitVec.ofNat 64 k) == 0) = (p == k) := by
  subst hx
  rcases hp with ⟨h1, h3⟩
  rcases p with _ | _ | _ | _ | p <;> (try omega) <;>
    rcases k with _ | _ | _ | _ | k <;> first | omega | decide

theorem select_ok (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) (s : State)
    (hpasses : s.gpr .r19 = BitVec.ofNat 64 p) :
    WP isa (passSelect d) s (StartPost (passOf d p).1 (passOf d p).2 s) := by
  have branch : ∀ (t : State) (q : Nat), q = p → t.mem = s.mem → t.rd = s.rd →
      t.wr = s.wr → (∀ r, r ≠ .r20 → t.gpr r = s.gpr r) →
      WP isa (.block (passStart (passOf d q).1 (passOf d q).2)) t
        (StartPost (passOf d p).1 (passOf d p).2 s) := by
    intro t q hq hm hrd hwr hg
    subst hq
    obtain ⟨u, run, ptr, count, mem, step, rd, wr, regs⟩ := passStart_ok (passOf d q).1
      (passOf_lt d q) (passOf d q).2 t
    refine WP.of_runBlock ⟨u, run, ?_, count, mem.trans hm, step, rd.trans hrd, wr.trans hwr, ?_⟩
    · rw [ptr, hg .r3 (by decide)]
    · intro r h16 h17 h18 h20
      exact (regs r h16 h17 h18).trans (hg r h20)
  let t₁ := s.write .r20 (s.gpr .r19 - BitVec.ofNat 64 3)
  have hg₁ : ∀ r, r ≠ .r20 → t₁.gpr r = s.gpr r := fun r h => gpr_write_of_ne _ _ h
  apply WP.seq
  refine WP.of_runBlock ⟨t₁, by
    rw [runBlock_cons, exec_subi (by decide) (by decide), runStep_some, runBlock_nil], ?_⟩
  have zf₁ : isa.eval (.zero .d .r20) t₁ = some (p == 3) := by
    change VG.PPC64LE.eval (.zero .d .r20) t₁ = _
    simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, t₁, gpr_write_self]
    rw [subi_zero _ p 3 hpasses hp (by decide)]
  apply WP.ite (p == 3) zf₁
  · intro h3
    exact branch t₁ 3 (by simpa using h3 : p = 3).symm rfl rfl rfl hg₁
  · intro h3
    apply WP.seq
    let t₂ := t₁.write .r20 (t₁.gpr .r19 - BitVec.ofNat 64 2)
    refine WP.of_runBlock ⟨t₂, by
      rw [runBlock_cons, exec_subi (by decide) (by decide), runStep_some, runBlock_nil], ?_⟩
    have zf₂ : isa.eval (.zero .d .r20) t₂ = some (p == 2) := by
      change VG.PPC64LE.eval (.zero .d .r20) t₂ = _
      simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, t₂, gpr_write_self]
      rw [subi_zero _ p 2 ((hg₁ .r19 (by decide)).trans hpasses) hp (by decide)]
    have hg₂ : ∀ r, r ≠ .r20 → t₂.gpr r = s.gpr r := fun r h =>
      (gpr_write_of_ne _ _ h).trans (hg₁ r h)
    apply WP.ite (p == 2) zf₂
    · intro h2
      exact branch t₂ 2 (by simpa using h2 : p = 2).symm rfl rfl rfl hg₂
    · intro h2
      have hp3 : p ≠ 3 := by simpa using h3
      have hp2 : p ≠ 2 := by simpa using h2
      exact branch t₂ 1 (by omega_using [hp, hp3, hp2]) rfl rfl rfl hg₂

/-- The registers a pass keeps. -/
def passKept : List Reg := [.r2, .r3, .r4, .r5, .r29, .r30, .r31]

structure PassPost (keys : DesSchedule) (direction : Direction)
    (origin : State) (v : BitVec 32 × BitVec 32) (n : Nat) (s : State) : Prop where
  left : s.gpr .r14 = (roundPrefix keys direction 16 v).2.setWidth 64
  right : s.gpr .r15 = (roundPrefix keys direction 16 v).1.setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ passKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem
  passes : s.gpr .r19 = BitVec.ofNat 64 (n - 1)
  zf : isa.eval (.nonzero .d .r19) s = some (decide (n ≠ 1))

theorem passCountAdvance_ok (s : State) :
    ∃ s', runBlock isa passCountAdvance s = some s' ∧
      s'.gpr .r19 = s.gpr .r19 - 1 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .r19 → s'.gpr r = s.gpr r) :=
  ⟨s.write .r19 (s.gpr .r19 - BitVec.ofNat 64 1), by
    rw [passCountAdvance, runBlock_cons, exec_subi (by decide) (by decide), runStep_some,
      runBlock_nil], gpr_write_self _ _ _, rfl, rfl, rfl, fun _ h => gpr_write_of_ne _ _ h⟩

/-- A complete DES pass: the choice of its keys by the passes left, its
sixteen rounds, the final half swap and the passes left counted down. -/
theorem pass_ok (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3)
    (keys : DesSchedule) (base : Addr) (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok scratchCfg origin) (hc : ConstsAt origin)
    (hl : origin.gpr .r14 = v.1.setWidth 64) (hr : origin.gpr .r15 = v.2.setWidth 64)
    (hpasses : origin.gpr .r19 = BitVec.ofNat 64 p)
    (hptr : origin.gpr .r3 + BitVec.ofNat 64 (passOffset (passOf d p).1 (passOf d p).2) =
      keyAddr base (passOf d p).2 0)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (keyAddr base (passOf d p).2 j) 8)
    (hsep : ∀ j < 16, (⟨keyAddr base (passOf d p).2 j, 8⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (keyAddr base (passOf d p).2 j) 64).setWidth 48 =
      roundKey keys (passOf d p).2 j) :
    WP isa (pass d) origin (PassPost keys (passOf d p).2 origin v p) := by
  apply WP.seq
  refine WP.mono (select_ok d hp origin hpasses) fun s hs => ?_
  generalize (passOf d p).2 = dir at hs hptr hread hsep hkeys ⊢
  have hbase : s.gpr .r5 = origin.gpr .r5 := hs.regs .r5 (by decide) (by decide) (by decide)
    (by decide)
  have hspill : spillRegion s = spillRegion origin := by simp only [spillRegion, hbase]
  have hloop := roundsLoop_ok keys dir base s v
    (hok.congr hbase hbase hs.rd hs.wr) (hc.congr hbase hs.mem)
    ((hs.regs .r14 (by decide) (by decide) (by decide) (by decide)).trans hl)
    ((hs.regs .r15 (by decide) (by decide) (by decide) (by decide)).trans hr)
    (hs.ptr.trans hptr) hs.count hs.step
    (by rw [hs.rd, hs.wr]; exact hread)
    (by rw [hspill]; exact hsep) (by rw [hs.mem]; exact hkeys)
  apply WP.seq
  refine WP.mono hloop fun s₂ hs₂ => ?_
  obtain ⟨s₃, run₃, left₃, right₃, rd₃, wr₃, mem₃, regs₃⟩ := swapHalves_ok s₂
  obtain ⟨s₄, run₄, p₄, rd₄, wr₄, mem₄, regs₄⟩ := passCountAdvance_ok s₃
  have hp₃ : s₃.gpr .r19 = BitVec.ofNat 64 p :=
    (regs₃ .r19 (by decide)).trans ((hs₂.regs .r19 (by decide)).trans
      ((hs.regs .r19 (by decide) (by decide) (by decide) (by decide)).trans hpasses))
  obtain ⟨hsub, hzero⟩ := countDown_rules p (by omega_using [hp]) hp.1
  refine WP.of_runBlock ⟨s₄, by simp only [runBoxes_append, run₃, Option.bind_some, run₄], ?_⟩
  refine ⟨?_, ?_, rd₄.trans (rd₃.trans (hs₂.rd.trans hs.rd)),
    wr₄.trans (wr₃.trans (hs₂.wr.trans hs.wr)), ?_, ?_, ?_, ?_⟩
  · exact (regs₄ .r14 (by decide)).trans (left₃.trans hs₂.right)
  · exact (regs₄ .r15 (by decide)).trans (right₃.trans hs₂.left)
  · intro q hq
    have hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    have hq'' : q ∈ roundStepKept := by revert hq; cases q <;> decide
    have hne : q ≠ .r16 ∧ q ≠ .r17 ∧ q ≠ .r18 ∧ q ≠ .r19 ∧ q ≠ .r20 := by
      revert hq; cases q <;> decide
    exact (regs₄ q hne.2.2.2.1).trans ((regs₃ q hq').trans ((hs₂.regs q hq'').trans
      (hs.regs q hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.2)))
  · have hf := hs₂.frame
    rw [hspill, hs.mem] at hf
    rw [mem₄, mem₃]
    exact hf
  · rw [p₄, hp₃, hsub]
  · change VG.PPC64LE.eval (.nonzero .d .r19) s₄ = some (decide (p ≠ 1))
    simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, p₄, hp₃]
    rw [hsub]
    rcases hp with ⟨h1, h3⟩
    rcases p with _ | _ | _ | _ | p <;> first | omega | decide

end VG.Proof.TripleDes.PPC64LE
