module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Ecb
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.Schedule
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Permutation
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.RoundLit
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.PPC64LE.MovImm
import VerifiedGarbage.Proof.TripleDes.Word
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Lit
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Block
public import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Linear
public import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.TripleDes.Pieces
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Feistel

/-! ### `TripleDes.PPC64LE.Pass`, which only this module used -/

section

/-! ### `TripleDes.PPC64LE.Spills`, which this module and modules that import it used -/

section

/-!
# The scratch buffer of the block functions

The block saves `r14`–`r28` in slots 0–14 of the scratch buffer at `r5` and
stores the round function's words of constants in slots 15–61 (`ConstsAt`).
The rounds write no memory, so their frame is the two slots left
(`spillRegion`), which keeps the constants and the saved registers.
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE

/-- The scratch buffer's 64 words, writable. -/
def scratchCfg : Cfg := { base := .r5, slots := 64, ext := .r5, exts := 0 }

/-- The slots the rounds may write: the two after the constants. -/
def spillRegion (s : State) : Region := ⟨s.gpr .r5 + BitVec.ofNat 64 496, 16⟩

/-- Slots 15–61 hold the round function's words of constants. -/
def ConstsAt (s : State) : Prop :=
  ∀ c < 47, s.mem.readW (wordAddr (s.gpr .r5) (15 + c)) 64 = roundConsts.getD c 0

theorem ConstsAt.of_frame {s t : State} (h : ConstsAt s) (hb : t.gpr .r5 = s.gpr .r5)
    (hf : Frame [spillRegion s] s.mem t.mem) : ConstsAt t := by
  intro c hc
  rw [hb, ← h c hc]
  exact hf.readW (r := ⟨wordAddr (s.gpr .r5) (15 + c), 8⟩) (Region.contains_self _ _)
    (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq
      exact Offset.disjoint _ (Or.inl (by omega_using [hc])) (by omega_using [hc]) (by omega_using [])) (by decide)

theorem ConstsAt.congr {s t : State} (h : ConstsAt s) (hb : t.gpr .r5 = s.gpr .r5)
    (hm : t.mem = s.mem) : ConstsAt t :=
  h.of_frame hb (by rw [hm]; exact Frame.refl _ _)

theorem runBoxes_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

end VG.Proof.TripleDes.PPC64LE

end

end

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

end

end

/-! ### `TripleDes.PPC64LE.Block`, which this module and modules that import it used -/

section

/-! ### `TripleDes.PPC64LE.Ready`, which only this module used -/

section

/-! ### `TripleDes.PPC64LE.WordState`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE
open VG.Proof.TripleDes (desCore roundPrefix)

/-- A DES word held as two zero-extended 32-bit Feistel registers. -/
structure WordState (x : BitVec 64) (s : State) : Prop where
  left : s.gpr .r14 = ((x >>> 32).setWidth 32).setWidth 64
  right : s.gpr .r15 = (x.setWidth 32).setWidth 64

theorem PassPost.wordState {keys : Spec.TripleDes.DesSchedule}
    {direction : Spec.TripleDes.Direction} {origin s : State} {x : BitVec 64} {n : Nat}
    (hs : PassPost keys direction origin ((x >>> 32).setWidth 32, x.setWidth 32) n s) :
    WordState (desCore keys direction x) s := by
  have hcore := VG.Proof.TripleDes.desCore_roundPrefix keys direction x
  let halves := roundPrefix keys direction 16 ((x >>> 32).setWidth 32, x.setWidth 32)
  have hleft : ((desCore keys direction x >>> 32).setWidth 32).setWidth 64 = halves.2.setWidth 64 :=
    (congrArg (fun v : BitVec 64 => ((v >>> 32).setWidth 32).setWidth 64) hcore).trans
      (congrArg (BitVec.setWidth 64) (VG.Proof.TripleDes.appended_left halves.2 halves.1))
  have hright : ((desCore keys direction x).setWidth 32).setWidth 64 = halves.1.setWidth 64 :=
    (congrArg (fun v : BitVec 64 => (v.setWidth 32).setWidth 64) hcore).trans
      (congrArg (BitVec.setWidth 64) (VG.Proof.TripleDes.appended_right halves.2 halves.1))
  exact ⟨hs.left.trans hleft.symm, hs.right.trans hright.symm⟩

end VG.Proof.TripleDes.PPC64LE

end

end

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def componentBase (base : Addr) (component : Nat) : Addr :=
  base + BitVec.ofNat 64 (128 * component)

structure Ready (keys : Nat → DesSchedule) (base : Addr) (s : State) : Prop where
  scratch : Ok scratchCfg s
  consts : ConstsAt s
  baseReg : s.gpr .r3 = base
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    InRegions (s.rd ++ s.wr) (keyAddr (componentBase base c) d j) 8
  separate : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (spillRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (s.mem.readW (keyAddr (componentBase base c) d j) 64).setWidth 48 = roundKey (keys c) d j

theorem Ready.congr {keys : Nat → DesSchedule} {base : Addr} {s t : State}
    (hs : Ready keys base s) (hbase : t.gpr .r5 = s.gpr .r5)
    (hkey : t.gpr .r3 = s.gpr .r3) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : Frame [spillRegion s] s.mem t.mem) : Ready keys base t := by
  have hwork : spillRegion t = spillRegion s :=
    congrArg (fun p => (⟨p + BitVec.ofNat 64 496, 16⟩ : Region)) hbase
  refine ⟨hs.scratch.congr hbase hbase hrd hwr, hs.consts.of_frame hbase hf, hkey.trans hs.baseReg,
    ?_, ?_, ?_⟩
  · rw [hrd, hwr]; exact hs.read
  · rw [hwork]; exact hs.separate
  · intro c hc d j hj
    have hmem := hf.readW (a := keyAddr (componentBase base c) d j) (w := 64)
      (r := ⟨keyAddr (componentBase base c) d j, 8⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hs.separate c hc d j hj) (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hs.values c hc d j hj)

theorem passPointer (base : Addr) (c : Nat) (d : Direction) :
    base + BitVec.ofNat 64 (passOffset c d) = keyAddr (componentBase base c) d 0 := by
  cases d
  · change base + BitVec.ofNat 64 (128 * c + 0) = base + BitVec.ofNat 64 (128 * c) + (0 : BitVec 64)
    exact (congrArg (fun n => base + BitVec.ofNat 64 n) (Nat.add_zero (128 * c))).trans
      (BitVec.add_zero (base + BitVec.ofNat 64 (128 * c))).symm
  · simp only [passOffset, keyAddr, componentBase, reduceCtorEq, ite_false]
    rw [Offset.add_ofNat_add_ofNat]


structure Stable (origin s : State) : Prop where
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ passKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

theorem Stable.trans {s t u : State} (hs : Stable s t) (ht : Stable t u) : Stable s u := by
  have hwork : spillRegion t = spillRegion s :=
    congrArg (fun p => (⟨p + BitVec.ofNat 64 496, 16⟩ : Region)) (hs.regs .r5 (by decide))
  have hf := ht.frame
  rw [hwork] at hf
  exact ⟨ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun q hq => (ht.regs q hq).trans (hs.regs q hq), hs.frame.trans hf⟩

theorem pass_word_ok (keys : Nat → DesSchedule) (base : Addr) (s : State) (x : BitVec 64)
    (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3)
    (hready : Ready keys base s) (hword : WordState x s)
    (hpasses : s.gpr .r19 = BitVec.ofNat 64 p) :
    WP isa (pass d) s (fun t =>
      WordState (VG.Proof.TripleDes.desCore (keys (passOf d p).1) (passOf d p).2 x) t ∧
      Ready keys base t ∧ Stable s t ∧
      t.gpr .r19 = BitVec.ofNat 64 (p - 1) ∧
      isa.eval (.nonzero .d .r19) t = some (decide (p ≠ 1))) := by
  have hc := passOf_lt d p
  have hptr : s.gpr .r3 + BitVec.ofNat 64 (passOffset (passOf d p).1 (passOf d p).2) =
      keyAddr (componentBase base (passOf d p).1) (passOf d p).2 0 := by
    rw [hready.baseReg]
    exact passPointer base _ _
  apply WP.mono (pass_ok d hp (keys (passOf d p).1) (componentBase base (passOf d p).1) s
    ((x >>> 32).setWidth 32, x.setWidth 32) hready.scratch hready.consts hword.left hword.right
    hpasses hptr (hready.read _ hc _) (hready.separate _ hc _) (hready.values _ hc _))
  intro t ht
  exact ⟨ht.wordState,
    hready.congr (ht.regs .r5 (by decide)) (ht.regs .r3 (by decide)) ht.rd ht.wr ht.frame,
    ⟨ht.rd, ht.wr, ht.regs, ht.frame⟩, ht.passes, ht.zf⟩

end VG.Proof.TripleDes.PPC64LE

end

end

/-! ### `TripleDes.PPC64LE.Save`, which only this module used -/

section

/-!
# Saving and restoring `r14`–`r28` in slots 0–14 of the scratch buffer
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

def savedReg (i : Nat) : Reg := savedRegs.getD i .r14

theorem blockSave_eq : blockSave = Spill.saveCode .r5 (Spill.slots savedReg 15) := by
  decide +kernel

theorem blockRestore_eq : blockRestore = Spill.restoreCode .r5 (Spill.slots savedReg 15) := by
  decide +kernel

def Saved (original current : State) : Prop :=
  ∀ i < 15, current.mem.readW (current.gpr .r5 + BitVec.ofNat 64 (8 * i)) 64 =
    original.gpr (savedReg i)

structure SavePost (original current : State) : Prop where
  gpr : current.gpr = original.gpr
  rd : current.rd = original.rd
  wr : current.wr = original.wr
  saved : Saved original current
  frame : Frame [⟨original.gpr .r5, 120⟩] original.mem current.mem

theorem blockSave_ok (s : State)
    (hw : ∀ i < 15, InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block blockSave) s (SavePost s) := by
  rw [blockSave_eq]
  refine WP.mono (Spill.save_wp (by decide) (by decide) (Spill.forall_slots hw)) fun s' h =>
    ⟨h.gpr, h.rd, h.wr, fun i hi => ?_, ?_⟩
  · rw [h.gpr, h.mem]
    exact Spill.saveMem_saved (l := Spill.slots savedReg 15) (by decide) s.mem (s.gpr .r5) s.gpr
      (savedReg i, 8 * i) (Spill.mem_slots hi)
  · rw [h.mem]; exact Spill.saveMem_frame_base (by decide) (by decide) _ _ _

structure RestorePost (original origin current : State) : Prop where
  saved : ∀ r ∈ savedRegs, current.gpr r = original.gpr r
  keep : Keep savedRegs origin current
  mem : current.mem = origin.mem

theorem blockRestore_ok (original s : State) (hsaved : Saved original s)
    (hread : ∀ i < 15, InRegions (s.rd ++ s.wr) (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block blockRestore) s (RestorePost original s) := by
  rw [blockRestore_eq]
  have hregs : (Spill.slots savedReg 15).map Prod.fst = savedRegs := by decide +kernel
  exact WP.mono (Spill.restore_wp (by decide) rfl (by decide) (by decide) (Spill.forall_slots hread)
    (Spill.forall_slots hsaved)) fun s' h =>
    ⟨fun r hr => h.gpr_of (.inl (hregs ▸ hr)), ⟨fun r hr => h.other r (hregs ▸ hr), h.rd, h.wr⟩,
      h.mem⟩

theorem savedSlot_spill_disjoint (s : State) (i : Nat) (hi : i < 15) :
    (⟨s.gpr .r5 + BitVec.ofNat 64 (8 * i), 8⟩ : Region).Disjoint (spillRegion s) :=
  Offset.disjoint (s.gpr .r5) (by omega_using [hi]) (by omega_using [hi]) (by decide)

theorem Saved.congr {original s t : State} (hs : Saved original s)
    (hbase : t.gpr .r5 = s.gpr .r5) (hf : Frame [spillRegion s] s.mem t.mem) :
    Saved original t := by
  intro i hi
  have hmem := hf.readW (a := s.gpr .r5 + BitVec.ofNat 64 (8 * i)) (w := 64)
    (r := ⟨s.gpr .r5 + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
    (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact savedSlot_spill_disjoint s i hi)
    (by decide)
  rw [hbase]
  exact hmem.trans (hs i hi)

end VG.Proof.TripleDes.PPC64LE

end

end

/-! ### `TripleDes.PPC64LE.BlockIO`, which only this module used -/

section

/-! ### `TripleDes.PPC64LE.Initial`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE
open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

theorem initial_ok (s : State) :
    ∃ s', runBlock isa (instrs initialPermutation.lit) s = some s' ∧
      s'.gpr .r8 = (Spec.TripleDes.permute Spec.TripleDes.ip
        ((s.gpr .r7).setWidth 64)).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) :=
  fixedPermutation_ok Spec.TripleDes.ip (by decide) (by decide)
    VG.Proof.TripleDes.ip_bounds .r7 .r8 (instrs initialPermutation.lit) initialPermutation_check s
end VG.Proof.TripleDes.PPC64LE
namespace VG.Proof.TripleDes.PPC64LE
open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

theorem initial_raw_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.ip 64 .r8 .r7 .r9 .r10) s = some s' ∧
      s'.gpr .r8 = Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .r7) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, mem, regs⟩ := initial_ok s
  have hcode : permuteCode Spec.TripleDes.ip 64 .r8 .r7 .r9 .r10 =
      instrs initialPermutation.lit := congrArg instrs initialPermutation.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, mem, regs⟩
  exact word.trans ((BitVec.setWidth_eq _).trans
    (congrArg (Spec.TripleDes.permute Spec.TripleDes.ip) (BitVec.setWidth_eq _)))
end VG.Proof.TripleDes.PPC64LE

namespace VG.Proof.TripleDes.PPC64LE
open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE
theorem final_ok (s : State) :
    ∃ s', runBlock isa (instrs finalPermutation.lit) s = some s' ∧
      s'.gpr .r8 = (Spec.TripleDes.permute Spec.TripleDes.fp
        ((s.gpr .r6).setWidth 64)).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) :=
  fixedPermutation_ok Spec.TripleDes.fp (by decide) (by decide)
    VG.Proof.TripleDes.fp_bounds .r6 .r8 (instrs finalPermutation.lit) finalPermutation_check s

theorem final_raw_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.fp 64 .r8 .r6 .r9 .r10) s = some s' ∧
      s'.gpr .r8 = Spec.TripleDes.permute Spec.TripleDes.fp (s.gpr .r6) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, mem, regs⟩ := final_ok s
  have hcode : permuteCode Spec.TripleDes.fp 64 .r8 .r6 .r9 .r10 =
      instrs finalPermutation.lit := congrArg instrs finalPermutation.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, mem, regs⟩
  exact word.trans ((BitVec.setWidth_eq _).trans
    (congrArg (Spec.TripleDes.permute Spec.TripleDes.fp) (BitVec.setWidth_eq _)))

end VG.Proof.TripleDes.PPC64LE

end

end

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

/-- The registers the block's load and store keep. -/
def loadKept : List Reg := passKept

theorem readData_ok (s : State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .r4) 8) :
    ∃ s', runBlock isa [.li .r6 0, .loadRev .d .r7 .r4 .r6] s = some s' ∧
      s'.gpr .r7 = Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .r4)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r6 → r ≠ .r7 → s'.gpr r = s.gpr r) := by
  let s₁ := s.write .r6 (BitVec.ofNat 64 0)
  have ha : s₁.gpr .r4 + s₁.gpr .r6 = s.gpr .r4 := by
    simp only [s₁, gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.add_zero]
  have hload := exec_loadRev_d (s := s₁) (t := .r7) (a := .r4) (b := .r6) (by decide)
    (by rw [ha]; exact hread)
  rw [ha] at hload
  let s₂ := s₁.write .r7 (rev64 (s₁.mem.readW (s.gpr .r4) 64))
  refine ⟨s₂, by
    rw [runBlock_cons, exec_li (by decide), runStep_some, runBlock_cons, hload, runStep_some,
      runBlock_nil], ?_, rfl, rfl, rfl, ?_⟩
  · rw [gpr_write_self]
    exact (decodeBlock_readW s.mem (s.gpr .r4)).symm
  · intro r h6 h7
    simp only [s₂, s₁, gpr_write, h6, h7, ite_false]

theorem rotateRight_zero32 (x : BitVec 32) : x.rotateRight 0 = x := by
  simp [BitVec.rotateRight, BitVec.rotateRightAux]

def splitHalves : List Instr := [.lsr .d .r14 .r8 32, .rotr .w .r15 .r8 0]

theorem splitHalves_ok (s : State) :
    ∃ s', runBlock isa splitHalves s = some s' ∧
      s'.gpr .r14 = s.gpr .r8 >>> 32 ∧
      s'.gpr .r15 = ((s.gpr .r8).setWidth 32).setWidth 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) := by
  let s₁ := s.write .r14 (s.gpr .r8 >>> 32)
  let s₂ := s₁.write .r15 (((s₁.gpr .r8).setWidth 32).rotateRight 0 |>.setWidth 64)
  refine ⟨s₂, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · rw [splitHalves, runBlock_cons, exec_lsr_d (by decide), runStep_some, runBlock_cons,
      exec_rotr_w (by decide), runStep_some, runBlock_nil]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false, rotateRight_zero32]
  · intro r h14 h15
    simp only [s₂, s₁, gpr_write, h14, h15, ite_false]

theorem upperHalf_extend (x : BitVec 64) :
    x >>> 32 = ((x >>> 32).setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases h : j < 32
  · simp only [h, hj, decide_true, Bool.true_and]
  · have hz : x.getLsbD (32 + j) = false := BitVec.getLsbD_of_ge _ _ (by omega_using [h])
    simp only [h, hj, decide_false, decide_true, Bool.false_and, Bool.true_and, hz]

theorem runAppend_some (xs ys : List Instr) (s t u : State)
    (hx : runBlock isa xs s = some t) (hy : runBlock isa ys t = some u) :
    runBlock isa (xs ++ ys) s = some u := by
  calc
    runBlock isa (xs ++ ys) s = (runBlock isa xs s).bind (runBlock isa ys) :=
      runBoxes_append xs ys s
    _ = (some t).bind (runBlock isa ys) := congrArg (fun v => v.bind (runBlock isa ys)) hx
    _ = runBlock isa ys t := Option.bind_some t (runBlock isa ys)
    _ = some u := hy

theorem initial_preserves : loadKept.all (fun r =>
    (instrs initialPermutation.lit).all (fun op => dstOf op != some r)) = true := by
  decide +kernel

theorem blockLoad_ok (s : State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .r4) 8) :
    ∃ s', runBlock isa blockLoad s = some s' ∧
      s'.gpr .r14 =
        (((Spec.TripleDes.permute Spec.TripleDes.ip
          (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .r4)))) >>> 32).setWidth 32).setWidth 64 ∧
      s'.gpr .r15 =
        ((Spec.TripleDes.permute Spec.TripleDes.ip
          (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .r4)))).setWidth 32).setWidth 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ loadKept, s'.gpr r = s.gpr r) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, regs₁⟩ := readData_ok s hread
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, mem₂, regs₂⟩ := initial_raw_ok s₁
  obtain ⟨s₃, run₃, left₃, right₃, mem₃, rd₃, wr₃, regs₃⟩ := splitHalves_ok s₂
  have hword : s₂.gpr .r8 = Spec.TripleDes.permute Spec.TripleDes.ip
      (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .r4))) :=
    word₂.trans (congrArg (Spec.TripleDes.permute Spec.TripleDes.ip) word₁)
  have hhead := runAppend_some _ _ _ _ _ run₁ run₂
  have htail := runAppend_some _ _ _ _ _ hhead run₃
  have hcode : blockLoad =
      (([.li .r6 0, .loadRev .d .r7 .r4 .r6] : List Instr) ++
        permuteCode Spec.TripleDes.ip 64 .r8 .r7 .r9 .r10) ++ splitHalves := by
    simp only [blockLoad, splitHalves, List.append_assoc]
  refine ⟨s₃, (congrArg (fun is => runBlock isa is s) hcode).trans htail, ?_, ?_,
    mem₃.trans (mem₂.trans mem₁), rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), ?_⟩
  · exact left₃.trans ((congrArg (fun x : BitVec 64 => x >>> 32) hword).trans (upperHalf_extend _))
  · exact right₃.trans (congrArg (fun x : BitVec 64 => (x.setWidth 32).setWidth 64) hword)
  · intro r hr
    have hno := List.all_eq_true.mp initial_preserves r hr
    have hne : r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r14 ∧ r ≠ .r15 := by
      clear hno; revert hr; cases r <;> decide
    exact (regs₃ r hne.2.2.1 hne.2.2.2).trans ((regs₂ r hno).trans (regs₁ r hne.1 hne.2.1))

end VG.Proof.TripleDes.PPC64LE

end

end

/-! ### `TripleDes.PPC64LE.Head`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

/-- Slots 0–61 of the scratch buffer: the saved registers and the constants. -/
def saveRegion (s : State) : Region := ⟨s.gpr .r5, 496⟩

structure HeadPre (keys : Nat → DesSchedule) (base : Addr) (s : State) : Prop where
  scratch : Ok scratchCfg s
  pointer : s.gpr .r3 = base
  saveRead : ∀ i < 15, InRegions (s.rd ++ s.wr) (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8
  saveWrite : ∀ i < 62, InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8
  dataRead : InRegions (s.rd ++ s.wr) (s.gpr .r4) 8
  dataSeparate : (⟨s.gpr .r4, 8⟩ : Region).Disjoint (saveRegion s)
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    InRegions (s.rd ++ s.wr) (keyAddr (componentBase base c) d j) 8
  separateWork : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (spillRegion s)
  separateSave : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (saveRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (s.mem.readW (keyAddr (componentBase base c) d j) 64).setWidth 48 = roundKey (keys c) d j

structure HeadPost (keys : Nat → DesSchedule) (base : Addr) (original s : State) : Prop where
  word : WordState (Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt original.mem (original.gpr .r4)))) s
  ready : Ready keys base s
  saved : Saved original s
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  regs : ∀ q ∈ loadKept, s.gpr q = original.gpr q
  frame : Frame [saveRegion original] original.mem s.mem

/-! ## The constants -/

theorem movImm64_ok (d : Reg) (v : BitVec 64) (s : State) :
    ∃ s', runBlock isa (movImm64 d v) s = some s' ∧ s'.gpr d = v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [movImm64, runBlock_cons, exec_lis, runStep_some, runBlock_cons, exec_ori, runStep_some,
    runBlock_cons, exec_lsl (by decide), runStep_some, runBlock_cons, exec_oris, runStep_some,
    runBlock_cons, exec_ori, runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [gpr_write_self]
    exact movImm64_eq v
  · simp [gpr_write, hr]

/-- The memory `m` with the words `vs` written at `B + off` on. -/
def constMem (m : Mem) (B : Addr) : List (BitVec 64) → Nat → Mem
  | [], _ => m
  | v :: vs, off => constMem (m.writeW (B + BitVec.ofNat 64 off) v) B vs (off + 8)

theorem constMem_frame (B : Addr) (vs : List (BitVec 64)) :
    ∀ (m : Mem) (off : Nat), off + 8 * vs.length ≤ 2048 →
      Frame [⟨B + BitVec.ofNat 64 off, 8 * vs.length⟩] m (constMem m B vs off) := by
  induction vs with
  | nil => intro m off _; exact Frame.refl _ _
  | cons v vs ih =>
    intro m off h
    simp only [List.length_cons] at h
    have h1 : Frame [⟨B + BitVec.ofNat 64 off, 8 * (vs.length + 1)⟩] m
        (m.writeW (B + BitVec.ofNat 64 off) v) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) v (by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [])
    have h2 := ih (m.writeW (B + BitVec.ofNat 64 off) v) (off + 8) (by omega_using [h])
    refine h1.trans (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.sub B (by omega_using []) (by omega_using [])

theorem constMem_read (B : Addr) (vs : List (BitVec 64)) :
    ∀ (m : Mem) (off : Nat), off + 8 * vs.length ≤ 2048 → ∀ c < vs.length,
      (constMem m B vs off).readW (B + BitVec.ofNat 64 (off + 8 * c)) 64 = vs.getD c 0 := by
  induction vs with
  | nil => intro _ _ _ c hc; simp at hc
  | cons v vs ih =>
    intro m off h c hc
    simp only [List.length_cons] at h hc
    rcases c with _ | c
    · have hf := constMem_frame B vs (m.writeW (B + BitVec.ofNat 64 off) v) (off + 8) (by omega_using [h])
      simp only [constMem, Nat.mul_zero, Nat.add_zero, List.getD_cons_zero]
      rw [hf.readW (r := ⟨B + BitVec.ofNat 64 off, 8⟩) (Region.contains_self _ _) (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr
          exact Offset.disjoint B (Or.inl (Nat.le_refl _)) (by omega_using [h]) (by omega_using [h])) (by decide),
        Mem.readW_writeW_self64]
    · simp only [constMem, List.getD_cons_succ]
      rw [show off + 8 * (c + 1) = off + 8 + 8 * c by omega_using []]
      exact ih _ (off + 8) (by omega_using [h]) c (by omega_using [hc])

theorem storeConsts_wp (vs : List (BitVec 64)) :
    ∀ (off : Nat) (s : State) (Q : State → Prop), off % 8 = 0 → off + 8 * vs.length ≤ 2048 →
      (∀ c < vs.length, InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 (off + 8 * c)) 8) →
      (∀ t : State, t.mem = constMem s.mem (s.gpr .r5) vs off → t.rd = s.rd → t.wr = s.wr →
        (∀ r, r ≠ .r6 → t.gpr r = s.gpr r) → Q t) →
      WP isa (.block (storeConsts vs off)) s Q := by
  induction vs with
  | nil =>
    intro off s Q _ _ _ hQ
    exact WP.block_nil (hQ s rfl rfl rfl fun _ _ => rfl)
  | cons v vs ih =>
    intro off s Q hoff hlim hin hQ
    simp only [List.length_cons] at hlim
    rw [storeConsts, WP.block_append_iff, WP.block_append_iff]
    obtain ⟨s₁, run₁, d₁, o₁, m₁, rd₁, wr₁⟩ := movImm64_ok t0 v s
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have hb₁ : s₁.gpr .r5 = s.gpr .r5 := o₁ _ (by decide)
    let s₂ : State := { s₁ with mem := s₁.mem.writeW (s₁.gpr .r5 + BitVec.ofNat 64 off) (s₁.gpr t0) }
    refine WP.of_runBlock ⟨s₂, ?_, ?_⟩
    · have h0 := hin 0 (by simp)
      simp only [Nat.mul_zero, Nat.add_zero] at h0
      show runBlock isa [.store .d t0 .r5 off] s₁ = some s₂
      rw [runBlock_cons, exec_store_d (by decide) ⟨by omega_using [hlim], by omega_using [hoff]⟩ (by rw [hb₁, wr₁]; exact h0),
        runStep_some, runBlock_nil]
    · have hb₂ : s₂.gpr .r5 = s.gpr .r5 := hb₁
      refine ih (off + 8) s₂ Q (by omega_using [hoff]) (by omega_using [hlim]) (fun c hc => ?_)
        fun t hm hrd hwr hg => hQ t ?_ (hrd.trans rd₁) (hwr.trans wr₁) fun r h0 => ?_
      · rw [hb₂, show off + 8 + 8 * c = off + 8 * (c + 1) by omega_using []]
        exact wr₁ ▸ hin (c + 1) (by simp only [List.length_cons]; omega_using [hc])
      · rw [hm, hb₂]
        show constMem (s₁.mem.writeW (s₁.gpr .r5 + BitVec.ofNat 64 off) (s₁.gpr t0)) _ vs (off + 8) = _
        rw [hb₁, d₁, m₁]; rfl
      · exact (hg r h0).trans (o₁ r h0)

/-! ## The head -/

theorem roundConsts_length : roundConsts.length = 47 := by
  rw [roundConsts.lit_eq]; decide +kernel

/-- The constants fit the scratch buffer, by their number: `decide` on it would evaluate them. -/
theorem consts_fit : constOff + 8 * roundConsts.length ≤ 2048 := by
  rw [roundConsts_length]; decide

theorem consts_ready {s t : State} (hb : t.gpr .r5 = s.gpr .r5)
    (hm : t.mem = constMem s.mem (s.gpr .r5) roundConsts constOff) : ConstsAt t := by
  intro c hc
  rw [hm, hb, wordAddr, show 8 * (15 + c) = constOff + 8 * c by unfold constOff; omega_using []]
  exact constMem_read _ _ _ _ consts_fit c (by rw [roundConsts_length]; exact hc)

theorem consts_frame (s : State) :
    Frame [saveRegion s] s.mem (constMem s.mem (s.gpr .r5) roundConsts constOff) :=
  (constMem_frame _ _ _ _ consts_fit).sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, by
      rw [roundConsts_length]; exact Offset.sub_base _ (by decide)⟩

theorem consts_saved {original s t : State} (hs : Saved original s) (hb : t.gpr .r5 = s.gpr .r5)
    (hm : t.mem = constMem s.mem (s.gpr .r5) roundConsts constOff) : Saved original t := by
  intro i hi
  rw [hm, hb, ← hs i hi]
  exact (constMem_frame _ _ _ _ consts_fit).readW (r := ⟨s.gpr .r5 + BitVec.ofNat 64 (8 * i), 8⟩)
    (Region.contains_self _ _) (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq
      rw [roundConsts_length]
      exact Offset.disjoint _ (Or.inl (by unfold constOff; omega_using [hi])) (by omega_using [hi]) (by decide)) (by decide)

theorem ready_afterSave {keys : Nat → DesSchedule} {base : Addr} {s t : State}
    (hp : HeadPre keys base s) (hb : t.gpr .r5 = s.gpr .r5) (hkey : t.gpr .r3 = s.gpr .r3)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hc : ConstsAt t) (hf : Frame [saveRegion s] s.mem t.mem) :
    Ready keys base t := by
  refine ⟨hp.scratch.congr hb hb hrd hwr, hc, hkey.trans hp.pointer, ?_, ?_, ?_⟩
  · rw [hrd, hwr]; exact hp.read
  · rw [show spillRegion t = spillRegion s from
      congrArg (fun p => (⟨p + BitVec.ofNat 64 496, 16⟩ : Region)) hb]
    exact hp.separateWork
  · intro c hc d j hj
    have hmem := hf.readW (a := keyAddr (componentBase base c) d j) (w := 64)
      (r := ⟨keyAddr (componentBase base c) d j, 8⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.separateSave c hc d j hj)
      (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hp.values c hc d j hj)

theorem blockHead_ok (keys : Nat → DesSchedule) (base : Addr) (s : State)
    (hp : HeadPre keys base s) :
    WP isa (.block (blockSave ++ storeConsts roundConsts constOff ++ blockLoad)) s
      (HeadPost keys base s) := by
  rw [WP.block_append_iff, WP.block_append_iff]
  apply WP.mono (blockSave_ok s fun i hi => hp.saveWrite i (by omega_using [hi]))
  intro s₁ hs₁
  have hb₁ : s₁.gpr .r5 = s.gpr .r5 := congrFun hs₁.gpr .r5
  refine storeConsts_wp roundConsts constOff s₁ _ (by decide) (by rw [roundConsts_length]; decide)
    (fun c hc => by
      rw [hs₁.wr, hb₁, show constOff + 8 * c = 8 * (15 + c) by unfold constOff; omega_using []]
      exact hp.saveWrite _ (by rw [roundConsts_length] at hc; omega_using [hc])) ?_
  intro s₂ m₂ rd₂ wr₂ g₂
  have hb₂ : s₂.gpr .r5 = s₁.gpr .r5 := g₂ _ (by decide)
  have hframe₂ : Frame [saveRegion s] s.mem s₂.mem := by
    refine hs₁.frame.sub (fun r hr => ?_) |>.trans ?_
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · rw [m₂, show saveRegion s = saveRegion s₁ by simp only [saveRegion, hb₁]]
      exact consts_frame s₁
  have hready := ready_afterSave hp (hb₂.trans hb₁) ((g₂ _ (by decide)).trans (congrFun hs₁.gpr .r3))
    (rd₂.trans hs₁.rd) (wr₂.trans hs₁.wr) (consts_ready hb₂ m₂) hframe₂
  have hsaved₂ := consts_saved hs₁.saved hb₂ m₂
  have hread₂ : InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .r4) 8 := by
    rw [rd₂, wr₂, hs₁.rd, hs₁.wr, g₂ _ (by decide), hs₁.gpr]; exact hp.dataRead
  have hdata : Spec.TripleDes.blockAt s₂.mem (s₂.gpr .r4) =
      Spec.TripleDes.blockAt s.mem (s.gpr .r4) := by
    rw [g₂ _ (by decide), hs₁.gpr]
    exact VG.Proof.TripleDes.blockAt_eq_of_frame _ hframe₂
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.dataSeparate)
  obtain ⟨s₃, run₃, left₃, right₃, mem₃, rd₃, wr₃, regs₃⟩ := blockLoad_ok s₂ hread₂
  have hframe : Frame [spillRegion s₂] s₂.mem s₃.mem := by
    rw [mem₃]; exact Frame.refl _ _
  have hinput := congrArg (fun b => Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock b)) hdata
  apply WP.of_runBlock
  refine ⟨s₃, run₃, ?_, hready.congr (regs₃ .r5 (by decide)) (regs₃ .r3 (by decide)) rd₃ wr₃ hframe,
    ?_, rd₃.trans (rd₂.trans hs₁.rd), wr₃.trans (wr₂.trans hs₁.wr), ?_, ?_⟩
  · exact ⟨left₃.trans (congrArg (fun x : BitVec 64 => ((x >>> 32).setWidth 32).setWidth 64) hinput),
      right₃.trans (congrArg (fun x : BitVec 64 => (x.setWidth 32).setWidth 64) hinput)⟩
  · intro i hi
    rw [regs₃ .r5 (by decide), mem₃]
    exact hsaved₂ i hi
  · intro q hq
    have hne : q ≠ .r6 := by revert hq; decide +revert
    exact (regs₃ q hq).trans ((g₂ q hne).trans (congrFun hs₁.gpr q))
  · rw [mem₃]; exact hframe₂

end VG.Proof.TripleDes.PPC64LE

end

end

/-! ### `TripleDes.PPC64LE.Body`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (desCore)

/-- The word after the first `k` passes of the block. -/
def passesDone (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) :
    Nat → BitVec 64
  | 0 => x
  | k + 1 => desCore (keys (passOf direction (3 - k)).1) (passOf direction (3 - k)).2
      (passesDone keys direction x k)

def blockCore (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) : BitVec 64 :=
  match direction with
  | .encrypt => desCore (keys 2) .encrypt (desCore (keys 1) .decrypt (desCore (keys 0) .encrypt x))
  | .decrypt => desCore (keys 0) .decrypt (desCore (keys 1) .encrypt (desCore (keys 2) .decrypt x))

theorem blockCore_passesDone (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) :
    blockCore keys direction x = passesDone keys direction x 3 := by
  cases direction <;> rfl

/-- The loop's invariant, with `m` passes left. -/
structure BodyInv (keys : Nat → DesSchedule) (base : Addr) (direction : Direction)
    (x : BitVec 64) (origin : State) (m : Nat) (s : State) : Prop where
  pos : 1 ≤ m
  le : m ≤ 3
  passes : s.gpr .r19 = BitVec.ofNat 64 m
  word : WordState (passesDone keys direction x (3 - m)) s
  ready : Ready keys base s
  stable : Stable origin s

theorem blockBody_ok (keys : Nat → DesSchedule) (base : Addr) (s : State) (x : BitVec 64)
    (direction : Direction) (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (blockBody direction) s
      (fun t => WordState (blockCore keys direction x) t ∧ Ready keys base t ∧ Stable s t) := by
  let s₁ := s.write .r19 (BitVec.ofNat 64 3)
  have hregs : ∀ r, r ≠ .r19 → s₁.gpr r = s.gpr r := fun r h => gpr_write_of_ne _ _ h
  have hframe : Frame [spillRegion s] s.mem s₁.mem := Frame.refl _ _
  have hstable : Stable s s₁ := ⟨rfl, rfl,
    fun q hq => hregs q (by revert hq; cases q <;> decide), hframe⟩
  apply WP.seq
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · rw [runBlock_cons, imm, exec_li (by decide), runStep_some, runBlock_nil]
  refine WP.loop (M := isa) (BodyInv keys base direction x s) ?_ 3 s₁
    ⟨by decide, by decide, gpr_write_self _ _ _, ?_,
      hready.congr (hregs .r5 (by decide)) (hregs .r3 (by decide)) rfl rfl hframe, hstable⟩
  · rintro m t ⟨hpos, hle, hpasses, hw, hr, hst⟩
    refine WP.mono (pass_word_ok keys base t _ direction ⟨hpos, hle⟩ hr hw hpasses)
      fun u ⟨hwu, hru, hsu, hpu, hzu⟩ => ?_
    have hdone : desCore (keys (passOf direction m).1) (passOf direction m).2
        (passesDone keys direction x (3 - m)) = passesDone keys direction x (3 - (m - 1)) := by
      rw [show 3 - (m - 1) = 3 - m + 1 by omega_using [hpos, hle], passesDone, show 3 - (3 - m) = m by omega_using [hle]]
    rw [hdone] at hwu
    by_cases hlast : m = 1
    · subst m
      refine Or.inl ⟨by rw [hzu]; rfl, ?_, hru, hst.trans hsu⟩
      rw [blockCore_passesDone]
      exact hwu
    · refine Or.inr ⟨by rw [hzu]; simp [hlast], m - 1, by omega_using [hpos],
        ⟨by omega_using [hpos, hlast], by omega_using [hle], hpu, hwu, hru, hst.trans hsu⟩⟩
  · exact ⟨(hregs .r14 (by decide)).trans hword.left, (hregs .r15 (by decide)).trans hword.right⟩

end VG.Proof.TripleDes.PPC64LE

end

end

/-! ### `TripleDes.PPC64LE.Tail`, which only this module used -/

section

/-! ### `TripleDes.PPC64LE.Store`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

def packHalves : List Instr := [.rotr .d .r6 .r14 32, .logic .xor .r6 .r6 .r15]

theorem rotateRight_extend (l : BitVec 32) :
    (l.setWidth 64).rotateRight 32 = l.setWidth 64 <<< 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : j < 32
  · simp [h, hj]
  · simp [h, hj]

theorem packHalves_ok (s : State) (l r : BitVec 32)
    (hl : s.gpr .r14 = l.setWidth 64) (hr : s.gpr .r15 = r.setWidth 64) :
    ∃ s', runBlock isa packHalves s = some s' ∧
      s'.gpr .r6 = l ++ r ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q, q ≠ .r6 → s'.gpr q = s.gpr q) := by
  let s₁ := s.write .r6 ((s.gpr .r14).rotateRight 32)
  let s₂ := s₁.write .r6 (s₁.gpr .r6 ^^^ s₁.gpr .r15)
  refine ⟨s₂, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · rw [packHalves, runBlock_cons, exec_rotr_d (by decide), runStep_some, runBlock_cons,
      exec_logic, runStep_some, runBlock_nil]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false, hl, hr,
      rotateRight_extend]
    exact packHalves_shift l r
  · intro q hq
    simp only [s₂, s₁, gpr_write, hq, ite_false]

theorem final_preserves : loadKept.all (fun r =>
    (instrs finalPermutation.lit).all (fun op => dstOf op != some r)) = true := by
  decide +kernel

theorem writeData_ok (s : State) (hwrite : InRegions s.wr (s.gpr .r4) 8) :
    ∃ s', runBlock isa [.li .r7 0, .storeRev .d .r8 .r4 .r7] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r4) (rev64 (s.gpr .r8)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q, q ≠ .r7 → s'.gpr q = s.gpr q) := by
  let s₁ := s.write .r7 (BitVec.ofNat 64 0)
  have ha : s₁.gpr .r4 + s₁.gpr .r7 = s.gpr .r4 := by
    simp only [s₁, gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.add_zero]
  have hstore := exec_storeRev_d (s := s₁) (t := .r8) (a := .r4) (b := .r7) (by decide)
    (by rw [ha]; exact hwrite)
  rw [ha] at hstore
  refine ⟨{ s₁ with mem := s₁.mem.writeW (s.gpr .r4) (rev64 (s₁.gpr .r8)) }, by
    rw [runBlock_cons, exec_li (by decide), runStep_some, runBlock_cons, hstore, runStep_some,
      runBlock_nil], ?_, rfl, rfl, ?_⟩
  · change s.mem.writeW (s.gpr .r4) (rev64 (s₁.gpr .r8)) = _
    rw [show s₁.gpr .r8 = s.gpr .r8 from gpr_write_of_ne _ _ (by decide)]
  · intro q hq
    exact gpr_write_of_ne _ _ hq

theorem blockStore_ok (s : State) (l r : BitVec 32)
    (hl : s.gpr .r14 = l.setWidth 64) (hr : s.gpr .r15 = r.setWidth 64)
    (hwrite : InRegions s.wr (s.gpr .r4) 8) :
    ∃ s', runBlock isa blockStore s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r4)
        (rev64 (Spec.TripleDes.permute Spec.TripleDes.fp (l ++ r))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ loadKept, s'.gpr q = s.gpr q) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, regs₁⟩ := packHalves_ok s l r hl hr
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, mem₂, regs₂⟩ := final_raw_ok s₁
  have r4₁ : s₁.gpr .r4 = s.gpr .r4 := regs₁ .r4 (by decide)
  have r4₂ : s₂.gpr .r4 = s.gpr .r4 :=
    (regs₂ .r4 (List.all_eq_true.mp final_preserves .r4 (by decide))).trans r4₁
  obtain ⟨s₃, run₃, mem₃, rd₃, wr₃, regs₃⟩ := writeData_ok s₂ (by
    rw [r4₂, wr₂, wr₁]; exact hwrite)
  have hhead := runAppend_some _ _ _ _ _ run₁ run₂
  have htail := runAppend_some _ _ _ _ _ hhead run₃
  have hcode : blockStore =
      (packHalves ++ permuteCode Spec.TripleDes.fp 64 .r8 .r6 .r9 .r10) ++
      ([.li .r7 0, .storeRev .d .r8 .r4 .r7] : List Instr) := rfl
  refine ⟨s₃, (congrArg (fun is => runBlock isa is s) hcode).trans htail, ?_,
    rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_⟩
  · rw [mem₃, mem₂, mem₁, r4₂, word₂, word₁]
  · intro q hq
    have hno := List.all_eq_true.mp final_preserves q hq
    have hne : q ≠ .r6 ∧ q ≠ .r7 := by clear hno; revert hq; cases q <;> decide
    exact (regs₃ q hne.2).trans ((regs₂ q hno).trans (regs₁ q hne.1))

end VG.Proof.TripleDes.PPC64LE

end

end


@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

structure TailPost (original origin : State) (x : BitVec 64) (s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (origin.gpr .r4) =
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp x)
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ loadKept, s.gpr q = origin.gpr q
  frame : Frame [⟨origin.gpr .r4, 8⟩] origin.mem s.mem

theorem blockTail_ok (original s : State) (x : BitVec 64)
    (hword : WordState x s) (hsaved : Saved original s)
    (hsavedRead : ∀ i < 15, InRegions (s.rd ++ s.wr) (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8)
    (hwrite : InRegions s.wr (s.gpr .r4) 8)
    (hsep : (⟨s.gpr .r4, 8⟩ : Region).Disjoint ⟨s.gpr .r5, 120⟩) :
    WP isa (.block (blockStore ++ blockRestore)) s (TailPost original s x) := by
  obtain ⟨s₁, run₁, mem₁, rd₁, wr₁, regs₁⟩ :=
    blockStore_ok s ((x >>> 32).setWidth 32) (x.setWidth 32) hword.left hword.right hwrite
  have hframe₁ : Frame [⟨s.gpr .r4, 8⟩] s.mem s₁.mem := by
    rw [mem₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have saved₁ : Saved original s₁ := by
    intro i hi
    rw [regs₁ .r5 (by decide)]
    refine (hframe₁.readW (r := ⟨s.gpr .r5 + BitVec.ofNat 64 (8 * i), 8⟩)
      (Region.contains_self _ _) (fun q hq => ?_) (by decide)).trans (hsaved i hi)
    obtain rfl := List.mem_singleton.mp hq
    exact (hsep.sub_right (Offset.sub_base _ (by omega_using [hi]))).symm
  have savedRead₁ : ∀ i < 15, InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [rd₁, wr₁, regs₁ .r5 (by decide)]
    exact hsavedRead
  apply WP.block_append
  apply WP.of_runBlock
  refine ⟨s₁, run₁, ?_⟩
  apply WP.mono (blockRestore_ok original s₁ saved₁ savedRead₁)
  intro s₂ hs₂
  have hregs₂ : ∀ q ∈ loadKept, s₂.gpr q = s.gpr q := by
    intro q hq
    have hn : q ∉ savedRegs := by revert hq; cases q <;> decide
    exact (hs₂.keep.gpr hn).trans (regs₁ q hq)
  refine ⟨?_, hs₂.saved, hs₂.keep.2.1.trans rd₁, hs₂.keep.2.2.trans wr₁, hregs₂, ?_⟩
  · rw [hs₂.mem, mem₁, VG.Proof.TripleDes.halves_append x]
    exact blockAt_writeW s.mem (s.gpr .r4) (Spec.TripleDes.permute Spec.TripleDes.fp x)
  · rw [hs₂.mem]; exact hframe₁

end VG.Proof.TripleDes.PPC64LE

end

end


@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction Schedule)

def blockResult (keys : Schedule) (direction : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.Block :=
  match direction with
  | .encrypt => Spec.TripleDes.encryptBlock keys b
  | .decrypt => Spec.TripleDes.decryptBlock keys b

theorem blockResult_core (keys : Schedule) (direction : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp
      (blockCore (Spec.TripleDes.componentSchedule keys) direction
        (Spec.TripleDes.permute Spec.TripleDes.ip (Spec.TripleDes.decodeBlock b)))) =
      blockResult keys direction b := by
  cases direction
  · exact (VG.Proof.TripleDes.encryptBlock_eq_cores keys b).symm
  · exact (VG.Proof.TripleDes.decryptBlock_eq_cores keys b).symm

def blockRegions (s : State) : List Region := [⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 512⟩]

structure BlockPost (keys : Schedule) (direction : Direction) (original s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (original.gpr .r4) =
    blockResult keys direction (Spec.TripleDes.blockAt original.mem (original.gpr .r4))
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  regs : ∀ q ∈ loadKept, s.gpr q = original.gpr q
  frame : Frame (blockRegions original) original.mem s.mem

theorem block_ok (keys : Schedule) (base : Addr) (direction : Direction) (s : State)
    (hp : HeadPre (Spec.TripleDes.componentSchedule keys) base s)
    (hwrite : InRegions s.wr (s.gpr .r4) 8) :
    WP isa (block direction) s (BlockPost keys direction s) := by
  apply WP.seq
  apply WP.mono (blockHead_ok (Spec.TripleDes.componentSchedule keys) base s hp)
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (blockBody_ok (Spec.TripleDes.componentSchedule keys) base s₁ _ direction hs₁.ready hs₁.word)
  intro s₂ hs₂
  have hregs₂ : ∀ q ∈ loadKept, s₂.gpr q = s.gpr q := by
    intro q hq
    exact (hs₂.2.2.regs q hq).trans (hs₁.regs q hq)
  have saved₂ := hs₁.saved.congr (hs₂.2.2.regs .r5 (by decide)) hs₂.2.2.frame
  have savedRead₂ : ∀ i < 15, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [hs₂.2.2.rd, hs₂.2.2.wr, hs₁.rd, hs₁.wr, hregs₂ .r5 (by decide)]
    exact hp.saveRead
  have hwrite₂ : InRegions s₂.wr (s₂.gpr .r4) 8 := by
    rw [hs₂.2.2.wr, hs₁.wr, hregs₂ .r4 (by decide)]
    exact hwrite
  have hsep₂ : (⟨s₂.gpr .r4, 8⟩ : Region).Disjoint ⟨s₂.gpr .r5, 120⟩ := by
    rw [hregs₂ .r4 (by decide), hregs₂ .r5 (by decide)]
    exact hp.dataSeparate.sub_right (Region.sub_prefix (by decide))
  apply WP.mono (blockTail_ok s s₂ _ hs₂.1 saved₂ savedRead₂ hwrite₂ hsep₂)
  intro s₃ hs₃
  refine ⟨?_, hs₃.saved, hs₃.rd.trans (hs₂.2.2.rd.trans hs₁.rd),
    hs₃.wr.trans (hs₂.2.2.wr.trans hs₁.wr),
    fun q hq => (hs₃.regs q hq).trans (hregs₂ q hq), ?_⟩
  · have hresult := hs₃.result
    rw [hregs₂ .r4 (by decide)] at hresult
    exact hresult.trans (blockResult_core keys direction _)
  · have hf₁ : Frame (blockRegions s) s.mem s₁.mem := hs₁.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨s.gpr .r5, 512⟩, by simp [blockRegions], Region.sub_prefix (by decide)⟩)
    have hf₂ : Frame (blockRegions s) s₁.mem s₂.mem := hs₂.2.2.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨⟨s.gpr .r5, 512⟩, by simp [blockRegions], ?_⟩
      have hbase := hs₁.regs .r5 (by decide)
      change Region.Sub ⟨s₁.gpr .r5 + BitVec.ofNat 64 496, 16⟩ ⟨s.gpr .r5, 512⟩
      rw [hbase]
      exact Offset.sub_base _ (by decide))
    have hf₃ : Frame (blockRegions s) s₂.mem s₃.mem := hs₃.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      rw [hregs₂ .r4 (by decide)]
      exact ⟨⟨s.gpr .r4, 8⟩, by simp [blockRegions], fun _ h => h⟩)
    exact hf₁.trans (hf₂.trans hf₃)

end VG.Proof.TripleDes.PPC64LE

end

end

/-! ### `TripleDes.PPC64LE.Pre`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction)

def blockContract (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 384⟩
    let data : Region := ⟨s.gpr .r4, 8⟩
    let scratch : Region := ⟨s.gpr .r5, 512⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch
  post s s' := Spec.TripleDes.blockAt s'.mem (s.gpr .r4) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3)) d (Spec.TripleDes.blockAt s.mem (s.gpr .r4))
  pub := PublicRegs [.r3, .r4, .r5]

def selectedRound (d : Direction) (j : Nat) : Nat := if d = .encrypt then j else 15 - j

theorem selectedRound_bound (d : Direction) (j : Nat) (hj : j < 16) : selectedRound d j < 16 := by
  cases d <;> simp only [selectedRound, reduceCtorEq, ite_true, ite_false] <;> omega_arith

theorem keyAddr_component (base : Addr) (c : Nat) (d : Direction) (j : Nat) :
    keyAddr (componentBase base c) d j = base + BitVec.ofNat 64 (8 * (16 * c + selectedRound d j)) := by
  unfold keyAddr componentBase selectedRound
  rw [Offset.add_ofNat_add_ofNat]
  exact congrArg (fun n => base + BitVec.ofNat 64 n) (by omega_using [])

/-- The block function's precondition, from its 512 bytes of scratch at
`x2` writable, the schedule at `x0` readable and the block at `x1`
writable, neither in the scratch. -/
theorem headPre_of (s : State)
    (scratchWrites : ∀ i < 64, InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8)
    (keyReads : ∀ i < 48, InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (8 * i)) 8)
    (dataWrite : InRegions s.wr (s.gpr .r4) 8)
    (keySep : Region.Disjoint ⟨s.gpr .r3, 384⟩ ⟨s.gpr .r5, 512⟩)
    (dataSep : Region.Disjoint ⟨s.gpr .r4, 8⟩ ⟨s.gpr .r5, 512⟩) :
    HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3)))
      (s.gpr .r3) s := by
  have inRd : ∀ {a n}, InRegions s.wr a n → InRegions (s.rd ++ s.wr) a n := fun ⟨r, h1, h2⟩ =>
    ⟨r, List.mem_append_right _ h1, h2⟩
  have scratch : Ok scratchCfg s := by
    refine ⟨scratchWrites, ?_, by decide, ?_⟩
    · intro k hk; change k < 0 at hk; omega
    · intro k hk j hj; change j < 0 at hj; omega
  have keySub : ∀ c < 3, ∀ direction : Direction, ∀ j < 16,
      Region.Sub ⟨keyAddr (componentBase (s.gpr .r3) c) direction j, 8⟩ ⟨s.gpr .r3, 384⟩ := by
    intro c hc direction j hj
    rw [keyAddr_component]
    have hindex := selectedRound_bound direction j hj
    exact Offset.sub_base _ (by omega_using [hc, hindex])
  have workSub : Region.Sub (spillRegion s) ⟨s.gpr .r5, 512⟩ := Offset.sub_base _ (by decide)
  have saveSub : Region.Sub (saveRegion s) ⟨s.gpr .r5, 512⟩ := Region.sub_prefix (by decide)
  refine ⟨scratch, rfl, (fun i hi => inRd (scratchWrites i (by omega_using [hi]))),
    (fun i hi => scratchWrites i (by omega_using [hi])), inRd dataWrite, dataSep.sub_right saveSub, ?_, ?_, ?_, ?_⟩
  · intro c hc direction j hj
    rw [keyAddr_component]
    exact keyReads _ (by have := selectedRound_bound direction j hj; omega_using [hc, this])
  · intro c hc direction j hj
    exact (keySep.sub_left (keySub c hc direction j hj)).sub_right workSub
  · intro c hc direction j hj
    exact (keySep.sub_left (keySub c hc direction j hj)).sub_right saveSub
  · intro c hc direction j hj
    rw [keyAddr_component]
    exact (VG.Proof.TripleDes.componentSchedule_readW s.mem (s.gpr .r3) c
      (selectedRound direction j) hc (selectedRound_bound direction j hj)).symm

theorem headPre_of_contract (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3)))
      (s.gpr .r3) s := by
  obtain ⟨hrd, hwr, keySep, dataSep⟩ := hs
  refine headPre_of s (fun i hi => ?_) (fun i hi => ?_) ?_ keySep dataSep
  · rw [hwr]
    exact ⟨⟨s.gpr .r5, 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [hrd, hwr]
    exact ⟨⟨s.gpr .r3, 384⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [hwr]
    exact ⟨⟨s.gpr .r4, 8⟩, by simp, Region.contains_self _ _⟩


end VG.Proof.TripleDes.PPC64LE

end

end


/-! # A call of the block function from the modes and CMAC on PPC64LE -/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Ecb

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

/-- The argument registers the block functions keep. -/
def kept : List Reg := [.r3, .r4, .r5]

def callContract (d : Spec.TripleDes.Direction) : Contract isa :=
  { blockContract d with
    post := fun s s' => (blockContract d).post s s' ∧ ∀ r ∈ kept, s'.gpr r = s.gpr r }

theorem block_correct' (d : Spec.TripleDes.Direction) (s : State) (hs : (callContract d).pre s) :
    ∃ t s', Exec isa (block d) s t s' ∧ abiPreserved s s' ∧ (callContract d).post s s' := by
  have hp := headPre_of_contract d s hs
  have hwrite : InRegions s.wr (s.gpr .r4) 8 := by
    rw [hs.2.1]
    exact ⟨⟨s.gpr .r4, 8⟩, by simp, Region.contains_self _ _⟩
  obtain ⟨t, s', he, post⟩ := block_ok (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3))
    (s.gpr .r3) d s hp hwrite
  have hlr : s'.lr = s.lr := by
    cases d
    · exact Exec.lr (c := encryptBlock) he (by lit_decide) (by lit_decide)
    · exact Exec.lr (c := decryptBlock) he (by lit_decide) (by lit_decide)
  refine ⟨t, s', he, ⟨?_, Exec.sp he, hlr⟩, post.result, ?_⟩
  · intro r hr
    have hkeep : ∀ q ∈ preserved, q ∈ savedRegs ∨ q ∈ loadKept := by decide
    rcases hkeep r hr with h | h
    · exact post.saved r h
    · exact post.regs r h
  · intro r hr
    exact post.regs r (by revert hr; decide +revert)

/-- The name of the block function of the direction `d`. -/
def blockName : Spec.TripleDes.Direction → String
  | .encrypt => "vg_triple_des_encrypt_block"
  | .decrypt => "vg_triple_des_decrypt_block"

theorem blockCall_eq (d : Spec.TripleDes.Direction) :
    Impl.TripleDes.PPC64LE.Ecb.blockCall d = .call (blockName d) (block d) := by cases d <;> rfl

structure CallPre (s : State) : Prop where
  reads : Covers [⟨s.gpr .r3, 384⟩, ⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 512⟩] (s.rd ++ s.wr)
  writes : Covers [⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 512⟩] s.wr
  keyScratch : (Region.mk (s.gpr .r3) 384).Disjoint ⟨s.gpr .r5, 512⟩
  dataScratch : (Region.mk (s.gpr .r4) 8).Disjoint ⟨s.gpr .r5, 512⟩

structure CallPost (d : Spec.TripleDes.Direction) (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 512⟩] s.mem s'.mem
  output : Spec.TripleDes.blockAt s'.mem (s.gpr .r4) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3)) d
      (Spec.TripleDes.blockAt s.mem (s.gpr .r4))

theorem call_ok (d : Spec.TripleDes.Direction) (s : State) (hp : CallPre s) :
    WP isa (Impl.TripleDes.PPC64LE.Ecb.blockCall d) s (CallPost d s) := by
  rw [blockCall_eq]
  have c3 := State.callEntry_gpr s (r := .r3) (by decide)
  have c4 := State.callEntry_gpr s (r := .r4) (by decide)
  have c5 := State.callEntry_gpr s (r := .r5) (by decide)
  refine WP.call (k := callContract d) (block_correct' d)
    (rd := [⟨s.gpr .r3, 384⟩])
    (wr := [⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 512⟩])
    ?_ hp.reads hp.writes ?_ (by cases d <;> rfl)
  · simp only [callContract, blockContract, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c3, c4, c5]
    exact ⟨trivial, trivial, hp.keyScratch, hp.dataScratch⟩
  · intro s' rd wr _ frame callee _ out
    refine ⟨?_, callee, rd, wr, frame, ?_⟩
    · intro r hr
      have h := out.2 r hr
      have hl : ∀ r ∈ kept, r ∉ linkRegs := by decide
      have hl := hl r hr
      simp only [State.withRegions_gpr, State.callEntry_gpr _ hl] at h
      exact h
    · have h := out.1
      change Spec.TripleDes.blockAt s'.mem _ = blockResult _ d _ at h
      simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4] at h
      exact h

end VG.Proof.TripleDes.PPC64LE.Ecb
