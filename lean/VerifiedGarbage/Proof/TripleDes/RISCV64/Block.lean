module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.FeistelLit
public import VerifiedGarbage.Proof.Framework.RISCV64.Linear
public import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.Proof.TripleDes.Pieces
import VerifiedGarbage.Proof.TripleDes.Round
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Block
public import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.TripleDes.Word
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.TripleDes.RISCV64.Bytes
import VerifiedGarbage.Proof.TripleDes.RISCV64.Permutation
import VerifiedGarbage.Proof.TripleDes.Schedule
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Feistel
public import VerifiedGarbage.Proof.Framework.Semantics

/-! ### `TripleDes.RISCV64.Body`, which only this module used -/

section

/-! ### `TripleDes.RISCV64.Pass`, which only this module used -/

section

/-! ### `TripleDes.RISCV64.Loop`, which only this module used -/

section

/-! ### `TripleDes.RISCV64.RoundBody`, which only this module used -/

section

/-! ### `TripleDes.RISCV64.FeistelRun`, which only this module used -/

section

/-! ### `TripleDes.RISCV64.Feistel`, which only this module used -/

section

/-!
# The round function on RISC-V

`feistel` is checked in three parts by evaluation. Its first part
(`feistelIn`) and its last (`feistelOut`) are linear (the lane domain,
`Framework/RISCV64/Linear.lean`): the first forms each lane's six input bits,
bits of R and of the round key, in `m 0`–`m 5`; the last XORs each output bit
into L at its destination under P. The middle part (`feistelTree`) is checked
over the position-table domain (`Framework/Bitslice/PosTable.lean`), on all
64 inputs of every lane at once: each lane's result is its table
(`laneTables`). The words of constants are external words of the frame.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.TripleDes.RISCV64
open VG.Proof.TripleDes (inputTable)

/-- The frame's first 70 words, read only: slots 15–69 hold the constants. -/
def feiCfg : Cfg := { base := sb, slots := 0, ext := sb, exts := 15 + 55 }

/-- External word `15 + c` is the constant `c`. -/
def constKs : List (Nat × BitVec 64) := (List.range 55).map fun c => (15 + c, roundConsts.getD c 0)

/-- R (input word 0) and the round key (input word 1). -/
def inRegs : List (Reg × Nat) := [(.a2, 0), (.t4, 1)]

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
def outRegs : List (Reg × Nat) := [(.t0, 0), (.a1, 1)]

/-- The low lane of the output that P moves to bit `q < 32` of L. -/
def pSrc (q : Nat) : Nat :=
  let t := 32 - Spec.TripleDes.p.getD (31 - q) 1
  8 * (t / 4) + outLane (t / 4) (t % 4)

def outBits (q : Nat) : List Nat := [64 + q] ++ (if q < 32 then [pSrc q, pSrc q + 4] else [])

theorem feistelOut_check :
    check (lanes 64 7) feiCfg (kExt constKs) (instrs feistelOut.lit) (linEnv outRegs)
      (linPost 7 [(.a1, outBits)]) = true := by
  lit_decide

/-- The input bits, the same table at every position. -/
def treeEnv : Env Nat :=
  { reg := fun r => ((List.range 6).find? (fun k => m k == r)).map
      fun k => .v (everywhere 64 64 (inputTable k)),
    slot := fun _ => none }

def treeExt (j : Nat) : Option Nat :=
  if 15 ≤ j then some (spreadConst 64 64 (roundConsts.getD (j - 15) 0).toNat) else none

def treePost (e : Env Nat) : Bool := word (e.reg .t0) == some laneTables

theorem feistelTree_check :
    check (posTables 64 64) feiCfg treeExt (instrs feistelTree.lit) treeEnv treePost = true := by
  lit_decide

end VG.Proof.TripleDes.RISCV64

end

end


/-!
# The round function on RISC-V, on the machine

The three checks of `Feistel.lean` on the machine, and their composition,
`feistel_ok`: `feistel` XORs the round function of R and the round key at
`a3` into L, keeps memory and the registers `feistelKept`.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.RegUpd VG.Bitslice VG.Impl.TripleDes.RISCV64
open VG.Proof.TripleDes (inputTable roundChunk roundChunk_bit)

/-- The words of constants in the frame at `sb`, in slots 15–69. -/
def ConstsAt (s : State) : Prop :=
  ∀ c < 55, s.mem.readW (wordAddr (s.gpr sb) (15 + c)) 64 = roundConsts.getD c 0

/-- What the round function needs of the frame: its first 70 words, aligned
and writable (so readable), with the constants. -/
structure FeiReady (s : State) : Prop where
  al : (s.gpr sb).toNat % 8 = 0
  wr : ∀ o < 70, InRegions s.wr (wordAddr (s.gpr sb) o) 8
  consts : ConstsAt s

theorem FeiReady.congr {s t : State} (h : FeiReady s) (hb : t.gpr sb = s.gpr sb)
    (hwr : t.wr = s.wr) (hm : t.mem = s.mem) : FeiReady t :=
  ⟨by rw [hb]; exact h.al, by rw [hb, hwr]; exact h.wr, by
    intro c hc; rw [hb, hm]; exact h.consts c hc⟩

theorem feiCfg_ok {s : State} (h : FeiReady s) : Ok feiCfg s where
  slotIn k hk := by simp [feiCfg] at hk
  extIn k hk := by
    obtain ⟨r, hr, hc⟩ := h.wr k hk
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  baseAl h0 := by simp [feiCfg] at h0
  extAl _ := h.al
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

/-! ## The three parts -/

/-- R and the round key, as input words. -/
def inWords (s : State) (i : Nat) : BitVec 64 := if i = 0 then s.gpr .a2 else s.gpr .t4

theorem feistelIn_ok (s : State) (h : FeiReady s) :
    ∃ s', runBlock isa (ePart ++ kPart ++ maskPart) s = some s' ∧
      (∀ k < 6, ∀ p < 64, (s'.gpr (m k)).getLsbD p = xorBits (inWords s) (maskBits k p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((ePart ++ kPart ++ maskPart).all fun i => dst i != some r) = true →
        s'.gpr r = s.gpr r) := by
  have hchk := feistelIn_check
  rw [← feistelIn.lit_eq] at hchk
  obtain ⟨s', hs', out, rd, wr, sp, keep, frame⟩ := linear_ok hchk (feiCfg_ok h) (inWords s)
    (fun r i hri => by
      simp only [inRegs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (kExt_rel (constKs_rel h.consts))
  exact ⟨s', hs', fun k hk p hp => out (m k) (maskBits k)
    (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩) p hp, rd, wr, sp,
    mem_of_frame_fei frame, keep⟩

/-- Lane `p`'s six input bits. -/
def laneInput (s : State) (p : Nat) : BitVec 6 := ofBits 6 fun k => (s.gpr (m k)).getLsbD p

theorem testBit_laneTables {p c : Nat} (hp : p < 64) (hc : c < 64) :
    laneTables.testBit (64 * p + c) = laneBit p c := by
  rw [laneTables, testBit_blocks (fun p => tableOf_lt _ 64) 64 p c hc, testBit_tableOf]
  simp [hp, hc]

theorem feistelTree_ok (s : State) (h : FeiReady s) :
    ∃ s', runBlock isa treePart s = some s' ∧
      (∀ p < 64, (s'.gpr .t0).getLsbD p = laneBit p (laneInput s p).toNat) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, (treePart.all fun i => dst i != some r) = true → s'.gpr r = s.gpr r) := by
  have hchk := feistelTree_check
  rw [← feistelTree.lit_eq] at hchk
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  let cs : Nat → Nat := fun p => (laneInput s p).toNat
  have hcs : ∀ p < 64, cs p < 64 := fun p _ => (laneInput s p).isLt
  have hrel : Rel (PosRel 64 cs) feiCfg treeExt treeEnv s := by
    refine ⟨fun r a hr => ?_, fun _ _ hk _ => by simp [feiCfg] at hk, fun j a hj hja => ?_⟩
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
        have hc : j - 15 < 55 := by simp only [feiCfg] at hj; omega_using [hj]
        have hw := h.consts (j - 15) hc
        rw [show 15 + (j - 15) = j by omega_arith] at hw
        rw [testBit_spreadConst hp (hcs p hp), BitVec.testBit_toNat]
        exact congrArg (fun x : BitVec 64 => x.getLsbD p) hw.symm
      · cases hja
  obtain ⟨s', hs', p₀⟩ := run (posTables_sound hcs) posRel_fun (feiCfg_ok h) hrel he
  have hout : e'.reg .t0 = some (.v laneTables) := by
    simp only [treePost, beq_iff_eq] at hpost
    cases hr : e'.reg .t0 with
    | none => rw [hr] at hpost; cases hpost
    | some v => cases v <;> rw [hr] at hpost <;> simp_all [word]
  refine ⟨s', hs', fun p hp => ?_, p₀.rd, p₀.wr, p₀.sp, mem_of_frame_fei p₀.frame,
    fun r hr => p₀.other r (by
      intro hw
      rw [show instrs (Code.block treePart) = treePart from rfl, hr] at hw
      cases hw)⟩
  have hb := p₀.rel.reg .t0 _ hout p hp
  rw [← hb, testBit_laneTables hp (hcs p hp)]

/-- The lanes' tables and L, as input words. -/
def outWords (s : State) (i : Nat) : BitVec 64 := if i = 0 then s.gpr .t0 else s.gpr .a1

theorem feistelOut_ok (s : State) (h : FeiReady s) :
    ∃ s', runBlock isa pPart s = some s' ∧
      (∀ q < 64, (s'.gpr .a1).getLsbD q = xorBits (outWords s) (outBits q)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, (pPart.all fun i => dst i != some r) = true → s'.gpr r = s.gpr r) := by
  have hchk := feistelOut_check
  rw [← feistelOut.lit_eq] at hchk
  obtain ⟨s', hs', out, rd, wr, sp, keep, frame⟩ := linear_ok hchk (feiCfg_ok h) (outWords s)
    (fun r i hri => by
      simp only [outRegs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (kExt_rel (constKs_rel h.consts))
  exact ⟨s', hs', fun q hq => out .a1 outBits (by simp) q hq, rd, wr, sp,
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
    laneInput s' p = roundChunk (7 - p / 8) ((s.gpr .a2).setWidth 32) ((s.gpr .t4).setWidth 48) := by
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
  [.ra, .s0, .s1, .s2, .s3, .s4, .s11, .a0, .a2, .a3, .a4, .a5, .a6, .a7]

theorem feistelIn_keeps : (.a1 :: feistelKept).all
    (fun r => (instrs feistelIn.lit).all fun i => dst i != some r) = true := by
  decide +kernel

theorem feistelTree_keeps : (.a1 :: feistelKept).all
    (fun r => (instrs feistelTree.lit).all fun i => dst i != some r) = true := by
  decide +kernel

theorem feistelOut_keeps : feistelKept.all
    (fun r => (instrs feistelOut.lit).all fun i => dst i != some r) = true := by
  decide +kernel

theorem feistelIn_keep {r : Reg} (hr : r ∈ .a1 :: feistelKept) :
    ((ePart ++ kPart ++ maskPart).all fun i => dst i != some r) = true := by
  have h := List.all_eq_true.mp feistelIn_keeps r hr
  rw [← feistelIn.lit_eq] at h
  exact h

theorem feistelTree_keep {r : Reg} (hr : r ∈ .a1 :: feistelKept) :
    (treePart.all fun i => dst i != some r) = true := by
  have h := List.all_eq_true.mp feistelTree_keeps r hr
  rw [← feistelTree.lit_eq] at h
  exact h

theorem feistelOut_keep {r : Reg} (hr : r ∈ feistelKept) :
    (pPart.all fun i => dst i != some r) = true := by
  have h := List.all_eq_true.mp feistelOut_keeps r hr
  rw [← feistelOut.lit_eq] at h
  exact h

theorem runBlock_append' (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

/-- The round function: L XORed with the round function of R and the round
key at `a3`. -/
theorem feistel_ok (s : State) (h : FeiReady s) (l r : BitVec 32)
    (hl : s.gpr .a1 = l.setWidth 64) (hr : s.gpr .a2 = r.setWidth 64)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .a3) 8) (hal : (s.gpr .a3).toNat % 8 = 0) :
    ∃ s', runBlock isa feistel s = some s' ∧
      s'.gpr .a1 = (l ^^^ Spec.TripleDes.roundFunction r
        ((s.mem.readW (s.gpr .a3) 64).setWidth 48)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ q ∈ feistelKept, s'.gpr q = s.gpr q) := by
  have ha3 : s.gpr .a3 + BitVec.ofNat 64 0 = s.gpr .a3 := BitVec.add_zero _
  let s₀ := s.write .t4 (s.mem.readW (s.gpr .a3) 64)
  have run₀ : runBlock isa keyLoad s = some s₀ := by
    rw [keyLoad, runBlock_cons, exec_load_d (by decide) (by rw [ha3]; exact hal)
      (by rw [ha3]; exact hread), ha3, runStep_some, runBlock_nil]
  have hready₀ : FeiReady s₀ := h.congr (gpr_write_of_ne _ _ (by decide)) rfl rfl
  obtain ⟨s₁, run₁, masks, rd₁, wr₁, sp₁, mem₁, keep₁⟩ := feistelIn_ok s₀ hready₀
  have hready₁ := hready₀.congr (keep₁ sb (feistelIn_keep (by decide))) wr₁ mem₁
  obtain ⟨s₂, run₂, tabs, rd₂, wr₂, sp₂, mem₂, keep₂⟩ := feistelTree_ok s₁ hready₁
  have hready₂ := hready₁.congr (keep₂ sb (feistelTree_keep (by decide))) wr₂ mem₂
  obtain ⟨s₃, run₃, outs, rd₃, wr₃, sp₃, mem₃, keep₃⟩ := feistelOut_ok s₂ hready₂
  have hL₂ : s₂.gpr .a1 = l.setWidth 64 := by
    rw [keep₂ .a1 (feistelTree_keep (by decide)), keep₁ .a1 (feistelIn_keep (by decide)),
      gpr_write_of_ne _ _ (by decide), hl]
  have hR₀ : (s₀.gpr .a2).setWidth 32 = r := by
    rw [gpr_write_of_ne _ _ (by decide), hr]; simp
  have hK₀ : s₀.gpr .t4 = s.mem.readW (s.gpr .a3) 64 := gpr_write_self _ _ _
  refine ⟨s₃, ?_, ?_, rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁),
    sp₃.trans (sp₂.trans sp₁), mem₃.trans (mem₂.trans mem₁), fun q hq => ?_⟩
  · rw [feistel, runBlock_append', runBlock_append', runBlock_append', run₀, Option.bind_some,
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
  · have hA : q ∈ .a1 :: feistelKept := List.mem_cons_of_mem _ hq
    have hne : q ≠ .t4 := by revert hq; cases q <;> decide
    rw [keep₃ q (feistelOut_keep hq), keep₂ q (feistelTree_keep hA), keep₁ q (feistelIn_keep hA),
      gpr_write_of_ne _ _ hne]

end VG.Proof.TripleDes.RISCV64

end

end


/-!
# A round

`roundBody_ok`: the round function (`feistel_ok`) and the half swap, the
standard DES round; `roundStep_ok`: with the next key and the round counted.
Neither writes memory.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.RegUpd VG.Impl.TripleDes.RISCV64

theorem runBoxes_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) :=
  runBlock_append' a b s

/-- The registers the half swap keeps. -/
def roundOuterKept : List Reg :=
  [.ra, .s0, .s1, .s2, .s3, .s4, .s11, .a0, kp, cnt, kstep, passes]

theorem swapHalves_ok (s : State) :
    ∃ s', runBlock isa swapHalves s = some s' ∧
      s'.gpr lReg = s.gpr rReg ∧ s'.gpr rReg = s.gpr lReg ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ q ∈ roundOuterKept, s'.gpr q = s.gpr q) := by
  let s₁ := s.write .t0 (s.gpr lReg + BitVec.ofInt 64 0)
  let s₂ := s₁.write lReg (s₁.gpr rReg + BitVec.ofInt 64 0)
  let s₃ := s₂.write rReg (s₂.gpr .t0 + BitVec.ofInt 64 0)
  refine ⟨s₃, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · rw [swapHalves, movR, movR, movR, runBlock_cons, exec_addi (by decide), runStep_some,
      runBlock_cons, exec_addi (by decide), runStep_some, runBlock_cons, exec_addi (by decide),
      runStep_some, runBlock_nil]
  · simp only [s₃, s₂, s₁, gpr_write, lReg, rReg, reduceCtorEq, ite_true, ite_false,
      BitVec.ofInt_ofNat, BitVec.add_zero]
  · simp only [s₃, s₂, s₁, gpr_write, lReg, rReg, reduceCtorEq, ite_true, ite_false,
      BitVec.ofInt_ofNat, BitVec.add_zero]
  · intro q hq
    have hne : q ≠ .t0 ∧ q ≠ lReg ∧ q ≠ rReg := by revert hq; cases q <;> decide
    simp only [s₃, s₂, s₁, gpr_write, hne.1, hne.2.1, hne.2.2, ite_false]

/-- One full Feistel round: the round function and the half swap. -/
theorem roundBody_ok (s : State) (l r : BitVec 32) (k : BitVec 64)
    (hl : s.gpr lReg = l.setWidth 64) (hr : s.gpr rReg = r.setWidth 64)
    (hk : s.mem.readW (s.gpr kp) 64 = k) (hready : FeiReady s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr kp) 8) (hal : (s.gpr kp).toNat % 8 = 0) :
    ∃ s', runBlock isa roundBody s = some s' ∧
      s'.gpr lReg = r.setWidth 64 ∧
      s'.gpr rReg = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ q ∈ roundOuterKept, s'.gpr q = s.gpr q) := by
  obtain ⟨s₁, run₁, value, rd₁, wr₁, sp₁, mem₁, keep₁⟩ :=
    feistel_ok s hready l r hl hr hread hal
  obtain ⟨s₂, run₂, left, right, rd₂, wr₂, sp₂, mem₂, keep₂⟩ := swapHalves_ok s₁
  refine ⟨s₂, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, mem₂.trans mem₁, ?_⟩
  · simp only [roundBody, runBoxes_append, run₁, Option.bind_some, run₂]
  · exact left.trans ((keep₁ rReg (by decide)).trans hr)
  · rw [right]; exact value.trans (by rw [show s.gpr .a3 = s.gpr kp from rfl, hk])
  · intro q hq
    have hq' : q ∈ feistelKept := by revert hq; cases q <;> decide
    exact (keep₂ q hq).trans (keep₁ q hq')

/-- The registers a round and the step to the next keep. -/
def roundStepKept : List Reg := [.ra, .s0, .s1, .s2, .s3, .s4, .s11, .a0, kstep, passes]

theorem countDown_rules : ∀ n < 17, 1 ≤ n →
    (BitVec.ofNat 64 n + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n - 1)) ∧
    ((BitVec.ofNat 64 n + BitVec.ofInt 64 (-1)) != 0) = decide (n ≠ 1) := by
  decide +kernel

theorem roundAdvance_ok (s : State) :
    ∃ s', runBlock isa roundAdvance s = some s' ∧
      s'.gpr kp = s.gpr kp + s.gpr kstep ∧
      s'.gpr cnt = s.gpr cnt + BitVec.ofInt 64 (-1) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ cnt → r ≠ kp → s'.gpr r = s.gpr r) := by
  let s₁ := s.write kp (s.gpr kp + s.gpr kstep)
  let s₂ := s₁.write cnt (s₁.gpr cnt + BitVec.ofInt 64 (-1))
  refine ⟨s₂, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · rw [roundAdvance, runBlock_cons, exec_add, runStep_some, runBlock_cons,
      exec_addi (by decide), runStep_some, runBlock_nil]
  · simp only [s₂, s₁, gpr_write, kp, cnt, kstep, reduceCtorEq, ite_true, ite_false]
  · simp only [s₂, s₁, gpr_write, kp, cnt, reduceCtorEq, ite_true, ite_false]
  · intro r h16 h17
    simp only [s₂, s₁, gpr_write, h16, h17, ite_false]

theorem roundStep_ok (s : State)
    (l r : BitVec 32) (k : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn' : n < 17)
    (hl : s.gpr lReg = l.setWidth 64) (hr : s.gpr rReg = r.setWidth 64)
    (hk : s.mem.readW (s.gpr kp) 64 = k) (hready : FeiReady s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr kp) 8) (hal : (s.gpr kp).toNat % 8 = 0)
    (hcount : s.gpr cnt = BitVec.ofNat 64 n) :
    ∃ s', runBlock isa (roundBody ++ roundAdvance) s = some s' ∧
      s'.gpr lReg = r.setWidth 64 ∧
      s'.gpr rReg = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)).setWidth 64 ∧
      s'.gpr kp = s.gpr kp + s.gpr kstep ∧
      s'.gpr cnt = BitVec.ofNat 64 (n - 1) ∧
      isa.eval (.nonzero cnt) s' = some (decide (n ≠ 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ q ∈ roundStepKept, s'.gpr q = s.gpr q) := by
  obtain ⟨s₁, run₁, left₁, right₁, rd₁, wr₁, sp₁, mem₁, keep₁⟩ :=
    roundBody_ok s l r k hl hr hk hready hread hal
  obtain ⟨s₂, run₂, ptr₂, count₂, rd₂, wr₂, sp₂, mem₂, keep₂⟩ := roundAdvance_ok s₁
  obtain ⟨hsub, hzero⟩ := countDown_rules n hn' hn
  have hcount₁ : s₁.gpr cnt = BitVec.ofNat 64 n := (keep₁ cnt (by decide)).trans hcount
  refine ⟨s₂, ?_, ?_, ?_, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁,
    mem₂.trans mem₁, ?_⟩
  · simp only [runBoxes_append, run₁, Option.bind_some, run₂]
  · exact (keep₂ lReg (by decide) (by decide)).trans left₁
  · exact (keep₂ rReg (by decide) (by decide)).trans right₁
  · rw [ptr₂, keep₁ kp (by decide), keep₁ kstep (by decide)]
  · rw [count₂, hcount₁, hsub]
  · change VG.RISCV64.eval (.nonzero cnt) s₂ = _
    simp only [VG.RISCV64.eval, count₂, hcount₁, hzero]
  · intro q hq
    have hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    have hneq : q ≠ cnt ∧ q ≠ kp := by revert hq; cases q <;> decide
    exact (keep₂ q hneq.1 hneq.2).trans (keep₁ q hq')

end VG.Proof.TripleDes.RISCV64

end

end


/-!
# The sixteen rounds of a pass

`roundsLoop_ok`: the loop of rounds, from the pass's first key at
`keyAddr base direction 0`, `kstep` bytes on each round.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.TripleDes.RISCV64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix feistelStep)

def keyAddr (base : Addr) (direction : Direction) (j : Nat) : Addr :=
  base + BitVec.ofNat 64 (8 * (if direction = .encrypt then j else 15 - j))

/-- The key step of a pass, in `kstep`. -/
def stepVal (direction : Direction) : BitVec 64 :=
  BitVec.ofInt 64 (if direction = .encrypt then 8 else -8)

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
  left : s.gpr lReg = (roundPrefix keys direction (16 - n) v).1.setWidth 64
  right : s.gpr rReg = (roundPrefix keys direction (16 - n) v).2.setWidth 64
  counter : s.gpr cnt = BitVec.ofNat 64 n
  pointer : s.gpr kp = keyAddr base direction (16 - n)
  stp : s.gpr kstep = stepVal direction
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  mem : s.mem = origin.mem

structure LoopPost (keys : DesSchedule) (direction : Direction)
    (origin : State) (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr lReg = (roundPrefix keys direction 16 v).1.setWidth 64
  right : s.gpr rReg = (roundPrefix keys direction 16 v).2.setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  mem : s.mem = origin.mem

/-- What the rounds need of the pass's keys: readable, aligned, and the
pass's round keys. -/
structure KeysAt (keys : DesSchedule) (direction : Direction) (base : Addr) (s : State) :
    Prop where
  read : ∀ j < 16, InRegions (s.rd ++ s.wr) (keyAddr base direction j) 8
  al : ∀ j < 16, (keyAddr base direction j).toNat % 8 = 0
  keys : ∀ j < 16, (s.mem.readW (keyAddr base direction j) 64).setWidth 48 =
    roundKey keys direction j

theorem loopStep (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hready : FeiReady origin) (hkeys : KeysAt keys direction base origin)
    (n : Nat) (s : State) (hs : LoopInv keys direction base origin v n s) :
    WP isa (.block (roundBody ++ roundAdvance)) s (fun s' =>
      (isa.eval (.nonzero cnt) s' = some false ∧ LoopPost keys direction origin v s') ∨
      (isa.eval (.nonzero cnt) s' = some true ∧ ∃ m < n, LoopInv keys direction base origin v m s')) := by
  have hj : 16 - n < 16 := by omega_using [hs.positive]
  have hreadyS : FeiReady s := hready.congr (hs.regs sb (by decide)) hs.wr hs.mem
  have hreadS : InRegions (s.rd ++ s.wr) (s.gpr kp) 8 := by
    rw [hs.rd, hs.wr, hs.pointer]; exact hkeys.read _ hj
  have halS : (s.gpr kp).toNat % 8 = 0 := by rw [hs.pointer]; exact hkeys.al _ hj
  have hk : (s.mem.readW (s.gpr kp) 64).setWidth 48 = roundKey keys direction (16 - n) := by
    rw [hs.pointer, hs.mem]
    exact hkeys.keys _ hj
  obtain ⟨s', run, left, right, ptr, count, flag, rd, wr, sp, mem, regs⟩ :=
    roundStep_ok s _ _ (s.mem.readW (s.gpr kp) 64) n hs.positive
      (by omega_using [hs.bounded]) hs.left hs.right rfl hreadyS hreadS halS hs.counter
  have hidx : 16 - (n - 1) = 16 - n + 1 := by
    omega_using [hs.positive, hs.bounded]
  have hleft : s'.gpr lReg = (roundPrefix keys direction (16 - (n - 1)) v).1.setWidth 64 := by
    rw [hidx]
    exact left.trans (congrArg (fun pair => pair.1.setWidth 64)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hright : s'.gpr rReg = (roundPrefix keys direction (16 - (n - 1)) v).2.setWidth 64 := by
    rw [hidx]
    have hval := congrArg (fun key =>
      ((roundPrefix keys direction (16 - n) v).1 ^^^
        Spec.TripleDes.roundFunction (roundPrefix keys direction (16 - n) v).2 key).setWidth 64) hk
    exact (right.trans hval).trans (congrArg (fun pair => pair.2.setWidth 64)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hframe : s'.mem = origin.mem := mem.trans hs.mem
  have hregs : ∀ q ∈ roundStepKept, s'.gpr q = origin.gpr q :=
    fun q hq => (regs q hq).trans (hs.regs q hq)
  refine WP.of_runBlock ⟨s', run, ?_⟩
  by_cases hlast : n = 1
  · left
    refine ⟨?_, ?_⟩
    · simpa only [hlast, ne_eq, not_true_eq_false, decide_false] using flag
    · subst n
      exact ⟨hleft, hright, rd.trans hs.rd, wr.trans hs.wr, sp.trans hs.sp, hregs, hframe⟩
  · right
    refine ⟨?_, n - 1, by omega_using [hs.positive], ?_⟩
    · simpa only [hlast, ne_eq, not_false_eq_true, decide_true] using flag
    · refine ⟨by omega_using [hs.positive, hlast], by omega_using [hs.bounded],
        hleft, hright, count, ?_, (regs kstep (by decide)).trans hs.stp,
        rd.trans hs.rd, wr.trans hs.wr, sp.trans hs.sp, hregs, hframe⟩
      rw [ptr, hs.pointer, hs.stp, keyAddr_step base direction (16 - n) (by
        omega_using [hs.positive, hlast]), ← hidx]

/-- The complete sixteen-round loop, in either key order. -/
theorem roundsLoop_ok (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hready : FeiReady origin)
    (hl : origin.gpr lReg = v.1.setWidth 64) (hr : origin.gpr rReg = v.2.setWidth 64)
    (hptr : origin.gpr kp = keyAddr base direction 0)
    (hcount : origin.gpr cnt = BitVec.ofNat 64 16)
    (hstep : origin.gpr kstep = stepVal direction)
    (hkeys : KeysAt keys direction base origin) :
    WP isa (.loop (.block (roundBody ++ roundAdvance)) (.nonzero cnt))
      origin (LoopPost keys direction origin v) := by
  apply WP.loop (M := isa) (body := .block (roundBody ++ roundAdvance))
    (c := .nonzero cnt) (Q := LoopPost keys direction origin v)
    (LoopInv keys direction base origin v)
    (loopStep keys direction base origin v hready hkeys)
    16 origin
  exact ⟨by decide, by decide, hl, hr, hcount, hptr, hstep, rfl, rfl, rfl,
    fun _ _ => rfl, rfl⟩

end VG.Proof.TripleDes.RISCV64

end

end


/-!
# A DES pass

`pass_ok`: the choice of the pass's keys by the passes left, its sixteen
rounds, the final half swap and the passes left counted down.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.RegUpd VG.Impl.TripleDes.RISCV64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix)

def passOffset (component : Nat) (direction : Direction) : Nat :=
  keyOff + 128 * component + if direction = .encrypt then 0 else 120

theorem passOffset_bound : ∀ c < 3, ∀ d : Direction, passOffset c d < 2048 := by
  intro c hc d
  cases d <;> simp only [passOffset, keyOff, reduceCtorEq, ite_true, ite_false] <;> omega_using [hc]

theorem passStart_ok (component : Nat) (hc : component < 3) (direction : Direction)
    (s : State) :
    ∃ s', runBlock isa (passStart component direction) s = some s' ∧
      s'.gpr kp = s.gpr sb + BitVec.ofNat 64 (passOffset component direction) ∧
      s'.gpr cnt = BitVec.ofNat 64 16 ∧ s'.mem = s.mem ∧
      s'.gpr kstep = stepVal direction ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ cnt → r ≠ kp → r ≠ kstep → s'.gpr r = s.gpr r) := by
  have hb := passOffset_bound component hc direction
  let s₁ := s.write kp (s.gpr sb + BitVec.ofInt 64 (passOffset component direction : Nat))
  let s₂ := s₁.write cnt (BitVec.ofInt 64 16)
  let s₃ := s₂.write kstep (stepVal direction)
  have e₃ : exec (.li kstep (if direction = .encrypt then 8 else -8)) s₂ = some s₃ := by
    rw [exec_li (by cases direction <;> decide)]
    rfl
  refine ⟨s₃, ?_, ?_, ?_, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · rw [passStart, runBlock_cons, show (keyOff + 128 * component +
        if direction = .encrypt then 0 else 120) = passOffset component direction from rfl,
      exec_addi (by constructor <;> omega_arith), runStep_some, runBlock_cons, exec_li (by decide),
      runStep_some, runBlock_cons, e₃, runStep_some, runBlock_nil]
  · simp only [s₃, s₂, s₁, gpr_write, kp, cnt, kstep, sb, reduceCtorEq, ite_true, ite_false,
      BitVec.ofInt_natCast]
  · simp only [s₃, s₂, s₁, gpr_write, kp, cnt, kstep, reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [s₃, gpr_write, ite_true]
  · intro r h16 h17 h18
    simp only [s₃, s₂, s₁, gpr_write, h16, h17, h18, ite_false]

/-- What choosing and starting the pass of component `c` and direction `d` leaves. -/
structure StartPost (c : Nat) (d : Direction) (s t : State) : Prop where
  ptr : t.gpr kp = s.gpr sb + BitVec.ofNat 64 (passOffset c d)
  count : t.gpr cnt = BitVec.ofNat 64 16
  mem : t.mem = s.mem
  stp : t.gpr kstep = stepVal d
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  regs : ∀ r, r ≠ cnt → r ≠ kp → r ≠ kstep → r ≠ .t6 → t.gpr r = s.gpr r

theorem passOf_lt (d : Direction) (p : Nat) : (passOf d p).1 < 3 := by
  cases d <;> (rcases p with _ | _ | _ | _ | p) <;> simp [passOf]

theorem subi_zero (x : BitVec 64) (p k : Nat) (hx : x = BitVec.ofNat 64 p) (hp : 1 ≤ p ∧ p ≤ 3)
    (hk : k ≤ 3) : ((x + BitVec.ofInt 64 (-(k : Int))) == 0) = (p == k) := by
  subst hx
  rcases hp with ⟨h1, h3⟩
  rcases p with _ | _ | _ | _ | p <;> (try omega) <;>
    rcases k with _ | _ | _ | _ | k <;> first | omega | decide

theorem select_ok (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) (s : State)
    (hpasses : s.gpr passes = BitVec.ofNat 64 p) :
    WP isa (passSelect d) s (StartPost (passOf d p).1 (passOf d p).2 s) := by
  have branch : ∀ (t : State) (q : Nat), q = p → t.mem = s.mem → t.rd = s.rd →
      t.wr = s.wr → t.sp = s.sp → (∀ r, r ≠ .t6 → t.gpr r = s.gpr r) →
      WP isa (.block (passStart (passOf d q).1 (passOf d q).2)) t
        (StartPost (passOf d p).1 (passOf d p).2 s) := by
    intro t q hq hm hrd hwr hsp hg
    subst hq
    obtain ⟨u, run, ptr, count, mem, kst, rd, wr, sp, regs⟩ := passStart_ok (passOf d q).1
      (passOf_lt d q) (passOf d q).2 t
    refine WP.of_runBlock ⟨u, run, ?_, count, mem.trans hm, kst, rd.trans hrd, wr.trans hwr,
      sp.trans hsp, ?_⟩
    · rw [ptr, hg sb (by decide)]
    · intro r h16 h17 h18 h20
      exact (regs r h16 h17 h18).trans (hg r h20)
  let t₁ := s.write .t6 (s.gpr passes + BitVec.ofInt 64 (-3))
  have hg₁ : ∀ r, r ≠ .t6 → t₁.gpr r = s.gpr r := fun r h => gpr_write_of_ne _ _ h
  apply WP.seq
  refine WP.of_runBlock ⟨t₁, by
    rw [runBlock_cons, exec_addi (by decide), runStep_some, runBlock_nil], ?_⟩
  have zf₁ : isa.eval (.zero .t6) t₁ = some (p == 3) := by
    change VG.RISCV64.eval (.zero .t6) t₁ = _
    simp only [VG.RISCV64.eval, t₁, gpr_write_self]
    rw [show BitVec.ofInt 64 (-3) = BitVec.ofInt 64 (-((3 : Nat) : Int)) from rfl,
      subi_zero _ p 3 hpasses hp (by decide)]
  apply WP.ite (p == 3) zf₁
  · intro h3
    exact branch t₁ 3 (by simpa using h3 : p = 3).symm rfl rfl rfl rfl hg₁
  · intro h3
    apply WP.seq
    let t₂ := t₁.write .t6 (t₁.gpr passes + BitVec.ofInt 64 (-2))
    refine WP.of_runBlock ⟨t₂, by
      rw [runBlock_cons, exec_addi (by decide), runStep_some, runBlock_nil], ?_⟩
    have zf₂ : isa.eval (.zero .t6) t₂ = some (p == 2) := by
      change VG.RISCV64.eval (.zero .t6) t₂ = _
      simp only [VG.RISCV64.eval, t₂, gpr_write_self]
      rw [show BitVec.ofInt 64 (-2) = BitVec.ofInt 64 (-((2 : Nat) : Int)) from rfl,
        subi_zero _ p 2 ((hg₁ passes (by decide)).trans hpasses) hp (by decide)]
    have hg₂ : ∀ r, r ≠ .t6 → t₂.gpr r = s.gpr r := fun r h =>
      (gpr_write_of_ne _ _ h).trans (hg₁ r h)
    apply WP.ite (p == 2) zf₂
    · intro h2
      exact branch t₂ 2 (by simpa using h2 : p = 2).symm rfl rfl rfl rfl hg₂
    · intro h2
      have hp3 : p ≠ 3 := by simpa using h3
      have hp2 : p ≠ 2 := by simpa using h2
      exact branch t₂ 1 (by omega_using [hp, hp3, hp2]) rfl rfl rfl rfl hg₂

/-- The registers a pass keeps. -/
def passKept : List Reg := [.ra, .s0, .s1, .s2, .s3, .s4, .s11, .a0]

structure PassPost (keys : DesSchedule) (direction : Direction)
    (origin : State) (v : BitVec 32 × BitVec 32) (n : Nat) (s : State) : Prop where
  left : s.gpr lReg = (roundPrefix keys direction 16 v).2.setWidth 64
  right : s.gpr rReg = (roundPrefix keys direction 16 v).1.setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ passKept, s.gpr q = origin.gpr q
  mem : s.mem = origin.mem
  pcount : s.gpr passes = BitVec.ofNat 64 (n - 1)
  zf : isa.eval (.nonzero passes) s = some (decide (n ≠ 1))

theorem passCountAdvance_ok (s : State) :
    ∃ s', runBlock isa passCountAdvance s = some s' ∧
      s'.gpr passes = s.gpr passes + BitVec.ofInt 64 (-1) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ (∀ r, r ≠ passes → s'.gpr r = s.gpr r) :=
  ⟨s.write passes (s.gpr passes + BitVec.ofInt 64 (-1)), by
    rw [passCountAdvance, runBlock_cons, exec_addi (by decide), runStep_some,
      runBlock_nil], gpr_write_self _ _ _, rfl, rfl, rfl, rfl, fun _ h => gpr_write_of_ne _ _ h⟩

/-- A complete DES pass. -/
theorem pass_ok (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3)
    (keys : DesSchedule) (base : Addr) (origin : State) (v : BitVec 32 × BitVec 32)
    (hready : FeiReady origin)
    (hl : origin.gpr lReg = v.1.setWidth 64) (hr : origin.gpr rReg = v.2.setWidth 64)
    (hpasses : origin.gpr passes = BitVec.ofNat 64 p)
    (hptr : origin.gpr sb + BitVec.ofNat 64 (passOffset (passOf d p).1 (passOf d p).2) =
      keyAddr base (passOf d p).2 0)
    (hkeys : KeysAt keys (passOf d p).2 base origin) :
    WP isa (pass d) origin (PassPost keys (passOf d p).2 origin v p) := by
  apply WP.seq
  refine WP.mono (select_ok d hp origin hpasses) fun s hs => ?_
  generalize (passOf d p).2 = dir at hs hptr hkeys ⊢
  have hbase : s.gpr sb = origin.gpr sb := hs.regs sb (by decide) (by decide) (by decide)
    (by decide)
  have hkeys' : KeysAt keys dir base s :=
    ⟨by rw [hs.rd, hs.wr]; exact hkeys.read, hkeys.al, by rw [hs.mem]; exact hkeys.keys⟩
  have hloop := roundsLoop_ok keys dir base s v
    (hready.congr hbase hs.wr hs.mem)
    ((hs.regs lReg (by decide) (by decide) (by decide) (by decide)).trans hl)
    ((hs.regs rReg (by decide) (by decide) (by decide) (by decide)).trans hr)
    (hs.ptr.trans hptr) hs.count hs.stp hkeys'
  apply WP.seq
  refine WP.mono hloop fun s₂ hs₂ => ?_
  obtain ⟨s₃, run₃, left₃, right₃, rd₃, wr₃, sp₃, mem₃, regs₃⟩ := swapHalves_ok s₂
  obtain ⟨s₄, run₄, p₄, rd₄, wr₄, sp₄, mem₄, regs₄⟩ := passCountAdvance_ok s₃
  have hp₃ : s₃.gpr passes = BitVec.ofNat 64 p :=
    (regs₃ passes (by decide)).trans ((hs₂.regs passes (by decide)).trans
      ((hs.regs passes (by decide) (by decide) (by decide) (by decide)).trans hpasses))
  obtain ⟨hsub, hzero⟩ := countDown_rules p (by omega_using [hp]) hp.1
  refine WP.of_runBlock ⟨s₄, by simp only [runBoxes_append, run₃, Option.bind_some, run₄], ?_⟩
  refine ⟨?_, ?_, rd₄.trans (rd₃.trans (hs₂.rd.trans hs.rd)),
    wr₄.trans (wr₃.trans (hs₂.wr.trans hs.wr)), sp₄.trans (sp₃.trans (hs₂.sp.trans hs.sp)),
    ?_, ?_, ?_, ?_⟩
  · exact (regs₄ lReg (by decide)).trans (left₃.trans hs₂.right)
  · exact (regs₄ rReg (by decide)).trans (right₃.trans hs₂.left)
  · intro q hq
    have hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    have hq'' : q ∈ roundStepKept := by revert hq; cases q <;> decide
    have hne : q ≠ cnt ∧ q ≠ kp ∧ q ≠ kstep ∧ q ≠ passes ∧ q ≠ .t6 := by
      revert hq; cases q <;> decide
    exact (regs₄ q hne.2.2.2.1).trans ((regs₃ q hq').trans ((hs₂.regs q hq'').trans
      (hs.regs q hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.2)))
  · rw [mem₄, mem₃, hs₂.mem, hs.mem]
  · rw [p₄, hp₃, hsub]
  · change VG.RISCV64.eval (.nonzero passes) s₄ = some (decide (p ≠ 1))
    simp only [VG.RISCV64.eval, p₄, hp₃]
    rw [hsub]
    rcases hp with ⟨h1, h3⟩
    rcases p with _ | _ | _ | _ | p <;> first | omega | decide

end VG.Proof.TripleDes.RISCV64

end

end


/-!
# The three passes of a block

`blockBody_ok`: the loop of the three passes, from a word in the halves'
registers (`WordState`) and the schedules' copy in the frame (`Ready`), to
the block function's core on it (`blockCore`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.RegUpd VG.Impl.TripleDes.RISCV64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (desCore roundPrefix roundKey)

/-- A DES word held as two zero-extended 32-bit Feistel registers. -/
structure WordState (x : BitVec 64) (s : State) : Prop where
  left : s.gpr lReg = ((x >>> 32).setWidth 32).setWidth 64
  right : s.gpr rReg = (x.setWidth 32).setWidth 64

theorem PassPost.wordState {keys : DesSchedule} {direction : Direction} {origin s : State}
    {x : BitVec 64} {n : Nat}
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

def componentBase (base : Addr) (component : Nat) : Addr :=
  base + BitVec.ofNat 64 (128 * component)

/-- The round function's constants in the frame, and the three schedules
`keys` from `base` (`sb + keyOff`) on. -/
structure Ready (keys : Nat → DesSchedule) (base : Addr) (s : State) : Prop where
  consts : FeiReady s
  baseReg : s.gpr sb + BitVec.ofNat 64 keyOff = base
  keys : ∀ c < 3, ∀ d : Direction, KeysAt (keys c) d (componentBase base c) s

theorem KeysAt.congr {keys : DesSchedule} {d : Direction} {base : Addr} {s t : State}
    (hs : KeysAt keys d base s) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hm : t.mem = s.mem) :
    KeysAt keys d base t :=
  ⟨by rw [hrd, hwr]; exact hs.read, hs.al, by rw [hm]; exact hs.keys⟩

theorem Ready.congr {keys : Nat → DesSchedule} {base : Addr} {s t : State}
    (hs : Ready keys base s) (hbase : t.gpr sb = s.gpr sb) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hm : t.mem = s.mem) : Ready keys base t :=
  ⟨hs.consts.congr hbase hwr hm, by rw [hbase]; exact hs.baseReg,
    fun c hc d => (hs.keys c hc d).congr hrd hwr hm⟩

theorem passPointer (b : Addr) (c : Nat) (d : Direction) :
    b + BitVec.ofNat 64 (passOffset c d) =
      keyAddr (componentBase (b + BitVec.ofNat 64 keyOff) c) d 0 := by
  simp only [passOffset, keyAddr, componentBase, Offset.add_ofNat_add_ofNat]
  cases d <;> simp only [reduceCtorEq, ite_true, ite_false, Nat.add_zero, Nat.mul_zero] <;>
    rw [Offset.add_ofNat_add_ofNat] <;> rfl

structure Stable (origin s : State) : Prop where
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ passKept, s.gpr q = origin.gpr q
  mem : s.mem = origin.mem

theorem Stable.trans {s t u : State} (hs : Stable s t) (ht : Stable t u) : Stable s u :=
  ⟨ht.rd.trans hs.rd, ht.wr.trans hs.wr, ht.sp.trans hs.sp,
    fun q hq => (ht.regs q hq).trans (hs.regs q hq), ht.mem.trans hs.mem⟩

theorem pass_word_ok (keys : Nat → DesSchedule) (base : Addr) (s : State) (x : BitVec 64)
    (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3)
    (hready : Ready keys base s) (hword : WordState x s)
    (hpasses : s.gpr passes = BitVec.ofNat 64 p) :
    WP isa (pass d) s (fun t =>
      WordState (desCore (keys (passOf d p).1) (passOf d p).2 x) t ∧
      Ready keys base t ∧ Stable s t ∧
      t.gpr passes = BitVec.ofNat 64 (p - 1) ∧
      isa.eval (.nonzero passes) t = some (decide (p ≠ 1))) := by
  have hc := passOf_lt d p
  have hptr : s.gpr sb + BitVec.ofNat 64 (passOffset (passOf d p).1 (passOf d p).2) =
      keyAddr (componentBase base (passOf d p).1) (passOf d p).2 0 := by
    rw [← hready.baseReg]
    exact passPointer _ _ _
  apply WP.mono (pass_ok d hp (keys (passOf d p).1) (componentBase base (passOf d p).1) s
    ((x >>> 32).setWidth 32, x.setWidth 32) hready.consts hword.left hword.right
    hpasses hptr (hready.keys _ hc _))
  intro t ht
  exact ⟨ht.wordState,
    hready.congr (ht.regs sb (by decide)) ht.rd ht.wr ht.mem,
    ⟨ht.rd, ht.wr, ht.sp, ht.regs, ht.mem⟩, ht.pcount, ht.zf⟩

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
  pcount : s.gpr passes = BitVec.ofNat 64 m
  word : WordState (passesDone keys direction x (3 - m)) s
  ready : Ready keys base s
  stable : Stable origin s

theorem blockBody_ok (keys : Nat → DesSchedule) (base : Addr) (s : State) (x : BitVec 64)
    (direction : Direction) (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (blockBody direction) s
      (fun t => WordState (blockCore keys direction x) t ∧ Ready keys base t ∧ Stable s t) := by
  let s₁ := s.write passes (BitVec.ofInt 64 3)
  have hregs : ∀ r, r ≠ passes → s₁.gpr r = s.gpr r := fun r h => gpr_write_of_ne _ _ h
  have hstable : Stable s s₁ := ⟨rfl, rfl, rfl,
    fun q hq => hregs q (by revert hq; cases q <;> decide), rfl⟩
  apply WP.seq
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · rw [runBlock_cons, exec_li (by decide), runStep_some, runBlock_nil]
  refine WP.loop (M := isa) (BodyInv keys base direction x s) ?_ 3 s₁
    ⟨by decide, by decide, gpr_write_self _ _ _, ?_,
      hready.congr (hregs sb (by decide)) rfl rfl rfl, hstable⟩
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
  · exact ⟨(hregs lReg (by decide)).trans hword.left, (hregs rReg (by decide)).trans hword.right⟩

end VG.Proof.TripleDes.RISCV64

end

end


/-!
# A block

`block_ok`: `block d dp doff` replaces the block at `doff(dp)` with its
encryption (or decryption) under the schedules' copy in the frame at `sb`,
writing only the block and the frame's slots 7–69, and keeps the registers
a caller expects preserved, `a0` and `ra`.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.RegUpd VG.RISCV64.ByteLoad
open VG.Impl.TripleDes.RISCV64
open VG.Impl.Words.RISCV64 (loadBE64 storeBE)
open VG.Spec.TripleDes (Direction Schedule Block)
open VG.Proof.TripleDes (desCore)

def blockResult (keys : Schedule) (direction : Direction) (b : Block) : Block :=
  match direction with
  | .encrypt => Spec.TripleDes.encryptBlock keys b
  | .decrypt => Spec.TripleDes.decryptBlock keys b

theorem blockResult_core (keys : Schedule) (direction : Direction) (b : Block) :
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp
      (blockCore (Spec.TripleDes.componentSchedule keys) direction
        (Spec.TripleDes.permute Spec.TripleDes.ip (Spec.TripleDes.decodeBlock b)))) =
      blockResult keys direction b := by
  cases direction
  · exact (VG.Proof.TripleDes.encryptBlock_eq_cores keys b).symm
  · exact (VG.Proof.TripleDes.decryptBlock_eq_cores keys b).symm

/-- The frame's slots 7–69: the saved registers and the round function's
constants. -/
def workRegion (s : State) : Region := ⟨s.gpr sb + BitVec.ofNat 64 56, 504⟩

/-- What the block needs: the block at `doff(dp)` and the frame of 118
slots at `sb`, with the schedules' copy from byte `keyOff` on. -/
structure BlockPre (k : Schedule) (dp : Reg) (doff : Nat) (s : State) : Prop where
  dpKept : dp ∈ passKept
  doffLt : doff + 8 ≤ 2048
  al : (s.gpr sb).toNat % 8 = 0
  wr : ∀ o < 118, InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (8 * o)) 8
  keys : Spec.TripleDes.scheduleAt s.mem (s.gpr sb + BitVec.ofNat 64 keyOff) = k
  data : InRegions s.wr (s.gpr dp + BitVec.ofNat 64 doff) 8
  sep : (⟨s.gpr dp + BitVec.ofNat 64 doff, 8⟩ : Region).Disjoint (workRegion s)

/-- The registers the block keeps: those a caller expects preserved, `a0`
and `ra`. -/
def blockKept : List Reg :=
  [.ra, .s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11, .a0]

structure BlockPost (k : Schedule) (d : Direction) (dp : Reg) (doff : Nat) (s t : State) :
    Prop where
  result : Spec.TripleDes.blockAt t.mem (s.gpr dp + BitVec.ofNat 64 doff) =
    blockResult k d (Spec.TripleDes.blockAt s.mem (s.gpr dp + BitVec.ofNat 64 doff))
  regs : ∀ r ∈ blockKept, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr dp + BitVec.ofNat 64 doff, 8⟩, workRegion s] s.mem t.mem

theorem savedSlots_fits : Spill.Fits savedSlots := by decide
theorem savedSlots_restorable : Spill.Restorable sb savedSlots := by decide

theorem savedSlots_in : ∀ p ∈ savedSlots, 56 ≤ p.2 ∧ p.2 + 8 ≤ 56 + 48 := by decide

/-- The schedules' copy, for the rounds. -/
theorem keysAt_of {k : Schedule} {s : State} (hal : (s.gpr sb).toNat % 8 = 0)
    (hwr : ∀ o < 118, InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (8 * o)) 8)
    (hk : Spec.TripleDes.scheduleAt s.mem (s.gpr sb + BitVec.ofNat 64 keyOff) = k)
    (c : Nat) (hc : c < 3) (d : Direction) :
    KeysAt (Spec.TripleDes.componentSchedule k c) d
      (componentBase (s.gpr sb + BitVec.ofNat 64 keyOff) c) s := by
  have haddr : ∀ j < 16, keyAddr (componentBase (s.gpr sb + BitVec.ofNat 64 keyOff) c) d j =
      s.gpr sb + BitVec.ofNat 64 (8 * (70 + 16 * c + (if d = .encrypt then j else 15 - j))) := by
    intro j hj
    simp only [keyAddr, componentBase, keyOff, Offset.add_ofNat_add_ofNat]
    exact congrArg (fun n => s.gpr sb + BitVec.ofNat 64 n) (by split <;> omega_using [])
  have hj' : ∀ j < 16, (if d = .encrypt then j else 15 - j) < 16 := fun j hj => by split <;> omega_arith
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [haddr j hj]
    have := hj' j hj
    obtain ⟨r, hr, hc'⟩ := hwr (70 + 16 * c + (if d = .encrypt then j else 15 - j)) (by omega_using [hc, this])
    exact ⟨r, List.mem_append_right _ hr, hc'⟩
  · rw [haddr j hj]; exact Spill.al8 hal (by omega_using [])
  · rw [haddr j hj]
    have h := VG.Proof.TripleDes.componentSchedule_readW s.mem
      (s.gpr sb + BitVec.ofNat 64 keyOff) c (if d = .encrypt then j else 15 - j) hc (hj' j hj)
    rw [hk, Offset.add_ofNat_add_ofNat] at h
    simp only [VG.Proof.TripleDes.roundKey]
    rw [h]
    exact congrArg (fun n => (s.mem.readW (s.gpr sb + BitVec.ofNat 64 n) 64).setWidth 48)
      (by simp only [keyOff]; omega_using [])

theorem ready_of {k : Schedule} {s : State} (hal : (s.gpr sb).toNat % 8 = 0)
    (hwr : ∀ o < 118, InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (8 * o)) 8)
    (hk : Spec.TripleDes.scheduleAt s.mem (s.gpr sb + BitVec.ofNat 64 keyOff) = k)
    (hc : ConstsAt s) :
    Ready (Spec.TripleDes.componentSchedule k) (s.gpr sb + BitVec.ofNat 64 keyOff) s :=
  ⟨⟨hal, fun o ho => hwr o (by omega_using [ho]), hc⟩, rfl, fun c hc d => keysAt_of hal hwr hk c hc d⟩

/-- IP of the block at `doff(dp)` in the halves. -/
theorem blockLoad_ok (dp : Reg) (doff : Nat) (hdp : dp ∈ passKept) (ho : doff + 8 ≤ 2048)
    (u : State) (hin : InRegions (u.rd ++ u.wr) (u.gpr dp + BitVec.ofNat 64 doff) 8) :
    WP isa (.block (blockLoad dp doff)) u fun t =>
      WordState (Spec.TripleDes.permute Spec.TripleDes.ip (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt u.mem (u.gpr dp + BitVec.ofNat 64 doff)))) t ∧
      t.mem = u.mem ∧ t.rd = u.rd ∧ t.wr = u.wr ∧ t.sp = u.sp ∧
      ∀ r ∈ blockKept, t.gpr r = u.gpr r := by
  have hne : Reg.t0 ≠ dp ∧ Reg.t1 ≠ dp := by revert hdp; cases dp <;> decide
  unfold blockLoad
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (loadBE64_ok (d := .t0) (tmp := .t1) (n := dp) hne.1 hne.2 (by decide)
    (by omega_using [ho]) hin) fun u₁ e₁ => ?_
  subst e₁
  have hcode : permuteCode Spec.TripleDes.ip 64 .t2 .t0 .t3 = instrs initialPermutation.lit :=
    congrArg instrs initialPermutation.lit_eq
  rw [hcode]
  obtain ⟨u₂, run₂, word₂, rd₂, wr₂, sp₂, mem₂, regs₂⟩ := fixedPermutation_ok Spec.TripleDes.ip
    (by decide) (by decide) VG.Proof.TripleDes.ip_bounds .t0 .t2 _ initialPermutation_check
    ((u.write .t1 ((u.mem (u.gpr dp + BitVec.ofNat 64 (doff + 7))).setWidth 64)).write .t0
      (be64 u.mem (u.gpr dp) doff))
  have hkeep : ∀ r ∈ blockKept,
      ((instrs initialPermutation.lit).all fun i => Straight.dst i != some r) = true := by
    decide +kernel
  refine WP.of_runBlock ⟨u₂, run₂, ?_⟩
  let x := Spec.TripleDes.permute Spec.TripleDes.ip (Spec.TripleDes.decodeBlock
    (Spec.TripleDes.blockAt u.mem (u.gpr dp + BitVec.ofNat 64 doff)))
  have hx : u₂.gpr .t2 = x := by
    rw [word₂, gpr_write_self, be64_decode]
    simp [x]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_shift_d (show 32 < 64 by decide),
    Option.some.injEq, exists_eq_left', gpr_write, lReg, rReg, reduceCtorEq, ite_true, ite_false,
    hx]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact upperHalf_extend x
  · exact lowerHalf_extend x
  · simp only [mem_write]; rw [mem₂]; rfl
  · simp only [rd_write]; rw [rd₂]; rfl
  · simp only [wr_write]; rw [wr₂]; rfl
  · simp only [sp_write]; rw [sp₂]; rfl
  · intro r hr
    have hr' : r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .t0 ∧ r ≠ .t1 := by revert hr; cases r <;> decide
    simp only [hr'.1, hr'.2.1, ite_false]
    rw [regs₂ r (hkeep r hr), gpr_write_of_ne _ _ hr'.2.2.1, gpr_write_of_ne _ _ hr'.2.2.2]

/-- FP of the halves to the block at `doff(dp)`. -/
theorem blockStore_ok (dp : Reg) (doff : Nat) (hdp : dp ∈ passKept) (ho : doff + 8 ≤ 2048)
    (u : State) (x : BitVec 64) (hw : WordState x u)
    (hin : InRegions u.wr (u.gpr dp + BitVec.ofNat 64 doff) 8) :
    WP isa (.block (blockStore dp doff)) u fun t =>
      t.mem = VG.WriteBytes.writeBytes u.mem (u.gpr dp + BitVec.ofNat 64 doff)
        (beBytes 8 (Spec.TripleDes.permute Spec.TripleDes.fp x)) ∧
      t.rd = u.rd ∧ t.wr = u.wr ∧ t.sp = u.sp ∧
      ∀ r ∈ blockKept, t.gpr r = u.gpr r := by
  have hne : Reg.t1 ≠ Reg.t2 ∧ Reg.t1 ≠ dp := by revert hdp; cases dp <;> decide
  unfold blockStore
  rw [WP.block_append_iff, WP.block_append_iff]
  let u₁ := (u.write .t0 (u.gpr lReg <<< 32)).write .t0
    ((u.write .t0 (u.gpr lReg <<< 32)).gpr .t0 ^^^ (u.write .t0 (u.gpr lReg <<< 32)).gpr rReg)
  have hu₁ : u₁.gpr .t0 = x := by
    have hl := hw.left
    have hr := hw.right
    simp only [lReg, rReg] at hl hr
    simp only [u₁, gpr_write_self, gpr_write, lReg, rReg, reduceCtorEq, ite_false, hl, hr]
    exact join_halves x
  refine WP.of_runBlock ⟨u₁, by
    rw [runBlock_cons, exec_shift_d (by decide), runStep_some, runBlock_cons, exec_logic,
      runStep_some, runBlock_nil], ?_⟩
  have hcode : permuteCode Spec.TripleDes.fp 64 .t2 .t0 .t3 = instrs finalPermutation.lit :=
    congrArg instrs finalPermutation.lit_eq
  rw [hcode]
  obtain ⟨u₂, run₂, word₂, rd₂, wr₂, sp₂, mem₂, regs₂⟩ := fixedPermutation_ok Spec.TripleDes.fp
    (by decide) (by decide) VG.Proof.TripleDes.fp_bounds .t0 .t2 _ finalPermutation_check u₁
  have hkeep : ∀ r ∈ blockKept,
      ((instrs finalPermutation.lit).all fun i => Straight.dst i != some r) = true := by
    decide +kernel
  have hkeep' : ((instrs finalPermutation.lit).all fun i => Straight.dst i != some dp) = true :=
    hkeep dp (by revert hdp; cases dp <;> decide)
  refine WP.of_runBlock ⟨u₂, run₂, ?_⟩
  have hdp₂ : u₂.gpr dp = u.gpr dp := by
    rw [regs₂ dp hkeep']
    have h0 : dp ≠ .t0 := by revert hdp; cases dp <;> decide
    simp only [u₁, gpr_write_of_ne _ _ h0]
  have hv : u₂.gpr .t2 = Spec.TripleDes.permute Spec.TripleDes.fp x := by
    rw [word₂, hu₁]; simp
  refine WP.mono (storeBE_ok (v := .t2) (tmp := .t1) (n := dp) (off := doff) (w := 8) hne.1 hne.2
    (by decide) (by decide) ho fun j hj => by
      rw [wr₂, hdp₂]
      exact in_byte' hin hj) fun t e => ?_
  subst e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_write, hdp₂, hv, mem₂]; rfl
  · simp only [rd_write]; rw [rd₂]; rfl
  · simp only [wr_write]; rw [wr₂]; rfl
  · simp only [sp_write]; rw [sp₂]; rfl
  · intro r hr
    have hr' : r ≠ .t1 ∧ r ≠ .t0 := by revert hr; cases r <;> decide
    rw [gpr_write_of_ne _ _ hr'.1]
    change u₂.gpr r = u.gpr r
    rw [regs₂ r (hkeep r hr)]
    simp only [u₁, gpr_write_of_ne _ _ hr'.2]

end VG.Proof.TripleDes.RISCV64
