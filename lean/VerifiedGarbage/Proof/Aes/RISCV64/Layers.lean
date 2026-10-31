module

import VerifiedGarbage.Impl.Aes.RISCV64.Ctr32
public import VerifiedGarbage.Proof.Framework.RISCV64.Linear
import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Aes.Bitsliced
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Aes.RISCV64.Inv
public import VerifiedGarbage.TCB.Mem

/-!
# The layers of bitsliced AES on RISC-V

As on x86-64 (`Proof/Aes/X86_64/Encrypt.lean`):

* `sboxCode` only combines words bitwise, so it computes the same Boolean
  function at each of the 64 bit positions: the kernel evaluates it once on
  truth tables of the 256 inputs (`Bitslice.table`) and compares the result
  with the specification's S-box on the same tables (`sboxT`, proved right
  in `Proof/Aes/SboxSpec.lean`). `sbox_ok` then gives, at every bit position
  `p`, the S-box of the byte formed by bit `p` of the eight words. Its run
  relates each abstract table to the concrete word at every position at
  once (`TabAll`), which makes the relation a function, as the evaluator
  needs.
* Each linear layer is checked by evaluation over the lane domain
  (`Framework/RISCV64/Linear.lean`): the kernel runs it on the input words
  as atoms and compares every output bit with the XOR of input bits given
  here. Position `p = 16r + 4c + b` of a word of the bitsliced state is byte
  `r + 4c` of block `b`. The layers read their masks from the slots of the
  scratch buffer (`bsKs`, `srKs`, `invSrKs`).
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Aes.RISCV64 VG.Proof.Aes
open VG.Spec.Aes (sbox)

/-! ## The masks -/

/-- The slots of masks `ms` from `base` on. -/
def ksOf (base : Nat) (ms : List (Nat × BitVec 64)) : List (Nat × BitVec 64) :=
  ms.map fun (k, v) => (base + k - 1, v)

def bsKs : List (Nat × BitVec 64) := ksOf bsSlot bsMasks
def srKs : List (Nat × BitVec 64) := ksOf srSlot srMasks
def invSrKs : List (Nat × BitVec 64) := ksOf invSrSlot invSrMasks

/-- The slots hold the masks `ks`. -/
def MasksAt (m : Mem) (b : Addr) (ks : List (Nat × BitVec 64)) : Prop :=
  ∀ k v, (k, v) ∈ ks → m.readW (wordAddr b k) 64 = v

/-! ## The S-box -/

/-- The S-box's memory: its spill slots, at `a5`. -/
def sboxCfg : Cfg := { base := sb, slots := 40, ext := sb, exts := 0 }

/-- The truth table of bit `k` of the input. -/
def inT (k : Nat) : Nat := tableOf (fun c => c.testBit k) 256

def inTs : List Nat := (List.range 8).map inT

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)).map fun k => .v (inT k)
    slot := fun _ => none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => word (e.reg (q j)) == some ((sboxT inTs).getD j 0)

theorem sbox_check :
    check (table 64 256) sboxCfg (fun _ => none) sboxCode sboxEnv sboxPost = true := by
  decide +kernel

theorem row_inTs {c : Nat} (hc : c < 256) : row inTs c = BitVec.ofNat 8 c := by
  refine row_ext fun j hj => ?_
  simp only [inTs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
    BitVec.getLsbD_ofNat, hj]

/-- A table related to a word at every bit position `p`, row `cs p`. -/
def TabAll (cs : Nat → Nat) (a : Nat) (x : BitVec 64) : Prop := ∀ p < 64, TableRel p (cs p) a x

theorem tabAll_sound {cs : Nat → Nat} (hcs : ∀ p < 64, cs p < 256) :
    (table 64 256).Sound (TabAll cs) where
  xor ha hb h p hp := (table_sound hp (hcs p hp)).xor (ha p hp) (hb p hp) h
  and ha hb h p hp := (table_sound hp (hcs p hp)).and (ha p hp) (hb p hp) h
  or ha hb h p hp := (table_sound hp (hcs p hp)).or (ha p hp) (hb p hp) h
  ror _ h := by cases h
  shr _ h := by cases h
  const h p hp := (table_sound hp (hcs p hp)).const h

theorem tabAll_fun {cs : Nat → Nat} (a : Nat) (x y : BitVec 64) (hx : TabAll cs a x)
    (hy : TabAll cs a y) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  have h1 := hx p hp
  have h2 := hy p hp
  simp only [TableRel] at h1 h2
  rw [← h1, ← h2]

/-- The registers the S-box (and every layer) may write. -/
def sboxWrites : List Reg := [q 0, q 1, q 2, q 3, q 4, q 5, q 6, q 7, .t0, .t1, .t2, .t3, .t4,
  .t5, .t6, .a6, .a7, .s8, .s9, .s10, .s11]

/-- The registers outside `sboxWrites`. -/
def restRegs : List Reg := [.ra, .a0, .a1, .a2, .a3, .a4, .a5]

theorem sbox_writes_rest :
    restRegs.all (fun r => sboxCode.all fun i => dst i != some r) = true := by
  decide +kernel

theorem not_sboxWrites (r : Reg) (hr : r ∉ sboxWrites) : r ∈ restRegs := by
  revert hr; cases r <;> decide

theorem writes_rest {is : List Instr}
    (h : restRegs.all (fun r => is.all fun i => dst i != some r) = true)
    (r : Reg) (hr : r ∉ sboxWrites) : (is.all fun i => dst i != some r) = true :=
  List.all_eq_true.mp h r (not_sboxWrites r hr)

/-- The S-box, at every bit position of the words in `q 0 … q 7`. -/
theorem sbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 64,
        (s'.gpr (q j)).getLsbD p = (sbox (bsByte (fun k => s.gpr (q k)) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ sbox_check
  have hout : ∀ j < 8, e'.reg (q j) = some (.v ((sboxT inTs).getD j 0)) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simp only [beq_iff_eq] at this
    cases h : e'.reg (q j) with
    | none => rw [h] at this; cases this
    | some v => cases v <;> rw [h] at this <;> simp_all [word]
  let cs : Nat → Nat := fun p => (bsByte (fun k => s.gpr (q k)) p).toNat
  have hcs : ∀ p < 64, cs p < 256 := fun p _ => (bsByte (fun k => s.gpr (q k)) p).isLt
  have hrel : Rel (TabAll cs) sboxCfg (fun _ => none) sboxEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨hqk, hkr⟩ := List.find?_some hk, List.mem_of_find?_eq_some hk
    have hk8 := List.mem_range.mp hkr
    simp only [beq_iff_eq] at hqk
    subst hqk
    intro p hp
    simp only [TableRel, inT, testBit_tableOf, hcs p hp, decide_true, Bool.true_and, cs,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8]
  obtain ⟨s', hs', p₀⟩ := run (tabAll_sound hcs) tabAll_fun hok hrel he
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, p₀.sp, fun r hr => p₀.other r ?_, p₀.frame⟩
  · have hc := hcs p hp
    have := p₀.rel.reg (q j) _ (hout j hj) p hp
    simp only [TableRel] at this
    rw [← this, ← getLsbD_row _ _ hj, row_sboxT (by simp [inTs]) hc, row_inTs hc]
    simp [cs]
  · simp [List.all_eq_true.mp sbox_writes_rest r (not_sboxWrites r hr)]

/-! ## The linear layers -/

/-- The memory of the layers, which they only read: the masks of the
transposes (and none for MixColumns) and of ShiftRows and its inverse, as
external words at `a5`, and for AddRoundKey the round key at `kp`. -/
def bsCfg : Cfg := { base := sb, slots := 0, ext := sb, exts := 58 }
def srCfg : Cfg := { base := sb, slots := 0, ext := sb, exts := 76 }
def arkCfg : Cfg := { base := sb, slots := 0, ext := kp, exts := 8 }

/-- The state registers hold input words `0 … 7`. -/
def qIns : List (Reg × Nat) := (List.range 8).map fun k => (q k, k)

/-- The outputs `q j`, bit `p` the XOR of the input bits `g j p`. -/
def qOuts (g : Nat → Nat → List Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (q j, g j)

theorem toBs_check :
    check (lanes 64 9) bsCfg (kExt bsKs) toBs (linEnv qIns) (linPost 9 (qOuts toBsG)) = true := by
  decide +kernel

theorem fromBs_check :
    check (lanes 64 9) bsCfg (kExt bsKs) fromBs (linEnv qIns) (linPost 9 (qOuts fromBsG)) = true := by
  decide +kernel

theorem shiftRows_check :
    check (lanes 64 9) srCfg (kExt srKs) shiftRows (linEnv qIns) (linPost 9 (qOuts srG)) = true := by
  decide +kernel

theorem mixColumns_check :
    check (lanes 64 9) bsCfg (kExt []) mixColumns (linEnv qIns) (linPost 9 (qOuts mcG)) = true := by
  decide +kernel

theorem addRoundKey_check :
    check (lanes 64 10) arkCfg (linExt 8) addRoundKey (linEnv qIns) (linPost 10 (qOuts arkG)) = true := by
  decide +kernel

/-! ## On the machine -/

theorem q_linear {k : Nat} {c : Cfg} {is : List Instr} {ext : Nat → Option (Nat × Nat)}
    {g : Nat → Nat → List Nat}
    (hchk : check (lanes 64 k) c ext is (linEnv qIns) (linPost k (qOuts g)) = true)
    (hk : 512 ≤ 2 ^ k)
    (hw : restRegs.all (fun r => is.all fun i => dst i != some r) = true)
    {s : State} (hok : Ok c s) (W : Nat → BitVec 64) (hW : ∀ i < 8, W i = s.gpr (q i))
    (hext : ∀ j a, j < c.exts → ext j = some a →
      LaneRel k (assign W (2 ^ k)) a (s.mem.readW (wordAddr (s.gpr c.ext) j) 64)) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ j < 8, ∀ p < 64, (s'.gpr (q j)).getLsbD p = xorBits W (g j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion c s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok hchk hok W (fun r i hri => by
    simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
    obtain ⟨i, hi, rfl, rfl⟩ := hri
    exact ⟨by omega_arith, hW i hi⟩) hext
  have hmem : ∀ j < 8, (q j, g j) ∈ qOuts g := fun j hj => by
    simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩
  exact ⟨s', hs', fun j hj p hp => hout (q j) (g j) (hmem j hj) p hp, hrd, hwr, hsp,
    fun r hr => hoth r (writes_rest hw r hr), hfr⟩

/-- The words of the state registers. -/
abbrev Q (s : State) (i : Nat) : BitVec 64 := s.gpr (q i)

/-- What a layer does besides its outputs. -/
def Rest (c : Cfg) (s s' : State) : Prop :=
  s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
    Frame [slotRegion c s] s.mem s'.mem

theorem toBs_ok {s : State} (hok : Ok bsCfg s) (hks : MasksAt s.mem (s.gpr sb) bsKs) :
    ∃ s', runBlock isa toBs s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p =
        (Q s (p % 4 + 4 * (idx p / 8))).getLsbD (8 * (idx p % 8) + j)) ∧ Rest bsCfg s s' := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear toBs_check (by decide) (by decide +kernel) hok (Q s)
    (fun _ _ => rfl) (kExt_rel hks)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, toBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by omega_arith)]

theorem fromBs_ok {s : State} (hok : Ok bsCfg s) (hks : MasksAt s.mem (s.gpr sb) bsKs) :
    ∃ s', runBlock isa fromBs s = some s' ∧
      (∀ k < 8, ∀ t < 64, (Q s' k).getLsbD t = (Q s (t % 8)).getLsbD (pos (k % 4) (t / 8 + 8 * (k / 4)))) ∧
      Rest bsCfg s s' := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear fromBs_check (by decide) (by decide +kernel) hok (Q s)
    (fun _ _ => rfl) (kExt_rel hks)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by simp only [pos]; omega_arith)]

theorem shiftRows_ok {s : State} (hok : Ok srCfg s) (hks : MasksAt s.mem (s.gpr sb) srKs) :
    ∃ s', runBlock isa shiftRows s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = (Q s j).getLsbD (srSrc p)) ∧ Rest srCfg s s' := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear shiftRows_check (by decide) (by decide +kernel) hok
    (Q s) (fun _ _ => rfl) (kExt_rel hks)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, srG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by simp only [srSrc]; omega_arith)]

theorem mixColumns_ok {s : State} (hok : Ok bsCfg s) :
    ∃ s', runBlock isa mixColumns s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = termsXor (Q s) (mcTerms j p)) ∧ Rest bsCfg s s' := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear mixColumns_check (by decide) (by decide +kernel) hok
    (Q s) (fun _ _ => rfl) (kExt_rel (ks := []) (fun _ _ h => by cases h))
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, mcG, xorBits_map]
  intro wt hwt
  obtain ⟨wk, -, rfl⟩ := List.mem_map.mp hwt
  exact Nat.mod_lt _ (by decide)

/-- Word `j` of the bitsliced round key at `kp`. -/
abbrev keyWord (s : State) (j : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr kp) j) 64

theorem addRoundKey_ok {s : State} (hok : Ok arkCfg s) :
    ∃ s', runBlock isa addRoundKey s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = ((Q s j).getLsbD p ^^ (keyWord s j).getLsbD p)) ∧
      Rest arkCfg s s' := by
  let W : Nat → BitVec 64 := fun i => if i < 8 then Q s i else keyWord s (i - 8)
  obtain ⟨s', hs', hout, rest⟩ := q_linear addRoundKey_check (by decide) (by decide +kernel) hok
    W (fun i hi => by simp [W, hi]) (linExt_rel fun j hj => by
      simp only [arkCfg] at hj ⊢
      refine ⟨by omega_arith, ?_⟩
      simp [W, show ¬ 8 + j < 8 by omega_arith])
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, arkG, xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ hp, bitOf_word _ _ _ hp]
  simp [W, hj, show ¬ 8 + j < 8 by omega_arith]

end VG.Proof.Aes.RISCV64
