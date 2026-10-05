import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Impl.Aes.AArch64.Ctr32
import VerifiedGarbage.Impl.Aes.AArch64.Linear
import VerifiedGarbage.Proof.Framework.AArch64.Linear
import VerifiedGarbage.Impl.Aes.AArch64.Sbox
import VerifiedGarbage.Proof.Aes.InvSboxSpec
import VerifiedGarbage.Proof.Aes.InvBitsliced
import VerifiedGarbage.Proof.Framework.AArch64.Straight
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Bitslice.Sym
import VerifiedGarbage.Proof.Aes.Blocks
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Impl.Aes.AArch64.Blocks

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.AArch64.Encrypt`. -/
section

section

section

/-!
# The bitsliced S-box on AArch64

`sboxCode` only combines words bitwise (and builds all ones with `movz` and
`sub`), so it computes the same Boolean function at each of the 64 bit
positions: the kernel evaluates it once on truth tables of the 256 inputs
(`Bitslice.table`) and compares the result with the specification's S-box
on the same tables (`sboxT`, proved right in `Proof/Aes/SboxSpec.lean`).
`sbox_ok` then gives, at every bit position `p`, the S-box of the byte
formed by bit `p` of the eight words.
-/

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes
open VG.Spec.Aes (sbox)

/-- The S-box's memory: its spill slots, at `x5`. -/
def sboxCfg : Cfg := { base := sb, slots := 48, ext := sb, exts := 0 }

/-- The truth table of bit `k` of the input. -/
def inT (k : Nat) : Nat := tableOf (fun c => c.testBit k) 256

def inTs : List Nat := (List.range 8).map VG.Proof.Aes.AArch64.inT

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)).map VG.Proof.Aes.AArch64.inT, slot := fun _ => none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (q j) == some ((sboxT VG.Proof.Aes.AArch64.inTs).getD j 0)

theorem sbox_check :
    VG.AArch64.Straight.check (table 64 256) VG.Proof.Aes.AArch64.sboxCfg (fun _ => none) sboxCode VG.Proof.Aes.AArch64.sboxEnv VG.Proof.Aes.AArch64.sboxPost = true := by
  decide +kernel

theorem row_inTs {c : Nat} (hc : c < 256) : row VG.Proof.Aes.AArch64.inTs c = BitVec.ofNat 8 c := by
  refine row_ext fun j hj => ?_
  simp only [VG.Proof.Aes.AArch64.inTs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, VG.Proof.Aes.AArch64.inT, testBit_tableOf, hc, decide_true, Bool.true_and,
    BitVec.getLsbD_ofNat, hj]

/-- The registers the layers of AES may write: the state, the S-box's
temporaries and all ones, and the linear layers' masks and temporaries. -/
def layerWrites : List Reg :=
  [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
   .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

/-- The registers outside `layerWrites`. -/
def layerKeep : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x30]

theorem not_layerWrites (r : Reg) (hr : r ∉ VG.Proof.Aes.AArch64.layerWrites) : r ∈ VG.Proof.Aes.AArch64.layerKeep := by
  revert hr; cases r <;> decide

/-- A block that writes none of `layerKeep` writes only `layerWrites`. -/
theorem writes_rest {is : List Instr}
    (h : layerKeep.all (fun r => is.all fun i => dstOf i != some r) = true)
    (r : Reg) (hr : r ∉ VG.Proof.Aes.AArch64.layerWrites) : (is.all fun i => dstOf i != some r) = true :=
  List.all_eq_true.mp h r (VG.Proof.Aes.AArch64.not_layerWrites r hr)

/-- The S-box, at every bit position of the words in `q 0 … q 7`. -/
theorem sbox_ok {s : State} (hok : Ok VG.Proof.Aes.AArch64.sboxCfg s) :
    ∃ s', runBlock isa sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 64,
        (s'.gpr (q j)).getLsbD p = (sbox (bsByte (fun k => s.gpr (q k)) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ VG.Proof.Aes.AArch64.layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.AArch64.sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.Aes.AArch64.sbox_check
  have hout : ∀ j < 8, e'.reg (q j) = some ((sboxT VG.Proof.Aes.AArch64.inTs).getD j 0) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  -- The run at bit position `p`, on the input formed by the bits `p`.
  have key : ∀ p < 64, ∃ s', runBlock isa sboxCode s = some s' ∧
      Post (TableRel p (bsByte (fun k => s.gpr (q k)) p).toNat) VG.Proof.Aes.AArch64.sboxCfg (fun _ => none) e' s s'
        (fun r => (sboxCode.all fun i => dstOf i != some r) = false) := by
    intro p hp
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_, (fun _ _ _ h => by cases h),
      (fun _ _ _ h => by cases h), (fun _ _ h => by cases h)⟩ he
    simp only [VG.Proof.Aes.AArch64.sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨hqk, hkr⟩ := List.find?_some hk, List.mem_of_find?_eq_some hk
    have hk8 := List.mem_range.mp hkr
    simp only [beq_iff_eq] at hqk
    subst hqk
    simp only [TableRel, VG.Proof.Aes.AArch64.inT, testBit_tableOf, hc, decide_true, Bool.true_and,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8]
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, p₀.sp, fun r hr => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    have := p₁.rel.reg (q j) _ (hout j hj)
    simp only [TableRel] at this
    rw [← this, ← getLsbD_row _ _ hj, row_sboxT (by simp [VG.Proof.Aes.AArch64.inTs]) hc, VG.Proof.Aes.AArch64.row_inTs hc]
    simp
  · simp [VG.Proof.Aes.AArch64.writes_rest (is := sboxCode) (by decide +kernel) r hr]

end VG.Proof.Aes.AArch64

end

/-!
# The linear layers of bitsliced AES on AArch64

Each layer is checked by evaluation over the lane domain
(`Framework/AArch64/Linear.lean`): the kernel runs it on the input words
as atoms and compares every output bit with the XOR of input bits given
here. Position `p = 16r + 4c + b` of a word of the bitsliced state is byte
`r + 4c` of block `b`.
-/

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes

/-- The memory of the layers: nothing in memory, and for
AddRoundKey the round key at `kp`. -/
def linCfg : Cfg := { base := sb, slots := 48, ext := sb, exts := 0 }
def arkCfg : Cfg := { base := sb, slots := 0, ext := kp, exts := 8 }

/-- The state registers hold input words `0 … 7`. -/
def qIns : List (Reg × Nat) := (List.range 8).map fun k => (q k, k)

/-- The outputs `q j`, bit `p` the XOR of the input bits `g j p`. -/
def qOuts (g : Nat → Nat → List Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (q j, g j)

theorem toBs_check : VG.AArch64.Straight.check (lanes 64 9) VG.Proof.Aes.AArch64.linCfg (linExt 0) toBs (linEnv VG.Proof.Aes.AArch64.qIns) (linPost 9 (VG.Proof.Aes.AArch64.qOuts toBsG)) = true := by
  decide +kernel

theorem fromBs_check :
    VG.AArch64.Straight.check (lanes 64 9) VG.Proof.Aes.AArch64.linCfg (linExt 0) fromBs (linEnv VG.Proof.Aes.AArch64.qIns) (linPost 9 (VG.Proof.Aes.AArch64.qOuts fromBsG)) = true := by
  decide +kernel

theorem shiftRows_check :
    VG.AArch64.Straight.check (lanes 64 9) VG.Proof.Aes.AArch64.linCfg (linExt 0) shiftRows (linEnv VG.Proof.Aes.AArch64.qIns) (linPost 9 (VG.Proof.Aes.AArch64.qOuts srG)) = true := by
  decide +kernel

theorem mixColumns_check :
    VG.AArch64.Straight.check (lanes 64 9) VG.Proof.Aes.AArch64.linCfg (linExt 0) mixColumns (linEnv VG.Proof.Aes.AArch64.qIns) (linPost 9 (VG.Proof.Aes.AArch64.qOuts mcG)) = true := by
  decide +kernel

theorem addRoundKey_check :
    VG.AArch64.Straight.check (lanes 64 10) VG.Proof.Aes.AArch64.arkCfg (linExt 8) addRoundKey (linEnv VG.Proof.Aes.AArch64.qIns) (linPost 10 (VG.Proof.Aes.AArch64.qOuts arkG)) = true := by
  decide +kernel

/-! ## On the machine -/

theorem q_linear {k xb : Nat} {c : Cfg} {is : List Instr} {g : Nat → Nat → List Nat}
    (hchk : VG.AArch64.Straight.check (lanes 64 k) c (linExt xb) is (linEnv VG.Proof.Aes.AArch64.qIns) (linPost k (VG.Proof.Aes.AArch64.qOuts g)) = true)
    (hk : 512 ≤ 2 ^ k)
    (hw : layerKeep.all (fun r => is.all fun i => dstOf i != some r) = true)
    {s : State} (hok : Ok c s) (W : Nat → BitVec 64) (hW : ∀ i < 8, W i = s.gpr (q i))
    (hext : ∀ j < c.exts,
      64 * (xb + j) + 64 ≤ 2 ^ k ∧ W (xb + j) = s.mem.readW (wordAddr (s.gpr c.ext) j) 64) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ j < 8, ∀ p < 64, (s'.gpr (q j)).getLsbD p = xorBits W (g j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ VG.Proof.Aes.AArch64.layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion c s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok hchk hok W (fun r i hri => by
    simp only [VG.Proof.Aes.AArch64.qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
    obtain ⟨i, hi, rfl, rfl⟩ := hri
    exact ⟨by omega, hW i hi⟩) hext
  have hmem : ∀ j < 8, (q j, g j) ∈ VG.Proof.Aes.AArch64.qOuts g := fun j hj => by
    simp only [VG.Proof.Aes.AArch64.qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩
  exact ⟨s', hs', fun j hj p hp => hout (q j) (g j) (hmem j hj) p hp, hrd, hwr, hsp,
    fun r hr => hoth r (VG.Proof.Aes.AArch64.writes_rest hw r hr), hfr⟩

/-- The words of the state registers. -/
abbrev Q (s : State) (i : Nat) : BitVec 64 := s.gpr (q i)

theorem toBs_ok {s : State} (hok : Ok VG.Proof.Aes.AArch64.linCfg s) :
    ∃ s', runBlock isa toBs s = some s' ∧
      (∀ j < 8, ∀ p < 64, (VG.Proof.Aes.AArch64.Q s' j).getLsbD p =
        (VG.Proof.Aes.AArch64.Q s (p % 4 + 4 * (idx p / 8))).getLsbD (8 * (idx p % 8) + j)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ VG.Proof.Aes.AArch64.layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.AArch64.linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := VG.Proof.Aes.AArch64.q_linear VG.Proof.Aes.AArch64.toBs_check (by decide) (by decide +kernel) hok (VG.Proof.Aes.AArch64.Q s)
    (fun _ _ => rfl) (fun j hj => by simp [VG.Proof.Aes.AArch64.linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, toBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by omega)]

theorem fromBs_ok {s : State} (hok : Ok VG.Proof.Aes.AArch64.linCfg s) :
    ∃ s', runBlock isa fromBs s = some s' ∧
      (∀ k < 8, ∀ t < 64, (VG.Proof.Aes.AArch64.Q s' k).getLsbD t = (VG.Proof.Aes.AArch64.Q s (t % 8)).getLsbD (pos (k % 4) (t / 8 + 8 * (k / 4)))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ VG.Proof.Aes.AArch64.layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.AArch64.linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := VG.Proof.Aes.AArch64.q_linear VG.Proof.Aes.AArch64.fromBs_check (by decide) (by decide +kernel) hok (VG.Proof.Aes.AArch64.Q s)
    (fun _ _ => rfl) (fun j hj => by simp [VG.Proof.Aes.AArch64.linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by simp only [pos]; omega)]

theorem shiftRows_ok {s : State} (hok : Ok VG.Proof.Aes.AArch64.linCfg s) :
    ∃ s', runBlock isa shiftRows s = some s' ∧
      (∀ j < 8, ∀ p < 64, (VG.Proof.Aes.AArch64.Q s' j).getLsbD p = (VG.Proof.Aes.AArch64.Q s j).getLsbD (srSrc p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ VG.Proof.Aes.AArch64.layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.AArch64.linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := VG.Proof.Aes.AArch64.q_linear VG.Proof.Aes.AArch64.shiftRows_check (by decide) (by decide +kernel) hok (VG.Proof.Aes.AArch64.Q s)
    (fun _ _ => rfl) (fun j hj => by simp [VG.Proof.Aes.AArch64.linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, srG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by simp only [srSrc]; omega)]

theorem mixColumns_ok {s : State} (hok : Ok VG.Proof.Aes.AArch64.linCfg s) :
    ∃ s', runBlock isa mixColumns s = some s' ∧
      (∀ j < 8, ∀ p < 64, (VG.Proof.Aes.AArch64.Q s' j).getLsbD p = termsXor (VG.Proof.Aes.AArch64.Q s) (mcTerms j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ VG.Proof.Aes.AArch64.layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.AArch64.linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := VG.Proof.Aes.AArch64.q_linear VG.Proof.Aes.AArch64.mixColumns_check (by decide) (by decide +kernel) hok (VG.Proof.Aes.AArch64.Q s)
    (fun _ _ => rfl) (fun j hj => by simp [VG.Proof.Aes.AArch64.linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, mcG, xorBits_map]
  intro wt hwt
  obtain ⟨wk, -, rfl⟩ := List.mem_map.mp hwt
  exact Nat.mod_lt _ (by decide)

/-- Word `j` of the bitsliced round key at `kp`. -/
abbrev keyWord (s : State) (j : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr kp) j) 64

theorem addRoundKey_ok {s : State} (hok : Ok VG.Proof.Aes.AArch64.arkCfg s) :
    ∃ s', runBlock isa addRoundKey s = some s' ∧
      (∀ j < 8, ∀ p < 64, (VG.Proof.Aes.AArch64.Q s' j).getLsbD p = ((VG.Proof.Aes.AArch64.Q s j).getLsbD p ^^ (VG.Proof.Aes.AArch64.keyWord s j).getLsbD p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ VG.Proof.Aes.AArch64.layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.AArch64.arkCfg s] s.mem s'.mem := by
  let W : Nat → BitVec 64 := fun i => if i < 8 then VG.Proof.Aes.AArch64.Q s i else VG.Proof.Aes.AArch64.keyWord s (i - 8)
  obtain ⟨s', hs', hout, rest⟩ := VG.Proof.Aes.AArch64.q_linear VG.Proof.Aes.AArch64.addRoundKey_check (by decide) (by decide +kernel) hok W
    (fun i hi => by simp [W, hi]) (fun j hj => by
      simp only [VG.Proof.Aes.AArch64.arkCfg] at hj ⊢
      refine ⟨by omega, ?_⟩
      simp [W, show ¬ 8 + j < 8 by omega])
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, arkG, xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ hp, bitOf_word _ _ _ hp]
  simp [W, hj, show ¬ 8 + j < 8 by omega]

end VG.Proof.Aes.AArch64

end

/-!
# Encrypting four blocks, bitsliced, on AArch64

`encrypt4_ok`: from four blocks in the registers (`InRel`), with the
bitsliced round keys in the scratch buffer (`KeysAt`), `encrypt4` leaves
the four ciphertexts, having written only the first 384 bytes of the
scratch buffer. The layers are composed from their proofs (above);
the round loop's invariant is the
specification's `foldl` over the rounds done.
-/

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes
open VG.Spec.Aes (roundKey subBytes shiftRows mixColumns addRoundKey cipher)

/-- The bitsliced round keys `0 … R` of the schedule `w`, from `K0`, 64 bytes each. -/
def KeysAt (m : Mem) (K0 : Addr) (R : Nat) (w : List Byte) : Prop :=
  ∀ j ≤ R, KeyRel (fun k => m.readW (wordAddr (K0 + BitVec.ofNat 64 (64 * j)) k) 64) (roundKey w j)

/-- What encryption needs: the scratch buffer (2048 bytes at `x5`) is
writable, and the round keys are in it, the last at byte `lastKey`. -/
structure EncPre (s₀ : State) (R : Nat) (w : List Byte) : Prop where
  scr : (⟨s₀.gpr sb, 2048⟩ : Region) ∈ s₀.wr
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  k0 : s₀.gpr .x0 = s₀.gpr sb + BitVec.ofNat 64 (1920 - 64 * R)
  keys : VG.Proof.Aes.AArch64.KeysAt s₀.mem (s₀.gpr .x0) R w

/-- What stays the same during encryption. -/
structure Ctx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ∉ VG.Proof.Aes.AArch64.layerWrites → r ≠ kp → s.gpr r = s₀.gpr r
  frame : Frame [⟨s₀.gpr sb, 384⟩] s₀.mem s.mem

theorem sb_not : sb ∉ VG.Proof.Aes.AArch64.layerWrites ∧ sb ≠ kp := by decide
theorem x0_not : Reg.x0 ∉ VG.Proof.Aes.AArch64.layerWrites ∧ Reg.x0 ≠ kp := by decide

theorem Ctx.refl (s₀ : State) : VG.Proof.Aes.AArch64.Ctx s₀ s₀ := ⟨rfl, rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _⟩

theorem Ctx.base {s₀ s : State} (hc : VG.Proof.Aes.AArch64.Ctx s₀ s) : s.gpr sb = s₀.gpr sb := hc.keep _ sb_not.1 sb_not.2

theorem Ctx.step {s₀ s s' : State} (hc : VG.Proof.Aes.AArch64.Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hoth : ∀ r, r ∉ VG.Proof.Aes.AArch64.layerWrites → r ≠ kp → s'.gpr r = s.gpr r)
    (hfr : Frame [⟨s.gpr sb, 384⟩] s.mem s'.mem) : VG.Proof.Aes.AArch64.Ctx s₀ s' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r h1 h2 => (hoth r h1 h2).trans (hc.keep r h1 h2),
    hc.frame.trans (by rw [← hc.base]; exact hfr)⟩

theorem Ctx.linOk {s₀ s : State} (hp : (⟨s₀.gpr sb, 2048⟩ : Region) ∈ s₀.wr) (hc : VG.Proof.Aes.AArch64.Ctx s₀ s) :
    Ok VG.Proof.Aes.AArch64.linCfg s :=
  Ok.of_region (r := ⟨s₀.gpr sb, 2048⟩) (by rw [hc.wr]; exact hp) (by simp [VG.Proof.Aes.AArch64.linCfg, hc.base])
    (by simp [VG.Proof.Aes.AArch64.linCfg]) (by simp [VG.Proof.Aes.AArch64.linCfg]) rfl

/-- The key area is outside what the layers write. -/
theorem keys_disjoint (b : Addr) : Region.Disjoint ⟨b + 1024, 1024⟩ ⟨b, 384⟩ :=
  Offset.disjoint_base (d := 1024) b (by omega) (by omega)

theorem addr3 (b : Addr) (x y z : Nat) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 y + BitVec.ofNat 64 z = b + BitVec.ofNat 64 (x + y + z) := by
  rw [BitVec.ofNat_add, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]

theorem off_contains (b : Addr) {base n len k : Nat} (h1 : base ≤ n) (h2 : n + k ≤ base + len)
    (h3 : base + len < 2 ^ 64) :
    (⟨b + BitVec.ofNat 64 base, len⟩ : Region).Contains (b + BitVec.ofNat 64 n) k := Offset.contains b h1 h2 h3

theorem key_contains (b : Addr) {R j k : Nat} (hR : R ≤ 14) (hj : j ≤ R) (hk : k < 8) :
    (⟨b + 1024, 1024⟩ : Region).Contains
      (wordAddr (b + BitVec.ofNat 64 (1920 - 64 * R) + BitVec.ofNat 64 (64 * j)) k) (64 / 8) := by
  simp only [wordAddr]
  rw [VG.Proof.Aes.AArch64.addr3]
  exact VG.Proof.Aes.AArch64.off_contains (base := 1024) b (by omega) (by omega) (by omega)

theorem keyRel_congr {K K' : Nat → BitVec 64} {rk : List Byte} (h : KeyRel K rk)
    (he : ∀ k < 8, K' k = K k) : KeyRel K' rk := by
  intro b hb i hi
  rw [← h b hb i hi]
  exact byte_ext fun j hj => by rw [getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, he j hj]

theorem EncPre.keysAt {s₀ s : State} {R : Nat} {w : List Byte} (hp : VG.Proof.Aes.AArch64.EncPre s₀ R w) (hc : VG.Proof.Aes.AArch64.Ctx s₀ s) :
    VG.Proof.Aes.AArch64.KeysAt s.mem (s₀.gpr .x0) R w := by
  intro j hj
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  refine VG.Proof.Aes.AArch64.keyRel_congr (hp.keys j hj) fun k hk => ?_
  rw [hp.k0]
  exact hc.frame.readW (VG.Proof.Aes.AArch64.key_contains _ hR hj hk)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Aes.AArch64.keys_disjoint _) (by decide)

theorem ark_cfg_ok {s : State} {b : Addr} {n : Nat} (hscr : (⟨b, 2048⟩ : Region) ∈ s.wr)
    (hk : s.gpr kp = b + BitVec.ofNat 64 n) (hn : n + 64 ≤ 2048) : Ok VG.Proof.Aes.AArch64.arkCfg s where
  slotIn k hk := by simp [VG.Proof.Aes.AArch64.arkCfg] at hk
  extIn k hk' := by
    simp only [VG.Proof.Aes.AArch64.arkCfg] at hk'
    refine ⟨⟨b, 2048⟩, List.mem_append_right _ hscr, ?_⟩
    have h := VG.Proof.Aes.AArch64.off_contains (base := 0) (n := n + 8 * k) (len := 2048) (k := 8) b (by omega) (by omega)
      (by omega)
    simp only [BitVec.add_zero] at h
    simpa [VG.Proof.Aes.AArch64.arkCfg, wordAddr, hk, BitVec.ofNat_add, BitVec.add_assoc] using h
  slots := by simp [VG.Proof.Aes.AArch64.arkCfg]
  sep k hk := by simp [VG.Proof.Aes.AArch64.arkCfg] at hk

/-! ## One layer at a time -/

/-- A layer that writes only `layerWrites` and the first 384 bytes of the
scratch buffer keeps `Ctx`. -/
theorem layer_wp {s₀ s : State} {is : List Instr} {P : State → Prop} {Q : State → Prop}
    (hl : ∃ s', runBlock isa is s = some s' ∧ P s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ∉ VG.Proof.Aes.AArch64.layerWrites → s'.gpr r = s.gpr r) ∧ Frame [⟨s.gpr sb, 8 * 48⟩] s.mem s'.mem)
    (hc : VG.Proof.Aes.AArch64.Ctx s₀ s)
    (hQ : ∀ s', VG.Proof.Aes.AArch64.Ctx s₀ s' → P s' → s'.gpr kp = s.gpr kp → Q s') : WP isa (.block is) s Q := by
  obtain ⟨s', hs', hP, hrd, hwr, hsp, hoth, hfr⟩ := hl
  exact WP.of_runBlock ⟨s', hs', hQ s' (hc.step hrd hwr hsp (fun r h _ => hoth r h) hfr) hP
    (hoth kp (by decide))⟩

/-! ## The rounds -/

/-- A middle round of the specification (round `j`). -/
def rnd (w : List Byte) (j : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  addRoundKey (mixColumns (shiftRows (subBytes x))) (roundKey w j)

/-- Rounds `1 … m`, as `cipher` folds them. -/
def midRounds (w : List Byte) (m : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  (List.range m).foldl (fun s j => VG.Proof.Aes.AArch64.rnd w (j + 1) s) x

theorem midRounds_succ (w : List Byte) (m : Nat) (x : Spec.Aes.State) :
    VG.Proof.Aes.AArch64.midRounds w (m + 1) x = VG.Proof.Aes.AArch64.rnd w (m + 1) (VG.Proof.Aes.AArch64.midRounds w m x) := by
  simp [VG.Proof.Aes.AArch64.midRounds, List.range_succ, List.foldl_append]

theorem kp_step (K : Addr) (m : Nat) :
    K + BitVec.ofNat 64 (64 * m) + BitVec.ofNat 64 64 = K + BitVec.ofNat 64 (64 * (m + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 64 * m + 64 = 64 * (m + 1) by omega]

theorem q_ne_kp (i : Nat) : q i ≠ kp := by
  unfold q; split <;> decide

theorem q_ne_t0 (i : Nat) : q i ≠ t0 := by
  unfold q; split <;> decide

/-- `add kp, kp, #64`. -/
theorem addKp_wp {s₀ s : State} {P : State → Prop} (hc : VG.Proof.Aes.AArch64.Ctx s₀ s)
    (h : ∀ s', VG.Proof.Aes.AArch64.Ctx s₀ s' → s'.gpr kp = s.gpr kp + BitVec.ofNat 64 64 →
      (∀ i, VG.Proof.Aes.AArch64.Q s' i = VG.Proof.Aes.AArch64.Q s i) → P s') :
    WP isa (.block [.addImm .x kp kp 64]) s P := by
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_addImm_x (by decide), runStep_some,
    runBlock_nil], h _ ?_ ?_ ?_⟩
  · exact hc.step rfl rfl rfl (fun r _ hr => by simp [State.write, hr]) (Frame.refl _ _)
  · simp [State.write, State.read]
  · intro i; simp [VG.Proof.Aes.AArch64.Q, State.write, VG.Proof.Aes.AArch64.q_ne_kp i]

/-- `sub t0, kp, x5; sub t0, t0, #(lastKey - 64)`. -/
theorem cmpLast_wp {s₀ s : State} {P : State → Prop} (hc : VG.Proof.Aes.AArch64.Ctx s₀ s)
    (h : ∀ s', VG.Proof.Aes.AArch64.Ctx s₀ s' → s'.gpr kp = s.gpr kp → (∀ i, VG.Proof.Aes.AArch64.Q s' i = VG.Proof.Aes.AArch64.Q s i) →
      s'.gpr t0 = s.gpr kp - s.gpr sb - BitVec.ofNat 64 (lastKey - 64) → P s') :
    WP isa (.block [.sub .x t0 kp sb, .subImm .x t0 t0 (lastKey - 64)]) s P := by
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, show exec (.sub .x t0 kp sb) s =
    some (s.write .x t0 (s.read .x kp - s.read .x sb)) from rfl, runStep_some, runBlock_cons,
    exec_subImm_x (by decide), runStep_some, runBlock_nil], h _ ?_ ?_ ?_ ?_⟩
  · exact hc.step rfl rfl rfl (fun r hr _ => by
      have : r ≠ t0 := fun h => hr (h ▸ by decide)
      simp [State.write, this]) (Frame.refl _ _)
  · simp [State.write, t0, kp]
  · intro i; simp [VG.Proof.Aes.AArch64.Q, State.write, VG.Proof.Aes.AArch64.q_ne_t0 i]
  · simp [State.write, State.read]

theorem t0_last (b : Addr) {R m : Nat} (hR : R ≤ 14) (hm : m + 1 < R) :
    (b + BitVec.ofNat 64 (1920 - 64 * R + 64 * (m + 1)) - b - BitVec.ofNat 64 (lastKey - 64) != 0) =
      !decide (m + 2 = R) := by
  simp only [lastKey]
  by_cases h : m + 2 = R
  · have e : b + BitVec.ofNat 64 (1920 - 64 * R + 64 * (m + 1)) - b - BitVec.ofNat 64 (1920 - 64) = 0 := by
      bv_omega
    rw [e]; simp [h]
  · have e : b + BitVec.ofNat 64 (1920 - 64 * R + 64 * (m + 1)) - b - BitVec.ofNat 64 (1920 - 64) ≠ 0 := by
      intro h'; apply h; bv_omega
    simpa [h] using e

theorem kp_off (K0 b : Addr) {R j : Nat} (hk : K0 = b + BitVec.ofNat 64 (1920 - 64 * R)) :
    K0 + BitVec.ofNat 64 (64 * j) = b + BitVec.ofNat 64 (1920 - 64 * R + 64 * j) := by
  rw [hk, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem ark_frame {s₀ s s' : State} (hc : VG.Proof.Aes.AArch64.Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hoth : ∀ r, r ∉ VG.Proof.Aes.AArch64.layerWrites → s'.gpr r = s.gpr r)
    (hfr : Frame [slotRegion VG.Proof.Aes.AArch64.arkCfg s] s.mem s'.mem) : VG.Proof.Aes.AArch64.Ctx s₀ s' :=
  hc.step hrd hwr hsp (fun r h _ => hoth r h)
    (hfr.sub fun r hr => ⟨_, List.mem_singleton_self _, fun a ha => by
      simp only [List.mem_singleton] at hr; subst hr
      simp [slotRegion, VG.Proof.Aes.AArch64.arkCfg, Region.Contains] at ha⟩)

/-- A middle round. -/
theorem round_ok {s₀ s : State} {R m : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : VG.Proof.Aes.AArch64.EncPre s₀ R w) (hc : VG.Proof.Aes.AArch64.Ctx s₀ s) (hk : s.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * m))
    (hm : m + 1 < R) (hbs : BsRel (VG.Proof.Aes.AArch64.Q s) T) :
    WP isa (.block roundBody) s fun s' => VG.Proof.Aes.AArch64.Ctx s₀ s' ∧
      s'.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * (m + 1)) ∧
      BsRel (VG.Proof.Aes.AArch64.Q s') (fun b => VG.Proof.Aes.AArch64.rnd w (m + 1) (T b)) ∧
      AArch64.eval (.nonzero .x t0) s' = some (!decide (m + 2 = R)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  simp only [roundBody]
  repeat rw [WP.block_append_iff (M := isa)]
  refine VG.Proof.Aes.AArch64.addKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
  rw [hk, VG.Proof.Aes.AArch64.kp_step] at hk₁
  have hbs₁ : BsRel (VG.Proof.Aes.AArch64.Q s₁) T := by
    have : VG.Proof.Aes.AArch64.Q s₁ = VG.Proof.Aes.AArch64.Q s := funext hq₁
    rw [this]; exact hbs
  refine VG.Proof.Aes.AArch64.layer_wp (VG.Proof.Aes.AArch64.sbox_ok (hc₁.linOk hp.scr)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
  have hbs₂ := bs_subBytes h₂ hbs₁
  refine VG.Proof.Aes.AArch64.layer_wp (VG.Proof.Aes.AArch64.shiftRows_ok (hc₂.linOk hp.scr)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
  have hbs₃ := bs_shiftRows h₃ hbs₂
  refine VG.Proof.Aes.AArch64.layer_wp (VG.Proof.Aes.AArch64.mixColumns_ok (hc₃.linOk hp.scr)) hc₃ fun s₄ hc₄ h₄ hk₄ => ?_
  have hbs₄ := bs_mixColumns h₄ hbs₃
  have hk₄' : s₄.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * (m + 1)) := by rw [hk₄, hk₃, hk₂, hk₁]
  have hok : Ok VG.Proof.Aes.AArch64.arkCfg s₄ := VG.Proof.Aes.AArch64.ark_cfg_ok (b := s₀.gpr sb) (by rw [hc₄.wr]; exact hp.scr)
    (by rw [hk₄', VG.Proof.Aes.AArch64.kp_off _ _ hp.k0]) (by omega)
  have hkey : KeyRel (VG.Proof.Aes.AArch64.keyWord s₄) (roundKey w (m + 1)) := by
    have := hp.keysAt hc₄ (m + 1) (by omega)
    unfold VG.Proof.Aes.AArch64.keyWord; rw [hk₄']; exact this
  obtain ⟨s₅, hs₅, h₅, hrd, hwr, hsp, hoth, hfr⟩ := VG.Proof.Aes.AArch64.addRoundKey_ok hok
  have hc₅ : VG.Proof.Aes.AArch64.Ctx s₀ s₅ := VG.Proof.Aes.AArch64.ark_frame hc₄ hrd hwr hsp hoth hfr
  have hbs₅ := bs_addRoundKey h₅ hbs₄ hkey
  refine WP.of_runBlock ⟨s₅, hs₅, ?_⟩
  refine VG.Proof.Aes.AArch64.cmpLast_wp hc₅ fun s₆ hc₆ hk₆ hq₆ ht₆ => ⟨hc₆, ?_, ?_, ?_⟩
  · rw [hk₆, hoth kp (by decide), hk₄']
  · have : VG.Proof.Aes.AArch64.Q s₆ = VG.Proof.Aes.AArch64.Q s₅ := funext hq₆
    rw [this]; exact hbs₅
  · simp only [AArch64.eval, State.read, Size.bits, BitVec.setWidth_eq, ht₆]
    rw [hoth kp (by decide), hk₄', hoth sb (by decide), hc₄.base, VG.Proof.Aes.AArch64.kp_off _ _ hp.k0, VG.Proof.Aes.AArch64.t0_last _ hR hm]

/-- `mov kp, x0`. -/
theorem movKp_wp {s₀ s : State} {P : State → Prop} (hc : VG.Proof.Aes.AArch64.Ctx s₀ s)
    (h : ∀ s', VG.Proof.Aes.AArch64.Ctx s₀ s' → s'.gpr kp = s.gpr .x0 → (∀ i, VG.Proof.Aes.AArch64.Q s' i = VG.Proof.Aes.AArch64.Q s i) → P s') :
    WP isa (.block [movR kp .x0]) s P := by
  refine WP.of_runBlock ⟨_, by rw [movR, runBlock_cons, exec_addImm_x (by decide), runStep_some,
    runBlock_nil], h _ ?_ ?_ ?_⟩
  · exact hc.step rfl rfl rfl (fun r _ hr => by simp [State.write, hr]) (Frame.refl _ _)
  · simp [State.write, State.read]
  · intro i; simp [VG.Proof.Aes.AArch64.Q, State.write, VG.Proof.Aes.AArch64.q_ne_kp i]

theorem ark_step {s₀ s : State} {R j : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : VG.Proof.Aes.AArch64.EncPre s₀ R w) (hc : VG.Proof.Aes.AArch64.Ctx s₀ s) (hk : s.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * j))
    (hj : j ≤ R) (hbs : BsRel (VG.Proof.Aes.AArch64.Q s) T) {P : State → Prop}
    (h : ∀ s', VG.Proof.Aes.AArch64.Ctx s₀ s' → s'.gpr kp = s.gpr kp → BsRel (VG.Proof.Aes.AArch64.Q s') (fun b => addRoundKey (T b) (roundKey w j)) →
      P s') : WP isa (.block addRoundKey) s P := by
  have hok : Ok VG.Proof.Aes.AArch64.arkCfg s := VG.Proof.Aes.AArch64.ark_cfg_ok (b := s₀.gpr sb) (by rw [hc.wr]; exact hp.scr)
    (by rw [hk, VG.Proof.Aes.AArch64.kp_off _ _ hp.k0]) (by rcases hp.rounds with h | h | h <;> omega)
  have hkey : KeyRel (VG.Proof.Aes.AArch64.keyWord s) (roundKey w j) := by
    have := hp.keysAt hc j hj
    unfold VG.Proof.Aes.AArch64.keyWord; rw [hk]; exact this
  obtain ⟨s', hs', h', hrd, hwr, hsp, hoth, hfr⟩ := VG.Proof.Aes.AArch64.addRoundKey_ok hok
  exact WP.of_runBlock ⟨s', hs', h s' (VG.Proof.Aes.AArch64.ark_frame hc hrd hwr hsp hoth hfr) (hoth kp (by decide))
    (bs_addRoundKey h' hbs hkey)⟩

theorem cipher_eq (R : Nat) (w : List Byte) (x : Spec.Aes.State) :
    cipher R w x = addRoundKey (shiftRows (subBytes (VG.Proof.Aes.AArch64.midRounds w (R - 1)
      (addRoundKey x (roundKey w 0))))) (roundKey w R) := rfl

/-- Four blocks, from `InRel` to `InRel` of their encryptions. -/
theorem encrypt4_ok {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}
    (hp : VG.Proof.Aes.AArch64.EncPre s₀ R w) (hin : InRel (VG.Proof.Aes.AArch64.Q s₀) S) :
    WP isa encrypt4 s₀ fun s => VG.Proof.Aes.AArch64.Ctx s₀ s ∧ InRel (VG.Proof.Aes.AArch64.Q s) (fun b => cipher R w (S b)) := by
  have hR1 : 2 ≤ R := by rcases hp.rounds with h | h | h <;> omega
  let A : Nat → Spec.Aes.State := fun b => addRoundKey (S b) (roundKey w 0)
  -- The rounds done so far.
  let Inv : Nat → State → Prop := fun n s => ∃ m, n = R - 1 - m ∧ m + 1 < R ∧ VG.Proof.Aes.AArch64.Ctx s₀ s ∧
    s.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * m) ∧ BsRel (VG.Proof.Aes.AArch64.Q s) (fun b => VG.Proof.Aes.AArch64.midRounds w m (A b))
  let Mid : State → Prop := fun s => VG.Proof.Aes.AArch64.Ctx s₀ s ∧
    s.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * (R - 1)) ∧
    BsRel (VG.Proof.Aes.AArch64.Q s) (fun b => VG.Proof.Aes.AArch64.midRounds w (R - 1) (A b))
  refine WP.seq (WP.mono (Q := Inv (R - 1)) ?_ fun s h => WP.seq (WP.mono (Q := Mid) ?_ fun s h => ?_))
  · -- toBs, the first round key.
    repeat rw [WP.block_append_iff (M := isa)]
    refine VG.Proof.Aes.AArch64.layer_wp (VG.Proof.Aes.AArch64.toBs_ok ((Ctx.refl s₀).linOk hp.scr)) (Ctx.refl s₀) fun s₁ hc₁ h₁ _ => ?_
    have hbs₁ := bs_of_in h₁ hin
    refine VG.Proof.Aes.AArch64.movKp_wp hc₁ fun s₂ hc₂ hk₂ hq₂ => ?_
    have hbs₂ : BsRel (VG.Proof.Aes.AArch64.Q s₂) S := by
      have : VG.Proof.Aes.AArch64.Q s₂ = VG.Proof.Aes.AArch64.Q s₁ := funext hq₂
      rw [this]; exact hbs₁
    have hk₂' : s₂.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * 0) := by
      rw [hk₂, hc₁.keep _ x0_not.1 x0_not.2]; simp
    exact VG.Proof.Aes.AArch64.ark_step hp hc₂ hk₂' (by omega) hbs₂ fun s₃ hc₃ hk₃ hbs₃ =>
      ⟨0, by omega, by omega, hc₃, by rw [hk₃, hk₂'], hbs₃⟩
  · -- The middle rounds.
    refine WP.loop (M := isa) Inv (fun n s hs => ?_) (R - 1) s h
    obtain ⟨m, rfl, hm, hc, hk, hbs⟩ := hs
    refine WP.mono (VG.Proof.Aes.AArch64.round_ok hp hc hk hm hbs) fun s' ⟨hc', hk', hbs', hz⟩ => ?_
    by_cases hlast : m + 2 = R
    · refine .inl ⟨hz.trans (by simp [hlast]), hc', ?_, ?_⟩
      · rw [hk']; congr 3; omega
      · rw [show R - 1 = m + 1 by omega]
        intro b hb i hi
        rw [hbs' b hb i hi]; simp only [VG.Proof.Aes.AArch64.midRounds_succ]
    · refine .inr ⟨hz.trans (by simp [hlast]), R - 1 - (m + 1), by omega, m + 1, rfl, by omega, hc',
        hk', fun b hb i hi => by rw [hbs' b hb i hi]; simp only [VG.Proof.Aes.AArch64.midRounds_succ]⟩
  · -- The last round, and back to blocks.
    obtain ⟨hc, hk, hbs⟩ := h
    rw [WP.block_append_iff (M := isa)]
    simp only [lastRound]
    repeat rw [WP.block_append_iff (M := isa)]
    refine VG.Proof.Aes.AArch64.addKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
    rw [hk, VG.Proof.Aes.AArch64.kp_step, show R - 1 + 1 = R by omega] at hk₁
    have hbs₁ : BsRel (VG.Proof.Aes.AArch64.Q s₁) (fun b => VG.Proof.Aes.AArch64.midRounds w (R - 1) (A b)) := by
      have : VG.Proof.Aes.AArch64.Q s₁ = VG.Proof.Aes.AArch64.Q s := funext hq₁
      rw [this]; exact hbs
    refine VG.Proof.Aes.AArch64.layer_wp (VG.Proof.Aes.AArch64.sbox_ok (hc₁.linOk hp.scr)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
    have hbs₂ := bs_subBytes h₂ hbs₁
    refine VG.Proof.Aes.AArch64.layer_wp (VG.Proof.Aes.AArch64.shiftRows_ok (hc₂.linOk hp.scr)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
    have hbs₃ := bs_shiftRows h₃ hbs₂
    refine VG.Proof.Aes.AArch64.ark_step hp hc₃ (by rw [hk₃, hk₂, hk₁]) (Nat.le_refl R) hbs₃ fun s₄ hc₄ _ hbs₄ => ?_
    refine VG.Proof.Aes.AArch64.layer_wp (VG.Proof.Aes.AArch64.fromBs_ok (hc₄.linOk hp.scr)) hc₄ fun s₅ hc₅ h₅ _ => ⟨hc₅, ?_⟩
    have := in_of_bs h₅ hbs₄
    intro b hb i hi j hj
    rw [this b hb i hi j hj]; simp only [VG.Proof.Aes.AArch64.cipher_eq]; rfl

end VG.Proof.Aes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.AArch64.Group`. -/
section

section

/-!
# Bitslicing the round keys, on AArch64

The key loop of `vg_aes_ctr32` bitslices each round key (loaded as four
identical blocks) with `toBs` and stores it in the scratch buffer. The
loads and stores are checked by evaluation over the naming domain
(`Bitslice.names`), `toBs` by its proof (`Encrypt.lean`).
-/

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes
open VG.Spec.Aes (roundKey)

/-! ## Loading a round key -/

def loadCfg : Cfg := { base := sb, slots := 0, ext := .x0, exts := 2 }

def loadPost (e : Env Nat) : Bool :=
  (List.range 4).all fun b => e.reg (q b) == some 0 && e.reg (q (b + 4)) == some 1

theorem keyLoad_check :
    VG.AArch64.Straight.check (names 64) VG.Proof.Aes.AArch64.loadCfg (fun k => some k) keyLoad { reg := fun _ => none, slot := fun _ => none }
      VG.Proof.Aes.AArch64.loadPost = true := by
  decide +kernel

/-- The registers the key loop writes. -/
def keyWrites : List Reg := .x0 :: .x1 :: .x2 :: VG.Proof.Aes.AArch64.layerWrites

theorem keyLoad_ok {s : State} {r : Region} {off : Nat} (hr : r ∈ s.rd ++ s.wr)
    (hb : s.gpr .x0 = r.base + BitVec.ofNat 64 off) (hoff : off + 16 ≤ r.len) (hn : r.len < 2 ^ 64) :
    ∃ s', runBlock isa keyLoad s = some s' ∧
      (∀ b < 4, s'.gpr (q b) = s.mem.readW (wordAddr (s.gpr .x0) 0) 64 ∧
        s'.gpr (q (b + 4)) = s.mem.readW (wordAddr (s.gpr .x0) 1) 64) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ∉ VG.Proof.Aes.AArch64.layerWrites → s'.gpr r = s.gpr r) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.Aes.AArch64.keyLoad_check
  have hok : Ok VG.Proof.Aes.AArch64.loadCfg s := Ok.of_ext (r := r) hr hb (by simp [VG.Proof.Aes.AArch64.loadCfg]; omega) hn rfl
  let V : Nat → BitVec 64 := fun k => s.mem.readW (wordAddr (s.gpr .x0) k) 64
  have hrel : Rel (NameRel V) VG.Proof.Aes.AArch64.loadCfg (fun k => some k) { reg := fun _ => none, slot := fun _ => none } s := by
    refine ⟨(fun _ _ h => by cases h), (fun _ _ _ h => by cases h), fun k a hk h => ?_,
      (fun _ _ h => by cases h)⟩
    simp only [Option.some.injEq] at h; subst h; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) hok hrel he
  refine ⟨s', hs', fun b hb => ?_, p.rd, p.wr, p.sp, ?_, fun r hr => p.other r ?_⟩
  · have := List.all_eq_true.mp hpost b (List.mem_range.mpr hb)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨p.rel.reg _ _ this.1, p.rel.reg _ _ this.2⟩
  · funext x
    exact p.frame x fun r' hr' hc => by
      simp only [List.mem_singleton] at hr'; subst hr'
      simp [slotRegion, VG.Proof.Aes.AArch64.loadCfg, Region.Contains] at hc
  · exact Bool.ne_false_of_eq_true (VG.Proof.Aes.AArch64.writes_rest (is := keyLoad) (by decide +kernel) r hr)

/-! ## Storing it -/

def storeCfg : Cfg := { base := .x1, slots := 8, ext := .x1, exts := 0 }

def storeEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)), slot := fun _ => none }

def storePost (e : Env Nat) : Bool := (List.range 8).all fun k => e.slot k == some k

theorem keyStore_check : VG.AArch64.Straight.check (names 64) VG.Proof.Aes.AArch64.storeCfg (fun _ => none) keyStore VG.Proof.Aes.AArch64.storeEnv VG.Proof.Aes.AArch64.storePost = true := by
  decide +kernel

theorem keyStore_ok {s : State} {r : Region} {off : Nat} (hr : r ∈ s.wr)
    (hb : s.gpr .x1 = r.base + BitVec.ofNat 64 off) (hoff : off + 64 ≤ r.len) (hn : r.len < 2 ^ 64) :
    ∃ s', runBlock isa keyStore s = some s' ∧
      (∀ k < 8, s'.mem.readW (wordAddr (s.gpr .x1) k) 64 = s.gpr (q k)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr = s.gpr ∧
      Frame [⟨s.gpr .x1, 64⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.Aes.AArch64.keyStore_check
  have hok : Ok VG.Proof.Aes.AArch64.storeCfg s := Ok.of_off (r := r) hr hb (by simp [VG.Proof.Aes.AArch64.storeCfg]; omega) hn rfl
  let V : Nat → BitVec 64 := fun k => s.gpr (q k)
  have hrel : Rel (NameRel V) VG.Proof.Aes.AArch64.storeCfg (fun _ => none) VG.Proof.Aes.AArch64.storeEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ hk _ => by simp [VG.Proof.Aes.AArch64.storeCfg] at hk),
      (fun _ _ h => by cases h)⟩
    simp only [VG.Proof.Aes.AArch64.storeEnv] at h
    have h1 := List.find?_some h
    simp only [beq_iff_eq] at h1; subst h1; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) hok hrel he
  refine ⟨s', hs', fun k hk => ?_, p.rd, p.wr, p.sp, ?_, p.frame⟩
  · have := List.all_eq_true.mp hpost k (List.mem_range.mpr hk)
    simp only [beq_iff_eq] at this
    have h := p.rel.slot k k hk this
    rw [p.base] at h
    exact h
  · funext r
    exact p.other r (by
      have : (keyStore.all fun i => dstOf i != some r) = true := by
        simp [keyStore, dstOf]
      simp [this])

/-! ## Stepping back -/

theorem keyStep_ok (s : State) :
    ∃ s', runBlock isa keyStep s = some s' ∧
      s'.gpr .x0 = s.gpr .x0 - 16 ∧ s'.gpr .x1 = s.gpr .x1 - 64 ∧ s'.gpr .x2 = s.gpr .x2 - 1 ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by rw [keyStep, runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_cons,
    exec_subImm_x (by decide), runStep_some, runBlock_cons, exec_subImm_x (by decide), runStep_some,
    runBlock_nil], ?_⟩
  refine ⟨by simp [State.write, State.read], by simp [State.write, State.read],
    by simp [State.write, State.read], fun r h1 h2 h3 => by simp [State.write, h1, h2, h3], rfl, rfl,
    rfl, rfl⟩

/-! ## Readings and regions -/

theorem readW_bit (m : Mem) (a : Addr) {i t : Nat} (hi : i < 8) (ht : t < 8) :
    (m.readW a 64).getLsbD (8 * i + t) = (m (a + BitVec.ofNat 64 i)).getLsbD t := by
  rw [← Mem.extractLsb'_read m a (n := 8) hi, BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, ht, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_setWidth]
  simp [show 8 * i + t < 64 by omega]

theorem base_sub (b : Addr) {lx ly : Nat} (h : lx ≤ ly) (hy : ly < 2 ^ 64) :
    Region.Sub ⟨b, lx⟩ ⟨b + BitVec.ofNat 64 0, ly⟩ := by
  intro a h
  simp only [Region.Contains] at h ⊢
  bv_omega

/-! ## The loop -/

/-- Where the loop runs: the scratch buffer at `b`, the key schedule `w`
at `sc` (as the bytes there). -/
structure KSetup (s₀ : State) (b sc : Addr) (R : Nat) (w : List Byte) : Prop where
  scr : (⟨b, 2048⟩ : Region) ∈ s₀.wr
  base : s₀.gpr sb = b
  sch : (⟨sc, 240⟩ : Region) ∈ s₀.rd ++ s₀.wr
  sep : Region.Disjoint ⟨sc, 240⟩ ⟨b, 2048⟩
  rounds : R ≤ 14
  w : ∀ i < 16 * (R + 1), w.getD i 0 = s₀.mem (sc + BitVec.ofNat 64 i)

/-- The address of bitsliced round key `i`. -/
abbrev keyAddr (b : Addr) (R i : Nat) : Addr := b + BitVec.ofNat 64 (1920 - 64 * (R - i))

/-- Before bitslicing round key `j`. -/
structure KInv (s₀ : State) (b sc : Addr) (R : Nat) (w : List Byte) (j : Nat) (s : State) : Prop where
  hj : j ≤ R
  x2 : s.gpr .x2 = BitVec.ofNat 64 (j + 1)
  x0 : s.gpr .x0 = sc + BitVec.ofNat 64 (16 * j)
  x1 : s.gpr .x1 = VG.Proof.Aes.AArch64.keyAddr b R j
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ∉ VG.Proof.Aes.AArch64.keyWrites → s.gpr r = s₀.gpr r
  frame : Frame [⟨b + BitVec.ofNat 64 0, 384⟩, ⟨b + BitVec.ofNat 64 1024, 1024⟩] s₀.mem s.mem
  done : ∀ i, j < i → i ≤ R →
    KeyRel (fun k => s.mem.readW (wordAddr (VG.Proof.Aes.AArch64.keyAddr b R i) k) 64) (roundKey w i)

/-- After the loop. -/
structure KDone (s₀ : State) (b : Addr) (R : Nat) (w : List Byte) (s : State) : Prop where
  x1 : s.gpr .x1 = VG.Proof.Aes.AArch64.keyAddr b R 0 - 64
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ∉ VG.Proof.Aes.AArch64.keyWrites → s.gpr r = s₀.gpr r
  frame : Frame [⟨b + BitVec.ofNat 64 0, 384⟩, ⟨b + BitVec.ofNat 64 1024, 1024⟩] s₀.mem s.mem
  keys : ∀ i ≤ R, KeyRel (fun k => s.mem.readW (wordAddr (VG.Proof.Aes.AArch64.keyAddr b R i) k) 64) (roundKey w i)

theorem roundKey_getD {w : List Byte} {j i : Nat} (hi : i < 16) :
    (roundKey w j).getD i 0 = w.getD (16 * j + i) 0 := by
  simp only [roundKey, List.getD_eq_getElem?_getD, List.getElem?_take, hi, ite_true,
    List.getElem?_drop]

theorem frame_regions (b : Addr) : ∀ r ∈ [(⟨b + BitVec.ofNat 64 0, 384⟩ : Region),
    ⟨b + BitVec.ofNat 64 1024, 1024⟩], Region.Sub r ⟨b + BitVec.ofNat 64 0, 2048⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.sub b (by omega) (by omega)
  · exact Offset.sub b (by omega) (by omega)

theorem wordAddr_off (b : Addr) (x k : Nat) : wordAddr (b + BitVec.ofNat 64 x) k = b + BitVec.ofNat 64 (x + 8 * k) := by
  rw [wordAddr, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem readW_off_frame {m m' : Mem} {b : Addr} {rs : List Region} (hf : Frame rs m m') {x : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 x, 8⟩ r) :
    m'.readW (b + BitVec.ofNat 64 x) 64 = m.readW (b + BitVec.ofNat 64 x) 64 :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-- The schedule's bytes are those of `w`. -/
theorem KInv.sched {s₀ : State} {b sc : Addr} {R : Nat} {w : List Byte} (hk : VG.Proof.Aes.AArch64.KSetup s₀ b sc R w)
    {j : Nat} {s : State} (hi : VG.Proof.Aes.AArch64.KInv s₀ b sc R w j s) {i : Nat} (hi16 : i < 16) :
    s.mem (sc + BitVec.ofNat 64 (16 * j + i)) = (roundKey w j).getD i 0 := by
  have hjR := hi.hj
  have hR := hk.rounds
  rw [VG.Proof.Aes.AArch64.roundKey_getD hi16, hk.w _ (by omega)]
  refine hi.frame _ fun r hr hc => ?_
  have hsub := VG.Proof.Aes.AArch64.frame_regions b r hr
  refine hk.sep _ ?_ (by simpa using hsub _ hc)
  simp only [Region.Contains]
  rw [show sc + BitVec.ofNat 64 (16 * j + i) - sc = BitVec.ofNat 64 (16 * j + i) by bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The round key as a state. -/
def rkv (w : List Byte) (j : Nat) : Spec.Aes.State := Vector.ofFn fun i => (roundKey w j).getD i 0

theorem keyRel_of_bs {K : Nat → BitVec 64} {w : List Byte} {j : Nat}
    (h : BsRel K fun _ => VG.Proof.Aes.AArch64.rkv w j) : KeyRel K (roundKey w j) := by
  intro b hb i hi
  rw [h b hb i hi, getD_eq _ hi, VG.Proof.Aes.AArch64.rkv, Vector.getElem_ofFn]

theorem keyWrites_not (r : Reg) (hr : r ∉ VG.Proof.Aes.AArch64.keyWrites) :
    r ∉ VG.Proof.Aes.AArch64.layerWrites ∧ r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 := by
  revert hr; cases r <;> decide

theorem add_ofNat_sub (b : Addr) {x y : Nat} (h : y ≤ x) :
    b + BitVec.ofNat 64 x - BitVec.ofNat 64 y = b + BitVec.ofNat 64 (x - y) := by
  rw [show x = (x - y) + y by omega, BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

theorem ofNat_sub_one {j : Nat} (h : 0 < j) : BitVec.ofNat 64 j - 1 = BitVec.ofNat 64 (j - 1) := by
  rw [show j = (j - 1) + 1 by omega, BitVec.ofNat_add, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

theorem keyAddr_pred (b : Addr) {R j : Nat} (hR : R ≤ 14) (hj : 0 < j) (hjR : j ≤ R) :
    VG.Proof.Aes.AArch64.keyAddr b R j - 64 = VG.Proof.Aes.AArch64.keyAddr b R (j - 1) := by
  simp only [VG.Proof.Aes.AArch64.keyAddr]
  rw [show 1920 - 64 * (R - j) = (1920 - 64 * (R - (j - 1))) + 64 by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem keyBody_ok {s₀ : State} {b sc : Addr} {R : Nat} {w : List Byte} (hk : VG.Proof.Aes.AArch64.KSetup s₀ b sc R w)
    {j : Nat} {s : State} (hi : VG.Proof.Aes.AArch64.KInv s₀ b sc R w j s) :
    WP isa (.block keyBody) s fun s' =>
      (j = 0 ∧ AArch64.eval (.nonzero .x .x2) s' = some false ∧ VG.Proof.Aes.AArch64.KDone s₀ b R w s') ∨
      (0 < j ∧ AArch64.eval (.nonzero .x .x2) s' = some true ∧ VG.Proof.Aes.AArch64.KInv s₀ b sc R w (j - 1) s') := by
  have hR := hk.rounds
  have hjR := hi.hj
  have hsb : s.gpr sb = b := by rw [hi.keep sb (by decide), hk.base]
  simp only [keyBody]
  repeat rw [WP.block_append_iff (M := isa)]
  -- Load the round key.
  obtain ⟨s₁, hs₁, hq₁, hrd₁, hwr₁, hsp₁, hm₁, hoth₁⟩ := VG.Proof.Aes.AArch64.keyLoad_ok (r := ⟨sc, 240⟩) (off := 16 * j)
    (by rw [hi.rd, hi.wr]; exact hk.sch) hi.x0 (by simp only; omega) (by simp only; omega)
  refine WP.of_runBlock ⟨s₁, hs₁, ?_⟩
  have hin : InRel (VG.Proof.Aes.AArch64.Q s₁) fun _ => VG.Proof.Aes.AArch64.rkv w j := by
    intro bb hb i hi16 t ht
    have hbyte := hi.sched hk hi16
    rw [getD_eq _ hi16, VG.Proof.Aes.AArch64.rkv, Vector.getElem_ofFn]
    simp only [VG.Proof.Aes.AArch64.Q]
    by_cases h8 : i < 8
    · rw [show bb + 4 * (i / 8) = bb by omega, (hq₁ bb hb).1, show i % 8 = i by omega,
        VG.Proof.Aes.AArch64.readW_bit _ _ h8 ht, wordAddr, hi.x0, ← hbyte]
      congr 2; rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega
    · rw [show bb + 4 * (i / 8) = bb + 4 by omega, (hq₁ bb hb).2, VG.Proof.Aes.AArch64.readW_bit _ _ (by omega) ht,
        wordAddr, hi.x0, ← hbyte]
      congr 2; rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega
  -- Bitslice it.
  have hok₁ : Ok VG.Proof.Aes.AArch64.linCfg s₁ := Ok.of_region (r := ⟨b, 2048⟩) (by rw [hwr₁, hi.wr]; exact hk.scr)
    (by simp only [VG.Proof.Aes.AArch64.linCfg]; rw [hoth₁ sb (by decide), hsb]) (by simp [VG.Proof.Aes.AArch64.linCfg]) (by simp [VG.Proof.Aes.AArch64.linCfg]) rfl
  obtain ⟨s₂, hs₂, hq₂, hrd₂, hwr₂, hsp₂, hoth₂, hfr₂⟩ := VG.Proof.Aes.AArch64.toBs_ok hok₁
  refine WP.of_runBlock ⟨s₂, hs₂, ?_⟩
  have hbs₂ := bs_of_in hq₂ hin
  -- Store it.
  have hx1₂ : s₂.gpr .x1 = VG.Proof.Aes.AArch64.keyAddr b R j := by
    rw [hoth₂ .x1 (by decide), hoth₁ .x1 (by decide), hi.x1]
  obtain ⟨s₃, hs₃, hst₃, hrd₃, hwr₃, hsp₃, hg₃, hfr₃⟩ := VG.Proof.Aes.AArch64.keyStore_ok (r := ⟨b, 2048⟩)
    (off := 1920 - 64 * (R - j)) (by rw [hwr₂, hwr₁, hi.wr]; exact hk.scr) hx1₂
    (by simp only; omega) (by simp only; omega)
  refine WP.of_runBlock ⟨s₃, hs₃, ?_⟩
  -- Step back.
  obtain ⟨s₄, hs₄, hx0₄, hx1₄, hx2₄, hoth₄, hm₄, hrd₄, hwr₄, hsp₄⟩ := VG.Proof.Aes.AArch64.keyStep_ok s₃
  refine WP.of_runBlock ⟨s₄, hs₄, ?_⟩
  have hsb₁ : s₁.gpr sb = b := by rw [hoth₁ sb (by decide), hsb]
  -- What is kept.
  have hkeep : ∀ r, r ∉ VG.Proof.Aes.AArch64.keyWrites → s₄.gpr r = s₀.gpr r := by
    intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := VG.Proof.Aes.AArch64.keyWrites_not r hr
    rw [hoth₄ r h2 h3 h4, hg₃, hoth₂ r h1, hoth₁ r h1, hi.keep r hr]
  have hfr : Frame [⟨b + BitVec.ofNat 64 0, 384⟩, ⟨b + BitVec.ofNat 64 1024, 1024⟩] s₀.mem s₄.mem := by
    rw [hm₄]
    refine hi.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hfr₂.sub fun r hr => ⟨_, List.mem_cons_self .., ?_⟩)
      (hfr₃.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [slotRegion, VG.Proof.Aes.AArch64.linCfg, hsb₁]
      exact VG.Proof.Aes.AArch64.base_sub b (by decide) (by decide)
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hx1₂]
      exact Offset.sub b (by omega) (by omega)
  -- The keys stored before.
  have hold : ∀ i, j < i → i ≤ R →
      KeyRel (fun k => s₄.mem.readW (wordAddr (VG.Proof.Aes.AArch64.keyAddr b R i) k) 64) (roundKey w i) := by
    intro i hji hiR
    refine VG.Proof.Aes.AArch64.keyRel_congr (hi.done i hji hiR) fun k hk => ?_
    simp only [VG.Proof.Aes.AArch64.keyAddr, VG.Proof.Aes.AArch64.wordAddr_off]
    rw [hm₄, VG.Proof.Aes.AArch64.readW_off_frame hfr₃ fun r hr => ?_, VG.Proof.Aes.AArch64.readW_off_frame hfr₂ fun r hr => ?_, hm₁]
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [slotRegion, VG.Proof.Aes.AArch64.linCfg, hsb₁]
      exact Offset.disjoint_base b (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hx1₂]
      exact Offset.disjoint b (by omega) (by omega) (by omega)
  -- The key stored now.
  have hnew : KeyRel (fun k => s₄.mem.readW (wordAddr (VG.Proof.Aes.AArch64.keyAddr b R j) k) 64) (roundKey w j) :=
    VG.Proof.Aes.AArch64.keyRel_congr (VG.Proof.Aes.AArch64.keyRel_of_bs hbs₂) fun k hk => by rw [hm₄, ← hx1₂, hst₃ k hk]
  have hx2 : s₃.gpr .x2 = BitVec.ofNat 64 (j + 1) := by
    rw [hg₃, hoth₂ .x2 (by decide), hoth₁ .x2 (by decide), hi.x2]
  have hx0 : s₃.gpr .x0 = sc + BitVec.ofNat 64 (16 * j) := by
    rw [hg₃, hoth₂ .x0 (by decide), hoth₁ .x0 (by decide), hi.x0]
  have hx1 : s₃.gpr .x1 = VG.Proof.Aes.AArch64.keyAddr b R j := by rw [hg₃, hx1₂]
  have hrd : s₄.rd = s₀.rd := by rw [hrd₄, hrd₃, hrd₂, hrd₁, hi.rd]
  have hwr : s₄.wr = s₀.wr := by rw [hwr₄, hwr₃, hwr₂, hwr₁, hi.wr]
  have hsp : s₄.sp = s₀.sp := by rw [hsp₄, hsp₃, hsp₂, hsp₁, hi.sp]
  have hx2' : s₄.gpr .x2 = BitVec.ofNat 64 j := by
    rw [hx2₄, hx2]; exact (VG.Proof.Aes.AArch64.ofNat_sub_one (j := j + 1) (by omega)).trans (by simp)
  have hev : AArch64.eval (.nonzero .x .x2) s₄ = some (BitVec.ofNat 64 j != 0) := by
    simp only [AArch64.eval, State.read, Size.bits, BitVec.setWidth_eq, hx2']
  by_cases h0 : j = 0
  · subst h0
    refine .inl ⟨rfl, hev.trans (by decide), ⟨by rw [hx1₄, hx1], hrd, hwr, hsp, hkeep, hfr,
      fun i hiR => ?_⟩⟩
    by_cases hi0 : i = 0
    · subst hi0; exact hnew
    · exact hold i (by omega) hiR
  · have hne : BitVec.ofNat 64 j ≠ 0 := by
      intro h; have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simp at this; omega
    refine .inr ⟨by omega, hev.trans (by simpa using hne),
      ⟨by omega, ?_, ?_, ?_, hrd, hwr, hsp, hkeep, hfr, ?_⟩⟩
    · rw [hx2', show j - 1 + 1 = j by omega]
    · rw [hx0₄, hx0, show 16 * (j - 1) = 16 * j - 16 by omega]
      exact VG.Proof.Aes.AArch64.add_ofNat_sub sc (y := 16) (by omega)
    · rw [hx1₄, hx1]; exact VG.Proof.Aes.AArch64.keyAddr_pred b hk.rounds (by omega) hi.hj
    · intro i hi' hiR
      by_cases hij : i = j
      · subst hij; exact hnew
      · exact hold i (by omega) hiR

theorem keyLoop_ok {s₀ : State} {b sc : Addr} {R : Nat} {w : List Byte} (hk : VG.Proof.Aes.AArch64.KSetup s₀ b sc R w)
    {s : State} (hi : VG.Proof.Aes.AArch64.KInv s₀ b sc R w R s) :
    WP isa (.loop (.block keyBody) (.nonzero .x .x2)) s (VG.Proof.Aes.AArch64.KDone s₀ b R w) := by
  refine WP.loop (M := isa) (VG.Proof.Aes.AArch64.KInv s₀ b sc R w) (fun n s hs => ?_) R s hi
  refine WP.mono (VG.Proof.Aes.AArch64.keyBody_ok hk hs) fun s' h => ?_
  rcases h with ⟨_, hev, hd⟩ | ⟨hn, hev, hi'⟩
  · exact .inl ⟨hev, hd⟩
  · exact .inr ⟨hev, n - 1, by omega, hi'⟩

end VG.Proof.Aes.AArch64

end

/-!
# One group of counter-mode blocks on AArch64

`ctrBlocks` builds the counter blocks `c + b` (`b < 4`) from the slots of
the counter block (`ctrBlocks_wp`, then `ctr_inRel` for `InRel`),
`encrypt4` encrypts them (`Encrypt.lean`), and `xorFull` or `xorTail` XOR
the keystream into the data, byte by byte.
-/

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes

/-- An access at an offset of a region. -/
theorem in_off {rs : List Region} {b : Addr} {len : Nat} (hr : (⟨b, len⟩ : Region) ∈ rs)
    {off n : Nat} (h : off + n ≤ len) (hl : len < 2 ^ 64) :
    InRegions rs (b + BitVec.ofNat 64 off) n :=
  ⟨_, hr, Offset.contains_base b h (by omega)⟩

theorem q_ctr : ∀ c < 4, q c ≠ .x5 ∧ q (c + 4) ≠ .x5 ∧ q c ≠ .x21 ∧ q (c + 4) ≠ .x21 ∧
    q c ≠ q (c + 4) := by
  decide

/-! ## The counter blocks -/

/-- The words of the counter block: bytes 0–7, bytes 8–11, and the counter. -/
abbrev cloW (m : Mem) (b : Addr) : BitVec 64 := m.readW (b + BitVec.ofNat 64 (8 * 59)) 64
abbrev chiW (m : Mem) (b : Addr) : BitVec 64 := m.readW (b + BitVec.ofNat 64 (8 * 60)) 64
abbrev numW (m : Mem) (b : Addr) : BitVec 32 := m.readW (b + BitVec.ofNat 64 (8 * 61)) 32

/-- The high word of counter block `c + i`. -/
def hiWord (hi : BitVec 64) (c : BitVec 32) (i : Nat) : BitVec 64 :=
  hi ^^^ (rev32 (c + BitVec.ofNat 32 i)).setWidth 64 <<< 32

theorem sw_32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by simp

set_option simprocs false in
theorem ctrBlock_ok {s : State} {b : Addr} {c : Nat} (hc : c < 4) (hb : s.gpr .x5 = b)
    (hw : (⟨b, 2048⟩ : Region) ∈ s.wr) :
    ∃ s', runBlock isa (ctrBlock c) s = some s' ∧
      s'.gpr (q c) = VG.Proof.Aes.AArch64.cloW s.mem b ∧ s'.gpr (q (c + 4)) = VG.Proof.Aes.AArch64.hiWord (VG.Proof.Aes.AArch64.chiW s.mem b) (VG.Proof.Aes.AArch64.numW s.mem b) c ∧
      (∀ r, r ≠ q c → r ≠ q (c + 4) → r ≠ t0 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := VG.Proof.Aes.AArch64.q_ctr c hc
  have hw' : (⟨b, 2048⟩ : Region) ∈ s.rd ++ s.wr := List.mem_append_right _ hw
  have i59 := VG.Proof.Aes.AArch64.in_off hw' (off := 8 * 59) (n := 8) (by omega) (by omega)
  have i60 := VG.Proof.Aes.AArch64.in_off hw' (off := 8 * 60) (n := 8) (by omega) (by omega)
  have i61 := VG.Proof.Aes.AArch64.in_off hw' (off := 8 * 61) (n := 4) (by omega) (by omega)
  have hc' : c < 4096 := by omega
  refine ⟨_, by
    simp (config := {decide := true}) only [ctrBlock, ldS, eorR, sb, t0, cLo, cHi, cNum,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, Size.bytes, Size.bits,
      State.read, State.write, hb, h1.symm, h3.symm, h4.symm, h5.symm, hc',
      ite_false, ite_true, i59, i60, i61, Option.map_some, Option.bind_some]
    rfl, ?_⟩
  refine ⟨by simp [h3, h5, VG.Proof.Aes.AArch64.cloW, Mem.readW], ?_, fun r r1 r2 r3 => by simp [r1, r2, show r ≠ .x21 from r3], rfl, rfl, rfl⟩
  simp only [VG.Proof.Aes.AArch64.hiWord, VG.Proof.Aes.AArch64.chiW, VG.Proof.Aes.AArch64.numW, Mem.readW, h4, h5.symm, ite_true, ite_false, VG.Proof.Aes.AArch64.sw_32, BitVec.setWidth_eq]

theorem ctrBlock_wp {s : State} {b : Addr} {c : Nat} (hc : c < 4) (hb : s.gpr .x5 = b)
    (hw : (⟨b, 2048⟩ : Region) ∈ s.wr) {P : State → Prop}
    (h : ∀ s', s'.gpr (q c) = VG.Proof.Aes.AArch64.cloW s.mem b → s'.gpr (q (c + 4)) = VG.Proof.Aes.AArch64.hiWord (VG.Proof.Aes.AArch64.chiW s.mem b) (VG.Proof.Aes.AArch64.numW s.mem b) c →
      (∀ r, r ≠ q c → r ≠ q (c + 4) → r ≠ t0 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block (ctrBlock c)) s P :=
  let ⟨s', hs, h1, h2, h3, h4, h5, h6⟩ := VG.Proof.Aes.AArch64.ctrBlock_ok hc hb hw
  WP.of_runBlock ⟨s', hs, h s' h1 h2 h3 h4 h5 h6⟩

set_option simprocs false in
/-- `c := c + 4`. -/
theorem ctrNext_ok {s : State} {b : Addr} (hb : s.gpr .x5 = b) (hw : (⟨b, 2048⟩ : Region) ∈ s.wr) :
    ∃ s', runBlock isa [.ldr .w t0 sb (8 * cNum), .addImm .w t0 t0 4, .str .w t0 sb (8 * cNum)] s =
        some s' ∧
      s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (8 * 61)) (VG.Proof.Aes.AArch64.numW s.mem b + 4) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i61 := VG.Proof.Aes.AArch64.in_off (List.mem_append_right s.rd hw) (off := 8 * 61) (n := 4) (by omega) (by omega)
  have o61 := VG.Proof.Aes.AArch64.in_off hw (off := 8 * 61) (n := 4) (by omega) (by omega)
  refine ⟨_, by
    simp (config := {decide := true}) only [sb, t0, cNum, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, State.load, State.store, Size.bytes, Size.bits, State.read, State.write, hb,
      ite_false, ite_true, i61, o61, Option.map_some, Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, fun r hr => by simp [show r ≠ .x21 from hr], rfl, rfl⟩
  simp only [VG.Proof.Aes.AArch64.numW, Mem.readW, Mem.writeW, VG.Proof.Aes.AArch64.sw_32, BitVec.setWidth_eq]
  rfl

theorem q_distinct : ∀ c < 4, ∀ d < 4, c ≠ d →
    q c ≠ q d ∧ q c ≠ q (d + 4) ∧ q (c + 4) ≠ q d ∧ q (c + 4) ≠ q (d + 4) := by
  decide

/-- The four counter blocks. -/
theorem ctrBlocks_wp {s : State} {b : Addr} (hb : s.gpr .x5 = b) (hw : (⟨b, 2048⟩ : Region) ∈ s.wr) :
    WP isa (.block ctrBlocks) s fun s' =>
      (∀ c < 4, s'.gpr (q c) = VG.Proof.Aes.AArch64.cloW s.mem b ∧
        s'.gpr (q (c + 4)) = VG.Proof.Aes.AArch64.hiWord (VG.Proof.Aes.AArch64.chiW s.mem b) (VG.Proof.Aes.AArch64.numW s.mem b) c) ∧
      (∀ r, r ∉ VG.Proof.Aes.AArch64.layerWrites → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (8 * 61)) (VG.Proof.Aes.AArch64.numW s.mem b + 4) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold ctrBlocks
  repeat rw [WP.block_append_iff (M := isa)]
  have keep : ∀ {s s' : State} {c : Nat}, c < 4 →
      (∀ r, r ≠ q c → r ≠ q (c + 4) → r ≠ t0 → s'.gpr r = s.gpr r) →
      ∀ r, r ∉ VG.Proof.Aes.AArch64.layerWrites → s'.gpr r = s.gpr r := by
    intro s s' c hc h r hr
    have : r ≠ q c ∧ r ≠ q (c + 4) ∧ r ≠ t0 := by
      refine ⟨fun h => hr ?_, fun h => hr ?_, fun h => hr (h ▸ by decide)⟩ <;>
        (subst h; unfold q; split <;> decide)
    exact h r this.1 this.2.1 this.2.2
  refine VG.Proof.Aes.AArch64.ctrBlock_wp (c := 0) (by omega) hb hw fun s₁ a₁ b₁ o₁ m₁ rd₁ wr₁ => ?_
  have hb₁ : s₁.gpr sb = b := (keep (by omega) o₁ .x5 (by decide)).trans hb
  refine VG.Proof.Aes.AArch64.ctrBlock_wp (c := 1) (by omega) hb₁ (wr₁ ▸ hw) fun s₂ a₂ b₂ o₂ m₂ rd₂ wr₂ => ?_
  have hb₂ : s₂.gpr sb = b := (keep (by omega) o₂ .x5 (by decide)).trans hb₁
  refine VG.Proof.Aes.AArch64.ctrBlock_wp (c := 2) (by omega) hb₂ (wr₂ ▸ wr₁ ▸ hw) fun s₃ a₃ b₃ o₃ m₃ rd₃ wr₃ => ?_
  have hb₃ : s₃.gpr sb = b := (keep (by omega) o₃ .x5 (by decide)).trans hb₂
  refine VG.Proof.Aes.AArch64.ctrBlock_wp (c := 3) (by omega) hb₃ (wr₃ ▸ wr₂ ▸ wr₁ ▸ hw) fun s₄ a₄ b₄ o₄ m₄ rd₄ wr₄ => ?_
  have hb₄ : s₄.gpr sb = b := (keep (by omega) o₄ .x5 (by decide)).trans hb₃
  obtain ⟨s₅, hs₅, m₅, o₅, rd₅, wr₅⟩ := VG.Proof.Aes.AArch64.ctrNext_ok hb₄ (wr₄ ▸ wr₃ ▸ wr₂ ▸ wr₁ ▸ hw)
  refine WP.of_runBlock ⟨s₅, hs₅, ?_, fun r hr => ?_, ?_, by rw [rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · have ht : ∀ c < 8, q c ≠ t0 := by decide
    intro c hc
    rw [o₅ _ (ht c (by omega)), o₅ _ (ht (c + 4) (by omega))]
    have pres : ∀ {s s' : State} (c d : Nat), c < 4 → d < 4 → c ≠ d →
        (∀ r, r ≠ q d → r ≠ q (d + 4) → r ≠ t0 → s'.gpr r = s.gpr r) →
        s'.gpr (q c) = s.gpr (q c) ∧ s'.gpr (q (c + 4)) = s.gpr (q (c + 4)) := by
      intro s s' c d hc hd hcd o
      have := VG.Proof.Aes.AArch64.q_distinct c hc d hd hcd
      exact ⟨o _ this.1 this.2.1 (ht c (by omega)), o _ this.2.2.1 this.2.2.2 (ht (c + 4) (by omega))⟩
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [(pres 0 3 (by omega) (by omega) (by omega) o₄).1, (pres 0 2 (by omega) (by omega) (by omega) o₃).1,
        (pres 0 1 (by omega) (by omega) (by omega) o₂).1, (pres 0 3 (by omega) (by omega) (by omega) o₄).2,
        (pres 0 2 (by omega) (by omega) (by omega) o₃).2, (pres 0 1 (by omega) (by omega) (by omega) o₂).2,
        a₁, b₁]
      exact ⟨rfl, rfl⟩
    · rw [(pres 1 3 (by omega) (by omega) (by omega) o₄).1, (pres 1 2 (by omega) (by omega) (by omega) o₃).1,
        (pres 1 3 (by omega) (by omega) (by omega) o₄).2, (pres 1 2 (by omega) (by omega) (by omega) o₃).2,
        a₂, b₂, m₁]
      exact ⟨rfl, rfl⟩
    · rw [(pres 2 3 (by omega) (by omega) (by omega) o₄).1, (pres 2 3 (by omega) (by omega) (by omega) o₄).2,
        a₃, b₃, m₂, m₁]
      exact ⟨rfl, rfl⟩
    · rw [a₄, b₄, m₃, m₂, m₁]
      exact ⟨rfl, rfl⟩
  · rw [o₅ r (fun h => hr (h ▸ by decide)), keep (by omega) o₄ r hr, keep (by omega) o₃ r hr,
      keep (by omega) o₂ r hr, keep (by omega) o₁ r hr]
  · rw [m₅, m₄, m₃, m₂, m₁]

/-! ## The counter blocks as states -/

theorem rev32_bit (v : BitVec 32) {k j : Nat} (hk : k < 4) (hj : j < 8) :
    (rev32 v).getLsbD (8 * k + j) = v.getLsbD (8 * (3 - k) + j) := by
  unfold rev32
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> (first | omega | (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega))

theorem rot_bit (v : BitVec 32) {p : Nat} (hp : p < 64) :
    (v.setWidth 64 <<< 32).getLsbD p = (decide (32 ≤ p) && v.getLsbD (p - 32)) := by
  rw [BitVec.getLsbD_shiftLeft]
  by_cases h : p < 32
  · simp [h, show ¬ 32 ≤ p by omega]
  · simp [h, show 32 ≤ p by omega, hp, show p - 32 < 64 by omega]

/-- The counter blocks `4g … 4g + 3` in the words, as `InRel` has them. -/
theorem ctr_inRel {Q : Nat → BitVec 64} {icb : Spec.Gcm.Block} {lo hi : BitVec 64} {C : BitVec 32}
    {g : Nat}
    (hlo : ∀ i < 8, ∀ j < 8, lo.getLsbD (8 * i + j) = icb.getLsbD (8 * (15 - i) + j))
    (hhi : ∀ i < 4, ∀ j < 8, hi.getLsbD (8 * i + j) = icb.getLsbD (8 * (7 - i) + j))
    (hhi' : ∀ p, 32 ≤ p → hi.getLsbD p = false)
    (hC : C = icb.extractLsb' 0 32 + BitVec.ofNat 32 (4 * g))
    (hQ : ∀ c < 4, Q c = lo ∧ Q (c + 4) = VG.Proof.Aes.AArch64.hiWord hi C c) :
    InRel Q (fun c => ctrState icb (4 * g + c)) := by
  intro c hc i hi16 j hj
  obtain ⟨h0, h1⟩ := hQ c hc
  simp only [ctrState, getD_eq _ hi16, Vector.getElem_ofFn]
  rw [ctrBlock_byte _ _ hi16]
  by_cases h8 : i < 8
  · rw [show i / 8 = 0 by omega, show i % 8 = i by omega, Nat.mul_zero, Nat.add_zero, h0,
      ite_eq_left (by omega), toBytes_getD _ hi16, BitVec.getLsbD_extractLsb', hlo i h8 j hj]
    simp [hj]
  · rw [show i / 8 = 1 by omega, Nat.mul_one, h1]
    unfold VG.Proof.Aes.AArch64.hiWord
    rw [BitVec.getLsbD_xor, VG.Proof.Aes.AArch64.rot_bit _ (by omega)]
    by_cases h12 : i < 12
    · rw [ite_eq_left h12, toBytes_getD _ hi16, BitVec.getLsbD_extractLsb', hhi (i % 8) (by omega) j hj]
      simp only [show ¬ 32 ≤ 8 * (i % 8) + j by omega, decide_false, Bool.false_and, Bool.xor_false, hj,
        decide_true, Bool.true_and]
      congr 1; omega
    · rw [ite_eq_right h12, hhi' _ (by omega), BitVec.getLsbD_extractLsb',
        show 8 * (i % 8) + j - 32 = 8 * (i % 8 - 4) + j by omega, VG.Proof.Aes.AArch64.rev32_bit _ (by omega) hj, hC,
        BitVec.add_assoc, ← BitVec.ofNat_add]
      simp only [show 32 ≤ 8 * (i % 8) + j by omega, decide_true, Bool.true_and, Bool.false_xor, hj]
      congr 1; omega

/-! ## XOR into the data -/

/-- XOR `v` into the 8 bytes at `a`. -/
def xorW (m : Mem) (a : Addr) (v : BitVec 64) : Mem := m.writeW a (m.readW a 64 ^^^ v)

theorem xorW_apply (m : Mem) (a x : Addr) (v : BitVec 64) :
    VG.Proof.Aes.AArch64.xorW m a v x = if (x - a).toNat < 8 then m x ^^^ v.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  unfold VG.Proof.Aes.AArch64.xorW Mem.writeW Mem.write
  split
  · rename_i h
    have hx : a + BitVec.ofNat 64 (x - a).toNat = x := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have := Mem.extractLsb'_read m a (n := 8) h
    rw [hx] at this
    rw [← this]
    ext t ht
    simp only [BitVec.getElem_extractLsb', BitVec.getElem_xor, Mem.readW]
    simp
  · rfl

/-- XOR two words into the 16 bytes at `a`. -/
theorem xorW2_apply (m : Mem) (a x : Addr) (v₁ v₂ : BitVec 64) :
    VG.Proof.Aes.AArch64.xorW (VG.Proof.Aes.AArch64.xorW m a v₁) (a + 8) v₂ x =
      if (x - a).toNat < 16 then
        m x ^^^ (if (x - a).toNat < 8 then v₁.extractLsb' (8 * (x - a).toNat) 8
          else v₂.extractLsb' (8 * ((x - a).toNat - 8)) 8)
      else m x := by
  rw [VG.Proof.Aes.AArch64.xorW_apply, VG.Proof.Aes.AArch64.xorW_apply]
  by_cases h : (x - a).toNat < 8
  · have : ¬ (x - (a + 8)).toNat < 8 := by bv_omega
    rw [ite_eq_right this, ite_eq_left h, ite_eq_left (show (x - a).toNat < 16 by omega), ite_eq_left h]
  · by_cases h' : (x - a).toNat < 16
    · have : (x - (a + 8)).toNat = (x - a).toNat - 8 := by bv_omega
      rw [this, ite_eq_left (show (x - a).toNat - 8 < 8 by omega), ite_eq_right h, ite_eq_left h',
        ite_eq_right h]
    · have : ¬ (x - (a + 8)).toNat < 8 := by bv_omega
      rw [ite_eq_right this, ite_eq_right h, ite_eq_right h']

theorem xorBlock_ok {s : State} {d : Addr} {c : Nat} (hc : c < 4) (hd : s.gpr .x3 = d)
    (h1 : InRegions s.wr (d + BitVec.ofNat 64 (16 * c)) 8)
    (h2 : InRegions s.wr (d + BitVec.ofNat 64 (16 * c) + 8) 8) (hq : q c ≠ t0 ∧ q (c + 4) ≠ t0) :
    ∃ s', runBlock isa (xorBlock c) s = some s' ∧
      s'.mem = VG.Proof.Aes.AArch64.xorW (VG.Proof.Aes.AArch64.xorW s.mem (d + BitVec.ofNat 64 (16 * c)) (s.gpr (q c)))
        (d + BitVec.ofNat 64 (16 * c) + 8) (s.gpr (q (c + 4))) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e2 : d + BitVec.ofNat 64 (16 * c + 8) = d + BitVec.ofNat 64 (16 * c) + 8 := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
  have i1 : InRegions (s.rd ++ s.wr) (d + BitVec.ofNat 64 (16 * c)) 8 :=
    let ⟨r, hr, h⟩ := h1; ⟨r, List.mem_append_right _ hr, h⟩
  have i2 : InRegions (s.rd ++ s.wr) (d + BitVec.ofNat 64 (16 * c) + 8) 8 :=
    let ⟨r, hr, h⟩ := h2; ⟨r, List.mem_append_right _ hr, h⟩
  have a1 : 16 * c % 8 = 0 := by omega
  have a2 : 16 * c < 4096 * 8 := by omega
  have a3 : (16 * c + 8) % 8 = 0 := by omega
  have a4 : 16 * c + 8 < 4096 * 8 := by omega
  have q1 : q c ≠ .x21 := hq.1
  have q2 : q (c + 4) ≠ .x21 := hq.2
  refine ⟨_, by
    simp (config := {decide := true}) only [xorBlock, eorR, t0, runBlock_cons, runStep_some,
      runBlock_nil, exec, addr, State.load, State.store, Size.bytes, Size.bits, State.read,
      State.write, e2, hd, q1, q2, ite_false, ite_true, i1, i2, h1, h2, a1, a2, a3, a4,
      and_self, Option.map_some, Option.bind_some, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨?_, fun r hr => by simp [show r ≠ .x21 from hr], rfl, rfl⟩
  simp only [VG.Proof.Aes.AArch64.xorW, Mem.readW, Mem.writeW, BitVec.setWidth_eq, Nat.reduceDiv, Nat.reduceMul]

/-- The data after `k` blocks: the keystream `ks` XORed into the first
`16 k` of the `16 n` bytes at `D`. -/
def DataInv (m₀ m : Mem) (D : Addr) (n k : Nat) (ks : Nat → Byte) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    m₀ (D + BitVec.ofNat 64 i) ^^^ (if i < 16 * k then ks i else 0)

theorem off_toNat (D : Addr) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    (D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 j)).toNat =
      if j ≤ i then i - j else 2 ^ 64 + i - j := Offset.sub_toNat' D hj hi

/-- One block of keystream XORed in. -/
theorem dataInv_step {m₀ m : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte} {v₁ v₂ : BitVec 64}
    (hn : 16 * n ≤ 2 ^ 64) (hk : k < n) (h : VG.Proof.Aes.AArch64.DataInv m₀ m D n k ks)
    (hks : ∀ t < 16, (if t < 8 then v₁.extractLsb' (8 * t) 8 else v₂.extractLsb' (8 * (t - 8)) 8) =
      ks (16 * k + t)) :
    VG.Proof.Aes.AArch64.DataInv m₀ (VG.Proof.Aes.AArch64.xorW (VG.Proof.Aes.AArch64.xorW m (D + BitVec.ofNat 64 (16 * k)) v₁) (D + BitVec.ofNat 64 (16 * k) + 8) v₂)
        D n (k + 1) ks ∧
      Frame [⟨D, 16 * n⟩] m
        (VG.Proof.Aes.AArch64.xorW (VG.Proof.Aes.AArch64.xorW m (D + BitVec.ofNat 64 (16 * k)) v₁) (D + BitVec.ofNat 64 (16 * k) + 8) v₂) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · rw [VG.Proof.Aes.AArch64.xorW2_apply, VG.Proof.Aes.AArch64.off_toNat D (by omega) (by omega), h i hi]
    by_cases h1 : 16 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 16 * k < 16
      · rw [ite_eq_left h2, hks _ h2, ite_eq_right (show ¬ i < 16 * k by omega),
          ite_eq_left (show i < 16 * (k + 1) by omega), show 16 * k + (i - 16 * k) = i by omega]
        simp
      · rw [ite_eq_right h2, ite_eq_right (show ¬ i < 16 * k by omega),
          ite_eq_right (show ¬ i < 16 * (k + 1) by omega)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 16 * k < 16 by omega),
        ite_eq_left (show i < 16 * k by omega), ite_eq_left (show i < 16 * (k + 1) by omega)]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx ⟨D, 16 * n⟩ (List.mem_singleton_self _)
    rw [VG.Proof.Aes.AArch64.xorW2_apply, ite_eq_right]
    have : 16 * k < 2 ^ 64 := by omega
    have : (BitVec.ofNat 64 (16 * k)).toNat = 16 * k := by simp; omega
    bv_omega

theorem dataInv_mono {m₀ m : Mem} {D : Addr} {n k k' : Nat} {ks : Nat → Byte} (h : VG.Proof.Aes.AArch64.DataInv m₀ m D n k ks)
    (hk : n ≤ k) (hk' : n ≤ k') : VG.Proof.Aes.AArch64.DataInv m₀ m D n k' ks := by
  intro i hi
  rw [h i hi, ite_eq_left (show i < 16 * k by omega), ite_eq_left (show i < 16 * k' by omega)]

/-- The keystream, byte by byte: byte `i` is byte `i mod 16` of the
encrypted counter block `i / 16`. -/
def keyStream (R : Nat) (w : List Byte) (icb : Spec.Gcm.Block) (i : Nat) : Byte :=
  (Spec.Aes.cipher R w (ctrState icb (i / 16))).getD (i % 16) 0

theorem ks_of_inRel {Q : Nat → BitVec 64} {R g : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
    (h : InRel Q (fun c => Spec.Aes.cipher R w (ctrState icb (4 * g + c)))) {c t : Nat} (hc : c < 4)
    (ht : t < 16) :
    (Q (c + 4 * (t / 8))).extractLsb' (8 * (t % 8)) 8 = VG.Proof.Aes.AArch64.keyStream R w icb (16 * (4 * g + c) + t) := by
  apply byte_ext
  intro j hj
  rw [BitVec.getLsbD_extractLsb', h c hc t ht j hj, VG.Proof.Aes.AArch64.keyStream,
    show (16 * (4 * g + c) + t) / 16 = 4 * g + c by omega, show (16 * (4 * g + c) + t) % 16 = t by omega]
  simp [hj]

theorem xorBlock_wp {s : State} {m₀ : Mem} {D : Addr} {n g c : Nat} {ks : Nat → Byte} (hc : c < 4)
    (hk : 4 * g + c < n) (hn : 16 * n < 2 ^ 64) (hD : (⟨D, 16 * n⟩ : Region) ∈ s.wr)
    (hd : s.gpr .x3 = D + BitVec.ofNat 64 (64 * g)) (hinv : VG.Proof.Aes.AArch64.DataInv m₀ s.mem D n (4 * g + c) ks)
    (hks : ∀ t < 16, (s.gpr (q (c + 4 * (t / 8)))).extractLsb' (8 * (t % 8)) 8 =
      ks (16 * (4 * g + c) + t))
    {P : State → Prop}
    (h : ∀ s', VG.Proof.Aes.AArch64.DataInv m₀ s'.mem D n (4 * g + c + 1) ks → Frame [⟨D, 16 * n⟩] s.mem s'.mem →
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block (xorBlock c)) s P := by
  have ha : D + BitVec.ofNat 64 (64 * g) + BitVec.ofNat 64 (16 * c) =
      D + BitVec.ofNat 64 (16 * (4 * g + c)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  have hq : ∀ c < 8, q c ≠ t0 := by decide
  have i1 := VG.Proof.Aes.AArch64.in_off hD (off := 16 * (4 * g + c)) (n := 8) (by omega) hn
  have i2 := VG.Proof.Aes.AArch64.in_off hD (off := 16 * (4 * g + c) + 8) (n := 8) (by omega) hn
  rw [BitVec.ofNat_add, ← BitVec.add_assoc] at i2
  rw [← ha] at i1 i2
  obtain ⟨s', hs', hm, ho, hrd, hwr⟩ :=
    VG.Proof.Aes.AArch64.xorBlock_ok hc hd i1 i2 ⟨hq c (by omega), hq (c + 4) (by omega)⟩
  rw [ha] at hm
  have hst := VG.Proof.Aes.AArch64.dataInv_step (v₁ := s.gpr (q c)) (v₂ := s.gpr (q (c + 4))) (by omega) hk hinv
    (fun t ht => by
      rw [← hks t ht]
      by_cases h8 : t < 8
      · rw [ite_eq_left h8, show t / 8 = 0 by omega, show t % 8 = t by omega, Nat.mul_zero, Nat.add_zero]
      · rw [ite_eq_right h8, show t / 8 = 1 by omega, show t % 8 = t - 8 by omega, Nat.mul_one])
  rw [← hm] at hst
  exact WP.of_runBlock ⟨s', hs', h s' hst.1 hst.2 ho hrd hwr⟩

/-! ## The XOR phase of a group -/

/-- After `k` blocks of the group have been XORed in, from `s₃`. -/
structure XS (m₀ : Mem) (D : Addr) (n g : Nat) (ks : Nat → Byte) (s₃ : State) (k : Nat) (s : State) :
    Prop where
  data : VG.Proof.Aes.AArch64.DataInv m₀ s.mem D n (4 * g + k) ks
  frame : Frame [⟨D, 16 * n⟩] s₃.mem s.mem
  keep : ∀ r, r ≠ t0 → s.gpr r = s₃.gpr r
  rd : s.rd = s₃.rd
  wr : s.wr = s₃.wr

/-- Before the XOR phase of group `g`: the keystream is in the words. -/
structure XPre (m₀ : Mem) (D : Addr) (n g : Nat) (ks : Nat → Byte) (s₃ : State) : Prop where
  hg : 4 * g < n
  hn : 16 * n < 2 ^ 64
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₃.wr
  x3 : s₃.gpr .x3 = D + BitVec.ofNat 64 (64 * g)
  x4 : s₃.gpr .x4 = BitVec.ofNat 64 (n - 4 * g)
  data : VG.Proof.Aes.AArch64.DataInv m₀ s₃.mem D n (4 * g) ks
  ks : ∀ c < 4, ∀ t < 16, (s₃.gpr (q (c + 4 * (t / 8)))).extractLsb' (8 * (t % 8)) 8 =
    ks (16 * (4 * g + c) + t)

/-- After the XOR phase: `x4` is zero if no data is left. -/
def XDone (m₀ : Mem) (D : Addr) (n g : Nat) (ks : Nat → Byte) (s₃ s : State) : Prop :=
  Frame [⟨D, 16 * n⟩] s₃.mem s.mem ∧ (∀ r, r ≠ t0 → r ≠ .x3 → r ≠ .x4 → s.gpr r = s₃.gpr r) ∧
    s.rd = s₃.rd ∧ s.wr = s₃.wr ∧
    ((s.gpr .x4 = 0 ∧ VG.Proof.Aes.AArch64.DataInv m₀ s.mem D n n ks) ∨
     (4 * g + 4 < n ∧ VG.Proof.Aes.AArch64.DataInv m₀ s.mem D n (4 * (g + 1)) ks ∧
      s.gpr .x3 = D + BitVec.ofNat 64 (64 * (g + 1)) ∧ s.gpr .x4 = BitVec.ofNat 64 (n - 4 * (g + 1))))

section Xor

variable {m₀ : Mem} {D : Addr} {n g : Nat} {ks : Nat → Byte} {s₃ : State}

theorem xs_step (hp : VG.Proof.Aes.AArch64.XPre m₀ D n g ks s₃) {k : Nat} (hk : k < 4) (hkn : 4 * g + k < n) {s : State}
    (hs : VG.Proof.Aes.AArch64.XS m₀ D n g ks s₃ k s) {P : State → Prop} (h : ∀ s', VG.Proof.Aes.AArch64.XS m₀ D n g ks s₃ (k + 1) s' → P s') :
    WP isa (.block (xorBlock k)) s P := by
  have hq : ∀ c < 8, q c ≠ t0 := by decide
  refine VG.Proof.Aes.AArch64.xorBlock_wp hk hkn hp.hn (hs.wr ▸ hp.dat) (by rw [hs.keep _ (by decide)]; exact hp.x3)
    hs.data (fun t ht => by rw [hs.keep _ (hq _ (by omega))]; exact hp.ks k hk t ht)
    fun s' d f o rd wr => h s' ⟨d, hs.frame.trans f, fun r hr => (o r hr).trans (hs.keep r hr),
      rd.trans hs.rd, wr.trans hs.wr⟩

theorem xs_zero (hp : VG.Proof.Aes.AArch64.XPre m₀ D n g ks s₃) {s : State} (hg : s.gpr = s₃.gpr) (hm : s.mem = s₃.mem)
    (hrd : s.rd = s₃.rd) (hwr : s.wr = s₃.wr) : VG.Proof.Aes.AArch64.XS m₀ D n g ks s₃ 0 s :=
  ⟨by rw [hm, Nat.add_zero]; exact hp.data, by rw [hm]; exact Frame.refl _ _,
    fun r _ => by rw [hg], hrd, hwr⟩

theorem advance_ok (s : State) :
    ∃ s', runBlock isa [.addImm .x .x3 .x3 64, .subImm .x .x4 .x4 4] s = some s' ∧
      s'.gpr .x3 = s.gpr .x3 + 64 ∧ s'.gpr .x4 = s.gpr .x4 - 4 ∧
      (∀ r, r ≠ .x3 → r ≠ .x4 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
    exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  exact ⟨by simp [State.write, State.read], by simp [State.write, State.read],
    fun r h1 h2 => by simp [State.write, h1, h2], rfl, rfl, rfl⟩

theorem clear_ok (s : State) :
    ∃ s', runBlock isa [.movz .x .x4 0 0] s = some s' ∧ s'.gpr .x4 = 0 ∧
      (∀ r, r ≠ .x4 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, exec]; rfl, ?_⟩
  exact ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl⟩

/-- `sub t0, x4, #k`, or `lsr t0, x4, #2`, then a test of `t0`. -/
theorem subT_ok (s : State) (k : Nat) (hk : k < 4096) :
    ∃ s', runBlock isa [.subImm .x t0 .x4 k] s = some s' ∧
      AArch64.eval (.nonzero .x t0) s' = some (s.gpr .x4 - BitVec.ofNat 64 k != 0) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by rw [runBlock_cons, exec_subImm_x hk, runStep_some, runBlock_nil], ?_⟩
  exact ⟨by simp [AArch64.eval, State.write, State.read], fun r h => by simp [State.write, h], rfl, rfl,
    rfl⟩

theorem lsrT_ok (s : State) :
    ∃ s', runBlock isa [lsrI t0 .x4 2] s = some s' ∧
      AArch64.eval (.nonzero .x t0) s' = some (s.gpr .x4 >>> 2 != 0) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by rw [lsrI, runBlock_cons, exec_lsr_x (by decide), runStep_some, runBlock_nil], ?_⟩
  exact ⟨by simp [AArch64.eval, State.write, State.read], fun r h => by simp [State.write, h], rfl, rfl,
    rfl⟩

theorem xorFull_eq : xorFull = xorBlock 0 ++ xorBlock 1 ++ xorBlock 2 ++ xorBlock 3 ++
    ([.addImm .x .x3 .x3 64, .subImm .x .x4 .x4 4] : List Instr) := rfl

theorem ofNat_sub_four {x : Nat} (h : 4 ≤ x) : BitVec.ofNat 64 x - 4 = BitVec.ofNat 64 (x - 4) := Offset.ofNat_sub_ofNat h

theorem ofNat_sub_ne {x k : Nat} (hx : x < 2 ^ 64) (hk : k < 4096) (hne : x ≠ k) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 k != 0) = true := by
  have : BitVec.ofNat 64 x - BitVec.ofNat 64 k ≠ 0 := by bv_omega
  simpa using this

theorem ofNat_sub_eq {k : Nat} : (BitVec.ofNat 64 k - BitVec.ofNat 64 k != 0) = false := by
  simp

theorem off_add64 (D : Addr) (g : Nat) :
    D + BitVec.ofNat 64 (64 * g) + 64 = D + BitVec.ofNat 64 (64 * (g + 1)) := (Offset.add_add D _ 64).trans (by rw [show 64 * g + 64 = 64 * (g + 1) by omega])

theorem shr2_ne (x : Nat) (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x >>> 2 != 0) = decide (4 ≤ x) := by
  by_cases h : 4 ≤ x
  · have : BitVec.ofNat 64 x >>> 2 ≠ 0 := by
      intro h'; have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.shiftRight_eq_div_pow] at this
      simp at this; omega
    simpa [h] using this
  · have : BitVec.ofNat 64 x >>> 2 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.shiftRight_eq_div_pow]
      simp; omega
    simp [this, h]

theorem xorPhase_wp (hp : VG.Proof.Aes.AArch64.XPre m₀ D n g ks s₃) :
    WP isa (.seq (.block [lsrI t0 .x4 2]) (.ite (.nonzero .x t0) (.block xorFull) xorTail)) s₃
      (VG.Proof.Aes.AArch64.XDone m₀ D n g ks s₃) := by
  have hg := hp.hg
  have hn := hp.hn
  obtain ⟨s₄, hs₄, ev₄, g₄, m₄, rd₄, wr₄⟩ := VG.Proof.Aes.AArch64.lsrT_ok s₃
  refine WP.seq (WP.of_runBlock ⟨s₄, hs₄, ?_⟩)
  have x₀ : VG.Proof.Aes.AArch64.XS m₀ D n g ks s₃ 0 s₄ := ⟨by rw [m₄, Nat.add_zero]; exact hp.data, by rw [m₄]; exact Frame.refl _ _,
    g₄, rd₄, wr₄⟩
  rw [hp.x4, VG.Proof.Aes.AArch64.shr2_ne _ (by omega)] at ev₄
  refine WP.ite (decide (4 ≤ n - 4 * g)) ev₄ (fun hb => ?_) (fun hb => ?_)
  · -- Four blocks.
    have h4 : 4 ≤ n - 4 * g := by simpa using hb
    rw [VG.Proof.Aes.AArch64.xorFull_eq]
    repeat rw [WP.block_append_iff (M := isa)]
    refine VG.Proof.Aes.AArch64.xs_step hp (k := 0) (by omega) (by omega) x₀ fun s₅ x₅ => ?_
    refine VG.Proof.Aes.AArch64.xs_step hp (k := 1) (by omega) (by omega) x₅ fun s₆ x₆ => ?_
    refine VG.Proof.Aes.AArch64.xs_step hp (k := 2) (by omega) (by omega) x₆ fun s₇ x₇ => ?_
    refine VG.Proof.Aes.AArch64.xs_step hp (k := 3) (by omega) (by omega) x₇ fun s₈ x₈ => ?_
    obtain ⟨s₉, hs₉, d₉, r₉, o₉, m₉, rd₉, wr₉⟩ := VG.Proof.Aes.AArch64.advance_ok s₈
    refine WP.of_runBlock ⟨s₉, hs₉, ?_⟩
    have e₁ : s₈.gpr .x3 = D + BitVec.ofNat 64 (64 * g) := (x₈.keep _ (by decide)).trans hp.x3
    have e₂ : s₈.gpr .x4 = BitVec.ofNat 64 (n - 4 * g) := (x₈.keep _ (by decide)).trans hp.x4
    refine ⟨m₉ ▸ x₈.frame, fun r h1 h2 h3 => (o₉ r h2 h3).trans (x₈.keep r h1), rd₉.trans x₈.rd,
      wr₉.trans x₈.wr, ?_⟩
    rw [r₉, e₂, m₉, VG.Proof.Aes.AArch64.ofNat_sub_four h4]
    by_cases hl : n - 4 * g = 4
    · refine .inl ⟨by rw [hl]; rfl, VG.Proof.Aes.AArch64.dataInv_mono x₈.data (by omega) (by omega)⟩
    · refine .inr ⟨by omega, by simpa [Nat.mul_add] using x₈.data, ?_, ?_⟩
      · rw [d₉, e₁]; exact VG.Proof.Aes.AArch64.off_add64 D g
      · rw [show n - 4 * (g + 1) = n - 4 * g - 4 by omega]
  · -- The last one to three blocks.
    have h4 : n - 4 * g < 4 := by simpa using hb
    unfold xorTail
    refine WP.seq ?_
    rw [WP.block_append_iff (M := isa)]
    refine VG.Proof.Aes.AArch64.xs_step hp (k := 0) (by omega) (by omega) x₀ fun s₅ x₅ => ?_
    obtain ⟨s₆, hs₆, ev₆, g₆, m₆, rd₆, wr₆⟩ := VG.Proof.Aes.AArch64.subT_ok s₅ 1 (by decide)
    refine WP.of_runBlock ⟨s₆, hs₆, ?_⟩
    have x₆ : VG.Proof.Aes.AArch64.XS m₀ D n g ks s₃ 1 s₆ := ⟨m₆ ▸ x₅.data, m₆ ▸ x₅.frame,
      fun r h => by rw [g₆ r h]; exact x₅.keep r h, rd₆.trans x₅.rd, wr₆.trans x₅.wr⟩
    rw [(x₅.keep _ (by decide)).trans hp.x4] at ev₆
    refine WP.seq (WP.mono (Q := VG.Proof.Aes.AArch64.XS m₀ D n g ks s₃ (n - 4 * g)) ?_ fun s hs => ?_)
    · by_cases h1 : n - 4 * g = 1
      · refine WP.ite false (ev₆.trans (by rw [h1]; exact congrArg some VG.Proof.Aes.AArch64.ofNat_sub_eq)) (fun h => by cases h)
          (fun _ => WP.block_nil (by rw [h1]; exact x₆))
      refine WP.ite true (ev₆.trans (congrArg some (VG.Proof.Aes.AArch64.ofNat_sub_ne (by omega) (by decide) h1))) (fun _ => ?_)
        (fun h => by cases h)
      refine WP.seq ?_
      rw [WP.block_append_iff (M := isa)]
      refine VG.Proof.Aes.AArch64.xs_step hp (k := 1) (by omega) (by omega) x₆ fun s₇ x₇ => ?_
      obtain ⟨s₈, hs₈, ev₈, g₈, m₈, rd₈, wr₈⟩ := VG.Proof.Aes.AArch64.subT_ok s₇ 2 (by decide)
      refine WP.of_runBlock ⟨s₈, hs₈, ?_⟩
      have x₈ : VG.Proof.Aes.AArch64.XS m₀ D n g ks s₃ 2 s₈ := ⟨m₈ ▸ x₇.data, m₈ ▸ x₇.frame,
        fun r h => by rw [g₈ r h]; exact x₇.keep r h, rd₈.trans x₇.rd, wr₈.trans x₇.wr⟩
      rw [(x₇.keep _ (by decide)).trans hp.x4] at ev₈
      by_cases h2 : n - 4 * g = 2
      · refine WP.ite false (ev₈.trans (by rw [h2]; exact congrArg some VG.Proof.Aes.AArch64.ofNat_sub_eq)) (fun h => by cases h)
          (fun _ => WP.block_nil (by rw [h2]; exact x₈))
      refine WP.ite true (ev₈.trans (congrArg some (VG.Proof.Aes.AArch64.ofNat_sub_ne (by omega) (by decide) h2))) (fun _ => ?_)
        (fun h => by cases h)
      have h3 : n - 4 * g = 2 + 1 := by omega
      refine VG.Proof.Aes.AArch64.xs_step hp (k := 2) (by omega) (by omega) x₈ fun s₉ x₉ => ?_
      rw [h3]; exact x₉
    · obtain ⟨s', hs', z', o', m', rd', wr'⟩ := VG.Proof.Aes.AArch64.clear_ok s
      refine WP.of_runBlock ⟨s', hs', m' ▸ hs.frame, fun r h1 _ h3 => (o' r h3).trans (hs.keep r h1),
        rd'.trans hs.rd, wr'.trans hs.wr, .inl ⟨z', ?_⟩⟩
      have := hs.data
      rw [show 4 * g + (n - 4 * g) = n by omega, ← m'] at this
      exact this

end Xor

/-! ## A group -/

/-- What the group loop runs with: `s₂` is the state after the round keys
are bitsliced, `b` the scratch buffer, `D` the data (`n` blocks, whose
bytes were `m₀`'s), `icb` the first counter block. -/
structure GSetup (s₂ : State) (b D : Addr) (n R : Nat) (w : List Byte) (icb : Spec.Gcm.Block) :
    Prop where
  scr : (⟨b, 2048⟩ : Region) ∈ s₂.wr
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₂.wr
  hn : 16 * n < 2 ^ 64
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 2048⟩
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  keys : VG.Proof.Aes.AArch64.KeysAt s₂.mem (b + BitVec.ofNat 64 (1920 - 64 * R)) R w
  lo : ∀ i < 8, ∀ j < 8, (VG.Proof.Aes.AArch64.cloW s₂.mem b).getLsbD (8 * i + j) = icb.getLsbD (8 * (15 - i) + j)
  hi : ∀ i < 4, ∀ j < 8, (VG.Proof.Aes.AArch64.chiW s₂.mem b).getLsbD (8 * i + j) = icb.getLsbD (8 * (7 - i) + j)
  hi' : ∀ p, 32 ≤ p → (VG.Proof.Aes.AArch64.chiW s₂.mem b).getLsbD p = false

/-- The memory a group writes: slots 0–47, the counter and the data. -/
abbrev gRegions (b D : Addr) (n : Nat) : List Region :=
  [⟨b, 384⟩, ⟨b + BitVec.ofNat 64 (8 * 61), 4⟩, ⟨D, 16 * n⟩]

/-- Before group `g`. -/
structure GInv (m₀ : Mem) (s₂ : State) (b D : Addr) (n R : Nat) (w : List Byte)
    (icb : Spec.Gcm.Block) (g : Nat) (s : State) : Prop where
  hg : 4 * g < n
  x3 : s.gpr .x3 = D + BitVec.ofNat 64 (64 * g)
  x4 : s.gpr .x4 = BitVec.ofNat 64 (n - 4 * g)
  base : s.gpr .x5 = b
  x0 : s.gpr .x0 = b + BitVec.ofNat 64 (1920 - 64 * R)
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame (VG.Proof.Aes.AArch64.gRegions b D n) s₂.mem s.mem
  num : VG.Proof.Aes.AArch64.numW s.mem b = icb.extractLsb' 0 32 + BitVec.ofNat 32 (4 * g)
  data : VG.Proof.Aes.AArch64.DataInv m₀ s.mem D n (4 * g) (VG.Proof.Aes.AArch64.keyStream R w icb)

/-- After the last group. -/
structure GDone (m₀ : Mem) (s₂ : State) (b D : Addr) (n R : Nat) (w : List Byte)
    (icb : Spec.Gcm.Block) (s : State) : Prop where
  base : s.gpr .x5 = b
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame (VG.Proof.Aes.AArch64.gRegions b D n) s₂.mem s.mem
  data : VG.Proof.Aes.AArch64.DataInv m₀ s.mem D n n (VG.Proof.Aes.AArch64.keyStream R w icb)

theorem scr_disj (b : Addr) {lx y ly : Nat} (h : lx ≤ y) (hy : y + ly ≤ 2048) :
    Region.Disjoint ⟨b, lx⟩ ⟨b + BitVec.ofNat 64 y, ly⟩ := Offset.base_disjoint b h (by omega)

theorem scr_sub (b : Addr) {x lx : Nat} (h : x + lx ≤ 2048) :
    Region.Sub ⟨b + BitVec.ofNat 64 x, lx⟩ ⟨b, 2048⟩ := Offset.sub_base b h

theorem keysAt_frame {m m' : Mem} {b : Addr} {R : Nat} {w : List Byte} {rs : List Region}
    (hR : R ≤ 14) (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + 1024, 1024⟩ r)
    (h : VG.Proof.Aes.AArch64.KeysAt m (b + BitVec.ofNat 64 (1920 - 64 * R)) R w) :
    VG.Proof.Aes.AArch64.KeysAt m' (b + BitVec.ofNat 64 (1920 - 64 * R)) R w :=
  fun j hj => VG.Proof.Aes.AArch64.keyRel_congr (h j hj) fun k hk => hf.readW (VG.Proof.Aes.AArch64.key_contains _ hR hj hk) hd (by decide)

theorem dataInv_frame {m₀ m m' : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : VG.Proof.Aes.AArch64.DataInv m₀ m D n k ks) : VG.Proof.Aes.AArch64.DataInv m₀ m' D n k ks := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨D, 16 * n⟩) hd (by simp only; omega) hi

theorem GSetup.dat_disj {s₂ : State} {b D : Addr} {n R : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
    (hs : VG.Proof.Aes.AArch64.GSetup s₂ b D n R w icb) {x lx : Nat} (h : x + lx ≤ 2048) :
    Region.Disjoint ⟨D, 16 * n⟩ ⟨b + BitVec.ofNat 64 x, lx⟩ :=
  hs.sep.sub_right (VG.Proof.Aes.AArch64.scr_sub b h)

theorem GSetup.keys_disj {s₂ : State} {b D : Addr} {n R : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
    (hs : VG.Proof.Aes.AArch64.GSetup s₂ b D n R w icb) : ∀ r ∈ VG.Proof.Aes.AArch64.gRegions b D n, Region.Disjoint ⟨b + 1024, 1024⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact VG.Proof.Aes.AArch64.keys_disjoint b
  · intro a h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    have : (BitVec.ofNat 64 (8 * 61)).toNat = 488 := by simp
    bv_omega
  · refine (hs.sep.sub_right fun a h => ?_).symm
    simp only [Region.Contains] at h ⊢
    bv_omega

theorem GSetup.slot_disj {s₂ : State} {b D : Addr} {n R : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
    (hs : VG.Proof.Aes.AArch64.GSetup s₂ b D n R w icb) {x lx : Nat} (h1 : 384 ≤ x) (h2 : x + lx ≤ 488 ∨ 492 ≤ x)
    (h3 : x + lx ≤ 2048) : ∀ r ∈ VG.Proof.Aes.AArch64.gRegions b D n, Region.Disjoint ⟨b + BitVec.ofNat 64 x, lx⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (VG.Proof.Aes.AArch64.scr_disj b h1 h3).symm
  · exact Offset.disjoint b (by omega) (by omega) (by omega)
  · exact (hs.dat_disj h3).symm

/-- One group: from before group `g`, to after the last group (`x4` zero) or
before group `g + 1`. -/
theorem group_ok {m₀ : Mem} {s₂ : State} {b D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (hs : VG.Proof.Aes.AArch64.GSetup s₂ b D n R w icb) {g : Nat} {s : State}
    (hi : VG.Proof.Aes.AArch64.GInv m₀ s₂ b D n R w icb g s) :
    WP isa group s fun s' => (AArch64.eval (.nonzero .x .x4) s' = some false ∧
        VG.Proof.Aes.AArch64.GDone m₀ s₂ b D n R w icb s') ∨
      (AArch64.eval (.nonzero .x .x4) s' = some true ∧ VG.Proof.Aes.AArch64.GInv m₀ s₂ b D n R w icb (g + 1) s') := by
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega
  have hn := hs.hn
  have hscr : (⟨b, 2048⟩ : Region) ∈ s.wr := hi.wr ▸ hs.scr
  unfold group
  refine WP.seq (WP.mono (VG.Proof.Aes.AArch64.ctrBlocks_wp hi.base hscr) fun s₁ ⟨hq₁, o₁, m₁, rd₁, wr₁⟩ => ?_)
  have hb₁ : s₁.gpr .x5 = b := (o₁ .x5 (by decide)).trans hi.base
  have c488 : (⟨b + BitVec.ofNat 64 (8 * 61), 4⟩ : Region).Contains
      (b + BitVec.ofNat 64 (8 * 61)) (32 / 8) := Region.contains_self _ _
  have f₁ : Frame [⟨b + BitVec.ofNat 64 (8 * 61), 4⟩] s.mem s₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c488
  have hf₁ : Frame (VG.Proof.Aes.AArch64.gRegions b D n) s₂.mem s₁.mem :=
    hi.frame.trans (f₁.mono fun r hr => by simp at hr; simp [hr])
  have clo : VG.Proof.Aes.AArch64.cloW s.mem b = VG.Proof.Aes.AArch64.cloW s₂.mem b :=
    hi.frame.readW (Region.contains_self _ _) (hs.slot_disj (by omega) (by omega) (by omega)) (by decide)
  have chi : VG.Proof.Aes.AArch64.chiW s.mem b = VG.Proof.Aes.AArch64.chiW s₂.mem b :=
    hi.frame.readW (Region.contains_self _ _) (hs.slot_disj (by omega) (by omega) (by omega)) (by decide)
  have hp : VG.Proof.Aes.AArch64.EncPre s₁ R w :=
    ⟨by rw [show sb = .x5 from rfl, hb₁, wr₁, hi.wr]; exact hs.scr, hs.rounds,
      by rw [o₁ .x0 (by decide), hi.x0, show sb = .x5 from rfl, hb₁],
      by rw [o₁ .x0 (by decide), hi.x0]; exact VG.Proof.Aes.AArch64.keysAt_frame hR hf₁ hs.keys_disj hs.keys⟩
  have hin : InRel (VG.Proof.Aes.AArch64.Q s₁) (fun c => ctrState icb (4 * g + c)) :=
    VG.Proof.Aes.AArch64.ctr_inRel (by rw [clo]; exact hs.lo) (by rw [chi]; exact hs.hi) (by rw [chi]; exact hs.hi') hi.num
      hq₁
  refine WP.seq (WP.mono (VG.Proof.Aes.AArch64.encrypt4_ok hp hin) fun s₃ ⟨hc₃, hin₃⟩ => ?_)
  have fr₃ := hc₃.frame
  rw [show sb = .x5 from rfl, hb₁] at fr₃
  have d384 : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 384⟩ := hs.sep.sub_right (Region.sub_prefix (by omega))
  have hx : VG.Proof.Aes.AArch64.XPre m₀ D n g (VG.Proof.Aes.AArch64.keyStream R w icb) s₃ :=
    { hg := hi.hg, hn := hn, dat := by rw [hc₃.wr, wr₁, hi.wr]; exact hs.dat
      x3 := by rw [hc₃.keep .x3 (by decide) (by decide), o₁ .x3 (by decide), hi.x3]
      x4 := by rw [hc₃.keep .x4 (by decide) (by decide), o₁ .x4 (by decide), hi.x4]
      data := VG.Proof.Aes.AArch64.dataInv_frame fr₃ (by simpa using d384) hn
        (VG.Proof.Aes.AArch64.dataInv_frame f₁ (by simpa using hs.dat_disj (by omega)) hn hi.data)
      ks := fun c hc t ht => VG.Proof.Aes.AArch64.ks_of_inRel hin₃ hc ht }
  refine WP.mono (VG.Proof.Aes.AArch64.xorPhase_wp hx) fun s' ⟨f', o', rd', wr', hz⟩ => ?_
  have keep : ∀ r, r ∉ VG.Proof.Aes.AArch64.layerWrites → r ≠ kp → r ≠ .x3 → r ≠ .x4 → s'.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => (o' r (fun h => h1 (h ▸ by decide)) h3 h4).trans ((hc₃.keep r h1 h2).trans (o₁ r h1))
  have base' : s'.gpr .x5 = b := (keep .x5 (by decide) (by decide) (by decide) (by decide)).trans hi.base
  have rd'' : s'.rd = s₂.rd := by rw [rd', hc₃.rd, rd₁, hi.rd]
  have wr'' : s'.wr = s₂.wr := by rw [wr', hc₃.wr, wr₁, hi.wr]
  have frame' : Frame (VG.Proof.Aes.AArch64.gRegions b D n) s₂.mem s'.mem :=
    hf₁.trans ((fr₃.mono fun r hr => by simp at hr; simp [hr]).trans (f'.mono fun r hr => by simp at hr; simp [hr]))
  rcases hz with ⟨z, d⟩ | ⟨h4, d, x3', x4'⟩
  · exact .inl ⟨by simp [AArch64.eval, State.read, z], base', rd'', wr'', frame', d⟩
  · refine .inr ⟨?_, ⟨by omega, x3', x4', base', ?_, rd'', wr'', frame', ?_, d⟩⟩
    · have hne : BitVec.ofNat 64 (n - 4 * (g + 1)) ≠ 0 := by
        intro h; have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        simp at this; omega
      simpa [AArch64.eval, State.read, x4'] using hne
    · rw [keep .x0 (by decide) (by decide) (by decide) (by decide), hi.x0]
    · have e₁ : VG.Proof.Aes.AArch64.numW s'.mem b = VG.Proof.Aes.AArch64.numW s₃.mem b :=
        f'.readW (Region.contains_self _ _) (by simpa using (hs.dat_disj (by omega)).symm) (by decide)
      have e₂ : VG.Proof.Aes.AArch64.numW s₃.mem b = VG.Proof.Aes.AArch64.numW s₁.mem b :=
        fr₃.readW (Region.contains_self _ _) (by simpa using (VG.Proof.Aes.AArch64.scr_disj b (by omega) (by omega)).symm)
          (by decide)
      rw [e₁, e₂, m₁, VG.Proof.Aes.AArch64.numW, Mem.readW_writeW_self32, hi.num, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp
      omega

/-- The loop over the groups. -/
theorem groups_ok {m₀ : Mem} {s₂ : State} {b D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (hs : VG.Proof.Aes.AArch64.GSetup s₂ b D n R w icb) {s : State}
    (hi : VG.Proof.Aes.AArch64.GInv m₀ s₂ b D n R w icb 0 s) :
    WP isa (.loop group (.nonzero .x .x4)) s (VG.Proof.Aes.AArch64.GDone m₀ s₂ b D n R w icb) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = n - 4 * g ∧ VG.Proof.Aes.AArch64.GInv m₀ s₂ b D n R w icb g s)
    (fun k s ⟨g, hk, hg⟩ => WP.mono (VG.Proof.Aes.AArch64.group_ok hs hg) fun s' h => ?_) n s ⟨0, by omega, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, n - 4 * (g + 1), by have := hg.hg; omega, g + 1, rfl, d⟩

end VG.Proof.Aes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.AArch64.Ctr32`. -/
section

/-!
# AES counter mode on AArch64: the whole function

The prologue saves the callee-saved registers (checked by evaluation in the
naming domain, as is the epilogue restoring them), copies the counter block
to its slots and writes back the final counter; the key loop and the
group loop (`Group.lean`) do the rest.
-/

namespace VG.Proof.Aes

open Spec.Gcm

open VG.AArch64 in
/-- AArch64 contract for `vg_aes_ctr32(schedule: *const [u8; 240], rounds:
usize, counter: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut
[u64; 256])`: XORs the AES counter-mode keystream from the counter block at
`counter` into the `n` blocks at `data`, and advances the counter block by `n`.

The code may read `schedule` (240 bytes) and read and write `counter` (16
bytes), `data` (`16 n` bytes) and `scratch` (2048 bytes, whose contents on
exit are unspecified). These may not overlap each other, and `data` may not
wrap around the end of the address space. `rounds` is 10, 12 or 14. The
pointers, `rounds` and `n` are public; the key schedule, the counter block
and the data are secret. -/
def ctr32AArch64 : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 240⟩
    let counter : Region := ⟨s.gpr .x2, 16⟩
    let data : Region := ⟨s.gpr .x3, 16 * (s.gpr .x4).toNat⟩
    let scratch : Region := ⟨s.gpr .x5, 2048⟩
    s.rd = [sched] ∧ s.wr = [counter, data, scratch] ∧
    sched.Disjoint counter ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
    counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .x3).toNat + 16 * (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
  post s s' :=
    let ciph := aesWith (s.gpr .x1).toNat
      (Spec.Aes.bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)))
    blocksAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat =
        ctr32 ciph (blockAt s.mem (s.gpr .x2)) (blocksAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) ∧
      blockAt s'.mem (s.gpr .x2) = Nat.repeat inc32 (s.gpr .x4).toNat (blockAt s.mem (s.gpr .x2))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for `vg_aes_expand_key(key: *const u8, key_len: usize,
schedule: *mut [u8; 240], scratch: *mut [u64; 64])`: writes the key schedule of
the `key_len`-byte key at `key` to `schedule`.

The code may read `key` (`key_len` bytes) and read and write `schedule`
(240 bytes) and `scratch` (512 bytes, whose contents on exit are
unspecified). These may not overlap each other. `key_len` is 16, 24 or 32.
The pointers and `key_len` are public; the key is secret. -/
def expandKeyAArch64 : Contract AArch64.isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let sched : Region := ⟨s.gpr .x2, 240⟩
    let scratch : Region := ⟨s.gpr .x3, 512⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧
    key.Disjoint sched ∧ key.Disjoint scratch ∧ sched.Disjoint scratch ∧
    ((s.gpr .x1).toNat = 16 ∨ (s.gpr .x1).toNat = 24 ∨ (s.gpr .x1).toNat = 32)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .x2) (16 * (Spec.Aes.rounds ((s.gpr .x1).toNat / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.Aes

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers the code uses, in the order of `savedRegs`. -/
def sreg : Nat → Reg
  | 0 => .x19 | 1 => .x20 | 2 => .x21 | 3 => .x22 | 4 => .x23 | 5 => .x24 | 6 => .x25
  | 7 => .x26 | 8 => .x27 | _ => .x28

/-- `savedRegs` at their offsets in bytes. -/
abbrev savedSlots : List (Reg × Nat) := savedRegs.map fun (r, k) => (r, 8 * k)

theorem savedSlots_eq : VG.Proof.Aes.AArch64.savedSlots = (List.range 10).map fun i => (VG.Proof.Aes.AArch64.sreg i, 8 * (48 + i)) := rfl

theorem slots_idx {p : Reg × Nat} (hp : p ∈ VG.Proof.Aes.AArch64.savedSlots) : ∃ i < 10, p = (VG.Proof.Aes.AArch64.sreg i, 8 * (48 + i)) := by
  rw [VG.Proof.Aes.AArch64.savedSlots_eq] at hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  exact ⟨i, List.mem_range.mp hi, rfl⟩

theorem slots_mem {i : Nat} (hi : i < 10) : (VG.Proof.Aes.AArch64.sreg i, 8 * (48 + i)) ∈ VG.Proof.Aes.AArch64.savedSlots := by
  rw [VG.Proof.Aes.AArch64.savedSlots_eq]; exact List.mem_map_of_mem (List.mem_range.mpr hi)

theorem slots_fits : Spill.Fits VG.Proof.Aes.AArch64.savedSlots := by decide

theorem slots_restorable : Spill.Restorable sb VG.Proof.Aes.AArch64.savedSlots := by decide

theorem slots_end : ∀ p ∈ VG.Proof.Aes.AArch64.savedSlots, p.2 + 8 ≤ 8 * 59 := by decide

theorem saveRegs_eq : saveRegs = Spill.saveCode sb VG.Proof.Aes.AArch64.savedSlots := rfl

theorem restoreRegs_eq : restoreRegs = Spill.restoreCode sb VG.Proof.Aes.AArch64.savedSlots := rfl

/-- The saved registers are in slots 48–57. -/
def Saved (s₀ : State) (b : Addr) (m : Mem) : Prop :=
  ∀ i < 10, m.readW (wordAddr b (48 + i)) 64 = s₀.gpr (VG.Proof.Aes.AArch64.sreg i)

theorem save_ok {s : State} {b : Addr} {n : Nat} (hw : (⟨b, n⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hn : 8 * 59 ≤ n) :
    WP isa (.block saveRegs) s fun s' => VG.Proof.Aes.AArch64.Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b, 8 * 59⟩] s.mem s'.mem := by
  rw [VG.Proof.Aes.AArch64.saveRegs_eq]; subst hb
  refine WP.mono (Spill.save_wp slots_fits.1 fun p hp => ?_) fun s' h =>
    ⟨fun i hi => ?_, h.gpr, h.rd, h.wr, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := VG.Proof.Aes.AArch64.slots_idx hp
    refine ⟨_, hw, ?_⟩
    show (⟨s.gpr sb, n⟩ : Region).Contains (s.gpr sb + BitVec.ofNat 64 (8 * (48 + i))) 8
    exact Offset.contains_base _ (by omega) (by omega)
  · have h' := Spill.saveMem_saved VG.Proof.Aes.AArch64.slots_fits s.mem (s.gpr sb) s.gpr _ (VG.Proof.Aes.AArch64.slots_mem hi)
    dsimp only at h'
    rw [h.mem]; exact h'
  · rw [h.mem]; exact Spill.saveMem_frame_base VG.Proof.Aes.AArch64.slots_end (by decide) _ _ _

theorem restore_ok {s₀ s : State} {b : Addr} {n : Nat} (hw : (⟨b, n⟩ : Region) ∈ s.wr)
    (hb : s.gpr sb = b) (hn : 8 * 59 ≤ n) (hs : VG.Proof.Aes.AArch64.Saved s₀ b s.mem) :
    WP isa (.block restoreRegs) s fun s' => (∀ i < 10, s'.gpr (VG.Proof.Aes.AArch64.sreg i) = s₀.gpr (VG.Proof.Aes.AArch64.sreg i)) ∧
      Frame [⟨b, 8 * 59⟩] s.mem s'.mem := by
  rw [VG.Proof.Aes.AArch64.restoreRegs_eq]
  refine WP.mono (Spill.restore_wp hb slots_fits.1 VG.Proof.Aes.AArch64.slots_restorable (fun p hp => ?_) (fun p hp => ?_))
    fun s' h => ⟨fun i hi => h.gpr _ (VG.Proof.Aes.AArch64.slots_mem hi), by rw [h.mem]; exact Frame.refl _ _⟩
  · obtain ⟨i, hi, rfl⟩ := VG.Proof.Aes.AArch64.slots_idx hp
    refine ⟨_, List.mem_append_right _ hw, ?_⟩
    show (⟨b, n⟩ : Region).Contains (b + BitVec.ofNat 64 (8 * (48 + i))) 8
    exact Offset.contains_base _ (by omega) (by omega)
  · obtain ⟨i, hi, rfl⟩ := VG.Proof.Aes.AArch64.slots_idx hp
    exact hs i hi

/-! ## The counter block -/

/-- The memory after `ctrSetup`: the counter block's slots, and the final
counter written back. -/
def setupMem (m : Mem) (b ctr : Addr) (N : BitVec 64) : Mem :=
  let m₁ := m.writeW (b + BitVec.ofNat 64 (8 * 59)) (m.readW (ctr + BitVec.ofNat 64 0) 64)
  let m₂ := m₁.writeW (b + BitVec.ofNat 64 (8 * 60))
    ((m₁.readW (ctr + BitVec.ofNat 64 8) 32).setWidth 64)
  let c := rev32 (m₂.readW (ctr + BitVec.ofNat 64 12) 32)
  let m₃ := m₂.writeW (b + BitVec.ofNat 64 (8 * 61)) c
  m₃.writeW (ctr + BitVec.ofNat 64 12) (rev32 (c + N.setWidth 32))

set_option simprocs false in
theorem ctrSetup_ok {s : State} {b ctr : Addr} (hb : s.gpr .x5 = b) (hc : s.gpr .x2 = ctr)
    (hw : (⟨b, 2048⟩ : Region) ∈ s.wr) (hcw : (⟨ctr, 16⟩ : Region) ∈ s.wr) :
    ∃ s', runBlock isa ctrSetup s = some s' ∧ s'.mem = VG.Proof.Aes.AArch64.setupMem s.mem b ctr (s.gpr .x4) ∧
      (∀ r, r ≠ .x6 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw' := List.mem_append_right s.rd hw
  have hcw' := List.mem_append_right s.rd hcw
  have l0 := VG.Proof.Aes.AArch64.in_off hcw' (off := 0) (n := 8) (by omega) (by omega)
  have l8 := VG.Proof.Aes.AArch64.in_off hcw' (off := 8) (n := 4) (by omega) (by omega)
  have l12 := VG.Proof.Aes.AArch64.in_off hcw' (off := 12) (n := 4) (by omega) (by omega)
  have w12 := VG.Proof.Aes.AArch64.in_off hcw (off := 12) (n := 4) (by omega) (by omega)
  have w59 := VG.Proof.Aes.AArch64.in_off hw (off := 8 * 59) (n := 8) (by omega) (by omega)
  have w60 := VG.Proof.Aes.AArch64.in_off hw (off := 8 * 60) (n := 8) (by omega) (by omega)
  have w61 := VG.Proof.Aes.AArch64.in_off hw (off := 8 * 61) (n := 4) (by omega) (by omega)
  refine ⟨_, by
    simp (config := {decide := true}) only [ctrSetup, stS, q, sb, cLo, cHi, cNum,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bytes,
      Size.bits, State.read, State.write, hb, hc, ite_false, ite_true, l0, l8, l12, w12, w59, w60, w61,
      Option.map_some, Option.bind_some, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨?_, fun r h => by simp [h], rfl, rfl⟩
  simp only [VG.Proof.Aes.AArch64.setupMem, Mem.writeW, Mem.readW, BitVec.setWidth_eq, VG.Proof.Aes.AArch64.sw_32]

theorem c_off (base : Addr) {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n :=
  Offset.contains_base base h ho

theorem out_of_disj {r₁ r₂ : Region} (hd : r₁.Disjoint r₂) {x a : Addr} {n : Nat} (hx : r₁.Contains x 1)
    (ha : r₂.Contains a n) : ¬ (x - a).toNat < n := fun h => hd x hx (ha.byte h)

section Setup

variable {m : Mem} {b ctr : Addr} {N : BitVec 64}

theorem setupMem_eq (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2048⟩) :
    VG.Proof.Aes.AArch64.setupMem m b ctr N =
      (((m.writeW (b + BitVec.ofNat 64 (8 * 59)) (m.readW (ctr + BitVec.ofNat 64 0) 64)).writeW
        (b + BitVec.ofNat 64 (8 * 60)) ((m.readW (ctr + BitVec.ofNat 64 8) 32).setWidth 64)).writeW
        (b + BitVec.ofNat 64 (8 * 61)) (rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32))).writeW
        (ctr + BitVec.ofNat 64 12)
          (rev32 (rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32) + N.setWidth 32)) := by
  have s8 : Mem.Sep (ctr + BitVec.ofNat 64 8) (32 / 8) (b + BitVec.ofNat 64 (8 * 59)) (64 / 8) :=
    hd.sep (VG.Proof.Aes.AArch64.c_off ctr (by omega) (by omega)) (VG.Proof.Aes.AArch64.c_off b (by omega) (by omega))
  have s12a : Mem.Sep (ctr + BitVec.ofNat 64 12) (32 / 8) (b + BitVec.ofNat 64 (8 * 59)) (64 / 8) :=
    hd.sep (VG.Proof.Aes.AArch64.c_off ctr (by omega) (by omega)) (VG.Proof.Aes.AArch64.c_off b (by omega) (by omega))
  have s12b : Mem.Sep (ctr + BitVec.ofNat 64 12) (32 / 8) (b + BitVec.ofNat 64 (8 * 60)) (64 / 8) :=
    hd.sep (VG.Proof.Aes.AArch64.c_off ctr (by omega) (by omega)) (VG.Proof.Aes.AArch64.c_off b (by omega) (by omega))
  simp only [VG.Proof.Aes.AArch64.setupMem]
  rw [Mem.readW_writeW_sep s8 (by decide), Mem.readW_writeW_sep s12b (by decide),
    Mem.readW_writeW_sep s12a (by decide)]

theorem setup_frame (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2048⟩) :
    Frame [⟨b + BitVec.ofNat 64 (8 * 59), 20⟩, ⟨ctr, 16⟩] m (VG.Proof.Aes.AArch64.setupMem m b ctr N) := by
  rw [VG.Proof.Aes.AArch64.setupMem_eq hd]
  have h₀ : (⟨b + BitVec.ofNat 64 (8 * 59), 20⟩ : Region) ∈
      [(⟨b + BitVec.ofNat 64 (8 * 59), 20⟩ : Region), ⟨ctr, 16⟩] := by simp
  have h₁ : (⟨ctr, 16⟩ : Region) ∈ [(⟨b + BitVec.ofNat 64 (8 * 59), 20⟩ : Region), ⟨ctr, 16⟩] := by
    simp
  exact ((((Frame.refl _ _).writeW h₀ _ (VG.Proof.Aes.AArch64.off_contains b (by omega) (by omega) (by omega))).writeW h₀ _
    (VG.Proof.Aes.AArch64.off_contains b (by omega) (by omega) (by omega))).writeW h₀ _
    (VG.Proof.Aes.AArch64.off_contains b (by omega) (by omega) (by omega))).writeW h₁ _ (VG.Proof.Aes.AArch64.c_off ctr (by omega) (by omega))

theorem setup_slots (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2048⟩) :
    VG.Proof.Aes.AArch64.cloW (VG.Proof.Aes.AArch64.setupMem m b ctr N) b = m.readW (ctr + BitVec.ofNat 64 0) 64 ∧
    VG.Proof.Aes.AArch64.chiW (VG.Proof.Aes.AArch64.setupMem m b ctr N) b = (m.readW (ctr + BitVec.ofNat 64 8) 32).setWidth 64 ∧
    VG.Proof.Aes.AArch64.numW (VG.Proof.Aes.AArch64.setupMem m b ctr N) b = rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32) := by
  rw [VG.Proof.Aes.AArch64.setupMem_eq hd]
  have t : ∀ {k w}, 8 * k + w / 8 ≤ 2048 → Mem.Sep (b + BitVec.ofNat 64 (8 * k)) (w / 8)
      (ctr + BitVec.ofNat 64 12) (32 / 8) := fun h =>
    hd.symm.sep (VG.Proof.Aes.AArch64.c_off b h (by omega)) (VG.Proof.Aes.AArch64.c_off ctr (by omega) (by omega))
  refine ⟨?_, ?_, ?_⟩
  · rw [VG.Proof.Aes.AArch64.cloW, Mem.readW_writeW_sep (t (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep b (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep b (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [VG.Proof.Aes.AArch64.chiW, Mem.readW_writeW_sep (t (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep b (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [VG.Proof.Aes.AArch64.numW, Mem.readW_writeW_sep (t (by omega)) (by decide), Mem.readW_writeW_self32]

theorem writeW_apply {m : Mem} {a x : Addr} {w : Nat} (v : BitVec w) :
    m.writeW a v x = if (x - a).toNat < w / 8 then
      (v.setWidth (8 * (w / 8))).extractLsb' (8 * (x - a).toNat) 8 else m x := rfl

theorem setup_ctr (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2048⟩) {k : Nat} (hk : k < 16) :
    VG.Proof.Aes.AArch64.setupMem m b ctr N (ctr + BitVec.ofNat 64 k) =
      if k < 12 then m (ctr + BitVec.ofNat 64 k)
      else (rev32 (rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32) + N.setWidth 32)).extractLsb'
        (8 * (k - 12)) 8 := by
  rw [VG.Proof.Aes.AArch64.setupMem_eq hd, VG.Proof.Aes.AArch64.writeW_apply, VG.Proof.Aes.AArch64.off_toNat ctr (by omega) (by omega)]
  have hx : (⟨ctr, 16⟩ : Region).Contains (ctr + BitVec.ofNat 64 k) 1 := VG.Proof.Aes.AArch64.c_off ctr (by omega) (by omega)
  by_cases h : k < 12
  · rw [ite_eq_right (show ¬ 12 ≤ k by omega), ite_eq_right (show ¬ 2 ^ 64 + k - 12 < 32 / 8 by omega),
      ite_eq_left h, VG.Proof.Aes.AArch64.writeW_apply, ite_eq_right (VG.Proof.Aes.AArch64.out_of_disj hd hx (VG.Proof.Aes.AArch64.c_off b (by omega) (by omega))),
      VG.Proof.Aes.AArch64.writeW_apply, ite_eq_right (VG.Proof.Aes.AArch64.out_of_disj hd hx (VG.Proof.Aes.AArch64.c_off b (by omega) (by omega))),
      VG.Proof.Aes.AArch64.writeW_apply, ite_eq_right (VG.Proof.Aes.AArch64.out_of_disj hd hx (VG.Proof.Aes.AArch64.c_off b (by omega) (by omega)))]
  · rw [ite_eq_left (show 12 ≤ k by omega), ite_eq_left (show k - 12 < 32 / 8 by omega),
      ite_eq_right h, BitVec.setWidth_eq]

end Setup

/-! ## The counter block and the data, as blocks -/

/-- The counter, as the slot holds it. -/
theorem icb_lo (m : Mem) (ctr : Addr) :
    rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32) = (Spec.Gcm.blockAt m ctr).extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have e : t = 8 * (t / 8) + t % 8 := by omega
  rw [e, VG.Proof.Aes.AArch64.rev32_bit _ (by omega) (by omega), BitVec.getLsbD_extractLsb', Nat.zero_add,
    decide_eq_true (by omega : 8 * (t / 8) + t % 8 < 32), Bool.true_and,
    show 8 * (t / 8) + t % 8 = 8 * (15 - (15 - t / 8)) + t % 8 by omega,
    blockAt_bit _ _ (by omega) (by omega)]
  have hb := Mem.readW_byte m (ctr + BitVec.ofNat 64 12) (i := 3 - t / 8) (by omega)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 12 + (3 - t / 8) = 15 - t / 8 by omega] at hb
  rw [hb, BitVec.getLsbD_extractLsb']
  simp [show t % 8 < 8 by omega]

theorem ctr_after {m m' : Mem} {ctr : Addr} {n : Nat}
    (h : ∀ k < 16, m' (ctr + BitVec.ofNat 64 k) = if k < 12 then m (ctr + BitVec.ofNat 64 k)
      else (rev32 (rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32) +
        (BitVec.ofNat 64 n).setWidth 32)).extractLsb' (8 * (k - 12)) 8) :
    Spec.Gcm.blockAt m' ctr = Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt m ctr) := by
  refine block_ext fun k hk => ?_
  rw [toBytes_blockAt _ _ hk, h k hk, ctrBlock_byte _ _ hk]
  split
  · rw [toBytes_blockAt _ _ hk]
  · rw [VG.Proof.Aes.AArch64.icb_lo, show (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n by
      apply BitVec.eq_of_toNat_eq; simp]
    refine byte_ext fun j hj => ?_
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', VG.Proof.Aes.AArch64.rev32_bit _ (by omega) hj]
    simp only [hj, decide_true, Bool.true_and]
    congr 1; omega

theorem ctr32_of_dataInv {m₀ m : Mem} {D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (h : VG.Proof.Aes.AArch64.DataInv m₀ m D n n (VG.Proof.Aes.AArch64.keyStream R w icb)) :
    Spec.Gcm.blocksAt m D n =
      Spec.Gcm.ctr32 (Spec.Gcm.aesWith R w) icb (Spec.Gcm.blocksAt m₀ D n) := by
  unfold Spec.Gcm.ctr32 Spec.Gcm.keystream Spec.Gcm.blocksAt
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith, List.length_map,
    List.length_range]
  simp only [List.length_map, List.length_range] at h1
  refine block_ext fun k hk => ?_
  rw [toBytes_xor _ _ hk, toBytes_blockAt _ _ hk, toBytes_blockAt _ _ hk, BitVec.add_assoc,
    ← BitVec.ofNat_add, h _ (by omega), ite_eq_left (by omega)]
  refine congrArg (_ ^^^ ·) ?_
  unfold Spec.Gcm.aesWith
  rw [toBytes_ofBytes (by simp) hk, VG.Proof.Aes.AArch64.keyStream, show (16 * i + k) / 16 = i by omega,
    show (16 * i + k) % 16 = k by omega, getD_eq _ hk, List.getD_eq_getElem?_getD,
    Vector.getElem?_toList, Vector.getElem?_eq_getElem hk, Option.getD_some]
  rfl

/-! ## Setting up the loops -/

theorem shl4 (x : BitVec 64) : x <<< 4 = BitVec.ofNat 64 (16 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem keySetup_ok (s : State) :
    ∃ s', runBlock isa keySetup s = some s' ∧ s'.gpr .x2 = s.gpr .x1 + 1 ∧
      s'.gpr .x0 = s.gpr .x0 + s.gpr .x1 <<< 4 ∧
      s'.gpr .x1 = s.gpr sb + BitVec.ofNat 64 1920 ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x6 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [↓reduceIte, Nat.reduceLT, keySetup, q, sb, lastKey, runBlock_cons, runStep_some,
      exec]
    rfl, ?_⟩
  refine ⟨by simp [State.write, State.read], by simp [State.write, State.read],
    by simp [State.write, State.read, sb], fun r h1 h2 h3 h4 => by simp [State.write, h1, h2, h3, h4],
    rfl, rfl, rfl⟩

theorem keyDone_ok (s : State) :
    ∃ s', runBlock isa keyDone s = some s' ∧ s'.gpr .x0 = s.gpr .x1 + 64 ∧
      (∀ r, r ≠ .x0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by rw [keyDone, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  exact ⟨by simp [State.write, State.read], fun r h => by simp [State.write, h], rfl, rfl, rfl⟩

/-! ## The whole function -/

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

/-- A frame within the writable regions. -/
theorem frame_wr {rs : List Region} {m m' : Mem} {C D b : Addr} {len : Nat} (hf : Frame rs m m')
    (h : ∀ r ∈ rs, Region.Sub r ⟨C, 16⟩ ∨ Region.Sub r ⟨D, len⟩ ∨ Region.Sub r ⟨b, 2048⟩) :
    Frame [⟨C, 16⟩, ⟨D, len⟩, ⟨b, 2048⟩] m m' :=
  hf.sub fun r hr => by
    rcases h r hr with h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩

theorem saved_frame {s₀ : State} {b : Addr} {m m' : Mem} {rs : List Region} (h : VG.Proof.Aes.AArch64.Saved s₀ b m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 384, 88⟩ r) :
    VG.Proof.Aes.AArch64.Saved s₀ b m' := fun i hi => by
  rw [← h i hi]
  exact hf.readW (VG.Proof.Aes.AArch64.off_contains b (by omega) (by omega) (by omega)) hd (by decide)

theorem notKeyWrites : ∀ r ∈ [Reg.x3, .x4, .x5], r ∉ VG.Proof.Aes.AArch64.keyWrites := by decide

theorem correct {s₀ : State} (hp : Proof.Aes.ctr32AArch64.pre s₀) :
    WP isa Impl.Aes.AArch64.ctr32 s₀ fun s' =>
      (∀ i < 10, s'.gpr (VG.Proof.Aes.AArch64.sreg i) = s₀.gpr (VG.Proof.Aes.AArch64.sreg i)) ∧ Proof.Aes.ctr32AArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dSC, dSD, dSS, dCD, dCS, dDS, hwrap, hR⟩ := hp
  have hwC : (⟨s₀.gpr .x2, 16⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hwD : (⟨s₀.gpr .x3, 16 * (s₀.gpr .x4).toNat⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hwS : (⟨s₀.gpr .x5, 2048⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hrS : (⟨s₀.gpr .x0, 240⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  have n16 : 16 * (s₀.gpr .x4).toNat < 2 ^ 64 := by
    refine Nat.lt_of_not_le fun hc => dCD (s₀.gpr .x2) (by simp [Region.Contains]) ?_
    simp only [Region.Contains]
    have := (s₀.gpr .x2 - s₀.gpr .x3).isLt
    omega
  have hR14 : (s₀.gpr .x1).toNat ≤ 14 := by omega
  -- The prologue.
  unfold Impl.Aes.AArch64.ctr32
  refine WP.seq ?_
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  refine WP.mono (VG.Proof.Aes.AArch64.save_ok hwS rfl (by decide)) fun s₁ ⟨sv₁, g₁, rd₁, wr₁, f₁⟩ => ?_
  obtain ⟨s₂, h₂, m₂, o₂, rd₂, wr₂⟩ :=
    VG.Proof.Aes.AArch64.ctrSetup_ok (s := s₁) (b := s₀.gpr .x5) (ctr := s₀.gpr .x2) (by rw [g₁]) (by rw [g₁])
      (wr₁ ▸ hwS) (wr₁ ▸ hwC)
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  obtain ⟨s₃, h₃, x2₃, x0₃, x1₃, o₃, m₃, rd₃, wr₃⟩ := VG.Proof.Aes.AArch64.keySetup_ok s₂
  refine WP.of_runBlock ⟨s₃, h₃, ?_⟩
  -- Registers and memory after the prologue.
  have g₃ : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x6 → s₃.gpr r = s₀.gpr r :=
    fun r h1 h2 h3 h4 => by rw [o₃ r h1 h2 h3 h4, o₂ r h4, g₁]
  have hb₃ : s₃.gpr sb = s₀.gpr .x5 := g₃ _ (by decide) (by decide) (by decide) (by decide)
  have fS : Frame [⟨s₀.gpr .x5 + BitVec.ofNat 64 (8 * 59), 20⟩, ⟨s₀.gpr .x2, 16⟩] s₁.mem s₃.mem := by
    rw [m₃, m₂, g₁]; exact VG.Proof.Aes.AArch64.setup_frame dCS
  have f₀₃ : Frame [⟨s₀.gpr .x5, 2048⟩, ⟨s₀.gpr .x2, 16⟩] s₀.mem s₃.mem := by
    refine (f₁.sub fun r hr => ⟨⟨s₀.gpr .x5, 2048⟩, by simp, ?_⟩).trans
      (fS.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨s₀.gpr .x5, 2048⟩, by simp, VG.Proof.Aes.AArch64.scr_sub _ (by omega)⟩
      · exact ⟨⟨s₀.gpr .x2, 16⟩, by simp, VG.Proof.Aes.AArch64.sub_refl _⟩
  let R := (s₀.gpr .x1).toNat
  let w := Spec.Aes.bytesAt s₀.mem (s₀.gpr .x0) (16 * (R + 1))
  have hk : VG.Proof.Aes.AArch64.KSetup s₃ (s₀.gpr .x5) (s₀.gpr .x0) R w :=
    { scr := by rw [wr₃, wr₂, wr₁]; exact hwS
      base := hb₃
      sch := List.mem_append_left _ (by rw [rd₃, rd₂, rd₁]; exact hrS)
      sep := dSS
      rounds := hR14
      w := fun i hi => by
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        refine (f₀₃.bytes (R := ⟨s₀.gpr .x0, 240⟩) (fun r hr => ?_) (by simp) (by simp only; omega)).symm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dSS
        · exact dSC }
  have hi₃ : VG.Proof.Aes.AArch64.KInv s₃ (s₀.gpr .x5) (s₀.gpr .x0) R w R s₃ :=
    { hj := Nat.le_refl _
      x2 := by
        rw [x2₃, o₂ _ (by decide), g₁]
        simp only [R]
        exact Offset.add_one_eq _
      x0 := by rw [x0₃, o₂ _ (by decide), o₂ _ (by decide), g₁, VG.Proof.Aes.AArch64.shl4]
      x1 := by rw [x1₃, o₂ _ (by decide), g₁]; simp [VG.Proof.Aes.AArch64.keyAddr, sb]
      rd := rfl
      wr := rfl
      sp := rfl
      keep := fun _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega) }
  -- The key loop.
  refine WP.seq (WP.mono (VG.Proof.Aes.AArch64.keyLoop_ok hk hi₃) fun s₄ d₄ => ?_)
  refine WP.seq ?_
  obtain ⟨s₅, h₅, x0₅, o₅, m₅, rd₅, wr₅⟩ := VG.Proof.Aes.AArch64.keyDone_ok s₄
  refine WP.of_runBlock ⟨s₅, h₅, ?_⟩
  have g₅ : ∀ r ∈ [Reg.x3, .x4, .x5], s₅.gpr r = s₃.gpr r := fun r hr => by
    rw [o₅ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide),
      d₄.keep r (VG.Proof.Aes.AArch64.notKeyWrites r hr)]
  have x4₅ : s₅.gpr .x4 = s₀.gpr .x4 := by
    rw [g₅ _ (by simp), g₃ _ (by decide) (by decide) (by decide) (by decide)]
  have x3₅ : s₅.gpr .x3 = s₀.gpr .x3 := by
    rw [g₅ _ (by simp), g₃ _ (by decide) (by decide) (by decide) (by decide)]
  have hb₅ : s₅.gpr .x5 = s₀.gpr .x5 := by rw [g₅ _ (by simp)]; exact hb₃
  have hK0 : s₅.gpr .x0 = s₀.gpr .x5 + BitVec.ofNat 64 (1920 - 64 * R) := by
    rw [x0₅, d₄.x1]; simp only [VG.Proof.Aes.AArch64.keyAddr, Nat.sub_zero, BitVec.sub_add_cancel]
  have fK : Frame [⟨s₀.gpr .x5 + BitVec.ofNat 64 0, 384⟩, ⟨s₀.gpr .x5 + BitVec.ofNat 64 1024, 1024⟩]
      s₃.mem s₅.mem := m₅ ▸ d₄.frame
  have kd : ∀ {x lx}, 384 ≤ x → x + lx ≤ 1024 → ∀ r ∈ [(⟨s₀.gpr .x5 + BitVec.ofNat 64 0, 384⟩ : Region),
      ⟨s₀.gpr .x5 + BitVec.ofNat 64 1024, 1024⟩], Region.Disjoint ⟨s₀.gpr .x5 + BitVec.ofNat 64 x, lx⟩ r := by
    intro x lx h1 h2 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have cd : ∀ {x lx}, x + lx ≤ 16 → ∀ r ∈ [(⟨s₀.gpr .x5, 8 * 59⟩ : Region)],
      Region.Disjoint ⟨s₀.gpr .x2 + BitVec.ofNat 64 x, lx⟩ r := by
    intro x lx h r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (dCS.sub_right (Region.sub_prefix (by omega))).sub_left (Offset.sub_base _ h)
  obtain ⟨sl₁, sl₂, sl₃⟩ := VG.Proof.Aes.AArch64.setup_slots (m := s₁.mem) (N := s₁.gpr .x4) dCS
  rw [← m₂, ← m₃] at sl₁ sl₂ sl₃
  have clo₅ : VG.Proof.Aes.AArch64.cloW s₅.mem (s₀.gpr .x5) = s₀.mem.readW (s₀.gpr .x2) 64 := by
    rw [VG.Proof.Aes.AArch64.cloW, fK.readW (Region.contains_self _ _) (kd (by omega) (by omega)) (by decide), ← VG.Proof.Aes.AArch64.cloW, sl₁,
      f₁.readW (Region.contains_self _ _) (cd (by omega)) (by decide)]
    simp
  have chi₅ : VG.Proof.Aes.AArch64.chiW s₅.mem (s₀.gpr .x5) = (s₀.mem.readW (s₀.gpr .x2 + BitVec.ofNat 64 8) 32).setWidth 64 := by
    rw [VG.Proof.Aes.AArch64.chiW, fK.readW (Region.contains_self _ _) (kd (by omega) (by omega)) (by decide), ← VG.Proof.Aes.AArch64.chiW, sl₂,
      f₁.readW (Region.contains_self _ _) (cd (by omega)) (by decide)]
  have num₅ : VG.Proof.Aes.AArch64.numW s₅.mem (s₀.gpr .x5) = rev32 (s₀.mem.readW (s₀.gpr .x2 + BitVec.ofNat 64 12) 32) := by
    rw [VG.Proof.Aes.AArch64.numW, fK.readW (Region.contains_self _ _) (kd (by omega) (by omega)) (by decide), ← VG.Proof.Aes.AArch64.numW, sl₃,
      f₁.readW (Region.contains_self _ _) (cd (by omega)) (by decide)]
  let icb := Spec.Gcm.blockAt s₀.mem (s₀.gpr .x2)
  let n := (s₀.gpr .x4).toNat
  have hs : VG.Proof.Aes.AArch64.GSetup s₅ (s₀.gpr .x5) (s₀.gpr .x3) n R w icb :=
    { scr := by rw [wr₅, d₄.wr, wr₃, wr₂, wr₁]; exact hwS
      dat := by rw [wr₅, d₄.wr, wr₃, wr₂, wr₁]; exact hwD
      hn := n16
      sep := dDS
      rounds := hR
      keys := fun j hj => VG.Proof.Aes.AArch64.keyRel_congr (d₄.keys j hj) fun k hk => by
        rw [m₅, VG.Proof.Aes.AArch64.keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add, show 1920 - 64 * R + 64 * j =
          1920 - 64 * (R - j) by omega]
      lo := fun i hi j hj => by
        rw [clo₅, VG.Proof.Aes.AArch64.readW_bit _ _ hi hj, blockAt_bit _ _ (by omega) hj]
      hi := fun i hi j hj => by
        rw [chi₅, BitVec.getLsbD_setWidth, show 8 * (7 - i) + j = 8 * (15 - (8 + i)) + j by omega,
          blockAt_bit _ _ (by omega) hj, BitVec.ofNat_add, ← BitVec.add_assoc,
          Mem.readW_byte s₀.mem (s₀.gpr .x2 + BitVec.ofNat 64 8) hi, BitVec.getLsbD_extractLsb']
        simp [hj, show 8 * i + j < 64 by omega]
      hi' := fun p hp => by
        rw [chi₅, BitVec.getLsbD_setWidth]
        simp [BitVec.getLsbD_of_ge _ _ hp] }
  -- The data is as on entry.
  have dd : ∀ r ∈ [(⟨s₀.gpr .x5, 2048⟩ : Region), ⟨s₀.gpr .x2, 16⟩],
      Region.Disjoint ⟨s₀.gpr .x3, 16 * n⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dDS
    · exact dCD.symm
  have data₅ : VG.Proof.Aes.AArch64.DataInv s₀.mem s₅.mem (s₀.gpr .x3) n 0 (VG.Proof.Aes.AArch64.keyStream R w icb) :=
    VG.Proof.Aes.AArch64.dataInv_frame fK (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact dDS.sub_right (VG.Proof.Aes.AArch64.scr_sub _ (by omega))) n16
      (VG.Proof.Aes.AArch64.dataInv_frame f₀₃ dd n16 fun i hi => by simp)
  refine WP.seq (WP.mono (Q := VG.Proof.Aes.AArch64.GDone s₀.mem s₅ (s₀.gpr .x5) (s₀.gpr .x3) n R w icb) ?_
    fun s₆ gd => ?_)
  · refine WP.ite (s₀.gpr .x4 == 0) (by simp [AArch64.eval, State.read, x4₅]) (fun h0 => ?_)
      (fun h0 => ?_)
    · have hn0 : n = 0 := by simp only [beq_iff_eq] at h0; simp [n, h0]
      exact WP.block_nil ⟨hb₅, rfl, rfl, Frame.refl _ _, fun i hi => by omega⟩
    · have hn0 : n ≠ 0 := by
        simp only [beq_eq_false_iff_ne, ne_eq] at h0
        intro h; apply h0; exact BitVec.eq_of_toNat_eq (by simpa [n] using h)
      refine VG.Proof.Aes.AArch64.groups_ok hs ⟨by omega, ?_, ?_, hb₅, hK0, rfl, rfl, Frame.refl _ _, ?_, data₅⟩
      · rw [x3₅]; simp
      · rw [x4₅]; simp [n]
      · rw [num₅, VG.Proof.Aes.AArch64.icb_lo]; simp [icb]
  -- The epilogue.
  have sv : VG.Proof.Aes.AArch64.Saved s₀ (s₀.gpr .x5) s₆.mem := by
    refine VG.Proof.Aes.AArch64.saved_frame (VG.Proof.Aes.AArch64.saved_frame (VG.Proof.Aes.AArch64.saved_frame sv₁ fS ?_) fK ?_) gd.frame ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact (dCS.sub_right (VG.Proof.Aes.AArch64.scr_sub _ (by omega))).symm
    · exact kd (by omega) (by omega)
    · intro r hr
      simp only [VG.Proof.Aes.AArch64.gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (VG.Proof.Aes.AArch64.scr_disj _ (by omega) (by omega)).symm
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact (dDS.sub_right (VG.Proof.Aes.AArch64.scr_sub _ (by omega))).symm
  refine WP.mono (VG.Proof.Aes.AArch64.restore_ok (by rw [gd.wr, wr₅, d₄.wr, wr₃, wr₂, wr₁]; exact hwS) gd.base (by decide) sv)
    fun s₇ ⟨rg₇, fR⟩ => ?_
  have fsub : ∀ {x lx}, x + lx ≤ 2048 → Region.Sub ⟨s₀.gpr .x5 + BitVec.ofNat 64 x, lx⟩ ⟨s₀.gpr .x5, 2048⟩ :=
    fun h => VG.Proof.Aes.AArch64.scr_sub _ h
  refine ⟨rg₇, ?_, ?_⟩
  · exact VG.Proof.Aes.AArch64.ctr32_of_dataInv (VG.Proof.Aes.AArch64.dataInv_frame fR (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dDS.sub_right (Region.sub_prefix (by omega))) n16 gd.data)
  · refine VG.Proof.Aes.AArch64.ctr_after fun k hk => ?_
    have hC : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
        (∀ r ∈ rs, Region.Disjoint ⟨s₀.gpr .x2, 16⟩ r) →
        m' (s₀.gpr .x2 + BitVec.ofNat 64 k) = m (s₀.gpr .x2 + BitVec.ofNat 64 k) :=
      fun hf hd => hf.bytes hd (by simp) hk
    rw [hC fR (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dCS.sub_right (Region.sub_prefix (by omega))),
      hC gd.frame (fun r hr => by
        simp only [VG.Proof.Aes.AArch64.gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dCS.sub_right (Region.sub_prefix (by omega))
        · exact dCS.sub_right (fsub (by omega))
        · exact dCD),
      hC fK (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact dCS.sub_right (fsub (by omega))),
      m₃, m₂, VG.Proof.Aes.AArch64.setup_ctr dCS hk, g₁,
      f₁.readW (Region.contains_self _ _) (cd (by omega)) (by decide)]
    split
    · exact hC f₁ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dCS.sub_right (Region.sub_prefix (by omega))
    · simp

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | .x5 => 0x4000
    | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 2048⟩]

theorem ctr32_correct (s : State) (hs : Proof.Aes.ctr32AArch64.pre s) :
    ∃ t s', Exec isa Impl.Aes.AArch64.ctr32 s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.ctr32AArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ :=
    WP.gprs (rs := [.x30]) (VG.Proof.Aes.AArch64.correct hs) (by decide +kernel) (by decide +kernel)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega)
  · exact h₁ 1 (by omega)
  · exact h₁ 2 (by omega)
  · exact h₁ 3 (by omega)
  · exact h₁ 4 (by omega)
  · exact h₁ 5 (by omega)
  · exact h₁ 6 (by omega)
  · exact h₁ 7 (by omega)
  · exact h₁ 8 (by omega)
  · exact h₁ 9 (by omega)
  · exact h₃ _ (by simp)

theorem ctr32_ct : ConstantTime isa Proof.Aes.ctr32AArch64.pre Proof.Aes.ctr32AArch64.pub
    Impl.Aes.AArch64.ctr32 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ctr32_verified :
    Verified AArch64.target Impl.Aes.AArch64.ctr32 (Spec.Gcm.ctr32Contract AArch64.abi) :=
  Verified.of_correct VG.Proof.Aes.AArch64.ctr32_correct VG.Proof.Aes.AArch64.ctr32_ct (by
    sig_implies [Spec.Gcm.ctr32Contract, Spec.Gcm.ctr32Sig, Proof.Aes.ctr32AArch64, AArch64.abi,
      AArch64.argRegs] [Proof.Aes.AArch64.satState] using Proof.Aes.AArch64.satState)

end VG.Proof.Aes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.AArch64.Decrypt`. -/
section

/-!
# Decrypting four blocks, bitsliced, on AArch64

The inverse layers (`Impl/Aes/AArch64/Inv.lean`) are checked by evaluation
as the cipher's are (`Encrypt.lean`): the inverse S-box on the truth
tables of the 256 inputs against the specification's (`invSboxT`), the
linear layers over the lane domain. `decrypt4_ok` composes them: from
four blocks in the registers (`InRel`), with the bitsliced round keys in
the scratch buffer (`EncPre`), `decrypt4` leaves the four plaintexts,
having written only the first 384 bytes of the scratch buffer. The round
loop's invariant is the specification's `foldl` over the rounds done, with
`kp` stepping down from the last round key.
-/

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes
open VG.Spec.Aes (invSbox roundKey invSubBytes invShiftRows invMixColumns addRoundKey invCipher)

/-! ## The inverse S-box -/

def invSboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (q j) == some ((invSboxT VG.Proof.Aes.AArch64.inTs).getD j 0)

theorem invSbox_check :
    VG.AArch64.Straight.check (table 64 256) VG.Proof.Aes.AArch64.sboxCfg (fun _ => none) invSboxCode VG.Proof.Aes.AArch64.sboxEnv VG.Proof.Aes.AArch64.invSboxPost = true := by
  decide +kernel

/-- The inverse S-box, at every bit position of the words in `q 0 … q 7`. -/
theorem invSbox_ok {s : State} (hok : Ok VG.Proof.Aes.AArch64.sboxCfg s) :
    ∃ s', runBlock isa invSboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 64,
        (s'.gpr (q j)).getLsbD p = (invSbox (bsByte (fun k => s.gpr (q k)) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ VG.Proof.Aes.AArch64.layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.AArch64.sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.Aes.AArch64.invSbox_check
  have hout : ∀ j < 8, e'.reg (q j) = some ((invSboxT VG.Proof.Aes.AArch64.inTs).getD j 0) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  have key : ∀ p < 64, ∃ s', runBlock isa invSboxCode s = some s' ∧
      Post (TableRel p (bsByte (fun k => s.gpr (q k)) p).toNat) VG.Proof.Aes.AArch64.sboxCfg (fun _ => none) e' s s'
        (fun r => (invSboxCode.all fun i => dstOf i != some r) = false) := by
    intro p hp
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_, (fun _ _ _ h => by cases h),
      (fun _ _ _ h => by cases h), (fun _ _ h => by cases h)⟩ he
    simp only [VG.Proof.Aes.AArch64.sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨hqk, hkr⟩ := List.find?_some hk, List.mem_of_find?_eq_some hk
    have hk8 := List.mem_range.mp hkr
    simp only [beq_iff_eq] at hqk
    subst hqk
    simp only [TableRel, VG.Proof.Aes.AArch64.inT, testBit_tableOf, hc, decide_true, Bool.true_and,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8]
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, p₀.sp, fun r hr => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    have := p₁.rel.reg (q j) _ (hout j hj)
    simp only [TableRel] at this
    rw [← this, ← getLsbD_row _ _ hj, row_invSboxT _ hc, VG.Proof.Aes.AArch64.row_inTs hc]
    simp
  · simp [VG.Proof.Aes.AArch64.writes_rest (is := invSboxCode) (by decide +kernel) r hr]

/-! ## The linear layers -/

theorem invShiftRows_check :
    VG.AArch64.Straight.check (lanes 64 9) VG.Proof.Aes.AArch64.linCfg (linExt 0) Impl.Aes.AArch64.invShiftRows (linEnv VG.Proof.Aes.AArch64.qIns)
      (linPost 9 (VG.Proof.Aes.AArch64.qOuts invSrG)) = true := by
  decide +kernel

theorem invMixColumns_check :
    VG.AArch64.Straight.check (lanes 64 9) VG.Proof.Aes.AArch64.linCfg (linExt 0) Impl.Aes.AArch64.invMixColumns (linEnv VG.Proof.Aes.AArch64.qIns)
      (linPost 9 (VG.Proof.Aes.AArch64.qOuts invMcG)) = true := by
  decide +kernel

theorem invShiftRows_ok {s : State} (hok : Ok VG.Proof.Aes.AArch64.linCfg s) :
    ∃ s', runBlock isa Impl.Aes.AArch64.invShiftRows s = some s' ∧
      (∀ j < 8, ∀ p < 64, (VG.Proof.Aes.AArch64.Q s' j).getLsbD p = (VG.Proof.Aes.AArch64.Q s j).getLsbD (invSrSrc p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ VG.Proof.Aes.AArch64.layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.AArch64.linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := VG.Proof.Aes.AArch64.q_linear VG.Proof.Aes.AArch64.invShiftRows_check (by decide) (by decide +kernel) hok
    (VG.Proof.Aes.AArch64.Q s) (fun _ _ => rfl) (fun j hj => by simp [VG.Proof.Aes.AArch64.linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, invSrG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by simp only [invSrSrc]; omega)]

theorem invMixColumns_ok {s : State} (hok : Ok VG.Proof.Aes.AArch64.linCfg s) :
    ∃ s', runBlock isa Impl.Aes.AArch64.invMixColumns s = some s' ∧
      (∀ j < 8, ∀ p < 64, (VG.Proof.Aes.AArch64.Q s' j).getLsbD p = termsXor (VG.Proof.Aes.AArch64.Q s) (invMcTerms j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ VG.Proof.Aes.AArch64.layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.AArch64.linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := VG.Proof.Aes.AArch64.q_linear VG.Proof.Aes.AArch64.invMixColumns_check (by decide) (by decide +kernel) hok
    (VG.Proof.Aes.AArch64.Q s) (fun _ _ => rfl) (fun j hj => by simp [VG.Proof.Aes.AArch64.linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, invMcG, xorBits_map]
  intro wt hwt
  obtain ⟨wk, -, rfl⟩ := List.mem_map.mp hwt
  exact Nat.mod_lt _ (by decide)

/-! ## The rounds -/

theorem kp_back (K : Addr) {m : Nat} (hm : 0 < m) :
    K + BitVec.ofNat 64 (64 * m) - BitVec.ofNat 64 64 = K + BitVec.ofNat 64 (64 * (m - 1)) := by
  rw [Offset.add_ofNat_sub K (by omega), show 64 * m - 64 = 64 * (m - 1) by omega]

/-- `sub kp, kp, #64`. -/
theorem subKp_wp {s₀ s : State} {P : State → Prop} (hc : VG.Proof.Aes.AArch64.Ctx s₀ s)
    (h : ∀ s', VG.Proof.Aes.AArch64.Ctx s₀ s' → s'.gpr kp = s.gpr kp - BitVec.ofNat 64 64 →
      (∀ i, VG.Proof.Aes.AArch64.Q s' i = VG.Proof.Aes.AArch64.Q s i) → P s') :
    WP isa (.block [.subImm .x kp kp 64]) s P := by
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_subImm_x (by decide), runStep_some,
    runBlock_nil], h _ ?_ ?_ ?_⟩
  · exact hc.step rfl rfl rfl (fun r _ hr => by simp [State.write, hr]) (Frame.refl _ _)
  · simp [State.write, State.read]
  · intro i; simp [VG.Proof.Aes.AArch64.Q, State.write, VG.Proof.Aes.AArch64.q_ne_kp i]

/-- `sub t0, kp, x0; sub t0, t0, #64`. -/
theorem cmpFirst_wp {s₀ s : State} {P : State → Prop} (hc : VG.Proof.Aes.AArch64.Ctx s₀ s)
    (h : ∀ s', VG.Proof.Aes.AArch64.Ctx s₀ s' → s'.gpr kp = s.gpr kp → (∀ i, VG.Proof.Aes.AArch64.Q s' i = VG.Proof.Aes.AArch64.Q s i) →
      s'.gpr t0 = s.gpr kp - s.gpr .x0 - BitVec.ofNat 64 64 → P s') :
    WP isa (.block [.sub .x t0 kp .x0, .subImm .x t0 t0 64]) s P := by
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, show exec (.sub .x t0 kp .x0) s =
    some (s.write .x t0 (s.read .x kp - s.read .x .x0)) from rfl, runStep_some, runBlock_cons,
    exec_subImm_x (by decide), runStep_some, runBlock_nil], h _ ?_ ?_ ?_ ?_⟩
  · exact hc.step rfl rfl rfl (fun r hr _ => by
      have : r ≠ t0 := fun h => hr (h ▸ by decide)
      simp [State.write, this]) (Frame.refl _ _)
  · simp [State.write, t0, kp]
  · intro i; simp [VG.Proof.Aes.AArch64.Q, State.write, VG.Proof.Aes.AArch64.q_ne_t0 i]
  · simp [State.write, State.read]

/-- `add kp, x5, #lastKey`. -/
theorem kpLast_wp {s₀ s : State} {P : State → Prop} (hc : VG.Proof.Aes.AArch64.Ctx s₀ s)
    (h : ∀ s', VG.Proof.Aes.AArch64.Ctx s₀ s' → s'.gpr kp = s.gpr sb + BitVec.ofNat 64 lastKey →
      (∀ i, VG.Proof.Aes.AArch64.Q s' i = VG.Proof.Aes.AArch64.Q s i) → P s') :
    WP isa (.block [.addImm .x kp sb lastKey]) s P := by
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_addImm_x (by decide), runStep_some,
    runBlock_nil], h _ ?_ ?_ ?_⟩
  · exact hc.step rfl rfl rfl (fun r _ hr => by simp [State.write, hr]) (Frame.refl _ _)
  · simp [State.write, State.read]
  · intro i; simp [VG.Proof.Aes.AArch64.Q, State.write, VG.Proof.Aes.AArch64.q_ne_kp i]

theorem t0_first (K : Addr) {m : Nat} (hm : m < 15) :
    (K + BitVec.ofNat 64 (64 * m) - K - BitVec.ofNat 64 64 != 0) = !decide (m = 1) := by
  rw [Offset.add_sub_cancel_left, bne, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  congr 1
  exact decide_eq_decide.mpr (by omega)

/-- A middle round of the inverse cipher. -/
theorem invRound_ok {s₀ s : State} {R m : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : VG.Proof.Aes.AArch64.EncPre s₀ R w) (hc : VG.Proof.Aes.AArch64.Ctx s₀ s) (hk : s.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * (R - m)))
    (hm : m + 1 < R) (hbs : BsRel (VG.Proof.Aes.AArch64.Q s) T) :
    WP isa (.block invRoundBody) s fun s' => VG.Proof.Aes.AArch64.Ctx s₀ s' ∧
      s'.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * (R - (m + 1))) ∧
      BsRel (VG.Proof.Aes.AArch64.Q s') (fun b => irnd R w m (T b)) ∧
      AArch64.eval (.nonzero .x t0) s' = some (!decide (m + 2 = R)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  simp only [invRoundBody]
  repeat rw [WP.block_append_iff (M := isa)]
  refine VG.Proof.Aes.AArch64.subKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
  rw [hk, VG.Proof.Aes.AArch64.kp_back _ (by omega), show R - m - 1 = R - (m + 1) by omega] at hk₁
  have hbs₁ : BsRel (VG.Proof.Aes.AArch64.Q s₁) T := by
    have : VG.Proof.Aes.AArch64.Q s₁ = VG.Proof.Aes.AArch64.Q s := funext hq₁
    rw [this]; exact hbs
  refine VG.Proof.Aes.AArch64.layer_wp (VG.Proof.Aes.AArch64.invShiftRows_ok (hc₁.linOk hp.scr)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
  have hbs₂ := bs_invShiftRows h₂ hbs₁
  refine VG.Proof.Aes.AArch64.layer_wp (VG.Proof.Aes.AArch64.invSbox_ok (hc₂.linOk hp.scr)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
  have hbs₃ := bs_invSubBytes h₃ hbs₂
  refine VG.Proof.Aes.AArch64.ark_step hp hc₃ (j := R - (m + 1)) (by rw [hk₃, hk₂, hk₁]) (by omega) hbs₃
    fun s₄ hc₄ hk₄ hbs₄ => ?_
  refine VG.Proof.Aes.AArch64.layer_wp (VG.Proof.Aes.AArch64.invMixColumns_ok (hc₄.linOk hp.scr)) hc₄ fun s₅ hc₅ h₅ hk₅ => ?_
  have hbs₅ := bs_invMixColumns h₅ hbs₄
  have hk₅' : s₅.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * (R - (m + 1))) := by
    rw [hk₅, hk₄, hk₃, hk₂, hk₁]
  refine VG.Proof.Aes.AArch64.cmpFirst_wp hc₅ fun s₆ hc₆ hk₆ hq₆ ht₆ => ⟨hc₆, ?_, ?_, ?_⟩
  · rw [hk₆, hk₅']
  · have : VG.Proof.Aes.AArch64.Q s₆ = VG.Proof.Aes.AArch64.Q s₅ := funext hq₆
    rw [this]
    intro b hb i hi
    rw [hbs₅ b hb i hi]
    simp only [irnd, show R - 1 - m = R - (m + 1) by omega]
  · simp only [AArch64.eval, State.read, Size.bits, BitVec.setWidth_eq, ht₆]
    rw [hk₅', hc₅.keep _ x0_not.1 x0_not.2, VG.Proof.Aes.AArch64.t0_first _ (by omega)]
    exact congrArg (some ∘ not) (decide_eq_decide.mpr (by omega))

/-- Four blocks, from `InRel` to `InRel` of their decryptions. -/
theorem decrypt4_ok {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}
    (hp : VG.Proof.Aes.AArch64.EncPre s₀ R w) (hin : InRel (VG.Proof.Aes.AArch64.Q s₀) S) :
    WP isa decrypt4 s₀ fun s => VG.Proof.Aes.AArch64.Ctx s₀ s ∧ InRel (VG.Proof.Aes.AArch64.Q s) (fun b => invCipher R w (S b)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hR1 : 2 ≤ R := by rcases hp.rounds with h | h | h <;> omega
  let A : Nat → Spec.Aes.State := fun b => addRoundKey (S b) (roundKey w R)
  let Inv : Nat → State → Prop := fun n s => ∃ m, n = R - 1 - m ∧ m + 1 < R ∧ VG.Proof.Aes.AArch64.Ctx s₀ s ∧
    s.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * (R - m)) ∧
    BsRel (VG.Proof.Aes.AArch64.Q s) (fun b => invMid R w m (A b))
  let Mid : State → Prop := fun s => VG.Proof.Aes.AArch64.Ctx s₀ s ∧
    s.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * 1) ∧
    BsRel (VG.Proof.Aes.AArch64.Q s) (fun b => invMid R w (R - 1) (A b))
  refine WP.seq (WP.mono (Q := Inv (R - 1)) ?_ fun s h => WP.seq (WP.mono (Q := Mid) ?_ fun s h => ?_))
  · -- toBs, the last round key.
    repeat rw [WP.block_append_iff (M := isa)]
    refine VG.Proof.Aes.AArch64.layer_wp (VG.Proof.Aes.AArch64.toBs_ok ((Ctx.refl s₀).linOk hp.scr)) (Ctx.refl s₀) fun s₁ hc₁ h₁ _ => ?_
    have hbs₁ := bs_of_in h₁ hin
    refine VG.Proof.Aes.AArch64.kpLast_wp hc₁ fun s₂ hc₂ hk₂ hq₂ => ?_
    have hbs₂ : BsRel (VG.Proof.Aes.AArch64.Q s₂) S := by
      have : VG.Proof.Aes.AArch64.Q s₂ = VG.Proof.Aes.AArch64.Q s₁ := funext hq₂
      rw [this]; exact hbs₁
    have hk₂' : s₂.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * R) := by
      rw [hk₂, hc₁.base, hp.k0, BitVec.add_assoc, ← BitVec.ofNat_add, lastKey]
      congr 2; omega
    exact VG.Proof.Aes.AArch64.ark_step hp hc₂ hk₂' (Nat.le_refl R) hbs₂ fun s₃ hc₃ hk₃ hbs₃ =>
      ⟨0, by omega, by omega, hc₃, by rw [hk₃, hk₂']; simp, hbs₃⟩
  · -- The middle rounds.
    refine WP.loop (M := isa) Inv (fun n s hs => ?_) (R - 1) s h
    obtain ⟨m, rfl, hm, hc, hk, hbs⟩ := hs
    refine WP.mono (VG.Proof.Aes.AArch64.invRound_ok hp hc hk hm hbs) fun s' ⟨hc', hk', hbs', hz⟩ => ?_
    by_cases hlast : m + 2 = R
    · refine .inl ⟨hz.trans (by simp [hlast]), hc', ?_, ?_⟩
      · rw [hk']; congr 3; omega
      · rw [show R - 1 = m + 1 by omega]
        intro b hb i hi
        rw [hbs' b hb i hi]; simp only [invMid_succ]
    · refine .inr ⟨hz.trans (by simp [hlast]), R - 1 - (m + 1), by omega, m + 1, rfl, by omega,
        hc', hk', fun b hb i hi => by rw [hbs' b hb i hi]; simp only [invMid_succ]⟩
  · -- The last round, and back to blocks.
    obtain ⟨hc, hk, hbs⟩ := h
    rw [WP.block_append_iff (M := isa)]
    simp only [invLastRound]
    repeat rw [WP.block_append_iff (M := isa)]
    refine VG.Proof.Aes.AArch64.subKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
    rw [hk, VG.Proof.Aes.AArch64.kp_back _ (by omega)] at hk₁
    have hbs₁ : BsRel (VG.Proof.Aes.AArch64.Q s₁) (fun b => invMid R w (R - 1) (A b)) := by
      have : VG.Proof.Aes.AArch64.Q s₁ = VG.Proof.Aes.AArch64.Q s := funext hq₁
      rw [this]; exact hbs
    refine VG.Proof.Aes.AArch64.layer_wp (VG.Proof.Aes.AArch64.invShiftRows_ok (hc₁.linOk hp.scr)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
    have hbs₂ := bs_invShiftRows h₂ hbs₁
    refine VG.Proof.Aes.AArch64.layer_wp (VG.Proof.Aes.AArch64.invSbox_ok (hc₂.linOk hp.scr)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
    have hbs₃ := bs_invSubBytes h₃ hbs₂
    refine VG.Proof.Aes.AArch64.ark_step hp hc₃ (j := 0) (by rw [hk₃, hk₂, hk₁]) (Nat.zero_le R) hbs₃ fun s₄ hc₄ _ hbs₄ => ?_
    refine VG.Proof.Aes.AArch64.layer_wp (VG.Proof.Aes.AArch64.fromBs_ok (hc₄.linOk hp.scr)) hc₄ fun s₅ hc₅ h₅ _ => ⟨hc₅, ?_⟩
    have := in_of_bs h₅ hbs₄
    intro b hb i hi j hj
    rw [this b hb i hi j hj]; simp only [invCipher_eq]; rfl

end VG.Proof.Aes.AArch64

end
