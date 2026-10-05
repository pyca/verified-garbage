import VerifiedGarbage.Proof.Aes.InvBitsliced
import VerifiedGarbage.Proof.Framework.Arm.Linear
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Impl.Aes.Arm.Ctr32
import VerifiedGarbage.Impl.Aes.Arm.Linear
import VerifiedGarbage.Impl.Aes.Arm.Sbox
import VerifiedGarbage.Proof.Aes.InvSboxSpec
import VerifiedGarbage.Proof.Framework.Bitslice.Sym
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.Gcm.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.Arm.Bitsliced`. -/
section

/-!
# Bitsliced AES in 32-bit words: the layout and the round transformations

As `Proof/Aes/Bitsliced.lean`, for two AES states in eight 32-bit words,
as in BearSSL's `aes_ct` (Thomas Pornin, MIT licence): bit `j` of byte
`i = r + 4c` of block `b` is bit `pos b i = 8r + 2c + b` of word `j`.
`BsRel Q S` says the words `Q` hold the states `S`. The lemmas here turn
what each layer of the code does to the bits (as its proof states it) into
the transformation of FIPS 197 it computes on the states; the byte-level
facts about `xtimes` are shared with the 64-bit layout.

The last section gives each linear layer as atoms (as the last section of
`Proof/Aes/Bitsliced.lean` does), for the checks by evaluation
(`Framework/Arm/Linear.lean`): bit `t`
of input word `i` is atom `32 i + t`.
-/

namespace VG.Proof.Aes.Arm

open VG VG.Bitslice VG.Spec.Aes
open VG.Proof.Aes (byte_ext getD_eq mul2 mul3 xtimes_bit)

/-- The byte at bit position `p` of eight words: its bit `k` is bit `p` of word `k`. -/
def bsByte (Q : Nat → BitVec 32) (p : Nat) : Byte := ofBits 8 fun k => (Q k).getLsbD p

theorem getLsbD_bsByte (Q : Nat → BitVec 32) (p : Nat) {k : Nat} (hk : k < 8) :
    (VG.Proof.Aes.Arm.bsByte Q p).getLsbD k = (Q k).getLsbD p := by
  rw [VG.Proof.Aes.Arm.bsByte, getLsbD_ofBits]; simp [hk]

/-- Byte `r + 4c` of block `b` is at position `8r + 2c + b`. -/
def pos (b i : Nat) : Nat := 8 * (i % 4) + 2 * (i / 4) + b

theorem pos_lt {b i : Nat} (hb : b < 2) (hi : i < 16) : VG.Proof.Aes.Arm.pos b i < 32 := by
  simp only [VG.Proof.Aes.Arm.pos]; omega

/-- The words `Q` hold the two states `S`. -/
def BsRel (Q : Nat → BitVec 32) (S : Nat → State) : Prop :=
  ∀ b < 2, ∀ i < 16, VG.Proof.Aes.Arm.bsByte Q (VG.Proof.Aes.Arm.pos b i) = (S b).getD i 0

/-- The words `K` hold the round key `rk` in both blocks. -/
def KeyRel (K : Nat → BitVec 32) (rk : List Byte) : Prop :=
  ∀ b < 2, ∀ i < 16, VG.Proof.Aes.Arm.bsByte K (VG.Proof.Aes.Arm.pos b i) = rk.getD i 0

/-- The words `Q` hold the two states word by word, little-endian: bytes
`4k … 4k + 3` of block `b` in word `2k + b`. -/
def InRel (Q : Nat → BitVec 32) (S : Nat → State) : Prop :=
  ∀ b < 2, ∀ i < 16, ∀ j < 8,
    (Q (2 * (i / 4) + b)).getLsbD (8 * (i % 4) + j) = ((S b).getD i 0).getLsbD j

/-! ## The layers -/

theorem bs_subBytes {Q Q' : Nat → BitVec 32} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = (VG.Spec.Aes.sbox (VG.Proof.Aes.Arm.bsByte Q p)).getLsbD j) (hr : VG.Proof.Aes.Arm.BsRel Q S) :
    VG.Proof.Aes.Arm.BsRel Q' fun b => subBytes (S b) := by
  intro b hb i hi
  have : VG.Proof.Aes.Arm.bsByte Q' (VG.Proof.Aes.Arm.pos b i) = VG.Spec.Aes.sbox (VG.Proof.Aes.Arm.bsByte Q (VG.Proof.Aes.Arm.pos b i)) :=
    VG.Proof.Aes.byte_ext fun j hj => by rw [VG.Proof.Aes.Arm.getLsbD_bsByte _ _ hj, h j hj _ (VG.Proof.Aes.Arm.pos_lt hb hi)]
  rw [this, hr b hb i hi, getD_eq _ hi, getD_eq _ hi]
  simp only [subBytes, Vector.getElem_map]

/-- ShiftRows: position `8r + 2c + b` from `8r + 2((c + r) mod 4) + b`. -/
def srSrc (p : Nat) : Nat := 8 * (p / 8) + 2 * ((p % 8 / 2 + p / 8) % 4) + p % 2

theorem srSrc_pos : ∀ b < 2, ∀ i < 16, VG.Proof.Aes.Arm.srSrc (VG.Proof.Aes.Arm.pos b i) = VG.Proof.Aes.Arm.pos b (i % 4 + 4 * ((i / 4 + i % 4) % 4)) := by
  decide

theorem bs_shiftRows {Q Q' : Nat → BitVec 32} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = (Q j).getLsbD (VG.Proof.Aes.Arm.srSrc p)) (hr : VG.Proof.Aes.Arm.BsRel Q S) :
    VG.Proof.Aes.Arm.BsRel Q' fun b => VG.Spec.Aes.shiftRows (S b) := by
  intro b hb i hi
  have : VG.Proof.Aes.Arm.bsByte Q' (VG.Proof.Aes.Arm.pos b i) = VG.Proof.Aes.Arm.bsByte Q (VG.Proof.Aes.Arm.pos b (i % 4 + 4 * ((i / 4 + i % 4) % 4))) :=
    VG.Proof.Aes.byte_ext fun j hj => by
      rw [VG.Proof.Aes.Arm.getLsbD_bsByte _ _ hj, VG.Proof.Aes.Arm.getLsbD_bsByte _ _ hj, h j hj _ (VG.Proof.Aes.Arm.pos_lt hb hi), VG.Proof.Aes.Arm.srSrc_pos b hb i hi]
  rw [this, hr b hb _ (by omega), getD_eq _ hi]
  simp only [VG.Spec.Aes.shiftRows, Vector.getElem_ofFn]

theorem bs_addRoundKey {Q Q' K : Nat → BitVec 32} {S : Nat → State} {rk : List Byte}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = ((Q j).getLsbD p ^^ (K j).getLsbD p))
    (hr : VG.Proof.Aes.Arm.BsRel Q S) (hk : VG.Proof.Aes.Arm.KeyRel K rk) : VG.Proof.Aes.Arm.BsRel Q' fun b => VG.Spec.Aes.addRoundKey (S b) rk := by
  intro b hb i hi
  have : VG.Proof.Aes.Arm.bsByte Q' (VG.Proof.Aes.Arm.pos b i) = VG.Proof.Aes.Arm.bsByte Q (VG.Proof.Aes.Arm.pos b i) ^^^ VG.Proof.Aes.Arm.bsByte K (VG.Proof.Aes.Arm.pos b i) :=
    VG.Proof.Aes.byte_ext fun j hj => by
      rw [BitVec.getLsbD_xor, VG.Proof.Aes.Arm.getLsbD_bsByte _ _ hj, VG.Proof.Aes.Arm.getLsbD_bsByte _ _ hj, VG.Proof.Aes.Arm.getLsbD_bsByte _ _ hj,
        h j hj _ (VG.Proof.Aes.Arm.pos_lt hb hi)]
  rw [this, hr b hb i hi, hk b hb i hi, getD_eq _ hi, getD_eq _ hi]
  simp only [VG.Spec.Aes.addRoundKey, Vector.getElem_ofFn, getD_eq _ hi]

theorem pos_div : ∀ b < 2, ∀ i < 16, VG.Proof.Aes.Arm.pos b i % 8 = 2 * (i / 4) + b ∧ VG.Proof.Aes.Arm.pos b i / 8 = i % 4 := by
  decide

/-- `ortho` from the words of the blocks to the bitsliced state. -/
theorem bs_of_in {Q Q' : Nat → BitVec 32} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = (Q (p % 8)).getLsbD (8 * (p / 8) + j))
    (hr : VG.Proof.Aes.Arm.InRel Q S) : VG.Proof.Aes.Arm.BsRel Q' S := by
  intro b hb i hi
  refine VG.Proof.Aes.byte_ext fun j hj => ?_
  obtain ⟨h1, h2⟩ := VG.Proof.Aes.Arm.pos_div b hb i hi
  rw [VG.Proof.Aes.Arm.getLsbD_bsByte _ _ hj, h j hj _ (VG.Proof.Aes.Arm.pos_lt hb hi), h1, h2, hr b hb i hi j hj]

/-- `ortho` from the bitsliced state back to the words of the blocks. -/
theorem in_of_bs {Q Q' : Nat → BitVec 32} {S : Nat → State}
    (h : ∀ k < 8, ∀ t < 32, (Q' k).getLsbD t = (Q (t % 8)).getLsbD (8 * (t / 8) + k))
    (hr : VG.Proof.Aes.Arm.BsRel Q S) : VG.Proof.Aes.Arm.InRel Q' S := by
  intro b hb i hi j hj
  rw [h _ (by omega) _ (by omega), ← VG.Proof.Aes.Arm.getLsbD_bsByte _ _ (by omega)]
  rw [show (8 * (i % 4) + j) % 8 = j by omega,
    show 8 * ((8 * (i % 4) + j) / 8) + (2 * (i / 4) + b) = VG.Proof.Aes.Arm.pos b i by simp only [VG.Proof.Aes.Arm.pos]; omega,
    hr b hb i hi]

/-! ## MixColumns -/

/-- The XOR of the bits `(w, t)` (bit `t` of word `w`). -/
def termsXor (Q : Nat → BitVec 32) (l : List (Nat × Nat)) : Bool :=
  l.foldr (fun wt b => (Q wt.1).getLsbD wt.2 ^^ b) false

/-- Position `p` moved `k` rows down (within its column). -/
def down (p k : Nat) : Nat := (p + 8 * k) % 32

/-- The bits `(w, k)` of `Proof.Aes.mcWords`: bit `w` of the byte `k` rows down. -/
def mcTerms (j p : Nat) : List (Nat × Nat) := (Proof.Aes.mcWords j).map fun wk => (wk.1, VG.Proof.Aes.Arm.down p wk.2)

theorem down_pos : ∀ b < 2, ∀ i < 16, ∀ k < 4,
    VG.Proof.Aes.Arm.down (VG.Proof.Aes.Arm.pos b i) k = VG.Proof.Aes.Arm.pos b ((i % 4 + k) % 4 + 4 * (i / 4)) := by
  decide

theorem termsXor_mc (Q : Nat → BitVec 32) (j p : Nat) : VG.Proof.Aes.Arm.termsXor Q (VG.Proof.Aes.Arm.mcTerms j p) =
    ((if j = 0 then false else ((Q (j - 1)).getLsbD (VG.Proof.Aes.Arm.down p 0) ^^ (Q (j - 1)).getLsbD (VG.Proof.Aes.Arm.down p 1))) ^^
     (if j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 then (Q 7).getLsbD (VG.Proof.Aes.Arm.down p 0) ^^ (Q 7).getLsbD (VG.Proof.Aes.Arm.down p 1)
      else false) ^^
     ((Q j).getLsbD (VG.Proof.Aes.Arm.down p 1) ^^ (Q j).getLsbD (VG.Proof.Aes.Arm.down p 2) ^^ (Q j).getLsbD (VG.Proof.Aes.Arm.down p 3))) := by
  simp only [VG.Proof.Aes.Arm.mcTerms, Proof.Aes.mcWords]
  split_ifs <;> simp [VG.Proof.Aes.Arm.termsXor]

theorem bs_mixColumns {Q Q' : Nat → BitVec 32} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = VG.Proof.Aes.Arm.termsXor Q (VG.Proof.Aes.Arm.mcTerms j p)) (hr : VG.Proof.Aes.Arm.BsRel Q S) :
    VG.Proof.Aes.Arm.BsRel Q' fun b => VG.Spec.Aes.mixColumns (S b) := by
  intro b hb i hi
  refine VG.Proof.Aes.byte_ext fun j hj => ?_
  have hbit : ∀ k < 4, ∀ w < 8, (Q w).getLsbD (VG.Proof.Aes.Arm.down (VG.Proof.Aes.Arm.pos b i) k) =
      ((S b).getD ((i % 4 + k) % 4 + 4 * (i / 4)) 0).getLsbD w := fun k hk w hw => by
    rw [VG.Proof.Aes.Arm.down_pos b hb i hi k hk, ← hr b hb _ (by omega), VG.Proof.Aes.Arm.getLsbD_bsByte _ _ hw]
  rw [VG.Proof.Aes.Arm.getLsbD_bsByte _ _ hj, h j hj _ (VG.Proof.Aes.Arm.pos_lt hb hi), getD_eq _ hi, VG.Proof.Aes.Arm.termsXor_mc]
  simp only [VG.Spec.Aes.mixColumns, Vector.getElem_ofFn, mul2, mul3, BitVec.getLsbD_xor, xtimes_bit _ hj]
  simp only [hbit 1 (by decide) _ hj, hbit 2 (by decide) _ hj,
    hbit 3 (by decide) _ hj, hbit 0 (by decide) 7 (by decide), hbit 1 (by decide) 7 (by decide),
    hbit 0 (by decide) (j - 1) (by omega), hbit 1 (by decide) (j - 1) (by omega)]
  generalize ((S b).getD ((i % 4 + 0) % 4 + 4 * (i / 4)) 0) = a0
  generalize ((S b).getD ((i % 4 + 1) % 4 + 4 * (i / 4)) 0) = a1
  generalize ((S b).getD ((i % 4 + 2) % 4 + 4 * (i / 4)) 0) = a2
  generalize ((S b).getD ((i % 4 + 3) % 4 + 4 * (i / 4)) 0) = a3
  by_cases h1 : (j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4) <;>
    simp only [h1, ite_true, ite_false, decide_true, decide_false, Bool.true_and,
      Bool.false_and, Bool.xor_false] <;>
    by_cases h0 : j = 0 <;>
    simp only [h0, ite_true, ite_false, Bool.false_xor, Bool.xor_assoc,
      Bool.xor_comm, Bool.xor_left_comm]

/-! ## The linear layers, as atoms -/

/-- `ortho` (both ways): bit `j` at position `p` from bit `8 ⌊p / 8⌋ + j` of
word `p mod 8`. -/
def orthoG (j p : Nat) : List Nat := [32 * (p % 8) + (8 * (p / 8) + j)]

def srG (j p : Nat) : List Nat := [32 * j + VG.Proof.Aes.Arm.srSrc p]

/-- MixColumns: the bits `mcTerms`, as atoms. -/
def mcG (j p : Nat) : List Nat := (VG.Proof.Aes.Arm.mcTerms j p).map fun wt => 32 * wt.1 + wt.2

/-- AddRoundKey: the round key is input words `8 … 15`. -/
def arkG (j p : Nat) : List Nat := [32 * j + p, 32 * (8 + j) + p]

open VG.Arm.Straight in
theorem xorBits_map (W : Nat → BitVec 32) (l : List (Nat × Nat)) (hl : ∀ wt ∈ l, wt.2 < 32) :
    Arm.Straight.xorBits W (l.map fun wt => 32 * wt.1 + wt.2) = VG.Proof.Aes.Arm.termsXor W l := by
  induction l with
  | nil => rfl
  | cons wt l ih =>
    simp only [List.map_cons, Arm.Straight.xorBits_cons, VG.Proof.Aes.Arm.termsXor, List.foldr_cons] at ih ⊢
    rw [Arm.Straight.bitOf_word _ _ _ (hl wt (by simp)), ih fun v hv => hl v (by simp [hv])]

end VG.Proof.Aes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.Arm.Sbox`. -/
section

/-!
# The bitsliced S-box on ARMv7

As on AArch64 (`Proof/Aes/AArch64/Encrypt.lean`): `sboxCode` only combines
words bitwise (and builds all ones with `mov` and `sub`, stored in a slot),
so it computes the same Boolean function at each of the 32 bit positions:
the kernel evaluates it once on truth tables of the 256 inputs
(`Bitslice.table`) and compares the result with the specification's S-box
on the same tables (`sboxT`, proved right in `Proof/Aes/SboxSpec.lean`).
`sbox_ok` then gives, at every bit position `p`, the S-box of the byte
formed by bit `p` of the eight words.
-/

namespace VG.Proof.Aes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Proof.Aes (sboxT row row_ext getLsbD_row row_sboxT)
open VG.Spec.Aes (sbox)

/-- The S-box's memory: its slots, at `r8`. -/
def sboxCfg : Cfg := { base := sb, slots := 32, ext := sb, exts := 0 }

/-- The truth table of bit `k` of the input. -/
def inT (k : Nat) : Nat := tableOf (fun c => c.testBit k) 256

def inTs : List Nat := (List.range 8).map VG.Proof.Aes.Arm.inT

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => VG.Impl.Aes.Arm.q k == r)).map VG.Proof.Aes.Arm.inT, slot := fun _ => none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (VG.Impl.Aes.Arm.q j) == some ((sboxT VG.Proof.Aes.Arm.inTs).getD j 0)

theorem sbox_check :
    VG.Arm.Straight.check (table 32 256) VG.Proof.Aes.Arm.sboxCfg (fun _ => none) sboxCode VG.Proof.Aes.Arm.sboxEnv VG.Proof.Aes.Arm.sboxPost = true := by
  decide +kernel

theorem row_inTs {c : Nat} (hc : c < 256) : row VG.Proof.Aes.Arm.inTs c = BitVec.ofNat 8 c := by
  refine row_ext fun j hj => ?_
  simp only [VG.Proof.Aes.Arm.inTs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, VG.Proof.Aes.Arm.inT, testBit_tableOf, hc, decide_true, Bool.true_and,
    BitVec.getLsbD_ofNat, hj]

/-- The registers the layers of AES may write: the state and the
temporaries (of the S-box and the linear layers). -/
def layerWrites : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r10, .r11, .r12, .lr]

/-- The registers outside `layerWrites`: the scratch buffer's base and the
round key pointer. -/
def layerKeep : List Reg := [.r8, .r9]

theorem not_layerWrites (r : Reg) (hr : r ∉ VG.Proof.Aes.Arm.layerWrites) : r ∈ VG.Proof.Aes.Arm.layerKeep := by
  revert hr; cases r <;> decide

/-- A block that writes none of `layerKeep` writes only `layerWrites`. -/
theorem writes_rest {is : List Instr}
    (h : layerKeep.all (fun r => is.all fun i => dstOf i != some r) = true)
    (r : Reg) (hr : r ∉ VG.Proof.Aes.Arm.layerWrites) : (is.all fun i => dstOf i != some r) = true :=
  List.all_eq_true.mp h r (VG.Proof.Aes.Arm.not_layerWrites r hr)

/-- The S-box, at every bit position of the words in `q 0 … q 7`. -/
theorem sbox_ok {s : State} (hok : Ok VG.Proof.Aes.Arm.sboxCfg s) :
    ∃ s', runBlock isa sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 32,
        (s'.gpr (VG.Impl.Aes.Arm.q j)).getLsbD p = (sbox (VG.Proof.Aes.Arm.bsByte (fun k => s.gpr (VG.Impl.Aes.Arm.q k)) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ VG.Proof.Aes.Arm.layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.Arm.sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.Aes.Arm.sbox_check
  have hout : ∀ j < 8, e'.reg (VG.Impl.Aes.Arm.q j) = some ((sboxT VG.Proof.Aes.Arm.inTs).getD j 0) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  -- The run at bit position `p`, on the input formed by the bits `p`.
  have key : ∀ p < 32, ∃ s', runBlock isa sboxCode s = some s' ∧
      VG.Arm.Straight.Post (TableRel p (VG.Proof.Aes.Arm.bsByte (fun k => s.gpr (VG.Impl.Aes.Arm.q k)) p).toNat) VG.Proof.Aes.Arm.sboxCfg (fun _ => none) e' s s'
        (fun r => (sboxCode.all fun i => dstOf i != some r) = false) := by
    intro p hp
    have hc := (VG.Proof.Aes.Arm.bsByte (fun k => s.gpr (VG.Impl.Aes.Arm.q k)) p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_, (fun _ _ _ h => by cases h),
      (fun _ _ _ h => by cases h), (fun _ _ h => by cases h)⟩ he
    simp only [VG.Proof.Aes.Arm.sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨hqk, hkr⟩ := List.find?_some hk, List.mem_of_find?_eq_some hk
    have hk8 := List.mem_range.mp hkr
    simp only [beq_iff_eq] at hqk
    subst hqk
    simp only [TableRel, VG.Proof.Aes.Arm.inT, testBit_tableOf, hc, decide_true, Bool.true_and,
      BitVec.testBit_toNat, VG.Proof.Aes.Arm.getLsbD_bsByte _ _ hk8]
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, p₀.sp, fun r hr => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have hc := (VG.Proof.Aes.Arm.bsByte (fun k => s.gpr (VG.Impl.Aes.Arm.q k)) p).isLt
    have := p₁.rel.reg (VG.Impl.Aes.Arm.q j) _ (hout j hj)
    simp only [TableRel] at this
    rw [← this, ← getLsbD_row _ _ hj, row_sboxT (by simp [VG.Proof.Aes.Arm.inTs]) hc, VG.Proof.Aes.Arm.row_inTs hc]
    simp
  · simp [VG.Proof.Aes.Arm.writes_rest (is := sboxCode) (by decide +kernel) r hr]

end VG.Proof.Aes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.Arm.Linear`. -/
section

/-!
# The linear layers of bitsliced AES on ARMv7

Each layer is checked by evaluation over the lane domain
(`Framework/Arm/Linear.lean`): the kernel runs it on the input words as
atoms and compares every output bit with the XOR of input bits given in
`Proof/Aes/Arm/Bitsliced.lean`. Position `p = 8r + 2c + b` of a word of the
bitsliced state is byte `r + 4c` of block `b`.
-/

namespace VG.Proof.Aes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm

/-- The memory of the layers: the S-box's slots, and for AddRoundKey the
round key at `kp`. -/
abbrev linCfg : Cfg := VG.Proof.Aes.Arm.sboxCfg
def arkCfg : Cfg := { base := sb, slots := 0, ext := kp, exts := 8 }

/-- The state registers hold input words `0 … 7`. -/
def qIns : List (Reg × Nat) := (List.range 8).map fun k => (VG.Impl.Aes.Arm.q k, k)

/-- The outputs `q j`, bit `p` the XOR of the input bits `g j p`. -/
def qOuts (g : Nat → Nat → List Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (VG.Impl.Aes.Arm.q j, g j)

theorem ortho_check :
    VG.Arm.Straight.check (lanes 32 8) VG.Proof.Aes.Arm.linCfg (linExt 0) ortho (linEnv VG.Proof.Aes.Arm.qIns) (linPost 8 (VG.Proof.Aes.Arm.qOuts VG.Proof.Aes.Arm.orthoG)) = true := by
  decide +kernel

theorem shiftRows_check :
    VG.Arm.Straight.check (lanes 32 8) VG.Proof.Aes.Arm.linCfg (linExt 0) shiftRows (linEnv VG.Proof.Aes.Arm.qIns) (linPost 8 (VG.Proof.Aes.Arm.qOuts VG.Proof.Aes.Arm.srG)) = true := by
  decide +kernel

theorem mixColumns_check :
    VG.Arm.Straight.check (lanes 32 8) VG.Proof.Aes.Arm.linCfg (linExt 0) mixColumns (linEnv VG.Proof.Aes.Arm.qIns) (linPost 8 (VG.Proof.Aes.Arm.qOuts VG.Proof.Aes.Arm.mcG)) = true := by
  decide +kernel

theorem addRoundKey_check :
    VG.Arm.Straight.check (lanes 32 9) VG.Proof.Aes.Arm.arkCfg (linExt 8) addRoundKey (linEnv VG.Proof.Aes.Arm.qIns) (linPost 9 (VG.Proof.Aes.Arm.qOuts VG.Proof.Aes.Arm.arkG)) = true := by
  decide +kernel

/-! ## On the machine -/

theorem q_linear {k xb : Nat} {c : Cfg} {is : List Instr} {g : Nat → Nat → List Nat}
    (hchk : VG.Arm.Straight.check (lanes 32 k) c (linExt xb) is (linEnv VG.Proof.Aes.Arm.qIns) (linPost k (VG.Proof.Aes.Arm.qOuts g)) = true)
    (hk : 256 ≤ 2 ^ k)
    (hw : layerKeep.all (fun r => is.all fun i => dstOf i != some r) = true)
    {s : State} (hok : Ok c s) (W : Nat → BitVec 32) (hW : ∀ i < 8, W i = s.gpr (VG.Impl.Aes.Arm.q i))
    (hext : ∀ j < c.exts,
      32 * (xb + j) + 32 ≤ 2 ^ k ∧ W (xb + j) = s.mem.readW (wordAddr (s.gpr c.ext) j) 32) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ j < 8, ∀ p < 32, (s'.gpr (VG.Impl.Aes.Arm.q j)).getLsbD p = Straight.xorBits W (g j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ VG.Proof.Aes.Arm.layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion c s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok hchk hok W (fun r i hri => by
    simp only [VG.Proof.Aes.Arm.qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
    obtain ⟨i, hi, rfl, rfl⟩ := hri
    exact ⟨by omega, hW i hi⟩) hext
  have hmem : ∀ j < 8, (VG.Impl.Aes.Arm.q j, g j) ∈ VG.Proof.Aes.Arm.qOuts g := fun j hj => by
    simp only [VG.Proof.Aes.Arm.qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩
  exact ⟨s', hs', fun j hj p hp => hout (VG.Impl.Aes.Arm.q j) (g j) (hmem j hj) p hp, hrd, hwr, hsp,
    fun r hr => hoth r (VG.Proof.Aes.Arm.writes_rest hw r hr), hfr⟩

/-- The words of the state registers. -/
abbrev Q (s : State) (i : Nat) : BitVec 32 := s.gpr (VG.Impl.Aes.Arm.q i)

theorem ortho_ok {s : State} (hok : Ok VG.Proof.Aes.Arm.linCfg s) :
    ∃ s', runBlock isa ortho s = some s' ∧
      (∀ j < 8, ∀ p < 32, (VG.Proof.Aes.Arm.Q s' j).getLsbD p = (VG.Proof.Aes.Arm.Q s (p % 8)).getLsbD (8 * (p / 8) + j)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ VG.Proof.Aes.Arm.layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.Arm.linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := VG.Proof.Aes.Arm.q_linear VG.Proof.Aes.Arm.ortho_check (by decide) (by decide +kernel) hok (VG.Proof.Aes.Arm.Q s)
    (fun _ _ => rfl) (fun j hj => by simp [VG.Proof.Aes.Arm.sboxCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, VG.Proof.Aes.Arm.orthoG, Straight.xorBits_cons, Straight.xorBits_nil, Bool.xor_false,
    Straight.bitOf_word _ _ _ (by omega)]

theorem shiftRows_ok {s : State} (hok : Ok VG.Proof.Aes.Arm.linCfg s) :
    ∃ s', runBlock isa shiftRows s = some s' ∧
      (∀ j < 8, ∀ p < 32, (VG.Proof.Aes.Arm.Q s' j).getLsbD p = (VG.Proof.Aes.Arm.Q s j).getLsbD (VG.Proof.Aes.Arm.srSrc p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ VG.Proof.Aes.Arm.layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.Arm.linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := VG.Proof.Aes.Arm.q_linear VG.Proof.Aes.Arm.shiftRows_check (by decide) (by decide +kernel) hok (VG.Proof.Aes.Arm.Q s)
    (fun _ _ => rfl) (fun j hj => by simp [VG.Proof.Aes.Arm.sboxCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, VG.Proof.Aes.Arm.srG, Straight.xorBits_cons, Straight.xorBits_nil, Bool.xor_false,
    Straight.bitOf_word _ _ _ (by simp only [VG.Proof.Aes.Arm.srSrc]; omega)]

theorem mixColumns_ok {s : State} (hok : Ok VG.Proof.Aes.Arm.linCfg s) :
    ∃ s', runBlock isa mixColumns s = some s' ∧
      (∀ j < 8, ∀ p < 32, (VG.Proof.Aes.Arm.Q s' j).getLsbD p = VG.Proof.Aes.Arm.termsXor (VG.Proof.Aes.Arm.Q s) (VG.Proof.Aes.Arm.mcTerms j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ VG.Proof.Aes.Arm.layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.Arm.linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := VG.Proof.Aes.Arm.q_linear VG.Proof.Aes.Arm.mixColumns_check (by decide) (by decide +kernel) hok (VG.Proof.Aes.Arm.Q s)
    (fun _ _ => rfl) (fun j hj => by simp [VG.Proof.Aes.Arm.sboxCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, VG.Proof.Aes.Arm.mcG, VG.Proof.Aes.Arm.xorBits_map]
  intro wt hwt
  obtain ⟨wk, -, rfl⟩ := List.mem_map.mp hwt
  exact Nat.mod_lt _ (by decide)

/-- Word `j` of the bitsliced round key at `kp`. -/
abbrev keyWord (s : State) (j : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr kp) j) 32

theorem addRoundKey_ok {s : State} (hok : Ok VG.Proof.Aes.Arm.arkCfg s) :
    ∃ s', runBlock isa addRoundKey s = some s' ∧
      (∀ j < 8, ∀ p < 32, (VG.Proof.Aes.Arm.Q s' j).getLsbD p = ((VG.Proof.Aes.Arm.Q s j).getLsbD p ^^ (VG.Proof.Aes.Arm.keyWord s j).getLsbD p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ VG.Proof.Aes.Arm.layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.Arm.arkCfg s] s.mem s'.mem := by
  let W : Nat → BitVec 32 := fun i => if i < 8 then VG.Proof.Aes.Arm.Q s i else VG.Proof.Aes.Arm.keyWord s (i - 8)
  obtain ⟨s', hs', hout, rest⟩ := VG.Proof.Aes.Arm.q_linear VG.Proof.Aes.Arm.addRoundKey_check (by decide) (by decide +kernel) hok W
    (fun i hi => by simp [W, hi]) (fun j hj => by
      simp only [VG.Proof.Aes.Arm.arkCfg] at hj ⊢
      refine ⟨by omega, ?_⟩
      simp [W, show ¬ 8 + j < 8 by omega])
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, VG.Proof.Aes.Arm.arkG, Straight.xorBits_cons, Straight.xorBits_cons,
    Straight.xorBits_nil, Bool.xor_false, Straight.bitOf_word _ _ _ hp,
    Straight.bitOf_word _ _ _ hp]
  simp [W, hj, show ¬ 8 + j < 8 by omega]

end VG.Proof.Aes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.Arm.Encrypt`. -/
section

/-!
# Encrypting two blocks, bitsliced, on ARMv7

`encrypt2_ok`: from two blocks in the registers (`InRel`), with the
bitsliced round keys in the scratch buffer (`KeysAt`) and `kp` at the
first, `encrypt2` leaves the two ciphertexts, having written only the first
128 bytes of the scratch buffer. The layers are composed from their proofs
(`Sbox.lean`, `Linear.lean`); the round loop's invariant is the
specification's `foldl` over the rounds done.
-/

namespace VG.Proof.Aes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Spec.Aes (roundKey subBytes shiftRows mixColumns addRoundKey cipher)

/-- The bitsliced round keys `0 … R` of the schedule `w`, from `K0`, 32 bytes each. -/
def KeysAt (m : Mem) (K0 : BitVec 32) (R : Nat) (w : List Byte) : Prop :=
  ∀ j ≤ R, VG.Proof.Aes.Arm.KeyRel (fun k => m.readW (wordAddr (K0 + BitVec.ofNat 32 (32 * j)) k) 32) (roundKey w j)

/-- What encryption needs: the scratch buffer (2048 bytes at `r8`) is
writable and does not wrap around, the round keys are in it, the last at
byte `lastKey`, and `kp` is at the first. -/
structure EncPre (s₀ : State) (R : Nat) (w : List Byte) : Prop where
  scr : (⟨State.addr (s₀.gpr sb), 2048⟩ : Region) ∈ s₀.wr
  fit : (s₀.gpr sb).toNat + 2048 ≤ 2 ^ 32
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  k0 : s₀.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (lastKey - 32 * R)
  keys : VG.Proof.Aes.Arm.KeysAt s₀.mem (s₀.gpr kp) R w

/-- What stays the same during encryption. -/
structure Ctx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ∉ VG.Proof.Aes.Arm.layerWrites → r ≠ kp → s.gpr r = s₀.gpr r
  frame : Frame [⟨State.addr (s₀.gpr sb), 128⟩] s₀.mem s.mem

theorem sb_not : sb ∉ VG.Proof.Aes.Arm.layerWrites ∧ sb ≠ kp := by decide

theorem Ctx.refl (s₀ : State) : VG.Proof.Aes.Arm.Ctx s₀ s₀ := ⟨rfl, rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _⟩

theorem Ctx.base {s₀ s : State} (hc : VG.Proof.Aes.Arm.Ctx s₀ s) : s.gpr sb = s₀.gpr sb := hc.keep _ sb_not.1 sb_not.2

theorem Ctx.step {s₀ s s' : State} (hc : VG.Proof.Aes.Arm.Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hoth : ∀ r, r ∉ VG.Proof.Aes.Arm.layerWrites → r ≠ kp → s'.gpr r = s.gpr r)
    (hfr : Frame [⟨State.addr (s.gpr sb), 128⟩] s.mem s'.mem) : VG.Proof.Aes.Arm.Ctx s₀ s' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r h1 h2 => (hoth r h1 h2).trans (hc.keep r h1 h2),
    hc.frame.trans (by rw [← hc.base]; exact hfr)⟩

theorem Ctx.linOk {s₀ s : State} {R : Nat} {w : List Byte} (hp : VG.Proof.Aes.Arm.EncPre s₀ R w) (hc : VG.Proof.Aes.Arm.Ctx s₀ s) : Ok VG.Proof.Aes.Arm.linCfg s :=
  Ok.of_off (off := 0) (by rw [hc.wr]; exact hp.scr) hp.fit (by show s.gpr sb = _; rw [hc.base]; simp)
    (by simp [VG.Proof.Aes.Arm.sboxCfg]) rfl

theorem toNat_lt_of_fit {b : BitVec 32} {n k : Nat} (h : b.toNat + n ≤ 2 ^ 32) (hk : k < n) :
    b.toNat + k < 2 ^ 32 := by omega

/-- The key area is outside what the layers write. -/
theorem keys_disjoint (b : Addr) : Region.Disjoint ⟨b + 1024, 1024⟩ ⟨b, 128⟩ := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

theorem key_contains {b : BitVec 32} (hfit : b.toNat + 2048 ≤ 2 ^ 32) {R j k : Nat} (hR : R ≤ 14)
    (hj : j ≤ R) (hk : k < 8) :
    (⟨State.addr b + 1024, 1024⟩ : Region).Contains
      (wordAddr (b + BitVec.ofNat 32 (lastKey - 32 * R) + BitVec.ofNat 32 (32 * j)) k) (32 / 8) := by
  simp only [wordAddr, lastKey]
  rw [add_ofNat_ofNat, add_ofNat_ofNat, addr_add (by omega)]
  simp only [Region.Contains]
  rw [show State.addr b + BitVec.ofNat 64 (2016 - 32 * R + (32 * j + 4 * k)) - (State.addr b + 1024) =
    BitVec.ofNat 64 (2016 - 32 * R + (32 * j + 4 * k) - 1024) by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem keyRel_congr {K K' : Nat → BitVec 32} {rk : List Byte} (h : VG.Proof.Aes.Arm.KeyRel K rk)
    (he : ∀ k < 8, K' k = K k) : VG.Proof.Aes.Arm.KeyRel K' rk := by
  intro b hb i hi
  rw [← h b hb i hi]
  exact VG.Proof.Aes.byte_ext fun j hj => by rw [VG.Proof.Aes.Arm.getLsbD_bsByte _ _ hj, VG.Proof.Aes.Arm.getLsbD_bsByte _ _ hj, he j hj]

theorem EncPre.keysAt {s₀ s : State} {R : Nat} {w : List Byte} (hp : VG.Proof.Aes.Arm.EncPre s₀ R w) (hc : VG.Proof.Aes.Arm.Ctx s₀ s) :
    VG.Proof.Aes.Arm.KeysAt s.mem (s₀.gpr kp) R w := by
  intro j hj
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  refine VG.Proof.Aes.Arm.keyRel_congr (hp.keys j hj) fun k hk => ?_
  rw [hp.k0]
  exact hc.frame.readW (VG.Proof.Aes.Arm.key_contains hp.fit hR hj hk)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Aes.Arm.keys_disjoint _) (by decide)

theorem ark_cfg_ok {s : State} {b : BitVec 32} {n : Nat}
    (hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr) (hfit : b.toNat + 2048 ≤ 2 ^ 32)
    (hk : s.gpr kp = b + BitVec.ofNat 32 n) (hn : n + 32 ≤ 2048) : Ok VG.Proof.Aes.Arm.arkCfg s :=
  Ok.of_ext (List.mem_append_right _ hscr) hfit hk (by simp [VG.Proof.Aes.Arm.arkCfg]; omega) rfl

/-! ## One layer at a time -/

/-- A layer that writes only `layerWrites` and the first 128 bytes of the
scratch buffer keeps `Ctx`. -/
theorem layer_wp {s₀ s : State} {is : List Instr} {P : State → Prop} {Q : State → Prop}
    (hl : ∃ s', runBlock isa is s = some s' ∧ P s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ∉ VG.Proof.Aes.Arm.layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [⟨State.addr (s.gpr sb), 4 * 32⟩] s.mem s'.mem)
    (hc : VG.Proof.Aes.Arm.Ctx s₀ s)
    (hQ : ∀ s', VG.Proof.Aes.Arm.Ctx s₀ s' → P s' → s'.gpr kp = s.gpr kp → Q s') : WP isa (.block is) s Q := by
  obtain ⟨s', hs', hP, hrd, hwr, hsp, hoth, hfr⟩ := hl
  exact WP.of_runBlock ⟨s', hs', hQ s' (hc.step hrd hwr hsp (fun r h _ => hoth r h) hfr) hP
    (hoth kp (by decide))⟩

/-! ## The rounds -/

/-- A middle round of the specification (round `j`). -/
def rnd (w : List Byte) (j : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  addRoundKey (mixColumns (shiftRows (subBytes x))) (roundKey w j)

/-- Rounds `1 … m`, as `cipher` folds them. -/
def midRounds (w : List Byte) (m : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  (List.range m).foldl (fun s j => VG.Proof.Aes.Arm.rnd w (j + 1) s) x

theorem midRounds_succ (w : List Byte) (m : Nat) (x : Spec.Aes.State) :
    VG.Proof.Aes.Arm.midRounds w (m + 1) x = VG.Proof.Aes.Arm.rnd w (m + 1) (VG.Proof.Aes.Arm.midRounds w m x) := by
  simp [VG.Proof.Aes.Arm.midRounds, List.range_succ, List.foldl_append]

theorem kp_step (K : BitVec 32) (m : Nat) :
    K + BitVec.ofNat 32 (32 * m) + 32 = K + BitVec.ofNat 32 (32 * (m + 1)) := by
  rw [BitVec.add_assoc, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, ← BitVec.ofNat_add,
    show 32 * m + 32 = 32 * (m + 1) by omega]

theorem q_ne_kp (i : Nat) : VG.Impl.Aes.Arm.q i ≠ kp := by
  unfold VG.Impl.Aes.Arm.q; split <;> decide

theorem q_ne_t0 (i : Nat) : VG.Impl.Aes.Arm.q i ≠ t0 := by
  unfold VG.Impl.Aes.Arm.q; split <;> decide

/-- `add kp, kp, #32`. -/
theorem addKp_wp {s₀ s : State} {P : State → Prop} (hc : VG.Proof.Aes.Arm.Ctx s₀ s)
    (h : ∀ s', VG.Proof.Aes.Arm.Ctx s₀ s' → s'.gpr kp = s.gpr kp + 32 → (∀ i, VG.Proof.Aes.Arm.Q s' i = VG.Proof.Aes.Arm.Q s i) → P s') :
    WP isa (.block [.dp .add kp kp (.imm 32)]) s P := by
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, show exec (.dp .add kp kp (.imm 32)) s =
    some (s.setReg kp (s.gpr kp + 32)) from rfl, runStep_some, runBlock_nil], h _ ?_ ?_ ?_⟩
  · exact hc.step rfl rfl rfl (fun r _ hr => by simp [State.setReg, hr]) (Frame.refl _ _)
  · simp [State.setReg]
  · intro i; simp [VG.Proof.Aes.Arm.Q, State.setReg, VG.Proof.Aes.Arm.q_ne_kp i]

/-- `sub t0, kp, sb; cmp t0, #(lastKey − 32)`. -/
theorem cmpLast_wp {s₀ s : State} {P : State → Prop} (hc : VG.Proof.Aes.Arm.Ctx s₀ s)
    (h : ∀ s', VG.Proof.Aes.Arm.Ctx s₀ s' → s'.gpr kp = s.gpr kp → (∀ i, VG.Proof.Aes.Arm.Q s' i = VG.Proof.Aes.Arm.Q s i) →
      s'.z = (s.gpr kp - s.gpr sb - BitVec.ofNat 32 (lastKey - 32) == 0) → P s') :
    WP isa (.block [.dp .sub t0 kp (.reg sb), .cmp t0 (.imm (BitVec.ofNat 32 (lastKey - 32)))]) s P := by
  refine WP.of_runBlock ⟨_, by
    rw [runBlock_cons, show exec (.dp .sub t0 kp (.reg sb)) s =
      some (s.setReg t0 (s.gpr kp - s.gpr sb)) from rfl, runStep_some, runBlock_cons,
      show exec (.cmp t0 (.imm (BitVec.ofNat 32 (lastKey - 32)))) (s.setReg t0 (s.gpr kp - s.gpr sb)) =
        some (subFlags (s.setReg t0 (s.gpr kp - s.gpr sb)) (s.gpr kp - s.gpr sb)
          (BitVec.ofNat 32 (lastKey - 32))) by simp [exec, Op2.eval, State.setReg, t0]; decide,
      runStep_some, runBlock_nil], h _ ?_ ?_ ?_ ?_⟩
  · exact hc.step rfl rfl rfl (fun r hr _ => by
      have : r ≠ t0 := fun h => hr (h ▸ by decide)
      simp [subFlags, State.setReg, this]) (Frame.refl _ _)
  · simp [subFlags, State.setReg, t0, kp]
  · intro i; simp [VG.Proof.Aes.Arm.Q, subFlags, State.setReg, VG.Proof.Aes.Arm.q_ne_t0 i]
  · simp [subFlags]

theorem t0_last (b : BitVec 32) {R m : Nat} (hR : R ≤ 14) (hm : m + 1 < R) :
    (!(b + BitVec.ofNat 32 (lastKey - 32 * R + 32 * (m + 1)) - b - BitVec.ofNat 32 (lastKey - 32) == 0)) =
      !decide (m + 2 = R) := by
  simp only [lastKey]
  by_cases h : m + 2 = R
  · have e : b + BitVec.ofNat 32 (2016 - 32 * R + 32 * (m + 1)) - b - BitVec.ofNat 32 (2016 - 32) = 0 := by
      bv_omega
    rw [e]; simp [h]
  · have e : b + BitVec.ofNat 32 (2016 - 32 * R + 32 * (m + 1)) - b - BitVec.ofNat 32 (2016 - 32) ≠ 0 := by
      intro h'; apply h; bv_omega
    simpa [h] using e

theorem kp_off (K0 b : BitVec 32) {R j : Nat} (hk : K0 = b + BitVec.ofNat 32 (lastKey - 32 * R)) :
    K0 + BitVec.ofNat 32 (32 * j) = b + BitVec.ofNat 32 (lastKey - 32 * R + 32 * j) := by
  rw [hk, add_ofNat_ofNat]

theorem ark_frame {s₀ s s' : State} (hc : VG.Proof.Aes.Arm.Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hoth : ∀ r, r ∉ VG.Proof.Aes.Arm.layerWrites → s'.gpr r = s.gpr r)
    (hfr : Frame [slotRegion VG.Proof.Aes.Arm.arkCfg s] s.mem s'.mem) : VG.Proof.Aes.Arm.Ctx s₀ s' :=
  hc.step hrd hwr hsp (fun r h _ => hoth r h)
    (hfr.sub fun r hr => ⟨_, List.mem_singleton_self _, fun a ha => by
      simp only [List.mem_singleton] at hr; subst hr
      simp [slotRegion, VG.Proof.Aes.Arm.arkCfg, Region.Contains] at ha⟩)

/-- A middle round. -/
theorem round_ok {s₀ s : State} {R m : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : VG.Proof.Aes.Arm.EncPre s₀ R w) (hc : VG.Proof.Aes.Arm.Ctx s₀ s) (hk : s.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * m))
    (hm : m + 1 < R) (hbs : VG.Proof.Aes.Arm.BsRel (VG.Proof.Aes.Arm.Q s) T) :
    WP isa (.block roundBody) s fun s' => VG.Proof.Aes.Arm.Ctx s₀ s' ∧
      s'.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * (m + 1)) ∧
      VG.Proof.Aes.Arm.BsRel (VG.Proof.Aes.Arm.Q s') (fun b => VG.Proof.Aes.Arm.rnd w (m + 1) (T b)) ∧
      Arm.eval .ne s' = some (!decide (m + 2 = R)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  simp only [roundBody]
  repeat rw [WP.block_append_iff (M := isa)]
  refine VG.Proof.Aes.Arm.addKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
  rw [hk, VG.Proof.Aes.Arm.kp_step] at hk₁
  have hbs₁ : VG.Proof.Aes.Arm.BsRel (VG.Proof.Aes.Arm.Q s₁) T := by
    have : VG.Proof.Aes.Arm.Q s₁ = VG.Proof.Aes.Arm.Q s := funext hq₁
    rw [this]; exact hbs
  refine VG.Proof.Aes.Arm.layer_wp (VG.Proof.Aes.Arm.sbox_ok (hc₁.linOk hp)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
  have hbs₂ := VG.Proof.Aes.Arm.bs_subBytes h₂ hbs₁
  refine VG.Proof.Aes.Arm.layer_wp (VG.Proof.Aes.Arm.shiftRows_ok (hc₂.linOk hp)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
  have hbs₃ := VG.Proof.Aes.Arm.bs_shiftRows h₃ hbs₂
  refine VG.Proof.Aes.Arm.layer_wp (VG.Proof.Aes.Arm.mixColumns_ok (hc₃.linOk hp)) hc₃ fun s₄ hc₄ h₄ hk₄ => ?_
  have hbs₄ := VG.Proof.Aes.Arm.bs_mixColumns h₄ hbs₃
  have hk₄' : s₄.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * (m + 1)) := by rw [hk₄, hk₃, hk₂, hk₁]
  have hok : Ok VG.Proof.Aes.Arm.arkCfg s₄ := VG.Proof.Aes.Arm.ark_cfg_ok (b := s₀.gpr sb) (by rw [hc₄.wr]; exact hp.scr) hp.fit
    (by rw [hk₄', VG.Proof.Aes.Arm.kp_off _ _ hp.k0]) (by simp only [lastKey]; omega)
  have hkey : VG.Proof.Aes.Arm.KeyRel (VG.Proof.Aes.Arm.keyWord s₄) (roundKey w (m + 1)) := by
    have := hp.keysAt hc₄ (m + 1) (by omega)
    unfold VG.Proof.Aes.Arm.keyWord; rw [hk₄']; exact this
  obtain ⟨s₅, hs₅, h₅, hrd, hwr, hsp, hoth, hfr⟩ := VG.Proof.Aes.Arm.addRoundKey_ok hok
  have hc₅ : VG.Proof.Aes.Arm.Ctx s₀ s₅ := VG.Proof.Aes.Arm.ark_frame hc₄ hrd hwr hsp hoth hfr
  have hbs₅ := VG.Proof.Aes.Arm.bs_addRoundKey h₅ hbs₄ hkey
  refine WP.of_runBlock ⟨s₅, hs₅, ?_⟩
  refine VG.Proof.Aes.Arm.cmpLast_wp hc₅ fun s₆ hc₆ hk₆ hq₆ hz₆ => ⟨hc₆, ?_, ?_, ?_⟩
  · rw [hk₆, hoth kp (by decide), hk₄']
  · have : VG.Proof.Aes.Arm.Q s₆ = VG.Proof.Aes.Arm.Q s₅ := funext hq₆
    rw [this]; exact hbs₅
  · simp only [Arm.eval, hz₆]
    rw [hoth kp (by decide), hk₄', hoth sb (by decide), hc₄.base, VG.Proof.Aes.Arm.kp_off _ _ hp.k0, VG.Proof.Aes.Arm.t0_last _ hR hm]

theorem ark_step {s₀ s : State} {R j : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : VG.Proof.Aes.Arm.EncPre s₀ R w) (hc : VG.Proof.Aes.Arm.Ctx s₀ s) (hk : s.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * j))
    (hj : j ≤ R) (hbs : VG.Proof.Aes.Arm.BsRel (VG.Proof.Aes.Arm.Q s) T) {P : State → Prop}
    (h : ∀ s', VG.Proof.Aes.Arm.Ctx s₀ s' → s'.gpr kp = s.gpr kp → VG.Proof.Aes.Arm.BsRel (VG.Proof.Aes.Arm.Q s') (fun b => addRoundKey (T b) (roundKey w j)) →
      P s') : WP isa (.block addRoundKey) s P := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hok : Ok VG.Proof.Aes.Arm.arkCfg s := VG.Proof.Aes.Arm.ark_cfg_ok (b := s₀.gpr sb) (by rw [hc.wr]; exact hp.scr) hp.fit
    (by rw [hk, VG.Proof.Aes.Arm.kp_off _ _ hp.k0]) (by simp only [lastKey]; omega)
  have hkey : VG.Proof.Aes.Arm.KeyRel (VG.Proof.Aes.Arm.keyWord s) (roundKey w j) := by
    have := hp.keysAt hc j hj
    unfold VG.Proof.Aes.Arm.keyWord; rw [hk]; exact this
  obtain ⟨s', hs', h', hrd, hwr, hsp, hoth, hfr⟩ := VG.Proof.Aes.Arm.addRoundKey_ok hok
  exact WP.of_runBlock ⟨s', hs', h s' (VG.Proof.Aes.Arm.ark_frame hc hrd hwr hsp hoth hfr) (hoth kp (by decide))
    (VG.Proof.Aes.Arm.bs_addRoundKey h' hbs hkey)⟩

theorem cipher_eq (R : Nat) (w : List Byte) (x : Spec.Aes.State) :
    cipher R w x = addRoundKey (shiftRows (subBytes (VG.Proof.Aes.Arm.midRounds w (R - 1)
      (addRoundKey x (roundKey w 0))))) (roundKey w R) := rfl

/-- Two blocks, from `InRel` to `InRel` of their encryptions. -/
theorem encrypt2_ok {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}
    (hp : VG.Proof.Aes.Arm.EncPre s₀ R w) (hin : VG.Proof.Aes.Arm.InRel (VG.Proof.Aes.Arm.Q s₀) S) :
    WP isa encrypt2 s₀ fun s => VG.Proof.Aes.Arm.Ctx s₀ s ∧ VG.Proof.Aes.Arm.InRel (VG.Proof.Aes.Arm.Q s) (fun b => cipher R w (S b)) := by
  have hR1 : 2 ≤ R := by rcases hp.rounds with h | h | h <;> omega
  let A : Nat → Spec.Aes.State := fun b => addRoundKey (S b) (roundKey w 0)
  -- The rounds done so far.
  let Inv : Nat → State → Prop := fun n s => ∃ m, n = R - 1 - m ∧ m + 1 < R ∧ VG.Proof.Aes.Arm.Ctx s₀ s ∧
    s.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * m) ∧ VG.Proof.Aes.Arm.BsRel (VG.Proof.Aes.Arm.Q s) (fun b => VG.Proof.Aes.Arm.midRounds w m (A b))
  let Mid : State → Prop := fun s => VG.Proof.Aes.Arm.Ctx s₀ s ∧
    s.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * (R - 1)) ∧
    VG.Proof.Aes.Arm.BsRel (VG.Proof.Aes.Arm.Q s) (fun b => VG.Proof.Aes.Arm.midRounds w (R - 1) (A b))
  refine WP.seq (WP.mono (Q := Inv (R - 1)) ?_ fun s h => WP.seq (WP.mono (Q := Mid) ?_ fun s h => ?_))
  · -- ortho, the first round key.
    rw [WP.block_append_iff (M := isa)]
    refine VG.Proof.Aes.Arm.layer_wp (VG.Proof.Aes.Arm.ortho_ok ((Ctx.refl s₀).linOk hp)) (Ctx.refl s₀) fun s₁ hc₁ h₁ hk₁ => ?_
    have hbs₁ := VG.Proof.Aes.Arm.bs_of_in h₁ hin
    have hk₁' : s₁.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * 0) := by rw [hk₁]; simp
    exact VG.Proof.Aes.Arm.ark_step hp hc₁ hk₁' (by omega) hbs₁ fun s₃ hc₃ hk₃ hbs₃ =>
      ⟨0, by omega, by omega, hc₃, by rw [hk₃, hk₁'], hbs₃⟩
  · -- The middle rounds.
    refine WP.loop (M := isa) Inv (fun n s hs => ?_) (R - 1) s h
    obtain ⟨m, rfl, hm, hc, hk, hbs⟩ := hs
    refine WP.mono (VG.Proof.Aes.Arm.round_ok hp hc hk hm hbs) fun s' ⟨hc', hk', hbs', hz⟩ => ?_
    by_cases hlast : m + 2 = R
    · refine .inl ⟨hz.trans (by simp [hlast]), hc', ?_, ?_⟩
      · rw [hk']; congr 3; omega
      · rw [show R - 1 = m + 1 by omega]
        intro b hb i hi
        rw [hbs' b hb i hi]; simp only [VG.Proof.Aes.Arm.midRounds_succ]
    · refine .inr ⟨hz.trans (by simp [hlast]), R - 1 - (m + 1), by omega, m + 1, rfl, by omega, hc',
        hk', fun b hb i hi => by rw [hbs' b hb i hi]; simp only [VG.Proof.Aes.Arm.midRounds_succ]⟩
  · -- The last round, and back to blocks.
    obtain ⟨hc, hk, hbs⟩ := h
    rw [WP.block_append_iff (M := isa)]
    simp only [lastRound]
    repeat rw [WP.block_append_iff (M := isa)]
    refine VG.Proof.Aes.Arm.addKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
    rw [hk, VG.Proof.Aes.Arm.kp_step, show R - 1 + 1 = R by omega] at hk₁
    have hbs₁ : VG.Proof.Aes.Arm.BsRel (VG.Proof.Aes.Arm.Q s₁) (fun b => VG.Proof.Aes.Arm.midRounds w (R - 1) (A b)) := by
      have : VG.Proof.Aes.Arm.Q s₁ = VG.Proof.Aes.Arm.Q s := funext hq₁
      rw [this]; exact hbs
    refine VG.Proof.Aes.Arm.layer_wp (VG.Proof.Aes.Arm.sbox_ok (hc₁.linOk hp)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
    have hbs₂ := VG.Proof.Aes.Arm.bs_subBytes h₂ hbs₁
    refine VG.Proof.Aes.Arm.layer_wp (VG.Proof.Aes.Arm.shiftRows_ok (hc₂.linOk hp)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
    have hbs₃ := VG.Proof.Aes.Arm.bs_shiftRows h₃ hbs₂
    refine VG.Proof.Aes.Arm.ark_step hp hc₃ (by rw [hk₃, hk₂, hk₁]) (Nat.le_refl R) hbs₃ fun s₄ hc₄ _ hbs₄ => ?_
    refine VG.Proof.Aes.Arm.layer_wp (VG.Proof.Aes.Arm.ortho_ok (hc₄.linOk hp)) hc₄ fun s₅ hc₅ h₅ _ => ⟨hc₅, ?_⟩
    have := VG.Proof.Aes.Arm.in_of_bs h₅ hbs₄
    intro b hb i hi j hj
    rw [this b hb i hi j hj]; simp only [VG.Proof.Aes.Arm.cipher_eq]; rfl

end VG.Proof.Aes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.Arm.Keys`. -/
section

/-!
# Bitslicing the round keys, on ARMv7

The key loop of `vg_aes_ctr32` bitslices each round key (loaded as two
identical blocks) with `ortho` and stores it in the scratch buffer. The
loads and stores are checked by evaluation over the naming domain
(`Bitslice.names`), `ortho` by its proof (`Linear.lean`). During the loop
the scratch buffer's base is not in a register: the round keys are stored
through `kp`.
-/

namespace VG.Proof.Aes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Spec.Aes (roundKey)

/-- `ortho` does not use memory: its check with no slots. -/
def noMem : Cfg := { base := sb, slots := 0, ext := sb, exts := 0 }

theorem ortho_check0 :
    VG.Arm.Straight.check (lanes 32 8) VG.Proof.Aes.Arm.noMem (linExt 0) ortho (linEnv VG.Proof.Aes.Arm.qIns) (linPost 8 (VG.Proof.Aes.Arm.qOuts VG.Proof.Aes.Arm.orthoG)) = true := by
  decide +kernel

theorem noMem_ok (s : State) : Ok VG.Proof.Aes.Arm.noMem s where
  slotIn k hk := by simp [VG.Proof.Aes.Arm.noMem] at hk
  extIn k hk := by simp [VG.Proof.Aes.Arm.noMem] at hk
  slots := by simp only [VG.Proof.Aes.Arm.noMem]; have := (s.gpr sb).isLt; omega
  sep k hk := by simp [VG.Proof.Aes.Arm.noMem] at hk

theorem frame_nil {m m' : Mem} {a : Addr} (h : Frame [⟨a, 4 * 0⟩] m m') : m' = m := by
  funext x
  exact h x fun r hr hc => by
    simp only [List.mem_singleton] at hr; subst hr
    simp [Region.Contains] at hc

/-- The registers `ortho` (and the loads of a round key) may write. -/
def orthoWrites : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r10, .r11]

theorem ortho_writes : ∀ r, r ∉ VG.Proof.Aes.Arm.orthoWrites → (ortho.all fun i => dstOf i != some r) = true := by
  intro r; cases r <;> decide +kernel

theorem keyLoad_writes : ∀ r, r ∉ VG.Proof.Aes.Arm.orthoWrites → (keyLoad.all fun i => dstOf i != some r) = true := by
  intro r; cases r <;> decide +kernel

/-- `ortho`, wherever `sb` points. -/
theorem ortho_ok' (s : State) :
    ∃ s', runBlock isa ortho s = some s' ∧
      (∀ j < 8, ∀ p < 32, (VG.Proof.Aes.Arm.Q s' j).getLsbD p = (VG.Proof.Aes.Arm.Q s (p % 8)).getLsbD (8 * (p / 8) + j)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ VG.Proof.Aes.Arm.orthoWrites → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem := by
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok VG.Proof.Aes.Arm.ortho_check0 (VG.Proof.Aes.Arm.noMem_ok s) (VG.Proof.Aes.Arm.Q s)
    (fun r i hri => by
      simp only [VG.Proof.Aes.Arm.qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega, rfl⟩) (fun j hj => by simp [VG.Proof.Aes.Arm.noMem] at hj)
  have hmem : ∀ j < 8, (VG.Impl.Aes.Arm.q j, VG.Proof.Aes.Arm.orthoG j) ∈ VG.Proof.Aes.Arm.qOuts VG.Proof.Aes.Arm.orthoG := fun j hj => by
    simp only [VG.Proof.Aes.Arm.qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩
  refine ⟨s', hs', fun j hj p hp => ?_, hrd, hwr, hsp, fun r hr => hoth r ?_, VG.Proof.Aes.Arm.frame_nil hfr⟩
  · rw [hout _ _ (hmem j hj) p hp, VG.Proof.Aes.Arm.orthoG, Straight.xorBits_cons, Straight.xorBits_nil, Bool.xor_false,
      Straight.bitOf_word _ _ _ (by omega)]
  · simp [VG.Proof.Aes.Arm.ortho_writes r hr]

/-! ## Loading a round key -/

def loadCfg : Cfg := { base := sb, slots := 0, ext := .r12, exts := 4 }

def loadPost (e : Env Nat) : Bool :=
  (List.range 4).all fun k => e.reg (VG.Impl.Aes.Arm.q (2 * k)) == some k && e.reg (VG.Impl.Aes.Arm.q (2 * k + 1)) == some k

theorem keyLoad_check :
    VG.Arm.Straight.check (names 32) VG.Proof.Aes.Arm.loadCfg (fun k => some k) keyLoad { reg := fun _ => none, slot := fun _ => none }
      VG.Proof.Aes.Arm.loadPost = true := by
  decide +kernel

/-- The registers the key loop writes. -/
def keyWrites : List Reg := kp :: VG.Proof.Aes.Arm.layerWrites

theorem keyLoad_ok {s : State} {b : BitVec 32} {len off : Nat}
    (hr : (⟨State.addr b, len⟩ : Region) ∈ s.rd ++ s.wr) (hfit : b.toNat + len ≤ 2 ^ 32)
    (hb : s.gpr .r12 = b + BitVec.ofNat 32 off) (hoff : off + 16 ≤ len) :
    ∃ s', runBlock isa keyLoad s = some s' ∧
      (∀ k < 4, s'.gpr (VG.Impl.Aes.Arm.q (2 * k)) = s.mem.readW (wordAddr (s.gpr .r12) k) 32 ∧
        s'.gpr (VG.Impl.Aes.Arm.q (2 * k + 1)) = s.mem.readW (wordAddr (s.gpr .r12) k) 32) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ∉ VG.Proof.Aes.Arm.orthoWrites → s'.gpr r = s.gpr r) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.Aes.Arm.keyLoad_check
  have hok : Ok VG.Proof.Aes.Arm.loadCfg s := Ok.of_ext hr hfit hb (by simp [VG.Proof.Aes.Arm.loadCfg]; omega) rfl
  let V : Nat → BitVec 32 := fun k => s.mem.readW (wordAddr (s.gpr .r12) k) 32
  have hrel : Rel (NameRel V) VG.Proof.Aes.Arm.loadCfg (fun k => some k) { reg := fun _ => none, slot := fun _ => none } s := by
    refine ⟨(fun _ _ h => by cases h), (fun _ _ _ h => by cases h), fun k a hk h => ?_,
      (fun _ _ h => by cases h)⟩
    simp only [Option.some.injEq] at h; subst h; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) hok hrel he
  refine ⟨s', hs', fun k hk => ?_, p.rd, p.wr, p.sp, ?_, fun r hr => p.other r ?_⟩
  · have := List.all_eq_true.mp hpost k (List.mem_range.mpr hk)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨p.rel.reg _ _ this.1, p.rel.reg _ _ this.2⟩
  · funext x
    exact p.frame x fun r' hr' hc => by
      simp only [List.mem_singleton] at hr'; subst hr'
      simp [slotRegion, VG.Proof.Aes.Arm.loadCfg, Region.Contains] at hc
  · exact Bool.ne_false_of_eq_true (VG.Proof.Aes.Arm.keyLoad_writes r hr)

/-! ## Storing it -/

def storeCfg : Cfg := { base := kp, slots := 8, ext := kp, exts := 0 }

def storeEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => VG.Impl.Aes.Arm.q k == r)), slot := fun _ => none }

def storePost (e : Env Nat) : Bool := (List.range 8).all fun k => e.slot k == some k

theorem keyStore_check : VG.Arm.Straight.check (names 32) VG.Proof.Aes.Arm.storeCfg (fun _ => none) keyStore VG.Proof.Aes.Arm.storeEnv VG.Proof.Aes.Arm.storePost = true := by
  decide +kernel

theorem keyStore_ok {s : State} {b : BitVec 32} {len off : Nat}
    (hr : (⟨State.addr b, len⟩ : Region) ∈ s.wr) (hfit : b.toNat + len ≤ 2 ^ 32)
    (hb : s.gpr kp = b + BitVec.ofNat 32 off) (hoff : off + 32 ≤ len) :
    ∃ s', runBlock isa keyStore s = some s' ∧
      (∀ k < 8, s'.mem.readW (wordAddr (s.gpr kp) k) 32 = s.gpr (VG.Impl.Aes.Arm.q k)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr = s.gpr ∧
      Frame [⟨State.addr (s.gpr kp), 32⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.Aes.Arm.keyStore_check
  have hok : Ok VG.Proof.Aes.Arm.storeCfg s := Ok.of_off hr hfit hb (by simp [VG.Proof.Aes.Arm.storeCfg]; omega) rfl
  let V : Nat → BitVec 32 := fun k => s.gpr (VG.Impl.Aes.Arm.q k)
  have hrel : Rel (NameRel V) VG.Proof.Aes.Arm.storeCfg (fun _ => none) VG.Proof.Aes.Arm.storeEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ hk _ => by simp [VG.Proof.Aes.Arm.storeCfg] at hk),
      (fun _ _ h => by cases h)⟩
    simp only [VG.Proof.Aes.Arm.storeEnv] at h
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
      s'.gpr .r12 = s.gpr .r12 - 16 ∧ s'.gpr kp = s.gpr kp - 32 ∧ s'.gpr .lr = s.gpr .lr - 1 ∧
      s'.z = (s.gpr .lr - 1 == 0) ∧
      (∀ r, r ≠ .r12 → r ≠ kp → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by simp only [keyStep, runBlock_cons, exec, Op2.eval]; rfl, ?_⟩
  refine ⟨by simp [State.setReg, subFlags, kp], by simp [State.setReg, subFlags, kp],
    by simp [State.setReg, subFlags, kp], by simp [State.setReg, subFlags, kp],
    fun r h1 h2 h3 => by simp [State.setReg, subFlags, h1, h2, h3], rfl, rfl, rfl, rfl⟩

/-! ## Readings and regions -/

/-! ## The loop -/

/-- Where the loop runs: the scratch buffer at `b`, the key schedule `w`
at `sc` (as the bytes there). -/
structure KSetup (s₀ : State) (b sc : BitVec 32) (R : Nat) (w : List Byte) : Prop where
  scr : (⟨State.addr b, 2048⟩ : Region) ∈ s₀.wr
  fit : b.toNat + 2048 ≤ 2 ^ 32
  sch : (⟨State.addr sc, 240⟩ : Region) ∈ s₀.rd ++ s₀.wr
  fitS : sc.toNat + 240 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨State.addr sc, 240⟩ ⟨State.addr b, 2048⟩
  rounds : R ≤ 14
  w : ∀ i < 16 * (R + 1), w.getD i 0 = s₀.mem (State.addr sc + BitVec.ofNat 64 i)

/-- The address of bitsliced round key `i`. -/
abbrev keyAddr (b : BitVec 32) (R i : Nat) : BitVec 32 := b + BitVec.ofNat 32 (lastKey - 32 * (R - i))

/-- The key area of the scratch buffer at `b`. -/
abbrev keyArea (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 1024, 1024⟩

/-- Before bitslicing round key `j` (the loop's counter aside). -/
structure KInv (s₀ : State) (b sc : BitVec 32) (R : Nat) (w : List Byte) (j : Nat) (s : State) : Prop where
  hj : j ≤ R
  r12 : s.gpr .r12 = sc + BitVec.ofNat 32 (16 * j)
  kp : s.gpr kp = VG.Proof.Aes.Arm.keyAddr b R j
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ∉ VG.Proof.Aes.Arm.keyWrites → s.gpr r = s₀.gpr r
  frame : Frame [VG.Proof.Aes.Arm.keyArea b] s₀.mem s.mem
  done : ∀ i, j < i → i ≤ R →
    VG.Proof.Aes.Arm.KeyRel (fun k => s.mem.readW (wordAddr (VG.Proof.Aes.Arm.keyAddr b R i) k) 32) (roundKey w i)

/-- After the loop. -/
structure KDone (s₀ : State) (b : BitVec 32) (R : Nat) (w : List Byte) (s : State) : Prop where
  kp : s.gpr kp = VG.Proof.Aes.Arm.keyAddr b R 0 - 32
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ∉ VG.Proof.Aes.Arm.keyWrites → s.gpr r = s₀.gpr r
  frame : Frame [VG.Proof.Aes.Arm.keyArea b] s₀.mem s.mem
  keys : ∀ i ≤ R, VG.Proof.Aes.Arm.KeyRel (fun k => s.mem.readW (wordAddr (VG.Proof.Aes.Arm.keyAddr b R i) k) 32) (roundKey w i)

theorem roundKey_getD {w : List Byte} {j i : Nat} (hi : i < 16) :
    (roundKey w j).getD i 0 = w.getD (16 * j + i) 0 := by
  simp only [roundKey, List.getD_eq_getElem?_getD, List.getElem?_take, hi, ite_true,
    List.getElem?_drop]

/-- The 64-bit address of a word of a round key. -/
theorem keyWord_addr {b : BitVec 32} (hfit : b.toNat + 2048 ≤ 2 ^ 32) {R i k : Nat} (hk : k < 8) :
    wordAddr (VG.Proof.Aes.Arm.keyAddr b R i) k = State.addr b + BitVec.ofNat 64 (lastKey - 32 * (R - i) + 4 * k) := by
  simp only [wordAddr, VG.Proof.Aes.Arm.keyAddr, lastKey]
  rw [add_ofNat_ofNat, addr_add (by omega)]

/-- The schedule's bytes are those of `w`. -/
theorem KInv.sched {s₀ : State} {b sc : BitVec 32} {R : Nat} {w : List Byte} (hk : VG.Proof.Aes.Arm.KSetup s₀ b sc R w)
    {j : Nat} {s : State} (hi : VG.Proof.Aes.Arm.KInv s₀ b sc R w j s) {i : Nat} (hi16 : i < 16) :
    s.mem (State.addr sc + BitVec.ofNat 64 (16 * j + i)) = (roundKey w j).getD i 0 := by
  have hjR := hi.hj
  have hR := hk.rounds
  rw [VG.Proof.Aes.Arm.roundKey_getD hi16, hk.w _ (by omega)]
  refine hi.frame _ fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  have hsub : Region.Sub (VG.Proof.Aes.Arm.keyArea b) ⟨State.addr b, 2048⟩ := by
    intro a h
    simp only [Region.Contains] at h ⊢
    bv_omega
  refine hk.sep _ ?_ (hsub _ hc)
  simp only [Region.Contains]
  rw [show State.addr sc + BitVec.ofNat 64 (16 * j + i) - State.addr sc = BitVec.ofNat 64 (16 * j + i) by
    bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The round key as a state. -/
def rkv (w : List Byte) (j : Nat) : Spec.Aes.State := Vector.ofFn fun i => (roundKey w j).getD i 0

theorem keyRel_of_bs {K : Nat → BitVec 32} {w : List Byte} {j : Nat}
    (h : VG.Proof.Aes.Arm.BsRel K fun _ => VG.Proof.Aes.Arm.rkv w j) : VG.Proof.Aes.Arm.KeyRel K (roundKey w j) := by
  intro b hb i hi
  rw [h b hb i hi, VG.Proof.Aes.getD_eq _ hi, VG.Proof.Aes.Arm.rkv, Vector.getElem_ofFn]

theorem keyWrites_not (r : Reg) (hr : r ∉ VG.Proof.Aes.Arm.keyWrites) :
    r ∉ VG.Proof.Aes.Arm.orthoWrites ∧ r ≠ .r12 ∧ r ≠ kp ∧ r ≠ .lr := by
  revert hr; cases r <;> decide

theorem keyAddr_pred (b : BitVec 32) {R j : Nat} (hR : R ≤ 14) (hj : 0 < j) (hjR : j ≤ R) :
    VG.Proof.Aes.Arm.keyAddr b R j - 32 = VG.Proof.Aes.Arm.keyAddr b R (j - 1) := by
  simp only [VG.Proof.Aes.Arm.keyAddr, lastKey]
  rw [show 2016 - 32 * (R - j) = (2016 - 32 * (R - (j - 1))) + 32 by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

/-- The part of the loop's body before the step: load round key `j`,
bitslice it and store it. -/
theorem keyFront_ok {s₀ : State} {b sc : BitVec 32} {R : Nat} {w : List Byte} (hk : VG.Proof.Aes.Arm.KSetup s₀ b sc R w)
    {j : Nat} {s : State} (hi : VG.Proof.Aes.Arm.KInv s₀ b sc R w j s) {rest : List Instr} {P : State → Prop}
    (h : ∀ s₃, s₃.gpr .r12 = sc + BitVec.ofNat 32 (16 * j) → s₃.gpr kp = VG.Proof.Aes.Arm.keyAddr b R j →
      s₃.gpr .lr = s.gpr .lr → (∀ r, r ∉ VG.Proof.Aes.Arm.keyWrites → s₃.gpr r = s₀.gpr r) →
      s₃.rd = s₀.rd → s₃.wr = s₀.wr → s₃.sp = s₀.sp → Frame [VG.Proof.Aes.Arm.keyArea b] s₀.mem s₃.mem →
      (∀ i, j ≤ i → i ≤ R →
        VG.Proof.Aes.Arm.KeyRel (fun k => s₃.mem.readW (wordAddr (VG.Proof.Aes.Arm.keyAddr b R i) k) 32) (roundKey w i)) →
      WP isa (.block rest) s₃ P) :
    WP isa (.block (keyLoad ++ ortho ++ keyStore ++ rest)) s P := by
  have hR := hk.rounds
  have hjR := hi.hj
  repeat rw [WP.block_append_iff (M := isa)]
  -- Load the round key.
  obtain ⟨s₁, hs₁, hq₁, hrd₁, hwr₁, hsp₁, hm₁, hoth₁⟩ := VG.Proof.Aes.Arm.keyLoad_ok (b := sc) (off := 16 * j)
    (by rw [hi.rd, hi.wr]; exact hk.sch) hk.fitS hi.r12 (by omega)
  refine WP.of_runBlock ⟨s₁, hs₁, ?_⟩
  have hin : VG.Proof.Aes.Arm.InRel (VG.Proof.Aes.Arm.Q s₁) fun _ => VG.Proof.Aes.Arm.rkv w j := by
    intro bb hb i hi16 t ht
    have hbyte := hi.sched hk hi16
    rw [VG.Proof.Aes.getD_eq _ hi16, VG.Proof.Aes.Arm.rkv, Vector.getElem_ofFn]
    simp only [VG.Proof.Aes.Arm.Q]
    have hq : s₁.gpr (VG.Impl.Aes.Arm.q (2 * (i / 4) + bb)) = s.mem.readW (wordAddr (s.gpr .r12) (i / 4)) 32 := by
      rcases (show bb = 0 ∨ bb = 1 by omega) with rfl | rfl
      · exact (hq₁ _ (by omega)).1
      · exact (hq₁ _ (by omega)).2
    rw [hq, readW_bit _ _ (show i % 4 < 4 by omega) ht, wordAddr, hi.r12, add_ofNat_ofNat,
      addr_add (by have := hk.fitS; omega), BitVec.add_assoc, ← BitVec.ofNat_add, ← hbyte]
    rw [show 16 * j + 4 * (i / 4) + i % 4 = 16 * j + i by omega]
  -- Bitslice it.
  obtain ⟨s₂, hs₂, hq₂, hrd₂, hwr₂, hsp₂, hoth₂, hm₂⟩ := VG.Proof.Aes.Arm.ortho_ok' s₁
  refine WP.of_runBlock ⟨s₂, hs₂, ?_⟩
  have hbs₂ := VG.Proof.Aes.Arm.bs_of_in hq₂ hin
  -- Store it.
  have hkp₂ : s₂.gpr kp = VG.Proof.Aes.Arm.keyAddr b R j := by
    rw [hoth₂ kp (by decide), hoth₁ kp (by decide), hi.kp]
  obtain ⟨s₃, hs₃, hst₃, hrd₃, hwr₃, hsp₃, hg₃, hfr₃⟩ := VG.Proof.Aes.Arm.keyStore_ok (b := b)
    (off := lastKey - 32 * (R - j)) (by rw [hwr₂, hwr₁, hi.wr]; exact hk.scr) hk.fit hkp₂
    (by simp only [lastKey]; omega)
  refine WP.of_runBlock ⟨s₃, hs₃, ?_⟩
  -- The region written now.
  have e : State.addr (VG.Proof.Aes.Arm.keyAddr b R j) = State.addr b + BitVec.ofNat 64 (lastKey - 32 * (R - j)) := by
    simp only [VG.Proof.Aes.Arm.keyAddr, lastKey]; rw [addr_add (by have := hk.fit; omega)]
  have hsubk : Region.Sub ⟨State.addr (VG.Proof.Aes.Arm.keyAddr b R j), 32⟩ (VG.Proof.Aes.Arm.keyArea b) := by
    rw [e]
    exact off_sub _ (by simp only [lastKey]; omega) (by simp only [lastKey]; omega) (by decide)
  refine h s₃ ?_ (by rw [hg₃, hkp₂]) ?_ (fun r hr => ?_) (by rw [hrd₃, hrd₂, hrd₁, hi.rd])
    (by rw [hwr₃, hwr₂, hwr₁, hi.wr]) (by rw [hsp₃, hsp₂, hsp₁, hi.sp]) ?_ (fun i hji hiR => ?_)
  · rw [hg₃, hoth₂ .r12 (by decide), hoth₁ .r12 (by decide), hi.r12]
  · rw [hg₃, hoth₂ .lr (by decide), hoth₁ .lr (by decide)]
  · obtain ⟨h1, -, -, -⟩ := VG.Proof.Aes.Arm.keyWrites_not r hr
    rw [hg₃, hoth₂ r h1, hoth₁ r h1, hi.keep r hr]
  · refine hi.frame.trans ?_
    rw [← hm₁, ← hm₂]
    rw [hkp₂] at hfr₃
    exact hfr₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact hsubk⟩
  · by_cases hij : i = j
    · subst hij
      exact VG.Proof.Aes.Arm.keyRel_congr (VG.Proof.Aes.Arm.keyRel_of_bs hbs₂) fun k hk => by rw [← hkp₂, hst₃ k hk]
    · refine VG.Proof.Aes.Arm.keyRel_congr (hi.done i (by omega) hiR) fun k hk8 => ?_
      rw [VG.Proof.Aes.Arm.keyWord_addr hk.fit hk8, hfr₃.readW (r := ⟨_, 4⟩) (Region.contains_self _ _) ?_
        (by decide), hm₂, hm₁]
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      rw [hkp₂, e]
      exact off_disjoint _ (by simp only [lastKey]; omega) (by simp only [lastKey]; omega)
        (by simp only [lastKey]; omega)

theorem keyBody_ok {s₀ : State} {b sc : BitVec 32} {R : Nat} {w : List Byte} (hk : VG.Proof.Aes.Arm.KSetup s₀ b sc R w)
    {j : Nat} {s : State} (hi : VG.Proof.Aes.Arm.KInv s₀ b sc R w j s) (hlr : s.gpr .lr = BitVec.ofNat 32 (j + 1)) :
    WP isa (.block keyBody) s fun s' =>
      (j = 0 ∧ Arm.eval .ne s' = some false ∧ VG.Proof.Aes.Arm.KDone s₀ b R w s') ∨
      (0 < j ∧ Arm.eval .ne s' = some true ∧ VG.Proof.Aes.Arm.KInv s₀ b sc R w (j - 1) s' ∧
        s'.gpr .lr = BitVec.ofNat 32 (j - 1 + 1)) := by
  have hR := hk.rounds
  have hjR := hi.hj
  simp only [keyBody]
  refine VG.Proof.Aes.Arm.keyFront_ok hk hi fun s₃ hr12 hkp hlr₃ hkeep₃ hrd hwr hsp hfr hkeys => ?_
  -- Step back.
  obtain ⟨s₄, hs₄, hr12₄, hkp₄, hlr₄, hz₄, hoth₄, hm₄, hrd₄, hwr₄, hsp₄⟩ := VG.Proof.Aes.Arm.keyStep_ok s₃
  refine WP.of_runBlock ⟨s₄, hs₄, ?_⟩
  have hkeep : ∀ r, r ∉ VG.Proof.Aes.Arm.keyWrites → s₄.gpr r = s₀.gpr r := by
    intro r hr
    obtain ⟨-, h2, h3, h4⟩ := VG.Proof.Aes.Arm.keyWrites_not r hr
    rw [hoth₄ r h2 h3 h4, hkeep₃ r hr]
  have hlr' : s₄.gpr .lr = BitVec.ofNat 32 j := by
    rw [hlr₄, hlr₃, hlr]; bv_omega
  have hev : Arm.eval .ne s₄ = some (!(BitVec.ofNat 32 j == 0)) := by
    simp only [Arm.eval, hz₄, hlr₃, hlr]
    congr 3; bv_omega
  rw [← hm₄] at hfr
  have hkeys' : ∀ i, j ≤ i → i ≤ R →
      VG.Proof.Aes.Arm.KeyRel (fun k => s₄.mem.readW (wordAddr (VG.Proof.Aes.Arm.keyAddr b R i) k) 32) (roundKey w i) := by
    rw [hm₄]; exact hkeys
  by_cases h0 : j = 0
  · subst h0
    exact .inl ⟨rfl, hev.trans (by decide), ⟨by rw [hkp₄, hkp], by rw [hrd₄, hrd], by rw [hwr₄, hwr],
      by rw [hsp₄, hsp], hkeep, hfr, fun i hiR => hkeys' i (by omega) hiR⟩⟩
  · have hne : BitVec.ofNat 32 j ≠ 0 := by
      intro h; have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simp at this; omega
    refine .inr ⟨by omega, hev.trans (by simpa using hne),
      ⟨by have := hi.hj; omega, ?_, ?_, by rw [hrd₄, hrd], by rw [hwr₄, hwr], by rw [hsp₄, hsp], hkeep,
        hfr, fun i hi' hiR => hkeys' i (by omega) hiR⟩, by rw [hlr', show j - 1 + 1 = j by omega]⟩
    · rw [hr12₄, hr12]; bv_omega
    · rw [hkp₄, hkp]; exact VG.Proof.Aes.Arm.keyAddr_pred b hk.rounds (by omega) hi.hj

theorem keyLoop_ok {s₀ : State} {b sc : BitVec 32} {R : Nat} {w : List Byte} (hk : VG.Proof.Aes.Arm.KSetup s₀ b sc R w)
    {s : State} (hi : VG.Proof.Aes.Arm.KInv s₀ b sc R w R s) (hlr : s.gpr .lr = BitVec.ofNat 32 (R + 1)) :
    WP isa (.loop (.block keyBody) .ne) s (VG.Proof.Aes.Arm.KDone s₀ b R w) := by
  refine WP.loop (M := isa) (fun n s => VG.Proof.Aes.Arm.KInv s₀ b sc R w n s ∧ s.gpr .lr = BitVec.ofNat 32 (n + 1))
    (fun n s hs => ?_) R s ⟨hi, hlr⟩
  refine WP.mono (VG.Proof.Aes.Arm.keyBody_ok hk hs.1 hs.2) fun s' h => ?_
  rcases h with ⟨_, hev, hd⟩ | ⟨hn, hev, hi', hlr'⟩
  · exact .inl ⟨hev, hd⟩
  · exact .inr ⟨hev, n - 1, by omega, hi', hlr'⟩

end VG.Proof.Aes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.Arm.Group`. -/
section

/-!
# One group of counter-mode blocks on ARMv7

A group stores the data pointer, the blocks left and the first round key
in slots 45–47 of the scratch buffer (`groupSave`), `ctrBlocks` builds the
counter blocks `c + b` (`b < 2`) from the slots of the counter block
(`front_wp`, then `ctr_inRel` for `InRel`), `encrypt2` encrypts them
(`Encrypt.lean`), `groupLoad` loads the three values back, and `xorFull` or
`xorTail` XOR the keystream into the data, a word at a time. The
per-instruction rules are those of `Proof/MdStream/Arm/Common.lean`.
-/

namespace VG.Proof.Aes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_cmp wp_rev
  wp_ldr wp_str)
open VG.Proof.Aes (ctrState ctrBlock_byte toBytes_getD getD_eq byte_ext)

theorem wp_eor {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2}
    {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho])
    (k _ (Upd.setReg _ _ _))

/-! ## Slots of the scratch buffer -/

/-- Slot `k` of the scratch buffer at `B`. -/
abbrev slotA (B : Addr) (k : Nat) : Addr := B + BitVec.ofNat 64 (4 * k)

theorem slot_addr {b : BitVec 32} (hfit : b.toNat + 2048 ≤ 2 ^ 32) {k : Nat} (hk : k < 512) :
    State.addr (b + BitVec.ofNat 32 (4 * k)) = VG.Proof.Aes.Arm.slotA (State.addr b) k := addr_add (by omega)

theorem slot_addr' {b : BitVec 32} {L : Nat} (hfit : b.toNat + L ≤ 2 ^ 32) {k : Nat} (hk : 4 * k + 4 ≤ L) :
    State.addr (b + BitVec.ofNat 32 (4 * k)) = VG.Proof.Aes.Arm.slotA (State.addr b) k := addr_add (by omega)

theorem slot_in {rs : List Region} {b : BitVec 32} (hr : (⟨State.addr b, 2048⟩ : Region) ∈ rs)
    (hfit : b.toNat + 2048 ≤ 2 ^ 32) {k : Nat} (hk : k < 512) : InRegions rs (VG.Proof.Aes.Arm.slotA (State.addr b) k) 4 := by
  rw [← VG.Proof.Aes.Arm.slot_addr hfit hk]; exact in_off hr hfit (by omega) (by omega)

theorem slotA_sep (B : Addr) {j k : Nat} (hj : j < 512) (hk : k < 512) (h : j ≠ k) :
    Mem.Sep (VG.Proof.Aes.Arm.slotA B j) (32 / 8) (VG.Proof.Aes.Arm.slotA B k) (32 / 8) := by
  intro x h₁ h₂
  simp only [VG.Proof.Aes.Arm.slotA] at h₁ h₂
  have : j < k ∨ k < j := by omega
  rcases this with h' | h' <;> bv_omega

theorem readW_writeW_slot (m : Mem) (B : Addr) {j k : Nat} (hj : j < 512) (hk : k < 512) (h : j ≠ k)
    (v : BitVec 32) : (m.writeW (VG.Proof.Aes.Arm.slotA B k) v).readW (VG.Proof.Aes.Arm.slotA B j) 32 = m.readW (VG.Proof.Aes.Arm.slotA B j) 32 :=
  Mem.readW_writeW_sep (VG.Proof.Aes.Arm.slotA_sep B hj hk h) (by decide)

section
variable {is : List Instr} {s : State} {Q : State → Prop} {b : BitVec 32}

theorem wp_ldS {t : Reg} {k : Nat} (hb : s.gpr sb = b) (hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr)
    (hfit : b.toNat + 2048 ≤ 2 ^ 32) (hk : k < 512)
    (c : ∀ s', Upd s s' t (s.mem.readW (VG.Proof.Aes.Arm.slotA (State.addr b) k) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (ldS t k :: is)) s Q :=
  wp_ldr (by omega) (by rw [hb]; exact VG.Proof.Aes.Arm.slot_addr hfit hk)
    (VG.Proof.Aes.Arm.slot_in (List.mem_append_right _ hscr) hfit hk) c

theorem wp_stS {t : Reg} {k : Nat} (hb : s.gpr sb = b) (hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr)
    (hfit : b.toNat + 2048 ≤ 2 ^ 32) (hk : k < 512)
    (c : ∀ s', Mupd s s' (s.mem.writeW (VG.Proof.Aes.Arm.slotA (State.addr b) k) (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (stS k t :: is)) s Q :=
  wp_str (by omega) (by rw [hb]; exact VG.Proof.Aes.Arm.slot_addr hfit hk) (VG.Proof.Aes.Arm.slot_in hscr hfit hk) c

end

/-! ## The counter blocks -/

/-- The words of the counter block in the slots: words 0–2, and the counter. -/
abbrev cwW (m : Mem) (B : Addr) (k : Nat) : BitVec 32 := m.readW (VG.Proof.Aes.Arm.slotA B (cW k)) 32
abbrev numW (m : Mem) (B : Addr) : BitVec 32 := m.readW (VG.Proof.Aes.Arm.slotA B cNum) 32

theorem q_ctr : ∀ bb < 2, ∀ k < 4, VG.Impl.Aes.Arm.q (2 * k + bb) ≠ sb ∧ VG.Impl.Aes.Arm.q (2 * k + bb) ≠ t0 ∧ VG.Impl.Aes.Arm.q (2 * k + bb) ≠ kp := by
  decide

theorem q_ne : ∀ a < 8, ∀ c < 8, a ≠ c → VG.Impl.Aes.Arm.q a ≠ VG.Impl.Aes.Arm.q c := by
  decide

theorem q_inj : ∀ bb < 2, ∀ j < 4, ∀ k < 4, j ≠ k → VG.Impl.Aes.Arm.q (2 * j + bb) ≠ VG.Impl.Aes.Arm.q (2 * k + bb) := by
  decide

theorem ctrBlock_wp {s : State} {b : BitVec 32} {bb : Nat} (hbb : bb < 2) (hb : s.gpr sb = b)
    (hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr) (hfit : b.toNat + 2048 ≤ 2 ^ 32) {P : State → Prop}
    (h : ∀ s', (∀ k < 3, s'.gpr (VG.Impl.Aes.Arm.q (2 * k + bb)) = VG.Proof.Aes.Arm.cwW s.mem (State.addr b) k) →
      s'.gpr (VG.Impl.Aes.Arm.q (2 * 3 + bb)) = rev (VG.Proof.Aes.Arm.numW s.mem (State.addr b) + BitVec.ofNat 32 bb) →
      (∀ r, (∀ k < 4, r ≠ VG.Impl.Aes.Arm.q (2 * k + bb)) → r ≠ t0 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → P s') :
    WP isa (.block (ctrBlock bb)) s P := by
  have qc := VG.Proof.Aes.Arm.q_ctr bb hbb
  have e0 : VG.Impl.Aes.Arm.q bb = VG.Impl.Aes.Arm.q (2 * 0 + bb) := by simp
  have e1 : VG.Impl.Aes.Arm.q (2 + bb) = VG.Impl.Aes.Arm.q (2 * 1 + bb) := by congr 1
  have e2 : VG.Impl.Aes.Arm.q (4 + bb) = VG.Impl.Aes.Arm.q (2 * 2 + bb) := by congr 1
  have e3 : VG.Impl.Aes.Arm.q (6 + bb) = VG.Impl.Aes.Arm.q (2 * 3 + bb) := by congr 1
  simp only [ctrBlock, e0, e1, e2, e3]
  refine VG.Proof.Aes.Arm.wp_ldS hb hscr hfit (by decide) fun s₁ u₁ => ?_
  have hb₁ : s₁.gpr sb = b := (u₁.other _ (qc 0 (by omega)).1.symm).trans hb
  refine VG.Proof.Aes.Arm.wp_ldS hb₁ (u₁.wr ▸ hscr) hfit (by decide) fun s₂ u₂ => ?_
  have hb₂ : s₂.gpr sb = b := (u₂.other _ (qc 1 (by omega)).1.symm).trans hb₁
  refine VG.Proof.Aes.Arm.wp_ldS hb₂ (u₂.wr ▸ u₁.wr ▸ hscr) hfit (by decide) fun s₃ u₃ => ?_
  have hb₃ : s₃.gpr sb = b := (u₃.other _ (qc 2 (by omega)).1.symm).trans hb₂
  refine VG.Proof.Aes.Arm.wp_ldS hb₃ (u₃.wr ▸ u₂.wr ▸ u₁.wr ▸ hscr) hfit (by decide) fun s₄ u₄ => ?_
  refine wp_add (op2_imm (by rcases (show bb = 0 ∨ bb = 1 by omega) with rfl | rfl <;> decide))
    fun s₅ u₅ => ?_
  refine wp_rev fun s₆ u₆ => ?_
  refine WP.block_nil (h s₆ (fun k hk => ?_) ?_ (fun r hr ht => ?_) ?_ ?_ ?_ ?_)
  · have hne : ∀ j < 4, j ≠ k → VG.Impl.Aes.Arm.q (2 * k + bb) ≠ VG.Impl.Aes.Arm.q (2 * j + bb) := fun j hj hjk =>
      VG.Proof.Aes.Arm.q_inj bb hbb k (by omega) j hj (Ne.symm hjk)
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
    · rw [u₆.other _ (hne 3 (by omega) (by omega)), u₅.other _ (qc 0 (by omega)).2.1,
        u₄.other _ (qc 0 (by omega)).2.1, u₃.other _ (hne 2 (by omega) (by omega)),
        u₂.other _ (hne 1 (by omega) (by omega)), u₁.gpr]
    · rw [u₆.other _ (hne 3 (by omega) (by omega)), u₅.other _ (qc 1 (by omega)).2.1,
        u₄.other _ (qc 1 (by omega)).2.1, u₃.other _ (hne 2 (by omega) (by omega)), u₂.gpr,
        u₁.mem]
    · rw [u₆.other _ (hne 3 (by omega) (by omega)), u₅.other _ (qc 2 (by omega)).2.1,
        u₄.other _ (qc 2 (by omega)).2.1, u₃.gpr, u₂.mem, u₁.mem]
  · rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.other _ (hr 3 (by omega)), u₅.other _ ht, u₄.other _ ht, u₃.other _ (hr 2 (by omega)),
      u₂.other _ (hr 1 (by omega)), u₁.other _ (hr 0 (by omega))]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-- The memory after `groupSave` and `ctrBlocks`. -/
def frontMem (m : Mem) (B : Addr) (d l f : BitVec 32) : Mem :=
  (((m.writeW (VG.Proof.Aes.Arm.slotA B dSlot) d).writeW (VG.Proof.Aes.Arm.slotA B lSlot) l).writeW (VG.Proof.Aes.Arm.slotA B fkSlot) f).writeW
    (VG.Proof.Aes.Arm.slotA B cNum) (VG.Proof.Aes.Arm.numW m B + 2)

theorem q_other : ∀ r, r ∉ VG.Proof.Aes.Arm.layerWrites → r ≠ kp → (∀ bb < 2, ∀ k < 4, r ≠ VG.Impl.Aes.Arm.q (2 * k + bb)) ∧ r ≠ t0 := by
  intro r; cases r <;> decide

theorem gs_read (m : Mem) (B : Addr) (d l f : BitVec 32) {k : Nat} (hk : k < 45) :
    (((m.writeW (VG.Proof.Aes.Arm.slotA B dSlot) d).writeW (VG.Proof.Aes.Arm.slotA B lSlot) l).writeW (VG.Proof.Aes.Arm.slotA B fkSlot) f).readW
      (VG.Proof.Aes.Arm.slotA B k) 32 = m.readW (VG.Proof.Aes.Arm.slotA B k) 32 := by
  rw [VG.Proof.Aes.Arm.readW_writeW_slot _ _ (by omega) (by decide) (by simp [fkSlot]; omega),
    VG.Proof.Aes.Arm.readW_writeW_slot _ _ (by omega) (by decide) (by simp [lSlot]; omega),
    VG.Proof.Aes.Arm.readW_writeW_slot _ _ (by omega) (by decide) (by simp [dSlot]; omega)]

/-- `groupSave` and the two counter blocks, and `c := c + 2`. -/
theorem front_wp {s : State} {b : BitVec 32} (hb : s.gpr sb = b)
    (hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr) (hfit : b.toNat + 2048 ≤ 2 ^ 32) {P : State → Prop}
    (h : ∀ s', (∀ bb < 2, (∀ k < 3, s'.gpr (VG.Impl.Aes.Arm.q (2 * k + bb)) = VG.Proof.Aes.Arm.cwW s.mem (State.addr b) k) ∧
        s'.gpr (VG.Impl.Aes.Arm.q (2 * 3 + bb)) = rev (VG.Proof.Aes.Arm.numW s.mem (State.addr b) + BitVec.ofNat 32 bb)) →
      s'.gpr kp = s.gpr .r12 → (∀ r, r ∉ VG.Proof.Aes.Arm.layerWrites → r ≠ kp → s'.gpr r = s.gpr r) →
      s'.mem = VG.Proof.Aes.Arm.frontMem s.mem (State.addr b) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → P s') :
    WP isa (.block (groupSave ++ ctrBlocks)) s P := by
  simp only [groupSave, List.cons_append, List.nil_append]
  refine VG.Proof.Aes.Arm.wp_stS hb hscr hfit (by decide) fun s₁ u₁ => ?_
  refine VG.Proof.Aes.Arm.wp_stS (u₁.gpr ▸ hb) (u₁.wr ▸ hscr) hfit (by decide) fun s₂ u₂ => ?_
  refine VG.Proof.Aes.Arm.wp_stS (u₂.gpr ▸ u₁.gpr ▸ hb) (u₂.wr ▸ u₁.wr ▸ hscr) hfit (by decide) fun s₃ u₃ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  have hb₄ : s₄.gpr sb = b := by rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr, hb]
  have hscr₄ : (⟨State.addr b, 2048⟩ : Region) ∈ s₄.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hscr
  have hm₄ : s₄.mem = ((s.mem.writeW (VG.Proof.Aes.Arm.slotA (State.addr b) dSlot) (s.gpr .r10)).writeW
      (VG.Proof.Aes.Arm.slotA (State.addr b) lSlot) (s.gpr .r11)).writeW (VG.Proof.Aes.Arm.slotA (State.addr b) fkSlot) (s.gpr .r12) := by
    simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr]
  simp only [ctrBlocks]
  repeat rw [WP.block_append_iff (M := isa)]
  refine VG.Proof.Aes.Arm.ctrBlock_wp (bb := 0) (by omega) hb₄ hscr₄ hfit fun s₅ c₅ n₅ o₅ m₅ rd₅ wr₅ sp₅ => ?_
  have hb₅ : s₅.gpr sb = b := (o₅ _ (fun k hk => (VG.Proof.Aes.Arm.q_ctr 0 (by omega) k hk).1.symm) (by decide)).trans hb₄
  refine VG.Proof.Aes.Arm.ctrBlock_wp (bb := 1) (by omega) hb₅ (wr₅ ▸ hscr₄) hfit fun s₆ c₆ n₆ o₆ m₆ rd₆ wr₆ sp₆ => ?_
  have hb₆ : s₆.gpr sb = b := (o₆ _ (fun k hk => (VG.Proof.Aes.Arm.q_ctr 1 (by omega) k hk).1.symm) (by decide)).trans hb₅
  refine VG.Proof.Aes.Arm.wp_ldS hb₆ (wr₆ ▸ wr₅ ▸ hscr₄) hfit (by decide) fun s₇ u₇ => ?_
  refine wp_add (op2_imm (by decide)) fun s₈ u₈ => ?_
  have hb₈ : s₈.gpr sb = b := by rw [u₈.other _ (by decide), u₇.other _ (by decide), hb₆]
  refine VG.Proof.Aes.Arm.wp_stS hb₈ (by rw [u₈.wr, u₇.wr, wr₆, wr₅]; exact hscr₄) hfit (by decide) fun s₉ u₉ => ?_
  have mnum : VG.Proof.Aes.Arm.numW s₄.mem (State.addr b) = VG.Proof.Aes.Arm.numW s.mem (State.addr b) := by
    rw [VG.Proof.Aes.Arm.numW, hm₄, VG.Proof.Aes.Arm.gs_read _ _ _ _ _ (by decide)]
  have mcw : ∀ k < 3, VG.Proof.Aes.Arm.cwW s₄.mem (State.addr b) k = VG.Proof.Aes.Arm.cwW s.mem (State.addr b) k := by
    intro k hk
    rw [VG.Proof.Aes.Arm.cwW, hm₄, VG.Proof.Aes.Arm.gs_read _ _ _ _ _ (by simp [cW]; omega)]
  refine WP.block_nil (h s₉ (fun bb hbb => ?_) ?_ (fun r h1 h2 => ?_) ?_ ?_ ?_ ?_)
  · have qo : ∀ k < 4, VG.Impl.Aes.Arm.q (2 * k + bb) ≠ t0 := fun k hk => (VG.Proof.Aes.Arm.q_ctr bb hbb k hk).2.1
    rcases (show bb = 0 ∨ bb = 1 by omega) with rfl | rfl
    · refine ⟨fun k hk => ?_, ?_⟩
      · rw [u₉.gpr, u₈.other _ (qo k (by omega)), u₇.other _ (qo k (by omega)),
          o₆ _ (fun j hj => VG.Proof.Aes.Arm.q_ne _ (by omega) _ (by omega) (by omega)) (qo k (by omega)), c₅ k hk, mcw k hk]
      · rw [u₉.gpr, u₈.other _ (qo 3 (by omega)), u₇.other _ (qo 3 (by omega)),
          o₆ _ (fun j hj => VG.Proof.Aes.Arm.q_ne _ (by omega) _ (by omega) (by omega)) (qo 3 (by omega)), n₅, mnum]
    · refine ⟨fun k hk => ?_, ?_⟩
      · rw [u₉.gpr, u₈.other _ (qo k (by omega)), u₇.other _ (qo k (by omega)), c₆ k hk, m₅, mcw k hk]
      · rw [u₉.gpr, u₈.other _ (qo 3 (by omega)), u₇.other _ (qo 3 (by omega)), n₆, m₅, mnum]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      o₆ _ (fun j hj => (VG.Proof.Aes.Arm.q_ctr 1 (by omega) j hj).2.2.symm) (by decide),
      o₅ _ (fun j hj => (VG.Proof.Aes.Arm.q_ctr 0 (by omega) j hj).2.2.symm) (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  · obtain ⟨hq, ht⟩ := VG.Proof.Aes.Arm.q_other r h1 h2
    rw [u₉.gpr, u₈.other _ ht, u₇.other _ ht, o₆ _ (hq 1 (by omega)) ht, o₅ _ (hq 0 (by omega)) ht,
      u₄.other _ h2, u₃.gpr, u₂.gpr, u₁.gpr]
  · rw [u₉.mem, u₈.gpr, u₇.gpr, u₈.mem, u₇.mem, m₆, m₅, VG.Proof.Aes.Arm.frontMem, ← mnum, hm₄]
  · rw [u₉.rd, u₈.rd, u₇.rd, rd₆, rd₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, wr₆, wr₅, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₉.sp, u₈.sp, u₇.sp, sp₆, sp₅, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-! ## The counter blocks as states -/

/-- The counter blocks `2g` and `2g + 1` in the words, as `InRel` has them. -/
theorem ctr_inRel {Q : Nat → BitVec 32} {icb : Spec.Gcm.Block} {W : Nat → BitVec 32} {C : BitVec 32}
    {g : Nat}
    (hw : ∀ k < 3, ∀ t < 4, ∀ j < 8, (W k).getLsbD (8 * t + j) = icb.getLsbD (8 * (15 - (4 * k + t)) + j))
    (hC : C = icb.extractLsb' 0 32 + BitVec.ofNat 32 (2 * g))
    (hQ : ∀ bb < 2, (∀ k < 3, Q (2 * k + bb) = W k) ∧ Q (2 * 3 + bb) = rev (C + BitVec.ofNat 32 bb)) :
    VG.Proof.Aes.Arm.InRel Q (fun bb => ctrState icb (2 * g + bb)) := by
  intro bb hb i hi16 j hj
  obtain ⟨h0, h1⟩ := hQ bb hb
  simp only [ctrState, getD_eq _ hi16, Vector.getElem_ofFn]
  rw [ctrBlock_byte _ _ hi16]
  by_cases h12 : i < 12
  · rw [ite_eq_left h12, h0 _ (by omega), toBytes_getD _ hi16, BitVec.getLsbD_extractLsb',
      hw _ (by omega) _ (by omega) _ hj, show 4 * (i / 4) + i % 4 = i by omega]
    simp [hj]
  · rw [ite_eq_right h12, show i / 4 = 3 by omega, h1, rev_bit _ (by omega) hj, hC,
      BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.getLsbD_extractLsb']
    simp only [hj, decide_true, Bool.true_and]
    congr 1; omega

/-! ## XOR into the data -/

/-- XOR `v` into the 4 bytes at `a`. -/
def xorW (m : Mem) (a : Addr) (v : BitVec 32) : Mem := m.writeW a (m.readW a 32 ^^^ v)

theorem xorW_apply (m : Mem) (a x : Addr) (v : BitVec 32) :
    VG.Proof.Aes.Arm.xorW m a v x = if (x - a).toNat < 4 then m x ^^^ v.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  unfold VG.Proof.Aes.Arm.xorW Mem.writeW Mem.write
  split
  · rename_i h
    have hx : a + BitVec.ofNat 64 (x - a).toNat = x := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have := Mem.extractLsb'_read m a (n := 4) h
    rw [hx] at this
    rw [← this]
    ext t ht
    simp only [BitVec.getElem_extractLsb', BitVec.getElem_xor, Mem.readW]
    simp
  · rfl

/-- The data after `k` words: the keystream `ks` XORed into the first `4 k`
of the `16 n` bytes at `D`. -/
def DataInv (m₀ m : Mem) (D : Addr) (n k : Nat) (ks : Nat → Byte) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    m₀ (D + BitVec.ofNat 64 i) ^^^ (if i < 4 * k then ks i else 0)

theorem off_toNat (D : Addr) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    (D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 j)).toNat =
      if j ≤ i then i - j else 2 ^ 64 + i - j := by
  rw [← BitVec.sub_sub, BitVec.add_comm D, BitVec.add_sub_cancel, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
  split
  · rw [show 2 ^ 64 - j + i = (i - j) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [show 2 ^ 64 - j + i = 2 ^ 64 + i - j by omega]; exact Nat.mod_eq_of_lt (by omega)

/-- One word of keystream XORed in. -/
theorem dataInv_step {m₀ m : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte} {v : BitVec 32}
    (hn : 16 * n ≤ 2 ^ 32) (hk : k < 4 * n) (h : VG.Proof.Aes.Arm.DataInv m₀ m D n k ks)
    (hks : ∀ t < 4, v.extractLsb' (8 * t) 8 = ks (4 * k + t)) :
    VG.Proof.Aes.Arm.DataInv m₀ (VG.Proof.Aes.Arm.xorW m (D + BitVec.ofNat 64 (4 * k)) v) D n (k + 1) ks ∧
      Frame [⟨D, 16 * n⟩] m (VG.Proof.Aes.Arm.xorW m (D + BitVec.ofNat 64 (4 * k)) v) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · rw [VG.Proof.Aes.Arm.xorW_apply, VG.Proof.Aes.Arm.off_toNat D (by omega) (by omega), h i hi]
    by_cases h1 : 4 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 4 * k < 4
      · rw [ite_eq_left h2, hks _ h2, ite_eq_right (show ¬ i < 4 * k by omega),
          ite_eq_left (show i < 4 * (k + 1) by omega), show 4 * k + (i - 4 * k) = i by omega]
        simp
      · rw [ite_eq_right h2, ite_eq_right (show ¬ i < 4 * k by omega),
          ite_eq_right (show ¬ i < 4 * (k + 1) by omega)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 4 * k < 4 by omega),
        ite_eq_left (show i < 4 * k by omega), ite_eq_left (show i < 4 * (k + 1) by omega)]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx _ (List.mem_singleton_self _)
    rw [VG.Proof.Aes.Arm.xorW_apply, ite_eq_right]
    have : 4 * k < 2 ^ 64 := by omega
    have : (BitVec.ofNat 64 (4 * k)).toNat = 4 * k := by simp; omega
    bv_omega

theorem dataInv_mono {m₀ m : Mem} {D : Addr} {n k k' : Nat} {ks : Nat → Byte} (h : VG.Proof.Aes.Arm.DataInv m₀ m D n k ks)
    (hk : 4 * n ≤ k) (hk' : 4 * n ≤ k') : VG.Proof.Aes.Arm.DataInv m₀ m D n k' ks := by
  intro i hi
  rw [h i hi, ite_eq_left (show i < 4 * k by omega), ite_eq_left (show i < 4 * k' by omega)]

/-- The keystream, byte by byte: byte `i` is byte `i mod 16` of the
encrypted counter block `i / 16`. -/
def keyStream (R : Nat) (w : List Byte) (icb : Spec.Gcm.Block) (i : Nat) : Byte :=
  (Spec.Aes.cipher R w (ctrState icb (i / 16))).getD (i % 16) 0

theorem ks_of_inRel {Q : Nat → BitVec 32} {R g : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
    (h : VG.Proof.Aes.Arm.InRel Q (fun bb => Spec.Aes.cipher R w (ctrState icb (2 * g + bb)))) {k t : Nat} (hk : k < 8)
    (ht : t < 4) :
    (Q (2 * (k % 4) + k / 4)).extractLsb' (8 * t) 8 = VG.Proof.Aes.Arm.keyStream R w icb (4 * (8 * g + k) + t) := by
  apply byte_ext
  intro j hj
  have := h (k / 4) (by omega) (4 * (k % 4) + t) (by omega) j hj
  rw [show (4 * (k % 4) + t) / 4 = k % 4 by omega, show (4 * (k % 4) + t) % 4 = t by omega] at this
  rw [BitVec.getLsbD_extractLsb', this, VG.Proof.Aes.Arm.keyStream,
    show (4 * (8 * g + k) + t) / 16 = 2 * g + k / 4 by omega,
    show (4 * (8 * g + k) + t) % 16 = 4 * (k % 4) + t by omega]
  simp [hj]

/-- Word `k` of a group of two blocks: `ldr`, `eor` with its keystream word, `str`. -/
def triple (k : Nat) : List Instr :=
  [.ldr .lr .r10 (4 * k), eorR .lr .lr (VG.Impl.Aes.Arm.q (2 * (k % 4) + k / 4)), .str .lr .r10 (4 * k)]

theorem xorFull_eq : xorFull = VG.Proof.Aes.Arm.triple 0 ++ VG.Proof.Aes.Arm.triple 1 ++ VG.Proof.Aes.Arm.triple 2 ++ VG.Proof.Aes.Arm.triple 3 ++ VG.Proof.Aes.Arm.triple 4 ++ VG.Proof.Aes.Arm.triple 5 ++
    VG.Proof.Aes.Arm.triple 6 ++ VG.Proof.Aes.Arm.triple 7 ++ ([.dp .add .r10 .r10 (.imm 32), .dp .sub .r11 .r11 (.imm 2)] : List Instr) := rfl

theorem xorTail_eq : xorTail = VG.Proof.Aes.Arm.triple 0 ++ VG.Proof.Aes.Arm.triple 1 ++ VG.Proof.Aes.Arm.triple 2 ++ VG.Proof.Aes.Arm.triple 3 ++
    ([.mov .r11 (.imm 0)] : List Instr) := rfl

/-- After `k` words of the group have been XORed in, from `s₃`. -/
structure XS (m₀ : Mem) (D : Addr) (n g : Nat) (ks : Nat → Byte) (s₃ : State) (k : Nat) (s : State) :
    Prop where
  data : VG.Proof.Aes.Arm.DataInv m₀ s.mem D n (8 * g + k) ks
  frame : Frame [⟨D, 16 * n⟩] s₃.mem s.mem
  keep : ∀ r, r ≠ .lr → r ≠ kp → s.gpr r = s₃.gpr r
  rd : s.rd = s₃.rd
  wr : s.wr = s₃.wr
  sp : s.sp = s₃.sp

/-- Before the XOR phase of group `g`: the keystream is in the words. -/
structure XPre (m₀ : Mem) (Dp : BitVec 32) (n g : Nat) (ks : Nat → Byte) (s₃ : State) : Prop where
  hg : 2 * g < n
  fit : Dp.toNat + 16 * n ≤ 2 ^ 32
  dat : (⟨State.addr Dp, 16 * n⟩ : Region) ∈ s₃.wr
  r10 : s₃.gpr .r10 = Dp + BitVec.ofNat 32 (32 * g)
  r11 : s₃.gpr .r11 = BitVec.ofNat 32 (n - 2 * g)
  data : VG.Proof.Aes.Arm.DataInv m₀ s₃.mem (State.addr Dp) n (8 * g) ks
  ks : ∀ k < 8, ∀ t < 4, (s₃.gpr (VG.Impl.Aes.Arm.q (2 * (k % 4) + k / 4))).extractLsb' (8 * t) 8 = ks (4 * (8 * g + k) + t)

section Xor

variable {m₀ : Mem} {Dp : BitVec 32} {n g : Nat} {ks : Nat → Byte} {s₃ : State}

theorem xs_step (hp : VG.Proof.Aes.Arm.XPre m₀ Dp n g ks s₃) {k : Nat} (hk : k < 8) (hkn : 8 * g + k < 4 * n) {s : State}
    (hs : VG.Proof.Aes.Arm.XS m₀ (State.addr Dp) n g ks s₃ k s) {is : List Instr} {P : State → Prop}
    (h : ∀ s', VG.Proof.Aes.Arm.XS m₀ (State.addr Dp) n g ks s₃ (k + 1) s' → WP isa (.block is) s' P) :
    WP isa (.block (VG.Proof.Aes.Arm.triple k ++ is)) s P := by
  have hn := hp.fit
  have ha : State.addr (s.gpr .r10 + BitVec.ofNat 32 (4 * k)) =
      State.addr Dp + BitVec.ofNat 64 (4 * (8 * g + k)) := by
    rw [hs.keep _ (by decide) (by decide), hp.r10, add_ofNat_ofNat, addr_add (by omega)]
    congr 2; omega
  have hin : InRegions s.wr (State.addr Dp + BitVec.ofNat 64 (4 * (8 * g + k))) 4 := by
    have := in_off (hs.wr ▸ hp.dat) hp.fit (off := 4 * (8 * g + k)) (n := 4) (by omega) (by omega)
    rwa [addr_add (by omega)] at this
  have hq : VG.Impl.Aes.Arm.q (2 * (k % 4) + k / 4) ≠ .lr := by unfold VG.Impl.Aes.Arm.q; split <;> decide
  have hqk : VG.Impl.Aes.Arm.q (2 * (k % 4) + k / 4) ≠ kp := (VG.Proof.Aes.Arm.q_ctr (k / 4) (by omega) (k % 4) (by omega)).2.2
  simp only [VG.Proof.Aes.Arm.triple, List.cons_append, List.nil_append]
  refine wp_ldr (by omega) ha (by
    obtain ⟨r, hr, hc⟩ := hin; exact ⟨r, List.mem_append_right _ hr, hc⟩) fun s₁ u₁ => ?_
  refine VG.Proof.Aes.Arm.wp_eor (op2_reg _ _) fun s₂ u₂ => ?_
  refine wp_str (a := State.addr Dp + BitVec.ofNat 64 (4 * (8 * g + k))) (by omega)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact ha)
    (by rw [u₂.wr, u₁.wr]; exact hin) fun s₃' u₃ => ?_
  have hst := VG.Proof.Aes.Arm.dataInv_step (v := s.gpr (VG.Impl.Aes.Arm.q (2 * (k % 4) + k / 4))) (by omega) hkn hs.data
    (fun t ht => by rw [hs.keep _ hq hqk]; exact hp.ks k hk t ht)
  have hm : s₃'.mem = VG.Proof.Aes.Arm.xorW s.mem (State.addr Dp + BitVec.ofNat 64 (4 * (8 * g + k)))
      (s.gpr (VG.Impl.Aes.Arm.q (2 * (k % 4) + k / 4))) := by
    rw [u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, u₁.other _ hq, VG.Proof.Aes.Arm.xorW]
  rw [← hm] at hst
  refine h s₃' ⟨by rw [show 8 * g + (k + 1) = 8 * g + k + 1 by omega]; exact hst.1,
    hs.frame.trans hst.2, fun r hr hr' => ?_, ?_, ?_, ?_⟩
  · rw [u₃.gpr, u₂.other _ hr, u₁.other _ hr, hs.keep r hr hr']
  · rw [u₃.rd, u₂.rd, u₁.rd, hs.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr, hs.wr]
  · rw [u₃.sp, u₂.sp, u₁.sp, hs.sp]

/-- After the XOR phase: `r11` is zero if no data is left. -/
def XDone (m₀ : Mem) (Dp : BitVec 32) (n g : Nat) (ks : Nat → Byte) (s₃ s : State) : Prop :=
  Frame [⟨State.addr Dp, 16 * n⟩] s₃.mem s.mem ∧
    (∀ r, r ≠ .lr → r ≠ kp → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₃.gpr r) ∧
    s.rd = s₃.rd ∧ s.wr = s₃.wr ∧ s.sp = s₃.sp ∧
    ((s.gpr .r11 = 0 ∧ VG.Proof.Aes.Arm.DataInv m₀ s.mem (State.addr Dp) n (4 * n) ks) ∨
     (2 * g + 2 < n ∧ VG.Proof.Aes.Arm.DataInv m₀ s.mem (State.addr Dp) n (8 * (g + 1)) ks ∧
      s.gpr .r10 = Dp + BitVec.ofNat 32 (32 * (g + 1)) ∧
      s.gpr .r11 = BitVec.ofNat 32 (n - 2 * (g + 1))))

theorem shr1_eq (x : Nat) (hx : x < 2 ^ 32) :
    (!(BitVec.ofNat 32 x >>> 1 - 0 == 0)) = decide (2 ≤ x) := by
  by_cases h : 2 ≤ x
  · have : BitVec.ofNat 32 x >>> 1 - 0 ≠ 0 := by bv_omega
    simpa [h] using this
  · have : BitVec.ofNat 32 x >>> 1 - 0 = 0 := by bv_omega
    rw [this]; simp [h]

theorem xorPhase_wp (hp : VG.Proof.Aes.Arm.XPre m₀ Dp n g ks s₃) :
    WP isa (.block [.mov kp (lsrOp .r11 1), .cmp kp (.imm 0)]) s₃ fun s =>
      WP isa (.ite .ne (.block xorFull) (.block xorTail)) s (VG.Proof.Aes.Arm.XDone m₀ Dp n g ks s₃) := by
  have hg := hp.hg
  have hn := hp.fit
  refine wp_mov (op2_lsr (by decide)) fun s₄ u₄ => wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ =>
    WP.block_nil ?_
  have ev₅ : Arm.eval .ne s₅ = some (decide (2 ≤ n - 2 * g)) := by
    rw [Arm.eval, z₅, u₄.gpr, hp.r11, VG.Proof.Aes.Arm.shr1_eq _ (by omega)]
  have g₅ : ∀ r, r ≠ kp → s₅.gpr r = s₃.gpr r := fun r hr => by rw [f₅.gpr, u₄.other r hr]
  have x₀ : VG.Proof.Aes.Arm.XS m₀ (State.addr Dp) n g ks s₃ 0 s₅ :=
    ⟨by rw [f₅.mem, u₄.mem]; exact hp.data, by rw [f₅.mem, u₄.mem]; exact Frame.refl _ _,
      fun r _ hr => g₅ r hr, by rw [f₅.rd, u₄.rd], by rw [f₅.wr, u₄.wr], by rw [f₅.sp, u₄.sp]⟩
  refine WP.ite (decide (2 ≤ n - 2 * g)) ev₅ (fun hb => ?_) (fun hb => ?_)
  · -- Two blocks.
    have h2 : 2 ≤ n - 2 * g := by simpa using hb
    rw [VG.Proof.Aes.Arm.xorFull_eq]
    simp only [List.append_assoc]
    refine VG.Proof.Aes.Arm.xs_step hp (k := 0) (by omega) (by omega) x₀ fun s₆ x₆ => ?_
    refine VG.Proof.Aes.Arm.xs_step hp (k := 1) (by omega) (by omega) x₆ fun s₇ x₇ => ?_
    refine VG.Proof.Aes.Arm.xs_step hp (k := 2) (by omega) (by omega) x₇ fun s₈ x₈ => ?_
    refine VG.Proof.Aes.Arm.xs_step hp (k := 3) (by omega) (by omega) x₈ fun s₉ x₉ => ?_
    refine VG.Proof.Aes.Arm.xs_step hp (k := 4) (by omega) (by omega) x₉ fun s₁₀ x₁₀ => ?_
    refine VG.Proof.Aes.Arm.xs_step hp (k := 5) (by omega) (by omega) x₁₀ fun s₁₁ x₁₁ => ?_
    refine VG.Proof.Aes.Arm.xs_step hp (k := 6) (by omega) (by omega) x₁₁ fun s₁₂ x₁₂ => ?_
    refine VG.Proof.Aes.Arm.xs_step hp (k := 7) (by omega) (by omega) x₁₂ fun s₁₃ x₁₃ => ?_
    refine wp_add (op2_imm (by decide)) fun s₁₄ u₁₄ => wp_sub (op2_imm (by decide)) fun s₁₅ u₁₅ =>
      WP.block_nil ⟨by rw [u₁₅.mem, u₁₄.mem]; exact x₁₃.frame, fun r h1 h2 h3 h4 => ?_,
        by rw [u₁₅.rd, u₁₄.rd, x₁₃.rd], by rw [u₁₅.wr, u₁₄.wr, x₁₃.wr], by rw [u₁₅.sp, u₁₄.sp, x₁₃.sp], ?_⟩
    · rw [u₁₅.other _ h4, u₁₄.other _ h3, x₁₃.keep r h1 h2]
    have e₁₀ : s₁₅.gpr .r10 = Dp + BitVec.ofNat 32 (32 * (g + 1)) := by
      rw [u₁₅.other _ (by decide), u₁₄.gpr, x₁₃.keep _ (by decide) (by decide), hp.r10]
      rw [BitVec.add_assoc, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, ← BitVec.ofNat_add]
      congr 2
    have e₁₁ : s₁₅.gpr .r11 = BitVec.ofNat 32 (n - 2 * (g + 1)) := by
      rw [u₁₅.gpr, u₁₄.other _ (by decide), x₁₃.keep _ (by decide) (by decide), hp.r11]
      bv_omega
    have d : VG.Proof.Aes.Arm.DataInv m₀ s₁₅.mem (State.addr Dp) n (8 * (g + 1)) ks := by
      rw [u₁₅.mem, u₁₄.mem]; exact x₁₃.data
    by_cases hl : n - 2 * g = 2
    · refine .inl ⟨by rw [e₁₁, show n - 2 * (g + 1) = 0 by omega]; rfl,
        VG.Proof.Aes.Arm.dataInv_mono d (by omega) (by omega)⟩
    · exact .inr ⟨by omega, d, e₁₀, e₁₁⟩
  · -- The last block.
    have h1 : n - 2 * g = 1 := by simp at hb; omega
    rw [VG.Proof.Aes.Arm.xorTail_eq]
    simp only [List.append_assoc]
    refine VG.Proof.Aes.Arm.xs_step hp (k := 0) (by omega) (by omega) x₀ fun s₆ x₆ => ?_
    refine VG.Proof.Aes.Arm.xs_step hp (k := 1) (by omega) (by omega) x₆ fun s₇ x₇ => ?_
    refine VG.Proof.Aes.Arm.xs_step hp (k := 2) (by omega) (by omega) x₇ fun s₈ x₈ => ?_
    refine VG.Proof.Aes.Arm.xs_step hp (k := 3) (by omega) (by omega) x₈ fun s₉ x₉ => ?_
    refine wp_mov (op2_imm (by decide)) fun s₁₀ u₁₀ =>
      WP.block_nil ⟨by rw [u₁₀.mem]; exact x₉.frame, fun r h1 h2 _ h4 => ?_,
        by rw [u₁₀.rd, x₉.rd], by rw [u₁₀.wr, x₉.wr], by rw [u₁₀.sp, x₉.sp],
        .inl ⟨u₁₀.gpr, ?_⟩⟩
    · rw [u₁₀.other _ h4, x₉.keep r h1 h2]
    · rw [u₁₀.mem]; exact VG.Proof.Aes.Arm.dataInv_mono x₉.data (by omega) (by omega)

end Xor

/-! ## A group -/

/-- What the group loop runs with: `s₂` is the state after the round keys
are bitsliced, `b` the scratch buffer, `Dp` the data (`n` blocks, whose
bytes were `m₀`'s), `icb` the first counter block. -/
structure GSetup (s₂ : State) (b Dp : BitVec 32) (n R : Nat) (w : List Byte) (icb : Spec.Gcm.Block) :
    Prop where
  scr : (⟨State.addr b, 2048⟩ : Region) ∈ s₂.wr
  fit : b.toNat + 2048 ≤ 2 ^ 32
  dat : (⟨State.addr Dp, 16 * n⟩ : Region) ∈ s₂.wr
  fitD : Dp.toNat + 16 * n ≤ 2 ^ 32
  sep : Region.Disjoint ⟨State.addr Dp, 16 * n⟩ ⟨State.addr b, 2048⟩
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  keys : VG.Proof.Aes.Arm.KeysAt s₂.mem (b + BitVec.ofNat 32 (lastKey - 32 * R)) R w
  words : ∀ k < 3, ∀ t < 4, ∀ j < 8,
    (VG.Proof.Aes.Arm.cwW s₂.mem (State.addr b) k).getLsbD (8 * t + j) = icb.getLsbD (8 * (15 - (4 * k + t)) + j)

/-- The memory a group writes: the S-box's slots, slots 44–47 and the data. -/
abbrev gRegions (B D : Addr) (n : Nat) : List Region :=
  [⟨B, 128⟩, ⟨B + BitVec.ofNat 64 176, 16⟩, ⟨D, 16 * n⟩]

/-- Before group `g`. -/
structure GInv (m₀ : Mem) (s₂ : State) (b Dp : BitVec 32) (n R : Nat) (w : List Byte)
    (icb : Spec.Gcm.Block) (g : Nat) (s : State) : Prop where
  hg : 2 * g < n
  r10 : s.gpr .r10 = Dp + BitVec.ofNat 32 (32 * g)
  r11 : s.gpr .r11 = BitVec.ofNat 32 (n - 2 * g)
  r12 : s.gpr .r12 = b + BitVec.ofNat 32 (lastKey - 32 * R)
  base : s.gpr sb = b
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (VG.Proof.Aes.Arm.gRegions (State.addr b) (State.addr Dp) n) s₂.mem s.mem
  num : VG.Proof.Aes.Arm.numW s.mem (State.addr b) = icb.extractLsb' 0 32 + BitVec.ofNat 32 (2 * g)
  data : VG.Proof.Aes.Arm.DataInv m₀ s.mem (State.addr Dp) n (8 * g) (VG.Proof.Aes.Arm.keyStream R w icb)

/-- After the last group. -/
structure GDone (m₀ : Mem) (s₂ : State) (b Dp : BitVec 32) (n R : Nat) (w : List Byte)
    (icb : Spec.Gcm.Block) (s : State) : Prop where
  base : s.gpr sb = b
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (VG.Proof.Aes.Arm.gRegions (State.addr b) (State.addr Dp) n) s₂.mem s.mem
  data : VG.Proof.Aes.Arm.DataInv m₀ s.mem (State.addr Dp) n (4 * n) (VG.Proof.Aes.Arm.keyStream R w icb)

theorem scr_disj (B : Addr) {lx y ly : Nat} (h : lx ≤ y) (hy : y + ly ≤ 2048) :
    Region.Disjoint ⟨B, lx⟩ ⟨B + BitVec.ofNat 64 y, ly⟩ := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have : (BitVec.ofNat 64 y).toNat = y := by simp; omega
  bv_omega

theorem scr_sub (B : Addr) {x lx : Nat} (h : x + lx ≤ 2048) :
    Region.Sub ⟨B + BitVec.ofNat 64 x, lx⟩ ⟨B, 2048⟩ := by
  intro a h₁
  simp only [Region.Contains] at h₁ ⊢
  have : (BitVec.ofNat 64 x).toNat = x := by simp; omega
  bv_omega

theorem keysAt_frame {m m' : Mem} {b : BitVec 32} (hfit : b.toNat + 2048 ≤ 2 ^ 32) {R : Nat}
    {w : List Byte} {rs : List Region} (hR : R ≤ 14) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨State.addr b + 1024, 1024⟩ r)
    (h : VG.Proof.Aes.Arm.KeysAt m (b + BitVec.ofNat 32 (lastKey - 32 * R)) R w) :
    VG.Proof.Aes.Arm.KeysAt m' (b + BitVec.ofNat 32 (lastKey - 32 * R)) R w :=
  fun j hj => VG.Proof.Aes.Arm.keyRel_congr (h j hj) fun k hk => hf.readW (VG.Proof.Aes.Arm.key_contains hfit hR hj hk) hd (by decide)

theorem dataInv_frame {m₀ m m' : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : VG.Proof.Aes.Arm.DataInv m₀ m D n k ks) : VG.Proof.Aes.Arm.DataInv m₀ m' D n k ks := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨D, 16 * n⟩) hd (by simp only; omega) hi

theorem front_frame (m : Mem) (B : Addr) (d l f : BitVec 32) :
    Frame [⟨B + BitVec.ofNat 64 176, 16⟩] m (VG.Proof.Aes.Arm.frontMem m B d l f) := by
  have c : ∀ k, 44 ≤ k → k < 48 →
      (⟨B + BitVec.ofNat 64 176, 16⟩ : Region).Contains (VG.Proof.Aes.Arm.slotA B k) (32 / 8) := by
    intro k h1 h2
    simp only [Region.Contains, VG.Proof.Aes.Arm.slotA]
    rw [show B + BitVec.ofNat 64 (4 * k) - (B + BitVec.ofNat 64 176) = BitVec.ofNat 64 (4 * k - 176) by
      bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  exact ((((Frame.refl _ m).writeW (List.mem_singleton_self _) _ (c 45 (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (c 46 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (c 47 (by omega) (by omega))).writeW (List.mem_singleton_self _) _ (c 44 (by omega) (by omega))

theorem front_read (m : Mem) (B : Addr) (d l f : BitVec 32) :
    (VG.Proof.Aes.Arm.frontMem m B d l f).readW (VG.Proof.Aes.Arm.slotA B dSlot) 32 = d ∧
      (VG.Proof.Aes.Arm.frontMem m B d l f).readW (VG.Proof.Aes.Arm.slotA B lSlot) 32 = l ∧
      (VG.Proof.Aes.Arm.frontMem m B d l f).readW (VG.Proof.Aes.Arm.slotA B fkSlot) 32 = f ∧
      VG.Proof.Aes.Arm.numW (VG.Proof.Aes.Arm.frontMem m B d l f) B = VG.Proof.Aes.Arm.numW m B + 2 := by
  simp only [VG.Proof.Aes.Arm.frontMem, VG.Proof.Aes.Arm.numW]
  refine ⟨?_, ?_, ?_, Mem.readW_writeW_self32 _ _ _⟩
  · rw [VG.Proof.Aes.Arm.readW_writeW_slot _ _ (by decide) (by decide) (by decide),
      VG.Proof.Aes.Arm.readW_writeW_slot _ _ (by decide) (by decide) (by decide),
      VG.Proof.Aes.Arm.readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [VG.Proof.Aes.Arm.readW_writeW_slot _ _ (by decide) (by decide) (by decide),
      VG.Proof.Aes.Arm.readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [VG.Proof.Aes.Arm.readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]

theorem slot_disj_regions {b Dp : BitVec 32} {n : Nat}
    (hsep : Region.Disjoint ⟨State.addr Dp, 16 * n⟩ ⟨State.addr b, 2048⟩) {x lx : Nat}
    (h1 : 128 ≤ x) (h2 : x + lx ≤ 176 ∨ 192 ≤ x) (h3 : x + lx ≤ 2048) :
    ∀ r ∈ VG.Proof.Aes.Arm.gRegions (State.addr b) (State.addr Dp) n,
      Region.Disjoint ⟨State.addr b + BitVec.ofNat 64 x, lx⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (VG.Proof.Aes.Arm.scr_disj _ h1 h3).symm
  · exact off_disjoint _ (by omega) (by omega) (by omega)
  · exact (hsep.sub_right (VG.Proof.Aes.Arm.scr_sub _ h3)).symm

theorem keys_disj_regions {b Dp : BitVec 32} {n : Nat}
    (hsep : Region.Disjoint ⟨State.addr Dp, 16 * n⟩ ⟨State.addr b, 2048⟩) :
    ∀ r ∈ VG.Proof.Aes.Arm.gRegions (State.addr b) (State.addr Dp) n,
      Region.Disjoint ⟨State.addr b + 1024, 1024⟩ r :=
  VG.Proof.Aes.Arm.slot_disj_regions hsep (x := 1024) (lx := 1024) (by omega) (by omega) (by omega)

/-- One group: from before group `g`, to after the last group or before
group `g + 1`. -/
theorem group_ok {m₀ : Mem} {s₂ : State} {b Dp : BitVec 32} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (hs : VG.Proof.Aes.Arm.GSetup s₂ b Dp n R w icb) {g : Nat} {s : State}
    (hi : VG.Proof.Aes.Arm.GInv m₀ s₂ b Dp n R w icb g s) :
    WP isa group s fun s' => (Arm.eval .ne s' = some false ∧ VG.Proof.Aes.Arm.GDone m₀ s₂ b Dp n R w icb s') ∨
      (Arm.eval .ne s' = some true ∧ VG.Proof.Aes.Arm.GInv m₀ s₂ b Dp n R w icb (g + 1) s') := by
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega
  have hfit := hs.fit
  have hfitD := hs.fitD
  have hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr := hi.wr ▸ hs.scr
  unfold group
  refine WP.seq (VG.Proof.Aes.Arm.front_wp hi.base hscr hfit fun s₁ hq₁ hkp₁ o₁ m₁ rd₁ wr₁ sp₁ => ?_)
  have hb₁ : s₁.gpr sb = b := (o₁ sb (by decide) (by decide)).trans hi.base
  have f₁ : Frame [⟨State.addr b + BitVec.ofNat 64 176, 16⟩] s.mem s₁.mem := by
    rw [m₁]; exact VG.Proof.Aes.Arm.front_frame _ _ _ _ _
  have hf₁ : Frame (VG.Proof.Aes.Arm.gRegions (State.addr b) (State.addr Dp) n) s₂.mem s₁.mem :=
    hi.frame.trans (f₁.mono fun r hr => by simp at hr; simp [hr])
  have hcw : ∀ k < 3, VG.Proof.Aes.Arm.cwW s.mem (State.addr b) k = VG.Proof.Aes.Arm.cwW s₂.mem (State.addr b) k := fun k hk =>
    hi.frame.readW (Region.contains_self _ _)
      (VG.Proof.Aes.Arm.slot_disj_regions hs.sep (by simp [cW]; omega) (by simp [cW]; omega) (by simp [cW]; omega))
      (by decide)
  have hp : VG.Proof.Aes.Arm.EncPre s₁ R w :=
    ⟨by rw [hb₁, wr₁, hi.wr]; exact hs.scr, by rw [hb₁]; exact hfit, hs.rounds,
      by rw [hkp₁, hi.r12, hb₁],
      by rw [hkp₁, hi.r12]; exact VG.Proof.Aes.Arm.keysAt_frame hfit hR hf₁ (VG.Proof.Aes.Arm.keys_disj_regions hs.sep) hs.keys⟩
  have hin : VG.Proof.Aes.Arm.InRel (VG.Proof.Aes.Arm.Q s₁) (fun bb => ctrState icb (2 * g + bb)) :=
    VG.Proof.Aes.Arm.ctr_inRel (W := fun k => VG.Proof.Aes.Arm.cwW s.mem (State.addr b) k)
      (fun k hk => by rw [hcw k hk]; exact hs.words k hk) hi.num
      (fun bb hbb => ⟨fun k hk => (hq₁ bb hbb).1 k hk, (hq₁ bb hbb).2⟩)
  refine WP.seq (WP.mono (VG.Proof.Aes.Arm.encrypt2_ok hp hin) fun s₃ ⟨hc₃, hin₃⟩ => ?_)
  have fr₃ := hc₃.frame
  rw [hb₁] at fr₃
  have hb₃ : s₃.gpr sb = b := hc₃.base.trans hb₁
  have hscr₃ : (⟨State.addr b, 2048⟩ : Region) ∈ s₃.wr := by rw [hc₃.wr, wr₁]; exact hscr
  have mslot : ∀ k, 45 ≤ k → k < 48 → s₃.mem.readW (VG.Proof.Aes.Arm.slotA (State.addr b) k) 32 =
      s₁.mem.readW (VG.Proof.Aes.Arm.slotA (State.addr b) k) 32 := fun k h1 h2 =>
    fr₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (VG.Proof.Aes.Arm.scr_disj _ (by omega) (by omega)).symm)
      (by decide)
  obtain ⟨rd10, rd11, rd12, rnum⟩ := VG.Proof.Aes.Arm.front_read s.mem (State.addr b) (s.gpr .r10) (s.gpr .r11)
    (s.gpr .r12)
  refine WP.seq ?_
  simp only [groupLoad, List.cons_append, List.nil_append]
  refine VG.Proof.Aes.Arm.wp_ldS hb₃ hscr₃ hfit (by decide) fun s₄ u₄ => ?_
  refine VG.Proof.Aes.Arm.wp_ldS (by rw [u₄.other _ (by decide), hb₃]) (by rw [u₄.wr]; exact hscr₃) hfit (by decide)
    fun s₅ u₅ => ?_
  refine VG.Proof.Aes.Arm.wp_ldS (by rw [u₅.other _ (by decide), u₄.other _ (by decide), hb₃])
    (by rw [u₅.wr, u₄.wr]; exact hscr₃) hfit (by decide) fun s₆ u₆ => ?_
  have e10 : s₆.gpr .r10 = Dp + BitVec.ofNat 32 (32 * g) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, mslot dSlot (by decide) (by decide), m₁,
      rd10, hi.r10]
  have e11 : s₆.gpr .r11 = BitVec.ofNat 32 (n - 2 * g) := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, mslot lSlot (by decide) (by decide), m₁, rd11, hi.r11]
  have e12 : s₆.gpr .r12 = b + BitVec.ofNat 32 (lastKey - 32 * R) := by
    rw [u₆.gpr, u₅.mem, u₄.mem, mslot fkSlot (by decide) (by decide), m₁, rd12, hi.r12]
  have mm₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  have gq₆ : ∀ i < 8, s₆.gpr (VG.Impl.Aes.Arm.q i) = s₃.gpr (VG.Impl.Aes.Arm.q i) := fun i hi' => by
    have : VG.Impl.Aes.Arm.q i ≠ .r10 ∧ VG.Impl.Aes.Arm.q i ≠ .r11 ∧ VG.Impl.Aes.Arm.q i ≠ .r12 := by revert hi'; revert i; decide
    rw [u₆.other _ this.2.2, u₅.other _ this.2.1, u₄.other _ this.1]
  have d384 : Region.Disjoint ⟨State.addr Dp, 16 * n⟩ ⟨State.addr b, 128⟩ :=
    hs.sep.sub_right (Region.sub_prefix (by omega))
  have hx : VG.Proof.Aes.Arm.XPre m₀ Dp n g (VG.Proof.Aes.Arm.keyStream R w icb) s₆ :=
    { hg := hi.hg, fit := hfitD, dat := by rw [u₆.wr, u₅.wr, u₄.wr, hc₃.wr, wr₁, hi.wr]; exact hs.dat
      r10 := e10, r11 := e11
      data := by
        rw [mm₆]
        refine VG.Proof.Aes.Arm.dataInv_frame fr₃ (by simpa using d384) (by omega)
          (VG.Proof.Aes.Arm.dataInv_frame f₁ (by simpa using hs.sep.sub_right (VG.Proof.Aes.Arm.scr_sub _ (by omega))) (by omega) hi.data)
      ks := fun k hk t ht => by rw [gq₆ _ (by omega)]; exact VG.Proof.Aes.Arm.ks_of_inRel hin₃ hk ht }
  refine WP.mono (VG.Proof.Aes.Arm.xorPhase_wp hx) fun s₇ h₇ => WP.seq (WP.mono h₇ fun s₈ hd₈ => ?_)
  obtain ⟨f₈, o₈, rd₈, wr₈, sp₈, hz⟩ := hd₈
  refine wp_cmp (op2_imm (by decide)) fun s₉ f₉ z₉ => WP.block_nil ?_
  have keep : ∀ r, r ∉ VG.Proof.Aes.Arm.layerWrites → r ≠ kp → s₉.gpr r = s.gpr r := by
    intro r h1 h2
    have : r ≠ .lr ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 := by revert h1 h2; cases r <;> decide
    rw [f₉.gpr, o₈ r this.1 h2 this.2.1 this.2.2.1, u₆.other _ this.2.2.2, u₅.other _ this.2.2.1,
      u₄.other _ this.2.1, hc₃.keep r h1 h2, o₁ r h1 h2]
  have base' : s₉.gpr sb = b := (keep sb (by decide) (by decide)).trans hi.base
  have rd' : s₉.rd = s₂.rd := by rw [f₉.rd, rd₈, u₆.rd, u₅.rd, u₄.rd, hc₃.rd, rd₁, hi.rd]
  have wr' : s₉.wr = s₂.wr := by rw [f₉.wr, wr₈, u₆.wr, u₅.wr, u₄.wr, hc₃.wr, wr₁, hi.wr]
  have sp' : s₉.sp = s₂.sp := by rw [f₉.sp, sp₈, u₆.sp, u₅.sp, u₄.sp, hc₃.sp, sp₁, hi.sp]
  have frame' : Frame (VG.Proof.Aes.Arm.gRegions (State.addr b) (State.addr Dp) n) s₂.mem s₉.mem := by
    rw [f₉.mem]
    refine hf₁.trans ((fr₃.mono fun r hr => by simp at hr; simp [hr]).trans ?_)
    rw [← mm₆]
    exact f₈.mono fun r hr => by simp at hr; simp [hr]
  have ev : Arm.eval .ne s₉ = some (!(s₈.gpr .r11 == 0)) := by
    have e0 : ∀ x : BitVec 32, x - (0 : BitVec 32) = x := fun x => by bv_omega
    simp only [Arm.eval, z₉, e0]
  rcases hz with ⟨z, d⟩ | ⟨h4, d, x10, x11⟩
  · exact .inl ⟨by rw [ev, z]; rfl, base', rd', wr', sp', frame', by rw [f₉.mem]; exact d⟩
  · refine .inr ⟨?_, ⟨by omega, by rw [f₉.gpr]; exact x10, by rw [f₉.gpr]; exact x11,
      by rw [f₉.gpr, o₈ _ (by decide) (by decide) (by decide) (by decide), e12], base', rd', wr', sp',
      frame', ?_, by rw [f₉.mem]; exact d⟩⟩
    · have hne : BitVec.ofNat 32 (n - 2 * (g + 1)) ≠ 0 := by
        intro h; have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        simp at this; omega
      rw [ev, x11]; simpa using hne
    · have e₁ : VG.Proof.Aes.Arm.numW s₈.mem (State.addr b) = VG.Proof.Aes.Arm.numW s₆.mem (State.addr b) :=
        f₈.readW (Region.contains_self _ _)
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (hs.sep.sub_right (VG.Proof.Aes.Arm.scr_sub (x := 176) (lx := 4) _ (by decide))).symm) (by decide)
      rw [f₉.mem]
      have e₂ : VG.Proof.Aes.Arm.numW s₃.mem (State.addr b) = VG.Proof.Aes.Arm.numW s₁.mem (State.addr b) :=
        fr₃.readW (Region.contains_self _ _)
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (VG.Proof.Aes.Arm.scr_disj (lx := 128) (y := 176) (ly := 4) _ (by omega) (by omega)).symm) (by decide)
      rw [e₁, mm₆, e₂, m₁, rnum, hi.num, BitVec.add_assoc]
      congr 1
      bv_omega

/-- The loop over the groups. -/
theorem groups_ok {m₀ : Mem} {s₂ : State} {b Dp : BitVec 32} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (hs : VG.Proof.Aes.Arm.GSetup s₂ b Dp n R w icb) {s : State}
    (hi : VG.Proof.Aes.Arm.GInv m₀ s₂ b Dp n R w icb 0 s) :
    WP isa (.loop group .ne) s (VG.Proof.Aes.Arm.GDone m₀ s₂ b Dp n R w icb) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = n - 2 * g ∧ VG.Proof.Aes.Arm.GInv m₀ s₂ b Dp n R w icb g s)
    (fun k s ⟨g, hk, hg⟩ => WP.mono (VG.Proof.Aes.Arm.group_ok hs hg) fun s' h => ?_) n s ⟨0, by omega, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, n - 2 * (g + 1), by have := hg.hg; omega, g + 1, rfl, d⟩

end VG.Proof.Aes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.Arm.Ctr32`. -/
section

/-!
# AES counter mode on ARMv7: the whole function

The prologue saves the callee-saved registers (checked by evaluation in the
naming domain, as is the epilogue restoring them), copies the counter block
to its slots and writes back the final counter; the key loop
(`Keys.lean`) and the group loop (`Group.lean`) do the rest.
-/

namespace VG.Proof.Aes

open Spec.Gcm

open VG.Arm in
/-- 32-bit ARM contract for `vg_aes_ctr32(schedule = r0, rounds = r1, counter =
r2, data = r3, n = [sp], scratch = [sp, #4])`: XORs the AES counter-mode
keystream from the counter block at `counter` into the `n` blocks at `data`,
and advances the counter block by `n`.

The code may read `schedule` (240 bytes) and the arguments on the stack (8
bytes at `sp`), and read and write `counter` (16 bytes), `data` (`16 n`
bytes) and `scratch` (2048 bytes, whose contents on exit are unspecified).
These may not overlap each other, and none may wrap around the end of the
(32-bit) address space. `rounds` is 10, 12 or 14. The pointers, `rounds` and
`n` are public; the key schedule, the counter block and the data are
secret. -/
def ctr32Arm : Contract Arm.isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 240⟩
    let counter : Region := ⟨State.addr (s.gpr .r2), 16⟩
    let data : Region := ⟨State.addr (s.gpr .r3), 16 * (stackArg s 0).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 2048⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [sched, args] ∧ s.wr = [counter, data, scratch] ∧
    sched.Disjoint counter ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
    counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
    counter.Disjoint args ∧ data.Disjoint args ∧ scratch.Disjoint args ∧
    (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + 16 * (stackArg s 0).toNat ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 2048 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
    ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    let ciph := aesWith (s.gpr .r1).toNat
      (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r0)) (16 * ((s.gpr .r1).toNat + 1)))
    blocksAt s'.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat =
        ctr32 ciph (blockAt s.mem (State.addr (s.gpr .r2)))
          (blocksAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat) ∧
      blockAt s'.mem (State.addr (s.gpr .r2)) =
        Nat.repeat inc32 (stackArg s 0).toNat (blockAt s.mem (State.addr (s.gpr .r2)))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.Aes

namespace VG.Proof.Aes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_cmp wp_rev
  wp_ldr wp_str wp_ldrSp)
open VG.Proof.Aes (ctrBlock_byte toBytes_getD getD_eq byte_ext block_ext toBytes_blockAt blockAt_bit
  toBytes_xor toBytes_ofBytes)

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers the code uses, in the order of `savedRegs`. -/
def sreg : Nat → Reg
  | 0 => .r4 | 1 => .r5 | 2 => .r6 | 3 => .r7 | 4 => .r8 | 5 => .r9 | 6 => .r10 | 7 => .r11
  | _ => .lr

def saveCfg (b : Reg) : Cfg := { base := b, slots := 41, ext := b, exts := 0 }

def saveEnv : Env Nat :=
  { reg := fun r => (List.range 9).find? (fun i => VG.Proof.Aes.Arm.sreg i == r), slot := fun _ => none }

def savePost (e : Env Nat) : Bool := (List.range 9).all fun i => e.slot (32 + i) == some i

theorem save_check12 :
    check (names 32) (VG.Proof.Aes.Arm.saveCfg .r12) (fun _ => none) (saveRegs .r12) VG.Proof.Aes.Arm.saveEnv VG.Proof.Aes.Arm.savePost = true := by
  decide +kernel

theorem save_check8 :
    check (names 32) (VG.Proof.Aes.Arm.saveCfg .r8) (fun _ => none) (saveRegs .r8) VG.Proof.Aes.Arm.saveEnv VG.Proof.Aes.Arm.savePost = true := by
  decide +kernel

def restoreEnv : Env Nat :=
  { reg := fun _ => none, slot := fun k => if 32 ≤ k ∧ k < 41 then some (k - 32) else none }

def restorePost (e : Env Nat) : Bool := (List.range 9).all fun i => e.reg (VG.Proof.Aes.Arm.sreg i) == some i

theorem restore_check :
    check (names 32) (VG.Proof.Aes.Arm.saveCfg .r12) (fun _ => none) (restoreRegs .r12) VG.Proof.Aes.Arm.restoreEnv VG.Proof.Aes.Arm.restorePost = true := by
  decide +kernel

/-- The saved registers are in slots 32–40. -/
def Saved (s₀ : State) (B : Addr) (m : Mem) : Prop :=
  ∀ i < 9, m.readW (VG.Proof.Aes.Arm.slotA B (32 + i)) 32 = s₀.gpr (VG.Proof.Aes.Arm.sreg i)

theorem saveCfg_ok {s : State} {b : BitVec 32} {br : Reg} {L : Nat} (hL : 4 * 41 ≤ L)
    (hw : (⟨State.addr b, L⟩ : Region) ∈ s.wr)
    (hfit : b.toNat + L ≤ 2 ^ 32) (hb : s.gpr br = b) : Ok (VG.Proof.Aes.Arm.saveCfg br) s :=
  Ok.of_off (off := 0) hw hfit (by simp [VG.Proof.Aes.Arm.saveCfg, hb]) (by simp [VG.Proof.Aes.Arm.saveCfg]; omega) rfl

theorem save_ok {s : State} {b : BitVec 32} {br : Reg} {L : Nat} (hL : 4 * 41 ≤ L)
    (hw : (⟨State.addr b, L⟩ : Region) ∈ s.wr) (hfit : b.toNat + L ≤ 2 ^ 32) (hb : s.gpr br = b)
    (hchk : check (names 32) (VG.Proof.Aes.Arm.saveCfg br) (fun _ => none) (saveRegs br) VG.Proof.Aes.Arm.saveEnv VG.Proof.Aes.Arm.savePost = true) :
    ∃ s', runBlock isa (saveRegs br) s = some s' ∧ VG.Proof.Aes.Arm.Saved s (State.addr b) s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨State.addr b, 4 * 41⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  let V : Nat → BitVec 32 := fun i => s.gpr (VG.Proof.Aes.Arm.sreg i)
  have hrel : Rel (NameRel V) (VG.Proof.Aes.Arm.saveCfg br) (fun _ => none) VG.Proof.Aes.Arm.saveEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ hk _ => by simp [VG.Proof.Aes.Arm.saveCfg] at hk),
      (fun _ _ h => by cases h)⟩
    simp only [VG.Proof.Aes.Arm.saveEnv] at h
    have h1 := List.find?_some h
    simp only [beq_iff_eq] at h1; subst h1; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) (VG.Proof.Aes.Arm.saveCfg_ok hL hw hfit hb) hrel he
  refine ⟨s', hs', fun i hi => ?_, funext fun r => p.other r ?_, p.rd, p.wr, p.sp, ?_⟩
  · have := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    simp only [beq_iff_eq] at this
    have h := p.rel.slot (32 + i) i (by simp [VG.Proof.Aes.Arm.saveCfg]; omega) this
    rw [p.base] at h
    simp only [VG.Proof.Aes.Arm.saveCfg, hb] at h
    rw [← VG.Proof.Aes.Arm.slot_addr' hfit (by omega)]
    exact h
  · have : ((saveRegs br).all fun i => dstOf i != some r) = true := by
      simp [saveRegs, savedRegs, dstOf]
    simp [this]
  · have := p.frame
    simpa [slotRegion, VG.Proof.Aes.Arm.saveCfg, hb] using this

theorem restore_ok {s₀ s : State} {b : BitVec 32} {L : Nat} (hL : 4 * 41 ≤ L)
    (hw : (⟨State.addr b, L⟩ : Region) ∈ s.wr) (hfit : b.toNat + L ≤ 2 ^ 32) (hb : s.gpr .r12 = b) (hs : VG.Proof.Aes.Arm.Saved s₀ (State.addr b) s.mem) :
    ∃ s', runBlock isa (restoreRegs .r12) s = some s' ∧ (∀ i < 9, s'.gpr (VG.Proof.Aes.Arm.sreg i) = s₀.gpr (VG.Proof.Aes.Arm.sreg i)) ∧
      Frame [⟨State.addr b, 4 * 41⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.Aes.Arm.restore_check
  let V : Nat → BitVec 32 := fun i => s₀.gpr (VG.Proof.Aes.Arm.sreg i)
  have hrel : Rel (NameRel V) (VG.Proof.Aes.Arm.saveCfg .r12) (fun _ => none) VG.Proof.Aes.Arm.restoreEnv s := by
    refine ⟨(fun r a h => by cases h), fun k a hk h => ?_, (fun _ _ hk _ => by simp [VG.Proof.Aes.Arm.saveCfg] at hk),
      (fun _ _ h => by cases h)⟩
    simp only [VG.Proof.Aes.Arm.restoreEnv] at h
    split at h
    · cases h
      rename_i hk'
      have := hs (k - 32) (by omega)
      rw [show 32 + (k - 32) = k by omega, ← VG.Proof.Aes.Arm.slot_addr' hfit (by simp [VG.Proof.Aes.Arm.saveCfg] at hk; omega)] at this
      simp only [NameRel, VG.Proof.Aes.Arm.saveCfg, hb]
      exact this
    · cases h
  obtain ⟨s', hs', p⟩ := run (names_sound V) (VG.Proof.Aes.Arm.saveCfg_ok hL hw hfit hb) hrel he
  refine ⟨s', hs', fun i hi => ?_, ?_⟩
  · have := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    simp only [beq_iff_eq] at this
    exact p.rel.reg _ i this
  · have := p.frame
    simpa [slotRegion, VG.Proof.Aes.Arm.saveCfg, hb] using this

/-! ## The prologue -/

/-- The memory after the counter part of the prologue: the counter block's
slots, and the final counter written back. -/
def setupMem (m : Mem) (B C : Addr) (N : BitVec 32) : Mem :=
  ((((m.writeW (VG.Proof.Aes.Arm.slotA B (cW 0)) (m.readW C 32)).writeW (VG.Proof.Aes.Arm.slotA B (cW 1))
    (m.readW (C + BitVec.ofNat 64 4) 32)).writeW (VG.Proof.Aes.Arm.slotA B (cW 2))
    (m.readW (C + BitVec.ofNat 64 8) 32)).writeW (VG.Proof.Aes.Arm.slotA B cNum)
    (rev (m.readW (C + BitVec.ofNat 64 12) 32))).writeW (C + BitVec.ofNat 64 12)
    (rev (rev (m.readW (C + BitVec.ofNat 64 12) 32) + N))

/-- What the prologue needs: the scratch buffer at `b`, the counter block
at `c` (16 bytes), disjoint and not wrapping around. -/
structure PSetup (s : State) (b c : BitVec 32) : Prop where
  scr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr
  fit : b.toNat + 2048 ≤ 2 ^ 32
  ctr : (⟨State.addr c, 16⟩ : Region) ∈ s.wr
  fitC : c.toNat + 16 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨State.addr c, 16⟩ ⟨State.addr b, 2048⟩
  args : Region.Disjoint ⟨stackArgAddr s 0, 4⟩ ⟨State.addr b, 2048⟩
  r2 : s.gpr .r2 = c

theorem ctr_addr {c : BitVec 32} (hfit : c.toNat + 16 ≤ 2 ^ 32) {k : Nat} (hk : k < 16) :
    State.addr (c + BitVec.ofNat 32 k) = State.addr c + BitVec.ofNat 64 k := addr_add (by omega)

theorem sep_ctr_slot {b c : BitVec 32} (hd : Region.Disjoint ⟨State.addr c, 16⟩ ⟨State.addr b, 2048⟩)
    {x k : Nat} (hx : x + 4 ≤ 16) (hk : k < 512) :
    Mem.Sep (State.addr c + BitVec.ofNat 64 x) (32 / 8) (VG.Proof.Aes.Arm.slotA (State.addr b) k) (32 / 8) :=
  hd.sep (by
    simp only [Region.Contains]
    rw [show State.addr c + BitVec.ofNat 64 x - State.addr c = BitVec.ofNat 64 x by bv_omega,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega) (by
    simp only [Region.Contains, VG.Proof.Aes.Arm.slotA]
    rw [show State.addr b + BitVec.ofNat 64 (4 * k) - State.addr b = BitVec.ofNat 64 (4 * k) by bv_omega,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega)

/-- The counter part of the prologue. -/
theorem ctrSetup_wp {s : State} {b c : BitVec 32} (hp : VG.Proof.Aes.Arm.PSetup s b c) (hb : s.gpr .r12 = b)
    {is : List Instr} {Q : State → Prop}
    (h : ∀ s', s'.mem = VG.Proof.Aes.Arm.setupMem s.mem (State.addr b) (State.addr c) (stackArg s 0) →
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      WP isa (.block is) s' Q)
    (hsp : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4) :
    WP isa (.block (([.ldr t0 .r2 0, .str t0 .r12 (4 * cW 0), .ldr t0 .r2 4, .str t0 .r12 (4 * cW 1),
      .ldr t0 .r2 8, .str t0 .r12 (4 * cW 2),
      .ldr t0 .r2 12, .rev t0 t0, .str t0 .r12 (4 * cNum),
      .ldrSp t1 0, .dp .add t0 t0 (.reg t1), .rev t0 t0, .str t0 .r2 12] : List Instr) ++ is)) s Q := by
  have hfit := hp.fit
  have hfitC := hp.fitC
  have ca : ∀ {k : Nat}, k < 16 → ∀ s' : State, s'.gpr .r2 = c →
      State.addr (s'.gpr .r2 + BitVec.ofNat 32 k) = State.addr c + BitVec.ofNat 64 k :=
    fun hk s' h => by rw [h]; exact VG.Proof.Aes.Arm.ctr_addr hfitC hk
  have sa : ∀ {k : Nat}, k < 512 → ∀ s' : State, s'.gpr .r12 = b →
      State.addr (s'.gpr .r12 + BitVec.ofNat 32 (4 * k)) = VG.Proof.Aes.Arm.slotA (State.addr b) k :=
    fun hk s' h => by rw [h]; exact VG.Proof.Aes.Arm.slot_addr hfit hk
  have cin : ∀ {x : Nat}, x + 4 ≤ 16 → ∀ rs, (⟨State.addr c, 16⟩ : Region) ∈ rs →
      InRegions rs (State.addr c + BitVec.ofNat 64 x) 4 := fun hx rs hr => by
    rw [← VG.Proof.Aes.Arm.ctr_addr hfitC (by omega)]; exact in_off hr hfitC hx (by omega)
  have sin : ∀ {k : Nat}, k < 512 → InRegions s.wr (VG.Proof.Aes.Arm.slotA (State.addr b) k) 4 :=
    fun hk => VG.Proof.Aes.Arm.slot_in hp.scr hfit hk
  simp only [List.cons_append, List.nil_append]
  refine wp_ldr (by omega) (ca (k := 0) (by omega) s hp.r2) (cin (by omega) _
    (List.mem_append_right _ hp.ctr)) fun s₁ u₁ => ?_
  refine wp_str (by decide) (sa (by decide) s₁ (by rw [u₁.other _ (by decide), hb]))
    (by rw [u₁.wr]; exact sin (by decide)) fun s₂ u₂ => ?_
  have r2₂ : s₂.gpr .r2 = c := by rw [u₂.gpr, u₁.other _ (by decide), hp.r2]
  have r12₂ : s₂.gpr .r12 = b := by rw [u₂.gpr, u₁.other _ (by decide), hb]
  have wr₂ : s₂.wr = s.wr := by rw [u₂.wr, u₁.wr]
  refine wp_ldr (by omega) (ca (k := 4) (by omega) s₂ r2₂) (cin (by omega) _
    (List.mem_append_right _ (wr₂ ▸ hp.ctr))) fun s₃ u₃ => ?_
  refine wp_str (by decide) (sa (by decide) s₃ (by rw [u₃.other _ (by decide), r12₂]))
    (by rw [u₃.wr, wr₂]; exact sin (by decide)) fun s₄ u₄ => ?_
  have r2₄ : s₄.gpr .r2 = c := by rw [u₄.gpr, u₃.other _ (by decide), r2₂]
  have r12₄ : s₄.gpr .r12 = b := by rw [u₄.gpr, u₃.other _ (by decide), r12₂]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, wr₂]
  refine wp_ldr (by omega) (ca (k := 8) (by omega) s₄ r2₄) (cin (by omega) _
    (List.mem_append_right _ (wr₄ ▸ hp.ctr))) fun s₅ u₅ => ?_
  refine wp_str (by decide) (sa (by decide) s₅ (by rw [u₅.other _ (by decide), r12₄]))
    (by rw [u₅.wr, wr₄]; exact sin (by decide)) fun s₆ u₆ => ?_
  have r2₆ : s₆.gpr .r2 = c := by rw [u₆.gpr, u₅.other _ (by decide), r2₄]
  have r12₆ : s₆.gpr .r12 = b := by rw [u₆.gpr, u₅.other _ (by decide), r12₄]
  have wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, wr₄]
  refine wp_ldr (by omega) (ca (k := 12) (by omega) s₆ r2₆) (cin (by omega) _
    (List.mem_append_right _ (wr₆ ▸ hp.ctr))) fun s₇ u₇ => ?_
  refine wp_rev fun s₈ u₈ => ?_
  refine wp_str (by decide) (sa (by decide) s₈ (by rw [u₈.other _ (by decide), u₇.other _ (by decide), r12₆]))
    (by rw [u₈.wr, u₇.wr, wr₆]; exact sin (by decide)) fun s₉ u₉ => ?_
  refine wp_ldrSp (by omega) (a := stackArgAddr s 0) (by
      rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]; simp [stackArgAddr])
    (by rw [u₉.rd, u₉.wr, u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, wr₆]
        rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; exact hsp) fun s₁₀ u₁₀ => ?_
  refine wp_add (op2_reg _ _) fun s₁₁ u₁₁ => ?_
  refine wp_rev fun s₁₂ u₁₂ => ?_
  refine wp_str (by omega) (a := State.addr c + BitVec.ofNat 64 12)
    (by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide)]; exact ca (by omega) s₆ r2₆)
    (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆]; exact cin (by omega) _ hp.ctr)
    fun s₁₃ u₁₃ => h s₁₃ ?_ (fun r h1 h2 => ?_) ?_ ?_ ?_
  · -- The memory.
    have m₂ : s₂.mem = s.mem.writeW (VG.Proof.Aes.Arm.slotA (State.addr b) (cW 0)) (s.mem.readW (State.addr c) 32) := by
      rw [u₂.mem, u₁.gpr, u₁.mem]; simp
    have m₄ : s₄.mem = s₂.mem.writeW (VG.Proof.Aes.Arm.slotA (State.addr b) (cW 1))
        (s.mem.readW (State.addr c + BitVec.ofNat 64 4) 32) := by
      rw [u₄.mem, u₃.gpr, u₃.mem, m₂, Mem.readW_writeW_sep (VG.Proof.Aes.Arm.sep_ctr_slot hp.sep (by omega) (by decide))
        (by decide)]
    have m₆ : s₆.mem = s₄.mem.writeW (VG.Proof.Aes.Arm.slotA (State.addr b) (cW 2))
        (s.mem.readW (State.addr c + BitVec.ofNat 64 8) 32) := by
      rw [u₆.mem, u₅.gpr, u₅.mem, m₄, Mem.readW_writeW_sep (VG.Proof.Aes.Arm.sep_ctr_slot hp.sep (by omega) (by decide))
        (by decide), m₂, Mem.readW_writeW_sep (VG.Proof.Aes.Arm.sep_ctr_slot hp.sep (by omega) (by decide)) (by decide)]
    have w₁₂ : s₆.mem.readW (State.addr c + BitVec.ofNat 64 12) 32 =
        s.mem.readW (State.addr c + BitVec.ofNat 64 12) 32 := by
      rw [m₆, Mem.readW_writeW_sep (VG.Proof.Aes.Arm.sep_ctr_slot hp.sep (by omega) (by decide)) (by decide), m₄,
        Mem.readW_writeW_sep (VG.Proof.Aes.Arm.sep_ctr_slot hp.sep (by omega) (by decide)) (by decide), m₂,
        Mem.readW_writeW_sep (VG.Proof.Aes.Arm.sep_ctr_slot hp.sep (by omega) (by decide)) (by decide)]
    have m₉ : s₉.mem = s₆.mem.writeW (VG.Proof.Aes.Arm.slotA (State.addr b) cNum)
        (rev (s.mem.readW (State.addr c + BitVec.ofNat 64 12) 32)) := by
      rw [u₉.mem, u₈.gpr, u₇.gpr, u₈.mem, u₇.mem, w₁₂]
    have sa0 : ∀ {k : Nat}, k < 512 → Mem.Sep (stackArgAddr s 0) (32 / 8) (VG.Proof.Aes.Arm.slotA (State.addr b) k) (32 / 8) :=
      fun {k} hk => hp.args.sep (Region.contains_self _ _) (by
        simp only [Region.Contains, VG.Proof.Aes.Arm.slotA]
        rw [show State.addr b + BitVec.ofNat 64 (4 * k) - State.addr b = BitVec.ofNat 64 (4 * k) by bv_omega,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        omega)
    have v₁₀ : s₉.mem.readW (stackArgAddr s 0) 32 = stackArg s 0 := by
      rw [m₉, Mem.readW_writeW_sep (sa0 (by decide)) (by decide), m₆,
        Mem.readW_writeW_sep (sa0 (by decide)) (by decide), m₄,
        Mem.readW_writeW_sep (sa0 (by decide)) (by decide), m₂,
        Mem.readW_writeW_sep (sa0 (by decide)) (by decide)]
      rfl
    rw [u₁₃.mem, u₁₂.gpr, u₁₁.gpr, u₁₀.gpr, u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₇.gpr,
      u₁₂.mem, u₁₁.mem, u₁₀.mem, v₁₀, m₉, w₁₂, m₆, m₄, m₂]
    rfl
  · rw [u₁₃.gpr, u₁₂.other _ h1, u₁₁.other _ h1, u₁₀.other _ h2, u₉.gpr, u₈.other _ h1,
      u₇.other _ h1, u₆.gpr, u₅.other _ h1, u₄.gpr, u₃.other _ h1, u₂.gpr, u₁.other _ h1]
  · rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆]
  · rw [u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

section Setup

variable {m : Mem} {b c : BitVec 32} {N : BitVec 32}

theorem c_off (C : Addr) {x n : Nat} (h : x + n ≤ 16) :
    (⟨C, 16⟩ : Region).Contains (C + BitVec.ofNat 64 x) n := by
  simp only [Region.Contains]
  rw [show C + BitVec.ofNat 64 x - C = BitVec.ofNat 64 x by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem s_off {B : Addr} {L : Nat} (hL : L < 2 ^ 64) {k : Nat} (h : 4 * k + 4 ≤ L) :
    (⟨B, L⟩ : Region).Contains (VG.Proof.Aes.Arm.slotA B k) 4 := by
  simp only [Region.Contains, VG.Proof.Aes.Arm.slotA]
  rw [show B + BitVec.ofNat 64 (4 * k) - B = BitVec.ofNat 64 (4 * k) by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem slots_frame (B : Addr) {k : Nat} (h1 : 41 ≤ k) (h2 : k < 45) :
    (⟨B + BitVec.ofNat 64 164, 16⟩ : Region).Contains (VG.Proof.Aes.Arm.slotA B k) (32 / 8) := by
  simp only [Region.Contains, VG.Proof.Aes.Arm.slotA]
  rw [show B + BitVec.ofNat 64 (4 * k) - (B + BitVec.ofNat 64 164) = BitVec.ofNat 64 (4 * k - 164) by
    bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem setup_frame :
    Frame [⟨State.addr b + BitVec.ofNat 64 164, 16⟩, ⟨State.addr c, 16⟩] m
      (VG.Proof.Aes.Arm.setupMem m (State.addr b) (State.addr c) N) := by
  have h₀ : (⟨State.addr b + BitVec.ofNat 64 164, 16⟩ : Region) ∈
      [(⟨State.addr b + BitVec.ofNat 64 164, 16⟩ : Region), ⟨State.addr c, 16⟩] := by simp
  have h₁ : (⟨State.addr c, 16⟩ : Region) ∈
      [(⟨State.addr b + BitVec.ofNat 64 164, 16⟩ : Region), ⟨State.addr c, 16⟩] := by simp
  exact (((((Frame.refl _ _).writeW h₀ _ (VG.Proof.Aes.Arm.slots_frame _ (by decide) (by decide))).writeW h₀ _
    (VG.Proof.Aes.Arm.slots_frame _ (by decide) (by decide))).writeW h₀ _ (VG.Proof.Aes.Arm.slots_frame _ (by decide) (by decide))).writeW
    h₀ _ (VG.Proof.Aes.Arm.slots_frame _ (by decide) (by decide))).writeW h₁ _ (VG.Proof.Aes.Arm.c_off _ (by omega))

theorem setup_cw (hd : Region.Disjoint ⟨State.addr c, 16⟩ ⟨State.addr b, 2048⟩) {k : Nat} (hk : k < 3) :
    VG.Proof.Aes.Arm.cwW (VG.Proof.Aes.Arm.setupMem m (State.addr b) (State.addr c) N) (State.addr b) k =
      m.readW (State.addr c + BitVec.ofNat 64 (4 * k)) 32 := by
  have t : Mem.Sep (VG.Proof.Aes.Arm.slotA (State.addr b) (cW k)) (32 / 8) (State.addr c + BitVec.ofNat 64 12) (32 / 8) :=
    hd.symm.sep (VG.Proof.Aes.Arm.s_off (by decide) (by simp [cW]; omega)) (VG.Proof.Aes.Arm.c_off _ (by omega))
  simp only [VG.Proof.Aes.Arm.cwW, VG.Proof.Aes.Arm.setupMem]
  rw [Mem.readW_writeW_sep t (by decide),
    VG.Proof.Aes.Arm.readW_writeW_slot _ _ (by simp [cW]; omega) (by decide) (by simp [cW, cNum]; omega)]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
  · rw [VG.Proof.Aes.Arm.readW_writeW_slot _ _ (by decide) (by decide) (by decide),
      VG.Proof.Aes.Arm.readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    simp
  · rw [VG.Proof.Aes.Arm.readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

theorem setup_num (hd : Region.Disjoint ⟨State.addr c, 16⟩ ⟨State.addr b, 2048⟩) :
    VG.Proof.Aes.Arm.numW (VG.Proof.Aes.Arm.setupMem m (State.addr b) (State.addr c) N) (State.addr b) =
      rev (m.readW (State.addr c + BitVec.ofNat 64 12) 32) := by
  have t : Mem.Sep (VG.Proof.Aes.Arm.slotA (State.addr b) cNum) (32 / 8) (State.addr c + BitVec.ofNat 64 12) (32 / 8) :=
    hd.symm.sep (VG.Proof.Aes.Arm.s_off (by decide) (by decide)) (VG.Proof.Aes.Arm.c_off _ (by omega))
  simp only [VG.Proof.Aes.Arm.numW, VG.Proof.Aes.Arm.setupMem]
  rw [Mem.readW_writeW_sep t (by decide), Mem.readW_writeW_self32]

theorem writeW_apply {m : Mem} {a x : Addr} {w : Nat} (v : BitVec w) :
    m.writeW a v x = if (x - a).toNat < w / 8 then
      (v.setWidth (8 * (w / 8))).extractLsb' (8 * (x - a).toNat) 8 else m x := rfl

theorem setup_ctr (hd : Region.Disjoint ⟨State.addr c, 16⟩ ⟨State.addr b, 2048⟩) {k : Nat} (hk : k < 16) :
    VG.Proof.Aes.Arm.setupMem m (State.addr b) (State.addr c) N (State.addr c + BitVec.ofNat 64 k) =
      if k < 12 then m (State.addr c + BitVec.ofNat 64 k)
      else (rev (rev (m.readW (State.addr c + BitVec.ofNat 64 12) 32) + N)).extractLsb'
        (8 * (k - 12)) 8 := by
  simp only [VG.Proof.Aes.Arm.setupMem]
  rw [VG.Proof.Aes.Arm.writeW_apply, VG.Proof.Aes.Arm.off_toNat _ (by omega) (by omega)]
  have hx : (⟨State.addr c, 16⟩ : Region).Contains (State.addr c + BitVec.ofNat 64 k) 1 :=
    VG.Proof.Aes.Arm.c_off _ (by omega)
  by_cases h : k < 12
  · rw [ite_eq_right (show ¬ 12 ≤ k by omega), ite_eq_right (show ¬ 2 ^ 64 + k - 12 < 32 / 8 by omega),
      ite_eq_left h, VG.Proof.Aes.Arm.writeW_apply, ite_eq_right (out_of_disj hd hx (VG.Proof.Aes.Arm.s_off (by decide) (by decide))),
      VG.Proof.Aes.Arm.writeW_apply, ite_eq_right (out_of_disj hd hx (VG.Proof.Aes.Arm.s_off (by decide) (by decide))),
      VG.Proof.Aes.Arm.writeW_apply, ite_eq_right (out_of_disj hd hx (VG.Proof.Aes.Arm.s_off (by decide) (by decide))),
      VG.Proof.Aes.Arm.writeW_apply, ite_eq_right (out_of_disj hd hx (VG.Proof.Aes.Arm.s_off (by decide) (by decide)))]
  · rw [ite_eq_left (show 12 ≤ k by omega), ite_eq_left (show k - 12 < 32 / 8 by omega),
      ite_eq_right h, BitVec.setWidth_eq]

end Setup

/-! ## The counter block and the data, as blocks -/

/-- The counter, as the slot holds it. -/
theorem icb_lo (m : Mem) (C : Addr) :
    rev (m.readW (C + BitVec.ofNat 64 12) 32) = (Spec.Gcm.blockAt m C).extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have e : t = 8 * (t / 8) + t % 8 := by omega
  rw [e, rev_bit _ (by omega) (by omega), BitVec.getLsbD_extractLsb', Nat.zero_add,
    decide_eq_true (by omega : 8 * (t / 8) + t % 8 < 32), Bool.true_and,
    show 8 * (t / 8) + t % 8 = 8 * (15 - (15 - t / 8)) + t % 8 by omega,
    blockAt_bit _ _ (by omega) (by omega)]
  have hb := Mem.readW_byte m (C + BitVec.ofNat 64 12) (i := 3 - t / 8) (by omega)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 12 + (3 - t / 8) = 15 - t / 8 by omega] at hb
  rw [hb, BitVec.getLsbD_extractLsb']
  simp [show t % 8 < 8 by omega]

theorem ctr_after {m m' : Mem} {C : Addr} {n : Nat}
    (h : ∀ k < 16, m' (C + BitVec.ofNat 64 k) = if k < 12 then m (C + BitVec.ofNat 64 k)
      else (rev (rev (m.readW (C + BitVec.ofNat 64 12) 32) + BitVec.ofNat 32 n)).extractLsb' (8 * (k - 12)) 8) :
    Spec.Gcm.blockAt m' C = Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt m C) := by
  refine block_ext fun k hk => ?_
  rw [toBytes_blockAt _ _ hk, h k hk, ctrBlock_byte _ _ hk]
  split
  · rw [toBytes_blockAt _ _ hk]
  · rw [VG.Proof.Aes.Arm.icb_lo]
    refine byte_ext fun j hj => ?_
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', rev_bit _ (by omega) hj]
    simp only [hj, decide_true, Bool.true_and]
    congr 1; omega

theorem ctr32_of_dataInv {m₀ m : Mem} {D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (h : VG.Proof.Aes.Arm.DataInv m₀ m D n (4 * n) (VG.Proof.Aes.Arm.keyStream R w icb)) :
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
  rw [toBytes_ofBytes (by simp) hk, VG.Proof.Aes.Arm.keyStream, show (16 * i + k) / 16 = i by omega,
    show (16 * i + k) % 16 = k by omega, getD_eq _ hk, List.getD_eq_getElem?_getD,
    Vector.getElem?_toList, Vector.getElem?_eq_getElem hk, Option.getD_some]
  rfl

/-! ## The whole function -/

section
variable (s₀ : State)

abbrev scP : BitVec 32 := s₀.gpr .r0
abbrev ctP : BitVec 32 := s₀.gpr .r2
abbrev dP : BitVec 32 := s₀.gpr .r3
abbrev nB : Nat := (stackArg s₀ 0).toNat
abbrev bP : BitVec 32 := stackArg s₀ 1
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 8⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨State.addr (VG.Proof.Aes.Arm.scP s₀), 240⟩, VG.Proof.Aes.Arm.argR s₀]
  wr : s₀.wr = [⟨State.addr (VG.Proof.Aes.Arm.ctP s₀), 16⟩, ⟨State.addr (VG.Proof.Aes.Arm.dP s₀), 16 * VG.Proof.Aes.Arm.nB s₀⟩, ⟨State.addr (VG.Proof.Aes.Arm.bP s₀), 2048⟩]
  dSC : Region.Disjoint ⟨State.addr (VG.Proof.Aes.Arm.scP s₀), 240⟩ ⟨State.addr (VG.Proof.Aes.Arm.ctP s₀), 16⟩
  dSD : Region.Disjoint ⟨State.addr (VG.Proof.Aes.Arm.scP s₀), 240⟩ ⟨State.addr (VG.Proof.Aes.Arm.dP s₀), 16 * VG.Proof.Aes.Arm.nB s₀⟩
  dSS : Region.Disjoint ⟨State.addr (VG.Proof.Aes.Arm.scP s₀), 240⟩ ⟨State.addr (VG.Proof.Aes.Arm.bP s₀), 2048⟩
  dCD : Region.Disjoint ⟨State.addr (VG.Proof.Aes.Arm.ctP s₀), 16⟩ ⟨State.addr (VG.Proof.Aes.Arm.dP s₀), 16 * VG.Proof.Aes.Arm.nB s₀⟩
  dCS : Region.Disjoint ⟨State.addr (VG.Proof.Aes.Arm.ctP s₀), 16⟩ ⟨State.addr (VG.Proof.Aes.Arm.bP s₀), 2048⟩
  dDS : Region.Disjoint ⟨State.addr (VG.Proof.Aes.Arm.dP s₀), 16 * VG.Proof.Aes.Arm.nB s₀⟩ ⟨State.addr (VG.Proof.Aes.Arm.bP s₀), 2048⟩
  dCA : Region.Disjoint ⟨State.addr (VG.Proof.Aes.Arm.ctP s₀), 16⟩ (VG.Proof.Aes.Arm.argR s₀)
  dDA : Region.Disjoint ⟨State.addr (VG.Proof.Aes.Arm.dP s₀), 16 * VG.Proof.Aes.Arm.nB s₀⟩ (VG.Proof.Aes.Arm.argR s₀)
  dSA : Region.Disjoint ⟨State.addr (VG.Proof.Aes.Arm.bP s₀), 2048⟩ (VG.Proof.Aes.Arm.argR s₀)
  fitS : (VG.Proof.Aes.Arm.scP s₀).toNat + 240 ≤ 2 ^ 32
  fitC : (VG.Proof.Aes.Arm.ctP s₀).toNat + 16 ≤ 2 ^ 32
  fitD : (VG.Proof.Aes.Arm.dP s₀).toNat + 16 * VG.Proof.Aes.Arm.nB s₀ ≤ 2 ^ 32
  fitB : (VG.Proof.Aes.Arm.bP s₀).toNat + 2048 ≤ 2 ^ 32
  fitSp : s₀.sp.toNat + 8 ≤ 2 ^ 32
  rounds : (s₀.gpr .r1).toNat = 10 ∨ (s₀.gpr .r1).toNat = 12 ∨ (s₀.gpr .r1).toNat = 14

theorem pre_of {s₀ : State} (h : Proof.Aes.ctr32Arm.pre s₀) : VG.Proof.Aes.Arm.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem argAddr_one (s : State) (h : s.sp.toNat + 8 ≤ 2 ^ 32) :
    stackArgAddr s 1 = stackArgAddr s 0 + BitVec.ofNat 64 4 := by
  simp only [stackArgAddr]
  rw [show (4 * 0 : Nat) = 0 from rfl, BitVec.add_zero, addr_add (by omega)]

theorem arg_in {s : State} (hsp : s.sp.toNat + 8 ≤ 2 ^ 32) (hr : VG.Proof.Aes.Arm.argR s ∈ s.rd) {i : Nat} (hi : i < 2) :
    InRegions (s.rd ++ s.wr) (stackArgAddr s i) 4 := by
  refine ⟨VG.Proof.Aes.Arm.argR s, List.mem_append_left _ hr, ?_⟩
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · simp [Region.Contains]
  · rw [VG.Proof.Aes.Arm.argAddr_one s hsp]
    simp only [Region.Contains]
    rw [show stackArgAddr s 0 + BitVec.ofNat 64 4 - stackArgAddr s 0 = BitVec.ofNat 64 4 by bv_omega]
    decide

/-- The stack arguments are as on entry. -/
theorem stackArg_frame {s s' : State} {rs : List Region} (hf : Frame rs s.mem s'.mem) (hsp : s'.sp = s.sp)
    (h8 : s.sp.toNat + 8 ≤ 2 ^ 32) (hd : ∀ r ∈ rs, Region.Disjoint (VG.Proof.Aes.Arm.argR s) r) {i : Nat} (hi : i < 2) :
    stackArg s' i = stackArg s i := by
  simp only [stackArg, stackArgAddr, hsp]
  refine hf.readW ?_ hd (by decide)
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · simp [Region.Contains, stackArgAddr]
  · have := VG.Proof.Aes.Arm.argAddr_one s h8
    simp only [stackArgAddr] at this
    rw [show 4 * 1 = 4 from rfl, this]
    simp only [Region.Contains, stackArgAddr]
    rw [show State.addr (s.sp + BitVec.ofNat 32 (4 * 0)) + BitVec.ofNat 64 4 -
      State.addr (s.sp + BitVec.ofNat 32 (4 * 0)) = BitVec.ofNat 64 4 by bv_omega]
    decide

theorem shl4 (x : BitVec 32) : x <<< 4 = BitVec.ofNat 32 (16 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem off_disjoint' (B : Addr) {x lx y ly : Nat} (h : x + lx ≤ y ∨ y + ly ≤ x)
    (hx : x + lx < 2 ^ 64) (hy : y + ly < 2 ^ 64) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 x, lx⟩ ⟨B + BitVec.ofNat 64 y, ly⟩ := off_disjoint B h hx hy

theorem sub_scr (B : Addr) {x lx : Nat} (h : x + lx ≤ 2048) :
    Region.Sub ⟨B + BitVec.ofNat 64 x, lx⟩ ⟨B, 2048⟩ := VG.Proof.Aes.Arm.scr_sub B h

theorem keyArea_sub (b : BitVec 32) : Region.Sub (VG.Proof.Aes.Arm.keyArea b) ⟨State.addr b, 2048⟩ := VG.Proof.Aes.Arm.sub_scr _ (by omega)

theorem correct {s₀ : State} (hp : VG.Proof.Aes.Arm.Pre s₀) :
    WP isa Impl.Aes.Arm.ctr32 s₀ fun s' =>
      (∀ i < 9, s'.gpr (VG.Proof.Aes.Arm.sreg i) = s₀.gpr (VG.Proof.Aes.Arm.sreg i)) ∧ Proof.Aes.ctr32Arm.post s₀ s' := by
  have hR14 : (s₀.gpr .r1).toNat ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hfit := hp.fitB
  have hwS : (⟨State.addr (VG.Proof.Aes.Arm.bP s₀), 2048⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have hwC : (⟨State.addr (VG.Proof.Aes.Arm.ctP s₀), 16⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have hwD : (⟨State.addr (VG.Proof.Aes.Arm.dP s₀), 16 * VG.Proof.Aes.Arm.nB s₀⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have hrS : (⟨State.addr (VG.Proof.Aes.Arm.scP s₀), 240⟩ : Region) ∈ s₀.rd := by rw [hp.rd]; simp
  have hrA : VG.Proof.Aes.Arm.argR s₀ ∈ s₀.rd := by rw [hp.rd]; simp
  let b := VG.Proof.Aes.Arm.bP s₀
  let B := State.addr b
  -- The prologue.
  unfold Impl.Aes.Arm.ctr32
  refine WP.seq ?_
  simp only [VG.Impl.Aes.Arm.prologue, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldrSp (by omega) (a := stackArgAddr s₀ 1) rfl (VG.Proof.Aes.Arm.arg_in hp.fitSp hrA (by omega))
    fun s₁ u₁ => ?_
  have hb₁ : s₁.gpr .r12 = b := u₁.gpr
  rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₂, h₂, sv₂, g₂, rd₂, wr₂, sp₂, f₂⟩ := VG.Proof.Aes.Arm.save_ok (by decide) (by rw [u₁.wr]; exact hwS) hfit hb₁ VG.Proof.Aes.Arm.save_check12
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  have sv₂' : VG.Proof.Aes.Arm.Saved s₀ B s₂.mem := fun i hi => by
    rw [sv₂ i hi]
    have : VG.Proof.Aes.Arm.sreg i ≠ .r12 := by revert hi; revert i; decide
    exact u₁.other _ this
  have f₀₂ : Frame [⟨B, 4 * 41⟩] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  have sp₂' : s₂.sp = s₀.sp := by rw [sp₂, u₁.sp]
  have argD : ∀ {x lx : Nat}, x + lx ≤ 2048 →
      Region.Disjoint (VG.Proof.Aes.Arm.argR s₀) ⟨State.addr (VG.Proof.Aes.Arm.bP s₀) + BitVec.ofNat 64 x, lx⟩ := fun h =>
    (hp.dSA.sub_left (VG.Proof.Aes.Arm.sub_scr _ h)).symm
  have argB : ∀ {lx : Nat}, lx ≤ 2048 → Region.Disjoint (VG.Proof.Aes.Arm.argR s₀) ⟨State.addr (VG.Proof.Aes.Arm.bP s₀), lx⟩ := fun h =>
    (hp.dSA.sub_left (Region.sub_prefix h)).symm
  have arg₂ : ∀ i < 2, stackArg s₂ i = stackArg s₀ i := fun i hi =>
    VG.Proof.Aes.Arm.stackArg_frame f₀₂ sp₂' hp.fitSp (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact argB (by omega)) hi
  have ps : VG.Proof.Aes.Arm.PSetup s₂ b (VG.Proof.Aes.Arm.ctP s₀) :=
    { scr := by rw [wr₂, u₁.wr]; exact hwS
      fit := hfit
      ctr := by rw [wr₂, u₁.wr]; exact hwC
      fitC := hp.fitC
      sep := hp.dCS
      args := by
        simp only [stackArgAddr, sp₂']
        exact (argB (lx := 2048) (by omega)).sub_left (Region.sub_prefix (by omega))
      r2 := by rw [g₂, u₁.other _ (by decide)] }
  refine VG.Proof.Aes.Arm.ctrSetup_wp ps (by rw [g₂, hb₁]) (fun s₃ m₃ o₃ rd₃ wr₃ sp₃ => ?_)
    (by rw [rd₂, wr₂, u₁.rd, u₁.wr]; simp only [stackArgAddr, sp₂']
        exact VG.Proof.Aes.Arm.arg_in hp.fitSp hrA (i := 0) (by omega))
  -- The key loop's setup.
  have r0₃ : s₃.gpr .r0 = VG.Proof.Aes.Arm.scP s₀ := by rw [o₃ _ (by decide) (by decide), g₂, u₁.other _ (by decide)]
  have r1₃ : s₃.gpr .r1 = s₀.gpr .r1 := by rw [o₃ _ (by decide) (by decide), g₂, u₁.other _ (by decide)]
  have r3₃ : s₃.gpr .r3 = VG.Proof.Aes.Arm.dP s₀ := by rw [o₃ _ (by decide) (by decide), g₂, u₁.other _ (by decide)]
  have r12₃ : s₃.gpr .r12 = b := by rw [o₃ _ (by decide) (by decide), g₂, hb₁]
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_add (VG.Proof.MdStream.Arm.op2_lsl (by decide))
    fun s₅ u₅ => wp_add (op2_imm (by decide)) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ =>
    WP.block_nil ?_
  have m₇ : s₇.mem = s₃.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, rd₂, u₁.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, wr₂, u₁.wr]
  have sp₇ : s₇.sp = s₀.sp := by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, sp₃, sp₂']
  let R := (s₀.gpr .r1).toNat
  let w := Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.Aes.Arm.scP s₀)) (16 * (R + 1))
  have f₂₃ : Frame [⟨B + BitVec.ofNat 64 164, 16⟩, ⟨State.addr (VG.Proof.Aes.Arm.ctP s₀), 16⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact VG.Proof.Aes.Arm.setup_frame
  have f₀₇ : Frame [⟨B, 2048⟩, ⟨State.addr (VG.Proof.Aes.Arm.ctP s₀), 16⟩] s₀.mem s₇.mem := by
    rw [m₇]
    refine (f₀₂.sub fun r hr => ⟨⟨B, 2048⟩, by simp, ?_⟩).trans (f₂₃.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨B, 2048⟩, by simp, VG.Proof.Aes.Arm.sub_scr _ (by omega)⟩
      · exact ⟨⟨State.addr (VG.Proof.Aes.Arm.ctP s₀), 16⟩, by simp, fun _ h => h⟩
  have hk : VG.Proof.Aes.Arm.KSetup s₇ b (VG.Proof.Aes.Arm.scP s₀) R w :=
    { scr := by rw [wr₇]; exact hwS
      fit := hfit
      sch := List.mem_append_left _ (by rw [rd₇]; exact hrS)
      fitS := hp.fitS
      sep := hp.dSS
      rounds := hR14
      w := fun i hi => by
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        refine (f₀₇.bytes (R := ⟨State.addr (VG.Proof.Aes.Arm.scP s₀), 240⟩) (fun r hr => ?_) (by simp)
          (by simp only; omega)).symm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.dSS
        · exact hp.dSC }
  have hi₇ : VG.Proof.Aes.Arm.KInv s₇ b (VG.Proof.Aes.Arm.scP s₀) R w R s₇ :=
    { hj := Nat.le_refl _
      r12 := by
        rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), r0₃,
          u₄.other _ (by decide), r1₃, VG.Proof.Aes.Arm.shl4]
      kp := by
        rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, r12₃]
        simp [VG.Proof.Aes.Arm.keyAddr, lastKey]
      rd := rfl
      wr := rfl
      sp := rfl
      keep := fun _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega) }
  have r8₇ : s₇.gpr .r8 = VG.Proof.Aes.Arm.dP s₀ := by rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
    u₄.other _ (by decide), r3₃]
  -- The key loop.
  have lr₇ : s₇.gpr .lr = BitVec.ofNat 32 (R + 1) := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), r1₃]
    simp only [R]; bv_omega
  refine WP.seq (WP.mono (VG.Proof.Aes.Arm.keyLoop_ok hk hi₇ lr₇) fun s₈ d₈ => ?_)
  have f₀₈ : Frame [⟨B, 2048⟩, ⟨State.addr (VG.Proof.Aes.Arm.ctP s₀), 16⟩] s₀.mem s₈.mem :=
    f₀₇.trans (d₈.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨B, 2048⟩, by simp, VG.Proof.Aes.Arm.keyArea_sub _⟩)
  have argv : ∀ (s : State), s.sp = s₀.sp →
      Frame [⟨B, 2048⟩, ⟨State.addr (VG.Proof.Aes.Arm.ctP s₀), 16⟩] s₀.mem s.mem →
      ∀ i < 2, s.mem.readW (stackArgAddr s₀ i) 32 = stackArg s₀ i := fun s hsp hf i hi => by
    have := VG.Proof.Aes.Arm.stackArg_frame hf hsp hp.fitSp (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact argB (by omega)
      · exact hp.dCA.symm) hi
    simp only [stackArg, stackArgAddr, hsp] at this
    exact this
  -- After the key loop.
  refine WP.seq ?_
  simp only [keyDone, List.cons_append, List.nil_append]
  have sp₈ : s₈.sp = s₀.sp := by rw [d₈.sp, sp₇]
  refine wp_add (op2_imm (by decide)) fun s₉ u₉ => wp_mov (op2_reg _ _) fun s₁₀ u₁₀ => ?_
  have sp₁₀ : s₁₀.sp = s₀.sp := by rw [u₁₀.sp, u₉.sp, sp₈]
  have rd₁₀ : s₁₀.rd = s₀.rd := by rw [u₁₀.rd, u₉.rd, d₈.rd, rd₇]
  have wr₁₀ : s₁₀.wr = s₀.wr := by rw [u₁₀.wr, u₉.wr, d₈.wr, wr₇]
  have m₁₀ : s₁₀.mem = s₈.mem := by rw [u₁₀.mem, u₉.mem]
  refine wp_ldrSp (by omega) (a := stackArgAddr s₀ 0) (by simp [stackArgAddr, sp₁₀])
    (by rw [rd₁₀, wr₁₀]; exact VG.Proof.Aes.Arm.arg_in hp.fitSp hrA (by omega)) fun s₁₁ u₁₁ => ?_
  refine wp_ldrSp (by omega) (a := stackArgAddr s₀ 1) (by simp [stackArgAddr, u₁₁.sp, sp₁₀])
    (by rw [u₁₁.rd, u₁₁.wr, rd₁₀, wr₁₀]; exact VG.Proof.Aes.Arm.arg_in hp.fitSp hrA (by omega)) fun s₁₂ u₁₂ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₁₃ f₁₃ z₁₃ => WP.block_nil ?_
  have n₁₂ : s₁₂.gpr .r11 = stackArg s₀ 0 := by
    rw [u₁₂.other _ (by decide), u₁₁.gpr, m₁₀, argv s₈ sp₈ f₀₈ 0 (by omega)]
  have n₁₃ : s₁₃.gpr .r11 = stackArg s₀ 0 := by rw [f₁₃.gpr, n₁₂]
  have b₁₃ : s₁₃.gpr sb = b := by
    rw [f₁₃.gpr, u₁₂.gpr, u₁₁.mem, m₁₀, argv s₈ sp₈ f₀₈ 1 (by omega)]
  have d₁₃ : s₁₃.gpr .r10 = VG.Proof.Aes.Arm.dP s₀ := by
    rw [f₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      d₈.keep _ (by decide), r8₇]
  have k₁₃ : s₁₃.gpr .r12 = b + BitVec.ofNat 32 (lastKey - 32 * R) := by
    rw [f₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr,
      d₈.kp]
    simp only [VG.Proof.Aes.Arm.keyAddr, Nat.sub_zero, BitVec.sub_add_cancel]
  have m₁₃ : s₁₃.mem = s₈.mem := by rw [f₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀]
  have rd₁₃ : s₁₃.rd = s₀.rd := by rw [f₁₃.rd, u₁₂.rd, u₁₁.rd, rd₁₀]
  have wr₁₃ : s₁₃.wr = s₀.wr := by rw [f₁₃.wr, u₁₂.wr, u₁₁.wr, wr₁₀]
  have sp₁₃ : s₁₃.sp = s₀.sp := by rw [f₁₃.sp, u₁₂.sp, u₁₁.sp, sp₁₀]
  -- The counter block's slots.
  have fK : Frame [VG.Proof.Aes.Arm.keyArea b] s₃.mem s₁₃.mem := by rw [m₁₃, ← m₇]; exact d₈.frame
  have kd : ∀ {x lx : Nat}, x + lx ≤ 1024 → ∀ r ∈ [VG.Proof.Aes.Arm.keyArea b],
      Region.Disjoint ⟨B + BitVec.ofNat 64 x, lx⟩ r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact off_disjoint _ (by omega) (by omega) (by omega)
  have cd : ∀ {x lx : Nat}, x + lx ≤ 16 → ∀ r ∈ [(⟨B, 4 * 41⟩ : Region)],
      Region.Disjoint ⟨State.addr (VG.Proof.Aes.Arm.ctP s₀) + BitVec.ofNat 64 x, lx⟩ r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    refine (hp.dCS.sub_right (Region.sub_prefix (by omega))).sub_left ?_
    exact VG.Proof.MdStream.Arm.sub_offset h (by omega)
  let icb := Spec.Gcm.blockAt s₀.mem (State.addr (VG.Proof.Aes.Arm.ctP s₀))
  let n := VG.Proof.Aes.Arm.nB s₀
  have cw₁₃ : ∀ k < 3, VG.Proof.Aes.Arm.cwW s₁₃.mem B k = s₀.mem.readW (State.addr (VG.Proof.Aes.Arm.ctP s₀) + BitVec.ofNat 64 (4 * k)) 32 := by
    intro k hk
    rw [VG.Proof.Aes.Arm.cwW, fK.readW (Region.contains_self _ _) (kd (by simp [cW]; omega)) (by decide), ← VG.Proof.Aes.Arm.cwW, m₃,
      VG.Proof.Aes.Arm.setup_cw hp.dCS hk, f₀₂.readW (Region.contains_self _ _) (cd (by omega)) (by decide)]
  have num₁₃ : VG.Proof.Aes.Arm.numW s₁₃.mem B = rev (s₀.mem.readW (State.addr (VG.Proof.Aes.Arm.ctP s₀) + BitVec.ofNat 64 12) 32) := by
    rw [VG.Proof.Aes.Arm.numW, fK.readW (Region.contains_self _ _) (kd (by decide)) (by decide), ← VG.Proof.Aes.Arm.numW, m₃,
      VG.Proof.Aes.Arm.setup_num hp.dCS, f₀₂.readW (Region.contains_self _ _) (cd (by omega)) (by decide)]
  have hs : VG.Proof.Aes.Arm.GSetup s₁₃ b (VG.Proof.Aes.Arm.dP s₀) n R w icb :=
    { scr := by rw [wr₁₃]; exact hwS
      fit := hfit
      dat := by rw [wr₁₃]; exact hwD
      fitD := hp.fitD
      sep := hp.dDS
      rounds := hp.rounds
      keys := fun j hj => VG.Proof.Aes.Arm.keyRel_congr (d₈.keys j hj) fun k hk => by
        rw [m₁₃, VG.Proof.Aes.Arm.keyAddr, add_ofNat_ofNat, show lastKey - 32 * R + 32 * j = lastKey - 32 * (R - j) by
          simp only [lastKey]; omega]
      words := fun k hk t ht j hj => by
        rw [cw₁₃ k hk, readW_bit _ _ ht hj, BitVec.add_assoc, ← BitVec.ofNat_add,
          blockAt_bit _ _ (by omega) hj] }
  -- The data is as on entry.
  have data₁₃ : VG.Proof.Aes.Arm.DataInv s₀.mem s₁₃.mem (State.addr (VG.Proof.Aes.Arm.dP s₀)) n 0 (VG.Proof.Aes.Arm.keyStream R w icb) := by
    intro i hi
    simp only [Nat.mul_zero, Nat.not_lt_zero, ite_false]
    have xz : ∀ x : Byte, x ^^^ 0 = x := fun x => by ext i; simp
    rw [m₁₃, xz]
    refine f₀₈.bytes (R := ⟨State.addr (VG.Proof.Aes.Arm.dP s₀), 16 * n⟩) (fun r hr => ?_)
      (by simp only; have := hp.fitD; omega) hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dDS
    · exact hp.dCD.symm
  refine WP.seq (WP.mono (Q := VG.Proof.Aes.Arm.GDone s₀.mem s₁₃ b (VG.Proof.Aes.Arm.dP s₀) n R w icb) ?_ fun s₁₄ gd => ?_)
  · have e0 : ∀ x : BitVec 32, x - (0 : BitVec 32) = x := fun x => by bv_omega
    refine WP.ite (stackArg s₀ 0 == 0) (by simp only [Arm.eval, z₁₃, n₁₂, e0]) (fun h0 => ?_)
      (fun h0 => ?_)
    · have hn0 : n = 0 := by
        simp only [beq_iff_eq] at h0; show (stackArg s₀ 0).toNat = 0; rw [h0]; rfl
      exact WP.block_nil ⟨b₁₃, rfl, rfl, rfl, Frame.refl _ _, fun i hi => by omega⟩
    · have hn0 : n ≠ 0 := by
        simp only [beq_eq_false_iff_ne, ne_eq] at h0
        intro h; apply h0; exact BitVec.eq_of_toNat_eq (by simpa [n] using h)
      refine VG.Proof.Aes.Arm.groups_ok hs ⟨by omega, by rw [d₁₃]; simp, ?_, k₁₃, b₁₃, rfl, rfl, rfl, Frame.refl _ _,
        by rw [num₁₃, VG.Proof.Aes.Arm.icb_lo]; simp [icb], data₁₃⟩
      rw [n₁₃]; simp only [n, VG.Proof.Aes.Arm.nB, Nat.mul_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- The epilogue.
  have sv : VG.Proof.Aes.Arm.Saved s₀ B s₁₄.mem := by
    intro i hi
    have c : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
        (∀ r ∈ rs, Region.Disjoint ⟨VG.Proof.Aes.Arm.slotA B (32 + i), 32 / 8⟩ r) →
        m'.readW (VG.Proof.Aes.Arm.slotA B (32 + i)) 32 = m.readW (VG.Proof.Aes.Arm.slotA B (32 + i)) 32 :=
      fun hf hd => hf.readW (Region.contains_self _ _) hd (by decide)
    rw [c gd.frame (VG.Proof.Aes.Arm.slot_disj_regions hp.dDS (by omega) (by omega) (by omega)), m₁₃,
      c d₈.frame (kd (by omega)), m₇, c f₂₃ ?_, sv₂' i hi]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact off_disjoint _ (by omega) (by omega) (by omega)
    · exact (hp.dCS.sub_right (VG.Proof.Aes.Arm.sub_scr (x := 4 * (32 + i)) (lx := 32 / 8) _ (by omega))).symm
  refine wp_ldrSp (by omega) (a := stackArgAddr s₀ 1) (by simp [stackArgAddr, gd.sp, sp₁₃])
    (by rw [gd.rd, gd.wr, rd₁₃, wr₁₃]; exact VG.Proof.Aes.Arm.arg_in hp.fitSp hrA (by omega)) fun s₁₅ u₁₅ => ?_
  have f₀₁₄ : Frame [⟨B, 2048⟩, ⟨State.addr (VG.Proof.Aes.Arm.ctP s₀), 16⟩, ⟨State.addr (VG.Proof.Aes.Arm.dP s₀), 16 * n⟩]
      s₀.mem s₁₄.mem := by
    refine (f₀₈.mono fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp).trans ?_
    rw [← m₁₃]
    refine gd.frame.sub fun r hr => ?_
    simp only [VG.Proof.Aes.Arm.gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨B, 2048⟩, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨B, 2048⟩, by simp, VG.Proof.Aes.Arm.sub_scr _ (by omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have b₁₅ : s₁₅.gpr .r12 = b := by
    rw [u₁₅.gpr]
    have := VG.Proof.Aes.Arm.stackArg_frame f₀₁₄ (by rw [gd.sp, sp₁₃]) hp.fitSp (i := 1) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact argB (by omega)
      · exact hp.dCA.symm
      · exact hp.dDA.symm) (by omega)
    simp only [stackArg, stackArgAddr, gd.sp, sp₁₃] at this
    exact this
  obtain ⟨s₁₆, h₁₆, rg₁₆, fR⟩ := VG.Proof.Aes.Arm.restore_ok (s₀ := s₀) (by decide) (by rw [u₁₅.wr, gd.wr, wr₁₃]; exact hwS) hfit
    b₁₅ (by rw [u₁₅.mem]; exact sv)
  refine WP.of_runBlock ⟨s₁₆, h₁₆, rg₁₆, ?_, ?_⟩
  · -- The data.
    rw [u₁₅.mem] at fR
    exact VG.Proof.Aes.Arm.ctr32_of_dataInv (VG.Proof.Aes.Arm.dataInv_frame fR (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.dDS.sub_right (Region.sub_prefix (by omega))) (by have := hp.fitD; omega) gd.data)
  · -- The counter block.
    rw [u₁₅.mem] at fR
    refine VG.Proof.Aes.Arm.ctr_after fun k hk => ?_
    have hC : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
        (∀ r ∈ rs, Region.Disjoint ⟨State.addr (VG.Proof.Aes.Arm.ctP s₀), 16⟩ r) →
        m' (State.addr (VG.Proof.Aes.Arm.ctP s₀) + BitVec.ofNat 64 k) = m (State.addr (VG.Proof.Aes.Arm.ctP s₀) + BitVec.ofNat 64 k) :=
      fun hf hd => hf.bytes hd (by simp) hk
    rw [hC fR (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.dCS.sub_right (Region.sub_prefix (by omega))),
      hC gd.frame (fun r hr => by
        simp only [VG.Proof.Aes.Arm.gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.dCS.sub_right (Region.sub_prefix (by omega))
        · exact hp.dCS.sub_right (VG.Proof.Aes.Arm.sub_scr _ (by omega))
        · exact hp.dCD),
      m₁₃, hC d₈.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.dCS.sub_right (VG.Proof.Aes.Arm.keyArea_sub _)),
      m₇, m₃, VG.Proof.Aes.Arm.setup_ctr hp.dCS hk, arg₂ 0 (by omega),
      f₀₂.readW (Region.contains_self _ _) (cd (by omega)) (by decide)]
    split
    · exact hC f₀₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.dCS.sub_right (Region.sub_prefix (by omega))
    · simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem ctr32_correct (s : State) (hs : Proof.Aes.ctr32Arm.pre s) :
    ∃ t s', Exec isa Impl.Aes.Arm.ctr32 s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32Arm.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Aes.Arm.correct (VG.Proof.Aes.Arm.pre_of hs)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega)
  · exact h₁ 1 (by omega)
  · exact h₁ 2 (by omega)
  · exact h₁ 3 (by omega)
  · exact h₁ 4 (by omega)
  · exact h₁ 5 (by omega)
  · exact h₁ 6 (by omega)
  · exact h₁ 7 (by omega)
  · exact h₁ 8 (by omega)

/-! ## Constant time -/

/-- The initial taint: the pointers, `rounds` and the stack arguments are
public; `r2` and `r3` point at the counter block and the data. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [16, 0, 2048],
    bases := [(.r2, 0), (.r3, 1)], argLen := 8, argBases := [(4, 2)] }

theorem wf₀ {s : State} (h : Proof.Aes.ctr32Arm.pre s) : VG.Arm.Taint.Wf VG.Proof.Aes.Arm.τ₀ s := by
  have hp := VG.Proof.Aes.Arm.pre_of h
  have e : (⟨State.addr s.sp, 8⟩ : Region) = VG.Proof.Aes.Arm.argR s := by simp [VG.Proof.Aes.Arm.argR, stackArgAddr]
  refine ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Aes.Arm.τ₀], ?_, ?_⟩, ?_, fun _ => ⟨hp.fitSp, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil]
    exact ⟨⟨hp.dCD, hp.dCS⟩, hp.dDS, fun _ h => h.elim, trivial⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    have := hp.fitC; have := hp.fitD; have := hp.fitB
    rintro r (rfl | rfl | rfl) <;> simp only [VG.Proof.MdStream.Arm.addr_toNat] <;> omega
  · intro p hp'
    simp only [VG.Proof.Aes.Arm.τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp [VG.Arm.Taint.region, hp.wr]
  · simp only [VG.Proof.Aes.Arm.τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.dCA.symm
    · exact hp.dDA.symm
    · exact hp.dSA.symm
  · intro p hp'
    simp only [VG.Proof.Aes.Arm.τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Aes.ctr32Arm.pre s₁) (h₂ : Proof.Aes.ctr32Arm.pre s₂)
    (hpub : Proof.Aes.ctr32Arm.pub s₁ s₂) : VG.Arm.Taint.Agree VG.Proof.Aes.Arm.τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0, a1⟩ := hpub
  have hp₁ := VG.Proof.Aes.Arm.pre_of h₁; have hp₂ := VG.Proof.Aes.Arm.pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Aes.Arm.wf₀ h₁, VG.Proof.Aes.Arm.wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    fun k hk => ?_⟩
  · simp only [VG.Proof.Aes.Arm.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [VG.Proof.Aes.Arm.ctP, VG.Proof.Aes.Arm.dP, VG.Proof.Aes.Arm.nB, VG.Proof.Aes.Arm.bP, p2, p3, a0, a1]
  · simp only [VG.Proof.Aes.Arm.τ₀] at hk
    rw [VG.Proof.MdStream.Arm.argByte_eq hp₁.fitSp hk, VG.Proof.MdStream.Arm.argByte_eq hp₂.fitSp hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : k / 4 = 0 ∨ k / 4 = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

theorem ctr32_ct : ConstantTime isa Proof.Aes.ctr32Arm.pre Proof.Aes.ctr32Arm.pub Impl.Aes.Arm.ctr32 :=
  VG.Taint.constantTime (A := VG.Arm.taint) VG.Proof.Aes.Arm.τ₀ (fun _ _ h₁ h₂ hp => VG.Proof.Aes.Arm.agree₀ h₁ h₂ hp) (by taint_decide)

/-- A state satisfying the precondition (with no data, and the scratch buffer at 0). -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0, 2048⟩]

theorem ctr32_verified :
    Verified Arm.target Impl.Aes.Arm.ctr32 (Spec.Gcm.ctr32Contract Arm.abi) :=
  Verified.of_correct VG.Proof.Aes.Arm.ctr32_correct VG.Proof.Aes.Arm.ctr32_ct (by
    sig_implies [Spec.Gcm.ctr32Contract, Spec.Gcm.ctr32Sig, Proof.Aes.ctr32Arm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Aes.Arm.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
      using Proof.Aes.Arm.sat)

end VG.Proof.Aes.Arm

end
