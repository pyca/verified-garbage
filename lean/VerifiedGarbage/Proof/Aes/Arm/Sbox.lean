module

public import VerifiedGarbage.Impl.Aes.Arm.Sbox
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Aes.Bitsliced
public import VerifiedGarbage.Proof.Framework.Arm.Linear

/-! ### `Aes.Arm.Bitsliced`, which only this module used -/

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

@[expose] public section

namespace VG.Proof.Aes.Arm

open VG VG.Bitslice VG.Spec.Aes
open VG.Proof.Aes (byte_ext getD_eq mul2 mul3 xtimes_bit)

/-- The byte at bit position `p` of eight words: its bit `k` is bit `p` of word `k`. -/
def bsByte (Q : Nat → BitVec 32) (p : Nat) : Byte := ofBits 8 fun k => (Q k).getLsbD p

theorem getLsbD_bsByte (Q : Nat → BitVec 32) (p : Nat) {k : Nat} (hk : k < 8) :
    (bsByte Q p).getLsbD k = (Q k).getLsbD p := by
  rw [bsByte, getLsbD_ofBits]; simp [hk]

/-- Byte `r + 4c` of block `b` is at position `8r + 2c + b`. -/
def pos (b i : Nat) : Nat := 8 * (i % 4) + 2 * (i / 4) + b

theorem pos_lt {b i : Nat} (hb : b < 2) (hi : i < 16) : pos b i < 32 := by
  simp only [pos]; omega_using [hb, hi]

/-- The words `Q` hold the two states `S`. -/
def BsRel (Q : Nat → BitVec 32) (S : Nat → State) : Prop :=
  ∀ b < 2, ∀ i < 16, bsByte Q (pos b i) = (S b).getD i 0

/-- The words `K` hold the round key `rk` in both blocks. -/
def KeyRel (K : Nat → BitVec 32) (rk : List Byte) : Prop :=
  ∀ b < 2, ∀ i < 16, bsByte K (pos b i) = rk.getD i 0

/-- The words `Q` hold the two states word by word, little-endian: bytes
`4k … 4k + 3` of block `b` in word `2k + b`. -/
def InRel (Q : Nat → BitVec 32) (S : Nat → State) : Prop :=
  ∀ b < 2, ∀ i < 16, ∀ j < 8,
    (Q (2 * (i / 4) + b)).getLsbD (8 * (i % 4) + j) = ((S b).getD i 0).getLsbD j

/-! ## The layers -/

theorem bs_subBytes {Q Q' : Nat → BitVec 32} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = (sbox (bsByte Q p)).getLsbD j) (hr : BsRel Q S) :
    BsRel Q' fun b => subBytes (S b) := by
  intro b hb i hi
  have : bsByte Q' (pos b i) = sbox (bsByte Q (pos b i)) :=
    byte_ext fun j hj => by rw [getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi)]
  rw [this, hr b hb i hi, getD_eq _ hi, getD_eq _ hi]
  simp only [subBytes, Vector.getElem_map]

/-- ShiftRows: position `8r + 2c + b` from `8r + 2((c + r) mod 4) + b`. -/
def srSrc (p : Nat) : Nat := 8 * (p / 8) + 2 * ((p % 8 / 2 + p / 8) % 4) + p % 2

theorem srSrc_pos : ∀ b < 2, ∀ i < 16, srSrc (pos b i) = pos b (i % 4 + 4 * ((i / 4 + i % 4) % 4)) := by
  decide

theorem bs_shiftRows {Q Q' : Nat → BitVec 32} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = (Q j).getLsbD (srSrc p)) (hr : BsRel Q S) :
    BsRel Q' fun b => shiftRows (S b) := by
  intro b hb i hi
  have : bsByte Q' (pos b i) = bsByte Q (pos b (i % 4 + 4 * ((i / 4 + i % 4) % 4))) :=
    byte_ext fun j hj => by
      rw [getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi), srSrc_pos b hb i hi]
  rw [this, hr b hb _ (by omega_using []), getD_eq _ hi]
  simp only [shiftRows, Vector.getElem_ofFn]

theorem bs_addRoundKey {Q Q' K : Nat → BitVec 32} {S : Nat → State} {rk : List Byte}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = ((Q j).getLsbD p ^^ (K j).getLsbD p))
    (hr : BsRel Q S) (hk : KeyRel K rk) : BsRel Q' fun b => addRoundKey (S b) rk := by
  intro b hb i hi
  have : bsByte Q' (pos b i) = bsByte Q (pos b i) ^^^ bsByte K (pos b i) :=
    byte_ext fun j hj => by
      rw [BitVec.getLsbD_xor, getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj,
        h j hj _ (pos_lt hb hi)]
  rw [this, hr b hb i hi, hk b hb i hi, getD_eq _ hi, getD_eq _ hi]
  simp only [addRoundKey, Vector.getElem_ofFn, getD_eq _ hi]

theorem pos_div : ∀ b < 2, ∀ i < 16, pos b i % 8 = 2 * (i / 4) + b ∧ pos b i / 8 = i % 4 := by
  decide

/-- `ortho` from the words of the blocks to the bitsliced state. -/
theorem bs_of_in {Q Q' : Nat → BitVec 32} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = (Q (p % 8)).getLsbD (8 * (p / 8) + j))
    (hr : InRel Q S) : BsRel Q' S := by
  intro b hb i hi
  refine byte_ext fun j hj => ?_
  obtain ⟨h1, h2⟩ := pos_div b hb i hi
  rw [getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi), h1, h2, hr b hb i hi j hj]

/-- `ortho` from the bitsliced state back to the words of the blocks. -/
theorem in_of_bs {Q Q' : Nat → BitVec 32} {S : Nat → State}
    (h : ∀ k < 8, ∀ t < 32, (Q' k).getLsbD t = (Q (t % 8)).getLsbD (8 * (t / 8) + k))
    (hr : BsRel Q S) : InRel Q' S := by
  intro b hb i hi j hj
  rw [h _ (by omega_using [hb, hi]) _ (by omega_using [hj]), ← getLsbD_bsByte _ _ (by omega_using [])]
  rw [show (8 * (i % 4) + j) % 8 = j by omega_using [hj],
    show 8 * ((8 * (i % 4) + j) / 8) + (2 * (i / 4) + b) = pos b i by simp only [pos]; omega_using [hj],
    hr b hb i hi]

/-! ## MixColumns -/

/-- The XOR of the bits `(w, t)` (bit `t` of word `w`). -/
def termsXor (Q : Nat → BitVec 32) (l : List (Nat × Nat)) : Bool :=
  l.foldr (fun wt b => (Q wt.1).getLsbD wt.2 ^^ b) false

/-- Position `p` moved `k` rows down (within its column). -/
def down (p k : Nat) : Nat := (p + 8 * k) % 32

/-- The bits `(w, k)` of `Proof.Aes.mcWords`: bit `w` of the byte `k` rows down. -/
def mcTerms (j p : Nat) : List (Nat × Nat) := (Proof.Aes.mcWords j).map fun wk => (wk.1, down p wk.2)

theorem down_pos : ∀ b < 2, ∀ i < 16, ∀ k < 4,
    down (pos b i) k = pos b ((i % 4 + k) % 4 + 4 * (i / 4)) := by
  decide

theorem termsXor_mc (Q : Nat → BitVec 32) (j p : Nat) : termsXor Q (mcTerms j p) =
    ((if j = 0 then false else ((Q (j - 1)).getLsbD (down p 0) ^^ (Q (j - 1)).getLsbD (down p 1))) ^^
     (if j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 then (Q 7).getLsbD (down p 0) ^^ (Q 7).getLsbD (down p 1)
      else false) ^^
     ((Q j).getLsbD (down p 1) ^^ (Q j).getLsbD (down p 2) ^^ (Q j).getLsbD (down p 3))) := by
  simp only [mcTerms, Proof.Aes.mcWords]
  (repeat' split) <;> simp [termsXor]

theorem bs_mixColumns {Q Q' : Nat → BitVec 32} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = termsXor Q (mcTerms j p)) (hr : BsRel Q S) :
    BsRel Q' fun b => mixColumns (S b) := by
  intro b hb i hi
  refine byte_ext fun j hj => ?_
  have hbit : ∀ k < 4, ∀ w < 8, (Q w).getLsbD (down (pos b i) k) =
      ((S b).getD ((i % 4 + k) % 4 + 4 * (i / 4)) 0).getLsbD w := fun k hk w hw => by
    rw [down_pos b hb i hi k hk, ← hr b hb _ (by omega_using [hi]), getLsbD_bsByte _ _ hw]
  rw [getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi), getD_eq _ hi, termsXor_mc]
  simp only [mixColumns, Vector.getElem_ofFn, mul2, mul3, BitVec.getLsbD_xor, xtimes_bit _ hj]
  simp only [hbit 1 (by decide) _ hj, hbit 2 (by decide) _ hj,
    hbit 3 (by decide) _ hj, hbit 0 (by decide) 7 (by decide), hbit 1 (by decide) 7 (by decide),
    hbit 0 (by decide) (j - 1) (by omega_using [hj]), hbit 1 (by decide) (j - 1) (by omega_using [hj])]
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

def srG (j p : Nat) : List Nat := [32 * j + srSrc p]

/-- MixColumns: the bits `mcTerms`, as atoms. -/
def mcG (j p : Nat) : List Nat := (mcTerms j p).map fun wt => 32 * wt.1 + wt.2

/-- AddRoundKey: the round key is input words `8 … 15`. -/
def arkG (j p : Nat) : List Nat := [32 * j + p, 32 * (8 + j) + p]

open VG.Arm.Straight in
theorem xorBits_map (W : Nat → BitVec 32) (l : List (Nat × Nat)) (hl : ∀ wt ∈ l, wt.2 < 32) :
    Arm.Straight.xorBits W (l.map fun wt => 32 * wt.1 + wt.2) = termsXor W l := by
  induction l with
  | nil => rfl
  | cons wt l ih =>
    simp only [List.map_cons, Arm.Straight.xorBits_cons, termsXor, List.foldr_cons] at ih ⊢
    rw [Arm.Straight.bitOf_word _ _ _ (hl wt (by simp)), ih fun v hv => hl v (by simp [hv])]

end VG.Proof.Aes.Arm

end

end


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

@[expose] public section

namespace VG.Proof.Aes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Proof.Aes (sboxT row row_ext getLsbD_row row_sboxT)
open VG.Spec.Aes (sbox)

/-- The S-box's memory: its slots, at `r8`. -/
def sboxCfg : Cfg := { base := sb, slots := 32, ext := sb, exts := 0 }

/-- The truth table of bit `k` of the input. -/
def inT (k : Nat) : Nat := tableOf (fun c => c.testBit k) 256

def inTs : List Nat := (List.range 8).map inT

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)).map inT, slot := fun _ => none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (q j) == some ((sboxT inTs).getD j 0)

theorem sbox_check :
    check (table 32 256) sboxCfg (fun _ => none) sboxCode sboxEnv sboxPost = true := by
  decide +kernel

theorem row_inTs {c : Nat} (hc : c < 256) : row inTs c = BitVec.ofNat 8 c := by
  refine row_ext fun j hj => ?_
  simp only [inTs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
    BitVec.getLsbD_ofNat, hj]

/-- The registers the layers of AES may write: the state and the
temporaries (of the S-box and the linear layers). -/
def layerWrites : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r10, .r11, .r12, .lr]

/-- The registers outside `layerWrites`: the scratch buffer's base and the
round key pointer. -/
def layerKeep : List Reg := [.r8, .r9]

theorem not_layerWrites (r : Reg) (hr : r ∉ layerWrites) : r ∈ layerKeep := by
  revert hr; cases r <;> decide

/-- A block that writes none of `layerKeep` writes only `layerWrites`. -/
theorem writes_rest {is : List Instr}
    (h : layerKeep.all (fun r => is.all fun i => !clobbers i r) = true)
    (r : Reg) (hr : r ∉ layerWrites) : (is.all fun i => !clobbers i r) = true :=
  List.all_eq_true.mp h r (not_layerWrites r hr)

/-- The S-box, at every bit position of the words in `q 0 … q 7`. -/
theorem sbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 32,
        (s'.gpr (q j)).getLsbD p = (sbox (bsByte (fun k => s.gpr (q k)) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ sbox_check
  have hout : ∀ j < 8, e'.reg (q j) = some ((sboxT inTs).getD j 0) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  -- The run at bit position `p`, on the input formed by the bits `p`.
  have key : ∀ p < 32, ∃ s', runBlock isa sboxCode s = some s' ∧
      Post (TableRel p (bsByte (fun k => s.gpr (q k)) p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => (sboxCode.all fun i => !clobbers i r) = false) := by
    intro p hp
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_, (fun _ _ _ h => by cases h),
      (fun _ _ _ h => by cases h), (fun _ _ h => by cases h)⟩ he
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨hqk, hkr⟩ := List.find?_some hk, List.mem_of_find?_eq_some hk
    have hk8 := List.mem_range.mp hkr
    simp only [beq_iff_eq] at hqk
    subst hqk
    simp only [TableRel, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8]
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega_using [])
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, p₀.sp, fun r hr => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    have := p₁.rel.reg (q j) _ (hout j hj)
    simp only [TableRel] at this
    rw [← this, ← getLsbD_row _ _ hj, row_sboxT (by simp [inTs]) hc, row_inTs hc]
    simp
  · simp [writes_rest (is := sboxCode) (by decide +kernel) r hr]

end VG.Proof.Aes.Arm
