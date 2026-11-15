module

public import VerifiedGarbage.Impl.Aes.AArch64.Neon.Blocks
public import VerifiedGarbage.Proof.Aes.Bitsliced
public import VerifiedGarbage.Proof.Aes.InvBitsliced
public import VerifiedGarbage.Proof.Framework.AArch64.StraightQ
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Aes.AArch64.Encrypt
public import VerifiedGarbage.Proof.Aes.InvSboxSpec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the kernel takes nine seconds to check the layers, which a change to the rounds' or the blocks' proofs does not repeat

@[expose] public section

section

/-!
# AES bitsliced in 128-bit words: the layout and the round transformations

Eight AES states in eight 128-bit words, as `Impl/Aes/AArch64/Neon/Blocks.lean`
lays them out: bit `j` of byte `i` of block `b` is bit `8 i + b` of word `j`.
`BsRel Q S` says the words `Q` hold the states `S`. As `Proof/Aes/Bitsliced.lean`
and `InvBitsliced.lean` do for four states in 64-bit words, the lemmas here
turn what each layer of the code does to the bits into the transformation
of FIPS 197 it computes on the states.
-/

namespace VG.Proof.Aes.AArch64.Neon

open VG VG.Bitslice VG.Spec.Aes
open VG.Proof.Aes (byte_ext getD_eq mul2 mul3 xtimes_bit mcWords invMcWords mulBits bitsXor
  mulBits_lt mul0e_bit mul0b_bit mul0d_bit mul09_bit)

/-- The byte at bit position `p` of eight words: its bit `k` is bit `p` of word `k`. -/
def bsByte (Q : Nat → BitVec 128) (p : Nat) : Byte := ofBits 8 fun k => (Q k).getLsbD p

theorem getLsbD_bsByte (Q : Nat → BitVec 128) (p : Nat) {k : Nat} (hk : k < 8) :
    (bsByte Q p).getLsbD k = (Q k).getLsbD p := by
  rw [bsByte, getLsbD_ofBits]; simp [hk]

/-- The words `Q` hold the eight states `S`. -/
def BsRel (Q : Nat → BitVec 128) (S : Nat → State) : Prop :=
  ∀ b < 8, ∀ i < 16, bsByte Q (8 * i + b) = (S b).getD i 0

/-- The words `K` hold the round key `rk` in all eight blocks. -/
def KeyRel (K : Nat → BitVec 128) (rk : List Byte) : Prop :=
  ∀ b < 8, ∀ i < 16, bsByte K (8 * i + b) = rk.getD i 0

/-- Word `b` holds the state `S b`, byte by byte. -/
def InRel (Q : Nat → BitVec 128) (S : Nat → State) : Prop :=
  ∀ b < 8, ∀ i < 16, ∀ j < 8, (Q b).getLsbD (8 * i + j) = ((S b).getD i 0).getLsbD j

/-! ## The layers -/

theorem bs_subBytes {Q Q' : Nat → BitVec 128} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 128, (Q' j).getLsbD p = (sbox (bsByte Q p)).getLsbD j) (hr : BsRel Q S) :
    BsRel Q' fun b => subBytes (S b) := by
  intro b hb i hi
  have : bsByte Q' (8 * i + b) = sbox (bsByte Q (8 * i + b)) :=
    byte_ext fun j hj => by rw [getLsbD_bsByte _ _ hj, h j hj _ (by omega_using [hb, hi])]
  rw [this, hr b hb i hi, getD_eq _ hi, getD_eq _ hi]
  simp only [subBytes, Vector.getElem_map]

theorem bs_invSubBytes {Q Q' : Nat → BitVec 128} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 128, (Q' j).getLsbD p = (invSbox (bsByte Q p)).getLsbD j) (hr : BsRel Q S) :
    BsRel Q' fun b => invSubBytes (S b) := by
  intro b hb i hi
  have : bsByte Q' (8 * i + b) = invSbox (bsByte Q (8 * i + b)) :=
    byte_ext fun j hj => by rw [getLsbD_bsByte _ _ hj, h j hj _ (by omega_using [hb, hi])]
  rw [this, hr b hb i hi, getD_eq _ hi, getD_eq _ hi]
  simp only [invSubBytes, Vector.getElem_map]

/-- ShiftRows: byte `r + 4c` from byte `r + 4 ((c + r) mod 4)`, of the same block. -/
def srSrc (p : Nat) : Nat := 8 * (p / 8 % 4 + 4 * ((p / 32 + p / 8 % 4) % 4)) + p % 8

theorem srSrc_pos : ∀ b < 8, ∀ i < 16,
    srSrc (8 * i + b) = 8 * (i % 4 + 4 * ((i / 4 + i % 4) % 4)) + b := by
  decide

theorem bs_shiftRows {Q Q' : Nat → BitVec 128} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 128, (Q' j).getLsbD p = (Q j).getLsbD (srSrc p)) (hr : BsRel Q S) :
    BsRel Q' fun b => shiftRows (S b) := by
  intro b hb i hi
  have : bsByte Q' (8 * i + b) = bsByte Q (8 * (i % 4 + 4 * ((i / 4 + i % 4) % 4)) + b) :=
    byte_ext fun j hj => by
      rw [getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, h j hj _ (by omega_using [hb, hi]),
        srSrc_pos b hb i hi]
  rw [this, hr b hb _ (by omega_using []), getD_eq _ hi]
  simp only [shiftRows, Vector.getElem_ofFn]

/-- InvShiftRows: byte `r + 4c` from byte `r + 4 ((c − r) mod 4)`. -/
def invSrSrc (p : Nat) : Nat := 8 * (p / 8 % 4 + 4 * ((p / 32 + 4 - p / 8 % 4) % 4)) + p % 8

theorem invSrSrc_pos : ∀ b < 8, ∀ i < 16,
    invSrSrc (8 * i + b) = 8 * (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4)) + b := by
  decide

theorem bs_invShiftRows {Q Q' : Nat → BitVec 128} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 128, (Q' j).getLsbD p = (Q j).getLsbD (invSrSrc p)) (hr : BsRel Q S) :
    BsRel Q' fun b => invShiftRows (S b) := by
  intro b hb i hi
  have : bsByte Q' (8 * i + b) = bsByte Q (8 * (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4)) + b) :=
    byte_ext fun j hj => by
      rw [getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, h j hj _ (by omega_using [hb, hi]),
        invSrSrc_pos b hb i hi]
  rw [this, hr b hb _ (by omega_using []), getD_eq _ hi]
  simp only [invShiftRows, Vector.getElem_ofFn]

theorem bs_addRoundKey {Q Q' K : Nat → BitVec 128} {S : Nat → State} {rk : List Byte}
    (h : ∀ j < 8, ∀ p < 128, (Q' j).getLsbD p = ((Q j).getLsbD p ^^ (K j).getLsbD p))
    (hr : BsRel Q S) (hk : KeyRel K rk) : BsRel Q' fun b => addRoundKey (S b) rk := by
  intro b hb i hi
  have : bsByte Q' (8 * i + b) = bsByte Q (8 * i + b) ^^^ bsByte K (8 * i + b) :=
    byte_ext fun j hj => by
      rw [BitVec.getLsbD_xor, getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj,
        h j hj _ (by omega_using [hb, hi])]
  rw [this, hr b hb i hi, hk b hb i hi, getD_eq _ hi, getD_eq _ hi]
  simp only [addRoundKey, Vector.getElem_ofFn, getD_eq _ hi]

/-- `ortho`, from the blocks to the bitsliced state. -/
theorem bs_of_in {Q Q' : Nat → BitVec 128} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 128, (Q' j).getLsbD p = (Q (p % 8)).getLsbD (8 * (p / 8) + j))
    (hr : InRel Q S) : BsRel Q' S := by
  intro b hb i hi
  refine byte_ext fun j hj => ?_
  rw [getLsbD_bsByte _ _ hj, h j hj _ (by omega_using [hb, hi]),
    show (8 * i + b) % 8 = b by omega_using [hb], show (8 * i + b) / 8 = i by omega_using [hb],
    hr b hb i hi j hj]

/-- `ortho`, from the bitsliced state back to the blocks. -/
theorem in_of_bs {Q Q' : Nat → BitVec 128} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 128, (Q' j).getLsbD p = (Q (p % 8)).getLsbD (8 * (p / 8) + j))
    (hr : BsRel Q S) : InRel Q' S := by
  intro b hb i hi j hj
  rw [h b hb _ (by omega_using [hj, hi]), show (8 * i + j) % 8 = j by omega_using [hj],
    show (8 * i + j) / 8 = i by omega_using [hj], ← getLsbD_bsByte _ _ hj, hr b hb i hi]

/-! ## MixColumns -/

/-- The XOR of the bits `(w, t)` (bit `t` of word `w`). -/
def termsXor (Q : Nat → BitVec 128) (l : List (Nat × Nat)) : Bool :=
  l.foldr (fun wt b => (Q wt.1).getLsbD wt.2 ^^ b) false

/-- Position `p` moved `k` rows down (within its column). -/
def down (p k : Nat) : Nat := 8 * (4 * (p / 32) + (p / 8 % 4 + k) % 4) + p % 8

/-- The bits `(w, k)` of `mcWords`: bit `w` of the byte `k` rows down. -/
def mcTerms (j p : Nat) : List (Nat × Nat) := (mcWords j).map fun wk => (wk.1, down p wk.2)

theorem down_pos : ∀ b < 8, ∀ i < 16, ∀ k < 4,
    down (8 * i + b) k = 8 * ((i % 4 + k) % 4 + 4 * (i / 4)) + b := by
  decide

theorem down_lt (p k : Nat) (hp : p < 128) : down p k < 128 := by
  simp only [down]; omega_using [hp]

theorem termsXor_mc (Q : Nat → BitVec 128) (j p : Nat) : termsXor Q (mcTerms j p) =
    ((if j = 0 then false else ((Q (j - 1)).getLsbD (down p 0) ^^ (Q (j - 1)).getLsbD (down p 1))) ^^
     (if j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 then (Q 7).getLsbD (down p 0) ^^ (Q 7).getLsbD (down p 1)
      else false) ^^
     ((Q j).getLsbD (down p 1) ^^ (Q j).getLsbD (down p 2) ^^ (Q j).getLsbD (down p 3))) := by
  simp only [mcTerms, mcWords]
  by_cases h₁ : j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4
  · rw [ite_eq_left h₁, ite_eq_left h₁]
    by_cases h₀ : j = 0
    · rw [ite_eq_left h₀, ite_eq_left h₀]; simp [termsXor]
    · rw [ite_eq_right h₀, ite_eq_right h₀]; simp [termsXor]
  · rw [ite_eq_right h₁, ite_eq_right h₁]
    by_cases h₀ : j = 0
    · rw [ite_eq_left h₀, ite_eq_left h₀]; simp [termsXor]
    · rw [ite_eq_right h₀, ite_eq_right h₀]; simp [termsXor]

theorem bs_mixColumns {Q Q' : Nat → BitVec 128} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 128, (Q' j).getLsbD p = termsXor Q (mcTerms j p)) (hr : BsRel Q S) :
    BsRel Q' fun b => mixColumns (S b) := by
  intro b hb i hi
  refine byte_ext fun j hj => ?_
  have hbit : ∀ k < 4, ∀ w < 8, (Q w).getLsbD (down (8 * i + b) k) =
      ((S b).getD ((i % 4 + k) % 4 + 4 * (i / 4)) 0).getLsbD w := fun k hk w hw => by
    rw [down_pos b hb i hi k hk, ← hr b hb _ (by omega_using [hi]), getLsbD_bsByte _ _ hw]
  rw [getLsbD_bsByte _ _ hj, h j hj _ (by omega_using [hb, hi]), getD_eq _ hi, termsXor_mc]
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

/-! ## InvMixColumns -/

/-- The bits `(w, k)` of `invMcWords`: bit `w` of the byte `k` rows down. -/
def invMcTerms (j p : Nat) : List (Nat × Nat) := (invMcWords j).map fun wk => (wk.1, down p wk.2)

theorem termsXor_append (Q : Nat → BitVec 128) (l₁ l₂ : List (Nat × Nat)) :
    termsXor Q (l₁ ++ l₂) = (termsXor Q l₁ ^^ termsXor Q l₂) := by
  induction l₁ with
  | nil => simp [termsXor]
  | cons wt l ih =>
    simp only [termsXor, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih, Bool.xor_assoc]

/-- The bits `ts` of the byte at `p`, read from the words when they hold it. -/
theorem termsXor_row {Q : Nat → BitVec 128} {p : Nat} {a : Byte}
    (ha : ∀ w < 8, (Q w).getLsbD p = a.getLsbD w) {ts : List Nat} (hts : ∀ t ∈ ts, t < 8) :
    termsXor Q (ts.map fun t => (t, p)) = bitsXor a ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, termsXor, List.foldr_cons, bitsXor] at ih ⊢
    rw [ha t (hts t (by simp)), ih fun u hu => hts u (by simp [hu])]

theorem invMcTerms_eq (j p : Nat) : invMcTerms j p =
    (mulBits 0x0e j).map (fun t => (t, down p 0)) ++ ((mulBits 0x0b j).map (fun t => (t, down p 1)) ++
      ((mulBits 0x0d j).map (fun t => (t, down p 2)) ++ (mulBits 0x09 j).map (fun t => (t, down p 3)))) := by
  simp [invMcTerms, invMcWords, List.map_map, Function.comp_def]

theorem bs_invMixColumns {Q Q' : Nat → BitVec 128} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 128, (Q' j).getLsbD p = termsXor Q (invMcTerms j p)) (hr : BsRel Q S) :
    BsRel Q' fun b => invMixColumns (S b) := by
  intro b hb i hi
  refine byte_ext fun j hj => ?_
  have hbit : ∀ k < 4, ∀ w < 8, (Q w).getLsbD (down (8 * i + b) k) =
      ((S b).getD ((i % 4 + k) % 4 + 4 * (i / 4)) 0).getLsbD w := fun k hk w hw => by
    rw [down_pos b hb i hi k hk, ← hr b hb _ (by omega_using [hi]), getLsbD_bsByte _ _ hw]
  have hlt := fun c hc => mulBits_lt c hc j hj
  rw [getLsbD_bsByte _ _ hj, h j hj _ (by omega_using [hb, hi]), getD_eq _ hi, invMcTerms_eq,
    termsXor_append, termsXor_append, termsXor_append,
    termsXor_row (hbit 0 (by decide)) (hlt 0x0e (by decide)),
    termsXor_row (hbit 1 (by decide)) (hlt 0x0b (by decide)),
    termsXor_row (hbit 2 (by decide)) (hlt 0x0d (by decide)),
    termsXor_row (hbit 3 (by decide)) (hlt 0x09 (by decide))]
  simp only [invMixColumns, Vector.getElem_ofFn, BitVec.getLsbD_xor]
  rw [mul0e_bit _ hj, mul0b_bit _ hj, mul0d_bit _ hj, mul09_bit _ hj]
  simp only [Bool.xor_assoc, Nat.add_zero]

/-! ## As atoms -/

/-- Bit `t` of input word `i` of a linear layer is atom `128 i + t`. -/
def srG (j p : Nat) : List Nat := [128 * j + srSrc p]
def invSrG (j p : Nat) : List Nat := [128 * j + invSrSrc p]
def mcG (j p : Nat) : List Nat := (mcTerms j p).map fun wt => 128 * wt.1 + wt.2
def invMcG (j p : Nat) : List Nat := (invMcTerms j p).map fun wt => 128 * wt.1 + wt.2

/-- AddRoundKey: the round key is input words `8 … 15`. -/
def arkG (j p : Nat) : List Nat := [128 * j + p, 128 * (8 + j) + p]

/-- `ortho`, on the doublewords: bit `t` of input word `i` is atom `64 i + t`. -/
def orthoG (j t : Nat) : List Nat := [64 * (t % 8) + (8 * (t / 8) + j)]

theorem xorBits_map (W : Nat → BitVec 128) (l : List (Nat × Nat)) (hl : ∀ wt ∈ l, wt.2 < 128) :
    xorBits W (l.map fun wt => 128 * wt.1 + wt.2) = termsXor W l := by
  induction l with
  | nil => rfl
  | cons wt l ih =>
    simp only [List.map_cons, xorBits_cons, termsXor, List.foldr_cons] at ih ⊢
    rw [bitOf_word _ _ _ (hl wt (by simp)), ih fun v hv => hl v (by simp [hv])]

end VG.Proof.Aes.AArch64.Neon

end

section

/-!
# The layers of AES bitsliced in AdvSIMD registers, on AArch64

Each layer of `Impl/Aes/AArch64/Neon/Blocks.lean` is checked by evaluation:
the S-boxes on the truth tables of the 256 inputs (`StraightV`, doubleword
by doubleword, against `sboxT` and `invSboxT`), `ortho` over the lane domain
on each doubleword, and the layers that permute and XOR bytes over the lane
domain on whole words (`StraightQ`). Each lemma gives what the layer does to
the bits of the state's words, as the lemmas above take it.
-/

namespace VG.Proof.Aes.AArch64.Neon

open VG VG.AArch64 VG.Bitslice VG.Impl.Aes.AArch64.Neon VG.Proof.Aes
open VG.AArch64.StraightV (vAddr vdword_dwords getLsbD_vdword)
open VG.Spec.Aes (sbox invSbox)
open VG.Impl.Tbl.AArch64 (const128)

/-- What a layer leaves alone: the general-purpose registers but `x6` and
`x7`, and memory but the S-boxes' slots. -/
structure Keeps (s s' : State) : Prop where
  gpr : ∀ g, g ≠ .x6 → g ≠ .x7 → s'.gpr g = s.gpr g
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨s.gpr sb, 96⟩] s.mem s'.mem

/-- The scratch buffer at `b`, 2048 bytes of it at least, is writable: the
block functions' own (`ScrIn.of_mem`), or the head of a longer one. -/
def ScrIn (b : Addr) (wr : List Region) : Prop :=
  ∃ L, 2048 ≤ L ∧ L < 2 ^ 64 ∧ (⟨b, L⟩ : Region) ∈ wr

theorem ScrIn.of_mem {b : Addr} {wr : List Region} (h : (⟨b, 2048⟩ : Region) ∈ wr) : ScrIn b wr :=
  ⟨2048, Nat.le_refl _, by decide, h⟩

theorem Keeps.refl (s : State) : Keeps s s := ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Keeps.trans {a b c : State} (h₁ : Keeps a b) (h₂ : Keeps b c) : Keeps a c where
  gpr g h6 h7 := (h₂.gpr g h6 h7).trans (h₁.gpr g h6 h7)
  rd := h₂.rd.trans h₁.rd
  wr := h₂.wr.trans h₁.wr
  sp := h₂.sp.trans h₁.sp
  frame := h₁.frame.trans (by have := h₂.frame; rwa [h₁.gpr sb (by decide) (by decide)] at this)

/-- A state that differs only in its vector registers. -/
theorem Keeps.of_v {s s' : State} (h : s' = { s with v := s'.v }) : Keeps s s' := by
  have e1 : s'.gpr = s.gpr := by rw [h]
  have e2 : s'.mem = s.mem := by rw [h]
  exact ⟨fun g _ _ => by rw [e1], by rw [h], by rw [h], by rw [h], by rw [e2]; exact Frame.refl _ _⟩

/-! ## The S-boxes -/

/-- The S-boxes' memory: their spill slots, at `sb`. -/
def sboxCfg : StraightV.Cfg := { base := sb, slots := 6 }

def sboxEnv : StraightV.Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => A k == r)).map inT, slot := fun _ => none }

def sboxPost (T : List Nat) (e : StraightV.Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (B j) == some (T.getD j 0)

theorem sbox_check :
    StraightV.check (table 64 256) sboxCfg sboxCode sboxEnv (sboxPost (sboxT inTs)) = true := by
  decide +kernel

theorem invSbox_check :
    StraightV.check (table 64 256) sboxCfg invSboxCode sboxEnv (sboxPost (invSboxT inTs)) = true := by
  decide +kernel

/-- A circuit checked to compute `f`, from the words in `A 0 … A 7` to `B 0 … B 7`. -/
theorem circuit_ok {code : List Instr} {T : List Nat} {f : Byte → Byte}
    (hchk : StraightV.check (table 64 256) sboxCfg code sboxEnv (sboxPost T) = true)
    (hT : ∀ c < 256, ∀ j < 8, (T.getD j 0).testBit c = (f (BitVec.ofNat 8 c)).getLsbD j)
    (hg : code.all (fun i => (dsts i).isEmpty) = true)
    {s : State} (hscr : ScrIn (s.gpr sb) s.wr) :
    ∃ s', runBlock isa code s = some s' ∧
      (∀ j < 8, ∀ p < 128,
        (s'.v (B j)).getLsbD p = (f (bsByte (fun k => s.v (A k)) p)).getLsbD j) ∧
      Keeps s s' := by
  obtain ⟨L, hL, hL64, hscr⟩ := hscr
  obtain ⟨e', he, hpost⟩ := StraightV.of_check _ _ hchk
  have hout : ∀ j < 8, e'.reg (B j) = some (T.getD j 0) := by
    intro j hj
    exact beq_iff_eq.mp (List.all_eq_true.mp hpost j (List.mem_range.mpr hj))
  have hok : StraightV.Ok sboxCfg s :=
    StraightV.Ok.of_off (r := ⟨s.gpr sb, L⟩) (off := 0) hscr (by simp [sboxCfg])
      (by simp only [sboxCfg]; omega_using [hL]) hL64
  have key : ∀ p < 64, ∃ s', runBlock isa code s = some s' ∧
      StraightV.Post (fun q => TableRel p (bsByte (fun k => s.v (A k)) (64 * q + p)).toNat) sboxCfg
        e' s s' (fun r => (code.all fun i => vdstOf i != some r) = false)
        (fun r => (code.all fun i => !clobbers i r) = false) := by
    intro p hp
    refine StraightV.run (fun q _ => table_sound hp (bsByte (fun k => s.v (A k)) (64 * q + p)).isLt) hok
      ⟨fun r a h q hq => ?_, (fun _ _ _ h => by cases h), (fun _ _ h => by cases h)⟩ he
    have hc := (bsByte (fun k => s.v (A k)) (64 * q + p)).isLt
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hqr := List.find?_some hk
    have hk8 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
    simp only [beq_iff_eq] at hqr
    subst hqr
    simp only [TableRel, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8, getLsbD_vdword _ hp]
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  refine ⟨s', hs', fun j hj P hP => ?_, fun g _ _ => p₀.gpr g ?_, p₀.rd, p₀.wr, p₀.sp, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key (P % 64) (Nat.mod_lt _ (by decide))
    rw [hs'] at hs''
    cases hs''
    have h := p₁.rel.reg (B j) _ (hout j hj) (P / 64) (by omega_using [hP])
    have eP : 64 * (P / 64) + P % 64 = P := Nat.div_add_mod P 64
    simp only [TableRel, eP, getLsbD_vdword _ (Nat.mod_lt _ (by decide) : P % 64 < 64)] at h
    rw [← h, hT _ (bsByte (fun k => s.v (A k)) P).isLt j hj, BitVec.ofNat_toNat]
    simp
  · simp only [Bool.not_eq_false, List.all_eq_true]
    intro i hi
    simpa using clobbers_eq_false_of_isEmpty (r := g) (List.all_eq_true.mp hg i hi)

/-- The S-box, at every bit position of the words. -/
theorem sbox_ok {s : State} (hscr : ScrIn (s.gpr sb) s.wr) :
    ∃ s', runBlock isa sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 128,
        (s'.v (B j)).getLsbD p = (sbox (bsByte (fun k => s.v (A k)) p)).getLsbD j) ∧
      Keeps s s' :=
  circuit_ok sbox_check (fun c hc j hj => by
    rw [← getLsbD_row _ _ hj, row_sboxT (by simp [inTs]) hc, row_inTs hc]) (by decide +kernel) hscr

/-- The inverse S-box, at every bit position of the words. -/
theorem invSbox_ok {s : State} (hscr : ScrIn (s.gpr sb) s.wr) :
    ∃ s', runBlock isa invSboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 128,
        (s'.v (B j)).getLsbD p = (invSbox (bsByte (fun k => s.v (A k)) p)).getLsbD j) ∧
      Keeps s s' :=
  circuit_ok invSbox_check (fun c hc j hj => by
    rw [← getLsbD_row _ _ hj, row_invSboxT _ hc, row_inTs hc]) (by decide +kernel) hscr

/-! ## `ortho` -/

def orthoCfg : StraightV.Cfg := { base := sb, slots := 0 }

def orthoEnv (P : Nat → VReg) : StraightV.Env (Nat × Nat) :=
  { reg := fun r => ((List.range 8).find? (fun k => P k == r)).map inWord, slot := fun _ => none }

def orthoPost (K : Nat) (P : Nat → VReg) (e : StraightV.Env (Nat × Nat)) : Bool :=
  (List.range 8).all fun j => outOk K (e.reg (P j)) (orthoG j)

theorem orthoA_check :
    StraightV.check (lanes 64 9) orthoCfg (bitslice A) (orthoEnv A) (orthoPost 9 A) = true := by
  decide +kernel

theorem orthoB_check :
    StraightV.check (lanes 64 9) orthoCfg (bitslice B) (orthoEnv B) (orthoPost 9 B) = true := by
  decide +kernel

/-- `ortho` on the words `P 0 … P 7`, with its masks. -/
theorem ortho_ok {K : Nat} {P : Nat → VReg}
    (hchk : StraightV.check (lanes 64 K) orthoCfg (bitslice P) (orthoEnv P) (orthoPost K P) = true)
    (hK : 512 ≤ 2 ^ K)
    (hg : (bitslice P).all (fun i => (dsts i).all (· == Reg.x6)) = true)
    (s : State) :
    ∃ s', runBlock isa (bitslice P) s = some s' ∧
      (∀ j < 8, ∀ p < 128, (s'.v (P j)).getLsbD p = (s.v (P (p % 8))).getLsbD (8 * (p / 8) + j)) ∧
      Keeps s s' := by
  obtain ⟨e', he, hpost⟩ := StraightV.of_check _ _ hchk
  have hok : StraightV.Ok orthoCfg s := ⟨fun _ h => absurd h (by simp [orthoCfg]), by simp [orthoCfg]⟩
  have hrel : StraightV.Rel (fun q => LaneRel K (assign (fun i => vdword (s.v (P i)) q) (2 ^ K)))
      orthoCfg (orthoEnv P) s := by
    refine ⟨fun r a h q _ => ?_, (fun _ _ hk => absurd hk (by simp [orthoCfg])), (fun _ _ h => by cases h)⟩
    simp only [orthoEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hqr := List.find?_some hk
    have hk8 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
    simp only [beq_iff_eq] at hqr
    subst hqr
    exact inWord_rel (fun i => vdword (s.v (P i)) q) (by omega_using [hk8, hK])
  obtain ⟨s', hs', p⟩ := StraightV.run (fun _ _ => lanes_sound) hok hrel he
  refine ⟨s', hs', fun j hj b hb => ?_, fun g h6 _ => p.gpr g ?_, p.rd, p.wr, p.sp, ?_⟩
  · obtain ⟨hv, hlt⟩ := outOk_spec (List.all_eq_true.mp hpost j (List.mem_range.mpr hj))
    have bits := outWord_rel_of_lt hlt (p.rel.reg (P j) _ hv (b / 64) (by omega_using [hb]))
      (b % 64) (Nat.mod_lt _ (by decide))
    have eb : 64 * (b / 64) + b % 64 = b := Nat.div_add_mod b 64
    rw [getLsbD_vdword _ (Nat.mod_lt _ (by decide)), eb] at bits
    rw [bits, orthoG, xorBits_cons, xorBits_nil, Bool.xor_false,
      bitOf_word _ _ _ (by omega_using [hj]),
      getLsbD_vdword _ (by omega_using [hj]),
      show b % 64 % 8 = b % 8 by omega_using [],
      show 64 * (b / 64) + (8 * (b % 64 / 8) + j) = 8 * (b / 8) + j by omega_using []]
  · simp only [Bool.not_eq_false, List.all_eq_true]
    intro i hi
    have := clobbers_eq_false_of_all (r := g) (List.all_eq_true.mp hg i hi) (by simpa using h6)
    simpa using this
  · refine p.frame.sub fun r hr => ⟨⟨s.gpr sb, 96⟩, by simp, ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by simp [orthoCfg])

/-! ## The layers that permute and XOR bytes -/

/-- No memory. -/
def noExt : StraightQ.Cfg := { ext := kp, exts := 0 }

/-- The bitsliced round key at `kp`. -/
def arkCfg : StraightQ.Cfg := { ext := kp, exts := 8 }

/-- The words `P 0 … P 7` are input words `0 … 7`. -/
def insOf (P : Nat → VReg) : List (VReg × Nat) := (List.range 8).map fun k => (P k, k)

/-- The outputs `P j`, bit `p` the XOR of the input bits `g j p`. -/
def outsOf (P : Nat → VReg) (g : Nat → Nat → List Nat) : List (VReg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (P j, g j)

theorem sr_check : StraightQ.check (lanes 128 10) noExt (StraightQ.linExt 0) (tbls B)
    (StraightQ.linEnv (insOf B) [(idxR, srIdx)]) (StraightQ.linPost 10 (outsOf B srG)) = true := by
  decide +kernel

theorem invSr_check : StraightQ.check (lanes 128 10) noExt (StraightQ.linExt 0) (tbls A)
    (StraightQ.linEnv (insOf A) [(idxR, invSrIdx)]) (StraightQ.linPost 10 (outsOf A invSrG)) = true := by
  decide +kernel

theorem mc_check : StraightQ.check (lanes 128 10) noExt (StraightQ.linExt 0) mcCore
    (StraightQ.linEnv (insOf B) [(idxR, rotIdx)]) (StraightQ.linPost 10 (outsOf A mcG)) = true := by
  decide +kernel

theorem invMc_check : StraightQ.check (lanes 128 10) noExt (StraightQ.linExt 0) (invMcPre ++ mcCore)
    (StraightQ.linEnv (insOf B) [(idxR, rotIdx)]) (StraightQ.linPost 10 (outsOf A invMcG)) = true := by
  decide +kernel

theorem arkA_check : StraightQ.check (lanes 128 11) arkCfg (StraightQ.linExt 8) (addRoundKey A)
    (StraightQ.linEnv (insOf A) []) (StraightQ.linPost 11 (outsOf A arkG)) = true := by
  decide +kernel

theorem arkB_check : StraightQ.check (lanes 128 11) arkCfg (StraightQ.linExt 8) (addRoundKey B)
    (StraightQ.linEnv (insOf B) []) (StraightQ.linPost 11 (outsOf B arkG)) = true := by
  decide +kernel

/-- A linear layer from the words `Pi` to the words `Po`, on the machine. -/
theorem lin_ok {k xb : Nat} {c : StraightQ.Cfg} {is : List Instr} {Pi Po : Nat → VReg}
    {cs : List (VReg × BitVec 128)} {g : Nat → Nat → List Nat}
    (hchk : StraightQ.check (lanes 128 k) c (StraightQ.linExt xb) is (StraightQ.linEnv (insOf Pi) cs)
      (StraightQ.linPost k (outsOf Po g)) = true)
    (hk : 1024 ≤ 2 ^ k) {s : State} (hok : StraightQ.Ok c s) (W : Nat → BitVec 128)
    (hW : ∀ i < 8, W i = s.v (Pi i)) (hcs : ∀ r v, (r, v) ∈ cs → s.v r = v)
    (hext : ∀ j < c.exts,
      128 * (xb + j) + 128 ≤ 2 ^ k ∧ W (xb + j) = s.mem.readW (vAddr (s.gpr c.ext) j) 128) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ j < 8, ∀ p < 128, (s'.v (Po j)).getLsbD p = xorBits W (g j p)) ∧
      s' = { s with v := s'.v } := by
  obtain ⟨s', hs', hout, hsame, -⟩ := StraightQ.linear_ok hchk hok W (fun r i hri => by
    simp only [insOf, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
    obtain ⟨i, hi, rfl, rfl⟩ := hri
    exact ⟨by omega_using [hk, hi], hW i hi⟩) hcs hext
  have hmem : ∀ j < 8, (Po j, g j) ∈ outsOf Po g := fun j hj => by
    simp only [outsOf, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩
  exact ⟨s', hs', fun j hj p hp => hout (Po j) (g j) (hmem j hj) p hp, hsame⟩

theorem noExt_ok (s : State) : StraightQ.Ok noExt s := fun _ h => absurd h (by simp [noExt])

/-- The bytes of the words `P 0 … P 7` permuted: bit `p` from bit `src p`. -/
theorem permBytes_wp {P : Nat → VReg} {c : BitVec 128} {g : Nat → Nat → List Nat} {src : Nat → Nat}
    (hchk : StraightQ.check (lanes 128 10) noExt (StraightQ.linExt 0) (tbls P)
      (StraightQ.linEnv (insOf P) [(idxR, c)]) (StraightQ.linPost 10 (outsOf P g)) = true)
    (hg : ∀ j p, g j p = [128 * j + src p]) (hsrc : ∀ p < 128, src p < 128)
    (hP : ∀ j < 8, P j ≠ idxR) (s : State) :
    WP isa (.block (permBytes P c)) s fun s' =>
      (∀ j < 8, ∀ p < 128, (s'.v (P j)).getLsbD p = (s.v (P j)).getLsbD (src p)) ∧ Keeps s s' := by
  unfold permBytes
  rw [WP.block_append_iff (M := isa)]
  refine WP.mono (Tbl.const128_ok s idxR c) fun t ⟨tv, to, tg, tm, trd, twr, tsp⟩ => ?_
  obtain ⟨s', hs', hout, hsame⟩ := lin_ok hchk (by decide) (noExt_ok t) (fun i => t.v (P i))
    (fun _ _ => rfl) (fun r v h => by
      simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact tv)
    (fun j hj => absurd hj (by simp [noExt]))
  have kt : Keeps s t := ⟨tg, trd, twr, tsp, by rw [tm]; exact Frame.refl _ _⟩
  refine WP.of_runBlock ⟨s', hs', fun j hj p hp => ?_, kt.trans (Keeps.of_v hsame)⟩
  rw [hout j hj p hp, hg, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ (hsrc p hp),
    to _ (hP j hj)]

theorem shiftRows_wp (s : State) :
    WP isa (.block (permBytes B srIdx)) s fun s' =>
      (∀ j < 8, ∀ p < 128, (s'.v (B j)).getLsbD p = (s.v (B j)).getLsbD (srSrc p)) ∧ Keeps s s' :=
  permBytes_wp sr_check (fun _ _ => rfl) (fun p hp => by simp only [srSrc]; omega_using [hp])
    (by decide) s

theorem invShiftRows_wp (s : State) :
    WP isa (.block (permBytes A invSrIdx)) s fun s' =>
      (∀ j < 8, ∀ p < 128, (s'.v (A j)).getLsbD p = (s.v (A j)).getLsbD (invSrSrc p)) ∧ Keeps s s' :=
  permBytes_wp invSr_check (fun _ _ => rfl) (fun p hp => by simp only [invSrSrc]; omega_using [hp])
    (by decide) s

/-- A layer of rotations of the columns, from `B 0 … B 7` to `A 0 … A 7`. -/
theorem columns_wp {core : List Instr} {terms : Nat → Nat → List (Nat × Nat)}
    (hchk : StraightQ.check (lanes 128 10) noExt (StraightQ.linExt 0) core
      (StraightQ.linEnv (insOf B) [(idxR, rotIdx)])
      (StraightQ.linPost 10 (outsOf A fun j p => (terms j p).map fun wt => 128 * wt.1 + wt.2)) = true)
    (hlt : ∀ j p, p < 128 → ∀ wt ∈ terms j p, wt.2 < 128) (s : State) :
    WP isa (.block (const128 idxR rotIdx ++ core)) s fun s' =>
      (∀ j < 8, ∀ p < 128, (s'.v (A j)).getLsbD p = termsXor (fun k => s.v (B k)) (terms j p)) ∧
        Keeps s s' := by
  rw [WP.block_append_iff (M := isa)]
  refine WP.mono (Tbl.const128_ok s idxR rotIdx) fun t ⟨tv, to, tg, tm, trd, twr, tsp⟩ => ?_
  obtain ⟨s', hs', hout, hsame⟩ := lin_ok hchk (by decide) (noExt_ok t) (fun i => s.v (B i))
    (fun i hi => (to _ (by revert i; decide)).symm) (fun r v h => by
      simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact tv)
    (fun j hj => absurd hj (by simp [noExt]))
  have kt : Keeps s t := ⟨tg, trd, twr, tsp, by rw [tm]; exact Frame.refl _ _⟩
  refine WP.of_runBlock ⟨s', hs', fun j hj p hp => ?_, kt.trans (Keeps.of_v hsame)⟩
  rw [hout j hj p hp, xorBits_map _ _ (hlt j p hp)]

theorem mixColumns_wp (s : State) :
    WP isa (.block mixColumns) s fun s' =>
      (∀ j < 8, ∀ p < 128, (s'.v (A j)).getLsbD p = termsXor (fun k => s.v (B k)) (mcTerms j p)) ∧
        Keeps s s' :=
  columns_wp mc_check (fun j p hp wt hwt => by
    obtain ⟨wk, -, rfl⟩ := List.mem_map.mp hwt
    exact down_lt p _ hp) s

theorem invMixColumns_wp (s : State) :
    WP isa (.block invMixColumns) s fun s' =>
      (∀ j < 8, ∀ p < 128, (s'.v (A j)).getLsbD p = termsXor (fun k => s.v (B k)) (invMcTerms j p)) ∧
        Keeps s s' :=
  columns_wp invMc_check (fun j p hp wt hwt => by
    obtain ⟨wk, -, rfl⟩ := List.mem_map.mp hwt
    exact down_lt p _ hp) s

/-- Word `j` of the bitsliced round key at `kp`. -/
abbrev keyWord (s : State) (j : Nat) : BitVec 128 := s.mem.readW (vAddr (s.gpr kp) j) 128

/-- AddRoundKey of the words `P 0 … P 7`. -/
theorem addRoundKey_ok {P : Nat → VReg}
    (hchk : StraightQ.check (lanes 128 11) arkCfg (StraightQ.linExt 8) (addRoundKey P)
      (StraightQ.linEnv (insOf P) []) (StraightQ.linPost 11 (outsOf P arkG)) = true)
    {s : State} (hok : StraightQ.Ok arkCfg s) :
    ∃ s', runBlock isa (addRoundKey P) s = some s' ∧
      (∀ j < 8, ∀ p < 128,
        (s'.v (P j)).getLsbD p = ((s.v (P j)).getLsbD p ^^ (keyWord s j).getLsbD p)) ∧
      Keeps s s' := by
  let W : Nat → BitVec 128 := fun i => if i < 8 then s.v (P i) else keyWord s (i - 8)
  obtain ⟨s', hs', hout, hsame⟩ := lin_ok hchk (by decide) hok W
    (fun i hi => by simp [W, hi]) (fun _ _ h => by cases h) (fun j hj => by
      simp only [arkCfg] at hj ⊢
      refine ⟨by omega_using [hj], ?_⟩
      simp [W, show ¬ 8 + j < 8 by omega_using []])
  refine ⟨s', hs', fun j hj p hp => ?_, Keeps.of_v hsame⟩
  rw [hout j hj p hp, arkG, xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ hp, bitOf_word _ _ _ hp]
  simp [W, hj, show ¬ 8 + j < 8 by omega_using []]

end VG.Proof.Aes.AArch64.Neon

end
