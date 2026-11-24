module

public import VerifiedGarbage.Impl.Aes.X86.Sse
public import VerifiedGarbage.Proof.Aes.Bitsliced
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Aes.InvSboxSpec
public import VerifiedGarbage.Proof.Aes.InvRounds
import VerifiedGarbage.Proof.Aes.Vector
public import VerifiedGarbage.Proof.Framework.X86.StraightX
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Impl.Aes.X86.Sse
meta import VerifiedGarbage.Proof.Aes.Bitsliced
meta import VerifiedGarbage.Proof.Aes.SboxSpec
meta import VerifiedGarbage.Proof.Aes.InvSboxSpec
meta import VerifiedGarbage.Proof.Aes.InvRounds
meta import VerifiedGarbage.Proof.Framework.X86.StraightX
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the kernel's checks of the layers, which a change to the proofs of the rounds need not run
-- again

@[expose] public section

namespace VG.Proof.Aes.X86.Sse

open VG VG.X86 VG.X86.StraightX VG.Bitslice VG.Impl.Aes.X86.Sse VG.Proof.Aes
open VG.Impl.Aes.X86 (sb)
open VG.Spec.Aes (sbox)

/-! ## The layout -/

/-- The row in dword `d`. -/
def rowOf (d : Nat) : Nat := d / 2 + 2 * (d % 2)

/-- Byte `r + 4c` of block `b` is at this position. -/
def pos (b i : Nat) : Nat := 32 * (2 * (i % 4 % 2) + i % 4 / 2) + 8 * (i / 4) + b

/-- The byte at position `p`. -/
def idx (p : Nat) : Nat := rowOf (p / 32) + 4 * (p / 8 % 4)

/-- Position `p` moved `k` rows down, and `row` columns right (`ShiftRows`). -/
def src (p k : Nat) : Nat :=
  let r := (rowOf (p / 32) + k) % 4
  32 * (2 * (r % 2) + r / 2) + 8 * ((p / 8 % 4 + r) % 4) + p % 8

/-! ## The layers, as atoms -/

def toBsG (j p : Nat) : List Nat := [128 * (p % 8) + (8 * idx p + j), 128 * 8 + (8 * idx p + j)]
def fromBsG (b t : Nat) : List Nat := [128 * (t % 8) + src (pos b (t / 8)) 0, 128 * 8 + t]
def linearG (j p : Nat) : List Nat := (mcWords j).map (fun wk => 128 * wk.1 + src p wk.2) ++ [128 * (8 + j) + p]
def bsKeyG (j p : Nat) : List Nat := [8 * idx p + j]

/-- The word of `{63}` in each byte. -/
def c63 : Nat := 0x63636363636363636363636363636363
/-- Bit `j` of `{63}` at every position. -/
def n63 (j : Nat) : Nat := if (0x63).testBit j then 2 ^ 128 - 1 else 0

/-- The state in slots `0 … 7`, the round keys at `kp`. -/
def roundCfg : Cfg := { base := sb, slots := slots, ext := kp, exts := 8 }
/-- The state, the schedule's round key at `ecx`. -/
def keyCfg : Cfg := { base := sb, slots := slots, ext := .ecx, exts := 1 }
/-- A bitsliced round key, from the schedule's at `ecx`. -/
def bsKeyCfg : Cfg := { base := kp, slots := 8, ext := .ecx, exts := 1 }

def qIns (j : Nat) : Option Nat := if j < 8 then some j else none
def qOuts (cst : Nat → Nat) (g : Nat → Nat → List Nat) : List (Nat × Nat × (Nat → List Nat)) :=
  (List.range 8).map fun j => (j, cst j, g j)

theorem toBs_check : check (lanes 128 11) keyCfg toBs (linEnv slots 1 8 qIns)
    (linPost slots 11 (qOuts (fun _ => 0) toBsG)) = true := by
  decide +kernel

theorem fromBs_check : check (lanes 128 11) keyCfg fromBs (linEnv slots 1 8 qIns)
    (linPost slots 11 (qOuts (fun _ => c63) fromBsG)) = true := by
  decide +kernel

theorem linear_check : check (lanes 128 11) roundCfg linear (linEnv slots 8 8 qIns)
    (linPost slots 11 (qOuts (fun _ => 0) linearG)) = true := by
  decide +kernel

theorem bsKey_check : check (lanes 128 7) bsKeyCfg bsKey (linEnv 8 1 0 (fun _ => none))
    (linPost 8 7 (qOuts n63 bsKeyG)) = true := by
  decide +kernel

/-- The place `InvShiftRows` moves to position `p`. -/
def invSrc (p : Nat) : Nat := 32 * (p / 32) + 8 * ((p / 8 % 4 + 4 - rowOf (p / 32)) % 4) + p % 8
/-- Position `p`, `k` rows down. -/
def down (p k : Nat) : Nat :=
  let r := (rowOf (p / 32) + k) % 4
  32 * (2 * (r % 2) + r / 2) + p % 32

def invFromBsG (b t : Nat) : List Nat := [128 * (t % 8) + invSrc (pos b (t / 8)), 128 * 8 + t]
def invLinearG (j p : Nat) : List Nat :=
  (invMcWords j).map (fun wk => 128 * wk.1 + invSrc (down p wk.2)) ++
    (invMcWords j).map (fun wk => 128 * (8 + wk.1) + down p wk.2)

theorem invToBs_check : check (lanes 128 11) keyCfg invToBs (linEnv slots 1 8 qIns)
    (linPost slots 11 (qOuts n63 toBsG)) = true := by
  decide +kernel

theorem invFromBs_check : check (lanes 128 11) keyCfg invFromBs (linEnv slots 1 8 qIns)
    (linPost slots 11 (qOuts (fun _ => 0) invFromBsG)) = true := by
  decide +kernel

theorem invLinear_check : check (lanes 128 11) roundCfg invLinear (linEnv slots 8 8 qIns)
    (linPost slots 11 (qOuts (fun _ => 0) invLinearG)) = true := by
  decide +kernel

def inT (k : Nat) : Nat := tableOf (fun c => c.testBit k) 256
def inTs : List Nat := (List.range 8).map inT

def sboxEnv : Env Nat := { slots := (List.range slots).map fun k => if k < 8 then some (inT k) else none }

/-- The S-box's tables, without the complements. -/
def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.slot j == some ((sboxT inTs).getD j 0 ^^^ (if (0x63).testBit j then 2 ^ 256 - 1 else 0))

def sboxCfg : Cfg := { base := sb, slots := slots, ext := sb, exts := 0 }

theorem sbox_check : check (table 128 256) sboxCfg sboxCode sboxEnv sboxPost = true := by
  decide +kernel

/-- The tables of the bits of the input XOR `{63}`. -/
def inT63 (k : Nat) : Nat := inT k ^^^ (if (0x63).testBit k then 2 ^ 256 - 1 else 0)
def inTs63 : List Nat := (List.range 8).map inT63

/-- The inverse S-box's tables, of the input XOR `{63}`. -/
def invSboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.slot j == some ((invSboxT inTs63).getD j 0)

theorem invSbox_check : check (table 128 256) sboxCfg invSboxCode sboxEnv invSboxPost = true := by
  decide +kernel

/-! ## The layers, on states -/

/-- The byte at position `p` of eight words: its bit `k` is bit `p` of word `k`. -/
def bsByte (Q : Nat → BitVec 128) (p : Nat) : Byte := ofBits 8 fun k => (Q k).getLsbD p

theorem getLsbD_bsByte (Q : Nat → BitVec 128) (p : Nat) {k : Nat} (hk : k < 8) :
    (bsByte Q p).getLsbD k = (Q k).getLsbD p := by
  rw [bsByte, getLsbD_ofBits]; simp [hk]

/-- The words `Q` hold the eight states `S`. -/
def BsRel (Q : Nat → BitVec 128) (S : Nat → Spec.Aes.State) : Prop :=
  ∀ b < 8, ∀ i < 16, bsByte Q (pos b i) = (S b).getD i 0

/-- The words `K` hold the round key `rk`, XORed with `{63}`, for all eight blocks. -/
def KeyRel (K : Nat → BitVec 128) (rk : List Byte) : Prop :=
  ∀ b < 8, ∀ i < 16, bsByte K (pos b i) = rk.getD i 0 ^^^ 0x63

/-- The words `Q` hold the eight blocks `S`, byte by byte. -/
def InRel (Q : Nat → BitVec 128) (S : Nat → Spec.Aes.State) : Prop :=
  ∀ b < 8, ∀ i < 16, ∀ j < 8, (Q b).getLsbD (8 * i + j) = ((S b).getD i 0).getLsbD j

/-- The word `w` holds the round key `rk`, byte by byte. -/
def RkRel (w : BitVec 128) (rk : List Byte) : Prop :=
  ∀ i < 16, ∀ j < 8, w.getLsbD (8 * i + j) = (rk.getD i 0).getLsbD j

/-- A state XORed with `{63}` in each byte. -/
def x63 (S : Spec.Aes.State) : Spec.Aes.State := Vector.ofFn fun i => S[i] ^^^ 0x63

theorem getD_x63 (S : Spec.Aes.State) {i : Nat} (hi : i < 16) : (x63 S).getD i 0 = S.getD i 0 ^^^ 0x63 := by
  rw [getD_eq _ hi, getD_eq _ hi, x63, Vector.getElem_ofFn]; rfl

theorem pos_lt {b i : Nat} (hb : b < 8) (hi : i < 16) : pos b i < 128 := by
  simp only [pos]; omega_using [hb, hi]

theorem pos_facts : ∀ b < 8, ∀ i < 16, pos b i % 8 = b ∧ idx (pos b i) = i := by decide

theorem src_pos : ∀ b < 8, ∀ i < 16, ∀ k < 4,
    src (pos b i) k = pos b ((i % 4 + k) % 4 + 4 * ((i / 4 + (i % 4 + k) % 4) % 4)) := by decide

theorem src_lt : ∀ p < 128, ∀ k < 4, src p k < 128 := by decide +kernel

theorem n63_bit {j p : Nat} (hp : p < 128) : (n63 j).testBit p = (0x63#8).getLsbD j := by
  rw [n63, show (0x63#8).getLsbD j = (0x63).testBit j from rfl]
  split
  · rename_i h; rw [Nat.testBit_two_pow_sub_one, decide_eq_true hp, h]
  · rename_i h; simp only [Nat.zero_testBit]; simpa using h

theorem c63_bits : ∀ i < 16, ∀ j < 8, c63.testBit (8 * i + j) = (0x63#8).getLsbD j := by decide +kernel

theorem xtimes_xor (a b : Byte) : Spec.Aes.xtimes (a ^^^ b) = Spec.Aes.xtimes a ^^^ Spec.Aes.xtimes b :=
  byte_ext fun j hj => by
    simp only [BitVec.getLsbD_xor, xtimes_bit _ hj]
    generalize decide (j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4) = d
    split <;> cases a.getLsbD 7 <;> cases b.getLsbD 7 <;> cases d <;> cases a.getLsbD (j - 1) <;>
      cases b.getLsbD (j - 1) <;> rfl

/-- A byte of `AddRoundKey` after `MixColumns`, `ShiftRows` and the S-box,
from bytes that leave out the S-box's `{63}` (`A`, at the rows from this one
down) and a key byte `K` XORed with it. -/
theorem mc63 (A : Nat → Byte) (K : Byte) :
    (Spec.Aes.xtimes ((A 0 ^^^ 0x63) ^^^ (A 1 ^^^ 0x63)) ^^^ (A 1 ^^^ 0x63) ^^^ (A 2 ^^^ 0x63) ^^^ (A 3 ^^^ 0x63)) ^^^
      (K ^^^ 0x63) =
    Spec.Aes.mul 0x02 (A 0) ^^^ Spec.Aes.mul 0x03 (A 1) ^^^ A 2 ^^^ A 3 ^^^ K := by
  rw [show (A 0 ^^^ 0x63) ^^^ (A 1 ^^^ 0x63) = A 0 ^^^ A 1 from byte_ext fun j _ => by
    simp only [BitVec.getLsbD_xor]
    cases (A 0).getLsbD j <;> cases (A 1).getLsbD j <;> cases (0x63 : BitVec 8).getLsbD j <;> rfl]
  rw [xtimes_xor, mul2, mul3]
  generalize Spec.Aes.xtimes (A 0) = x
  generalize Spec.Aes.xtimes (A 1) = y
  generalize A 1 = a; generalize A 2 = b; generalize A 3 = c
  exact byte_ext fun j _ => by
    simp only [BitVec.getLsbD_xor]
    cases (0x63 : BitVec 8).getLsbD j <;> cases x.getLsbD j <;> cases y.getLsbD j <;> cases a.getLsbD j <;>
      cases b.getLsbD j <;> cases c.getLsbD j <;> cases K.getLsbD j <;> rfl

/-- What `linear` does to the bytes: `g p k` is the byte `k` rows down from position `p` after ShiftRows. -/
theorem linear_byte {W : Nat → BitVec 128} {Q' : Nat → BitVec 128}
    (h : ∀ j < 8, ∀ p < 128, (Q' j).getLsbD p = xorBits W (linearG j p)) {p : Nat} (hp : p < 128) :
    bsByte Q' p = Spec.Aes.xtimes (bsByte W (src p 0) ^^^ bsByte W (src p 1)) ^^^ bsByte W (src p 1) ^^^
      bsByte W (src p 2) ^^^ bsByte W (src p 3) ^^^ bsByte (fun k => W (8 + k)) p := by
  refine byte_ext fun j hj => ?_
  have hw : ∀ w k, k < 4 → bitOf W (128 * w + src p k) = (W w).getLsbD (src p k) :=
    fun w k hk => bitOf_word W w _ (src_lt p hp k hk)
  have hk : bitOf W (128 * (8 + j) + p) = (W (8 + j)).getLsbD p := bitOf_word W _ _ hp
  rw [getLsbD_bsByte _ _ hj, h j hj p hp]
  simp only [BitVec.getLsbD_xor, xtimes_bit _ hj, getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ (show 7 < 8 by decide),
    getLsbD_bsByte _ _ (show j - 1 < 8 by omega_using [hj]), linearG, mcWords]
  revert hk hj
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => ?_
  | j + 8 => intro hj; omega
  all_goals
    intro _ hk
    simp (disch := decide) only [↓reduceIte, Nat.reduceEqDiff, Nat.reduceSub, or_self, or_true, or_false,
      List.map_cons, List.map_nil, List.nil_append, List.cons_append,
      xorBits_cons, xorBits_nil, hw, hk, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_xor,
      Bool.xor_false, Bool.xor_assoc]

open VG.Spec.Aes (subBytes shiftRows mixColumns addRoundKey)
open VG.Proof.Aes.Vector (getD_addRoundKey getD_mixColumns getD_shiftRows getD_subBytes)

theorem bs_sub {Q Q' : Nat → BitVec 128} {S : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ p < 128, (Q' j).getLsbD p = (sbox (bsByte Q p) ^^^ 0x63).getLsbD j) (hr : BsRel Q S) :
    BsRel Q' fun b => x63 (subBytes (S b)) := by
  intro b hb i hi
  rw [getD_x63 _ hi, getD_subBytes _ hi, ← hr b hb i hi]
  exact byte_ext fun j hj => by rw [getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi)]

theorem bs_linear {W Q' : Nat → BitVec 128} {T : Nat → Spec.Aes.State} {rk : List Byte}
    (h : ∀ j < 8, ∀ p < 128, (Q' j).getLsbD p = xorBits W (linearG j p)) (hr : BsRel W fun b => x63 (T b))
    (hk : KeyRel (fun k => W (8 + k)) rk) :
    BsRel Q' fun b => addRoundKey (mixColumns (shiftRows (T b))) rk := by
  intro b hb i hi
  have hs : ∀ k < 4, (i % 4 + k) % 4 + 4 * ((i / 4 + (i % 4 + k) % 4) % 4) < 16 := fun k _ => by omega_using []
  have hm : ∀ k, (i % 4 + k) % 4 + 4 * (i / 4) < 16 := fun k => by omega_using [hi]
  have e : ∀ k, ((i % 4 + k) % 4 + 4 * (i / 4)) % 4 = (i % 4 + k) % 4 := fun k => by omega_using []
  have e' : ∀ k, ((i % 4 + k) % 4 + 4 * (i / 4)) / 4 = i / 4 := fun k => by omega_using [hi]
  have hA : ∀ k < 4, bsByte W (src (pos b i) k) =
      (T b).getD ((i % 4 + k) % 4 + 4 * ((i / 4 + (i % 4 + k) % 4) % 4)) 0 ^^^ 0x63 := fun k hk => by
    rw [src_pos b hb i hi k hk, hr b hb _ (hs k hk), getD_x63 _ (hs k hk)]
  rw [linear_byte h (pos_lt hb hi), hA 0 (by decide), hA 1 (by decide), hA 2 (by decide), hA 3 (by decide),
    hk b hb i hi, getD_addRoundKey _ _ hi, getD_mixColumns _ hi]
  rw [getD_shiftRows _ (hm 0), getD_shiftRows _ (hm 1), getD_shiftRows _ (hm 2), getD_shiftRows _ (hm 3)]
  simp only [e, e']
  exact mc63 (fun k => (T b).getD ((i % 4 + k) % 4 + 4 * ((i / 4 + (i % 4 + k) % 4) % 4)) 0) _

theorem bs_toBs {W Q' : Nat → BitVec 128} {S : Nat → Spec.Aes.State} {rk : List Byte}
    (h : ∀ j < 8, ∀ p < 128, (Q' j).getLsbD p = xorBits W (toBsG j p)) (hr : InRel W S) (hk : RkRel (W 8) rk) :
    BsRel Q' fun b => addRoundKey (S b) rk := by
  intro b hb i hi
  obtain ⟨h1, h2⟩ := pos_facts b hb i hi
  rw [getD_addRoundKey _ _ hi]
  refine byte_ext fun j hj => ?_
  rw [getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi), toBsG, h1, h2, xorBits_cons, xorBits_cons, xorBits_nil,
    Bool.xor_false, bitOf_word _ _ _ (by omega_using [hi, hj]), bitOf_word _ _ _ (by omega_using [hi, hj]),
    hr b hb i hi j hj, hk i hi j hj, BitVec.getLsbD_xor]

theorem bs_fromBs {W Q' : Nat → BitVec 128} {T : Nat → Spec.Aes.State} {rk : List Byte}
    (h : ∀ b < 8, ∀ t < 128, (Q' b).getLsbD t = (c63.testBit t ^^ xorBits W (fromBsG b t)))
    (hr : BsRel W fun b => x63 (T b)) (hk : RkRel (W 8) rk) :
    InRel Q' fun b => addRoundKey (shiftRows (T b)) rk := by
  intro b hb i hi j hj
  have hs : i % 4 + 4 * ((i / 4 + i % 4) % 4) < 16 := by omega_using []
  have hsrc := src_pos b hb i hi 0 (by decide)
  rw [show (i % 4 + 0) % 4 = i % 4 by omega_using []] at hsrc
  rw [h b hb _ (by omega_using [hi, hj]), c63_bits i hi j hj, getD_addRoundKey _ _ hi, getD_shiftRows _ hi,
    fromBsG, show (8 * i + j) % 8 = j by omega_using [hj], show (8 * i + j) / 8 = i by omega_using [hj],
    xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (src_lt _ (pos_lt hb hi) 0 (by decide)), bitOf_word _ _ _ (by omega_using [hi, hj]),
    ← getLsbD_bsByte _ _ hj, hsrc, hr b hb _ hs, getD_x63 _ hs, hk i hi j hj, BitVec.getLsbD_xor,
    BitVec.getLsbD_xor]
  rw [show (0x63 : BitVec 8).getLsbD j = (0x63#8).getLsbD j from rfl]
  cases (0x63#8).getLsbD j <;> cases ((T b).getD (i % 4 + 4 * ((i / 4 + i % 4) % 4)) 0).getLsbD j <;>
    cases (rk.getD i 0).getLsbD j <;> rfl

theorem bs_key {W K : Nat → BitVec 128} {rk : List Byte}
    (h : ∀ j < 8, ∀ p < 128, (K j).getLsbD p = ((n63 j).testBit p ^^ xorBits W (bsKeyG j p)))
    (hk : RkRel (W 0) rk) : KeyRel K rk := by
  intro b hb i hi
  obtain ⟨-, h2⟩ := pos_facts b hb i hi
  refine byte_ext fun j hj => ?_
  have e : bitOf W (8 * i + j) = (W 0).getLsbD (8 * i + j) := by
    have := bitOf_word W 0 (8 * i + j) (by omega_using [hi, hj])
    rwa [Nat.mul_zero, Nat.zero_add] at this
  rw [getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi), n63_bit (pos_lt hb hi), bsKeyG, h2, xorBits_cons, xorBits_nil,
    Bool.xor_false, e, hk i hi j hj, BitVec.getLsbD_xor, Bool.xor_comm]
  rfl

/-! ## The layers, on the machine -/

/-- Slot `j`, of 16 bytes. -/
abbrev Q (s : State) (j : Nat) : BitVec 128 := s.mem.readW (xAddr (s.gpr sb) j) 128

/-- The region of the slots. -/
abbrev slotsR (s : State) : Region := ⟨(s.gpr sb).setWidth 64, 16 * slots⟩

theorem row_inTs {c : Nat} (hc : c < 256) : row inTs c = BitVec.ofNat 8 c := by
  refine row_ext fun j hj => ?_
  simp only [inTs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
    BitVec.getLsbD_ofNat, hj]

theorem sbox_keeps : (sboxCode.all fun i => i.dst == none) = true := by decide +kernel
theorem linear_keeps : (linear.all fun i => i.dst == none) = true := by decide +kernel
theorem toBs_keeps : (toBs.all fun i => i.dst == none || i.dst == some .eax) = true := by decide +kernel
theorem fromBs_keeps : (fromBs.all fun i => i.dst == none || i.dst == some .eax) = true := by decide +kernel
theorem bsKey_keeps : (bsKey.all fun i => i.dst == none || i.dst == some .eax) = true := by decide +kernel

theorem keep_all {is : List Instr} (h : (is.all fun i => i.dst == none) = true) (r : Reg) :
    (is.all fun i => i.dst != some r) = true :=
  List.all_eq_true.mpr fun i hi => by
    have := List.all_eq_true.mp h i hi
    rw [beq_iff_eq.mp this]; rfl

theorem keep_eax {is : List Instr} (h : (is.all fun i => i.dst == none || i.dst == some .eax) = true) {r : Reg}
    (hr : r ≠ .eax) : (is.all fun i => i.dst != some r) = true :=
  List.all_eq_true.mpr fun i hi => by
    have := List.all_eq_true.mp h i hi
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rcases this with h | h <;> rw [h]
    · rfl
    · exact bne_iff_ne.mpr fun e => hr (Option.some.inj e).symm

/-- The complement of a bit of the S-box, as a table. -/
theorem compl_bit {j c : Nat} (hc : c < 256) :
    (if (0x63).testBit j then 2 ^ 256 - 1 else 0).testBit c = (0x63 : BitVec 8).getLsbD j := by
  rw [show (0x63 : BitVec 8).getLsbD j = (0x63).testBit j from rfl]
  split
  · rename_i h; rw [Nat.testBit_two_pow_sub_one, decide_eq_true hc, h]
  · rename_i h; simp only [Nat.zero_testBit]; simpa using h

/-- The S-box, at every bit position of the words in slots `0 … 7`. -/
theorem sbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 128, (Q s' j).getLsbD p = (sbox (bsByte (Q s) p) ^^^ 0x63).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, s'.gpr r = s.gpr r) ∧ Frame [slotsR s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ sbox_check
  have hout : ∀ j < 8, e'.slot j =
      some ((sboxT inTs).getD j 0 ^^^ (if (0x63).testBit j then 2 ^ 256 - 1 else 0)) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    exact beq_iff_eq.mp this
  -- The run at bit position `p`, on the input formed by the bits `p`.
  have key : ∀ p < 128, ∃ s', runBlock isa sboxCode s = some s' ∧
      Post (TableRel p (bsByte (Q s) p).toNat) sboxCfg e' s s'
        (fun r => (sboxCode.all fun i => i.dst != some r) = false) := by
    intro p hp
    have hc := (bsByte (Q s) p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_, fun k a _ h => ?_, fun j _ hj _ => ?_, fun r v h => ?_⟩ he
    · revert h; cases r <;> intro h <;> cases h
    · obtain ⟨-, h'⟩ := getD_map_range h
      split at h'
      · rename_i hk8
        cases h'
        simp only [TableRel, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
          BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8, Q, sboxCfg]
      · cases h'
    · simp [sboxCfg] at hj
    · revert h; cases r <;> intro h <;> cases h
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega_using [])
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, fun r => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have hc := (bsByte (Q s) p).isLt
    have := p₁.rel.slot j _ (by simp [sboxCfg, slots]; omega_using [hj]) (hout j hj)
    have hb : s''.gpr sb = s.gpr sb := p₁.base
    simp only [TableRel, sboxCfg, hb] at this
    rw [Q, hb, ← this, Nat.testBit_xor, compl_bit hc, BitVec.getLsbD_xor, ← getLsbD_row _ _ hj,
      row_sboxT (by simp [inTs]) hc, row_inTs hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [keep_all sbox_keeps r]; exact Bool.noConfusion

theorem mem_qOuts {cst : Nat → Nat} {g : Nat → Nat → List Nat} {j : Nat} (hj : j < 8) :
    (j, cst j, g j) ∈ qOuts cst g := List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

theorem qIns_some {j i : Nat} (h : qIns j = some i) : j < 8 ∧ i = j := by
  unfold qIns at h
  split at h
  · rename_i hj; cases h; exact ⟨hj, rfl⟩
  · cases h

/-- What a layer of the round keeps, the registers `t` aside. -/
theorem round_layer {c : Cfg} (hb : c.base = sb) (hs : c.slots = slots) {is : List Instr} {cst : Nat → Nat}
    {g : Nat → Nat → List Nat}
    (hchk : check (lanes 128 11) c is (linEnv c.slots c.exts 8 qIns) (linPost c.slots 11 (qOuts cst g)) = true)
    {s : State} (hok : Ok c s) (he : c.exts ≤ 8) (W : Nat → BitVec 128) (hW : ∀ j < 8, W j = Q s j)
    (hK : ∀ j < c.exts, W (8 + j) = s.mem.readW (xAddr (s.gpr c.ext) j) 128)
    (hkb : (is.all fun i => i.dst != some sb) = true) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ j < 8, ∀ p < 128, (Q s' j).getLsbD p = ((cst j).testBit p ^^ xorBits W (g j p))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, (is.all fun i => i.dst != some r) = true → s'.gpr r = s.gpr r) ∧ Frame [slotsR s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, hrd, hwr, hg, hf⟩ := linear_ok hchk hok W (fun j i h _ => by
      obtain ⟨hj, rfl⟩ := qIns_some h
      exact ⟨by omega_using [hj], by rw [hW _ hj, hb]⟩) (fun j hj => ⟨by omega_using [hj, he], hK j hj⟩)
  refine ⟨s', hs', fun j hj p hp => ?_, hrd, hwr, hg, ?_⟩
  · rw [Q, hg sb hkb, ← hb]; exact hout j _ _ (mem_qOuts hj) p hp
  · simp only [slotRegion, hb, hs] at hf; exact hf

end VG.Proof.Aes.X86.Sse
