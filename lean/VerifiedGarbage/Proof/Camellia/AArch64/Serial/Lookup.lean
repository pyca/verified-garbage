module

public import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Core
public import VerifiedGarbage.Proof.Camellia.SerialPure
public import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Interleave
import Mathlib.Tactic.IntervalCases

/-! ### `Camellia.AArch64.Serial.ByteOps`, which only this module used -/

section

/-! # Byte-lane identities for Camellia's register substitution -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl
open VG.Impl.Camellia.AArch64.Serial
open VG.Proof.Camellia.Serial

theorem dup_byte (x : BitVec 64) (e : Nat) (he : e < 16) :
    vbyte (ofVDwords x x) e = byte x (e % 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vbyte, ofVDwords, byte, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    hi, decide_true, Bool.true_and]
  by_cases h : e < 8
  · simp only [show 8*e+i < 64 by omega_using [hi, h], ite_true, Nat.mod_eq_of_lt h]
  · simp only [show ¬8*e+i < 64 by omega_using [h], ite_false]
    congr 1
    omega_using [he, h]

/-! ## The rotations of a word's bytes -/

/-- The bytes through `SBOX4`, counting from the least significant. -/
def preChosen (e : Nat) : Bool := e%8 = 1 ∨ e%8 = 4
/-- The bytes through `SBOX2`. -/
def leftChosen (e : Nat) : Bool := e%8 = 3 ∨ e%8 = 6
/-- The bytes through `SBOX3`. -/
def rightChosen (e : Nat) : Bool := e%8 = 2 ∨ e%8 = 5

/-- What `rotateIn` leaves of `x`. -/
def rotIn (x : BitVec 64) : BitVec 64 :=
  ((x &&& keepIn) ||| (inHigh &&& x.rotateRight 63)) ||| (inLow &&& x.rotateRight 7)

/-- What `rotateOut` leaves of `y`. -/
def rotOut (y : BitVec 64) : BitVec 64 :=
  (((y &&& keepOut) ||| (outHigh &&& y.rotateRight 63)) ||| (outLow &&& y.rotateRight 7)) |||
    ((downLow &&& y.rotateRight 1) ||| (inLow &&& y.rotateRight 8).rotateRight 49)

/-- The masks' bits. -/
theorem mask_bits : ∀ i < 64,
    keepIn.getLsbD i = !preChosen (i / 8) ∧
    inHigh.getLsbD i = (preChosen (i / 8) && decide (i % 8 ≠ 0)) ∧
    inLow.getLsbD i = (preChosen (i / 8) && decide (i % 8 = 0)) ∧
    keepOut.getLsbD i = !(leftChosen (i / 8) || rightChosen (i / 8)) ∧
    outHigh.getLsbD i = (leftChosen (i / 8) && decide (i % 8 ≠ 0)) ∧
    outLow.getLsbD i = (leftChosen (i / 8) && decide (i % 8 = 0)) ∧
    downLow.getLsbD i = (rightChosen (i / 8) && decide (i % 8 ≠ 7)) ∧
    inLow.getLsbD ((i + 49) % 64) = (rightChosen (i / 8) && decide (i % 8 = 7)) := by
  decide

theorem ror_bit (x : BitVec 64) {r i : Nat} (hr : r < 64) (hi : i < 64) :
    (x.rotateRight r).getLsbD i = x.getLsbD ((i + r) % 64) := by
  rw [BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hr]
  by_cases h : i < 64 - r
  · simp only [h, ↓reduceIte]; congr 1; omega_using [h, hr]
  · simp only [h, ↓reduceIte, hi, decide_true, Bool.true_and]; congr 1; omega_using [h, hr, hi]

theorem getLsbD_byte (x : BitVec 64) (j : Nat) {k : Nat} (hk : k < 8) :
    (byte x j).getLsbD k = x.getLsbD (8 * j + k) := by
  simp only [byte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hk, decide_true, Bool.true_and]

theorem rotl1_bit (b : Byte) {k : Nat} (hk : k < 8) : (b.rotateLeft 1).getLsbD k = b.getLsbD ((k + 7) % 8) := by
  rw [BitVec.getLsbD_rotateLeft, show (1 : Nat) % 8 = 1 from rfl]
  by_cases h : k < 1
  · simp only [h, ↓reduceIte]; congr 1; omega_using [h]
  · simp only [h, ↓reduceIte, hk, decide_true, Bool.true_and]; congr 1; omega_using [h, hk]

theorem rotl7_bit (b : Byte) {k : Nat} (hk : k < 8) : (b.rotateLeft 7).getLsbD k = b.getLsbD ((k + 1) % 8) := by
  rw [BitVec.getLsbD_rotateLeft, show (7 : Nat) % 8 = 7 from rfl]
  by_cases h : k < 7
  · simp only [h, ↓reduceIte]; congr 1; omega_using [h]
  · simp only [h, ↓reduceIte, hk, decide_true, Bool.true_and]; congr 1; omega_using [h, hk]

/-- Bit `i` of `rotIn x`: of the bytes through `SBOX4`, the bit below it in its byte. -/
theorem rotIn_bit (x : BitVec 64) {i : Nat} (hi : i < 64) :
    (rotIn x).getLsbD i =
      x.getLsbD (if preChosen (i / 8) then 8 * (i / 8) + (i % 8 + 7) % 8 else i) := by
  obtain ⟨h0, h1, h2, -⟩ := mask_bits i hi
  simp only [rotIn, BitVec.getLsbD_or, BitVec.getLsbD_and, ror_bit x (by decide : 63 < 64) hi,
    ror_bit x (by decide : 7 < 64) hi, h0, h1, h2]
  by_cases hp : preChosen (i / 8) = true
  · have hp' := hp
    simp only [preChosen, decide_eq_true_eq] at hp'
    by_cases hk : i % 8 = 0
    · simp [hp, hk]
      congr 1; omega_using [hp', hk, hi]
    · simp [hp, hk]
      congr 1; omega_using [hp', hk, hi]
  · simp [hp]

/-- Bit `i` of `rotOut y`. -/
theorem rotOut_bit (y : BitVec 64) {i : Nat} (hi : i < 64) :
    (rotOut y).getLsbD i =
      y.getLsbD (if leftChosen (i / 8) then 8 * (i / 8) + (i % 8 + 7) % 8
        else if rightChosen (i / 8) then 8 * (i / 8) + (i % 8 + 1) % 8 else i) := by
  obtain ⟨-, -, -, h3, h4, h5, h6, h7⟩ := mask_bits i hi
  simp only [rotOut, BitVec.getLsbD_or, BitVec.getLsbD_and, ror_bit y (by decide : 63 < 64) hi,
    ror_bit y (by decide : 7 < 64) hi, ror_bit y (by decide : 1 < 64) hi,
    ror_bit (inLow &&& y.rotateRight 8) (by decide : 49 < 64) hi,
    ror_bit y (by decide : 8 < 64) (Nat.mod_lt (i + 49) (by decide : 0 < 64)), h3, h4, h5, h6, h7]
  by_cases hl : leftChosen (i / 8) = true
  · have hl' := hl
    simp only [leftChosen, decide_eq_true_eq] at hl'
    have hr : rightChosen (i / 8) = false := by
      simp only [rightChosen, decide_eq_false_iff_not]; omega_using [hl']
    by_cases hk : i % 8 = 0
    · simp [hl, hr, hk]
      congr 1; omega_using [hl', hk, hi]
    · simp [hl, hr, hk]
      congr 1; omega_using [hl', hk, hi]
  · by_cases hr : rightChosen (i / 8) = true
    · have hr' := hr
      simp only [rightChosen, decide_eq_true_eq] at hr'
      by_cases hk : i % 8 = 7
      · simp [hl, hr, hk]
        congr 1; omega_using [hr', hk, hi]
      · simp [hl, hr, hk]
        congr 1; omega_using [hr', hk, hi]
    · simp [hl, hr]

/-- The bytes through `SBOX4` are rotated left by one bit. -/
theorem rotIn_byte (x : BitVec 64) (j : Nat) (hj : j < 8) :
    byte (rotIn x) j = if preChosen j then (byte x j).rotateLeft 1 else byte x j := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [getLsbD_byte _ _ hk, rotIn_bit _ (by omega_using [hj, hk]), show (8 * j + k) / 8 = j by omega_using [hk],
    show (8 * j + k) % 8 = k by omega_using [hk]]
  cases preChosen j
  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [getLsbD_byte _ _ hk]
  · simp only [↓reduceIte]; rw [rotl1_bit _ hk, getLsbD_byte _ _ (Nat.mod_lt _ (by decide))]

theorem chosen_disjoint : ∀ j < 8, ¬(leftChosen j = true ∧ rightChosen j = true) := by decide

/-- The bytes through `SBOX2` are rotated left by one bit, those through `SBOX3` by seven. -/
theorem rotOut_byte (y : BitVec 64) (j : Nat) (hj : j < 8) :
    byte (rotOut y) j =
      (let c := if leftChosen j then (byte y j).rotateLeft 1 else byte y j
       if rightChosen j then c.rotateLeft 7 else c) := by
  have hd := chosen_disjoint j hj
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [getLsbD_byte _ _ hk, rotOut_bit _ (by omega_using [hj, hk]), show (8 * j + k) / 8 = j by omega_using [hk],
    show (8 * j + k) % 8 = k by omega_using [hk]]
  cases hl : leftChosen j <;> cases hr : rightChosen j
  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [getLsbD_byte _ _ hk]
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [rotl7_bit _ hk, getLsbD_byte _ _ (Nat.mod_lt _ (by decide))]
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [rotl1_bit _ hk, getLsbD_byte _ _ (Nat.mod_lt _ (by decide))]
  · exact absurd ⟨hl, hr⟩ hd

/-- A word is its bytes. -/
theorem eq_packed (x : BitVec 64) (t : Nat → Byte) (h : ∀ j < 8, byte x j = t j) : x = packed t := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h₁ := congrArg (fun b : Byte => b.getLsbD (i%8)) (h (i/8) (by omega_using [hi]))
  have h₂ := congrArg (fun b : Byte => b.getLsbD (i%8)) (byte_packed t (i/8) (by omega_using [hi]))
  simp only [getLsbD_byte _ _ (show i % 8 < 8 by omega_using []), show 8*(i/8)+i%8=i by omega_using []] at h₁ h₂
  exact h₁.trans h₂.symm

theorem low64_eq_packed (v : BitVec 128) (t : Nat → Byte)
    (h : ∀ j < 8, vbyte v j = t j) : v.extractLsb' 0 64 = packed t := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h₁ := congrArg (fun b : Byte => b.getLsbD (i%8)) (h (i/8) (by omega_using [hi]))
  have h₂ := congrArg (fun b : Byte => b.getLsbD (i%8))
    (byte_packed t (i/8) (by omega_using [hi]))
  simp only [vbyte, BitVec.getLsbD_extractLsb', show i%8 < 8 by omega_using [],
    decide_true, Bool.true_and, show 8*(i/8)+i%8=i by omega_using []] at h₁
  simp only [byte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    show i%8 < 8 by omega_using [], decide_true, Bool.true_and,
    show 8*(i/8)+i%8=i by omega_using []] at h₂
  simp only [BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and,Nat.zero_add]
  exact h₁.trans h₂.symm

end VG.Proof.Camellia.AArch64.Serial

end

end


/-! # Camellia's four S-box variants through one register table -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl
open VG.Impl.Camellia.AArch64.Serial
open VG.Proof.Camellia.Serial

def Constants (s : State) : Prop :=
  s.v .v4 = bc 64 ∧ s.v .v5 = bc 128 ∧ s.v .v6 = bc 192

/-- The masks of the rotations, in their registers. -/
def Masks (s : State) : Prop :=
  s.gpr .x0 = keepIn ∧ s.gpr .x3 = inHigh ∧ s.gpr .x4 = inLow ∧ s.gpr .x9 = keepOut ∧
  s.gpr .x13 = outHigh ∧ s.gpr .x14 = outLow ∧ s.gpr .x15 = downLow

/-- The masks' registers. -/
def maskRegs : List Reg := [.x0, .x3, .x4, .x9, .x13, .x14, .x15]

theorem Masks.of_regs {s t : State} (hm : Masks s) (h : ∀ r ∈ maskRegs, t.gpr r = s.gpr r) : Masks t :=
  ⟨(h _ (by decide)).trans hm.1, (h _ (by decide)).trans hm.2.1, (h _ (by decide)).trans hm.2.2.1,
    (h _ (by decide)).trans hm.2.2.2.1, (h _ (by decide)).trans hm.2.2.2.2.1,
    (h _ (by decide)).trans hm.2.2.2.2.2.1, (h _ (by decide)).trans hm.2.2.2.2.2.2⟩

def Table (s : State) : Prop :=
  ∀ k < 256, tbyte s.v k = Spec.Camellia.sbox1Table.getD k 0

theorem Constants.preserved {s t : State} (hc : Constants s)
    (hv : VOnly [.v0,.v1,.v2,.v3] s t) : Constants t :=
  ⟨(hv.2 _ (by decide)).trans hc.1,(hv.2 _ (by decide)).trans hc.2.1,
    (hv.2 _ (by decide)).trans hc.2.2⟩

theorem Masks.preserved {s t : State} (hm : Masks s)
    (hv : VOnly [.v0,.v1,.v2,.v3] s t) : Masks t :=
  hm.of_regs fun r _ => congrFun hv.gpr r

theorem Table.preserved {s t : State} (ht : Table s)
    (hv : VOnly [.v0,.v1,.v2,.v3] s t) : Table t := by
  intro k hk
  rw [tbyte_congr' (fun j hj => hv.2 _ (by
    have hn := treg_ne j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1⟩)) k hk]
  exact ht k hk

theorem indices_run (s : State) (hc : Constants s) :
    ∃ t, runBlock isa indices s = some t ∧
      t.v .v0 = s.v .v0 ∧
      (∀ e < 16, vbyte (t.v .v1) e = vbyte (s.v .v0) e ^^^ 64) ∧
      (∀ e < 16, vbyte (t.v .v2) e = vbyte (s.v .v0) e ^^^ 128) ∧
      (∀ e < 16, vbyte (t.v .v3) e = vbyte (s.v .v0) e ^^^ 192) ∧
      VOnly [.v0,.v1,.v2,.v3] s t := by
  let a := s.setV .v1 (s.v .v0 ^^^ s.v .v4)
  let b := a.setV .v2 (a.v .v0 ^^^ a.v .v5)
  let c := b.setV .v3 (b.v .v0 ^^^ b.v .v6)
  have h0 : c.v .v0 = s.v .v0 := by simp [c,b,a,State.setV]
  have h1 : c.v .v1 = s.v .v0 ^^^ bc 64 := by simp [c,b,a,State.setV,hc.1]
  have h2 : c.v .v2 = s.v .v0 ^^^ bc 128 := by simp [c,b,a,State.setV,hc.2.1]
  have h3 : c.v .v3 = s.v .v0 ^^^ bc 192 := by simp [c,b,a,State.setV,hc.2.2]
  refine ⟨c,?_,h0,?_,?_,?_,?_⟩
  · simp only [indices,runBlock_cons,exec_eorv,runStep_some,runBlock_nil]
    rfl
  · intro e he; rw [h1,vbyte_xor,vbyte_bc _ he]
  · intro e he; rw [h2,vbyte_xor,vbyte_bc _ he]
  · intro e he; rw [h3,vbyte_xor,vbyte_bc _ he]
  · exact ((VOnly.setV s (by simp) _).trans
      (VOnly.setV a (by simp) _)).trans (VOnly.setV b (by simp) _)

/-- Lookup in the single SBOX1 table, retaining every prepared constant. -/
theorem lookup_run (s : State) (hc : Constants s) (ht : Table s) :
    ∃ t, runBlock isa (indices ++ VG.Impl.Tbl.AArch64.select true) s = some t ∧
      (∀ e < 16, vbyte (t.v .v0) e = Spec.Camellia.sbox1 (vbyte (s.v .v0) e)) ∧
      VOnly [.v0,.v1,.v2,.v3] s t := by
  obtain ⟨a,ha,h0,h1,h2,h3,hv⟩ := indices_run s hc
  let I := fun e => vbyte (s.v .v0) e
  obtain ⟨b,hb,bo,bv⟩ := select_full_run (s := a) I
    (fun e _ => by rw [h0]) h1 h2 h3
  refine ⟨b,?_,?_,hv.trans bv⟩
  · rw [VG.Interleave.runBlock_append,ha,Option.bind_some,hb]
  · intro e he
    rw [bo e he,ht.preserved hv _ (I e).isLt]
    rfl

/-- The rotations surrounding SBOX1 are exactly SBOX1, SBOX2, SBOX3 and SBOX4. -/
theorem substituted_byte (x : BitVec 64) (j : Nat) (hj : j < 8) :
    (let a := if preChosen j then (byte x j).rotateLeft 1 else byte x j
     let b := Spec.Camellia.sbox1 a
     let c := if leftChosen j then b.rotateLeft 1 else b
     if rightChosen j then c.rotateLeft 7 else c) = substitutedByte x j := by
  interval_cases j <;> rfl

/-- `rotateIn`: the bytes through `SBOX4` rotated. -/
theorem rotateIn_run (s : State) (hm : Masks s) :
    ∃ t, runBlock isa rotateIn s = some t ∧ t.gpr .x10 = rotIn (s.gpr .x10) ∧
      (∀ r, r ∉ [.x10,.x11,.x12,.x16] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a := s.write .x .x11 (s.read .x .x10 &&& s.read .x .x0)
  let b := a.write .x .x12 (a.read .x .x3 &&& (a.read .x .x10).rotateRight 63)
  let c := b.write .x .x16 (b.read .x .x4 &&& (b.read .x .x10).rotateRight 7)
  let d := c.write .x .x11 (c.read .x .x11 ||| c.read .x .x12)
  let t := d.write .x .x10 (d.read .x .x11 ||| d.read .x .x16)
  refine ⟨t,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · rfl
  · simp only [t,d,c,b,a,State.read,Size.bits,gpr_write,BitVec.setWidth_eq,↓reduceIte,reduceCtorEq,
      hm.1,hm.2.1,hm.2.2.1,rotIn]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [t,d,c,b,a,gpr_write_of_ne _ _ _ hr.1,gpr_write_of_ne _ _ _ hr.2.1,
      gpr_write_of_ne _ _ _ hr.2.2.1,gpr_write_of_ne _ _ _ hr.2.2.2]

/-- `rotateOut`: the bytes through `SBOX2` and `SBOX3` rotated. -/
theorem rotateOut_run (s : State) (hm : Masks s) :
    ∃ t, runBlock isa rotateOut s = some t ∧ t.gpr .x10 = rotOut (s.gpr .x10) ∧
      (∀ r, r ∉ [.x10,.x11,.x12,.x16,.x17] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a := s.write .x .x11 (s.read .x .x10 &&& s.read .x .x9)
  let b := a.write .x .x12 (a.read .x .x13 &&& (a.read .x .x10).rotateRight 63)
  let c := b.write .x .x16 (b.read .x .x14 &&& (b.read .x .x10).rotateRight 7)
  let d := c.write .x .x17 (c.read .x .x15 &&& (c.read .x .x10).rotateRight 1)
  let e := d.write .x .x10 (d.read .x .x4 &&& (d.read .x .x10).rotateRight 8)
  let f := e.write .x .x17 (e.read .x .x17 ||| (e.read .x .x10).rotateRight 49)
  let g := f.write .x .x11 (f.read .x .x11 ||| f.read .x .x12)
  let h := g.write .x .x11 (g.read .x .x11 ||| g.read .x .x16)
  let t := h.write .x .x10 (h.read .x .x11 ||| h.read .x .x17)
  refine ⟨t,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · rfl
  · simp only [t,h,g,f,e,d,c,b,a,State.read,Size.bits,gpr_write,BitVec.setWidth_eq,↓reduceIte,reduceCtorEq,
      hm.2.2.1,hm.2.2.2.1,hm.2.2.2.2.1,hm.2.2.2.2.2.1,hm.2.2.2.2.2.2,rotOut]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [t,h,g,f,e,d,c,b,a,gpr_write_of_ne _ _ _ hr.1,gpr_write_of_ne _ _ _ hr.2.1,
      gpr_write_of_ne _ _ _ hr.2.2.1,gpr_write_of_ne _ _ _ hr.2.2.2.1,gpr_write_of_ne _ _ _ hr.2.2.2.2]

/-- The complete constant-time substitution preserves the register-resident table. -/
theorem substitute_run (s : State) (hc : Constants s) (hm : Masks s) (ht : Table s) :
    ∃ t, runBlock isa substitute s = some t ∧
      t.gpr .x10 = substituted (s.gpr .x10) ∧
      (∀ r, r ∉ [.x10,.x11,.x12,.x16,.x17] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ v, v ∉ [.v0,.v1,.v2,.v3] → t.v v = s.v v) := by
  obtain ⟨p,pe,pv,pg,pm,prd,pwr,psp,pvec⟩ := rotateIn_run s hm
  have pc : Constants p := by simpa only [Constants,pvec] using hc
  have pt : Table p := by simpa only [Table,pvec] using ht
  let a := p.setV .v0 (ofVDwords (p.gpr .x10) (p.gpr .x10))
  have av : VOnly [.v0,.v1,.v2,.v3] p a := VOnly.setV p (by simp) _
  obtain ⟨c,ce,cb,cv⟩ := lookup_run a (pc.preserved av) (pt.preserved av)
  have ac := av.trans cv
  let g := c.write .x .x10 ((c.v .v0).extractLsb' 0 64)
  have word : g.gpr .x10 = packed fun j => Spec.Camellia.sbox1 (byte (rotIn (s.gpr .x10)) j) := by
    rw [show g.gpr .x10 = (c.v .v0).extractLsb' 0 64 by
      simp only [g,gpr_write_self,Size.bits,BitVec.setWidth_eq]]
    apply low64_eq_packed
    intro j hj
    rw [cb j (by omega_using [hj]),show a.v .v0 = ofVDwords (p.gpr .x10) (p.gpr .x10) from rfl,
      dup_byte _ j (by omega_using [hj]),Nat.mod_eq_of_lt hj,pv]
  have gother : ∀ r, r ∉ [.x10,.x11,.x12,.x16] → g.gpr r = s.gpr r := by
    intro r hr
    have h10 : r ≠ .x10 := fun h => hr (by rw [h]; exact List.mem_cons_self)
    rw [show g.gpr r = c.gpr r from gpr_write_of_ne _ _ _ h10,ac.gpr,pg r hr]
  have gm : Masks g := hm.of_regs fun r hr => gother r (by revert r; decide)
  obtain ⟨t,te,tv,tg,tm,trd,twr,tsp,tvec⟩ := rotateOut_run g gm
  refine ⟨t,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hdup : runBlock isa [.vop (.dup .d2 .v0 .x10)] p = some a := rfl
    have eq : substitute = rotateIn ++ ([.vop (.dup .d2 .v0 .x10)] ++
        ((indices ++ VG.Impl.Tbl.AArch64.select true) ++ ([.umov .x .x10 .v0 0] ++ rotateOut))) := by
      simp only [substitute,List.append_assoc]
    rw [eq,VG.Interleave.runBlock_append,pe,Option.bind_some,
      VG.Interleave.runBlock_append,hdup,Option.bind_some,
      VG.Interleave.runBlock_append,ce,Option.bind_some,
      VG.Interleave.runBlock_append,runBlock_cons]
    rw [show exec (.umov .x .x10 .v0 0) c = some g by simp [exec,Size.bits,g]]
    rw [runStep_some,runBlock_nil,Option.bind_some,te]
  · rw [tv,word,substituted]
    refine eq_packed _ _ fun j hj => ?_
    rw [rotOut_byte _ j hj,byte_packed _ j hj,rotIn_byte _ j hj]
    exact substituted_byte _ j hj
  · intro r hr
    have h4 : r ∉ [.x10,.x11,.x12,.x16] := fun h => hr (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      rcases h with h | h | h | h <;> simp [h])
    rw [tg r hr,gother r h4]
  · rw [tm]; exact ac.mem.trans pm
  · rw [trd]; exact ac.rd.trans prd
  · rw [twr]; exact ac.wr.trans pwr
  · rw [tsp]; change c.sp = s.sp; rw [ac.1,psp]
  · intro v hv
    rw [tvec]; change c.v v = s.v v; rw [ac.2 v hv,pvec]

end VG.Proof.Camellia.AArch64.Serial
