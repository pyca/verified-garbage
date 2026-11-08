module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Run
public import VerifiedGarbage.Proof.Blowfish.F
public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Blowfish.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep

/-!
# Blowfish on PPC64LE: an S-box lookup

`lookup_run`: `lookup j` leaves S-box `j`'s entry for the byte `3 - j` of
xL's low word in the accumulator's low word, changing only the lookup's
registers (and vector registers).
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE

open VG VG.PPC64LE VG.Impl.Blowfish.PPC64LE VG.Spec.Blowfish VG.Proof.Blowfish

/-- What a lookup needs: the schedule at `r3` readable and zero in `r0`. -/
structure LookEnv (s : State) : Prop where
  rd : ∀ o n, o + n ≤ 4168 → InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 o) n
  zero : s.gpr .r0 = 0#64

/-- The registers a lookup writes. -/
def lookRegs : List Reg := [.r9, .r10, .r11, .r12, .r14, .r15]

theorem LookEnv.keep {s t : State} (E : LookEnv s) {rs : List Reg} (h : Keep rs s t)
    (h3 : Reg.r3 ∉ rs) (h0 : Reg.r0 ∉ rs) : LookEnv t := by
  refine ⟨fun o n ho => ?_, by rw [h.gpr h0]; exact E.zero⟩
  rw [h.gpr h3, h.2.1, h.2.2]; exact E.rd o n ho

theorem lo_zero : lo 0#64 = 0#32 := rfl

theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero .d r) s = some (s.gpr r != 0#64) := by
  simp only [eval, State.read, BitVec.setWidth_eq]; rfl

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero .d r) s = some (s.gpr r == 0#64) := by
  simp only [eval, State.read, BitVec.setWidth_eq]; rfl

/-- `a - c` (as doublewords, both below `2 ^ 64`) is nonzero iff `a ≠ c`. -/
theorem ofNat_sub_bne {a c : Nat} (ha : a < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 c != 0#64) = !decide (a = c) := by
  by_cases h : a = c
  · subst h; simp
  · have : BitVec.ofNat 64 a - BitVec.ofNat 64 c ≠ 0#64 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
      omega_arith
    simp [this, h]

theorem ofNat_bne_zero {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a != 0#64) = !decide (a = 0) := by
  by_cases h : a = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 a ≠ 0#64 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at this
      omega_arith
    simp [this, h]

/-! ## The index -/

theorem index_val (x : BitVec 64) {j : Nat} (hj : j < 4) :
    (x <<< (32 + 8 * j)) >>> 56 = (quarter (lo x) j).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [quarter, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft]
  by_cases h8 : i < 8
  · simp only [h8, decide_true, Bool.true_and, show 56 + i < 64 by omega_arith,
      show ¬ (56 + i < 32 + 8 * j) by omega_arith, decide_false, Bool.not_false,
      show 8 * (3 - j) + i < 32 by omega_arith]
    rw [decide_eq_true hi, Bool.true_and]
    congr 1; omega_arith
  · simp only [h8, decide_false, Bool.false_and]
    by_cases h : 56 + i < 64
    · omega_arith
    · simp [h]

theorem index_run (s : State) {j : Nat} (hj : j < 4) :
    WP isa (.block (index j)) s fun t =>
      t.gpr .r9 = (quarter (lo (s.gpr .r4)) j).setWidth 64 ∧ t.mem = s.mem := by
  rw [← index_val _ hj]
  unfold index
  brun [show 32 + 8 * j < 64 by omega_arith]

/-! ## Vector values -/

theorem read_sixteen (m : Mem) (a : Addr) : m.read a 16 = m.readW a 128 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

/-- `c` in every byte. -/
def splatV (c : Byte) : BitVec 128 := ofVBytes fun _ => c

theorem vbyte_splatV (c : Byte) (i : Nat) : vbyte (splatV c) i = c := by
  by_cases hi : i < 16
  · exact vbyte_packed _ hi
  · have : vbyte (splatV c) i = vbyte (splatV c) 15 := by
      simp only [vbyte, show 15 - i = 0 by omega]
    rw [this]; exact vbyte_packed _ (by decide)

theorem vbyte_zero (i : Nat) : vbyte 0#128 i = 0#8 := by simp [vbyte]

theorem vbyte_top (x u : BitVec 64) : vbyte (x <<< 56 ++ u) 0 = x.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  simp only [show ¬ 8 * (15 - 0) + i < 64 by omega, ite_false, show 8 * (15 - 0) + i - 64 < 64 by omega,
    decide_true, Bool.true_and, show ¬ 8 * (15 - 0) + i - 64 < 56 by omega, decide_false, Bool.not_false]
  congr 1; omega

theorem perm_splat0 (x u : BitVec 64) :
    (ofVBytes fun i =>
      if (vbyte (0#128) i).toNat % 32 < 16 then vbyte (x <<< 56 ++ u) ((vbyte (0#128) i).toNat % 32)
      else vbyte (x <<< 56 ++ u) ((vbyte (0#128) i).toNat % 32 - 16)) = splatV (x.setWidth 8) := by
  simp only [vbyte_zero, BitVec.toNat_zero, Nat.zero_mod, show (0 : Nat) < 16 by decide, ite_true, vbyte_top]
  rfl

theorem setWidth_xor7 (idx : Byte) : (idx.setWidth 64 ^^^ 7#64).setWidth 8 = idx ^^^ 7#8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem setWidth_shr5 (idx : Byte) : (idx.setWidth 64 >>> 5).setWidth 8 = idx >>> 5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  by_cases h : 5 + i < 8 <;> simp [h, show 5 + i < 64 by omega]

theorem vbyte_hot (u : BitVec 64) {k : Nat} (hk : k < 8) :
    vbyte (255#64 <<< 56 ++ u) k = if k = 0 then 255#8 else 0#8 := by
  have e : vbyte (255#64 <<< 56 ++ u) k = (255#64 <<< 56).extractLsb' (8 * (7 - k)) 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
      show ¬ 8 * (15 - k) + i < 64 by omega, ite_false]
    congr 1; omega
  rw [e]
  have : ∀ k < 8, (255#64 <<< 56).extractLsb' (8 * (7 - k)) 8 = if k = 0 then 255#8 else 0#8 := by decide
  exact this k hk

/-! ## The start -/

theorem start_run (s : State) {j : Nat} (hj : j < 4) {idx : Byte} (h9 : s.gpr .r9 = idx.setWidth 64) :
    WP isa (.block (lookupStart j)) s fun t =>
      t.vpr .v0 = 0#128 ∧ t.vpr .v1 = splatV (idx ^^^ 7#8) ∧ t.vpr .v2 = splatV (idx >>> 5) ∧
      (∀ k < 8, vbyte (t.vpr .v3) k = if k = 0 then 255#8 else 0#8) ∧
      t.gpr .r15 = s.gpr .r3 + BitVec.ofNat 64 (1024 * j) ∧ t.gpr .r11 = 16#64 ∧ t.gpr .r14 = 256#64 ∧
      t.gpr .r9 = 272#64 ∧ t.mem = s.mem := by
  unfold lookupStart splat vperm
  brun [reduceVOpEval, vZero, vIdx, vChunk, vHot, vpr_writeV, gpr_writeV, mem_writeV, ↓read_sixteen,
    show 1024 * j < 32768 by omega, BitVec.xor_self, h9, perm_splat0, setWidth_xor7, setWidth_shr5]
  intro k hk; rw [vbyte_hot _ hk]

/-! ## A row -/

theorem row_run (u : State) {j : Nat} (hj : j < 4) {rp : Addr} {M : BitVec 128} (h15 : u.gpr .r15 = rp)
    (h0 : u.gpr .r0 = 0#64) (h11 : u.gpr .r11 = 16#64) (h14 : u.gpr .r14 = 256#64) (h9 : u.gpr .r9 = 272#64)
    (hM : (ofVBytes fun i => if (vbyte (u.vpr .v2) i).toNat % 32 < 16 then
        vbyte (u.vpr .v3) ((vbyte (u.vpr .v2) i).toNat % 32)
      else vbyte (u.vpr .v3) ((vbyte (u.vpr .v2) i).toNat % 32 - 16)) = M)
    (a0 : InRegions (u.rd ++ u.wr) rp 16) (a16 : InRegions (u.rd ++ u.wr) (rp + 16#64) 16)
    (a256 : InRegions (u.rd ++ u.wr) (rp + 256#64) 16) (a272 : InRegions (u.rd ++ u.wr) (rp + 272#64) 16)
    (b0 : InRegions (u.rd ++ u.wr) (rp + 512#64) 16) (b16 : InRegions (u.rd ++ u.wr) (rp + 512#64 + 16#64) 16)
    (b256 : InRegions (u.rd ++ u.wr) (rp + 512#64 + 256#64) 16)
    (b272 : InRegions (u.rd ++ u.wr) (rp + 512#64 + 272#64) 16) :
    WP isa (.block (row j)) u fun t =>
      let sel := fun (v : VReg) (a : Addr) => (u.vpr v &&& ~~~M) ||| (swapDwords (u.mem.readW a 128) &&& M)
      t.vpr .v6 = sel .v6 rp ∧ t.vpr .v7 = sel .v7 (rp + 16#64) ∧ t.vpr .v8 = sel .v8 (rp + 256#64) ∧
      t.vpr .v9 = sel .v9 (rp + 272#64) ∧ t.vpr .v10 = sel .v10 (rp + 512#64) ∧
      t.vpr .v11 = sel .v11 (rp + 512#64 + 16#64) ∧ t.vpr .v12 = sel .v12 (rp + 512#64 + 256#64) ∧
      t.vpr .v13 = sel .v13 (rp + 512#64 + 272#64) ∧
      t.vpr .v3 = BitVec.extractLsb' 128 128 ((u.vpr .v0 ++ u.vpr .v3) <<< 120) ∧
      t.vpr .v0 = u.vpr .v0 ∧ t.vpr .v1 = u.vpr .v1 ∧ t.vpr .v2 = u.vpr .v2 ∧
      t.gpr .r15 = rp + 512#64 - 480#64 ∧
      t.gpr .r12 = rp + 512#64 - 480#64 - u.gpr .r3 - BitVec.ofNat 64 (1024 * j + 256) ∧ t.mem = u.mem := by
  unfold row selLoad vperm offReg
  brun [reduceVOpEval, vZero, vIdx, vChunk, vHot, vMask, vLoad, vSel, vpr_writeV, gpr_writeV, mem_writeV,
    ↓read_sixteen, h15, h0, h11, h14, h9, addrX, rd_writeV, wr_writeV, List.getD_cons_zero, List.getD_cons_succ,
    a0, a16, a256, a272, b0, b16, b256, b272, hM, show 1024 * j ≤ 32512 by omega]

/-! ## The mask and the one-hot vector -/

theorem ofVBytes_const_ite (c : Prop) [Decidable c] :
    (ofVBytes fun _ => if c then 255#8 else 0#8) = if c then BitVec.allOnes 128 else 0#128 := by
  by_cases h : c
  · simp only [h, ite_true]; decide
  · simp only [h, ite_false]; decide

theorem mask_eq {v2 v3 : BitVec 128} {idx : Byte} {i : Nat} (h2 : v2 = splatV (idx >>> 5))
    (h3 : ∀ k < 8, vbyte v3 k = if k = i then 255#8 else 0#8) :
    (ofVBytes fun k => if (vbyte v2 k).toNat % 32 < 16 then vbyte v3 ((vbyte v2 k).toNat % 32)
      else vbyte v3 ((vbyte v2 k).toNat % 32 - 16)) =
      if idx.toNat / 32 = i then BitVec.allOnes 128 else 0#128 := by
  have hx : (idx >>> 5).toNat = idx.toNat / 32 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hl : idx.toNat / 32 < 8 := by have := idx.isLt; omega
  subst h2
  simp only [vbyte_splatV, hx, Nat.mod_eq_of_lt (show idx.toNat / 32 < 32 by omega),
    show idx.toNat / 32 < 16 by omega, ite_true, h3 _ hl]
  exact ofVBytes_const_ite _

theorem sel_ite (a b : BitVec 128) (c : Prop) [Decidable c] :
    (a &&& ~~~(if c then BitVec.allOnes 128 else 0#128)) ||| (b &&& (if c then BitVec.allOnes 128 else 0#128)) =
      if c then b else a := by
  by_cases h : c
  · simp only [h, ite_true, BitVec.not_allOnes, BitVec.and_zero, BitVec.zero_or, BitVec.and_allOnes]
  · simp only [h, ite_false, BitVec.not_zero, BitVec.and_allOnes, BitVec.and_zero, BitVec.or_zero]

theorem vbyte_shift1 (x : BitVec 128) {k : Nat} (hk : k < 16) :
    vbyte (BitVec.extractLsb' 128 128 ((0#128 ++ x) <<< 120)) k = if k = 0 then 0#8 else vbyte x (k - 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, hr,
    decide_true, Bool.true_and]
  by_cases h0 : k = 0
  · subst h0
    simp only [ite_true, BitVec.getLsbD_zero, show 128 + (8 * (15 - 0) + r) < 128 + 128 by omega,
      decide_true, Bool.true_and, show ¬ 128 + (8 * (15 - 0) + r) < 120 by omega, decide_false, Bool.not_false,
      show ¬ 128 + (8 * (15 - 0) + r) - 120 < 128 by omega, ite_false, Bool.and_false]
  · simp only [h0, ite_false, BitVec.getLsbD_extractLsb', hr, decide_true, Bool.true_and,
      show 128 + (8 * (15 - k) + r) < 128 + 128 by omega, show ¬ 128 + (8 * (15 - k) + r) < 120 by omega,
      decide_false, Bool.not_false, show 128 + (8 * (15 - k) + r) - 120 < 128 by omega, ite_true]
    simp only [show 8 * (15 - k) + r < 128 by omega, decide_true, Bool.true_and]
    congr 1; omega

theorem hot_shift (x : BitVec 128) {i : Nat} (h : ∀ k < 8, vbyte x k = if k = i then 255#8 else 0#8) :
    ∀ k < 8, vbyte (BitVec.extractLsb' 128 128 ((0#128 ++ x) <<< 120)) k =
      if k = i + 1 then 255#8 else 0#8 := by
  intro k hk
  rw [vbyte_shift1 _ (by omega)]
  by_cases h0 : k = 0
  · simp [h0]
  · rw [ite_eq_right h0, h _ (by omega)]
    by_cases e : k - 1 = i
    · rw [ite_eq_left e, ite_eq_left (by omega)]
    · rw [ite_eq_right e, ite_eq_right (by omega)]

/-! ## The rows -/

/-- Half `hf` of plane `b`'s row of S-box `j` that holds `x` (entries
`32 (x / 32)` to `32 (x / 32) + 31`), as `lxvd2x` loads it. -/
def chunk (m : Mem) (S : Addr) (j x b hf : Nat) : BitVec 128 :=
  swapDwords (m.readW (S + BitVec.ofNat 64 (1024 * j + 256 * b + 16 * hf + 32 * (x / 32))) 128)

/-- After `i` rows of S-box `j` for the index `idx`, from the lookup's
start `s₀`. -/
structure RowInv (s₀ : State) (j : Nat) (idx : Byte) (i : Nat) (u : State) : Prop where
  le : i ≤ 8
  v0 : u.vpr .v0 = 0#128
  v1 : u.vpr .v1 = splatV (idx ^^^ 7#8)
  v2 : u.vpr .v2 = splatV (idx >>> 5)
  hot : ∀ k < 8, vbyte (u.vpr .v3) k = if k = i then 255#8 else 0#8
  sel : idx.toNat / 32 < i → ∀ b < 4, ∀ hf < 2,
    u.vpr (vSel (2 * b + hf)) = chunk s₀.mem (s₀.gpr .r3) j idx.toNat b hf
  rp : u.gpr .r15 = s₀.gpr .r3 + BitVec.ofNat 64 (1024 * j + 32 * i)
  o16 : u.gpr .r11 = 16#64
  o256 : u.gpr .r14 = 256#64
  o272 : u.gpr .r9 = 272#64
  keep : Keep lookRegs s₀ u
  mem : u.mem = s₀.mem

theorem add512_sub480 (p : Addr) : p + 512#64 - 480#64 = p + BitVec.ofNat 64 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- A kept row: the loaded half if the row holds the index, else what was
kept. -/
theorem sel_step {idx : Byte} {i : Nat} {old new c : BitVec 128}
    (hn : idx.toNat / 32 = i → new = c) (ho : idx.toNat / 32 < i → old = c) (h : idx.toNat / 32 < i + 1) :
    (if idx.toNat / 32 = i then new else old) = c := by
  by_cases e : idx.toNat / 32 = i
  · rw [ite_eq_left e]; exact hn e
  · rw [ite_eq_right e]; exact ho (by omega)

theorem row_step {s₀ : State} (E : LookEnv s₀) {j : Nat} (hj : j < 4) (idx : Byte) {i : Nat}
    (hi : i < 8) {u : State} (I : RowInv s₀ j idx i u) :
    WP isa (.block (row j)) u fun u' =>
      RowInv s₀ j idx (i + 1) u' ∧
        u'.gpr .r12 = BitVec.ofNat 64 (1024 * j + 32 * (i + 1)) - BitVec.ofNat 64 (1024 * j + 256) := by
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [I.keep.2.1, I.keep.2.2]
  have h3 : u.gpr .r3 = s₀.gpr .r3 := I.keep.gpr (by decide)
  have h0 : u.gpr .r0 = 0#64 := by rw [I.keep.gpr (by decide)]; exact E.zero
  obtain ⟨S, hS⟩ : ∃ S, s₀.gpr .r3 = S := ⟨_, rfl⟩
  have hrp : u.gpr .r15 = S + BitVec.ofNat 64 (1024 * j + 32 * i) := by rw [I.rp, hS]
  have reg : ∀ o, o ≤ 784 →
      InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (1024 * j + 32 * i + o)) 16 := fun o ho => by
    rw [hrd, ← hS]; exact E.rd _ _ (by omega)
  have f1 : ∀ o, S + BitVec.ofNat 64 (1024 * j + 32 * i) + BitVec.ofNat 64 o =
      S + BitVec.ofNat 64 (1024 * j + 32 * i + o) := fun o => Offset.add_add _ _ _
  have f2 : ∀ o, S + BitVec.ofNat 64 (1024 * j + 32 * i) + 512#64 + BitVec.ofNat 64 o =
      S + BitVec.ofNat 64 (1024 * j + 32 * i + (512 + o)) := fun o => by
    rw [show (512#64 : BitVec 64) = BitVec.ofNat 64 512 from rfl, Offset.add_add, Offset.add_add, Nat.add_assoc]
  have f0 : S + BitVec.ofNat 64 (1024 * j + 32 * i) = S + BitVec.ofNat 64 (1024 * j + 32 * i + 0) := rfl
  have g16 : (16#64 : BitVec 64) = BitVec.ofNat 64 16 := rfl
  have g256 : (256#64 : BitVec 64) = BitVec.ofNat 64 256 := rfl
  have g272 : (272#64 : BitVec 64) = BitVec.ofNat 64 272 := rfl
  have a0 := reg 0 (by decide)
  have a16 := reg 16 (by decide)
  have a256 := reg 256 (by decide)
  have a272 := reg 272 (by decide)
  have b0 := reg (512 + 0) (by decide)
  have b16 := reg (512 + 16) (by decide)
  have b256 := reg (512 + 256) (by decide)
  have b272 := reg (512 + 272) (by decide)
  rw [← f0] at a0
  rw [← f1, ← g16] at a16
  rw [← f1, ← g256] at a256
  rw [← f1, ← g272] at a272
  rw [← f2, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at b0
  rw [← f2, ← g16] at b16
  rw [← f2, ← g256] at b256
  rw [← f2, ← g272] at b272
  refine WP.mono (WP.keep [.r15, .r12]
    (row_run u hj hrp (by rw [h0]) I.o16 I.o256 I.o272 (mask_eq I.v2 I.hot) a0 a16 a256 a272 b0 b16 b256 b272)
    (by rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide) rfl)
    fun u' ⟨⟨e6, e7, e8, e9, e10, e11, e12, e13, e3, e0, e1, e2, e15, er12, em⟩, ak⟩ => ?_
  simp only [sel_ite] at e6 e7 e8 e9 e10 e11 e12 e13
  have hm : u.mem = s₀.mem := I.mem
  -- The kept halves.
  have hs : ∀ (v : VReg) (b hf o : Nat) (a : Addr), b < 4 → hf < 2 →
      a = S + BitVec.ofNat 64 (1024 * j + 32 * i + o) → o = 256 * b + 16 * hf →
      u.vpr v = u.vpr (vSel (2 * b + hf)) →
      idx.toNat / 32 < i + 1 →
      (if idx.toNat / 32 = i then swapDwords (u.mem.readW a 128) else u.vpr v) = chunk s₀.mem S j idx.toNat b hf :=
    fun v b hf o a hb hhf ha ho hv h => sel_step (fun e => by
        rw [hm, ha, chunk]; congr 4; omega)
      (fun h' => by rw [hv, ← hS]; exact I.sel h' b hb hf hhf) h
  have rp' : u'.gpr .r15 = S + BitVec.ofNat 64 (1024 * j + 32 * (i + 1)) := by
    rw [e15, add512_sub480, Offset.add_add]; congr 2
  refine ⟨⟨by omega, by rw [e0, I.v0], by rw [e1, I.v1], by rw [e2, I.v2],
    by rw [e3, I.v0]; exact hot_shift _ I.hot, fun h b hb hf hhf => ?_, by rw [rp', hS],
    by rw [ak.gpr (by decide), I.o16], by rw [ak.gpr (by decide), I.o256], by rw [ak.gpr (by decide), I.o272],
    I.keep.trans ak |>.mono (by decide), em.trans I.mem⟩, ?_⟩
  · rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
      rcases (by omega : hf = 0 ∨ hf = 1) with rfl | rfl
    · rw [show vSel (2 * 0 + 0) = .v6 from rfl, e6, hS]
      exact hs _ 0 0 0 _ (by decide) (by decide) rfl rfl rfl h
    · rw [show vSel (2 * 0 + 1) = .v7 from rfl, e7, hS]
      exact hs _ 0 1 16 _ (by decide) (by decide) (by rw [g16, f1]) rfl rfl h
    · rw [show vSel (2 * 1 + 0) = .v8 from rfl, e8, hS]
      exact hs _ 1 0 256 _ (by decide) (by decide) (by rw [g256, f1]) rfl rfl h
    · rw [show vSel (2 * 1 + 1) = .v9 from rfl, e9, hS]
      exact hs _ 1 1 272 _ (by decide) (by decide) (by rw [g272, f1]) rfl rfl h
    · rw [show vSel (2 * 2 + 0) = .v10 from rfl, e10, hS]
      exact hs _ 2 0 512 _ (by decide) (by decide)
        (by rw [← BitVec.add_zero (_ + 512#64), show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, f2]) rfl rfl h
    · rw [show vSel (2 * 2 + 1) = .v11 from rfl, e11, hS]
      exact hs _ 2 1 528 _ (by decide) (by decide) (by rw [g16, f2]) rfl rfl h
    · rw [show vSel (2 * 3 + 0) = .v12 from rfl, e12, hS]
      exact hs _ 3 0 768 _ (by decide) (by decide) (by rw [g256, f2]) rfl rfl h
    · rw [show vSel (2 * 3 + 1) = .v13 from rfl, e13, hS]
      exact hs _ 3 1 784 _ (by decide) (by decide) (by rw [g272, f2]) rfl rfl h
  · rw [er12, ← e15, rp', h3, hS, Offset.add_sub_cancel_left]

theorem rows_run {s₀ : State} (E : LookEnv s₀) {j : Nat} (hj : j < 4) (idx : Byte) {u : State}
    (I : RowInv s₀ j idx 0 u) : WP isa (.loop (.block (row j)) (.nonzero .d .r12)) u (RowInv s₀ j idx 8) := by
  refine WP.loop (M := isa) (Q := RowInv s₀ j idx 8)
    (fun (n : Nat) (v : State) => ∃ k, k < 8 ∧ n = 8 - k ∧ RowInv s₀ j idx k v) ?_ 8 u ⟨0, by decide, rfl, I⟩
  intro n v ⟨k, hk, hn, J⟩
  refine WP.mono (row_step E hj idx hk J) fun v' ⟨J', hz⟩ => ?_
  rw [eval_nonzero, hz, ofNat_sub_bne (by omega_arith) (by omega_arith)]
  by_cases e : k + 1 = 8
  · left
    exact ⟨by rw [e]; simp, e ▸ J'⟩
  · right
    exact ⟨by simp; omega_arith, n - 1, by omega_arith, k + 1, by omega_arith, by omega_arith, J'⟩

/-! ## The entry -/

theorem top_byte (f : Nat → Byte) : vdword (ofVBytes f) 0 >>> 56 = (f 0).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  by_cases h : i < 8
  · simp only [show 56 + i < 64 by omega, decide_true, Bool.true_and]
    have := getLsbD_packed f (j := 15) (r := i) (by decide) h
    rw [show 64 * (1 - 0) + (56 + i) = 8 * 15 + i by omega, this]
    simp [show i < 64 by omega]
  · simp [show ¬ 56 + i < 64 by omega, BitVec.getLsbD_of_ge (f 0) i (by omega)]

theorem vbyte_load (m : Mem) (a : Addr) {k : Nat} (hk : k < 16) :
    vbyte (swapDwords (m.readW a 128)) k = m (a + BitVec.ofNat 64 (15 - (if k < 8 then k + 8 else k - 8))) := by
  rw [vbyte_swapDwords _ hk, vbyte, Mem.readW, BitVec.setWidth_eq]
  exact Mem.extractLsb'_read m a (n := 16) (by split <;> omega)

theorem pick (m : Mem) (a a' : Addr) (ha : a' = a + BitVec.ofNat 64 16) {x : Nat} (hx : x < 32) :
    (if (x ^^^ 7) < 16 then vbyte (swapDwords (m.readW a 128)) (x ^^^ 7)
      else vbyte (swapDwords (m.readW a' 128)) ((x ^^^ 7) - 16)) = m (a + BitVec.ofNat 64 x) := by
  have lo : ∀ x < 16, (x ^^^ 7) < 16 ∧ 15 - (if (x ^^^ 7) < 8 then (x ^^^ 7) + 8 else (x ^^^ 7) - 8) = x := by
    decide
  have hi : ∀ x < 32, 16 ≤ x → ¬ (x ^^^ 7) < 16 ∧ (x ^^^ 7) - 16 < 16 ∧
      16 + (15 - (if (x ^^^ 7) - 16 < 8 then (x ^^^ 7) - 16 + 8 else (x ^^^ 7) - 16 - 8)) = x := by
    decide
  by_cases h : x < 16
  · obtain ⟨l1, l2⟩ := lo x h
    rw [ite_eq_left l1, vbyte_load _ _ l1, l2]
  · obtain ⟨l1, l2, l3⟩ := hi x hx (by omega)
    rw [ite_eq_right l1, vbyte_load _ _ l2, ha, Offset.add_add, l3]

theorem xor7_mod (x : Byte) : (x ^^^ 7#8).toNat % 32 = (x.toNat % 32) ^^^ 7 := by
  have : ∀ x : Byte, (x ^^^ 7#8).toNat % 32 = (x.toNat % 32) ^^^ 7 := by decide
  exact this x

/-- The low word of four bytes ORed into place. -/
theorem assemble (b0 b1 b2 b3 : Byte) {c : Nat} (hc : c < 4) :
    (lo ((((b0.setWidth 64 ||| b1.setWidth 64 <<< 8) ||| b2.setWidth 64 <<< 16) |||
      b3.setWidth 64 <<< 24))).extractLsb' (8 * c) 8 = [b0, b1, b2, b3].getD c 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  have z : ∀ (b : Byte) (n : Nat), 8 ≤ n → b.getLsbD n = false := fun b n h => BitVec.getLsbD_of_ge b n h
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl
  · simp [show i < 32 by omega, show i < 64 by omega, hi, show i < 16 by omega, show i < 24 by omega]
  · simp [show 8 + i < 32 by omega, show 8 + i < 64 by omega, show 8 + i < 16 by omega,
      show 8 + i < 24 by omega, show i < 64 by omega]
  · simp [show 16 + i < 32 by omega, show 16 + i < 64 by omega, show ¬ 16 + i < 16 by omega,
      show 16 + i < 24 by omega, z b0 (16 + i) (by omega), z b1 (16 + i - 8) (by omega), show i < 64 by omega]
  · simp [show 24 + i < 32 by omega, show 24 + i < 64 by omega, show ¬ 24 + i < 16 by omega,
      show ¬ 24 + i < 24 by omega, z b0 (24 + i) (by omega), z b1 (24 + i - 8) (by omega),
      z b2 (24 + i - 16) (by omega), show i < 64 by omega]

theorem end_run (v : State) {S : Addr} {j : Nat} (hj : j < 4) {idx : Byte} {m : Mem}
    (h1 : v.vpr .v1 = splatV (idx ^^^ 7#8))
    (hs : ∀ b < 4, ∀ hf < 2, v.vpr (vSel (2 * b + hf)) = chunk m S j idx.toNat b hf) :
    WP isa (.block lookupEnd) v fun t => lo (t.gpr .r10) = sEntry (scheduleAt m S) j idx ∧ t.mem = v.mem := by
  unfold lookupEnd entryByte vperm
  brun [reduceVOpEval, vByte, vSel, vIdx, List.getD_cons_zero, List.getD_cons_succ, vpr_writeV, gpr_writeV,
    mem_writeV, List.range_succ, List.range_zero, List.map_cons, List.map_nil, top_byte, h1, vbyte_splatV, xor7_mod]
  have hx : idx.toNat % 32 < 32 := Nat.mod_lt _ (by decide)
  have pb : ∀ b < 4, ∀ r₀ r₁ : VReg, r₀ = vSel (2 * b) → r₁ = vSel (2 * b + 1) →
      (if idx.toNat % 32 ^^^ 7 < 16 then vbyte (v.vpr r₀) (idx.toNat % 32 ^^^ 7)
        else vbyte (v.vpr r₁) ((idx.toNat % 32 ^^^ 7) - 16)) =
        m (S + BitVec.ofNat 64 (1024 * j + 256 * b + idx.toNat)) := by
    intro b hb r₀ r₁ e₀ e₁
    rw [e₀, e₁, show 2 * b = 2 * b + 0 from rfl, hs b hb 0 (by decide), hs b hb 1 (by decide), chunk, chunk,
      pick m _ _ (by rw [Offset.add_add]; congr 2; omega) hx, Offset.add_add,
      show 1024 * j + 256 * b + 16 * 0 + 32 * (idx.toNat / 32) + idx.toNat % 32 = 1024 * j + 256 * b + idx.toNat by
        omega]
  rw [pb 0 (by decide) .v6 .v7 rfl rfl, pb 1 (by decide) .v8 .v9 rfl rfl, pb 2 (by decide) .v10 .v11 rfl rfl,
    pb 3 (by decide) .v12 .v13 rfl rfl]
  refine word_ext fun c hc => ?_
  rw [assemble _ _ _ _ hc, sEntry_byte m S hj hc idx]
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- The lookup of S-box `j` for the byte `3 - j` of xL's low word. -/
theorem lookup_run {s : State} (E : LookEnv s) {j : Nat} (hj : j < 4) :
    WP isa (lookup j) s fun t =>
      lo (t.gpr .r10) = sEntry (scheduleAt s.mem (s.gpr .r3)) j (quarter (lo (s.gpr .r4)) j) ∧
        Keep lookRegs s t ∧ t.mem = s.mem := by
  let idx := quarter (lo (s.gpr .r4)) j
  unfold lookup
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r9] (index_run s hj) (by rfl) rfl) fun t ⟨⟨t9, tm⟩, tk⟩ => ?_
  refine WP.mono (WP.keep [.r12, .r9, .r15, .r11, .r14] (start_run t hj t9)
    (by rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide) rfl)
    fun u ⟨⟨u0, u1, u2, u3, u15, u11, u14, u9, um⟩, uk⟩ => ?_
  have K0 : Keep lookRegs s u := (tk.trans uk).mono (by decide)
  have I0 : RowInv s j idx 0 u := ⟨by decide, u0, u1, u2, u3, fun h => absurd h (Nat.not_lt_zero _),
    by rw [u15, tk.gpr (by decide)]; rfl, u11, u14, u9, K0, by rw [um, tm]⟩
  apply WP.seq
  refine WP.mono (rows_run E hj idx I0) fun v V => ?_
  have hl : idx.toNat / 32 < 8 := by have := idx.isLt; omega
  refine WP.mono (WP.keep [.r10, .r12] (end_run v hj V.v1 (V.sel hl)) (by decide) rfl)
    fun w ⟨⟨w10, wm⟩, wk⟩ => ⟨w10, (V.keep.trans wk).mono (by decide), by rw [wm, V.mem]⟩
