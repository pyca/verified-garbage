module

public import VerifiedGarbage.Proof.Camellia.X86.AesNiMaps
public import VerifiedGarbage.Proof.Camellia.SerialPure
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Camellia by the AES S-box on x86 (32-bit): what the parts of the block's code compute

Each part of `Impl.Camellia.X86.AesNi`'s code that only computes in the XMM
registers, as a statement about the registers' bytes: the kernel has
checked what the code leaves in them (`Proof/Camellia/X86/AesNiMaps.lean`,
with `Proof/Framework/X86/ByteMap.lean`), and here that is said of a state.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.AesNi

open VG VG.X86 VG.X86.ByteMap VG.Impl.Camellia.X86.AesNi

/-- What every part of the code needs of the state: the table's address in
its register, the 128 bytes of keys at `esi` readable, and the mask. -/
structure Env (s : State) : Prop where
  tb : s.gpr tbr = s.syms tableName
  fit : (s.gpr kr).toNat + 128 ≤ 2 ^ 32
  acc : ∀ o, o + 16 ≤ 128 → InRegions (s.rd ++ s.wr) (addr (s.gpr kr) o) 16
  msk : ∀ i < 16, byte (s.xmm m0) i = 0x0f#8

theorem Env.rel {s : State} (h : Env s) : Rel params (envOf params s) regs₀ s :=
  (rel_init (p := params) h.tb h.fit h.acc).const m0 h.msk

/-- Byte `o` of the keys at `esi`. -/
def kb (s : State) (o : Nat) : Byte := s.mem ((s.gpr kr).setWidth 64 + BitVec.ofNat 64 o)

/-- Slot `q` of a spread register: the exclusive-or of its two quadwords'. -/
def fd (x : BitVec 128) (q : Nat) : Byte := byte x q ^^^ byte x (q + 8)

/-- A round's map of the S-boxes' output bytes `z`, at byte `j`: P, with the
map after the S-box for each pair of positions. -/
def glin (z : Nat → Byte) (j : Nat) : Byte :=
  (sets j).foldr (fun i acc => nmap (kOf (isA j) (kind i)) (z i) ^^^ acc) 0#8

section
variable {s : State}

theorem env_var (r : XReg) {q : Nat} (hq : q < 16) :
    mask (envOf params s) (var r q) nvars = byte (s.xmm r) q := by
  have hr : r.ctorIdx < 8 := by cases r <;> decide
  rw [var, mask_bit _ (by show 16 * r.ctorIdx + q < 1024; omega_using [hr, hq]), envOf_reg params s r hq]

theorem env_fold (r : XReg) {q : Nat} (hq : q < 8) :
    mask (envOf params s) (fold r q) nvars = fd (s.xmm r) q := by
  rw [fold, mask_xor, env_var r (by omega_arith), env_var r (by omega_arith)]; rfl

theorem env_key {o : Nat} (ho : o < 128) : mask (envOf params s) (2 ^ (128 + o)) nvars = kb s o := by
  rw [mask_bit _ (by show 128 + o < 1024; omega_arith), envOf_key]; rfl

/-- The terms of `roundRef`, for any list of bytes. -/
theorem sum_terms (env : Nat → BitVec 8) (xr : XReg) (a : Bool) (l : List Nat) :
    sum env (l.flatMap fun i =>
      [⟨[.look (tblAt (oN (kOf a (kind i)))), .xorc 0x0f#8, .and 0x0f#8, .aes], fold xr (slot i)⟩,
       ⟨[.look (tblAt (oN (kOf a (kind i)) + 16)), .hi4, .aes], fold xr (slot i)⟩]) =
      l.foldr (fun i acc => nmap (kOf a (kind i)) (aesSbox (mask env (fold xr (slot i)) nvars)) ^^^ acc) 0#8 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, sum, List.foldr_cons, ih]
    rw [← BitVec.xor_assoc]; rfl

theorem slot_lt (i : Nat) : slot i < 8 := Nat.mod_lt _ (by decide)

theorem env_fold_slot (r : XReg) (j : Nat) :
    mask (envOf params s) (fold r (slot j)) nvars = fd (s.xmm r) (slot j) := env_fold r (slot_lt j)

/-- Round `i` of a group: `xr` takes its eight key bytes, and the spread `y`
the round's map of the S-boxes of the spread `xr`. -/
theorem round_wp {xr y : XReg} {i : Nat} (hi : i < 6) (hok : roundOk xr y i = true) (he : Env s) :
    WP isa (.block (round xr y i)) s fun s' => Same s s' ∧
      (∀ q < 16, byte (s'.xmm xr) q = byte (s.xmm xr) q ^^^ (if q < 8 then kb s (16 + 8 * i + q) else 0#8)) ∧
      (∀ q < 8, fd (s'.xmm y) q =
        fd (s.xmm y) q ^^^ glin (fun j => aesSbox (fd (s.xmm xr) (slot j))) (slot q)) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  unfold roundOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨hx, hy⟩, hm⟩, cy⟩, cx⟩, cm⟩ := hok
  refine run_wp he.rel hrun fun s' hr hs => ⟨hs, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · rw [hr.bytes hx q hq, BV.same_eval _ (List.all_eq_true.mp cx q (List.mem_range.mpr hq))]
    simp only [BV.eval, sum, BitVec.xor_zero, mask_xor, env_var xr hq]
    by_cases h8 : q < 8
    · rw [ite_eq_left h8, ite_eq_left h8, show 128 + 16 + 8 * i + q = 128 + (16 + 8 * i + q) by omega_arith,
        env_key (by omega_arith)]
    · rw [ite_eq_right h8, ite_eq_right h8, mask_zero]
  · have e := BV.same_eval (envOf params s) (List.all_eq_true.mp cy q (List.mem_range.mpr hq))
    rw [BV.xor_eval, ← hr.bytes hy q (by omega_arith), ← hr.bytes hy (q + 8) (by omega_arith)] at e
    rw [fd, e, roundRef, BV.eval, sum_terms, env_fold y hq, BitVec.xor_zero, glin]
    simp only [env_fold_slot]
  · rw [hr.bytes hm q hq, BV.same_eval _ (List.all_eq_true.mp cm q (List.mem_range.mpr hq)), BV.cst_eval]

end

/-! ## The byte maps and Camellia's F -/

open VG.Proof.Camellia.Serial (packed byte_packed substitutedByte substituted permuted)

/-- Byte `j` of a half, from the least significant. -/
abbrev bz (w : BitVec 64) (j : Nat) : Byte := Serial.byte w j

theorem byte_ofNat (b : Byte) : BitVec.ofNat 8 b.toNat = b := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `sbox_all`, of a byte. -/
theorem sbox_ok (ai : Bool) {j : Nat} (hj : j < 4) (b : Byte) :
    nmap (kOf ai j) (aesSbox (qT (j == 3) b ^^^ c5)) = qT ai (sb j b) ^^^ mc ai j := by
  have h := List.all_eq_true.mp sbox_all b.toNat (List.mem_range.mpr b.isLt)
  have h := List.all_eq_true.mp h ai (by cases ai <;> simp)
  have h := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  rw [byte_ofNat, beq_iff_eq] at h
  rw [h, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem qI_qT (a : Bool) (b : Byte) : qI a (qT a b) = b := by
  have h := List.all_eq_true.mp inv_all b.toNat (List.mem_range.mpr b.isLt)
  have h := List.all_eq_true.mp h a (by cases a <;> simp)
  rw [byte_ofNat, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  exact h.1

theorem qT_qI (a : Bool) (b : Byte) : qT a (qI a b) = b := by
  have h := List.all_eq_true.mp inv_all b.toNat (List.mem_range.mpr b.isLt)
  have h := List.all_eq_true.mp h a (by cases a <;> simp)
  rw [byte_ofNat, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  exact h.2

/-- A nibble table of the byte maps, of nibbles. -/
theorem lk_xor {t : Nat} (ht : t ∈ [oT, oT + 16, oT + 32, oT + 48, oI, oI + 16, oI + 32, oI + 48]) {x y : Byte}
    (hx : x.toNat < 16) (hy : y.toNat < 16) : lk t (x ^^^ y) = lk t x ^^^ lk t y := by
  have h := List.all_eq_true.mp lin16_all x.toNat (List.mem_range.mpr hx)
  have h := List.all_eq_true.mp h y.toNat (List.mem_range.mpr hy)
  have h := List.all_eq_true.mp h t ht
  rw [beq_iff_eq, byte_ofNat, byte_ofNat] at h
  rw [← h]
  exact congrArg (lk t) (BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 8) x.isLt y.isLt)]))

theorem lo_lt (b : Byte) : (b &&& 0x0f#8).toNat < 16 := by
  rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem hi_lt (b : Byte) : (b >>> 4).toNat < 16 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega_using [b.isLt]

/-- The byte maps are linear. -/
theorem bmap_xor {t : Nat} (ht : t = oT ∨ t = oI) (a : Bool) (u v : Byte) :
    bmap t a (u ^^^ v) = bmap t a u ^^^ bmap t a v := by
  have e₁ : (u ^^^ v) &&& 0x0f#8 = u &&& 0x0f#8 ^^^ v &&& 0x0f#8 := Fn.lin_xor (g := .and 0x0f#8) rfl u v
  have e₂ : (u ^^^ v) >>> 4 = u >>> 4 ^^^ v >>> 4 := Fn.lin_xor (g := .hi4) rfl u v
  have m₀ : t ∈ [oT, oT + 16, oT + 32, oT + 48, oI, oI + 16, oI + 32, oI + 48] := by
    rcases ht with rfl | rfl <;> decide
  have m₁ : t + 16 ∈ [oT, oT + 16, oT + 32, oT + 48, oI, oI + 16, oI + 32, oI + 48] := by
    rcases ht with rfl | rfl <;> decide
  have m₂ : t + 32 ∈ [oT, oT + 16, oT + 32, oT + 48, oI, oI + 16, oI + 32, oI + 48] := by
    rcases ht with rfl | rfl <;> decide
  have m₃ : t + 48 ∈ [oT, oT + 16, oT + 32, oT + 48, oI, oI + 16, oI + 32, oI + 48] := by
    rcases ht with rfl | rfl <;> decide
  unfold bmap
  rw [e₁, e₂, lk_xor m₀ (lo_lt u) (lo_lt v), lk_xor m₁ (hi_lt u) (hi_lt v),
    lk_xor m₂ (lo_lt u) (lo_lt v), lk_xor m₃ (hi_lt u) (hi_lt v)]
  cases a
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.xor_zero]; ac_rfl
  · simp only [↓reduceIte]; ac_rfl

theorem qT_xor (a : Bool) (u v : Byte) : qT a (u ^^^ v) = qT a u ^^^ qT a v := bmap_xor (.inl rfl) a u v
theorem qI_xor (a : Bool) (u v : Byte) : qI a (u ^^^ v) = qI a u ^^^ qI a v := bmap_xor (.inr rfl) a u v

theorem qT_zero (a : Bool) : qT a 0#8 = 0#8 := by
  have := qT_xor a 0#8 0#8
  rw [BitVec.xor_self] at this
  rw [this, BitVec.xor_self]

/-- Byte `j` of a half in the rounds' form. -/
def dq (w : BitVec 64) (j : Nat) : Byte := qT (isA j) (bz w j)

theorem bz_xor (x y : BitVec 64) (j : Nat) : bz (x ^^^ y) j = bz x j ^^^ bz y j := by
  simp only [Serial.byte, BitVec.ushiftRight_xor_distrib, BitVec.setWidth_xor]

theorem dq_xor (x y : BitVec 64) (j : Nat) : dq (x ^^^ y) j = dq x j ^^^ dq y j := by
  rw [dq, bz_xor, qT_xor]; rfl

/-- The constant a round adds at byte `j`. -/
def gc (j : Nat) : Byte := (sets j).foldr (fun i acc => mc (isA j) (kind i) ^^^ acc) 0#8

/-- `qT` of an exclusive-or of S-boxes, with the constants. -/
theorem fold_sbox (ai : Bool) (t : Nat → Byte) (l : List Nat) (hl : ∀ i ∈ l, i < 8) :
    l.foldr (fun i acc => nmap (kOf ai (kind i)) (aesSbox (qT (isA i) (t i) ^^^ c5)) ^^^ acc) 0#8 =
      qT ai (l.foldr (fun i acc => sb (kind i) (t i) ^^^ acc) 0#8) ^^^
        l.foldr (fun i acc => mc ai (kind i) ^^^ acc) 0#8 := by
  induction l with
  | nil => simp only [List.foldr_nil, qT_zero, BitVec.xor_zero]
  | cons i l ih =>
    have hk : kind i < 4 := by
      have := hl i (List.mem_cons_self ..)
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega_arith
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp only [List.foldr_cons, ih fun j hj => hl j (List.mem_cons_of_mem _ hj), qT_xor]
    rw [show isA i = (kind i == 3) from rfl, sbox_ok ai hk]
    ac_rfl

/-- Byte `j` of F's output: P of the S-boxes. -/
theorem f_byte (x k : BitVec 64) {j : Nat} (hj : j < 8) :
    bz (Spec.Camellia.f x k) j = (sets j).foldr (fun i acc => sb (kind i) (bz (x ^^^ k) i) ^^^ acc) 0#8 := by
  rw [Serial.f_eq, Serial.linearWord_eq]
  have e : ∀ y : BitVec 64, permuted y = packed (fun j =>
      let a := Serial.byte y 7; let b := Serial.byte y 6; let c := Serial.byte y 5; let d := Serial.byte y 4
      let e := Serial.byte y 3; let f := Serial.byte y 2; let g := Serial.byte y 1; let h := Serial.byte y 0
      match j with
      | 0 => a ^^^ d ^^^ e ^^^ f ^^^ g
      | 1 => c ^^^ d ^^^ e ^^^ f ^^^ h
      | 2 => b ^^^ c ^^^ e ^^^ g ^^^ h
      | 3 => a ^^^ b ^^^ f ^^^ g ^^^ h
      | 4 => b ^^^ c ^^^ d ^^^ e ^^^ f ^^^ g
      | 5 => a ^^^ b ^^^ c ^^^ e ^^^ f ^^^ h
      | 6 => a ^^^ b ^^^ d ^^^ e ^^^ g ^^^ h
      | _ => a ^^^ c ^^^ d ^^^ f ^^^ g ^^^ h) := fun _ => rfl
  show Serial.byte (permuted _) j = _
  rw [e, byte_packed _ j hj]
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega_arith
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [substituted, byte_packed _ _ (by decide : 0 < 8), byte_packed _ _ (by decide : 1 < 8),
      byte_packed _ _ (by decide : 2 < 8), byte_packed _ _ (by decide : 3 < 8), byte_packed _ _ (by decide : 4 < 8),
      byte_packed _ _ (by decide : 5 < 8), byte_packed _ _ (by decide : 6 < 8), byte_packed _ _ (by decide : 7 < 8),
      substitutedByte, sets, List.getD_cons_zero, List.getD_cons_succ, List.foldr_cons, List.foldr_nil, sb, kind,
      BitVec.xor_zero] <;> ac_rfl

/-- A round's map of the S-boxes of a half and a key in the rounds' form is
F's output in that form, and a constant. -/
theorem glin_f (x k : BitVec 64) {j : Nat} (hj : j < 8) :
    glin (fun i => aesSbox (dq x i ^^^ dq k i ^^^ c5)) j = dq (Spec.Camellia.f x k) j ^^^ gc j := by
  have hs : ∀ i ∈ sets j, i < 8 := by
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega_arith
    rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [dq, f_byte x k hj, gc, ← fold_sbox (isA j) (fun i => bz (x ^^^ k) i) (sets j) hs, glin]
  simp only [← dq_xor]
  rfl

end VG.Proof.Camellia.X86.AesNi
