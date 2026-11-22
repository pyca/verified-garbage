module

public import VerifiedGarbage.Proof.Camellia.X86.AesNiMaps
public import VerifiedGarbage.Proof.Camellia.SerialPure
public import VerifiedGarbage.Proof.Camellia.Words
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseLanes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Camellia.CtrCipher
public import VerifiedGarbage.Spec.Camellia.Cbc
public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Proof.Camellia.Layout
public import VerifiedGarbage.Proof.Camellia.Common
public import VerifiedGarbage.Proof.Framework.X86.SymFrame

/-!
# Camellia by the AES S-box on x86 (32-bit): the core of the modes

`coreSpec`: `Impl.Camellia.X86.AesNi.core` meets what the modes need of a
core (`Proof.Modes.X86.CoreSpec`), with the key the number of rounds and
the schedule's words, read through the first two stack arguments, and its
cipher `Spec.Camellia.cipher` under them.

* Each part of the code that only computes in the XMM registers, as a
  statement about the registers' bytes: the kernel has checked what the code
  leaves in them (`Proof/Camellia/X86/AesNiMaps.lean`, with
  `Proof/Framework/X86/ByteMap.lean`), and here that is said of a state
  (`round_wp`, `head_wp`, …), and of Camellia's F (`glin_f`, `rounds6_wp`:
  the six rounds of a group in the rounds' form).
* The FL layer on the halves as bytes (`layerMid_wp`: two steps of masks, a
  rotation by one and moves of a 32-bit lane), and `crypt_wp`: the block of
  the modes' buffer, enciphered under the keys in the scratch buffer
  (`Keys`).
* `prepare_wp`: `prepare` reads the schedule, a group of rounds at a time,
  and stores each group's keys: what each of its blocks stores is an
  expression of the schedule's bytes that the kernel has checked
  (`prep_all`), and those are the keys `crypt` needs, of the subkeys as the
  schedule stores them.
* The key is ready (`Ready`) when the keys are in the scratch buffer, the
  table's address in its first slot, and the number of rounds still in its
  stack argument, apart from every writable region, where `crypt` reads it
  again. `prepare` gets the table's address in a frame of four bytes below
  `esp` before it reads the schedule and the arguments, so the key's
  arguments (`KeyArgs`) say that those bytes are apart from them.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.AesNi

/-! ## What the parts of the block's code compute -/

section


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

/-! ### The byte maps and Camellia's F -/

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

/-! ### The conversions -/

theorem lk_zero {t : Nat} (ht : t ∈ [oT, oT + 16, oT + 32, oT + 48, oI, oI + 16, oI + 32, oI + 48]) : lk t 0#8 = 0#8 := by
  have := lk_xor ht (x := 0#8) (y := 0#8) (by decide) (by decide)
  rw [BitVec.xor_self] at this
  rw [this, BitVec.xor_self]

theorem and_f_of_lt {x : Byte} (h : x.toNat < 16) : x &&& 0x0f#8 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x0f#8 : Byte).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt h]

theorem eval_and (c b : Byte) : Fn.eval (.and c) b = b &&& c := rfl
theorem eval_hi4 (b : Byte) : Fn.eval .hi4 b = b >>> 4 := rfl
theorem eval_look (t : Nat) (b : Byte) : Fn.eval (.look (tblAt t)) b = lk t b := rfl

/-- The four look-ups of a byte map are the map, with its difference at the
slots of s4. -/
theorem cterms_eval (env : Nat → BitVec 8) {t : Nat} (ht : t = oT ∨ t = oI) {q : Nat} (hq : q < 16) (v : Nat) :
    sum env (cterms t q v) = bmap t (isA (slot (q % 8))) (mask env v nvars) := by
  have hm := List.all_eq_true.mp m4_all q (List.mem_range.mpr hq)
  rw [beq_iff_eq] at hm
  have m₂ : t + 32 ∈ [oT, oT + 16, oT + 32, oT + 48, oI, oI + 16, oI + 32, oI + 48] := by
    rcases ht with rfl | rfl <;> simp
  have m₃ : t + 48 ∈ [oT, oT + 16, oT + 32, oT + 48, oI, oI + 16, oI + 32, oI + 48] := by
    rcases ht with rfl | rfl <;> simp
  simp only [cterms, sum, Term.eval, chain, eval_and, eval_hi4, eval_look, hm, BitVec.xor_zero]
  unfold bmap
  by_cases ha : isA (slot (q % 8)) = true
  · rw [ite_eq_left ha, ite_eq_left ha, and_f_of_lt (lo_lt _), and_f_of_lt (hi_lt _)]; ac_rfl
  · rw [ite_eq_right ha, ite_eq_right ha, BitVec.and_zero, BitVec.and_zero, lk_zero m₂, lk_zero m₃]; ac_rfl

section
variable {s : State}

/-- A plain register's bytes after a checked part. -/
theorem same_bytes {ρ : Regs} {s' : State} (hr : Rel params (envOf params s) ρ s') {r : XReg}
    (hsh : (ρ.get r).sh = false) {ref : Nat → BV}
    (hc : ((List.range 16).all fun q => (get (ρ.get r).bs q).same (ref q)) = true) {q : Nat} (hq : q < 16) :
    byte (s'.xmm r) q = (ref q).eval (envOf params s) := by
  rw [hr.bytes hsh q hq, BV.same_eval _ (List.all_eq_true.mp hc q (List.mem_range.mpr hq))]

theorem mask_ok {ρ : Regs} {s' : State} (hr : Rel params (envOf params s) ρ s') (h : maskOk ρ = true) :
    ∀ q < 16, byte (s'.xmm m0) q = 0x0f#8 := fun q hq => by
  simp only [maskOk, Bool.and_eq_true, Bool.not_eq_true'] at h
  rw [same_bytes hr h.1 h.2 hq, BV.cst_eval]

theorem fd_zero_hi {x : BitVec 128} {q : Nat} (h : byte x (q + 8) = 0#8) : fd x q = byte x q := by
  rw [fd, h, BitVec.xor_zero]

/-- What `unpackOk` says of the two registers, spread. -/
theorem unpack_ok {ρ : Regs} {s' : State} (hr : Rel params (envOf params s) ρ s') {w : Nat → BV}
    (h : unpackOk ρ w = true) {q : Nat} (hq : q < 8) :
    fd (s'.xmm .xmm0) q = (w q).eval (envOf params s) ∧ fd (s'.xmm .xmm1) q = (w (q + 8)).eval (envOf params s) := by
  simp only [unpackOk, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h0, h1⟩, hc⟩ := h
  have c := fun q hq => List.all_eq_true.mp hc q (List.mem_range.mpr hq)
  have lo := c q (by omega_arith)
  have hi := c (q + 8) (by omega_arith)
  simp only [Bool.and_eq_true, ite_eq_left hq, ite_eq_right (show ¬ q + 8 < 8 by omega_arith)] at lo hi
  constructor
  · rw [fd_zero_hi (by rw [hr.bytes h0 _ (by omega_arith), BV.same_eval _ hi.1, BV.zero_eval]),
      hr.bytes h0 _ (by omega_arith), BV.same_eval _ lo.1]
  · rw [fd_zero_hi (by rw [hr.bytes h1 _ (by omega_arith), BV.same_eval _ hi.2, BV.zero_eval]),
      hr.bytes h1 _ (by omega_arith), BV.same_eval _ lo.2]

theorem bswq_lt {q : Nat} (h : q < 16) : bswq q < 16 := by unfold bswq; split <;> [skip; split <;> [skip; split]] <;> omega_arith

/-- The block in `xmm0`, in the order of `BSW`, to the rounds' form with the
first keys, spread in `xmm0` and `xmm1`; and the mask. -/
theorem head_wp (htb : s.gpr tbr = s.syms tableName) (hfit : (s.gpr kr).toNat + 128 ≤ 2 ^ 32)
    (hacc : ∀ o, o + 16 ≤ 128 → InRegions (s.rd ++ s.wr) (addr (s.gpr kr) o) 16) :
    WP isa (.block headX) s fun s' => Same s s' ∧
      (∀ q < 8, fd (s'.xmm .xmm0) q = qT (isA (slot q)) (byte (s.xmm .xmm0) (bswq q)) ^^^ kb s q ∧
        fd (s'.xmm .xmm1) q = qT (isA (slot q)) (byte (s.xmm .xmm0) (bswq (q + 8))) ^^^ kb s (q + 8)) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  have hok := conv_all.1
  unfold headOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  rw [Bool.and_eq_true] at hok
  refine run_wp (rel_init (p := params) htb hfit hacc) hrun fun s' hr hs => ⟨hs, fun q hq => ?_, mask_ok hr hok.2⟩
  obtain ⟨e₀, e₁⟩ := unpack_ok hr hok.1 hq
  rw [e₀, e₁]
  simp only [BV.eval, BitVec.xor_zero, cterms_eval _ (.inl rfl) (show q < 16 by omega_arith),
    cterms_eval _ (.inl rfl) (show q + 8 < 16 by omega_arith), env_var .xmm0 (bswq_lt (show q < 16 by omega_arith)),
    env_var .xmm0 (bswq_lt (show q + 8 < 16 by omega_arith)), show (q + 8) % 8 = q by omega_arith,
    show q % 8 = q by omega_arith, env_key (show q < 128 by omega_arith)]
  rw [show 128 + (q + 8) = 128 + (q + 8) from rfl, env_key (show q + 8 < 128 by omega_arith)]
  exact ⟨BitVec.xor_comm _ _, BitVec.xor_comm _ _⟩

/-- The two spread halves, packed: slot `q` of the first, or `q - 8` of the second. -/
def pkv (s : State) (q : Nat) : Byte := if q < 8 then fd (s.xmm .xmm0) q else fd (s.xmm .xmm1) (q - 8)

theorem env_pk {q : Nat} (hq : q < 16) : mask (envOf params s) (pk q) nvars = pkv s q := by
  unfold pk pkv
  by_cases h : q < 8
  · rw [ite_eq_left h, ite_eq_left h, env_fold _ h]
  · rw [ite_eq_right h, ite_eq_right h, env_fold _ (by omega_arith)]

/-- The spread halves, out of the rounds' form, as the bytes of `xmm4`. -/
theorem layerIn_wp (he : Env s) :
    WP isa (.block layerIn) s fun s' => Same s s' ∧
      (∀ q < 16, byte (s'.xmm .xmm4) q = qI (isA (slot (q % 8))) (pkv s q)) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  have hok := conv_all.2.1
  unfold layerInOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  refine run_wp he.rel hrun fun s' hr hs => ⟨hs, fun q hq => ?_, mask_ok hr hok.2⟩
  rw [same_bytes hr hok.1.1 hok.1.2 hq]
  simp only [BV.eval, BitVec.xor_zero, cterms_eval _ (.inr rfl) hq, env_pk hq, mask_zero, BitVec.zero_xor]
  rfl

/-- The bytes of `xmm4`, into the rounds' form with the keys at byte 112,
spread in `xmm0` and `xmm1`. -/
theorem layerOut_wp (he : Env s) :
    WP isa (.block layerOut) s fun s' => Same s s' ∧
      (∀ q < 8, fd (s'.xmm .xmm0) q = qT (isA (slot q)) (byte (s.xmm .xmm4) q) ^^^ kb s (112 + q) ∧
        fd (s'.xmm .xmm1) q = qT (isA (slot q)) (byte (s.xmm .xmm4) (q + 8)) ^^^ kb s (120 + q)) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  have hok := conv_all.2.2.1
  unfold layerOutOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  rw [Bool.and_eq_true] at hok
  refine run_wp he.rel hrun fun s' hr hs => ⟨hs, fun q hq => ?_, mask_ok hr hok.2⟩
  obtain ⟨e₀, e₁⟩ := unpack_ok hr hok.1 hq
  rw [e₀, e₁]
  simp only [BV.eval, BitVec.xor_zero, cterms_eval _ (.inl rfl) (show q < 16 by omega_arith),
    cterms_eval _ (.inl rfl) (show q + 8 < 16 by omega_arith), env_var .xmm4 (show q < 16 by omega_arith),
    env_var .xmm4 (show q + 8 < 16 by omega_arith), show (q + 8) % 8 = q by omega_arith,
    show q % 8 = q by omega_arith]
  rw [show 128 + 112 + q = 128 + (112 + q) by omega_arith, show 128 + 112 + (q + 8) = 128 + (120 + q) by omega_arith,
    env_key (by omega_arith), env_key (by omega_arith)]
  exact ⟨BitVec.xor_comm _ _, BitVec.xor_comm _ _⟩

theorem outq_lt {q : Nat} (h : q < 16) : outq q < 16 := by
  unfold outq bswq
  repeat' split
  all_goals omega_arith

/-- The spread halves after the last round, as the block's bytes in `xmm6`,
with the last keys (at byte 64). -/
theorem tail_wp (he : Env s) :
    WP isa (.block tailX) s fun s' => Same s s' ∧
      ∀ q < 16, byte (s'.xmm .xmm6) q = qI (isA (slot (outq q % 8))) (pkv s (outq q)) ^^^ kb s (64 + q) := by
  have hok := conv_all.2.2.2
  unfold tailOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  refine run_wp he.rel hrun fun s' hr hs => ⟨hs, fun q hq => ?_⟩
  rw [same_bytes hr hok.1 hok.2 hq]
  simp only [BV.eval, BitVec.xor_zero, cterms_eval _ (.inr rfl) (outq_lt hq), env_pk (outq_lt hq)]
  rw [show 128 + 64 + q = 128 + (64 + q) by omega_arith, env_key (by omega_arith)]
  exact BitVec.xor_comm _ _

end

/-! ### The rounds of a group -/

theorem xor_x3 (a b : Byte) : a ^^^ (a ^^^ b) = b := by rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
theorem xor_lc (a b c : Byte) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by ac_rfl

/-- Exclusive-ors of bytes, up to order and pairs that cancel. -/
macro "xor_norm" : tactic =>
  `(tactic| simp only [BitVec.xor_assoc, BitVec.xor_comm, xor_lc, xor_x3, BitVec.xor_self, BitVec.xor_zero,
    BitVec.zero_xor])

/-- The register `x` spreads the bytes `f` of a half: byte `j` in slot `slot j`. -/
def Spread (x : BitVec 128) (f : Nat → Byte) : Prop := ∀ j < 8, fd x (slot j) = f j

theorem Spread.congr {x : BitVec 128} {f g : Nat → Byte} (h : Spread x f) (e : ∀ j < 8, f j = g j) : Spread x g :=
  fun j hj => (h j hj).trans (e j hj)

theorem slot_slot {j : Nat} (h : j < 8) : slot (slot j) = j := by unfold slot; omega_arith

theorem sets_lt {j : Nat} (hj : j < 8) : ∀ i ∈ sets j, i < 8 := by
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega_arith
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem foldr_congr_mem {l : List Nat} {f g : Nat → Byte → Byte} (h : ∀ i ∈ l, ∀ a, f i a = g i a) (z : Byte) :
    l.foldr f z = l.foldr g z := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih fun i hi => h i (List.mem_cons_of_mem _ hi), h i (List.mem_cons_self ..)]

theorem glin_congr {z z' : Nat → Byte} (h : ∀ i < 8, z i = z' i) {j : Nat} (hj : j < 8) : glin z j = glin z' j :=
  foldr_congr_mem (fun i hi a => by rw [h i (sets_lt hj i hi)]) _

section
variable {s : State}

theorem Env.same {s' : State} (he : Env s) (hs : Same s s') (hm : ∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) :
    Env s' := by
  obtain ⟨f, rfl⟩ := hs
  exact ⟨he.tb, he.fit, he.acc, hm⟩

theorem kb_same {s' : State} (hs : Same s s') (o : Nat) : kb s' o = kb s o := by
  obtain ⟨f, rfl⟩ := hs; rfl

/-- `round_wp`, of spread registers. -/
theorem round_spread {xr y : XReg} {i : Nat} (hi : i < 6) (hok : roundOk xr y i = true) (he : Env s)
    {f g : Nat → Byte} (hx : Spread (s.xmm xr) f) (hy : Spread (s.xmm y) g) :
    WP isa (.block (round xr y i)) s fun s' => Same s s' ∧ Env s' ∧
      Spread (s'.xmm xr) (fun j => f j ^^^ kb s (16 + 8 * i + slot j)) ∧
      Spread (s'.xmm y) (fun j => g j ^^^ glin (fun i => aesSbox (f i)) j) := by
  refine WP.mono (round_wp hi hok he) fun s' ⟨hs, hX, hY, hm⟩ => ⟨hs, he.same hs hm, fun j hj => ?_, fun j hj => ?_⟩
  · have hq := slot_lt j
    show fd (s'.xmm xr) (slot j) = f j ^^^ kb s (16 + 8 * i + slot j)
    rw [fd, hX _ (by omega_arith), hX _ (by omega_arith), ite_eq_left hq, ite_eq_right (by omega_arith),
      BitVec.xor_zero, ← hx j hj, fd]
    ac_rfl
  · show fd (s'.xmm y) (slot j) = g j ^^^ glin (fun i => aesSbox (f i)) j
    rw [hY _ (slot_lt j), hy j hj, slot_slot hj]
    exact congrArg (g j ^^^ ·) (glin_congr (fun i hi => congrArg aesSbox (hx i hi)) hj)

/-- The keys of a group of six rounds with the subkeys `k 0 … k 5`, at
`esi`: the differences of the rounds' keys, with the maps' constants. -/
structure GroupKeys (s : State) (k : Nat → BitVec 64) : Prop where
  d : ∀ r < 4, ∀ j < 8, kb s (16 + 8 * r + slot j) = dq (k r ^^^ k (r + 2)) j ^^^ gc j
  d4 : ∀ j < 8, kb s (48 + slot j) = dq (k 4) j ^^^ gc j ^^^ c5
  d5 : ∀ j < 8, kb s (56 + slot j) = dq (k 5) j ^^^ c5

theorem GroupKeys.same {s' : State} {k : Nat → BitVec 64} (h : GroupKeys s k) (hs : Same s s') : GroupKeys s' k :=
  ⟨fun r hr j hj => by rw [kb_same hs]; exact h.d r hr j hj, fun j hj => by rw [kb_same hs]; exact h.d4 j hj,
    fun j hj => by rw [kb_same hs]; exact h.d5 j hj⟩

theorem ok0 (i : Nat) (hi : i ∈ [0, 2, 4]) : roundOk .xmm0 .xmm1 i = true := List.all_eq_true.mp round_all.1 i hi
theorem ok1 (i : Nat) (hi : i ∈ [1, 3, 5]) : roundOk .xmm1 .xmm0 i = true := List.all_eq_true.mp round_all.2 i hi

theorem tgt (x k k' : BitVec 64) (j : Nat) :
    dq x j ^^^ dq k j ^^^ c5 ^^^ (dq (k ^^^ k') j ^^^ gc j) = dq x j ^^^ dq k' j ^^^ c5 ^^^ gc j := by
  rw [dq_xor]; xor_norm

theorem src (x y k k' : BitVec 64) {j : Nat} (hj : j < 8) :
    dq y j ^^^ dq k' j ^^^ c5 ^^^ gc j ^^^ glin (fun i => aesSbox (dq x i ^^^ dq k i ^^^ c5)) j =
      dq (y ^^^ Spec.Camellia.f x k) j ^^^ dq k' j ^^^ c5 := by
  rw [glin_f _ _ hj, dq_xor]; xor_norm

theorem tgt4 (x k : BitVec 64) (j : Nat) :
    dq x j ^^^ dq k j ^^^ c5 ^^^ (dq k j ^^^ gc j ^^^ c5) = dq x j ^^^ gc j := by xor_norm

theorem src5 (x y k : BitVec 64) {j : Nat} (hj : j < 8) :
    dq y j ^^^ gc j ^^^ glin (fun i => aesSbox (dq x i ^^^ dq k i ^^^ c5)) j = dq (y ^^^ Spec.Camellia.f x k) j := by
  rw [glin_f _ _ hj, dq_xor]; xor_norm

theorem tgt5 (x k : BitVec 64) (j : Nat) : dq x j ^^^ dq k j ^^^ c5 ^^^ (dq k j ^^^ c5) = dq x j := by xor_norm

/-- Two rounds, whose keys' differences are with `kc` and `kd`. -/
theorem pair_wp {i : Nat} (hi : i = 0 ∨ i = 2) (he : Env s) {ka kb' kc kd a b : BitVec 64}
    (h₁ : ∀ j < 8, kb s (16 + 8 * i + slot j) = dq (ka ^^^ kc) j ^^^ gc j)
    (h₂ : ∀ j < 8, kb s (16 + 8 * (i + 1) + slot j) = dq (kb' ^^^ kd) j ^^^ gc j)
    (h0 : Spread (s.xmm .xmm0) fun j => dq a j ^^^ dq ka j ^^^ c5)
    (h1 : Spread (s.xmm .xmm1) fun j => dq b j ^^^ dq kb' j ^^^ c5 ^^^ gc j) :
    WP isa (.block (round .xmm0 .xmm1 i ++ round .xmm1 .xmm0 (i + 1))) s fun s' => Same s s' ∧ Env s' ∧
      Spread (s'.xmm .xmm0) (fun j => dq (Proof.Camellia.pair ka kb' (a, b)).1 j ^^^ dq kc j ^^^ c5) ∧
      Spread (s'.xmm .xmm1) (fun j => dq (Proof.Camellia.pair ka kb' (a, b)).2 j ^^^ dq kd j ^^^ c5 ^^^ gc j) := by
  have o0 : roundOk .xmm0 .xmm1 i = true := ok0 i (by rcases hi with rfl | rfl <;> decide)
  have o1 : roundOk .xmm1 .xmm0 (i + 1) = true := ok1 (i + 1) (by rcases hi with rfl | rfl <;> decide)
  refine WP.block_append_iff.mpr (WP.mono (round_spread (by omega_arith) o0 he h0 h1) fun s₁ ⟨e₁, he₁, x₁, y₁⟩ => ?_)
  have x₁ := x₁.congr (g := fun j => dq a j ^^^ dq kc j ^^^ c5 ^^^ gc j) fun j hj =>
    (congrArg (dq a j ^^^ dq ka j ^^^ c5 ^^^ ·) (h₁ j hj)).trans (tgt a ka kc j)
  have y₁ := y₁.congr (g := fun j => dq (b ^^^ Spec.Camellia.f a ka) j ^^^ dq kb' j ^^^ c5) fun j hj => src a b ka kb' hj
  refine WP.mono (round_spread (by omega_arith) o1 he₁ y₁ x₁) fun s₂ ⟨e₂, he₂, y₂, x₂⟩ => ?_
  refine ⟨e₁.trans e₂, he₂, x₂.congr fun j hj => src _ a kb' kc hj, y₂.congr fun j hj => ?_⟩
  have hk : kb s₁ (16 + 8 * (i + 1) + slot j) = dq (kb' ^^^ kd) j ^^^ gc j := (kb_same e₁ _).trans (h₂ j hj)
  exact (congrArg (dq (b ^^^ Spec.Camellia.f a ka) j ^^^ dq kb' j ^^^ c5 ^^^ ·) hk).trans (tgt _ kb' kd j)

/-- The last two rounds of a group. -/
theorem lastpair_wp (he : Env s) {ka kb' a b : BitVec 64}
    (h₁ : ∀ j < 8, kb s (48 + slot j) = dq ka j ^^^ gc j ^^^ c5)
    (h₂ : ∀ j < 8, kb s (56 + slot j) = dq kb' j ^^^ c5)
    (h0 : Spread (s.xmm .xmm0) fun j => dq a j ^^^ dq ka j ^^^ c5)
    (h1 : Spread (s.xmm .xmm1) fun j => dq b j ^^^ dq kb' j ^^^ c5 ^^^ gc j) :
    WP isa (.block (round .xmm0 .xmm1 4 ++ round .xmm1 .xmm0 5)) s fun s' => Same s s' ∧ Env s' ∧
      Spread (s'.xmm .xmm0) (dq (Proof.Camellia.pair ka kb' (a, b)).1) ∧
      Spread (s'.xmm .xmm1) (dq (Proof.Camellia.pair ka kb' (a, b)).2) := by
  refine WP.block_append_iff.mpr (WP.mono (round_spread (by decide) (ok0 4 (by decide)) he h0 h1)
    fun s₁ ⟨e₁, he₁, x₁, y₁⟩ => ?_)
  have x₁ := x₁.congr (g := fun j => dq a j ^^^ gc j) fun j hj =>
    (congrArg (dq a j ^^^ dq ka j ^^^ c5 ^^^ ·) (h₁ j hj)).trans (tgt4 a ka j)
  have y₁ := y₁.congr (g := fun j => dq (b ^^^ Spec.Camellia.f a ka) j ^^^ dq kb' j ^^^ c5) fun j hj => src a b ka kb' hj
  refine WP.mono (round_spread (by decide) (ok1 5 (by decide)) he₁ y₁ x₁) fun s₂ ⟨e₂, he₂, y₂, x₂⟩ => ?_
  refine ⟨e₁.trans e₂, he₂, x₂.congr fun j hj => src5 _ a kb' hj, y₂.congr fun j hj => ?_⟩
  have hk : kb s₁ (16 + 8 * 5 + slot j) = dq kb' j ^^^ c5 := (kb_same e₁ _).trans (h₂ j hj)
  exact (congrArg (dq (b ^^^ Spec.Camellia.f a ka) j ^^^ dq kb' j ^^^ c5 ^^^ ·) hk).trans (tgt5 _ kb' j)

open VG.Proof.Camellia (pair) in
/-- The six rounds of a group: from the halves `a` and `b` with the first
two keys, spread in `xmm0` and `xmm1`, to the halves after the three pairs
of rounds. -/
theorem rounds6_wp (he : Env s) {k : Nat → BitVec 64} (hk : GroupKeys s k) {a b : BitVec 64}
    (h0 : Spread (s.xmm .xmm0) fun j => dq a j ^^^ dq (k 0) j ^^^ c5)
    (h1 : Spread (s.xmm .xmm1) fun j => dq b j ^^^ dq (k 1) j ^^^ c5 ^^^ gc j) :
    WP isa (.block rounds6) s fun s' => Same s s' ∧ Env s' ∧
      Spread (s'.xmm .xmm0) (dq (pair (k 4) (k 5) (pair (k 2) (k 3) (pair (k 0) (k 1) (a, b)))).1) ∧
      Spread (s'.xmm .xmm1) (dq (pair (k 4) (k 5) (pair (k 2) (k 3) (pair (k 0) (k 1) (a, b)))).2) := by
  unfold rounds6
  rw [← List.append_assoc, ← List.append_assoc (round .xmm0 .xmm1 2)]
  refine WP.block_append_iff.mpr (WP.mono (pair_wp (.inl rfl) he (hk.d 0 (by decide)) (hk.d 1 (by decide)) h0 h1)
    fun s₁ ⟨e₁, he₁, x₁, y₁⟩ => ?_)
  have k₁ := hk.same e₁
  refine WP.block_append_iff.mpr (WP.mono (pair_wp (.inr rfl) he₁ (k₁.d 2 (by decide)) (k₁.d 3 (by decide)) x₁ y₁)
    fun s₂ ⟨e₂, he₂, x₂, y₂⟩ => ?_)
  have k₂ := k₁.same e₂
  exact WP.mono (lastpair_wp he₂ k₂.d4 k₂.d5 x₂ y₂) fun s₃ ⟨e₃, he₃, x₃, y₃⟩ => ⟨(e₁.trans e₂).trans e₃, he₃, x₃, y₃⟩

end

end

/-! ## The FL layer and the block -/

section


open VG VG.X86 VG.X86.ByteMap VG.Impl.Camellia.X86.AesNi
open VG.Impl.Modes.X86 (sb at_ argOp)
open VG.Proof.Modes.X86 (ScrIn)

/-! ### The FL layer -/

theorem dword_psllq32 (a : BitVec 128) {k : Nat} (hk : k < 4) :
    dword (XShiftOp.eval .psllq a 32) k = if k % 2 = 1 then dword a (k - 1) else 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_dword, decide_eq_true hi, Bool.true_and,
    show 32 * k + i = 64 * (k / 2) + (32 * (k % 2) + i) by omega_arith,
    psllq32_bit a (show k / 2 < 2 by omega_arith) (show 32 * (k % 2) + i < 64 by omega_arith)]
  by_cases h : k % 2 = 1
  · rw [ite_eq_left h, decide_eq_true (show 32 ≤ 32 * (k % 2) + i by omega_arith), Bool.true_and, getLsbD_dword,
      decide_eq_true hi, Bool.true_and]
    exact congrArg _ (by omega_arith)
  · rw [ite_eq_right h, decide_eq_false (show ¬ 32 ≤ 32 * (k % 2) + i by omega_arith), Bool.false_and]
    exact (BitVec.getLsbD_zero ..).symm

theorem dword_psrlq32 (a : BitVec 128) {k : Nat} (hk : k < 4) :
    dword (XShiftOp.eval .psrlq a 32) k = if k % 2 = 0 then dword a (k + 1) else 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_dword, decide_eq_true hi, Bool.true_and,
    show 32 * k + i = 64 * (k / 2) + (32 * (k % 2) + i) by omega_arith,
    psrlq32_bit a (show k / 2 < 2 by omega_arith) (show 32 * (k % 2) + i < 64 by omega_arith)]
  by_cases h : k % 2 = 0
  · rw [ite_eq_left h, decide_eq_true (show 32 * (k % 2) + i < 32 by omega_arith), Bool.true_and, getLsbD_dword,
      decide_eq_true hi, Bool.true_and]
    exact congrArg _ (by omega_arith)
  · rw [ite_eq_right h, decide_eq_false (show ¬ 32 * (k % 2) + i < 32 by omega_arith), Bool.false_and]
    exact (BitVec.getLsbD_zero ..).symm

/-- What `step` leaves of `v` with the mask `e`. -/
def flv (v e : BitVec 128) : BitVec 128 :=
  XBinOp.eval .pxor (XBinOp.eval .pxor v (XShiftOp.eval .psllq (XBinOp.eval .por
    (XShiftOp.eval .pslld (XBinOp.eval .pand e v) 1) (XShiftOp.eval .psrld (XBinOp.eval .pand e v) 31)) 32))
    (XShiftOp.eval .psrlq (XBinOp.eval .pand e v) 32)

theorem dword_flv (v e : BitVec 128) {k : Nat} (hk : k < 4) :
    dword (flv v e) k = if k % 2 = 0 then dword v k ^^^ (dword e (k + 1) &&& dword v (k + 1))
      else dword v k ^^^ (dword e (k - 1) &&& dword v (k - 1)).rotateLeft 1 := by
  have h1 : (1 : BitVec 8).toNat < 32 := by decide
  have h31 : (31 : BitVec 8).toNat < 32 := by decide
  rw [flv, dword_pxor, dword_pxor, dword_psllq32 _ hk, dword_psrlq32 _ hk]
  rcases cases4 hk with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, ↓reduceIte, BitVec.xor_zero,
      dword_por, dword_pslld _ _ h1 (show 0 < 4 by decide), dword_psrld _ _ h31 (show 0 < 4 by decide),
      dword_pslld _ _ h1 (show 2 < 4 by decide), dword_psrld _ _ h31 (show 2 < 4 by decide),
      Lanes.dword_pand, Nat.zero_add, Nat.one_ne_zero, Nat.zero_ne_one]
  all_goals rfl

/-- The halves in a register: each with its high 32 bits first. -/
def hl (L R : BitVec 64) : BitVec 128 :=
  ofDwords ((L >>> 32).setWidth 32) (L.setWidth 32) ((R >>> 32).setWidth 32) (R.setWidth 32)

theorem xor_andn (a b k : BitVec 32) : a ^^^ k ^^^ (~~~k &&& b) = a ^^^ (b ||| k) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, decide_true,
    Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases k.getLsbD i <;> rfl

theorem xor_andn' (a b k : BitVec 32) : a ^^^ (~~~k &&& b) ^^^ k = a ^^^ (b ||| k) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, decide_true,
    Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases k.getLsbD i <;> rfl

theorem hi_app (a b : BitVec 32) : ((a ++ b) >>> 32).setWidth 32 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, decide_eq_true hi, Bool.true_and,
    ite_eq_right (by omega_arith), Nat.add_sub_cancel_left]

theorem lo_app (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, decide_eq_true hi, Bool.true_and, ite_eq_left hi]

/-- The FL layer's three steps, on the halves. -/
theorem flv_fl (L R ke1 ke2 : BitVec 64) :
    flv (XBinOp.eval .pxor (flv (hl L R) (ofDwords ((ke1 >>> 32).setWidth 32) 0#32 0#32 (~~~ ke2.setWidth 32)))
        (ofDwords (ke1.setWidth 32) 0#32 (ke2.setWidth 32) 0#32))
      (ofDwords 0#32 (~~~ ke1.setWidth 32) ((ke2 >>> 32).setWidth 32) 0#32) =
      hl (Spec.Camellia.fl L ke1) (Spec.Camellia.flinv R ke2) := by
  have z : (0#32).rotateLeft 1 = 0#32 := by decide
  rw [← ofDwords_dword (flv _ _)]
  simp only [dword_flv _ _ (show 0 < 4 by decide), dword_flv _ _ (show 1 < 4 by decide),
    dword_flv _ _ (show 2 < 4 by decide), dword_flv _ _ (show 3 < 4 by decide), dword_pxor, hl,
    dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, Nat.reduceMod, Nat.reduceAdd,
    Nat.reduceSub, ↓reduceIte, Nat.reduceEqDiff, BitVec.zero_and, BitVec.xor_zero, z, Spec.Camellia.fl,
    Spec.Camellia.flinv, hi_app, lo_app, xor_andn, xor_andn']
  simp only [BitVec.and_comm]

theorem bz_hi (w : BitVec 64) {j : Nat} (hj : j < 4) :
    ((w >>> 32).setWidth 32).extractLsb' (8 * j) 8 = bz w (j + 4) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, Serial.byte, hi,
    decide_true, Bool.true_and, show 8 * j + i < 32 by omega_arith, show 32 + (8 * j + i) = 8 * (j + 4) + i by omega_arith]

theorem bz_lo (w : BitVec 64) {j : Nat} (hj : j < 4) : (w.setWidth 32).extractLsb' (8 * j) 8 = bz w j := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, Serial.byte, hi,
    decide_true, Bool.true_and, show 8 * j + i < 32 by omega_arith]

/-- The bytes of the halves in a register. -/
theorem byte_hl (L R : BitVec 64) {j : Nat} (hj : j < 8) :
    byte (hl L R) (slot j) = bz L j ∧ byte (hl L R) (slot j + 8) = bz R j := by
  have e := fun i (hi : i < 16) => byte_ofDwords (fun k => [(L >>> 32).setWidth 32, L.setWidth 32,
    (R >>> 32).setWidth 32, R.setWidth 32].getD k 0) hi
  simp only [List.getD_cons_zero, List.getD_cons_succ] at e
  have hs := slot_lt j
  rw [hl, e _ (by omega_arith), e _ (by omega_arith)]
  unfold slot at hs ⊢
  by_cases h : j < 4
  · rw [show (j + 4) % 8 / 4 = 1 by omega_arith, show ((j + 4) % 8 + 8) / 4 = 3 by omega_arith,
      show (j + 4) % 8 % 4 = j by omega_arith, show ((j + 4) % 8 + 8) % 4 = j by omega_arith]
    exact ⟨bz_lo L h, bz_lo R h⟩
  · rw [show (j + 4) % 8 / 4 = 0 by omega_arith, show ((j + 4) % 8 + 8) / 4 = 2 by omega_arith,
      show (j + 4) % 8 % 4 = j - 4 by omega_arith, show ((j + 4) % 8 + 8) % 4 = j - 4 by omega_arith]
    have := bz_hi L (j := j - 4) (by omega_arith)
    have := bz_hi R (j := j - 4) (by omega_arith)
    rw [show j - 4 + 4 = j by omega_arith] at *
    exact ⟨‹_›, ‹_›⟩

/-- A register is its bytes. -/
theorem ext16 {x y : BitVec 128} (h : ∀ i < 16, byte x i = byte y i) : x = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e := congrArg (·.getLsbD (i % 8)) (h (i / 8) (by omega_arith))
  simp only [byte, BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega_arith, decide_true, Bool.true_and,
    show 8 * (i / 8) + i % 8 = i by omega_arith] at e
  exact e

/-- A register with the bytes of the halves. -/
theorem eq_hl {x : BitVec 128} {L R : BitVec 64}
    (h : ∀ j < 8, byte x (slot j) = bz L j ∧ byte x (slot j + 8) = bz R j) : x = hl L R := by
  refine ext16 fun i hi => ?_
  by_cases h8 : i < 8
  · have := (h (slot i) (slot_lt i)).1
    rw [slot_slot h8] at this
    rw [this, ← (byte_hl L R (slot_lt i)).1, slot_slot h8]
  · have := (h (slot (i - 8)) (slot_lt _)).2
    rw [slot_slot (by omega_arith), show i - 8 + 8 = i by omega_arith] at this
    have e := (byte_hl L R (slot_lt (i - 8))).2
    rw [slot_slot (by omega_arith), show i - 8 + 8 = i by omega_arith] at e
    rw [this, e]

variable {s : State}

/-- An instruction that writes an XMM register, from a state given by its XMM registers. -/
theorem wp_xs {f : XReg → BitVec 128} {i : Instr} {is : List Instr} {Q : State → Prop} {d : XReg} {v : BitVec 128}
    (h : exec i { s with xmm := f } = some (State.setXmm { s with xmm := f } d v))
    (k : WP isa (.block is) { s with xmm := fun r => if r = d then v else f r } Q) :
    WP isa (.block (i :: is)) { s with xmm := f } Q := Wp.cons h k

theorem step_wp {off : Nat} (ha : InRegions (s.rd ++ s.wr) (addr (s.gpr kr) off) 16) :
    WP isa (.block (step .xmm4 .xmm2 .xmm3 .xmm5 off)) s fun s' => Same s s' ∧
      s'.xmm .xmm4 = flv (s.xmm .xmm4) (s.mem.readW (addr (s.gpr kr) off) 128) ∧ s'.xmm m0 = s.xmm m0 := by
  refine Wp.cons (s' := { s with xmm := fun r => if r = .xmm2 then s.mem.readW (addr (s.gpr kr) off) 128 else s.xmm r }) ?_
    (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl
      (wp_xs rfl (wp_xs rfl (WP.block_nil ⟨⟨_, rfl⟩, rfl, rfl⟩)))))))))))
  show (s.load128 (addr (s.gpr kr) off)).map _ = _
  rw [State.load128, ite_eq_left ha]; rfl

/-- The masks of the FL layer after a group, the 16 bytes at each of bytes
64, 80 and 96 of its keys (`w`), from its two subkeys. -/
structure LayerWords (w : Nat → BitVec 128) (ke1 ke2 : BitVec 64) : Prop where
  e1 : w 64 = ofDwords ((ke1 >>> 32).setWidth 32) 0#32 0#32 (~~~ ke2.setWidth 32)
  e2 : w 80 = ofDwords 0#32 (~~~ ke1.setWidth 32) ((ke2 >>> 32).setWidth 32) 0#32
  c : w 96 = ofDwords (ke1.setWidth 32) 0#32 (ke2.setWidth 32) 0#32

/-- FL and FL⁻¹ of the halves in `xmm4`. -/
theorem layerMid_wp (he : Env s) {L R ke1 ke2 : BitVec 64} (hv : s.xmm .xmm4 = hl L R)
    (hk : LayerWords (fun o => s.mem.readW (addr (s.gpr kr) o) 128) ke1 ke2) :
    WP isa (.block layerMid) s fun s' => Same s s' ∧ Env s' ∧
      s'.xmm .xmm4 = hl (Spec.Camellia.fl L ke1) (Spec.Camellia.flinv R ke2) := by
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono (step_wp (he.acc 64 (by decide)))
    fun s₁ ⟨e₁, v₁, m₁⟩ => ?_))
  obtain ⟨f₁, rfl⟩ := e₁
  refine Wp.cons (s' := { s with xmm := fun r => if r = .xmm2 then s.mem.readW (addr (s.gpr kr) 96) 128 else f₁ r }) ?_
    (wp_xs rfl (WP.block_nil ?_))
  · show (State.load128 _ (addr (s.gpr kr) 96)).map _ = _
    rw [State.load128, ite_eq_left (he.acc 96 (by decide))]; rfl
  refine WP.mono (step_wp (he.acc 80 (by decide))) fun s₃ ⟨e₃, v₃, m₃⟩ => ?_
  obtain ⟨f₃, rfl⟩ := e₃
  refine ⟨⟨_, rfl⟩, ⟨he.tb, he.fit, he.acc, fun q hq => ?_⟩, ?_⟩
  · show byte (f₃ m0) q = _
    rw [show f₃ m0 = f₁ m0 from m₃, show f₁ m0 = s.xmm m0 from m₁]; exact he.msk q hq
  · show f₃ .xmm4 = _
    rw [show f₃ .xmm4 = flv (XBinOp.eval .pxor (f₁ .xmm4) (s.mem.readW (addr (s.gpr kr) 96) 128))
      (s.mem.readW (addr (s.gpr kr) 80) 128) from v₃, show f₁ .xmm4 = _ from v₁,
      show s.mem.readW (addr (s.gpr kr) 64) 128 = _ from hk.e1, show s.mem.readW (addr (s.gpr kr) 80) 128 = _ from hk.e2,
      show s.mem.readW (addr (s.gpr kr) 96) 128 = _ from hk.c, hv, flv_fl]

/-! ### The keys in the scratch buffer -/

/-- Byte `o` of the keys in the scratch buffer at `B`. -/
def kAt (m : Mem) (B : BitVec 32) (o : Nat) : Byte := m (B.setWidth 64 + BitVec.ofNat 64 (24 + o))

/-- The 16 bytes at byte `o` of the keys in the scratch buffer at `B`. -/
def wAt (m : Mem) (B : BitVec 32) (o : Nat) : BitVec 128 :=
  m.readW (B.setWidth 64 + BitVec.ofNat 64 (24 + o)) 128

/-- The keys of `g` groups of rounds in the scratch buffer at `B`, from the
subkeys `E` in the order they are stored: 112 bytes a group, which are the
first two subkeys in the rounds' form (with the two before them, for the
first group), the six rounds' keys (`GroupKeys`), and then either the masks
of the FL layer or, after the last group, the last two subkeys as they are
stored. -/
structure Keys (m : Mem) (B : BitVec 32) (g : Nat) (E : Nat → BitVec 64) : Prop where
  kin0 : ∀ j < 8, kAt m B (slot j) = dq (E 0 ^^^ E 2) j ^^^ c5 ∧
    kAt m B (slot j + 8) = dq (E 1 ^^^ E 3) j ^^^ c5 ^^^ gc j
  kin : ∀ i, i + 1 < g → ∀ j < 8,
    kAt m B (112 * i + (112 + slot j)) = dq (E (2 + 8 * (i + 1))) j ^^^ c5 ∧
      kAt m B (112 * i + (120 + slot j)) = dq (E (2 + 8 * (i + 1) + 1)) j ^^^ c5 ^^^ gc j
  rk : ∀ i < g, ∀ r < 4, ∀ j < 8, kAt m B (112 * i + (16 + 8 * r + slot j)) =
    dq (E (2 + 8 * i + r) ^^^ E (2 + 8 * i + (r + 2))) j ^^^ gc j
  rk4 : ∀ i < g, ∀ j < 8, kAt m B (112 * i + (48 + slot j)) = dq (E (2 + 8 * i + 4)) j ^^^ gc j ^^^ c5
  rk5 : ∀ i < g, ∀ j < 8, kAt m B (112 * i + (56 + slot j)) = dq (E (2 + 8 * i + 5)) j ^^^ c5
  fl : ∀ i, i + 1 < g → LayerWords (fun o => wAt m B (112 * i + o)) (E (8 + 8 * i)) (E (9 + 8 * i))
  out : ∀ j < 8, kAt m B (112 * (g - 1) + (64 + (7 - j))) = bz (E (8 * g)) j ∧
    kAt m B (112 * (g - 1) + (72 + (7 - j))) = bz (E (8 * g + 1)) j

/-- A state of `crypt` at group `i`, from the state `s₀` it starts in: the
keys' pointer at the group's keys, the table's address, and memory as it
was. -/
structure At (s₀ : State) (B : BitVec 32) (i : Nat) (s : State) : Prop where
  base : s.gpr Impl.Modes.X86.sb = B
  esp : s.gpr .esp = s₀.gpr .esp
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  tb : s.gpr tbr = s₀.syms tableName
  kp : s.gpr kr = B + BitVec.ofNat 32 (24 + 112 * i)

section
variable {s₀ : State} {B : BitVec 32} {i : Nat}

theorem At.same {s' : State} (h : At s₀ B i s) (hs : Same s s') : At s₀ B i s' := by
  obtain ⟨f, rfl⟩ := hs
  exact ⟨h.base, h.esp, h.mem, h.rd, h.wr, h.syms, h.tb, h.kp⟩

theorem At.kr64 (h : At s₀ B i s) (hf : B.toNat + 544 ≤ 2 ^ 32) (hi : i < 4) :
    (s.gpr Impl.Camellia.X86.AesNi.kr).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 (24 + 112 * i) := by
  rw [h.kp]
  exact addr_eq (by omega_arith)

theorem At.krNat (h : At s₀ B i s) (hf : B.toNat + 544 ≤ 2 ^ 32) (hi : i < 4) :
    (s.gpr Impl.Camellia.X86.AesNi.kr).toNat = B.toNat + (24 + 112 * i) := by
  rw [h.kp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 24 + 112 * i) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

theorem At.adr (h : At s₀ B i s) (hf : B.toNat + 544 ≤ 2 ^ 32) (hi : i < 4) {o : Nat} (ho : o ≤ 128) :
    VG.X86.addr (s.gpr Impl.Camellia.X86.AesNi.kr) o = B.setWidth 64 + BitVec.ofNat 64 (24 + (112 * i + o)) := by
  have := h.krNat hf hi
  rw [addr_eq (by omega_arith), h.kr64 hf hi, Offset.add_ofNat_add_ofNat, Nat.add_assoc]

theorem At.env (h : At s₀ B i s) (hs : ScrIn s₀ B 136) (hi : i < 4) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) :
    Env s := by
  have hf := hs.fit
  have hn := h.krNat hf hi
  refine ⟨by rw [h.tb, h.syms], by omega_arith, fun o ho => ⟨_, List.mem_append_right _ (by rw [h.wr]; exact hs.wr), ?_⟩, hm⟩
  rw [h.adr hf hi (by omega_arith)]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem At.key (h : At s₀ B i s) (hf : B.toNat + 544 ≤ 2 ^ 32) (hi : i < 4) (o : Nat) :
    AesNi.kb s o = kAt s₀.mem B (112 * i + o) := by
  rw [AesNi.kb, h.kr64 hf hi, Offset.add_ofNat_add_ofNat, Nat.add_assoc, h.mem]; rfl

theorem At.word (h : At s₀ B i s) (hf : B.toNat + 544 ≤ 2 ^ 32) (hi : i < 4) {o : Nat} (ho : o ≤ 128) :
    s.mem.readW (VG.X86.addr (s.gpr Impl.Camellia.X86.AesNi.kr) o) 128 = wAt s₀.mem B (112 * i + o) := by
  rw [h.adr hf hi ho, h.mem]; rfl

/-- A general register written by an instruction that leaves the others,
memory and the XMM registers. -/
theorem At.upd {s' : State} {d : Reg} {v : BitVec 32} (h : At s₀ B i s) (u : Wp.Upd s s' d v)
    (hd : d ≠ Impl.Modes.X86.sb ∧ d ≠ .esp ∧ d ≠ tbr ∧ d ≠ Impl.Camellia.X86.AesNi.kr) : At s₀ B i s' :=
  ⟨by rw [u.other _ (Ne.symm hd.1)]; exact h.base, by rw [u.other _ (Ne.symm hd.2.1)]; exact h.esp,
    u.mem.trans h.mem, u.rd.trans h.rd, u.wr.trans h.wr, u.syms.trans h.syms,
    by rw [u.other _ (Ne.symm hd.2.2.1)]; exact h.tb, by rw [u.other _ (Ne.symm hd.2.2.2)]; exact h.kp⟩

end

/-! ### The block -/

section
variable {is : List Instr} {Q : State → Prop}

/-- `sub d, v`, with the flags and the XMM registers. -/
theorem wp_subi_x {d : Reg} {v : BitVec 32}
    (k : ∀ s', Wp.Upd s s' d (s.gpr d - v) → s'.xmm = s.xmm → s'.zf = some (s.gpr d - v == 0) →
      WP isa (.block is) s' Q) : WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ (Wp.Upd.flags _ _ _ _ _ _) rfl rfl)

theorem wp_addi_x {d : Reg} {v : BitVec 32}
    (k : ∀ s', Wp.Upd s s' d (s.gpr d + v) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ (Wp.Upd.flags _ _ _ _ _ _) rfl)

theorem wp_test_x {d : Reg}
    (k : ∀ s', Wp.Fupd s s' → s'.xmm = s.xmm → s'.zf = some (s.gpr d &&& s.gpr d == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.reg d) :: is)) s Q :=
  Wp.cons rfl (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl)

end

theorem bswq_slot {j : Nat} (hj : j < 8) : bswq (slot j) = 7 - j ∧ bswq (slot j + 8) = 15 - j := by
  unfold bswq slot
  constructor <;> (repeat' split) <;> omega_arith

theorem bz_byteOf (w : BitVec 64) {j : Nat} (hj : j < 8) : bz w j = Proof.Camellia.byteOf w (7 - j) := by
  show (w >>> (8 * j)).setWidth 8 = (w >>> (56 - 8 * (7 - j))).setWidth 8
  rw [show 56 - 8 * (7 - j) = 8 * j by omega_arith]

/-- The halves `d` in the rounds' form with the first two subkeys of group
`i`, spread in `xmm0` and `xmm1`. -/
def Halves (s : State) (E : Nat → BitVec 64) (i : Nat) (d : BitVec 64 × BitVec 64) : Prop :=
  Spread (s.xmm .xmm0) (fun j => dq d.1 j ^^^ dq (E (2 + 8 * i)) j ^^^ c5) ∧
    Spread (s.xmm .xmm1) (fun j => dq d.2 j ^^^ dq (E (2 + 8 * i + 1)) j ^^^ c5 ^^^ gc j)

/-- The block at byte 8 of the scratch buffer to the first round's halves:
`cryptHead` reads bytes 8 to 24, the keys, and the two stack arguments. -/
theorem cryptHead_wp {B : BitVec 32} {R : Nat} (hB : s.gpr Impl.Modes.X86.sb = B) (hs : ScrIn s B 136)
    (hR : R = 18 ∨ R = 24) (hin : InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4)
    (hv : s.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 R)
    (htab : s.mem.readW (B.setWidth 64) 32 = s.syms tableName) :
    WP isa (.block cryptHead) s fun s' => At s B 0 s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧
      s'.gpr .ecx = BitVec.ofNat 32 (R / 6) ∧
      ∀ q < 8, fd (s'.xmm .xmm0) q =
          qT (isA (slot q)) (s.mem (B.setWidth 64 + BitVec.ofNat 64 (8 + bswq q))) ^^^ kAt s.mem B q ∧
        fd (s'.xmm .xmm1) q =
          qT (isA (slot q)) (s.mem (B.setWidth 64 + BitVec.ofNat 64 (8 + bswq (q + 8)))) ^^^ kAt s.mem B (q + 8) := by
  have hf := hs.fit
  have hw : InRegions (s.rd ++ s.wr) (addr B 0) 4 := ⟨_, List.mem_append_right _ hs.wr, by
    rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  show WP isa (.block (.mov tbr (.mem ⟨Impl.Modes.X86.sb, 0⟩) :: .mov .ecx (.mem ⟨.esp, 4 + 4 * 1⟩) ::
    .shift .shr .ecx 3 :: .alu .add .ecx (.imm 1) :: .mov kr (.reg Impl.Modes.X86.sb) :: .alu .add kr (.imm 24) ::
    .movdquLoad .xmm0 ⟨Impl.Modes.X86.sb, 8⟩ :: headX)) s _
  refine Wp.wp_ldm hB hw fun s₁ u₁ => ?_
  refine Wp.wp_ldm (u₁.other .esp (by decide)) (by rw [u₁.rd, u₁.wr]; exact hin) fun s₂ u₂ => ?_
  refine Wp.wp_shr (by decide) fun s₃ u₃ _ => ?_
  refine Wp.wp_addi fun s₄ u₄ => ?_
  refine Wp.wp_mov fun s₅ u₅ => ?_
  refine Wp.wp_addi fun s₆ u₆ => ?_
  have e₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have b₆ : s₆.gpr Impl.Modes.X86.sb = B := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hB]
  have r₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have w₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have hl : InRegions (s₆.rd ++ s₆.wr) (addr B 8) 16 := ⟨_, List.mem_append_right _ (by rw [w₆]; exact hs.wr), by
    rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine Wp.cons (s' := s₆.setXmm .xmm0 (s₆.mem.readW (addr B 8) 128)) ?_ ?_
  · show (s₆.load128 (addr (s₆.gpr Impl.Modes.X86.sb) 8)).map _ = _
    rw [b₆, State.load128, ite_eq_left hl]; rfl
  have a : At s B 0 (s₆.setXmm .xmm0 (s₆.mem.readW (addr B 8) 128)) := by
    refine ⟨b₆, ?_, e₆, r₆, w₆, ?_, ?_, ?_⟩
    · show s₆.gpr .esp = _
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide)]
    · show s₆.syms = _
      rw [u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]
    · show s₆.gpr tbr = _
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr, addr_eq (by omega_arith), BitVec.add_zero]
      exact htab
    · show s₆.gpr kr = _
      rw [u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), hB]
      rfl
  have hn := a.krNat hf (by decide)
  refine WP.mono (head_wp (by rw [a.tb, a.syms]) (by omega_arith) fun o ho =>
    ⟨_, List.mem_append_right _ (by rw [a.wr]; exact hs.wr), by
      rw [a.adr hf (by decide) (by omega_arith)]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩) fun s' ⟨e', hx, hm⟩ => ?_
  have hbyte : ∀ k < 16, byte ((s₆.setXmm .xmm0 (s₆.mem.readW (addr B 8) 128)).xmm .xmm0) k =
      s.mem (B.setWidth 64 + BitVec.ofNat 64 (8 + k)) := fun k hk => by
    show (s₆.mem.readW (addr B 8) 128).extractLsb' (8 * k) 8 = _
    rw [byte_readW _ _ (by omega_arith), addr_eq (by omega_arith), Offset.add_ofNat_add_ofNat, e₆]
  refine ⟨a.same e', hm, ?_, fun q hq => ?_⟩
  · obtain ⟨f, rfl⟩ := e'
    show s₆.gpr .ecx = _
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem]
    show (s.mem.readW (s.ea (argOp 1)) 32 >>> 3) + 1 = _
    rw [hv]
    rcases hR with rfl | rfl <;> rfl
  · obtain ⟨x₀, x₁⟩ := hx q hq
    rw [x₀, x₁, hbyte _ (bswq_lt (show q < 16 by omega_arith)), hbyte _ (bswq_lt (show q + 8 < 16 by omega_arith)),
      a.key hf (by decide), a.key hf (by decide), Nat.mul_zero, Nat.zero_add, Nat.zero_add]
    exact ⟨rfl, rfl⟩

section
variable {s₀ : State} {B : BitVec 32} {g i : Nat} {E : Nat → BitVec 64}

open VG.Proof.Camellia (pair group groups byteOf)

/-- The three pairs of rounds of group `i`. -/
def tri (E : Nat → BitVec 64) (i : Nat) (d : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  pair (E (2 + 8 * i + 4)) (E (2 + 8 * i + 5)) (pair (E (2 + 8 * i + 2)) (E (2 + 8 * i + 3))
    (pair (E (2 + 8 * i)) (E (2 + 8 * i + 1)) d))

theorem group_eq (g : Nat) (E : Nat → BitVec 64) (d : BitVec 64 × BitVec 64) (i : Nat) :
    group g E d i = if i + 1 < g then
      (Spec.Camellia.fl (tri E i d).1 (E (8 + 8 * i)), Spec.Camellia.flinv (tri E i d).2 (E (9 + 8 * i)))
      else tri E i d := by
  simp only [group, tri, show 3 + 8 * i = 2 + 8 * i + 1 by omega_arith, show 4 + 8 * i = 2 + 8 * i + 2 by omega_arith,
    show 5 + 8 * i = 2 + 8 * i + 3 by omega_arith, show 6 + 8 * i = 2 + 8 * i + 4 by omega_arith,
    show 7 + 8 * i = 2 + 8 * i + 5 by omega_arith]

/-- The six rounds of group `i` and the count of the groups left. -/
theorem rounds_wp (hs : ScrIn s₀ B 136) (hk : Keys s₀.mem B g E) (hi : i < g) (hg : g ≤ 4) (h : At s₀ B i s)
    (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) {d : BitVec 64 × BitVec 64} (hh : Halves s E i d) {n : Nat}
    (hc : s.gpr .ecx = BitVec.ofNat 32 n) (hn : 1 ≤ n) (hn4 : n ≤ 4) :
    WP isa (.block rounds) s fun s' => At s₀ B i s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧
      s'.gpr .ecx = BitVec.ofNat 32 (n - 1) ∧ s'.zf = some (decide (n = 1)) ∧
      Spread (s'.xmm .xmm0) (dq (tri E i d).1) ∧ Spread (s'.xmm .xmm1) (dq (tri E i d).2) := by
  have hf := hs.fit
  have hi4 : i < 4 := by omega_arith
  have he := h.env hs hi4 hm
  have hK : GroupKeys s (fun r => E (2 + 8 * i + r)) :=
    ⟨fun r hr j hj => by rw [h.key hf hi4]; exact hk.rk i hi r hr j hj,
      fun j hj => by rw [h.key hf hi4]; exact hk.rk4 i hi j hj,
      fun j hj => by rw [h.key hf hi4]; exact hk.rk5 i hi j hj⟩
  refine WP.block_append_iff.mpr (WP.mono (rounds6_wp he hK (a := d.1) (b := d.2) hh.1 hh.2)
    fun s₁ ⟨e₁, he₁, x₁, y₁⟩ => ?_)
  have c₁ : s₁.gpr .ecx = BitVec.ofNat 32 n := by obtain ⟨f, rfl⟩ := e₁; exact hc
  refine wp_subi_x fun s₂ u₂ xe z₂ => WP.block_nil ?_
  refine ⟨(h.same e₁).upd u₂ (by decide), by rw [xe]; exact he₁.msk, ?_, ?_, by rw [xe]; exact x₁,
    by rw [xe]; exact y₁⟩
  · rw [u₂.gpr, c₁]; exact Wp.ofNat_pred hn
  · rw [z₂, c₁, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_beq (by omega_arith) (by decide)]

/-- FL and FL⁻¹ after group `i`, into the next group's form. -/
theorem layer_wp (hs : ScrIn s₀ B 136) (hk : Keys s₀.mem B g E) (hi : i + 1 < g) (hg : g ≤ 4) (h : At s₀ B i s)
    (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) {P : BitVec 64 × BitVec 64}
    (h0 : Spread (s.xmm .xmm0) (dq P.1)) (h1 : Spread (s.xmm .xmm1) (dq P.2)) {n : Nat}
    (hc : s.gpr .ecx = BitVec.ofNat 32 n) (hn : 1 ≤ n) (hn4 : n ≤ 4) :
    WP isa (.block layer) s fun s' => At s₀ B (i + 1) s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧
      s'.gpr .ecx = BitVec.ofNat 32 n ∧ s'.zf = some false ∧
      Halves s' E (i + 1) (Spec.Camellia.fl P.1 (E (8 + 8 * i)), Spec.Camellia.flinv P.2 (E (9 + 8 * i))) := by
  have hf := hs.fit
  have hi4 : i < 4 := by omega_arith
  have he := h.env hs hi4 hm
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.block_append_iff.mpr
    (WP.mono (layerIn_wp he) fun s₁ ⟨e₁, v₁, m₁⟩ => ?_)))
  have a₁ := h.same e₁
  have he₁ := a₁.env hs hi4 m₁
  have hv : s₁.xmm .xmm4 = hl P.1 P.2 := eq_hl fun j hj => by
    have sj := slot_lt j
    rw [v₁ _ (by omega_arith), v₁ _ (by omega_arith), show slot j % 8 = slot j by omega_arith,
      show (slot j + 8) % 8 = slot j by omega_arith, slot_slot hj, pkv, pkv, ite_eq_left sj,
      ite_eq_right (by omega_arith), Nat.add_sub_cancel, h0 j hj, h1 j hj]
    exact ⟨qI_qT _ _, qI_qT _ _⟩
  refine WP.mono (layerMid_wp he₁ hv (ke1 := E (8 + 8 * i)) (ke2 := E (9 + 8 * i)) ⟨?_, ?_, ?_⟩)
    fun s₂ ⟨e₂, he₂, v₂⟩ => ?_
  · show s₁.mem.readW (addr (s₁.gpr kr) 64) 128 = _
    rw [a₁.word hf hi4 (by decide)]; exact (hk.fl i hi).e1
  · show s₁.mem.readW (addr (s₁.gpr kr) 80) 128 = _
    rw [a₁.word hf hi4 (by decide)]; exact (hk.fl i hi).e2
  · show s₁.mem.readW (addr (s₁.gpr kr) 96) 128 = _
    rw [a₁.word hf hi4 (by decide)]; exact (hk.fl i hi).c
  have a₂ := a₁.same e₂
  refine WP.mono (layerOut_wp he₂) fun s₃ ⟨e₃, x₃, m₃⟩ => ?_
  have a₃ := a₂.same e₃
  have c₃ : s₃.gpr .ecx = BitVec.ofNat 32 n := by
    obtain ⟨f₁, rfl⟩ := e₁; obtain ⟨f₂, rfl⟩ := e₂; obtain ⟨f₃, rfl⟩ := e₃; exact hc
  refine wp_addi_x fun s₄ u₄ xe₄ => wp_test_x fun s₅ u₅ xe₅ z₅ => WP.block_nil ?_
  have x₅ : s₅.xmm = s₃.xmm := xe₅.trans xe₄
  refine ⟨⟨?_, ?_, u₅.mem.trans (u₄.mem.trans a₃.mem), u₅.rd.trans (u₄.rd.trans a₃.rd),
    u₅.wr.trans (u₄.wr.trans a₃.wr), u₅.syms.trans (u₄.syms.trans a₃.syms), ?_, ?_⟩, by rw [x₅]; exact m₃, ?_, ?_,
    fun j hj => ?_, fun j hj => ?_⟩
  · rw [u₅.gpr, u₄.other _ (by decide)]; exact a₃.base
  · rw [u₅.gpr, u₄.other _ (by decide)]; exact a₃.esp
  · rw [u₅.gpr, u₄.other _ (by decide)]; exact a₃.tb
  · rw [u₅.gpr, u₄.gpr, a₃.kp, show (112 : BitVec 32) = BitVec.ofNat 32 112 from rfl, Offset.add_ofNat_add_ofNat,
      show 24 + 112 * i + 112 = 24 + 112 * (i + 1) by omega_arith]
  · rw [u₅.gpr, u₄.other _ (by decide)]; exact c₃
  · rw [z₅, u₄.other _ (by decide), c₃, BitVec.and_self, Wp.ofNat_beq_zero (by omega_arith),
      decide_eq_false (by omega_arith)]
  · show fd (s₅.xmm .xmm0) (slot j) = _
    rw [x₅, (x₃ _ (slot_lt j)).1, slot_slot hj, a₂.key hf hi4, (hk.kin i hi j hj).1, v₂, (byte_hl _ _ hj).1]
    exact (BitVec.xor_assoc _ _ _).symm
  · show fd (s₅.xmm .xmm1) (slot j) = _
    rw [x₅, (x₃ _ (slot_lt j)).2, slot_slot hj, a₂.key hf hi4, (hk.kin i hi j hj).2, v₂, (byte_hl _ _ hj).2]
    simp only [dq, BitVec.xor_assoc]

/-- The loop's invariant, with `n` groups left. -/
def Inv (s₀ : State) (B : BitVec 32) (g : Nat) (E : Nat → BitVec 64) (d₀ : BitVec 64 × BitVec 64) (n : Nat)
    (s : State) : Prop :=
  1 ≤ n ∧ n ≤ g ∧ At s₀ B (g - n) s ∧ (∀ q < 16, byte (s.xmm m0) q = 0x0f#8) ∧ s.gpr .ecx = BitVec.ofNat 32 n ∧
    Halves s E (g - n) ((List.range (g - n)).foldl (group g E) d₀)

theorem foldl_group (g : Nat) (E : Nat → BitVec 64) (d₀ : BitVec 64 × BitVec 64) (i : Nat) :
    (List.range (i + 1)).foldl (group g E) d₀ = group g E ((List.range i).foldl (group g E) d₀) i := by
  rw [List.range_succ, List.foldl_append]; rfl

/-- The groups of rounds: the halves after the last, in the rounds' form. -/
theorem loop_wp (hs : ScrIn s₀ B 136) (hk : Keys s₀.mem B g E) (hg : g ≤ 4) {d₀ : BitVec 64 × BitVec 64} {n : Nat}
    (hI : Inv s₀ B g E d₀ n s) :
    WP isa (.loop (.seq (.block rounds) (.ite .e (.block []) (.block layer))) .ne) s fun s' =>
      At s₀ B (g - 1) s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧
      Spread (s'.xmm .xmm0) (dq (groups g E d₀).1) ∧ Spread (s'.xmm .xmm1) (dq (groups g E d₀).2) := by
  refine WP.loop (M := isa) (Inv s₀ B g E d₀) ?_ n s hI
  rintro n s ⟨hn, hng, a, hm, hc, hh⟩
  refine WP.seq (WP.mono (rounds_wp hs hk (by omega_arith) hg a hm hh hc hn (by omega_arith))
    fun s₁ ⟨a₁, m₁, c₁, z₁, x₁, y₁⟩ => ?_)
  refine WP.ite (decide (n = 1)) z₁ (fun hb => WP.block_nil (.inl ⟨?_, ?_⟩)) fun hb => ?_
  · show s₁.zf.map _ = _
    rw [z₁, hb]; rfl
  · have h1 : n = 1 := of_decide_eq_true hb
    subst h1
    have e : groups g E d₀ = tri E (g - 1) ((List.range (g - 1)).foldl (group g E) d₀) := by
      have := foldl_group g E d₀ (g - 1)
      rw [Nat.sub_add_cancel hng] at this
      rw [groups, this, group_eq, ite_eq_right (by omega_arith)]
    rw [e]
    exact ⟨a₁, m₁, x₁, y₁⟩
  · have h1 : n ≠ 1 := of_decide_eq_false hb
    have hi : g - n + 1 < g := by omega_arith
    refine WP.mono (layer_wp hs hk hi hg a₁ m₁ x₁ y₁ c₁ (by omega_arith) (by omega_arith))
      fun s₂ ⟨a₂, m₂, c₂, z₂, h₂⟩ => .inr ⟨?_, n - 1, by omega_arith, by omega_arith, by omega_arith, ?_, m₂, c₂, ?_⟩
    · show s₂.zf.map _ = _
      rw [z₂]; rfl
    · rw [show g - (n - 1) = g - n + 1 by omega_arith]; exact a₂
    · rw [show g - (n - 1) = g - n + 1 by omega_arith, foldl_group, group_eq, ite_eq_left hi]; exact h₂

theorem outq_slot {j : Nat} (hj : j < 8) : outq (7 - j) = 8 + slot j ∧ outq (15 - j) = slot j := by
  unfold outq bswq slot
  constructor <;> (repeat' split) <;> omega_arith

/-- The halves after the last round to the block, at byte 8 of the scratch
buffer, with the last two subkeys. -/
theorem cryptTail_wp (hs : ScrIn s₀ B 136) (hk : Keys s₀.mem B g E) (hg1 : 1 ≤ g) (hg : g ≤ 4)
    (h : At s₀ B (g - 1) s) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) {P : BitVec 64 × BitVec 64}
    (h0 : Spread (s.xmm .xmm0) (dq P.1)) (h1 : Spread (s.xmm .xmm1) (dq P.2)) :
    WP isa (.block cryptTail) s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s₀.gpr .esp ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.syms = s₀.syms ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 8, 16⟩] s₀.mem s'.mem ∧
      ∀ q < 16, s'.mem (B.setWidth 64 + BitVec.ofNat 64 8 + BitVec.ofNat 64 q) =
        if q < 8 then byteOf (P.2 ^^^ E (8 * g)) q else byteOf (P.1 ^^^ E (8 * g + 1)) (q - 8) := by
  have hf := hs.fit
  have hi4 : g - 1 < 4 := by omega_arith
  have he := h.env hs hi4 hm
  refine WP.block_append_iff.mpr (WP.mono (tail_wp he) fun s₁ ⟨e₁, v₁⟩ => ?_)
  have a₁ := h.same e₁
  have ha : addr B 8 = B.setWidth 64 + BitVec.ofNat 64 8 := addr_eq (by omega_arith)
  have hw : InRegions s₁.wr (addr B 8) 16 := ⟨_, by rw [a₁.wr]; exact hs.wr, by
    rw [ha]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have key : ∀ j < 8, byte (s₁.xmm .xmm6) (7 - j) = bz (P.2 ^^^ E (8 * g)) j ∧
      byte (s₁.xmm .xmm6) (15 - j) = bz (P.1 ^^^ E (8 * g + 1)) j := fun j hj => by
    have sj := slot_lt j
    rw [v₁ _ (by omega_arith), v₁ _ (by omega_arith), (outq_slot hj).1, (outq_slot hj).2,
      show (8 + slot j) % 8 = slot j by omega_arith, show slot j % 8 = slot j by omega_arith, slot_slot hj, pkv, pkv,
      ite_eq_right (by omega_arith), ite_eq_left sj, Nat.add_sub_cancel_left, h1 j hj, h0 j hj, dq, dq, qI_qT, qI_qT,
      h.key hf hi4, h.key hf hi4, (hk.out j hj).1, show 64 + (15 - j) = 72 + (7 - j) by omega_arith, (hk.out j hj).2,
      bz_xor, bz_xor]
    exact ⟨rfl, rfl⟩
  refine Wp.cons (s' := { s₁ with mem := s₁.mem.writeW (addr B 8) (s₁.xmm .xmm6) }) ?_ (WP.block_nil ?_)
  · show s₁.store128 (addr (s₁.gpr Impl.Modes.X86.sb) 8) _ = _
    rw [a₁.base, State.store128, ite_eq_left hw]
  refine ⟨a₁.base, a₁.esp, a₁.rd, a₁.wr, a₁.syms, ?_, fun q hq => ?_⟩
  · show Frame _ s₀.mem (s₁.mem.writeW (addr B 8) _)
    rw [a₁.mem, ha]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 16)
  · show (s₁.mem.writeW (addr B 8) (s₁.xmm .xmm6)) _ = _
    rw [← ha, ← byte_readW (s₁.mem.writeW (addr B 8) (s₁.xmm .xmm6)) (addr B 8) (w := 128) (k := q) (by omega_arith),
      Mem.readW_writeW_self _ _ 16 _ (by decide)]
    show byte (s₁.xmm .xmm6) q = _
    by_cases h8 : q < 8
    · have := (key (7 - q) (by omega_arith)).1
      rw [show 7 - (7 - q) = q by omega_arith] at this
      rw [ite_eq_left h8, this, bz_byteOf _ (by omega_arith), show 7 - (7 - q) = q by omega_arith]
    · have := (key (15 - q) (by omega_arith)).2
      rw [show 15 - (15 - q) = q by omega_arith] at this
      rw [ite_eq_right h8, this, bz_byteOf _ (by omega_arith), show 7 - (15 - q) = q - 8 by omega_arith]

theorem blockAt_get (m : Mem) (p : Addr) {i : Nat} (hi : i < 16) :
    (Spec.Camellia.blockAt m p)[i] = m (p + BitVec.ofNat 64 i) := by
  simp only [Spec.Camellia.blockAt, Vector.getElem_ofFn]

end

/-- `crypt` enciphers the block at byte 8 of the scratch buffer, under the
keys there, and changes nothing else in memory. -/
theorem crypt_wp {B : BitVec 32} {R : Nat} {ws : List (BitVec 64)} (hB : s.gpr Impl.Modes.X86.sb = B)
    (hs : ScrIn s B 136) (hR : R = 18 ∨ R = 24) (hk : Keys s.mem B (R / 6) (fun i => ws.getD i 0))
    (hin : InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4) (hv : s.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 R)
    (htab : s.mem.readW (B.setWidth 64) 32 = s.syms tableName) :
    WP isa crypt s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.syms = s.syms ∧ Frame [⟨B.setWidth 64 + BitVec.ofNat 64 8, 16⟩] s.mem s'.mem ∧
      Spec.Aes.bytesAt s'.mem (B.setWidth 64 + BitVec.ofNat 64 8) 16 =
        Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords R ws)
          (Spec.Aes.bytesAt s.mem (B.setWidth 64 + BitVec.ofNat 64 8) 16) := by
  obtain ⟨g, hg⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  have hg34 : g = 3 ∨ g = 4 := by omega_arith
  rw [hg] at hk
  obtain ⟨E, hE⟩ : ∃ E : Nat → BitVec 64, E = fun i => ws.getD i 0 := ⟨_, rfl⟩
  rw [← hE] at hk
  obtain ⟨blk, hblk⟩ : ∃ blk, blk = Spec.Camellia.blockAt s.mem (B.setWidth 64 + BitVec.ofNat 64 8) := ⟨_, rfl⟩
  obtain ⟨D₁, hD₁⟩ : ∃ D₁, D₁ = (Spec.Camellia.decodeBlock blk >>> 64).setWidth 64 := ⟨_, rfl⟩
  obtain ⟨D₂, hD₂⟩ : ∃ D₂, D₂ = (Spec.Camellia.decodeBlock blk).setWidth 64 := ⟨_, rfl⟩
  have hb : ∀ j < 8, s.mem (B.setWidth 64 + BitVec.ofNat 64 (8 + (7 - j))) = bz D₁ j ∧
      s.mem (B.setWidth 64 + BitVec.ofNat 64 (8 + (15 - j))) = bz D₂ j := fun j hj => by
    rw [bz_byteOf _ hj, bz_byteOf _ hj, hD₁, hD₂, Proof.Camellia.byteOf_hi blk (by omega_arith),
      Proof.Camellia.byteOf_lo blk (by omega_arith), hblk, blockAt_get _ _ (by omega_arith),
      blockAt_get _ _ (by omega_arith), Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat,
      show 8 + (8 + (7 - j)) = 8 + (15 - j) by omega_arith]
    exact ⟨rfl, rfl⟩
  show WP isa (.seq (.block cryptHead) (.seq (.loop (.seq (.block rounds) (.ite .e (.block []) (.block layer))) .ne)
    (.block cryptTail))) s _
  refine WP.seq (WP.mono (cryptHead_wp hB hs hR hin hv htab) fun s₁ ⟨a₁, m₁, c₁, x₁⟩ => ?_)
  have hI : Inv s B g E (D₁ ^^^ E 0, D₂ ^^^ E 1) g s₁ := by
    refine ⟨by omega_arith, Nat.le_refl _, by rw [Nat.sub_self]; exact a₁, m₁, by rw [c₁, hg], ?_⟩
    rw [Nat.sub_self]
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · show fd (s₁.xmm .xmm0) (slot j) = dq (D₁ ^^^ E 0) j ^^^ dq (E 2) j ^^^ c5
      rw [(x₁ _ (slot_lt j)).1, slot_slot hj, (bswq_slot hj).1, (hk.kin0 j hj).1, (hb j hj).1, dq_xor, dq_xor]
      simp only [dq, BitVec.xor_assoc]
    · show fd (s₁.xmm .xmm1) (slot j) = dq (D₂ ^^^ E 1) j ^^^ dq (E 3) j ^^^ c5 ^^^ gc j
      rw [(x₁ _ (slot_lt j)).2, slot_slot hj, (bswq_slot hj).2, (hk.kin0 j hj).2, (hb j hj).2, dq_xor, dq_xor]
      simp only [dq, BitVec.xor_assoc]
  refine WP.seq (WP.mono (loop_wp hs hk (by omega_arith) hI) fun s₂ ⟨a₂, m₂, x₂, y₂⟩ => ?_)
  refine WP.mono (cryptTail_wp hs hk (by omega_arith) (by omega_arith) a₂ m₂ x₂ y₂)
    fun s₃ ⟨b₃, e₃, r₃, w₃, y₃, f₃, v₃⟩ => ⟨b₃, e₃, r₃, w₃, y₃, f₃, ?_⟩
  rw [Proof.Camellia.cipher_bytes hR, hg, ← hE, ← hblk]
  refine List.ext_getElem (by simp [Spec.Aes.bytesAt]) fun q h₁ _ => ?_
  have hq : q < 16 := by simpa [Spec.Aes.bytesAt] using h₁
  subst hD₁ hD₂
  rw [Vector.getElem_toList]
  simp only [Proof.Camellia.cryptWords]
  rw [Proof.Camellia.encodeBlock_getElem _ _ hq, ← v₃ q hq]
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range]

end

/-! ## The keys `prepare` leaves -/

section


open VG VG.X86 VG.X86.ByteMap VG.Impl.Camellia.X86.AesNi
open VG.Impl.Modes.X86 (at_ argOp)
open VG.Proof.Modes.X86 (ScrIn)

/-- The schedule's bytes in `m` are those of `M`. -/
def Sch (M m : Mem) (p : BitVec 32) : Prop :=
  ∀ o < 272, m (p.setWidth 64 + BitVec.ofNat 64 o) = M (p.setWidth 64 + BitVec.ofNat 64 o)

/-- Subkey `k` of the schedule at `p`, as stored. -/
def Ew (M : Mem) (p : BitVec 32) (k : Nat) : BitVec 64 :=
  Spec.Camellia.wordAt M (p.setWidth 64 + BitVec.ofNat 64 (8 * k))

theorem sch_bz {M m : Mem} {p : BitVec 32} (h : Sch M m p) {k j : Nat} (hk : k < 34) (hj : j < 8) :
    m (p.setWidth 64 + BitVec.ofNat 64 (8 * k + (7 - j))) = bz (Ew M p k) j := by
  rw [h _ (by omega_arith), bz_byteOf _ hj, Ew, Proof.Camellia.byteOf_wordAt _ _ (by omega_arith),
    Offset.add_ofNat_add_ofNat]

/-- What `prepare` needs of the state it starts in: the scratch buffer, and
the schedule, apart from it. -/
structure PEnv (s₀ : State) (B p : BitVec 32) : Prop where
  scr : ScrIn s₀ B 136
  sch : (⟨p.setWidth 64, 272⟩ : Region) ∈ s₀.rd ++ s₀.wr
  pfit : p.toNat + 272 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨p.setWidth 64, 272⟩ ⟨B.setWidth 64, 544⟩

/-- A state of `prepare` at group `i`: the schedule's pointer at the group's
subkeys, the keys' pointer at the group's keys, the table's address, and
the mask. -/
structure PAt (s₀ : State) (B p : BitVec 32) (i : Nat) (s : State) : Prop where
  base : s.gpr Impl.Modes.X86.sb = B
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  tb : s.gpr tbr = s₀.syms tableName
  sp : s.gpr .eax = p + BitVec.ofNat 32 (64 * i)
  kp : s.gpr kr = B + BitVec.ofNat 32 (24 + 112 * i)
  msk : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8

section
variable {s₀ s : State} {B p : BitVec 32} {i : Nat}

theorem PAt.kr64 (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 4) :
    (s.gpr Impl.Camellia.X86.AesNi.kr).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 (24 + 112 * i) := by
  have hf := he.scr.fit
  rw [h.kp]
  exact addr_eq (by omega_arith)

theorem PAt.krNat (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 4) :
    (s.gpr Impl.Camellia.X86.AesNi.kr).toNat = B.toNat + (24 + 112 * i) := by
  have hf := he.scr.fit
  rw [h.kp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 24 + 112 * i) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

theorem PAt.ax64 (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 4) :
    (s.gpr .eax).setWidth 64 = p.setWidth 64 + BitVec.ofNat 64 (64 * i) := by
  have hf := he.pfit
  rw [h.sp]
  exact addr_eq (by omega_arith)

theorem PAt.axNat (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 4) :
    (s.gpr .eax).toNat = p.toNat + 64 * i := by
  have hf := he.pfit
  rw [h.sp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 64 * i) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

/-- The state as the expressions of `prepare`'s blocks start from it. -/
theorem PAt.rel (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 4) :
    Rel pparams (envOf pparams s) regs₀ s := by
  have hf := he.pfit
  have hn := h.axNat he hi
  refine (rel_init (p := pparams) (by show s.gpr tbr = s.syms tableName; rw [h.tb, h.syms]) (by show (s.gpr .eax).toNat + 80 ≤ _; omega_arith)
    fun o ho => ⟨_, by rw [h.rd, h.wr]; exact he.sch, ?_⟩).const m0 h.msk
  show Region.Contains _ (addr (s.gpr .eax) o) 16
  have ho' : o + 16 ≤ 80 := ho
  rw [addr_eq (by omega_arith), h.ax64 he hi, Offset.add_ofNat_add_ofNat]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- The keys of the group are writable, apart from the schedule. -/
theorem PAt.ok (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 4) : OutOk pparams oparams s := by
  have hf := he.scr.fit
  have hp := he.pfit
  have hn := h.krNat he hi
  have ha := h.axNat he hi
  refine ⟨by show (s.gpr kr).toNat + 128 ≤ _; omega_arith, fun o ho => ⟨_, by rw [h.wr]; exact he.scr.wr, ?_⟩, ?_,
    by show (s.gpr .eax).toNat + 80 ≤ _; omega_arith⟩
  · show Region.Contains _ (addr (s.gpr kr) o) 16
    have ho' : o + 16 ≤ 128 := ho
    rw [addr_eq (by omega_arith), h.kr64 he hi, Offset.add_ofNat_add_ofNat]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  · show Region.Disjoint ⟨(s.gpr .eax).setWidth 64, 80⟩ ⟨(s.gpr kr).setWidth 64, 128⟩
    rw [h.ax64 he hi, h.kr64 he hi]
    exact (he.sep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))

/-- The bytes of the two subkeys at byte `off` of the schedule from `eax`,
in the rounds' form. -/
theorem pT_eval (off : Nat) {q : Nat} (hq : q < 16) (ho : off ≤ 64) :
    (pT off q).eval (envOf pparams s) =
      qT (isA (slot (q % 8))) (s.mem ((s.gpr .eax).setWidth 64 + BitVec.ofNat 64 (off + bswq q))) := by
  have hb := bswq_lt hq
  simp only [pT, BV.eval, mask_zero, BitVec.zero_xor, BitVec.xor_zero, cterms_eval _ (.inl rfl) hq,
    mask_bit _ (show 128 + (off + bswq q) < nvars by show _ < 1024; omega_arith), envOf_key]
  rfl

/-- … as subkey `k` of the schedule, which starts at byte `off` from `eax`,
or 8 bytes after. -/
theorem pT_lo {M : Mem} (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 4) (hS : Sch M s.mem p) {off k : Nat}
    (hk : 8 * k = 64 * i + off) (ho : off ≤ 64) {j : Nat} (hj : j < 8) :
    (pT off (slot j)).eval (envOf pparams s) = dq (Ew M p k) j := by
  have sj := slot_lt j
  rw [pT_eval off (by omega_arith) ho, (bswq_slot hj).1, show slot j % 8 = slot j by omega_arith, slot_slot hj,
    h.ax64 he hi, Offset.add_ofNat_add_ofNat, show 64 * i + (off + (7 - j)) = 8 * k + (7 - j) by omega_arith,
    sch_bz hS (by omega_arith) hj]
  rfl

theorem pT_hi {M : Mem} (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 4) (hS : Sch M s.mem p) {off k : Nat}
    (hk : 8 * k = 64 * i + off + 8) (ho : off ≤ 64) {j : Nat} (hj : j < 8) :
    (pT off (slot j + 8)).eval (envOf pparams s) = dq (Ew M p k) j := by
  have sj := slot_lt j
  rw [pT_eval off (by omega_arith) ho, (bswq_slot hj).2, show (slot j + 8) % 8 = slot j by omega_arith, slot_slot hj,
    h.ax64 he hi, Offset.add_ofNat_add_ofNat, show 64 * i + (off + (15 - j)) = 8 * k + (7 - j) by omega_arith,
    sch_bz hS (by omega_arith) hj]
  rfl

/-- A register's bytes, as the kernel compared them. -/
theorem rel_bytes {q : Params} {env : Nat → BitVec 8} {ρ : Regs} {s' : State} (hr : Rel q env ρ s') {r : XReg}
    (hsh : (ρ.get r).sh = false) {ref : Nat → BV}
    (hc : ((List.range 16).all fun k => (get (ρ.get r).bs k).same (ref k)) = true) {k : Nat} (hk : k < 16) :
    byte (s'.xmm r) k = (ref k).eval env := by
  rw [hr.bytes hsh k hk, BV.same_eval _ (List.all_eq_true.mp hc k (List.mem_range.mpr hk))]

theorem rel_mask {q : Params} {env : Nat → BitVec 8} {ρ : Regs} {s' : State} (hr : Rel q env ρ s')
    (h : maskOk ρ = true) : ∀ k < 16, byte (s'.xmm m0) k = 0x0f#8 := fun k hk => by
  simp only [maskOk, Bool.and_eq_true, Bool.not_eq_true'] at h
  rw [rel_bytes hr h.1 h.2 hk, BV.cst_eval]

/-- A state after stores of one of `prepare`'s blocks. -/
theorem PAt.relS {s' : State} {env : Nat → BitVec 8} {σ : Regs × Outs} (h : PAt s₀ B p i s)
    (hr : RelS pparams oparams env σ s s') (hm : ∀ k < 16, byte (s'.xmm m0) k = 0x0f#8) : PAt s₀ B p i s' :=
  ⟨by rw [hr.gpr]; exact h.base, by rw [hr.gpr]; exact h.esp, hr.rd.trans h.rd, hr.wr.trans h.wr,
    hr.syms.trans h.syms, by rw [hr.gpr]; exact h.tb, by rw [hr.gpr]; exact h.sp, by rw [hr.gpr]; exact h.kp, hm⟩

/-- A byte a block stored at offset `o` of the group's keys. -/
theorem out_eval {s' : State} {env : Nat → BitVec 8} {σ : Regs × Outs} (h : PAt s₀ B p i s) (he : PEnv s₀ B p)
    (hi : i < 4) (hr : RelS pparams oparams env σ s s') {o : Nat} {f : Nat → BV} (hok : outOk σ.2 o f = true)
    {k : Nat} (hk : k < 16) : kAt s'.mem B (112 * i + (o + k)) = (f k).eval env := by
  rw [← hr.out hok hk]
  show s'.mem _ = s'.mem ((s.gpr kr).setWidth 64 + _)
  rw [h.kr64 he hi, Offset.add_ofNat_add_ofNat, Nat.add_assoc]

/-- The bytes outside those a block stored. -/
theorem out_frame {s' : State} {env : Nat → BitVec 8} {σ : Regs × Outs} (h : PAt s₀ B p i s) (he : PEnv s₀ B p)
    (hi : i < 4) (hr : RelS pparams oparams env σ s s') {lo hi' : Nat} (hin : outsIn σ.2 lo hi' = true) :
    Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (24 + 112 * i + lo), hi' - lo⟩] s.mem s'.mem := by
  have := hr.frameIn hin
  rw [show (s.gpr oparams.oreg) = s.gpr kr from rfl, h.kr64 he hi, Offset.add_ofNat_add_ofNat] at this
  exact this

theorem pconst {j : Nat} (hj : j < 8) :
    byte (tblAt oCK) (slot j) = c5 ∧ byte (tblAt oCK) (slot j + 8) = c5 ^^^ gc j ∧
    byte (tblAt oGG) (slot j) = gc j ∧ byte (tblAt oGG) (slot j + 8) = gc j ∧
    byte (tblAt oCW2) (slot j) = gc j ^^^ c5 ∧ byte (tblAt oCW2) (slot j + 8) = c5 := by
  have h := List.all_eq_true.mp pconst_all j (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ := h
  exact ⟨a, b, c, d, e, f⟩

/-- A group's keys from its six subkeys (`prepGroupX`): the first two
subkeys in the rounds' form, with what `xmm6` held, and the rounds' keys. -/
theorem prepGroupX_wp {M : Mem} (he : PEnv s₀ B p) (hi : i < 4) (h : PAt s₀ B p i s) (hS : Sch M s.mem p) :
    WP isa (.block prepGroupX) s fun s' => PAt s₀ B p i s' ∧ s'.gpr .ecx = s.gpr .ecx ∧
      (∀ q < 16, byte (s'.xmm .xmm6) q = 0#8) ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (24 + 112 * i), 64⟩] s.mem s'.mem ∧
      (∀ j < 8, kAt s'.mem B (112 * i + slot j) =
          byte (s.xmm .xmm6) (slot j) ^^^ dq (Ew M p (2 + 8 * i)) j ^^^ c5 ∧
        kAt s'.mem B (112 * i + (slot j + 8)) =
          byte (s.xmm .xmm6) (slot j + 8) ^^^ dq (Ew M p (2 + 8 * i + 1)) j ^^^ c5 ^^^ gc j) ∧
      (∀ r < 4, ∀ j < 8, kAt s'.mem B (112 * i + (16 + 8 * r + slot j)) =
        dq (Ew M p (2 + 8 * i + r) ^^^ Ew M p (2 + 8 * i + (r + 2))) j ^^^ gc j) ∧
      (∀ j < 8, kAt s'.mem B (112 * i + (48 + slot j)) = dq (Ew M p (2 + 8 * i + 4)) j ^^^ gc j ^^^ c5) ∧
      (∀ j < 8, kAt s'.mem B (112 * i + (56 + slot j)) = dq (Ew M p (2 + 8 * i + 5)) j ^^^ c5) := by
  have hok := prep_all.2.1
  unfold prepGroupOk at hok
  split at hok <;> [cases hok; rename_i σ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨o0, o16⟩, o32⟩, o48⟩, oin⟩, x6s⟩, x6⟩, mk⟩ := hok
  refine runS_wp (h.ok he hi) (RelS.init (h.rel he hi) rfl) hrun fun s' hr => ?_
  have lo := fun {off k : Nat} (hk : 8 * k = 64 * i + off) (ho : off ≤ 64) {j : Nat} (hj : j < 8) =>
    pT_lo h he hi hS hk ho hj
  have hi' := fun {off k : Nat} (hk : 8 * k = 64 * i + off + 8) (ho : off ≤ 64) {j : Nat} (hj : j < 8) =>
    pT_hi h he hi hS hk ho hj
  have v6 : ∀ q < 16, (BV.var (16 * 6 + q)).eval (envOf pparams s) = byte (s.xmm .xmm6) q := fun q hq => by
    rw [BV.var_eval _ (show 16 * 6 + q < nvars by show _ < 1024; omega_arith)]
    exact envOf_reg pparams s .xmm6 hq
  refine ⟨h.relS hr (rel_mask hr.rel mk), by rw [hr.gpr], fun q hq => ?_, ?_, fun j hj => ⟨?_, ?_⟩,
    fun r hr4 j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [rel_bytes hr.rel x6s x6 hq, BV.zero_eval]
  · have := out_frame h he hi hr oin
    rwa [Nat.add_zero, Nat.sub_zero] at this
  · have sj := slot_lt j
    obtain ⟨c, -⟩ := pconst hj
    rw [show 112 * i + slot j = 112 * i + (0 + slot j) by omega_arith, out_eval h he hi hr o0 (by omega_arith),
      BV.xor_eval, BV.xor_eval, v6 _ (by omega_arith), cb, BV.cst_eval, c,
      lo (k := 2 + 8 * i) (off := 16) (by omega_arith) (by decide) hj]
    ac_rfl
  · have sj := slot_lt j
    obtain ⟨-, c, -⟩ := pconst hj
    rw [show 112 * i + (slot j + 8) = 112 * i + (0 + (slot j + 8)) by omega_arith,
      out_eval h he hi hr o0 (by omega_arith), BV.xor_eval, BV.xor_eval, v6 _ (by omega_arith), cb, BV.cst_eval, c,
      hi' (k := 2 + 8 * i + 1) (off := 16) (by omega_arith) (by decide) hj]
    ac_rfl
  · have sj := slot_lt j
    obtain ⟨-, -, g₀, g₁, -⟩ := pconst hj
    have hr' : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega_arith
    rcases hr' with rfl | rfl | rfl | rfl
    · rw [show 16 + 8 * 0 + slot j = 16 + slot j by omega_arith, out_eval h he hi hr o16 (by omega_arith),
        BV.xor_eval, BV.xor_eval, cb, BV.cst_eval, g₀, dq_xor,
        lo (k := 2 + 8 * i + 0) (off := 16) (by omega_arith) (by decide) hj,
        lo (k := 2 + 8 * i + (0 + 2)) (off := 32) (by omega_arith) (by decide) hj]
    · rw [show 16 + 8 * 1 + slot j = 16 + (slot j + 8) by omega_arith, out_eval h he hi hr o16 (by omega_arith),
        BV.xor_eval, BV.xor_eval, cb, BV.cst_eval, g₁, dq_xor,
        hi' (k := 2 + 8 * i + 1) (off := 16) (by omega_arith) (by decide) hj,
        hi' (k := 2 + 8 * i + (1 + 2)) (off := 32) (by omega_arith) (by decide) hj]
    · rw [show 16 + 8 * 2 + slot j = 32 + slot j by omega_arith, out_eval h he hi hr o32 (by omega_arith),
        BV.xor_eval, BV.xor_eval, cb, BV.cst_eval, g₀, dq_xor,
        lo (k := 2 + 8 * i + 2) (off := 32) (by omega_arith) (by decide) hj,
        lo (k := 2 + 8 * i + (2 + 2)) (off := 48) (by omega_arith) (by decide) hj]
    · rw [show 16 + 8 * 3 + slot j = 32 + (slot j + 8) by omega_arith, out_eval h he hi hr o32 (by omega_arith),
        BV.xor_eval, BV.xor_eval, cb, BV.cst_eval, g₁, dq_xor,
        hi' (k := 2 + 8 * i + 3) (off := 32) (by omega_arith) (by decide) hj,
        hi' (k := 2 + 8 * i + (3 + 2)) (off := 48) (by omega_arith) (by decide) hj]
  · have sj := slot_lt j
    obtain ⟨-, -, -, -, c, -⟩ := pconst hj
    rw [out_eval h he hi hr o48 (by omega_arith), BV.xor_eval, cb, BV.cst_eval, c,
      lo (k := 2 + 8 * i + 4) (off := 48) (by omega_arith) (by decide) hj, BitVec.xor_assoc]
  · have sj := slot_lt j
    obtain ⟨-, -, -, -, -, c⟩ := pconst hj
    rw [show 56 + slot j = 48 + (slot j + 8) by omega_arith, out_eval h he hi hr o48 (by omega_arith), BV.xor_eval, cb,
      BV.cst_eval, c, hi' (k := 2 + 8 * i + 5) (off := 48) (by omega_arith) (by decide) hj]

theorem pmask :
    dword (tblAt oN1) 0 = 0#32 ∧ dword (tblAt oN1) 1 = 0#32 ∧ dword (tblAt oN1) 2 = 0#32 ∧
    dword (tblAt oN1) 3 = BitVec.allOnes 32 ∧
    dword (tblAt oM1) 0 = BitVec.allOnes 32 ∧ dword (tblAt oM1) 1 = 0#32 ∧ dword (tblAt oM1) 2 = 0#32 ∧
    dword (tblAt oM1) 3 = BitVec.allOnes 32 ∧
    dword (tblAt oN2) 0 = 0#32 ∧ dword (tblAt oN2) 1 = BitVec.allOnes 32 ∧ dword (tblAt oN2) 2 = 0#32 ∧
    dword (tblAt oN2) 3 = 0#32 ∧
    dword (tblAt oM2) 0 = 0#32 ∧ dword (tblAt oM2) 1 = BitVec.allOnes 32 ∧
    dword (tblAt oM2) 2 = BitVec.allOnes 32 ∧ dword (tblAt oM2) 3 = 0#32 := by
  have h := pmask_all
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, h⟩, i⟩, j⟩, k⟩, l⟩, m⟩, n⟩, o⟩, q⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, q⟩

/-- The first two masks of the FL layer, from the halves in a register. -/
theorem mask_words (L R : BitVec 64) :
    XBinOp.eval .pand (XBinOp.eval .pxor (hl L R) (tblAt oN1)) (tblAt oM1) =
        ofDwords ((L >>> 32).setWidth 32) 0#32 0#32 (~~~ R.setWidth 32) ∧
      XBinOp.eval .pand (XBinOp.eval .pxor (hl L R) (tblAt oN2)) (tblAt oM2) =
        ofDwords 0#32 (~~~ L.setWidth 32) ((R >>> 32).setWidth 32) 0#32 := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, q⟩ := pmask
  constructor
  · rw [← ofDwords_dword (XBinOp.eval .pand _ _)]
    simp only [Lanes.dword_pand, dword_pxor, hl, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
      dword_ofDwords_3, a, b, c, d, e, f, g, h, BitVec.xor_zero, BitVec.and_zero, BitVec.and_allOnes,
      BitVec.xor_allOnes]
  · rw [← ofDwords_dword (XBinOp.eval .pand _ _)]
    simp only [Lanes.dword_pand, dword_pxor, hl, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
      dword_ofDwords_3, i, j, k, l, m, n, o, q, BitVec.xor_zero, BitVec.and_zero, BitVec.and_allOnes,
      BitVec.xor_allOnes]

/-- The third: the low halves of the two subkeys. -/
theorem shift_words (L R : BitVec 64) :
    XShiftOp.eval .psrlq (hl L R) 32 = ofDwords (L.setWidth 32) 0#32 (R.setWidth 32) 0#32 := by
  rw [← ofDwords_dword (XShiftOp.eval .psrlq _ _)]
  simp only [dword_psrlq32 _ (show 0 < 4 by decide), dword_psrlq32 _ (show 1 < 4 by decide),
    dword_psrlq32 _ (show 2 < 4 by decide), dword_psrlq32 _ (show 3 < 4 by decide), hl, dword_ofDwords_1,
    dword_ofDwords_3, Nat.reduceMod, Nat.reduceAdd, ↓reduceIte, Nat.reduceEqDiff]

/-- The 16 bytes at byte `o` of the keys, as a register's bytes. -/
theorem wAt_bytes (m : Mem) (B : BitVec 32) (o : Nat) {x : BitVec 128}
    (h : ∀ q < 16, kAt m B (o + q) = byte x q) : wAt m B o = x :=
  ext16 fun q hq => by
    rw [← h q hq]
    show (m.readW _ 128).extractLsb' (8 * q) 8 = _
    rw [byte_readW _ _ (by omega_arith), Offset.add_ofNat_add_ofNat, Nat.add_assoc]
    rfl

/-- The masks of the FL layer after a group, from its two subkeys
(`prepMasksX`). -/
theorem prepMasksX_wp {M : Mem} (he : PEnv s₀ B p) (hi : i < 4) (h : PAt s₀ B p i s) (hS : Sch M s.mem p) :
    WP isa (.block prepMasksX) s fun s' => PAt s₀ B p i s' ∧ s'.gpr .ecx = s.gpr .ecx ∧
      (∀ q < 16, byte (s'.xmm .xmm6) q = byte (s.xmm .xmm6) q) ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (24 + 112 * i + 64), 48⟩] s.mem s'.mem ∧
      LayerWords (fun o => wAt s'.mem B (112 * i + o)) (Ew M p (8 + 8 * i)) (Ew M p (9 + 8 * i)) := by
  have hok := prep_all.2.2.1
  unfold prepMasksOk at hok
  split at hok <;> [cases hok; rename_i σ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨o64, o80⟩, o96⟩, oin⟩, x6s⟩, x6⟩, mk⟩ := hok
  refine runS_wp (h.ok he hi) (RelS.init (h.rel he hi) rfl) hrun fun s' hr => ?_
  -- The two subkeys, shuffled: the halves in a register.
  have hX : ∀ q < 16, s.mem ((s.gpr .eax).setWidth 64 + BitVec.ofNat 64 (64 + bswq q)) =
      byte (hl (Ew M p (8 + 8 * i)) (Ew M p (9 + 8 * i))) q := fun q hq => by
    rw [h.ax64 he hi, Offset.add_ofNat_add_ofNat]
    by_cases h8 : q < 8
    · have sq := slot_lt q
      have e := (byte_hl (Ew M p (8 + 8 * i)) (Ew M p (9 + 8 * i)) sq).1
      rw [slot_slot h8] at e
      have b := (bswq_slot sq).1
      rw [slot_slot h8] at b
      rw [e, b, show 64 * i + (64 + (7 - slot q)) = 8 * (8 + 8 * i) + (7 - slot q) by omega_arith,
        sch_bz hS (by omega_arith) sq]
    · have sq := slot_lt (q - 8)
      have e := (byte_hl (Ew M p (8 + 8 * i)) (Ew M p (9 + 8 * i)) sq).2
      rw [slot_slot (by omega_arith), show q - 8 + 8 = q by omega_arith] at e
      have b := (bswq_slot sq).2
      rw [slot_slot (by omega_arith), show q - 8 + 8 = q by omega_arith] at b
      rw [e, b, show 64 * i + (64 + (15 - slot (q - 8))) = 8 * (9 + 8 * i) + (7 - slot (q - 8)) by omega_arith,
        sch_bz hS (by omega_arith) sq]
  have hM : ∀ n m q, q < 16 → (pM n m q).eval (envOf pparams s) =
      byte (XBinOp.eval .pand (XBinOp.eval .pxor (hl (Ew M p (8 + 8 * i)) (Ew M p (9 + 8 * i))) (tblAt n))
        (tblAt m)) q := fun n m q hq => by
    have hb := bswq_lt hq
    simp only [pM, BV.eval, mask_zero, sum, Term.eval, chain, eval_and, BitVec.zero_xor, BitVec.xor_zero,
      mask_bit _ (show 128 + (64 + bswq q) < nvars by show _ < 1024; omega_arith), envOf_key]
    rw [show s.gpr pparams.kreg = s.gpr .eax from rfl, hX q hq]
    show _ = byte ((_ ^^^ tblAt n) &&& tblAt m) q
    rw [byte_and, byte_xor]
    exact (Fn.lin_xor (g := .and (byte (tblAt m) q)) rfl _ _).symm
  obtain ⟨w₁, w₂⟩ := mask_words (Ew M p (8 + 8 * i)) (Ew M p (9 + 8 * i))
  refine ⟨h.relS hr (rel_mask hr.rel mk), by rw [hr.gpr], fun q hq => ?_, ?_, ?_, ?_, ?_⟩
  · rw [rel_bytes hr.rel x6s x6 hq, BV.var_eval _ (show 16 * 6 + q < nvars by show _ < 1024; omega_arith)]
    exact envOf_reg pparams s .xmm6 hq
  · exact out_frame h he hi hr oin
  · show wAt s'.mem B (112 * i + 64) = _
    rw [← w₁]
    exact wAt_bytes _ _ _ fun q hq => by rw [Nat.add_assoc, out_eval h he hi hr o64 hq, hM _ _ q hq]
  · show wAt s'.mem B (112 * i + 80) = _
    rw [← w₂]
    exact wAt_bytes _ _ _ fun q hq => by rw [Nat.add_assoc, out_eval h he hi hr o80 hq, hM _ _ q hq]
  · show wAt s'.mem B (112 * i + 96) = _
    rw [← shift_words]
    refine wAt_bytes _ _ _ fun q hq => ?_
    rw [Nat.add_assoc, out_eval h he hi hr o96 hq, byte_psrlq32 _ hq]
    by_cases h4 : q % 8 < 4
    · rw [ite_eq_left h4, ite_eq_left h4,
        BV.var_eval _ (show 128 + (64 + bswq (q + 4)) < nvars by
          have := bswq_lt (show q + 4 < 16 by omega_arith); show _ < 1024; omega_arith),
        envOf_key, show s.gpr pparams.kreg = s.gpr .eax from rfl, hX _ (by omega_arith)]
    · rw [ite_eq_right h4, ite_eq_right h4, BV.zero_eval]

/-- The last two subkeys, as stored (`prepTail`). -/
theorem prepTail_wp {M : Mem} (he : PEnv s₀ B p) (hi : i < 4) (h : PAt s₀ B p i s) (hS : Sch M s.mem p) {k : Nat}
    (hk : k = 8 + 8 * i) :
    WP isa (.block prepTail) s fun s' => PAt s₀ B p i s' ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (24 + 112 * i + 64), 16⟩] s.mem s'.mem ∧
      ∀ j < 8, kAt s'.mem B (112 * i + (64 + (7 - j))) = bz (Ew M p k) j ∧
        kAt s'.mem B (112 * i + (72 + (7 - j))) = bz (Ew M p (k + 1)) j := by
  have hok := prep_all.2.2.2
  unfold prepTailOk at hok
  split at hok <;> [cases hok; rename_i σ hrun]
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨o64, oin⟩, mk⟩ := hok
  refine runS_wp (h.ok he hi) (RelS.init (h.rel he hi) rfl) hrun fun s' hr => ?_
  have hv : ∀ q < 16, kAt s'.mem B (112 * i + (64 + q)) = s.mem (p.setWidth 64 + BitVec.ofNat 64 (64 * i + (64 + q))) :=
    fun q hq => by
      rw [out_eval h he hi hr o64 hq, BV.var_eval _ (show 128 + (64 + q) < nvars by show _ < 1024; omega_arith),
        envOf_key, show s.gpr pparams.kreg = s.gpr .eax from rfl, h.ax64 he hi, Offset.add_ofNat_add_ofNat]
  refine ⟨h.relS hr (rel_mask hr.rel mk), out_frame h he hi hr oin, fun j hj => ⟨?_, ?_⟩⟩
  · rw [hv _ (by omega_arith), show 64 * i + (64 + (7 - j)) = 8 * k + (7 - j) by omega_arith,
      sch_bz hS (by omega_arith) hj]
  · rw [show 72 + (7 - j) = 64 + (15 - j) by omega_arith, hv _ (by omega_arith),
      show 64 * i + (64 + (15 - j)) = 8 * (k + 1) + (7 - j) by omega_arith, sch_bz hS (by omega_arith) hj]

end

/-! ### The keys of the groups so far -/

/-- A byte of the keys outside what was written. -/
theorem kAt_frame {m m' : Mem} {B : BitVec 32} {a n o : Nat}
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (24 + a), n⟩] m m') (ho : o < a ∨ a + n ≤ o) (ha : a + n ≤ 520)
    (hb : o ≤ 520) : kAt m' B o = kAt m B o := by
  refine hf _ fun r hr hc => ?_
  rw [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint (B.setWidth 64) (d := 24 + o) (n := 1) (e := 24 + a) (k := n) (by omega_arith) (by omega_arith)
    (by omega_arith) _ (Region.contains_self _ 1) hc

/-- 16 bytes of the keys outside what was written. -/
theorem wAt_frame {m m' : Mem} {B : BitVec 32} {a n o : Nat}
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (24 + a), n⟩] m m') (ho : o + 16 ≤ a ∨ a + n ≤ o) (ha : a + n ≤ 520)
    (hb : o ≤ 520) : wAt m' B o = wAt m B o := by
  refine hf.readW (r := ⟨B.setWidth 64 + BitVec.ofNat 64 (24 + o), 16⟩) (Region.contains_self _ 16) (fun r hr => ?_)
    (by decide)
  rw [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint (B.setWidth 64) (by omega_arith) (by omega_arith) (by omega_arith)

/-- The keys of the groups before `i`, of `g` (`Keys`, without the last two
subkeys). -/
structure KeysTo (m : Mem) (B : BitVec 32) (g : Nat) (E : Nat → BitVec 64) (i : Nat) : Prop where
  kin0 : 0 < i → ∀ j < 8, kAt m B (slot j) = dq (E 0 ^^^ E 2) j ^^^ c5 ∧
    kAt m B (slot j + 8) = dq (E 1 ^^^ E 3) j ^^^ c5 ^^^ gc j
  kin : ∀ i', i' + 1 < i → ∀ j < 8,
    kAt m B (112 * i' + (112 + slot j)) = dq (E (2 + 8 * (i' + 1))) j ^^^ c5 ∧
      kAt m B (112 * i' + (120 + slot j)) = dq (E (2 + 8 * (i' + 1) + 1)) j ^^^ c5 ^^^ gc j
  rk : ∀ i' < i, ∀ r < 4, ∀ j < 8, kAt m B (112 * i' + (16 + 8 * r + slot j)) =
    dq (E (2 + 8 * i' + r) ^^^ E (2 + 8 * i' + (r + 2))) j ^^^ gc j
  rk4 : ∀ i' < i, ∀ j < 8, kAt m B (112 * i' + (48 + slot j)) = dq (E (2 + 8 * i' + 4)) j ^^^ gc j ^^^ c5
  rk5 : ∀ i' < i, ∀ j < 8, kAt m B (112 * i' + (56 + slot j)) = dq (E (2 + 8 * i' + 5)) j ^^^ c5
  fl : ∀ i', i' + 1 < g → i' < i →
    LayerWords (fun o => wAt m B (112 * i' + o)) (E (8 + 8 * i')) (E (9 + 8 * i'))

theorem KeysTo.zero (m : Mem) (B : BitVec 32) (g : Nat) (E : Nat → BitVec 64) : KeysTo m B g E 0 :=
  ⟨fun h => absurd h (Nat.lt_irrefl 0), fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ _ h => absurd h (Nat.not_lt_zero _)⟩

/-- The keys of the groups before `i` are outside what is written after
them. -/
theorem KeysTo.frame {m m' : Mem} {B : BitVec 32} {g i a n : Nat} {E : Nat → BitVec 64} (h : KeysTo m B g E i)
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (24 + a), n⟩] m m') (hi : i ≤ 4)
    (hlo : ∀ i' < i, 112 * i' + 64 ≤ a) (hfl : ∀ i', i' + 1 < g → i' < i → 112 * i' + 112 ≤ a)
    (han : a + n ≤ 520) : KeysTo m' B g E i := by
  have sl := slot_lt
  refine ⟨fun h0 j hj => ?_, fun i' hi' j hj => ?_, fun i' hi' r hr j hj => ?_, fun i' hi' j hj => ?_,
    fun i' hi' j hj => ?_, fun i' hg hi' => ⟨?_, ?_, ?_⟩⟩
  · have := sl j
    have := hlo 0 h0
    rw [kAt_frame hf (by omega_arith) han (by omega_arith), kAt_frame hf (by omega_arith) han (by omega_arith)]
    exact h.kin0 h0 j hj
  · have := sl j
    have := hlo (i' + 1) hi'
    rw [kAt_frame hf (by omega_arith) han (by omega_arith), kAt_frame hf (by omega_arith) han (by omega_arith)]
    exact h.kin i' hi' j hj
  · have := sl j
    have := hlo i' hi'
    rw [kAt_frame hf (by omega_arith) han (by omega_arith)]
    exact h.rk i' hi' r hr j hj
  · have := sl j
    have := hlo i' hi'
    rw [kAt_frame hf (by omega_arith) han (by omega_arith)]
    exact h.rk4 i' hi' j hj
  · have := sl j
    have := hlo i' hi'
    rw [kAt_frame hf (by omega_arith) han (by omega_arith)]
    exact h.rk5 i' hi' j hj
  · have := hfl i' hg hi'
    show wAt m' B (112 * i' + 64) = _
    rw [wAt_frame hf (by omega_arith) han (by omega_arith)]
    exact (h.fl i' hg hi').e1
  · have := hfl i' hg hi'
    show wAt m' B (112 * i' + 80) = _
    rw [wAt_frame hf (by omega_arith) han (by omega_arith)]
    exact (h.fl i' hg hi').e2
  · have := hfl i' hg hi'
    show wAt m' B (112 * i' + 96) = _
    rw [wAt_frame hf (by omega_arith) han (by omega_arith)]
    exact (h.fl i' hg hi').c

/-- What `xmm6` holds at group `i`: the first two subkeys in the rounds'
form at the first, and zero after. -/
def X6 (x : BitVec 128) (E : Nat → BitVec 64) (i : Nat) : Prop :=
  if i = 0 then ∀ j < 8, byte x (slot j) = dq (E 0) j ∧ byte x (slot j + 8) = dq (E 1) j
  else ∀ q < 16, byte x q = 0#8

/-- The keys of one more group. -/
theorem KeysTo.step {m : Mem} {B : BitVec 32} {g i : Nat} {E : Nat → BitVec 64} {x : BitVec 128}
    (h : KeysTo m B g E i) (hx : X6 x E i)
    (hin : ∀ j < 8, kAt m B (112 * i + slot j) = byte x (slot j) ^^^ dq (E (2 + 8 * i)) j ^^^ c5 ∧
      kAt m B (112 * i + (slot j + 8)) = byte x (slot j + 8) ^^^ dq (E (2 + 8 * i + 1)) j ^^^ c5 ^^^ gc j)
    (hrk : ∀ r < 4, ∀ j < 8, kAt m B (112 * i + (16 + 8 * r + slot j)) =
      dq (E (2 + 8 * i + r) ^^^ E (2 + 8 * i + (r + 2))) j ^^^ gc j)
    (hrk4 : ∀ j < 8, kAt m B (112 * i + (48 + slot j)) = dq (E (2 + 8 * i + 4)) j ^^^ gc j ^^^ c5)
    (hrk5 : ∀ j < 8, kAt m B (112 * i + (56 + slot j)) = dq (E (2 + 8 * i + 5)) j ^^^ c5)
    (hfl : i + 1 < g → LayerWords (fun o => wAt m B (112 * i + o)) (E (8 + 8 * i)) (E (9 + 8 * i))) :
    KeysTo m B g E (i + 1) := by
  refine ⟨fun _ j hj => ?_, fun i' hi' j hj => ?_, fun i' hi' r hr j hj => ?_, fun i' hi' j hj => ?_,
    fun i' hi' j hj => ?_, fun i' hg hi' => ?_⟩
  · by_cases h0 : i = 0
    · subst h0
      rw [X6, ite_eq_left rfl] at hx
      have a := hin j hj
      rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add, (hx j hj).1, (hx j hj).2] at a
      rw [a.1, a.2, dq_xor, dq_xor]
      exact ⟨rfl, rfl⟩
    · exact h.kin0 (by omega_arith) j hj
  · by_cases hl : i' + 1 = i
    · subst hl
      rw [X6, ite_eq_right (Nat.succ_ne_zero _)] at hx
      have sj := slot_lt j
      have a := hin j hj
      rw [hx _ (by omega_arith), hx _ (by omega_arith), BitVec.zero_xor, BitVec.zero_xor] at a
      rw [show 112 * i' + (112 + slot j) = 112 * (i' + 1) + slot j by omega_arith,
        show 112 * i' + (120 + slot j) = 112 * (i' + 1) + (slot j + 8) by omega_arith]
      exact a
    · exact h.kin i' (by omega_arith) j hj
  · by_cases hl : i' = i
    · subst hl; exact hrk r hr j hj
    · exact h.rk i' (by omega_arith) r hr j hj
  · by_cases hl : i' = i
    · subst hl; exact hrk4 j hj
    · exact h.rk4 i' (by omega_arith) j hj
  · by_cases hl : i' = i
    · subst hl; exact hrk5 j hj
    · exact h.rk5 i' (by omega_arith) j hj
  · by_cases hl : i' = i
    · subst hl; exact hfl hg
    · exact h.fl i' hg (by omega_arith)

/-! ### The loop over the groups -/

section
variable {s₀ s : State} {B p : BitVec 32} {g i : Nat} {M : Mem}

/-- The schedule is outside what `prepare` writes of the keys. -/
theorem Sch.frame {m m' : Mem} {a n : Nat} (h : Sch M m p) (he : PEnv s₀ B p)
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 a, n⟩] m m') (han : a + n ≤ 544) : Sch M m' p := fun o ho => by
  rw [← h o ho]
  refine hf.bytes (R := ⟨p.setWidth 64, 272⟩) (fun r hr => ?_) (by show (272 : Nat) ≤ 2 ^ 64; decide) ho
  rw [List.mem_singleton] at hr; subst hr
  exact he.sep.sub_right (Offset.sub_base _ han)

/-- A general register written by an instruction that leaves the others,
memory and the XMM registers. -/
theorem PAt.upd {s' : State} {d : Reg} {v : BitVec 32} (h : PAt s₀ B p i s) (u : Wp.Upd s s' d v)
    (hx : s'.xmm = s.xmm)
    (hd : d ≠ Impl.Modes.X86.sb ∧ d ≠ .esp ∧ d ≠ tbr ∧ d ≠ .eax ∧ d ≠ Impl.Camellia.X86.AesNi.kr) :
    PAt s₀ B p i s' :=
  ⟨by rw [u.other _ (Ne.symm hd.1)]; exact h.base, by rw [u.other _ (Ne.symm hd.2.1)]; exact h.esp,
    u.rd.trans h.rd, u.wr.trans h.wr, u.syms.trans h.syms, by rw [u.other _ (Ne.symm hd.2.2.1)]; exact h.tb,
    by rw [u.other _ (Ne.symm hd.2.2.2.1)]; exact h.sp, by rw [u.other _ (Ne.symm hd.2.2.2.2)]; exact h.kp,
    by rw [hx]; exact h.msk⟩

/-- The loop's invariant, with `n` groups left, from the memory `m₁`. -/
def PInv (s₀ : State) (M m₁ : Mem) (B p : BitVec 32) (g n : Nat) (s : State) : Prop :=
  1 ≤ n ∧ n ≤ g ∧ PAt s₀ B p (g - n) s ∧ s.gpr .ecx = BitVec.ofNat 32 n ∧ Sch M s.mem p ∧
    Frame [⟨B.setWidth 64 + BitVec.ofNat 64 24, 480⟩] m₁ s.mem ∧ KeysTo s.mem B g (Ew M p) (g - n) ∧
    X6 (s.xmm .xmm6) (Ew M p) (g - n)

/-- The groups' keys. -/
theorem ploop_wp {m₁ : Mem} (he : PEnv s₀ B p) (hg : g ≤ 4) {n : Nat} (hI : PInv s₀ M m₁ B p g n s) :
    WP isa (.loop (.seq (.block prepGroup) (.ite .e (.block []) (.block prepMasks))) .ne) s fun s' =>
      PAt s₀ B p (g - 1) s' ∧ Sch M s'.mem p ∧ Frame [⟨B.setWidth 64 + BitVec.ofNat 64 24, 480⟩] m₁ s'.mem ∧
      KeysTo s'.mem B g (Ew M p) g := by
  refine WP.loop (M := isa) (PInv s₀ M m₁ B p g) ?_ n s hI
  rintro n s ⟨hn, hng, a, hc, hS, hF, K, hx⟩
  have hi : g - n < 4 := by omega_arith
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (prepGroupX_wp he hi a hS)
    fun s₁ ⟨a₁, c₁, x₁, f₁, kin, rk, rk4, rk5⟩ => ?_))
  have hS₁ : Sch M s₁.mem p := hS.frame he f₁ (by omega_arith)
  have K₁ : KeysTo s₁.mem B g (Ew M p) (g - n) := K.frame f₁ (by omega_arith) (fun i' h' => by omega_arith)
    (fun i' _ h' => by omega_arith) (by omega_arith)
  have F₁ : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 24, 480⟩] m₁ s₁.mem :=
    hF.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)⟩)
  refine wp_subi_x fun s₂ u₂ xe₂ z₂ => WP.block_nil ?_
  have a₂ := a₁.upd u₂ xe₂ (by decide)
  have c₂ : s₂.gpr .ecx = BitVec.ofNat 32 (n - 1) := by rw [u₂.gpr, c₁, hc]; exact Wp.ofNat_pred hn
  have z₂' : s₂.zf = some (decide (n = 1)) := by
    rw [z₂, c₁, hc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_beq (by omega_arith) (by decide)]
  refine WP.ite (decide (n = 1)) z₂' (fun hb => WP.block_nil (.inl ⟨?_, ?_⟩)) fun hb => ?_
  · show s₂.zf.map _ = _
    rw [z₂', hb]; rfl
  · have h1 : n = 1 := of_decide_eq_true hb
    subst h1
    have K₂ := K₁.step hx kin rk rk4 rk5 (fun h' => by omega_arith)
    rw [Nat.sub_add_cancel hng] at K₂
    exact ⟨a₂, by rw [u₂.mem]; exact hS₁, by rw [u₂.mem]; exact F₁, by rw [u₂.mem]; exact K₂⟩
  · have h1 : n ≠ 1 := of_decide_eq_false hb
    have hS₂ : Sch M s₂.mem p := by rw [u₂.mem]; exact hS₁
    refine WP.block_append_iff.mpr (WP.mono (prepMasksX_wp he hi a₂ hS₂) fun s₃ ⟨a₃, c₃, x₃, f₃, fl₃⟩ => ?_)
    rw [u₂.mem, Nat.add_assoc] at f₃
    have sl := slot_lt
    have K₃ := (K₁.frame f₃ (by omega_arith) (fun i' h' => by omega_arith) (fun i' _ h' => by omega_arith)
      (by omega_arith)).step hx
      (fun j hj => by
        have := sl j
        rw [kAt_frame f₃ (by omega_arith) (by omega_arith) (by omega_arith),
          kAt_frame f₃ (by omega_arith) (by omega_arith) (by omega_arith)]
        exact kin j hj)
      (fun r hr j hj => by
        have := sl j
        rw [kAt_frame f₃ (by omega_arith) (by omega_arith) (by omega_arith)]; exact rk r hr j hj)
      (fun j hj => by
        have := sl j
        rw [kAt_frame f₃ (by omega_arith) (by omega_arith) (by omega_arith)]; exact rk4 j hj)
      (fun j hj => by
        have := sl j
        rw [kAt_frame f₃ (by omega_arith) (by omega_arith) (by omega_arith)]; exact rk5 j hj)
      (fun _ => fl₃)
    have hS₃ : Sch M s₃.mem p := hS₁.frame he f₃ (by omega_arith)
    have F₃ : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 24, 480⟩] m₁ s₃.mem :=
      F₁.trans (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)⟩)
    refine wp_addi_x fun s₄ u₄ xe₄ => wp_addi_x fun s₅ u₅ xe₅ => wp_test_x fun s₆ u₆ xe₆ z₆ => WP.block_nil ?_
    have x₆ : s₆.xmm = s₃.xmm := xe₆.trans (xe₅.trans xe₄)
    have m₆ : s₆.mem = s₃.mem := u₆.mem.trans (u₅.mem.trans u₄.mem)
    have c₆ : s₆.gpr .ecx = BitVec.ofNat 32 (n - 1) := by
      rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), c₃, c₂]
    refine .inr ⟨?_, n - 1, by omega_arith, by omega_arith, by omega_arith, ?_, c₆, by rw [m₆]; exact hS₃,
      by rw [m₆]; exact F₃, ?_, ?_⟩
    · show s₆.zf.map _ = _
      rw [z₆, u₅.other _ (by decide), u₄.other _ (by decide), c₃, c₂, BitVec.and_self,
        Wp.ofNat_beq_zero (by omega_arith), decide_eq_false (by omega_arith)]
      rfl
    · rw [show g - (n - 1) = g - n + 1 by omega_arith]
      refine ⟨?_, ?_, u₆.rd.trans (u₅.rd.trans (u₄.rd.trans a₃.rd)), u₆.wr.trans (u₅.wr.trans (u₄.wr.trans a₃.wr)),
        u₆.syms.trans (u₅.syms.trans (u₄.syms.trans a₃.syms)), ?_, ?_, ?_, by rw [x₆]; exact a₃.msk⟩
      · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide)]; exact a₃.base
      · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide)]; exact a₃.esp
      · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide)]; exact a₃.tb
      · rw [u₆.gpr, u₅.other _ (by decide), u₄.gpr, a₃.sp, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl,
          Offset.add_ofNat_add_ofNat, show 64 * (g - n) + 64 = 64 * (g - n + 1) by omega_arith]
      · rw [u₆.gpr, u₅.gpr, u₄.other _ (by decide), a₃.kp, show (112 : BitVec 32) = BitVec.ofNat 32 112 from rfl,
          Offset.add_ofNat_add_ofNat, show 24 + 112 * (g - n) + 112 = 24 + 112 * (g - n + 1) by omega_arith]
    · rw [show g - (n - 1) = g - n + 1 by omega_arith, m₆]; exact K₃
    · rw [show g - (n - 1) = g - n + 1 by omega_arith, X6, ite_eq_right (Nat.succ_ne_zero _), x₆]
      intro q hq
      rw [x₃ q hq, show s₂.xmm = s₁.xmm from xe₂]
      exact x₁ q hq

end

/-! ### `prepare` -/

section
variable {s : State} {B p : BitVec 32} {M : Mem}

/-- The table's address to the scratch buffer's first slot, the registers
of the loop, and the first two subkeys in the rounds' form (`prepHead`),
with the table's address in `eax`. -/
theorem prepHead_wp {R : Nat} (hB : s.gpr Impl.Modes.X86.sb = B) (he : PEnv s B p) (hR : R = 18 ∨ R = 24)
    (hax : s.gpr .eax = s.syms tableName) (hS : Sch M s.mem p)
    (hin0 : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4) (hp : s.mem.readW (s.ea (argOp 0)) 32 = p)
    (h0B : Region.Disjoint ⟨s.ea (argOp 0), 4⟩ ⟨B.setWidth 64, 544⟩)
    (hin1 : InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4)
    (hv : s.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 R)
    (h1B : Region.Disjoint ⟨s.ea (argOp 1), 4⟩ ⟨B.setWidth 64, 544⟩) :
    WP isa (.block prepHead) s fun s' => PAt s B p 0 s' ∧ s'.gpr .ecx = BitVec.ofNat 32 (R / 6) ∧
      Sch M s'.mem p ∧ Frame [⟨B.setWidth 64, 4⟩] s.mem s'.mem ∧
      s'.mem.readW (B.setWidth 64) 32 = s.syms tableName ∧ X6 (s'.xmm .xmm6) (Ew M p) 0 := by
  have hf := he.scr.fit
  have hpf := he.pfit
  have ha0 : addr B 0 = B.setWidth 64 := by rw [addr_eq (by omega_arith), BitVec.add_zero]
  have hw : InRegions s.wr (addr B 0) 4 := ⟨_, he.scr.wr, by
    rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  show WP isa (.block (.store ⟨Impl.Modes.X86.sb, 0⟩ .eax :: .mov tbr (.reg .eax) :: .mov .eax (.mem ⟨.esp, 4 + 4 * 0⟩) ::
    .mov .ecx (.mem ⟨.esp, 4 + 4 * 1⟩) :: .shift .shr .ecx 3 :: .alu .add .ecx (.imm 1) ::
    .mov kr (.reg Impl.Modes.X86.sb) :: .alu .add kr (.imm 24) :: prepHeadX)) s _
  refine Wp.wp_stm hB hw fun s₂ u₂ => ?_
  have f₂ : Frame [⟨B.setWidth 64, 4⟩] s.mem s₂.mem := by
    rw [u₂.mem, ha0]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 4)
  have sub4 : Region.Sub ⟨B.setWidth 64, 4⟩ ⟨B.setWidth 64, 544⟩ := Region.sub_prefix (by decide)
  have e0 : s₂.mem.readW (s.ea (argOp 0)) 32 = p := by
    rw [f₂.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h0B.sub_right sub4) (by decide), hp]
  have e1 : s₂.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 R := by
    rw [f₂.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h1B.sub_right sub4) (by decide), hv]
  refine Wp.wp_mov fun s₃ u₃ => ?_
  refine Wp.wp_ldm (B := s.gpr .esp) (by rw [u₃.other _ (by decide), u₂.gpr]) (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hin0)
    fun s₄ u₄ => ?_
  refine Wp.wp_ldm (B := s.gpr .esp) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hin1) fun s₅ u₅ => ?_
  refine Wp.wp_shr (by decide) fun s₆ u₆ _ => ?_
  refine Wp.wp_addi fun s₇ u₇ => ?_
  refine Wp.wp_mov fun s₈ u₈ => ?_
  refine Wp.wp_addi fun s₉ u₉ => ?_
  have m₉ : s₉.mem = s₂.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have r₉ : s₉.rd = s.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]
  have w₉ : s₉.wr = s.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]
  have y₉ : s₉.syms = s.syms := by rw [u₉.syms, u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms]
  have b₉ : s₉.gpr Impl.Modes.X86.sb = B := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hB]
  have sp₉ : s₉.gpr .esp = s.gpr .esp := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  have t₉ : s₉.gpr tbr = s.syms tableName := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, hax]
  have a₉ : s₉.gpr .eax = p := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.gpr, u₃.mem]
    exact e0
  have c₉ : s₉.gpr .ecx = BitVec.ofNat 32 (R / 6) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.gpr, u₄.mem, u₃.mem]
    show (s₂.mem.readW (s.ea (argOp 1)) 32 >>> 3) + 1 = _
    rw [e1]
    rcases hR with rfl | rfl <;> rfl
  have k₉ : s₉.gpr kr = B + BitVec.ofNat 32 (24 + 112 * 0) := by
    rw [u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hB]
    rfl
  have hS₉ : Sch M s₉.mem p := by
    rw [m₉]
    exact hS.frame (a := 0) he (by rw [BitVec.add_zero]; exact f₂) (by decide)
  have hok := prep_all.1
  unfold prepHeadOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨x6s, x6⟩, mk⟩ := hok
  have hrel : Rel pparams (envOf pparams s₉) Regs.init s₉ := rel_init (p := pparams)
    (by show s₉.gpr tbr = s₉.syms tableName; rw [t₉, y₉]) (by show (s₉.gpr .eax).toNat + 80 ≤ _; rw [a₉]; omega_arith)
    fun o ho => ⟨_, by rw [r₉, w₉]; exact he.sch, by
      show Region.Contains _ (addr (s₉.gpr .eax) o) 16
      have ho' : o + 16 ≤ 80 := ho
      rw [a₉, addr_eq (by omega_arith)]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine run_wp hrel hrun fun s' hr hs => ?_
  obtain ⟨f, rfl⟩ := hs
  refine ⟨⟨b₉, sp₉, r₉, w₉, y₉, t₉, by rw [show (_ : State).gpr .eax = s₉.gpr .eax from rfl, a₉]; simp, k₉,
    rel_mask hr mk⟩, c₉, hS₉, by rw [show (_ : State).mem = s₉.mem from rfl, m₉]; exact f₂, ?_, ?_⟩
  · show s₉.mem.readW (B.setWidth 64) 32 = _
    rw [m₉, u₂.mem, ha0, Mem.readW_writeW_self32, hax]
  · rw [X6, ite_eq_left rfl]
    intro j hj
    have sj := slot_lt j
    rw [rel_bytes hr x6s x6 (show slot j < 16 by omega_arith), rel_bytes hr x6s x6 (show slot j + 8 < 16 by omega_arith),
      pT_eval 0 (by omega_arith) (by decide), pT_eval 0 (by omega_arith) (by decide), (bswq_slot hj).1,
      (bswq_slot hj).2, show slot j % 8 = slot j by omega_arith, show (slot j + 8) % 8 = slot j by omega_arith,
      slot_slot hj, a₉, show 0 + (7 - j) = 8 * 0 + (7 - j) by omega_arith,
      show 0 + (15 - j) = 8 * 1 + (7 - j) by omega_arith, sch_bz hS₉ (by decide) hj, sch_bz hS₉ (by decide) hj]
    exact ⟨rfl, rfl⟩

/-- `prepare` leaves the keys of the schedule's subkeys in the scratch
buffer, and the table's address in its first slot; it writes only the core's
slots, and the four bytes below `esp` of the frame that gets the table's
address. -/
theorem prepare_wp {R : Nat} (hB : s.gpr Impl.Modes.X86.sb = B) (he : PEnv s B p) (hR : R = 18 ∨ R = 24)
    (hesp : 4 ≤ (s.gpr .esp).toNat)
    (hin0 : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4) (hp : s.mem.readW (s.ea (argOp 0)) 32 = p)
    (h0B : Region.Disjoint ⟨s.ea (argOp 0), 4⟩ ⟨B.setWidth 64, 544⟩)
    (hin1 : InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4)
    (hv : s.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 R)
    (h1B : Region.Disjoint ⟨s.ea (argOp 1), 4⟩ ⟨B.setWidth 64, 544⟩)
    (hkS : Region.Disjoint (below (s.gpr .esp) 4) ⟨p.setWidth 64, 272⟩)
    (h0S : Region.Disjoint (below (s.gpr .esp) 4) ⟨s.ea (argOp 0), 4⟩)
    (h1S : Region.Disjoint (below (s.gpr .esp) 4) ⟨s.ea (argOp 1), 4⟩) :
    WP isa prepare s fun s' => Keys s'.mem B (R / 6) (Ew s.mem p) ∧
      s'.mem.readW (B.setWidth 64) 32 = s.syms tableName ∧ s'.gpr Impl.Modes.X86.sb = B ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64, 504⟩, below (s.gpr .esp) 4] s.mem s'.mem := by
  obtain ⟨g, hg⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  have hg34 : g = 3 ∨ g = 4 := by omega_arith
  have hf := he.scr.fit
  rw [hg]
  show WP isa (.seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1)) (.seq (.block prepHead) (.seq
    (.loop (.seq (.block prepGroup) (.ite .e (.block []) (.block prepMasks))) .ne) (.block prepTail)))) s _
  refine WP.seq (WP.mono (symFrame_ok tableName s hesp) fun s₁ a₁ => ?_)
  have esp₁ : s₁.gpr .esp = s.gpr .esp := a₁.gpr .esp (by decide)
  have ea₁ : ∀ k, s₁.ea (argOp k) = s.ea (argOp k) := fun k => by
    show addr (s₁.gpr .esp) _ = addr (s.gpr .esp) _
    rw [esp₁]
  have he₁ : PEnv s₁ B p :=
    ⟨⟨by rw [a₁.wr]; exact he.scr.wr, he.scr.fit⟩, by rw [a₁.rd, a₁.wr]; exact he.sch, he.pfit, he.sep⟩
  have hS₁ : Sch s.mem s₁.mem p := fun o ho =>
    a₁.frame.bytes (R := ⟨p.setWidth 64, 272⟩) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hkS.symm) (by show (272 : Nat) ≤ 2 ^ 64; decide) ho
  have p₁ : s₁.mem.readW (s.ea (argOp 0)) 32 = p := by
    rw [a₁.frame.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h0S.symm) (by decide), hp]
  have v₁ : s₁.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 R := by
    rw [a₁.frame.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h1S.symm) (by decide), hv]
  refine WP.seq (WP.mono (prepHead_wp (R := R) (M := s.mem) (by rw [a₁.gpr _ (by decide)]; exact hB) he₁ hR
    (by rw [a₁.addr, a₁.syms]) hS₁ (by rw [ea₁, a₁.rd, a₁.wr]; exact hin0) (by rw [ea₁]; exact p₁)
    (by rw [ea₁]; exact h0B) (by rw [ea₁, a₁.rd, a₁.wr]; exact hin1) (by rw [ea₁]; exact v₁)
    (by rw [ea₁]; exact h1B)) fun s₂ ⟨a₂, c₂, hS₂, f₂, t₂, x₂⟩ => ?_)
  have hI : PInv s₁ s.mem s₂.mem B p g g s₂ :=
    ⟨by omega_arith, Nat.le_refl _, by rw [Nat.sub_self]; exact a₂, by rw [c₂, hg], hS₂, Frame.refl _ _,
      by rw [Nat.sub_self]; exact KeysTo.zero _ _ _ _, by rw [Nat.sub_self]; exact x₂⟩
  refine WP.seq (WP.mono (ploop_wp he₁ (by omega_arith) hI) fun s₃ ⟨a₃, hS₃, F₃, K₃⟩ => ?_)
  refine WP.mono (prepTail_wp he₁ (i := g - 1) (by omega_arith) a₃ hS₃ (k := 8 * g) (by omega_arith))
    fun s₄ ⟨a₄, f₄, o₄⟩ => ?_
  rw [Nat.add_assoc] at f₄
  have K₄ := K₃.frame f₄ (by omega_arith) (fun i' h' => by omega_arith) (fun i' h' _ => by omega_arith)
    (by omega_arith)
  refine ⟨⟨K₄.kin0 (by omega_arith), K₄.kin, K₄.rk, K₄.rk4, K₄.rk5, fun i hi => K₄.fl i hi (by omega_arith), o₄⟩,
    ?_, a₄.base, a₄.esp.trans esp₁, a₄.rd.trans a₁.rd, a₄.wr.trans a₁.wr, a₄.syms.trans a₁.syms, ?_⟩
  · rw [f₄.readW (r := ⟨B.setWidth 64, 4⟩) (Region.contains_self _ 4) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)) (by decide),
      F₃.readW (r := ⟨B.setWidth 64, 4⟩) (Region.contains_self _ 4) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by decide) (by decide)) (by decide), t₂, a₁.syms]
  · refine (((a₁.frame.mono fun r hr => ?_).trans (f₂.sub fun r hr => ?_)).trans (F₃.sub fun r hr => ?_)).trans
      (f₄.sub fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by omega_arith)⟩

/-- The keys depend on the subkeys the code reads: the first `8 g + 2`. -/
theorem Keys.congr {m : Mem} {g : Nat} {E E' : Nat → BitVec 64} (h : Keys m B g E) (hg : 1 ≤ g)
    (e : ∀ k < 8 * g + 2, E k = E' k) : Keys m B g E' := by
  refine ⟨fun j hj => ?_, fun i hi j hj => ?_, fun i hi r hr j hj => ?_, fun i hi j hj => ?_, fun i hi j hj => ?_,
    fun i hi => ?_, fun j hj => ?_⟩
  · rw [← e 0 (by omega_arith), ← e 1 (by omega_arith), ← e 2 (by omega_arith), ← e 3 (by omega_arith)]
    exact h.kin0 j hj
  · rw [← e _ (by omega_arith), ← e (2 + 8 * (i + 1) + 1) (by omega_arith)]
    exact h.kin i hi j hj
  · rw [← e _ (by omega_arith), ← e (2 + 8 * i + (r + 2)) (by omega_arith)]
    exact h.rk i hi r hr j hj
  · rw [← e _ (by omega_arith)]
    exact h.rk4 i hi j hj
  · rw [← e _ (by omega_arith)]
    exact h.rk5 i hi j hj
  · rw [← e _ (by omega_arith), ← e (9 + 8 * i) (by omega_arith)]
    exact h.fl i hi
  · rw [← e _ (by omega_arith), ← e (8 * g + 1) (by omega_arith)]
    exact h.out j hj

end

end

/-! ## The core -/

section


open VG VG.X86 VG.X86.ByteMap VG.Impl.Camellia.X86.AesNi
open VG.Impl.Modes.X86 (at_ argOp)
open VG.Proof.Modes.X86 (ScrIn coreRegion blkRegion blkAddr stkRegion slotA CoreSpec Layout)
open VG.Proof.Camellia (schedWords schedWords_getD wordAt_frame)

/-- The number of rounds and the schedule's words, through the first two
stack arguments, the schedule outside the regions `rs`, as are those
arguments, the number of rounds outside every writable region, and the four
bytes below `esp` apart from the schedule and from those arguments. -/
def KeyArgs (s : State) (rs : List Region) (k : Nat × List (BitVec 64)) : Prop :=
  ∃ p : BitVec 32, InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4 ∧ s.mem.readW (s.ea (argOp 0)) 32 = p ∧
    InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4 ∧ s.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 k.1 ∧
    (k.1 = 18 ∨ k.1 = 24) ∧ k.2 = schedWords s.mem (p.setWidth 64) k.1 ∧
    (⟨p.setWidth 64, 272⟩ : Region) ∈ s.rd ++ s.wr ∧ p.toNat + 272 ≤ 2 ^ 32 ∧
    (∀ r ∈ rs, Region.Disjoint ⟨p.setWidth 64, 272⟩ r) ∧ (∀ r ∈ rs, Region.Disjoint ⟨s.ea (argOp 0), 4⟩ r) ∧
    (∀ r ∈ rs, Region.Disjoint ⟨s.ea (argOp 1), 4⟩ r) ∧ (∀ r ∈ s.wr, Region.Disjoint ⟨s.ea (argOp 1), 4⟩ r) ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 4) ⟨p.setWidth 64, 272⟩ ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 4) ⟨s.ea (argOp 0), 4⟩ ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 4) ⟨s.ea (argOp 1), 4⟩

/-- The number of rounds `R` in the second stack argument, readable and apart
from every writable region. -/
def RArg (s : State) (R : Nat) : Prop :=
  InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4 ∧ s.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 R ∧
    ∀ r ∈ s.wr, Region.Disjoint ⟨s.ea (argOp 1), 4⟩ r

theorem ea_esp {s s' : State} (h : s'.gpr .esp = s.gpr .esp) (i : Nat) : s'.ea (argOp i) = s.ea (argOp i) := by
  show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64
  rw [h]

theorem RArg.frame {s s' : State} {R : Nat} {rs : List Region} (h : RArg s R) (hesp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ s.wr, Region.Sub r r') : RArg s' R := by
  obtain ⟨hin, hv, hd⟩ := h
  refine ⟨by rw [hrd, hwr, ea_esp hesp]; exact hin, ?_, by rw [hwr, ea_esp hesp]; exact hd⟩
  rw [ea_esp hesp, hf.readW (Region.contains_self _ _) (fun r hr => by
    obtain ⟨r', hr', hs⟩ := hsub r hr; exact (hd r' hr').sub_right hs) (by decide), hv]

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Nat × List (BitVec 64)} (h : KeyArgs s rs k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨p, hin0, hp, hin1, hR, hRv, hws, hsch, hfit, hdis, hd0, hd1, hdw, hkS, h0S, h1S⟩ := h
  have hea := ea_esp hesp
  refine ⟨p, by rw [hrd, hwr, hea]; exact hin0, ?_, by rw [hrd, hwr, hea]; exact hin1, ?_, hRv, ?_,
    by rw [hrd, hwr]; exact hsch, hfit, hdis, by rw [hea]; exact hd0, by rw [hea]; exact hd1,
    by rw [hwr, hea]; exact hdw, by rw [hesp]; exact hkS, by rw [hesp, hea]; exact h0S,
    by rw [hesp, hea]; exact h1S⟩
  · rw [hea, hf.readW (Region.contains_self _ _) hd0 (by decide), hp]
  · rw [hea, hf.readW (Region.contains_self _ _) hd1 (by decide), hR]
  · rw [hws]
    simp only [schedWords]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    have hl : 8 * i + 8 ≤ 272 := by simp only [Spec.Camellia.scheduleLength] at hi; omega_using [hRv, hi]
    exact (wordAt_frame hf fun r hr => (hdis r hr).sub_left (VG.Offset.sub_base _ hl)).symm

/-- The key `k` is ready in the scratch buffer at `B`. -/
def Ready (s : State) (B : BitVec 32) (k : Nat × List (BitVec 64)) : Prop :=
  Keys s.mem B (k.1 / 6) (fun i => k.2.getD i 0) ∧ s.mem.readW (B.setWidth 64) 32 = s.syms tableName ∧
    RArg s k.1 ∧ (k.1 = 18 ∨ k.1 = 24) ∧ B.toNat + 544 ≤ 2 ^ 32

/-- The 16 bytes at a byte of the keys, from the bytes. -/
theorem wAt_congr {m m' : Mem} {B : BitVec 32} {o : Nat} (h : ∀ q < 16, kAt m' B (o + q) = kAt m B (o + q)) :
    wAt m' B o = wAt m B o :=
  wAt_bytes m' B o fun q hq => by
    rw [h q hq]
    show _ = (m.readW _ 128).extractLsb' (8 * q) 8
    rw [byte_readW _ _ (by omega_arith), Offset.add_ofNat_add_ofNat, Nat.add_assoc]
    rfl

/-- The keys are their bytes. -/
theorem Keys.eqOn {m m' : Mem} {B : BitVec 32} {g : Nat} {E : Nat → BitVec 64} (h : Keys m B g E) (hg : g ≤ 4)
    (e : ∀ o < 480, kAt m' B o = kAt m B o) : Keys m' B g E := by
  have sl := slot_lt
  refine ⟨fun j hj => ?_, fun i hi j hj => ?_, fun i hi r hr j hj => ?_, fun i hi j hj => ?_, fun i hi j hj => ?_,
    fun i hi => ⟨?_, ?_, ?_⟩, fun j hj => ?_⟩
  · have := sl j
    rw [e _ (by omega_arith), e _ (by omega_arith)]; exact h.kin0 j hj
  · have := sl j
    rw [e _ (by omega_arith), e _ (by omega_arith)]; exact h.kin i hi j hj
  · have := sl j
    rw [e _ (by omega_arith)]; exact h.rk i hi r hr j hj
  · have := sl j
    rw [e _ (by omega_arith)]; exact h.rk4 i hi j hj
  · have := sl j
    rw [e _ (by omega_arith)]; exact h.rk5 i hi j hj
  · show wAt m' B (112 * i + 64) = _
    rw [wAt_congr fun q hq => e _ (by omega_arith)]; exact (h.fl i hi).e1
  · show wAt m' B (112 * i + 80) = _
    rw [wAt_congr fun q hq => e _ (by omega_arith)]; exact (h.fl i hi).e2
  · show wAt m' B (112 * i + 96) = _
    rw [wAt_congr fun q hq => e _ (by omega_arith)]; exact (h.fl i hi).c
  · rw [e _ (by omega_arith), e _ (by omega_arith)]; exact h.out j hj

theorem core_total : core.total = 136 := rfl
theorem core_slots : core.slots = 126 := rfl

/-- The key stays ready through what a mode writes outside the core's slots
or within its buffer. -/
theorem ready_frame {s s' : State} {B : BitVec 32} {k : Nat × List (BitVec 64)} {rs : List Region}
    (h : Ready s B k) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsy : s'.syms = s.syms) (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, ∃ r' ∈ s.wr, Region.Sub r r')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion core B) r ∨ Region.Sub r (blkRegion core B)) : Ready s' B k := by
  obtain ⟨hk, ht, ha, hR, hfit⟩ := h
  have keep : ∀ {a n : Nat}, a + n ≤ 504 → (a + n ≤ 8 ∨ 24 ≤ a) → ∀ r ∈ rs,
      Region.Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 a, n⟩ r := fun {a n} h₁ h₂ r hr => by
    rcases hd r hr with h | h
    · exact h.sub_left (Offset.sub_base _ (by rw [core_slots]; omega_arith))
    · exact (Offset.disjoint (B.setWidth 64) (d := a) (n := n) (e := 4 * core.buf) (k := 4 * core.bw * core.G)
        (by show a + n ≤ 8 ∨ 8 + 16 ≤ a; omega_arith) (by omega_arith) (by decide)).sub_right h
  refine ⟨hk.eqOn (by omega_arith) fun o ho => ?_, ?_, ha.frame hesp hrd hwr hf hs, hR, hfit⟩
  · have := hf.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 (24 + o), 1⟩) (keep (by omega_arith) (.inr (by omega_arith)))
      (by show (1 : Nat) ≤ 2 ^ 64; decide) (i := 0) (show (0 : Nat) < 1 by decide)
    rw [BitVec.add_zero] at this
    exact this
  · have e := hf.readW (r := ⟨B.setWidth 64 + BitVec.ofNat 64 0, 4⟩) (a := B.setWidth 64 + BitVec.ofNat 64 0)
      (w := 32) (Region.contains_self _ 4) (keep (by decide) (.inl (by decide))) (by decide)
    rw [BitVec.add_zero] at e
    rw [e, hsy]; exact ht

theorem prepare_ok {s : State} {B : BitVec 32} {rs : List Region} {k : Nat × List (BitVec 64)}
    (hB : s.gpr Impl.Modes.X86.sb = B) (hs : ScrIn s B core.total)
    (hR : (⟨B.setWidth 64, 4 * core.total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k)
    (hsp : core.stack ≤ (s.gpr .esp).toNat) :
    WP isa core.prepare s fun s' => Ready s' B k ∧ s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion core B, stkRegion (s.gpr .esp) core.stack] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨p, hin0, hp, hin1, hRa, hRv, hws, hsch, hfit, hdis, hd0, hd1, hdw, hkS, h0S, h1S⟩ := hk
  simp only at hRa hRv hws ⊢
  have he : PEnv s B p := ⟨hs, hsch, hfit, hdis _ hR⟩
  refine WP.mono (prepare_wp hB he hRv hsp hin0 hp (hd0 _ hR) hin1 hRa (hd1 _ hR) hkS h0S h1S)
    fun s' ⟨K, t, b, e, rd, wr, sy, f⟩ => ?_
  refine ⟨⟨K.congr (by omega_arith) fun i hi => ?_, by rw [t, sy], ⟨by rw [rd, wr, ea_esp e]; exact hin1, ?_,
    by rw [wr, ea_esp e]; exact hdw⟩, hRv, hs.fit⟩, b, e, f, rd, wr⟩
  · rw [hws, schedWords_getD _ _ (by simp only [Spec.Camellia.scheduleLength]; exact hi)]
    rfl
  · rw [ea_esp e, f.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), hRa]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hd1 _ hR).sub_right (Region.sub_prefix (by decide))
    · exact h1S.symm

theorem crypt_ok {s : State} {B : BitVec 32} {k : Nat × List (BitVec 64)} (hB : s.gpr Impl.Modes.X86.sb = B)
    (hs : ScrIn s B core.total) (hr : Ready s B k) :
    WP isa core.crypt s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ Ready s' B k ∧
      Frame [coreRegion core B, stkRegion (s.gpr .esp) core.stack] s.mem s'.mem ∧
      (∀ j < core.G, Spec.Aes.bytesAt s'.mem (blkAddr core B j) (4 * core.bw) =
        Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords k.1 k.2)
          (Spec.Aes.bytesAt s.mem (blkAddr core B j) (4 * core.bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨hk, ht, ha, hR, hfit⟩ := hr
  refine WP.mono (crypt_wp hB hs hR hk ha.1 ha.2.1 ht) fun s' ⟨b, e, rd, wr, sy, f, v⟩ => ?_
  have hblk : blkAddr core B 0 = B.setWidth 64 + BitVec.ofNat 64 8 := by
    show B.setWidth 64 + BitVec.ofNat 64 (4 * 2) + BitVec.ofNat 64 (4 * 4 * 0) = _
    rw [Offset.add_ofNat_add_ofNat]
  refine ⟨b, e, ready_frame ⟨hk, ht, ha, hR, hfit⟩ e rd wr sy f (fun r hr => ?_) (fun r hr => ?_),
    f.sub fun r hr => ?_, fun j hj => ?_, rd, wr⟩
  · rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, hs.wr, Offset.sub_base _ (by decide)⟩
  · rw [List.mem_singleton] at hr; subst hr
    exact .inr fun _ h => h
  · rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
  · have h0 : j = 0 := by
      have : j < 1 := hj
      omega_arith
    subst h0
    rw [hblk]
    exact v

/-- Camellia's core by the AES S-box meets what the modes need. -/
def coreSpec : CoreSpec core where
  Key := Nat × List (BitVec 64)
  cipher k := Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords k.1 k.2)
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len _ _ := by simp [Spec.Camellia.cipher, core]
  layout := ⟨by decide, .inr rfl, by decide, by decide⟩
  keyArgs_congr h e r w _ f := keyArgs_congr h e r w f
  ready_frame h e r w sy f hs hd := ready_frame h e r w sy f hs hd
  prepare_wp hB hs hR hk hsp := prepare_ok hB hs hR hk hsp
  crypt_wp hB hs hr _ := crypt_ok hB hs hr

end

end VG.Proof.Camellia.X86.AesNi
