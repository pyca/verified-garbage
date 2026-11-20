module

public import VerifiedGarbage.Proof.AesXts.AArch64.CT
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Xts.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Spec.Xts.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
public import VerifiedGarbage.Impl.AesXts.AArch64
public import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant
public import VerifiedGarbage.Proof.AesCbc.AArch64.Block
public import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.AesCbc.AArch64.Verified
meta import VerifiedGarbage.Impl.AesXts.AArch64
meta import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Block
meta import VerifiedGarbage.Proof.AesXts.Spec
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Verified
meta import VerifiedGarbage.Proof.AesXts.AArch64.CT
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
import VerifiedGarbage.Proof.AesCbc.AArch64.Body
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Impl.AesXts.AArch64Aes
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
public import VerifiedGarbage.Proof.AesCbc.Spec
public import VerifiedGarbage.Proof.AesXts.Alpha16
import VerifiedGarbage.Proof.AesXts.Alpha
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.AesXts.AArch64.Steps
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
public import VerifiedGarbage.Proof.AesCbc.AArch64.Loop
meta import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Body
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Impl.AesXts.AArch64Aes
meta import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
meta import VerifiedGarbage.Proof.AesCbc.Spec
meta import VerifiedGarbage.Proof.AesXts.Alpha16
meta import VerifiedGarbage.Proof.AesXts.Alpha
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.AesXts.AArch64.Steps
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Loop
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `AesXts.AArch64.Aes.Top`, which only this module used -/

section

/-! ### `AesXts.AArch64.Aes.Group`, which only this module used -/

section

/-! ### `AesXts.AArch64.Aes.Pre`, which only this module used -/

section

/-! ### `AesXts.AArch64.Aes.Word`, which only this module used -/

section

/-!
# One-pass XTS-AES on AArch64: blocks and tweaks as words

The one-pass functions (`Impl/AesXts/AArch64Aes.lean`) hold blocks and
tweaks as 128-bit words, in vector registers and in memory, and the tweak
also as its two 64-bit halves in `x14` and `x15`. A word's bytes are `b16`
of it (`bytesAt_b16`, `st_toList`); XOR of words is XOR of their bytes
(`b16_xor`); and the cipher of a register's state is the cipher of its bytes
(`ciphOf_b16`). `xts_word`: the XTS of a block from its words, as the
functions compute it. `mulA128_append`: `AArch64Aes.mulA` on the halves is
`mulA128` on the word, and `twW t k`, the tweak `k` blocks on as a word, has
the bytes of `Spec.Xts.next` (`b16_twW`).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Aes

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesXts (b16 mulA128)
open VG.Proof.Aes.AArch64.Aese (st ext_vbyte vbyte_readW)
open VG.Proof.AesCbc (ciphOf)

theorem bytesAt_b16 (m : Mem) (p : Addr) : bytesAt m p 16 = b16 (m.readW p 128) :=
  AesXts.bytesAt_readW (k := 16) m p

theorem b16_xor (a b : BitVec 128) : b16 (a ^^^ b) = Spec.Cbc.xor (b16 a) (b16 b) := by
  apply List.ext_getElem (by simp [b16, Spec.Cbc.xor])
  intro k h₁ h₂
  obtain hk : k < 16 := by simpa [b16] using h₁
  simp only [b16, Spec.Cbc.xor, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  ext j hj
  simp

theorem st_toList (v : BitVec 128) : (st v).toList = b16 v := by
  apply List.ext_getElem (by simp [b16])
  intro i h₁ h₂
  simp [st, b16, vbyte]

/-- The function of states of a direction: the cipher or its inverse. -/
def stF (enc : Bool) (nr : Nat) (w : List Byte) : Spec.Aes.State → Spec.Aes.State :=
  if enc then Spec.Aes.cipher nr w else Spec.Aes.invCipher nr w

theorem ciphOf_b16 (enc : Bool) (nr : Nat) (w : List Byte) (v : BitVec 128) :
    ciphOf enc nr w (b16 v) = (stF enc nr w (st v)).toList := by
  obtain e : (Vector.ofFn fun i : Fin 16 => (b16 v).getD i.1 0) = st v := by
    apply Vector.ext
    intro i hi
    simp [b16, st, vbyte]
  cases enc
  · simp only [ciphOf, stF, Bool.false_eq_true, ↓reduceIte, Spec.Cbc.aesInvWith, e]
  · simp only [ciphOf, stF, ↓reduceIte, Spec.Cbc.aesWith, e]

/-- A block `d` through XTS with the tweak `t`, as words, when `c` is the
word of the cipher of `d ⊕ t`'s state. -/
theorem xts_word (enc : Bool) (nr : Nat) (w : List Byte) (d t c : BitVec 128)
    (hc : st c = stF enc nr w (st (d ^^^ t))) :
    b16 (c ^^^ t) = Spec.Xts.block (ciphOf enc nr w) (b16 t) (b16 d) := by
  rw [Spec.Xts.block, b16_xor, ← st_toList c, hc, ← ciphOf_b16, b16_xor]

/-! ## The tweak -/

/-- The low half of the tweak times `α`, from its halves. -/
def mulLo (lo hi : BitVec 64) : BitVec 64 := (lo <<< 1) ^^^ (if hi.msb then (0x87 : BitVec 64) else 0)

/-- The high half of the tweak times `α`, from its halves. -/
def mulHi (lo hi : BitVec 64) : BitVec 64 := (hi <<< 1) ||| (if lo.msb then (1 : BitVec 64) else 0)

theorem msb_append64 (lo hi : BitVec 64) : (hi ++ lo).msb = hi.msb := by
  simp only [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_append]; rfl
theorem k87 {i : Nat} (h : i < 64) : (135#128)[i] = (135#64)[i] := by
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat]
  simp [h]; omega_arith
theorem k87' {i : Nat} (h : 64 ≤ i) (h' : i < 128) : (135#128)[i] = false := by
  rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat]
  simp [h']; exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) h))
theorem k1 {j : Nat} (h : j < 64) (h0 : j ≠ 0) : (1#64)[j] = false := by
  rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat]
  simp only [h, decide_true, Bool.true_and]; exact Nat.testBit_lt_two_pow (Nat.one_lt_two_pow h0)
theorem mulA128_append (lo hi : BitVec 64) : mulA128 (hi ++ lo) = mulHi lo hi ++ mulLo lo hi := by
  rw [mulA128, msb_append64, mulHi, mulLo]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last]
  simp only [Nat.add_one_sub_one]
  by_cases h64 : i < 64
  · by_cases h0 : i = 0
    · subst h0; cases hi.getLsbD 63 <;> simp
    · have : ¬ i < 1 := by omega_arith
      cases hi.getLsbD 63 <;> simp [h64, this, show i - 1 < 64 by omega_arith, hi', k87 h64]
  · by_cases h0 : i = 64
    · subst h0; cases hi.getLsbD 63 <;> cases lo.getLsbD 63 <;> simp [k87']
    · have : ¬ i - 64 < 1 := by omega_arith
      cases hi.getLsbD 63 <;> cases lo.getLsbD 63 <;>
        simp [h64, this, show ¬ i - 1 < 64 by omega_arith, hi', k87' (by omega_arith) hi', k1 (show i - 64 < 64 by omega_arith) (by omega_arith),
          show i - 1 - 64 = i - 64 - 1 by omega_arith, show i - 64 < 64 by omega_arith] <;> omega_arith
/-- `dup v.2d, lo` then `ins v.d[1], hi`. -/
theorem setLane_dup (lo hi : BitVec 64) : setLane (ofVDwords lo lo) 64 1 hi = hi ++ lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [setLane, ofVDwords, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_append]
  by_cases h : i < 64 <;> simp [h, hi', show i - 64 < 64 by omega_arith, show i - 64 < 128 by omega_arith]

/-- The tweak `k` blocks on from `t`, as a word. -/
def twW (t : BitVec 128) (k : Nat) : BitVec 128 := Nat.repeat mulA128 k t

theorem twW_succ (t : BitVec 128) (k : Nat) : twW t (k + 1) = mulA128 (twW t k) := rfl

theorem b16_twW (t : BitVec 128) : ∀ k, b16 (twW t k) = Spec.Xts.next (b16 t) k
  | 0 => rfl
  | k + 1 => by rw [twW_succ, AesXts.mulAlpha_b16, b16_twW t k, AesXts.next_succ]

theorem vbyte_append_lo (x y : BitVec 64) {i : Nat} (h : i < 8) : vbyte (x ++ y) i = y.extractLsb' (8 * i) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [vbyte, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_append]; simp [show 8 * i + j < 64 by omega_arith]
theorem vbyte_append_hi (x y : BitVec 64) {i : Nat} (h : 8 ≤ i) (h' : i < 16) :
    vbyte (x ++ y) i = x.extractLsb' (8 * (i - 8)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [vbyte, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_append]; simp [show ¬ 8 * i + j < 64 by omega_arith]
  exact congrArg _ (by omega_arith)
/-- 16 bytes as two doublewords. -/
theorem readW128 (m : Mem) (a : Addr) : m.readW a 128 = m.readW (a + BitVec.ofNat 64 8) 64 ++ m.readW a 64 := by
  apply ext_vbyte; intro i hi
  rw [vbyte_readW _ _ hi]
  by_cases h : i < 8
  · rw [vbyte_append_lo _ _ h]; simp only [Mem.readW, BitVec.setWidth_eq]
    exact (Mem.extractLsb'_read m a (n := 8) h).symm
  · rw [vbyte_append_hi _ _ (by omega_arith) hi]; simp only [Mem.readW, BitVec.setWidth_eq]
    rw [Mem.extractLsb'_read m _ (n := 8) (show i - 8 < 8 by omega_arith), Offset.add_add_eq a (show 8 + (i - 8) = i by omega_arith)]

end VG.Proof.AesXts.AArch64.Aes

end

end


/-!
# One-pass XTS-AES on AArch64: the tweaks XORed in

`mulA_run`: `AArch64Aes.mulA` multiplies the tweak in `x14` (low) and `x15`
(high) by `α` (`mulA128` of `x15 ++ x14`), through `x9` and `x10`.
`pre1_run`: one block loaded, XORed with the tweak, the tweak saved to the
scratch buffer, and the tweak multiplied by `α`. `pre_ok`: `pre rs j` does
that for each register of `rs`, with the tweaks `twW t k` from the tweak `t`
in `x14` and `x15`.
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Aes

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.AesXts.AArch64Aes (mulA pre1 pre post1 post preL1 preL genStep gen)
open VG.Proof.AesXts (mulA128)
open VG.Proof.Aes.AArch64.Aese (exec_ldrq exec_strq setV_v_self setV_v_of_ne)

/-- The tweak in `x14` (low) and `x15` (high). -/
abbrev tweakOf (s : State) : BitVec 128 := s.gpr .x15 ++ s.gpr .x14

theorem write16 (m : Mem) (a : Addr) (v : BitVec 128) : m.write a 16 v = m.writeW a v := by
  simp [Mem.writeW]

theorem mulA_run (s : State) :
    ∃ s', runBlock isa mulA s = some s' ∧ tweakOf s' = mulA128 (tweakOf s) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → s'.gpr r = s.gpr r) ∧
      s'.v = s.v ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [mulA, gpr_addWithCarry, c_addWithCarry, c_write, mem_addWithCarry, rd_addWithCarry,
    wr_addWithCarry, sp_addWithCarry], ?_⟩
  refine ⟨?_, fun r h₁ h₂ h₃ h₄ => by simp [gpr_write, gpr_addWithCarry, h₁, h₂, h₃, h₄], rfl, rfl, rfl, rfl, rfl⟩
  rw [tweakOf, tweakOf, mulA128_append]
  simp only [gpr_write, gpr_addWithCarry, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq, Size.bits]
  simp only [mulHi, mulLo, AesXts.AArch64.carry_c, AesXts.AArch64.add_bit, AesXts.AArch64.sel_87,
    Bool.false_eq_true, ↓reduceIte, AesXts.AArch64.or_zero']

theorem pre1_run (b : VReg) (j : Nat) (s : State) (hb : b ≠ .v31) (hj : j < 8)
    (hld : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (16 * j)) 16)
    (hst : InRegions s.wr (s.gpr .x5 + BitVec.ofNat 64 (16 * j)) 16) :
    ∃ s', runBlock isa (pre1 b j) s = some s' ∧
      s'.v b = s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (16 * j)) 128 ^^^ tweakOf s ∧
      (∀ r, r ≠ b → r ≠ .v31 → s'.v r = s.v r) ∧
      s'.mem = s.mem.writeW (s.gpr .x5 + BitVec.ofNat 64 (16 * j)) (tweakOf s) ∧
      tweakOf s' = mulA128 (tweakOf s) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.setV b (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (16 * j)) 128)
  let s₂ := s₁.setV .v31 (ofVDwords (s.gpr .x14) (s.gpr .x14))
  let s₃ := s₂.setV .v31 (setLane (ofVDwords (s.gpr .x14) (s.gpr .x14)) 64 1 (s.gpr .x15))
  let s₄ : State := { s₃ with mem := s.mem.write (s.gpr .x5 + BitVec.ofNat 64 (16 * j)) 16 (tweakOf s) }
  let s₅ := s₄.setV b (s₄.v b ^^^ s₄.v .v31)
  obtain e₃ : s₃.v .v31 = tweakOf s := by simp [s₃, setV_v_self, setLane_dup]
  obtain x₁ : exec (.ldrq b .x2 (16 * j)) s = some s₁ := exec_ldrq ⟨by omega_arith, by omega_arith⟩ hld
  have x₂ : exec (.vop (.dup .d2 .v31 .x14)) s₁ = some s₂ := rfl
  obtain x₃ : exec (.vop (.ins .d2 .v31 1 .x15)) s₂ = some s₃ := by
    simp only [exec, VOp.eval, s₂, setV_v_self]; rfl
  obtain x₄ : exec (.strq .v31 .x5 (16 * j)) s₃ = some s₄ := by
    rw [exec_strq ⟨by omega_arith, by omega_arith⟩ (by simpa [s₃, s₂, s₁, State.setV] using hst), e₃]; rfl
  have x₅ : exec (.vop (.logic .eor b b .v31)) s₄ = some s₅ := rfl
  obtain h1 : runBlock isa (pre1 b j) s = runBlock isa mulA s₅ := by
    simp only [pre1, List.cons_append, List.nil_append, runBlock_cons]
    simp only [isa, x₁, runStep_some, runBlock_cons, x₂, x₃, x₄, x₅]
  obtain ⟨s', hr, ht, hg, hv, hm, hsp, hrd, hwr⟩ := mulA_run s₅
  have tw₅ : tweakOf s₅ = tweakOf s := rfl
  refine ⟨s', h1 ▸ hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv]; simp only [s₅, setV_v_self]
    rw [e₃]; simp [s₄, s₃, s₂, s₁, State.setV, hb]
  · intro r h₁ h₂; rw [hv]; simp [s₅, s₄, s₃, s₂, s₁, State.setV, h₁, h₂]
  · rw [hm, ← write16]; rfl
  · rw [ht, tw₅]
  · intro r h₁ h₂ h₃ h₄; rw [hg r h₁ h₂ h₃ h₄]; rfl
  · rw [hsp]; rfl
  · rw [hrd]; rfl
  · rw [hwr]; rfl

theorem twW_mulA (t : BitVec 128) : ∀ k, twW (mulA128 t) k = twW t (k + 1)
  | 0 => rfl
  | k + 1 => by rw [twW_succ, twW_mulA t k, ← twW_succ]

/-- `pre rs j`, from the data blocks `D + 16 (j + k)` and with the tweaks
saved at `S + 16 (j + k)`. -/
theorem pre_ok (D S : Addr) (hS : S.toNat + 128 ≤ 2 ^ 64) :
    ∀ (rs : List VReg) (j : Nat) (s : State), rs.Nodup → .v31 ∉ rs → j + rs.length ≤ 8 →
    s.gpr .x2 = D → s.gpr .x5 = S →
    (∀ k < rs.length, InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 (16 * (j + k))) 16) →
    (∀ k < rs.length, InRegions s.wr (S + BitVec.ofNat 64 (16 * (j + k))) 16) →
    (∀ k < rs.length, Region.Disjoint ⟨D + BitVec.ofNat 64 (16 * (j + k)), 16⟩ ⟨S, 128⟩) →
    WP isa (.block (pre rs j)) s fun s' =>
      (∀ k (h : k < rs.length), s'.v rs[k] =
        s.mem.readW (D + BitVec.ofNat 64 (16 * (j + k))) 128 ^^^ twW (tweakOf s) k) ∧
      (∀ k < rs.length, s'.mem.readW (S + BitVec.ofNat 64 (16 * (j + k))) 128 = twW (tweakOf s) k) ∧
      Frame [⟨S + BitVec.ofNat 64 (16 * j), 16 * rs.length⟩] s.mem s'.mem ∧
      tweakOf s' = twW (tweakOf s) rs.length ∧
      (∀ r, r ∉ rs → r ≠ .v31 → s'.v r = s.v r) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | [], _, s, _, _, _, _, _, _, _, _ =>
    WP.block_nil ⟨fun _ h => absurd h (by simp), fun _ h => absurd h (by simp), Frame.refl _ _, rfl,
      fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  | b :: bs, j, s, hnd, h31, hj, hx2, hx5, hld, hst, hds => by
    obtain hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    obtain hb31 : b ≠ .v31 := fun h => h31 (h ▸ List.mem_cons_self ..)
    simp only [List.length_cons] at hj
    obtain e0 : ∀ (p : Addr) (k : Nat), p + BitVec.ofNat 64 (16 * (j + 1 + k)) = p + BitVec.ofNat 64 (16 * (j + (k + 1))) :=
      fun p k => by rw [show j + 1 + k = j + (k + 1) by omega_arith]
    obtain ⟨s₁, r₁, v₁, o₁, m₁, t₁, g₁, sp₁, rd₁, wr₁⟩ := pre1_run b j s hb31 (by omega_arith)
      (by rw [hx2]; simpa using hld 0 (by simp)) (by rw [hx5]; simpa using hst 0 (by simp))
    rw [Impl.AesXts.AArch64Aes.pre, WP.block_append_iff]
    refine WP.of_runBlock ⟨s₁, r₁, ?_⟩
    obtain f₁ : Frame [⟨S + BitVec.ofNat 64 (16 * j), 16⟩] s.mem s₁.mem := by
      rw [m₁, hx5]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine WP.mono (pre_ok D S hS bs (j + 1) s₁ (List.nodup_cons.mp hnd).2 (fun h => h31 (List.mem_cons_of_mem _ h))
      (by omega_arith) (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), hx2])
      (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), hx5])
      (fun k hk => by rw [rd₁, wr₁, e0]; exact hld (k + 1) (by simp; omega_arith))
      (fun k hk => by rw [wr₁, e0]; exact hst (k + 1) (by simp; omega_arith))
      (fun k hk => by rw [e0]; exact hds (k + 1) (by simp; omega_arith)))
      fun s' ⟨v', m', f', t', o', g', sp', rd', wr'⟩ => ?_
    simp only [t₁, twW_mulA] at v' m' t'
    obtain hsl : ∀ k, k < 8 → Region.Sub ⟨S + BitVec.ofNat 64 (16 * k), 16⟩ ⟨S, 128⟩ :=
      fun k hk => Offset.sub_base S (by omega_arith)
    obtain hdj : ∀ k < bs.length + 1, Region.Disjoint ⟨D + BitVec.ofNat 64 (16 * (j + k)), 16⟩
        ⟨S + BitVec.ofNat 64 (16 * j), 16⟩ :=
      fun k hk => (hds k (by simpa using hk)).sub_right (hsl j (by omega_arith))
    refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_, fun r hr h => ?_, fun r h₁ h₂ h₃ h₄ => ?_,
      sp'.trans sp₁, rd'.trans rd₁, wr'.trans wr₁⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [o' _ hbs hb31, v₁, hx2]; rfl
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [v' k (by simpa using hk), e0,
          f₁.readW (r := ⟨D + BitVec.ofNat 64 (16 * (j + (k + 1))), 16⟩) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact hdj (k + 1) (by simpa using hk)) (by decide)]
    · cases k with
      | zero =>
        rw [Nat.add_zero, f'.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint S (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), m₁, hx5]
        exact Mem.readW_writeW_self _ _ 16 _ (by decide)
      | succ k =>
        rw [← e0]; exact m' k (by simpa using hk)
    · refine (f₁.sub fun r hr => ?_).trans (f'.sub fun r hr => ?_) <;>
        simp only [List.mem_singleton] at hr <;> subst hr <;> refine ⟨_, List.mem_singleton_self _, ?_⟩
      · exact Region.sub_prefix (by simp; omega_arith)
      · exact Offset.sub S (by omega_arith) (by simp; omega_arith)
    · rw [t', List.length_cons, Nat.add_comm]
    · simp only [List.mem_cons, not_or] at hr
      rw [o' r hr.2 h, o₁ r hr.1 h]
    · rw [g' r h₁ h₂ h₃ h₄, g₁ r h₁ h₂ h₃ h₄]

/-- `post t rs j`: each register of `rs` XORed with the tweak saved at
`S + 16 (j + k)` (`t` holding `S`) and stored to the data block `D + 16 (j + k)`. -/
theorem post_ok (t : Reg) (D S : Addr) (hS : S.toNat + 128 ≤ 2 ^ 64) :
    ∀ (rs : List VReg) (j : Nat) (s : State), rs.Nodup → .v31 ∉ rs → j + rs.length ≤ 8 →
    D.toNat + 16 * (j + rs.length) ≤ 2 ^ 64 →
    s.gpr .x2 = D → s.gpr t = S →
    (∀ k < rs.length, InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 (16 * (j + k))) 16) →
    (∀ k < rs.length, InRegions s.wr (D + BitVec.ofNat 64 (16 * (j + k))) 16) →
    (∀ k < rs.length, Region.Disjoint ⟨D + BitVec.ofNat 64 (16 * (j + k)), 16⟩ ⟨S, 128⟩) →
    WP isa (.block (post t rs j)) s fun s' =>
      (∀ k (h : k < rs.length), s'.mem.readW (D + BitVec.ofNat 64 (16 * (j + k))) 128 =
        s.v rs[k] ^^^ s.mem.readW (S + BitVec.ofNat 64 (16 * (j + k))) 128) ∧
      Frame [⟨D + BitVec.ofNat 64 (16 * j), 16 * rs.length⟩] s.mem s'.mem ∧
      (∀ r, r ∉ rs → r ≠ .v31 → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | [], _, s, _, _, _, _, _, _, _, _, _ =>
    WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | b :: bs, j, s, hnd, h31, hj, hD, hx2, hx5, hld, hst, hds => by
    obtain hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    obtain hb31 : b ≠ .v31 := fun h => h31 (h ▸ List.mem_cons_self ..)
    simp only [List.length_cons] at hj hD
    obtain e0 : ∀ (p : Addr) (k : Nat), p + BitVec.ofNat 64 (16 * (j + 1 + k)) = p + BitVec.ofNat 64 (16 * (j + (k + 1))) :=
      fun p k => by rw [show j + 1 + k = j + (k + 1) by omega_arith]
    let T := s.mem.readW (S + BitVec.ofNat 64 (16 * j)) 128
    let s₁ := s.setV .v31 T
    let s₂ := s₁.setV b (s₁.v b ^^^ s₁.v .v31)
    let s₃ : State := { s₂ with mem := s.mem.write (D + BitVec.ofNat 64 (16 * j)) 16 (s.v b ^^^ T) }
    obtain x₁ : exec (.ldrq .v31 t (16 * j)) s = some s₁ := by
      rw [exec_ldrq ⟨by omega_arith, by omega_arith⟩ (by rw [hx5]; simpa using hld 0 (by simp)), hx5]
    have x₂ : exec (.vop (.logic .eor b b .v31)) s₁ = some s₂ := rfl
    obtain v₂ : s₂.v b = s.v b ^^^ T := by
      simp [s₂, s₁, State.setV, hb31]
    obtain x₃ : exec (.strq b .x2 (16 * j)) s₂ = some s₃ := by
      rw [exec_strq ⟨by omega_arith, by omega_arith⟩ (by simpa [s₂, s₁, State.setV, hx2] using hst 0 (by simp)), v₂]
      simp only [s₂, s₁, State.setV, hx2]; rfl
    rw [Impl.AesXts.AArch64Aes.post, Impl.AesXts.AArch64Aes.post1, WP.block_append_iff]
    refine WP.of_runBlock ⟨s₃, by simp only [runBlock_cons, isa, x₁, runStep_some,
      x₂, x₃, runBlock_nil], ?_⟩
    obtain hsl : ∀ k, k < 8 → Region.Sub ⟨S + BitVec.ofNat 64 (16 * k), 16⟩ ⟨S, 128⟩ :=
      fun k hk => Offset.sub_base S (by omega_arith)
    obtain f₃ : Frame [⟨D + BitVec.ofNat 64 (16 * j), 16⟩] s.mem s₃.mem := by
      rw [show s₃.mem = s.mem.writeW (D + BitVec.ofNat 64 (16 * j)) (s.v b ^^^ T) from (write16 _ _ _)]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    obtain hT : ∀ k, k < bs.length + 1 → s₃.mem.readW (S + BitVec.ofNat 64 (16 * (j + k))) 128 =
        s.mem.readW (S + BitVec.ofNat 64 (16 * (j + k))) 128 := fun k hk =>
      f₃.readW (r := ⟨S + BitVec.ofNat 64 (16 * (j + k)), 16⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ((hds 0 (by simp)).sub_right (hsl (j + k) (by omega_arith))).symm) (by decide)
    refine WP.mono (post_ok t D S hS bs (j + 1) s₃ (List.nodup_cons.mp hnd).2 (fun h => h31 (List.mem_cons_of_mem _ h))
      (by omega_arith) (by omega_arith) (by simpa [s₃, s₂, s₁, State.setV] using hx2)
      (by simpa [s₃, s₂, s₁, State.setV] using hx5)
      (fun k hk => by rw [e0]; simpa [s₃, s₂, s₁, State.setV] using hld (k + 1) (by simp; omega_arith))
      (fun k hk => by rw [e0]; simpa [s₃, s₂, s₁, State.setV] using hst (k + 1) (by simp; omega_arith))
      (fun k hk => by rw [e0]; exact hds (k + 1) (by simp; omega_arith)))
      fun s' ⟨d', f', o', g', sp', rd', wr'⟩ => ?_
    refine ⟨fun k hk => ?_, ?_, fun r hr h => ?_, ?_, ?_, ?_, ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [f'.readW (r := ⟨D + BitVec.ofNat 64 (16 * j), 16⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint D (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
        exact (congrArg (fun m : Mem => m.readW _ 128) (write16 _ _ _)).trans
          (Mem.readW_writeW_self _ _ 16 _ (by decide))
      | succ k =>
        simp only [List.getElem_cons_succ]
        obtain hk' : k < bs.length := by simpa using hk
        rw [← e0, d' k hk', e0, hT (k + 1) (by simpa using hk)]
        obtain hv : s₃.v bs[k] = s.v bs[k] := by
          obtain hne : bs[k] ≠ b := fun h => hbs (h ▸ List.getElem_mem _)
          obtain hne' : bs[k] ≠ .v31 := fun h => h31 (h ▸ List.mem_cons_of_mem _ (List.getElem_mem _))
          simp [s₃, s₂, s₁, State.setV, hne, hne']
        rw [hv]
    · refine (f₃.sub fun r hr => ?_).trans (f'.sub fun r hr => ?_) <;>
        simp only [List.mem_singleton] at hr <;> subst hr <;> refine ⟨_, List.mem_singleton_self _, ?_⟩
      · exact Region.sub_prefix (by simp; omega_arith)
      · exact Offset.sub D (by omega_arith) (by simp; omega_arith)
    · simp only [List.mem_cons, not_or] at hr
      rw [o' r hr.2 h]; simp [s₃, s₂, s₁, State.setV, hr.1, h]
    · rw [g']; rfl
    · rw [sp']; rfl
    · rw [rd']; rfl
    · rw [wr']; rfl

/-- `preL rs j`: each register of `rs` loaded from the data block
`D + 16 (j + k)` and XORed with the tweak at `S + 16 (j + k)` (`x12`
holding `S`). -/
theorem preL_ok (D S : Addr) :
    ∀ (rs : List VReg) (j : Nat) (s : State), rs.Nodup → .v31 ∉ rs → j + rs.length ≤ 8 →
    s.gpr .x2 = D → s.gpr .x12 = S →
    (∀ k < rs.length, InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 (16 * (j + k))) 16) →
    (∀ k < rs.length, InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 (16 * (j + k))) 16) →
    WP isa (.block (preL rs j)) s fun s' =>
      (∀ k (h : k < rs.length), s'.v rs[k] =
        s.mem.readW (D + BitVec.ofNat 64 (16 * (j + k))) 128 ^^^
          s.mem.readW (S + BitVec.ofNat 64 (16 * (j + k))) 128) ∧
      (∀ r, r ∉ rs → r ≠ .v31 → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | [], _, s, _, _, _, _, _, _, _ =>
    WP.block_nil ⟨fun _ h => absurd h (by simp), fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  | b :: bs, j, s, hnd, h31, hj, hx2, hx12, hld, hlt => by
    obtain hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    obtain hb31 : b ≠ .v31 := fun h => h31 (h ▸ List.mem_cons_self ..)
    simp only [List.length_cons] at hj
    obtain e0 : ∀ (p : Addr) (k : Nat), p + BitVec.ofNat 64 (16 * (j + 1 + k)) = p + BitVec.ofNat 64 (16 * (j + (k + 1))) :=
      fun p k => by rw [show j + 1 + k = j + (k + 1) by omega_arith]
    let d := s.mem.readW (D + BitVec.ofNat 64 (16 * j)) 128
    let T := s.mem.readW (S + BitVec.ofNat 64 (16 * j)) 128
    let s₁ := s.setV b d
    let s₂ := s₁.setV .v31 T
    let s₃ := s₂.setV b (s₂.v b ^^^ s₂.v .v31)
    obtain x₁ : exec (.ldrq b .x2 (16 * j)) s = some s₁ := by
      rw [exec_ldrq ⟨by omega_arith, by omega_arith⟩ (by rw [hx2]; simpa using hld 0 (by simp)), hx2]
    obtain x₂ : exec (.ldrq .v31 .x12 (16 * j)) s₁ = some s₂ := by
      rw [exec_ldrq ⟨by omega_arith, by omega_arith⟩ (by simpa [s₁, State.setV, hx12] using hlt 0 (by simp))]
      simp [s₁, State.setV, hx12, s₂, T]
    have x₃ : exec (.vop (.logic .eor b b .v31)) s₂ = some s₃ := rfl
    rw [preL, preL1, WP.block_append_iff]
    refine WP.of_runBlock ⟨s₃, by simp only [runBlock_cons, isa, x₁, runStep_some, x₂, x₃, runBlock_nil], ?_⟩
    obtain v₃ : s₃.v b = d ^^^ T := by simp [s₃, s₂, s₁, State.setV, hb31]
    have g₃ : s₃.gpr = s.gpr := rfl
    have m₃ : s₃.mem = s.mem := rfl
    refine WP.mono (preL_ok D S bs (j + 1) s₃ (List.nodup_cons.mp hnd).2 (fun h => h31 (List.mem_cons_of_mem _ h))
      (by omega_arith) (by rw [g₃, hx2]) (by rw [g₃, hx12])
      (fun k hk => by rw [e0]; exact hld (k + 1) (by simp; omega_arith))
      (fun k hk => by rw [e0]; exact hlt (k + 1) (by simp; omega_arith)))
      fun s' ⟨v', o', g', m', sp', rd', wr'⟩ => ?_
    refine ⟨fun k hk => ?_, fun r hr h => ?_, g'.trans g₃, m'.trans m₃, sp', rd', wr'⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [o' _ hbs hb31, v₃]
      | succ k =>
        simp only [List.getElem_cons_succ]
        obtain hk' : k < bs.length := by simpa using hk
        rw [v' k hk', m₃, e0, e0]
    · simp only [List.mem_cons, not_or] at hr
      rw [o' r hr.2 h]; simp [s₃, s₂, s₁, State.setV, hr.1, h]

/-- The tweak in `lo`, `hi` stored as two words at `a`, read as one. -/
theorem readW_store2 (m : Mem) (a : Addr) (lo hi : BitVec 64) :
    ((m.writeW a lo).writeW (a + BitVec.ofNat 64 8) hi).readW a 128 = hi ++ lo := by
  obtain hs : Mem.Sep a (64 / 8) (a + BitVec.ofNat 64 8) (64 / 8) := by
    have := Offset.sep a (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)
    simpa using this
  rw [readW128, Mem.readW_writeW_self64, Mem.readW_writeW_sep hs (by decide), Mem.readW_writeW_self64]

/-- `genStep r j`: the tweak stored at `S + 16 j` (`r` holding `S`), and
multiplied by `α`. -/
theorem genStep_run (r : Reg) (S : Addr) (j : Nat) (s : State) (hj : j < 8) (hr : s.gpr r = S)
    (in0 : InRegions s.wr (S + BitVec.ofNat 64 (16 * j)) 8)
    (in8 : InRegions s.wr (S + BitVec.ofNat 64 (16 * j + 8)) 8) :
    ∃ s', runBlock isa (genStep r j) s = some s' ∧
      s'.mem = (s.mem.writeW (S + BitVec.ofNat 64 (16 * j)) (s.gpr .x14)).writeW
        (S + BitVec.ofNat 64 (16 * j + 8)) (s.gpr .x15) ∧
      tweakOf s' = mulA128 (tweakOf s) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → s'.gpr r = s.gpr r) ∧
      s'.v = s.v ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ : State := { s with mem := s.mem.writeW (S + BitVec.ofNat 64 (16 * j)) (s.gpr .x14) }
  let s₂ : State := { s₁ with mem := s₁.mem.writeW (S + BitVec.ofNat 64 (16 * j + 8)) (s.gpr .x15) }
  obtain x₁ : exec (.str .x .x14 r (16 * j)) s = some s₁ := by
    rw [exec_str_x ⟨by omega_arith, by omega_arith⟩ (by rw [hr]; exact in0), hr]
  obtain x₂ : exec (.str .x .x15 r (16 * j + 8)) s₁ = some s₂ := by
    rw [exec_str_x ⟨by omega_arith, by omega_arith⟩ (by simpa [s₁, hr] using in8)]
    simp [s₁, s₂, hr]
  obtain ⟨s', hr', ht, hg, hv, hm, hsp, hrd, hwr⟩ := mulA_run s₂
  refine ⟨s', ?_, by rw [hm], by rw [ht], fun r h1 h2 h3 h4 => by rw [hg r h1 h2 h3 h4],
    by rw [hv], by rw [hsp], by rw [hrd], by rw [hwr]⟩
  rw [genStep, List.cons_append, List.cons_append, List.nil_append]
  simp only [runBlock_cons, isa, x₁, runStep_some, x₂]
  exact hr'

/-- The first `k` steps of `gen r`, from the tweak `t`: the tweaks `twW t j`
at `S + 16 j` (`r` holding `S`). -/
theorem gen_ok (r : Reg) (S : Addr) (hS : S.toNat + 128 ≤ 2 ^ 64) (h9 : r ≠ .x9) (h10 : r ≠ .x10)
    (h14 : r ≠ .x14) (h15 : r ≠ .x15) (s : State) (hr : s.gpr r = S)
    (hin : ∀ d, d + 8 ≤ 128 → InRegions s.wr (S + BitVec.ofNat 64 d) 8) :
    ∀ k ≤ 8, WP isa (.block ((List.range k).flatMap (genStep r))) s fun s' =>
      (∀ j < k, s'.mem.readW (S + BitVec.ofNat 64 (16 * j)) 128 = twW (tweakOf s) j) ∧
      Frame [⟨S, 128⟩] s.mem s'.mem ∧ tweakOf s' = twW (tweakOf s) k ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → s'.gpr r = s.gpr r) ∧
      s'.v = s.v ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (by omega_arith), Frame.refl _ _, rfl, fun _ _ _ _ _ => rfl, rfl, rfl, rfl,
      rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (gen_ok r S hS h9 h10 h14 h15 s hr hin k (by omega_arith))
      fun s₁ ⟨e₁, f₁, t₁, g₁, v₁, sp₁, rd₁, wr₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    obtain ⟨s', r', m', t', g', v', sp', rd', wr'⟩ := genStep_run r S k s₁ (by omega_arith)
      (by rw [g₁ r h9 h10 h14 h15, hr]) (by rw [wr₁]; exact hin _ (by omega_arith))
      (by rw [wr₁]; exact hin _ (by omega_arith))
    refine WP.of_runBlock ⟨s', r', ?_⟩
    obtain hsep : ∀ j < k, Region.Disjoint ⟨S + BitVec.ofNat 64 (16 * j), 16⟩ ⟨S + BitVec.ofNat 64 (16 * k), 16⟩ :=
      fun j hj => Offset.disjoint S (by omega_arith) (by omega_arith) (by omega_arith)
    obtain fk : Frame [⟨S + BitVec.ofNat 64 (16 * k), 16⟩] s₁.mem s'.mem := by
      rw [m']
      obtain c0 : Region.Contains ⟨S + BitVec.ofNat 64 (16 * k), 16⟩ (S + BitVec.ofNat 64 (16 * k)) (64 / 8) := by
        have := Offset.contains_base (S + BitVec.ofNat 64 (16 * k)) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
        simpa using this
      obtain c8 : Region.Contains ⟨S + BitVec.ofNat 64 (16 * k), 16⟩ (S + BitVec.ofNat 64 (16 * k + 8)) (64 / 8) := by
        rw [← Offset.add_add_eq S (show 16 * k + 8 = 16 * k + 8 from rfl)]
        exact Offset.contains_base _ (d := 8) (n := 8) (k := 16) (by decide) (by decide)
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c8
    refine ⟨fun j hj => ?_, ?_, by rw [t', t₁]; rfl, fun r h1 h2 h3 h4 => by rw [g' r h1 h2 h3 h4, g₁ r h1 h2 h3 h4],
      v'.trans v₁, sp'.trans sp₁, rd'.trans rd₁, wr'.trans wr₁⟩
    · by_cases hjk : j = k
      · subst hjk
        rw [m', ← Offset.add_add_eq S (show 16 * j + 8 = 16 * j + 8 from rfl), readW_store2, ← tweakOf, t₁]
      · rw [fk.readW (r := ⟨S + BitVec.ofNat 64 (16 * j), 16⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hsep j (by omega_arith)) (by decide), e₁ j (by omega_arith)]
    · exact f₁.trans (fk.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub_base S (by omega_arith)⟩)

end VG.Proof.AesXts.AArch64.Aes

end

end


/-!
# One-pass XTS-AES on AArch64: a group of blocks

The loops keep `XInv B enc s₀ c p`: after `c` blocks, with the data pointer
and the number of blocks left at block `p` (`p = c` but between a group and
its advance), the tweak of block `c` in `x14` and `x15` (`twW`), the round
keys as `B` needs them, and the first `c` data blocks replaced with their
XTS (`outB`), the others as they were. `group_ok`: a group of blocks
(`[v0]`, after the eight-block groups of `Group8.lean`) through `B` takes it
from `c` to `c + N`, by `pre_ok`, `B.ok` and `post_ok`; `xts_word` gives
each block.
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Aes

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesXts (b16)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.AArch64 (W R Iv Dp N S schR ivR dataR scrR UPre blk wK iv0)
open VG.Proof.Aes.AArch64.Aese (BlockFn BlockRegs VFrame st)
open VG.Impl.AesXts.AArch64Aes (pre post blk1)
open VG.Proof.Aes.AArch64.Aese (ushr3 eval_zero eval_nonzero)
open VG.Impl.Aes.AArch64.Aese (regs8)

/-- The tweak at the start, as a word. -/
abbrev tw0 (s₀ : State) : BitVec 128 := s₀.mem.readW (Iv s₀) 128

/-- Block `k` after XTS. -/
abbrev outB (enc : Bool) (s₀ : State) (k : Nat) : List Byte :=
  Spec.Xts.block (ciphOf enc (R s₀) (wK s₀)) (Spec.Xts.next (iv0 s₀) k) (bytesAt s₀.mem (blk s₀ k) 16)

/-- After `c` blocks, with the data pointer and count at block `p`. -/
structure XInv (B : BlockFn) (enc : Bool) (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ N s₀
  keys : B.K (R s₀) (wK s₀) s
  x2 : s.gpr .x2 = blk s₀ p
  x3 : s.gpr .x3 = BitVec.ofNat 64 (N s₀ - p)
  x5 : s.gpr .x5 = S s₀
  x11 : s.gpr .x11 = Iv s₀
  tw : tweakOf s = twW (tw0 s₀) c
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀, scrR s₀] s₀.mem s.mem
  data : ∀ k < N s₀, bytesAt s.mem (blk s₀ k) 16 =
    if k < c then outB enc s₀ k else bytesAt s₀.mem (blk s₀ k) 16

theorem twW_add (t : BitVec 128) (c : Nat) : ∀ k, twW (twW t c) k = twW t (c + k)
  | 0 => rfl
  | k + 1 => by rw [twW_succ, twW_add t c k, ← twW_succ]; rfl

theorem iv0_b16 (s₀ : State) : iv0 s₀ = b16 (tw0 s₀) := bytesAt_b16 _ _

theorem bregs (rs : List VReg) (h : rs = regs8 ∨ rs = [.v0]) :
    BlockRegs rs ∧ .v31 ∉ rs ∧ rs.length ≤ 8 ∧ BlockRegs (rs ++ ([.v31] : List VReg)) := by
  rcases h with rfl | rfl <;> exact ⟨⟨by decide, by decide⟩, by decide, by decide, ⟨by decide, by decide⟩⟩

/-- Blocks `c … c + N − 1` (`N` the number of registers) through `B`, the
pointer not yet advanced. -/
theorem group_ok (B : BlockFn) (enc : Bool) (hF : B.F = stF enc) {s₀ : State} (hp : UPre s₀)
    (rs : List VReg) (hrs : rs = regs8 ∨ rs = [.v0]) (adv : List Instr) {Q : State → Prop} {c : Nat}
    (hc : c + rs.length ≤ N s₀) {s : State} (hI : XInv B enc s₀ c c s)
    (hQ : ∀ s', XInv B enc s₀ (c + rs.length) c s' → WP isa (.block adv) s' Q) :
    WP isa (.seq (.block (pre rs 0)) (.seq (B.f rs) (.block (post .x5 rs 0 ++ adv)))) s Q := by
  obtain ⟨hbr, h31, hlen, hbr31⟩ := bregs rs hrs
  have hdw := hp.data_wrap
  obtain hpos : 0 < rs.length := by rcases hrs with rfl | rfl <;> decide
  have hsw := hp.scr_wrap
  obtain hW : s.wr = [Iv s₀ |> fun a => (⟨a, 16⟩ : Region), dataR s₀, scrR s₀] := by rw [hI.wr, hp.wr]
  obtain eb : ∀ k, blk s₀ c + BitVec.ofNat 64 (16 * (0 + k)) = blk s₀ (c + k) := fun k =>
    Offset.add_add_eq _ (by omega_arith)
  obtain inD : ∀ k < rs.length, (dataR s₀).Contains (blk s₀ c + BitVec.ofNat 64 (16 * (0 + k))) 16 :=
    fun k hk => by rw [eb]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain inS : ∀ k < rs.length, (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 (16 * (0 + k))) 16 :=
    fun k hk => Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain dS : ∀ k < rs.length, Region.Disjoint ⟨blk s₀ c + BitVec.ofNat 64 (16 * (0 + k)), 16⟩ ⟨S s₀, 128⟩ :=
    fun k hk => by
      rw [eb]
      exact (hp.data_scr.sub_left (UPre.data_sub (by omega_arith))).sub_right (Region.sub_prefix (by decide))
  -- The tweaks XORed in.
  refine WP.seq (WP.mono (pre_ok (blk s₀ c) (S s₀) (by omega_arith) rs 0 s hbr.1 h31 (by omega_arith) hI.x2 hI.x5
    (fun k hk => ⟨dataR s₀, by rw [hW]; simp, inD k hk⟩)
    (fun k hk => ⟨scrR s₀, by rw [hW]; simp, inS k hk⟩) dS)
    fun s₁ ⟨v₁, m₁, f₁, t₁, o₁, g₁, sp₁, rd₁, wr₁⟩ => ?_)
  obtain hK₁ := B.of_v hI.keys hbr31 (fun r hr => o₁ r (fun h => hr (List.mem_append_left _ h))
    (fun h => hr (h ▸ List.mem_append_right _ (List.mem_singleton_self _))))
    (g₁ _ (by decide) (by decide) (by decide) (by decide)) (g₁ _ (by decide) (by decide) (by decide) (by decide))
  -- The rounds.
  refine WP.seq (WP.mono (B.ok hbr hK₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  -- The tweaks XORed in again, and the blocks stored.
  rw [WP.block_append_iff]
  obtain g₂ : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → s₂.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [f₂.gpr, g₁ r h1 h2 h3 h4]
  obtain hW₂ : s₂.wr = [Iv s₀ |> fun a => (⟨a, 16⟩ : Region), dataR s₀, scrR s₀] := by rw [f₂.wr, wr₁, hW]
  refine WP.mono (post_ok .x5 (blk s₀ c) (S s₀) (by omega_arith) rs 0 s₂ hbr.1 h31 (by omega_arith)
    (by rw [hp.blk_toNat (k := c) (by omega_arith)]; omega_arith)
    (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), hI.x2])
    (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), hI.x5])
    (fun k hk => ⟨scrR s₀, by rw [f₂.rd, rd₁, hI.rd, hp.rd, hW₂]; simp, inS k hk⟩)
    (fun k hk => ⟨dataR s₀, by rw [hW₂]; simp, inD k hk⟩) dS)
    fun s₃ ⟨d₃, f₃, o₃, g₃, sp₃, rd₃, wr₃⟩ => hQ s₃ ?_
  obtain g₃' : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₃, g₂ r h1 h2 h3 h4]
  have m₂ : s₂.mem = s₁.mem := f₂.mem
  obtain tw₃ : tweakOf s₃ = twW (tw0 s₀) (c + rs.length) := by
    rw [tweakOf, g₃, f₂.gpr, ← tweakOf, t₁, hI.tw, twW_add]
  obtain hsl : Region.Sub ⟨S s₀ + BitVec.ofNat 64 (16 * 0), 16 * rs.length⟩ (scrR s₀) :=
    UPre.scr_sub (by omega_arith)
  obtain hdl : Region.Sub ⟨blk s₀ c + BitVec.ofNat 64 (16 * 0), 16 * rs.length⟩ (dataR s₀) := by
    rw [Nat.mul_zero, BitVec.add_zero, blk]
    exact Offset.sub_base _ (by omega_arith)
  refine ⟨by omega_arith, ?_, by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), hI.x2],
    by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), hI.x3],
    by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), hI.x5],
    by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), hI.x11], tw₃,
    by rw [rd₃, f₂.rd, rd₁, hI.rd], by rw [wr₃, f₂.wr, wr₁, hI.wr], ?_, fun k hk => ?_⟩
  · exact B.of_v (B.of_v hK₁ hbr f₂.v (by rw [f₂.gpr]) (by rw [f₂.gpr])) hbr31
      (fun r hr => o₃ r (fun h => hr (List.mem_append_left _ h))
        (fun h => hr (h ▸ List.mem_append_right _ (List.mem_singleton_self _)))) (by rw [g₃]) (by rw [g₃])
  · refine hI.frame.trans ((f₁.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, hsl⟩
    · rw [← m₂]
      exact f₃.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, hdl⟩
  · by_cases hin : c ≤ k ∧ k < c + rs.length
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + i := ⟨k - c, by omega_arith⟩
      obtain hi : i < rs.length := by omega_arith
      obtain e := d₃ i hi
      rw [eb] at e
      rw [bytesAt_b16, e, m₂]
      obtain mi := m₁ i hi
      rw [hI.tw, twW_add] at mi
      rw [mi]
      obtain vi := v₁ i hi
      rw [eb, hI.tw, twW_add] at vi
      obtain hc' : st (s₂.v rs[i]) = stF enc (R s₀) (wK s₀)
          (st (s.mem.readW (blk s₀ (c + i)) 128 ^^^ twW (tw0 s₀) (c + i))) := by
        rw [e₂ _ (List.getElem_mem hi), vi, hF]
      rw [xts_word enc (R s₀) (wK s₀) _ _ _ hc', b16_twW, ← iv0_b16, ← bytesAt_b16, hI.data _ hk]
      simp only [show ¬ c + i < c by omega_arith, ite_false, show c + i < c + rs.length by omega_arith, ite_true]
    · have hk' : ¬ (c ≤ k ∧ k < c + rs.length) := hin
      rw [Proof.Cmac.bytesAt_frame16 f₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [Nat.mul_zero, BitVec.add_zero, blk, blk]
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)),
        m₂, Proof.Cmac.bytesAt_frame16 f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right hsl), hI.data k hk]
      by_cases hkc : k < c
      · simp only [hkc, ite_true, show k < c + rs.length by omega_arith]
      · simp only [hkc, ite_false, show ¬ k < c + rs.length by omega_arith]


/-! ## The loops -/

/-- `s'` is `s` but for `x2`, `x3` and `x13`. -/
theorem XInv.adv {B : BlockFn} {enc : Bool} {s₀ : State} {c p : Nat} {s s' : State}
    (h : XInv B enc s₀ c p s) (p' : Nat) (hx2 : s'.gpr .x2 = blk s₀ p')
    (hx3 : s'.gpr .x3 = BitVec.ofNat 64 (N s₀ - p'))
    (g : ∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x13 → s'.gpr r = s.gpr r) (hv : s'.v = s.v) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : XInv B enc s₀ c p' s' :=
  ⟨h.le, B.of_v h.keys (vs := []) ⟨List.nodup_nil, by simp⟩ (fun _ _ => by rw [hv])
      (g _ (by decide) (by decide) (by decide)) (g _ (by decide) (by decide) (by decide)),
    hx2, hx3, by rw [g _ (by decide) (by decide) (by decide), h.x5],
    by rw [g _ (by decide) (by decide) (by decide), h.x11],
    by rw [tweakOf, g _ (by decide) (by decide) (by decide), g _ (by decide) (by decide) (by decide)]; exact h.tw,
    by rw [hrd, h.rd], by rw [hwr, h.wr], by rw [hm]; exact h.frame, fun k hk => by rw [hm]; exact h.data k hk⟩

theorem blk1_ok (B : BlockFn) (enc : Bool) (hF : B.F = stF enc) {s₀ : State} (hp : UPre s₀) {c : Nat}
    (hc : c + 1 ≤ N s₀) {s : State} (hI : XInv B enc s₀ c c s) :
    WP isa (blk1 B.f) s (XInv B enc s₀ (c + 1) (c + 1)) := by
  have hn := hp.data_wrap
  refine group_ok B enc hF hp [.v0] (.inr rfl) _ hc hI fun s₁ h₁ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  refine h₁.adv (c + 1) ?_ ?_ (fun r h2 h3 _ => by simp [State.write, h2, h3]) rfl rfl rfl rfl
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, h₁.x2]
    exact Offset.add_add_eq _ (by omega_arith)
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, h₁.x3]
    rw [Offset.ofNat_sub_ofNat (by omega_arith), show N s₀ - c - 1 = N s₀ - (c + 1) by omega_arith]

/-- The one-block loop, for the fewer than eight blocks left. -/
theorem loop1_ok (B : BlockFn) (enc : Bool) (hF : B.F = stF enc) {s₀ : State} (hp : UPre s₀) {c : Nat}
    {s₂ : State} (hc : N s₀ - c < 8) (hI₂ : XInv B enc s₀ c c s₂) :
    WP isa (.ite (.zero .x .x3) (.block []) (.loop (blk1 B.f) (.nonzero .x .x3))) s₂
      (XInv B enc s₀ (N s₀) (N s₀)) := by
  obtain hn : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  refine WP.ite (decide (N s₀ - c = 0)) (eval_zero hI₂.x3 (by omega_arith)) (fun h => ?_) (fun h => ?_)
  · have : c = N s₀ := by have := hI₂.le; simp at h; omega_arith
    exact WP.block_nil (this ▸ hI₂)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = N s₀ - c ∧ c < N s₀ ∧ XInv B enc s₀ c c s
    obtain hstep : ∀ m s, I1 m s → WP isa (blk1 B.f) s (fun s' =>
        (AArch64.eval (.nonzero .x .x3) s' = some false ∧ XInv B enc s₀ (N s₀) (N s₀) s') ∨
        (AArch64.eval (.nonzero .x .x3) s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (blk1_ok B enc hF hp hc hI) fun s' hI' => ?_
      rw [eval_nonzero hI'.x3 (by omega_arith)]
      by_cases hlast : N s₀ - (c + 1) = 0
      · have : c + 1 = N s₀ := by omega_arith
        exact .inl ⟨by simp [hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [hlast], N s₀ - (c + 1), by omega_arith, c + 1, rfl, by omega_arith, hI'⟩
    obtain hlt : c < N s₀ := by have := hI₂.le; simp at h; omega_arith
    exact WP.loop (M := isa) I1 hstep (N s₀ - c) s₂ ⟨c, rfl, hlt, hI₂⟩

end VG.Proof.AesXts.AArch64.Aes

end

end

/-! ### `AesXts.AArch64.Aes.Setup`, which only this module used -/

section

/-!
# One-pass XTS-AES on AArch64: the setup

`enter_ok`: the arguments moved where the round code of
`vg_aes_encrypt_blocks_aes` expects them, and the tweak loaded into `x14` and
`x15`. `encSetup_ok`, `decSetup_ok`: the round keys loaded as `aes` and
`aesDec` need them (`Keys`, `DKeys`), as `Aese.encSetup_ok` and
`Aese.decSetup_ok` show for the block functions, from a state whose
schedule at `x0` is readable and `x3` the number of blocks: so `XInv … 0 0`
holds after `enter ++ setup` (`setup_ok`).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Aes

open VG VG.AArch64
open VG.Spec.Aes (bytesAt roundKey)
open VG.Proof.AesCbc.AArch64 (W R Iv Dp N S schR ivR dataR scrR UPre blk wK iv0)
open VG.Proof.Aes.AArch64.Aese
open VG.Impl.Aes.AArch64.Aese (keysCommon encSetup decSetup kreg dreg)
open VG.Impl.AesXts.AArch64Aes (enter)

/-- What the key setups need of the state: the schedule at `x0` readable,
and `x1` a number of rounds. -/
structure KPre (s : State) : Prop where
  key_in : ∀ {o : Nat}, o + 16 ≤ 240 → InRegions (s.rd ++ s.wr) (bkp s + BitVec.ofNat 64 o) 16
  rounds : bnr s = 10 ∨ bnr s = 12 ∨ bnr s = 14

theorem common_ok' {s₀ : State} (hp : KPre s₀) : WP isa (.block keysCommon) s₀ (Common s₀) := by
  have hR := hp.rounds
  obtain hn : bnb s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
  obtain hx1 : s₀.gpr .x1 = BitVec.ofNat 64 (bnr s₀) := by simp [bnr]
  obtain hx3 : s₀.gpr .x3 = BitVec.ofNat 64 (bnb s₀) := by simp [bnb]
  rw [keysCommon, WP.block_append_iff]
  refine WP.mono (loads_ok s₀ (fun j hj => hp.key_in (by omega_using [hj])) 13 (Nat.le_refl _))
    fun s₁ ⟨e₁, f₁⟩ => ?_
  obtain g : ∀ r, s₁.gpr r = s₀.gpr r := fun r => f₁.gpr r (by simp)
  obtain e9 : s₁.gpr .x0 + s₁.gpr .x1 <<< 4 = bkp s₀ + BitVec.ofNat 64 (16 * bnr s₀) := by
    rw [g, g, Proof.Aes.AArch64.shl4]
  obtain rdwr : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [f₁.rd, f₁.wr]
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsl_x (sh := 4) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_add, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, e9,
      BitVec.add_zero, rdwr]
    exact hp.key_in (by omega_using [hR])), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 10) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 12) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 3) (by decide), WP.block_nil ?_⟩
  refine ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, ?_, f₁.rd, f₁.wr⟩
  · simp only [State.setV, State.write, (kreg_ne j).2, ite_false]
    rw [e₁ j hj]
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9, BitVec.add_zero, f₁.mem]
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9]
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g, hx1]; rfl
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g, hx1]; rfl
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g, hx3]
    exact ushr3 (by omega_using [hn])
  · simp only [State.setV, State.write, h1, h2, h3, h4, ite_false, g]
  · exact f₁.mem

/-- What a key setup leaves. -/
structure KPost (K : Nat → List Byte → State → Prop) (s₀ s : State) : Prop where
  keys : K (bnr s₀) (bsch s₀) s
  x13 : s.gpr .x13 = BitVec.ofNat 64 (bnb s₀ / 8)
  gpr : ∀ r, r ≠ .x9 → r ≠ .x6 → r ≠ .x7 → r ≠ .x13 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem encSetup_ok' {s₀ : State} (hp : KPre s₀) : WP isa (.block encSetup) s₀ (KPost Keys s₀) := by
  have hR := hp.rounds
  rw [encSetup, WP.block_append_iff]
  refine WP.mono (common_ok' hp) fun s₁ c₁ => ?_
  obtain e9' : bkp s₀ + BitVec.ofNat 64 (16 * bnr s₀) - BitVec.ofNat 64 16 =
      bkp s₀ + BitVec.ofNat 64 (16 * (bnr s₀ - 1)) := by
    rw [Offset.add_ofNat_sub _ (by omega_using [hR]), show 16 * bnr s₀ - 16 = 16 * (bnr s₀ - 1) by omega_using []]
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.write, State.read, ite_true, BitVec.setWidth_eq, c₁.x9,
      e9', BitVec.add_zero, c₁.rd, c₁.wr]
    exact hp.key_in (by omega_using [hR])), WP.block_nil ?_⟩
  obtain hL : ∀ j, j ≤ bnr s₀ → 16 * j + 16 ≤ 16 * (bnr s₀ + 1) := fun j hj => by omega_using [hj]
  refine ⟨⟨hR, fun j hj => ?_, ?_, ?_, ?_, ?_⟩, ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩
  · simp only [State.setV, State.write, (kreg_ne j).1, ite_false]
    rw [c₁.kreg j (by omega_using [hR, hj])]
    exact keyIs_readW _ _ (hL j (by omega_using [hj]))
  · simp only [State.setV, State.write, State.read, ite_true, BitVec.setWidth_eq, c₁.x9, e9',
      BitVec.add_zero, c₁.mem]
    exact keyIs_readW _ _ (hL _ (by omega_using []))
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.v30]
    exact keyIs_readW _ _ (hL _ (Nat.le_refl _))
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.x6]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.x7]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.x13]
  · simp only [State.setV, State.write, h1, ite_false]; exact c₁.gpr r h1 h2 h3 h4
  · simp only [State.setV, State.write, c₁.mem]
  · simp only [State.setV, State.write, c₁.rd]
  · simp only [State.setV, State.write, c₁.wr]

theorem decSetup_ok' {s₀ : State} (hp : KPre s₀) : WP isa (.block decSetup) s₀ (KPost DKeys s₀) := by
  have hR := hp.rounds
  rw [decSetup, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (common_ok' hp) fun s₁ c₁ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 208) (by decide) (by
    rw [c₁.gpr _ (by decide) (by decide) (by decide) (by decide), c₁.rd, c₁.wr]
    exact hp.key_in (by omega_using [])), WP.block_nil ?_⟩
  refine WP.mono (imcs_ok _ 13 (Nat.le_refl _)) fun s₂ ⟨e₂, o₂, g₂, m₂, rd₂, wr₂⟩ => ?_
  obtain hL : ∀ j, j ≤ bnr s₀ → 16 * j + 16 ≤ 16 * (bnr s₀ + 1) := fun j hj => by omega_using [hj]
  obtain x0 : s₁.gpr .x0 = bkp s₀ := c₁.gpr _ (by decide) (by decide) (by decide) (by decide)
  obtain pre : ∀ j, 1 ≤ j → j ≤ 13 → j < bnr s₀ →
      KeyIs ((s₁.setV .v29 (s₁.mem.readW (s₁.gpr .x0 + BitVec.ofNat 64 208) 128)).v (dreg j))
        (roundKey (bsch s₀) j) := by
    intro j h1 h2 h3
    by_cases h13 : j = 13
    · subst h13
      simp only [Impl.Aes.AArch64.Aese.dreg, ite_true, setV_v_self, x0, c₁.mem]
      have := keyIs_readW s₀.mem (bkp s₀) (L := 16 * (bnr s₀ + 1)) (j := 13) (hL 13 (by omega_using [h3]))
      simpa using this
    · simp only [Impl.Aes.AArch64.Aese.dreg, h13, ite_false]
      rw [setV_v_of_ne _ _ (kreg_ne j).1, c₁.kreg j (by omega_using [h2, h13])]
      exact keyIs_readW _ _ (hL j (by omega_using [h3]))
  refine ⟨⟨hR, ?_, fun j h1 h2 => ?_, ?_, ?_, ?_⟩, ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩
  · rw [o₂ _ fun j hj => (dreg_ne j hj).1.symm, setV_v_of_ne _ _ (by decide), c₁.v30]
    exact keyIs_readW _ _ (hL _ (Nat.le_refl _))
  · have hj13 : j ≤ 13 := by omega_using [hR, h2]
    have := e₂ (j - 1) (by omega_using [hj13])
    rw [show j - 1 + 1 = j by omega_using [h1], ite_eq_left (by omega_using [hj13])] at this
    rw [this]
    exact keyIs_aesimc (pre j h1 hj13 h2)
  · rw [o₂ _ fun j hj => (dreg_ne j hj).2.symm, setV_v_of_ne _ _ (by decide)]
    have := c₁.kreg 0 (by omega_using [])
    simp only [Impl.Aes.AArch64.Aese.kreg] at this
    rw [this]
    exact keyIs_readW _ _ (hL 0 (by omega_using []))
  · rw [g₂]; simp only [State.setV]; exact c₁.x6
  · rw [g₂]; simp only [State.setV]; exact c₁.x7
  · rw [g₂]; simp only [State.setV, c₁.x13]
  · rw [g₂]; simp only [State.setV]; exact c₁.gpr r h1 h2 h3 h4
  · rw [m₂]; simp only [State.setV, c₁.mem]
  · rw [rd₂]; simp only [State.setV, c₁.rd]
  · rw [wr₂]; simp only [State.setV, c₁.wr]

end VG.Proof.AesXts.AArch64.Aes

end

end

/-! ### `AesXts.AArch64.Aes.Group8`, which only this module used -/

section

/-!
# One-pass XTS-AES on AArch64: the eight-block groups

The eight-block loop keeps `YInv B enc s₀ c`: after `c` blocks, as `XInv`
says of the data, the pointers and the round keys, but with the tweaks a
group ahead: those of blocks `c … c + 7` in the bank at `x12` (one of
`scratch` and `scratch + 128`, the other at `x8`), and that of block
`c + 8` in `x14` and `x15`. `blk8_ok`: a group takes it to `c + 8`, by
`preL_ok`, `gen_ok` (the next group's tweaks, into the bank at `x8`), `B.ok`
and `post_ok`, and swaps the banks; `start8_ok` and `end8_ok` go from and
back to `XInv`, and `loop8_ok` runs the loop.
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Aes

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesXts (b16)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.AArch64 (W R Iv Dp N S schR ivR dataR scrR UPre blk wK iv0)
open VG.Proof.Aes.AArch64.Aese (BlockFn BlockRegs VFrame st ushr3 eval_zero eval_nonzero)
open VG.Impl.AesXts.AArch64Aes (preL gen post blk8 start8 end8)
open VG.Impl.Aes.AArch64.Aese (regs8)

/-- The bank at offset `e` of the scratch buffer. -/
abbrev bank (s₀ : State) (e : Nat) : Addr := S s₀ + BitVec.ofNat 64 e

/-- After `c` blocks, with the tweaks of blocks `c … c + 7` in the bank at
`x12`, `scratch + e`, and that of block `c + 8` in `x14` and `x15`. -/
structure YInv (B : BlockFn) (enc : Bool) (s₀ : State) (c e : Nat) (s : State) : Prop where
  le : c ≤ N s₀
  keys : B.K (R s₀) (wK s₀) s
  x2 : s.gpr .x2 = blk s₀ c
  x3 : s.gpr .x3 = BitVec.ofNat 64 (N s₀ - c)
  x5 : s.gpr .x5 = S s₀
  x11 : s.gpr .x11 = Iv s₀
  he : e = 0 ∨ e = 128
  x12 : s.gpr .x12 = bank s₀ e
  x8 : s.gpr .x8 = bank s₀ (128 - e)
  cur : ∀ j < 8, s.mem.readW (bank s₀ e + BitVec.ofNat 64 (16 * j)) 128 = twW (tw0 s₀) (c + j)
  tw : tweakOf s = twW (tw0 s₀) (c + 8)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀, scrR s₀] s₀.mem s.mem
  data : ∀ k < N s₀, bytesAt s.mem (blk s₀ k) 16 =
    if k < c then outB enc s₀ k else bytesAt s₀.mem (blk s₀ k) 16

theorem banks_disj {s₀ : State} {e : Nat} (he : e = 0 ∨ e = 128) :
    Region.Disjoint ⟨bank s₀ e, 128⟩ ⟨bank s₀ (128 - e), 128⟩ :=
  Offset.disjoint _ (by omega_using [he]) (by omega_using [he]) (by omega_using [])

theorem bank_sub {s₀ : State} {e : Nat} (he : e = 0 ∨ e = 128) : Region.Sub ⟨bank s₀ e, 128⟩ (scrR s₀) :=
  Offset.sub_base _ (by omega_using [he])

theorem bank_slot {s₀ : State} {e j : Nat} (he : e = 0 ∨ e = 128) (hj : j < 8) :
    (scrR s₀).Contains (bank s₀ e + BitVec.ofNat 64 (16 * j)) 16 := by
  rw [bank, Offset.add_add]; exact Offset.contains_base _ (by omega_using [he, hj]) (by omega_using [he, hj])

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem bank_toNat {e : Nat} (he : e = 0 ∨ e = 128) : (bank s₀ e).toNat + 128 ≤ 2 ^ 64 := by
  have := hp.scr_wrap
  rw [bank, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show e < 2 ^ 64 by omega_using [he]),
    Nat.mod_eq_of_lt (by omega_using [he, this])]
  omega_using [he, this]

theorem blk_bank {e k : Nat} (he : e = 0 ∨ e = 128) (hk : k < N s₀) :
    Region.Disjoint ⟨blk s₀ k, 16⟩ ⟨bank s₀ e, 128⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (bank_sub he)

end

/-- One group of eight blocks, and the banks swapped. -/
theorem blk8_ok (B : BlockFn) (enc : Bool) (hF : B.F = stF enc) {s₀ : State} (hp : UPre s₀) {c e : Nat}
    (hc : c + 8 ≤ N s₀) {s : State} (hI : YInv B enc s₀ c e s) :
    WP isa (blk8 B.f) s fun s' =>
      YInv B enc s₀ (c + 8) (128 - e) s' ∧ s'.gpr .x13 = BitVec.ofNat 64 ((N s₀ - (c + 8)) / 8) := by
  obtain hbr : BlockRegs regs8 := ⟨by decide, by decide⟩
  obtain hbr31 : BlockRegs (regs8 ++ ([.v31] : List VReg)) := ⟨by decide, by decide⟩
  obtain h31 : VReg.v31 ∉ regs8 := by decide
  have hdw := hp.data_wrap
  have hsw := hp.scr_wrap
  have he := hI.he
  have hl : regs8.length = 8 := rfl
  obtain hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [hI.wr, hp.wr]
  obtain hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [hI.rd, hW, hp.rd]; rfl
  obtain eb : ∀ k, blk s₀ c + BitVec.ofNat 64 (16 * (0 + k)) = blk s₀ (c + k) := fun k =>
    Offset.add_add_eq _ (by omega_arith)
  obtain ec : ∀ k, bank s₀ e + BitVec.ofNat 64 (16 * (0 + k)) = bank s₀ e + BitVec.ofNat 64 (16 * k) :=
    fun k => by rw [Nat.zero_add]
  obtain inD : ∀ k < 8, (dataR s₀).Contains (blk s₀ c + BitVec.ofNat 64 (16 * (0 + k))) 16 :=
    fun k hk => by rw [eb]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  -- The blocks loaded and the tweaks XORed in.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (preL_ok (blk s₀ c) (bank s₀ e) regs8 0 s hbr.1 h31 (by decide) hI.x2 hI.x12
    (fun k hk => ⟨dataR s₀, by rw [hR]; simp, inD k hk⟩)
    (fun k hk => ⟨scrR s₀, by rw [hR]; simp, by rw [ec]; exact bank_slot he hk⟩))
    fun s₁ ⟨v₁, o₁, g₁, m₁, sp₁, rd₁, wr₁⟩ => ?_
  -- The next group's tweaks, into the other bank.
  obtain hx8 : s₁.gpr .x8 = bank s₀ (128 - e) := by rw [g₁, hI.x8]
  obtain inN : ∀ d, d + 8 ≤ 128 → InRegions s₁.wr (bank s₀ (128 - e) + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨scrR s₀, by rw [wr₁, hW]; simp, by rw [bank, Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine WP.mono (gen_ok .x8 (bank s₀ (128 - e)) (bank_toNat hp (by omega_arith)) (by decide) (by decide) (by decide)
    (by decide) s₁ hx8 inN 8 (Nat.le_refl _)) fun s₂ ⟨e₂, f₂, t₂, g₂, v₂, sp₂, rd₂, wr₂⟩ => ?_
  obtain hK₂ : B.K (R s₀) (wK s₀) s₂ := by
    obtain hK₁ := B.of_v hI.keys hbr31 (fun r hr => o₁ r (fun h => hr (List.mem_append_left _ h))
      (fun h => hr (h ▸ List.mem_append_right _ (List.mem_singleton_self _)))) (by rw [g₁]) (by rw [g₁])
    exact B.of_v hK₁ (vs := []) ⟨List.nodup_nil, by simp⟩ (fun _ _ => by rw [v₂])
      (g₂ _ (by decide) (by decide) (by decide) (by decide)) (g₂ _ (by decide) (by decide) (by decide) (by decide))
  -- The rounds.
  refine WP.seq (WP.mono (B.ok hbr hK₂) fun s₃ ⟨e₃, f₃⟩ => ?_)
  obtain g₃ : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [f₃.gpr, g₂ r h1 h2 h3 h4, g₁]
  obtain hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [f₃.wr, wr₂, wr₁, hW]
  obtain hR₃ : s₃.rd ++ s₃.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [f₃.rd, rd₂, rd₁, hW₃, hI.rd, hp.rd]; rfl
  -- The current bank, after the next one is written.
  obtain curB : ∀ j < 8, s₃.mem.readW (bank s₀ e + BitVec.ofNat 64 (16 * j)) 128 = twW (tw0 s₀) (c + j) :=
    fun j hj => by
      rw [f₃.mem, f₂.readW (r := ⟨bank s₀ e + BitVec.ofNat 64 (16 * j), 16⟩) (Region.contains_self _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (banks_disj he).sub_left (Offset.sub_base _ (by omega_arith))) (by decide), m₁, hI.cur j hj]
  -- The tweaks XORed in again, the blocks stored, and the advance and swap.
  rw [WP.block_append_iff]
  refine WP.mono (post_ok .x12 (blk s₀ c) (bank s₀ e) (bank_toNat hp he) regs8 0 s₃ hbr.1 h31 (by decide)
    (by rw [hp.blk_toNat (k := c) (by omega_arith)]; omega_arith)
    (by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hI.x2])
    (by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hI.x12])
    (fun k hk => ⟨scrR s₀, by rw [hR₃]; simp, by rw [ec]; exact bank_slot he hk⟩)
    (fun k hk => ⟨dataR s₀, by rw [hW₃]; simp, inD k hk⟩)
    (fun k hk => by rw [eb]; exact blk_bank hp he (by omega_arith)))
    fun s₄ ⟨d₄, f₄, o₄, g₄, sp₄, rd₄, wr₄⟩ => ?_
  obtain g₄' : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₄, g₃ r h1 h2 h3 h4]
  obtain tw₄ : tweakOf s₄ = twW (tw0 s₀) (c + 16) := by
    rw [tweakOf, g₄, f₃.gpr, ← tweakOf, t₂, tweakOf, g₁, ← tweakOf, hI.tw, twW_add]
  obtain hsl : Region.Sub ⟨bank s₀ (128 - e), 128⟩ (scrR s₀) := bank_sub (by omega_arith)
  obtain hdl : Region.Sub ⟨blk s₀ c + BitVec.ofNat 64 (16 * 0), 16 * regs8.length⟩ (dataR s₀) := by
    rw [Nat.mul_zero, BitVec.add_zero, blk]
    exact Offset.sub_base _ (show 16 * c + 16 * 8 ≤ 16 * N s₀ by omega_arith)
  -- The next bank, after the blocks are stored.
  obtain nxt : ∀ j < 8, s₄.mem.readW (bank s₀ (128 - e) + BitVec.ofNat 64 (16 * j)) 128 =
      twW (tw0 s₀) (c + 8 + j) := fun j hj => by
    rw [f₄.readW (r := ⟨bank s₀ (128 - e) + BitVec.ofNat 64 (16 * j), 16⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ((hp.data_scr.sub_left hdl).sub_right fun a h => hsl a (Offset.sub_base _ (by omega_arith) a h)).symm)
      (by decide), f₃.mem, e₂ j hj, tweakOf, g₁, ← tweakOf, hI.tw, twW_add]
  -- The data blocks.
  obtain hdata : ∀ k < N s₀, bytesAt s₄.mem (blk s₀ k) 16 =
      if k < c + 8 then outB enc s₀ k else bytesAt s₀.mem (blk s₀ k) 16 := by
    intro k hk
    by_cases hin : c ≤ k ∧ k < c + 8
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + i := ⟨k - c, by omega_arith⟩
      obtain hi : i < regs8.length := by show i < 8; omega_arith
      obtain hd := d₄ i hi
      rw [eb] at hd
      rw [bytesAt_b16, hd, ec, curB i (by omega_arith)]
      obtain vi := v₁ i hi
      rw [eb, ec, hI.cur i (by omega_arith)] at vi
      obtain hc' : st (s₃.v regs8[i]) = stF enc (R s₀) (wK s₀)
          (st (s.mem.readW (blk s₀ (c + i)) 128 ^^^ twW (tw0 s₀) (c + i))) := by
        rw [e₃ _ (List.getElem_mem hi), v₂, vi, hF]
      rw [xts_word enc (R s₀) (wK s₀) _ _ _ hc', b16_twW, ← iv0_b16, ← bytesAt_b16, hI.data _ hk]
      simp only [show ¬ c + i < c by omega_arith, ite_false, show c + i < c + 8 by omega_arith, ite_true]
    · rw [Proof.Cmac.bytesAt_frame16 f₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [Nat.mul_zero, BitVec.add_zero, blk, blk]
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)),
        f₃.mem, Proof.Cmac.bytesAt_frame16 f₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact blk_bank hp (by omega_arith) hk), m₁, hI.data k hk]
      by_cases hkc : k < c
      · simp only [hkc, ite_true, show k < c + 8 by omega_arith]
      · simp only [hkc, ite_false, show ¬ k < c + 8 by omega_arith]
  obtain fr : Frame [dataR s₀, scrR s₀] s₀.mem s₄.mem := by
    refine hI.frame.trans ((?_ : Frame [dataR s₀, scrR s₀] s.mem s₂.mem).trans ?_)
    · rw [← m₁]
      exact f₂.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, hsl⟩
    · rw [← f₃.mem]
      exact f₄.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, hdl⟩
  -- `add x2, 128`, `sub x3, 8`, `lsr x13`, and the banks swapped through `x10`.
  obtain h4 : BitVec.ofNat 64 (N s₀ - c) - BitVec.ofNat 64 8 = BitVec.ofNat 64 (N s₀ - (c + 8)) := by
    rw [Offset.ofNat_sub_ofNat (by omega_arith), show N s₀ - c - 8 = N s₀ - (c + 8) by omega_arith]
  obtain x2₄ : s₄.gpr .x2 = blk s₀ c := by rw [g₄' _ (by decide) (by decide) (by decide) (by decide), hI.x2]
  obtain x3₄ : s₄.gpr .x3 = BitVec.ofNat 64 (N s₀ - c) := by
    rw [g₄' _ (by decide) (by decide) (by decide) (by decide), hI.x3]
  obtain x12₄ : s₄.gpr .x12 = bank s₀ e := by rw [g₄' _ (by decide) (by decide) (by decide) (by decide), hI.x12]
  obtain x8₄ : s₄.gpr .x8 = bank s₀ (128 - e) := by
    rw [g₄' _ (by decide) (by decide) (by decide) (by decide), hI.x8]
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 128) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 8) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 3) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 0) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 0) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 0) (by decide), WP.block_nil ?_⟩
  refine ⟨⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, by omega_arith, ?_, ?_, fun j hj => ?_, ?_, rd₄.trans (f₃.rd.trans (rd₂.trans
    (rd₁.trans hI.rd))), wr₄.trans (f₃.wr.trans (wr₂.trans (wr₁.trans hI.wr))), fr, hdata⟩, ?_⟩
  · exact B.of_v (B.of_v hK₂ hbr f₃.v (by rw [f₃.gpr]) (by rw [f₃.gpr])) hbr31
      (fun r hr => o₄ r (fun h => hr (List.mem_append_left _ h))
        (fun h => hr (h ▸ List.mem_append_right _ (List.mem_singleton_self _))))
      (by simp [State.write, g₄]) (by simp [State.write, g₄])
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, x2₄]
    exact Offset.add_add_eq _ (by omega_arith)
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, x3₄]
    exact h4
  · simp only [State.write, reduceCtorEq, ite_false]
    rw [g₄' _ (by decide) (by decide) (by decide) (by decide), hI.x5]
  · simp only [State.write, reduceCtorEq, ite_false]
    rw [g₄' _ (by decide) (by decide) (by decide) (by decide), hI.x11]
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, x8₄,
      BitVec.add_zero]
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, x12₄,
      BitVec.add_zero]
    rw [show 128 - (128 - e) = e by omega_arith]
  · show s₄.mem.readW _ 128 = _
    rw [nxt j hj, Nat.add_right_comm]
  · rw [tweakOf]; simp only [State.write, reduceCtorEq, ite_false]; rw [← tweakOf, tw₄]
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, x3₄]
    rw [h4, ushr3 (by omega_arith)]

/-- The banks set up, and the first group's tweaks stored. -/
theorem start8_ok (B : BlockFn) (enc : Bool) {s₀ : State} (hp : UPre s₀) {s : State}
    (hI : XInv B enc s₀ 0 0 s) : WP isa (.block start8) s (YInv B enc s₀ 0 0) := by
  have hsw := hp.scr_wrap
  obtain hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [hI.wr, hp.wr]
  rw [start8, List.cons_append, List.cons_append, List.nil_append]
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 0) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 128) (by decide), ?_⟩
  obtain x12₁ : ((s.write .x .x12 (s.read .x .x5 + BitVec.ofNat _ 0)).write .x .x8
      ((s.write .x .x12 (s.read .x .x5 + BitVec.ofNat _ 0)).read .x .x5 + BitVec.ofNat _ 128)).gpr .x12 =
      S s₀ := by simp [State.write, State.read, hI.x5]
  refine WP.mono (gen_ok .x12 (S s₀) (by omega_using [hsw]) (by decide) (by decide) (by decide) (by decide) _ x12₁
    (fun d hd => ⟨scrR s₀, by simp [State.write, hW], Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])⟩) 8
    (Nat.le_refl _)) fun s₂ ⟨e₂, f₂, t₂, g₂, v₂, sp₂, rd₂, wr₂⟩ => ?_
  obtain g : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → r ≠ .x12 → r ≠ .x8 → s₂.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by rw [g₂ r h1 h2 h3 h4]; simp [State.write, h5, h6]
  obtain tw₁ : tweakOf ((s.write .x .x12 (s.read .x .x5 + BitVec.ofNat _ 0)).write .x .x8
      ((s.write .x .x12 (s.read .x .x5 + BitVec.ofNat _ 0)).read .x .x5 + BitVec.ofNat _ 128)) =
      twW (tw0 s₀) 0 := by
    rw [← hI.tw]; simp [tweakOf, State.write]
  obtain hsub : Region.Sub ⟨S s₀, 128⟩ (scrR s₀) := Region.sub_prefix (by decide)
  refine ⟨Nat.zero_le _, ?_, by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.x2],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.x3],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.x5],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.x11], .inl rfl,
    ?_, ?_, fun j hj => ?_, ?_, by rw [rd₂]; exact hI.rd, by rw [wr₂]; exact hI.wr, ?_, fun k hk => ?_⟩
  · exact B.of_v hI.keys (vs := []) ⟨List.nodup_nil, by simp⟩ (fun _ _ => by rw [v₂]; rfl)
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
  · rw [g₂ _ (by decide) (by decide) (by decide) (by decide)]; simp [State.write, State.read, hI.x5, bank]
  · rw [g₂ _ (by decide) (by decide) (by decide) (by decide)]; simp [State.write, State.read, hI.x5, bank]
  · rw [show bank s₀ 0 = S s₀ by simp [bank], e₂ j hj, tw₁, twW_add]
  · rw [t₂, tw₁, twW_add]
  · exact hI.frame.trans (f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, hsub⟩)
  · rw [Proof.Cmac.bytesAt_frame16 f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right hsub)]
    exact hI.data k hk

/-- The tweak of the next block loaded back. -/
theorem end8_ok (B : BlockFn) (enc : Bool) {s₀ : State} (hp : UPre s₀) {c e : Nat} {s : State}
    (hI : YInv B enc s₀ c e s) : WP isa (.block end8) s (XInv B enc s₀ c c) := by
  have hsw := hp.scr_wrap
  have he := hI.he
  obtain hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [hI.rd, hI.wr, hp.rd, hp.wr]; rfl
  obtain c0 : InRegions (s.rd ++ s.wr) (s.gpr .x12 + BitVec.ofNat 64 0) 8 :=
    ⟨scrR s₀, by rw [hR]; simp, by rw [hI.x12, bank, Offset.add_add]; exact Offset.contains_base _ (by omega_using [he]) (by omega_using [he])⟩
  obtain c8 : InRegions (s.rd ++ s.wr) (s.gpr .x12 + BitVec.ofNat 64 8) 8 :=
    ⟨scrR s₀, by rw [hR]; simp, by rw [hI.x12, bank, Offset.add_add]; exact Offset.contains_base _ (by omega_using [he]) (by omega_using [he])⟩
  rw [end8, WP.block_cons_iff]; refine ⟨_, exec_ldr_x (off := 0) (by decide) c0, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldr_x (off := 8) (by decide) (by simpa [State.write] using c8), WP.block_nil ?_⟩
  obtain g : ∀ r, r ≠ .x14 → r ≠ .x15 → ((s.write .x .x14 (s.mem.readW (s.gpr .x12 + BitVec.ofNat 64 0) 64)).write .x .x15
      ((s.write .x .x14 (s.mem.readW (s.gpr .x12 + BitVec.ofNat 64 0) 64)).mem.readW
        ((s.write .x .x14 (s.mem.readW (s.gpr .x12 + BitVec.ofNat 64 0) 64)).gpr .x12 + BitVec.ofNat 64 8) 64)).gpr r =
      s.gpr r := fun r h1 h2 => by simp [State.write, h1, h2]
  refine ⟨hI.le, B.of_v hI.keys (vs := []) ⟨List.nodup_nil, by simp⟩ (fun _ _ => rfl)
      (g _ (by decide) (by decide)) (g _ (by decide) (by decide)),
    by rw [g _ (by decide) (by decide), hI.x2], by rw [g _ (by decide) (by decide), hI.x3],
    by rw [g _ (by decide) (by decide), hI.x5], by rw [g _ (by decide) (by decide), hI.x11], ?_,
    hI.rd, hI.wr, hI.frame, hI.data⟩
  have := hI.cur 0 (by decide)
  rw [Nat.mul_zero, Nat.add_zero, readW128, ← hI.x12] at this
  simp only [tweakOf, State.write, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, BitVec.add_zero]
  rw [BitVec.add_zero] at this
  exact this

/-- The eight-block loop, from the state after the setup. -/
theorem loop8_ok (B : BlockFn) (enc : Bool) (hF : B.F = stF enc) {s₀ : State} (hp : UPre s₀) {s₁ : State}
    (hI₁ : XInv B enc s₀ 0 0 s₁) (h13 : s₁.gpr .x13 = BitVec.ofNat 64 (N s₀ / 8)) :
    WP isa (.ite (.zero .x .x13) (.block [])
        (.seq (.block start8) (.seq (.loop (blk8 B.f) (.nonzero .x .x13)) (.block end8)))) s₁
      fun s => ∃ c, N s₀ - c < 8 ∧ XInv B enc s₀ c c s := by
  obtain hn : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  refine WP.ite (decide (N s₀ / 8 = 0)) (eval_zero h13 (by omega_using [hn])) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil ⟨0, by simp at h; omega_using [h], hI₁⟩
  · refine WP.seq (WP.mono (start8_ok B enc hp hI₁) fun s₂ h₂ => ?_)
    let I8 : Nat → State → Prop := fun m s => ∃ c e, m = N s₀ - c ∧ c + 8 ≤ N s₀ ∧ YInv B enc s₀ c e s
    obtain hstep : ∀ m s, I8 m s → WP isa (blk8 B.f) s (fun s' =>
        (AArch64.eval (.nonzero .x .x13) s' = some false ∧ ∃ c e, N s₀ - c < 8 ∧ YInv B enc s₀ c e s') ∨
        (AArch64.eval (.nonzero .x .x13) s' = some true ∧ ∃ m' < m, I8 m' s')) := by
      rintro m s ⟨c, e, rfl, hc, hI⟩
      refine WP.mono (blk8_ok B enc hF hp hc hI) fun s' ⟨hI', h13'⟩ => ?_
      rw [eval_nonzero h13' (by omega_using [hn])]
      by_cases hlt : N s₀ - (c + 8) < 8
      · exact .inl ⟨by simp; omega_using [hlt], c + 8, 128 - e, hlt, hI'⟩
      · exact .inr ⟨by simp; omega_using [hlt], N s₀ - (c + 8), by omega_using [hc], c + 8, 128 - e, rfl, by omega_using [hlt], hI'⟩
    refine WP.seq (WP.mono (WP.loop (M := isa) I8 hstep (N s₀) s₂ ⟨0, 0, rfl, by simp at h; omega_using [h], h₂⟩)
      fun s₃ ⟨c, e, hc, h₃⟩ => ?_)
    exact WP.mono (end8_ok B enc hp h₃) fun s₄ h₄ => ⟨c, hc, h₄⟩

end VG.Proof.AesXts.AArch64.Aes

end

end


/-!
# One-pass XTS-AES on AArch64: the whole function

`crypt_wp`: `crypt setup B.f` meets the contract of `vg_aes_xts_encrypt` (or
`vg_aes_xts_decrypt`) as `modeAArch64 (xtsMode enc)` states it, but for the
registers it preserves, when `setup` loads the round keys `B` needs
(`KPre`, `KPost`) and `B` computes the cipher (or its inverse) of the
direction: `enter` and `setup` reach `XInv … 0 0` (`setup_ok`), the
eight-block groups leave fewer than eight blocks (`loop8_ok`,
`Group8.lean`), the one-block loop the rest (`loop1_ok`), reaching
`XInv … N N`, and `finish` writes the tweak after the last block back
(`finish_ok`).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Aes

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesXts (b16)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.AArch64 (W R Iv Dp N S schR ivR dataR scrR UPre blk wK iv0 modeAArch64 in_rw)
open VG.Proof.Aes.AArch64.Aese (BlockFn bkp bnr bnb bsch)
open VG.Impl.AesXts.AArch64Aes (enter finish crypt)

theorem enter_ok {s₀ : State} (hp : UPre s₀) :
    WP isa (.block enter) s₀ fun s =>
      s.gpr .x11 = Iv s₀ ∧ s.gpr .x2 = Dp s₀ ∧ s.gpr .x3 = s₀.gpr .x4 ∧ tweakOf s = tw0 s₀ ∧
      (∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x11 → r ≠ .x14 → r ≠ .x15 → s.gpr r = s₀.gpr r) ∧
      s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  have hiv := hp.iv_wrap
  obtain hW : s₀.rd ++ s₀.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [hp.rd, hp.wr]; rfl
  rw [enter, WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 0) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 0) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 0) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldr_x (off := 0) (by decide) (by
    simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, Size.bits,
      BitVec.add_zero]
    rw [hW]; exact in_rw (r := ivR s₀) (by simp)
      (by simpa using Offset.contains_base (Iv s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide))), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldr_x (off := 8) (by decide) (by
    simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, Size.bits,
      BitVec.add_zero]
    rw [hW]; exact in_rw (r := ivR s₀) (by simp)
      (Offset.contains_base (Iv s₀) (d := 8) (n := 8) (k := 16) (by decide) (by decide))), WP.block_nil ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r h2 h3 h11 h14 h15 => ?_, rfl, rfl, rfl⟩
  · simp [State.write, State.read]
  · simp [State.write, State.read]
  · simp [State.write, State.read]
  · simp only [tweakOf, State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq,
      BitVec.add_zero]
    exact (readW128 _ _).symm
  · simp [State.write, h2, h3, h11, h14, h15]

/-- `enter` and the key setup. -/
theorem setup_ok (B : BlockFn) (enc : Bool) {setup : List Instr}
    (hs : ∀ s, KPre s → WP isa (.block setup) s (KPost B.K s)) {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (enter ++ setup)) s₀ fun s =>
      XInv B enc s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (N s₀ / 8) := by
  rw [WP.block_append_iff]
  refine WP.mono (enter_ok hp) fun s₁ ⟨x11, x2, x3, t₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  obtain hx0 : bkp s₁ = W s₀ := g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain hx1 : bnr s₁ = R s₀ := by
    simp only [bnr, R]; rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  obtain kp : KPre s₁ := ⟨fun ho => by
      rw [rd₁, wr₁, hx0, hp.rd]
      exact in_rw (by simp) (Offset.contains_base _ ho (by omega_using [ho])), by rw [hx1]; exact hp.rounds⟩
  refine WP.mono (hs s₁ kp) fun s₂ k₂ => ?_
  obtain g : ∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x11 → r ≠ .x14 → r ≠ .x15 → r ≠ .x9 → r ≠ .x6 → r ≠ .x7 →
      r ≠ .x13 → s₂.gpr r = s₀.gpr r := fun r h2 h3 h11 h14 h15 h9 h6 h7 h13 => by
    rw [k₂.gpr r h9 h6 h7 h13, g₁ r h2 h3 h11 h14 h15]
  obtain hsch : bsch s₁ = wK s₀ := by simp only [bsch, wK, hx0, hx1, m₁]
  refine ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩, ?_⟩
  · rw [← hsch, ← hx1]; exact k₂.keys
  · rw [k₂.gpr _ (by decide) (by decide) (by decide) (by decide), x2, blk, Nat.mul_zero, BitVec.add_zero]
  · rw [k₂.gpr _ (by decide) (by decide) (by decide) (by decide), x3, Nat.sub_zero]
    exact Proof.AesCbc.AArch64.x4_ofNat s₀
  · exact g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  · rw [k₂.gpr _ (by decide) (by decide) (by decide) (by decide), x11]
  · rw [tweakOf, k₂.gpr _ (by decide) (by decide) (by decide) (by decide),
      k₂.gpr _ (by decide) (by decide) (by decide) (by decide), ← tweakOf, t₁]; rfl
  · rw [k₂.rd, rd₁]
  · rw [k₂.wr, wr₁]
  · rw [k₂.mem, m₁]; exact Frame.refl _ _
  · rw [k₂.mem, m₁]; simp
  · rw [k₂.x13]; simp only [bnb, x3]

theorem getElem_tweaks (t : List Byte) {n k : Nat} (hk : k < n) :
    (Spec.Xts.tweaks t n)[k]'(by rw [AesXts.length_tweaks]; exact hk) = Spec.Xts.next t k := by
  induction n generalizing t k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k => simp only [Spec.Xts.tweaks, List.getElem_cons_succ]; rw [ih _ (by omega_using [hk]), AesXts.next_succ']

/-- The tweak after the last block written back. -/
theorem finish_ok (B : BlockFn) (enc : Bool) {s₀ : State} (hp : UPre s₀) {s : State}
    (h : XInv B enc s₀ (N s₀) (N s₀) s) :
    WP isa (.block finish) s fun s' => (modeAArch64 (AesXts.xtsMode enc)).post s₀ s' ∧
      s'.gpr = s.gpr ∧ s'.v = s.v := by
  have hiv := hp.iv_wrap
  obtain hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  rw [finish, WP.block_cons_iff]; refine ⟨_, exec_str_x (off := 0) (by decide) (by
    rw [hW, h.x11]; exact in_rw (r := ivR s₀) (by simp)
      (Offset.contains_base (Iv s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide))), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_str_x (off := 8) (by decide) (by
    rw [hW, h.x11]; exact in_rw (r := ivR s₀) (by simp)
      (Offset.contains_base (Iv s₀) (d := 8) (n := 8) (k := 16) (by decide) (by decide))), WP.block_nil ?_⟩
  obtain fr : Frame [ivR s₀] s.mem ((s.mem.writeW (Iv s₀) (s.gpr .x14)).writeW (Iv s₀ + BitVec.ofNat 64 8)
      (s.gpr .x15)) := Proof.Cmac.frame_store2 _ _ _
  obtain hs : Mem.Sep (Iv s₀) (64 / 8) (Iv s₀ + BitVec.ofNat 64 8) (64 / 8) := by
    have := Offset.sep (Iv s₀) (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)
    simpa using this
  refine ⟨⟨?_, ?_⟩, rfl, rfl⟩ <;> simp only [h.x11, BitVec.add_zero]
  · show Spec.Cbc.blocksAt _ (Dp s₀) (N s₀) = Spec.Xts.crypt (ciphOf enc (R s₀) (wK s₀)) (iv0 s₀)
      (Spec.Cbc.blocksAt s₀.mem (Dp s₀) (N s₀))
    apply List.ext_getElem (by rw [AesXts.length_crypt, AesCbc.length_blocksAt, AesCbc.length_blocksAt])
    intro k h₁ h₂
    obtain hk : k < N s₀ := by rwa [AesCbc.length_blocksAt] at h₁
    rw [AesCbc.getElem_blocksAt _ _ hk]
    simp only [Spec.Xts.crypt, List.getElem_zipWith]
    rw [getElem_tweaks _ (by rwa [AesCbc.length_blocksAt]), AesCbc.getElem_blocksAt _ _ hk,
      Proof.Cmac.bytesAt_frame16 fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hp.iv_data.sub_right (UPre.data_sub hk)).symm),
      h.data k hk]
    simp only [hk, ite_true]
  · show bytesAt _ (Iv s₀) 16 = Spec.Xts.next (iv0 s₀) (Spec.Cbc.blocksAt s₀.mem (Dp s₀) (N s₀)).length
    rw [AesCbc.length_blocksAt, bytesAt_b16, readW128, Mem.readW_writeW_self64,
      Mem.readW_writeW_sep hs (by decide), Mem.readW_writeW_self64, ← tweakOf, h.tw, b16_twW,
      ← iv0_b16]

/-- The whole function, but for the registers it preserves. -/
theorem crypt_wp (B : BlockFn) (enc : Bool) (hF : B.F = stF enc) {setup : List Instr}
    (hs : ∀ s, KPre s → WP isa (.block setup) s (KPost B.K s)) {s₀ : State}
    (h0 : (modeAArch64 (AesXts.xtsMode enc)).pre s₀) :
    WP isa (crypt setup B.f) s₀ ((modeAArch64 (AesXts.xtsMode enc)).post s₀) := by
  obtain hp := UPre.of h0
  refine WP.seq (WP.mono (setup_ok B enc hs hp) fun s₁ ⟨hI₁, h13⟩ => ?_)
  refine WP.seq (WP.mono (loop8_ok B enc hF hp hI₁ h13) fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  refine WP.seq (WP.mono (loop1_ok B enc hF hp hc hI₂) fun s₃ hI₃ => ?_)
  exact WP.mono (finish_ok B enc hp hI₃) fun _ h => h.1

end VG.Proof.AesXts.AArch64.Aes

end

end

/-! ### `AesXts.AArch64.Aes.Verified`, which only this module used -/

section

/-! ### `AesXts.AArch64.Verified`, which this module and modules that import it used -/

section

/-!
# XTS-AES on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), from `crypt_wp` and `crypt_ct`, a state satisfying the
precondition, and the shared contracts of `Spec/Xts/Contract.lean` (with no
stack: the call keeps the return address in `x30`, which the functions save
in the scratch buffer).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64

open VG VG.AArch64 VG.Impl.AesXts.AArch64
open VG.Proof.AesCbc (ciphOf aesWith_state aesInvWith_state)
open VG.Proof.AesCbc.AArch64
open VG.Proof.Aes.AArch64 (BlocksImpl)

theorem encrypt_keepsV (v : BlocksImpl) : (encrypt v.enc).allInstrs keepsV = true := by
  simp only [encrypt, crypt, batch, pass, Code.allInstrs, v.encKeepsV]; decide +kernel

theorem encrypt_correct (v : BlocksImpl) (s : State) (hs : (modeAArch64 (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa (encrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode true)).post s s' :=
  WP.withPreservedV (crypt_wp true v.encOk v.encNoFrames (fun R w m p => (aesWith_state R w m p).symm) hs)
    (encrypt_keepsV v)

theorem decrypt_keepsV (v : BlocksImpl) : (decrypt v.dec).allInstrs keepsV = true := by
  simp only [decrypt, crypt, batch, pass, Code.allInstrs, v.decKeepsV]; decide +kernel

theorem decrypt_correct (v : BlocksImpl) (s : State) (hs : (modeAArch64 (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa (decrypt v.dec) s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode false)).post s s' :=
  WP.withPreservedV (crypt_wp false v.decOk v.decNoFrames (fun R w m p => (aesInvWith_state R w m p).symm) hs)
    (decrypt_keepsV v)

end VG.Proof.AesXts.AArch64

end

end

/-!
# One-pass XTS-AES on AArch64: `Verified`

Correctness (`crypt_wp` with `encFn` or `decFn`, whose setups load the round
keys, `encSetup_ok'` and `decSetup_ok'`), the registers preserved (no
instruction writes a callee-saved one), constant time (`taint_decide`: only
the pointers, `rounds` and `n` reach a branch or an address), and the shared
contracts of `Spec/Xts/Contract.lean`, from the same contracts
`modeAArch64 (xtsMode enc)` as the functions calling a block function
(`AArch64/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Aes

open VG VG.AArch64
open VG.Impl.AesXts.AArch64Aes (encrypt decrypt)
open VG.Proof.AesCbc.AArch64 (modeAArch64)
open VG.Proof.Aes.AArch64.Aese (encFn decFn)

theorem encFn_F : encFn.F = stF true := rfl

theorem decFn_F : decFn.F = stF false := rfl

theorem encrypt_keepsV : encrypt.allInstrs keepsV = true := by lit_decide

theorem decrypt_keepsV : decrypt.allInstrs keepsV = true := by lit_decide

theorem encrypt_noFrames : encrypt.noFrames = true := by lit_decide

theorem decrypt_noFrames : decrypt.noFrames = true := by lit_decide

theorem encrypt_correct (s : State) (hs : (modeAArch64 (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode true)).post s s' := by
  obtain ⟨t, s', he, h₂, h₁⟩ := WP.gprs (rs := preserved)
    (crypt_wp encFn true encFn_F (fun _ hp => encSetup_ok' hp) hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he encrypt_keepsV⟩, h₂⟩

theorem decrypt_correct (s : State) (hs : (modeAArch64 (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode false)).post s s' := by
  obtain ⟨t, s', he, h₂, h₁⟩ := WP.gprs (rs := preserved)
    (crypt_wp decFn false decFn_F (fun _ hp => decSetup_ok' hp) hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he decrypt_keepsV⟩, h₂⟩

theorem encrypt_ct (enc : Bool) : ConstantTime isa (modeAArch64 (AesXts.xtsMode enc)).pre
    (modeAArch64 (AesXts.xtsMode enc)).pub encrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decrypt_ct (enc : Bool) : ConstantTime isa (modeAArch64 (AesXts.xtsMode enc)).pre
    (modeAArch64 (AesXts.xtsMode enc)).pub decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.AesXts.AArch64.Aes

end

end

/-!
# Implementations of `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt` on AArch64

An `XtsImpl` is what a function that calls the whole-block functions needs
of them, so that its proof holds for every implementation: each is a
variant of the interface `AesXts` on AArch64 (`Variants/AesXts/AArch64/`),
and each caller (in `Generic/AesXts/AArch64/`) is emitted once for each of
them (see `TCB/Emit.lean`). Both functions are proven against the contracts
`modeAArch64 (xtsMode true)` and `modeAArch64 (xtsMode false)`, have no
frames and write no callee-saved vector register.

There are two: the functions calling the bitsliced block functions
(`XtsImpl.blocks .scalar`, `vg_aes_xts_encrypt`), and the one-pass functions
with the AES instructions, which call nothing (`XtsImpl.aes`,
`vg_aes_xts_encrypt_aes`); both are emitted by
`Artifacts/AesXts/AArch64.lean`.
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64

open VG VG.AArch64
open VG.Proof.AesCbc (aesWith_state aesInvWith_state)
open VG.Proof.AesCbc.AArch64 (modeAArch64)
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-- An implementation of `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt` on AArch64. -/
structure XtsImpl where
  /-- `vg_aes_xts_encrypt`: its symbol and code. -/
  enc : Impl.Aes.AArch64.Blocks
  encNoFrames : enc.code.noFrames = true
  encOk : ∀ s, (modeAArch64 (AesXts.xtsMode true)).pre s →
    ∃ t s', Exec isa enc.code s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode true)).post s s'
  encCt : ConstantTime isa (modeAArch64 (AesXts.xtsMode true)).pre (modeAArch64 (AesXts.xtsMode true)).pub
    enc.code
  encKeepsV : enc.code.allInstrs keepsV = true
  /-- `vg_aes_xts_decrypt`: its symbol and code. -/
  dec : Impl.Aes.AArch64.Blocks
  decNoFrames : dec.code.noFrames = true
  decOk : ∀ s, (modeAArch64 (AesXts.xtsMode false)).pre s →
    ∃ t s', Exec isa dec.code s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode false)).post s s'
  decCt : ConstantTime isa (modeAArch64 (AesXts.xtsMode false)).pre (modeAArch64 (AesXts.xtsMode false)).pub
    dec.code
  decKeepsV : dec.code.allInstrs keepsV = true
  /-- What the names of its callers' instances end with (e.g. `_aes`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String
  /-- `enc.code` and `dec.code` write, of the registers the calling
  convention does not preserve, only those they state (`enc.clear`,
  `dec.clear`): a caller clears them with its own before returning
  (`ScrubAll.scrubSide_union0`). -/
  encScrub : AArch64.ScrubAll.calleeSide enc.code enc.clear = true
  decScrub : AArch64.ScrubAll.calleeSide dec.code dec.clear = true

namespace XtsImpl

theorem crypt_noFrames {b : Impl.Aes.AArch64.Blocks} (h : b.code.noFrames = true) :
    (Impl.AesXts.AArch64.crypt b).noFrames = true := by
  simp [Impl.AesXts.AArch64.crypt, Impl.AesXts.AArch64.batch, Impl.AesXts.AArch64.pass, Code.noFrames, h]

/-- `crypt`'s own instructions write only the registers `Impl/` states
(`Impl.AesXts.AArch64.cryptOwn`): evaluated once, with code that does nothing
in the place of the block function. -/
private theorem crypt_own :
    AArch64.ScrubAll.calleeSide (Impl.AesXts.AArch64.crypt ⟨"", .block [], ⟨[], [], []⟩⟩) Impl.AesXts.AArch64.cryptOwn = true := by
  kernel_rfl

/-- `crypt` around a block function that writes the registers `cl` writes its
own and those. -/
theorem crypt_scrub {b : Impl.Aes.AArch64.Blocks} {cl : Impl.Residue.AArch64.Clear}
    (hc : AArch64.ScrubAll.calleeSide b.code cl = true) :
    AArch64.ScrubAll.calleeSide (Impl.AesXts.AArch64.crypt b) (Impl.AesXts.AArch64.cryptOwn.union cl) = true := by
  have h0 := AArch64.ScrubAll.sideAll_union_left (b := cl) crypt_own
  have h1 := AArch64.ScrubAll.sideAll_union_right (a := Impl.AesXts.AArch64.cryptOwn) hc
  simp only [AArch64.ScrubAll.calleeSide, Impl.AesXts.AArch64.crypt, Impl.AesXts.AArch64.batch,
    AArch64.ScrubAll.sideAll, Bool.and_eq_true] at h0 h1 ⊢
  simp only [h0, h1, and_self]

/-- The functions calling the block functions of `v`, `vg_aes_xts_encrypt`
and `vg_aes_xts_decrypt` with `v`'s suffix. -/
def blocks (v : BlocksImpl) : XtsImpl where
  enc := ⟨"vg_aes_xts_encrypt" ++ v.suffix, Impl.AesXts.AArch64.encrypt v.enc,
    Impl.AesXts.AArch64.cryptOwn.union v.enc.clear⟩
  encNoFrames := crypt_noFrames v.encNoFrames
  encOk := encrypt_correct v
  encCt := crypt_ct true v.encOk v.encCt v.encNoFrames fun R w m p => (aesWith_state R w m p).symm
  encKeepsV := encrypt_keepsV v
  dec := ⟨"vg_aes_xts_decrypt" ++ v.suffix, Impl.AesXts.AArch64.decrypt v.dec,
    Impl.AesXts.AArch64.cryptOwn.union v.dec.clear⟩
  decNoFrames := crypt_noFrames v.decNoFrames
  decOk := decrypt_correct v
  decCt := crypt_ct false v.decOk v.decCt v.decNoFrames fun R w m p => (aesInvWith_state R w m p).symm
  decKeepsV := decrypt_keepsV v
  suffix := v.suffix
  features := v.features
  encScrub := crypt_scrub v.encScrub
  decScrub := crypt_scrub v.decScrub

/-- The one-pass functions with the AES instructions,
`vg_aes_xts_encrypt_aes` and `vg_aes_xts_decrypt_aes`. -/
def aes : XtsImpl where
  enc := ⟨"vg_aes_xts_encrypt" ++ "_aes", Impl.AesXts.AArch64Aes.encrypt, Impl.AesXts.AArch64Aes.clear⟩
  encNoFrames := Aes.encrypt_noFrames
  encOk := Aes.encrypt_correct
  encCt := Aes.encrypt_ct true
  encKeepsV := Aes.encrypt_keepsV
  dec := ⟨"vg_aes_xts_decrypt" ++ "_aes", Impl.AesXts.AArch64Aes.decrypt, Impl.AesXts.AArch64Aes.clear⟩
  decNoFrames := Aes.decrypt_noFrames
  decOk := Aes.decrypt_correct
  decCt := Aes.decrypt_ct false
  decKeepsV := Aes.decrypt_keepsV
  suffix := "_aes"
  features := ["aes"]
  encScrub := by lit_decide
  decScrub := by lit_decide

end XtsImpl

end VG.Proof.AesXts.AArch64
