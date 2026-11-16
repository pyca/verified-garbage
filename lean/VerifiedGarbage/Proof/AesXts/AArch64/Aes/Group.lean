module

public import VerifiedGarbage.Impl.AesXts.AArch64Aes
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
public import VerifiedGarbage.Proof.AesCbc.Spec
public import VerifiedGarbage.Proof.AesXts.Alpha16
import VerifiedGarbage.Proof.AesXts.Alpha
import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.AesXts.AArch64.Steps
import VerifiedGarbage.Proof.AesCbc.AArch64.Block
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
public import VerifiedGarbage.Proof.AesCbc.AArch64.Loop
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesCbc.AArch64.Body

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
