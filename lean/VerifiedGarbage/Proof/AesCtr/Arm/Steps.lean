module

public import VerifiedGarbage.Proof.AesCtr.Inc
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Reduce
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Impl.AesCtr.Arm
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Ctr
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-CTR on ARMv7: the code around the call

Each block of the code around the call of `vg_aes_ctr32` run once: `count`
leaves the call's number of blocks in `r9` (`mWord`, which is
`min(left, 2³² − c)`: `mWord_toNat`), `adv` moves on past them and sets Z if
the counter block's last word is zero, and `carry` adds `2³²` to the counter
block (`carryMem`, `carryMem_bytes`): three words, loaded and byte-reversed,
the last plus 1 and each other plus the carry out of the one after it,
reversed again and stored.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCtr.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCtr.Arm
open VG.Spec.Aes (bytesAt)

theorem gpr_addFlags (s : State) (x y : BitVec 32) : (addFlags s x y).gpr = s.gpr := rfl
theorem mem_addFlags (s : State) (x y : BitVec 32) : (addFlags s x y).mem = s.mem := rfl
theorem rd_addFlags (s : State) (x y : BitVec 32) : (addFlags s x y).rd = s.rd := rfl
theorem wr_addFlags (s : State) (x y : BitVec 32) : (addFlags s x y).wr = s.wr := rfl
theorem c_addFlags (s : State) (x y : BitVec 32) :
    (addFlags s x y).c = decide (2 ^ 32 ≤ x.toNat + y.toNat) := rfl
theorem gpr_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).gpr = s.gpr := rfl
theorem mem_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).mem = s.mem := rfl
theorem rd_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).rd = s.rd := rfl
theorem wr_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).wr = s.wr := rfl
theorem c_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).c = decide (y.toNat ≤ x.toNat) := rfl
theorem z_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).z = (x - y == 0) := rfl
theorem sp_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).sp = s.sp := rfl
theorem sp_addFlags (s : State) (x y : BitVec 32) : (addFlags s x y).sp = s.sp := rfl

/-- The carry out of `x + y`. -/
abbrev carryOut (x y : BitVec 32) : Bool := decide (2 ^ 32 ≤ x.toNat + y.toNat)

/-- A carry as a word, as `mov r12, #0; adc r12, r12, #0` computes it. -/
abbrev cw (c : Bool) : BitVec 32 := 0 + 0 + (if c then 1 else 0)

/-! ## The number of blocks -/

/-- What `count` leaves in `r9`, from the counter block's last 32 bits `c`
and the blocks left. -/
def mWord (c left : BitVec 32) : BitVec 32 :=
  ((left - 1) ^^^ (((left - 1) ^^^ ~~~c) &&& (0 - cw (decide ((~~~c).toNat ≤ (left - 1).toNat))))) + 1

theorem count_ok (s : State) {Q : Addr} (hq : State.addr (s.gpr .r6) = Q)
    (hfit : (s.gpr .r6).toNat + 16 ≤ 2 ^ 32)
    (rq : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 12) 4) :
    ∃ s', runBlock isa count s = some s' ∧
      s'.gpr .r9 = mWord (rev (s.mem.readW (Q + BitVec.ofNat 64 12) 32)) (s.gpr .r8) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a12 : State.addr (s.gpr .r6 + BitVec.ofNat 32 12) = Q + BitVec.ofNat 64 12 := by
    rw [addr_add (by omega_using [hfit]), hq]
  have i0 (t : State) : (Op2.imm 0).eval t = some 0 := Proof.MdStream.Arm.op2_imm (by decide)
  have i1 (t : State) : (Op2.imm 1).eval t = some 1 := Proof.MdStream.Arm.op2_imm (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, count, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
      i0, i1, Proof.MdStream.Arm.op2_reg, State.load32, Option.map_some, Nat.reduceLT,
      gpr_setReg, rd_setReg, wr_setReg, c_setReg, gpr_subFlags, mem_subFlags, rd_subFlags,
      wr_subFlags, c_subFlags, a12, rq]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ h₂ h₃ h₄ h₅ => by simp [gpr_setReg, gpr_subFlags, h₁, h₂, h₃, h₄, h₅], rfl, rfl, rfl, rfl⟩
  simp only [gpr_setReg, gpr_subFlags, reduceCtorEq, ↓reduceIte, mem_setReg, c_setReg, c_subFlags]
  rfl

/-- `count`'s number of blocks: what is left, but no further than where the
counter block's last 32 bits wrap around. -/
theorem mWord_toNat (c left : BitVec 32) (hl : 0 < left.toNat) :
    (mWord c left).toNat = min left.toNat (2 ^ 32 - c.toNat) := by
  have hc := c.isLt
  have hL := left.isLt
  have o : (1 : BitVec 32).toNat = 1 := rfl
  have e1 : (left - 1).toNat = left.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, o]; omega), o]
  have e2 : (~~~c).toNat = 2 ^ 32 - 1 - c.toNat := by rw [BitVec.toNat_not]
  unfold mWord
  by_cases h : (~~~c).toNat ≤ (left - 1).toNat
  · rw [decide_eq_true h]
    have hm : (0 - cw true : BitVec 32) = BitVec.allOnes 32 := by decide
    rw [hm, BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor, BitVec.toNat_add, e2, o]
    rw [e1, e2] at h
    omega
  · rw [decide_eq_false h]
    have hm : (0 - cw false : BitVec 32) = 0 := by decide
    have z (x : BitVec 32) : x &&& 0 = 0 := by simp
    have z' (x : BitVec 32) : x ^^^ 0 = x := by simp
    rw [hm, z, z', BitVec.toNat_add, e1, o]
    rw [e1, e2] at h
    omega

/-! ## On past the call's blocks -/

theorem adv_ok (s : State) {Q : Addr} (hq : State.addr (s.gpr .r6) = Q)
    (hfit : (s.gpr .r6).toNat + 16 ≤ 2 ^ 32)
    (rq : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 12) 4) :
    ∃ s', runBlock isa adv s = some s' ∧
      s'.gpr .r8 = s.gpr .r8 - s.gpr .r9 ∧ s'.gpr .r7 = s.gpr .r7 + (s.gpr .r9 <<< 4) ∧
      s'.z = (s.mem.readW (Q + BitVec.ofNat 64 12) 32 - 0 == 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r7 → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a12 : State.addr (s.gpr .r6 + BitVec.ofNat 32 12) = Q + BitVec.ofNat 64 12 := by
    rw [addr_add (by omega_using [hfit]), hq]
  have i0 (t : State) : (Op2.imm 0).eval t = some 0 := Proof.MdStream.Arm.op2_imm (by decide)
  have sh (t : State) : (Op2.shifted .r9 .lsl 4).eval t = some (t.gpr .r9 <<< 4) :=
    Proof.MdStream.Arm.op2_lsl (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, adv, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
      i0, sh, Proof.MdStream.Arm.op2_reg, State.load32, Option.map_some, Nat.reduceLT,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, a12, rq]
    rfl, ?_⟩
  refine ⟨by simp [gpr_setReg, gpr_subFlags], by simp [gpr_setReg, gpr_subFlags], ?_,
    fun r h₁ h₂ h₃ => by simp [gpr_setReg, gpr_subFlags, h₁, h₂, h₃], rfl, rfl, rfl, rfl⟩
  simp only [z_subFlags, gpr_setReg, reduceCtorEq, ↓reduceIte, mem_setReg]

/-! ## The carry into the first 96 bits -/

/-- The memory after `carry` on the block at `Q`. -/
def carryMem (m : Mem) (Q : Addr) : Mem :=
  let a2 := rev (m.readW (Q + BitVec.ofNat 64 8) 32)
  let a1 := rev (m.readW (Q + BitVec.ofNat 64 4) 32)
  let a0 := rev (m.readW Q 32)
  let t2 := cw (carryOut a2 1)
  let t1 := carryOut a1 t2
  ((m.writeW (Q + BitVec.ofNat 64 8) (rev (a2 + 1))).writeW (Q + BitVec.ofNat 64 4) (rev (a1 + t2))).writeW Q
    (rev (a0 + 0 + (if t1 then 1 else 0)))

theorem carry_ok (s : State) {Q : Addr} (hq : State.addr (s.gpr .r6) = Q)
    (hfit : (s.gpr .r6).toNat + 16 ≤ 2 ^ 32)
    (hr : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 d) n)
    (hw : ∀ d n, d + n ≤ 16 → InRegions s.wr (Q + BitVec.ofNat 64 d) n) :
    ∃ s', runBlock isa carry s = some s' ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = carryMem s.mem Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a (d : Nat) (hd : d < 16) : State.addr (s.gpr .r6 + BitVec.ofNat 32 d) = Q + BitVec.ofNat 64 d := by
    rw [addr_add (by omega_using [hfit, hd]), hq]
  have a0 : State.addr (s.gpr .r6 + BitVec.ofNat 32 0) = Q := by rw [a 0 (by decide)]; simp
  have r0 : InRegions (s.rd ++ s.wr) Q 4 := by simpa using hr 0 4 (by decide)
  have w0 : InRegions s.wr Q 4 := by simpa using hw 0 4 (by decide)
  have i0 (t : State) : (Op2.imm 0).eval t = some 0 := Proof.MdStream.Arm.op2_imm (by decide)
  have i1 (t : State) : (Op2.imm 1).eval t = some 1 := Proof.MdStream.Arm.op2_imm (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, carry, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
      i0, i1, Proof.MdStream.Arm.op2_reg, State.load32, State.store32, Option.map_some, Nat.reduceLT,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, c_setReg, gpr_addFlags, mem_addFlags, rd_addFlags,
      wr_addFlags, c_addFlags, a0, a 4 (by decide), a 8 (by decide),
      r0, hr 4 4 (by decide), hr 8 4 (by decide), w0, hw 4 4 (by decide), hw 8 4 (by decide)]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ h₃ h₄ => by simp [gpr_setReg, gpr_addFlags, h₁, h₂, h₃, h₄], rfl, rfl, rfl, rfl⟩

theorem cw_toNat (c : Bool) : (cw c).toNat = c.toNat := by cases c <;> rfl

theorem carryOut_toNat (x y : BitVec 32) : (carryOut x y).toNat = (x.toNat + y.toNat) / 2 ^ 32 := by
  have := x.isLt
  have := y.isLt
  by_cases h : 2 ^ 32 ≤ x.toNat + y.toNat
  · rw [carryOut, decide_eq_true h]; simp only [Bool.toNat_true]; omega_using [h]
  · rw [carryOut, decide_eq_false h]; simp only [Bool.toNat_false]; omega_using [h]

theorem add_cw_toNat (a : BitVec 32) (c : Bool) : (a + cw c).toNat = (a.toNat + c.toNat) % 2 ^ 32 := by
  rw [BitVec.toNat_add, cw_toNat]

theorem add_ite_toNat (a : BitVec 32) (c : Bool) :
    (a + 0 + (if c then 1 else 0)).toNat = (a.toNat + c.toNat) % 2 ^ 32 := by
  have e₀ : (0 : BitVec 32).toNat = 0 := rfl
  cases c
  · have e : ((if false = true then 1 else 0 : BitVec 32)).toNat = 0 := rfl
    rw [BitVec.toNat_add, BitVec.toNat_add, e₀, e]; simp only [Bool.toNat_false]; omega_using []
  · have e : ((if true = true then 1 else 0 : BitVec 32)).toNat = 1 := rfl
    rw [BitVec.toNat_add, BitVec.toNat_add, e₀, e]; simp only [Bool.toNat_true]; omega_using []

open VG.Proof.AesCtr (rv32 bytesAt_append bytesAt_writeW_rv32 bytesAt_writeW_sep bytesAt_writeW_sep'
  bytesAt_rv32 toNat_append toNat_ofNat length_ofNat ofNat_add ofNat_congr) in
/-- The block at `P` plus `2³²` as words: the reversed words `rv32 wᵢ` stored
at `P + 8`, `P + 4` and `P`, each the word read there plus the carry out of
the words after it, the first of them plus 1; the last word is kept. -/
theorem add32_words32 (m : Mem) (P : Addr) (w0 w1 w2 : BitVec 32)
    (h2 : w2.toNat = ((rv32 (m.readW (P + BitVec.ofNat 64 8) 32)).toNat + 1) % 2 ^ 32)
    (h1 : w1.toNat = ((rv32 (m.readW (P + BitVec.ofNat 64 4) 32)).toNat +
      ((rv32 (m.readW (P + BitVec.ofNat 64 8) 32)).toNat + 1) / 2 ^ 32) % 2 ^ 32)
    (h0 : w0.toNat = ((rv32 (m.readW P 32)).toNat +
      ((rv32 (m.readW (P + BitVec.ofNat 64 4) 32)).toNat +
        ((rv32 (m.readW (P + BitVec.ofNat 64 8) 32)).toNat + 1) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32) :
    bytesAt (((m.writeW (P + BitVec.ofNat 64 8) (rv32 w2)).writeW (P + BitVec.ofNat 64 4) (rv32 w1)).writeW P
      (rv32 w0)) P 16 = Spec.Ctr.ofNat (Spec.Ctr.toNat (bytesAt m P 16) + 2 ^ 32) 16 := by
  have split (m' : Mem) : bytesAt m' P 16 = bytesAt m' P 4 ++ (bytesAt m' (P + BitVec.ofNat 64 4) 4 ++
      (bytesAt m' (P + BitVec.ofNat 64 8) 4 ++ bytesAt m' (P + BitVec.ofNat 64 12) 4)) := by
    rw [show (16 : Nat) = 4 + 12 from rfl, bytesAt_append, show (12 : Nat) = 4 + 8 from rfl, bytesAt_append,
      show (8 : Nat) = 4 + 4 from rfl, bytesAt_append, Offset.add_add_eq P (show 4 + 4 = 8 from rfl),
      Offset.add_add_eq P (show 8 + 4 = 12 from rfl)]
  rw [split, split m]
  -- The words of the result.
  rw [bytesAt_writeW_rv32, bytesAt_writeW_sep _ _ _ (by decide) (by decide), bytesAt_writeW_rv32,
    bytesAt_writeW_sep _ _ _ (by decide) (by decide), bytesAt_writeW_sep' _ _ _ (by decide) (by decide),
    bytesAt_writeW_rv32, bytesAt_writeW_sep _ _ _ (by decide) (by decide),
    bytesAt_writeW_sep' _ _ _ (by decide) (by decide), bytesAt_writeW_sep' _ _ _ (by decide) (by decide)]
  -- The words of the counter block.
  rw [bytesAt_rv32 m P, bytesAt_rv32 m (P + BitVec.ofNat 64 4), bytesAt_rv32 m (P + BitVec.ofNat 64 8),
    bytesAt_rv32 m (P + BitVec.ofNat 64 12)]
  have b0 := (rv32 (m.readW P 32)).isLt
  have b1 := (rv32 (m.readW (P + BitVec.ofNat 64 4) 32)).isLt
  have b2 := (rv32 (m.readW (P + BitVec.ofNat 64 8) 32)).isLt
  have b3 := (rv32 (m.readW (P + BitVec.ofNat 64 12) 32)).isLt
  generalize (rv32 (m.readW P 32)).toNat = A0 at *
  generalize (rv32 (m.readW (P + BitVec.ofNat 64 4) 32)).toNat = A1 at *
  generalize (rv32 (m.readW (P + BitVec.ofNat 64 8) 32)).toNat = A2 at *
  generalize (rv32 (m.readW (P + BitVec.ofNat 64 12) 32)).toNat = A3 at *
  have hv : Spec.Ctr.toNat (Spec.Ctr.ofNat A0 4 ++ (Spec.Ctr.ofNat A1 4 ++ (Spec.Ctr.ofNat A2 4 ++
      Spec.Ctr.ofNat A3 4))) = A0 * 2 ^ 96 + A1 * 2 ^ 64 + A2 * 2 ^ 32 + A3 := by
    simp only [toNat_append, toNat_ofNat, length_ofNat, List.length_append, Nat.reducePow, Nat.reduceAdd]
    simp only [Nat.reducePow] at b0 b1 b2 b3
    rw [Nat.mod_eq_of_lt b0, Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt b2, Nat.mod_eq_of_lt b3]
    omega_using []
  rw [hv, show (16 : Nat) = 4 + (4 + (4 + 4)) from rfl, ofNat_add, ofNat_add, ofNat_add]
  simp only [Nat.reducePow, Nat.reduceAdd] at *
  exact congr (congrArg HAppend.hAppend (ofNat_congr (by omega_using [h0, b0, b1, b2, b3])))
    (congr (congrArg HAppend.hAppend (ofNat_congr (by omega_using [h1, b0, b1, b2, b3])))
      (congr (congrArg HAppend.hAppend (ofNat_congr (by omega_using [h2, b0, b1, b2, b3])))
        (ofNat_congr (by omega_using [b0, b1, b2, b3]))))

theorem carryMem_bytes (m : Mem) (Q : Addr) :
    bytesAt (carryMem m Q) Q 16 = Spec.Ctr.ofNat (Spec.Ctr.toNat (bytesAt m Q 16) + 2 ^ 32) 16 := by
  have e₁ : (1 : BitVec 32).toNat = 1 := rfl
  apply add32_words32
  · show (rev _ + 1).toNat = ((rev _).toNat + 1) % 2 ^ 32
    rw [BitVec.toNat_add]; rfl
  · show (rev _ + cw _).toNat = _
    rw [add_cw_toNat, carryOut_toNat, e₁]; rfl
  · show (rev _ + 0 + _).toNat = _
    rw [add_ite_toNat, carryOut_toNat, cw_toNat, carryOut_toNat, e₁]; rfl

theorem carryMem_frame (m : Mem) (Q : Addr) : Frame [⟨Q, 16⟩] m (carryMem m Q) :=
  (((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base Q (d := 8) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base Q (d := 4) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (by simpa using Offset.contains_base Q (d := 0) (n := 4) (k := 16) (by decide) (by decide))

end VG.Proof.AesCtr.Arm
