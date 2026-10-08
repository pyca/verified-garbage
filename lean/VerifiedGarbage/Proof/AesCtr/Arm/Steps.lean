import VerifiedGarbage.Proof.AesCtr.Inc
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.AesCbc.Arm.Body
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Impl.AesCtr.Arm

/-!
# AES-CTR on ARMv7: the increment

`incr` run once, with its memory as explicit writes (`incMem`): four words,
loaded and byte-reversed, the last plus 1 and each other plus the carry out
of the one after it (taken into `r12` with `adc`), reversed again and
stored. `incMem_bytes`: the block it writes is `Spec.Ctr.inc` of the one it
read.
-/

namespace VG.Proof.AesCtr.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCtr.Arm
open VG.Spec.Aes (bytesAt)

theorem gpr_addFlags (s : State) (x y : BitVec 32) : (addFlags s x y).gpr = s.gpr := rfl
theorem mem_addFlags (s : State) (x y : BitVec 32) : (addFlags s x y).mem = s.mem := rfl
theorem rd_addFlags (s : State) (x y : BitVec 32) : (addFlags s x y).rd = s.rd := rfl
theorem wr_addFlags (s : State) (x y : BitVec 32) : (addFlags s x y).wr = s.wr := rfl
theorem sp_addFlags (s : State) (x y : BitVec 32) : (addFlags s x y).sp = s.sp := rfl
theorem c_addFlags (s : State) (x y : BitVec 32) :
    (addFlags s x y).c = decide (2 ^ 32 ≤ x.toNat + y.toNat) := rfl

/-- The carry out of `x + y`. -/
abbrev carry (x y : BitVec 32) : Bool := decide (2 ^ 32 ≤ x.toNat + y.toNat)

/-- A carry as a word, as `mov r12, #0; adc r12, r12, #0` computes it. -/
abbrev cw (c : Bool) : BitVec 32 := 0 + 0 + (if c then 1 else 0)

/-- The memory after `incr` on the block at `Q`. -/
def incMem (m : Mem) (Q : Addr) : Mem :=
  let a3 := rev (m.readW (Q + BitVec.ofNat 64 12) 32)
  let a2 := rev (m.readW (Q + BitVec.ofNat 64 8) 32)
  let a1 := rev (m.readW (Q + BitVec.ofNat 64 4) 32)
  let a0 := rev (m.readW Q 32)
  let t3 := cw (carry a3 1)
  let t2 := cw (carry a2 t3)
  let t1 := carry a1 t2
  (((m.writeW (Q + BitVec.ofNat 64 12) (rev (a3 + 1))).writeW (Q + BitVec.ofNat 64 8) (rev (a2 + t3))).writeW
    (Q + BitVec.ofNat 64 4) (rev (a1 + t2))).writeW Q (rev (a0 + 0 + (if t1 then 1 else 0)))

theorem incr_ok (s : State) {Q : Addr} (hq : State.addr (s.gpr .r6) = Q)
    (hfit : (s.gpr .r6).toNat + 16 ≤ 2 ^ 32)
    (hr : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 d) n)
    (hw : ∀ d n, d + n ≤ 16 → InRegions s.wr (Q + BitVec.ofNat 64 d) n) :
    ∃ s', runBlock isa incr s = some s' ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = incMem s.mem Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a (d : Nat) (hd : d < 16) : State.addr (s.gpr .r6 + BitVec.ofNat 32 d) = Q + BitVec.ofNat 64 d := by
    rw [addr_add (by omega), hq]
  have a0 : State.addr (s.gpr .r6 + BitVec.ofNat 32 0) = Q := by rw [a 0 (by decide)]; simp
  have r0 : InRegions (s.rd ++ s.wr) Q 4 := by simpa using hr 0 4 (by decide)
  have w0 : InRegions s.wr Q 4 := by simpa using hw 0 4 (by decide)
  have i0 (t : State) : (Op2.imm 0).eval t = some 0 := Proof.MdStream.Arm.op2_imm (by decide)
  have i1 (t : State) : (Op2.imm 1).eval t = some 1 := Proof.MdStream.Arm.op2_imm (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, incr, runBlock_cons, runStep_some, runBlock_nil, exec,
      i0, i1, Proof.MdStream.Arm.op2_reg, State.load32, State.store32, Option.map_some, Nat.reduceLT,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, c_setReg, gpr_addFlags, mem_addFlags, rd_addFlags,
      wr_addFlags, c_addFlags, a0, a 4 (by decide), a 8 (by decide), a 12 (by decide),
      r0, hr 4 4 (by decide), hr 8 4 (by decide), hr 12 4 (by decide), w0, hw 4 4 (by decide),
      hw 8 4 (by decide), hw 12 4 (by decide)]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ h₃ h₄ h₅ => by simp [gpr_setReg, gpr_addFlags, h₁, h₂, h₃, h₄, h₅], rfl, rfl, rfl, rfl⟩

theorem cw_toNat (c : Bool) : (cw c).toNat = c.toNat := by cases c <;> rfl

theorem carry_toNat (x y : BitVec 32) : (carry x y).toNat = (x.toNat + y.toNat) / 2 ^ 32 := by
  have := x.isLt
  have := y.isLt
  by_cases h : 2 ^ 32 ≤ x.toNat + y.toNat
  · rw [carry, decide_eq_true h]; simp only [Bool.toNat_true]; omega
  · rw [carry, decide_eq_false h]; simp only [Bool.toNat_false]; omega

theorem add_cw_toNat (a : BitVec 32) (c : Bool) : (a + cw c).toNat = (a.toNat + c.toNat) % 2 ^ 32 := by
  rw [BitVec.toNat_add, cw_toNat]

theorem add_ite_toNat (a : BitVec 32) (c : Bool) :
    (a + 0 + (if c then 1 else 0)).toNat = (a.toNat + c.toNat) % 2 ^ 32 := by
  have e₀ : (0 : BitVec 32).toNat = 0 := rfl
  cases c
  · have e : ((if false = true then 1 else 0 : BitVec 32)).toNat = 0 := rfl
    rw [BitVec.toNat_add, BitVec.toNat_add, e₀, e]; simp only [Bool.toNat_false]; omega
  · have e : ((if true = true then 1 else 0 : BitVec 32)).toNat = 1 := rfl
    rw [BitVec.toNat_add, BitVec.toNat_add, e₀, e]; simp only [Bool.toNat_true]; omega

theorem incMem_bytes (m : Mem) (Q : Addr) : bytesAt (incMem m Q) Q 16 = Spec.Ctr.inc (bytesAt m Q 16) := by
  have e₁ : (1 : BitVec 32).toNat = 1 := rfl
  apply AesCtr.inc_words32
  · show (rev _ + 1).toNat = ((rev _).toNat + 1) % 2 ^ 32
    rw [BitVec.toNat_add]; rfl
  · show (rev _ + cw _).toNat = _
    rw [add_cw_toNat, carry_toNat, e₁]; rfl
  · show (rev _ + cw _).toNat = _
    rw [add_cw_toNat, carry_toNat, cw_toNat, carry_toNat, e₁]; rfl
  · show (rev _ + 0 + _).toNat = _
    rw [add_ite_toNat, carry_toNat, cw_toNat, carry_toNat, cw_toNat, carry_toNat, e₁]; rfl

theorem incMem_frame (m : Mem) (Q : Addr) : Frame [⟨Q, 16⟩] m (incMem m Q) :=
  ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base Q (d := 12) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base Q (d := 8) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base Q (d := 4) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (by simpa using Offset.contains_base Q (d := 0) (n := 4) (k := 16) (by decide) (by decide))

end VG.Proof.AesCtr.Arm
