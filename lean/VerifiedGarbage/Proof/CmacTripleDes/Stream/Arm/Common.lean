module

import VerifiedGarbage.Proof.MdStream.Arm.Common
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.CmacTripleDes.Stream
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.CmacTripleDes.Arm.RoundLit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Spec.Cmac.TripleDesContract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `CmacTripleDes.Stream.Arm.Contract`, which this module and modules that import it used -/

section

/-!
# Streaming TDEA-CMAC on ARMv7: the contracts the proofs are written against

The artifacts' contracts are the shared ones of
`Spec/Cmac/TripleDesContract.lean`, with the working space as an argument
(`Proof/CmacTripleDes/StreamScratch.lean`), which imply these
(`Verified.lean`). `stream_init` uses no stack; `absorb` and `finish` push
the working space's address, the stack argument of the code of `update` and
`finalize`, below the stack pointer: so the 4 bytes below it may not overlap
any buffer.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.Arm

open VG VG.Arm

/-- `vg_cmac_triple_des_stream_init(state = r0, key = r1, key_len = r2, scratch = r3)`. -/
def initArm : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 416⟩
    let key : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
    let scr : Region := ⟨State.addr (s.gpr .r3), 640⟩
    s.rd = [key] ∧ s.wr = [state, scr] ∧ state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧
      (s.gpr .r0).toNat + 416 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 640 ≤ 2 ^ 32 ∧ Spec.TripleDes.validKey (s.gpr .r2).toNat
  post s s' :=
    Spec.Cmac.tdesRepr s'.mem (State.addr (s.gpr .r0))
      (Spec.TripleDes.bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat) []
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3

/-- `count`, in `r2:r3` (AAPCS: the low word in `r2`). -/
def countArm (s : State) : BitVec 64 := s.gpr .r3 ++ s.gpr .r2

/-- `vg_cmac_triple_des_absorb(state = r0, count = r2:r3, data = [sp], len = [sp, #4], scratch = [sp, #8])`. -/
def absorbArm : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 416⟩
    let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 2), 688⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    let blw : Region := ⟨State.addr s.sp - 4, 4⟩
    s.rd = [data, args] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      args.Disjoint state ∧ args.Disjoint scr ∧
      blw.Disjoint state ∧ blw.Disjoint data ∧ blw.Disjoint scr ∧
      (s.gpr .r0).toNat + 416 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
      (stackArg s 2).toNat + 688 ≤ 2 ^ 32 ∧ 4 ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32
  post s s' :=
    ∀ key msg, Spec.Cmac.tdesRepr s.mem (State.addr (s.gpr .r0)) key msg →
      countArm s = BitVec.ofNat 64 msg.length → msg.length + (stackArg s 1).toNat < 2 ^ 64 →
      Spec.Cmac.tdesRepr s'.mem (State.addr (s.gpr .r0)) key
        (msg ++ Spec.Aes.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

/-- `vg_cmac_triple_des_finish(state = r0, count = r2:r3, out = [sp], scratch = [sp, #4])`. -/
def finishArm : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 416⟩
    let out : Region := ⟨State.addr (stackArg s 0), 8⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 640⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let blw : Region := ⟨State.addr s.sp - 4, 4⟩
    s.rd = [args] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scr ∧
      blw.Disjoint state ∧ blw.Disjoint out ∧ blw.Disjoint scr ∧
      (s.gpr .r0).toNat + 416 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 8 ≤ 2 ^ 32 ∧
      (stackArg s 1).toNat + 640 ≤ 2 ^ 32 ∧ 4 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' :=
    ∀ key msg, Spec.Cmac.tdesRepr s.mem (State.addr (s.gpr .r0)) key msg →
      countArm s = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem (State.addr (stackArg s 0)) 8 = Spec.Cmac.tdesCmac key 8 msg
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.CmacTripleDes.Stream.Arm

end

end

/-!
# Streaming TDEA-CMAC on ARMv7: arithmetic and memory

`count` in a register pair (`toNat_append32`, `or_beq_zero`), the number of
bytes held back as the code computes it from the low word of `count`
(`held_lo`), conditions, and bytes written.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.Arm

open VG VG.Arm
open VG.Proof.CmacTripleDes.Stream (held held_pos held_zero)
open VG.Proof.MdStream.Arm (eval_eq eval_ne ofNat_beq_zero sub_ofNat cmp0)

/-! ## `count` in a register pair -/

theorem toNat_append32 (hi lo : BitVec 32) : (hi ++ lo : BitVec 64).toNat = hi.toNat * 2 ^ 32 + lo.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]

/-- A count in a register pair is zero iff the OR of its words is. -/
theorem or_beq_zero {lo hi : BitVec 32} {x : Nat} (h : (hi ++ lo : BitVec 64) = BitVec.ofNat 64 x)
    (hx : x < 2 ^ 64) : ((lo ||| hi) - 0 == 0) = decide (x = 0) := by
  have e := congrArg BitVec.toNat h
  rw [toNat_append32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at e
  rw [show (lo ||| hi) - 0 = lo ||| hi from BitVec.sub_zero _]
  by_cases hx0 : x = 0
  · have h1 : lo = 0 := BitVec.eq_of_toNat_eq (by show lo.toNat = 0; omega_using [e, hx0])
    have h2 : hi = 0 := BitVec.eq_of_toNat_eq (by show hi.toNat = 0; omega_using [e, hx0])
    simp [h1, h2, hx0]
  · rw [decide_eq_false hx0, beq_eq_false_iff_ne]
    intro h0
    obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h0
    rw [h1, h2] at e
    rw [BitVec.toNat_zero] at e
    omega_using [e, hx0]

theorem count_eq (s : State) : (s.gpr .r3 ++ s.gpr .r2 : BitVec 64) = BitVec.ofNat 64 (countArm s).toNat :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]; rfl)

theorem and7 (x : BitVec 32) : (x &&& 7).toNat = x.toNat % 8 := by
  rw [BitVec.toNat_and, show (7 : BitVec 32).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The number of bytes held back for a nonzero count, as `sub 1; and 7;
add 1` computes it from its low word. -/
theorem held_lo {lo hi : BitVec 32} {x : Nat} (h : (hi ++ lo : BitVec 64) = BitVec.ofNat 64 x)
    (hx : x < 2 ^ 64) (h0 : x ≠ 0) : ((lo - 1) &&& 7) + 1 = BitVec.ofNat 32 (held x) := by
  have e := congrArg BitVec.toNat h
  rw [toNat_append32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at e
  rw [held_pos (by omega_using [h0])]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, and7, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
  have := lo.isLt
  have := hi.isLt
  omega_using [h0, e]

/-! ## Conditions -/

theorem eq_iff (s : State) {k : Nat} (h : s.z = (BitVec.ofNat 32 k - 0 == 0)) (hk : k < 2 ^ 32) :
    isa.eval .eq s = some (decide (k = 0)) := by
  show VG.Arm.eval .eq s = _
  rw [eval_eq, h, cmp0 hk]

/-- A pointer plus an offset that does not wrap. -/
theorem toNat_add_ofNat {p : BitVec 32} {k : Nat} (h : p.toNat + k < 2 ^ 32) :
    (p + BitVec.ofNat 32 k).toNat = p.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_using [h]), Nat.mod_eq_of_lt h]

theorem toNat_ofNat64 {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem add_ofNat32 (p : BitVec 32) (a b : Nat) :
    p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## Bytes written -/

section
open VG.WriteBytes

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} (h : xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i h1 _
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega_arith : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) =
      Spec.Aes.bytesAt m p r ++ xs := by
  rw [Proof.Cmac.Stream.bytesAt_append, bytesAt_writeBytes_self _ _ (by omega_using [h])]
  congr 1
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact writeBytes_before m p xs (List.mem_range.mp hi) (by omega_using [h])

end

end VG.Proof.CmacTripleDes.Stream.Arm
