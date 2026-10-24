module

import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top1
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
public import VerifiedGarbage.Impl.Dsa.Arm.ProbablePrime
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Base
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.Arm.Target

/-! # DSA's probable-prime test on ARMv7: the arguments to the allocation (`pre_ok`)

After the allocation of 32 bytes at `aA s`, `pre` stores the words
`allocVals` there, `used` into `r2` and `L` into `r1`; only `r1`–`r3`, `r12`
and the allocation change.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_str wp_mov wp_dp wp_ldr op2_imm op2_lsl dpVal)
open VG.Proof.Bignum.Arm (wp_stackAddr)
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords len draw checks)
open VG.Impl.RsaKeyGen.Arm.Candidate (aoR aoRl aoP aoS aoSl aoEl aoPl)

/-- The allocation's base. -/
abbrev aA (s : State) : Addr := State.addr (s.sp - BitVec.ofNat 32 32)

/-- The allocation's words, by offset. -/
def allocVals (bits : Nat) (s : State) : List (Nat × BitVec 32) :=
  [(0, BitVec.ofNat 32 (len bits)), (4, s.gpr .r0), (8, BitVec.ofNat 32 (draw bits)), (12, s.gpr .r2),
    (16, s.gpr .r3), (20, s.gpr .r0 + BitVec.ofNat 32 keyOff), (24, BitVec.ofNat 32 (keyWords bits)),
    (28, BitVec.ofNat 32 (checks bits))]

/-- The immediates `pre` moves are encodable. -/
abbrev PreEnc (bits : Nat) : Prop :=
  encodable (BitVec.ofNat 32 (keyWords bits / 32)) = true ∧ encodable (BitVec.ofNat 32 (len bits)) = true ∧
    encodable (BitVec.ofNat 32 (draw bits)) = true ∧ encodable (BitVec.ofNat 32 (checks bits)) = true ∧
    encodable (BitVec.ofNat 32 (8 * Impl.Dsa.Arm.ProbablePrime.words bits)) = true ∧ keyWords bits % 32 = 0 ∧ keyWords bits < 2 ^ 32

theorem readW_writeW_off (m : Mem) (A : Addr) {o p : Nat} (v : BitVec 32) (h : o + 4 ≤ p ∨ p + 4 ≤ o)
    (ho : o + 4 ≤ 2 ^ 64) (hp : p + 4 ≤ 2 ^ 64) :
    (m.writeW (A + BitVec.ofNat 64 o) v).readW (A + BitVec.ofNat 64 p) 32 = m.readW (A + BitVec.ofNat 64 p) 32 :=
  Mem.readW_writeW_sep (Offset.sep A (by omega) hp ho) (by decide)

section
variable {s : State}

theorem aA_add (h : 32 ≤ s.sp.toNat) {o : Nat} (ho : o ≤ 32) :
    State.addr (s.sp - BitVec.ofNat 32 32 + BitVec.ofNat 32 0 + BitVec.ofNat 32 o) = aA s + BitVec.ofNat 64 o := by
  rw [BitVec.add_zero]
  exact addr_add (by rw [sub_toNat' h]; omega)

/-- The allocation's arguments. -/
theorem pre_ok {bits : Nat} (enc : PreEnc bits) (h1 : 144 ≤ s.sp.toNat) (h2 : s.sp.toNat + 4 ≤ 2 ^ 32)
    (hA : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4) :
    WP isa (.block (Impl.Dsa.Arm.ProbablePrime.pre bits)) (allocated 32 s) fun t =>
      Rest [.r1, .r2, .r3, .r12] (allocated 32 s) t ∧ Frame [⟨aA s, 32⟩] s.mem t.mem ∧
      (∀ p ∈ allocVals bits s, t.mem.readW (aA s + BitVec.ofNat 64 p.1) 32 = p.2) ∧
      t.gpr .r1 = BitVec.ofNat 32 (8 * Impl.Dsa.Arm.ProbablePrime.words bits) ∧ t.gpr .r2 = stackArg s 0 := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := enc
  have hs := s.sp.isLt
  have hsp : (allocated 32 s).sp = s.sp - BitVec.ofNat 32 32 := rfl
  have hwr : (allocated 32 s).wr = ⟨aA s, 32⟩ :: s.wr := rfl
  have win : ∀ o, o + 4 ≤ 32 → InRegions (allocated 32 s).wr (aA s + BitVec.ofNat 64 o) 4 := fun o ho =>
    ⟨_, by rw [hwr]; exact List.mem_cons_self, Offset.contains_base _ ho (by omega)⟩
  unfold Impl.Dsa.Arm.ProbablePrime.pre
  refine wp_stackAddr (r := .r12) (d := 0) (by decide) fun u0 h0 => ?_
  have r12 : ∀ {u : State}, u.gpr .r12 = u0.gpr .r12 → ∀ o, o ≤ 32 →
      State.addr (u.gpr .r12 + BitVec.ofNat 32 o) = aA s + BitVec.ofNat 64 o := fun hu o ho => by
    rw [hu, h0.gpr, hsp]; exact aA_add (by omega) ho
  simp only [aoR, aoRl, aoP, aoS, aoSl, aoEl, aoPl, Impl.Dsa.Arm.ProbablePrime.aoChk]
  refine wp_str (a := aA s + BitVec.ofNat 64 12) (by decide) (r12 rfl _ (by decide))
    (by rw [h0.wr]; exact win 12 (by decide)) fun u1 m1 => ?_
  refine wp_str (a := aA s + BitVec.ofNat 64 16) (by decide) (r12 (by rw [m1.gpr]) _ (by decide))
    (by rw [m1.wr, h0.wr]; exact win 16 (by decide)) fun u2 m2 => ?_
  refine wp_str (a := aA s + BitVec.ofNat 64 4) (by decide) (r12 (by rw [m2.gpr, m1.gpr]) _ (by decide))
    (by rw [m2.wr, m1.wr, h0.wr]; exact win 4 (by decide)) fun u3 m3 => ?_
  refine wp_dp (op2_imm (by decide)) fun u4 h4 => ?_
  refine wp_str (a := aA s + BitVec.ofNat 64 20) (by decide)
    (r12 (by rw [h4.other _ (by decide), m3.gpr, m2.gpr, m1.gpr]) _ (by decide))
    (by rw [h4.wr, m3.wr, m2.wr, m1.wr, h0.wr]; exact win 20 (by decide)) fun u5 m5 => ?_
  refine wp_mov (op2_imm e1) fun u6 h6 => wp_mov (op2_lsl (by decide)) fun u7 h7 => ?_
  have g7 : ∀ r, r ≠ .r3 → u7.gpr r = u0.gpr r := fun r hr => by
    rw [h7.other _ hr, h6.other _ hr, m5.gpr, h4.other _ hr, m3.gpr, m2.gpr, m1.gpr]
  have w7 : u7.wr = (allocated 32 s).wr := by rw [h7.wr, h6.wr, m5.wr, h4.wr, m3.wr, m2.wr, m1.wr, h0.wr]
  refine wp_str (a := aA s + BitVec.ofNat 64 24) (by decide) (r12 (g7 _ (by decide)) _ (by decide))
    (by rw [w7]; exact win 24 (by decide)) fun u8 m8 => ?_
  refine wp_mov (op2_imm e2) fun u9 h9 => ?_
  refine wp_str (a := aA s + BitVec.ofNat 64 0) (by decide)
    (r12 (by rw [h9.other _ (by decide), m8.gpr, g7 _ (by decide)]) _ (by decide))
    (by rw [h9.wr, m8.wr, w7]; exact win 0 (by decide)) fun u10 m10 => ?_
  refine wp_mov (op2_imm e3) fun u11 h11 => ?_
  have g11 : ∀ r, r ≠ .r3 → u11.gpr r = u0.gpr r := fun r hr => by
    rw [h11.other _ hr, m10.gpr, h9.other _ hr, m8.gpr, g7 _ hr]
  have w11 : u11.wr = (allocated 32 s).wr := by rw [h11.wr, m10.wr, h9.wr, m8.wr, w7]
  refine wp_str (a := aA s + BitVec.ofNat 64 8) (by decide) (r12 (g11 _ (by decide)) _ (by decide))
    (by rw [w11]; exact win 8 (by decide)) fun u12 m12 => ?_
  refine wp_mov (op2_imm e4) fun u13 h13 => ?_
  refine wp_str (a := aA s + BitVec.ofNat 64 28) (by decide)
    (r12 (by rw [h13.other _ (by decide), m12.gpr, g11 _ (by decide)]) _ (by decide))
    (by rw [h13.wr, m12.wr, w11]; exact win 28 (by decide)) fun u14 m14 => ?_
  have g14 : ∀ r, r ≠ .r3 → u14.gpr r = u0.gpr r := fun r hr => by
    rw [m14.gpr, h13.other _ hr, m12.gpr, g11 _ hr]
  have mem14 : u14.mem = ((((((((s.mem.writeW (aA s + BitVec.ofNat 64 12) (s.gpr .r2)).writeW
      (aA s + BitVec.ofNat 64 16) (s.gpr .r3)).writeW (aA s + BitVec.ofNat 64 4) (s.gpr .r0)).writeW
      (aA s + BitVec.ofNat 64 20) (s.gpr .r0 + BitVec.ofNat 32 keyOff)).writeW
      (aA s + BitVec.ofNat 64 24) (BitVec.ofNat 32 (keyWords bits))).writeW
      (aA s + BitVec.ofNat 64 0) (BitVec.ofNat 32 (len bits))).writeW
      (aA s + BitVec.ofNat 64 8) (BitVec.ofNat 32 (draw bits))).writeW
      (aA s + BitVec.ofNat 64 28) (BitVec.ofNat 32 (checks bits))) := by
    have k7 : u7.gpr .r3 = BitVec.ofNat 32 (keyWords bits) := by
      rw [h7.gpr, h6.gpr]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (a := keyWords bits / 32) (by omega)]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt e7]
      omega
    rw [m14.mem, h13.gpr, h13.mem, m12.mem, h11.gpr, h11.mem, m10.mem, h9.gpr, h9.mem, m8.mem, k7, h7.mem,
      h6.mem, m5.mem, h4.gpr, dpVal, h4.mem, m3.mem, m2.mem, m1.mem, h0.mem]
    simp only [m1.gpr, m2.gpr, m3.gpr, h0.other .r0 (by decide), h0.other .r2 (by decide),
      h0.other .r3 (by decide)]
    rfl
  have argA : State.addr (u14.gpr .r12 + BitVec.ofNat 32 32) = stackArgAddr s 0 := by
    rw [g14 _ (by decide), h0.gpr, hsp, BitVec.add_zero, BitVec.sub_add_cancel]
    simp [stackArgAddr]
  have rd14 : u14.rd ++ u14.wr = s.rd ++ (⟨aA s, 32⟩ :: s.wr) := by
    rw [m14.rd, m14.wr, h13.rd, h13.wr, m12.rd, m12.wr, w11, h11.rd, m10.rd, h9.rd, m8.rd, h7.rd, h6.rd, m5.rd, h4.rd,
      m3.rd, m2.rd, m1.rd, h0.rd]; rfl
  refine wp_ldr (a := stackArgAddr s 0) (by decide) argA (by
    rw [rd14]; obtain ⟨r, hr, hc⟩ := hA; refine ⟨r, ?_, hc⟩
    rcases List.mem_append.mp hr with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)) fun u15 h15 => ?_
  refine wp_mov (op2_imm e5) fun t ht => WP.block_nil ?_
  have fr : Frame [⟨aA s, 32⟩] s.mem u14.mem := by
    rw [mem14]
    have c : ∀ o, o + 4 ≤ 32 → (⟨aA s, 32⟩ : Region).Contains (aA s + BitVec.ofNat 64 o) (32 / 8) :=
      fun o ho => Offset.contains_base _ ho (by omega)
    exact (((((((((Frame.refl _ _).writeW List.mem_cons_self _ (c 12 (by decide))).writeW List.mem_cons_self _
      (c 16 (by decide))).writeW List.mem_cons_self _ (c 4 (by decide))).writeW List.mem_cons_self _
      (c 20 (by decide))).writeW List.mem_cons_self _ (c 24 (by decide))).writeW List.mem_cons_self _
      (c 0 (by decide))).writeW List.mem_cons_self _ (c 8 (by decide))).writeW List.mem_cons_self _
      (c 28 (by decide)))
  have eA : stackArgAddr s 0 = aA s + BitVec.ofNat 64 32 := by
    rw [← argA, g14 _ (by decide), h0.gpr, hsp, BitVec.add_zero]
    exact addr_add (by rw [sub_toNat' (by omega)]; omega)
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, by rw [ht.mem, h15.mem]; exact fr, fun p hp => ?_, ht.gpr, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ht.other _ hr.1, h15.other _ hr.2.1, g14 _ hr.2.2.1, h0.other _ hr.2.2.2]
  · rw [ht.rd, h15.rd, m14.rd, h13.rd, m12.rd, h11.rd, m10.rd, h9.rd, m8.rd, h7.rd, h6.rd, m5.rd, h4.rd,
      m3.rd, m2.rd, m1.rd, h0.rd]
  · rw [ht.wr, h15.wr, m14.wr, h13.wr, m12.wr, w11]
  · rw [ht.sp, h15.sp, m14.sp, h13.sp, m12.sp, h11.sp, m10.sp, h9.sp, m8.sp, h7.sp, h6.sp, m5.sp, h4.sp,
      m3.sp, m2.sp, m1.sp, h0.sp]
  · rw [ht.mem, h15.mem, mem14]
    simp only [allocVals, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := first | decide | omega) only [readW_writeW_off, Mem.readW_writeW_self32]
  · rw [ht.other _ (by decide), h15.gpr, mem14]
    simp only [stackArg]
    rw [eA]
    simp (disch := first | decide | omega) only [readW_writeW_off]

end

end VG.Proof.Dsa.Arm.Prime
