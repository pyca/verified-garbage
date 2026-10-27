module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top1
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
`allocVals` there, those of the size from the second stack argument
(`sizeVals`), `used` into `r2` and `L` into `r1`; only `r1`–`r3`, `r12` and
the allocation change.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_str wp_mov wp_dp wp_ldr op2_imm op2_lsl op2_lsr dpVal)
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

/-- The words `pre` computes from the size, for each size. -/
theorem sizeVals {bits : Nat} (hb : Bits bits) :
    ((BitVec.ofNat 32 bits + 255) >>> 8) <<< 5 = BitVec.ofNat 32 (8 * Impl.Dsa.Arm.ProbablePrime.words bits) ∧
      BitVec.ofNat 32 (8 * Impl.Dsa.Arm.ProbablePrime.words bits) <<< 4 + 32 = BitVec.ofNat 32 (keyWords bits) ∧
      BitVec.ofNat 32 bits >>> 3 = BitVec.ofNat 32 (len bits) ∧
      ((BitVec.ofNat 32 bits + 63) >>> 6) <<< 3 = BitVec.ofNat 32 (draw bits) ∧
      ((BitVec.ofNat 32 bits - 1) >>> 11) <<< 6 + 64 = BitVec.ofNat 32 (checks bits) := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide

theorem readW_writeW_off (m : Mem) (A : Addr) {o p : Nat} (v : BitVec 32) (h : o + 4 ≤ p ∨ p + 4 ≤ o)
    (ho : o + 4 ≤ 2 ^ 64) (hp : p + 4 ≤ 2 ^ 64) :
    (m.writeW (A + BitVec.ofNat 64 o) v).readW (A + BitVec.ofNat 64 p) 32 = m.readW (A + BitVec.ofNat 64 p) 32 :=
  Mem.readW_writeW_sep (Offset.sep A (by omega_arith) hp ho) (by decide)

section
variable {s : State}

theorem aA_add (h : 32 ≤ s.sp.toNat) {o : Nat} (ho : s.sp.toNat + o < 2 ^ 32 + 32) :
    State.addr (s.sp - BitVec.ofNat 32 32 + BitVec.ofNat 32 0 + BitVec.ofNat 32 o) = aA s + BitVec.ofNat 64 o := by
  rw [BitVec.add_zero]
  exact addr_add (by rw [sub_toNat' h]; omega_arith)

/-- Stack argument `i < 2` is readable. -/
theorem argIn (h1 : s.sp.toNat + 8 ≤ 2 ^ 32) (hA : (⟨stackArgAddr s 0, 8⟩ : Region) ∈ s.rd ++ s.wr) {i : Nat}
    (hi : i < 2) : InRegions (s.rd ++ s.wr) (stackArgAddr s i) 4 := by
  refine ⟨_, hA, ?_⟩
  have e : stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (4 * i) := by
    simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]; exact addr_add (by omega_arith)
  rw [e]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem CIn.argsIn {bits : Nat} (h : CIn bits s) : (⟨stackArgAddr s 0, 8⟩ : Region) ∈ s.rd ++ s.wr :=
  List.mem_append_left _ (by rw [h.rd]; exact List.mem_cons_of_mem _ List.mem_cons_self)

/-- The allocation's arguments. -/
theorem pre_ok {bits : Nat} (hb : Bits bits) (h1 : 144 ≤ s.sp.toNat) (h2 : s.sp.toNat + 8 ≤ 2 ^ 32)
    (hA : (⟨stackArgAddr s 0, 8⟩ : Region) ∈ s.rd ++ s.wr) (harg : stackArg s 1 = BitVec.ofNat 32 bits) :
    WP isa (.block Impl.Dsa.Arm.ProbablePrime.pre) (allocated 32 s) fun t =>
      Rest [.r1, .r2, .r3, .r12] (allocated 32 s) t ∧ Frame [⟨aA s, 32⟩] s.mem t.mem ∧
      (∀ p ∈ allocVals bits s, t.mem.readW (aA s + BitVec.ofNat 64 p.1) 32 = p.2) ∧
      t.gpr .r1 = BitVec.ofNat 32 (8 * Impl.Dsa.Arm.ProbablePrime.words bits) ∧ t.gpr .r2 = stackArg s 0 := by
  obtain ⟨v1, v2, v3, v4, v5⟩ := sizeVals hb
  have hs := s.sp.isLt
  have hsp : (allocated 32 s).sp = s.sp - BitVec.ofNat 32 32 := rfl
  have hwr : (allocated 32 s).wr = ⟨aA s, 32⟩ :: s.wr := rfl
  have hrd : (allocated 32 s).rd ++ (allocated 32 s).wr = s.rd ++ (⟨aA s, 32⟩ :: s.wr) := rfl
  have win : ∀ o, o + 4 ≤ 32 → InRegions (allocated 32 s).wr (aA s + BitVec.ofNat 64 o) 4 := fun o ho =>
    ⟨_, by rw [hwr]; exact List.mem_cons_self, Offset.contains_base _ ho (by omega_arith)⟩
  -- The stack arguments, above the allocation.
  have argIn' : ∀ i, i < 2 → InRegions ((allocated 32 s).rd ++ (allocated 32 s).wr) (stackArgAddr s i) 4 :=
    fun i hi => by
      obtain ⟨r, hr, hc⟩ := argIn h2 hA hi; refine ⟨r, ?_, hc⟩
      rw [hrd]; rcases List.mem_append.mp hr with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  have eA : ∀ i, i < 2 → stackArgAddr s i = aA s + BitVec.ofNat 64 (32 + 4 * i) := fun i hi => by
    rw [aA, addr_sub' (by omega_arith), BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    exact addr_add (by omega_arith)
  have eA0 : stackArgAddr s 0 = aA s + BitVec.ofNat 64 32 := eA 0 (by decide)
  have eA1 : stackArgAddr s 1 = aA s + BitVec.ofNat 64 36 := eA 1 (by decide)
  unfold Impl.Dsa.Arm.ProbablePrime.pre Impl.Dsa.Arm.ProbablePrime.wordsOf Impl.Dsa.Arm.ProbablePrime.bitsOf
  simp only [List.cons_append, List.nil_append, aoR, aoRl, aoP, aoS, aoSl, aoEl, aoPl,
    Impl.Dsa.Arm.ProbablePrime.aoChk]
  refine wp_stackAddr (r := .r12) (d := 0) (by decide) fun u0 h0 => ?_
  have r12 : ∀ {u : State}, u.gpr .r12 = u0.gpr .r12 → ∀ o, o ≤ 36 →
      State.addr (u.gpr .r12 + BitVec.ofNat 32 o) = aA s + BitVec.ofNat 64 o := fun hu o ho => by
    rw [hu, h0.gpr, hsp]; exact aA_add (by omega_arith) (by omega_arith)
  have hr12 : ∀ {u : State}, Rest [.r1, .r2, .r3] u0 u → u.gpr .r12 = u0.gpr .r12 := fun R => R.gpr _ (by decide)
  have hwr' : ∀ {u : State}, Rest [.r1, .r2, .r3] u0 u → u.wr = (allocated 32 s).wr := fun R => by
    rw [R.wr, h0.wr]
  have hrd' : ∀ {u : State}, Rest [.r1, .r2, .r3] u0 u →
      u.rd ++ u.wr = (allocated 32 s).rd ++ (allocated 32 s).wr := fun R => by
    rw [R.rd, R.wr, h0.rd, h0.wr]
  -- The arguments.
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
  have R5 : Rest [.r1, .r2, .r3] u0 u5 :=
    ((((m1.rest _).trans (m2.rest _)).trans (m3.rest _)).trans (h4.rest (by simp))).trans (m5.rest _)
  -- The size.
  refine wp_ldr (a := stackArgAddr s 1) (by decide) (by rw [r12 (hr12 R5) 36 (by decide), eA1])
    (by rw [hrd' R5]; exact argIn' 1 (by decide)) fun u6 h6 => ?_
  have R6 : Rest [.r1, .r2, .r3] u0 u6 := R5.trans (h6.rest (by simp))
  have x6 : u6.gpr .r2 = BitVec.ofNat 32 bits := by
    rw [h6.gpr, ← harg, m5.mem, h4.mem, m3.mem, m2.mem, m1.mem, h0.mem]
    show _ = s.mem.readW (stackArgAddr s 1) 32
    rw [eA1]
    simp (disch := first | decide | omega_arith) only [readW_writeW_off]
    rfl
  -- `L`.
  refine wp_dp (op2_imm (by decide)) fun u7 h7 => wp_mov (op2_lsr (by decide)) fun u8 h8 =>
    wp_mov (op2_lsl (by decide)) fun u9 h9 => ?_
  have x9 : u9.gpr .r1 = BitVec.ofNat 32 (8 * Impl.Dsa.Arm.ProbablePrime.words bits) := by
    rw [h9.gpr, h8.gpr, h7.gpr, x6]; simp only [dpVal]; exact v1
  have Q9 : Rest [.r1, .r3] u6 u9 := ((h7.rest (by simp)).trans (h8.rest (by simp))).trans (h9.rest (by simp))
  -- The key working space's words.
  refine wp_mov (op2_lsl (by decide)) fun u10 h10 => wp_dp (op2_imm (by decide)) fun u11 h11 => ?_
  have x11 : u11.gpr .r3 = BitVec.ofNat 32 (keyWords bits) := by
    rw [h11.gpr, h10.gpr, x9]; simp only [dpVal]; exact v2
  have Q11 : Rest [.r1, .r3] u6 u11 := (Q9.trans (h10.rest (by simp))).trans (h11.rest (by simp))
  have R11 : Rest [.r1, .r2, .r3] u0 u11 := R6.trans (Q11.mono (by simp))
  refine wp_str (a := aA s + BitVec.ofNat 64 24) (by decide) (r12 (hr12 R11) _ (by decide))
    (by rw [hwr' R11]; exact win 24 (by decide)) fun u12 m12 => ?_
  -- The candidate's bytes.
  refine wp_mov (op2_lsr (by decide)) fun u13 h13 => ?_
  have r2_12 : u12.gpr .r2 = BitVec.ofNat 32 bits := by rw [m12.gpr, Q11.gpr _ (by decide), x6]
  have x13 : u13.gpr .r3 = BitVec.ofNat 32 (len bits) := by rw [h13.gpr, r2_12, v3]
  have R13 : Rest [.r1, .r2, .r3] u0 u13 := (R11.trans (m12.rest _)).trans (h13.rest (by simp))
  refine wp_str (a := aA s + BitVec.ofNat 64 0) (by decide) (r12 (hr12 R13) _ (by decide))
    (by rw [hwr' R13]; exact win 0 (by decide)) fun u14 m14 => ?_
  -- A witness's octets.
  have r2_14 : u14.gpr .r2 = BitVec.ofNat 32 bits := by rw [m14.gpr, h13.other _ (by decide), r2_12]
  refine wp_dp (op2_imm (by decide)) fun u15 h15 => wp_mov (op2_lsr (by decide)) fun u16 h16 =>
    wp_mov (op2_lsl (by decide)) fun u17 h17 => ?_
  have x17 : u17.gpr .r3 = BitVec.ofNat 32 (draw bits) := by
    rw [h17.gpr, h16.gpr, h15.gpr, r2_14]; simp only [dpVal]; exact v4
  have Q17 : Rest [.r3] u14 u17 := ((h15.rest (by simp)).trans (h16.rest (by simp))).trans (h17.rest (by simp))
  have R17 : Rest [.r1, .r2, .r3] u0 u17 := (R13.trans (m14.rest _)).trans (Q17.mono (by simp))
  refine wp_str (a := aA s + BitVec.ofNat 64 8) (by decide) (r12 (hr12 R17) _ (by decide))
    (by rw [hwr' R17]; exact win 8 (by decide)) fun u18 m18 => ?_
  -- The uniform witnesses needed.
  have r2_18 : u18.gpr .r2 = BitVec.ofNat 32 bits := by rw [m18.gpr, Q17.gpr _ (by decide), r2_14]
  refine wp_dp (op2_imm (by decide)) fun u19 h19 => wp_mov (op2_lsr (by decide)) fun u20 h20 =>
    wp_mov (op2_lsl (by decide)) fun u21 h21 => wp_dp (op2_imm (by decide)) fun u22 h22 => ?_
  have x22 : u22.gpr .r3 = BitVec.ofNat 32 (checks bits) := by
    rw [h22.gpr, h21.gpr, h20.gpr, h19.gpr, r2_18]; simp only [dpVal]; exact v5
  have Q22 : Rest [.r3] u18 u22 :=
    (((h19.rest (by simp)).trans (h20.rest (by simp))).trans (h21.rest (by simp))).trans (h22.rest (by simp))
  have R22 : Rest [.r1, .r2, .r3] u0 u22 := (R17.trans (m18.rest _)).trans (Q22.mono (by simp))
  refine wp_str (a := aA s + BitVec.ofNat 64 28) (by decide) (r12 (hr12 R22) _ (by decide))
    (by rw [hwr' R22]; exact win 28 (by decide)) fun u23 m23 => ?_
  have R23 : Rest [.r1, .r2, .r3] u0 u23 := R22.trans (m23.rest _)
  have mem23 : u23.mem = ((((((((s.mem.writeW (aA s + BitVec.ofNat 64 12) (s.gpr .r2)).writeW
      (aA s + BitVec.ofNat 64 16) (s.gpr .r3)).writeW (aA s + BitVec.ofNat 64 4) (s.gpr .r0)).writeW
      (aA s + BitVec.ofNat 64 20) (s.gpr .r0 + BitVec.ofNat 32 keyOff)).writeW
      (aA s + BitVec.ofNat 64 24) (BitVec.ofNat 32 (keyWords bits))).writeW
      (aA s + BitVec.ofNat 64 0) (BitVec.ofNat 32 (len bits))).writeW
      (aA s + BitVec.ofNat 64 8) (BitVec.ofNat 32 (draw bits))).writeW
      (aA s + BitVec.ofNat 64 28) (BitVec.ofNat 32 (checks bits))) := by
    rw [m23.mem, x22, h22.mem, h21.mem, h20.mem, h19.mem, m18.mem, x17, h17.mem, h16.mem, h15.mem, m14.mem, x13,
      h13.mem, m12.mem, x11, h11.mem, h10.mem, h9.mem, h8.mem, h7.mem, h6.mem, m5.mem, h4.gpr, dpVal, h4.mem,
      m3.mem, m2.mem, m1.mem, h0.mem]
    simp only [m1.gpr, m2.gpr, m3.gpr, h0.other .r0 (by decide), h0.other .r2 (by decide),
      h0.other .r3 (by decide)]
    rfl
  -- `used`.
  refine wp_ldr (a := stackArgAddr s 0) (by decide) (by rw [r12 (hr12 R23) 32 (by decide), eA0])
    (by rw [hrd' R23]; exact argIn' 0 (by decide)) fun t ht => WP.block_nil ?_
  have Q23 : Rest [.r2, .r3] u9 u23 :=
    ((((((((((((((h10.rest (by simp)).trans (h11.rest (by simp))).trans (m12.rest _)).trans
      (h13.rest (by simp))).trans (m14.rest _)).trans (h15.rest (by simp))).trans (h16.rest (by simp))).trans
      (h17.rest (by simp))).trans (m18.rest _)).trans (h19.rest (by simp))).trans (h20.rest (by simp))).trans
      (h21.rest (by simp))).trans (h22.rest (by simp))).trans (m23.rest _))
  have fr : Frame [⟨aA s, 32⟩] s.mem u23.mem := by
    rw [mem23]
    have c : ∀ o, o + 4 ≤ 32 → (⟨aA s, 32⟩ : Region).Contains (aA s + BitVec.ofNat 64 o) (32 / 8) :=
      fun o ho => Offset.contains_base _ ho (by omega_arith)
    exact (((((((((Frame.refl _ _).writeW List.mem_cons_self _ (c 12 (by decide))).writeW List.mem_cons_self _
      (c 16 (by decide))).writeW List.mem_cons_self _ (c 4 (by decide))).writeW List.mem_cons_self _
      (c 20 (by decide))).writeW List.mem_cons_self _ (c 24 (by decide))).writeW List.mem_cons_self _
      (c 0 (by decide))).writeW List.mem_cons_self _ (c 8 (by decide))).writeW List.mem_cons_self _
      (c 28 (by decide)))
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, by rw [ht.mem]; exact fr, fun p hp => ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ht.other _ hr.2.1, R23.gpr _ (by simp [hr.1, hr.2.1, hr.2.2.1]), h0.other _ hr.2.2.2]
  · rw [ht.rd, R23.rd, h0.rd]
  · rw [ht.wr, hwr' R23]
  · rw [ht.sp, R23.sp, h0.sp]
  · rw [ht.mem, mem23]
    simp only [allocVals, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := first | decide | omega_arith) only [readW_writeW_off, Mem.readW_writeW_self32]
  · rw [ht.other _ (by decide), Q23.gpr _ (by decide), x9]
  · rw [ht.gpr, mem23]
    simp only [stackArg]
    rw [eA0]
    simp (disch := first | decide | omega_arith) only [readW_writeW_off]

end

end VG.Proof.Dsa.Arm.Prime
