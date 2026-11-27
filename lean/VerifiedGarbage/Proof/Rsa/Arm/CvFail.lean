module

import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Rsa.Arm.CrtValues
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Sig
public import Aesop.BuiltinRules

/-! ### `Rsa.Arm.CvBase`, which this module and modules that import it used -/

section

/-! # `vg_rsa_crt_values` on ARMv7: the arguments

`CvPre s`: what the contract says of the arguments in the initial state `s`
(`cv_pre`), in the names used here: the working space `cvB s` of `cvZ s`
bytes, the modulus' length `cvK s` and `cvW s = ⌈cvK s / 4⌉`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

abbrev reg (a : BitVec 32) (n : Nat) : Region := ⟨State.addr a, n⟩

abbrev cvB (s : State) : BitVec 32 := stackArg s 10
abbrev cvZ (s : State) : Nat := (stackArg s 11).toNat * 8
abbrev cvK (s : State) : Nat := (stackArg s 3).toNat
abbrev cvW (s : State) : Nat := (cvK s + 3) / 4
abbrev cvPl (s : State) : Nat := (stackArg s 5).toNat
abbrev cvQl (s : State) : Nat := (stackArg s 7).toNat
abbrev cvDl (s : State) : Nat := (stackArg s 9).toNat

/-- The regions. -/
abbrev rDp (s : State) : Region := reg (s.gpr .r0) (s.gpr .r1).toNat
abbrev rDq (s : State) : Region := reg (s.gpr .r2) (s.gpr .r3).toNat
abbrev rQi (s : State) : Region := reg (stackArg s 0) (stackArg s 1).toNat
abbrev rN (s : State) : Region := reg (stackArg s 2) (stackArg s 3).toNat
abbrev rP (s : State) : Region := reg (stackArg s 4) (stackArg s 5).toNat
abbrev rQ (s : State) : Region := reg (stackArg s 6) (stackArg s 7).toNat
abbrev rD (s : State) : Region := reg (stackArg s 8) (stackArg s 9).toNat
abbrev rS (s : State) : Region := reg (stackArg s 10) ((stackArg s 11).toNat * 8)
abbrev rA (s : State) : Region := ⟨stackArgAddr s 0, 48⟩

structure CvPre (s : State) : Prop where
  sp48 : s.sp.toNat + 48 ≤ 2 ^ 32
  rd : s.rd = [rN s, rP s, rQ s, rD s, rA s]
  wr : s.wr = [rDp s, rDq s, rQi s, rS s]
  dpDq : (rDp s).Disjoint (rDq s)
  dpQi : (rDp s).Disjoint (rQi s)
  dpN : (rDp s).Disjoint (rN s)
  dpP : (rDp s).Disjoint (rP s)
  dpQ : (rDp s).Disjoint (rQ s)
  dpD : (rDp s).Disjoint (rD s)
  dpS : (rDp s).Disjoint (rS s)
  dpA : (rDp s).Disjoint (rA s)
  dqQi : (rDq s).Disjoint (rQi s)
  dqN : (rDq s).Disjoint (rN s)
  dqP : (rDq s).Disjoint (rP s)
  dqQ : (rDq s).Disjoint (rQ s)
  dqD : (rDq s).Disjoint (rD s)
  dqS : (rDq s).Disjoint (rS s)
  dqA : (rDq s).Disjoint (rA s)
  qiN : (rQi s).Disjoint (rN s)
  qiP : (rQi s).Disjoint (rP s)
  qiQ : (rQi s).Disjoint (rQ s)
  qiD : (rQi s).Disjoint (rD s)
  qiS : (rQi s).Disjoint (rS s)
  qiA : (rQi s).Disjoint (rA s)
  nS : (rN s).Disjoint (rS s)
  pS : (rP s).Disjoint (rS s)
  qS : (rQ s).Disjoint (rS s)
  dS : (rD s).Disjoint (rS s)
  sA : (rS s).Disjoint (rA s)
  fDp : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  fDq : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32
  fQi : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32
  fN : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 32
  fP : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 32
  fQ : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 32
  fD : (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 32
  fS : (stackArg s 10).toNat + (stackArg s 11).toNat * 8 ≤ 2 ^ 32
  valid : Spec.Rsa.lenValid (cvK s)
  pl1 : 1 ≤ cvPl s
  pl2 : cvPl s < cvK s
  ql1 : 1 ≤ cvQl s
  ql2 : cvQl s < cvK s
  dpLen : (s.gpr .r1).toNat = cvPl s
  qiLen : (stackArg s 1).toNat = cvPl s
  dqLen : (s.gpr .r3).toNat = cvQl s
  dl1 : 1 ≤ cvDl s
  dl2 : cvDl s ≤ cvK s
  scr : Spec.Rsa.scratchWords (cvK s) ≤ (stackArg s 11).toNat

theorem cv_pre (s : State) (h : (Spec.Rsa.crtValuesContract abi 0).pre s) : CvPre s := by
  sig_pre [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  obtain ⟨sp48, rd, wr, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21, a22, a23, a24, a25, a26, f1, f2, f3, f4, f5, f6, f7, f8, v, l1, l2, l3, l4, l5, l6, l7, l8, l9,
    l10⟩ := h
  exact ⟨sp48, rd, wr, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21, a22, a23, a24, a25, a26, f1, f2, f3, f4, f5, f6, f7, f8, v, l1, l2, l3, l4, l5, l6, l7, l8, l9,
    l10⟩

theorem CvPre.kb {s : State} (h : CvPre s) : 64 ≤ cvK s ∧ cvK s ≤ 1024 := h.valid

theorem CvPre.w16 {s : State} (h : CvPre s) : 16 ≤ cvW s ∧ cvW s ≤ 256 := by
  have := h.valid; simp only [Spec.Rsa.lenValid] at this
  have e : cvW s = (cvK s + 3) / 4 := rfl
  omega_using [this, e]

/-- The working space is large enough for the 25 arrays. -/
theorem CvPre.fits {s : State} (h : CvPre s) : arr (cvW s) nArr ≤ cvZ s := by
  have := h.valid; have := h.scr
  simp only [Spec.Rsa.lenValid, Spec.Rsa.scratchWords] at *
  simp only [arr, S, hdr, nArr, cvZ, cvW]
  omega_arith

/-! ## Loads of stack arguments -/

/-- `ldr t, [sp, #4i]` of a stack argument. -/
theorem wp_ldrSp {s : State} (hrd : rA s ∈ s.rd) (sp48 : s.sp.toNat + 48 ≤ 2 ^ 32) {i : Nat} (hi : i < 12)
    {t : Reg} {rest : List Instr} {Q : State → Prop} (k : ∀ s', Upd s s' t (stackArg s i) → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrSp t (4 * i) :: rest)) s Q := by
  refine WP.cons (s' := s.setReg t (stackArg s i)) ?_ (k _ (Upd.setReg _ _ _))
  have hin : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 4 := by
    refine ⟨rA s, List.mem_append_left _ hrd, ?_⟩
    simp only [Region.Contains, stackArgAddr]
    rw [addr_add (by omega_using [sp48, hi]), addr_add (by omega_using []), Nat.mul_zero, BitVec.add_zero,
      Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    omega_using [hi]
  simp only [exec, show 4 * i < 4096 by omega_using [hi], ↓reduceIte, State.load32, hin, Option.map_some]
  rfl

end VG.Proof.Rsa.Arm.CrtValues

end

end

/-! ### `Rsa.Arm.CvState`, which this module and modules that import it used -/

section

/-! # `vg_rsa_crt_values` on ARMv7: what every stage keeps

`Base s₀ s`: the stack pointer and the regions are those of the initial
state `s₀`, memory outside the working space is `s₀`'s, and the header holds
the registers to restore and `dp` and `dq` (`savedVal`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- The registers saved at bytes `20 + 4 i` of the header. -/
def savedReg : Nat → Reg
  | 0 => .r4 | 1 => .r5 | 2 => .r6 | 3 => .r7 | 4 => .r8 | 5 => .r9 | 6 => .r10 | 7 => .r11 | 8 => .lr
  | 9 => .r0 | _ => .r2

structure Base (s0 s : State) : Prop where
  pre : CvPre s0
  sp : s.sp = s0.sp
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  frame : Frame [rS s0] s0.mem s.mem
  saved : ∀ i < 11, slot s.mem (cvB s0) (20 + 4 * i) = (s0.gpr (savedReg i)).toNat

/-- Memory outside the working space, by the offset from its base. -/
theorem out_of_ofs {s0 : State} {x : Addr} (hx : ¬ (rS s0).Contains x 1) :
    cvZ s0 ≤ ofs (State.addr (cvB s0)) x := by
  simp only [Region.Contains] at hx
  simp only [ofs, cvZ, cvB]
  omega_using [hx]

theorem Base.keep {s0 s t : State} (h : Base s0 s) {js ds : List Nat}
    (k : Keep (cvB s0) (cvW s0) js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < nArr)
    (hds : ∀ d ∈ ds, d + 4 ≤ 20 ∨ 64 ≤ d) (hdh : ∀ d ∈ ds, d + 4 ≤ hdr)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Base s0 t := by
  have fits := h.pre.fits
  refine ⟨h.pre, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, ?_, fun i hi => ?_⟩
  · refine h.frame.trans fun x hx => k.out (Z := cvZ s0) (fun j hj => ?_) (fun d hd => ?_)
      (out_of_ofs (by simpa using hx))
    · exact Nat.le_trans (arr_end (hjs j hj)) fits
    · exact Nat.le_trans (hdh d hd) (Nat.le_trans (Nat.le_add_right _ _) fits)
  · rw [k.slot (by simp only [hdr]; omega_using [hi]) (fun d hd => by rcases hds d hd with e | e <;> omega_arith)]
    exact h.saved i hi

theorem Base.of_rest {s0 s t : State} (h : Base s0 s) {ws : List Reg} (r : Rest ws s t)
    (m : t.mem = s.mem) : Base s0 t :=
  ⟨h.pre, r.sp.trans h.sp, r.rd.trans h.rd, r.wr.trans h.wr, m ▸ h.frame, fun i hi => m ▸ h.saved i hi⟩

/-- A stack argument. -/
theorem Base.arg {s0 s : State} (h : Base s0 s) {i : Nat} (hi : i < 12) : stackArg s i = stackArg s0 i := by
  have sp := h.pre.sp48
  unfold stackArg
  have ea : stackArgAddr s i = stackArgAddr s0 i := by simp only [stackArgAddr, h.sp]
  rw [ea]
  refine h.frame.readW (r := rA s0) ?_ (fun r hr => ?_) (by decide)
  · simp only [Region.Contains, stackArgAddr]
    rw [addr_add (by omega_using [hi, sp]), addr_add (by omega_using []), Nat.mul_zero, BitVec.add_zero, Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat]
    omega_using [hi]
  · simp only [List.mem_singleton] at hr; subst hr; exact h.pre.sA.symm

theorem Base.rA_mem {s0 s : State} (h : Base s0 s) : rA s ∈ s.rd := by
  rw [h.rd, h.pre.rd]; simp [rA, stackArgAddr, h.sp]

/-- The working space. -/
theorem Base.ws {s0 s : State} (h : Base s0 s) (h7 : s.gpr .r7 = BitVec.ofNat 32 (S (cvW s0)))
    (h8 : s.gpr .r8 = cvB s0) (h9 : s.gpr .r9 = BitVec.ofNat 32 (cvW s0)) :
    Ws s (cvB s0) (cvZ s0) (cvW s0) nArr := by
  have := h.pre.w16
  refine ⟨h.pre.fS, ?_, h.pre.fits, by omega_using [this], by omega_using [this], h7, h8, h9⟩
  rw [h.wr, h.pre.wr]; simp

/-- `ctx`: `r7`, `r8` and `r9` from the stack arguments. -/
theorem ctx_ok {s0 s : State} (h : Base s0 s) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Base s0 t → Ws t (cvB s0) (cvZ s0) (cvW s0) nArr → Rest [.r7, .r8, .r9] s t → t.mem = s.mem →
      WP isa (.block rest) t Q) :
    WP isa (.block (ctx ++ rest)) s Q := by
  have sp := h.pre.sp48
  rw [h.sp.symm] at sp
  have w16 := h.pre.w16
  have kb := h.pre.kb
  unfold ctx stride
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrSp h.rA_mem sp (i := 10) (by decide) fun s1 u1 => ?_
  have b1 := h.of_rest (u1.rest (ws := [.r8]) (by simp)) u1.mem
  refine wp_ldrSp b1.rA_mem (by rw [u1.sp]; exact sp) (i := 3) (by decide) fun s2 u2 => ?_
  have b2 := b1.of_rest (u2.rest (ws := [.r9]) (by simp)) u2.mem
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  refine wp_mov (op2_lsl (by decide)) fun t u6 => ?_
  have rest : Rest [.r7, .r8, .r9] s t := (u1.rest (by simp)).trans ((u2.rest (by simp)).trans
    ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans (u6.rest (by simp))))))
  have mt : t.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have bt := h.of_rest rest mt
  have a3 : stackArg s1 3 = stackArg s0 3 := b1.arg (by decide)
  have e9 : s4.gpr .r9 = BitVec.ofNat 32 (cvW s0) := by
    rw [u4.gpr, u3.gpr, dpVal, u2.gpr, a3]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat,
      show (3 : BitVec 32).toNat = 3 from rfl]
    have : (stackArg s0 3).toNat < 2 ^ 32 := (stackArg s0 3).isLt
    simp only [cvW, cvK] at *
    omega_using [w16]
  have t9 : t.gpr .r9 = BitVec.ofNat 32 (cvW s0) := by
    rw [u6.other _ (by decide), u5.other _ (by decide), e9]
  have e7 : t.gpr .r7 = BitVec.ofNat 32 (S (cvW s0)) := by
    rw [u6.gpr, u5.gpr, dpVal, e9]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (2 : BitVec 32).toNat = 2 from rfl]
    simp only [S]
    omega_using []
  have e8 : t.gpr .r8 = cvB s0 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), u1.gpr, h.arg (by decide)]
  exact k t bt (bt.ws e7 e8 t9) rest mt

end VG.Proof.Rsa.Arm.CrtValues

end

end

/-! # `vg_rsa_crt_values` on ARMv7: the outputs, an invalid modulus, and the return

`Done s₀ s`: as `Base`, with the outputs written too. `fail_ok`: zeros to
the three outputs; `restore_ok`: the registers back.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

structure Done (s0 s : State) : Prop where
  pre : CvPre s0
  sp : s.sp = s0.sp
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  frame : Frame [rS s0, rDp s0, rDq s0, rQi s0] s0.mem s.mem
  saved : ∀ i < 11, slot s.mem (cvB s0) (20 + 4 * i) = (s0.gpr (savedReg i)).toNat

theorem Base.done {s0 s : State} (h : Base s0 s) : Done s0 s :=
  ⟨h.pre, h.sp, h.rd, h.wr, h.frame.mono (by simp), h.saved⟩

theorem Done.arg {s0 s : State} (h : Done s0 s) {i : Nat} (hi : i < 12) : stackArg s i = stackArg s0 i := by
  have sp := h.pre.sp48
  unfold stackArg
  have ea : stackArgAddr s i = stackArgAddr s0 i := by simp only [stackArgAddr, h.sp]
  rw [ea]
  refine h.frame.readW (r := rA s0) ?_ (fun r hr => ?_) (by decide)
  · simp only [Region.Contains, stackArgAddr]
    rw [addr_add (by omega_using [hi, sp]), addr_add (by omega_using []), Nat.mul_zero, BitVec.add_zero, Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat]
    omega_using [hi]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.pre.sA.symm
    · exact h.pre.dpA.symm
    · exact h.pre.dqA.symm
    · exact h.pre.qiA.symm

theorem Done.rA_mem {s0 s : State} (h : Done s0 s) : rA s ∈ s.rd := by
  rw [h.rd, h.pre.rd]; simp [rA, stackArgAddr, h.sp]

theorem Done.of_rest {s0 s t : State} (h : Done s0 s) {ws : List Reg} (r : Rest ws s t)
    (m : t.mem = s.mem) : Done s0 t :=
  ⟨h.pre, r.sp.trans h.sp, r.rd.trans h.rd, r.wr.trans h.wr, m ▸ h.frame, fun i hi => m ▸ h.saved i hi⟩

/-- The bytes of a region apart from a frame. -/
theorem bytes_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' a n = Spec.Rsa.bytesAt m a n := by
  unfold Spec.Rsa.bytesAt
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact hf.bytes (R := ⟨a, n⟩) hd hn hi

/-- A slot of the header, apart from a frame. -/
theorem slot_frame {s0 : State} (h : CvPre s0) {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (rS s0).Disjoint r) {i : Nat} (hi : i < 11) :
    slot m' (cvB s0) (20 + 4 * i) = slot m (cvB s0) (20 + 4 * i) := by
  have := h.fits
  have fS := h.fS
  have hz : 64 ≤ cvZ s0 := Nat.le_trans (by simp only [arr, hdr, nArr, S]; omega_using []) this
  exact congrArg BitVec.toNat
    (hf.readW (r := rS s0) (Offset.contains_base _ (by simp only [cvZ] at hz; omega_using [hi, hz]) (by omega_using [hi])) hd (by decide))

/-- An output written. -/
theorem Done.out {s0 s t : State} (h : Done s0 s) {R : Region} (hR : R = rDp s0 ∨ R = rDq s0 ∨ R = rQi s0)
    (f : Frame [R] s.mem t.mem) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Done s0 t := by
  have pre := h.pre
  refine ⟨h.pre, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, h.frame.trans (f.mono ?_), fun i hi => ?_⟩
  · rcases hR with rfl | rfl | rfl <;> simp
  · rw [slot_frame pre f (fun r hr => ?_) hi, h.saved i hi]
    simp only [List.mem_singleton] at hr; subst hr
    rcases hR with rfl | rfl | rfl
    · exact pre.dpS.symm
    · exact pre.dqS.symm
    · exact pre.qiS.symm

theorem zero_mask_bytes (bs : List Byte) :
    bs.map (· &&& (0 : BitVec 32).setWidth 8) = List.replicate bs.length 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons, List.length_cons, List.replicate_succ, ih]; congr 1; simp

theorem bytesAt_length (m : Mem) (a : Addr) (n : Nat) : (Spec.Rsa.bytesAt m a n).length = n := by
  simp [Spec.Rsa.bytesAt]

/-- `maskBytes` with `r2 = 0` on an output: zeros. -/
theorem zeroOut_ok {s0 s : State} (h : Done s0 s) {R : Region} (hR : R = rDp s0 ∨ R = rDq s0 ∨ R = rQi s0)
    {dst : BitVec 32} (hb : R.base = State.addr dst) (hn : 0 < R.len) (hl : R.len < 2 ^ 32)
    (fit : dst.toNat + R.len ≤ 2 ^ 32)
    (p0 : s.gpr .r0 = dst) (plr : s.gpr .lr = BitVec.ofNat 32 R.len) (p2 : s.gpr .r2 = 0) :
    WP isa maskBytes s fun t => Done s0 t ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) R.len = List.replicate R.len 0 ∧ Frame [R] s.mem t.mem ∧
      Rest [.r0, .r1, .lr] s t := by
  have hwr : R ∈ s.wr := by rw [h.wr, h.pre.wr]; rcases hR with rfl | rfl | rfl <;> simp
  have eR : R = ⟨State.addr dst, R.len⟩ := by cases R; simp_all
  refine WP.mono (maskBuffer_ok s hn hl fit ⟨R, hwr, by rw [← hb]; exact Region.contains_self _ _⟩
    p0 plr) fun t ⟨b, f, r⟩ => ⟨h.out hR (by rw [eR]; exact f) r.sp r.rd r.wr, ?_, by rw [eR]; exact f, r⟩
  rw [b, p2, zero_mask_bytes, bytesAt_length]

end VG.Proof.Rsa.Arm.CrtValues
