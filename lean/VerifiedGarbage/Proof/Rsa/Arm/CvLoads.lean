module

public import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Block

/-! # `vg_rsa_crt_values` on ARMv7: the working space zeroed and the numbers read (`loads_ok`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

/-- `args`: a pointer and a length from the stack. -/
theorem args_ok {s0 s : State} (h : Base s0 s) {i : Nat} (hi : i + 1 < 12) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ t, Base s0 t → Rest [.r4, .r6] s t → t.mem = s.mem → t.gpr .r4 = stackArg s0 i →
      t.gpr .r6 = BitVec.ofNat 32 (stackArg s0 (i + 1)).toNat → WP isa (.block rest) t Q) :
    WP isa (.block (args (4 * i) (4 * (i + 1)) ++ rest)) s Q := by
  have sp := h.pre.sp48
  refine wp_ldrSp h.rA_mem (by rw [h.sp]; exact sp) (by omega) fun s1 u1 => ?_
  have b1 := h.of_rest (u1.rest (ws := [.r4]) (by simp)) u1.mem
  refine wp_ldrSp b1.rA_mem (by rw [b1.sp]; exact sp) hi fun t u2 => ?_
  have b2 := b1.of_rest (u2.rest (ws := [.r6]) (by simp)) u2.mem
  exact k t b2 ((u1.rest (by simp)).trans (u2.rest (by simp))) (u2.mem.trans u1.mem)
    (by rw [u2.other _ (by decide), u1.gpr, h.arg (by omega)])
    (by rw [u2.gpr, b1.arg hi]; simp)

theorem num_of_full {m : Mem} {B : BitVec 32} {w j : Nat} {bs : List Byte}
    (h : val32 m (State.addr B) (arr w j) (w + 2) = Spec.Rsa.os2ip bs) (hl : bs.length ≤ 4 * w) :
    num m B w j = Spec.Rsa.os2ip bs := by
  have lt : Spec.Rsa.os2ip bs < 2 ^ (32 * w) :=
    Nat.lt_of_lt_of_le (VG.Proof.Rsa.lt_of_os2ip bs)
      (by rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega))
  rw [← h] at lt ⊢
  exact val32_low2 lt

end VG.Proof.Rsa.Arm.CrtValues

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

/-- `setup` and `zero`: every array zero, and `w` in the division's header. -/
theorem setupZero_ok {s0 s : State} (h : Base s0 s) :
    WP isa (.seq (.block setup) zero) s fun t => Base s0 t ∧ Ws t (cvB s0) (cvZ s0) (cvW s0) nArr ∧
      t.mem.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0) ∧
      ∀ j < nArr, val32 t.mem (State.addr (cvB s0)) (arr (cvW s0) j) (cvW s0 + 2) = 0 := by
  have pre := h.pre
  have w16 := pre.w16
  have fits := pre.fits
  have fS := pre.fS
  rw [WP.seq_iff]
  unfold setup
  refine ctx_ok h fun s1 b1 h1 r1 m1 => ?_
  refine wp_strSlot h1 (d := 16) (by decide) fun s2 u2 => ?_
  have h2 := h1.of_mupd u2
  have hz : 64 ≤ cvZ s0 := Nat.le_trans (by simp only [arr, hdr, nArr, S]; omega) fits
  have o2 := writeW32_outside s1.mem (State.addr (cvB s0)) (d := 16) (s1.gpr .r9) (by decide)
  rw [← u2.mem] at o2
  have b2 : Base s0 s2 := b1.outside o2 (by omega) (by omega) u2.sp u2.rd u2.wr
  have c2 : s2.mem.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0) := by
    rw [u2.mem, Mem.readW_writeW_self32, h1.r9]
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun s4 u4 => ?_
  refine wp_mul fun s5 u5 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s6 u6 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u7 => WP.block_nil ?_
  have rest : Rest [.r0, .lr, .r3] s2 u := (u3.rest (by simp)).trans ((u4.rest (by simp)).trans
    ((u5.rest (by simp)).trans ((u6.rest (by simp)).trans (u7.rest (by simp)))))
  have mu : u.mem = s2.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem]
  have bu := b2.of_rest rest mu
  have hu := h2.rest rest
  have p0 : u.gpr .r0 = cvB s0 + BitVec.ofNat 32 hdr := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr,
      dpVal, h2.r8]
  have plr : u.gpr .lr = BitVec.ofNat 32 (nArr * (cvW s0 + 2)) := by
    rw [u7.other _ (by decide), u6.gpr, u5.gpr, u4.gpr, u4.other _ (by decide), u3.other _ (by decide), h2.r7]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [nArr, S]
    rw [Nat.mod_eq_of_lt (a := 25) (by decide), Nat.mod_eq_of_lt (a := 4 * (cvW s0 + 2)) (by omega),
      Nat.mod_eq_of_lt (a := 25 * (4 * (cvW s0 + 2))) (by omega), Nat.mod_eq_of_lt (a := 25 * (cvW s0 + 2)) (by omega)]
    omega
  have nfit : hdr + 4 * (nArr * (cvW s0 + 2)) ≤ cvZ s0 := by
    have := fits; simp only [arr, S, nArr] at this ⊢; omega
  refine WP.mono (zero_ok u (base := cvB s0) (size := cvZ s0) (o := hdr) (n := nArr * (cvW s0 + 2))
    ⟨h.pre.fS, nfit, ⟨rS s0, by rw [bu.wr, pre.wr]; simp, Region.contains_self _ _⟩⟩
    (by simp only [nArr]; omega) p0 plr (by rw [u7.gpr])) fun t inv => ?_
  have bt := bu.outside inv.outside (by simp only [hdr]; omega) nfit inv.rest.sp inv.rest.rd inv.rest.wr
  refine ⟨bt, hu.rest inv.rest, ?_, fun j hj => ?_⟩
  · have e := inv.outside.w32 (d := 16) (by simp only [hdr]; omega) (by omega)
    apply BitVec.eq_of_toNat_eq
    rw [show (t.mem.readW (off (State.addr (cvB s0)) 16) 32).toNat = w32 t.mem (State.addr (cvB s0)) 16 from rfl,
      e, show w32 u.mem (State.addr (cvB s0)) 16 = (u.mem.readW (off (State.addr (cvB s0)) 16) 32).toNat from rfl,
      mu, c2]
  · have := val32_zero_part inv.value (a := j * (cvW s0 + 2)) (c := cvW s0 + 2) (by
      have := Nat.mul_le_mul_right (cvW s0 + 2) (show j + 1 ≤ nArr by omega)
      rw [Nat.succ_mul] at this; omega)
    simpa only [arr, S, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

theorem argsLoad_ok {s0 s : State} (h : Base s0 s) (hw : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr)
    {i : Nat} (hi : i + 1 < 12) {j : Nat} (hj : j < nArr) {R : Region}
    (inp : Input s0 R (stackArg s0 i) (stackArg s0 (i + 1)).toNat) {rest : List (Prog isa)} {Q : State → Prop}
    (k : ∀ t, Base s0 t → Ws t (cvB s0) (cvZ s0) (cvW s0) nArr → Keep (cvB s0) (cvW s0) [j] [] s.mem t.mem →
      val32 t.mem (State.addr (cvB s0)) (arr (cvW s0) j) (cvW s0 + 2) =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (State.addr (stackArg s0 i)) (stackArg s0 (i + 1)).toNat) →
      WP isa (seqs rest) t Q) (hrest : rest ≠ []) :
    WP isa (seqs (.block (args (4 * i) (4 * (i + 1))) :: load j :: rest)) s Q := by
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil (args _ _)]
  refine args_ok h hi fun u bu ru mu p4 p6 => WP.block_nil ?_
  rw [wp_seqs_cons hrest]
  refine WP.mono (load_ok bu (hw.rest ru) hj inp p4 p6) fun t ⟨bt, ht, kt, vt, _⟩ => k t bt ht (mu ▸ kt) vt

theorem input_n {s0 : State} (h : CvPre s0) : Input s0 (rN s0) (stackArg s0 2) (stackArg s0 3).toNat :=
  ⟨rfl, by rw [h.rd]; simp, h.nS, h.fN, by have := h.kb; simp only [cvK] at this; omega, Nat.le_refl _⟩
theorem input_p {s0 : State} (h : CvPre s0) : Input s0 (rP s0) (stackArg s0 4) (stackArg s0 5).toNat :=
  ⟨rfl, by rw [h.rd]; simp, h.pS, h.fP, h.pl1, Nat.le_of_lt h.pl2⟩
theorem input_q {s0 : State} (h : CvPre s0) : Input s0 (rQ s0) (stackArg s0 6) (stackArg s0 7).toNat :=
  ⟨rfl, by rw [h.rd]; simp, h.qS, h.fQ, h.ql1, Nat.le_of_lt h.ql2⟩
theorem input_d {s0 : State} (h : CvPre s0) : Input s0 (rD s0) (stackArg s0 8) (stackArg s0 9).toNat :=
  ⟨rfl, by rw [h.rd]; simp, h.dS, h.fD, h.dl1, h.dl2⟩

theorem loads_ok {s0 s : State} (h : Base s0 s) : WP isa loads s (StA s0) := by
  have pre := h.pre
  have w16 := pre.w16
  have kb := pre.kb
  have hk : ∀ k, k ≤ cvK s0 → k ≤ 4 * cvW s0 := fun k hk => by simp only [cvW] at *; omega
  unfold loads
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.seq_iff.mp (setupZero_ok h)) fun u hu => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono hu fun t1 ⟨b1, h1, c1, z1⟩ => ?_
  refine argsLoad_ok b1 h1 (i := 2) (by decide) (j := aDQ) (by decide) (input_n pre)
    (fun t2 b2 h2 k2 v2 => ?_) (List.cons_ne_nil _ _)
  refine argsLoad_ok b2 h2 (i := 4) (by decide) (j := aP) (by decide) (input_p pre)
    (fun t3 b3 h3 k3 v3 => ?_) (List.cons_ne_nil _ _)
  refine argsLoad_ok b3 h3 (i := 6) (by decide) (j := aQ) (by decide) (input_q pre)
    (fun t4 b4 h4 k4 v4 => ?_) (List.cons_ne_nil _ _)
  rw [show seqs [Code.block (args 32 36), load aD] =
    .seq (.block (args (4 * 8) (4 * (8 + 1)) ++ [])) (load aD) from rfl, WP.seq_iff]
  refine args_ok b4 (by decide) fun u bu ru mu p4 p6 => WP.block_nil ?_
  refine WP.mono (load_ok bu (h4.rest ru) (j := aD) (by decide) (input_d pre) p4 p6)
    fun t ⟨bt, ht, k5', v5, _⟩ => ?_
  have k5 : Keep (cvB s0) (cvW s0) [aD] [] t4.mem t.mem := mu ▸ k5'
  have fit := fun j (hj : j < nArr) => h1.fit64 (j := j) hj
  have full : ∀ j < nArr, j ∉ [aDQ, aP, aQ, aD] →
      val32 t.mem (State.addr (cvB s0)) (arr (cvW s0) j) (cvW s0 + 2) =
        val32 t1.mem (State.addr (cvB s0)) (arr (cvW s0) j) (cvW s0 + 2) := by
    intro j hj hn
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [k5.full (by simpa using fun e => hn.2.2.2 e.symm) (by simp) (fit j hj),
      k4.full (by simpa using fun e => hn.2.2.1 e.symm) (by simp) (fit j hj),
      k3.full (by simpa using fun e => hn.2.1 e.symm) (by simp) (fit j hj),
      k2.full (by simpa using fun e => hn.1 e.symm) (by simp) (fit j hj)]
  refine ⟨bt, ht, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [← c1]
    refine BitVec.eq_of_toNat_eq ?_
    change slot t.mem (cvB s0) 16 = slot t1.mem (cvB s0) 16
    rw [k5.slot (by decide) (by simp), k4.slot (by decide) (by simp), k3.slot (by decide) (by simp),
      k2.slot (by decide) (by simp)]
  · refine num_of_full ?_ (by rw [bytesAt_length]; exact hk _ (Nat.le_refl _))
    rw [k5.full (by decide) (by simp) (fit _ (by decide)), k4.full (by decide) (by simp) (fit _ (by decide)),
      k3.full (by decide) (by simp) (fit _ (by decide)), v2]
  · refine num_of_full ?_ (by rw [bytesAt_length]; exact hk _ (Nat.le_of_lt pre.pl2))
    rw [k5.full (by decide) (by simp) (fit _ (by decide)), k4.full (by decide) (by simp) (fit _ (by decide)), v3]
  · refine num_of_full ?_ (by rw [bytesAt_length]; exact hk _ (Nat.le_of_lt pre.ql2))
    rw [k5.full (by decide) (by simp) (fit _ (by decide)), v4]
  · exact num_of_full v5 (by rw [bytesAt_length]; exact hk _ pre.dl2)
  · simp only [zeroArrs, List.mem_cons, List.not_mem_nil, or_false] at hj
    have hj' : j < nArr := by simp only [nArr]; omega
    have hn : j ∉ [aDQ, aP, aQ, aD] := by
      simp only [aDQ, aP, aQ, aD, List.mem_cons, List.not_mem_nil, or_false]; omega
    rw [full j hj' hn, z1 j hj']

end VG.Proof.Rsa.Arm.CrtValues
