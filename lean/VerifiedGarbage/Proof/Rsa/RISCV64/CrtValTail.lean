module

public import VerifiedGarbage.Impl.Rsa.RISCV64.CrtValues
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyLoops
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyWordDiv
public import VerifiedGarbage.Proof.Rsa.RISCV64.IbOps
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyOps
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # `vg_rsa_crt_values` on RISC-V: the inverse's tail by words

For a balanced key, `CrtValues.invG` runs the inverse without its doublings
(`InvBatch.inverseS`) and then `CrtValues.tail`, `y := y 2^K mod m` for
`K = 6 (w + 1) = 64 Q + T`: `y`'s words shifted left by `T` into word `Q` of a
zeroed array (`shlTLoop_ok`), and one division by words (`divW_ok`). -/

-- separate module: its proofs (the tail's shift and division) are not re-checked with every change to the
-- inverse's phase (`CrtValInv.lean`)

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Loops

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64 VG.Impl.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.CrtValues (shlTBody)

theorem exec_sllr (d n m : Reg) (s : State) :
    exec (.shiftReg .sll .d d n m) s = some (s.write d (s.gpr n <<< ((s.gpr m).toNat % 64))) := rfl

theorem exec_srlr (d n m : Reg) (s : State) :
    exec (.shiftReg .srl .d d n m) s = some (s.write d (s.gpr n >>> ((s.gpr m).toNat % 64))) := rfl

/-- A word shifted left by `T`, the carry `c < 2^T` in: the word out and the
carry out are the word times `2^T` plus `c`. -/
theorem shl64_arith (x c : BitVec 64) {T : Nat} (hT : 0 < T) (hT' : T < 64) (hc : c.toNat < 2 ^ T) :
    ((x <<< T) ||| c).toNat + 2 ^ 64 * (x >>> (64 - T)).toNat = x.toNat * 2 ^ T + c.toNat := by
  have h1 : (x <<< T).toNat = x.toNat * 2 ^ T % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have h2 : (x >>> (64 - T)).toNat = x.toNat / 2 ^ (64 - T) := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hd : x <<< T &&& c = 0 := by
    apply BitVec.eq_of_getElem_eq; intro i hi
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft]
    by_cases h : i < T
    · simp [h]
    · have : c.toNat < 2 ^ i := Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) (by omega))
      simp [h, BitVec.getElem_eq_testBit_toNat, Nat.testBit_lt_two_pow this]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hd, BitVec.toNat_add, h1, h2]
  have e : x.toNat * 2 ^ T = x.toNat * 2 ^ T % 2 ^ 64 + 2 ^ 64 * (x.toNat / 2 ^ (64 - T)) := by
    have : x.toNat * 2 ^ T / 2 ^ 64 = x.toNat / 2 ^ (64 - T) := by
      rw [show (2 : Nat) ^ 64 = 2 ^ (64 - T) * 2 ^ T by rw [← Nat.pow_add]; congr 1; omega,
        Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)]
    rw [← this]; exact (Nat.mod_add_div _ _).symm
  have lt : x.toNat * 2 ^ T % 2 ^ 64 + c.toNat < 2 ^ 64 := by
    have : x.toNat * 2 ^ T % 2 ^ 64 + 2 ^ T ≤ 2 ^ 64 := by
      have hm : 2 ^ T ∣ x.toNat * 2 ^ T % 2 ^ 64 :=
        (Nat.dvd_mod_iff (Nat.pow_dvd_pow 2 (by omega))).mpr (Nat.dvd_mul_left _ _)
      obtain ⟨k, hk⟩ := hm
      have : x.toNat * 2 ^ T % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (Nat.two_pow_pos _)
      have e64 : (2 : Nat) ^ 64 = 2 ^ T * 2 ^ (64 - T) := by rw [← Nat.pow_add]; congr 1; omega
      rw [hk] at this ⊢
      rw [e64] at this ⊢
      have : k < 2 ^ (64 - T) := Nat.lt_of_mul_lt_mul_left this
      calc 2 ^ T * k + 2 ^ T = 2 ^ T * (k + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ ≤ 2 ^ T * 2 ^ (64 - T) := Nat.mul_le_mul_left _ this
    omega
  rw [Nat.mod_eq_of_lt lt]
  omega

/-- The shift over `n` words (`countLoop .t3 shlTBody`), from `t0` to `t1`
apart from them, by `T` in `t2` (`64 - T` in `t6`), from a zero carry in
`a4`: the words written and the carry out are the words read times `2^T`. -/
theorem shlTLoop_ok {s : State} {B : Addr} {Z dO dS n T : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dS) (h1 : s.gpr .t1 = off B dO) (h2 : s.gpr .t2 = BitVec.ofNat 64 T)
    (h6 : s.gpr .t6 = BitVec.ofNat 64 (64 - T)) (h4 : s.gpr .a4 = 0) (h3 : s.gpr .t3 = BitVec.ofNat 64 n)
    (hT : 0 < T) (hT' : T < 64) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hS8 : dS % 8 = 0) (hO8 : dO % 8 = 0) (hS : dS + 8 * n ≤ Z) (hO : dO + 8 * n ≤ Z)
    (hap : dS + 8 * n ≤ dO ∨ dO + 8 * n ≤ dS) :
    WP isa (countLoop .t3 shlTBody) s fun t =>
      wordsVal t.mem B dO n + 2 ^ (64 * n) * (t.gpr .a4).toNat = wordsVal s.mem B dS n * 2 ^ T ∧
      Outside B dO (8 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dS + 8 * i) ∧ t.gpr .t1 = off B (dO + 8 * i) ∧ Outside B dO (8 * i) s.mem t.mem ∧
      (t.gpr .a4).toNat < 2 ^ T ∧
      wordsVal t.mem B dO i + 2 ^ (64 * i) * (t.gpr .a4).toNat = wordsVal s.mem B dS i * 2 ^ T ∧
      Keep [.t0, .t1, .t3, .t4, .t5, .a4] s t
  refine WP.mono (wp_countdown (body := .block (shlTBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j1, jout, j4l, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, Outside.refl _ _ _ _, by rw [h4]; exact Nat.two_pow_pos _,
      by simp [wordsVal, h4], Keep.refl _ _⟩ h3)
    fun t ⟨_, _, jout, _, jeq, jk⟩ => ⟨jeq, jout, jk.mono (by decide)⟩
  have hs' := hs.congr jk.2.2
  have t2 : t.gpr .t2 = BitVec.ofNat 64 T := (jk.gpr (by decide)).trans h2
  have t6 : t.gpr .t6 = BitVec.ofNat 64 (64 - T) := (jk.gpr (by decide)).trans h6
  have T2 : (t.gpr .t2).toNat % 64 = T := by rw [t2, BitVec.toNat_ofNat]; omega
  have T6 : (t.gpr .t6).toNat % 64 = 64 - T := by rw [t6, BitVec.toNat_ofNat]; omega
  have hst : WP isa (.block (shlTBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t0 = off B (dS + 8 * i + 8) ∧ t'.gpr .t1 = off B (dO + 8 * i + 8) ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.gpr .a4 = word t.mem B (dS + 8 * i) >>> (64 - T) ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (word t.mem B (dS + 8 * i) <<< T ||| t.gpr .a4)) ∧
      Keep [.t0, .t1, .t3, .t4, .t5, .a4] t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [shlTBody, exec_sllr, exec_srlr, j0, j1, T2, T6, hs'.ld (show dS + 8 * i + 8 ≤ Z by omega_arith),
      hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dS + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l0, l1, l3, l4, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dS + 8 * i + 8 = dS + 8 * (i + 1) by omega_arith]
  · rw [l1, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · rw [l4, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := (word t.mem B (dS + 8 * i)).isLt
    exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add, show 64 - T + T = 64 by omega]; exact this)
  · have wa : word t.mem B (dS + 8 * i) = word s.mem B (dS + 8 * i) := by
      rcases hap with hap | hap
      · exact jout.word (by omega_arith) (by omega_arith)
      · exact jout.word (by omega_arith) (by omega_arith)
    have k := shl64_arith (word s.mem B (dS + 8 * i)) (t.gpr .a4) hT hT' j4l
    rw [lm, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), l4, wa, wordsVal_succ_top s.mem B dS i,
      Nat.mul_succ, Nat.pow_add]
    rw [← wa] at k ⊢
    have e2 : 2 ^ (64 * i) * ((word t.mem B (dS + 8 * i) <<< T ||| t.gpr .a4).toNat +
        2 ^ 64 * (word t.mem B (dS + 8 * i) >>> (64 - T)).toNat) =
        2 ^ (64 * i) * ((word t.mem B (dS + 8 * i)).toNat * 2 ^ T + (t.gpr .a4).toNat) := by rw [k]
    rw [Nat.add_mul, ← jeq]
    grind

end VG.Proof.Rsa.RISCV64.Loops

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr)
open VG.Impl.Rsa.RISCV64.InvBatch (zeroW zeros)
open VG.RISCV64.RegUpd

/-- `zeroW j` on the working space alone: `[j]` := 0. -/
theorem zeroWs_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) (hN : N ≤ 256) :
    WP isa (zeroW j) s fun t => Ws t B Z w N ∧ Keys.Frame B w [j] [] s.mem t.mem ∧ num t.mem B w j = 0 ∧
      Keep kRegs s t := by
  have fj := h.arr_fit hj
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wle
  have := arr_al4 w j
  rw [zeroW, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (by omega) ?_
  refine WP.mono (WP.keep [.t3] (Q := fun u => u.gpr .t3 = BitVec.ofNat 64 (2 * w + 2) ∧
    u.gpr .t0 = off B (arr w j) ∧ u.mem = s.mem) ?_ (by rfl) (by rfl)) fun u ⟨⟨u3, u0, um⟩, ku⟩ => ?_
  · brun [h.s9]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have k1 : Keep kRegs s u := ((Keep.write _ .t0 _).trans ku).mono (by decide)
  rw [zeros, WP.seq_iff]
  refine WP.mono (WP.keep [.t5] (Q := fun y => y.gpr .t5 = 0 ∧ y.mem = u.mem) (by brun [fin64_exec_li_zero])
    (by rfl) (by rfl)) fun y ⟨⟨y5, ym⟩, ky⟩ => ?_
  have k2 : Keep kRegs s y := Keep.trans' k1 (ky.mono (by decide))
  refine WP.mono (zeroLoop_ok (dO := arr w j) (n := 2 * w + 2) (h.of_keep k2).scr (by rw [ky.gpr (by decide)]; exact u0)
    (by rw [ky.gpr (by decide)]; exact u3) y5 (by omega) (by omega) (by omega) (by omega)) fun t ⟨z, out, kt⟩ => ?_
  rw [ym, um] at out
  refine ⟨h.of_keep (Keep.trans' k2 (kt.mono (by decide))), Keys.Frame.of_arr (d := 0)
    (by simpa only [Nat.add_zero] using out) (by omega) (by simp), ?_, Keep.trans' k2 (kt.mono (by decide))⟩
  rw [num_eq]
  exact val32_zero fun i hi => z i (by omega)

end VG.Proof.Rsa.RISCV64.InvBatch

namespace VG.Proof.Rsa.RISCV64.CrtValues

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (ptr)
open VG.Impl.Rsa.RISCV64.CrtValues (aDQ aDR aTD aTT nArr shape saveK restoreK tailSetup tail)
open VG.Impl.Rsa.RISCV64.Keys (seqs copy)

theorem cv_exec_li32 {s : State} {d : Reg} : exec (.li d 32) s = some (s.write d 32#64) := by
  rw [exec_li (by decide)]; rfl

theorem cv_exec_li64 {s : State} {d : Reg} : exec (.li d 64) s = some (s.write d 64#64) := by
  rw [exec_li (by decide)]; rfl

theorem wr_other {m : Mem} {B : Addr} {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (he : e + 8 ≤ 2 ^ 64) (hd : d + 8 ≤ 2 ^ 64) : word (m.writeW (off B e) v) B d = word m B d :=
  (writeW_outside m B v he).word h hd

theorem Outside.writeW_in {B : Addr} {o n e : Nat} {m m' : Mem} (h : Outside B o n m m') (v : BitVec 64)
    (he : o ≤ e) (he' : e + 8 ≤ o + n) (hf : e + 8 ≤ 2 ^ 64) : Outside B o n m (m'.writeW (off B e) v) :=
  h.trans ((writeW_outside m' B v hf).mono he he')

/-- `saveK`: `kept` into `aDQ`'s first nine words. -/
theorem saveK_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) (hq : aDQ < N) (hw : 7 ≤ w) :
    WP isa (.block saveK) s fun t => Ws t B Z w N ∧ Keys.Frame B w [aDQ] [] s.mem t.mem ∧ Keep [.t0] s t ∧
      word t.mem B (arr w aDQ) = s.gpr .s1 ∧ word t.mem B (arr w aDQ + 8) = s.gpr .s2 ∧
      word t.mem B (arr w aDQ + 16) = s.gpr .s3 ∧ word t.mem B (arr w aDQ + 24) = s.gpr .s4 ∧
      word t.mem B (arr w aDQ + 32) = s.gpr .a0 ∧ word t.mem B (arr w aDQ + 40) = s.gpr .a1 ∧
      word t.mem B (arr w aDQ + 48) = s.gpr .a2 ∧ word t.mem B (arr w aDQ + 56) = s.gpr .a3 ∧
      word t.mem B (arr w aDQ + 64) = s.gpr .a6 := by
  have fit := h.arr_fit hq
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have al := arr_al w aDQ
  unfold saveK
  refine ptr_ok h (by decide) (by decide) (show aDQ < 2048 by decide) ?_
  generalize hA : arr w aDQ = A at fit al
  refine WP.mono (WP.keep [] (Q := fun t => t.mem =
      ((((((((s.mem.writeW (off B A) (s.gpr .s1)).writeW (off B (A + 8)) (s.gpr .s2)).writeW (off B (A + 16)) (s.gpr .s3)).writeW (off B (A + 24)) (s.gpr .s4)).writeW (off B (A + 32)) (s.gpr .a0)).writeW (off B (A + 40)) (s.gpr .a1)).writeW (off B (A + 48)) (s.gpr .a2)).writeW (off B (A + 56)) (s.gpr .a3)).writeW (off B (A + 64)) (s.gpr .a6)) (by
    brun [BitVec.add_zero, h.scr.st (show A + 8 ≤ Z by omega), h.scr.al8 (show A + 8 ≤ Z by omega) al,
      h.scr.st (show A + 8 + 8 ≤ Z by omega), h.scr.al8 (show A + 8 + 8 ≤ Z by omega) (by omega),
      h.scr.st (show A + 16 + 8 ≤ Z by omega), h.scr.al8 (show A + 16 + 8 ≤ Z by omega) (by omega),
      h.scr.st (show A + 24 + 8 ≤ Z by omega), h.scr.al8 (show A + 24 + 8 ≤ Z by omega) (by omega),
      h.scr.st (show A + 32 + 8 ≤ Z by omega), h.scr.al8 (show A + 32 + 8 ≤ Z by omega) (by omega),
      h.scr.st (show A + 40 + 8 ≤ Z by omega), h.scr.al8 (show A + 40 + 8 ≤ Z by omega) (by omega),
      h.scr.st (show A + 48 + 8 ≤ Z by omega), h.scr.al8 (show A + 48 + 8 ≤ Z by omega) (by omega),
      h.scr.st (show A + 56 + 8 ≤ Z by omega), h.scr.al8 (show A + 56 + 8 ≤ Z by omega) (by omega),
      h.scr.st (show A + 64 + 8 ≤ Z by omega), h.scr.al8 (show A + 64 + 8 ≤ Z by omega) (by omega)])
    (by rfl) (by rfl)) fun t ⟨tm, k⟩ => ?_
  have kk : Keep [.t0] s t := ((Keep.write _ _ _).trans k).mono (by decide)
  refine ⟨h.of_keep kk, ?_, kk, ?_⟩
  · have o : Outside B A 72 s.mem t.mem := by
      rw [tm]
      repeat refine Outside.writeW_in ?_ _ (by omega) (by omega) (by omega)
      exact Outside.refl _ _ _ _
    rw [← hA] at o
    exact Keys.Frame.of_arr (o := aDQ) (d := 0) (n := 72) (by simpa using o) (by omega) (by simp)
  · rw [tm]
    simp (disch := omega) only [wr_other, Mont.word_writeW_self, and_self]

/-- `restoreK`: `kept` back from `aDQ`'s first nine words. -/
theorem restoreK_ok {u : State} {B : Addr} {Z w N : Nat} (h : Ws u B Z w N) (hq : aDQ < N) (hw : 7 ≤ w)
    {v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64}
    (e1 : word u.mem B (arr w aDQ) = v1) (e2 : word u.mem B (arr w aDQ + 8) = v2)
    (e3 : word u.mem B (arr w aDQ + 16) = v3) (e4 : word u.mem B (arr w aDQ + 24) = v4)
    (e5 : word u.mem B (arr w aDQ + 32) = v5) (e6 : word u.mem B (arr w aDQ + 40) = v6)
    (e7 : word u.mem B (arr w aDQ + 48) = v7) (e8 : word u.mem B (arr w aDQ + 56) = v8)
    (e9 : word u.mem B (arr w aDQ + 64) = v9) :
    WP isa (.block restoreK) u fun t => (t.gpr .s1 = v1 ∧ t.gpr .s2 = v2 ∧ t.gpr .s3 = v3 ∧ t.gpr .s4 = v4 ∧
      t.gpr .a0 = v5 ∧ t.gpr .a1 = v6 ∧ t.gpr .a2 = v7 ∧ t.gpr .a3 = v8 ∧ t.gpr .a6 = v9 ∧ t.mem = u.mem) ∧
      Keep [.t0, .s1, .s2, .s3, .s4, .a0, .a1, .a2, .a3, .a6] u t := by
  have fit := h.arr_fit hq
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have al := arr_al w aDQ
  unfold restoreK
  refine ptr_ok h (by decide) (by decide) (show aDQ < 2048 by decide) ?_
  generalize hA : arr w aDQ = A at fit al e1 e2 e3 e4 e5 e6 e7 e8 e9
  have r1 : u.mem.readW (off B A) 64 = v1 := e1
  have r2 : u.mem.readW (off B (A + 8)) 64 = v2 := e2
  have r3 : u.mem.readW (off B (A + 16)) 64 = v3 := e3
  have r4 : u.mem.readW (off B (A + 24)) 64 = v4 := e4
  have r5 : u.mem.readW (off B (A + 32)) 64 = v5 := e5
  have r6 : u.mem.readW (off B (A + 40)) 64 = v6 := e6
  have r7 : u.mem.readW (off B (A + 48)) 64 = v7 := e7
  have r8 : u.mem.readW (off B (A + 56)) 64 = v8 := e8
  have r9 : u.mem.readW (off B (A + 64)) 64 = v9 := e9
  refine WP.mono (WP.keep [.t0, .s1, .s2, .s3, .s4, .a0, .a1, .a2, .a3, .a6] (Q := fun t =>
      t.gpr .s1 = v1 ∧ t.gpr .s2 = v2 ∧ t.gpr .s3 = v3 ∧ t.gpr .s4 = v4 ∧ t.gpr .a0 = v5 ∧ t.gpr .a1 = v6 ∧
        t.gpr .a2 = v7 ∧ t.gpr .a3 = v8 ∧ t.gpr .a6 = v9 ∧ t.mem = u.mem) (by
    brun [BitVec.add_zero, r1, r2, r3, r4, r5, r6, r7, r8, r9,
      h.scr.ld (show A + 8 ≤ Z by omega), h.scr.al8 (show A + 8 ≤ Z by omega) al,
      h.scr.ld (show A + 8 + 8 ≤ Z by omega), h.scr.al8 (show A + 8 + 8 ≤ Z by omega) (by omega),
      h.scr.ld (show A + 16 + 8 ≤ Z by omega), h.scr.al8 (show A + 16 + 8 ≤ Z by omega) (by omega),
      h.scr.ld (show A + 24 + 8 ≤ Z by omega), h.scr.al8 (show A + 24 + 8 ≤ Z by omega) (by omega),
      h.scr.ld (show A + 32 + 8 ≤ Z by omega), h.scr.al8 (show A + 32 + 8 ≤ Z by omega) (by omega),
      h.scr.ld (show A + 40 + 8 ≤ Z by omega), h.scr.al8 (show A + 40 + 8 ≤ Z by omega) (by omega),
      h.scr.ld (show A + 48 + 8 ≤ Z by omega), h.scr.al8 (show A + 48 + 8 ≤ Z by omega) (by omega),
      h.scr.ld (show A + 56 + 8 ≤ Z by omega), h.scr.al8 (show A + 56 + 8 ≤ Z by omega) (by omega),
      h.scr.ld (show A + 64 + 8 ≤ Z by omega), h.scr.al8 (show A + 64 + 8 ≤ Z by omega) (by omega)])
    (by rfl) (by rfl)) fun t ⟨q, k⟩ => ⟨q, ((Keep.write _ _ _).trans k).mono (by decide)⟩

/-- The registers the divisions by words write. -/
abbrev dwRegs : List Reg :=
  [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]


/-- `shape`: `t0 = 0` exactly for `p_len` (`s4`) a multiple of 8 and at least
32, equal to `q_len` (`s6`) and to `4 w` (`s9`). -/
theorem shape_ok {s : State} {pl ql w : Nat} (h4 : s.gpr .s4 = BitVec.ofNat 64 pl)
    (h6 : s.gpr .s6 = BitVec.ofNat 64 ql) (h9 : s.gpr .s9 = BitVec.ofNat 64 w) (hpl : pl < 2 ^ 32)
    (hql : ql < 2 ^ 32) (hw : w ≤ 1024) :
    WP isa (.block shape) s fun t =>
      ((t.gpr .t0 = 0 ↔ (pl % 8 = 0 ∧ 4 * w = pl ∧ pl = ql ∧ 32 ≤ pl)) ∧ t.mem = s.mem) ∧ Keep [.t0, .t1] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have hP : ∀ x : Nat, x < 2 ^ 32 → (BitVec.ofNat 64 x).toNat = x := fun x hx => by
    rw [BitVec.toNat_ofNat]; omega
  unfold shape
  brun [h4, h6, h9, cv_exec_li32]
  simp only [Keys.bv_or0, Keys.bv_xor0, Keys.bv_lt_ite0]
  have l2 : BitVec.ofNat 64 w <<< 2 = BitVec.ofNat 64 (4 * w) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hP w (by omega), BitVec.toNat_ofNat]; omega
  simp only [l2, Keys.bv_and7, hP pl hpl, BitVec.lt_def, show (32#64).toNat = 32 from rfl, Nat.not_lt]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h1, ?_, ?_, h4⟩
    · have := congrArg BitVec.toNat h2; rw [hP _ (by omega), hP pl hpl] at this; exact this
    · have := congrArg BitVec.toNat h3; rw [hP pl hpl, hP ql hql] at this; exact this
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, by rw [h2]⟩, by rw [h3]⟩, h4⟩


/-- `tailSetup`, for `K = 6 (w + 1)`: the pointers, `T = K mod 64`, `64 - T`,
the carry and the count. -/
theorem tailSetup_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) (hD : aDR < N) :
    WP isa (.block tailSetup) s fun t =>
      (t.gpr .t0 = off B (arr w 3) ∧ t.gpr .t1 = off B (arr w aDR + 8 * ((6 * w + 6) / 64)) ∧
        t.gpr .t2 = BitVec.ofNat 64 ((6 * w + 6) % 64) ∧ t.gpr .t6 = BitVec.ofNat 64 (64 - (6 * w + 6) % 64) ∧
        t.gpr .a4 = 0 ∧ t.gpr .t3 = BitVec.ofNat 64 (w / 2 + 1) ∧ t.mem = s.mem) ∧
      Keep [.t0, .t1, .t2, .t3, .t5, .t6, .a4] s t := by
  have := h.wle
  have nw := h.nowrap
  have fit := h.fits
  unfold tailSetup
  refine ptr2_ok h (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) fun t p0 p1 kt mt => ?_
  have ht := h.of_keep kt
  refine WP.mono (WP.keep [.t1, .t2, .t3, .t5, .t6, .a4] (Q := fun u =>
    u.gpr .t0 = off B (arr w 3) ∧ u.gpr .t1 = off B (arr w aDR + 8 * ((6 * w + 6) / 64)) ∧
      u.gpr .t2 = BitVec.ofNat 64 ((6 * w + 6) % 64) ∧ u.gpr .t6 = BitVec.ofNat 64 (64 - (6 * w + 6) % 64) ∧
      u.gpr .a4 = 0 ∧ u.gpr .t3 = BitVec.ofNat 64 (w / 2 + 1) ∧ u.mem = s.mem) ?_ (by rfl) (by rfl))
    fun u ⟨q, k⟩ => ⟨q, (kt.trans k).mono (by decide)⟩
  brun [p0, p1, ht.s9, mt, fin64_exec_li_zero, cv_exec_li64]
  have h64 : 6 * w + 6 < 2 ^ 64 := by omega
  have hK : off (BitVec.ofNat 64 w) (w + w) + off (BitVec.ofNat 64 w) (w + w) + 6#64 =
      BitVec.ofNat 64 (6 * w + 6) := by
    apply BitVec.eq_of_toNat_eq
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hT : BitVec.ofNat 64 (6 * w + 6) &&& 63#64 = BitVec.ofNat 64 ((6 * w + 6) % 64) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [show (63 : Nat) % 2 ^ 64 = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h64,
      Nat.mod_eq_of_lt (show (6 * w + 6) % 2 ^ 6 < 2 ^ 64 by omega)]
  rw [hK, hT]
  have fD := h.arr_fit hD
  have hS : S w = 8 * (w + 2) := rfl
  refine ⟨rfl, ?_, rfl, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt h64]
    have : (6 * w + 6) / 2 ^ 6 * 2 ^ 3 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (show arr w aDR < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show arr w aDR + 8 * ((6 * w + 6) / 64) < 2 ^ 64 by omega)]
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have : (6 * w + 6) % 64 % 2 ^ 64 = (6 * w + 6) % 64 := Nat.mod_eq_of_lt (by omega)
    rw [this]
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega


/-- The dividend: `n` words at word `Q` of a number of `w` words, zero elsewhere. -/
theorem placed_val {m m0 : Mem} {B : Addr} {d w Q n : Nat} (hQ : Q + n ≤ w) (hz : wordsVal m0 B d w = 0)
    (ho : Outside B (d + 8 * Q) (8 * n) m0 m) (hf : d + 8 * w ≤ 2 ^ 64) :
    wordsVal m B d w = 2 ^ (64 * Q) * wordsVal m B (d + 8 * Q) n := by
  have e1 := wordsVal_append m B d Q (w - Q)
  have e2 := wordsVal_append m B (d + 8 * Q) n (w - Q - n)
  rw [show Q + (w - Q) = w by omega] at e1
  rw [show n + (w - Q - n) = w - Q by omega] at e2
  have z1 : wordsVal m B d Q = 0 := by
    rw [ho.wordsVal (.inl (by omega)) (by omega)]
    simpa using wordsVal_zero_part (a := 0) (c := Q) hz (by omega)
  have z2 : wordsVal m B (d + 8 * Q + 8 * n) (w - Q - n) = 0 := by
    rw [ho.wordsVal (.inr (by omega)) (by omega), show d + 8 * Q + 8 * n = d + 8 * (Q + n) by omega]
    exact wordsVal_zero_part hz (by omega)
  rw [e1, e2, z1, z2]
  simp

/-- `tail`: `y := y 2^(6 (w + 1)) mod m` in array 3, for `y < 2^(64 v)`,
exact for `m` (array 8) of exactly `v = w / 2` words. -/
theorem tail_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w nArr) (hw : 8 ≤ w) (hw2 : w % 2 = 0) :
    WP isa tail s fun t => Ws t B Z w nArr ∧ Keys.Frame B w [aDR, 3, aTD, aTT] [] s.mem t.mem ∧
      Keep dwRegs s t ∧
      (num s.mem B w 3 < 2 ^ (64 * (w / 2)) → InW w (num s.mem B w 8) →
        num t.mem B w 3 = num s.mem B w 3 * 2 ^ (6 * (w + 1)) % num s.mem B w 8) := by
  have hS : S w = 8 * (w + 2) := rfl
  have fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have hwl := h.wle
  have nw := h.nowrap
  have fR := fit aDR (by decide)
  have d3R : arr w 3 + S w ≤ arr w aDR := arr_end (by decide)
  have hT0 : 0 < (6 * w + 6) % 64 := by omega
  have hK : 6 * (w + 1) = 64 * ((6 * w + 6) / 64) + (6 * w + 6) % 64 := by omega
  generalize hQ : (6 * w + 6) / 64 = Q at hK
  generalize hT : (6 * w + 6) % 64 = T at hK hT0
  have hT64 : T < 64 := by omega
  have hQv : Q + (w / 2 + 1) ≤ w := by omega
  unfold tail
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (InvBatch.zeroWs_ok h (j := aDR) (by decide) (by decide)) fun t1 ⟨w1, f1, z1, k1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (tailSetup_ok w1 (by decide)) fun t2 ⟨⟨p0, p1, p2, p6, p4, p3, m2⟩, k2⟩ => ?_
  rw [hQ] at p1
  rw [hT] at p2 p6
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have w2 := w1.of_keep k2
  refine WP.mono (Loops.shlTLoop_ok w2.scr (dS := arr w 3) (dO := arr w aDR + 8 * Q) (n := w / 2 + 1)
    p0 p1 p2 p6 p4 p3 hT0 hT64 (by omega) (by omega) (arr_al _ _) (by have := arr_al w aDR; omega)
    (by have := w2.arr_fit (j := 3) (by decide); omega) (by have := w2.arr_fit (j := aDR) (by decide); omega)
    (.inl (by omega))) fun t3 ⟨v3, o3, k3⟩ => ?_
  -- `y`'s words, and the dividend.
  have nR3 : num s.mem B w 3 < 2 ^ (64 * (w / 2)) →
      num t3.mem B w aDR = num s.mem B w 3 * 2 ^ (6 * (w + 1)) := fun hy => by
   have y1 : num t1.mem B w 3 = num s.mem B w 3 := f1.num (by decide) (by simp) (fit _ (by decide))
   have yv : wordsVal t2.mem B (arr w 3) (w / 2 + 1) = num s.mem B w 3 := by
     rw [m2]
     exact words_low (by omega) y1 (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by omega)))
   rw [yv] at v3
   have ylt : num s.mem B w 3 * 2 ^ T < 2 ^ (64 * (w / 2 + 1)) := by
     rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
     exact Nat.mul_lt_mul_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by omega)) (Nat.two_pow_pos _)
   have c0 : (t3.gpr .a4).toNat = 0 := by
     rcases Nat.eq_zero_or_pos (t3.gpr .a4).toNat with e | e
     · exact e
     · have := Nat.le_mul_of_pos_right (2 ^ (64 * (w / 2 + 1))) e
       omega
   rw [c0, Nat.mul_zero, Nat.add_zero] at v3
   have o3' : Outside B (arr w aDR + 8 * Q) (8 * (w / 2 + 1)) t1.mem t3.mem := by rw [← m2]; exact o3
   show wordsVal t3.mem B (arr w aDR) w = _
   rw [placed_val hQv z1 o3' (by omega), v3, hK, Nat.pow_add]
   ac_rfl
  have w3 : Ws t3 B Z w nArr := w2.of_keep k3
  have F3 : Keys.Frame B w [aDR] [] s.mem t3.mem :=
    f1.trans (Keys.Frame.of_arr (o := aDR) (d := 8 * Q) (n := 8 * (w / 2 + 1)) (by rw [← m2]; exact o3)
      (by omega) (by simp))
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (InvBatch.zeroWs_ok w3 (j := 3) (by decide) (by decide)) fun t4 ⟨w4, f4, z4, k4⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (Keys.copy_ok w4 (o := aTD) (a := 8) (by decide) (by decide) (by decide) (by decide))
    fun t5 ⟨w5, f5, v5, k5, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (fixTop_ok w5 (m := aTD) (by decide) (by decide) (by omega))
    fun t6 ⟨w6, f6, v6, p6', _, _, k6, _⟩ => ?_
  rw [show seqs [VG.Impl.Rsa.RISCV64.WordDiv.divW aDR VG.Impl.Rsa.RISCV64.InvBatch.aY aTD aTT] =
    VG.Impl.Rsa.RISCV64.WordDiv.divW aDR VG.Impl.Rsa.RISCV64.InvBatch.aY aTD aTT from rfl]
  have n3 : num t6.mem B w 3 = 0 := by
    rw [f6.num (by decide) (by simp) (fit _ (by decide)), f5.num (by decide) (by simp) (fit _ (by decide))]
    exact z4
  have nR : num t6.mem B w aDR = num t3.mem B w aDR := by
    rw [f6.num (by decide) (by simp) (fit _ (by decide)), f5.num (by decide) (by simp) (fit _ (by decide)),
      f4.num (by decide) (by simp) (fit _ (by decide))]
  have r0 : wordsVal t6.mem B (arr w 3) (w / 2) = 0 := by
    simpa using wordsVal_zero_part (a := 0) (c := w / 2) n3 (by omega)
  refine WP.mono (divW_ok w6 (a := aDR) (r := 3) (m := aTD) (t := aTT) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw hw2 r0 p6')
    fun t ⟨w7, f7, k7, x7, top7, hi7⟩ => ?_
  refine ⟨w7, ?_, ?_, fun hy hin => ?_⟩
  · exact (F3.mono (by simp) (by simp)).trans ((f4.mono (by simp) (by simp)).trans ((f5.mono (by simp) (by simp)).trans
      ((f6.mono (by simp) (by simp)).trans (f7.mono (by simp) (by simp)))))
  · exact Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans'
      (k1.mono (rs' := dwRegs) (by decide)) (k2.mono (rs' := dwRegs) (by decide)))
      (k3.mono (rs' := dwRegs) (by decide))) (k4.mono (rs' := dwRegs) (by decide)))
      (k5.mono (rs' := dwRegs) (by decide))) (k6.mono (rs' := dwRegs) (by decide)))
      (k7.mono (rs' := dwRegs) (by decide))
  · -- The divisor is `m`, whose top word is not zero.
    have m8 : num t4.mem B w 8 = num s.mem B w 8 := by
      rw [f4.num (by decide) (by simp) (fit _ (by decide)), F3.num (by decide) (by simp) (fit _ (by decide))]
    have mv : wordsVal t5.mem B (arr w aTD) (w / 2) = num s.mem B w 8 :=
      words_low (w := w) (v := w / 2) (by omega) (show num t5.mem B w aTD = _ by rw [v5, m8]) hin.2
    have tp := top_pos (m := t5.mem) (B := B) (d := arr w aTD) (v := w / 2) (by omega) (by rw [mv]; exact hin.1)
    have hne : ¬ (word t5.mem B (arr w aTD + 8 * (w / 2 - 1))).toNat = 0 := by omega
    rw [v6, mv, ite_eq_right hne, Nat.add_zero, nR, nR3 hy] at x7
    refine num_of_low (v := w / 2) (by omega) x7 top7 ?_
    rw [hi7]
    exact wordsVal_zero_part n3 (by omega)

end VG.Proof.Rsa.RISCV64.CrtValues
