module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.St
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.St
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import VerifiedGarbage.Proof.Rsa.Arm.RdTwos
import VerifiedGarbage.Proof.Rsa.TwosMath
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Tools
import VerifiedGarbage.Proof.Rsa.Arm.Stage.MM
import VerifiedGarbage.Proof.Rsa.Arm.Stage.KS
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Taint2
import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont2
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Dsa.Arm.Prime.Math`, which this module and modules that import it used -/

section

/-! # A candidate on ARMv7: the bits the code sets and clears

The candidate's two top bits set by or'ing its top word with `0xC0000000`
(`topBits_val`), and its low bit by `orOne` (`candidate_eq`); a witness's
bit 1 set (`or_two_split`) and its top bit cleared by shifting its top word
(`clrTop_val`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime

/-- A word shifted left one bit and back: its top bit cleared. -/
theorem bv_clr_top (v : BitVec 32) : ((v <<< 1) >>> 1).toNat = v.toNat % 2 ^ 31 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := v.isLt
  rw [show (2 : Nat) ^ 32 = 2 ^ 31 * 2 from rfl, Nat.pow_one, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (by decide)]

/-- The top word, word `i`, of a number of `i + 1` words with its top bit cleared. -/
theorem clrTop_val {x i : Nat} (hx : x < 2 ^ (32 * i + 32)) :
    x % 2 ^ (32 * i) + 2 ^ (32 * i) * ((BitVec.ofNat 32 (x / 2 ^ (32 * i) % 2 ^ 32) <<< 1) >>> 1).toNat +
      2 ^ (32 * (i + 1)) * (x / 2 ^ (32 * (i + 1))) = x % 2 ^ (32 * i + 31) := by
  have e : x / 2 ^ (32 * (i + 1)) = 0 := Nat.div_eq_of_lt (by rwa [Nat.mul_succ])
  rw [e, Nat.mul_zero, Nat.add_zero, bv_clr_top, BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_mod_of_dvd _ (by decide),
    Nat.pow_add, Nat.mod_mul]

/-- Or'ing with a number below `2^32` changes only the low word. -/
theorem or_low {x b : Nat} (hb : b < 2 ^ 32) : x ||| b = (x % 2 ^ 32 ||| b) + 2 ^ 32 * (x / 2 ^ 32) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hl : x % 2 ^ 32 ||| b < 2 ^ 32 := Nat.or_lt_two_pow (Nat.mod_lt _ (by decide)) hb
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hl, Nat.testBit_or, Nat.testBit_or, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow]
  by_cases h : i < 32
  · simp [h]
  · simp only [h, ↓reduceIte]
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega_using [h]))),
      Bool.or_false, Nat.sub_add_cancel (by omega_using [h])]

end VG.Proof.Dsa.Arm.Prime

end

end

/-! ### `Dsa.Arm.Prime.Words`, which this module and modules that import it used -/

section

/-! # A candidate on ARMv7: a high word of an array changed

`hiOp_ok`: word `i` of `[j]`, at byte `4 W − c`, read into `r1`, changed by
`ops` and stored back (`topBits`, `clrTopBit`); `val32_write_any`: a word
written into a number of words.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

/-- Word `i` of a number of `k` words. -/
theorem val32_word (m : Mem) (base : Addr) {d k i : Nat} (hi : i < k) :
    w32 m base (d + 4 * i) = val32 m base d k / 2 ^ (32 * i) % 2 ^ 32 := by
  obtain ⟨r, rfl⟩ : ∃ r, k = i + (r + 1) := ⟨k - i - 1, by omega_arith⟩
  rw [val32_append m base d i (r + 1)]
  simp only [val32]
  have lo := val32_lt m base d i
  have hw : w32 m base (d + 4 * i) < 2 ^ 32 := (m.readW _ 32).isLt
  have hp : 0 < 2 ^ (32 * i) := Nat.two_pow_pos _
  rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt lo, Nat.zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hw]

/-- Word `i` of a number written. -/
theorem val32_write_any (m : Mem) (base : Addr) {d k i : Nat} (v : BitVec 32) (hi : i < k)
    (fit : d + 4 * k ≤ 2 ^ 64) :
    val32 (m.writeW (off base (d + 4 * i)) v) base d k =
      val32 m base d k % 2 ^ (32 * i) + 2 ^ (32 * i) * v.toNat + 2 ^ (32 * (i + 1)) * (val32 m base d k / 2 ^ (32 * (i + 1))) := by
  have o := writeW32_outside m base (d := d + 4 * i) v (by omega_arith)
  obtain ⟨r, rfl⟩ : ∃ r, k = i + (r + 1) := ⟨k - i - 1, by omega_arith⟩
  rw [val32_append _ base d i (r + 1), val32_append m base d i (r + 1)]
  simp only [val32]
  have e1 : val32 (m.writeW (off base (d + 4 * i)) v) base d i = val32 m base d i := o.val32 (by omega_arith) (by omega_arith)
  have e2 : w32 (m.writeW (off base (d + 4 * i)) v) base (d + 4 * i) = v.toNat := by
    simp only [w32]; rw [Mem.readW_writeW_self32]
  have e3 : val32 (m.writeW (off base (d + 4 * i)) v) base (d + 4 * i + 4) r = val32 m base (d + 4 * i + 4) r :=
    o.val32 (by omega_arith) (by omega_arith)
  rw [e1, e2, e3]
  have lo := val32_lt m base d i
  have hw : w32 m base (d + 4 * i) < 2 ^ 32 := (m.readW _ 32).isLt
  have hp : 0 < 2 ^ (32 * i) := Nat.two_pow_pos _
  have hq : 2 ^ (32 * (i + 1)) = 2 ^ (32 * i) * 2 ^ 32 := by rw [← Nat.pow_add]; congr 1
  generalize val32 m base d i = L at *
  generalize w32 m base (d + 4 * i) = x at *
  generalize val32 m base (d + 4 * i + 4) r = T
  have hmod : (L + 2 ^ (32 * i) * (x + 2 ^ 32 * T)) % 2 ^ (32 * i) = L := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lo]
  have hdiv : (L + 2 ^ (32 * i) * (x + 2 ^ 32 * T)) / 2 ^ (32 * (i + 1)) = T := by
    rw [hq, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt lo, Nat.zero_add,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos 32), Nat.div_eq_of_lt hw, Nat.zero_add]
  rw [hmod, hdiv, hq, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem hiOpR_ok {s : State} {B : BitVec 32} {Z w N j i : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) (hr2 : s.gpr .r2 = BitVec.ofNat 32 (4 * (i + 1)))
    (hiw : i < w) {ops rest : List Instr} {Q : State → Prop} {f : BitVec 32 → BitVec 32}
    (hops : ∀ u : State, ∀ R : State → Prop, (∀ u', Upd u u' .r1 (f (u.gpr .r1)) → R u') →
      WP isa (.block ops) u R)
    (k : ∀ t, Ws t B Z w N → Keep B w [j] [] s.mem t.mem →
      num t.mem B w j = num s.mem B w j % 2 ^ (32 * i) +
        2 ^ (32 * i) * (f (BitVec.ofNat 32 (num s.mem B w j / 2 ^ (32 * i) % 2 ^ 32))).toNat +
        2 ^ (32 * (i + 1)) * (num s.mem B w j / 2 ^ (32 * (i + 1))) →
      Rest [.r0, .r1] s t → WP isa (.block rest) t Q) :
    WP isa (.block (ptr .r0 j ++ .dp .add .r0 .r0 (.reg .r2) :: .dp .sub .r0 .r0 (.imm 4) ::
      .ldr .r1 .r0 0 :: (ops ++ .str .r1 .r0 0 :: rest))) s Q := by
  have fit := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  have wl := h.wle
  refine ptr_ok h (by decide) (by omega_arith) fun s1 p1 r1 m1 h1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  have e3 : s3.gpr .r0 = B + BitVec.ofNat 32 (arr w j + 4 * i) := by
    rw [u3.gpr, dpVal, u2.gpr, dpVal, p1, r1.gpr _ (by decide), hr2]
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    show B + BitVec.ofNat 32 _ - BitVec.ofNat 32 4 = _
    rw [VG.Proof.Rsa.Arm.Recover.add_ofNat_sub32 _ (by omega_arith)]
    congr 2
  have h3 : Ws s3 B Z w N :=
    (h1.of_upd u2 (by decide) (by decide) (by decide)).of_upd u3 (by decide) (by decide) (by decide)
  have a0 : State.addr (s3.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w j + 4 * i) := by
    rw [e3, BitVec.add_zero]; exact h.addr (by omega_arith)
  refine wp_ldr (by decide) a0 (h3.read (by omega_arith)) fun s4 u4 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hops s4 _ fun u' x => x) fun s5 u5 => ?_
  have h5 : Ws s5 B Z w N := (h3.of_upd u4 (by decide) (by decide) (by decide)).of_upd u5 (by decide)
    (by decide) (by decide)
  have a5 : State.addr (s5.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w j + 4 * i) := by
    rw [u5.other _ (by decide), u4.other _ (by decide)]; exact a0
  refine wp_str (by decide) a5 (h5.write (by omega_arith)) fun t u6 => ?_
  have mt : t.mem = s.mem.writeW (off (State.addr B) (arr w j + 4 * i)) (s5.gpr .r1) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, m1]
  have o1 := writeW32_outside s.mem (State.addr B) (d := arr w j + 4 * i) (s5.gpr .r1) (by omega_arith)
  rw [← mt] at o1
  refine k t (h5.of_mupd u6) (Keep.of_arr (d := 4 * i) o1 (by omega_arith) (by simp)) ?_
    ((r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans (u6.rest _))))))
  have v4 : s4.gpr .r1 = BitVec.ofNat 32 (num s.mem B w j / 2 ^ (32 * i) % 2 ^ 32) := by
    rw [u4.gpr, u3.mem, u2.mem, m1]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))]
    exact val32_word s.mem (State.addr B) hiw
  change val32 _ _ _ _ = _
  rw [mt, val32_write_any _ _ _ hiw (by omega_arith), u5.gpr, v4]

end VG.Proof.Dsa.Arm.Prime

end

end

/-! # A candidate on ARMv7: more operations as pieces

Halvings, words of constants, header words set, the candidate's bits and a
witness's fixed bits, as pieces (`VP`) on a stage.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)
open VG.Impl.RsaKeyGen.Arm.Key (setWd setHi)

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- `r11 := 0`. -/
theorem St.pmov11 (cert : Cert (.block [.mov .r11 (.imm 0)])) : VP (St P E A L V LS) (.block [.mov .r11 (.imm 0)])
    (fun σ s => St P E A L V LS σ s ∧ s.gpr .r11 = 0) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ =>
    wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ⟨⟨e, h.of_rest (u.rest (ws := [.r11]) (by simp)) u.mem,
      hw.of_upd u (by decide) (by decide) (by decide)⟩, u.gpr⟩

/-- `half j` with `r11 = 0`: `[j] := [j] / 2`. -/
theorem St.phalf {j : Nat} (cert : Cert (half j)) (hj : j ∈ L) :
    VP (fun σ s => St P E A L V LS σ s ∧ s.gpr .r11 = 0) (half j)
      (St P E (fun σ => upd (A σ) j (A σ j / 2)) (j :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, r11⟩ => by
    have hj' := h.live_lt j hj
    exact WP.mono (half_ok hw hj' (by decide) (by rw [r11]; decide)) fun t ⟨ht, k, v, r⟩ =>
      ⟨e, h.write1 k hj' (by simp) r.sp r.rd r.wr (by rw [v, r11, h.arrs j hj]; simp) (by simp), ht⟩

/-- `setWd j o x`: word `o / 4` of `[j]` := `x`, above the number. -/
theorem St.psetWd {j o x : Nat} (cert : Cert (.block (setWd j o x))) (hj : j ∈ L) (ho : o % 4 = 0)
    (how : o / 4 < 10) (hx : encodable (BitVec.ofNat 32 x) = true)
    (hl : ∀ σ, E σ → A σ j < 2 ^ (32 * (o / 4))) :
    VP (St P E A L V LS) (.block (setWd j o x))
      (St P E (fun σ => upd (A σ) j (A σ j + 2 ^ (32 * (o / 4)) * (x % 2 ^ 32))) (j :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    rw [← List.append_nil (setWd j o x)]
    have hj' := h.live_lt j hj
    refine setWd_ok hw hj' (by decide) ho (by have := h.pre.wge; omega_using [how, this]) hx (by rw [h.arrs j hj]; exact hl σ e)
      fun t ht k v r => WP.block_nil ⟨e, h.write1 k hj' (by simp) r.sp r.rd r.wr (by rw [v, h.arrs j hj]) (by simp),
        ht⟩

/-- `setS d v`: the header word `d := v`. -/
theorem St.psetS {d v : Nat} (cert : Cert (.block (setS d v))) (hd : LsOk d) (hv : encodable (BitVec.ofNat 32 v) = true)
    (hv' : v < 2 ^ 32) :
    VP (St P E A L V LS) (.block (setS d v)) (St P E A L (fun σ => upd (V σ) d v) (d :: LS)) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    unfold setS
    refine wp_mov (op2_imm hv) fun s1 u1 => ?_
    have h1 := h.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
    have hw1 := hw.of_upd u1 (by decide) (by decide) (by decide)
    refine h1.str hw1 hd fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
    rwa [u1.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv'] at ht

end

end VG.Proof.Dsa.Arm.Prime
