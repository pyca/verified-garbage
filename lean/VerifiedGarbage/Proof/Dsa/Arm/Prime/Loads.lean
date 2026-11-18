module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Base
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Rsa.Arm.KcStart
import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Bignum.Arm.LoadBE
import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
import VerifiedGarbage.Proof.Rsa.Arm.Stage.KS
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Loads
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Mul
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
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Taint2
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont2
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Dsa.Arm.Prime.Ops`, which the modules that import this one used -/

section

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

end

end

/-! # A candidate on ARMv7: the frame's words, the working space set up, and loads

`Bk P σ s`: what every state of the body keeps of `σ`: memory but `chg`.
Frame words but 0 keep their values (`Bk.fwEq`, `KS.fwEq`). `LS P σ
A s`: the working space with `W` words, `W` in the division's header, and
every array's `W + 2` words holding `A`. `load_okC`: an array read from
octets most significant first.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

structure Bk (P : CP) (σ s : State) : Prop where
  pre : In P σ
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  frame : Frame P.chg σ.mem s.mem

structure LS (P : CP) (σ : State) (A : Nat → Nat) (s : State) : Prop where
  bk : Bk P σ s
  ws : Ws s P.B P.Z P.W nArr
  cnt : slot s.mem P.B 16 = P.W
  full : ∀ j < nArr, val32 s.mem (State.addr P.B) (arr P.W j) (P.W + 2) = A j

/-- A frame word other than 0. -/
abbrev FwOk (o : Nat) : Prop := 4 ≤ o ∧ o + 4 ≤ 88 ∧ o % 4 = 0

section
variable {P : CP} {σ s t : State}

theorem In.rC_eq (pre : In P σ) : P.rC = ⟨State.addr P.sp - BitVec.ofNat 64 56, 56⟩ := by
  show (⟨State.addr (P.sp - BitVec.ofNat 32 56), 56⟩ : Region) = _
  rw [FrameStack.addr_sub' pre.spLo]

/-- A frame word but 0 is apart from what the body changes. -/
theorem In.fwSep (pre : In P σ) {o : Nat} (ho : FwOk o) :
    ∀ r ∈ P.chg, Region.Disjoint ⟨off (State.addr P.sp) o, 4⟩ r := by
  have spf := pre.spFit
  intro r hr
  simp only [CP.chg, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact pre.sF.symm.sub_left (Offset.sub_base _ (by omega))
  · exact pre.uF.symm.sub_left (Offset.sub_base _ (by omega))
  · rw [pre.rC_eq]; exact Offset.disjoint_below _ (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)

/-- A frame word is readable. -/
theorem In.fwRead (pre : In P σ) {o : Nat} (ho' : o + 4 ≤ 88) (h4 : o % 4 = 0) :
    InRegions (σ.rd ++ σ.wr) (off (State.addr P.sp) o) 4 := by
  have spf := pre.spFit
  rcases (by omega_arith : o + 4 ≤ 56 ∨ 56 ≤ o) with c | c
  · exact ⟨⟨State.addr P.sp, 56⟩, List.mem_append_right _ (by rw [pre.wr]; simp),
      Offset.contains_base _ c (by omega_arith)⟩
  · have read := CallLay.inRegions_sub pre.rdA (off := o - 56) (l := 4) (by omega_arith) (by decide)
    rwa [show off (State.addr P.sp) 56 + BitVec.ofNat 64 (o - 56) = off (State.addr P.sp) o by
      simp only [off]; rw [Offset.add_add]; congr 2; omega_arith] at read

theorem Bk.of_rest (h : Bk P σ s) {rs : List Reg} (r : Rest rs s t) (m : t.mem = s.mem) : Bk P σ t :=
  ⟨h.pre, r.sp.trans h.sp, r.rd.trans h.rd, r.wr.trans h.wr, m ▸ h.frame⟩

theorem Bk.of_frame (h : Bk P σ s) (f : Frame P.chg s.mem t.mem) (sp : t.sp = s.sp) (rd : t.rd = s.rd)
    (wr : t.wr = s.wr) : Bk P σ t :=
  ⟨h.pre, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, h.frame.trans f⟩

theorem Bk.of_upd (h : Bk P σ s) {r : Reg} {v : BitVec 32} (u : Upd s t r v) : Bk P σ t :=
  ⟨h.pre, u.sp.trans h.sp, u.rd.trans h.rd, u.wr.trans h.wr, u.mem ▸ h.frame⟩

theorem Bk.rS_mem (h : Bk P σ s) : P.rS ∈ s.wr := by rw [h.wr]; exact h.pre.rS_mem

theorem KS.bk {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat} (h : KS P σ A live V ls s) :
    Bk P σ s :=
  ⟨h.pre, h.sp, h.rd, h.wr, h.frame⟩

/-- A frame word keeps its value. -/
theorem Bk.fwEq (h : Bk P σ s) {o : Nat} (ho : FwOk o) : fw s.mem P o = fw σ.mem P o :=
  h.frame.readW (r := ⟨off (State.addr P.sp) o, 4⟩) (Region.contains_self _ _) (h.pre.fwSep ho) (by decide)

/-- `ldr t, [sp, #o]` of a frame word whose value `v` is known. -/
theorem Bk.ldrSpV (h : Bk P σ s) {o : Nat} (ho' : o + 4 ≤ 88) (h4 : o % 4 = 0) {v : BitVec 32}
    (hv : fw s.mem P o = v) {t : Reg} {rest : List Instr}
    {Q : State → Prop} (k : ∀ s', Upd s s' t v → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrSp t o :: rest)) s Q := by
  have pre := h.pre
  have spf := pre.spFit
  obtain ea : State.addr (s.sp + BitVec.ofNat 32 o) = off (State.addr P.sp) o := by
    rw [h.sp, pre.sp]; exact addr_add (by omega_arith)
  refine wp_loadStack (by omega_arith) ea ?_ fun s' u => k s' (by rw [← hv]; exact u)
  rw [h.rd, h.wr]
  exact pre.fwRead ho' h4

/-- `ldr t, [sp, #o]` of a frame word but 0. -/
theorem Bk.ldrSp (h : Bk P σ s) {o : Nat} (ho : FwOk o) {t : Reg} {rest : List Instr}
    {Q : State → Prop} (k : ∀ s', Upd s s' t (fw σ.mem P o) → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrSp t o :: rest)) s Q :=
  h.ldrSpV ho.2.1 ho.2.2 (h.fwEq ho) k

/-- `setupC` after the base and `out_len` are loaded. -/
theorem setupTail_ok (h : Bk P σ s) (r8 : s.gpr .r8 = P.B) (r9 : s.gpr .r9 = BitVec.ofNat 32 P.L) :
    WP isa (.block (([.mov .r9 (.shifted .r9 .lsr 2), .dp .add .r9 .r9 (.imm 2)] : List Instr) ++ stride ++
      ([.str .r9 .r8 16, .dp .add .r0 .r8 (.imm (BitVec.ofNat 32 hdr)), .mov .lr (.imm (BitVec.ofNat 32 nArr)),
        .mul .lr .lr .r7, .mov .lr (.shifted .lr .lsr 2), .mov .r3 (.imm 0)] : List Instr))) s fun t =>
      Bk P σ t ∧ Ws t P.B P.Z P.W nArr ∧ slot t.mem P.B 16 = P.W ∧
      t.gpr .r0 = P.B + BitVec.ofNat 32 hdr ∧ t.gpr .lr = BitVec.ofNat 32 (nArr * (P.W + 2)) ∧
      t.gpr .r3 = 0 := by
  have pre := h.pre
  obtain k1 := pre.k1; have k2 := pre.k2
  have wl := pre.wle
  simp only [List.cons_append, List.append_assoc]
  refine wp_mov (op2_lsr (by decide)) fun s1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  obtain h9 : s2.gpr .r9 = BitVec.ofNat 32 P.W := by
    rw [u2.gpr, dpVal, u1.gpr, r9]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, show (2 : BitVec 32).toNat = 2 from rfl]
    simp only [CP.W]
    omega_arith
  refine VG.Proof.Rsa.Arm.KeyCheck.stride_ok (by omega_arith) h9 fun s5 h7 r5 m5 => ?_
  obtain r45 : Rest [.r9, .r7] s s5 := (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (r5.mono (by simp)))
  obtain m45 : s5.mem = s.mem := m5.trans (u2.mem.trans u1.mem)
  obtain ws5 : Ws s5 P.B P.Z P.W nArr :=
    ⟨pre.fS, by rw [r45.wr]; exact h.rS_mem, pre.fits, by simp only [CP.W]; omega_arith, by simp only [CP.W]; omega_arith, h7,
      by rw [r45.gpr _ (by decide), r8], by rw [r5.gpr _ (by decide), h9]⟩
  refine wp_strSlot ws5 (d := 16) (by decide) fun s6 u6 => ?_
  obtain ws6 := ws5.of_mupd u6
  obtain o6 := writeW32_outside s5.mem (State.addr P.B) (d := 16) (s5.gpr .r9) (by decide)
  rw [← u6.mem] at o6
  refine wp_dp (op2_imm (by decide)) fun s7 u7 => ?_
  refine wp_mov (op2_imm (by decide)) fun s8 u8 => ?_
  refine wp_mul fun s9 u9 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s10 u10 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u11 => WP.block_nil ?_
  obtain rt : Rest [.r0, .lr, .r3] s6 t := (u7.rest (by simp)).trans ((u8.rest (by simp)).trans
    ((u9.rest (by simp)).trans ((u10.rest (by simp)).trans (u11.rest (by simp)))))
  obtain mt : t.mem = s6.mem := by rw [u11.mem, u10.mem, u9.mem, u8.mem, u7.mem]
  obtain ot : Outside (State.addr P.B) 16 4 s.mem t.mem := by rw [mt, ← m45]; exact o6
  have hz := pre.hdr_Z
  refine ⟨h.of_frame (fun x hx => ot x (.inr ?_)) (by rw [rt.sp, u6.sp, r45.sp]) (by rw [rt.rd, u6.rd, r45.rd])
      (by rw [rt.wr, u6.wr, r45.wr]), ws6.rest rt, ?_, ?_, ?_, by rw [u11.gpr]⟩
  · have := hx _ (List.mem_cons_self)
    simp only [Region.Contains] at this
    simp only [ofs, hdr] at *; omega_arith
  · rw [mt, u6.mem, slot_write_self, ws5.r9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  · rw [u11.other _ (by decide), u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.gpr,
      dpVal, u6.gpr, ws5.r8]
  · rw [u11.other _ (by decide), u10.gpr, u9.gpr, u8.gpr, u8.other _ (by decide), u7.other _ (by decide), u6.gpr,
      ws5.r7]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [nArr, S]
    rw [Nat.mod_eq_of_lt (a := 65) (by decide), Nat.mod_eq_of_lt (a := 4 * (P.W + 2)) (by omega_arith),
      Nat.mod_eq_of_lt (a := 65 * (4 * (P.W + 2))) (by omega_arith), Nat.mod_eq_of_lt (a := 65 * (P.W + 2)) (by omega_arith)]
    omega_arith

theorem zero_ls (h : Bk P σ s) (hw : Ws s P.B P.Z P.W nArr) (cnt : slot s.mem P.B 16 = P.W)
    (p0 : s.gpr .r0 = P.B + BitVec.ofNat 32 hdr) (plr : s.gpr .lr = BitVec.ofNat 32 (nArr * (P.W + 2)))
    (r3 : s.gpr .r3 = 0) : WP isa VG.Impl.Bignum.Arm.zero s (LS P σ fun _ => 0) := by
  have pre := h.pre
  have fits := pre.fits
  obtain nfit : hdr + 4 * (nArr * (P.W + 2)) ≤ P.Z := by
    obtain e : arr P.W nArr = hdr + 4 * (nArr * (P.W + 2)) := by
      show hdr + nArr * (4 * (P.W + 2)) = _; rw [Nat.mul_left_comm]
    rw [← e]; exact fits
  refine WP.mono (zero_ok s (base := P.B) (size := P.Z) (o := hdr) (n := nArr * (P.W + 2))
    ⟨pre.fS, nfit, ⟨P.rS, h.rS_mem, Region.contains_self _ _⟩⟩ (Nat.mul_pos (by decide) (by omega_arith)) p0 plr r3)
    fun t inv => ?_
  refine ⟨h.of_frame (fun x hx => inv.outside x (.inr ?_)) inv.rest.sp inv.rest.rd inv.rest.wr,
    hw.rest inv.rest, ?_, fun j hj => ?_⟩
  · have := hx _ (List.mem_cons_self)
    simp only [Region.Contains] at this
    simp only [ofs] at *; omega_arith
  · rw [← cnt]
    exact inv.outside.w32 (d := 16) (by simp only [hdr]; omega_arith) (by decide)
  · have := VG.Proof.Rsa.Arm.CrtValues.val32_zero_part inv.value (a := j * (P.W + 2)) (c := P.W + 2) (by
      have := Nat.mul_le_mul_right (P.W + 2) (show j + 1 ≤ nArr by omega_arith)
      rw [Nat.succ_mul] at this; omega_arith)
    simpa only [arr, S, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

/-- `load j`: array `j`'s `W + 2` words := the `k` bytes at `r4` (`r6 = k`). -/
theorem load_okC (h : Bk P σ s) (hw : Ws s P.B P.Z P.W nArr) {j : Nat}
    (hj : j < nArr) {src : BitVec 32} {k : Nat}
    (rd : InRegions (σ.rd ++ σ.wr) (State.addr src) k) (sepC : ∀ r ∈ P.chg, Region.Disjoint ⟨State.addr src, k⟩ r)
    (fit : src.toNat + k ≤ 2 ^ 32) (hk : 0 < k)
    (hkL : k ≤ P.L) (p4 : s.gpr .r4 = src) (p6 : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa (VG.Impl.Rsa.Arm.CrtValues.load j) s fun t => Bk P σ t ∧ Ws t P.B P.Z P.W nArr ∧
      Keep P.B P.W [j] [] s.mem t.mem ∧
      val32 t.mem (State.addr P.B) (arr P.W j) (P.W + 2) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt σ.mem (State.addr src) k) ∧
      Rest [.r0, .r1, .r2, .r3, .r5, .lr] s t := by
  have pre := h.pre
  obtain fa := hw.arr_fit hj
  have nw := hw.nowrap
  have hS : S P.W = 4 * (P.W + 2) := rfl
  obtain hkw : k ≤ 4 * P.W := by simp only [CP.W]; omega_arith
  obtain sepS : Region.Disjoint ⟨State.addr src, k⟩ P.rS := sepC _ List.mem_cons_self
  rw [VG.Impl.Rsa.Arm.CrtValues.load, WP.seq_iff]
  refine ptr_ok hw (by decide) (by simp only [nArr] at hj; omega_arith) fun s1 p1 r1 m1 h1 => ?_
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u4 => WP.block_nil ?_
  obtain rest : Rest [.r0, .r3, .r5, .lr] s u :=
    (r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp))))
  obtain mu : u.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, m1]
  obtain bu := h.of_rest rest mu
  obtain hu := hw.rest rest
  obtain ad : State.addr (P.B + BitVec.ofNat 32 (arr P.W j)) = off (State.addr P.B) (arr P.W j) :=
    hw.addr (by omega_arith)
  obtain p0 : u.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W j) := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), p1]
  refine WP.mono (loadBE_ok u (src := src) (dst := P.B + BitVec.ofNat 32 (arr P.W j)) (n := P.W + 2)
    hk (by omega_arith) (by omega_arith) fit
    (by rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega_arith), BitVec.toNat_ofNat]; omega_arith)
    (by rw [bu.rd, bu.wr]; exact rd)
    ⟨P.rS, bu.rS_mem, by rw [ad]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    (by
      rw [ad]
      refine fun a ha hb => sepS a ha ?_
      exact Region.Contains.byte (r := P.rS) (b := off (State.addr P.B) (arr P.W j)) (n := 4 * (P.W + 2))
        (Offset.contains_base _ (by omega_arith) (by omega_arith)) (by simp only [Region.Contains] at hb; omega_arith))
    p0 (by rw [rest.gpr _ (by decide), p4])
    (by rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, p1])
    (by rw [rest.gpr _ (by decide), p6])
    (by rw [u4.other _ (by decide), u3.gpr, dpVal, u2.other .r9 (by decide), r1.gpr .r9 (by decide), hw.r9]
        exact (BitVec.ofNat_add_ofNat (n := 32) P.W 2))
    (by rw [u4.gpr])) ?_
  rintro t ⟨v, f, r⟩
  rw [ad] at f v
  obtain k : Keep P.B P.W [j] [] u.mem t.mem := VG.Proof.Rsa.Arm.CrtValues.Keep.of_frame_arr f (by omega_arith)
  refine ⟨bu.of_frame (keep_frameC k (by simpa using pre.fitZ hj) (by simp) pre.hdr_Z) r.sp r.rd r.wr,
    hu.rest r, mu ▸ k, ?_, (rest.mono (by simp)).trans (r.mono (by simp))⟩
  rw [VG.Proof.Rsa.Arm.CrtValues.val32_off, Nat.add_zero] at v
  rw [v, mu, VG.Proof.Rsa.Arm.CrtValues.bytes_frame h.frame sepC (by omega_arith)]

end

section
variable {P : CP} {σ s : State} {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem KS.ldrSp (h : KS P σ A live V ls s) {o : Nat} (ho : FwOk o) {t : Reg} {rest : List Instr}
    {Q : State → Prop} (k : ∀ s', Upd s s' t (fw σ.mem P o) → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrSp t o :: rest)) s Q :=
  h.bk.ldrSp ho k

end

end VG.Proof.Dsa.Arm.Prime
