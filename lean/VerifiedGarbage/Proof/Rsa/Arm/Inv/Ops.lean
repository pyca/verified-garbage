module

public import VerifiedGarbage.Impl.Rsa.Arm.Inverse
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.Arm.RowState
public import VerifiedGarbage.Proof.Rsa.Arm.Inv.Geo
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.Mac
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Reduce
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Arm.SubRow
import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasRow
import VerifiedGarbage.Proof.Bignum.Arm.CopyWords

/-! # The array operations of `inverse` on ARMv7, at `k + 1` (or `k`) words -/

@[expose] public section

/-! ## The array operations at `k + 1` (or `k`) words -/

namespace VG.Proof.Rsa.Arm.Inv
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.Keys.Inv
open VG.Proof.X25519.Arm (Rest Upd ofNat_beq_zero wp_ldr wp_str wp_dp wp_subs op2_imm dpVal toNat_shr toNat_shl toNat_mul_lt)
open VG.Proof.Bignum.Arm (add_cross_value add_word_value partials_value RowCtx row_addr row_writable)
open VG.Proof.Mont

theorem low16 (y : BitVec 32) : (y &&& ~~~((y >>> 16) <<< 16)).toNat = y.toNat % 65536 := by
  have e : y &&& ~~~((y >>> 16) <<< 16) = y &&& ((0xffff : BitVec 16).setWidth 32) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have ones : ∀ j < 16, (0xffff : BitVec 16).getLsbD j = true := by decide
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
    by_cases h : i < 16
    · simp only [ones i h, h, decide_true, Bool.not_true, Bool.false_and, Bool.not_false, Bool.and_true]
    · have h16 : 16 + (i - 16) = i := by omega
      simp only [h, decide_false, Bool.not_false, Bool.true_and, h16,
        BitVec.getLsbD_of_ge (0xffff : BitVec 16) i (by omega)]
      cases y.getLsbD i <;> simp
  rw [e]; exact VG.Proof.X25519.Arm.toNat_and_mask16 y

end VG.Proof.Rsa.Arm.Inv

namespace VG.Proof.Rsa.Arm.Inv
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.Keys.Inv
open VG.Proof.X25519.Arm
open VG.Proof.Bignum.Arm (subRow_ok selectAliasRow_ok copyWords_ok zero_ok)
open VG.Proof.Rsa.Arm.Keys (wp_ldrSlot)

/-- The words of `sel1` and `copy1`: `k`, or `k + 1`. -/
abbrev len1 (k : Nat) (low : Bool) : Nat := if low then k else k + 1

theorem cnt1_ok {s : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk s B Z W k N) {rest : List Instr}
    {Q : State → Prop} (kk : ∀ t, Upd s t .lr (BitVec.ofNat 32 (k + 1)) → WP isa (.block rest) t Q) :
    WP isa (.block (cnt1 :: rest)) s Q :=
  wp_dp (op2_imm (by decide)) fun t u => kk t (by
    have e : dpVal .add (s.gpr .r9) 1 = BitVec.ofNat 32 (k + 1) := by
      rw [dpVal, h.r9, BitVec.ofNat_add]; rfl
    exact e ▸ u)

theorem cntL_ok {s : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk s B Z W k N) (low : Bool)
    {rest : List Instr} {Q : State → Prop}
    (kk : ∀ t, Upd s t .lr (BitVec.ofNat 32 (len1 k low)) → WP isa (.block rest) t Q) :
    WP isa (.block ((if low then Instr.mov .lr (.reg .r9) else cnt1) :: rest)) s Q := by
  cases low
  · exact cnt1_ok h kk
  · exact wp_mov (op2_reg _ _) fun t u => kk t (by rw [h.r9] at u; exact u)

/-- `sub1 o a b`: `[o] = [a] - [b]`, `k + 1` words, the borrow in `r11`. -/
theorem sub1_ok {s : State} {B : BitVec 32} {Z W k N o a b : Nat} (h : Gk s B Z W k N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hoa : o ≠ a) (hob : o ≠ b) :
    WP isa (sub1 o a b) s fun t => Gk t B Z W k N ∧ Keep B W [o] [] s.mem t.mem ∧
      nk t.mem B W o (k + 1) + nk s.mem B W b (k + 1) =
        nk s.mem B W a (k + 1) + 2 ^ (32 * (k + 1)) * (t.gpr .r11).toNat ∧
      (t.gpr .r11).toNat ≤ 1 ∧ Rest opRegs s t := by
  rw [sub1, WP.seq_iff]
  refine h.ptr3_ok (o := o) (a := a) (b := b) (by omega) (by omega) (by omega) fun s3 p0 p10 p12 r3 m3 h3 => ?_
  refine cnt1_ok h3 fun s4 u4 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u5 => WP.block_nil ?_
  have hu : Gk u B Z W k N := (h3.rest (u4.rest (ws := [.lr]) (by simp))).rest (u5.rest (ws := [.r11]) (by simp))
  have mu : u.mem = s.mem := u5.mem.trans (u4.mem.trans m3)
  have restU : Rest opRegs s u :=
    (r3.mono (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp)))
  refine WP.mono (subRow_ok u (hu.subCtx ho ha hb hoa hob (L := k + 1) (by have := h.kle; omega)) (by omega)
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p0])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p10])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p12])
    (by rw [u5.other _ (by decide), u4.gpr])
    (by rw [u5.gpr]; decide)) ?_
  intro t inv
  have v := inv.value
  rw [u5.gpr, mu] at v
  refine ⟨hu.rest inv.rest, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero, mu] using inv.outside)
      (by simp only [S]; have := h.kle; omega) (by simp), ?_, inv.borrow, restU.trans (inv.rest.mono (by simp))⟩
  simpa using v

/-- `sel1 o a b low`: `[o] = [b]` if `r11` is 1, `[a]` if it is 0 (`o` may be `a` or `b`). -/
theorem sel1_ok {s : State} {B : BitVec 32} {Z W k N o a b : Nat} (low : Bool) (h : Gk s B Z W k N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (bit : (s.gpr .r11).toNat ≤ 1) :
    WP isa (sel1 o a b low) s fun t => Gk t B Z W k N ∧ Keep B W [o] [] s.mem t.mem ∧
      nk t.mem B W o (len1 k low) =
        (if (s.gpr .r11).toNat = 0 then nk s.mem B W a (len1 k low) else nk s.mem B W b (len1 k low)) ∧
      Rest opRegs s t ∧ Outside (State.addr B) (arr W o) (4 * len1 k low) s.mem t.mem := by
  rw [sel1, WP.seq_iff]
  refine h.ptr3_ok (o := o) (a := a) (b := b) (by omega) (by omega) (by omega) fun s3 p0 p10 p12 r3 m3 h3 => ?_
  refine cntL_ok h3 low fun u u4 => WP.block_nil ?_
  have hu : Gk u B Z W k N := h3.rest (u4.rest (ws := [.lr]) (by simp))
  have mu : u.mem = s.mem := u4.mem.trans m3
  have restU : Rest opRegs s u := (r3.mono (by simp)).trans (u4.rest (by simp))
  have b11 : u.gpr .r11 = s.gpr .r11 := (u4.other _ (by decide)).trans (r3.gpr _ (by decide))
  have hL : len1 k low ≤ W + 2 := by have := h.kle; simp only [len1]; split <;> omega
  have hL0 : 0 < len1 k low := by have := h.kpos; simp only [len1]; split <;> omega
  refine WP.mono (selectAliasRow_ok u (hu.selCtx ho ha hb hL) hL0
    (by rw [u4.other _ (by decide), p0]) (by rw [u4.other _ (by decide), p10])
    (by rw [u4.other _ (by decide), p12]) u4.gpr (by rw [b11]; exact bit)) ?_
  intro t inv
  have v := inv.value
  rw [b11, mu] at v
  exact ⟨hu.rest inv.rest, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero, mu] using inv.outside)
      (by simp only [S]; omega) (by simp), v, restU.trans (inv.rest.mono (by simp)), by rw [← mu]; exact inv.outside⟩

/-- `copy1 o a low`: `[o] = [a]`. -/
theorem copy1_ok {s : State} {B : BitVec 32} {Z W k N o a : Nat} (low : Bool) (h : Gk s B Z W k N)
    (ho : o < N) (ha : a < N) (hN : N ≤ 256) (hoa : o ≠ a) :
    WP isa (copy1 o a low) s fun t => Gk t B Z W k N ∧ Keep B W [o] [] s.mem t.mem ∧
      nk t.mem B W o (len1 k low) = nk s.mem B W a (len1 k low) ∧ Rest opRegs s t ∧
      Outside (State.addr B) (arr W o) (4 * len1 k low) s.mem t.mem := by
  rw [copy1, WP.seq_iff]
  refine h.ptr3_ok (o := o) (a := a) (b := a) (by omega) (by omega) (by omega) fun s3 p0 p10 p12 r3 m3 h3 => ?_
  refine cntL_ok h3 low fun s4 u4 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u5 => WP.block_nil ?_
  have hu : Gk u B Z W k N := (h3.rest (u4.rest (ws := [.lr]) (by simp))).rest (u5.rest (ws := [.r11]) (by simp))
  have mu : u.mem = s.mem := u5.mem.trans (u4.mem.trans m3)
  have restU : Rest opRegs s u :=
    (r3.mono (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp)))
  have hL : len1 k low ≤ W + 2 := by have := h.kle; simp only [len1]; split <;> omega
  have hL0 : 0 < len1 k low := by have := h.kpos; simp only [len1]; split <;> omega
  refine WP.mono (copyWords_ok u (hu.subCtx ho ha ha hoa hoa hL) hL0
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p0])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p10])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p12])
    (by rw [u5.other _ (by decide), u4.gpr])) ?_
  intro t inv
  have v := inv.value
  rw [mu] at v
  refine ⟨hu.rest inv.rest, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero, mu] using inv.outside)
      (by simp only [S]; omega) (by simp), ?_, restU.trans (inv.rest.mono (by simp)), by rw [← mu]; exact inv.outside⟩
  change val32 _ _ _ _ = _; rw [v]; split <;> rfl

/-- `[o] = 0` for `L` words from `r0 = [o]`, `lr = L`, `r3 = 0`. -/
theorem zeroAt_ok {s : State} {B : BitVec 32} {Z W k N o L : Nat} (h : Gk s B Z W k N) (ho : o < N)
    (hL : L ≤ W + 2) (hL0 : 0 < L) (p0 : s.gpr .r0 = B + BitVec.ofNat 32 (arr W o))
    (pl : s.gpr .lr = BitVec.ofNat 32 L) (z3 : s.gpr .r3 = 0) :
    WP isa zero s fun t => Gk t B Z W k N ∧ Keep B W [o] [] s.mem t.mem ∧ nk t.mem B W o L = 0 ∧
      Rest [.r0, .lr] s t := by
  refine WP.mono (zero_ok s (h.zeroCtx ho hL) hL0 p0 pl z3) fun t inv => ?_
  exact ⟨h.rest inv.rest, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using inv.outside)
    (by simp only [S]; omega) (by simp), inv.value, inv.rest⟩

theorem zero1_ok {s : State} {B : BitVec 32} {Z W k N o : Nat} (h : Gk s B Z W k N) (ho : o < N)
    (hN : N ≤ 256) :
    WP isa (zero1 o) s fun t => Gk t B Z W k N ∧ Keep B W [o] [] s.mem t.mem ∧
      nk t.mem B W o (k + 1) = 0 ∧ Rest opRegs s t := by
  rw [zero1, WP.seq_iff]
  refine h.ptr_ok (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  refine cnt1_ok h1 fun s2 u2 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u3 => WP.block_nil ?_
  have hu : Gk u B Z W k N := (h1.rest (u2.rest (ws := [.lr]) (by simp))).rest (u3.rest (ws := [.r3]) (by simp))
  have mu : u.mem = s.mem := u3.mem.trans (u2.mem.trans m1)
  refine WP.mono (zeroAt_ok hu ho (by have := h.kle; omega) (by omega)
    (by rw [u3.other _ (by decide), u2.other _ (by decide), p1]) (by rw [u3.other _ (by decide), u2.gpr])
    u3.gpr) fun t ⟨ht, kt, vt, rt⟩ => ⟨ht, mu ▸ kt, vt, ((r1.mono (by simp)).trans ((u2.rest (by simp)).trans
      (u3.rest (by simp)))).trans (rt.mono (by simp))⟩

theorem zeroW_ok {s : State} {B : BitVec 32} {Z W k N o : Nat} (h : Gk s B Z W k N) (ho : o < N)
    (hN : N ≤ 256) :
    WP isa (zeroW o) s fun t => Gk t B Z W k N ∧ Keep B W [o] [] s.mem t.mem ∧
      nk t.mem B W o W = 0 ∧ Rest opRegs s t := by
  rw [zeroW, WP.seq_iff]
  refine h.ptr_ok (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u4 => WP.block_nil ?_
  have hu : Gk u B Z W k N := ((h1.rest (u2.rest (ws := [.lr]) (by simp))).rest (u3.rest (ws := [.lr]) (by simp))).rest
    (u4.rest (ws := [.r3]) (by simp))
  have mu : u.mem = s.mem := u4.mem.trans (u3.mem.trans (u2.mem.trans m1))
  have hW : 0 < W := Nat.lt_of_lt_of_le h.kpos h.kle
  have cnt : u.gpr .lr = BitVec.ofNat 32 W := by
    rw [u4.other _ (by decide), u3.gpr, dpVal, u2.gpr, h1.r7]
    apply BitVec.eq_of_toNat_eq
    have := h.wle
    rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (2 : BitVec 32).toNat = 2 from rfl]
    simp only [S, Nat.shiftRight_eq_div_pow]
    omega
  refine WP.mono (zeroAt_ok hu ho (by omega) hW
    (by rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), p1]) cnt u4.gpr)
    fun t ⟨ht, kt, vt, rt⟩ => ⟨ht, mu ▸ kt, vt, ((r1.mono (by simp)).trans ((u2.rest (by simp)).trans
      ((u3.rest (by simp)).trans (u4.rest (by simp))))).trans (rt.mono (by simp))⟩

/-! ## Words at a byte of an array -/

/-- The word at byte `d` of array `j`. -/
abbrev aw (m : Mem) (B : BitVec 32) (W j d : Nat) : Nat := w32 m (State.addr B) (arr W j + d)

theorem Gk.arrAddr {s : State} {B : BitVec 32} {Z W k N j d : Nat} (h : Gk s B Z W k N) (hj : j < N)
    {r : Reg} {o : Nat} (hr : s.gpr r = B + BitVec.ofNat 32 (arr W j + d))
    (ho : d + o + 4 ≤ S W) :
    State.addr (s.gpr r + BitVec.ofNat 32 o) = off (State.addr B) (arr W j + d + o) := by
  have := h.arr_fit hj
  rw [hr, Offset.add_add]
  exact h.addr (by omega)

/-- The sign of a word, as a bit. -/
theorem sign_bit (x : BitVec 32) : (x >>> 31).toNat = if 2 ^ 31 ≤ x.toNat then 1 else 0 := by
  rw [toNat_shr]; have := x.isLt; split <;> omega

/-- The magnitude of a word. -/
theorem abs_word (x : BitVec 32) :
    ((x ^^^ ((x >>> 31) - ((x >>> 31) <<< 1))) - ((x >>> 31) - ((x >>> 31) <<< 1))).toNat = x.toInt.natAbs := by
  have hs := sign_bit x
  rw [BitVec.toInt_eq_toNat_cond]
  have hx := x.isLt
  by_cases h : 2 ^ 31 ≤ x.toNat
  · have e1 : x >>> 31 = 1 := by apply BitVec.eq_of_toNat_eq; rw [hs]; simp [h]
    have ns : (x ^^^ BitVec.allOnes 32) - BitVec.allOnes 32 = -x := by
      rw [BitVec.xor_allOnes, BitVec.neg_eq_not_add]
      have : BitVec.allOnes 32 = -1 := by decide
      rw [this, BitVec.sub_neg]; rfl
    rw [e1, show (1 : BitVec 32) - (1 : BitVec 32) <<< 1 = BitVec.allOnes 32 by decide, ns]
    rw [BitVec.toNat_neg]
    have : ¬ 2 * x.toNat < 2 ^ 32 := by omega
    simp only [this, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · have e1 : x >>> 31 = 0 := by apply BitVec.eq_of_toNat_eq; rw [hs]; simp [h]
    have z : (x ^^^ 0) - 0 = x := by simp
    rw [e1, show (0 : BitVec 32) - (0 : BitVec 32) <<< 1 = 0 by decide, z]
    have : 2 * x.toNat < 2 ^ 32 := by omega
    simp only [this, ↓reduceIte]
    omega

/-- A word of an array outside the frame. -/
theorem Keep.aw {B : BitVec 32} {W : Nat} {js : List Nat} {m m' : Mem} (h : Keep B W js [] m m') {j d : Nat}
    (hd : d + 4 ≤ S W) (hj : ∀ x ∈ js, x ≠ j) (fit : arr W j + S W ≤ 2 ^ 64) : aw m' B W j d = aw m B W j d := by
  have := Outs.val32 (k := 1) (d := arr W j + d) h (fun r hr => ?_) (by omega)
  · simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨x, hx, rfl⟩ | ⟨e, he, rfl⟩
  · have := arr_disj (w := W) (hj x hx); dsimp only; omega
  · simp at he

theorem val32_low (m : Mem) (base : Addr) (d k : Nat) : val32 m base d k = val32 m base d (k + 1) % 2 ^ (32 * k) := by
  rw [val32_succ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt _ _ _ _)]

end VG.Proof.Rsa.Arm.Inv
