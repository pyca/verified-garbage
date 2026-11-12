module

public import VerifiedGarbage.Proof.Rsa.Arm.KdStep
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Rsa.Arm.KdDiv
import VerifiedGarbage.Proof.Framework.Omega

/-! # The key checks' low product on ARMv7 (`KeyDiv.mulLo`): a row per word of `[x]` -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv VG.Proof.Rsa.Arm.Keys VG.Proof.Mont VG.Impl.Bignum.Arm
  VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_str wp_cmp wp_ldr op2_reg op2_imm op2_lsr op2_lsl dpVal)
open VG.Impl.Rsa.Arm.Keys (ptr copy)

/-- A row's arithmetic: `[o] = Xᵢ Y mod 2^(32 w)` before the row of word `xᵢ` at `i`, which adds
`xᵢ` times `Y`'s low `w - i` words to `[o]`'s words from `i`, gives `(Xᵢ + 2^(32 i) xᵢ) Y mod 2^(32 w)`. -/
theorem row_math {P K A Y low old new c xi Yt : Nat} (hlow : low < P)
    (hnew : new < K) (hA : A % (P * K) = low + P * old) (hYt : Yt = Y % K)
    (hrow : new + K * c = old + xi * Yt) : (A + P * xi * Y) % (P * K) = low + P * new := by
  have e1 := Nat.div_add_mod A (P * K)
  have e2 := Nat.div_add_mod Y K
  rw [hA] at e1
  rw [← hYt] at e2
  generalize A / (P * K) = q1 at e1
  generalize Y / K = y2 at e2
  have E : A + P * xi * Y = (low + P * new) + P * K * (q1 + xi * y2 + c) := by
    rw [← e1, ← e2]
    have : P * (new + K * c) = P * (old + xi * Yt) := by rw [hrow]
    grind
  have hlt : low + P * new < P * K := by
    have := Nat.mul_le_mul_left P (show new + 1 ≤ K by omega)
    rw [Nat.mul_add, Nat.mul_one] at this; omega
  rw [E, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- The product's invariant before row `i`: `[o] = Xᵢ Y mod 2^(32 w)` for `Xᵢ` the low `i`
words of `[x]` and `Y = [y]`, `4 i` at 72, and only `[o]` and 72 changed since `s0`. -/
structure MulInv (s0 v : State) (B : BitVec 32) (Z w N o x y Y i : Nat) : Prop where
  ws : Ws v B Z w N
  c16 : slot v.mem B 16 = w
  J : slot v.mem B sJ = 4 * i
  hi : i ≤ w / 2
  val : num v.mem B w o = val32 v.mem (State.addr B) (arr w x) i * Y % 2 ^ (32 * w)
  hY : num v.mem B w y = Y
  keep : Keep B w [o] [sJ] s0.mem v.mem
  rest : Rest divRegs s0 v

theorem shr2_val {i : Nat} (hi : 4 * i < 2 ^ 32) : BitVec.ofNat 32 (4 * i) >>> 2 = BitVec.ofNat 32 i := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hi]
  omega

theorem shl1_val {w : Nat} (_hw : w ≤ 1024) : BitVec.ofNat 32 w <<< 1 = BitVec.ofNat 32 (2 * w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- `mulRow o x y`: row `i`, and `4 (i + 1)` at 72 with `Z` set when it is `2 w`. -/
theorem mulRow_ok {s0 v : State} {B : BitVec 32} {Z w N o x y Y i : Nat} (I : MulInv s0 v B Z w N o x y Y i)
    (ho : o < N) (hx : x < N) (hy : y < N) (hN : N ≤ 256) (hox : o ≠ x) (hoy : o ≠ y) (hi : i < w / 2) :
    WP isa (mulRow o x y) v fun v' => MulInv s0 v' B Z w N o x y Y (i + 1) ∧ (v'.z = decide (4 * (i + 1) = 2 * w)) := by
  have h := I.ws
  have := h.wle
  have nw := h.nowrap
  have fo := h.arr_fit ho
  have fy := h.arr_fit hy
  have fx := h.arr_fit hx
  have go := h.fit64 ho
  have gy := h.fit64 hy
  have gx := h.fit64 hx
  have doy := arr_disj (w := w) hoy
  have dox := arr_disj (w := w) hox
  have hz' := h.hdr_le
  simp only [S] at fo fy fx go gy gx doy dox
  simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz'
  have tv : ∀ {o' v' : Nat}, slot v.mem B o' = v' → v.mem.readW (off (State.addr B) o') 32 = BitVec.ofNat 32 v' :=
    fun e => by rw [← e]; exact (ofNat_toNat32 _).symm
  rw [mulRow, wp_seq_blocks, WP.seq_iff]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine ptr_ok h (r := .r0) (by decide) (j := o) (by omega) fun u1 p1 r1 m1 h1 => ?_
  refine wp_ldrSlot h1 (d := sJ) (by decide) fun u2 U2 => ?_
  have h2 : Ws u2 B Z w N := h1.of_upd U2 (by decide) (by decide) (by decide)
  have v2 : u2.gpr .r2 = BitVec.ofNat 32 (4 * i) := by rw [U2.gpr, m1]; exact tv I.J
  refine wp_dp (op2_reg _ _) fun u3 U3 => ?_
  have h3 : Ws u3 B Z w N := h2.of_upd U3 (by decide) (by decide) (by decide)
  refine ptr_ok h3 (r := .r12) (by decide) (j := y) (by omega) fun u4 p4 r4 m4 h4 => ?_
  refine wp_mov (op2_lsr (by decide)) fun u5 U5 => ?_
  have h5 : Ws u5 B Z w N := h4.of_upd U5 (by decide) (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun u6 U6 => ?_
  have h6 : Ws u6 B Z w N := h5.of_upd U6 (by decide) (by decide) (by decide)
  refine ptr_ok h6 (r := .r1) (by decide) (j := x) (by omega) fun u7 p7 r7 m7 h7 => ?_
  refine wp_dp (op2_reg _ _) fun u8 U8 => ?_
  have h8 : Ws u8 B Z w N := h7.of_upd U8 (by decide) (by decide) (by decide)
  have a8 : State.addr (u8.gpr .r1 + BitVec.ofNat 32 0) = off (State.addr B) (arr w x + 4 * i) := by
    rw [U8.gpr, dpVal, p7, r7.gpr (.r2) (by decide), U6.other (.r2) (by decide), U5.other (.r2) (by decide),
      r4.gpr (.r2) (by decide), U3.other (.r2) (by decide), v2, BitVec.add_zero, add_ofNat_assoc]
    exact h.addr (by omega)
  refine wp_ldr (by decide) a8 (by rw [U8.rd, U8.wr, r7.rd, r7.wr, U6.rd, U6.wr, U5.rd, U5.wr, r4.rd, r4.wr, U3.rd,
    U3.wr, U2.rd, U2.wr, r1.rd, r1.wr]; exact h.read (by omega)) fun u9 U9 => ?_
  have h9 : Ws u9 B Z w N := h8.of_upd U9 (by decide) (by decide) (by decide)
  refine wp_mov (op2_imm (by decide)) fun u U10 => WP.block_nil ?_
  have hu : Ws u B Z w N := h9.of_upd U10 (by decide) (by decide) (by decide)
  have mu : u.mem = v.mem := by
    rw [U10.mem, U9.mem, U8.mem, m7, U6.mem, U5.mem, m4, U3.mem, U2.mem, m1]
  have restU : Rest divRegs v u :=
    ((r1.mono (by decide)).trans ((U2.rest (by decide)).trans (U3.rest (by decide)))).trans
      (((r4.mono (by decide)).trans ((U5.rest (by decide)).trans (U6.rest (by decide)))).trans
        ((r7.mono (by decide)).trans ((U8.rest (by decide)).trans ((U9.rest (by decide)).trans (U10.rest (by decide))))))
  have q0 : u.gpr .r0 = B + BitVec.ofNat 32 (arr w o + 4 * i) := by
    rw [U10.other _ (by decide), U9.other _ (by decide), U8.other _ (by decide), r7.gpr _ (by decide),
      U6.other _ (by decide), U5.other _ (by decide), r4.gpr _ (by decide), U3.gpr, dpVal, U2.other _ (by decide), p1,
      v2, add_ofNat_assoc]
  have q12 : u.gpr .r12 = B + BitVec.ofNat 32 (arr w y) := by
    rw [U10.other _ (by decide), U9.other _ (by decide), U8.other _ (by decide), r7.gpr _ (by decide),
      U6.other _ (by decide), U5.other _ (by decide), p4]
  have qlr : u.gpr .lr = BitVec.ofNat 32 (w - i) := by
    rw [U10.other _ (by decide), U9.other _ (by decide), U8.other _ (by decide), r7.gpr _ (by decide), U6.gpr, dpVal,
      U5.gpr, h5.r9, r4.gpr (.r2) (by decide), U3.other (.r2) (by decide), v2, shr2_val (by omega)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have q1 : (u.gpr .r1).toNat = w32 v.mem (State.addr B) (arr w x + 4 * i) := by
    rw [U10.other _ (by decide), U9.gpr, U8.mem, m7, U6.mem, U5.mem, m4, U3.mem, U2.mem, m1]
  have q11 : (u.gpr .r11).toNat = 0 := by rw [U10.gpr]; rfl
  have rc : RowCtx u B Z (arr w o + 4 * i) (arr w y) (w - i) :=
    ⟨h.nowrap, by omega, by omega, by omega, by rw [restU.wr]; exact h.writable⟩
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12, .lr]
    (row_ok u rc (by omega) q0 q12 qlr) (by decide)) fun v1 ⟨inv, kv⟩ => ?_
  have h81 : v1.gpr .r8 = B := by rw [kv.gpr _ (by decide), hu.r8]
  have hA : (State.addr B).toNat + Z ≤ 2 ^ 32 := by simp only [State.addr, BitVec.toNat_setWidth]; omega
  have o0 : 160 ≤ arr w o := Nat.le_add_right _ _
  have x0 : 160 ≤ arr w x := Nat.le_add_right _ _
  have y0 : 160 ≤ arr w y := Nat.le_add_right _ _
  have s16 : slot v1.mem B 16 = w := by
    simp only [slot]; rw [inv.outside.w32 (by omega) (by omega), mu]; exact I.c16
  refine kctx_ok (h.m.of (by rw [kv.wr, restU.wr])) h81 s16 h.wpos this fun v2 W2 R2 m2 => ?_
  refine wp_ldrSlot W2 (d := sJ) (by decide) fun v3 U3' => ?_
  have sJ1 : slot v1.mem B sJ = 4 * i := by
    simp only [slot]; rw [inv.outside.w32 (Or.inl (by simp only [sJ]; omega)) (by simp only [sJ]; omega), mu]
    exact I.J
  refine wp_dp (op2_imm (by decide)) fun v4 U4 => ?_
  have W4 : Ws v4 B Z w N := (W2.of_upd U3' (by decide) (by decide) (by decide)).of_upd U4 (by decide) (by decide)
    (by decide)
  have aJ : State.addr (v4.gpr .r8 + BitVec.ofNat 32 sJ) = off (State.addr B) sJ :=
    (congrArg (fun z => State.addr (z + BitVec.ofNat 32 sJ)) W4.r8).trans (h.addr (d := sJ) (by simp only [sJ]; omega))
  have wJ : InRegions v4.wr (off (State.addr B) sJ) 4 :=
    (U4.wr.trans (U3'.wr.trans (R2.wr.trans (kv.wr.trans restU.wr)))) ▸ h.write (d := sJ) (by simp only [sJ]; omega)
  refine wp_str (by decide) aJ wJ fun v5 U5' => ?_
  refine wp_mov (op2_lsl (by decide)) fun v6 U6' => ?_
  refine wp_cmp (op2_reg _ _) fun v7 F7 z7 => WP.block_nil ?_
  have r04 : v4.gpr .r0 = BitVec.ofNat 32 (4 * (i + 1)) := by
    rw [U4.gpr, dpVal, U3'.gpr, m2]
    rw [show v1.mem.readW (off (State.addr B) sJ) 32 = BitVec.ofNat 32 (4 * i) by
      rw [← sJ1]; exact (ofNat_toNat32 _).symm]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (4 : BitVec 32).toNat = 4 from rfl]; omega
  have m5 : v5.mem = v1.mem.writeW (off (State.addr B) sJ) (BitVec.ofNat 32 (4 * (i + 1))) := by
    rw [U5'.mem, r04, U4.mem, U3'.mem, m2]
  have m7 : v7.mem = v5.mem := F7.mem.trans U6'.mem
  have W7 : Ws v7 B Z w N := ((W4.of_mupd U5').of_upd U6' (by decide) (by decide) (by decide)).of (by rw [F7.gpr])
    (by rw [F7.gpr]) (by rw [F7.gpr]) F7.wr
  -- The value.
  have vv := inv.value
  rw [q1, q11, mu, Nat.add_zero] at vv
  have hlow : val32 v1.mem (State.addr B) (arr w o) i = val32 v.mem (State.addr B) (arr w o) i := by
    rw [inv.outside.val32 (Or.inl (by omega)) (by omega), mu]
  have hxv : ∀ k, k ≤ w + 2 → val32 v1.mem (State.addr B) (arr w x) k = val32 v.mem (State.addr B) (arr w x) k :=
    fun k hk => by rw [inv.outside.val32 (by omega) (by omega), mu]
  have hyv : ∀ k, k ≤ w + 2 → val32 v1.mem (State.addr B) (arr w y) k = val32 v.mem (State.addr B) (arr w y) k :=
    fun k hk => by rw [inv.outside.val32 (by omega) (by omega), mu]
  have sJw : ∀ {d k}, d + 4 * k ≤ 2 ^ 64 → (d + 4 * k ≤ sJ ∨ sJ + 4 ≤ d) →
      val32 v7.mem (State.addr B) d k = val32 v1.mem (State.addr B) d k := fun hf hd => by
    rw [m7, m5, Outside.val32 (writeW32_outside _ _ _ (by simp only [sJ]; omega)) hd hf]
  have ew : w = i + (w - i) := by omega
  have hPK : (2 : Nat) ^ (32 * w) = 2 ^ (32 * i) * 2 ^ (32 * (w - i)) := by rw [← Nat.pow_add]; congr 1; omega
  have hval := I.val
  simp only [num] at hval
  rw [ew, val32_append, ← ew, hPK] at hval
  have hYt : val32 v.mem (State.addr B) (arr w y) (w - i) = Y % 2 ^ (32 * (w - i)) := by
    have := I.hY; simp only [num] at this; rw [← this, val32_low _ _ _ (show w - i ≤ w by omega)]
  have R := row_math (P := 2 ^ (32 * i)) (K := 2 ^ (32 * (w - i))) (A := val32 v.mem (State.addr B) (arr w x) i * Y)
    (val32_lt _ _ _ _) (val32_lt _ _ _ _) hval.symm hYt vv
  have o7 : val32 v7.mem (State.addr B) (arr w o) w = val32 v1.mem (State.addr B) (arr w o) w :=
    sJw (by omega) (Or.inr (by simp only [sJ]; omega))
  refine ⟨⟨W7, ?_, ?_, by omega, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [slot]; rw [m7, m5, w32_write_ne hA (by simp only [sJ]; omega) (by omega) (by simp only [sJ]; omega)]
    exact s16
  · simp only [slot]; rw [m7, m5, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · simp only [num]
    rw [o7, ew, val32_append, ← ew, hlow, sJw (d := arr w x) (k := i + 1) (by omega)
      (Or.inr (by simp only [sJ]; omega)), hxv _ (by omega), val32_succ, hPK, Nat.add_mul]
    exact R.symm
  · simp only [num]; rw [sJw (d := arr w y) (k := w) (by omega) (Or.inr (by simp only [sJ]; omega)), hyv _ (by omega)]
    have := I.hY; simp only [num] at this; exact this
  · rw [m7, m5]
    refine (I.keep.trans ?_).trans (keep_write _ _ (by simp) (by simp only [sJ]; omega))
    rw [← mu]
    exact Keep.of_arr (d := 4 * i) inv.outside (by simp only [S]; omega) (by simp)
  · refine I.rest.trans (rest_back h W7 (ws := divRegs ++ [.r7, .r8, .r9]) ?_)
    exact ((restU.mono (by decide)).trans (kv.mono (by decide))).trans ((R2.mono (by decide)).trans
      (((U3'.rest (by decide)).trans (U4.rest (by decide))).trans ((U5'.rest _).trans ((U6'.rest (by decide)).trans
        (F7.rest _)))))
  · rw [z7, U6'.other _ (by decide), U5'.gpr, r04, U6'.gpr, U5'.gpr, U4.other _ (by decide), U3'.other _ (by decide),
      W2.r9, shl1_val this]
    by_cases e : 4 * (i + 1) = 2 * w
    · rw [e]; simp
    · have : BitVec.ofNat 32 (4 * (i + 1)) - BitVec.ofNat 32 (2 * w) ≠ 0 := fun h0 => by
        have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
        have : (0 : BitVec 32).toNat = 0 := rfl
        omega
      rw [show (BitVec.ofNat 32 (4 * (i + 1)) - BitVec.ofNat 32 (2 * w) == 0) = false from
        beq_eq_false_iff_ne.mpr this]
      simp [e]

/-- `mulLo`'s start: `[o] := 0`, then `0` at 72. -/
theorem mulInit_ok {s : State} {B : BitVec 32} {Z w N o y : Nat} (x : Nat) (h : Ws s B Z w N) (ho : o < N)
    (hy : y < N) (hN : N ≤ 256) (hoy : o ≠ y) (ho0 : o ≠ 0) (h16 : slot s.mem B 16 = w) (hw2 : 2 ≤ w)
    (hz : num s.mem B w 0 = 0) :
    WP isa (copy o 0) s fun v1 => Ws v1 B Z w N ∧ WP isa (.block [.mov .r0 (.imm 0), .str .r0 .r8 sJ]) v1
      fun v => MulInv s v B Z w N o x y (num s.mem B w y) 0 := by
  have := h.wle
  have nw := h.nowrap
  have hz' := h.hdr_le
  simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz'
  refine WP.mono (copy_ok h ho (by omega) hN ho0) fun v1 ⟨W1, K1, C1, R1, _⟩ => ⟨W1, ?_⟩
  refine wp_mov (op2_imm (by decide)) fun v2 U2 => ?_
  have W2 : Ws v2 B Z w N := W1.of_upd U2 (by decide) (by decide) (by decide)
  have aJ : State.addr (v2.gpr .r8 + BitVec.ofNat 32 sJ) = off (State.addr B) sJ :=
    (congrArg (fun z => State.addr (z + BitVec.ofNat 32 sJ)) W2.r8).trans (h.addr (d := sJ) (by simp only [sJ]; omega))
  have wJ : InRegions v2.wr (off (State.addr B) sJ) 4 :=
    (U2.wr.trans (R1.wr)) ▸ h.write (d := sJ) (by simp only [sJ]; omega)
  refine wp_str (by decide) aJ wJ fun v3 U3 => WP.block_nil ?_
  have W3 : Ws v3 B Z w N := W2.of_mupd U3
  have m3 : v3.mem = v1.mem.writeW (off (State.addr B) sJ) (0 : BitVec 32) := by rw [U3.mem, U2.gpr, U2.mem]
  have K3 : Keep B w [o] [sJ] s.mem v3.mem := by
    rw [m3]; exact K1.mono.trans (keep_write _ _ (by simp) (by simp only [sJ]; omega))
  refine ⟨W3, ?_, ?_, by omega, ?_, K3.num (by simpa using hoy) (by decide) (h.fit64 hy), K3,
    (R1.mono (by decide)).trans ((U2.rest (by decide)).trans (U3.rest _))⟩
  · rw [K3.slot (by decide) (by decide)]; exact h16
  · simp only [slot]; rw [m3, w32_write_self]; rfl
  · rw [show num v3.mem B w o = num v1.mem B w o by
      simp only [num]; rw [m3, Outside.val32 (writeW32_outside _ _ _ (by simp only [sJ]; omega))
        (Or.inr (by have : 160 ≤ arr w o := Nat.le_add_right _ _; simp only [sJ]; omega)) (h.fit64 ho |> fun g => by
          simp only [S] at g; omega)], C1, hz]
    simp only [val32, Nat.zero_mul, Nat.zero_mod]

/-- `mulLo`'s rows, from the invariant before row 0. -/
theorem mulLoop_ok {s0 v : State} {B : BitVec 32} {Z w N o x y Y : Nat} (I0 : MulInv s0 v B Z w N o x y Y 0)
    (ho : o < N) (hx : x < N) (hy : y < N) (hN : N ≤ 256) (hox : o ≠ x) (hoy : o ≠ y) (hw : w % 2 = 0)
    (hw2 : 2 ≤ w) {X : Nat} (hX : num s0.mem B w x = X) (hXl : X < 2 ^ (32 * (w / 2))) :
    WP isa (.loop (mulRow o x y) .ne) v fun v' => Ws v' B Z w N ∧ num v'.mem B w o = X * Y % 2 ^ (32 * w) ∧
      Keep B w [o] [sJ] s0.mem v'.mem ∧ Rest divRegs s0 v' := by
  have gx := I0.ws.fit64 hx
  refine WP.loop (M := isa) (fun n v => ∃ i, n = w / 2 - i ∧ i < w / 2 ∧ MulInv s0 v B Z w N o x y Y i) ?_
    (w / 2) v ⟨0, by omega, by omega, I0⟩
  rintro n v ⟨i, rfl, hi, I⟩
  refine WP.mono (mulRow_ok I ho hx hy hN hox hoy hi) fun v' ⟨I', z'⟩ => ?_
  by_cases e : i + 1 = w / 2
  · left
    refine ⟨?_, ?_⟩
    · change some (!v'.z) = some false
      rw [z']; simp only [show 4 * (i + 1) = 2 * w by omega, decide_true, Bool.not_true]
    · refine ⟨I'.ws, ?_, I'.keep, I'.rest⟩
      rw [I'.val, e, val32_low _ _ _ (show w / 2 ≤ w by omega)]
      have := I'.keep.num (j := x) (by simpa using hox) (by decide) gx
      simp only [num] at this hX ⊢
      rw [this, hX, Nat.mod_eq_of_lt hXl]
  · right
    refine ⟨?_, w / 2 - (i + 1), by omega, i + 1, rfl, by omega, I'⟩
    change some (!v'.z) = some true
    rw [z']; simp only [show ¬4 * (i + 1) = 2 * w by omega, decide_false, Bool.not_false]

/-- `mulLo o x y`: `[o] := X Y mod 2^(32 w)` for `X = [x]` of `w / 2` words and `Y = [y]`,
`w` even. -/
theorem mulLo_ok {s : State} {B : BitVec 32} {Z w N o x y : Nat} (h : Ws s B Z w N) (ho : o < N) (hx : x < N)
    (hy : y < N) (hN : N ≤ 256) (hox : o ≠ x) (hoy : o ≠ y) (ho0 : o ≠ 0)
    (h16 : slot s.mem B 16 = w) (hw : w % 2 = 0) (hw2 : 2 ≤ w) {X Y : Nat} (hX : num s.mem B w x = X)
    (hXl : X < 2 ^ (32 * (w / 2))) (hY : num s.mem B w y = Y) (hz : num s.mem B w 0 = 0) :
    WP isa (mulLo o x y) s fun v => Ws v B Z w N ∧ num v.mem B w o = X * Y % 2 ^ (32 * w) ∧
      Keep B w [o] [sJ] s.mem v.mem ∧ Rest divRegs s v := by
  rw [mulLo]
  simp only [VG.Impl.Rsa.Arm.Keys.seqs]
  rw [WP.seq_iff]
  refine WP.mono (mulInit_ok x h ho hy hN hoy ho0 h16 hw2 hz) fun v1 ⟨_, h1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono h1 fun v I0 => ?_
  rw [hY] at I0
  exact mulLoop_ok I0 ho hx hy hN hox hoy hw hw2 hX hXl

end VG.Proof.Rsa.Arm.KeyDiv
