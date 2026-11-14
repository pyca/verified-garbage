module
-- separate module: the proof of Appendix C.2's body is split in a chain of modules, so that a change rebuilds only the modules after it
public import VerifiedGarbage.Proof.Rsa.Arm.RdGcd

import VerifiedGarbage.Proof.Rsa.Arm.KdMul
import VerifiedGarbage.Proof.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.Arm.KdDivCT
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops2
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Slots
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ctx
import VerifiedGarbage.Proof.Framework.Arm.Keep
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Views

/-! # `vg_rsa_recover_primes_det` on ARMv7: the products by rows

`rowProd_vp`: `[o] := y [x]` modulo `2^(32 W)` for `y` the narrow array `2 Y` (the
low `w` words of the wide `Y`), a row per word of `y`: row `i` adds `yᵢ [x]` to
`[o]`'s `W - i` words from word `i`, its carry dropped (`rows_mod`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.RecoverDet
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Recover
open VG.Impl.Rsa.Arm.Keys hiding aT1 aT2 aT3 aT4
open VG.Proof.X25519.Arm
open VG.Impl.Rsa.Arm.RecoverDet
open VG.Impl.Rsa.Arm.Recover (nArr aW)
open VG.Proof.Bignum.Arm (row_ok RowCtx)
open VG.Proof.Rsa.Arm.KeyDiv (ofNat_toNat32 add_ofNat_assoc shr2_val)

/-- A row's arithmetic: `[o] = Yᵢ X mod p q` (for `p = 2^(32 i)`, `q = 2^(32 (W - i))`), split
at word `i` into `low` and `old`; the row adds `yᵢ Xlo` (`Xlo = X mod q`) to `old`, its carry
`c` dropped: `[o] = (Yᵢ + p yᵢ) X mod p q`. -/
theorem rows_mod {p q O low old new c Yi yi X Xlo Xhi : Nat} (hlow : low < p) (hO : low + p * old = O)
    (hOv : O = Yi * X % (p * q)) (hnew : new < q) (hrow : new + q * c = old + yi * Xlo)
    (hX : Xlo + q * Xhi = X) : low + p * new = (Yi + p * yi) * X % (p * q) := by
  have lt : low + p * new < p * q := by
    have : p * new + p ≤ p * q := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hnew
    omega_using [hlow, this]
  have e1 : p * (new + q * c) = p * (old + yi * Xlo) := by rw [hrow]
  rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, ← Nat.mul_assoc] at e1
  rw [← Nat.mod_eq_of_lt lt, ← Nat.add_mul_mod_self_left (low + p * new) (p * q) c]
  have e2 : low + p * new + p * q * c = Yi * X % (p * q) + p * yi * Xlo := by omega_using [hO, hOv, e1]
  have e3 : (Yi + p * yi) * X = Yi * X + p * yi * Xlo + p * q * (yi * Xhi) := by
    rw [Nat.add_mul, ← hX, Nat.mul_add (p * yi), Nat.mul_add Yi,
      show p * yi * (q * Xhi) = p * q * (yi * Xhi) by rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_left_comm yi]]
    omega_using []
  rw [e2, e3, Nat.add_mul_mod_self_left, Nat.add_mod (Yi * X), Nat.add_mod (Yi * X % (p * q)), Nat.mod_mod]

theorem val32_lo (mem : Mem) (base : Addr) (d : Nat) {k n : Nat} (h : k ≤ n) :
    val32 mem base d k = val32 mem base d n % 2 ^ (32 * k) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [val32_append, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt _ _ _ _)]

/-- What a product by rows needs of its arrays: the narrow `2 Y` live, `x` wide and live, `o`
wide, apart from `x` and `Y`, and no narrow array in it. -/
structure RCfg (o x Y : Nat) (L LW : List Nat) : Prop where
  hy : 2 * Y ∈ L
  hx : x ∈ LW
  ho : o < 22
  hY : Y < 22
  hox : o ≠ x
  hoY : o ≠ Y
  hL : ∀ j ∈ L, j / 2 ≠ o

section
variable {P : RP}

/-- Before row `i`: `[o] = (y mod 2^(32 i)) [x]` modulo `2^(32 W)`, and `4 i` at `sK`. -/
abbrev RS (P : RP) (σ : State) (A : Nat → Nat) (L : List Nat) (AW : Nat → Nat) (LW : List Nat)
    (V : Nat → Nat) (LS : List Nat) (o x Y i : Nat) (s : State) : Prop :=
  KS P σ A L (upd AW o (A (2 * Y) % 2 ^ (32 * i) * AW x % 2 ^ (32 * P.W))) (o :: LW) (upd V sK (4 * i))
    (sK :: LS) s ∧ Ws s P.B P.Z P.W 22

/-- What a row's count block does: `r1 := 4 R`, from the slots of the stage (`LS` but `sK`, and `w` at 16). -/
abbrev CntOk (P : RP) (V : Nat → Nat) (LS : List Nat) (cnt : List Instr) (R : Nat) : Prop :=
  ∀ t, Ws t P.B P.Z P.W 22 → t.mem.readW (off (State.addr P.B) 16) 32 = BitVec.ofNat 32 P.w →
    (∀ d ∈ LS, d ≠ sK → slot t.mem P.B d = V d) → ∀ {rest : List Instr} {Q : State → Prop},
    (∀ u, Rest [.r1] t u → u.mem = t.mem → u.gpr .r1 = BitVec.ofNat 32 (4 * R) → WP isa (.block rest) u Q) →
    WP isa (.block (cnt ++ rest)) t Q

theorem pRowG_ok {o x Y : Nat} {L LW LS : List Nat} (c : RCfg o x Y L LW) {σ s : State} {A AW V : Nat → Nat}
    {cnt : List Instr} {R : Nat} (hR : R ≤ P.w) (hc : CntOk P V LS cnt R)
    {i : Nat} (hi : i < R) (h : RS P σ A L AW LW V LS o x Y i s) :
    WP isa (pRowG o x Y cnt) s fun t => RS P σ A L AW LW V LS o x Y (i + 1) t ∧ t.z = decide (i + 1 = R) := by
  obtain ⟨h, hv⟩ := h
  have sz := h.sizes
  have wl := sz.wle
  have Wl := sz.Wle
  have eW : P.W = 2 * P.w + 2 := rfl
  have nw := hv.nowrap
  have fo := fitZ_W sz c.ho
  have fx := fitZ_W sz (h.liveW_lt x (List.mem_cons_of_mem _ c.hx))
  have fY := fitZ_W sz c.hY
  have Z64 := Z_64 sz
  have dox := arr_disj (w := P.W) c.hox
  have doY := arr_disj (w := P.W) c.hoY
  simp only [S] at fo fx fY dox doY
  have hS : S P.W = 4 * (P.W + 2) := rfl
  have hxL : x ∈ o :: LW := List.mem_cons_of_mem _ c.hx
  -- The first block: `[o]`'s address and `4 i`.
  rw [pRowG, WP.seq_iff, pRowA]
  refine ptr_ok hv (r := .r0) (by decide) (j := o) (by have := c.ho; omega_using [this]) fun s1 p1 r1 m1 hv1 => ?_
  have h1 := h.of_rest r1 m1 (by decide)
  refine h1.ldrSlot hv1 (d := sK) (List.mem_cons_self ..) (r := .r2) (by decide) fun s2 h2 hv2 U2 =>
    WP.block_nil ?_
  rw [upd_self] at U2
  -- The second: the row's pointers, count and word of `y`.
  rw [pRowBG, WP.seq_iff]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_dp (op2_reg _ _) fun s3 U3 => ?_
  have hv3 : Ws s3 P.B P.Z P.W 22 := hv2.of_upd U3 (by decide) (by decide) (by decide)
  refine ptr_ok hv3 (r := .r12) (by decide) (j := x) (by have := h.liveW_lt x hxL; omega_using [this])
    fun s4 p4 r4 m4 hv4 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s5 U5 => ?_
  have hv5 : Ws s5 P.B P.Z P.W 22 := hv4.of_upd U5 (by decide) (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s6 U6 => ?_
  have hv6 : Ws s6 P.B P.Z P.W 22 := hv5.of_upd U6 (by decide) (by decide) (by decide)
  refine ptr_ok hv6 (r := .r1) (by decide) (j := Y) (by have := c.hY; omega_using [this]) fun s7 p7 r7 m7 hv7 => ?_
  refine wp_dp (op2_reg _ _) fun s8 U8 => ?_
  have hv8 : Ws s8 P.B P.Z P.W 22 := hv7.of_upd U8 (by decide) (by decide) (by decide)
  have v2 : s2.gpr .r2 = BitVec.ofNat 32 (4 * i) := U2.gpr
  have a8 : State.addr (s8.gpr .r1 + BitVec.ofNat 32 0) = off (State.addr P.B) (arr P.W Y + 4 * i) := by
    rw [U8.gpr, dpVal, p7, r7.gpr (.r2) (by decide), U6.other (.r2) (by decide), U5.other (.r2) (by decide),
      r4.gpr (.r2) (by decide), U3.other (.r2) (by decide), v2, BitVec.add_zero, add_ofNat_assoc]
    exact hv.addr (by omega_using [hR, hi, eW, fY])
  have m8 : s8.mem = s.mem := by
    rw [U8.mem, m7, U6.mem, U5.mem, m4, U3.mem, U2.mem, m1]
  refine wp_ldr (by decide) a8 (by rw [U8.rd, U8.wr, r7.rd, r7.wr, U6.rd, U6.wr, U5.rd, U5.wr, r4.rd, r4.wr,
    U3.rd, U3.wr, U2.rd, U2.wr, r1.rd, r1.wr]; exact hv.read (by omega_using [hR, hi, eW, fY])) fun s9 U9 => ?_
  have hv9 : Ws s9 P.B P.Z P.W 22 := hv8.of_upd U9 (by decide) (by decide) (by decide)
  refine wp_mov (op2_imm (by decide)) fun u U10 => WP.block_nil ?_
  have hu : Ws u P.B P.Z P.W 22 := hv9.of_upd U10 (by decide) (by decide) (by decide)
  have mu : u.mem = s.mem := by rw [U10.mem, U9.mem, m8]
  have restU : Rest [.r0, .r1, .r2, .r3, .r11, .r12, .lr] s u :=
    ((r1.mono (by decide)).trans ((U2.rest (by decide)).trans (U3.rest (by decide)))).trans
      (((r4.mono (by decide)).trans ((U5.rest (by decide)).trans (U6.rest (by decide)))).trans
        ((r7.mono (by decide)).trans ((U8.rest (by decide)).trans ((U9.rest (by decide)).trans (U10.rest (by decide))))))
  have hu' : KS P σ A L (upd AW o (A (2 * Y) % 2 ^ (32 * i) * AW x % 2 ^ (32 * P.W))) (o :: LW)
      (upd V sK (4 * i)) (sK :: LS) u := h.of_rest restU mu (by decide)
  have q0 : u.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W o + 4 * i) := by
    rw [U10.other _ (by decide), U9.other _ (by decide), U8.other _ (by decide), r7.gpr _ (by decide),
      U6.other _ (by decide), U5.other _ (by decide), r4.gpr _ (by decide), U3.gpr, dpVal, U2.other _ (by decide), p1,
      v2, add_ofNat_assoc]
  have q12 : u.gpr .r12 = P.B + BitVec.ofNat 32 (arr P.W x) := by
    rw [U10.other _ (by decide), U9.other _ (by decide), U8.other _ (by decide), r7.gpr _ (by decide),
      U6.other _ (by decide), U5.other _ (by decide), p4]
  have qlr : u.gpr .lr = BitVec.ofNat 32 (P.W - i) := by
    rw [U10.other _ (by decide), U9.other _ (by decide), U8.other _ (by decide), r7.gpr _ (by decide), U6.gpr, dpVal,
      U5.gpr, U5.other .r9 (by decide), r4.gpr .r9 (by decide), U3.other .r9 (by decide), U2.other .r9 (by decide),
      r1.gpr .r9 (by decide), hv.r9, r4.gpr .r2 (by decide), U3.other .r2 (by decide), v2, shr2_val (by omega_using [hR, hi, wl]),
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [hR, hi, wl]) (by omega_using [hR, hi, eW])]
  have q1 : (u.gpr .r1).toNat = w32 s.mem (State.addr P.B) (arr P.W Y + 4 * i) := by
    rw [U10.other _ (by decide), U9.gpr, m8]
  have q11 : (u.gpr .r11).toNat = 0 := by rw [U10.gpr]; rfl
  have rc : RowCtx u P.B P.Z (arr P.W o + 4 * i) (arr P.W x) (P.W - i) :=
    ⟨nw, by omega_using [hR, hi, eW, fo], by omega_using [fx], by omega_using [dox], hu.writable⟩
  -- The row.
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12, .lr]
    (row_ok u rc (by omega_using [hR, hi, eW]) q0 q12 qlr) (by decide)) fun v1 ⟨inv, kv⟩ => ?_
  have k1 : Keep P.B P.W [o] [] u.mem v1.mem :=
    Keep.of_arr (d := 4 * i) inv.outside (by simp only [S]; omega_using [hR, hi, eW]) (by simp)
  -- Its value.
  have Wsplit : ∀ (m : Mem) (d : Nat), val32 m (State.addr P.B) d P.W =
      val32 m (State.addr P.B) d i + 2 ^ (32 * i) * val32 m (State.addr P.B) (d + 4 * i) (P.W - i) := by
    intro m d
    have := val32_append m (State.addr P.B) d i (P.W - i)
    rwa [Nat.add_sub_cancel' (by omega_using [hR, hi, eW])] at this
  have Xsplit : ∀ (m : Mem) (d : Nat), val32 m (State.addr P.B) d P.W =
      val32 m (State.addr P.B) d (P.W - i) + 2 ^ (32 * (P.W - i)) *
        val32 m (State.addr P.B) (d + 4 * (P.W - i)) i := by
    intro m d
    have := val32_append m (State.addr P.B) d (P.W - i) i
    rwa [Nat.sub_add_cancel (by omega_using [hR, hi, eW])] at this
  have hov := h.arrsW o (List.mem_cons_self ..)
  rw [upd_self] at hov
  have hxv := h.arrsW x hxL
  rw [upd_ne _ _ (Ne.symm c.hox)] at hxv
  have hyv := h.arrs (2 * Y) c.hy
  change val32 s.mem (State.addr P.B) (arr P.W o) P.W = _ at hov
  change val32 s.mem (State.addr P.B) (arr P.W x) P.W = _ at hxv
  change val32 s.mem (State.addr P.B) (arr P.w (2 * Y)) P.w = _ at hyv
  have vv := inv.value
  rw [q1, q11, mu, Nat.add_zero] at vv
  have hlow : val32 v1.mem (State.addr P.B) (arr P.W o) i = val32 s.mem (State.addr P.B) (arr P.W o) i := by
    rw [inv.outside.val32 (Or.inl (by omega_using [])) (by omega_using [hR, hi, eW, nw, fo]), mu]
  have aY : arr P.W Y = arr P.w (2 * Y) := VG.Proof.Rsa.Arm.Recover.arr_W P.w Y
  have Ylo : A (2 * Y) % 2 ^ (32 * (i + 1)) =
      A (2 * Y) % 2 ^ (32 * i) + 2 ^ (32 * i) * w32 s.mem (State.addr P.B) (arr P.W Y + 4 * i) := by
    rw [← hyv, ← val32_lo _ _ _ (show i + 1 ≤ P.w by omega_using [hR, hi]), ← val32_lo _ _ _ (show i ≤ P.w by omega_using [hR, hi]), val32_succ,
      aY]
  have pq : (2 : Nat) ^ (32 * i) * 2 ^ (32 * (P.W - i)) = 2 ^ (32 * P.W) := by
    rw [← Nat.pow_add]; congr 1; omega_using [hR, hi, wl, Wl, eW, nw, fo, fx, fY, Z64, dox, doY, aY]
  have eV : num v1.mem P.B P.W o = A (2 * Y) % 2 ^ (32 * (i + 1)) * AW x % 2 ^ (32 * P.W) := by
    change val32 v1.mem (State.addr P.B) (arr P.W o) P.W = _
    rw [Wsplit, hlow, Ylo, ← pq]
    rw [Wsplit, ← pq] at hov
    rw [Xsplit] at hxv
    exact rows_mod (val32_lt _ _ _ _) rfl hov (val32_lt _ _ _ _) vv hxv
  have r81 : v1.gpr .r8 = P.B := by rw [kv.gpr _ (by decide), hu'.r8]
  have K1 := hu'.write_W k1 c.ho (by simp) r81 kv.sp kv.rd kv.wr eV c.hL (by simp)
  -- The context, the next offset and whether it is the last row.
  refine WP.block_append (WP.mono (ctxW_ok K1.bs K1.r8 K1.cnt) fun v2 ⟨hv2', rr2, mm2⟩ => ?_)
  have K2 := K1.of_rest rr2 mm2 (by decide)
  refine K2.ldrSlot hv2' (d := sK) (List.mem_cons_self ..) (r := .r0) (by decide) fun v3 K3 hv3' U3' => ?_
  rw [upd_self] at U3'
  refine wp_dp (op2_imm (by decide)) fun v4 U4' => ?_
  obtain ⟨K4, hv4'⟩ := K3.reg hv3' (U4'.rest (ws := [.r0]) (by simp)) U4'.mem
  have r04 : v4.gpr .r0 = BitVec.ofNat 32 (4 * (i + 1)) := by
    rw [U4'.gpr, dpVal, U3'.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (4 : BitVec 32).toNat = 4 from rfl]; omega_using []
  refine K4.strSlot hv4' (d := sK) (r := .r0) (by decide) fun v5 K5 hv5' g5 _ => ?_
  refine hc v5 hv5' K5.cnt (fun d hd hdk => by
      rw [K5.sl d (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd))]; simp only [upd, hdk, ↓reduceIte])
    fun v7 U7' m7 c1 => ?_
  obtain ⟨K7, hv7'⟩ := K5.reg hv5' U7' m7
  refine wp_cmp (op2_reg _ _) fun v8 F8 z8 => WP.block_nil ?_
  obtain ⟨K8, hv8'⟩ := K7.reg hv7' (F8.rest []) F8.mem
  rw [r04] at K8
  refine ⟨⟨K8.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ hj, ?_⟩)
    (fun d hd => ⟨List.mem_cons_of_mem _ hd, ?_⟩), hv8'⟩, ?_⟩
  · simp only [upd]; split <;> rfl
  · simp only [upd]; split
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hR, hi, wl])]
    · rfl
  · have c0 : v7.gpr .r0 = BitVec.ofNat 32 (4 * (i + 1)) := by
      rw [U7'.gpr _ (by decide), g5, r04]
    rw [z8, c0, c1]
    by_cases e : i + 1 = R
    · rw [e]; simp
    · have : BitVec.ofNat 32 (4 * (i + 1)) - BitVec.ofNat 32 (4 * R) ≠ 0 := fun h0 => by
        have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
        have : (0 : BitVec 32).toNat = 0 := rfl
        omega_arith
      rw [show (BitVec.ofNat 32 (4 * (i + 1)) - BitVec.ofNat 32 (4 * R) == 0) = false from
        beq_eq_false_iff_ne.mpr this]
      exact (decide_eq_false e).symm

/-- `cntW`: `4 w`, from the count at 16. -/
theorem cntW_ok {V : Nat → Nat} {LS : List Nat} : CntOk P V LS cntW P.w := by
  intro t hv c16 _ rest Q k
  have wl := hv.wle
  refine wp_ldrSlot hv (d := 16) (by decide) fun v6 U6' => ?_
  refine wp_mov (op2_lsl (by decide)) fun v7 U7' => ?_
  refine k v7 ((U6'.rest (ws := [.r1]) (by simp)).trans (U7'.rest (ws := [.r1]) (by simp))) (by rw [U7'.mem, U6'.mem]) ?_
  rw [U7'.gpr, U6'.gpr, c16]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : P.w ≤ 1024 := by simp only [RP.W] at wl; omega_using [wl]
  omega_using []

theorem pRow_ok {o x Y : Nat} {L LW LS : List Nat} (c : RCfg o x Y L LW) {σ s : State} {A AW V : Nat → Nat}
    {i : Nat} (hi : i < P.w) (h : RS P σ A L AW LW V LS o x Y i s) :
    WP isa (pRow o x Y) s fun t => RS P σ A L AW LW V LS o x Y (i + 1) t ∧ t.z = decide (i + 1 = P.w) :=
  pRowG_ok c (Nat.le_refl _) cntW_ok hi h

/-- After `R` rows: `[o] = (y mod 2^(32 R)) [x]` modulo `2^(32 W)`, and `4 R` at `sK`. -/
def RIG (P : RP) (R y x o : Nat) (A : State → Nat → Nat) (L : List Nat) (AW : State → Nat → Nat) (LW : List Nat)
    (V : State → Nat → Nat) (LS : List Nat) (σ s : State) : Prop :=
  KS P σ (A σ) L (upd (AW σ) o (A σ y % 2 ^ (32 * R) * AW σ x % 2 ^ (32 * P.W))) (o :: LW)
    (upd (V σ) sK (4 * R)) (sK :: LS) s ∧ Ws s P.B P.Z P.w nArr

/-- After the rows: `[o] = (y mod 2^(32 w)) [x]` modulo `2^(32 W)`, and `4 w` at `sK`. -/
abbrev RI (P : RP) (y x o : Nat) (A : State → Nat → Nat) (L : List Nat) (AW : State → Nat → Nat) (LW : List Nat)
    (V : State → Nat → Nat) (LS : List Nat) (σ s : State) : Prop :=
  RIG P P.w y x o A L AW LW V LS σ s

/-- A product's steps (`ProdF`) are the model's: after `k`, `(y mod 2^k) x` modulo `2^(32 W)`. -/
theorem pr_rows {g : Nat × Nat × Nat → Nat × Nat × Nat} (hg : ProdF P g) {y x : Nat} (hx : x < 2 ^ (32 * P.W))
    (k : Nat) : (pr g y x k).2.2 = y % 2 ^ k * x % 2 ^ (32 * P.W) := by
  have e : g = VG.Proof.Rsa.RecoverDet.prodStep (32 * P.W) := funext fun ⟨a, b, c⟩ => hg a b c
  simp only [pr, e, VG.Proof.Rsa.RecoverDet.prod_iter _ _ _ hx k]

/-- A row's first block: `[o]`'s address in `r0` and `4 i` in `r2`. -/
theorem pRowA_regs {o x Y : Nat} {L LW LS : List Nat} (c : RCfg o x Y L LW) {σ s : State} {A AW V : Nat → Nat}
    {i : Nat} (h : RS P σ A L AW LW V LS o x Y i s) :
    WP isa (.block (pRowA o)) s fun t => Ws t P.B P.Z P.W 22 ∧
      t.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W o) ∧ t.gpr .r2 = BitVec.ofNat 32 (4 * i) := by
  obtain ⟨h, hv⟩ := h
  rw [pRowA]
  refine ptr_ok hv (r := .r0) (by decide) (j := o) (by have := c.ho; omega_using [this]) fun s1 p1 r1 m1 hv1 => ?_
  have h1 := h.of_rest r1 m1 (by decide)
  refine h1.ldrSlot hv1 (d := sK) (List.mem_cons_self ..) (r := .r2) (by decide) fun s2 _ hv2 U2 =>
    WP.block_nil ⟨hv2, by rw [U2.other _ (by decide), p1], by rw [U2.gpr, upd_self]⟩

/-- `R` rows: `[o] := (y mod 2^(32 R)) [x]` modulo `2^(32 W)`, and `4 R` at `sK`. -/
theorem rowProdG_vp {o x Y : Nat} {L LW LS : List Nat} (c : RCfg o x Y L LW) (hz : wZ ∈ LW) (hoz : o ≠ wZ)
    {E : State → Prop} {A AW V : State → Nat → Nat} (z0 : ∀ σ, E σ → AW σ wZ = 0)
    {cnt : List Instr} {R : Nat} (pos : 0 < R) (hR : R ≤ P.w) (hc : ∀ σ, E σ → CntOk P (V σ) LS cnt R)
    (certC : DCert (copy o wZ)) (certA : DCert (.block (pRowA o))) (certB : RowCert (pRowBG x Y cnt)) :
    VP (Dk P E A L AW LW V LS P.w nArr) (rowProdG o x Y cnt)
      (fun σ s => E σ ∧ RIG P R (2 * Y) x o A L AW LW V LS σ s) := by
  simp only [rowProdG, seqs]
  refine VP.seq (G := Dk P E A L AW LW V LS P.W 22) (VP.dctx toW_taint (fun _ _ h => h.2.2)
    fun σ s ⟨e, h, hv⟩ => ?_) ?_
  · rw [← List.append_nil toW]
    exact h.toW hv fun t ht hvt _ => WP.block_nil ⟨e, ht, hvt⟩
  refine VP.seq (G := Dk P E A L (fun σ => upd (AW σ) o 0) (o :: LW) V LS P.W 22)
    (VP.dctx certC (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_) ?_
  · refine WP.mono (h.copy_W hv (o := o) (a := wZ) c.ho hz hoz c.hL) fun t ⟨ht, hvt, _⟩ => ⟨e, ?_, hvt⟩
    rwa [z0 σ e] at ht
  refine VP.seq (G := fun σ s => E σ ∧ RS P σ (A σ) L (AW σ) LW (V σ) LS o x Y 0 s)
    (VP.dctx rowsInit_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_) ?_
  · rw [rowsInit]
    refine wp_mov (op2_imm (by decide)) fun s1 U1 => ?_
    obtain ⟨h1, hv1⟩ := h.reg hv (U1.rest (ws := [.r0]) (by simp)) U1.mem
    refine h1.strSlot hv1 (d := sK) (r := .r0) (by decide) fun t ht hvt _ _ => WP.block_nil ⟨e, ?_, hvt⟩
    rw [U1.gpr] at ht
    refine ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
    simp only [upd]; split
    · simp only [Nat.mul_zero, Nat.pow_zero, Nat.mod_one, Nat.zero_mul, Nat.zero_mod]
    · rfl
  refine VP.seq (VP.count (E := E) (I := fun k σ s => RS P σ (A σ) L (AW σ) LW (V σ) LS o x Y k s) pos
    fun k hk => ?_) ?_
  · refine VP.seq (G := fun σ t => (Ws t P.B P.Z P.W 22 ∧ t.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W o) ∧
        t.gpr .r2 = BitVec.ofNat 32 (4 * k)) ∧
        WP isa (pRowBG x Y cnt) t fun u => (E σ ∧ RS P σ (A σ) L (AW σ) LW (V σ) LS o x Y (k + 1) u) ∧
          u.z = decide (R - (k + 1) = 0))
      (VP.dctx certA (fun _ _ h => h.2.2) fun σ s ⟨e, h⟩ => ?_)
      (VP.taint _ certB (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ t h => h.2)
    · have hw := pRowG_ok c hR (hc σ e) hk h
      rw [pRowG, WP.seq_iff] at hw
      refine VG.Proof.Rsa.Arm.KeyDiv.wp_and (pRowA_regs c h) (WP.mono hw fun t ht => WP.mono ht
        fun u ⟨hu, z⟩ => ⟨⟨e, hu⟩, ?_⟩)
      rw [z]; congr 1; exact propext ⟨fun e => by omega_using [e], fun e => by omega_using [hk, e]⟩
    · obtain ⟨⟨w₁, a₁, b₁⟩, _⟩ := h₁
      obtain ⟨⟨w₂, a₂, b₂⟩, _⟩ := h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [w₁.r7, w₂.r7]
      · rw [w₁.r8, w₂.r8]
      · rw [w₁.r9, w₂.r9]
  refine VP.dctx toN_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_
  rw [← List.append_nil toN]
  exact h.toN hv fun t ht hvt _ => WP.block_nil ⟨e, ht, hvt⟩

/-- The rows: `[o] := y [x]` modulo `2^(32 W)`, and `4 w` at `sK`. -/
theorem rowProd_vp {o x Y : Nat} {L LW LS : List Nat} (c : RCfg o x Y L LW) (hz : wZ ∈ LW) (hoz : o ≠ wZ)
    {E : State → Prop} {A AW V : State → Nat → Nat} (z0 : ∀ σ, E σ → AW σ wZ = 0)
    (certC : DCert (copy o wZ)) (certA : DCert (.block (pRowA o))) (certB : RowCert (pRowB x Y)) :
    VP (Dk P E A L AW LW V LS P.w nArr) (rowProd o x Y) (fun σ s => E σ ∧ RI P (2 * Y) x o A L AW LW V LS σ s) := by
  refine VP.of_imp (p := 0 < P.w) (fun σ s ⟨_, h, _⟩ => by show 0 < 2 * P.w6 + 2; omega_using []) fun pos => ?_
  exact rowProdG_vp c hz hoz z0 pos (Nat.le_refl _) (fun _ _ => cntW_ok) certC certA certB

end

end VG.Proof.Rsa.Arm.RecoverDet
