module
public import VerifiedGarbage.Impl.Dsa.Arm.Stream
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Context
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Dsa.Arm.Doubling
import VerifiedGarbage.Proof.Dsa.Arm.Checks
import VerifiedGarbage.Proof.Mont.Arm.Dyn.ExponentParts
import VerifiedGarbage.Proof.Dsa.StreamBytes
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.Arm.Dyn.PowerTwo
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# DSA on 32-bit ARM: the arithmetic on slots

`reduceStream n` reduces the bytes from `r11` to `lr` modulo the context's
modulus into the result slot (`reduceStream_ok`), a byte at a time
(`streamStep_ok`: eight doublings and the byte's addition); `modulusMinus`
writes `m - amount` (`modulusMinus_ok`), `ordinaryMul` and `ordinaryAdd`
multiply and add ordinary residues (`ordinaryMul_ok`, `ordinaryAdd_ok`).
All of them change only the result and product slots, the temporary slot and
the accumulator (`streamRanges`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_ldrb wp_dp wp_cmp op2_imm op2_reg dpVal eval_ne
  eval_eq)

theorem _root_.VG.Proof.Mont.Arm.Dyn.OpKeep.refl (n : Nat) (base : Addr) (o : Nat) (s : State) :
    OpKeep n base o s s := ⟨Rest.refl _ _, Outs.refl _ _ _⟩

theorem _root_.VG.Proof.Mont.Arm.Dyn.OpKeep.trans {n o : Nat} {base : Addr} {s t u : State}
    (h₁ : OpKeep n base o s t) (h₂ : OpKeep n base o t u) : OpKeep n base o s u :=
  ⟨h₁.rest.trans h₂.rest, h₁.mem.trans h₂.mem⟩

/-- The memory the slot arithmetic changes: the result and product slots, the
temporary slot and the accumulator. -/
abbrev streamRanges (n : Nat) : List (Nat × Nat) :=
  [(slot n 9, 8 * n), (slot n 10, 8 * n), (slot n 1, 8 * n), (slot n 2, 4 * (8 * n + 2))]

theorem _root_.VG.Proof.Mont.Arm.Dyn.OpKeep.streamRanges {n o : Nat} {base : Addr} {s t : State}
    (K : OpKeep n base o s t) (ho : o = 9 ∨ o = 10 := by decide) : Outs base (streamRanges n) s.mem t.mem :=
  K.mem.mono fun r hr => by
    simp only [opRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases ho with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> simp

/-- Memory past the context is kept. -/
theorem Outs.outside {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m') {o n : Nat}
    (hr : ∀ r ∈ rs, o ≤ r.1 ∧ r.1 + r.2 ≤ o + n) : Outside base o n m m' :=
  fun x hx => h x fun r hr' => by have := hr r hr'; omega_arith

theorem streamRanges_inside (n : Nat) : ∀ r ∈ streamRanges n, 0 ≤ r.1 ∧ r.1 + r.2 ≤ 0 + contextBytes n := by
  have b9 := slot_bound (n := n) (i := 9) (by decide)
  have b10 := slot_bound (n := n) (i := 10) (by decide)
  have b1 := slot_le (n := n) (i := 1) (j := 2) (by decide)
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  have a := slot_acc n
  simp only [stride] at *
  simp only [streamRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl) <;> constructor <;> omega_arith

/-! ## Doublings and a byte -/

theorem reduceStep_ok {n size m : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (hv : val32 s.mem base (slot n 9) (2 * n) < m) (hb : val32 s.mem base (slot n 10) (2 * n) < m) :
    WP isa (reduceStep n) s fun t => Context n m base size t ∧ OpKeep n base 9 s t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        (256 * val32 s.mem base (slot n 9) (2 * n) + val32 s.mem base (slot n 10) (2 * n)) % m := by
  have m1 := h.gt_one
  have nw : base.toNat + contextBytes n ≤ 2 ^ 32 := by have := h.ws.nowrap; have := h.size_le; omega_arith
  unfold reduceStep
  refine WP.seq (WP.mono (doubles_ok 8 h hv (by decide)) fun u ⟨cu, Ku, Vu⟩ => ?_)
  have Bu := Ku.val32 (i := 10) (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw
  refine WP.mono (context_add_ok cu (o := 9) (a := 9) (b := 10) (by decide) (by decide) (by decide)
    (by rw [Vu]; exact Nat.mod_lt _ (by omega_arith)) (by rw [Bu]; exact hb)) fun t ⟨ct, Kt, Vt⟩ =>
    ⟨ct, Ku.trans Kt, ?_⟩
  rw [Vt, Vu, Bu, Nat.mod_add_mod]

/-- A number below `2³²` with its low word replaced. -/
theorem val32_low_write {m : Mem} {base : Addr} {d k : Nat} (hk : 0 < k) (hn : base.toNat + d + 4 * k ≤ 2 ^ 32)
    (hv : val32 m base d k < 2 ^ 32) (v : BitVec 32) : val32 (m.writeW (off base d) v) base d k = v.toNat := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_arith⟩
  have hu : val32 (m.writeW (off base d) v) base (d + 4) j = val32 m base (d + 4) j :=
    val32_congr fun i hi => w32_write_ne (size := d + 4 * (j + 1)) (by omega_arith) (by omega_arith) (by omega_arith) (.inr (by omega_arith)) v
  rw [val32] at hv ⊢
  rw [w32_write_self, hu]
  omega_arith

theorem streamStep_ok {n size m i len : Nat} {base : Addr} {s : State} {p : BitVec 32}
    (h : Context n m base size s) (hm : 255 < m) (hi : i < len) (hlen : p.toNat + len ≤ 2 ^ 32)
    (hl : len < 2 ^ 32)
    (hc : s.gpr .r11 = p + BitVec.ofNat 32 i) (he : s.gpr .lr = p + BitVec.ofNat 32 len)
    (hr : InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hv : val32 s.mem base (slot n 9) (2 * n) < m) (hpad : val32 s.mem base (slot n 10) (2 * n) < 2 ^ 32) :
    WP isa (streamStep n) s fun t =>
      Context n m base size t ∧ t.gpr .r11 = p + BitVec.ofNat 32 (i + 1) ∧ t.gpr .lr = s.gpr .lr ∧
      t.z = decide (i + 1 = len) ∧
      val32 t.mem base (slot n 9) (2 * n) =
        (256 * val32 s.mem base (slot n 9) (2 * n) + (s.mem (State.addr p + BitVec.ofNat 64 i)).toNat) % m ∧
      val32 t.mem base (slot n 10) (2 * n) < 2 ^ 32 ∧
      Outs base (streamRanges n) s.mem t.mem ∧ Rest (.r11 :: dclob) s t := by
  have sz := h.size_le
  have sm := h.small
  have nw := h.ws.nowrap
  have b10 := slot_bound (n := n) (i := 10) (by decide)
  have s9 := slot_le (n := n) (i := 9) (j := 10) (by decide)
  have n0 := h.n0
  simp only [stride] at b10 s9
  unfold streamStep
  have ea : State.addr (s.gpr .r11 + BitVec.ofNat 32 0) = State.addr p + BitVec.ofNat 64 i := by
    rw [hc, Offset.add_add, Nat.add_zero, VG.Arm.addr_add (by omega_arith)]
  refine WP.seq (wp_ldrb (by decide) ea hr fun s₁ u₁ => wp_ptr (d := .r10) (by decide) (by simp only [prodS]; omega_arith)
    fun s₂ u₂ => ?_)
  have w₂ : Ws s₂ base size := (h.ws.of_upd u₁ (by decide)).of_upd u₂ (by decide)
  refine wp_str (by decide) (w₂.ea (K := prodS n) (d := 0) (by simp only [u₂.get, u₁.get, reduceCtorEq, ↓reduceIte])
    (by simp only [prodS]; omega_arith)) (w₂.write (d := prodS n + 0) (n := 4) (by simp only [prodS]; omega_arith))
    fun s₃ m₃ => WP.block_nil ?_
  have mem₃ : s₃.mem = s.mem.writeW (off base (slot n 10)) (BitVec.setWidth 32 (s.mem (State.addr p + BitVec.ofNat 64 i))) := by
    rw [m₃.mem, u₂.mem, u₁.mem, u₂.other .r4 (by decide), u₁.gpr]; rfl
  have O₃ : Outside base (slot n 10) (8 * n) s.mem s₃.mem := by
    rw [mem₃]; exact (writeW32_outside _ _ _ (by omega_arith)).mono (Nat.le_refl _) (by omega_arith)
  have w₃ : Ws s₃ base size := w₂.of_mupd m₃
  have c₃ : Context n m base size s₃ := h.of_slot w₃ O₃ (by decide)
  have byte := (s.mem (State.addr p + BitVec.ofNat 64 i)).isLt
  have B₃ : val32 s₃.mem base (slot n 10) (2 * n) = (s.mem (State.addr p + BitVec.ofNat 64 i)).toNat := by
    rw [mem₃, val32_low_write (by omega_arith) (by omega_arith) hpad, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_arith)]
  have Y₃ : val32 s₃.mem base (slot n 9) (2 * n) = val32 s.mem base (slot n 9) (2 * n) :=
    O₃.val32 (by omega_arith) (by omega_arith)
  have R₃ : Rest (.r11 :: dclob) s s₃ :=
    ((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (m₃.rest _)
  refine WP.seq (WP.mono (reduceStep_ok c₃ (by rw [Y₃]; exact hv) (by rw [B₃]; omega_arith)) fun u ⟨cu, Ku, Vu⟩ => ?_)
  refine wp_dp (op2_imm (by decide)) fun t₁ v₁ => wp_cmp (op2_reg _ _) fun t f z => WP.block_nil ?_
  have Ru : Rest (.r11 :: dclob) s u := R₃.trans (Ku.rest.mono (by decide))
  have r11 : t₁.gpr .r11 = p + BitVec.ofNat 32 (i + 1) := by
    rw [v₁.gpr, dpVal, Ku.rest.gpr .r11 (by decide), m₃.gpr, u₂.other .r11 (by decide),
      u₁.other .r11 (by decide), hc]
    show p + BitVec.ofNat 32 i + BitVec.ofNat 32 1 = _
    rw [Offset.add_add]
  have lr : t₁.gpr .lr = s.gpr .lr := by rw [v₁.other .lr (by decide)]; exact Ru.gpr .lr (by decide)
  have mt : t.mem = u.mem := by rw [f.mem, v₁.mem]
  refine ⟨⟨?_, c₃.size_le, c₃.small, c₃.n0, ?_, c₃.gt_one, ?_⟩, by rw [f.gpr]; exact r11, by rw [f.gpr]; exact lr,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact (cu.ws.of_upd v₁ (by decide)).of_fupd f
  · rw [mt]; exact cu.modulus
  · rw [mt]; exact cu.inverse
  · rw [z, r11, lr, he, sub_add_add, cmp_ofNat (by omega_arith) (by omega_arith)]
  · rw [mt, Vu, Y₃, B₃]
  · have nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by omega_arith
    rw [mt, Ku.val32 (i := 10) (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', B₃]
    omega_arith
  · rw [mt]
    exact (Outs.of_outside O₃ (by simp)).trans Ku.streamRanges
  · exact (Ru.trans (v₁.rest (by decide))).trans (f.rest _)

/-! ## The stream -/

/-- The bytes from `r11 = p` to `lr = p + len`, reduced modulo `m` into the
result slot. -/
theorem reduceStream_ok {n size m len : Nat} {base : Addr} {s : State} {p : BitVec 32}
    (h : Context n m base size s) (hm : 255 < m) (hlen : p.toNat + len ≤ 2 ^ 32) (hl : len < 2 ^ 32)
    (hc : s.gpr .r11 = p) (he : s.gpr .lr = p + BitVec.ofNat 32 len)
    (hr : ∀ i < len, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨State.addr p, len⟩ ⟨off base 0, contextBytes n⟩) :
    WP isa (reduceStream n) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr p) len) % m ∧
      Outs base (streamRanges n) s.mem t.mem ∧ Rest (.r11 :: dclob) s t := by
  have sz := h.size_le
  have sm := h.small
  have nw := h.ws.nowrap
  have b9 := slot_bound (n := n) (i := 9) (by decide)
  have b10 := slot_bound (n := n) (i := 10) (by decide)
  have s9 := slot_le (n := n) (i := 9) (j := 10) (by decide)
  have n0 := h.n0
  have m0 : 0 < m := by omega_arith
  simp only [stride] at b9 b10 s9
  have e8 : 4 * (2 * n) = 8 * n := by omega_arith
  unfold reduceStream
  refine WP.seq (WP.mono (zeros_ok h.ws (k := 2 * n) (o := resS n) (by omega_arith) (by simp only [resS]; omega_arith)
    (by simp only [resS]; omega_arith)) fun u₁ ⟨w₁, Z₁, O₁, R₁⟩ => ?_)
  rw [e8] at O₁
  have c₁ := h.of_slot w₁ O₁ (by decide)
  refine WP.seq (WP.mono (zeros_ok w₁ (k := 2 * n) (o := prodS n) (by omega_arith) (by simp only [prodS]; omega_arith)
    (by simp only [prodS]; omega_arith)) fun u₂ ⟨w₂, Z₂, O₂, R₂⟩ => ?_)
  rw [e8] at O₂
  have c₂ := c₁.of_slot w₂ O₂ (by decide)
  have Y₂ : val32 u₂.mem base (slot n 9) (2 * n) = 0 := by
    rw [O₂.val32 (by simp only [prodS]; omega_arith) (by omega_arith)]; exact val32_zeros Z₁
  have P₂ : val32 u₂.mem base (slot n 10) (2 * n) = 0 := val32_zeros Z₂
  have K₂ : Outs base (streamRanges n) s.mem u₂.mem :=
    (Outs.of_outside O₁ (by simp [resS])).trans (Outs.of_outside O₂ (by simp [prodS]))
  have R₂' : Rest (.r11 :: dclob) s u₂ := (R₁.mono (by decide)).trans (R₂.mono (by decide))
  have r11 : u₂.gpr .r11 = p := by rw [R₂.gpr .r11 (by decide), R₁.gpr .r11 (by decide), hc]
  have lr : u₂.gpr .lr = p + BitVec.ofNat 32 len := by rw [R₂.gpr .lr (by decide), R₁.gpr .lr (by decide), he]
  refine WP.seq (wp_cmp (op2_reg _ _) fun u₃ f₃ z₃ => WP.block_nil ?_)
  have c₃ : Context n m base size u₃ := ⟨c₂.ws.of_fupd f₃, c₂.size_le, c₂.small, c₂.n0, by rw [f₃.mem]; exact c₂.modulus,
    c₂.gt_one, by rw [f₃.mem]; exact c₂.inverse⟩
  have R₃ : Rest (.r11 :: dclob) s u₃ := R₂'.trans (f₃.rest _)
  have K₃ : Outs base (streamRanges n) s.mem u₃.mem := by rw [f₃.mem]; exact K₂
  have p0 : p = p + BitVec.ofNat 32 0 := (BitVec.add_zero p).symm
  have d0 := sub_add_add p 0 len
  rw [BitVec.add_zero] at d0
  rw [r11, lr, d0, cmp_ofNat (by omega_arith) (by omega_arith)] at z₃
  have dec0 : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr p) 0) % m = 0 := by
    simp only [Spec.Rsa.bytesAt, List.range_zero, List.map_nil, Spec.Dsa.decodeBE, List.foldl_nil, Nat.zero_mod]
  refine WP.ite (decide (0 = len)) (by rw [eval_eq, z₃]) (fun hz => WP.block_nil ⟨c₃, ?_, K₃, R₃⟩) fun hz => ?_
  · have hz : len = 0 := (of_decide_eq_true hz).symm
    rw [f₃.mem, Y₂, hz, dec0]
  have hpos : 0 < len := by have := of_decide_eq_false hz; omega_arith
  have inside := streamRanges_inside n
  refine WP.loop (M := isa) (fun k (u : State) => ∃ i, k = len - i ∧ i < len ∧ Context n m base size u ∧
      u.gpr .r11 = p + BitVec.ofNat 32 i ∧ u.gpr .lr = p + BitVec.ofNat 32 len ∧
      val32 u.mem base (slot n 9) (2 * n) = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr p) i) % m ∧
      val32 u.mem base (slot n 10) (2 * n) < 2 ^ 32 ∧ Outs base (streamRanges n) s.mem u.mem ∧
      Rest (.r11 :: dclob) s u) ?_ len u₃
    ⟨0, by omega_arith, hpos, c₃, by rw [f₃.gpr, r11]; exact p0, by rw [f₃.gpr, lr], by rw [f₃.mem, Y₂, dec0],
      by rw [f₃.mem, P₂]; decide, K₃, R₃⟩
  rintro k u ⟨i, rfl, hi, cu, r11u, lru, Vu, Pu, Ou, Ru⟩
  refine WP.mono (streamStep_ok cu hm hi hlen hl r11u lru (by rw [Ru.rd, Ru.wr]; exact hr i hi)
    (by rw [Vu]; exact Nat.mod_lt _ m0) Pu) fun t ⟨ct, r11t, lrt, zt, Vt, Pt, Ot, Rt⟩ => ?_
  have byte : u.mem (State.addr p + BitVec.ofNat 64 i) = s.mem (State.addr p + BitVec.ofNat 64 i) :=
    VG.Proof.Weierstrass.keep_of_disjoint (Outs.outside Ou inside) hd (by omega_arith) hi (by omega_arith)
  have Vt' : val32 t.mem base (slot n 9) (2 * n) =
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr p) (i + 1)) % m := by
    rw [Vt, Vu, byte, VG.Proof.Dsa.reduce_prefix_succ]
  by_cases hl : i + 1 = len
  · exact .inl ⟨by rw [eval_ne, zt]; simp [hl], ct, by rw [Vt', hl], Ou.trans Ot, Ru.trans Rt⟩
  · exact .inr ⟨by rw [eval_ne, zt]; simp [hl], len - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, ct, r11t,
      by rw [lrt, lru], Vt', Pt, Ou.trans Ot, Ru.trans Rt⟩

/-! ## Slot arithmetic -/

/-- `[resS] = m - amount`. -/
theorem modulusMinus_ok {n size m amount : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (ha : amount ≤ m) (hn4 : 8 * n ≤ 4096) :
    WP isa (modulusMinus n amount) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) = m - amount ∧ Outs base (streamRanges n) s.mem t.mem ∧
      Rest dclob s t := by
  have sz := h.size_le
  have sm := h.small
  have b10 := slot_bound (n := n) (i := 10) (by decide)
  have s09 := slot_le (n := n) (i := 0) (j := 9) (by decide)
  have s9 := slot_le (n := n) (i := 9) (j := 10) (by decide)
  have n0 := h.n0
  have hm : m < 2 ^ (32 * (2 * n)) := by rw [← h.modulus]; exact val32_lt _ _ _ _
  simp only [stride] at b10 s09 s9
  have e8 : 4 * (2 * n) = 8 * n := by omega_arith
  unfold modulusMinus
  refine WP.seq (WP.mono (setConst_ok h.ws (k := 2 * n) (o := prodS n) (x := amount) (by omega_arith)
    (by simp only [prodS]; omega_arith) (by simp only [prodS]; omega_arith) (by omega_arith)) fun u ⟨Vu, Ru, Ou⟩ => ?_)
  rw [e8] at Ou
  have cu := h.of_slot (h.ws.of_rest Ru (by decide)) Ou (by decide)
  refine WP.mono (subWords_ok cu.ws (k := 2 * n) (o := resS n) (a := modS n) (b := prodS n) (by omega_arith)
    (by simp only [modS]; omega_arith) (by simp only [prodS]; omega_arith) (by simp only [resS]; omega_arith)
    (by simp only [modS]; omega_arith) (by simp only [prodS]; omega_arith) (by simp only [resS]; omega_arith)
    (by simp only [resS, modS]; omega_arith) (by simp only [resS, prodS]; omega_arith)) fun t ⟨Vt, Rt, Ot⟩ => ⟨?_, ?_, ?_, Ru.trans Rt⟩
  · rw [e8] at Ot; exact cu.of_slot (cu.ws.of_rest Rt (by decide)) Ot (by decide)
  · show val32 t.mem base (resS n) (2 * n) = _
    have Vu' : val32 u.mem base (slot n 10) (2 * n) = amount := by rw [Nat.mod_eq_of_lt (by omega_arith)] at Vu; exact Vu
    rw [Vt, show modS n = slot n 0 from rfl, cu.modulus, show prodS n = slot n 10 from rfl, Vu', show m + 2 ^ (32 * (2 * n)) - amount = (m - amount) + 2 ^ (32 * (2 * n)) by omega_arith,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]
  · rw [e8] at Ot; exact (Outs.of_outside Ou (by simp [prodS])).trans (Outs.of_outside Ot (by simp [resS]))

/-- `[resS] = [expS] [baseS] mod m`, from `R² mod m` in slot 7. -/
theorem ordinaryMul_ok {n size m : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (hr2 : val32 s.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m) :
    WP isa (ordinaryMul n) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 11) (2 * n) * val32 s.mem base (slot n 8) (2 * n) % m ∧
      Outs base (streamRanges n) s.mem t.mem ∧ Rest dclob s t := by
  have nw : base.toNat + contextBytes n ≤ 2 ^ 32 := by have := h.ws.nowrap; have := h.size_le; omega_arith
  unfold ordinaryMul
  refine WP.seq (WP.mono (context_mul_ok h (o := 10) (a := 8) (b := 7) (by decide) (by decide) (by decide)
    (by rw [hr2]; exact Nat.mod_lt _ (by have := h.gt_one; omega_arith))) fun u ⟨cu, Ku, ltu, Vu⟩ => ?_)
  have Pu : val32 u.mem base (slot n 10) (2 * n) = val32 s.mem base (slot n 8) (2 * n) * 2 ^ (64 * n) % m :=
    mont_encode h.coprime ltu (by rw [Vu, hr2])
  have Eu := Ku.val32 (i := 11) (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw
  refine WP.mono (context_mul_ok cu (o := 9) (a := 11) (b := 10) (by decide) (by decide) (by decide) ltu)
    fun t ⟨ct, Kt, ltt, Vt⟩ => ⟨ct, ?_, Ku.streamRanges.trans Kt.streamRanges, Ku.rest.trans Kt.rest⟩
  rw [Pu, Eu] at Vt
  rw [← Nat.mod_eq_of_lt ltt, ← Eu]
  rw [Eu]
  exact VG.Proof.Dsa.mont_scale h.coprime Vt

/-- `[resS] = [baseS] + [expS] mod m`. -/
theorem ordinaryAdd_ok {n size m : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (ha : val32 s.mem base (slot n 8) (2 * n) < m) (hb : val32 s.mem base (slot n 11) (2 * n) < m) :
    WP isa (ordinaryAdd n) s fun t => Context n m base size t ∧ OpKeep n base 9 s t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        (val32 s.mem base (slot n 8) (2 * n) + val32 s.mem base (slot n 11) (2 * n)) % m :=
  context_add_ok h (o := 9) (a := 8) (b := 11) (by decide) (by decide) (by decide) ha hb

end VG.Proof.Dsa.Arm
