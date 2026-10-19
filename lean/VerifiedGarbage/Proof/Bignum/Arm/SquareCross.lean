module

public import VerifiedGarbage.Proof.Bignum.Arm.SquareInit
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block

/-! # The square's rows of cross products -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_dp wp_mov wp_subs op2_imm op2_reg dpVal ofNat_beq_zero)

/-- The head word of a zero number. -/
theorem val32_zero_head {m : Mem} {b : Addr} {d k : Nat} (h : val32 m b d (k + 1) = 0) :
    w32 m b d = 0 := by
  rw [val32] at h
  omega

/-- The count of rows decremented, Z after the last. -/
theorem sqCount_ok (s : State) {base : BitVec 32} {size M c : Nat} (ws : Workspace s base size)
    (fit : M + 20 ≤ size) (p0 : s.gpr .r0 = base + BitVec.ofNat 32 M)
    (hc : s.mem.readW (off (State.addr base) (M + 16)) 32 = BitVec.ofNat 32 c) (h1 : 1 ≤ c)
    (h32 : c < 2 ^ 32) :
    WP isa (.block sqCount) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) (M + 16)) (BitVec.ofNat 32 (c - 1)) ∧
      t.z = decide (c = 1) ∧ Rest [.lr] s t := by
  have nowrap := ws.nowrap
  unfold sqCount
  refine wp_ldr (by decide) (sq_ea nowrap p0 (by omega)) (ws.read (by omega)) fun s1 u1 => ?_
  refine wp_subs (op2_imm (by decide)) fun s2 u2 hz => ?_
  refine wp_str_z (by decide) (sq_ea nowrap ((u2.other .r0 (by decide)).trans ((u1.other .r0 (by decide)).trans p0))
    (by omega)) (by rw [u2.wr, u1.wr]; exact ws.write (by omega)) fun t u3 z3 => WP.block_nil ?_
  have v : s2.gpr .lr = BitVec.ofNat 32 (c - 1) := by
    rw [u2.gpr, u1.gpr, hc]
    change BitVec.ofNat 32 c - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · rw [u3.mem, u2.mem, u1.mem, v]
  · rw [z3, hz, u1.gpr, hc]
    change (BitVec.ofNat 32 c - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show c - 1 = 0 ↔ c = 1 by omega]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest _))

theorem crossArgs_ok (s : State) {base : BitVec 32} {size M A C P : Nat} (ws : Workspace s base size)
    (fit : M + 24 ≤ size) (p0 : s.gpr .r0 = base + BitVec.ofNat 32 M)
    (hn : s.mem.readW (off (State.addr base) (M + 12)) 32 = base + BitVec.ofNat 32 A)
    (hc : s.mem.readW (off (State.addr base) (M + 16)) 32 = BitVec.ofNat 32 C)
    (ht : s.mem.readW (off (State.addr base) (M + 20)) 32 = base + BitVec.ofNat 32 P) :
    WP isa (.block crossArgs) s fun t =>
      t.gpr .r2 = base + BitVec.ofNat 32 A ∧ t.gpr .r12 = base + BitVec.ofNat 32 (A + 4) ∧
      t.gpr .lr = BitVec.ofNat 32 C ∧ t.gpr .r0 = base + BitVec.ofNat 32 P ∧ t.gpr .r11 = 0 ∧
      t.mem = (s.mem.writeW (off (State.addr base) (M + 20)) (base + BitVec.ofNat 32 (P + 8))).writeW
        (off (State.addr base) (M + 12)) (base + BitVec.ofNat 32 (A + 4)) ∧
      Rest [.r0, .r2, .r3, .r4, .r11, .r12, .lr] s t := by
  have nowrap := ws.nowrap
  unfold crossArgs
  refine wp_ldr (by decide) (sq_ea nowrap p0 (by omega)) (ws.read (by omega)) fun s1 u1 => ?_
  have p1 := (u1.other .r0 (by decide)).trans p0
  refine wp_ldr (by decide) (sq_ea nowrap p1 (by omega)) (by rw [u1.rd, u1.wr]; exact ws.read (by omega))
    fun s2 u2 => ?_
  have p2 := (u2.other .r0 (by decide)).trans p1
  refine wp_ldr (by decide) (sq_ea nowrap p2 (by omega))
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact ws.read (by omega)) fun s3 u3 => ?_
  have p3 := (u3.other .r0 (by decide)).trans p2
  refine wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
  have p4 := (u4.other .r0 (by decide)).trans p3
  refine wp_str (by decide) (sq_ea nowrap p4 (by omega))
    (by rw [u4.wr, u3.wr, u2.wr, u1.wr]; exact ws.write (by omega)) fun s5 u5 => ?_
  have p5 : s5.gpr .r0 = base + BitVec.ofNat 32 M := by rw [u5.gpr]; exact p4
  refine wp_dp (op2_imm (by decide)) fun s6 u6 => ?_
  have p6 := (u6.other .r0 (by decide)).trans p5
  refine wp_str (by decide) (sq_ea nowrap p6 (by omega))
    (by rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]; exact ws.write (by omega)) fun s7 u7 => ?_
  refine wp_mov (op2_reg _ _) fun s8 u8 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u9 => WP.block_nil ?_
  have g2 : s2.gpr .r2 = base + BitVec.ofNat 32 A := by rw [u2.other .r2 (by decide), u1.gpr, hn]
  have g3 : s3.gpr .r3 = base + BitVec.ofNat 32 P := by rw [u3.gpr, u2.mem, u1.mem, ht]
  have v4 : s4.gpr .r4 = base + BitVec.ofNat 32 (P + 8) := by
    rw [u4.gpr, dpVal, g3]
    change base + BitVec.ofNat 32 P + BitVec.ofNat 32 8 = _
    rw [Offset.add_add]
  have v6 : s6.gpr .r12 = base + BitVec.ofNat 32 (A + 4) := by
    rw [u6.gpr, dpVal, u5.gpr, u4.other .r2 (by decide), u3.other .r2 (by decide), g2]
    change base + BitVec.ofNat 32 A + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
  refine ⟨?_, ?_, ?_, ?_, u9.gpr, ?_, ?_⟩
  · rw [u9.other .r2 (by decide), u8.other .r2 (by decide), u7.gpr, u6.other .r2 (by decide), u5.gpr,
      u4.other .r2 (by decide), u3.other .r2 (by decide), g2]
  · rw [u9.other .r12 (by decide), u8.other .r12 (by decide), u7.gpr, v6]
  · rw [u9.other .lr (by decide), u8.other .lr (by decide), u7.gpr, u6.other .lr (by decide), u5.gpr,
      u4.other .lr (by decide), u3.other .lr (by decide), u2.gpr, u1.mem, hc]
  · rw [u9.other .r0 (by decide), u8.gpr, u7.gpr, u6.other .r3 (by decide), u5.gpr,
      u4.other .r3 (by decide), g3]
  · rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, v6, v4]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans
      ((u5.rest _).trans ((u6.rest (by simp)).trans ((u7.rest _).trans ((u8.rest (by simp)).trans (u9.rest (by simp)))))))))

/-- The row's scalar. -/
theorem crossScalar_ok (s : State) {base : BitVec 32} {size A : Nat} (ws : Workspace s base size)
    (fit : A + 4 ≤ size) (p2 : s.gpr .r2 = base + BitVec.ofNat 32 A) :
    WP isa (.block crossScalar) s fun t =>
      t.gpr .r1 = s.mem.readW (off (State.addr base) A) 32 ∧ t.mem = s.mem ∧ Rest [.r1] s t := by
  unfold crossScalar
  refine wp_ldr (by decide) (by simpa only [Nat.add_zero] using sq_ea ws.nowrap p2 (imm := 0) (by omega))
    (ws.read fit) fun t u => WP.block_nil ⟨u.gpr, u.mem, u.rest (by simp)⟩

/-- The row's carry stored above it. -/
theorem crossCarry_ok (s : State) {base : BitVec 32} {size d : Nat} (ws : Workspace s base size)
    (fit : d + 4 ≤ size) (p0 : s.gpr .r0 = base + BitVec.ofNat 32 d) :
    WP isa (.block crossCarry) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) d) (s.gpr .r11) ∧ Rest [] s t := by
  unfold crossCarry
  refine wp_str (by decide) (by simpa only [Nat.add_zero] using sq_ea ws.nowrap p0 (imm := 0) (by omega))
    (ws.write fit) fun t u => WP.block_nil ⟨u.mem, u.rest _⟩

/-- A row's value step: the window, extended by the zero word above it,
gains the scalar product. -/
theorem cross_value {V5 V3 P Xo Xn L L4 Q r w A : Nat} (hrep : V5 + P * Xo = V3 + P * Xn)
    (hn : Xn = L4 + Q * r) (hrow : L4 + Q * r = L + w * A + 0) (ho : Xo = L + Q * 0) :
    V5 = V3 + P * (w * A) := by
  subst hn ho
  rw [hrow] at hrep
  grind

section
variable {m0 : Mem} {base : BitVec 32} {size out a mod M n : Nat} {inv : BitVec 32}

theorem crossRound_ok (s : State) {k : Nat} (h : CrossInv m0 base size out a mod M n inv k s)
    (hk : k + 2 ≤ n) :
    WP isa crossRound s fun t => CrossInv m0 base size out a mod M n inv (k + 1) t ∧
      t.z = decide (k + 2 = n) ∧ Rest roundClobbers s t := by
  have env := h.env
  have nowrap := env.nowrap
  have := env.fits; have := env.count; have := env.sepA; have := env.aFits; have := env.header
  -- The row's window, `len` words at `o`, and the word above it.
  obtain ⟨o, ho⟩ : ∃ o, o = M + 28 + 8 * k := ⟨_, rfl⟩
  obtain ⟨len, hlen⟩ : ∃ len, len = n - 1 - k := ⟨_, rfl⟩
  rw [crossRound, WP.seq_iff]
  refine WP.mono (sqAnchor_ok s env) ?_
  rintro s1 ⟨p1, m1, r1⟩
  have e1 := env.of_mem m1 r1
  rw [WP.seq_iff]
  refine WP.mono (crossArgs_ok s1 (A := a + 4 * k) (C := len) (P := o) e1.workspace (by omega) p1
    (by rw [m1]; exact h.next) (by rw [m1, hlen]; exact h.cnt) (by rw [m1, ho]; exact h.tptr)) ?_
  rintro s2 ⟨g2, g12, glr, g0, g11, m2, r2⟩
  have o2a := writeW32_outside s1.mem (State.addr base) (d := M + 20) (base + BitVec.ofNat 32 (o + 8))
    (by omega)
  have o2b := writeW32_outside (s1.mem.writeW (off (State.addr base) (M + 20)) (base + BitVec.ofNat 32 (o + 8)))
    (State.addr base) (d := M + 12) (base + BitVec.ofNat 32 (a + 4 * k + 4)) (by omega)
  rw [← m2] at o2b
  have O2 : Outside (State.addr base) (M + 12) 12 s1.mem s2.mem :=
    (o2a.mono (by omega) (by omega)).trans (o2b.mono (by omega) (by omega))
  have e2 := e1.next (Outs.of_outside (O2.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega) (by omega))
    (by simp)) r2
  rw [WP.seq_iff]
  refine WP.mono (crossScalar_ok s2 e2.workspace (by omega) g2) ?_
  rintro s3 ⟨g1, m3, r3⟩
  have e3 := e2.of_mem m3 r3
  have ctx : RowCtx s3 base size o (a + 4 * (k + 1)) len :=
    ⟨nowrap, by omega, by omega, by omega, e3.workspace.writable⟩
  rw [WP.seq_iff]
  refine WP.mono (row_ok s3 ctx (by omega) ((r3.gpr .r0 (by simp)).trans g0)
    (by rw [r3.gpr .r12 (by simp), g12, show a + 4 * k + 4 = a + 4 * (k + 1) by omega])
    ((r3.gpr .lr (by simp)).trans glr)) ?_
  intro s4 ri
  have e4 := e3.next (Outs.of_outside (ri.outside.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega)
    (by omega)) (by simp)) ri.rest
  rw [WP.seq_iff]
  refine WP.mono (crossCarry_ok s4 e4.workspace (d := o + 4 * len) (by omega) ri.outPtr) ?_
  rintro s5 ⟨m5, r5⟩
  have o5 := writeW32_outside s4.mem (State.addr base) (d := o + 4 * len) (s4.gpr .r11) (by omega)
  rw [← m5] at o5
  have OW : Outside (State.addr base) o (4 * len + 4) s3.mem s5.mem :=
    (ri.outside.mono (by omega) (by omega)).trans (o5.mono (by omega) (by omega))
  have e5 := e4.next (Outs.of_outside (o5.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega) (by omega))
    (by simp)) r5
  rw [WP.seq_iff]
  refine WP.mono (sqAnchor_ok s5 e5) ?_
  rintro s6 ⟨p6, m6, r6⟩
  have e6 := e5.of_mem m6 r6
  have cnt6 : s6.mem.readW (off (State.addr base) (M + 16)) 32 = BitVec.ofNat 32 len := by
    rw [m6, outside_read32 OW (by omega) (by omega), m3, m2, rd_other _ (by omega) (by omega) (by omega),
      rd_other _ (by omega) (by omega) (by omega), m1, hlen]
    exact h.cnt
  refine WP.mono (sqCount_ok s6 e6.workspace (by omega) p6 cnt6 (by omega) (by omega)) ?_
  rintro t ⟨m7, z7, r7⟩
  have o7 := writeW32_outside s6.mem (State.addr base) (d := M + 16) (BitVec.ofNat 32 (len - 1)) (by omega)
  rw [← m7] at o7
  have et := e6.next (Outs.of_outside (o7.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega) (by omega))
    (by simp)) r7
  -- Everything but the metadata's words from `M + 12` and the row.
  have all : Outs (State.addr base) [(M + 12, 12), (o, 4 * len + 4)] s.mem t.mem := by
    have A1 : Outs (State.addr base) [(M + 12, 12), (o, 4 * len + 4)] s1.mem s2.mem :=
      Outs.of_outside O2 (by simp)
    have A2 : Outs (State.addr base) [(M + 12, 12), (o, 4 * len + 4)] s3.mem s5.mem :=
      Outs.of_outside OW (by simp)
    have A3 : Outs (State.addr base) [(M + 12, 12), (o, 4 * len + 4)] s6.mem t.mem :=
      Outs.of_outside (o7.mono (o' := M + 12) (n' := 12) (by omega) (by omega)) (by simp)
    rw [m1] at A1; rw [m3] at A2; rw [m6] at A3
    exact A1.trans (A2.trans A3)
  -- The value.
  have aw := e2.aWord (j := k) (by omega)
  have av := e3.aVal (d := a + 4 * (k + 1)) (k := len) (by omega) (by omega)
  have v3 : val32 s3.mem (State.addr base) (M + 24) (2 * n + 2) = sqCross m0 (State.addr base) a n k := by
    rw [m3, O2.val32 (by omega) (by omega), m1]; exact h.value
  have rep := val32_replace (m := s3.mem) (m' := s5.mem) (base := State.addr base) (d := M + 24)
    (i := 2 * k + 1) (j := n - k) (k := n + 1 - k) (OW.val32 (by omega) (by omega))
    (OW.val32 (by omega) (by omega))
  rw [show 2 * k + 1 + (n - k) + (n + 1 - k) = 2 * n + 2 by omega,
    show M + 24 + 4 * (2 * k + 1) = o by omega, show n - k = len + 1 by omega] at rep
  have xn : val32 s5.mem (State.addr base) o len = val32 s4.mem (State.addr base) o len :=
    o5.val32 (by omega) (by omega)
  have wn : w32 s5.mem (State.addr base) (o + 4 * len) = (s4.gpr .r11).toNat := by
    rw [m5, w32_write_self]
  have wo : w32 s3.mem (State.addr base) (o + 4 * len) = 0 := by
    rw [m3, O2.w32 (by omega) (by omega), m1, show o + 4 * len = M + 24 + 4 * (k + n) by omega]
    have z := h.top
    rw [show n + 2 - k = (n + 1 - k) + 1 by omega] at z
    exact val32_zero_head z
  have row := ri.value
  rw [(r3.gpr .r11 (by simp)).trans g11, g1] at row
  change _ = _ + w32 s2.mem (State.addr base) (a + 4 * k) * _ + (0 : BitVec 32).toNat at row
  rw [aw, show a + 4 * (k + 1) = a + 4 * (k + 1) from rfl] at row
  have vt : val32 t.mem (State.addr base) (M + 24) (2 * n + 2) = val32 s5.mem (State.addr base) (M + 24) (2 * n + 2) := by
    rw [o7.val32 (by omega) (by omega), m6]
  refine ⟨⟨et, by omega, h.md.of_outs all (by simp; omega) (by omega), ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [m7, rd_other _ (by omega) (by omega) (by omega), m6, outside_read32 OW (by omega) (by omega), m3, m2,
      rd_self, show a + 4 * k + 4 = a + 4 * (k + 1) by omega]
  · rw [m7, rd_self, hlen, show n - 1 - k - 1 = n - 1 - (k + 1) by omega]
  · rw [m7, rd_other _ (by omega) (by omega) (by omega), m6, outside_read32 OW (by omega) (by omega), m3, m2,
      rd_other _ (by omega) (by omega) (by omega), rd_self, ho, show M + 28 + 8 * k + 8 = M + 28 + 8 * (k + 1) by omega]
  · rw [vt]
    have := cross_value rep (by rw [val32_succ, xn, wn]) row (by rw [val32_succ, wo])
    rw [this, v3, av, hlen]
    rfl
  · rw [all.val32 (by simp; omega) (by omega)]
    have z := h.top
    rw [show n + 2 - k = 1 + (n + 2 - (k + 1)) by omega] at z
    have z' := val32_zero_tail z
    rwa [show M + 24 + 4 * (k + n) + 4 * 1 = M + 24 + 4 * (k + 1 + n) by omega] at z'
  · rw [z7, hlen]; simp only [show n - 1 - k = 1 ↔ k + 2 = n by omega]
  · exact (r1.mono (by simp [roundClobbers])).trans ((r2.mono (by simp [roundClobbers])).trans
      ((r3.mono (by simp [roundClobbers])).trans ((ri.rest.mono (by simp [loopClobbers, roundClobbers])).trans
      ((r5.mono (by simp [roundClobbers])).trans ((r6.mono (by simp [roundClobbers])).trans
      (r7.mono (by simp [roundClobbers])))))))

theorem crossRows_ok (s : State) (h : CrossInv m0 base size out a mod M n inv 0 s) :
    WP isa crossRows s fun t => CrossInv m0 base size out a mod M n inv (n - 1) t ∧
      Rest roundClobbers s t := by
  have hn := h.env.count
  let loopInv := fun k t => ∃ i, i + k = n - 1 ∧ 0 < k ∧
    CrossInv m0 base size out a mod M n inv i t ∧ Rest roundClobbers s t
  unfold crossRows
  refine WP.loop (M := isa) loopInv ?_ (n - 1) s ?_
  · intro k t hk
    obtain ⟨i, hik, hk, hi, rest⟩ := hk
    refine WP.mono (crossRound_ok t hi (by omega)) ?_
    rintro u ⟨hu, hz, ru⟩
    by_cases he : i + 2 = n
    · left
      refine ⟨?_, by rw [show n - 1 = i + 1 by omega]; exact hu, rest.trans ru⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu, rest.trans ru⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · exact ⟨0, by omega, by omega, h, Rest.refl _ _⟩

end

end VG.Proof.Bignum.Arm
