module
-- separate module: the proof of the division by words is split in a chain of modules (`KdNorm`, `KdTop`, `KdEst`, `KdStep`, `KdDiv`), so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Rsa.Arm.KdNorm
import VerifiedGarbage.Proof.Framework.Offset

/-! # The top words of a window of the key checks' division on ARMv7 (`KeyDiv.topWords`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv VG.Proof.Rsa.Arm.Keys VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

/-- `Ws` without its registers: what a block that clobbers `r7`–`r9` still has. -/
structure WsM (s : State) (B : BitVec 32) (Z w N : Nat) : Prop where
  nowrap : B.toNat + Z ≤ 2 ^ 32
  writable : (⟨State.addr B, Z⟩ : Region) ∈ s.wr
  fits : arr w N ≤ Z

theorem _root_.VG.Proof.Rsa.Arm.Keys.Ws.m {s : State} {B : BitVec 32} {Z w N : Nat} (h : Ws s B Z w N) : WsM s B Z w N :=
  ⟨h.nowrap, h.writable, h.fits⟩

theorem WsM.of {s t : State} {B : BitVec 32} {Z w N : Nat} (h : WsM s B Z w N) (wr : t.wr = s.wr) :
    WsM t B Z w N :=
  ⟨h.nowrap, wr ▸ h.writable, h.fits⟩

theorem WsM.hdr_le {s : State} {B : BitVec 32} {Z w N : Nat} (h : WsM s B Z w N) :
    VG.Impl.Rsa.Arm.Keys.hdr ≤ Z :=
  Nat.le_trans (Nat.le_add_right _ _) h.fits

theorem WsM.addr {s : State} {B : BitVec 32} {Z w N d : Nat} (h : WsM s B Z w N) (hd : d < Z) :
    State.addr (B + BitVec.ofNat 32 d) = off (State.addr B) d :=
  VG.Arm.addr_add (by have := h.nowrap; omega_using [hd, this])

theorem WsM.write {s : State} {B : BitVec 32} {Z w N d : Nat} (h : WsM s B Z w N) (hd : d + 4 ≤ Z) :
    InRegions s.wr (off (State.addr B) d) 4 :=
  ⟨_, h.writable, Offset.contains_base _ hd (by have := h.nowrap; omega_using [hd, this])⟩

theorem WsM.read {s : State} {B : BitVec 32} {Z w N d : Nat} (h : WsM s B Z w N) (hd : d + 4 ≤ Z) :
    InRegions (s.rd ++ s.wr) (off (State.addr B) d) 4 := by
  obtain ⟨R, hR, hsub⟩ := h.write hd
  exact ⟨R, List.mem_append_right _ hR, hsub⟩

/-- A word of `y P` from two words of `y`: `lo(a P) + hi(b P)`, modulo `2^32`. -/
abbrev wordP (a b P : Nat) : Nat := (a * P % 2 ^ 32 + b * P / 2 ^ 32) % 2 ^ 32

theorem ofNat_lo_hi {a b : Nat} : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 ((a + b) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

/-- The registers `topWords` changes. -/
abbrev topRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

/-- `topWords`: from `r10` at `X`, the window's words `y₀ … y₃` there, `u₀` (64),
`u₁` (`r11`) and `u₂` (68), the words of `y P` from them. -/
theorem topWords_ok {s : State} {B : BitVec 32} {Z w N X : Nat} (h : Ws s B Z w N)
    (hXZ : X + 16 ≤ Z) (h10 : s.gpr .r10 = B + BitVec.ofNat 32 X) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ t, t.mem = (s.mem.writeW (off (State.addr B) sU0) (BitVec.ofNat 32 (wordP
        (w32 s.mem (State.addr B) (X + 4)) (w32 s.mem (State.addr B) X) (slot s.mem B sP)))).writeW
        (off (State.addr B) sU2) (BitVec.ofNat 32 (wordP (w32 s.mem (State.addr B) (X + 12))
          (w32 s.mem (State.addr B) (X + 8)) (slot s.mem B sP))) →
      t.gpr .r11 = BitVec.ofNat 32 (wordP (w32 s.mem (State.addr B) (X + 8)) (w32 s.mem (State.addr B) (X + 4))
        (slot s.mem B sP)) → t.gpr .r12 = B → Rest topRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (topWords ++ rest)) s Q := by
  have nw := h.nowrap
  have hz := h.hdr_le
  generalize ey0 : w32 s.mem (State.addr B) X = y0 at k
  generalize ey1 : w32 s.mem (State.addr B) (X + 4) = y1 at k
  generalize ey2 : w32 s.mem (State.addr B) (X + 8) = y2 at k
  generalize ey3 : w32 s.mem (State.addr B) (X + 12) = y3 at k
  generalize eP : slot s.mem B sP = P at k
  have a0 : State.addr (B + BitVec.ofNat 32 X) = off (State.addr B) X := h.addr (by omega_using [hXZ])
  have a4 : State.addr (B + BitVec.ofNat 32 X + BitVec.ofNat 32 4) = off (State.addr B) (X + 4) := by
    rw [add_ofNat_assoc]; exact h.addr (by omega_using [hXZ])
  have a8 : State.addr (B + BitVec.ofNat 32 X + BitVec.ofNat 32 8) = off (State.addr B) (X + 8) := by
    rw [add_ofNat_assoc]; exact h.addr (by omega_using [hXZ])
  have a12 : State.addr (B + BitVec.ofNat 32 X + BitVec.ofNat 32 12) = off (State.addr B) (X + 12) := by
    rw [add_ofNat_assoc]; exact h.addr (by omega_using [hXZ])
  have aP := h.addr (d := sP) (by simp only [sP, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega_using [hz])
  have r0 : InRegions (s.rd ++ s.wr) (off (State.addr B) X) 4 := h.read (by omega_using [hXZ])
  have r4 : InRegions (s.rd ++ s.wr) (off (State.addr B) (X + 4)) 4 := h.read (by omega_using [hXZ])
  have r8 : InRegions (s.rd ++ s.wr) (off (State.addr B) (X + 8)) 4 := h.read (by omega_using [hXZ])
  have r12 : InRegions (s.rd ++ s.wr) (off (State.addr B) (X + 12)) 4 := h.read (by omega_using [hXZ])
  have rP : InRegions (s.rd ++ s.wr) (off (State.addr B) sP) 4 :=
    h.read (by simp only [sP, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega_using [hz])
  have v0 : s.mem.readW (off (State.addr B) X) 32 = BitVec.ofNat 32 y0 := by rw [← ey0]; exact (ofNat_toNat32 _).symm
  have v4 : s.mem.readW (off (State.addr B) (X + 4)) 32 = BitVec.ofNat 32 y1 := by
    rw [← ey1]; exact (ofNat_toNat32 _).symm
  have v8 : s.mem.readW (off (State.addr B) (X + 8)) 32 = BitVec.ofNat 32 y2 := by
    rw [← ey2]; exact (ofNat_toNat32 _).symm
  have v12 : s.mem.readW (off (State.addr B) (X + 12)) 32 = BitVec.ofNat 32 y3 := by
    rw [← ey3]; exact (ofNat_toNat32 _).symm
  have vP : s.mem.readW (off (State.addr B) sP) 32 = BitVec.ofNat 32 P := by rw [← eP]; exact (ofNat_toNat32 _).symm
  have hy0 : y0 < 2 ^ 32 := ey0 ▸ BitVec.isLt _
  have hy1 : y1 < 2 ^ 32 := ey1 ▸ BitVec.isLt _
  have hy2 : y2 < 2 ^ 32 := ey2 ▸ BitVec.isLt _
  have hy3 : y3 < 2 ^ 32 := ey3 ▸ BitVec.isLt _
  have hP : P < 2 ^ 32 := eP ▸ BitVec.isLt _
  have tn : ∀ {a : Nat}, a < 2 ^ 32 → (BitVec.ofNat 32 a).toNat = a := fun h => by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h
  simp only [topWords, List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r12, .r0, .r11, .lr, .r10, .r2, .r1] (Q := fun v =>
      v.gpr .r12 = B ∧ v.gpr .r0 = BitVec.ofNat 32 y0 ∧ v.gpr .r11 = BitVec.ofNat 32 y1 ∧
      v.gpr .lr = BitVec.ofNat 32 y2 ∧ v.gpr .r10 = BitVec.ofNat 32 y3 ∧ v.gpr .r2 = BitVec.ofNat 32 P ∧
      v.gpr .r1 = BitVec.ofNat 32 y0 ∧ v.mem = s.mem) (by
    krun [h.r8, h10, a0, a4, a8, a12, aP, r0, r4, r8, r12, rP, v0, v4, v8, v12, vP]) (by decide))
    fun v1 ⟨⟨b1, x1, y1', l1, t1, p1, i1, m1⟩, k1⟩ => ?_)
  refine wp_wide fun v2 e2 P2 => ?_
  rw [i1, p1, tn hy0, tn hP] at e2
  obtain ⟨lo2, hi2⟩ := wide_lo_hi (BitVec.isLt _) e2
  have g := fun (r : Reg) (hr : r ∉ VG.Proof.Bignum.Arm.clobbers) => P2.regs r hr
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r0, .r1] (Q := fun v =>
      v.gpr .r0 = v2.gpr .r4 ∧ v.gpr .r1 = BitVec.ofNat 32 y1 ∧ v.mem = v2.mem) (by
    krun [g .r11 (by decide), y1']) (by decide)) fun v3 ⟨⟨x3, i3, m3⟩, k3⟩ => ?_)
  refine wp_wide fun v4 e4 P4 => ?_
  rw [i3, tn hy1, (k3.gpr _ (by decide)).trans ((P2.regs _ (by decide)).trans p1), tn hP] at e4
  obtain ⟨lo4, hi4⟩ := wide_lo_hi (BitVec.isLt _) e4
  have wU0 : InRegions v4.wr (off (State.addr B) sU0) 4 := by
    rw [P4.wr, k3.wr, P2.wr, k1.wr]; exact h.write (by simp only [sU0, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega_using [hz])
  have aU0 := h.addr (d := sU0) (by simp only [sU0, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega_using [hz])
  have b4 : v4.gpr .r12 = B := (P4.regs _ (by decide)).trans ((k3.gpr _ (by decide)).trans ((P2.regs _ (by decide)).trans b1))
  have l4 : v4.gpr .lr = BitVec.ofNat 32 y2 :=
    (P4.regs _ (by decide)).trans ((k3.gpr _ (by decide)).trans ((P2.regs _ (by decide)).trans l1))
  have x4 : v4.gpr .r0 = v2.gpr .r4 := (P4.regs _ (by decide)).trans x3
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r3, .r0, .r1] (Q := fun v =>
      v.mem = v4.mem.writeW (off (State.addr B) sU0) (v4.gpr .r3 + v2.gpr .r4) ∧ v.gpr .r0 = v4.gpr .r4 ∧
      v.gpr .r1 = BitVec.ofNat 32 y2) (by
    krun [b4, l4, x4, aU0, wU0]) (by decide)) fun v5 ⟨⟨m5, x5, i5⟩, k5⟩ => ?_)
  have p5 : v5.gpr .r2 = BitVec.ofNat 32 P :=
    (k5.gpr _ (by decide)).trans ((P4.regs _ (by decide)).trans ((k3.gpr _ (by decide)).trans
      ((P2.regs _ (by decide)).trans p1)))
  refine wp_wide fun v6 e6 P6 => ?_
  rw [i5, p5, tn hy2, tn hP] at e6
  obtain ⟨lo6, hi6⟩ := wide_lo_hi (BitVec.isLt _) e6
  have x6 : v6.gpr .r0 = v4.gpr .r4 := (P6.regs _ (by decide)).trans x5
  have t6 : v6.gpr .r10 = BitVec.ofNat 32 y3 :=
    (P6.regs _ (by decide)).trans ((k5.gpr _ (by decide)).trans ((P4.regs _ (by decide)).trans
      ((k3.gpr _ (by decide)).trans ((P2.regs _ (by decide)).trans t1))))
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r11, .r0, .r1] (Q := fun v =>
      v.gpr .r11 = v6.gpr .r3 + v4.gpr .r4 ∧ v.gpr .r0 = v6.gpr .r4 ∧ v.gpr .r1 = BitVec.ofNat 32 y3 ∧
      v.mem = v6.mem) (by
    krun [x6, t6]) (by decide)) fun v7 ⟨⟨u7, x7, i7, m7⟩, k7⟩ => ?_)
  have p7 : v7.gpr .r2 = BitVec.ofNat 32 P := (k7.gpr _ (by decide)).trans ((P6.regs _ (by decide)).trans p5)
  refine wp_wide fun v8 e8 P8 => ?_
  rw [i7, p7, tn hy3, tn hP] at e8
  obtain ⟨lo8, hi8⟩ := wide_lo_hi (BitVec.isLt _) e8
  have x8 : v8.gpr .r0 = v6.gpr .r4 := (P8.regs _ (by decide)).trans x7
  have b8 : v8.gpr .r12 = B :=
    (P8.regs _ (by decide)).trans ((k7.gpr _ (by decide)).trans ((P6.regs _ (by decide)).trans
      ((k5.gpr _ (by decide)).trans b4)))
  have aU2 := h.addr (d := sU2) (by simp only [sU2, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega_using [hz])
  have wU2 : InRegions v8.wr (off (State.addr B) sU2) 4 := by
    rw [P8.wr, k7.wr, P6.wr, k5.wr, P4.wr, k3.wr, P2.wr, k1.wr]
    exact h.write (by simp only [sU2, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega_using [hz])
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r3] (Q := fun v =>
      v.mem = v8.mem.writeW (off (State.addr B) sU2) (v8.gpr .r3 + v6.gpr .r4) ∧ v.gpr .r11 = v8.gpr .r11 ∧
      v.gpr .r12 = B) (by
    krun [x8, b8, aU2, wU2]) (by decide)) fun v9 ⟨⟨m9, u9, b9⟩, k9⟩ => ?_)
  refine k v9 ?_ ?_ b9 ?_
  · rw [m9, P8.mem, m7, P6.mem, m5, P4.mem, m3, P2.mem, m1]
    congr 2
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, lo4, hi2, BitVec.toNat_ofNat]; simp only [wordP]; omega_using []
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, lo8, hi6, BitVec.toNat_ofNat]; simp only [wordP]; omega_using []
  · rw [u9, P8.regs _ (by decide), u7]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, lo6, hi4, BitVec.toNat_ofNat]; simp only [wordP]; omega_using []
  · exact (((k1.mono (by decide)).trans (Preserves.toRest P2 |>.mono (by decide))).trans
      ((k3.mono (by decide)).trans (Preserves.toRest P4 |>.mono (by decide)))).trans
      ((((k5.mono (by decide)).trans (Preserves.toRest P6 |>.mono (by decide))).trans
        ((k7.mono (by decide)).trans (Preserves.toRest P8 |>.mono (by decide)))).trans (k9.mono (by decide)))

end VG.Proof.Rsa.Arm.KeyDiv
