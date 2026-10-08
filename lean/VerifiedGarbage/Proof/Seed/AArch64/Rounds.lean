import VerifiedGarbage.Proof.Seed.AArch64.Round
import VerifiedGarbage.Proof.Seed.Rounds

/-!
# Sixteen rounds on AArch64

`rounds_ok`: `rounds d` does sixteen rounds on every lane, with round
`j + 1`'s key at `x0 + j * step` (`kp`), and moves `x0` back.
-/

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64 VG.Proof.Seed

/-- Where round `j + 1`'s key is, from `p`. -/
def kp (d : Spec.Seed.Direction) (p : Addr) (j : Nat) : Addr := p + BitVec.ofNat 64 j * stepW d

theorem kp_succ (d : Spec.Seed.Direction) (p : Addr) (j : Nat) : kp d p j + stepW d = kp d p (j + 1) := by
  simp only [kp, BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]

theorem exec_keyBack (d : Spec.Seed.Direction) (s : State) :
    exec (keyBack d) s = some (s.write .x .x0 (s.gpr .x0 - BitVec.ofNat 64 16 * stepW d)) := by
  cases d
  · rw [keyBack, exec_subImm_x (by decide), read_x]; rfl
  · rw [keyBack, exec_addImm_x (by decide), read_x, show BitVec.ofNat 64 16 * stepW .decrypt =
      -BitVec.ofNat 64 128 by decide, BitVec.sub_neg]

theorem kp_back (d : Spec.Seed.Direction) (p : Addr) : kp d p 16 - BitVec.ofNat 64 16 * stepW d = p := by
  rw [kp, BitVec.add_sub_cancel]

/-- The round keys, read from memory `m`. -/
def keysAt (d : Spec.Seed.Direction) (m : Mem) (p : Addr) (j : Nat) : Spec.Seed.Word × Spec.Seed.Word :=
  (m.readW (kp d p j) 32, m.readW (kp d p j + 4) 32)

/-- The keys can be read and are outside the scratch buffer. -/
def KeysOk (d : Spec.Seed.Direction) (s : State) (p : Addr) : Prop :=
  ∀ j < 16, InRegions (s.rd ++ s.wr) (kp d p j) 4 ∧ InRegions (s.rd ++ s.wr) (kp d p j + 4) 4 ∧
    Region.Disjoint ⟨kp d p j, 8⟩ (scratchR s)

/-- After `16 - m` rounds, with `m` left. -/
structure RoundsInv (d : Spec.Seed.Direction) (s₀ : State) (m : Nat) (s : State) : Prop where
  le : 1 ≤ m ∧ m ≤ 16
  quads : ∀ b < 16, quad s b = roundsN (keysAt d s₀.mem (s₀.gpr .x0)) (16 - m) (quad s₀ b)
  room : Room s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = kp d (s₀.gpr .x0) (16 - m)
  x4 : s.gpr .x4 = BitVec.ofNat 64 m
  regs : ∀ r ∈ [Reg.x1, .x2, .x5], s.gpr r = s₀.gpr r
  frame : Frame [workR s₀] s₀.mem s.mem

theorem contains_prefix {a : Addr} {k n : Nat} (h : k ≤ n) : (⟨a, n⟩ : Region).Contains a k := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

theorem x4_sub (m : Nat) (h : 1 ≤ m) (h' : m ≤ 16) :
    BitVec.ofNat 64 m - 1 = BitVec.ofNat 64 (m - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem rounds_ok (d : Spec.Seed.Direction) {s : State} (h : Room s) (hk : KeysOk d s (s.gpr .x0)) :
    WP isa (rounds d) s (fun s' =>
      (∀ b < 16, quad s' b = roundsN (keysAt d s.mem (s.gpr .x0)) 16 (quad s b)) ∧
      Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r ∈ [Reg.x0, .x1, .x2, .x5], s'.gpr r = s.gpr r) ∧
      Frame [workR s] s.mem s'.mem) := by
  let s1 := s.write .x .x4 ((16 : BitVec 16).setWidth 64 <<< (16 * 0))
  have e1 : runBlock isa [.movz .x .x4 16 0] s = some s1 := rfl
  have q1 : ∀ b, quad s1 b = quad s b := fun b => by
    simp only [quad, s1, lv_write _ _ _ (show ¬ Reg.x5 = .x4 by decide)]
  refine WP.seq (WP.of_runBlock ⟨s1, e1, ?_⟩)
  refine WP.seq (WP.loop (M := isa) (fun m t => RoundsInv d s m t) ?_ 16 s1 ?_)
  · intro m t inv
    have hi : 16 - m < 16 := by have := inv.le; omega
    obtain ⟨hk0, hk1, hdis⟩ := hk (16 - m) hi
    have hk0' : InRegions (t.rd ++ t.wr) (t.gpr .x0) 4 := by rw [inv.rd, inv.wr, inv.x0]; exact hk0
    have hk1' : InRegions (t.rd ++ t.wr) (t.gpr .x0 + 4) 4 := by rw [inv.rd, inv.wr, inv.x0]; exact hk1
    obtain ⟨t', ht', hq, hroom, hrd, hwr, hsp, hx0, hx4, hx1, hx2, hx5, hfr⟩ :=
      round_ok d inv.room hk0' hk1'
    -- The key, from the original memory.
    have hkey : (t.mem.readW (t.gpr .x0) 32, t.mem.readW (t.gpr .x0 + 4) 32) =
        keysAt d s.mem (s.gpr .x0) (16 - m) := by
      simp only [keysAt, inv.x0]
      have hd : ∀ r ∈ [workR s], Region.Disjoint ⟨kp d (s.gpr .x0) (16 - m), 8⟩ r := by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact hdis.sub_right (Region.sub_prefix (by unfold scratchSlots; omega))
      congr 1
      · exact inv.frame.readW (contains_prefix (by decide)) hd (by decide)
      · rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
        exact inv.frame.readW (Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by omega) (by omega))
          hd (by decide)
    refine WP.of_runBlock ⟨t', ht', ?_⟩
    have hquads : ∀ b < 16, quad t' b = roundsN (keysAt d s.mem (s.gpr .x0)) (16 - (m - 1)) (quad s b) := by
      intro b hb
      rw [hq b hb, hkey, inv.quads b hb, show 16 - (m - 1) = 16 - m + 1 by have := inv.le; omega,
        roundsN_succ]
    have hx4' : t'.gpr .x4 = BitVec.ofNat 64 (m - 1) := by
      rw [hx4, inv.x4, x4_sub m inv.le.1 inv.le.2]
    have hregs : ∀ r ∈ [Reg.x1, .x2, .x5], t'.gpr r = s.gpr r := by
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hx1]; exact inv.regs _ (by simp)
      · rw [hx2]; exact inv.regs _ (by simp)
      · rw [hx5]; exact inv.regs _ (by simp)
    have hframe : Frame [workR s] s.mem t'.mem := by
      refine inv.frame.trans ?_
      simpa [workR, inv.regs .x5 (by simp)] using hfr
    have hc : isa.eval (.nonzero .x .x4) t' = some (BitVec.ofNat 64 (m - 1) != 0) := by
      show some (t'.read .x .x4 != 0) = _
      rw [read_x, hx4']
    by_cases hm1 : m = 1
    · subst hm1
      left
      refine ⟨by rw [hc]; rfl, ?_⟩
      let u := t'.write .x .x0 (t'.gpr .x0 - BitVec.ofNat 64 16 * stepW d)
      refine WP.of_runBlock ⟨u, by rw [runBlock_cons, exec_keyBack, runStep_some, runBlock_nil], ?_⟩
      have hu5 : u.gpr .x5 = t'.gpr .x5 := gpr_write_of_ne _ _ _ (by decide)
      refine ⟨fun b hb => ?_, room_congr hroom hu5 rfl, by rw [rd_write, hrd, inv.rd],
        by rw [wr_write, hwr, inv.wr], by rw [sp_write, hsp, inv.sp], fun r hr => ?_, by rw [mem_write]; exact hframe⟩
      · have : quad u b = quad t' b := by simp only [quad, u, lv_write _ _ _ (show ¬ Reg.x5 = .x0 by decide)]
        rw [this, hquads b hb]
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | hr
        · rw [gpr_write_self, BitVec.setWidth_eq, hx0, inv.x0, kp_succ, kp_back]
        · rw [gpr_write_of_ne _ _ _ (by rcases hr with rfl | rfl | rfl <;> decide)]
          exact hregs _ (by simpa using hr)
    · right
      refine ⟨?_, m - 1, by omega, ⟨by have := inv.le; omega, hquads, hroom, by rw [hrd, inv.rd],
        by rw [hwr, inv.wr], by rw [hsp, inv.sp], ?_, hx4', hregs, hframe⟩⟩
      · rw [hc]
        have : (BitVec.ofNat 64 (m - 1) != 0) = true := by
          simp only [bne_iff_ne, ne_eq]
          intro h0
          have hm2 : 2 ≤ m := by have := inv.le; omega
          have hm16 := inv.le.2
          have := congrArg BitVec.toNat h0
          rw [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mod_eq_of_lt (by omega)] at this
          omega
        rw [this]
      · rw [hx0, inv.x0, kp_succ, show 16 - m + 1 = 16 - (m - 1) by have := inv.le; omega]
  · refine ⟨by omega, fun b _ => by rw [q1]; rfl, room_congr h rfl rfl, rfl, rfl, rfl,
      by simp [s1, kp, gpr_write], rfl, fun r hr => ?_, Frame.refl _ _⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rfl

end VG.Proof.Seed.AArch64
