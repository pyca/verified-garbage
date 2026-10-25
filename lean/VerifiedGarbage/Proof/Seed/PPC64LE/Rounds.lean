module

public import VerifiedGarbage.Proof.Seed.PPC64LE.Round
public import VerifiedGarbage.Proof.Seed.Rounds
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Sixteen rounds on PPC64LE

`rounds_ok`: `rounds d` does sixteen rounds on every lane, with round
`j + 1`'s key at `r3 + j * step` (`kp`), and moves `r3` back.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE VG.Proof.Seed

/-- Where round `j + 1`'s key is, from `p`. -/
def kp (d : Spec.Seed.Direction) (p : Addr) (j : Nat) : Addr := p + BitVec.ofNat 64 j * stepW d

theorem kp_succ (d : Spec.Seed.Direction) (p : Addr) (j : Nat) : kp d p j + stepW d = kp d p (j + 1) := by
  simp only [kp, BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]

theorem exec_keyBack (d : Spec.Seed.Direction) (s : State) :
    exec (keyBack d) s = some (s.write .r3 (s.gpr .r3 - BitVec.ofNat 64 16 * stepW d)) := by
  cases d
  · rw [keyBack, exec_subi' (n := .r3) (by decide)]; rfl
  · rw [keyBack, exec_addi' (n := .r3) (by decide), show BitVec.ofNat 64 16 * stepW .decrypt =
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
  quads : ∀ b < 16, quad s b = roundsN (keysAt d s₀.mem (s₀.gpr .r3)) (16 - m) (quad s₀ b)
  room : Room s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r3 : s.gpr .r3 = kp d (s₀.gpr .r3) (16 - m)
  r7 : s.gpr .r7 = BitVec.ofNat 64 m
  regs : ∀ r ∈ [Reg.r2, .r4, .r5, .r6, .r8], s.gpr r = s₀.gpr r
  frame : Frame [workR s₀] s₀.mem s.mem

theorem contains_prefix {a : Addr} {k n : Nat} (h : k ≤ n) : (⟨a, n⟩ : Region).Contains a k := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

theorem r7_sub (m : Nat) (h : 1 ≤ m) (h' : m ≤ 16) :
    BitVec.ofNat 64 m - 1 = BitVec.ofNat 64 (m - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega_arith

theorem rounds_ok (d : Spec.Seed.Direction) {s : State} (h : Room s) (hk : KeysOk d s (s.gpr .r3)) :
    WP isa (rounds d) s (fun s' =>
      (∀ b < 16, quad s' b = roundsN (keysAt d s.mem (s.gpr .r3)) 16 (quad s b)) ∧
      Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r ∈ [Reg.r2, .r3, .r4, .r5, .r6, .r8], s'.gpr r = s.gpr r) ∧
      Frame [workR s] s.mem s'.mem) := by
  let s1 := s.write .r7 (BitVec.ofNat 64 16)
  have e1 : runBlock isa [.li .r7 16] s = some s1 := by
    simp only [runBlock_cons, exec_li (show 16 < 2 ^ 15 by decide), runStep_some, runBlock_nil, s1]
  have q1 : ∀ b, quad s1 b = quad s b := fun b => by
    simp only [quad, s1, lv_write _ _ (show ¬ Reg.r8 = .r7 by decide)]
  refine WP.seq (WP.of_runBlock ⟨s1, e1, ?_⟩)
  refine WP.seq (WP.loop (M := isa) (fun m t => RoundsInv d s m t) ?_ 16 s1 ?_)
  · intro m t inv
    have hi : 16 - m < 16 := by have := inv.le; omega_arith
    obtain ⟨hk0, hk1, hdis⟩ := hk (16 - m) hi
    have hk0' : InRegions (t.rd ++ t.wr) (t.gpr .r3) 4 := by rw [inv.rd, inv.wr, inv.r3]; exact hk0
    have hk1' : InRegions (t.rd ++ t.wr) (t.gpr .r3 + 4) 4 := by rw [inv.rd, inv.wr, inv.r3]; exact hk1
    obtain ⟨t', ht', hq, hroom, hrd, hwr, hsp, hr3, hr7, hx1, hx2, hx0, hx6, hx5, hfr⟩ :=
      round_ok d inv.room hk0' hk1'
    -- The key, from the original memory.
    have hkey : (t.mem.readW (t.gpr .r3) 32, t.mem.readW (t.gpr .r3 + 4) 32) =
        keysAt d s.mem (s.gpr .r3) (16 - m) := by
      simp only [keysAt, inv.r3]
      have hd : ∀ r ∈ [workR s], Region.Disjoint ⟨kp d (s.gpr .r3) (16 - m), 8⟩ r := by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact hdis.sub_right (Region.sub_prefix (by unfold scratchSlots; omega_arith))
      congr 1
      · exact inv.frame.readW (contains_prefix (by decide)) hd (by decide)
      · rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
        exact inv.frame.readW (Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by omega_arith) (by omega_arith))
          hd (by decide)
    refine WP.of_runBlock ⟨t', ht', ?_⟩
    have hquads : ∀ b < 16, quad t' b = roundsN (keysAt d s.mem (s.gpr .r3)) (16 - (m - 1)) (quad s b) := by
      intro b hb
      rw [hq b hb, hkey, inv.quads b hb, show 16 - (m - 1) = 16 - m + 1 by have := inv.le; omega_arith,
        roundsN_succ]
    have hr7' : t'.gpr .r7 = BitVec.ofNat 64 (m - 1) := by
      rw [hr7, inv.r7, r7_sub m inv.le.1 inv.le.2]
    have hregs : ∀ r ∈ [Reg.r2, .r4, .r5, .r6, .r8], t'.gpr r = s.gpr r := by
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hx0]; exact inv.regs _ (by simp)
      · rw [hx1]; exact inv.regs _ (by simp)
      · rw [hx2]; exact inv.regs _ (by simp)
      · rw [hx6]; exact inv.regs _ (by simp)
      · rw [hx5]; exact inv.regs _ (by simp)
    have hframe : Frame [workR s] s.mem t'.mem := by
      refine inv.frame.trans ?_
      simpa [workR, inv.regs .r8 (by simp)] using hfr
    have hc : isa.eval (.nonzero .d .r7) t' = some (BitVec.ofNat 64 (m - 1) != 0) := by
      show some (t'.read .d .r7 != 0) = _
      rw [show t'.read .d .r7 = t'.gpr .r7 from BitVec.setWidth_eq _, hr7']
    by_cases hm1 : m = 1
    · subst hm1
      left
      refine ⟨by rw [hc]; rfl, ?_⟩
      let u := t'.write .r3 (t'.gpr .r3 - BitVec.ofNat 64 16 * stepW d)
      refine WP.of_runBlock ⟨u, by rw [runBlock_cons, exec_keyBack, runStep_some, runBlock_nil], ?_⟩
      have hu5 : u.gpr .r8 = t'.gpr .r8 := gpr_write_of_ne _ _ (by decide)
      refine ⟨fun b hb => ?_, room_congr hroom hu5 rfl, by rw [rd_write, hrd, inv.rd],
        by rw [wr_write, hwr, inv.wr], by rw [sp_write, hsp, inv.sp], fun r hr => ?_, by rw [mem_write]; exact hframe⟩
      · have : quad u b = quad t' b := by simp only [quad, u, lv_write _ _ (show ¬ Reg.r8 = .r3 by decide)]
        rw [this, hquads b hb]
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | hr
        · rw [gpr_write_of_ne _ _ (by decide)]; exact hregs _ (by simp)
        · rw [gpr_write_self, hr3, inv.r3, kp_succ, kp_back]
        · rw [gpr_write_of_ne _ _ (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
          exact hregs _ (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; exact .inr hr)
    · right
      refine ⟨?_, m - 1, by omega_arith, ⟨by have := inv.le; omega_arith, hquads, hroom, by rw [hrd, inv.rd],
        by rw [hwr, inv.wr], by rw [hsp, inv.sp], ?_, hr7', hregs, hframe⟩⟩
      · rw [hc]
        have : (BitVec.ofNat 64 (m - 1) != 0) = true := by
          simp only [bne_iff_ne, ne_eq]
          intro h0
          have hm2 : 2 ≤ m := by have := inv.le; omega_arith
          have hm16 := inv.le.2
          have := congrArg BitVec.toNat h0
          rw [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mod_eq_of_lt (by omega_arith)] at this
          omega_arith
        rw [this]
      · rw [hr3, inv.r3, kp_succ, show 16 - m + 1 = 16 - (m - 1) by have := inv.le; omega_arith]
  · refine ⟨by omega_arith, fun b _ => by rw [q1]; rfl, room_congr h rfl rfl, rfl, rfl, rfl,
      by simp [s1, kp, gpr_write], rfl, fun r hr => ?_, Frame.refl _ _⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Seed.PPC64LE
