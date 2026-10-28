module

public import VerifiedGarbage.Proof.Seed.RISCV64.Round
public import VerifiedGarbage.Proof.Seed.Rounds
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Sixteen rounds on RISC-V

As on PPC64LE (`Proof/Seed/PPC64LE/Rounds.lean`): `rounds_ok`: `rounds d`
does sixteen rounds on every lane, with round `j + 1`'s key at
`a0 + j * step` (`kp`), and moves `a0` back.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64 VG.Proof.Seed
open VG.Impl.Aes.RISCV64 (sb)

/-- Where round `j + 1`'s key is, from `p`. -/
def kp (d : Spec.Seed.Direction) (p : Addr) (j : Nat) : Addr := p + BitVec.ofNat 64 j * stepW d

theorem kp_succ (d : Spec.Seed.Direction) (p : Addr) (j : Nat) : kp d p j + stepW d = kp d p (j + 1) := by
  simp only [kp, BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]

theorem exec_keyBack (d : Spec.Seed.Direction) (s : State) :
    exec (keyBack d) s = some (s.write .a0 (s.gpr .a0 - BitVec.ofNat 64 16 * stepW d)) := by
  cases d
  · rw [keyBack, exec_addi (by decide), show (-128 : Int) = -((128 : Nat) : Int) from rfl,
      RISCV64.Steps.add_ofInt_neg]; rfl
  · rw [keyBack, exec_addi (by decide), show BitVec.ofNat 64 16 * stepW .decrypt =
      -BitVec.ofNat 64 128 by decide, BitVec.sub_neg]; rfl

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
  quads : ∀ b < 16, quad s b = roundsN (keysAt d s₀.mem (s₀.gpr .a0)) (16 - m) (quad s₀ b)
  room : Room s
  masks : Masks s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  a0 : s.gpr .a0 = kp d (s₀.gpr .a0) (16 - m)
  a4 : s.gpr .a4 = BitVec.ofNat 64 m
  regs : ∀ r ∈ [Reg.ra, .a1, .a2, .a3, .a5], s.gpr r = s₀.gpr r
  frame : Frame [workR s₀] s₀.mem s.mem

theorem contains_prefix {a : Addr} {k n : Nat} (h : k ≤ n) : (⟨a, n⟩ : Region).Contains a k := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

theorem a4_sub (m : Nat) (h : 1 ≤ m) (h' : m ≤ 16) :
    BitVec.ofNat 64 m - 1 = BitVec.ofNat 64 (m - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega_arith

theorem rounds_ok (d : Spec.Seed.Direction) {s : State} (h : Room s) (hm : Masks s)
    (hk : KeysOk d s (s.gpr .a0)) :
    WP isa (rounds d) s (fun s' =>
      (∀ b < 16, quad s' b = roundsN (keysAt d s.mem (s.gpr .a0)) 16 (quad s b)) ∧
      Room s' ∧ Masks s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r ∈ [Reg.ra, .a0, .a1, .a2, .a3, .a5], s'.gpr r = s.gpr r) ∧
      Frame [workR s] s.mem s'.mem) := by
  let s1 := s.write .a4 (BitVec.ofNat 64 16)
  have e1 : runBlock isa [.li .a4 16] s = some s1 := by
    simp only [runBlock_cons, exec_li (show imm12 16 by decide), runStep_some, runBlock_nil, s1]
    rfl
  have q1 : ∀ b, quad s1 b = quad s b := fun b => by
    simp only [quad, s1, lv_write _ _ (show ¬ sb = .a4 by decide)]
  refine WP.seq (WP.of_runBlock ⟨s1, e1, ?_⟩)
  refine WP.seq (WP.loop (M := isa) (fun m t => RoundsInv d s m t) ?_ 16 s1 ?_)
  · intro m t inv
    have hi : 16 - m < 16 := by have := inv.le; omega_arith
    obtain ⟨hk0, hk1, hdis⟩ := hk (16 - m) hi
    have hk0' : InRegions (t.rd ++ t.wr) (t.gpr .a0) 4 := by rw [inv.rd, inv.wr, inv.a0]; exact hk0
    have hk1' : InRegions (t.rd ++ t.wr) (t.gpr .a0 + 4) 4 := by rw [inv.rd, inv.wr, inv.a0]; exact hk1
    obtain ⟨t', ht', hq, hroom, hmasks, hrd, hwr, hsp, hr3, hr7, hx1, hx2, hx3, hx5, hxra, hfr⟩ :=
      round_ok d inv.room inv.masks hk0' hk1'
    -- The key, from the original memory.
    have hkey : (t.mem.readW (t.gpr .a0) 32, t.mem.readW (t.gpr .a0 + 4) 32) =
        keysAt d s.mem (s.gpr .a0) (16 - m) := by
      simp only [keysAt, inv.a0]
      have hd : ∀ r ∈ [workR s], Region.Disjoint ⟨kp d (s.gpr .a0) (16 - m), 8⟩ r := by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact hdis.sub_right (Region.sub_prefix (by unfold scratchSlots; omega_arith))
      congr 1
      · exact inv.frame.readW (contains_prefix (by decide)) hd (by decide)
      · rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
        exact inv.frame.readW (Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by omega_arith) (by omega_arith))
          hd (by decide)
    refine WP.of_runBlock ⟨t', ht', ?_⟩
    have hquads : ∀ b < 16, quad t' b = roundsN (keysAt d s.mem (s.gpr .a0)) (16 - (m - 1)) (quad s b) := by
      intro b hb
      rw [hq b hb, hkey, inv.quads b hb, show 16 - (m - 1) = 16 - m + 1 by have := inv.le; omega_arith,
        roundsN_succ]
    have hr7' : t'.gpr .a4 = BitVec.ofNat 64 (m - 1) := by
      rw [hr7, inv.a4, a4_sub m inv.le.1 inv.le.2]
    have hregs : ∀ r ∈ [Reg.ra, .a1, .a2, .a3, .a5], t'.gpr r = s.gpr r := by
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hxra]; exact inv.regs _ (by simp)
      · rw [hx1]; exact inv.regs _ (by simp)
      · rw [hx2]; exact inv.regs _ (by simp)
      · rw [hx3]; exact inv.regs _ (by simp)
      · rw [hx5]; exact inv.regs _ (by simp)
    have hframe : Frame [workR s] s.mem t'.mem := by
      refine inv.frame.trans ?_
      simpa [workR, show t.gpr sb = s.gpr sb from inv.regs .a5 (by simp)] using hfr
    have hc : isa.eval (.nonzero .a4) t' = some (BitVec.ofNat 64 (m - 1) != 0) := by
      rw [RISCV64.Steps.eval_nonzero, hr7']
    by_cases hm1 : m = 1
    · subst hm1
      left
      refine ⟨by rw [hc]; rfl, ?_⟩
      let u := t'.write .a0 (t'.gpr .a0 - BitVec.ofNat 64 16 * stepW d)
      refine WP.of_runBlock ⟨u, by rw [runBlock_cons, exec_keyBack, runStep_some, runBlock_nil], ?_⟩
      have hu5 : u.gpr sb = t'.gpr sb := gpr_write_of_ne _ _ (by decide)
      refine ⟨fun b hb => ?_, room_congr hroom hu5 rfl,
        hmasks.frame hu5 (gpr_write_of_ne _ _ (by decide)) (by rw [mem_write]; exact Frame.refl _ _),
        by rw [rd_write, hrd, inv.rd],
        by rw [wr_write, hwr, inv.wr], by rw [sp_write, hsp, inv.sp], fun r hr => ?_, by rw [mem_write]; exact hframe⟩
      · have : quad u b = quad t' b := by simp only [quad, u, lv_write _ _ (show ¬ sb = .a0 by decide)]
        rw [this, hquads b hb]
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | hr
        · rw [gpr_write_of_ne _ _ (by decide)]; exact hregs _ (by simp)
        · rw [gpr_write_self, hr3, inv.a0, kp_succ, kp_back]
        · rw [gpr_write_of_ne _ _ (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
          exact hregs _ (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; exact .inr hr)
    · right
      refine ⟨?_, m - 1, by omega_arith, ⟨by have := inv.le; omega_arith, hquads, hroom, hmasks,
        by rw [hrd, inv.rd],
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
      · rw [hr3, inv.a0, kp_succ, show 16 - m + 1 = 16 - (m - 1) by have := inv.le; omega_arith]
  · refine ⟨by omega_arith, fun b _ => by rw [q1]; rfl, room_congr h rfl rfl,
      hm.frame (gpr_write_of_ne _ _ (by decide)) (gpr_write_of_ne _ _ (by decide))
        (by simp only [s1, mem_write]; exact Frame.refl _ _), rfl, rfl, rfl,
      by simp [s1, kp, gpr_write], rfl, fun r hr => ?_, Frame.refl _ _⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Seed.RISCV64
