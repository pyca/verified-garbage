import VerifiedGarbage.Proof.Seed.X86_64.Round
import VerifiedGarbage.Proof.Seed.Rounds

/-!
# Sixteen rounds on x86-64

`rounds_ok`: `rounds d` does sixteen rounds on every lane, with round
`j + 1`'s key at `rdi + j * step` (`kp`), and moves `rdi` back.
-/

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64 VG.Proof.Seed

/-- The step of the key pointer. -/
def stepW (d : Spec.Seed.Direction) : BitVec 64 := (BitVec.ofInt 32 (keyStep d)).signExtend 64

/-- Where round `j + 1`'s key is, from `p`. -/
def kp (d : Spec.Seed.Direction) (p : Addr) (j : Nat) : Addr := p + BitVec.ofNat 64 j * stepW d

theorem kp_succ (d : Spec.Seed.Direction) (p : Addr) (j : Nat) : kp d p j + stepW d = kp d p (j + 1) := by
  simp only [kp, BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]

theorem step16 (d : Spec.Seed.Direction) :
    (BitVec.ofInt 32 (16 * keyStep d)).signExtend 64 = BitVec.ofNat 64 16 * stepW d := by
  cases d <;> decide

theorem kp_back (d : Spec.Seed.Direction) (p : Addr) :
    kp d p 16 - (BitVec.ofInt 32 (16 * keyStep d)).signExtend 64 = p := by
  rw [step16, kp, BitVec.add_sub_cancel]

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
  quads : ∀ b < 16, quad s b = roundsN (keysAt d s₀.mem (s₀.gpr .rdi)) (16 - m) (quad s₀ b)
  masks : MasksIn s
  room : Room s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rdi : s.gpr .rdi = kp d (s₀.gpr .rdi) (16 - m)
  r8 : s.gpr .r8 = BitVec.ofNat 64 m
  regs : ∀ r ∈ [Reg.rsi, .rdx, .r9, .rsp], s.gpr r = s₀.gpr r
  frame : Frame [workR s₀] s₀.mem s.mem

theorem contains_prefix {a : Addr} {k n : Nat} (h : k ≤ n) : (⟨a, n⟩ : Region).Contains a k := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

theorem r8_sub (m : Nat) (h : 1 ≤ m) (h' : m ≤ 16) :
    BitVec.ofNat 64 m - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (m - 1) := by
  rw [show (1 : BitVec 32).signExtend 64 = 1 from rfl]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem rounds_ok (d : Spec.Seed.Direction) {s : State} (h : Room s) (hm : MasksIn s)
    (hk : KeysOk d s (s.gpr .rdi)) :
    WP isa (rounds d) s (fun s' =>
      (∀ b < 16, quad s' b = roundsN (keysAt d s.mem (s.gpr .rdi)) 16 (quad s b)) ∧
      MasksIn s' ∧ Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.rdi, .rsi, .rdx, .r9, .rsp], s'.gpr r = s.gpr r) ∧
      Frame [workR s] s.mem s'.mem) := by
  let s1 := s.setReg .r8 ((16 : BitVec 32).signExtend 64)
  have e1 : runBlock isa [.mov .r8 (.imm 16)] s = some s1 := rfl
  have q1 : ∀ b, quad s1 b = quad s b := fun b => by
    simp only [quad, s1, lv_setReg _ _ (show ¬ Reg.r9 = .r8 by decide)]
  refine WP.seq (WP.of_runBlock ⟨s1, e1, ?_⟩)
  refine WP.seq (WP.loop (M := isa) (fun m t => RoundsInv d s m t) ?_ 16 s1 ?_)
  · intro m t inv
    have hi : 16 - m < 16 := by have := inv.le; omega
    obtain ⟨hk0, hk1, hdis⟩ := hk (16 - m) hi
    have hk0' : InRegions (t.rd ++ t.wr) (t.gpr .rdi) 4 := by rw [inv.rd, inv.wr, inv.rdi]; exact hk0
    have hk1' : InRegions (t.rd ++ t.wr) (t.gpr .rdi + 4) 4 := by rw [inv.rd, inv.wr, inv.rdi]; exact hk1
    obtain ⟨t', ht', hq, hm', hroom, hrd, hwr, hrdi, hr8, hzf, hrsi, hrdx, hr9, hrsp, hfr⟩ :=
      round_ok d inv.room inv.masks hk0' hk1'
    -- The key, from the original memory.
    have hkey : (t.mem.readW (t.gpr .rdi) 32, t.mem.readW (t.gpr .rdi + 4) 32) =
        keysAt d s.mem (s.gpr .rdi) (16 - m) := by
      simp only [keysAt, inv.rdi]
      have hd : ∀ r ∈ [workR s], Region.Disjoint ⟨kp d (s.gpr .rdi) (16 - m), 8⟩ r := by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact hdis.sub_right (Region.sub_prefix (by unfold scratchSlots; omega))
      congr 1
      · exact inv.frame.readW (contains_prefix (by decide)) hd (by decide)
      · rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
        exact inv.frame.readW (Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by omega) (by omega))
          hd (by decide)
    refine WP.of_runBlock ⟨t', ht', ?_⟩
    have hquads : ∀ b < 16, quad t' b = roundsN (keysAt d s.mem (s.gpr .rdi)) (16 - (m - 1)) (quad s b) := by
      intro b hb
      rw [hq b hb, hkey, inv.quads b hb, show 16 - (m - 1) = 16 - m + 1 by have := inv.le; omega,
        roundsN_succ]
    have hr8' : t'.gpr .r8 = BitVec.ofNat 64 (m - 1) := by
      rw [hr8, inv.r8, r8_sub m inv.le.1 inv.le.2]
    have hregs : ∀ r ∈ [Reg.rsi, .rdx, .r9, .rsp], t'.gpr r = s.gpr r := by
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hrsi]; exact inv.regs _ (by simp)
      · rw [hrdx]; exact inv.regs _ (by simp)
      · rw [hr9]; exact inv.regs _ (by simp)
      · rw [hrsp]; exact inv.regs _ (by simp)
    have hframe : Frame [workR s] s.mem t'.mem := by
      refine inv.frame.trans ?_
      simpa [workR, inv.regs .r9 (by simp)] using hfr
    by_cases hm1 : m = 1
    · subst hm1
      left
      refine ⟨?_, ?_⟩
      · show t'.zf.map (!·) = some false
        rw [hzf, inv.r8, r8_sub 1 (by omega) (by omega)]; rfl
      · obtain ⟨u, eu, hu, -, hreg, hmem, hrd', hwr'⟩ := exec_sub_imm t' .rdi (BitVec.ofInt 32 (16 * keyStep d))
        refine WP.of_runBlock ⟨u, by rw [runBlock_cons, eu, runStep_some, runBlock_nil], ?_⟩
        have hu9 : u.gpr .r9 = t'.gpr .r9 := hreg _ (by decide)
        refine ⟨fun b hb => ?_, ?_, room_congr hroom hu9 hwr', by rw [hrd', hrd, inv.rd],
          by rw [hwr', hwr, inv.wr], fun r hr => ?_, by rw [hmem]; exact hframe⟩
        · have : quad u b = quad t' b := by simp only [quad, lv, laneA, hmem, hu9]
          rw [this, hquads b hb]
        · intro kv hkv
          show u.mem.readW (Straight.wordAddr (u.gpr .r9) kv.1) 64 = kv.2
          rw [hmem, hu9]; exact hm' kv hkv
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
          rcases hr with rfl | hr
          · rw [hu, hrdi, inv.rdi, show (BitVec.ofInt 32 (keyStep d)).signExtend 64 = stepW d from rfl,
              kp_succ, kp_back]
          · rw [hreg _ (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
            exact hregs _ (by simpa using hr)
    · right
      refine ⟨?_, m - 1, by omega, ⟨by have := inv.le; omega, hquads, hm', hroom, by rw [hrd, inv.rd],
        by rw [hwr, inv.wr], ?_, hr8', hregs, hframe⟩⟩
      · show t'.zf.map (!·) = some true
        rw [hzf, inv.r8, r8_sub m inv.le.1 inv.le.2]
        have : (BitVec.ofNat 64 (m - 1) == 0) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          intro h0
          have hm2 : 2 ≤ m := by have := inv.le; omega
          have hm16 := inv.le.2
          have := congrArg BitVec.toNat h0
          rw [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mod_eq_of_lt (by omega)] at this
          omega
        rw [this]; rfl
      · rw [hrdi, inv.rdi, show (BitVec.ofInt 32 (keyStep d)).signExtend 64 = stepW d from rfl,
          kp_succ, show 16 - m + 1 = 16 - (m - 1) by have := inv.le; omega]
  · refine ⟨by omega, fun b _ => by rw [q1]; rfl, fun kv hkv => hm kv hkv, room_congr h rfl rfl,
      rfl, rfl, by simp [s1, kp, gpr_setReg], rfl, fun r hr => ?_, Frame.refl _ _⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Seed.X86_64
