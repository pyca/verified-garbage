import VerifiedGarbage.Proof.Seed.X86_64.Steps
import VerifiedGarbage.Proof.Framework.Bitslice.Sym
import VerifiedGarbage.Proof.Framework.ReadHalves

/-!
# Lanes and slots; exchanging the halves

A lane is half of a 64-bit slot (`lv_slot`), so `g16`'s words are lanes of
`tSlot 0` (`wordQ_lv`). `swap_ok`: `swapHalves` exchanges the arrays of
`L` (`arrSlot 0`, `arrSlot 1`) with those of `R` (`arrSlot 2`, `arrSlot 3`),
checked by evaluating its moves over named words (`Bitslice.names`).
-/

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Seed.X86_64

theorem lv_slot (s : State) (k b : Nat) :
    lv s k b = ((slotW s (k + b / 2)) >>> (32 * (b % 2))).setWidth 32 := by
  have ha : laneA s k b = wordAddr (s.gpr .r9) (k + b / 2) + BitVec.ofNat 64 (4 * (b % 2)) := by
    simp only [laneA, wordAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2; omega
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · rw [lv, ha, h, show wordAddr (s.gpr .r9) (k + b / 2) + BitVec.ofNat 64 (4 * 0) =
      wordAddr (s.gpr .r9) (k + b / 2) by simp, Mem.readW_lo32 (a := wordAddr (s.gpr .r9) (k + b / 2)) (v := slotW s (k + b / 2)) rfl]
    simp
  · rw [lv, ha, h, show 4 * 1 = 4 from rfl, Mem.readW_hi32 (a := wordAddr (s.gpr .r9) (k + b / 2)) (v := slotW s (k + b / 2)) rfl]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi]

theorem wordQ_lv (s : State) (w : Nat) :
    Proof.Seed.wordQ (fun i => slotW s (tSlot i)) w = lv s (tSlot 0) w := by
  rw [lv_slot]; rfl

/-- The slots `swapHalves` moves, and those below them. -/
def swapCfg : Cfg := { base := .r9, slots := 125, ext := .r9, exts := 0 }

def swapEnv : Env Nat := { reg := fun _ => none, slot := fun k => if k < 125 then some k else none }

def swapPost (e : Env Nat) : Bool :=
  (List.range 16).all (fun k => e.slot (93 + k) == some (109 + k) && e.slot (109 + k) == some (93 + k)) &&
    (List.range 93).all fun j => e.slot j == some j

theorem swap_check : check (names 64) swapCfg (fun _ => none) swapHalves swapEnv swapPost = true := by
  decide +kernel

theorem ok_of_room {s : State} (h : Room s) {c : Cfg} (hb : c.base = .r9) (hs : c.slots ≤ 132)
    (he : c.exts = 0) : Ok c s :=
  ⟨fun k hk => ⟨_, h, by
      rw [hb]; exact Offset.contains_base _ (by unfold scratchSlots; omega) (by omega)⟩,
    fun k hk => by omega, by omega, fun _ _ j hj => by omega⟩

theorem swap_writes (r : Reg) (h1 : r ≠ .rax) (h2 : r ≠ .rcx) :
    (swapHalves.all fun i => i.dst != some r) = true := by
  cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | decide

theorem swap_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa swapHalves s = some s' ∧
      (∀ w < 4, ∀ b < 16, lv s' (arrSlot w) b = lv s (arrSlot ((w + 2) % 4)) b) ∧
      (∀ j < 93, slotW s' j = slotW s j) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ Frame [workR s] s.mem s'.mem := by
  have hok : Ok swapCfg s := ok_of_room h rfl (by decide) rfl
  have hrel : Rel (NameRel (fun k => slotW s k)) swapCfg (fun _ => none) swapEnv s := by
    refine ⟨fun _ _ h => (by cases h), fun k a hk h => ?_, fun _ _ hk => (by cases hk)⟩
    simp only [swapEnv, show k < 125 from hk, ite_true, Option.some.injEq] at h
    subst h; rfl
  obtain ⟨e, he, hp⟩ := of_check _ _ _ swap_check
  obtain ⟨s', hs', p⟩ := run (names_sound _) hok hrel he
  simp only [swapPost, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hp
  have hr9 : s'.gpr .r9 = s.gpr .r9 := p.base
  have hsl : ∀ k a, k < 125 → e.slot k = some a → slotW s' k = slotW s a := by
    intro k a hk hka
    exact p.rel.slot k a hk hka
  refine ⟨s', hs', fun w hw b hb => ?_, fun j hj => hsl j j (by omega) (hp.2 j hj), p.rd, p.wr,
    fun r h1 h2 => p.other r ?_, ?_⟩
  · rw [lv_slot, lv_slot]
    congr 2
    rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega) with rfl | rfl | rfl | rfl
    · exact hsl _ _ (by simp [arrSlot]; omega) ((hp.1 (b / 2) (by omega)).1)
    · rw [show arrSlot 1 + b / 2 = 93 + (8 + b / 2) by simp [arrSlot]; omega,
        show arrSlot ((1 + 2) % 4) + b / 2 = 109 + (8 + b / 2) by simp [arrSlot]; omega]
      exact hsl _ _ (by omega) ((hp.1 (8 + b / 2) (by omega)).1)
    · rw [show arrSlot 2 + b / 2 = 109 + b / 2 by simp [arrSlot],
        show arrSlot ((2 + 2) % 4) + b / 2 = 93 + b / 2 by simp [arrSlot]]
      exact hsl _ _ (by omega) ((hp.1 (b / 2) (by omega)).2)
    · rw [show arrSlot 3 + b / 2 = 109 + (8 + b / 2) by simp [arrSlot]; omega,
        show arrSlot ((3 + 2) % 4) + b / 2 = 93 + (8 + b / 2) by simp [arrSlot]; omega]
      exact hsl _ _ (by omega) ((hp.1 (8 + b / 2) (by omega)).2)
  · rw [swap_writes r h1 h2]; decide
  · have := p.frame
    refine this.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s, List.mem_singleton_self _, Region.sub_prefix (by simp [swapCfg])⟩

end VG.Proof.Seed.X86_64
