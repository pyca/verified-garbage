import VerifiedGarbage.Proof.Ed448.AArch64.BaseStep

/-!
# Ed448 base-point multiplication on AArch64: the loop over the bits

After the bits above `n` (counting down from 456), `R` (slots 0–2) is the
reference ladder's point after those bits (`Proof.Ed448.ladder`): each
iteration doubles it and adds `B` when the next bit is set. `B` (slots 8–10)
stays the base point and slot 11 `d`.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off Outside2 workRegs)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv setCounter_ok)
open VG.Impl.X448.AArch64 (BITS ACC)

/-- One bit: the ladder's point after the bits above `t`, then after bit `t`. -/
theorem ladder_step {e : Fin 22 → Spec.X448.Fe} {k t : Nat} (ht : t < 456)
    (hr : pt e 0 1 2 = ladder k (456 - (t + 1))) (hq : pt e 8 9 10 = Spec.Ed448.basePoint)
    (hd : e 11 = Spec.Ed448.d) :
    pt (stepEnv (decide ((k >>> t) &&& 1 = 1)) e) 0 1 2 = ladder k (456 - t) := by
  rw [stepEnv_pt, hd, hq, addWith_d, hr, ladder_bit k ht]
  rfl

/-- The loop's invariant, after the bits above `n` of `k`. -/
structure MInv (base : Addr) (k : Nat) (s₀ : State) (n : Nat) (s : State) : Prop where
  scr : Scr s base
  bounded : BoundedEnv s.mem base
  x19 : s.gpr .x19 = BitVec.ofNat 64 n
  regs : Keeps (.x19 :: workRegs) s₀ s
  mem : Outside2 base 64 2816 ACC 512 s₀.mem s.mem
  q : pt (E s.mem base) 8 9 10 = Spec.Ed448.basePoint
  d : E s.mem base 11 = Spec.Ed448.d
  rep : pt (E s.mem base) 0 1 2 = ladder k (456 - n)

theorem loop_ok {s₀ : State} {base : Addr} {k : Nat}
    (hbits : ∀ t < 456, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 456 → MInv base k s₀ n s →
      WP isa (.loop step (.nonzero .x .x19)) s fun s' => MInv base k s₀ 0 s' := by
  intro n s hn1 hn2 hi
  refine WP.loop (M := isa) (body := step) (c := .nonzero .x .x19)
    (Q := fun s' => MInv base k s₀ 0 s')
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 456 ∧ MInv base k s₀ m s) ?_ n s ⟨hn1, hn2, hi⟩
  rintro m s ⟨hm1, hm2, hi⟩
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  have hb2 : (k >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1) := by
    have hofs : VG.Proof.X448.AArch64.ofs base (off base (BITS + t)) = BITS + t :=
      Mem.sub_ofNat_toNat base (by simp only [BITS]; omega)
    rw [hi.mem _ (by rw [hofs]; simp only [BITS]; omega) (by rw [hofs]; simp only [BITS, ACC]; omega)]
    exact hbits t (by omega)
  refine WP.mono (step_ok hi.scr hi.bounded (by omega) hi.x19 hb2 hbit)
    fun s' ⟨c', z', k', b', o', e'⟩ => ?_
  have inv : MInv base k s₀ t s' := by
    refine ⟨hi.scr.of_keeps k' (by decide), b', c', hi.regs.trans k', hi.mem.trans o', ?_, ?_, ?_⟩
    · rw [e', stepEnv_q]; exact hi.q
    · rw [e', stepEnv_d]; exact hi.d
    · rw [e']; exact ladder_step (by omega) hi.rep hi.q hi.d
  simp only [eval, State.read, BitVec.setWidth_eq, bne, z']
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h
    exact .inl ⟨rfl, inv⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬t = 0), Bool.not_false], t, by omega,
      h, by omega, inv⟩

/-- The counter set to 456, then the loop. -/
theorem mulLoop_ok {s : State} {base : Addr} {k : Nat}
    (hbits : ∀ t < 456, s.mem (off base (BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1))
    (hs : Scr s base) (hb : BoundedEnv s.mem base) (hq : pt (E s.mem base) 8 9 10 = Spec.Ed448.basePoint)
    (hd : E s.mem base 11 = Spec.Ed448.d) (hr : pt (E s.mem base) 0 1 2 = Spec.Ed448.identity) :
    WP isa mulLoop s fun s' => MInv base k s 0 s' := by
  rw [mulLoop, WP.seq_iff]
  refine WP.mono (setCounter_ok s 456 (by decide)) fun s₁ ⟨c₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  refine loop_ok (s₀ := s) hbits 456 s₁ (by decide) (by decide) ⟨?_, m₁ ▸ hb, c₁, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(g₁ _ (by decide)).trans hs.x3, (g₁ _ (by decide)).trans hs.mask, wr₁ ▸ hs.wr, hs.nowrap⟩
  · exact ⟨fun r hr => g₁ r (fun h => hr (h ▸ List.mem_cons_self)), rd₁, wr₁⟩
  · rw [m₁]; exact Outside2.refl _ _ _ _ _ _
  · rw [m₁]; exact hq
  · rw [m₁]; exact hd
  · rw [m₁, Nat.sub_self]; exact hr

end VG.Proof.Ed448.AArch64
