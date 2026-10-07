import VerifiedGarbage.Proof.Mont.Arm.Ops
import VerifiedGarbage.Proof.Weierstrass.Unch

/-!
# Saving and restoring registers in the working space, on 32-bit ARM

`strs_ok` stores registers at offsets of the working space (apart from each
other), and `ldrs_ok` loads them back; `Unch.readW32` reads a word that a
change apart from it kept.
-/

namespace VG.Proof.Weierstrass.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Proof.Mont.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_ldr wp_str)

theorem Outs.unch {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m') :
    VG.Proof.Weierstrass.Unch base rs m m' := h

/-- A number apart from every range that changed. -/
theorem Outs.wordsVal {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    {d k : Nat} (hd : ∀ r ∈ rs, d + 8 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 8 * k ≤ 2 ^ 64) :
    VG.Proof.Mont.wordsVal m' base d k = VG.Proof.Mont.wordsVal m base d k := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  exact h.val32 (fun r hr => by have := hd r hr; omega) (by omega)

/-- A 32-bit word apart from the ranges. -/
theorem Unch.readW32 {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    {d : Nat} (hd : ∀ w ∈ W, d + 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  (Mem.readW_congr fun i hi => (h _ fun w hw' => by
    rw [ofs_off base (by omega)]; have := hd w hw'; omega).symm).symm

/-- Stores of registers at offsets of the working space, apart from each other. -/
theorem strs_ok {s : State} {base : Addr} {sz : Nat} (hs : Scr s base sz) :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, p.2 + 4 ≤ sz) →
    l.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) →
    WP isa (.block (l.map fun p => .str p.1 wb p.2)) s fun s' =>
      Rest [] s s' ∧ Outs base (l.map fun p => (p.2, 4)) s.mem s'.mem ∧
      ∀ p ∈ l, s'.mem.readW (off base p.2) 32 = s.gpr p.1
  | [], _, _ => WP.block_nil ⟨Rest.refl _ _, Outs.refl _ _ _, fun _ h => absurd h List.not_mem_nil⟩
  | p :: l, hl, hp => by
    have hn := hs.nowrap
    have h0 := hl p List.mem_cons_self
    rw [List.pairwise_cons] at hp
    rw [List.map_cons]
    refine wp_str (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.write h0) fun s₁ m₁ => ?_
    have hs₁ := hs.of_rest (m₁.rest []) (by decide)
    refine WP.mono (strs_ok hs₁ l (fun q h => hl q (List.mem_cons_of_mem _ h)) hp.2) fun s' ⟨K, O, V⟩ => ?_
    have O₁ : Outside base p.2 4 s.mem s₁.mem := by rw [m₁.mem]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨(m₁.rest _).trans K, ?_, fun q hq => ?_⟩
    · rw [List.map_cons]
      exact (Outs.of_outside O₁ List.mem_cons_self).trans (O.mono fun r hr => List.mem_cons_of_mem _ hr)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [Unch.readW32 (VG.Proof.Weierstrass.Arm.Outs.unch O) (fun w hw => by
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
          exact hp.1 r hr) (by omega), m₁.mem, Mem.readW_writeW_self32]
      · rw [V q hq, m₁.gpr]

/-- Loads of registers (not `r12`) from offsets of the working space. -/
theorem ldrs_ok {s : State} {base : Addr} {sz : Nat} (hs : Scr s base sz) :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, p.2 + 4 ≤ sz) → (l.map Prod.fst).Nodup → (∀ p ∈ l, p.1 ≠ .r12) →
    WP isa (.block (l.map fun p => .ldr p.1 wb p.2)) s fun s' =>
      s'.mem = s.mem ∧ Rest (l.map Prod.fst) s s' ∧
      ∀ p ∈ l, s'.gpr p.1 = s.mem.readW (off base p.2) 32
  | [], _, _, _ => WP.block_nil ⟨rfl, Rest.refl _ _, fun _ h => absurd h List.not_mem_nil⟩
  | p :: l, hl, hnd, h12 => by
    have hn := hs.nowrap
    have h0 := hl p List.mem_cons_self
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.map_cons]
    refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read h0) fun s₁ u₁ => ?_
    have hs₁ := hs.of_rest (u₁.rest (ws := [p.1]) (by simp)) (by simpa using (h12 p List.mem_cons_self).symm)
    refine WP.mono (ldrs_ok hs₁ l (fun q h => hl q (List.mem_cons_of_mem _ h)) hnd.2
      (fun q h => h12 q (List.mem_cons_of_mem _ h))) fun s' ⟨M, K, V⟩ => ?_
    refine ⟨by rw [M, u₁.mem], ((u₁.rest (by simp)).trans (K.mono fun r hr => by simp [hr])), fun q hq => ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [K.gpr _ hnd.1, u₁.gpr]
    · rw [V q hq, u₁.mem]

end VG.Proof.Weierstrass.Arm
