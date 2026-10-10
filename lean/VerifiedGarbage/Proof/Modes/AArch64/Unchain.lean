import VerifiedGarbage.Proof.Modes.AArch64.Copy
import VerifiedGarbage.Proof.Modes.Unchain

/-!
# Unchaining CBC blocks on AArch64

`unchainBlocks_wp`: the loop `unchainBlocks` turns `c ≥ 1` decrypted blocks
at `x14` (the core's buffer) and their ciphertext blocks at `x15` (the data)
into the plaintext blocks: block `j` at `x15` becomes the decrypted block
`j` XORed with the chaining value (the 16 bytes at `H`, the mode's
`hiSlot` and `loSlot`) for `j = 0`, and with ciphertext block `j - 1`
otherwise; the chaining value becomes the last ciphertext block. Each word's
stores are `Proof.Modes.unchainMem`'s.
-/

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb ldS stS eorR)

variable {c : Core}

theorem unchainWord_eq (c : Core) (w : Nat) : c.unchainWord w =
    ([.ldr .x .x8 .x14 (8 * w)] : List Instr) ++ (([ldS .x9 (c.hiSlot + w)] : List Instr) ++
    (([eorR .x8 .x8 .x9] : List Instr) ++ (([.str .x .x8 .x14 (8 * w)] : List Instr) ++
    (([.ldr .x .x8 .x15 (8 * w)] : List Instr) ++ (([stS (c.hiSlot + w) .x8] : List Instr) ++
    (([.ldr .x .x8 .x14 (8 * w)] : List Instr) ++ ([.str .x .x8 .x15 (8 * w)] : List Instr))))))) := rfl

/-- `unchainWord w`, with the scratch buffer at `b`: `unchainMem` at the
words `8 w` from `x14` and `x15` and the chaining value's word `w`. -/
theorem unchainWord_ok {s : State} {b : Addr} (w : Nat) (hw : w < 2) (hb : s.gpr sb = b)
    (hk : 8 * (c.hiSlot + w) < 32768)
    (ha : InRegions s.wr (s.gpr .x14 + BitVec.ofNat 64 (8 * w)) 8)
    (hh : InRegions s.wr (wordAddr b (c.hiSlot + w)) 8)
    (he : InRegions s.wr (s.gpr .x15 + BitVec.ofNat 64 (8 * w)) 8) :
    ∃ s', runBlock isa (c.unchainWord w) s = some s' ∧
      s'.mem = unchainMem s.mem (s.gpr .x14 + BitVec.ofNat 64 (8 * w)) (wordAddr b (c.hiSlot + w))
        (s.gpr .x15 + BitVec.ofNat 64 (8 * w)) ∧
      (∀ r, r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd : (8 * w) % 8 = 0 ∧ 8 * w < 32768 := ⟨by omega, by omega⟩
  obtain ⟨s₁, e₁, d₁, o₁, m₁, rd₁, wr₁⟩ := ldr_ok s .x8 .x14 hd (inRd ha)
  obtain ⟨s₂, e₂, d₂, o₂, m₂, rd₂, wr₂⟩ := ldS_ok (s := s₁) (k := c.hiSlot + w) .x9
    (by rw [o₁ _ (by decide), hb]) hk (by rw [rd₁, wr₁]; exact inRd hh)
  obtain ⟨s₃, e₃, d₃, o₃, m₃, rd₃, wr₃⟩ := eor_ok s₂ .x8 .x8 .x9
  have x14₃ : s₃.gpr .x14 = s.gpr .x14 := by rw [o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide)]
  have x15₃ : s₃.gpr .x15 = s.gpr .x15 := by rw [o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide)]
  have sb₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide), hb]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂, wr₁]
  have rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂, rd₁]
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := str_ok s₃ .x8 .x14 hd (by rw [wr₃', x14₃]; exact ha)
  obtain ⟨s₅, e₅, d₅, o₅, m₅, rd₅, wr₅⟩ := ldr_ok s₄ .x8 .x15 hd
    (by rw [rd₄, wr₄, rd₃', wr₃', g₄, x15₃]; exact inRd he)
  obtain ⟨s₆, e₆, m₆, g₆, rd₆, wr₆⟩ := stS_ok (s := s₅) (b := b) (k := c.hiSlot + w) .x8
    (by rw [o₅ _ (by decide), g₄, sb₃]) hk (by rw [wr₅, wr₄, wr₃']; exact hh)
  obtain ⟨s₇, e₇, d₇, o₇, m₇, rd₇, wr₇⟩ := ldr_ok s₆ .x8 .x14 hd
    (by rw [rd₆, wr₆, rd₅, wr₅, rd₄, wr₄, rd₃', wr₃', g₆, o₅ _ (by decide), g₄, x14₃]; exact inRd ha)
  obtain ⟨s₈, e₈, m₈, g₈, rd₈, wr₈⟩ := str_ok s₇ .x8 .x15 hd
    (by rw [wr₇, wr₆, wr₅, wr₄, wr₃', o₇ _ (by decide), g₆, o₅ _ (by decide), g₄, x15₃]; exact he)
  refine ⟨s₈, ?_, ?_, fun r h1 h2 => ?_, by rw [rd₈, rd₇, rd₆, rd₅, rd₄, rd₃'],
    by rw [wr₈, wr₇, wr₆, wr₅, wr₄, wr₃']⟩
  · rw [unchainWord_eq, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, runBlock_app, e₆,
      Option.bind_some, runBlock_app, e₇, Option.bind_some, e₈]
  · have x14₆ : s₆.gpr .x14 = s.gpr .x14 := by rw [g₆, o₅ _ (by decide), g₄, x14₃]
    have x15₇ : s₇.gpr .x15 = s.gpr .x15 := by rw [o₇ _ (by decide), g₆, o₅ _ (by decide), g₄, x15₃]
    have x15₄ : s₄.gpr .x15 = s.gpr .x15 := by rw [g₄, x15₃]
    have x8₂ : s₂.gpr .x8 = s.mem.readW (s.gpr .x14 + BitVec.ofNat 64 (8 * w)) 64 := by rw [o₂ _ (by decide), d₁]
    simp only [m₈, m₇, m₆, m₅, m₄, m₃, m₂, m₁, d₇, d₅, d₃, d₂, x8₂, x15₇, x14₃, x14₆, x15₄, unchainMem]
  · rw [g₈, o₇ r h1, g₆, o₅ r h1, g₄, o₃ r h1, o₂ r h2, o₁ r h1]

/-! ## The loop -/

/-- Unchaining, after `j` of `nb` blocks: the decryptions at `A`, the
ciphertexts at `E`, the chaining value at `H`. -/
structure UInv (A E H : Addr) (nb : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  x14 : s.gpr .x14 = A + BitVec.ofNat 64 (16 * j)
  x15 : s.gpr .x15 = E + BitVec.ofNat 64 (16 * j)
  x17 : s.gpr .x17 = BitVec.ofNat 64 (nb - j)
  out : ∀ t < 16 * j, s.mem (E + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t) ^^^
    (if t < 16 then s₀.mem (H + BitVec.ofNat 64 t) else s₀.mem (E + BitVec.ofNat 64 (t - 16)))
  rest : ∀ t, 16 * j ≤ t → t < 16 * nb → s.mem (E + BitVec.ofNat 64 t) = s₀.mem (E + BitVec.ofNat 64 t)
  bufRest : ∀ t, 16 * j ≤ t → t < 16 * nb → s.mem (A + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  chain : ∀ u < 16, s.mem (H + BitVec.ofNat 64 u) =
    if j = 0 then s₀.mem (H + BitVec.ofNat 64 u) else s₀.mem (E + BitVec.ofNat 64 (16 * (j - 1) + u))
  frame : Frame [⟨A, 16 * nb⟩, ⟨E, 16 * nb⟩, ⟨H, 16⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → r ≠ .x8 → r ≠ .x9 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem UInv.init {A E H : Addr} {nb : Nat} {s₀ : State} (ha : s₀.gpr .x14 = A) (hb : s₀.gpr .x15 = E)
    (hc : s₀.gpr .x17 = BitVec.ofNat 64 nb) : UInv A E H nb s₀ 0 s₀ :=
  ⟨by rw [ha]; simp, by rw [hb]; simp, by rw [hc, Nat.sub_zero], fun t ht => by omega, fun _ _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ => by rw [ite_eq_left rfl], Frame.refl _ _, fun _ _ _ _ _ _ => rfl, rfl, rfl⟩

theorem unchainBlocks_wp (hL : Layout c) {B A E : Addr} {nb : Nat} {s₀ : State} (hn : 0 < nb)
    (hn59 : nb < 2 ^ 59) (hB : s₀.gpr sb = B)
    (inA : ∀ t < 2 * nb, InRegions s₀.wr (A + BitVec.ofNat 64 (8 * t)) 8)
    (inE : ∀ t < 2 * nb, InRegions s₀.wr (E + BitVec.ofNat 64 (8 * t)) 8)
    (inH : ∀ w < 2, InRegions s₀.wr (wordAddr B (c.hiSlot + w)) 8)
    (dAE : Region.Disjoint ⟨A, 16 * nb⟩ ⟨E, 16 * nb⟩) (dAH : Region.Disjoint ⟨A, 16 * nb⟩ ⟨wordAddr B c.hiSlot, 16⟩)
    (dEH : Region.Disjoint ⟨E, 16 * nb⟩ ⟨wordAddr B c.hiSlot, 16⟩)
    (hs : UInv A E (wordAddr B c.hiSlot) nb s₀ 0 s₀) :
    WP isa c.unchainBlocks s₀ (UInv A E (wordAddr B c.hiSlot) nb s₀ nb) := by
  let H := wordAddr B c.hiSlot
  have hk : ∀ w < 2, 8 * (c.hiSlot + w) < 32768 := fun w hw => by
    have := hL.small; have := hL.room; simp only [Core.hiSlot]; omega
  have hH8 : wordAddr B (c.hiSlot + 1) = H + BitVec.ofNat 64 8 := by
    simp only [H, wordAddr]; rw [addr_add, Nat.mul_succ]
  have hN : 16 * nb < 2 ^ 64 := by omega
  have dHE : Region.Disjoint ⟨H, 16⟩ ⟨E, 16 * nb⟩ := fun y h1 h2 => dEH y h2 h1
  have dHA : Region.Disjoint ⟨H, 16⟩ ⟨A, 16 * nb⟩ := fun y h1 h2 => dAH y h2 h1
  have dEA : Region.Disjoint ⟨E, 16 * nb⟩ ⟨A, 16 * nb⟩ := fun y h1 h2 => dAE y h2 h1
  refine WP.loop (M := isa) (fun n s => ∃ j, n = nb - j ∧ j < nb ∧ UInv A E H nb s₀ j s)
    (fun n s hs => ?_) nb s₀ ⟨0, by omega, hn, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  let a := A + BitVec.ofNat 64 (16 * j)
  let e := E + BitVec.ofNat 64 (16 * j)
  have subA : Region.Sub ⟨a, 16⟩ ⟨A, 16 * nb⟩ := VG.Offset.sub_base A (by omega)
  have subE : Region.Sub ⟨e, 16⟩ ⟨E, 16 * nb⟩ := VG.Offset.sub_base E (by omega)
  have hah : Region.Disjoint ⟨a, 16⟩ ⟨H, 16⟩ := dAH.sub_left subA
  have hae : Region.Disjoint ⟨a, 16⟩ ⟨e, 16⟩ := (dAE.sub_left subA).sub_right subE
  have hhe : Region.Disjoint ⟨H, 16⟩ ⟨e, 16⟩ := dHE.sub_right subE
  have base : s.gpr sb = B := by rw [hi.regs _ (by decide) (by decide) (by decide) (by decide) (by decide), hB]
  have wA : ∀ k, k < 2 → InRegions s.wr (a + BitVec.ofNat 64 (8 * k)) 8 := fun k hk => by
    rw [hi.wr, addr_add, show 16 * j + 8 * k = 8 * (2 * j + k) by omega]; exact inA _ (by omega)
  have wE : ∀ k, k < 2 → InRegions s.wr (e + BitVec.ofNat 64 (8 * k)) 8 := fun k hk => by
    rw [hi.wr, addr_add, show 16 * j + 8 * k = 8 * (2 * j + k) by omega]; exact inE _ (by omega)
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := unchainWord_ok (c := c) (s := s) 0 (by decide) base (hk 0 (by decide))
    (by rw [hi.x14]; exact wA 0 (by decide)) (by rw [hi.wr]; exact inH 0 (by decide))
    (by rw [hi.x15]; exact wE 0 (by decide))
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := unchainWord_ok (c := c) (s := s₁) 1 (by decide)
    (by rw [g₁ _ (by decide) (by decide), base]) (hk 1 (by decide))
    (by rw [wr₁, g₁ _ (by decide) (by decide), hi.x14]; exact wA 1 (by decide)) (by rw [wr₁, hi.wr]; exact inH 1 (by decide))
    (by rw [wr₁, g₁ _ (by decide) (by decide), hi.x15]; exact wE 1 (by decide))
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := addImm_ok s₂ .x14 .x14 (v := 16) (by decide)
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₃ .x15 .x15 (v := 16) (by decide)
  obtain ⟨s₅, e₅, c₅, o₅, m₅, rd₅, wr₅⟩ := subImm_ok s₄ .x17 .x17 (v := 1) (by decide)
  refine WP.of_runBlock ⟨s₅, by
    rw [show c.unchainWord 0 ++ c.unchainWord 1 ++
        ([.addImm .x .x14 .x14 16, .addImm .x .x15 .x15 16, .subImm .x .x17 .x17 1] : List Instr) =
        c.unchainWord 0 ++ (c.unchainWord 1 ++ ([.addImm .x .x14 .x14 16] ++
        ([.addImm .x .x15 .x15 16] ++ ([.subImm .x .x17 .x17 1] : List Instr)))) by simp,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, e₅], ?_⟩
  have hm : s₅.mem = unchainMem (unchainMem s.mem a H e) (a + BitVec.ofNat 64 8) (H + BitVec.ofNat 64 8)
      (e + BitVec.ofNat 64 8) := by
    rw [m₅, m₄, m₃, m₂, m₁, g₁ _ (by decide) (by decide), g₁ _ (by decide) (by decide), hi.x14, hi.x15, ← hH8]
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, BitVec.add_zero, a, e, H]
  have ub := fun x => unchainBlock_apply s.mem x hah hae hhe
  -- Where the bytes of each region are.
  have eE : ∀ {t}, 16 * j ≤ t → t < 16 * (j + 1) → (E + BitVec.ofNat 64 t - e).toNat = t - 16 * j :=
    fun h1 h2 => off_sub_toNat E h1 (by omega)
  have nE : ∀ {t}, t < 16 * j ∨ 16 * (j + 1) ≤ t → t < 16 * nb → ¬ (E + BitVec.ofNat 64 t - e).toNat < 16 :=
    fun h1 h2 => off_sub_not E (by omega) (by omega) (by omega) (by omega)
  have nA : ∀ {t}, t < 16 * j ∨ 16 * (j + 1) ≤ t → t < 16 * nb → ¬ (A + BitVec.ofNat 64 t - a).toNat < 16 :=
    fun h1 h2 => off_sub_not A (by omega) (by omega) (by omega) (by omega)
  have EH : ∀ {t}, t < 16 * nb → ¬ (E + BitVec.ofNat 64 t - H).toNat < 16 :=
    fun h => not_near dEH h (by decide) (by omega)
  have Ea : ∀ {t}, t < 16 * nb → ¬ (E + BitVec.ofNat 64 t - a).toNat < 16 :=
    fun h => not_near (dEA.sub_right subA) h (by decide) (by omega)
  have Ae : ∀ {t}, t < 16 * nb → ¬ (A + BitVec.ofNat 64 t - e).toNat < 16 :=
    fun h => not_near (dAE.sub_right subE) h (by decide) (by omega)
  have AH : ∀ {t}, t < 16 * nb → ¬ (A + BitVec.ofNat 64 t - H).toNat < 16 :=
    fun h => not_near dAH h (by decide) (by omega)
  have hinv : UInv A E H nb s₀ (j + 1) s₅ := by
    refine ⟨?_, ?_, ?_, fun t ht => ?_, fun t h1 h2 => ?_, fun t h1 h2 => ?_, fun u hu => ?_,
      hi.frame.trans fun x hx => ?_, fun r h1 h2 h3 h4 h5 => ?_,
      by rw [rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₅ _ (by decide), o₄ _ (by decide), a₃, g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), hi.x14,
        addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega]
    · rw [o₅ _ (by decide), a₄, o₃ _ (by decide), g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), hi.x15,
        addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega]
    · rw [c₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), hi.x17,
        VG.Offset.ofNat_sub_ofNat (by omega),
        show nb - j - 1 = nb - (j + 1) by omega]
    · rw [hm, ub]
      by_cases h0 : 16 * j ≤ t
      · rw [ite_eq_left (by rw [eE h0 ht]; omega), eE h0 ht, addr_add A,
          show 16 * j + (t - 16 * j) = t by omega, hi.bufRest t (by omega) (by omega),
          hi.chain _ (by omega)]
        by_cases hj0 : j = 0
        · subst hj0
          rw [ite_eq_left rfl, ite_eq_left (by omega), Nat.sub_zero]
        · rw [ite_eq_right hj0, ite_eq_right (by omega), show 16 * (j - 1) + (t - 16 * j) = t - 16 by omega]
      · rw [ite_eq_right (nE (.inl (by omega)) (by omega)), ite_eq_right (EH (by omega)),
          ite_eq_right (Ea (by omega))]
        exact hi.out t (by omega)
    · rw [hm, ub, ite_eq_right (nE (.inr h1) h2), ite_eq_right (EH h2), ite_eq_right (Ea h2)]
      exact hi.rest t (by omega) h2
    · rw [hm, ub, ite_eq_right (Ae h2), ite_eq_right (AH h2), ite_eq_right (nA (.inr h1) h2)]
      exact hi.bufRest t (by omega) h2
    · rw [hm, ub, ite_eq_right (not_near (dHE.sub_right subE) hu (Nat.le_refl _) (by decide)),
        ite_eq_left (by rw [off_self H (by omega)]; exact hu), off_self H (by omega), addr_add E, hi.rest _ (by omega) (by omega), ite_eq_right (by omega),
        show j + 1 - 1 = j by omega]
    · have hx1 : ¬ (x - e).toNat < 16 := fun h => hx _ (List.mem_cons_of_mem _ List.mem_cons_self)
        (subE x (by simp only [Region.Contains]; omega))
      have hx2 : ¬ (x - H).toNat < 16 := fun h => hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)) (by simp only [Region.Contains]; omega)
      have hx3 : ¬ (x - a).toNat < 16 := fun h => hx _ List.mem_cons_self
        (subA x (by simp only [Region.Contains]; omega))
      rw [hm, ub, ite_eq_right hx1, ite_eq_right hx2, ite_eq_right hx3]
    · rw [o₅ r h3, o₄ r h2, o₃ r h1, g₂ r h4 h5, g₁ r h4 h5, hi.regs r h1 h2 h3 h4 h5]
  have hz : isa.eval (.nonzero .x .x17) s₅ = some !(decide (nb - (j + 1) = 0)) := by
    rw [eval_nonzero, ← ofNat_beq_zero (by omega)]
    congr 2
    rw [c₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), hi.x17,
      VG.Offset.ofNat_sub_ofNat (by omega), show nb - j - 1 = nb - (j + 1) by omega]
  by_cases hl : j + 1 = nb
  · refine .inl ⟨by rw [hz, decide_eq_true (by omega)]; rfl, by rw [show j + 1 = nb from hl] at hinv; exact hinv⟩
  · exact .inr ⟨by rw [hz, decide_eq_false (by omega)]; rfl, nb - (j + 1), by omega, j + 1, rfl, by omega, hinv⟩

end VG.Proof.Modes.AArch64
