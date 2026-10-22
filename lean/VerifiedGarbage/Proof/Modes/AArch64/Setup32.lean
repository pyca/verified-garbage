module

public import VerifiedGarbage.Proof.Modes.AArch64.Setup
public import VerifiedGarbage.Proof.Modes.Ctr32
public import VerifiedGarbage.Impl.Modes.AArch64.Ctr32
import VerifiedGarbage.Proof.Modes.AArch64.Counter32
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Counter mode with `inc₃₂` on AArch64: the entry

`setup32_ok`: the entry block of `ctr32` does what `ctr`'s does
(`setup_ok`, `Setup.lean`), but writes `inc₃₂ⁿ(T₁)` back
(`ctr32Val V n`) rather than `T₁ + n`.
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS)
open VG.Spec.Aes (bytesAt)

theorem ctr32Setup_eq (c : Core) (r : CtrRegs) : c.ctr32Setup r =
    ([.ldr .x .x6 r.ctr 0] : List Instr) ++ (([.rev .x6 .x6] : List Instr) ++
      (([.ldr .x .x7 r.ctr 8] : List Instr) ++ (([.rev .x7 .x7] : List Instr) ++
      (([stS c.hiSlot .x6] : List Instr) ++ (([stS c.loSlot .x7] : List Instr) ++
      (Core.inc32By .x10 r.n ++
      (([.rev .x6 .x6] : List Instr) ++ (([.rev .x7 .x7] : List Instr) ++
      (([.str .x .x7 r.ctr 8] : List Instr) ++ ([.str .x .x6 r.ctr 0] : List Instr)))))))))) := rfl

variable {c : Core}

/-- The entry block. -/
theorem setup32_ok (hL : Layout c) {r : CtrRegs} (hr : RegsOk r) (s : State) {B P : Addr}
    (hB : s.gpr r.scr = B) (hs : ScrIn s B c.total) (hP : s.gpr r.ctr = P) (hwP : (⟨P, 16⟩ : Region) ∈ s.wr)
    (hsep : Region.Disjoint ⟨P, 16⟩ ⟨B, 8 * c.total⟩) :
    ∃ s', runBlock isa (c.ctrEntry r ++ c.ctr32Setup r) s = some s' ∧ s'.gpr sb = B ∧
      (∀ i < 10, s'.mem.readW (wordAddr B (c.slots + i)) 64 = s.gpr (Core.savedRegs.getD i .x19)) ∧
      s'.mem.readW (wordAddr B c.hiSlot) 64 = hiOf (ctrVal s.mem P) ∧
      s'.mem.readW (wordAddr B c.loSlot) 64 = loOf (ctrVal s.mem P) ∧
      bytesAt s'.mem P 16 = Spec.Ctr.ofNat (ctr32Val (ctrVal s.mem P) (s.gpr r.n).toNat) 16 ∧
      Frame [modeRegion c B, ⟨P, 16⟩] s.mem s'.mem ∧
      (∀ x, x ∉ SetupRegs → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsm := hL.small
  have hroom := hL.room
  have hN : 8 * c.total < 2 ^ 64 := by omega
  have sl : ∀ k, c.slots ≤ k → k < c.total → InRegions s.wr (wordAddr B k) 8 := fun k _ hk =>
    slot_wr hs.wr hN hk
  have p0 : P + BitVec.ofNat 64 0 = P := by simp
  obtain ⟨cs, c6, c7, c10⟩ := not_setupRegs hr.ctr
  obtain ⟨ns, n6, n7, n10⟩ := not_setupRegs hr.n
  -- The scratch buffer to `sb`.
  obtain ⟨s₁, e₁, b₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s sb r.scr
  have b₁' : s₁.gpr sb = B := by rw [b₁, hB]
  -- The callee-saved registers.
  obtain ⟨s₂, e₂, v₂, f₂, g₂, rd₂, wr₂⟩ := stores_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .x19) 10 s₁
    b₁' (fun i hi => by rw [wr₁]; exact sl _ (by omega) (by omega)) (by omega)
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁]
  have keep₂ : ∀ x, x ≠ sb → s₂.gpr x = s.gpr x := fun x hx => by rw [g₂, o₁ x hx]
  have P₂ : s₂.gpr r.ctr = P := by rw [keep₂ _ cs, hP]
  have fe : Frame [modeRegion c B] s.mem s₂.mem := by
    rw [← m₁]
    exact f₂.sub fun x hx => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx
      exact VG.Offset.sub B (by omega) (by omega)⟩
  have dP : ∀ k, c.slots ≤ k → k < c.total → ∀ x ∈ [(⟨P, 16⟩ : Region)],
      Region.Disjoint ⟨wordAddr B k, 8⟩ x := fun k h1 h2 x hx => by
    simp only [List.mem_singleton] at hx; subst hx
    exact (hsep.sub_right (VG.Offset.sub_base B (by omega))).symm
  -- The counter.
  have inP : ∀ d, d + 8 ≤ 16 → InRegions s.wr (P + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨_, hwP, VG.Offset.contains_base P hd (by omega)⟩
  obtain ⟨hv, lv⟩ := halves s.mem P
  let V := ctrVal s.mem P
  have mP : ∀ d, d + 8 ≤ 16 →
      s₂.mem.readW (P + BitVec.ofNat 64 d) 64 = s.mem.readW (P + BitVec.ofNat 64 d) 64 := fun d hd =>
    fe.readW (r := ⟨P, 16⟩) (VG.Offset.contains_base P (by omega) (by omega)) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact hsep.sub_right (VG.Offset.sub_base B (by omega))) (by decide)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := ldr_ok s₂ .x6 r.ctr (off := 0) (by decide)
    (by rw [rd₂', wr₂', P₂]; exact inRd (inP 0 (by decide)))
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := rev_ok s₃ .x6 .x6
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := ldr_ok s₄ .x7 r.ctr (off := 8) (by decide)
    (by rw [rd₄, wr₄, rd₃, wr₃, rd₂', wr₂', o₄ _ (Ne.symm c6).symm, o₃ _ c6, P₂]; exact inRd (inP 8 (by decide)))
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := rev_ok s₅ .x7 .x7
  have g₆ : ∀ x, x ≠ .x6 → x ≠ .x7 → s₆.gpr x = s₂.gpr x := fun x h1 h2 => by
    rw [o₆ x h2, o₅ x h2, o₄ x h1, o₃ x h1]
  have mP0 := mP 0 (by decide)
  rw [p0] at mP0
  have x6₆ : s₆.gpr .x6 = hiOf V := by
    rw [o₆ _ (by decide), o₅ _ (by decide), r₄, r₃, P₂, p0, mP0, hv]; rfl
  have x7₆ : s₆.gpr .x7 = loOf V := by
    rw [r₆, r₅, m₄, m₃, o₄ _ c6, o₃ _ c6, P₂, mP 8 (by decide), lv]; rfl
  have wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, wr₃, wr₂']
  have rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₄, rd₃, rd₂']
  have b₆ : s₆.gpr sb = B := by rw [g₆ _ (by decide) (by decide), g₂, b₁']
  have hH : c.hiSlot < c.total := by simp only [Core.hiSlot]; omega
  have hLo : c.loSlot < c.total := by simp only [Core.loSlot]; omega
  obtain ⟨s₇, e₇, m₇, g₇, rd₇, wr₇⟩ := stS_ok (s := s₆) (b := B) (k := c.hiSlot) .x6 b₆ (by omega)
    (by rw [wr₆']; exact sl _ (by simp only [Core.hiSlot]; omega) hH)
  obtain ⟨s₈, e₈, m₈, g₈, rd₈, wr₈⟩ := stS_ok (s := s₇) (b := B) (k := c.loSlot) .x7 (by rw [g₇, b₆]) (by omega)
    (by rw [wr₇, wr₆']; exact sl _ (by simp only [Core.loSlot]; omega) hLo)
  let N := (s.gpr r.n).toNat
  obtain ⟨s₁₀, e₁₀, l₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ := inc32By_ok s₈ (T := .x10) (by decide) r.n (V := V) (j := N)
    (by rw [g₈, g₇, g₆ _ n6 n7, keep₂ _ ns]; simp [N]) (by rw [g₈, g₇, x7₆])
  have h₁₀ : s₁₀.gpr .x6 = hiOf (ctr32Val V N) := by
    rw [o₁₀ _ (by decide) (by decide), g₈, g₇, x6₆, hiOf_ctr32Val]
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := rev_ok s₁₀ .x6 .x6
  obtain ⟨s₁₂, e₁₂, r₁₂, o₁₂, m₁₂, rd₁₂, wr₁₂⟩ := rev_ok s₁₁ .x7 .x7
  have keep₁₂ : ∀ x, x ≠ .x6 → x ≠ .x7 → x ≠ .x10 → s₁₂.gpr x = s₆.gpr x := fun x h1 h2 h3 => by
    rw [o₁₂ x h2, o₁₁ x h1, o₁₀ x h2 h3, g₈, g₇]
  have P₁₂ : s₁₂.gpr r.ctr = P := by rw [keep₁₂ _ c6 c7 c10, g₆ _ c6 c7, P₂]
  have wr₁₂' : s₁₂.wr = s.wr := by rw [wr₁₂, wr₁₁, wr₁₀, wr₈, wr₇, wr₆']
  obtain ⟨s₁₃, e₁₃, m₁₃, g₁₃, rd₁₃, wr₁₃⟩ := str_ok s₁₂ .x7 r.ctr (off := 8) (by decide)
    (by rw [P₁₂, wr₁₂']; exact inP 8 (by decide))
  obtain ⟨s₁₄, e₁₄, m₁₄, g₁₄, rd₁₄, wr₁₄⟩ := str_ok s₁₃ .x6 r.ctr (off := 0) (by decide)
    (by rw [g₁₃, P₁₂, wr₁₃, wr₁₂']; exact inP 0 (by decide))
  have mem₈ : s₈.mem = (s₂.mem.writeW (wordAddr B c.hiSlot) (hiOf V)).writeW (wordAddr B c.loSlot) (loOf V) := by
    rw [m₈, m₇, g₇, x6₆, x7₆, m₆, m₅, m₄, m₃]
  have mem₁₄ : s₁₄.mem = (s₈.mem.writeW (P + BitVec.ofNat 64 8) (rev64 (loOf (ctr32Val V N)))).writeW P
      (rev64 (hiOf (ctr32Val V N))) := by
    rw [m₁₄, g₁₃, P₁₂, p0, m₁₃, P₁₂, m₁₂, m₁₁, m₁₀, o₁₂ .x6 (by decide), r₁₁, h₁₀, r₁₂, o₁₁ .x7 (by decide),
      l₁₀]
  -- The frames.
  have fS : Frame [modeRegion c B] s₂.mem s₈.mem := by
    rw [mem₈]
    have hm : modeRegion c B ∈ [modeRegion c B] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (VG.Offset.contains B (by simp only [Core.hiSlot]; omega)
      (by simp only [Core.hiSlot]; omega) (by omega))).writeW hm _
      (VG.Offset.contains B (by simp only [Core.loSlot]; omega) (by simp only [Core.loSlot]; omega) (by omega))
  have fP : Frame [⟨P, 16⟩] s₈.mem s₁₄.mem := by
    rw [mem₁₄]
    have hm : (⟨P, 16⟩ : Region) ∈ [(⟨P, 16⟩ : Region)] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (VG.Offset.contains_base P (by decide) (by decide))).writeW hm _
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
  have thruP : ∀ k, c.slots ≤ k → k < c.total →
      s₁₄.mem.readW (wordAddr B k) 64 = s₈.mem.readW (wordAddr B k) 64 := fun k h1 h2 =>
    fP.readW (Region.contains_self _ _) (dP k h1 h2) (by decide)
  have b8 : ∀ k, k < c.total → 8 * k < 2 ^ 64 := fun k hk => by omega
  have mem8 : ∀ k, c.slots ≤ k → k < c.total → k ≠ c.hiSlot → k ≠ c.loSlot →
      s₈.mem.readW (wordAddr B k) 64 = s₂.mem.readW (wordAddr B k) 64 := fun k h1 h2 hh hl => by
    rw [mem₈, readW_slot_write _ (b8 k h2) (b8 _ hLo), ite_eq_right hl, readW_slot_write _ (b8 k h2) (b8 _ hH),
      ite_eq_right hh]
  have hsv : ∀ i < 10, Core.savedRegs.getD i .x19 ≠ sb := by decide
  refine ⟨s₁₄, ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, fun x hx => ?_,
    by rw [rd₁₄, rd₁₃, rd₁₂, rd₁₁, rd₁₀, rd₈, rd₇, rd₆'], by rw [wr₁₄, wr₁₃, wr₁₂']⟩
  · rw [runBlock_app, ctrEntry_eq, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, ctr32Setup_eq,
      runBlock_app, e₃, Option.bind_some, runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some,
      runBlock_app, e₆, Option.bind_some, runBlock_app, e₇, Option.bind_some, runBlock_app, e₈, Option.bind_some,
      runBlock_app, e₁₀, Option.bind_some, runBlock_app, e₁₁,
      Option.bind_some, runBlock_app, e₁₂, Option.bind_some, runBlock_app, e₁₃, Option.bind_some, e₁₄]
  · rw [g₁₄, g₁₃, keep₁₂ _ (by decide) (by decide) (by decide), b₆]
  · have k1 : c.slots ≤ c.slots + i := by omega
    have k2 : c.slots + i < c.total := by omega
    rw [thruP _ k1 k2, mem8 _ k1 k2 (by simp only [Core.hiSlot]; omega) (by simp only [Core.loSlot]; omega),
      v₂ i hi, o₁ _ (hsv i hi)]
  · rw [thruP _ (by simp only [Core.hiSlot]; omega) hH, mem₈,
      readW_slot_write _ (b8 _ hH) (b8 _ hLo), ite_eq_right (by simp only [Core.hiSlot, Core.loSlot]; omega),
      Mem.readW_writeW_self64]
  · rw [thruP _ (by simp only [Core.loSlot]; omega) hLo, mem₈, Mem.readW_writeW_self64]
  · rw [mem₁₄]; exact bytes_pair2 _ _ _
  · exact (fe.trans (fS.sub fun x hx => ⟨x, hx, fun _ h => h⟩) |>.sub fun x hx => ⟨x, by
      simp only [List.mem_singleton] at hx; rw [hx]; exact List.mem_cons_self, fun _ h => h⟩).trans
      (fP.sub fun x hx => ⟨x, by
        simp only [List.mem_singleton] at hx; rw [hx]; exact List.mem_cons_of_mem _ List.mem_cons_self,
        fun _ h => h⟩)
  · obtain ⟨h1, h2, h3, h4⟩ := not_setupRegs hx
    rw [g₁₄, g₁₃, keep₁₂ x h2 h3 h4, g₆ x h2 h3, keep₂ x h1]

end VG.Proof.Modes.AArch64
