module
public import VerifiedGarbage.Proof.Modes.X86_64.Setup
import VerifiedGarbage.Proof.Modes.X86_64.Counter32

import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.Modes.X86_64.Ctr32
public import VerifiedGarbage.Proof.Framework.X86_64.Straight
public import VerifiedGarbage.Proof.Modes.Ctr32
public import VerifiedGarbage.Proof.Modes.X86_64.Core

/-!
# Counter mode with `inc₃₂` on x86-64: the entry

`setup32_ok`: the entry block of `ctr32` does what `ctr`'s does
(`setup_ok`), but writes `inc₃₂ⁿ(T₁)` back (`ctr32Val V n`) rather than
`T₁ + n`.
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

theorem ctr32Setup_eq (c : Core) (r : CtrRegs) : c.ctr32Setup r =
    ([.mov .rax (.mem (at_ r.ctr 0))] : List Instr) ++ (([.bswap .rax] : List Instr) ++
      (([.mov .rbx (.mem (at_ r.ctr 8))] : List Instr) ++ (([.bswap .rbx] : List Instr) ++
      (([st c.hiSlot .rax] : List Instr) ++ (([st c.loSlot .rbx] : List Instr) ++
      (Core.inc32By .rax (.reg r.n) ++ (([movS .rax c.hiSlot] : List Instr) ++
      (([.bswap .rax] : List Instr) ++ (([.bswap .rbx] : List Instr) ++
      (([.store (at_ r.ctr 8) .rbx] : List Instr) ++ ([.store (at_ r.ctr 0) .rax] : List Instr))))))))))) := rfl

variable {c : Core}

/-- The entry block. -/
theorem setup32_ok (hL : Layout c) {r : CtrRegs} (hr : RegsOk r) (s : State) {B P : Addr}
    (hB : s.gpr r.scr = B) (hs : ScrIn s B c.ctrSlots) (hP : s.gpr r.ctr = P) (hwP : (⟨P, 16⟩ : Region) ∈ s.wr)
    (hsep : Region.Disjoint ⟨P, 16⟩ ⟨B, 8 * c.ctrSlots⟩) :
    ∃ s', runBlock isa (c.ctrEntry r ++ c.ctr32Setup r) s = some s' ∧ s'.gpr sb = B ∧
      (∀ i < 6, s'.mem.readW (wordAddr B (c.slots + i)) 64 = s.gpr (Core.savedRegs.getD i .rbx)) ∧
      s'.mem.readW (wordAddr B c.hiSlot) 64 = hiOf (ctrVal s.mem P) ∧
      s'.mem.readW (wordAddr B c.loSlot) 64 = loOf (ctrVal s.mem P) ∧
      bytesAt s'.mem P 16 = Spec.Ctr.ofNat (ctr32Val (ctrVal s.mem P) (s.gpr r.n).toNat) 16 ∧
      Frame [modeRegion c B, ⟨P, 16⟩] s.mem s'.mem ∧
      (∀ x, x ≠ sb → x ≠ .rax → x ≠ .rbx → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsm := hL.small
  have hroom := hL.room
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega_arith
  have sl : ∀ k, c.slots ≤ k → k < c.ctrSlots → InRegions s.wr (wordAddr B k) 8 := fun k _ hk =>
    slot_wr hs.wr hN hk
  have p0 : P + BitVec.ofNat 64 0 = P := by simp
  -- The scratch buffer to `sb`.
  obtain ⟨s₁, e₁, b₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s sb r.scr
  have b₁' : s₁.gpr sb = B := by rw [b₁, hB]
  have keep₁ : ∀ x, x ≠ sb → s₁.gpr x = s.gpr x := o₁
  -- The callee-saved registers.
  obtain ⟨s₂, e₂, v₂, f₂, g₂, rd₂, wr₂⟩ := stores_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .rbx) 6 s₁ b₁'
    (fun i hi => by rw [wr₁]; exact sl _ (by omega_arith) (by simp only [Core.ctrSlots]; omega_arith))
    (by omega_arith)
  let s₄ := s₂
  have m₄e : s₄.mem = s₂.mem := rfl
  have g₄' : s₄.gpr = s₁.gpr := g₂
  have wr₄' : s₄.wr = s.wr := by rw [show s₄.wr = s₂.wr from rfl, wr₂, wr₁]
  have rd₄' : s₄.rd = s.rd := by rw [show s₄.rd = s₂.rd from rfl, rd₂, rd₁]
  have keep₄ : ∀ x, x ≠ sb → s₄.gpr x = s.gpr x := fun x hx => by rw [g₄', keep₁ x hx]
  have P₄ : s₄.gpr r.ctr = P := by rw [keep₄ _ hr.ctr.1, hP]
  have fe : Frame [modeRegion c B] s.mem s₄.mem := by
    rw [← m₁]
    exact f₂.sub fun x hx => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx
      exact VG.Offset.sub B (by omega_arith) (by omega_arith)⟩
  have dP : ∀ k, c.slots ≤ k → k < c.ctrSlots → ∀ x ∈ [(⟨P, 16⟩ : Region)],
      Region.Disjoint ⟨wordAddr B k, 8⟩ x := fun k h1 h2 x hx => by
    simp only [List.mem_singleton] at hx; subst hx
    exact (hsep.sub_right (VG.Offset.sub_base B (by omega_arith))).symm
  have memP : bytesAt s₄.mem P 16 = bytesAt s.mem P 16 :=
    bytesAt_frame fe (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact hsep.sub_right (VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_arith))) (by decide)
  -- The counter.
  have inP : ∀ d, d + 8 ≤ 16 → InRegions s.wr (P + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨_, hwP, VG.Offset.contains_base P hd (by omega_arith)⟩
  obtain ⟨hv, lv⟩ := halves s.mem P
  let V := ctrVal s.mem P
  have mP : ∀ d, d + 8 ≤ 16 →
      s₄.mem.readW (P + BitVec.ofNat 64 d) 64 = s.mem.readW (P + BitVec.ofNat 64 d) 64 := fun d hd =>
    fe.readW (r := ⟨P, 16⟩) (VG.Offset.contains_base P (by omega_arith) (by omega_arith)) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact hsep.sub_right (VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_arith))) (by decide)
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := ld_ok s₄ .rax r.ctr 0
    (by rw [rd₄', wr₄', P₄]; exact inRd (inP 0 (by decide)))
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := bswap_ok s₅ .rax
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇⟩ := ld_ok s₆ .rbx r.ctr 8
    (by rw [rd₆, wr₆, rd₅, wr₅, rd₄', wr₄', o₆ _ hr.ctr.2.1, o₅ _ hr.ctr.2.1, P₄]; exact inRd (inP 8 (by decide)))
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := bswap_ok s₇ .rbx
  have g₈ : ∀ x, x ≠ .rax → x ≠ .rbx → s₈.gpr x = s₄.gpr x := fun x h1 h2 => by
    rw [o₈ x h2, o₇ x h2, o₆ x h1, o₅ x h1]
  have mP0 := mP 0 (by decide)
  rw [p0] at mP0
  have rax₈ : s₈.gpr .rax = hiOf V := by
    rw [o₈ _ (by decide), o₇ _ (by decide), r₆, r₅, P₄, p0, mP0, hv]; rfl
  have rbx₈ : s₈.gpr .rbx = loOf V := by
    rw [r₈, r₇, m₆, m₅, o₆ _ hr.ctr.2.1, o₅ _ hr.ctr.2.1, P₄, mP 8 (by decide), lv]; rfl
  have wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₇, wr₆, wr₅, wr₄']
  have rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₇, rd₆, rd₅, rd₄']
  have b₈ : s₈.gpr sb = B := by rw [g₈ _ (by decide) (by decide), g₄', b₁']
  have hH : c.hiSlot < c.ctrSlots := by simp only [Core.hiSlot, Core.ctrSlots]; omega_arith
  have hLo : c.loSlot < c.ctrSlots := by simp only [Core.loSlot, Core.ctrSlots]; omega_arith
  obtain ⟨s₉, e₉, m₉, g₉, rd₉, wr₉⟩ := stReg_ok (s := s₈) (b := B) (k := c.hiSlot) .rax b₈
    (by rw [wr₈']; exact sl _ (by simp only [Core.hiSlot]; omega_arith) hH)
  obtain ⟨s₁₀, e₁₀, m₁₀, g₁₀, rd₁₀, wr₁₀⟩ := stReg_ok (s := s₉) (b := B) (k := c.loSlot) .rbx (by rw [g₉, b₈])
    (by rw [wr₉, wr₈']; exact sl _ (by simp only [Core.loSlot]; omega_arith) hLo)
  let N := (s.gpr r.n).toNat
  have n₁₀ : s₁₀.gpr r.n = BitVec.ofNat 64 N := by
    rw [g₁₀, g₉, g₈ _ hr.n.2.1 hr.n.2.2, keep₄ _ hr.n.1]; simp [N]
  obtain ⟨s₁₁, e₁₁, l₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := inc32By_ok s₁₀ (T := .rax) (by decide) (.reg r.n) (V := V)
    (j := N) (fun t ht _ => by
      simp only [readSrc32, ht _ hr.n.2.1 hr.n.2.2, n₁₀, Option.some.injEq]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega_arith) (by rw [g₁₀, g₉, rbx₈])
  have b₁₁ : s₁₁.gpr sb = B := by rw [o₁₁ _ (by decide) (by decide), g₁₀, g₉, b₈]
  obtain ⟨s₁₁b, e₁₁b, v₁₁b, o₁₁b, m₁₁b, rd₁₁b, wr₁₁b⟩ := movS_ok (s := s₁₁) (b := B) (k := c.hiSlot) .rax b₁₁
    (by rw [rd₁₁, wr₁₁, rd₁₀, wr₁₀, rd₉, wr₉, rd₈', wr₈']; exact inRd (sl _ (by simp only [Core.hiSlot]; omega_arith) hH))
  have h₁₁ : s₁₁b.gpr .rax = hiOf (ctr32Val V N) := by
    rw [v₁₁b, m₁₁, m₁₀, readW_slot_write _ (by omega_arith) (by omega_arith),
      ite_eq_right (by simp only [Core.hiSlot, Core.loSlot]; omega_arith), m₉, Mem.readW_writeW_self64, rax₈,
      hiOf_ctr32Val]
  obtain ⟨s₁₂, e₁₂, r₁₂, o₁₂, m₁₂, rd₁₂, wr₁₂⟩ := bswap_ok s₁₁b .rax
  obtain ⟨s₁₃, e₁₃, r₁₃, o₁₃, m₁₃, rd₁₃, wr₁₃⟩ := bswap_ok s₁₂ .rbx
  have keep₁₃ : ∀ x, x ≠ .rax → x ≠ .rbx → s₁₃.gpr x = s₈.gpr x := fun x h1 h2 => by
    rw [o₁₃ x h2, o₁₂ x h1, o₁₁b x h1, o₁₁ x h2 h1, g₁₀, g₉]
  have P₁₃ : s₁₃.gpr r.ctr = P := by rw [keep₁₃ _ hr.ctr.2.1 hr.ctr.2.2, g₈ _ hr.ctr.2.1 hr.ctr.2.2, P₄]
  have wr₁₃' : s₁₃.wr = s.wr := by rw [wr₁₃, wr₁₂, wr₁₁b, wr₁₁, wr₁₀, wr₉, wr₈']
  obtain ⟨s₁₄, e₁₄, m₁₄, g₁₄, rd₁₄, wr₁₄⟩ := stM_ok s₁₃ r.ctr .rbx 8 (by rw [P₁₃, wr₁₃']; exact inP 8 (by decide))
  obtain ⟨s₁₅, e₁₅, m₁₅, g₁₅, rd₁₅, wr₁₅⟩ := stM_ok s₁₄ r.ctr .rax 0
    (by rw [g₁₄, P₁₃, wr₁₄, wr₁₃']; exact inP 0 (by decide))
  have mem₁₀ : s₁₀.mem = (s₄.mem.writeW (wordAddr B c.hiSlot) (hiOf V)).writeW (wordAddr B c.loSlot) (loOf V) := by
    rw [m₁₀, m₉, g₉, rax₈, rbx₈, m₈, m₇, m₆, m₅]
  have mem₁₅ : s₁₅.mem = (s₁₀.mem.writeW (P + BitVec.ofNat 64 8) (bswap64 (loOf (ctr32Val V N)))).writeW P
      (bswap64 (hiOf (ctr32Val V N))) := by
    rw [m₁₅, g₁₄, P₁₃, p0, m₁₄, P₁₃, m₁₃, m₁₂, m₁₁b, m₁₁, o₁₃ .rax (by decide), r₁₂, h₁₁, r₁₃, o₁₂ .rbx (by decide),
      o₁₁b .rbx (by decide), l₁₁]
  -- The frames.
  have fS : Frame [modeRegion c B] s₄.mem s₁₀.mem := by
    rw [mem₁₀]
    have hm : modeRegion c B ∈ [modeRegion c B] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (VG.Offset.contains B (by simp only [Core.hiSlot]; omega_arith)
      (by simp only [Core.hiSlot]; omega_arith) (by omega_arith))).writeW hm _
      (VG.Offset.contains B (by simp only [Core.loSlot]; omega_arith) (by simp only [Core.loSlot]; omega_arith) (by omega_arith))
  have fP : Frame [⟨P, 16⟩] s₁₀.mem s₁₅.mem := by
    rw [mem₁₅]
    have hm : (⟨P, 16⟩ : Region) ∈ [(⟨P, 16⟩ : Region)] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (VG.Offset.contains_base P (by decide) (by decide))).writeW hm _
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
  have thruP : ∀ k, c.slots ≤ k → k < c.ctrSlots →
      s₁₅.mem.readW (wordAddr B k) 64 = s₁₀.mem.readW (wordAddr B k) 64 := fun k h1 h2 =>
    fP.readW (Region.contains_self _ _) (dP k h1 h2) (by decide)
  have b8 : ∀ k, k < c.ctrSlots → 8 * k < 2 ^ 64 := fun k hk => by omega_arith
  have mem10 : ∀ k, c.slots ≤ k → k < c.ctrSlots → k ≠ c.hiSlot → k ≠ c.loSlot →
      s₁₀.mem.readW (wordAddr B k) 64 = s₄.mem.readW (wordAddr B k) 64 := fun k h1 h2 hh hl => by
    rw [mem₁₀, readW_slot_write _ (b8 k h2) (b8 _ hLo), ite_eq_right hl, readW_slot_write _ (b8 k h2) (b8 _ hH), ite_eq_right hh]
  have hsv : ∀ i < 6, Core.savedRegs.getD i .rbx ≠ sb := by decide
  refine ⟨s₁₅, ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, fun x h1 h2 h3 => ?_,
    by rw [rd₁₅, rd₁₄, rd₁₃, rd₁₂, rd₁₁b, rd₁₁, rd₁₀, rd₉, rd₈'], by rw [wr₁₅, wr₁₄, wr₁₃']⟩
  · rw [runBlock_app, ctrEntry_eq, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, ctr32Setup_eq,
      runBlock_app, e₅, Option.bind_some, runBlock_app, e₆, Option.bind_some, runBlock_app, e₇, Option.bind_some,
      runBlock_app, e₈, Option.bind_some, runBlock_app, e₉, Option.bind_some, runBlock_app, e₁₀, Option.bind_some,
      runBlock_app, e₁₁, Option.bind_some, runBlock_app, e₁₁b, Option.bind_some, runBlock_app, e₁₂, Option.bind_some, runBlock_app, e₁₃,
      Option.bind_some, runBlock_app, e₁₄, Option.bind_some, e₁₅]
  · rw [g₁₅, g₁₄, keep₁₃ _ (by decide) (by decide), b₈]
  · have k1 : c.slots ≤ c.slots + i := by omega_arith
    have k2 : c.slots + i < c.ctrSlots := by simp only [Core.ctrSlots]; omega_arith
    rw [thruP _ k1 k2, mem10 _ k1 k2 (by simp only [Core.hiSlot]; omega_arith) (by simp only [Core.loSlot]; omega_arith),
      m₄e, v₂ i hi, keep₁ _ (hsv i hi)]
  · rw [thruP _ (by simp only [Core.hiSlot]; omega_arith) hH, mem₁₀,
      readW_slot_write _ (b8 _ hH) (b8 _ hLo), ite_eq_right (by simp only [Core.hiSlot, Core.loSlot]; omega_arith),
      Mem.readW_writeW_self64]
  · rw [thruP _ (by simp only [Core.loSlot]; omega_arith) hLo, mem₁₀, Mem.readW_writeW_self64]
  · rw [mem₁₅]; exact bytes_pair2 _ _ _
  · exact (fe.trans (fS.sub fun x hx => ⟨x, hx, fun _ h => h⟩) |>.sub fun x hx => ⟨x, by
      simp only [List.mem_singleton] at hx; rw [hx]; exact List.mem_cons_self, fun _ h => h⟩).trans
      (fP.sub fun x hx => ⟨x, by
        simp only [List.mem_singleton] at hx; rw [hx]; exact List.mem_cons_of_mem _ List.mem_cons_self,
        fun _ h => h⟩)
  · rw [g₁₅, g₁₄, keep₁₃ x h2 h3, g₈ x h2 h3, keep₄ x h1]

end VG.Proof.Modes.X86_64
