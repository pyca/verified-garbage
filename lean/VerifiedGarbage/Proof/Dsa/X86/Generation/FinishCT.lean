module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Finish
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.TimingFlags
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86.Generation.AttemptCT

/-! # Two runs of one geometry's search and result leak the same -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc at_)

/-- The pointers and the count of a copy or a clearing of `out`. -/
def outPins (E : Env) (src : Reg) (n : Nat) (r : Reg) : BitVec 32 :=
  if r = src then E.base.setWidth 32 + BitVec.ofNat 32 sPk
  else if r = .ebx ∨ r = .esi then E.out.setWidth 32
  else if r = .ecx then BitVec.ofNat 32 n
  else if r = .eax then 0
  else baseVal E r

theorem outPart_ct {g : Geo} {E : Env} (v : E.Valid) :
    RelCT isa (Both fun (o : COut) t => Base E t ∧ SRes E g t.mem o) g.outPart fun _ _ => True := by
  have sz := v.size_ge
  have hb : ∀ (o : COut) t, Base E t ∧ SRes E g t.mem o → Base E t := fun _ _ h => h.1
  unfold Geo.outPart
  simp only [seqs]
  refine cmpF_ct (o := fStatus) (v := 1) (by simp only [fStatus, hdr]; omega) (by decide) stOf hb
    (fun o t h => h.2.status) (fun o => by rcases o with _ | _ | _ <;> simp [stOf]) ?_ ?_
  · -- p||q||g out.
    refine RelCT.seq (both_post (Ψ := fun _ t => ∀ r ∈ [Reg.esp, .edi, .ebx, .esi, .ecx],
        t.gpr r = outPins E .esi (2 * g.pLen + g.qLen) r)
      (both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins (h.1.base hb))
        (tcheckE _ _ (.block ([.mov .ebx (.mem (sc 0))] ++ scr .esi 0 ++ [.mov .ecx (.imm 0)])) (by kernel_rfl)
          (by decide +kernel) (by decide +kernel))) fun R t h => ?_)
      (both_agree _ _ (fun _ _ h => h) (tcheck _ _ (by decide +kernel)))
    have B := h.1.base hb
    refine ld_ok B.scr (r := .ebx) (d := fOut) (by simp only [fOut, hdr]; omega) fun t₂ u₂ =>
      scr_ok fun t₃ e₃ g₃ m₃ _ _ _ => wp_movi fun t₄ u₄ => WP.block_nil ?_
    have pins := base_pins B
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₄.other _ (by decide), g₃ _ (by decide), u₂.other _ (by decide)]; exact pins _ (by simp)
    · rw [u₄.other _ (by decide), g₃ _ (by decide), u₂.other _ (by decide)]; exact pins _ (by simp)
    · rw [u₄.other _ (by decide), g₃ _ (by decide), u₂.gpr, B.outW]; rfl
    · rw [u₄.other _ (by decide), e₃, u₂.other _ (by decide), B.edi]; rfl
    · rw [u₄.gpr]; rfl
  · -- Zeros out.
    refine RelCT.seq (both_post (Ψ := fun _ t => ∀ r ∈ [Reg.esp, .edi, .esi, .ecx, .eax],
        t.gpr r = outPins E .edx (2 * g.pLen + g.qLen) r)
      (both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins (h.1.base hb))
        (tcheckE _ _ (.block [.mov .esi (.mem (sc 0)), .mov .ecx (.imm 0), .mov .eax (.imm 0)]) (by kernel_rfl)
          (by decide +kernel) (by decide +kernel))) fun R t h => ?_)
      (both_agree _ _ (fun _ _ h => h) (tcheck _ _ (by decide +kernel)))
    have B := h.1.base hb
    refine ld_ok B.scr (r := .esi) (d := fOut) (by simp only [fOut, hdr]; omega) fun t₂ u₂ =>
      wp_movi fun t₃ u₃ => wp_movi fun t₄ u₄ => WP.block_nil ?_
    have pins := base_pins B
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]; exact pins _ (by simp)
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]; exact pins _ (by simp)
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, B.outW]; rfl
    · rw [u₄.other _ (by decide), u₃.gpr]; rfl
    · rw [u₄.gpr]; rfl

/-- `esp`, `edi` and `ebx` the pointer `P`. -/
def ptrPins (E : Env) (P : Addr) (r : Reg) : BitVec 32 := if r = .ebx then P.setWidth 32 else baseVal E r

/-- The words of `state` and `used`: each block's stores go through `ebx`,
which the block before loaded with the same pointer in both runs. -/
theorem results_ct {E : Env} (v : E.Valid) {α : Type} {Φ : α → State → Prop} (hb : ∀ a t, Φ a t → Base E t)
    (u val : Nat) : RelCT isa (Both Φ) (Geo.results u val) fun _ _ => True := by
  have sz := v.size_ge
  have nw := v.scratchFit
  have sf := v.stFit
  unfold Geo.results
  simp only [seqs]
  refine RelCT.seq (both_post (Ψ := fun _ t => Base E t ∧ ∀ r ∈ [Reg.esp, .edi, .ebx], t.gpr r = ptrPins E E.stP r)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => base_pins (hb a t h))
      (tcheckE _ _ (.block [.mov .ebx (.mem (sc 0))]) (by kernel_rfl) (by decide +kernel) (by decide +kernel)))
    fun a t h => ?_) ?_
  · have B := hb a t h
    refine ld_ok B.scr (r := .ebx) (d := fStP) (by simp only [fStP, hdr]; omega) fun t₁ u₁ => WP.block_nil ?_
    refine ⟨B.regs u₁.mem (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.rd u₁.wr u₁.syms, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [u₁.other _ (by decide)]; exact base_pins B _ (by simp)
    · rw [u₁.other _ (by decide)]; exact base_pins B _ (by simp)
    · rw [u₁.gpr, B.stPW]; rfl
  refine RelCT.seq (both_post (Ψ := fun _ t => Base E t ∧ ∀ r ∈ [Reg.esp, .edi, .ebx], t.gpr r = ptrPins E E.usedP r)
    (both_agree [.esp, .edi, .ebx] (fun _ => ptrPins E E.stP) (fun a t h => h.2)
      (tcheckE _ _ (.block [.store (at_ .ebx 0) .edx, .store (at_ .ebx 0) .ecx, .mov .eax (.imm 0),
        .store (at_ .ebx 0) .eax, .store (at_ .ebx 0) .eax, .mov .ebx (.mem (sc 0))]) (by kernel_rfl)
        (by decide +kernel) (by decide +kernel))) fun a t h => ?_) ?_
  · obtain ⟨B, P⟩ := h
    have b₀ : t.gpr .ebx = E.stP.setWidth 32 := P .ebx (by simp)
    have cS : ∀ d, d + 4 ≤ 32 → E.stRegion.Contains (E.stP + BitVec.ofNat 64 d) 4 :=
      fun d h => Offset.contains_base _ h (by omega)
    refine stB_ok (P := E.stP) (d := 0) b₀ (by omega) B.stW (cS 0 (by omega)) fun t₂ M₂ => ?_
    refine stB_ok (P := E.stP) (d := 24) (by rw [M₂.gpr]; exact b₀) (by omega) (by rw [M₂.wr]; exact B.stW)
      (cS 24 (by omega)) fun t₃ M₃ => wp_movi fun t₄ u₄ => ?_
    have b₄ : t₄.gpr .ebx = E.stP.setWidth 32 := by rw [u₄.other _ (by decide), M₃.gpr, M₂.gpr, b₀]
    refine stB_ok (P := E.stP) (d := 4) b₄ (by omega) (by rw [u₄.wr, M₃.wr, M₂.wr]; exact B.stW)
      (cS 4 (by omega)) fun t₅ M₅ => ?_
    refine stB_ok (P := E.stP) (d := 28) (by rw [M₅.gpr]; exact b₄) (by omega)
      (by rw [M₅.wr, u₄.wr, M₃.wr, M₂.wr]; exact B.stW) (cS 28 (by omega)) fun t₆ M₆ => ?_
    have F₆ : Frame [E.stRegion] t.mem t₆.mem := by
      rw [M₆.mem, M₅.mem, u₄.mem, M₃.mem, M₂.mem]
      exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (cS 0 (by omega))).writeW List.mem_cons_self _
        (cS 24 (by omega))).writeW List.mem_cons_self _ (cS 4 (by omega))).writeW List.mem_cons_self _
        (cS 28 (by omega))
    have edi₆ : t₆.gpr .edi = t.gpr .edi := by
      rw [M₆.gpr, M₅.gpr, u₄.other _ (by decide), M₃.gpr, M₂.gpr]
    have esp₆ : t₆.gpr .esp = t.gpr .esp := by
      rw [M₆.gpr, M₅.gpr, u₄.other _ (by decide), M₃.gpr, M₂.gpr]
    have B₆ := B.frame v F₆ (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨(v.stFar _ List.mem_cons_self).symm, (v.stFar _ (by simp)).symm, (v.stFar _ (by simp)).symm⟩) edi₆ esp₆
      (by rw [M₆.rd, M₅.rd, u₄.rd, M₃.rd, M₂.rd]) (by rw [M₆.wr, M₅.wr, u₄.wr, M₃.wr, M₂.wr])
      (by rw [M₆.syms, M₅.syms, u₄.syms, M₃.syms, M₂.syms])
    refine ld_ok B₆.scr (r := .ebx) (d := fUsedP) (by simp only [fUsedP, hdr]; omega) fun t₇ u₇ => WP.block_nil ?_
    refine ⟨B₆.regs u₇.mem (u₇.other _ (by decide)) (u₇.other _ (by decide)) u₇.rd u₇.wr u₇.syms, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [u₇.other _ (by decide)]; exact base_pins B₆ _ (by simp)
    · rw [u₇.other _ (by decide)]; exact base_pins B₆ _ (by simp)
    · rw [u₇.gpr, B₆.usedPW]; rfl
  exact both_agree [.esp, .edi, .ebx] (fun _ => ptrPins E E.usedP) (fun a t h => h.2)
    (tcheckE _ _ (.block [.store (at_ .ebx 0) .eax, .mov .eax (.mem (sc 0)), .store (at_ .ebx 0) .eax,
      .mov .eax (.imm 0)]) (by kernel_rfl) (by decide +kernel) (by decide +kernel))

/-- `edx` and `ecx` zero, then the words. -/
theorem zeroResults_ct {E : Env} (v : E.Valid) {α : Type} {Φ : α → State → Prop} (hb : ∀ a t, Φ a t → Base E t)
    (u val : Nat) :
    RelCT isa (Both Φ) (.seq (.block [.mov .edx (.imm 0), .mov .ecx (.imm 0)]) (Geo.results u val))
      fun _ _ => True :=
  RelCT.seq (both_post (Ψ := fun _ t => Base E t)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => base_pins (hb a t h)) (tcheck _ _ (by decide +kernel)))
    fun a t h => wp_movi fun t₁ u₁ => wp_movi fun t₂ u₂ => WP.block_nil ((hb a t h).regs (by rw [u₂.mem, u₁.mem])
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
      (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) (by rw [u₂.syms, u₁.syms]))) (results_ct v (fun _ _ h => h) u val)

/-- The request after `rand` ran out: its branches are on the octets left. -/
theorem ranOut_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) :
    RelCT isa (Both fun (a : Nat × Nat) t => Base E t ∧
      t.mem.readW (off E.base fC) 32 = BitVec.ofNat 32 a.2 ∧ a.2 ≤ E.witLen) g.ranOut fun _ _ => True := by
  have sz := v.size_ge
  have bd := G.bounds
  have wl := v.witLen32
  have budget : g.budget < 2 ^ 32 := by simp only [Geo.budget]; omega
  have lb : 256 * g.pLen < 2 ^ 32 := by omega
  unfold Geo.ranOut
  simp only [seqs]
  -- The octets left, compared with the budget.
  refine RelCT.seq (both_post (Ψ := fun (a : Nat × Nat) t => Base E t ∧
      t.gpr .eax = BitVec.ofNat 32 (E.witLen - a.2) ∧ isa.eval .b t = some (decide (E.witLen - a.2 < g.budget)))
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => base_pins h.1) ?_) fun a t h => ?_) ?_
  · rcases G.lengths with ⟨h₁, _⟩ | ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> simp only [Geo.budget, h₁] <;>
      exact tcheck _ _ (by decide +kernel)
  · rw [← List.append_nil (Geo.avail ++ _), List.append_assoc]
    exact availCmp_ok v h.1 h.2.1 h.2.2 budget fun t' g' m' rd' wr' sy' e' c' =>
      WP.block_nil ⟨h.1.regs m' (g' _ (by decide) (by decide)) (g' _ (by decide) (by decide)) rd' wr' sy', e', c'⟩
  refine both_ite (fun a => decide (E.witLen - a.2 < g.budget)) (fun a t h => h.2.2) ?_
    (zeroResults_ct v (fun a t h => h.1.1) _ _)
  -- At least `256 p_len`.
  refine RelCT.seq (both_post (Ψ := fun (a : Nat × Nat) t => Base E t ∧
      t.gpr .eax = BitVec.ofNat 32 (E.witLen - a.2) ∧ E.witLen - a.2 < g.budget ∧
      isa.eval .b t = some (decide (E.witLen - a.2 < 256 * g.pLen)))
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => base_pins h.1.1) ?_) fun a t h => ?_) ?_
  · rcases G.lengths with ⟨h₁, _⟩ | ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> simp only [h₁] <;> exact tcheck _ _ (by decide +kernel)
  · have lt : E.witLen - a.2 < g.budget := of_decide_eq_true h.2
    refine wp_cmpi fun t₁ f₁ c₁ _ => WP.block_nil ⟨h.1.1.regs f₁.mem (by rw [f₁.gpr]) (by rw [f₁.gpr]) f₁.rd f₁.wr
      f₁.syms, by rw [f₁.gpr]; exact h.1.2.1, lt, ?_⟩
    show t₁.cf = _
    rw [c₁, h.1.2.1, toNat_ofNat_lt (by omega), toNat_ofNat_lt lb]
  refine RelCT.seq (both_post (Ψ := fun (a : Nat × Nat) t => Base E t ∧
      t.gpr .eax = BitVec.ofNat 32 (max (E.witLen - a.2) (256 * g.pLen)) ∧ E.witLen - a.2 < g.budget)
    (both_ite (fun a => decide (E.witLen - a.2 < 256 * g.pLen)) (fun a t h => h.2.2.2)
      (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => base_pins h.1.1)
        (tcheckE _ _ (.block [.mov .eax (.imm 0)]) (by kernel_rfl) (by decide +kernel) (by decide +kernel)))
      (RelCT.block_nil fun _ _ _ => trivial)) fun a t h => ?_) ?_
  · refine WP.ite _ h.2.2.2 (fun hl => wp_movi fun t₁ u₁ => WP.block_nil ⟨h.1.regs u₁.mem (u₁.other _ (by decide))
      (u₁.other _ (by decide)) u₁.rd u₁.wr u₁.syms, ?_, h.2.2.1⟩) (fun hl => WP.block_nil ⟨h.1, ?_, h.2.2.1⟩)
    · rw [u₁.gpr, Nat.max_eq_right (by have := of_decide_eq_true hl; omega)]
    · rw [h.2.1, Nat.max_eq_left (by have := of_decide_eq_false hl; omega)]
  -- Twice, at most the budget.
  refine RelCT.seq (both_post (Ψ := fun (a : Nat × Nat) t => Base E t ∧
      isa.eval .b t = some (decide (2 * max (E.witLen - a.2) (256 * g.pLen) < g.budget)))
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => base_pins h.1) ?_) fun a t h => ?_) ?_
  · rcases G.lengths with ⟨h₁, _⟩ | ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> simp only [Geo.budget, h₁] <;>
      exact tcheck _ _ (by decide +kernel)
  · have mx : max (E.witLen - a.2) (256 * g.pLen) < 2 ^ 31 := by
      have := h.2.2; simp only [Geo.budget] at this; omega
    refine wp_add fun t₁ u₁ _ => wp_cmpi fun t₂ f₂ c₂ _ => WP.block_nil ⟨h.1.regs (by rw [f₂.mem, u₁.mem])
      (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.rd, u₁.rd])
      (by rw [f₂.wr, u₁.wr]) (by rw [f₂.syms, u₁.syms]), ?_⟩
    show t₂.cf = _
    have a₁ : t₁.gpr .eax = BitVec.ofNat 32 (2 * max (E.witLen - a.2) (256 * g.pLen)) := by
      rw [u₁.gpr, h.2.1, ← BitVec.ofNat_add]; congr 1; omega
    rw [c₂, a₁, toNat_ofNat_lt (by omega), toNat_ofNat_lt budget]
  refine RelCT.seq (both_post (Ψ := fun _ t => Base E t)
    (both_ite (fun a => decide (2 * max (E.witLen - a.2) (256 * g.pLen) < g.budget)) (fun a t h => h.2)
      (RelCT.block_nil fun _ _ _ => trivial)
      (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => base_pins h.1.1)
        (tcheckE _ _ (.block [.mov .eax (.imm 0)]) (by kernel_rfl) (by decide +kernel) (by decide +kernel))))
    fun a t h => ?_) ?_
  · exact WP.ite _ h.2 (fun _ => WP.block_nil h.1) (fun _ => wp_movi fun t₁ u₁ => WP.block_nil (h.1.regs u₁.mem
      (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.rd u₁.wr u₁.syms))
  -- The seeds left, then the words.
  refine RelCT.seq (both_post (Ψ := fun _ t => Base E t)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => base_pins h) (tcheck _ _ (by decide +kernel)))
    fun a t h => ?_) (results_ct v (fun _ _ h => h) _ _)
  exact wp_mov fun t₁ u₁ => ld_ok (Scr.of_eq h.scr (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.wr)
    (r := .edx) (d := fSeedLeft) (by simp only [fSeedLeft, hdr]; omega) fun t₂ u₂ => WP.block_nil (h.regs
      (by rw [u₂.mem, u₁.mem]) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
      (by rw [u₂.syms, u₁.syms]))

/-- The cursor of the controller's end. -/
def cOf : COut → Nat
  | .found _ u => u
  | .noSeeds c => c
  | .ranOut _ c => c

theorem finish_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen) :
    RelCT isa (Both fun (o : COut) t => Base E t ∧ SRes E g t.mem o) g.finish fun _ _ => True := by
  have sz := v.size_ge
  have stLt : ∀ o : COut, stOf o < 2 ^ 32 := fun o => by rcases o with _ | _ | _ <;> simp [stOf]
  unfold Geo.finish
  simp only [seqs]
  refine RelCT.seq (both_post (Ψ := fun o t => Base E t ∧ SRes E g t.mem o) (outPart_ct v) fun o t h =>
    WP.mono (outPart_ok G v hp hq h.1 h.2) fun u ⟨_, F, e, p, r, w, y⟩ =>
      ⟨h.1.frame v F (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨v.outScratch.symm, v.witFar.2.1, v.tableFar.2.1⟩) e p r w y,
        h.2.frame G v F fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact v.outScratch.symm⟩) ?_
  have hb : ∀ (o : COut) t, Base E t ∧ SRes E g t.mem o → Base E t := fun _ _ h => h.1
  refine cmpF_ct (o := fStatus) (v := 1) (by simp only [fStatus, hdr]; omega) (by decide) stOf hb
    (fun o t h => h.2.status) stLt (zeroResults_ct v (fun o t h => h.1.base hb) _ _) ?_
  have hb₁ : ∀ (o : COut) t, (CmpAfter (fun o t => Base E t ∧ SRes E g t.mem o) o t ∧
      decide (stOf o = 1) = false) → Base E t := fun o t h => h.1.base hb
  refine cmpF_ct (o := fStatus) (v := 2) (by simp only [fStatus, hdr]; omega) (by decide) stOf hb₁
    (fun o t h => by obtain ⟨s, ⟨-, R⟩, m, -⟩ := h.1.elim; rw [m]; exact R.status) stLt ?_
    (zeroResults_ct v (fun o t h => h.1.base hb₁) _ _)
  refine both_map (fun o => (0, cOf o)) (fun o t h => ?_) (ranOut_ct G v)
  obtain ⟨C, h2⟩ := h
  obtain ⟨s₁, ⟨C₁, -⟩, m₁, e₁, p₁, r₁, w₁, y₁⟩ := C.elim
  obtain ⟨s, ⟨B, R⟩, m, e, p, r, w, y⟩ := C₁.elim
  refine ⟨(B.regs m e p r w y).regs m₁ e₁ p₁ r₁ w₁ y₁, ?_⟩
  rcases o with _ | _ | ⟨j, c⟩
  · simp [stOf] at h2
  · simp [stOf] at h2
  · exact ⟨by rw [m₁, m]; exact R.2.1, R.2.2.2.1⟩

theorem generate_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen) :
    RelCT isa (Both fun (_ : Unit) => SIn E) g.generate fun _ _ => True := by
  unfold Geo.generate
  refine RelCT.seq (both_post (Ψ := fun _ t => Base E t ∧ SRes E g t.mem (sOut E E.k0 0)) (search_ct G v hp hq)
    fun _ s ⟨B, hL, hC, hst⟩ => WP.mono (search_ok G v hp hq B hL hC hst) fun t ⟨K, R, _⟩ => ⟨K.base, R⟩) ?_
  exact both_map (fun _ => sOut E E.k0 0) (fun _ _ h => h) (finish_ct G v hp hq)

end VG.Proof.Dsa.X86.Generation
