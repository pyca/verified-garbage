module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Instances
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ABI
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Correct
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
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Entry
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ABIEntry
public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Dsa.X86.PowCallFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNoSpBase
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86

/-! ### `Dsa.X86.Generation.TopCT`, which only this module used -/

section

/-! ### `Dsa.X86.Generation.FinishCT`, which only this module used -/

section

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
  obtain hb : ∀ (o : COut) t, Base E t ∧ SRes E g t.mem o → Base E t := fun _ _ h => h.1
  unfold Geo.outPart
  simp only [seqs]
  refine cmpF_ct (o := fStatus) (v := 1) (by simp only [fStatus, hdr]; omega_using [sz]) (by decide) stOf hb
    (fun o t h => h.2.status) (fun o => by rcases o with _ | _ | _ <;> simp [stOf]) ?_ ?_
  · -- p||q||g out.
    refine RelCT.seq (both_post (Ψ := fun _ t => ∀ r ∈ [Reg.esp, .edi, .ebx, .esi, .ecx],
        t.gpr r = outPins E .esi (2 * g.pLen + g.qLen) r)
      (both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins (h.1.base hb))
        (tcheckE _ _ (.block ([.mov .ebx (.mem (sc 0))] ++ scr .esi 0 ++ [.mov .ecx (.imm 0)])) (by kernel_rfl)
          (by decide +kernel) (by decide +kernel))) fun R t h => ?_)
      (both_agree _ _ (fun _ _ h => h) (tcheck _ _ (by decide +kernel)))
    obtain B := h.1.base hb
    refine ld_ok B.scr (r := .ebx) (d := fOut) (by simp only [fOut, hdr]; omega_using [sz]) fun t₂ u₂ =>
      scr_ok fun t₃ e₃ g₃ m₃ _ _ _ => wp_movi fun t₄ u₄ => WP.block_nil ?_
    obtain pins := base_pins B
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
    obtain B := h.1.base hb
    refine ld_ok B.scr (r := .esi) (d := fOut) (by simp only [fOut, hdr]; omega_using [sz]) fun t₂ u₂ =>
      wp_movi fun t₃ u₃ => wp_movi fun t₄ u₄ => WP.block_nil ?_
    obtain pins := base_pins B
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
    refine ld_ok B.scr (r := .ebx) (d := fStP) (by simp only [fStP, hdr]; omega_using [sz]) fun t₁ u₁ => WP.block_nil ?_
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
    obtain b₀ : t.gpr .ebx = E.stP.setWidth 32 := P .ebx (by simp)
    obtain cS : ∀ d, d + 4 ≤ 32 → E.stRegion.Contains (E.stP + BitVec.ofNat 64 d) 4 :=
      fun d h => Offset.contains_base _ h (by omega_using [h])
    refine stB_ok (P := E.stP) (d := 0) b₀ (by omega_using [sf]) B.stW (cS 0 (by omega_using [])) fun t₂ M₂ => ?_
    refine stB_ok (P := E.stP) (d := 24) (by rw [M₂.gpr]; exact b₀) (by omega_using [sf]) (by rw [M₂.wr]; exact B.stW)
      (cS 24 (by omega_using [])) fun t₃ M₃ => wp_movi fun t₄ u₄ => ?_
    obtain b₄ : t₄.gpr .ebx = E.stP.setWidth 32 := by rw [u₄.other _ (by decide), M₃.gpr, M₂.gpr, b₀]
    refine stB_ok (P := E.stP) (d := 4) b₄ (by omega_using [sf]) (by rw [u₄.wr, M₃.wr, M₂.wr]; exact B.stW)
      (cS 4 (by omega_using [])) fun t₅ M₅ => ?_
    refine stB_ok (P := E.stP) (d := 28) (by rw [M₅.gpr]; exact b₄) (by omega_using [sf])
      (by rw [M₅.wr, u₄.wr, M₃.wr, M₂.wr]; exact B.stW) (cS 28 (by omega_using [])) fun t₆ M₆ => ?_
    obtain F₆ : Frame [E.stRegion] t.mem t₆.mem := by
      rw [M₆.mem, M₅.mem, u₄.mem, M₃.mem, M₂.mem]
      exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (cS 0 (by omega_using []))).writeW List.mem_cons_self _
        (cS 24 (by omega_using []))).writeW List.mem_cons_self _ (cS 4 (by omega_using []))).writeW List.mem_cons_self _
        (cS 28 (by omega_using []))
    obtain edi₆ : t₆.gpr .edi = t.gpr .edi := by
      rw [M₆.gpr, M₅.gpr, u₄.other _ (by decide), M₃.gpr, M₂.gpr]
    obtain esp₆ : t₆.gpr .esp = t.gpr .esp := by
      rw [M₆.gpr, M₅.gpr, u₄.other _ (by decide), M₃.gpr, M₂.gpr]
    obtain B₆ := B.frame v F₆ (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨(v.stFar _ List.mem_cons_self).symm, (v.stFar _ (by simp)).symm, (v.stFar _ (by simp)).symm⟩) edi₆ esp₆
      (by rw [M₆.rd, M₅.rd, u₄.rd, M₃.rd, M₂.rd]) (by rw [M₆.wr, M₅.wr, u₄.wr, M₃.wr, M₂.wr])
      (by rw [M₆.syms, M₅.syms, u₄.syms, M₃.syms, M₂.syms])
    refine ld_ok B₆.scr (r := .ebx) (d := fUsedP) (by simp only [fUsedP, hdr]; omega_using [sz]) fun t₇ u₇ => WP.block_nil ?_
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
  obtain budget : g.budget < 2 ^ 32 := by simp only [Geo.budget]; omega_using [bd]
  obtain lb : 256 * g.pLen < 2 ^ 32 := by omega_using [bd]
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
    rw [c₁, h.1.2.1, toNat_ofNat_lt (by omega_using [wl]), toNat_ofNat_lt lb]
  refine RelCT.seq (both_post (Ψ := fun (a : Nat × Nat) t => Base E t ∧
      t.gpr .eax = BitVec.ofNat 32 (max (E.witLen - a.2) (256 * g.pLen)) ∧ E.witLen - a.2 < g.budget)
    (both_ite (fun a => decide (E.witLen - a.2 < 256 * g.pLen)) (fun a t h => h.2.2.2)
      (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => base_pins h.1.1)
        (tcheckE _ _ (.block [.mov .eax (.imm 0)]) (by kernel_rfl) (by decide +kernel) (by decide +kernel)))
      (RelCT.block_nil fun _ _ _ => trivial)) fun a t h => ?_) ?_
  · refine WP.ite _ h.2.2.2 (fun hl => wp_movi fun t₁ u₁ => WP.block_nil ⟨h.1.regs u₁.mem (u₁.other _ (by decide))
      (u₁.other _ (by decide)) u₁.rd u₁.wr u₁.syms, ?_, h.2.2.1⟩) (fun hl => WP.block_nil ⟨h.1, ?_, h.2.2.1⟩)
    · rw [u₁.gpr, Nat.max_eq_right (by have := of_decide_eq_true hl; omega_using [this])]
    · rw [h.2.1, Nat.max_eq_left (by have := of_decide_eq_false hl; omega_using [this])]
  -- Twice, at most the budget.
  refine RelCT.seq (both_post (Ψ := fun (a : Nat × Nat) t => Base E t ∧
      isa.eval .b t = some (decide (2 * max (E.witLen - a.2) (256 * g.pLen) < g.budget)))
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => base_pins h.1) ?_) fun a t h => ?_) ?_
  · rcases G.lengths with ⟨h₁, _⟩ | ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> simp only [Geo.budget, h₁] <;>
      exact tcheck _ _ (by decide +kernel)
  · have mx : max (E.witLen - a.2) (256 * g.pLen) < 2 ^ 31 := by
      have := h.2.2; simp only [Geo.budget] at this; omega_using [bd, this]
    refine wp_add fun t₁ u₁ _ => wp_cmpi fun t₂ f₂ c₂ _ => WP.block_nil ⟨h.1.regs (by rw [f₂.mem, u₁.mem])
      (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.rd, u₁.rd])
      (by rw [f₂.wr, u₁.wr]) (by rw [f₂.syms, u₁.syms]), ?_⟩
    show t₂.cf = _
    obtain a₁ : t₁.gpr .eax = BitVec.ofNat 32 (2 * max (E.witLen - a.2) (256 * g.pLen)) := by
      rw [u₁.gpr, h.2.1, ← BitVec.ofNat_add]; congr 1; omega_using []
    rw [c₂, a₁, toNat_ofNat_lt (by omega_using [mx]), toNat_ofNat_lt budget]
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
    (r := .edx) (d := fSeedLeft) (by simp only [fSeedLeft, hdr]; omega_using [sz]) fun t₂ u₂ => WP.block_nil (h.regs
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
  obtain stLt : ∀ o : COut, stOf o < 2 ^ 32 := fun o => by rcases o with _ | _ | _ <;> simp [stOf]
  unfold Geo.finish
  simp only [seqs]
  refine RelCT.seq (both_post (Ψ := fun o t => Base E t ∧ SRes E g t.mem o) (outPart_ct v) fun o t h =>
    WP.mono (outPart_ok G v hp hq h.1 h.2) fun u ⟨_, F, e, p, r, w, y⟩ =>
      ⟨h.1.frame v F (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨v.outScratch.symm, v.witFar.2.1, v.tableFar.2.1⟩) e p r w y,
        h.2.frame G v F fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact v.outScratch.symm⟩) ?_
  obtain hb : ∀ (o : COut) t, Base E t ∧ SRes E g t.mem o → Base E t := fun _ _ h => h.1
  refine cmpF_ct (o := fStatus) (v := 1) (by simp only [fStatus, hdr]; omega_using [sz]) (by decide) stOf hb
    (fun o t h => h.2.status) stLt (zeroResults_ct v (fun o t h => h.1.base hb) _ _) ?_
  obtain hb₁ : ∀ (o : COut) t, (CmpAfter (fun o t => Base E t ∧ SRes E g t.mem o) o t ∧
      decide (stOf o = 1) = false) → Base E t := fun o t h => h.1.base hb
  refine cmpF_ct (o := fStatus) (v := 2) (by simp only [fStatus, hdr]; omega_using [sz]) (by decide) stOf hb₁
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

end

end


/-! # Parameter generation's trace depends only on its public inputs -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Proof.Mont.X86.Compact (entered savedRegisters)

theorem map_toNat_inj : ∀ {l₁ l₂ : List Byte}, l₁.map (fun x => x.toNat) = l₂.map (fun x => x.toNat) → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem map_toNat_inj64 {a b : List (BitVec 64)} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

theorem pub_env {s₁ s₂ : State} (h : genContract.pub s₁ s₂) :
    callEnv s₁ = callEnv s₂ ∧ s₁.gpr .esp = s₂.gpr .esp := by
  sig_pub [genContract, Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts] at h
  obtain ⟨esp, sy, leak, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
  rw [a3, a4, a7] at leak
  obtain ⟨lw, lb⟩ := List.append_inj leak (by simp [Spec.Rsa.wordsAt])
  obtain eW := map_toNat_inj64 lw
  change [s₁.mem.readW (BitVec.setWidth 64 (arg s₂ 7) + BitVec.ofNat 64 0) 64,
      s₁.mem.readW (BitVec.setWidth 64 (arg s₂ 7) + 8) 64, _, _] =
    [s₂.mem.readW (BitVec.setWidth 64 (arg s₂ 7) + BitVec.ofNat 64 0) 64,
      s₂.mem.readW (BitVec.setWidth 64 (arg s₂ 7) + 8) 64, _, _] at eW
  simp only [List.cons.injEq] at eW
  obtain ⟨w0, w1, -, -, -⟩ := eW
  obtain e0 : BitVec.setWidth 64 (arg s₂ 7) + BitVec.ofNat 64 0 = BitVec.setWidth 64 (arg s₂ 7) := by simp
  rw [e0] at w0
  refine ⟨?_, esp⟩
  simp only [callEnv, pLenOf, a0, a2, a3, a4, a5, a6, a7, esp, sy, w0, w1, map_toNat_inj lb]

/-- At the entry: the frame of saved registers pushed, from a state the
contract holds in. -/
def TIn (E : Env) (t : State) : Prop := ∃ s, callEnv s = E ∧ CallFacts s ∧ t = entered s

/-- After the entry. -/
def TEnt (E : Env) (t : State) : Prop := ∃ s, callEnv s = E ∧ CallFacts s ∧ EPost s t

theorem entry_ct : RelCT isa (Both TIn) (.block entry) fun _ _ => True := by
  rw [show entry = [.mov .edi (.mem (VG.Impl.Mont.X86.Compact.arg 5))] ++ entry.tail from rfl]
  refine RelCT.block_append (RelCT.seq (both_post (Ψ := fun E t => ∀ r ∈ [Reg.esp, .edi], t.gpr r = baseVal E r)
    (both_agree [.esp] (fun E => baseVal E) (fun E t h r hr => ?_) (tcheck _ _ (by decide +kernel)))
    fun E t h => ?_) (both_agree [.esp, .edi] (fun E => baseVal E) (fun _ _ h => h) (tcheck _ _ (by decide +kernel))))
  · obtain ⟨s, rfl, F, rfl⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact (entered_inv F).esp
  · obtain ⟨s, rfl, F, rfl⟩ := h
    obtain I₀ := entered_inv F
    refine wp_ldm (B := (callEnv s).sp) I₀.esp (by rw [addrArg]; exact argAccess F I₀ (by decide))
      fun t₀ u₀ => WP.block_nil fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [u₀.other _ (by decide)]; exact I₀.esp
    · rw [u₀.gpr, addrArg, argValue F I₀ (by decide)]
      exact (narrow _).symm

/-- After the pointer to `state`. -/
def TPtr (E : Env) (t : State) : Prop := ∃ s t₀, callEnv s = E ∧ CallFacts s ∧ EPost s t₀ ∧ DPtr s t₀ t

/-- After `state`'s reads, then the comparison of its width with `c`. -/
def TCmp (c : Nat) (E : Env) (t : State) : Prop :=
  ∃ s, callEnv s = E ∧ CallFacts s ∧ SIn E t ∧ t.gpr .eax = BitVec.ofNat 32 E.pLen ∧
    isa.eval .e t = some (decide (E.pLen = c))

theorem TCmp.pins {c : Nat} {E : Env} {t : State} (h : TCmp c E t) : ∀ r ∈ [Reg.esp], t.gpr r = baseVal E r := by
  obtain ⟨s, rfl, F, ⟨B, _⟩, _⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact B.sp

/-- One geometry, chosen by `state[1]`. -/
theorem run_ct {g : Geo} (G : GeoOk g) {c : Nat} {Φ : Env → State → Prop} (hd : ∀ E t, Φ E t → TCmp c E t)
    (hpl : ∀ E t, Φ E t → E.pLen = g.pLen) : RelCT isa (Both Φ) g.generate fun _ _ => True := by
  refine both_exists fun E => relct_of_fact (P := E.Valid ∧ E.pLen = g.pLen ∧ E.qLen = g.qLen)
    (fun s t h => ?_) fun ⟨v, hp, hq⟩ =>
      (generate_ct G v hp hq).mono (fun s t h => ⟨(), by obtain ⟨_, _, _, I, _⟩ := hd _ _ h.1; exact I,
        by obtain ⟨_, _, _, I, _⟩ := hd _ _ h.2; exact I⟩) fun _ _ h => h
  obtain hp := hpl _ _ h.1
  obtain ⟨s', rfl, F, _⟩ := hd _ _ h.1
  refine ⟨F.valid, hp, ?_⟩
  have := G.lengths
  change pLenOf s' = _ at hp
  change (if pLenOf s' = 128 then 20 else 32) = _
  split <;> omega

theorem dispatch_ct {g1 g2 g3 : Geo} (G1 : GeoOk g1) (G2 : GeoOk g2) (G3 : GeoOk g3) (h1 : g1.pLen = 128)
    (h2 : g2.pLen = 256) (h3 : g3.pLen = 384) :
    RelCT isa (Both TEnt) (dispatch g1 g2 g3) fun _ _ => True := by
  unfold dispatch
  simp only [seqs]
  refine RelCT.seq (both_post (Ψ := TPtr)
    (both_agree [.esp] (fun E => baseVal E) (fun E t h r hr => ?_) (tcheck _ _ (by decide +kernel)))
    fun E t h => ?_) ?_
  · obtain ⟨s, rfl, F, P⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact P.inv.esp
  · obtain ⟨s, rfl, F, P⟩ := h
    exact WP.mono (dPtr_ok F P) fun t₁ D => ⟨s, t, rfl, F, P, D⟩
  refine RelCT.seq (both_post (Ψ := TCmp 128)
    (both_agree [.esp, .edi, .ebx] (fun E => ptrPins E E.stP) (fun E t h r hr => ?_)
      (tcheck _ _ (by decide +kernel))) fun E t h => ?_) ?_
  · obtain ⟨s, t₀, rfl, F, P, D⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [D.esp]; exact P.inv.esp
    · rw [D.edi]; exact P.base.edi
    · rw [D.ebx]; exact (narrow _).symm
  · obtain ⟨s, t₀, rfl, F, P, D⟩ := h
    exact WP.mono (dRead_ok F P D) fun t₅ R => ⟨s, rfl, F, ⟨R.base, R.left, R.cur, R.status⟩, R.eax, R.zf⟩
  refine both_ite (fun E => decide (E.pLen = 128)) (fun E t h => by obtain ⟨_, _, _, _, _, z⟩ := h; exact z)
    (run_ct G1 (fun _ _ h => h.1) fun E t h => by rw [h1]; exact of_decide_eq_true h.2) ?_
  refine RelCT.seq (both_post (Ψ := fun E t => TCmp 256 E t ∧ decide (E.pLen = 128) = false)
    (both_agree [.esp] (fun E => baseVal E) (fun E t h => h.1.pins) (tcheck _ _ (by decide +kernel)))
    fun E t h => ?_) ?_
  · obtain ⟨⟨s, rfl, F, I, ax, _⟩, n⟩ := h
    obtain p32 : pLenOf s < 2 ^ 32 := by rcases F.pLens with h | h | h <;> rw [h] <;> decide
    refine wp_cmpi fun t₃ f₃ _ z₃ => WP.block_nil ⟨⟨s, rfl, F, ⟨I.1.regs f₃.mem (by rw [f₃.gpr]) (by rw [f₃.gpr])
      f₃.rd f₃.wr f₃.syms, by rw [f₃.mem]; exact I.2.1, by rw [f₃.mem]; exact I.2.2.1, by rw [f₃.mem]; exact I.2.2.2⟩,
      by rw [f₃.gpr, ax], ?_⟩, n⟩
    show t₃.zf = _
    rw [z₃, ax]
    exact congrArg some (sub_beq (b := 256) p32 (by decide))
  refine both_ite (fun E => decide (E.pLen = 256))
    (fun E t h => by obtain ⟨⟨_, _, _, _, _, z⟩, _⟩ := h; exact z)
    (run_ct G2 (fun _ _ h => h.1.1) fun E t h => by rw [h2]; exact of_decide_eq_true h.2)
    (run_ct G3 (fun _ _ h => h.1.1) fun E t h => ?_)
  obtain ⟨⟨⟨s, rfl, F, _⟩, n128⟩, n256⟩ := h
  obtain a := of_decide_eq_false n128
  obtain b := of_decide_eq_false n256
  rw [h3]
  change ¬ pLenOf s = 128 at a
  change ¬ pLenOf s = 256 at b
  change pLenOf s = 384
  rcases F.pLens with c | c | c <;> omega_arith

/-- Two runs from inputs the contract makes public leak the same. -/
theorem constantTime {g1 g2 g3 : Geo} (G1 : GeoOk g1) (G2 : GeoOk g2) (G3 : GeoOk g3) (h1 : g1.pLen = 128)
    (h2 : g2.pLen = 256) (h3 : g3.pLen = 384) :
    ConstantTime isa genContract.pre genContract.pub (code g1 g2 g3) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold code
  refine RelCT.frame (R := fun _ _ => True) (fun s₁ s₂ h => (pub_env h.2.2).2) ?_
  refine RelCT.seq (R := VG.X86.Taint.Agree (τr [.esp])) ?_ (tcheck [.esp] _ (by decide +kernel))
  obtain body := RelCT.seq (both_post (Ψ := TEnt) entry_ct
    fun E t ⟨s, hE, F, ht⟩ => ht ▸ WP.mono (entry_ok F) fun u P => ⟨s, hE, F, P⟩) (dispatch_ct G1 G2 G3 h1 h2 h3)
  refine ((body.mono (fun a b ⟨s₁, s₂, ⟨p₁, p₂, pb⟩, ha, hb⟩ => ⟨callEnv s₁, ⟨s₁, rfl, call_facts p₁, ha⟩,
      ⟨s₂, (pub_env pb).1.symm, call_facts p₂, hb⟩⟩) fun _ _ h => h).wpDep
    (F := fun (σ u : State) => u.gpr .esp = σ.gpr .esp) fun a b h => ?_).mono (fun _ _ h => h)
    fun a' b' ⟨_, σ₁, σ₂, H, e₁, e₂⟩ => agree_regs fun r hr => ?_
  · obtain ⟨s₁, s₂, ⟨p₁, p₂, _⟩, rfl, rfl⟩ := h
    exact ⟨WP.mono (body_ok G1 G2 G3 h1 h2 h3 (call_facts p₁)) fun t ⟨_, _, K⟩ => K.1 .esp (by decide),
      WP.mono (body_ok G1 G2 G3 h1 h2 h3 (call_facts p₂)) fun t ⟨_, _, K⟩ => K.1 .esp (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    obtain ⟨s₁, s₂, ⟨_, _, pb⟩, rfl, rfl⟩ := H
    rw [e₁, e₂, pushed_esp, pushed_esp, (pub_env pb).2]

end VG.Proof.Dsa.X86.Generation

end

end

/-! ### `Dsa.X86.Generation.Satisfiable`, which only this module used -/

section

/-! # A state meets the precondition: 1024-bit p, 160-bit q, an empty tape

`state` at `0x12000` holds `[0, 128, 32769 · 128, 0]`. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86

def satArgument : Nat → BitVec 32
  | 0 => 0x10000
  | 1 => 276
  | 2 => 0x11000
  | 3 => 0x20000
  | 4 => 0
  | 5 => 0x100000
  | 6 => 9216
  | _ => 0x12000

/-- The arguments at the stack pointer plus 4. -/
def satArguments : Mem := fun a =>
  (satArgument ((a - 0x80004#64).toNat / 4)).extractLsb' (8 * ((a - 0x80004#64).toNat % 4)) 8

def satMemory : Mem := fun a =>
  if (a - 0x80004#64).toNat < 32 then satArguments a
  else if a.toNat = 0x12008 then 0x80
  else if a.toNat = 0x12010 then 0x80
  else if a.toNat = 0x12012 then 0x40
  else constMem 0x30000#64 VG.Impl.RsaKeyGen.TrialTable32.packed a

def satState : State where
  gpr r := if r = .esp then 0x80000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemory
  rd := [⟨0x20000, 0⟩, ⟨0x30000, 8192⟩]
  wr := [⟨0x10000, 276⟩, ⟨0x11000, 8⟩, ⟨0x100000, 73728⟩, ⟨0x12000, 32⟩, ⟨0x80004, 32⟩]
  syms _ := 0x30000

theorem sat_argument_word (i : Nat) (index : i < 8) :
    satArguments.readW (BitVec.ofNat 64 (0x80004 + 4 * i)) 32 = satArgument i := by
  obtain cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega_using [index]
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem sat_arguments (i : Nat) (index : i < 8) : arg satState i = satArgument i := by
  obtain address : argAddr satState i = BitVec.ofNat 64 (0x80004 + 4 * i) := by
    change ((0x80000#32 + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64) = _
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using [index]
  unfold arg
  rw [address, ← sat_argument_word i index]
  apply Mem.readW_congr
  intro j hj
  change (if _ then _ else _) = _
  refine ite_eq_left ?_
  change ((BitVec.ofNat 64 (0x80004 + 4 * i) + BitVec.ofNat 64 j) - 0x80004#64).toNat < 32
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [index, hj]

private theorem single_held {m : Mem} {f : String → Addr} {name : String} {words : List (BitVec 64)}
    (H : ∀ i < words.length, m.readW (f name + BitVec.ofNat 64 (8 * i)) 64 = words.getD i 0) :
    Abi.constsHeld m f [(name, words)] := by
  intro c mem
  obtain rfl := List.mem_singleton.mp mem
  exact H

private theorem packed_regions (f : String → Addr) :
    Abi.constRegions f [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] =
      [⟨f VG.Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩] := by
  rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.Dsa.X86.ProbablePrime.packed_length]

theorem sat_table :
    Abi.constsHeld satState.mem (fun name => (satState.syms name).setWidth 64)
      VG.Impl.RsaKeyGen.TrialTable32.consts := by
  apply single_held
  intro i index
  obtain fit : 8 * VG.Impl.RsaKeyGen.TrialTable32.packed.length ≤ 2 ^ 64 := by
    rw [VG.Proof.Dsa.X86.ProbablePrime.packed_length]; decide
  obtain small : i < 1024 := by simpa only [VG.Proof.Dsa.X86.ProbablePrime.packed_length] using index
  change satMemory.readW (0x30000#64 + BitVec.ofNat 64 (8 * i)) 64 =
    VG.Impl.RsaKeyGen.TrialTable32.packed.getD i 0
  obtain held := constMem_held 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed fit i index
  refine Eq.trans (Mem.readW_congr (m := satMemory)
    (m' := constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed) ?_) held
  intro j hj
  obtain e : (0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat = 0x30000 + 8 * i + j := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [small, hj]
  change (if _ then _ else if _ then _ else if _ then _ else if _ then _ else _) = _
  rw [ite_eq_right (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [small, hj]),
    ite_eq_right (by rw [e]; omega_using []), ite_eq_right (by rw [e]; omega_using []), ite_eq_right (by rw [e]; omega_using [])]
  rfl

theorem sat_w0 : satMemory.readW (BitVec.setWidth 64 (satArgument 7)) 64 = 0#64 := by decide +kernel

theorem sat_w8 : satMemory.readW (BitVec.setWidth 64 (satArgument 7) + 8) 64 = 128#64 := by decide +kernel

theorem sat_w16 : satMemory.readW (BitVec.setWidth 64 (satArgument 7) + 16) 64 = BitVec.ofNat 64 (32769 * 128) := by
  decide +kernel

theorem sat_argAddr : argAddr satState 0 = 0x80004#64 := by
  change ((0x80000#32 + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64) = _
  decide

theorem satisfiable : ∃ s, genContract.pre s := by
  refine ⟨satState, ?_⟩
  sig_pre [genContract, Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, stackBelow]
  simp only [sat_arguments 0 (by decide), sat_arguments 1 (by decide), sat_arguments 2 (by decide),
    sat_arguments 3 (by decide), sat_arguments 4 (by decide), sat_arguments 5 (by decide),
    sat_arguments 6 (by decide), sat_arguments 7 (by decide), sat_argAddr]
  simp only [packed_regions, List.forall_mem_singleton]
  simp only [sat_w0, sat_w8, sat_w16]
  sig_and_intros
  all_goals first
    | exact sat_table
    | rfl
    | decide +kernel
    | exact Region.disjoint_of_sep (by decide +kernel)

end VG.Proof.Dsa.X86.Generation

end

end

/-! ### `Dsa.X86.Generation.NoSp`, which only this module used -/

section

/-! # Parameter generation never writes ESP outside its frames -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

theorem checked {c : Prog isa} (H : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  rw [H i hi]
  rfl

theorem nosp_seq {a b : Prog isa} (A : NoSp a) (B : NoSp b) : NoSp (.seq a b) := fun i hi =>
  (List.mem_append.mp hi).elim (A i) (B i)

theorem nosp_seqs {l : List (Prog isa)} (h : ∀ p ∈ l, NoSp p) : NoSp (seqs l) := by
  induction l with
  | nil => exact NoSp.of_all rfl
  | cons p ps ih =>
    cases ps with
    | nil => exact h p List.mem_cons_self
    | cons q qs =>
      exact nosp_seq (h p List.mem_cons_self) (ih fun r hr => h r (List.mem_cons_of_mem _ hr))

theorem storeW_mem {dst : Reg} {o : Nat} {xs : List Byte} {n : Nat} {i : Instr}
    (h : i ∈ Impl.Pbkdf2.Md.X86.storeW dst o xs n) : Taint.clobbers i .esp = false := by
  obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl <;> rfl

theorem hash_noSp (H : Impl.Pbkdf2.Md.X86.Hash) (iv : List (BitVec 32)) (n dst : Nat) (hc : NoSp H.compC)
    (hout : ∀ i ∈ H.out, Taint.clobbers i .esp = false) : NoSp (hash H iv n dst) := by
  unfold VG.Impl.Dsa.X86.Generation.hash
  simp only [seqs]
  refine nosp_seq ?_ (nosp_seq ?_ ?_)
  · intro i hi
    simp only [instrs, ivStore, scr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with (((((rfl | rfl) | h) | h) | (rfl | rfl)) | (rfl | rfl))
    all_goals first | rfl | exact storeW_mem h
  · apply NoSp.of_all
    simp only [Impl.MdStream.X86.compressAt, Impl.MdStream.X86.compressWith, Code.allInstrs, checked hc]
    rfl
  · intro i hi
    simp only [instrs, scr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with ((rfl | rfl) | (rfl | rfl)) | h
    all_goals first | rfl | exact hout i h

theorem test_noSp (name : String) {callee : Prog isa} (C : NoSp callee) : NoSp (test name callee) := by
  apply NoSp.of_all
  simp only [test, seqs, Code.allInstrs, checked C]
  rfl

theorem check_call_noSp (pLen qLen chkWords : Nat) (name : String) {callee : Prog isa} (C : NoSp callee) :
    NoSp (check pLen qLen chkWords name callee) := by
  apply NoSp.of_all
  simp only [check, seqs, Code.allInstrs, checked C]
  rfl

theorem pArith_noSp (pLen qLen : Nat) : NoSp (pArith pLen qLen) := by
  apply NoSp.of_all
  simp only [pArith, seqs, Code.allInstrs, checked (VG.Proof.RsaKeyGen.X86.KeyNoSp.constant _ _ _)]
  rfl

theorem pow_noSp (n e : Nat) : NoSp (Impl.Dsa.X86.Pow.call n e) := by
  apply NoSp.of_all
  simp only [Impl.Dsa.X86.Pow.call, Code.allInstrs, checked (Proof.Dsa.X86.Pow.body_noSp n e)]
  rfl

namespace Geo
variable {g : Geo} (hc : NoSp g.H.compC) (hout : ∀ i ∈ g.H.out, Taint.clobbers i .esp = false)
  (hq : NoSp g.qCode) (hp : NoSp g.pCode) (hk : NoSp g.checkCode)
include hc hout

omit hc hout in
theorem seedIn_noSp' (g : Geo) : NoSp g.seedIn := NoSp.of_all (by rfl)

theorem qPart_noSp (hq : NoSp g.qCode) : NoSp g.qPart := by
  apply NoSp.of_all
  simp only [Geo.qPart, seqs, Code.allInstrs, checked (seedIn_noSp' g), checked (hash_noSp _ _ _ _ hc hout),
    checked (test_noSp _ hq)]
  rfl

theorem pHash_noSp (j : Nat) : NoSp (g.pHash j) := by
  apply NoSp.of_all
  simp only [Geo.pHash, seqs, Code.allInstrs, checked (seedIn_noSp' g), checked (hash_noSp _ _ _ _ hc hout)]
  rfl

theorem pX_noSp : NoSp g.pX := by
  unfold Geo.pX
  refine nosp_seqs fun p hp => ?_
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hp
  rcases hp with ⟨j, _, rfl⟩ | rfl
  · exact pHash_noSp hc hout j
  · exact NoSp.of_all rfl

theorem pAttempt_noSp (hp : NoSp g.pCode) : NoSp g.pAttempt := by
  apply NoSp.of_all
  simp only [Geo.pAttempt, seqs, Code.allInstrs, checked (pX_noSp hc hout), checked (pArith_noSp _ _),
    checked (test_noSp _ hp)]
  rfl

theorem pPart_noSp (hp : NoSp g.pCode) : NoSp g.pPart := by
  apply NoSp.of_all
  simp only [Geo.pPart, seqs, Code.allInstrs, checked (pAttempt_noSp hc hout hp)]
  rfl

omit hc hout in
theorem gStep_noSp (g : Geo) : NoSp g.gStep := by
  apply NoSp.of_all
  simp only [Geo.gStep, seqs, Code.allInstrs, checked (pow_noSp _ _)]
  rfl

omit hc hout in
theorem gPart_noSp (g : Geo) : NoSp g.gPart := by
  apply NoSp.of_all
  simp only [Geo.gPart, seqs, Code.allInstrs, checked (gStep_noSp g)]
  rfl

theorem attempt_noSp (hq : NoSp g.qCode) (hp : NoSp g.pCode) (hk : NoSp g.checkCode) : NoSp g.attempt := by
  apply NoSp.of_all
  simp only [Geo.attempt, Geo.gWindow, Geo.gShort, seqs, Code.allInstrs, checked (qPart_noSp hc hout hq),
    checked (pPart_noSp hc hout hp), checked (gPart_noSp g), checked (check_call_noSp _ _ _ _ hk)]
  rfl

theorem generate_noSp (hq : NoSp g.qCode) (hp : NoSp g.pCode) (hk : NoSp g.checkCode) : NoSp g.generate := by
  apply NoSp.of_all
  simp only [Geo.generate, Geo.search, Geo.finish, Geo.outPart, Geo.ranOut, Geo.accepted, Geo.exhausted,
    Geo.results, seqs, Code.allInstrs, checked (attempt_noSp hc hout hq hp hk)]
  rfl

end Geo

end VG.Proof.Dsa.X86.Generation

end

end


/-! # DSA parameter generation on i686 is verified

And the pairs of a SHA-1 and a SHA-256 backend that it is emitted for
(`hashPairs`). -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Dsa.X86.Generation

theorem body_noSp {g1 g2 g3 : Geo} (n1 : NoSp g1.generate) (n2 : NoSp g2.generate) (n3 : NoSp g3.generate) :
    NoSp (.seq (.seq (.block entry) (dispatch g1 g2 g3)) (.block VG.Impl.Mont.X86.Compact.restoreRegs)) := by
  apply NoSp.of_all
  simp only [dispatch, seqs, Code.allInstrs, checked n1, checked n2, checked n3]
  rfl

theorem generate1_noSp (v1 : Proof.Sha1.X86.Variants.Backend) (v : RoundImpl) : NoSp (geo1 v1 v).generate :=
  Geo.generate_noSp v1.cmpSp sha1_outNoSp (geo1Ok v1 v).qNoSp (geo1Ok v1 v).pNoSp (geo1Ok v1 v).cNoSp

theorem generate256_noSp (pLen : Nat) (v256 : Proof.Sha256.X86.Variants.Backend) (v : RoundImpl) :
    NoSp (geo256 pLen v256 v).generate :=
  Geo.generate_noSp v256.cmpSp sha256_outNoSp (ProbablePrime.code_noSp compact_noSp v.noSp _ _ _)
    (ProbablePrime.code_noSp compact_noSp v.noSp _ _ _) check_noSp

theorem verified (v1 : Proof.Sha1.X86.Variants.Backend) (v256 : Proof.Sha256.X86.Variants.Backend) (v : RoundImpl) :
    Verified target (code (geo1 v1 v) (geo256 256 v256 v) (geo256 384 v256 v)) genContract :=
  ⟨correct (geo1Ok v1 v) (geo2Ok v256 v) (geo3Ok v256 v) rfl rfl rfl
      (body_noSp (generate1_noSp v1 v) (generate256_noSp 256 v256 v) (generate256_noSp 384 v256 v)),
    constantTime (geo1Ok v1 v) (geo2Ok v256 v) (geo3Ok v256 v) rfl rfl rfl, satisfiable⟩

theorem writesSp_false {i : Instr} (h : VG.X86.Taint.clobbers i .esp = false) : isa.writesSp i = false := by
  cases i <;> simp_all [VG.X86.Taint.clobbers, VG.X86.Taint.dst, Instr.dst]

theorem code_all (v1 : Proof.Sha1.X86.Variants.Backend) (v256 : Proof.Sha256.X86.Variants.Backend) (v : RoundImpl) :
    (code (geo1 v1 v) (geo256 256 v256 v) (geo256 384 v256 v)).all (fun i => !isa.writesSp i) = true := by
  obtain hb := body_noSp (generate1_noSp v1 v) (generate256_noSp 256 v256 v) (generate256_noSp 384 v256 v)
  refine Code.all_of_allInstrs ?_
  simp only [code, Code.allInstrs]
  obtain inner : Code.allInstrs (fun i => !isa.writesSp i)
      (.seq (.seq (.block entry) (dispatch (geo1 v1 v) (geo256 256 v256 v) (geo256 384 v256 v)))
        (.block VG.Impl.Mont.X86.Compact.restoreRegs)) = true := by
    rw [Code.allInstrs_eq, List.all_eq_true]
    intro i hi
    rw [writesSp_false (hb i hi)]
    rfl
  simp only [Code.allInstrs] at inner
  simp only [inner]
  rfl

/-- The pairs of a SHA-1 and a SHA-256 backend that the parameter search is
emitted for, best first: those for the same CPUs (both baselines or both SHA
extensions). Either other pair needs the features of one of these, which
runs both hashes with them. -/
def hashPairs : List (Proof.Sha1.X86.Variants.Backend × Proof.Sha256.X86.Variants.Backend) :=
  Proof.Variants.Sha1.X86.variants.flatMap fun v1 => Proof.Variants.Sha256.X86.variants.filterMap fun v256 =>
    if v1.suffix == v256.suffix then some (v1, v256) else none

end VG.Proof.Dsa.X86.Generation
