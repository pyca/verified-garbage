module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.GPart
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TimingFlags
import VerifiedGarbage.Proof.Dsa.X86.PowCallTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Two runs of the generator from the same `p` and `q` leak the same -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)
open VG.Impl.Mont.X86.Dynamic (chainW selectsW slot)

/-- `h` number `j` as a number. -/
abbrev hVal (E : Env) (j : Nat) : Nat := Spec.Dsa.decodeBE (hChunk E j)

/-- Before `h` number `a.1`, with `p`, `(p − 1)/q` and `fG` at `a.2`. -/
structure GSIn (E : Env) (g : Geo) (a : Nat × Nat × Nat × Nat) (s : State) : Prop where
  base : Base E s
  hj : (a.1 + 1) * E.pLen ≤ E.hsLen
  hH : s.mem.readW (off E.base fH) 32 = (E.hs + BitVec.ofNat 64 (a.1 * E.pLen)).setWidth 32
  hone : val32 s.mem E.base aOne g.n32 = 1
  hpm1 : val32 s.mem E.base aPm1 g.n32 = a.2.1 - 1
  hP : val32 s.mem E.base aP g.n32 = a.2.1
  hE : val32 s.mem E.base aE g.n32 = a.2.2.1
  hx : a.2.2.1 < 2 ^ (32 * g.e)
  hp1 : 1 < a.2.1
  hodd : a.2.1 % 2 = 1
  hF : s.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 a.2.2.2

/-- `h` loaded and compared: `h`'s address is the same in both runs. -/
theorem gHead_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) :
    RelCT isa (Both (GSIn E g)) (Prog.chain [.block [.mov .esi (.mem (sc fH)), .mov .ecx (.imm (BitVec.ofNat 32 g.pLen))],
      VG.Impl.Bignum.X86.loadBE g.n64 aH, chainW .sbb g.n32 aTmp aOne aH, .block [.store (sc fLo) .ecx],
      chainW .sbb g.n32 aTmp aH aPm1, .block [.alu .and .ecx (.mem (sc fLo)), .alu .cmp .ecx (.imm 0)]] (.block []))
      fun _ _ => True := by
  have sz := v.size_ge
  refine RelCT.seq (both_post (Ψ := fun a t => ∀ r ∈ [Reg.esp, .edi, .esi, .ecx],
      t.gpr r = if r = .esi then (E.hs + BitVec.ofNat 64 (a.1 * E.pLen)).setWidth 32
        else if r = .ecx then BitVec.ofNat 32 g.pLen else baseVal E r)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins h.base)
      (tcheckE _ _ (.block [.mov .esi (.mem (sc 0)), .mov .ecx (.imm 0)]) rfl (by decide +kernel)
        (by decide +kernel))) fun a s h => ?_) ?_
  · refine ld_ok h.base.scr (d := fH) (by simp only [fH, hdr]; omega) fun t₁ u₁ => wp_movi fun t₂ u₂ =>
      WP.block_nil ?_
    have pins := base_pins h.base
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact pins _ (by simp)
    · rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact pins _ (by simp)
    · rw [u₂.other _ (by decide), u₁.gpr, h.hH]; rfl
    · rw [u₂.gpr]; rfl
  · refine both_agree [.esp, .edi, .esi, .ecx] _ (fun _ _ h => h) ?_
    unfold Geo.n64 Geo.n32
    rcases G.lengths with ⟨h₁, _⟩ | ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> rw [h₁] <;> exact tcheck _ _ (by decide +kernel)

/-- p, h and `(p − 1)/q` into the exponentiation's arrays. -/
theorem gSel_ct {g : Geo} (G : GeoOk g) {α : Type} {Φ : α → State → Prop} {E : Env}
    (hb : ∀ a s, Φ a s → Base E s) :
    RelCT isa (Both Φ) (Prog.chain [.block [.mov .ecx (.imm 0)],
      selectsW g.n32 aP aP (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).modulus,
      .block [.mov .ecx (.imm 0)], selectsW g.n32 aH aH (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).base,
      .block [.mov .ecx (.imm 0)], selectsW g.e aE aE (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).exponent] (.block []))
      fun _ _ => True := by
  refine both_agree [.esp, .edi] (fun _ => baseVal E) (fun a s h => base_pins (hb a s h)) ?_
  rw [G.e]
  unfold Geo.n64 Geo.n32
  rcases G.lengths with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;> exact tcheck _ _ (by decide +kernel)

/-- `g` and the check `g > 1`. -/
theorem gCall_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) :
    RelCT isa (Both fun (a : Nat × Nat × Nat × Nat) t => ∃ s, Base E s ∧ SelPost E g a.2.1 (hVal E a.1) a.2.2.1 a.2.2.2 s t ∧
        1 < a.2.1 ∧ a.2.1 % 2 = 1)
      (Prog.chain [VG.Impl.Dsa.X86.Pow.call g.n64 g.e,
        chainW .sbb g.n32 aTmp aOne (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result,
        .block [.alu .cmp .ecx (.imm 0)]] (.block [])) fun _ _ => True := by
  have low := v.low
  have pinsOf : ∀ (a : Nat × Nat × Nat × Nat) t, (∃ s, Base E s ∧ SelPost E g a.2.1 (hVal E a.1) a.2.2.1 a.2.2.2 s t ∧
      1 < a.2.1 ∧ a.2.1 % 2 = 1) → ∀ r ∈ [Reg.esp, .edi], t.gpr r = baseVal E r := fun a t h => by
    obtain ⟨s, B, S, _⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact S.sp
    · rw [S.keeps.1 _ (by decide)]; exact B.edi
  let Pin : State → Prop := fun t => ∀ r ∈ [Reg.esp, .edi], t.gpr r = baseVal E r
  refine RelCT.seq (R := fun t₁ t₂ => Pin t₁ ∧ Pin t₂) ?_ ?_
  · have call := (VG.Proof.Dsa.X86.Pow.call_relCT g.n64 g.e).mono (P' := Both fun (a : Nat × Nat × Nat × Nat) t =>
        ∃ s, Base E s ∧ SelPost E g a.2.1 (hVal E a.1) a.2.2.1 a.2.2.2 s t ∧ 1 < a.2.1 ∧ a.2.1 % 2 = 1)
      (fun s t h => by
        obtain ⟨a, h₁, h₂⟩ := h
        have p₁ := pinsOf a s h₁
        have p₂ := pinsOf a t h₂
        refine ⟨(p₁ _ (by simp)).trans (p₂ _ (by simp)).symm, (p₁ _ (by simp)).trans (p₂ _ (by simp)).symm, ?_⟩
        rw [p₁ _ (by simp)]
        show 12 ≤ E.sp.toNat
        omega) (fun _ _ h => h)
    refine (call.wp (F₁ := Pin) (F₂ := Pin) fun s t h => ?_).mono (fun _ _ h => h) fun _ _ h => h.2
    obtain ⟨a, ⟨s₀, _, S₁, hp1, hodd⟩, ⟨t₀, _, S₂, _⟩⟩ := h
    have p₁ := pinsOf a s ⟨s₀, ‹_›, S₁, hp1, hodd⟩
    have p₂ := pinsOf a t ⟨t₀, ‹_›, S₂, hp1, hodd⟩
    refine ⟨WP.mono (gPowCall_regs G v hp1 hodd S₁) fun u ⟨e₁, e₂⟩ r hr => ?_,
      WP.mono (gPowCall_regs G v hp1 hodd S₂) fun u ⟨e₁, e₂⟩ r hr => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [e₁]; exact p₁ _ (by simp)
      · rw [e₂]; exact p₁ _ (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [e₁]; exact p₂ _ (by simp)
      · rw [e₂]; exact p₂ _ (by simp)
  · refine (show RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) _ _ from ?_).mono
      (fun s t h => agree_regs fun r hr => (h.1 r hr).trans (h.2 r hr).symm) fun _ _ h => h
    rw [show (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result = slot g.n64 6 from rfl]
    unfold Geo.n64 Geo.n32
    rcases G.lengths with ⟨h₁, _⟩ | ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> rw [h₁] <;> exact tcheck _ _ (by decide +kernel)

/-- One `h`. -/
theorem gStep_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) :
    RelCT isa (Both (GSIn E g)) g.gStep fun _ _ => True := by
  have sz := v.size_ge
  unfold Geo.gStep
  show RelCT isa _ (Prog.chain [_, _, _, _, _, _] (.ite .e (.block []) _)) _
  refine RelCT.chain (RelCT.seq (both_post (Ψ := fun a t => ∃ s, GSIn E g a s ∧ RangePost E g a.1 a.2.1 s t)
    (gHead_ct G v) fun a s h => gRange_ok G v hp h.base h.hj h.hH h.hone h.hpm1 (P := .block [])
      fun t R => WP.block_nil ⟨s, h, R⟩) ?_)
  refine both_ite (fun a => !decide (1 < hVal E a.1 ∧ hVal E a.1 < a.2.1 - 1))
    (fun a t h => by obtain ⟨s, _, R⟩ := h; exact R.zf) (RelCT.block_nil fun _ _ _ => trivial) ?_
  -- In range: `g`.
  show RelCT isa _ (Prog.chain [_, _, _, _, _, _, _, _, _] (.ite .e (.block []) _)) _
  refine RelCT.chain (RelCT.seq (both_post (Ψ := fun a u => Base E u ∧
      isa.eval .e u = some (!decide (1 < gVal (hVal E a.1) a.2.1 a.2.2.1))) ?_
    fun a t h => by
      obtain ⟨⟨s, I, R⟩, _⟩ := h
      obtain ⟨kP, kE, kOne, fGR⟩ := range_keeps G v R I.hone I.hP I.hE I.hF
      exact gPowMid_ok G v R.base kP R.h kE I.hx kOne I.hp1 I.hodd fGR (P := .block [])
        fun u M => WP.block_nil ⟨M.base, M.zf⟩) ?_)
  · show RelCT isa _ (Prog.chain [_, _, _, _, _, _] (Prog.chain [_, _, _] (.block []))) _
    refine RelCT.chain (RelCT.seq (both_post (Ψ := fun a t => ∃ s, Base E s ∧
        SelPost E g a.2.1 (hVal E a.1) a.2.2.1 a.2.2.2 s t ∧ 1 < a.2.1 ∧ a.2.1 % 2 = 1)
      (gSel_ct G fun a t h => by obtain ⟨⟨s, _, R⟩, _⟩ := h; exact R.base) fun a t h => ?_) (gCall_ct G v))
    obtain ⟨⟨s, I, R⟩, _⟩ := h
    obtain ⟨kP, kE, kOne, fGR⟩ := range_keeps G v R I.hone I.hP I.hE I.hF
    exact gPowSel_ok G v R.base kP R.h kE I.hx kOne fGR (P := .block [])
      fun u S => WP.block_nil ⟨t, R.base, S, I.hp1, I.hodd⟩
  refine both_ite (fun a => !decide (1 < gVal (hVal E a.1) a.2.1 a.2.2.1)) (fun a t h => h.2)
    (RelCT.block_nil fun _ _ _ => trivial) ?_
  -- `g` out.
  refine both_agree [.esp, .edi] (fun _ => baseVal E) (fun a s h => base_pins h.1.1) ?_
  rw [show (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result = slot g.n64 6 from rfl]
  unfold Geo.n64
  rcases G.lengths with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;> exact tcheck _ _ (by decide +kernel)

end VG.Proof.Dsa.X86.Generation
