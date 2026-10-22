module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.GPart
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TimingFlags
import VerifiedGarbage.Proof.Dsa.X86.PowCallTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base

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

/-- Another whole `h` is left. -/
theorem next_h {E : Env} (v : E.Valid) {j : Nat} (hne : E.hsLen - j * E.pLen ≠ 0) :
    (j + 1) * E.pLen ≤ E.hsLen := by
  have whole : E.hsLen = E.hsLen / E.pLen * E.pLen := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero v.hsWhole)).symm
  have hlt : j * E.pLen < E.hsLen / E.pLen * E.pLen := by omega
  have := Nat.lt_of_mul_lt_mul_right hlt
  have := Nat.mul_le_mul_right E.pLen (show j + 1 ≤ E.hsLen / E.pLen by omega)
  omega

/-- Before the generator, from `p` `a.1`, `q` `a.2.1` and `(p − 1)/q` `a.2.2`. -/
structure GPIn (E : Env) (g : Geo) (a : Nat × Nat × Nat) (s : State) : Prop where
  base : Base E s
  hx' : a.2.2 = (a.1 - 1) / a.2.1
  hone : val32 s.mem E.base aOne g.n32 = 1
  hpm1 : val32 s.mem E.base aPm1 g.n32 = a.1 - 1
  hP : val32 s.mem E.base aP g.n32 = a.1
  hE : val32 s.mem E.base aE g.n32 = a.2.2
  hxl : a.2.2 < 2 ^ (32 * g.e)
  hp1 : 1 < a.1
  hodd : a.1 % 2 = 1
  hplt : a.1 < 2 ^ (8 * g.pLen)

theorem gPart_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) :
    RelCT isa (Both (GPIn E g)) g.gPart fun _ _ => True := by
  have sz := v.size_ge
  have lens := v.lens
  have pl := v.pLen_ge
  refine both_exists fun a => ?_
  obtain ⟨p, Q, x⟩ := a
  refine relct_of_fact (fun s t h => (⟨h.1.hx', h.1.hxl, h.1.hp1, h.1.hodd, h.1.hplt⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _))
    fun ⟨hx', hxl, hp1, hodd, hplt⟩ => ?_
  unfold Geo.gPart
  show RelCT isa _ (.seq (.block _) (.loop _ .e)) _
  let N := E.hsLen / E.pLen + 1
  let GIn : State → Prop := fun σ => Base E σ ∧ val32 σ.mem E.base aOne g.n32 = 1 ∧
    val32 σ.mem E.base aPm1 g.n32 = p - 1 ∧ val32 σ.mem E.base aP g.n32 = p ∧ val32 σ.mem E.base aE g.n32 = x
  let I : Nat → State → State → Prop := fun n => Both fun (j : Nat) t =>
    (∃ σ, GIn σ ∧ GLoop E g p Q (Spec.Dsa.generator p Q (hList E)) σ j t) ∧ j + n = N
  refine RelCT.seq (R := I N) ?_ ?_
  · -- The state words.
    have tr : RelCT isa (fun s t => GPIn E g (p, Q, x) s ∧ GPIn E g (p, Q, x) t)
        (.block [.mov .eax (.mem (sc fHs)), .store (sc fH) .eax, .mov .eax (.mem (sc fHsLen)),
          .store (sc fHLeft) .eax, .mov .eax (.imm 4), .store (sc fG) .eax]) fun _ _ => True :=
      (tcheck [.esp, .edi] _ (by decide +kernel)).mono (fun s t h => agree_regs fun r hr =>
        (base_pins h.1.base r hr).trans (base_pins h.2.base r hr).symm) fun _ _ h => h
    refine (tr.wpDep (F := fun σ t => GLoop E g p Q (Spec.Dsa.generator p Q (hList E)) σ 0 t)
      fun s t h => ⟨gInit_ok G v h.1.base p Q, gInit_ok G v h.2.base p Q⟩).mono (fun _ _ h => h)
      fun s' t' ⟨_, σ₁, σ₂, ⟨P₁, P₂⟩, L₁, L₂⟩ => ⟨0, ⟨⟨σ₁, ⟨P₁.base, P₁.hone, P₁.hpm1, P₁.hP, P₁.hE⟩, L₁⟩, by simp⟩,
        ⟨σ₂, ⟨P₂.base, P₂.hone, P₂.hpm1, P₂.hP, P₂.hE⟩, L₂⟩, by simp⟩
  -- The `h`s.
  refine RelCT.loop (M := isa) (Q := fun _ _ => True) I (fun n => ?_) N
  refine both_exists fun j => ?_
  refine relct_of_fact (fun s t h => h.1.2) fun hjN => ?_
  let J : State → Prop := fun t => (∃ σ, GIn σ ∧ GLoop E g p Q (Spec.Dsa.generator p Q (hList E)) σ j t) ∧ j + n = N
  have hbJ : ∀ (u : Unit) t, J t → Base E t := fun _ t h => by
    obtain ⟨⟨σ, _, L⟩, _⟩ := h; exact L.keep.base
  have tr : RelCT isa (fun s t => J s ∧ J t)
      (seqs [.block (cmpF fHLeft 0),
        .ite .e (.block (stImm fG 2))
          (seqs [g.gStep, .block [.mov .eax (.mem (sc fH)), .alu .add .eax (.imm (BitVec.ofNat 32 g.pLen)),
            .store (sc fH) .eax, .mov .eax (.mem (sc fHLeft)), .alu .sub .eax (.imm (BitVec.ofNat 32 g.pLen)),
            .store (sc fHLeft) .eax]]),
        .block (cmpF fG 4)]) fun _ _ => True := by
    refine (show RelCT isa (Both fun (_ : Unit) t => J t) _ _ from ?_).mono (fun s t h => ⟨(), h.1, h.2⟩)
      fun _ _ h => h
    simp only [seqs]
    refine RelCT.assoc (RelCT.seq (cmpF_ct (o := fHLeft) (v := 0) (by simp only [fHLeft, hdr]; omega) (by decide)
      (fun _ => E.hsLen - j * E.pLen) hbJ (fun _ t h => by obtain ⟨⟨σ, _, L⟩, _⟩ := h; exact L.left)
      (fun _ => by omega) (Q := VG.X86.Taint.Agree (τr [.esp, .edi])) ?_ ?_)
      (tcheckE _ _ (.block (cmpF 0 0)) (cmpF_erase _ _) (by decide +kernel) (by decide +kernel)))
    · -- None left.
      exact (tkeep [.esp, .edi] _ (by decide +kernel)).mono (fun s t ⟨_, h₁, h₂⟩ => agree_regs fun r hr =>
        (base_pins (h₁.1.base hbJ) r hr).trans (base_pins (h₂.1.base hbJ) r hr).symm) fun _ _ h => h
    · -- `h` number `j`.
      have gs : ∀ (u : Unit) t, CmpAfter (fun (_ : Unit) t => J t) u t ∧
          decide (E.hsLen - j * E.pLen = 0) = false → GSIn E g (j, p, x, 4) t := fun u t h => by
        obtain ⟨⟨s, ⟨⟨σ, ⟨_, hone, hpm1, hP, hE⟩, L⟩, _⟩, gr, m, rd, wr, sy⟩, hz⟩ := h
        have hne : E.hsLen - j * E.pLen ≠ 0 := of_decide_eq_false hz
        have B : Base E t := L.keep.base.regs m (gr _ (by decide)) (gr _ (by decide)) rd wr sy
        have kept : ∀ {d : Nat}, 9728 ≤ d → d + 4 * g.n32 ≤ 9728 + 400 * 8 ∨ 9728 + 400 * 10 ≤ d →
            d + 4 * g.n32 ≤ E.size → val32 t.mem E.base d g.n32 = val32 σ.mem E.base d g.n32 :=
          fun h₀ h₁ h₂ => by rw [m]; exact gkeep_arrs G v L.keep h₀ h₁ h₂
        have bd := G.bounds
        have n32 : g.n32 = g.pLen / 4 := rfl
        exact ⟨B, next_h v hne, by rw [m]; exact L.fh,
          by rw [kept (by simp only [aOne, arr]; omega) (by simp only [aOne, arr]; omega)
            (by simp only [aOne, arr]; omega), hone],
          by rw [kept (by simp only [aPm1, arr]; omega) (by simp only [aPm1, arr]; omega)
            (by simp only [aPm1, arr]; omega), hpm1],
          by rw [kept (by simp only [aP, arr]; omega) (by simp only [aP, arr]; omega)
            (by simp only [aP, arr]; omega), hP],
          by rw [kept (by simp only [aE, arr]; omega) (by simp only [aE, arr]; omega)
            (by simp only [aE, arr]; omega), hE], hxl, hp1, hodd, by rw [m]; exact L.fg⟩
      refine RelCT.seq (both_post (Ψ := fun _ t => Base E t)
        (both_map (fun _ => (j, p, x, 4)) gs (gStep_ct G v hp)) fun u t h => ?_) ?_
      · have I := gs u t h
        exact WP.mono (gStep_ok G v hp I.base I.hj I.hH I.hone I.hpm1 I.hP I.hE I.hx I.hp1 I.hodd hplt I.hF)
          fun _ S => S.base
      · refine both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins h) ?_
        rcases G.lengths with ⟨h₁, _⟩ | ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> rw [h₁] <;>
          exact tkeep _ _ (by decide +kernel)
  have post : ∀ (σ t : State), GIn σ → GLoop E g p Q (Spec.Dsa.generator p Q (hList E)) σ j t →
      WP isa (seqs [.block (cmpF fHLeft 0),
        .ite .e (.block (stImm fG 2))
          (seqs [g.gStep, .block [.mov .eax (.mem (sc fH)), .alu .add .eax (.imm (BitVec.ofNat 32 g.pLen)),
            .store (sc fH) .eax, .mov .eax (.mem (sc fHLeft)), .alu .sub .eax (.imm (BitVec.ofNat 32 g.pLen)),
            .store (sc fHLeft) .eax]]),
        .block (cmpF fG 4)]) t fun t' => isa.eval .e t' = some (gCont E p x j) ∧
          (gCont E p x j = true → (j + 1) * E.pLen ≤ E.hsLen ∧
            GLoop E g p Q (Spec.Dsa.generator p Q (hList E)) σ (j + 1) t') := fun σ t ⟨_, hone, hpm1, hP, hE⟩ L =>
    WP.mono (gBody_ok G v hp hx' hone hpm1 hP hE hxl hp1 hodd hplt L) fun t' h => by
      rcases h with ⟨z, c, _⟩ | ⟨z, c, hj1, L'⟩
      · exact ⟨by rw [c]; exact z, fun h => absurd (c.symm.trans h) (by decide)⟩
      · exact ⟨by rw [c]; exact z, fun _ => ⟨hj1, L'⟩⟩
  refine (tr.wpDep (F := fun s t' => ∃ σ, GIn σ ∧ isa.eval .e t' = some (gCont E p x j) ∧
      (gCont E p x j = true → (j + 1) * E.pLen ≤ E.hsLen ∧
        GLoop E g p Q (Spec.Dsa.generator p Q (hList E)) σ (j + 1) t')) fun s t h => ⟨?_, ?_⟩).mono
    (fun _ _ h => h) fun s' t' H => ?_
  · obtain ⟨⟨σ, hσ, L⟩, _⟩ := h.1
    exact WP.mono (post σ s hσ L) fun t' h' => ⟨σ, hσ, h'⟩
  · obtain ⟨⟨σ, hσ, L⟩, _⟩ := h.2
    exact WP.mono (post σ t hσ L) fun t' h' => ⟨σ, hσ, h'⟩
  obtain ⟨_, _, _, _, ⟨σ₁, hσ₁, z₁, c₁⟩, ⟨σ₂, hσ₂, z₂, c₂⟩⟩ := H
  refine ⟨z₁.trans z₂.symm, fun _ => trivial, fun ht => ?_⟩
  have hc : gCont E p x j = true := by rw [z₁] at ht; exact Option.some.inj ht
  obtain ⟨hj1, L₁⟩ := c₁ hc
  obtain ⟨_, L₂⟩ := c₂ hc
  have : j + 1 ≤ E.hsLen / E.pLen := (Nat.le_div_iff_mul_le (by omega)).mpr hj1
  exact ⟨n - 1, by omega, j + 1, ⟨⟨σ₁, hσ₁, L₁⟩, by omega⟩, ⟨σ₂, hσ₂, L₂⟩, by omega⟩

end VG.Proof.Dsa.X86.Generation
