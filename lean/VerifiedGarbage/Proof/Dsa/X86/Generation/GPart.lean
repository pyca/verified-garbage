module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.GPow
import VerifiedGarbage.Proof.Dsa.X86.Generation.Seqs
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Dsa.Generation.Search
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Octets

/-! # The generator: the `h` of the tape in turn (A.2.1) -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- That `h` gives a generator: in range, and its `g` above 1. -/
def Found (h p x : Nat) : Prop := 1 < h ∧ h < p - 1 ∧ 1 < gVal h p x

instance (h p x : Nat) : Decidable (Found h p x) := by unfold Found; infer_instance

/-- After one `h`. -/
structure GStepPost (E : Env) (g : Geo) (j p x F : Nat) (s t : State) : Prop where
  base : Base E t
  fg : t.mem.readW (off E.base fG) 32 =
    BitVec.ofNat 32 (if Found (Spec.Dsa.decodeBE (hChunk E j)) p x then 1 else F)
  gb : Found (Spec.Dsa.decodeBE (hChunk E j)) p x → Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen + g.qLen))
    g.pLen = Spec.Dsa.encodeBE g.pLen (gVal (Spec.Dsa.decodeBE (hChunk E j)) p x)
  chg : E.Chg (rRanges ++ wRanges g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

/-- What the range check of `h` keeps: the arrays the exponentiation reads, and `fG`. -/
theorem range_keeps {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s t : State} {j p x F : Nat}
    (R : RangePost E g j p s t) (hone : val32 s.mem E.base aOne g.n32 = 1)
    (hP : val32 s.mem E.base aP g.n32 = p) (hE : val32 s.mem E.base aE g.n32 = x)
    (hF : s.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F) :
    val32 t.mem E.base aP g.n32 = p ∧ val32 t.mem E.base aE g.n32 = x ∧ val32 t.mem E.base aOne g.n32 = 1 ∧
      t.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F := by
  have sz := v.size_ge
  have bd := G.bounds
  have n32 : g.n32 = g.pLen / 4 := rfl
  have nle : g.n32 ≤ 96 := by omega
  have rA := rRanges_apart v
  have keepR : ∀ {d : Nat}, 9728 + 400 * 10 ≤ d ∨ d + 4 * g.n32 ≤ 9728 + 400 * 8 → d + 4 * g.n32 ≤ E.size →
      fLo + 4 ≤ d ∨ d + 4 * g.n32 ≤ fLo →
      val32 t.mem E.base d g.n32 = val32 s.mem E.base d g.n32 := fun h₁ h₂ h₃ =>
    Env.Chg.val32 v R.chg h₂ fun o ho => ⟨(rA o ho).1, by
      simp only [rRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;> simp only [aTmp, aH, arr, fLo, hdr] at h₃ ⊢ <;> omega⟩
  have fGR : t.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F := by
    rw [Env.Chg.word v R.chg (by simp only [fG, hdr]; omega) (fun o ho => ⟨(rA o ho).1, by
      simp only [rRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;> simp only [aTmp, aH, arr, fLo, fG, hdr] <;> omega⟩), hF]
  exact ⟨by rw [keepR (by simp only [aP, arr]; omega) (by simp only [aP, arr]; omega)
      (by left; simp only [aP, arr, fLo, hdr]; omega), hP],
    by rw [keepR (by simp only [aE, arr]; omega) (by simp only [aE, arr]; omega)
      (by left; simp only [aE, arr, fLo, hdr]; omega), hE],
    by rw [keepR (by simp only [aOne, arr]; omega) (by simp only [aOne, arr]; omega)
      (by left; simp only [aOne, arr, fLo, hdr]; omega), hone], fGR⟩

theorem gStep_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) {s : State} (B : Base E s)
    {j p x F : Nat} (hj : (j + 1) * E.pLen ≤ E.hsLen)
    (hH : s.mem.readW (off E.base fH) 32 = (E.hs + BitVec.ofNat 64 (j * E.pLen)).setWidth 32)
    (hone : val32 s.mem E.base aOne g.n32 = 1) (hpm1 : val32 s.mem E.base aPm1 g.n32 = p - 1)
    (hP : val32 s.mem E.base aP g.n32 = p) (hE : val32 s.mem E.base aE g.n32 = x) (hx : x < 2 ^ (32 * g.e))
    (hp1 : 1 < p) (hodd : p % 2 = 1) (hplt : p < 2 ^ (8 * g.pLen))
    (hF : s.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F) :
    WP isa g.gStep s (GStepPost E g j p x F s) := by
  have sz := v.size_ge
  have bd := G.bounds
  unfold Geo.gStep
  refine gRange_ok G v hp B hj hH hone hpm1 (P := .ite .e (.block []) _) fun t R => ?_
  obtain ⟨kP, kE, kOne, fGR⟩ := range_keeps G v R hone hP hE hF
  have widenR : E.Chg (rRanges ++ wRanges g) s.mem t.mem :=
    R.chg.widen fun o ho => ⟨o, List.mem_append_left _ ho, Nat.le_refl _, Nat.le_refl _⟩
  refine WP.ite _ R.zf (fun hz => WP.block_nil ?_) (fun hz => ?_)
  · -- Out of range.
    have hn : ¬ Found (Spec.Dsa.decodeBE (hChunk E j)) p x := fun ⟨a, b, _⟩ => by
      simp only [a, b, and_self, decide_true, Bool.not_true, Bool.false_eq_true] at hz
    exact ⟨R.base, by rw [fGR]; simp only [hn, ↓reduceIte], fun h => absurd h hn, widenR, R.rd, R.wr, R.syms⟩
  · -- In range: `g`.
    have hin : 1 < Spec.Dsa.decodeBE (hChunk E j) ∧ Spec.Dsa.decodeBE (hChunk E j) < p - 1 := by
      simpa using hz
    refine WP.mono (gPow_ok G v R.base (p := p) (h := Spec.Dsa.decodeBE (hChunk E j)) (x := x) (F := F)
      kP R.h kE hx kOne hp1 hodd hplt fGR) fun t' P => ?_
    have iff : Found (Spec.Dsa.decodeBE (hChunk E j)) p x ↔ 1 < gVal (Spec.Dsa.decodeBE (hChunk E j)) p x :=
      ⟨fun h => h.2.2, fun h => ⟨hin.1, hin.2, h⟩⟩
    refine ⟨P.base, by rw [P.fg]; simp only [iff], fun h => P.gb (iff.mp h),
      widenR.trans (P.chg.widen fun o ho => ⟨o, List.mem_append_right _ ho, Nat.le_refl _, Nat.le_refl _⟩),
      by rw [P.rd, R.rd], by rw [P.wr, R.wr], by rw [P.syms, R.syms]⟩

/-- The `h` candidates of the tape. -/
def hList (E : Env) : List Nat := (Spec.Dsa.generationChunks E.pLen E.hT).map Spec.Dsa.decodeBE

theorem hList_length (E : Env) : (hList E).length = E.hT.length / E.pLen := by
  simp [hList, Spec.Dsa.generationChunks]

theorem hList_drop (E : Env) {j : Nat} (hj : j < E.hT.length / E.pLen) :
    (hList E).drop j = Spec.Dsa.decodeBE (hChunk E j) :: (hList E).drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [hList_length]; exact hj)]
  simp [hList, Spec.Dsa.generationChunks, hChunk]

/-- The ranges the generator changes. -/
def gRanges (g : Geo) : List (Nat × Nat) := rRanges ++ wRanges g ++ [(fH, 4), (fHLeft, 4)]

theorem gRanges_apart {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) : E.Apart (gRanges g) := by
  have sz := v.size_ge
  intro o ho
  rcases List.mem_append.mp ho with h | h
  · rcases List.mem_append.mp h with h | h
    · exact rRanges_apart v o h
    · exact wRanges_apart G v o h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp only [fH, fHLeft, fOut, fWitLen, hdr] <;> omega

/-- What the generator keeps. -/
structure GKeep (E : Env) (g : Geo) (s t : State) : Prop where
  base : Base E t
  chg : E.Chg (gRanges g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

/-- The generator's result in memory `m`. -/
def GRes (E : Env) (g : Geo) (m : Mem) : Option Nat → Prop
  | none => m.readW (off E.base fG) 32 = BitVec.ofNat 32 2
  | some gv => m.readW (off E.base fG) 32 = BitVec.ofNat 32 1 ∧
      Spec.Rsa.bytesAt m (off E.base (sPk + g.pLen + g.qLen)) g.pLen = Spec.Dsa.encodeBE g.pLen gv

theorem GKeep.mem {E : Env} {g : Geo} {s t t' : State} (K : GKeep E g s t) (hm : t'.mem = t.mem)
    (edi : t'.gpr .edi = t.gpr .edi) (sp : t'.gpr .esp = t.gpr .esp) (rd : t'.rd = t.rd) (wr : t'.wr = t.wr)
    (sy : t'.syms = t.syms) : GKeep E g s t' :=
  ⟨K.base.regs hm edi sp rd wr sy, by rw [hm]; exact K.chg, by rw [rd, K.rd], by rw [wr, K.wr], by rw [sy, K.syms]⟩

theorem GKeep.store {E : Env} {g : Geo} {s t t' : State} (K : GKeep E g s t) (G : GeoOk g) (v : E.Valid) {d : Nat}
    (hd : (d, 4) ∈ gRanges g) (x : BitVec 32) (hm : t'.mem = t.mem.writeW (off E.base d) x)
    (edi : t'.gpr .edi = t.gpr .edi) (sp : t'.gpr .esp = t.gpr .esp) (rd : t'.rd = t.rd) (wr : t'.wr = t.wr)
    (sy : t'.syms = t.syms) : GKeep E g s t' := by
  have C : E.Chg [(d, 4)] t.mem t'.mem := by
    rw [hm]; exact (Env.Chg.refl _ _).store (List.mem_singleton_self _) (by decide) x
  exact ⟨K.base.keep v C (fun o ho => gRanges_apart G v o (by simp only [List.mem_singleton] at ho; rw [ho]; exact hd))
    edi sp rd wr sy, K.chg.trans (C.widen fun o ho => ⟨o, by simp only [List.mem_singleton] at ho; rw [ho]; exact hd,
      Nat.le_refl _, Nat.le_refl _⟩), by rw [rd, K.rd], by rw [wr, K.wr], by rw [sy, K.syms]⟩

/-- A pointer into a tape, moved on. -/
theorem ptr_add (x : BitVec 64) (c : Nat) :
    x.setWidth 32 + BitVec.ofNat 32 c = (x + BitVec.ofNat 64 c).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)]
  omega

/-- At the loop's head, before `h` number `j`. -/
structure GLoop (E : Env) (g : Geo) (p Q : Nat) (Rg : Option Nat) (s : State) (j : Nat) (t : State) : Prop where
  keep : GKeep E g s t
  fh : t.mem.readW (off E.base fH) 32 = (E.hs + BitVec.ofNat 64 (j * E.pLen)).setWidth 32
  left : t.mem.readW (off E.base fHLeft) 32 = BitVec.ofNat 32 (E.hsLen - j * E.pLen)
  fg : t.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 4
  hj : j * E.pLen ≤ E.hsLen
  spec : Spec.Dsa.generator p Q ((hList E).drop j) = Rg

/-- The arrays outside the generator's working space are as they were. -/
theorem gkeep_arrs {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s t : State} (K : GKeep E g s t) {d : Nat}
    (h₀ : 9728 ≤ d) (h₁ : d + 4 * g.n32 ≤ 9728 + 400 * 8 ∨ 9728 + 400 * 10 ≤ d) (h₂ : d + 4 * g.n32 ≤ E.size) :
    val32 t.mem E.base d g.n32 = val32 s.mem E.base d g.n32 := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have n32 : g.n32 = g.pLen / 4 := rfl
  have gA := gRanges_apart G v
  exact Env.Chg.val32 v K.chg h₂ fun o ho => ⟨(gA o ho).1, by
      simp only [gRanges, rRanges, wRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [aTmp, aH, arr, fLo, sPk, fG, fH, fHLeft, hdr] at h₀ h₁ h₂ ⊢ <;> omega⟩

/-- Whether the loop goes on after `h` number `j`. -/
def gCont (E : Env) (p x j : Nat) : Bool :=
  decide (E.hsLen - j * E.pLen ≠ 0 ∧ ¬ Found (Spec.Dsa.decodeBE (hChunk E j)) p x)

/-- One `h`: the loop exits with the generator's result, or goes on. -/
theorem gBody_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) {p Q x : Nat}
    {Rg : Option Nat} {s : State} (hx' : x = (p - 1) / Q)
    (hone : val32 s.mem E.base aOne g.n32 = 1) (hpm1 : val32 s.mem E.base aPm1 g.n32 = p - 1)
    (hP : val32 s.mem E.base aP g.n32 = p) (hE : val32 s.mem E.base aE g.n32 = x) (hxl : x < 2 ^ (32 * g.e))
    (hp1 : 1 < p) (hodd : p % 2 = 1) (hplt : p < 2 ^ (8 * g.pLen)) {j : Nat} {t : State}
    (L : GLoop E g p Q Rg s j t) :
    WP isa (seqs [.block (cmpF fHLeft 0),
      .ite .e (.block (stImm fG 2))
        (seqs [g.gStep, .block [.mov .eax (.mem (sc fH)), .alu .add .eax (.imm (BitVec.ofNat 32 g.pLen)),
          .store (sc fH) .eax, .mov .eax (.mem (sc fHLeft)), .alu .sub .eax (.imm (BitVec.ofNat 32 g.pLen)),
          .store (sc fHLeft) .eax]]),
      .block (cmpF fG 4)]) t fun t' =>
      (t'.zf = some false ∧ gCont E p x j = false ∧ GKeep E g s t' ∧ GRes E g t'.mem Rg) ∨
      (t'.zf = some true ∧ gCont E p x j = true ∧ (j + 1) * E.pLen ≤ E.hsLen ∧ GLoop E g p Q Rg s (j + 1) t') := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have hl : E.hT.length = E.hsLen := by rw [← L.keep.base.hs, VG.Proof.Bignum.bytesAt_length]
  have lens := v.lens
  have whole : E.hsLen = E.hsLen / E.pLen * E.pLen := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero v.hsWhole)).symm
  have pl := v.pLen_ge
  have gA := gRanges_apart G v
  have arrK : ∀ {d : Nat}, 9728 ≤ d → d + 4 * g.n32 ≤ 9728 + 400 * 8 ∨ 9728 + 400 * 10 ≤ d →
      d + 4 * g.n32 ≤ E.size → val32 t.mem E.base d g.n32 = val32 s.mem E.base d g.n32 := fun h₀ h₁ h₂ =>
    gkeep_arrs G v L.keep h₀ h₁ h₂
  have n32 : g.n32 = g.pLen / 4 := rfl
  simp only [seqs]
  refine WP.seq (cmpF_end L.keep.base.scr (o := fHLeft) (v := 0) (by simp only [fHLeft, hdr]; omega) L.left
    (by omega) (by decide) fun t₁ g₁ m₁ rd₁ wr₁ sy₁ z₁ => ?_)
  have K₁ := L.keep.mem m₁ (g₁ _ (by decide)) (g₁ _ (by decide)) rd₁ wr₁ sy₁
  refine WP.seq (WP.ite _ z₁ (fun hz => stImm_end K₁.base.scr (o := fG) (v := 2) (by simp only [fG, hdr]; omega)
    fun t₂ g₂ m₂ rd₂ wr₂ sy₂ => ?_) (fun hz => ?_))
  · -- No `h` left.
    have h0 : E.hsLen - j * E.pLen = 0 := of_decide_eq_true hz
    have K₂ := K₁.store G v (d := fG) (by simp [gRanges, wRanges]) _ m₂ (g₂ _ (by decide)) (g₂ _ (by decide)) rd₂ wr₂
      sy₂
    refine cmpF_end K₂.base.scr (o := fG) (v := 4) (w := 2) (by simp only [fG, hdr]; omega)
      (by rw [m₂, Mem.readW_writeW_self32]) (by decide) (by decide) fun t₃ g₃ m₃ rd₃ wr₃ sy₃ z₃ => ?_
    refine .inl ⟨z₃, by simp [gCont, h0], K₂.mem m₃ (g₃ _ (by decide)) (g₃ _ (by decide)) rd₃ wr₃ sy₃, ?_⟩
    have hN : E.hT.length / E.pLen ≤ j := by
      rw [hl]; exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; omega)
    have hR : Rg = none := by
      rw [← L.spec, List.drop_eq_nil_of_le (by rw [hList_length]; exact hN)]
      rfl
    rw [hR]; show _ = _; rw [m₃, m₂, Mem.readW_writeW_self32]
  · -- `h` number `j`.
    have hne : E.hsLen - j * E.pLen ≠ 0 := of_decide_eq_false hz
    have hj1 : (j + 1) * E.pLen ≤ E.hsLen := by
      have hlt : j * E.pLen < E.hsLen / E.pLen * E.pLen := by omega
      have := Nat.lt_of_mul_lt_mul_right hlt
      have := Nat.mul_le_mul_right E.pLen (show j + 1 ≤ E.hsLen / E.pLen by omega)
      omega
    have hjN : j < E.hT.length / E.pLen := by
      rw [hl]; exact Nat.lt_of_mul_lt_mul_right (a := E.pLen) (by rw [Nat.succ_mul] at hj1; omega)
    refine WP.seq (WP.mono (gStep_ok G v hp K₁.base (j := j) (p := p) (x := x) (F := 4) hj1
      (by rw [m₁]; exact L.fh)
      (by rw [m₁, arrK (by simp only [aOne, arr]; omega) (by simp only [aOne, arr]; omega) (by simp only [aOne, arr]; omega),
        hone])
      (by rw [m₁, arrK (by simp only [aPm1, arr]; omega) (by simp only [aPm1, arr]; omega) (by simp only [aPm1, arr]; omega),
        hpm1])
      (by rw [m₁, arrK (by simp only [aP, arr]; omega) (by simp only [aP, arr]; omega) (by simp only [aP, arr]; omega), hP])
      (by rw [m₁, arrK (by simp only [aE, arr]; omega) (by simp only [aE, arr]; omega) (by simp only [aE, arr]; omega), hE])
      hxl hp1 hodd hplt (by rw [m₁]; exact L.fg)) fun t₂ S => ?_)
    have K₂ : GKeep E g s t₂ := ⟨S.base, K₁.chg.trans (S.chg.widen fun o ho => ⟨o, List.mem_append_left _ ho,
      Nat.le_refl _, Nat.le_refl _⟩), by rw [S.rd, K₁.rd], by rw [S.wr, K₁.wr], by rw [S.syms, K₁.syms]⟩
    have word₂ : ∀ d, hdr ≤ d → d + 4 ≤ fG →
        t₂.mem.readW (off E.base d) 32 = t₁.mem.readW (off E.base d) 32 :=
      fun d hd' hd => Env.Chg.word v S.chg (by simp only [fG, hdr] at hd; omega) fun o ho => ⟨by
        rcases List.mem_append.mp ho with h | h
        · exact (rRanges_apart v o h).1
        · exact (wRanges_apart G v o h).1, by
        simp only [rRanges, wRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [aTmp, aH, arr, fLo, sPk, fG, hdr] at hd hd' ⊢ <;> omega⟩
    -- The next `h`.
    refine ld_ok K₂.base.scr (d := fH) (by simp only [fH, hdr]; omega) fun t₃ u₃ => wp_addi fun t₄ u₄ =>
      st_ok (Scr.of_eq K₂.base.scr (by rw [u₄.other _ (by decide), u₃.other _ (by decide)])
        (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]) (by rw [u₄.wr, u₃.wr])) (d := fH)
        (by simp only [fH, hdr]; omega) fun t₅ M₅ => ?_
    have m₅ : t₅.mem = t₂.mem.writeW (off E.base fH) ((E.hs + BitVec.ofNat 64 ((j + 1) * E.pLen)).setWidth 32) := by
      rw [M₅.mem, u₄.mem, u₃.mem, u₄.gpr, u₃.gpr, word₂ fH (by simp only [fH, hdr]; omega) (by simp only [fH, fG, hdr]; omega), m₁, L.fh, ← hp,
        ptr_add, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.succ_mul]
    have K₅ := K₂.store G v (d := fH) (by simp [gRanges]) _ m₅
      (by rw [M₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide)])
      (by rw [M₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide)]) (by rw [M₅.rd, u₄.rd, u₃.rd])
      (by rw [M₅.wr, u₄.wr, u₃.wr]) (by rw [M₅.syms, u₄.syms, u₃.syms])
    refine ld_ok K₅.base.scr (d := fHLeft) (by simp only [fHLeft, hdr]; omega) fun t₆ u₆ => wp_subi fun t₇ u₇ _ _ =>
      st_ok (Scr.of_eq K₅.base.scr (by rw [u₇.other _ (by decide), u₆.other _ (by decide)])
        (by rw [u₇.other _ (by decide), u₆.other _ (by decide)]) (by rw [u₇.wr, u₆.wr])) (d := fHLeft)
        (by simp only [fHLeft, hdr]; omega) fun t₈ M₈ => WP.block_nil ?_
    have ws : ∀ (m : Mem) {d e : Nat}, d + 4 ≤ sState → e + 4 ≤ sState → (d + 4 ≤ e ∨ e + 4 ≤ d) → ∀ y,
        (m.writeW (off E.base e) y).readW (off E.base d) 32 = m.readW (off E.base d) 32 :=
      fun m d e h₁ h₂ h y => word_store_other v m (by simp only [sState] at h₁; omega)
        (by simp only [sState] at h₂; omega) h y
    have m₈ : t₈.mem = t₅.mem.writeW (off E.base fHLeft) (BitVec.ofNat 32 (E.hsLen - (j + 1) * E.pLen)) := by
      rw [M₈.mem, u₇.mem, u₆.mem, u₇.gpr, u₆.gpr, m₅, ws _ (by simp only [fHLeft, sState, hdr]; omega)
        (by simp only [fH, sState, hdr]; omega) (by simp only [fH, fHLeft, hdr]; omega),
        word₂ fHLeft (by simp only [fHLeft, hdr]; omega) (by simp only [fHLeft, fG, hdr]; omega), m₁, L.left, ← hp,
        sub_ofNat (by rw [hp] at hj1 ⊢; rw [Nat.succ_mul] at hj1; omega), Nat.succ_mul, Nat.sub_sub]
    have K₈ := K₅.store G v (d := fHLeft) (by simp [gRanges]) _ m₈
      (by rw [M₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide)])
      (by rw [M₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide)]) (by rw [M₈.rd, u₇.rd, u₆.rd])
      (by rw [M₈.wr, u₇.wr, u₆.wr]) (by rw [M₈.syms, u₇.syms, u₆.syms])
    have fG₈ : t₈.mem.readW (off E.base fG) 32 =
        BitVec.ofNat 32 (if Found (Spec.Dsa.decodeBE (hChunk E j)) p x then 1 else 4) := by
      rw [m₈, ws _ (by simp only [fG, sState, hdr]; omega) (by simp only [fHLeft, sState, hdr]; omega)
        (by simp only [fG, fHLeft, hdr]; omega), m₅, ws _ (by simp only [fG, sState, hdr]; omega)
        (by simp only [fH, sState, hdr]; omega) (by simp only [fG, fH, hdr]; omega), S.fg]
    have spec := L.spec
    rw [hList_drop E hjN, VG.Proof.Dsa.Generation.generator_cons] at spec
    refine cmpF_end K₈.base.scr (o := fG) (v := 4) (by simp only [fG, hdr]; omega) fG₈ (by split <;> omega)
      (by decide) fun t₉ g₉ m₉ rd₉ wr₉ sy₉ z₉ => ?_
    have K₉ := K₈.mem m₉ (g₉ _ (by decide)) (g₉ _ (by decide)) rd₉ wr₉ sy₉
    by_cases hf : Found (Spec.Dsa.decodeBE (hChunk E j)) p x
    · -- A generator.
      refine .inl ⟨by rw [show t₉.zf = _ from z₉]; simp [hf], by simp [gCont, hf], K₉, ?_⟩
      have hR : Rg = some (gVal (Spec.Dsa.decodeBE (hChunk E j)) p x) := by
        rw [← spec]; simp only [hf.1, hf.2.1, and_self, ↓reduceIte]
        rw [VG.Proof.Dsa.powMod_eq, ← hx']
        simp only [show 1 < Spec.Dsa.decodeBE (hChunk E j) ^ x % p from hf.2.2, ↓reduceIte]; rfl
      rw [hR]
      refine ⟨by rw [m₉, fG₈]; simp only [hf, ↓reduceIte], ?_⟩
      rw [m₉, m₈, Env.Chg.scratch v ((Env.Chg.refl [(fHLeft, 4)] t₅.mem).store (List.mem_singleton_self _)
        (by decide) _) (by simp only [sPk]; omega) (fun o ho => by
          simp only [List.mem_singleton] at ho; subst ho; simp only [fHLeft, sPk, hdr]; omega), m₅,
        Env.Chg.scratch v ((Env.Chg.refl [(fH, 4)] t₂.mem).store (List.mem_singleton_self _)
        (by decide) _) (by simp only [sPk]; omega) (fun o ho => by
          simp only [List.mem_singleton] at ho; subst ho; simp only [fH, sPk, hdr]; omega), S.gb hf]
    · -- On to the next `h`.
      refine .inr ⟨by rw [show t₉.zf = _ from z₉]; simp [hf], by simp [gCont, hne, hf], hj1, K₉, ?_, ?_, ?_, hj1, ?_⟩
      · rw [m₉, m₈, ws _ (by simp only [fH, sState, hdr]; omega) (by simp only [fHLeft, sState, hdr]; omega)
          (by simp only [fH, fHLeft, hdr]; omega), m₅, Mem.readW_writeW_self32]
      · rw [m₉, m₈, Mem.readW_writeW_self32]
      · rw [m₉, fG₈]; simp only [hf, ↓reduceIte]
      · rw [← spec]
        by_cases hr : 1 < Spec.Dsa.decodeBE (hChunk E j) ∧ Spec.Dsa.decodeBE (hChunk E j) < p - 1
        · have : ¬ 1 < gVal (Spec.Dsa.decodeBE (hChunk E j)) p x := fun h => hf ⟨hr.1, hr.2, h⟩
          simp only [hr, and_self, ↓reduceIte]
          rw [VG.Proof.Dsa.powMod_eq, ← hx']
          simp only [show ¬ 1 < Spec.Dsa.decodeBE (hChunk E j) ^ x % p from this, ↓reduceIte]
        · simp only [hr, ↓reduceIte]

/-- The generator's state words: the first `h`, all of the tape left, `fG` := 4. -/
theorem gInit_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s : State} (B : Base E s) (p Q : Nat) :
    WP isa (.block [.mov .eax (.mem (sc fHs)), .store (sc fH) .eax, .mov .eax (.mem (sc fHsLen)),
      .store (sc fHLeft) .eax, .mov .eax (.imm 4), .store (sc fG) .eax]) s
      (GLoop E g p Q (Spec.Dsa.generator p Q (hList E)) s 0) := by
  have sz := v.size_ge
  have K₀ : GKeep E g s s := ⟨B, Env.Chg.refl _ _, rfl, rfl, rfl⟩
  have ws : ∀ (m : Mem) {d e : Nat}, d + 4 ≤ sState → e + 4 ≤ sState → (d + 4 ≤ e ∨ e + 4 ≤ d) → ∀ y,
      (m.writeW (off E.base e) y).readW (off E.base d) 32 = m.readW (off E.base d) 32 :=
    fun m d e h₁ h₂ h y => word_store_other v m (by simp only [sState] at h₁; omega)
      (by simp only [sState] at h₂; omega) h y
  refine ld_ok B.scr (d := fHs) (by simp only [fHs, hdr]; omega) fun s₁ u₁ =>
    st_ok (Scr.of_eq B.scr (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.wr) (d := fH)
      (by simp only [fH, hdr]; omega) fun s₂ M₂ => ?_
  have K₂ := K₀.store G v (d := fH) (by simp [gRanges]) _ (by rw [M₂.mem, u₁.mem]) (by rw [M₂.gpr, u₁.other _ (by decide)])
    (by rw [M₂.gpr, u₁.other _ (by decide)]) (by rw [M₂.rd, u₁.rd]) (by rw [M₂.wr, u₁.wr]) (by rw [M₂.syms, u₁.syms])
  refine ld_ok K₂.base.scr (d := fHsLen) (by simp only [fHsLen, hdr]; omega) fun s₃ u₃ =>
    st_ok (Scr.of_eq K₂.base.scr (u₃.other _ (by decide)) (u₃.other _ (by decide)) u₃.wr) (d := fHLeft)
      (by simp only [fHLeft, hdr]; omega) fun s₄ M₄ => ?_
  have K₄ := K₂.store G v (d := fHLeft) (by simp [gRanges]) _ (by rw [M₄.mem, u₃.mem])
    (by rw [M₄.gpr, u₃.other _ (by decide)]) (by rw [M₄.gpr, u₃.other _ (by decide)]) (by rw [M₄.rd, u₃.rd])
    (by rw [M₄.wr, u₃.wr]) (by rw [M₄.syms, u₃.syms])
  refine wp_movi fun s₅ u₅ => st_ok (Scr.of_eq K₄.base.scr (u₅.other _ (by decide)) (u₅.other _ (by decide)) u₅.wr)
    (d := fG) (by simp only [fG, hdr]; omega) fun s₆ M₆ => WP.block_nil ?_
  have K₆ := K₄.store G v (d := fG) (by simp [gRanges, wRanges]) _ (by rw [M₆.mem, u₅.mem])
    (by rw [M₆.gpr, u₅.other _ (by decide)]) (by rw [M₆.gpr, u₅.other _ (by decide)]) (by rw [M₆.rd, u₅.rd])
    (by rw [M₆.wr, u₅.wr]) (by rw [M₆.syms, u₅.syms])
  have m₆ : s₆.mem = ((s.mem.writeW (off E.base fH) (s.mem.readW (off E.base fHs) 32)).writeW (off E.base fHLeft)
      (s.mem.readW (off E.base fHsLen) 32)).writeW (off E.base fG) (4 : BitVec 32) := by
    rw [M₆.mem, u₅.mem, u₅.gpr, M₄.mem, u₃.mem, u₃.gpr, M₂.mem, u₁.mem, u₁.gpr,
      ws _ (by simp only [fHsLen, sState, hdr]; omega) (by simp only [fH, sState, hdr]; omega)
      (by simp only [fHsLen, fH, hdr]; omega)]
  refine ⟨K₆, ?_, ?_, by rw [m₆, Mem.readW_writeW_self32]; rfl, by omega, by rw [List.drop_zero]⟩
  · rw [m₆, ws _ (by simp only [fH, sState, hdr]; omega) (by simp only [fG, sState, hdr]; omega)
      (by simp only [fH, fG, hdr]; omega), ws _ (by simp only [fH, sState, hdr]; omega)
      (by simp only [fHLeft, sState, hdr]; omega) (by simp only [fH, fHLeft, hdr]; omega),
      Mem.readW_writeW_self32, B.hsW, Nat.zero_mul, BitVec.add_zero]
  · rw [m₆, ws _ (by simp only [fHLeft, sState, hdr]; omega) (by simp only [fG, sState, hdr]; omega)
      (by simp only [fHLeft, fG, hdr]; omega), Mem.readW_writeW_self32, B.hsLenW, Nat.zero_mul, Nat.sub_zero]

/-- The generator over the whole `h` tape. -/
theorem gPart_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) {s : State} (B : Base E s)
    {p Q x : Nat} (hx' : x = (p - 1) / Q)
    (hone : val32 s.mem E.base aOne g.n32 = 1) (hpm1 : val32 s.mem E.base aPm1 g.n32 = p - 1)
    (hP : val32 s.mem E.base aP g.n32 = p) (hE : val32 s.mem E.base aE g.n32 = x) (hxl : x < 2 ^ (32 * g.e))
    (hp1 : 1 < p) (hodd : p % 2 = 1) (hplt : p < 2 ^ (8 * g.pLen)) :
    WP isa g.gPart s fun t => GKeep E g s t ∧ GRes E g t.mem (Spec.Dsa.generator p Q (hList E)) := by
  have sz := v.size_ge
  have lens := v.lens
  have pl := v.pLen_ge
  have hl : E.hT.length = E.hsLen := by rw [← B.hs, VG.Proof.Bignum.bytesAt_length]
  unfold Geo.gPart
  show WP isa (.seq (.block _) (.loop _ .e)) s _
  refine WP.seq (WP.mono (gInit_ok G v B p Q) fun s₆ L₀ => ?_)
  have hm : E.hsLen / E.pLen * E.pLen ≤ E.hsLen := Nat.div_mul_le_self _ _
  refine WP.loop (M := isa) (fun m t => ∃ j, j + m = E.hsLen / E.pLen + 1 ∧
      GLoop E g p Q (Spec.Dsa.generator p Q (hList E)) s j t)
    (fun m t ⟨j, hm', L⟩ => WP.mono (gBody_ok G v hp hx' hone hpm1 hP hE hxl hp1 hodd hplt L) fun t' h => ?_)
    (E.hsLen / E.pLen + 1) s₆ ⟨0, by omega, L₀⟩
  rcases h with ⟨z, _, K, res⟩ | ⟨z, _, hj1, L'⟩
  · exact .inl ⟨z, K, res⟩
  · have : j + 1 ≤ E.hsLen / E.pLen := (Nat.le_div_iff_mul_le (by omega)).mpr hj1
    exact .inr ⟨z, m - 1, by omega, j + 1, by omega, L'⟩

end VG.Proof.Dsa.X86.Generation
