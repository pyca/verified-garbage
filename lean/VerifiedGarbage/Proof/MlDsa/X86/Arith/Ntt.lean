module

public import VerifiedGarbage.Proof.MlDsa.X86.Arith.Mul
public import VerifiedGarbage.Proof.MlDsa.X86.Arith.Lazy
public import VerifiedGarbage.Impl.MlDsa.X86.Arith.Ntt
import VerifiedGarbage.Proof.Mont.X86.Sse2.Lanes
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.X86.Arith.Mul
meta import VerifiedGarbage.Proof.MlDsa.X86.Arith.Lazy
meta import VerifiedGarbage.Impl.MlDsa.X86.Arith.Ntt
meta import VerifiedGarbage.Proof.Mont.X86.Sse2.Lanes
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.SseDword
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_ntt`
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Arith.Vec

open VG VG.X86 VG.X86.Lanes VG.Impl.MlDsa.X86.Arith
open VG.Impl.MlKem.X86 (at_)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86.Arith
open VG.Spec.MlDsa VG.Proof.MlDsa
open VG.Proof.MlKem.X86 (toNat_ofNat32 eq_ofNat_of_toNat E0 retR Piece ea_add ea_off ptr_next satState add_ofNat_add
  cnt_next cnt_ne)

/-! ## Straight-line XMM code -/

variable {s : State}

/-- A 16-byte store. -/
theorem wp_st {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {r : XReg} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hin : InRegions s.wr a 16)
    (k : WP isa (.block is) { ({ s with mem := s.mem.writeW a (f r) } : State) with xmm := f } Q) :
    WP isa (.block (.movdquStore m r :: is)) { s with xmm := f } Q :=
  Wp.cons (show State.store128 { s with xmm := f } (s.ea m) (f r) = _ by
    rw [ha, State.store128, ite_eq_left hin]) k

/-- An 8-byte load. -/
theorem wp_lq {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {d : XReg} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : WP isa (.block is)
      { s with xmm := fun r => if r = d then (0 : BitVec 64) ++ s.mem.readW a 64 else f r } Q) :
    WP isa (.block (.movqLoad d m :: is)) { s with xmm := f } Q :=
  Wp.cons (show (State.load64 { s with xmm := f } (s.ea m)).map _ = _ by
    rw [ha, State.load64, ite_eq_left hin]; rfl) k

theorem inRd16 {a : Addr} (h : InRegions s.wr a 16) : InRegions (s.rd ++ s.wr) a 16 :=
  let ⟨r, hr, c⟩ := h; ⟨r, List.mem_append_right _ hr, c⟩

/-- The constants of the layers: `c3` is `c + 1` for the differences `a + c - b`. -/
structure VK (c3 : BitVec 32) (f : XReg → BitVec 128) : Prop where
  q : f .xmm7 = qV
  nqi : f .xmm6 = nqiV
  ones : f .xmm4 = onesV
  c3 : f .xmm3 = bc c3

theorem VK.of_eq {c3 : BitVec 32} {f g : XReg → BitVec 128} (hc : VK c3 f)
    (h : ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm5 → g r = f r) : VK c3 g :=
  ⟨(h _ (by decide) (by decide) (by decide) (by decide)).trans hc.q,
    (h _ (by decide) (by decide) (by decide) (by decide)).trans hc.nqi,
    (h _ (by decide) (by decide) (by decide) (by decide)).trans hc.ones,
    (h _ (by decide) (by decide) (by decide) (by decide)).trans hc.c3⟩

/-- `vjoin` with `xmm5` as its temporary. -/
theorem vjoin5_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} (hm : 0 < s.mcdt)
    (h6 : f .xmm6 = nqiV) (h7 : f .xmm7 = qV)
    (k : ∀ g : XReg → BitVec 128, g .xmm0 = joinV (f .xmm0) (f .xmm2) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm5 → r ≠ .xmm2 → g r = f r) → WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (vjoin .xmm0 .xmm2 .xmm5 ++ is)) { s with xmm := f } Q := by
  refine wp_xs rfl (wp_pm hm (wp_pm hm (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_pm hm (wp_pm hm (wp_xs rfl
    (wp_xs rfl (k _ ?_ ?_))))))))))
  · simp only [joinV, redcV]
    rw [← h6, ← h7]
    rfl
  · intro r h0 h1 h2
    simp only [h0, h1, h2, ite_false]

/-- `vmont` with `xmm5`, the zetas, as its temporary. -/
theorem vmont5_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} (hm : 0 < s.mcdt)
    (h6 : f .xmm6 = nqiV) (h7 : f .xmm7 = qV)
    (k : ∀ g : XReg → BitVec 128, g .xmm0 = montV (f .xmm0) (f .xmm5) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm5 → r ≠ .xmm2 → g r = f r) → WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (vmont .xmm0 .xmm5 .xmm2 .xmm5 ++ is)) { s with xmm := f } Q := by
  refine wp_xs rfl (wp_xs rfl (wp_pm hm (wp_pm hm (vjoin5_wp hm h6 h7 fun g hg hr => k g (hg.trans rfl)
    fun r h0 h1 h2 => (hr r h0 h1 h2).trans ?_))))
  simp only [h0, h2, ite_false]

/-- `vmont2` by the zetas in `xmm5`. -/
theorem vmont25_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} (hm : 0 < s.mcdt)
    (h6 : f .xmm6 = nqiV) (h7 : f .xmm7 = qV)
    (k : ∀ g : XReg → BitVec 128, g .xmm0 = mont2V (f .xmm0) (f .xmm5) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm5 → r ≠ .xmm2 → g r = f r) → WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (vmont2 .xmm0 .xmm5 .xmm2 ++ is)) { s with xmm := f } Q := by
  refine wp_xs rfl (wp_xs rfl (wp_pm hm (wp_xs rfl (wp_pm hm (vjoin5_wp hm h6 h7 fun g hg hr => k g (hg.trans rfl)
    fun r h0 h1 h2 => (hr r h0 h1 h2).trans ?_)))))
  simp only [h0, h1, h2, ite_false]

/-- The sums in `xmm1` and the differences in `xmm2`. -/
theorem bfTail_wp {c1 : BitVec 32} {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    (h3 : f .xmm3 = bc c1) (h4 : f .xmm4 = onesV)
    (k : ∀ g : XReg → BitVec 128, g .xmm1 = sumV (f .xmm1) (f .xmm0) →
      g .xmm2 = difV (f .xmm1) (f .xmm0) (bc c1) → (∀ r, r ≠ .xmm1 → r ≠ .xmm2 → g r = f r) →
      WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (bfTail ++ is)) { s with xmm := f } Q := by
  refine wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (k _ ?_ ?_ ?_)))))
  · rfl
  · simp only [difV]
    rw [← h3, ← h4]
    rfl
  · intro r h1 h2
    simp only [h1, h2, ite_false]

/-! ## Four butterflies -/

/-- The code of four butterflies: from the vectors at `[eax]` and
`[eax + d]` and the zetas in `xmm5`, it stores `FX` and `FY` of them there,
and keeps the constants (and the zetas, if `keep`). -/
def BodyOk (c3 : BitVec 32) (body : List Instr) (d : Nat) (keep : Bool)
    (FX FY : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128) : Prop :=
  ∀ (s : State) (f : XReg → BitVec 128) (is : List Instr) (Q : State → Prop) (P P' : Addr), 0 < s.mcdt → VK c3 f →
    s.ea (at_ .eax 0) = P → s.ea (at_ .eax d) = P' → InRegions s.wr P 16 → InRegions s.wr P' 16 →
    (∀ (g : XReg → BitVec 128) (vx vy : BitVec 128),
      vx = FX (s.mem.readW P 128) (s.mem.readW P' 128) (f .xmm5) →
      vy = FY (s.mem.readW P 128) (s.mem.readW P' 128) (f .xmm5) → VK c3 g → (keep = true → g .xmm5 = f .xmm5) →
      WP isa (.block is) { ({ s with mem := (s.mem.writeW P vx).writeW P' vy } : State) with xmm := g } Q) →
    WP isa (.block (body ++ is)) { s with xmm := f } Q

theorem fBody_ok (d : Nat) : BodyOk fwdC1 (fBody d) d true (fwdX sh4) (fwdY sh4) := by
  intro s f is Q P P' hm hc ha ha' hin hin' k
  rw [show fBody d ++ is = .movdquLoad .xmm0 (at_ .eax d) :: (vmont .xmm0 .xmm5 .xmm2 .xmm1 ++
      (.movdquLoad .xmm1 (at_ .eax 0) :: (bfTail ++
        (.movdquStore (at_ .eax 0) .xmm1 :: .movdquStore (at_ .eax d) .xmm2 :: is)))) by
    simp only [fBody, List.append_assoc, List.cons_append, List.nil_append]]
  refine wp_ld ha' (inRd16 hin') (vmont_wp hm hc.nqi hc.q fun g₁ v₁ r₁ => wp_ld ha (inRd16 hin)
    (bfTail_wp ((r₁ _ (by decide) (by decide) (by decide)).trans hc.c3)
      ((r₁ _ (by decide) (by decide) (by decide)).trans hc.ones) fun g₂ s₂ d₂ r₂ =>
      wp_st ha hin (wp_st ha' hin' (k g₂ _ _ ?_ ?_ ?_ ?_))))
  · rw [s₂]; show sumV _ (g₁ .xmm0) = _; rw [v₁]; rfl
  · rw [d₂]; show difV _ (g₁ .xmm0) _ = _; rw [v₁]; rfl
  · exact hc.of_eq fun r h0 h1 h2 _ => (r₂ r h1 h2).trans (by
      show (if r = XReg.xmm1 then _ else g₁ r) = _
      rw [ite_eq_right h1, r₁ r h0 h1 h2]
      show (if r = XReg.xmm0 then _ else f r) = _
      rw [ite_eq_right h0])
  · intro _
    exact (r₂ _ (by decide) (by decide)).trans (r₁ _ (by decide) (by decide) (by decide))

theorem fBody2_ok : BodyOk fwdC1 fBody2 16 false (fwdX sh2) (fwdY sh2) := by
  intro s f is Q P P' hm hc ha ha' hin hin' k
  rw [show fBody2 ++ is = .movdquLoad .xmm0 (at_ .eax 0) :: .movdquLoad .xmm2 (at_ .eax 16) :: xmov .xmm1 .xmm0 ::
      xb .punpckhqdq .xmm0 .xmm2 :: xb .punpcklqdq .xmm1 .xmm2 :: (vmont .xmm0 .xmm5 .xmm2 .xmm5 ++ (bfTail ++
        (xmov .xmm0 .xmm1 :: xb .punpcklqdq .xmm0 .xmm2 :: xb .punpckhqdq .xmm1 .xmm2 ::
          .movdquStore (at_ .eax 0) .xmm0 :: .movdquStore (at_ .eax 16) .xmm1 :: is))) by
    simp only [fBody2, gath2, scat2, List.append_assoc, List.cons_append, List.nil_append]]
  refine wp_ld ha (inRd16 hin) (wp_ld ha' (inRd16 hin') (wp_xs rfl (wp_xs rfl (wp_xs rfl
    (vmont5_wp hm hc.nqi hc.q fun g₁ v₁ r₁ =>
      bfTail_wp ((r₁ _ (by decide) (by decide) (by decide)).trans hc.c3)
        ((r₁ _ (by decide) (by decide) (by decide)).trans hc.ones) fun g₂ s₂ d₂ r₂ =>
        wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_st ha hin (wp_st ha' hin' (k _ _ _ ?_ ?_ ?_ ?_))))))))))
  · show XBinOp.eval .punpcklqdq (g₂ .xmm1) (g₂ .xmm2) = _
    rw [s₂, d₂, v₁, r₁ .xmm1 (by decide) (by decide) (by decide)]; rfl
  · show XBinOp.eval .punpckhqdq (g₂ .xmm1) (g₂ .xmm2) = _
    rw [s₂, d₂, v₁, r₁ .xmm1 (by decide) (by decide) (by decide)]; rfl
  · exact hc.of_eq fun r h0 h1 h2 h5 => by
      show (if r = XReg.xmm1 then _ else if r = XReg.xmm0 then _ else if r = XReg.xmm0 then _ else g₂ r) = _
      rw [ite_eq_right h1, ite_eq_right h0, ite_eq_right h0, r₂ r h1 h2, r₁ r h0 h5 h2]
      show (if r = XReg.xmm1 then _ else if r = XReg.xmm0 then _ else if r = XReg.xmm1 then _ else
        if r = XReg.xmm2 then _ else if r = XReg.xmm0 then _ else f r) = _
      rw [ite_eq_right h1, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_right h0]
  · intro e; exact absurd e (by decide)

theorem fBody1_ok : BodyOk fwdC1 fBody1 16 false (fwdX sh1) (fwdY sh1) := by
  intro s f is Q P P' hm hc ha ha' hin hin' k
  rw [show fBody1 ++ is = .movdquLoad .xmm0 (at_ .eax 0) :: .movdquLoad .xmm2 (at_ .eax 16) ::
      .xop (.pshufd .xmm0 .xmm0 0xD8) :: .xop (.pshufd .xmm2 .xmm2 0xD8) :: xmov .xmm1 .xmm0 ::
      xb .punpckhqdq .xmm0 .xmm2 :: xb .punpcklqdq .xmm1 .xmm2 :: (vmont2 .xmm0 .xmm5 .xmm2 ++ (bfTail ++
        (xmov .xmm0 .xmm1 :: xb .punpckldq .xmm0 .xmm2 :: xb .punpckhdq .xmm1 .xmm2 ::
          .movdquStore (at_ .eax 0) .xmm0 :: .movdquStore (at_ .eax 16) .xmm1 :: is))) by
    simp only [fBody1, gath1, scat1, List.append_assoc, List.cons_append, List.nil_append]]
  refine wp_ld ha (inRd16 hin) (wp_ld ha' (inRd16 hin') (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl
    (vmont25_wp hm hc.nqi hc.q fun g₁ v₁ r₁ =>
      bfTail_wp ((r₁ _ (by decide) (by decide) (by decide)).trans hc.c3)
        ((r₁ _ (by decide) (by decide) (by decide)).trans hc.ones) fun g₂ s₂ d₂ r₂ =>
        wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_st ha hin (wp_st ha' hin' (k _ _ _ ?_ ?_ ?_ ?_))))))))))))
  · show XBinOp.eval .punpckldq (g₂ .xmm1) (g₂ .xmm2) = _
    rw [s₂, d₂, v₁, r₁ .xmm1 (by decide) (by decide) (by decide)]; rfl
  · show XBinOp.eval .punpckhdq (g₂ .xmm1) (g₂ .xmm2) = _
    rw [s₂, d₂, v₁, r₁ .xmm1 (by decide) (by decide) (by decide)]; rfl
  · exact hc.of_eq fun r h0 h1 h2 h5 => by
      show (if r = XReg.xmm1 then _ else if r = XReg.xmm0 then _ else if r = XReg.xmm0 then _ else g₂ r) = _
      rw [ite_eq_right h1, ite_eq_right h0, ite_eq_right h0, r₂ r h1 h2, r₁ r h0 h5 h2]
      show (if r = XReg.xmm1 then _ else if r = XReg.xmm0 then _ else if r = XReg.xmm1 then _ else
        if r = XReg.xmm2 then _ else if r = XReg.xmm0 then _ else if r = XReg.xmm2 then _ else
        if r = XReg.xmm0 then _ else f r) = _
      rw [ite_eq_right h1, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_right h0, ite_eq_right h2,
        ite_eq_right h0]
  · intro e; exact absurd e (by decide)

/-! ## The function's memory -/

section
variable (s₀ : State)
/-- `scratch`, which holds the table of zetas. -/
abbrev sP : BitVec 32 := arg s₀ 1
abbrev sA : Addr := (sP s₀).setWidth 64
end

theorem sp12 {s₀ : State} (hp : NttLoop.Pre s₀) : 12 ≤ (E0 s₀).toNat := by have := hp.sp; omega_using [this]

/-- A region apart from the contract's stack is apart from the MCDT frame. -/
theorem mcdt_disj {s₀ : State} (hp : NttLoop.Pre s₀) {R : Region} (h : (stkR s₀).Disjoint R) :
    (mcdtR s₀).Disjoint R := by
  intro a h₁ h₂
  refine h a ?_ h₂
  have := hp.sp
  have := (E0 s₀).isLt
  simp only [Region.Contains] at h₁ ⊢
  bv_omega

/-- The arguments, at `[esp + 16 + 4i]` after the push. -/
theorem arg_M0 {s₀ : State} (hp : NttLoop.Pre s₀) {i : Nat} (hi : i < 2) :
    ((M0 s₀).gpr .esp + BitVec.ofNat 32 (16 + 4 * i)).setWidth 64 = argAddr s₀ i ∧
      (M0 s₀).mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  refine ⟨?_, ?_⟩
  · rw [M0_esp]; simp only [argAddr, E0]; congr 1; have := hp.sp; bv_omega
  · exact (M0_frame s₀ (sp12 hp)).readW (hp.arg_in hi) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (mcdt_disj hp hp.stk_a).symm) (by decide)

theorem in_f16 {s₀ : State} (hp : NttLoop.Pre s₀) {s : State} (hw : s.wr = (M0 s₀).wr) {u : Nat} (hu : u < 64) :
    InRegions s.wr (coeffAddr (fA s₀) (4 * u)) 16 := by
  rw [hw, M0_wr, hp.wr]
  exact ⟨polyRegion (fA s₀), by simp, Offset.contains_base _ (by omega_using [hu]) (by omega_using [hu])⟩

theorem in_tbl {s₀ : State} (hp : NttLoop.Pre s₀) {s : State} (hw : s.wr = (M0 s₀).wr) {j n : Nat}
    (h : 4 * j + n ≤ 1024) : InRegions (s.rd ++ s.wr) (coeffAddr (sA s₀) j) n := by
  rw [hw, M0_wr, hp.wr]
  exact ⟨polyRegion (sA s₀), List.mem_append_right _ (by simp),
    Offset.contains_base _ (by omega_using [h]) (by omega_using [h])⟩

theorem in_arg {s₀ : State} (hp : NttLoop.Pre s₀) {s : State} (hw : s.wr = (M0 s₀).wr) {i : Nat} (hi : i < 2) :
    InRegions s.wr (argAddr s₀ i) 4 := by
  rw [hw, M0_wr, hp.wr]
  exact ⟨aR2 s₀, by simp, hp.arg_in hi⟩

/-- What every piece keeps: the stack pointer, the permissions, the MCDT
depth, the callee-saved registers, the table `T` in `scratch`, `f` and
`f + 1024` in the argument slots, and the constants `VP`. -/
structure Base (s₀ : State) (T : List Nat) (VP : (XReg → BitVec 128) → Prop) (s : State) : Prop where
  esp : s.gpr .esp = (M0 s₀).gpr .esp
  rd : s.rd = (M0 s₀).rd
  wr : s.wr = (M0 s₀).wr
  mcdt : s.mcdt = s₀.mcdt + 1
  saved : ∀ r ∈ [Reg.ebx, .esi, .edi, .ebp], s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (fA s₀), polyRegion (sA s₀), aR2 s₀] (M0 s₀).mem s.mem
  tbl : ∀ k < 256, coeffAt s.mem (sA s₀) k = BitVec.ofNat 32 (T.getD k 0)
  arg0 : s.mem.readW (argAddr s₀ 0) 32 = fP s₀
  slot : s.mem.readW (argAddr s₀ 1) 32 = fP s₀ + 1024
  vp : VP s.xmm

/-- Writes to `f` and to XMM registers keep the rest. -/
theorem Base.step {s₀ : State} (hp : NttLoop.Pre s₀) {T : List Nat} {VP VP' : (XReg → BitVec 128) → Prop}
    {s : State} (h : Base s₀ T VP s) {m' : Mem} (hf : Frame [polyRegion (fA s₀)] s.mem m')
    {g : XReg → BitVec 128} (hg : VP' g) : Base s₀ T VP' { ({ s with mem := m' } : State) with xmm := g } where
  esp := h.esp
  rd := h.rd
  wr := h.wr
  mcdt := h.mcdt
  saved := h.saved
  frame := h.frame.trans (hf.mono fun r hr => by simp at hr ⊢; exact .inl hr)
  tbl k hk := by
    show coeffAt m' (sA s₀) k = _
    rw [coeffAt_congr (m := s.mem) (fun j hj => hf.bytes (R := polyRegion (sA s₀))
      (by simpa using hp.f_s.symm) (polyLen _) hj) (by rw [n_eq]; exact hk)]
    exact h.tbl k hk
  arg0 := by
    show m'.readW _ 32 = _
    rw [hf.readW (hp.arg_in (by decide)) (by simpa using hp.f_a.symm) (by decide)]; exact h.arg0
  slot := by
    show m'.readW _ 32 = _
    rw [hf.readW (hp.arg_in (by decide)) (by simpa using hp.f_a.symm) (by decide)]; exact h.slot
  vp := hg

/-- `eax`, `ecx`, `edx` and the flags are free, and so are the XMM registers that hold no constant. -/
theorem Base.of_gpr {s₀ : State} {T : List Nat} {VP VP' : (XReg → BitVec 128) → Prop} {s s' : State}
    (h : Base s₀ T VP s) (hg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hmc : s'.mcdt = s.mcdt) (hmem : s'.mem = s.mem) (hx : VP' s'.xmm) :
    Base s₀ T VP' s' where
  esp := (hg _ (by decide) (by decide) (by decide)).trans h.esp
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  mcdt := hmc.trans h.mcdt
  saved r hr := by
    have := h.saved r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact (hg _ (by decide) (by decide) (by decide)).trans this
  frame := hmem ▸ h.frame
  tbl := hmem ▸ h.tbl
  arg0 := hmem ▸ h.arg0
  slot := hmem ▸ h.slot
  vp := hx

/-- The coefficients in memory: those of `D` stand for those of `G`, below
`bd' · q`, and the others for those of `f`, below `bd · q`. -/
def Co (s₀ : State) (m : Mem) (bd bd' : Nat) (f G : Poly) (D : Nat → Prop) : Prop :=
  ∀ i < 256, (D i → Lz bd' (coeffAt m (fA s₀) i).toNat G[i]!) ∧ (¬ D i → Lz bd (coeffAt m (fA s₀) i).toNat f[i]!)

theorem Co.congr {s₀ : State} {m : Mem} {bd bd' : Nat} {f G : Poly} {D D' : Nat → Prop}
    (h : Co s₀ m bd bd' f G D) (e : ∀ i < 256, (D' i ↔ D i)) : Co s₀ m bd bd' f G D' :=
  fun i hi => ⟨fun hd => (h i hi).1 ((e i hi).mp hd), fun hn => (h i hi).2 fun hd => hn ((e i hi).mpr hd)⟩

/-- The coefficient at position `p` of the vectors of coefficients `4u` and `4u'`. -/
def idx (u u' p : Nat) : Nat := if p < 4 then 4 * u + p else 4 * u' + (p - 4)

/-- The coefficients of those two vectors. -/
def In8 (u u' i : Nat) : Prop := (4 * u ≤ i ∧ i < 4 * u + 4) ∨ (4 * u' ≤ i ∧ i < 4 * u' + 4)

/-- Four butterflies on the vectors of coefficients `4u` and `4u'`, none of
which is done: they are, afterwards. -/
theorem body_step {c3 : BitVec 32} {body : List Instr} {d : Nat} {keep : Bool}
    {FX FY : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128} (hb : BodyOk c3 body d keep FX FY)
    {s₀ : State} (hp : NttLoop.Pre s₀) {T : List Nat} {s : State} (h : Base s₀ T (VK c3) s) {u u' : Nat}
    (hu : u < 64) (hu' : u' < 64) (hd : 16 * u + d = 16 * u')
    (heax : s.gpr .eax = fP s₀ + BitVec.ofNat 32 (16 * u)) {bd bd' : Nat} {f G : Poly} {D : Nat → Prop}
    (hco : Co s₀ s.mem bd bd' f G D) (hD : ∀ i, In8 u u' i → ¬ D i)
    (hnew : ∀ X Y, (∀ p < 8, Lz bd (pos X Y p).toNat f[idx u u' p]!) →
      ∀ p < 8, Lz bd' (pos (FX X Y (s.xmm .xmm5)) (FY X Y (s.xmm .xmm5)) p).toNat G[idx u u' p]!)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ (m : Mem) (g : XReg → BitVec 128),
      Base s₀ T (VK c3) { ({ s with mem := m } : State) with xmm := g } →
      Co s₀ m bd bd' f G (fun i => D i ∨ In8 u u' i) → (keep = true → g .xmm5 = s.xmm .xmm5) →
      WP isa (.block is) { ({ s with mem := m } : State) with xmm := g } Q) :
    WP isa (.block (body ++ is)) s Q := by
  have eP : s.ea (at_ .eax 0) = coeffAddr (fA s₀) (4 * u) := by
    rw [State.ea, at_, heax, show 16 * u = 4 * (4 * u) by omega_using []]
    exact ea_ptr hp.f_fit (by omega_using [hu])
  have eP' : s.ea (at_ .eax d) = coeffAddr (fA s₀) (4 * u') := by
    have := ea_ptr hp.f_fit (k := 4 * u') (by omega_using [hu'])
    rw [add_ofNat_add, Nat.add_zero] at this
    rw [State.ea, at_, heax, add_ofNat_add, hd, show 16 * u' = 4 * (4 * u') by omega_using []]
    exact this
  have hm : 0 < s.mcdt := by rw [h.mcdt]; exact Nat.succ_pos _
  have hcon : (polyRegion (fA s₀)).Contains (coeffAddr (fA s₀) (4 * u)) (128 / 8) :=
    Offset.contains_base _ (by omega_using [hu]) (by omega_using [hu])
  have hcon' : (polyRegion (fA s₀)).Contains (coeffAddr (fA s₀) (4 * u')) (128 / 8) :=
    Offset.contains_base _ (by omega_using [hu']) (by omega_using [hu'])
  show WP isa (.block (body ++ is)) { s with xmm := s.xmm } Q
  refine hb s s.xmm is Q _ _ hm h.vp eP eP' (in_f16 hp h.wr hu) (in_f16 hp h.wr hu') fun g vx vy ex ey hg hk5 => ?_
  have dX : ∀ j < 4, dword (s.mem.readW (coeffAddr (fA s₀) (4 * u)) 128) j = coeffAt s.mem (fA s₀) (4 * u + j) :=
    fun j hj => by rw [dword_readW _ _ hj, coeffAddr_add, ← coeffAt_eq]
  have dY : ∀ j < 4, dword (s.mem.readW (coeffAddr (fA s₀) (4 * u')) 128) j = coeffAt s.mem (fA s₀) (4 * u' + j) :=
    fun j hj => by rw [dword_readW _ _ hj, coeffAddr_add, ← coeffAt_eq]
  have hV : ∀ p < 8, Lz bd (pos (s.mem.readW (coeffAddr (fA s₀) (4 * u)) 128)
      (s.mem.readW (coeffAddr (fA s₀) (4 * u')) 128) p).toNat f[idx u u' p]! := fun p hp8 => by
    by_cases h4 : p < 4
    · rw [pos, ite_eq_left h4, idx, ite_eq_left h4, dX p h4]
      exact (hco _ (by omega_using [hu, h4])).2 (hD _ (.inl ⟨by omega_using [], by omega_using [h4]⟩))
    · rw [pos, ite_eq_right h4, idx, ite_eq_right h4, dY _ (by omega_using [h4, hp8])]
      exact (hco _ (by omega_using [hu', hp8])).2 (hD _ (.inr ⟨by omega_using [], by omega_using [h4, hp8]⟩))
  have hN := hnew _ _ hV
  refine k _ g (h.step hp (((Frame.refl _ _).writeW (List.mem_singleton_self _) vx hcon).writeW
    (List.mem_singleton_self _) vy hcon') hg) (fun i hi => ?_) hk5
  rw [coeffAt_write16 _ _ _ hu' hi, coeffAt_write16 _ _ _ hu hi]
  by_cases h2 : 4 * u' ≤ i ∧ i < 4 * u' + 4
  · rw [ite_eq_left h2]
    have := hN (4 + (i - 4 * u')) (by omega_using [h2])
    rw [pos, ite_eq_right (by omega_using []), ← ey, idx, ite_eq_right (by omega_using []),
      show 4 + (i - 4 * u') - 4 = i - 4 * u' by omega_using [],
      show 4 * u' + (i - 4 * u') = i by omega_using [h2]] at this
    exact ⟨fun _ => this, fun hn => absurd (.inr (.inr h2)) hn⟩
  · rw [ite_eq_right h2]
    by_cases h1 : 4 * u ≤ i ∧ i < 4 * u + 4
    · rw [ite_eq_left h1]
      have := hN (i - 4 * u) (by omega_using [h1])
      rw [pos, ite_eq_left (by omega_using [h1]), ← ex, idx, ite_eq_left (by omega_using [h1]),
        show 4 * u + (i - 4 * u) = i by omega_using [h1]] at this
      exact ⟨fun _ => this, fun hn => absurd (.inr (.inl h1)) hn⟩
    · rw [ite_eq_right h1]
      refine ⟨fun hd' => (hco i hi).1 (hd'.resolve_right fun h8 => ?_), fun hn => (hco i hi).2 fun hdi => hn (.inl hdi)⟩
      rcases h8 with h8 | h8
      · exact h1 h8
      · exact h2 h8

/-! ## The start of a layer -/

/-- Before a layer: every coefficient stands for that of `f`, below
`bd · q`, and `edx` is at the zeta of number `zp`. -/
structure LS (s₀ : State) (T : List Nat) (VP : (XReg → BitVec 128) → Prop) (bd : Nat) (f : Poly) (zp : Nat)
    (s : State) : Prop where
  base : Base s₀ T VP s
  edx : s.gpr .edx = sP s₀ + BitVec.ofNat 32 (4 * zp)
  co : ∀ i < 256, Lz bd (coeffAt s.mem (fA s₀) i).toNat f[i]!

theorem layStart_wp {s₀ : State} (hp : NttLoop.Pre s₀) {T : List Nat} {VP : (XReg → BitVec 128) → Prop} {s : State}
    (h : Base s₀ T VP s) : WP isa (.block layStart) s fun s' => s' = s.setReg .eax (fP s₀) := by
  obtain ⟨a₀, -⟩ := arg_M0 hp (i := 0) (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at a₀
  have ea : (s.gpr .esp + BitVec.ofNat 32 16).setWidth 64 = argAddr s₀ 0 := by rw [h.esp]; exact a₀
  have i₀ : InRegions (s.rd ++ s.wr) (argAddr s₀ 0) 4 := inRd (in_arg hp h.wr (by decide))
  apply WP.of_runBlock
  simp only [layStart, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea, State.load32,
    Option.map_some, ea, i₀, h.arg0, ite_true, Option.some.injEq, exists_eq_left']

theorem Base.setEax {s₀ : State} {T : List Nat} {VP : (XReg → BitVec 128) → Prop} {s : State} (h : Base s₀ T VP s)
    (v : BitVec 32) : Base s₀ T VP (s.setReg .eax v) :=
  h.of_gpr (fun r h1 _ _ => by simp only [State.setReg, h1, ite_false]) rfl rfl rfl rfl h.vp

/-! ## A layer with `len ≥ 4` -/

theorem blk_ix (gl c : Nat) : 2 * (4 * gl) * c = 8 * (gl * c) := by
  rw [← Nat.mul_assoc 2 4 gl, Nat.mul_assoc]

/-- The coefficients done after `t` groups of block `c`, of `gl` groups. -/
def D4 (gl c t i : Nat) : Prop :=
  i < 8 * (gl * c) ∨ (8 * (gl * c) ≤ i ∧ i < 8 * (gl * c) + 4 * t) ∨
    (8 * (gl * c) + 4 * gl ≤ i ∧ i < 8 * (gl * c) + 4 * gl + 4 * t)

/-- Before block `c` of a layer with `len = 4 · gl`. -/
structure LInv (s₀ : State) (T : List Nat) (c3 : BitVec 32) (bd bd' : Nat) (f G : Poly) (gl zp c : Nat)
    (s : State) : Prop where
  base : Base s₀ T (VK c3) s
  eax : s.gpr .eax = fP s₀ + BitVec.ofNat 32 (16 * (2 * (gl * c)))
  edx : s.gpr .edx = sP s₀ + BitVec.ofNat 32 (4 * (zp + c))
  co : Co s₀ s.mem bd bd' f G (fun i => i < 8 * (gl * c))

/-- After `t` groups of four butterflies of block `c`. -/
structure GInv (s₀ : State) (T : List Nat) (c3 : BitVec 32) (bd bd' : Nat) (f G : Poly) (gl zp c t : Nat)
    (s : State) : Prop where
  base : Base s₀ T (VK c3) s
  eax : s.gpr .eax = fP s₀ + BitVec.ofNat 32 (16 * (2 * (gl * c) + t))
  ecx : s.gpr .ecx = BitVec.ofNat 32 (gl - t)
  edx : s.gpr .edx = sP s₀ + BitVec.ofNat 32 (4 * (zp + c + 1))
  z : s.xmm .xmm5 = bc (BitVec.ofNat 32 (T.getD (zp + c) 0))
  co : Co s₀ s.mem bd bd' f G (D4 gl c t)

theorem tab_lt {T : List Nat} {zv : Nat → Zq} (hT : NttLoop.TabOK T zv) {k : Nat} (hk : k < 256) :
    T.getD k 0 < 2 ^ 32 := by
  rw [hT k hk]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)

theorem blkInit_wp {s₀ : State} (hp : NttLoop.Pre s₀) {T : List Nat} {c3 : BitVec 32} {bd bd' : Nat} {f G : Poly}
    {gl zp c : Nat} (hz : zp + c < 256) {s : State} (h : LInv s₀ T c3 bd bd' f G gl zp c s) :
    WP isa (.block (blkInit (4 * gl))) s (GInv s₀ T c3 bd bd' f G gl zp c 0) := by
  have ez : (s.gpr .edx + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (sA s₀) (zp + c) := by
    rw [h.edx]; exact ea_ptr hp.s_fit hz
  have iz : InRegions (s.rd ++ s.wr) (coeffAddr (sA s₀) (zp + c)) 4 := in_tbl hp h.base.wr (by omega_using [hz])
  have vz : s.mem.readW (coeffAddr (sA s₀) (zp + c)) 32 = BitVec.ofNat 32 (T.getD (zp + c) 0) := h.base.tbl _ hz
  apply WP.of_runBlock
  simp only [blkInit, at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, XOp.exec, State.setXmm, readSrc,
    State.ea, State.load32, State.setReg, arithFlags, State.setFlags, Option.map_some, Option.bind_some, ez, iz, vz,
    reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
  refine ⟨h.base.of_gpr (fun r h1 h2 h3 => by simp only [h2, h3, ite_false]) rfl rfl rfl rfl
    (h.base.vp.of_eq fun r _ _ _ h5 => by simp only [h5, ite_false]), h.eax, ?_, ?_, bc_eq _, h.co.congr fun i hi => ?_⟩
  · show BitVec.ofNat 32 (4 * gl / 4) = _
    rw [Nat.mul_div_cancel_left gl (by decide), Nat.sub_zero]
  · show s.gpr .edx + 4 = _
    rw [h.edx]; exact ptr_next _ _ 4
  · simp only [D4]; omega_using []

theorem gstep {c3 : BitVec 32} {T : List Nat} {zv : Nat → Zq} {sS sD : Zq → Zq → Zq → Zq} {body : Nat → List Instr}
    {FX FY : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128} (hb : ∀ d, BodyOk c3 (body d) d true FX FY)
    {bd bd' : Nat} (hN : NewOk sh4 FX FY sS sD bd bd') (hT : NttLoop.TabOK T zv) {s₀ : State}
    (hp : NttLoop.Pre s₀) {f G : Poly} {gl zp : Nat} (hG : LayOk sS sD zv f G (4 * gl) zp) {B c t : Nat}
    (hB : gl * B = 32) (hc : c < B) (ht : t < gl) (hz : zp + c < 256) {s : State}
    (h : GInv s₀ T c3 bd bd' f G gl zp c t s) :
    WP isa (.block (body (4 * (4 * gl)) ++ groupEnd)) s fun s' =>
      GInv s₀ T c3 bd bd' f G gl zp c (t + 1) s' ∧ eval .ne s' = some (decide (t + 1 < gl)) := by
  have hL : gl * c + gl ≤ 32 := by
    have := Nat.mul_le_mul_left gl (Nat.succ_le_of_lt hc)
    rw [Nat.mul_succ, hB] at this; exact this
  have i1 : ∀ e < 4, idx (2 * (gl * c) + t) (2 * (gl * c) + t + gl) (sh4.pa e) =
      2 * (4 * gl) * c + (4 * t + e) := fun e he => by
    show (if e < 4 then 4 * (2 * (gl * c) + t) + e else _) = _
    rw [ite_eq_left he, blk_ix]; omega_using []
  have i2 : ∀ e < 4, idx (2 * (gl * c) + t) (2 * (gl * c) + t + gl) (sh4.pb e) =
      2 * (4 * gl) * c + (4 * t + e) + 4 * gl := fun e he => by
    show (if e + 4 < 4 then _ else 4 * (2 * (gl * c) + t + gl) + (e + 4 - 4)) = _
    rw [ite_eq_right (by omega_using []), blk_ix]; omega_using []
  refine body_step (hb _) hp h.base (u := 2 * (gl * c) + t) (u' := 2 * (gl * c) + t + gl) (by omega_using [hL, ht])
    (by omega_using [hL, ht]) (by omega_using []) h.eax h.co (fun i h8 hd => ?_)
    (fun X Y hV => hN f G _ _ (fun _ => zv (zp + c)) (fun e he => ?_) (fun e he => ?_) X Y hV)
    fun m g bs co k5 => ?_
  · simp only [In8] at h8
    simp only [D4] at hd
    omega_using [h8, hd, ht]
  · show (dword (s.xmm .xmm5) (2 * (e / 2))).toNat = _
    rw [h.z, dword_bc _ (show 2 * (e / 2) < 4 by omega_using [he]), toNat_ofNat32 (tab_lt hT hz), hT _ hz]
  · rw [i1 e he, i2 e he]
    exact hG c (4 * t + e) (by omega_using [ht, he]) (by rw [blk_ix]; omega_using [hL, ht, he])
  · apply WP.of_runBlock
    simp only [groupEnd, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.setReg, arithFlags,
      State.setFlags, Option.bind_some, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
    refine ⟨⟨bs.of_gpr (fun r h1 h2 _ => by simp only [h1, h2, ite_false]) rfl rfl rfl rfl bs.vp, ?_, ?_, h.edx,
      (k5 rfl).trans h.z, co.congr fun i hi => ?_⟩, ?_⟩
    · show s.gpr .eax + 16 = _
      rw [h.eax]; exact ptr_next _ _ 16
    · show s.gpr .ecx - 1 = _
      rw [h.ecx]; exact cnt_next ht
    · simp only [D4, In8]; omega_using []
    · show (some (s.gpr .ecx - 1 == 0) : Option Bool).map (!·) = _
      rw [h.ecx]; exact cnt_ne ht (by omega_using [hL])

theorem blkEnd_wp {s₀ : State} (hp : NttLoop.Pre s₀) {T : List Nat} {c3 : BitVec 32} {bd bd' : Nat} {f G : Poly}
    {gl zp B c : Nat} (hB : gl * B = 32) (hc : c < B) {s : State} (h : GInv s₀ T c3 bd bd' f G gl zp c gl s) :
    WP isa (.block (blkEnd (4 * gl))) s fun s' =>
      LInv s₀ T c3 bd bd' f G gl zp (c + 1) s' ∧ eval .ne s' = some (decide (c + 1 < B)) := by
  have hgl : 0 < gl := Nat.pos_of_ne_zero fun e => by rw [e, Nat.zero_mul] at hB; exact absurd hB (by decide)
  have hL : gl * (c + 1) ≤ 32 := by
    have := Nat.mul_le_mul_left gl (Nat.succ_le_of_lt hc)
    rwa [hB] at this
  obtain ⟨a₁, -⟩ := arg_M0 hp (i := 1) (by decide)
  simp only [Nat.mul_one, Nat.reduceAdd] at a₁
  have ea : (s.gpr .esp + BitVec.ofNat 32 20).setWidth 64 = argAddr s₀ 1 := by rw [h.base.esp]; exact a₁
  have i₁ : InRegions (s.rd ++ s.wr) (argAddr s₀ 1) 4 := inRd (in_arg hp h.base.wr (by decide))
  have sl := h.base.slot
  have e1 : s.gpr .eax + BitVec.ofNat 32 (4 * (4 * gl)) = fP s₀ + BitVec.ofNat 32 (16 * (2 * (gl * (c + 1)))) := by
    rw [h.eax, add_ofNat_add, Nat.mul_succ]
    exact congrArg (fun k => fP s₀ + BitVec.ofNat 32 k) (by omega_using [])
  apply WP.of_runBlock
  simp only [blkEnd, at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, ea, i₁, sl, reduceCtorEq, ↓reduceIte,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨h.base.of_gpr (fun r h1 _ _ => by simp only [h1, ite_false]) rfl rfl rfl rfl h.base.vp, e1, h.edx,
    h.co.congr fun i hi => ?_⟩, ?_⟩
  · simp only [D4]; rw [Nat.mul_succ]; omega_using []
  · show (some (s.gpr .eax + BitVec.ofNat 32 (4 * (4 * gl)) - (fP s₀ + 1024) == 0) : Option Bool).map (!·) = _
    rw [e1, NttLoop.end_cmp _ (by omega_using [hL])]
    simp only [Option.map_some, Option.some.injEq]
    by_cases h1 : c + 1 < B
    · have := Nat.mul_lt_mul_of_pos_left h1 hgl
      rw [hB] at this
      rw [decide_eq_true h1, decide_eq_false (by omega_using [this])]; rfl
    · have e : c + 1 = B := by omega_using [hc, h1]
      rw [decide_eq_false h1, e, hB]; rfl

theorem lay4_piece {c3 : BitVec 32} {T : List Nat} {zv : Nat → Zq} {sS sD : Zq → Zq → Zq → Zq}
    {body : Nat → List Instr} {FX FY : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128}
    (hb : ∀ d, BodyOk c3 (body d) d true FX FY) {bd bd' : Nat} (hN : NewOk sh4 FX FY sS sD bd bd')
    (hT : NttLoop.TabOK T zv) (gl B zp : Nat) (hB : gl * B = 32) (hz : zp + B ≤ 256) (f G : State → Poly)
    (hG : ∀ s₀, LayOk sS sD zv (f s₀) (G s₀) (4 * gl) zp) {h₁ h₂ h₃ h₄ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.sseTaint.check (τr [.esp]) (.block layStart) h₁).isSome = true)
    (t₂ : (VG.X86.sseTaint.check (τr [.esp, .eax, .edx]) (.block (blkInit (4 * gl))) h₂).isSome = true)
    (t₃ : (VG.X86.sseTaint.check (τr [.esp, .eax, .ecx, .edx]) (.block (body (4 * (4 * gl)) ++ groupEnd))
      h₃).isSome = true)
    (t₄ : (VG.X86.sseTaint.check (τr [.esp, .eax, .edx]) (.block (blkEnd (4 * gl))) h₄).isSome = true) :
    Piece NttLoop.Pre NttLoop.Pub (fun s₀ s => LS s₀ T (VK c3) bd (f s₀) zp s)
      (fun s₀ s => LS s₀ T (VK c3) bd' (G s₀) (zp + B) s) (layer4 body (4 * gl)) := by
  have hBp : 0 < B := Nat.pos_of_ne_zero fun e => by rw [e, Nat.mul_zero] at hB; exact absurd hB (by decide)
  have hgl : 0 < gl := Nat.pos_of_ne_zero fun e => by rw [e, Nat.zero_mul] at hB; exact absurd hB (by decide)
  refine Piece.mono (A := fun s₀ s => LS s₀ T (VK c3) bd (f s₀) zp s)
    (B := fun s₀ s => LInv s₀ T c3 bd bd' (f s₀) (G s₀) gl zp B s)
    (Piece.seq (B := fun s₀ s => LInv s₀ T c3 bd bd' (f s₀) (G s₀) gl zp 0 s)
    (Piece.sse [.esp] (fun s₀ s hp h => (layStart_wp hp h.base).mono fun s' e => ?_)
      (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) t₁)
    (Piece.loop (fun c s₀ s => LInv s₀ T c3 bd bd' (f s₀) (G s₀) gl zp c s) hBp fun c hc =>
      Piece.seq (Piece.sse [.esp, .eax, .edx] (fun s₀ s hp h => blkInit_wp hp (by omega_using [hz, hc]) h)
          (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) t₂)
        (Piece.seq (Piece.loop (fun t s₀ s => GInv s₀ T c3 bd bd' (f s₀) (G s₀) gl zp c t s) hgl fun t ht =>
            Piece.sse [.esp, .eax, .ecx, .edx]
              (fun s₀ s hp h => gstep hb hN hT hp (hG s₀) hB hc ht (by omega_using [hz, hc]) h)
              (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) t₃)
          (Piece.sse [.esp, .eax, .edx] (fun s₀ s hp h => blkEnd_wp hp hB hc h)
            (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) t₄)))) (fun _ _ _ h => h) fun s₀ s _ h => ?_
  · subst e
    refine ⟨h.base.setEax _, ?_, h.edx, fun i hi => ⟨fun hd => absurd hd (by rw [Nat.mul_zero]; omega_using []),
      fun _ => h.co i hi⟩⟩
    show fP s₀ = fP s₀ + BitVec.ofNat 32 (16 * (2 * (gl * 0)))
    rw [Nat.mul_zero]; exact (BitVec.add_zero _).symm
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.base.esp, h'.base.esp, M0_esp, M0_esp, hq.1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h.base.esp, h'.base.esp, M0_esp, M0_esp, hq.1]
    · rw [h.eax, h'.eax, fP, fP, hq.2.1]
    · rw [h.edx, h'.edx, sP, sP, hq.2.2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h.base.esp, h'.base.esp, M0_esp, M0_esp, hq.1]
    · rw [h.eax, h'.eax, fP, fP, hq.2.1]
    · rw [h.ecx, h'.ecx]
    · rw [h.edx, h'.edx, sP, sP, hq.2.2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h.base.esp, h'.base.esp, M0_esp, M0_esp, hq.1]
    · rw [h.eax, h'.eax, fP, fP, hq.2.1]
    · rw [h.edx, h'.edx, sP, sP, hq.2.2]
  · exact ⟨h.base, h.edx, fun i hi => (h.co i hi).1 (by rw [hB]; exact hi)⟩

/-! ## The layers with `len = 2` and `len = 1` -/

/-- After `k` steps of eight coefficients, each with `nz` zetas. -/
structure FInv (s₀ : State) (T : List Nat) (c3 : BitVec 32) (bd bd' : Nat) (f G : Poly) (nz zp k : Nat)
    (s : State) : Prop where
  base : Base s₀ T (VK c3) s
  eax : s.gpr .eax = fP s₀ + BitVec.ofNat 32 (16 * (2 * k))
  edx : s.gpr .edx = sP s₀ + BitVec.ofNat 32 (4 * (zp + nz * k))
  co : Co s₀ s.mem bd bd' f G (fun i => i < 8 * k)

/-- The code that loads the zetas of a step, `nb` bytes at `[edx]`, into `xmm5`. -/
def ZlOk (zl : List Instr) (nb : Nat) (zsel : Mem → Addr → BitVec 128) : Prop :=
  ∀ (s : State) (f : XReg → BitVec 128) (is : List Instr) (Q : State → Prop) (a : Addr), s.ea (at_ .edx 0) = a →
    InRegions (s.rd ++ s.wr) a nb →
    (∀ g : XReg → BitVec 128, g .xmm5 = zsel s.mem a → (∀ r, r ≠ .xmm5 → g r = f r) →
      WP isa (.block is) { s with xmm := g } Q) →
    WP isa (.block (zl ++ is)) { s with xmm := f } Q

theorem zl2_ok : ZlOk zl2 8 fun m a => shufDwords ((0 : BitVec 64) ++ m.readW a 64) 0x98 :=
  fun _ _ _ _ _ ha hin k => wp_lq ha hin (wp_xs rfl (k _ rfl fun r h5 => by simp only [h5, ite_false]))

theorem zl1_ok : ZlOk zl1 16 fun m a => m.readW a 128 :=
  fun _ _ _ _ _ ha hin k => wp_ld ha hin (k _ rfl fun r h5 => by simp only [h5, ite_false])

/-- A layer whose steps are of eight coefficients, with `nz` zetas each:
doubleword `sh.zl e` of the zetas loaded is the zeta of number `zq e` of
the step, and that of the butterfly `e`. -/
structure FlatOk (sh : Shape) (nz len : Nat) (zq : Nat → Nat) (zsel : Mem → Addr → BitVec 128) : Prop where
  zeta : ∀ (m : Mem) (tA : Addr) (T : List Nat) (zv : Nat → Zq), NttLoop.TabOK T zv →
    (∀ j < 256, coeffAt m tA j = BitVec.ofNat 32 (T.getD j 0)) → ∀ j, j + nz ≤ 256 → ∀ e < 4,
      (dword (zsel m (coeffAddr tA j)) (sh.zl e)).toNat = (zv (j + zq e)).val * 2 ^ 32 % q
  pairs : ∀ (sS sD : Zq → Zq → Zq → Zq) (zv : Nat → Zq) (f G : Poly) (zp : Nat), LayOk sS sD zv f G len zp →
    ∀ k < 32, ∀ e < 4,
      G[idx (2 * k) (2 * k + 1) (sh.pa e)]! = sS f[idx (2 * k) (2 * k + 1) (sh.pa e)]!
          f[idx (2 * k) (2 * k + 1) (sh.pb e)]! (zv (zp + nz * k + zq e)) ∧
        G[idx (2 * k) (2 * k + 1) (sh.pb e)]! = sD f[idx (2 * k) (2 * k + 1) (sh.pa e)]!
          f[idx (2 * k) (2 * k + 1) (sh.pb e)]! (zv (zp + nz * k + zq e))

theorem idx_flat (k : Nat) {p : Nat} (hp : p < 8) : idx (2 * k) (2 * k + 1) p = 8 * k + p := by
  rw [idx]
  by_cases h : p < 4
  · rw [ite_eq_left h]; omega_using []
  · rw [ite_eq_right h]; omega_using [h, hp]

theorem lay2_at {sS sD : Zq → Zq → Zq → Zq} {zv : Nat → Zq} {f G : Poly} {zp : Nat} (hG : LayOk sS sD zv f G 2 zp)
    {k p : Nat} (hk : k < 32) (hp : p % 4 < 2) (hp8 : p < 8) :
    G[8 * k + p]! = sS f[8 * k + p]! f[8 * k + p + 2]! (zv (zp + 2 * k + p / 4)) ∧
      G[8 * k + p + 2]! = sD f[8 * k + p]! f[8 * k + p + 2]! (zv (zp + 2 * k + p / 4)) := by
  have := hG (2 * k + p / 4) (p % 4) hp (by omega_using [hk, hp8, hp])
  rwa [show 2 * 2 * (2 * k + p / 4) + p % 4 = 8 * k + p by omega_using [], ← Nat.add_assoc zp] at this

theorem flat2 : FlatOk sh2 2 2 (fun e => e / 2) fun m a => shufDwords ((0 : BitVec 64) ++ m.readW a 64) 0x98 where
  zeta m tA T zv hT htb j hj e he := by
    have z0 : (dword (shufDwords ((0 : BitVec 64) ++ m.readW (coeffAddr tA j) 64) 0x98) 0).toNat =
        (zv j).val * 2 ^ 32 % q := by
      rw [dword_shufDwords _ _ (by decide)]
      show (dword ((0 : BitVec 64) ++ m.readW (coeffAddr tA j) 64) 0).toNat = _
      rw [VG.Proof.Mont.X86.Sse2.dword_movq_0, VG.Proof.Mont.X86.Sse2.readW64_lo, ← coeffAt_eq,
        htb j (by omega_using [hj]), toNat_ofNat32 (tab_lt hT (by omega_using [hj])), hT j (by omega_using [hj])]
    have z2 : (dword (shufDwords ((0 : BitVec 64) ++ m.readW (coeffAddr tA j) 64) 0x98) 2).toNat =
        (zv (j + 1)).val * 2 ^ 32 % q := by
      rw [dword_shufDwords _ _ (by decide)]
      show (dword ((0 : BitVec 64) ++ m.readW (coeffAddr tA j) 64) 1).toNat = _
      rw [VG.Proof.Mont.X86.Sse2.dword_movq_1, VG.Proof.Mont.X86.Sse2.readW64_hi,
        show coeffAddr tA j + 4 = coeffAddr tA (j + 1) from coeffAddr_add tA j 1, ← coeffAt_eq,
        htb (j + 1) (by omega_using [hj]), toNat_ofNat32 (tab_lt hT (by omega_using [hj])),
        hT (j + 1) (by omega_using [hj])]
    rcases cases4 he with rfl | rfl | rfl | rfl
    · exact z0
    · exact z0
    · exact z2
    · exact z2
  pairs sS sD zv f G zp hG k hk e he := by
    rw [idx_flat k (sh2_ok.lt e he).1, idx_flat k (sh2_ok.lt e he).2]
    rcases cases4 he with rfl | rfl | rfl | rfl
    · exact lay2_at hG hk (p := 0) (by decide) (by decide)
    · exact lay2_at hG hk (p := 1) (by decide) (by decide)
    · exact lay2_at hG hk (p := 4) (by decide) (by decide)
    · exact lay2_at hG hk (p := 5) (by decide) (by decide)

theorem lay1_at {sS sD : Zq → Zq → Zq → Zq} {zv : Nat → Zq} {f G : Poly} {zp : Nat} (hG : LayOk sS sD zv f G 1 zp)
    {k e : Nat} (hk : k < 32) (he : e < 4) :
    G[8 * k + 2 * e]! = sS f[8 * k + 2 * e]! f[8 * k + 2 * e + 1]! (zv (zp + 4 * k + e)) ∧
      G[8 * k + 2 * e + 1]! = sD f[8 * k + 2 * e]! f[8 * k + 2 * e + 1]! (zv (zp + 4 * k + e)) := by
  have := hG (4 * k + e) 0 (by decide) (by omega_using [hk, he])
  rwa [show 2 * 1 * (4 * k + e) + 0 = 8 * k + 2 * e by omega_using [], ← Nat.add_assoc zp] at this

theorem flat1 : FlatOk sh1 4 1 (fun e => e) fun m a => m.readW a 128 where
  zeta m tA T zv hT htb j hj e he := by
    show (dword (m.readW (coeffAddr tA j) 128) e).toNat = _
    rw [dword_readW _ _ he, coeffAddr_add, ← coeffAt_eq, htb (j + e) (by omega_using [hj, he]),
      toNat_ofNat32 (tab_lt hT (by omega_using [hj, he])), hT (j + e) (by omega_using [hj, he])]
  pairs sS sD zv f G zp hG k hk e he := by
    rw [idx_flat k (sh1_ok.lt e he).1, idx_flat k (sh1_ok.lt e he).2]
    exact lay1_at hG hk he

theorem fstep {sh : Shape} {nz len : Nat} {zq : Nat → Nat} {zsel : Mem → Addr → BitVec 128}
    (hfl : FlatOk sh nz len zq zsel) (hnz : 0 < nz) {zl : List Instr} (hzl : ZlOk zl (4 * nz) zsel)
    {c3 : BitVec 32} {body : List Instr} {FX FY : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128}
    (hb : BodyOk c3 body 16 false FX FY) {sS sD : Zq → Zq → Zq → Zq} {bd bd' : Nat}
    (hN : NewOk sh FX FY sS sD bd bd') {T : List Nat} {zv : Nat → Zq} (hT : NttLoop.TabOK T zv) {s₀ : State}
    (hp : NttLoop.Pre s₀) {f G : Poly} {zp : Nat} (hG : LayOk sS sD zv f G len zp) (hz : zp + nz * 32 ≤ 256)
    {k : Nat} (hk : k < 32) {s : State} (h : FInv s₀ T c3 bd bd' f G nz zp k s) :
    WP isa (.block (zl ++ (body ++ flatEnd (4 * nz)))) s fun s' =>
      FInv s₀ T c3 bd bd' f G nz zp (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 32)) := by
  have hj : zp + nz * k + nz ≤ 256 := by
    have := Nat.mul_le_mul_left nz (Nat.succ_le_of_lt hk)
    rw [Nat.mul_succ] at this; omega_using [hz, this]
  have ez : s.ea (at_ .edx 0) = coeffAddr (sA s₀) (zp + nz * k) := by
    rw [State.ea, at_, h.edx]; exact ea_ptr hp.s_fit (by omega_using [hj, hnz])
  show WP isa (.block (zl ++ (body ++ flatEnd (4 * nz)))) { s with xmm := s.xmm } _
  refine hzl s s.xmm _ _ _ ez (in_tbl hp h.base.wr (by omega_using [hj])) fun g g5 gr => ?_
  have bs : Base s₀ T (VK c3) { s with xmm := g } :=
    ⟨h.base.esp, h.base.rd, h.base.wr, h.base.mcdt, h.base.saved, h.base.frame, h.base.tbl, h.base.arg0,
      h.base.slot, h.base.vp.of_eq fun r _ _ _ h5 => gr r h5⟩
  refine body_step hb hp bs (u := 2 * k) (u' := 2 * k + 1) (by omega_using [hk]) (by omega_using [hk])
    (by omega_using []) h.eax h.co (fun i h8 hd => ?_)
    (fun X Y hV => hN f G _ _ (fun e => zv (zp + nz * k + zq e)) (fun e he => ?_)
      (hfl.pairs sS sD zv f G zp hG k hk) X Y hV) fun m g' bs' co _ => ?_
  · simp only [In8] at h8; omega_using [h8, hd]
  · show (dword (g .xmm5) (sh.zl e)).toNat = _
    rw [g5]; exact hfl.zeta _ _ T zv hT h.base.tbl _ hj e he
  · obtain ⟨a₁, -⟩ := arg_M0 hp (i := 1) (by decide)
    simp only [Nat.mul_one, Nat.reduceAdd] at a₁
    have ea : (s.gpr .esp + BitVec.ofNat 32 20).setWidth 64 = argAddr s₀ 1 := by rw [h.base.esp]; exact a₁
    have i₁ : InRegions (s.rd ++ s.wr) (argAddr s₀ 1) 4 := inRd (in_arg hp h.base.wr (by decide))
    have sl : m.readW (argAddr s₀ 1) 32 = fP s₀ + 1024 := bs'.slot
    have e1 : s.gpr .eax + 32 = fP s₀ + BitVec.ofNat 32 (16 * (2 * (k + 1))) := by
      rw [h.eax, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, add_ofNat_add]
      exact congrArg (fun k => fP s₀ + BitVec.ofNat 32 k) (by omega_using [])
    apply WP.of_runBlock
    simp only [flatEnd, at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea,
      State.load32, State.setReg, arithFlags, State.setFlags, Option.bind_some, ea, i₁, sl,
      reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
    refine ⟨⟨bs'.of_gpr (fun r h1 _ h3 => by simp only [h1, h3, ite_false]) rfl rfl rfl rfl bs'.vp, e1, ?_,
      co.congr fun i hi => ?_⟩, ?_⟩
    · show s.gpr .edx + BitVec.ofNat 32 (4 * nz) = _
      rw [h.edx, add_ofNat_add, Nat.mul_succ]
      exact congrArg (fun k => sP s₀ + BitVec.ofNat 32 k) (by omega_using [])
    · simp only [In8]; omega_using []
    · show (some (s.gpr .eax + 32 - (fP s₀ + 1024) == 0) : Option Bool).map (!·) = _
      rw [e1, NttLoop.end_cmp _ (by omega_using [hk])]
      simp only [Option.map_some, Option.some.injEq]
      by_cases h1 : k + 1 < 32
      · rw [decide_eq_true h1, decide_eq_false (by omega_using [h1])]; rfl
      · rw [decide_eq_false h1, decide_eq_true (by omega_using [hk, h1])]; rfl

theorem layFlat_piece {sh : Shape} {nz len : Nat} {zq : Nat → Nat} {zsel : Mem → Addr → BitVec 128}
    (hfl : FlatOk sh nz len zq zsel) (hnz : 0 < nz) {zl : List Instr} (hzl : ZlOk zl (4 * nz) zsel)
    {c3 : BitVec 32} {body : List Instr} {FX FY : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128}
    (hb : BodyOk c3 body 16 false FX FY) {sS sD : Zq → Zq → Zq → Zq} {bd bd' : Nat}
    (hN : NewOk sh FX FY sS sD bd bd') {T : List Nat} {zv : Nat → Zq} (hT : NttLoop.TabOK T zv) (zp : Nat)
    (hz : zp + nz * 32 ≤ 256) (f G : State → Poly) (hG : ∀ s₀, LayOk sS sD zv (f s₀) (G s₀) len zp)
    {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.sseTaint.check (τr [.esp]) (.block layStart) h₁).isSome = true)
    (t₂ : (VG.X86.sseTaint.check (τr [.esp, .eax, .edx]) (.block (zl ++ (body ++ flatEnd (4 * nz))))
      h₂).isSome = true) :
    Piece NttLoop.Pre NttLoop.Pub (fun s₀ s => LS s₀ T (VK c3) bd (f s₀) zp s)
      (fun s₀ s => LS s₀ T (VK c3) bd' (G s₀) (zp + nz * 32) s) (layerFlat zl body (4 * nz)) := by
  refine Piece.mono (A := fun s₀ s => LS s₀ T (VK c3) bd (f s₀) zp s)
    (B := fun s₀ s => FInv s₀ T c3 bd bd' (f s₀) (G s₀) nz zp 32 s)
    (Piece.seq (B := fun s₀ s => FInv s₀ T c3 bd bd' (f s₀) (G s₀) nz zp 0 s)
    (Piece.sse [.esp] (fun s₀ s hp h => (layStart_wp hp h.base).mono fun s' e => ?_)
      (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) t₁)
    (Piece.loop (fun k s₀ s => FInv s₀ T c3 bd bd' (f s₀) (G s₀) nz zp k s) (by decide) fun k hk =>
      Piece.sse [.esp, .eax, .edx] (fun s₀ s hp h => fstep hfl hnz hzl hb hN hT hp (hG s₀) hz hk h)
        (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) t₂)) (fun _ _ _ h => h) fun s₀ s _ h => ?_
  · subst e
    exact ⟨h.base.setEax _, (BitVec.add_zero _).symm, h.edx, fun i hi =>
      ⟨fun hd => absurd hd (by omega_using []), fun _ => h.co i hi⟩⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.base.esp, h'.base.esp, M0_esp, M0_esp, hq.1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h.base.esp, h'.base.esp, M0_esp, M0_esp, hq.1]
    · rw [h.eax, h'.eax, fP, fP, hq.2.1]
    · rw [h.edx, h'.edx, sP, sP, hq.2.2]
  · exact ⟨h.base, h.edx, fun i hi => (h.co i hi).1 hi⟩

/-! ## The constants and the table -/

/-- The polynomial at entry. -/
abbrev F (s₀ : State) : Poly := polyAt s₀.mem (fA s₀)

/-- What is written apart from `f` keeps `f`. -/
theorem keep_f {s₀ : State} (hp : NttLoop.Pre s₀) {m : Mem}
    (hf : Frame [polyRegion (sA s₀), aR2 s₀] (M0 s₀).mem m) {i : Nat} (hi : i < 256) :
    coeffAt m (fA s₀) i = coeffAt s₀.mem (fA s₀) i := by
  rw [coeffAt_congr (m := s₀.mem) (m' := m) (fun j hj => ?_) hi]
  rw [hf.bytes (R := polyRegion (fA s₀)) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.f_s
      · exact hp.f_a) (polyLen _) hj,
    (M0_frame s₀ (sp12 hp)).bytes (R := polyRegion (fA s₀)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (mcdt_disj hp hp.stk_f).symm) (polyLen _) hj]

/-- After the constants: `eax` is `scratch`. -/
structure S1 (s₀ : State) (c3 : BitVec 32) (s : State) : Prop where
  esp : s.gpr .esp = (M0 s₀).gpr .esp
  eax : s.gpr .eax = sP s₀
  rd : s.rd = (M0 s₀).rd
  wr : s.wr = (M0 s₀).wr
  mem : s.mem = (M0 s₀).mem
  mcdt : s.mcdt = s₀.mcdt + 1
  saved : ∀ r ∈ [Reg.ebx, .esi, .edi, .ebp], s.gpr r = s₀.gpr r
  vk : VK c3 s.xmm

theorem consts_wp {s₀ : State} (hp : NttLoop.Pre s₀) (c3 : BitVec 32) :
    WP isa (.block (nttConsts c3)) (M0 s₀) (S1 s₀ c3) := by
  obtain ⟨a₁, v₁⟩ := arg_M0 hp (i := 1) (by decide)
  simp only [Nat.mul_one, Nat.reduceAdd] at a₁
  have i₁ : InRegions ((M0 s₀).rd ++ (M0 s₀).wr) (argAddr s₀ 1) 4 := inRd (in_arg hp rfl (by decide))
  apply WP.of_runBlock
  simp only [nttConsts, vconst, at_, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, XOp.exec, State.setXmm, readSrc, State.ea, State.load32, State.setReg, a₁, i₁, v₁, Option.map_some,
    reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun r hr => ?_, ⟨bc_eq _, bc_eq _, bc_eq _, bc_eq _⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> rfl

theorem table_wp {s₀ : State} (hp : NttLoop.Pre s₀) (T : List Nat) {c3 : BitVec 32} {s : State}
    (h : S1 s₀ c3 s) : WP isa (.block (nttTable T)) s (LS s₀ T (VK c3) 1 (F s₀) 1) := by
  obtain ⟨a₀, v₀⟩ := arg_M0 hp (i := 0) (by decide)
  obtain ⟨a₁, -⟩ := arg_M0 hp (i := 1) (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd] at a₀ a₁
  rw [nttTable]
  refine table_spec T (p := sA s₀) _ _ _ (fun k hk => ?_) (fun k hk => ?_) fun s₂ o₂ f₂ c₂ => ?_
  · show (s.gpr .eax + BitVec.ofNat 32 (4 * k)).setWidth 64 = _
    rw [h.eax]
    exact ea_off (by have : (sP s₀).toNat + 1024 ≤ 2 ^ 32 := hp.s_fit; omega_using [this, hk])
  · exact ⟨polyRegion (sA s₀), by rw [h.wr, M0_wr, hp.wr]; simp, coeff_contains _ (by rw [n_eq]; exact hk)⟩
  have esp₂ : s₂.gpr .esp = (M0 s₀).gpr .esp := (o₂.gpr .esp (by decide)).trans h.esp
  have eax₂ : s₂.gpr .eax = sP s₀ := (o₂.gpr .eax (by decide)).trans h.eax
  have rd₂ : s₂.rd = (M0 s₀).rd := o₂.rd.trans h.rd
  have wr₂ : s₂.wr = (M0 s₀).wr := o₂.wr.trans h.wr
  have f₂' : Frame [polyRegion (sA s₀)] (M0 s₀).mem s₂.mem := h.mem ▸ f₂
  have a16 : (s₂.gpr .esp + BitVec.ofNat 32 16).setWidth 64 = argAddr s₀ 0 := by rw [esp₂]; exact a₀
  have a20 : (s₂.gpr .esp + BitVec.ofNat 32 20).setWidth 64 = argAddr s₀ 1 := by rw [esp₂]; exact a₁
  have in0 : InRegions (s₂.rd ++ s₂.wr) (argAddr s₀ 0) 4 := inRd (in_arg hp wr₂ (by decide))
  have in1 : InRegions s₂.wr (argAddr s₀ 1) 4 := in_arg hp wr₂ (by decide)
  have hsa : ∀ r ∈ [polyRegion (sA s₀)], (aR2 s₀).Disjoint r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hp.s_a.symm
  have v0 : s₂.mem.readW (argAddr s₀ 0) 32 = fP s₀ := by
    rw [f₂'.readW (hp.arg_in (by decide)) hsa (by decide)]; exact v₀
  apply WP.of_runBlock
  simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32,
    State.store32, State.setReg, arithFlags, State.setFlags, Option.map_some, Option.bind_some, a16, a20, in0, in1,
    v0, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
  have fr : Frame [polyRegion (sA s₀), aR2 s₀] (M0 s₀).mem (s₂.mem.writeW (argAddr s₀ 1) (fP s₀ + 1024)) :=
    (f₂'.mono fun r hr => by simp at hr ⊢; exact .inl hr).writeW (by simp) _ (hp.arg_in (by decide))
  refine ⟨⟨esp₂, rd₂, wr₂, o₂.mcdt.trans h.mcdt, fun r hr => ?_, fr.mono fun r hr => by simp at hr ⊢; exact .inr hr,
    fun k hk => ?_, ?_, Mem.readW_writeW_self32 _ _ _, ?_⟩, ?_, fun i hi => ?_⟩
  · have e : s₂.gpr r = s.gpr r := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact o₂.gpr _ (by decide)
    have e' := h.saved r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact e.trans e'
  · show coeffAt (s₂.mem.writeW (argAddr s₀ 1) (fP s₀ + 1024)) (sA s₀) k = _
    rw [coeffAt_eq, Mem.readW_writeW_sep (Region.Disjoint.sep hp.s_a (coeff_contains _ (by rw [n_eq]; exact hk))
      (hp.arg_in (by decide))) (by decide), ← coeffAt_eq, c₂ k hk]
  · show (s₂.mem.writeW (argAddr s₀ 1) (fP s₀ + 1024)).readW (argAddr s₀ 0) 32 = _
    rw [Mem.readW_writeW_sep (NttLoop.arg01_sep hp) (by decide), v0]
  · show VK c3 s₂.xmm
    rw [o₂.xmm]; exact h.vk
  · show s₂.gpr .eax + 4 = _
    rw [eax₂]; rfl
  · show Lz 1 (coeffAt (s₂.mem.writeW (argAddr s₀ 1) (fP s₀ + 1024)) (fA s₀) i).toNat _
    rw [keep_f hp fr hi]
    have hr := hp.f_red i (by rw [n_eq]; exact hi)
    exact ⟨by rw [Nat.one_mul]; exact hr, by
      rw [polyAt_val hp.f_red (by rw [n_eq]; exact hi)]; exact Nat.mod_eq_of_lt hr⟩

theorem init_piece (T : List Nat) (c3 : BitVec 32) {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.sseTaint.check (τr [.esp]) (.block (nttConsts c3)) h₁).isSome = true)
    (t₂ : (VG.X86.sseTaint.check (τr [.esp, .eax]) (.block (nttTable T)) h₂).isSome = true) :
    Piece NttLoop.Pre NttLoop.Pub (fun s₀ s => s = M0 s₀) (fun s₀ s => LS s₀ T (VK c3) 1 (F s₀) 1 s)
      (nttInit T c3) := by
  refine Piece.seq (B := fun s₀ s => S1 s₀ c3 s)
    (Piece.sse [.esp] (fun s₀ s hp e => e ▸ consts_wp hp c3) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_) t₁)
    (Piece.sse [.esp, .eax] (fun s₀ s hp h => table_wp hp T h) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) t₂)
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', M0_esp, M0_esp, hq.1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.esp, h'.esp, M0_esp, M0_esp, hq.1]
    · rw [h.eax, h'.eax, sP, sP, hq.2.2]

/-! ## A pass over the coefficients -/

/-- After `k` groups of four coefficients of a pass: they are `red` of what they stood for, reduced. -/
structure PInv (s₀ : State) (T : List Nat) (VP : (XReg → BitVec 128) → Prop) (bd : Nat) (G : Poly)
    (red : Zq → Zq) (k : Nat) (s : State) : Prop where
  base : Base s₀ T VP s
  eax : s.gpr .eax = fP s₀ + BitVec.ofNat 32 (16 * k)
  done : ∀ i < 4 * k, (coeffAt s.mem (fA s₀) i).toNat = (red G[i]!).val
  rest : ∀ i < 256, 4 * k ≤ i → Lz bd (coeffAt s.mem (fA s₀) i).toNat G[i]!

/-- The code of a pass, on `x` in `xmm0`. -/
def PassOk (core : List Instr) (VP : (XReg → BitVec 128) → Prop) (Fx : BitVec 128 → BitVec 128) : Prop :=
  ∀ (s : State) (f : XReg → BitVec 128) (x : BitVec 128) (is : List Instr) (Q : State → Prop), 0 < s.mcdt → VP f →
    (∀ g : XReg → BitVec 128, g .xmm0 = Fx x → VP g → WP isa (.block is) { s with xmm := g } Q) →
    WP isa (.block (core ++ is)) { s with xmm := fun r => if r = .xmm0 then x else f r } Q

theorem pstep {core : List Instr} {VP : (XReg → BitVec 128) → Prop} {Fx : BitVec 128 → BitVec 128}
    (hc : PassOk core VP Fx) {bd : Nat} {red : Zq → Zq} (hl : PassLane bd Fx red) {s₀ : State}
    (hp : NttLoop.Pre s₀) {T : List Nat} {G : Poly} {k : Nat} (hk : k < 64) {s : State}
    (h : PInv s₀ T VP bd G red k s) :
    WP isa (.block (passStep core)) s fun s' =>
      PInv s₀ T VP bd G red (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 64)) := by
  have eP : s.ea (at_ .eax 0) = coeffAddr (fA s₀) (4 * k) := by
    rw [State.ea, at_, h.eax, show 16 * k = 4 * (4 * k) by omega_using []]
    exact ea_ptr hp.f_fit (by omega_using [hk])
  have hm : 0 < s.mcdt := by rw [h.base.mcdt]; exact Nat.succ_pos _
  have iP := in_f16 hp h.base.wr hk
  have hcon : (polyRegion (fA s₀)).Contains (coeffAddr (fA s₀) (4 * k)) (128 / 8) :=
    Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])
  show WP isa (.block (.movdquLoad .xmm0 (at_ .eax 0) :: (core ++ _))) { s with xmm := s.xmm } _
  refine wp_ld eP (inRd16 iP) (hc s _ _ _ _ hm h.base.vp fun g vg cg => wp_st eP iP ?_)
  have bs := h.base.step hp ((Frame.refl _ _).writeW (List.mem_singleton_self _) (g .xmm0) hcon) cg
  have dX : ∀ j < 4, dword (s.mem.readW (coeffAddr (fA s₀) (4 * k)) 128) j = coeffAt s.mem (fA s₀) (4 * k + j) :=
    fun j hj => by rw [dword_readW _ _ hj, coeffAddr_add, ← coeffAt_eq]
  have lanes : ∀ j < 4, (dword (g .xmm0) j).toNat = (red G[4 * k + j]!).val := fun j hj => by
    rw [vg]
    exact hl _ (fun i => G[4 * k + i]!) (fun i hi => by
      show Lz bd (dword (s.mem.readW (coeffAddr (fA s₀) (4 * k)) 128) i).toNat _
      rw [dX i hi]; exact h.rest _ (by omega_using [hk, hi]) (by omega_using [])) j hj
  obtain ⟨a₁, -⟩ := arg_M0 hp (i := 1) (by decide)
  simp only [Nat.mul_one, Nat.reduceAdd] at a₁
  have ea : (s.gpr .esp + BitVec.ofNat 32 20).setWidth 64 = argAddr s₀ 1 := by rw [h.base.esp]; exact a₁
  have i₁ : InRegions (s.rd ++ s.wr) (argAddr s₀ 1) 4 := inRd (in_arg hp h.base.wr (by decide))
  have sl : (s.mem.writeW (coeffAddr (fA s₀) (4 * k)) (g .xmm0)).readW (argAddr s₀ 1) 32 = fP s₀ + 1024 := bs.slot
  have e1 : s.gpr .eax + 16 = fP s₀ + BitVec.ofNat 32 (16 * (k + 1)) := by rw [h.eax]; exact ptr_next _ _ 16
  apply WP.of_runBlock
  simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, ea, i₁, sl, reduceCtorEq, ↓reduceIte,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨bs.of_gpr (fun r h1 _ _ => by simp only [h1, ite_false]) rfl rfl rfl rfl bs.vp, e1, fun i hi => ?_,
    fun i hi hk' => ?_⟩, ?_⟩
  · show (coeffAt (s.mem.writeW (coeffAddr (fA s₀) (4 * k)) (g .xmm0)) (fA s₀) i).toNat = _
    rw [coeffAt_write16 _ _ _ hk (by omega_using [hi, hk])]
    by_cases h1 : 4 * k ≤ i ∧ i < 4 * k + 4
    · rw [ite_eq_left h1, lanes _ (by omega_using [h1]), show 4 * k + (i - 4 * k) = i by omega_using [h1]]
    · rw [ite_eq_right h1]; exact h.done i (by omega_using [hi, h1])
  · show Lz bd (coeffAt (s.mem.writeW (coeffAddr (fA s₀) (4 * k)) (g .xmm0)) (fA s₀) i).toNat _
    rw [coeffAt_write16 _ _ _ hk hi, ite_eq_right (by omega_using [hk'])]
    exact h.rest i hi (by omega_using [hk'])
  · show (some (s.gpr .eax + 16 - (fP s₀ + 1024) == 0) : Option Bool).map (!·) = _
    rw [e1, NttLoop.end_cmp _ (by omega_using [hk])]
    simp only [Option.map_some, Option.some.injEq]
    by_cases h1 : k + 1 < 64
    · rw [decide_eq_true h1, decide_eq_false (by omega_using [h1])]; rfl
    · rw [decide_eq_false h1, decide_eq_true (by omega_using [hk, h1])]; rfl

theorem pass_piece {init core : List Instr} {VP VP' : (XReg → BitVec 128) → Prop} {Fx : BitVec 128 → BitVec 128}
    {bd : Nat} {red : Zq → Zq} {T : List Nat} (hc : PassOk core VP' Fx) (hl : PassLane bd Fx red) (G : State → Poly)
    (zp : Nat)
    (hinit : ∀ s₀ s, NttLoop.Pre s₀ → LS s₀ T VP bd (G s₀) zp s →
      WP isa (.block (init ++ layStart)) s (PInv s₀ T VP' bd (G s₀) red 0))
    {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.sseTaint.check (τr [.esp]) (.block (init ++ layStart)) h₁).isSome = true)
    (t₂ : (VG.X86.sseTaint.check (τr [.esp, .eax]) (.block (passStep core)) h₂).isSome = true) :
    Piece NttLoop.Pre NttLoop.Pub (fun s₀ s => LS s₀ T VP bd (G s₀) zp s)
      (fun s₀ s => PInv s₀ T VP' bd (G s₀) red 64 s) (pass init core) := by
  refine Piece.seq (B := fun s₀ s => PInv s₀ T VP' bd (G s₀) red 0 s)
    (Piece.sse [.esp] hinit (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) t₁)
    (Piece.loop (fun k s₀ s => PInv s₀ T VP' bd (G s₀) red k s) (by decide) fun k hk =>
      Piece.sse [.esp, .eax] (fun s₀ s hp h => pstep hc hl hp hk h) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) t₂)
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.base.esp, h'.base.esp, M0_esp, M0_esp, hq.1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.base.esp, h'.base.esp, M0_esp, M0_esp, hq.1]
    · rw [h.eax, h'.eax, fP, fP, hq.2.1]

/-! ## The last pass of `ntt` -/

/-- The constants of the last pass of `ntt`. -/
structure VF (f : XReg → BitVec 128) : Prop where
  q : f .xmm7 = qV
  ones : f .xmm4 = onesV
  m23 : f .xmm5 = bc 8388607#32
  nq1 : f .xmm3 = bc 4286586880#32

/-- What `finFold` leaves in `xmm0`. -/
def foldV (x : BitVec 128) : BitVec 128 :=
  XBinOp.eval .paddd (XBinOp.eval .paddd (XBinOp.eval .paddd (XBinOp.eval .pand x (bc 8388607#32))
    (XShiftOp.eval .pslld (XShiftOp.eval .psrld x 23) 13)) (XBinOp.eval .pxor (XShiftOp.eval .psrld x 23) onesV))
    (bc 4286586880#32)

/-- What `finSub` leaves in `xmm0`. -/
def csubT (y : BitVec 128) : BitVec 128 :=
  XBinOp.eval .paddd y (XBinOp.eval .pandn (XBinOp.eval .paddd (XShiftOp.eval .psrld y 31) onesV) qV)

theorem finFold_wp {f : XReg → BitVec 128} {x : BitVec 128} {is : List Instr} {Q : State → Prop} (hc : VF f)
    (k : ∀ g : XReg → BitVec 128, g .xmm0 = foldV x → (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → g r = f r) →
      WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (finFold ++ is)) { s with xmm := fun r => if r = .xmm0 then x else f r } Q := by
  refine wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl
    (k _ ?_ ?_)))))))))
  · simp only [foldV]
    rw [← hc.ones, ← hc.m23, ← hc.nq1]
    rfl
  · intro r h0 h1 h2
    simp only [h0, h1, h2, ite_false]

theorem finSub_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} (h4 : f .xmm4 = onesV)
    (h7 : f .xmm7 = qV)
    (k : ∀ g : XReg → BitVec 128, g .xmm0 = csubT (f .xmm0) → (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → g r = f r) →
      WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (finSub ++ is)) { s with xmm := f } Q := by
  refine wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (k _ ?_ ?_)))))
  · simp only [csubT]
    rw [← h4, ← h7]
    rfl
  · intro r h0 h1
    simp only [h0, h1, ite_false]

theorem finCore_ok : PassOk finCore VF finV := by
  intro s f x is Q _ hc k
  rw [show finCore ++ is = finFold ++ (finSub ++ is) by simp only [finCore, List.append_assoc]]
  refine finFold_wp hc fun g₁ v₁ r₁ => finSub_wp ((r₁ _ (by decide) (by decide) (by decide)).trans hc.ones)
    ((r₁ _ (by decide) (by decide) (by decide)).trans hc.q) fun g₂ v₂ r₂ => k g₂ ?_ ?_
  · rw [v₂, v₁]; rfl
  · exact ⟨(r₂ _ (by decide) (by decide)).trans ((r₁ _ (by decide) (by decide) (by decide)).trans hc.q),
      (r₂ _ (by decide) (by decide)).trans ((r₁ _ (by decide) (by decide) (by decide)).trans hc.ones),
      (r₂ _ (by decide) (by decide)).trans ((r₁ _ (by decide) (by decide) (by decide)).trans hc.m23),
      (r₂ _ (by decide) (by decide)).trans ((r₁ _ (by decide) (by decide) (by decide)).trans hc.nq1)⟩

theorem finInit_wp {s₀ : State} (hp : NttLoop.Pre s₀) {T : List Nat} {c3 : BitVec 32} {G : Poly} {zp : Nat}
    {s : State} (h : LS s₀ T (VK c3) 17 G zp s) :
    WP isa (.block (finInit ++ layStart)) s (PInv s₀ T VF 17 G id 0) := by
  obtain ⟨a₀, -⟩ := arg_M0 hp (i := 0) (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at a₀
  have ea : (s.gpr .esp + BitVec.ofNat 32 16).setWidth 64 = argAddr s₀ 0 := by rw [h.base.esp]; exact a₀
  have i₀ : InRegions (s.rd ++ s.wr) (argAddr s₀ 0) 4 := inRd (in_arg hp h.base.wr (by decide))
  have v0 := h.base.arg0
  apply WP.of_runBlock
  simp only [finInit, layStart, vconst, at_, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, XOp.exec, State.setXmm, readSrc, State.ea, State.load32, State.setReg, ea, i₀, v0,
    Option.map_some, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
  exact ⟨h.base.of_gpr (fun r h1 _ _ => by simp only [h1, ite_false]) rfl rfl rfl rfl
    ⟨h.base.vp.q, h.base.vp.ones, bc_eq _, bc_eq _⟩, (BitVec.add_zero _).symm,
    fun i hi => absurd hi (by omega_using []), fun i hi _ => h.co i hi⟩

end VG.Proof.MlDsa.X86.Arith.Vec

/-! ## `vg_mldsa_ntt` -/

namespace VG.Proof.MlDsa.X86.Arith.NttFwd

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86.Arith VG.Proof.MlDsa.X86.Arith.Vec
open VG.Spec.MlDsa VG.Proof.MlDsa
open VG.Proof.MlKem.X86 (Piece satState)

theorem tab : NttLoop.TabOK montZetaTable zetas := fun _ hk => montZeta_eq hk

section
variable (s₀ : State)
/-- The polynomial after the layers with `len` = 128, …, 1. -/
abbrev L1 : Poly := nttLayer (F s₀) 128
abbrev L2 : Poly := nttLayer (L1 s₀) 64
abbrev L3 : Poly := nttLayer (L2 s₀) 32
abbrev L4 : Poly := nttLayer (L3 s₀) 16
abbrev L5 : Poly := nttLayer (L4 s₀) 8
abbrev L6 : Poly := nttLayer (L5 s₀) 4
abbrev L7 : Poly := nttLayer (L6 s₀) 2
abbrev L8 : Poly := nttLayer (L7 s₀) 1
end

theorem fold_eq (s₀ : State) : nttLens.foldl nttLayer (F s₀) = L8 s₀ := by
  simp only [nttLens, List.foldl_cons, List.foldl_nil]

theorem body_piece : Piece NttLoop.Pre NttLoop.Pub (fun s₀ s => s = M0 s₀)
    (fun s₀ s => PInv s₀ montZetaTable VF 17 (L8 s₀) id 64 s)
    (.seq (nttInit montZetaTable fwdC)
      (.seq (layer4 fBody 128) (.seq (layer4 fBody 64) (.seq (layer4 fBody 32) (.seq (layer4 fBody 16)
        (.seq (layer4 fBody 8) (.seq (layer4 fBody 4) (.seq (layerFlat zl2 fBody2 8)
          (.seq (layerFlat zl1 fBody1 16) (pass finInit finCore)))))))))) := by
  refine Piece.seq (B := fun s₀ s => LS s₀ montZetaTable (VK fwdC1) 1 (F s₀) 1 s)
    (Vec.init_piece montZetaTable fwdC1 (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay4_piece fBody_ok (fwd_new sh4 sh4_ok (by decide)) tab 32 1 1 (by decide) (by decide) F L1
    (fun s₀ => fwd_lay _ (by decide) (by decide)) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide)) ?_
  refine Piece.seq (lay4_piece fBody_ok (fwd_new sh4 sh4_ok (by decide)) tab 16 2 2 (by decide) (by decide) L1 L2
    (fun s₀ => fwd_lay _ (by decide) (by decide)) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide)) ?_
  refine Piece.seq (lay4_piece fBody_ok (fwd_new sh4 sh4_ok (by decide)) tab 8 4 4 (by decide) (by decide) L2 L3
    (fun s₀ => fwd_lay _ (by decide) (by decide)) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide)) ?_
  refine Piece.seq (lay4_piece fBody_ok (fwd_new sh4 sh4_ok (by decide)) tab 4 8 8 (by decide) (by decide) L3 L4
    (fun s₀ => fwd_lay _ (by decide) (by decide)) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide)) ?_
  refine Piece.seq (lay4_piece fBody_ok (fwd_new sh4 sh4_ok (by decide)) tab 2 16 16 (by decide) (by decide) L4 L5
    (fun s₀ => fwd_lay _ (by decide) (by decide)) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide)) ?_
  refine Piece.seq (lay4_piece fBody_ok (fwd_new sh4 sh4_ok (by decide)) tab 1 32 32 (by decide) (by decide) L5 L6
    (fun s₀ => fwd_lay _ (by decide) (by decide)) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide)) ?_
  refine Piece.seq (layFlat_piece flat2 (by decide) zl2_ok fBody2_ok (fwd_new sh2 sh2_ok (by decide)) tab 64
    (by decide) L6 L7 (fun s₀ => fwd_lay _ (by decide) (by decide)) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (layFlat_piece flat1 (by decide) zl1_ok fBody1_ok (fwd_new sh1 sh1_ok (by decide)) tab 128
    (by decide) L7 L8 (fun s₀ => fwd_lay _ (by decide) (by decide)) (by taint_decide) (by taint_decide)) ?_
  exact pass_piece finCore_ok fin_lanes L8 256 (fun _ _ hp h => finInit_wp hp h) (by taint_decide) (by taint_decide)

theorem piece : Piece NttLoop.Pre NttLoop.Pub (fun s₀ s => s = s₀)
    (fun s₀ s' => McdtPost (PInv s₀ montZetaTable VF 17 (L8 s₀) id 64) s₀ s') Impl.MlDsa.X86.Arith.ntt :=
  Piece.mcdt (fun s₀ => [polyRegion (fA s₀), polyRegion (sA s₀), aR2 s₀]) (NoSp.of_all (by lit_decide))
    (fun _ hp => sp12 hp)
    (fun _ hp r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨mcdt_disj hp hp.stk_f, hp.ret_f⟩
      · exact ⟨mcdt_disj hp hp.stk_s, hp.ret_s⟩
      · exact ⟨mcdt_disj hp hp.stk_a, hp.ret_a⟩)
    (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h =>
      ⟨⟨h.base.frame, h.base.esp, h.base.rd, h.base.wr, h.base.mcdt, h.base.saved⟩, h⟩)

theorem satZero (a : Addr) (ha : a.toNat < 0x5000) : NttLoop.satMem a = 0 := by
  simp only [NttLoop.satMem]
  rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_using [ha])]

theorem verified : Verified X86.target Impl.MlDsa.X86.Arith.ntt (nttContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => NttLoop.Pre.of (t := VG.Spec.MlDsa.ntt) h rfl)
    fun s s' _ _ h => by
      sig_pub [nttContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [nttContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    have hp := NttLoop.Pre.of (t := VG.Spec.MlDsa.ntt) h₀ rfl
    refine Proof.MlDsa.Arith.polyIs_frame hm (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (mcdt_disj hp hp.stk_f).symm) ?_
    refine polyIs_of_toNat fun i hi => ?_
    rw [ntt_eq_layers]
    show _ = ((nttLens.foldl nttLayer (F s₀))[i]!).val
    rw [fold_eq]
    exact hinv.done i hi
  · let st := satState NttLoop.satMem [] [⟨0, 1024⟩, ⟨0x400, 1024⟩, ⟨0x5004, 8⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 0x400 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [nttContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, e]
    trace_state
    sorry

end VG.Proof.MlDsa.X86.Arith.NttFwd
