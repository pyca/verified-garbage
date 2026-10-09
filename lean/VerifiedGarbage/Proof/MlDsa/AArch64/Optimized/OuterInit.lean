import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterLoop

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt
open VG.Impl.MlKem.AArch64 (mov)

/-- Immutable tail of the expanded table used by the first three layers. -/
structure HoistedMem (s : State) (z : Nat → Int) : Prop where
  range : ∀ i < 8, 0 ≤ z (i+1) ∧ z (i+1) < 8380417
  q : ∀ e < 4, vword (s.v .v16) e = 8380417#32
  read : ∀ i : Fin 4, InRegions (s.rd++s.wr)
    (s.gpr .x1+BitVec.ofNat 64 (3840+16*i.val)) 16
  roots : ∀ g < 4, ∀ e < 4,
    vword (s.mem.read (s.gpr .x1+BitVec.ofNat 64 (3840+16*g)) 16) e =
    if e%2=0 then BitVec.ofInt 32 (z (2*g+e/2+1))
    else BitVec.ofInt 32 (reciprocal (z (2*g+e/2+1)))

theorem hoistedInit_ok {s : State} {rest : List Instr} {Q : State → Prop} {z : Nat → Int}
    (h : HoistedMem s z)
    (k : ∀ t, VChg rootRegs s t → Hoisted t z → WP isa (.block rest) t Q) :
    WP isa (.block (hoistedInit ++ rest)) s Q := by
  let loads : List (VReg × Nat) := [(.v25,3840),(.v26,3856),(.v27,3872),(.v28,3888)]
  have hl : loads.map (fun p => Instr.ldrq p.1 .x1 p.2) = hoistedInit := by rfl
  rw [←hl]
  refine load_many_ok loads .x1 (by decide) (by decide) ?_ fun t hc hv => ?_
  · have hs : ∀ p ∈ loads, ∃ i : Fin 4, p.2=3840+16*i.val := by decide
    intro p hp
    obtain ⟨i,hi⟩ := hs p hp
    simpa only [hi] using h.read i
  · refine k t hc ⟨h.range,?_,?_⟩
    · intro e he
      rw [hc.get .v16 (by decide)]
      exact h.q e he
    · intro g hg e he
      have hm : ∀ i : Fin 4, (rootRegs[i.val]!,3840+16*i.val) ∈ loads := by decide
      rw [hv _ (hm ⟨g,hg⟩)]
      exact h.roots g hg e he

theorem outerSetup_ok (s : State) :
    WP isa (.block [mov .x2 .x0,.movz .x .x5 8 0]) s fun t =>
      ((t.gpr .x2=s.gpr .x0 ∧ t.gpr .x5=8 ∧ t.mem=s.mem) ∧ Keep [.x2,.x5] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [mov]

theorem outerRenamed_ok {s : State} {z : Nat → Int} (h : HoistedMem s z)
    (hr : ∀ u < 8, ∀ i : Fin 8, InRegions (s.rd++s.wr)
      ((s.gpr .x0+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16)
    (hw : ∀ u < 8, ∀ i : Fin 8, InRegions s.wr
      ((s.gpr .x0+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16) :
    WP isa outerRenamed s fun t => Keep [.x2,.x5] s t ∧ Hoisted t z ∧
      t.gpr .x2=s.gpr .x0+128 ∧ t.mem=outerPassMem s.mem (s.gpr .x0) z 8 := by
  rw [outerRenamed_eq]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (outerSetup_ok s) fun s₁ ⟨⟨⟨hp₁,hc₁,hm₁⟩,hk₁⟩,hv₁⟩ => ?_
  have ht₁ : HoistedMem s₁ z := by
    refine ⟨h.range,?_,?_,?_⟩
    · simpa only [hv₁] using h.q
    · simpa only [hk₁.rd,hk₁.wr,hk₁.get .x1] using h.read
    · simpa only [hm₁,hk₁.get .x1] using h.roots
  refine hoistedInit_ok ht₁ (rest := []) fun s₂ hk₂ ht₂ => ?_
  apply WP.block_nil_iff.mpr
  refine WP.mono (outerLoop_ok ht₂ ?_ ?_ ?_) fun t ⟨hk₃,ht₃,hp₃,hm₃⟩ => ?_
  · simpa only [hk₂.gpr] using hc₁
  · simpa only [hk₂.rd,hk₂.wr,hk₂.gpr,hk₁.rd,hk₁.wr,hp₁] using hr
  · simpa only [hk₂.wr,hk₂.gpr,hk₁.wr,hp₁] using hw
  · refine ⟨((hk₁.trans hk₂.keep).trans hk₃).mono,ht₃,?_,?_⟩
    · simpa only [hk₂.gpr,hp₁] using hp₃
    · simpa only [hk₂.mem,hm₁,hk₂.gpr,hp₁] using hm₃

end VG.Proof.MlDsa.AArch64.Optimized
