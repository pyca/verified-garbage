module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# RSA with the CRT on x86-64: the selection with AVX2 is constant time

As `tabSel_ct` for `Crt.tabSelect`: the window flows only into the masks,
and a pass's addresses and counts come from its head, whose registers
(`GathBV`) the correctness of the head (`gathHeadV_ok`) pins in both runs.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- After `j` passes of the selection with AVX2, in the workspace of `p`. -/
def GathPassIV (p : XPub) (j : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (X Xc v : Nat), GathPassInv t₀ (off p.B p.o) p.wx minv X Xc v 32 j s ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ v < 32

/-- After the head of pass `q.2` with AVX2: its bases, counts and the
workspace, whatever the window. -/
def GathBV (q : XPub × Nat) (s : State) : Prop :=
  ∃ v, GRegsV (off q.1.B q.1.o) q.1.wx q.2 v s ∧ s.gpr .r14 = BitVec.ofNat 64 0 ∧
    s.gpr .r11 = BitVec.ofNat 64 (8 * (q.1.wx + 2)) ∧ s.gpr .r15 = BitVec.ofNat 64 (8 * q.2) ∧
    s.gpr .rdi = off q.1.B q.1.o

theorem pins_GathBV :
    Pins GathBV [.rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .rax, .rbx, .r12, .r13, .r14, .r11, .r15, .rdi] := by
  intro q s₁ s₂ ⟨_, g₁, a₁, b₁, c₁, d₁⟩ ⟨_, g₂, a₂, b₂, c₂, d₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (g₁.base 0 (by decide)).trans (g₂.base 0 (by decide)).symm
  · exact (g₁.base 1 (by decide)).trans (g₂.base 1 (by decide)).symm
  · exact (g₁.base 2 (by decide)).trans (g₂.base 2 (by decide)).symm
  · exact (g₁.base 3 (by decide)).trans (g₂.base 3 (by decide)).symm
  · exact (g₁.base 4 (by decide)).trans (g₂.base 4 (by decide)).symm
  · exact (g₁.base 5 (by decide)).trans (g₂.base 5 (by decide)).symm
  · exact (g₁.base 6 (by decide)).trans (g₂.base 6 (by decide)).symm
  · exact (g₁.base 7 (by decide)).trans (g₂.base 7 (by decide)).symm
  · exact g₁.bx.trans g₂.bx.symm
  · exact g₁.r12.trans g₂.r12.symm
  · exact g₁.r13.trans g₂.r13.symm
  · exact a₁.trans a₂.symm
  · exact b₁.trans b₂.symm
  · exact c₁.trans c₂.symm
  · exact d₁.trans d₂.symm

/-- A pass of the selection with AVX2 leaks the same in runs with the same
workspace, whatever the window. -/
theorem passBodyV_ct :
    RelCT isa (Two fun (q : XPub × Nat) s => q.2 < 4 ∧ GathPassIV q.1 q.2 s) (seqs Crt.gatherPassV)
      fun _ _ => True := by
  rw [show seqs Crt.gatherPassV = .seq (seqs Crt.gatherHeadV) (.seq (.block [.alu .test .r12 (.reg .r12)])
      (.seq (.ite .ne (.loop (.block (Crt.gatherBodyV .l256 4 ++ ([.alu .cmp .r14 (.reg .r12)] : List Instr))) .ne)
          (.block []))
        (.seq (.block [.alu .cmp .r14 (.reg .r13)]) (.seq (.ite .ne (.block (Crt.gatherBodyV .l128 2)) (.block []))
          (.block Crt.gatherEndV))))) from rfl]
  refine RelCT.seq (two_piece (Ψ := GathBV) [.rdi] (pins_rdi (fun q => off q.1.B q.1.o)
    fun _ _ ⟨_, _, _, _, _, _, hI, _⟩ => hI.ctx.good.rdi) (by taint_decide)
    fun q s ⟨hp, t₀, minv, X, Xc, v, hI, hw, hw', hv⟩ =>
      WP.mono (gathHeadV_ok hI.ctx hw' hv hp hI.nib hI.idx hI.ent) fun t ⟨hG, h14, h11, h15, _, k⟩ =>
        ⟨v, hG, h14, h11, h15, (k.gpr (by decide)).trans hI.ctx.good.rdi⟩) ?_
  exact two_taint _ pins_GathBV (by taint_decide)

theorem pins_nil {α : Type} (Φ : α → State → Prop) : Pins Φ [] :=
  fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

/-- The selection with AVX2 leaks the same in runs with the same workspace. -/
theorem tabSelV_ct : CrtSel.avx.CT := by
  show RelCT isa (Two (SelP 32)) (seqs Crt.tabSelectV) fun _ _ => True
  rw [tabSelectV_eq]
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < 4 ∧ GathPassIV p 0 s) [.rdi]
    (pins_rdi (fun p : XPub => off p.B p.o) fun _ _ ⟨_, _, _, _, hc, _⟩ => hc.good.rdi) (by taint_decide)
    fun p s ⟨minv, X, Xc, v, hc, hw, hw', hv, ht, hN⟩ => ?_) ?_
  · have hn := hc.scrT.nowrap
    refine WP.mono (selInit_ok hc ht) fun t₁ ⟨hm₁, k₁⟩ => ⟨by decide, t₁, minv, X, Xc, v, ?_, hw, hw', hv⟩
    have o1 := writeW_outside s.mem (off p.B p.o) (d := 8 * Crt.sEnt) (off (off p.B p.o) (slot p.wx 8)) (by decide)
    have o2 := writeW_outside (s.mem.writeW (off (off p.B p.o) (8 * Crt.sEnt)) (off (off p.B p.o) (slot p.wx 8)))
      (off p.B p.o) (d := 8 * Crt.sJ) (BitVec.setWidth 64 (0 : BitVec 32)) (by decide)
    rw [← hm₁] at o2
    have f₁ : Frm (off p.B p.o) (selRanges p.wx) s.mem t₁.mem :=
      (Frm.of_outside o1 (by simp [selRanges])).trans (Frm.of_outside o2 (by simp [selRanges]))
    refine ⟨hc.of_win (f₁.mono (selRanges_sub p.wx)) k₁.2.2 (k₁.gpr (by decide)), ?_, ?_, ?_, .inl rfl,
      Frm.refl _ _ _, Keep.refl _ _⟩
    · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hN
    · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hm₁, word_writeW_self]; rfl
  refine RelCT.seq (R := Two fun (_ : XPub) (_ : State) => True)
    ((two_loop (Φ := GathPassIV) (Ψ := fun _ _ => True) (fun _ => 4) passBodyV_ct
      fun p j s hj ⟨t₀, minv, X, Xc, v, hI, hw, hw', hv⟩ =>
        WP.mono (gPassV_ok hw hw' hv hj hI) fun s' ⟨hz, hI'⟩ =>
          ⟨eval_ne_count hj hz, fun _ => ⟨t₀, minv, X, Xc, v, hI', hw, hw', hv⟩, fun _ => trivial⟩).mono
      (fun _ _ h => h) fun _ _ h => h) ?_
  exact two_taint [] (pins_nil _) (by taint_decide)

end VG.Proof.Bignum.X86_64
