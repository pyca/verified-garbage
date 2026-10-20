module

import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowS
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowS
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# A square's row in constant time

`rowS_ct`: as `row_ct`, for `AdxRect8.rowS`: its blocks but the last, the
handed carry, the last block. Whether the row has one block, and when the
loop stops, are the public layout's; the handed carry is only added.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset handOffset)
open VG.Proof.MlKem.X86_64 (Keep)

/-- The handed carry's slot is outside what a row writes. -/
theorem hand_frame {m m' : Mem} {B : Addr} {w : Nat} (hf : Frm B (rowRanges w) m m') :
    word m' B handOffset = word m B handOffset := by
  refine hf.word_eq ?_ (by unfold handOffset sFn; omega)
  intro r hr
  simp only [rowRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Or.inl (by unfold rawBase handOffset sFn slot hdrBytes aAcc; omega)
  · exact Or.inr (by unfold carryOffset handOffset sFn; omega)
  · exact Or.inr (by unfold handOffset sFn; omega)

/-- At column block `k` of a square's row, before the handed carry is added:
the pending carry and the handed carry at most 2. -/
def LoopStateH (ps : List (Nat × Nat)) (a b : Nat) (L : RowLayout) (k : Nat) (s : State) : Prop :=
  ∃ s₀ mi x cb, Ops s₀.mem L.B L.w ps ∧ cb ≤ 2 ∧ (word s₀.mem L.B handOffset).toNat ≤ 2 ∧
    StreamInv s₀ L.B L.Z L.w a b L.i L.j₀ k mi x cb s

theorem LoopStateH.loop {ps : List (Nat × Nat)} {a b : Nat} {L : RowLayout} {k : Nat} {s : State}
    (h : LoopStateH ps a b L k s) : LoopState ps a b L k s := by
  obtain ⟨s₀,mi,x,cb,hv,_,_,h⟩ := h
  exact ⟨s₀,mi,x,cb,hv,h⟩

theorem pinsH (ps : List (Nat × Nat)) (a b : Nat) (k : RowLayout → Nat) :
    Pins (fun L s => LoopStateH ps a b L (k L) s) [.rdi,.rcx,.rbp,.rsi] := by
  rintro L s t ⟨_,_,_,_,_,_,_,hs⟩ ⟨_,_,_,_,_,_,_,ht⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hs.rdi.trans ht.rdi.symm
  · exact hs.pa.trans ht.pa.symm
  · exact hs.pb.trans ht.pb.symm
  · exact hs.po.trans ht.po.symm

theorem setupH_fw {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (L : RowLayout) (s : State)
    (h : (RowState ps L 0 s ∧ word s.mem L.B carryOffset = 0) ∧ (word s.mem L.B handOffset).toNat ≤ 2) :
    WP isa (.block (AdxRect8.setup ca cb)) s
      (fun t => RowBases ps a b L t ∧ (word t.mem L.B handOffset).toNat ≤ 2) := by
  obtain ⟨⟨⟨mi,hg,hv,hI,hJ⟩,hc⟩,hh⟩ := h
  simp only [Nat.mul_zero,Nat.add_zero] at hJ
  refine WP.mono (setup_ok hg.scr hg.rdi hg.hdr L.hZ hv pa pb hI hJ) fun t ⟨ca,cb,co,mt,kt⟩ => ?_
  exact ⟨⟨⟨mi,hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,mt ▸ hv,mt ▸ hI,mt ▸ hJ,
    mt ▸ hc,ca,cb,co⟩,mt ▸ hh⟩

theorem loadH_fw {ps : List (Nat × Nat)} {a b : Nat} (L : RowLayout) (s : State)
    (h : RowBases ps a b L s ∧ (word s.mem L.B handOffset).toNat ≤ 2) :
    WP isa (.block AdxRotate8.loadCols) s (LoopStateH ps a b L 0) := by
  obtain ⟨⟨⟨mi,hg⟩,hv,hI,hJ,hc,ca,cb,co⟩,hh⟩ := h
  have hwN := L.hwN; have hn := L.hn
  exact WP.mono (rowLoad_ok (s₀ := s) hg.scr hg.rdi hg.hdr L.hZ L.hi (by omega) hI hJ (by rw [hc]; rfl)
    ca cb co rfl (Keep.refl _ _)) fun t ht => ⟨s,mi,0,2,hv,Nat.le_refl _,hh,ht⟩

theorem one_fw {ps : List (Nat × Nat)} {a b : Nat} (L : RowLayout) (s : State) (h : LoopStateH ps a b L 0 s) :
    WP isa (.block AdxRect8.oneTest) s
      (fun t => LoopStateH ps a b L 0 t ∧ isa.eval .e t = some (decide (L.n = 1))) := by
  obtain ⟨s₀,mi,x,cb,hv,hcb,hh,h⟩ := h
  have hwN := L.hwN; have hw := L.hw; have hn := L.hn
  refine WP.mono (oneTest_ok (j := L.j₀) h.scr h.rdi h.hdr L.hZ (by omega) (by omega)
    (by simpa only [Nat.mul_zero,Nat.add_zero] using h.indexJ)) fun t ⟨mt,zt,kt⟩ =>
      ⟨⟨s₀,mi,x,cb,hv,hcb,hh,h.of_keep mt kt⟩,?_⟩
  simp only [eval,zt]
  exact congrArg some (decide_eq_decide.mpr (by omega))

theorem rowS_body_ct {ps : List (Nat × Nat)} {a b : Nat}
    (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) :
    RelCT isa (Two fun (p : RowLayout × Nat) s => p.2 < p.1.n - 1 ∧ LoopStateH ps a b p.1 p.2 s)
      AdxRect8.rowStepS (fun _ _ => True) := by
  unfold AdxRect8.rowStepS
  refine two_map (Φ' := AtLoop ps a b) id (fun p s h => ⟨by dsimp only [id]; omega, h.2.loop⟩) ?_
  refine RelCT.seq (two_piece [.rdi,.rcx,.rbp,.rsi] (loop_pins ps a b) (by taint_decide)
      (tile_fw ha hb ha1 ha2 hb1 hb2)) (two_taint [.rdi] ?_ (by taint_decide))
  intro p s t hs ht r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.trans ht.symm

theorem rowS_fw {ps : List (Nat × Nat)} {a b : Nat}
    (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (L : RowLayout) (k : Nat) (s : State) (hk : k < L.n - 1) (h : LoopStateH ps a b L k s) :
    WP isa AdxRect8.rowStepS s fun t =>
      isa.eval .ne t = some (decide (k+1 < L.n - 1)) ∧
      (k+1 < L.n - 1 → LoopStateH ps a b L (k+1) t) ∧ (k+1 = L.n - 1 → LoopStateH ps a b L (L.n - 1) t) := by
  obtain ⟨s₀,mi,x,cb,hv,hcb,hh,h⟩ := h
  have hwN := L.hwN; have hw := L.hw
  unfold AdxRect8.rowStepS
  refine WP.mono (streamStep_gen L.hZ L.hw L.hi ha hb ha1 ha2 hb1 hb2 L.hwN (by omega)
    (fun u hs hd hh' hj => nextColumnS_ok hs hd hh' L.hZ (by omega) (by omega) hj) h) fun t ⟨zt,ht⟩ => ?_
  have post : LoopStateH ps a b L (k+1) t := ⟨s₀,mi,x,2,hv,Nat.le_refl _,hh,ht⟩
  refine ⟨?_,fun _ => post,fun he => he ▸ post⟩
  simp only [eval,zt,Option.map_some]
  by_cases he : k+1 = L.n - 1
  · simp only [show L.j₀+8*k+16 = L.w by omega,decide_true,Bool.not_true,
      show ¬(k+1 < L.n - 1) by omega,decide_false]
  · simp only [show ¬(L.j₀+8*k+16 = L.w) by omega,decide_false,Bool.not_false,
      show k+1 < L.n - 1 by omega,decide_true]

theorem hand_fw {ps : List (Nat × Nat)} {a b : Nat} (L : RowLayout) (s : State)
    (h : LoopStateH ps a b L (L.n - 1) s) :
    WP isa (.block AdxRect8.addHand) s (LoopState ps a b L (L.n - 1)) := by
  obtain ⟨s₀,mi,x,cb,hv,hcb,hh,h⟩ := h
  have hwN := L.hwN; have hn := L.hn; have hi := L.hi
  refine WP.mono (addHand_inv L.hZ (by omega) hcb h rfl (by rw [hand_frame h.frame]; exact hh))
    fun t ht => ⟨s₀,mi,_,4,hv,ht⟩

theorem rowS_ct {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca cb)) hint).isSome = true) :
    RelCT isa (Two fun L s => (RowState ps L 0 s ∧ word s.mem L.B carryOffset = 0) ∧
        (word s.mem L.B handOffset).toNat ≤ 2) (AdxRect8.rowS ca cb)
      (Two fun L s => RowState ps L L.n s) := by
  unfold AdxRect8.rowS
  refine RelCT.seq (two_piece [.rdi] ?_ hS (setupH_fw pa pb)) ?_
  · rintro L s t ⟨⟨⟨mi,hs,_⟩,_⟩,_⟩ ⟨⟨⟨mj,ht,_⟩,_⟩,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  refine RelCT.seq (two_piece [.rsi] ?_ (by taint_decide) loadH_fw) ?_
  · rintro L s t ⟨⟨_,_,_,_,_,_,_,hs⟩,_⟩ ⟨⟨_,_,_,_,_,_,_,ht⟩,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.trans ht.symm
  -- the blocks but the last
  refine RelCT.seq (R := Two (fun L s => LoopStateH ps a b L (L.n - 1) s))
    (RelCT.seq (two_piece [.rdi,.rcx,.rbp,.rsi] (pinsH ps a b fun _ => 0) (by taint_decide) one_fw)
      (two_ite (fun L s₁ s₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_)) ?_
  · refine two_post (two_taint [] (fun _ _ _ _ _ r hr => by simp at hr) (by taint_decide)) ?_
    intro L s ⟨⟨h,he⟩,hz⟩
    rw [he] at hz
    have h1 : L.n = 1 := by simpa using hz
    exact WP.block_nil (by rw [h1]; exact h)
  · refine (two_loop (fun L : RowLayout => L.n - 1) (Φ := LoopStateH ps a b)
      (Ψ := fun L s => LoopStateH ps a b L (L.n - 1) s)
      (rowS_body_ct ha hb ha1 ha2 hb1 hb2) (rowS_fw ha hb ha1 ha2 hb1 hb2)).mono ?_ (fun _ _ h => h)
    rintro s t ⟨L,⟨⟨hs,es⟩,zs⟩,⟨⟨ht,_⟩,_⟩⟩
    rw [es] at zs
    have h1 : L.n ≠ 1 := by simpa using zs
    have hn := L.hn
    exact ⟨L,⟨by omega,hs⟩,by omega,ht⟩
  -- the handed carry, the last block, the columns stored
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) hand_fw) ?_
  · rintro L s t ⟨_,_,_,_,_,_,_,hs⟩ ⟨_,_,_,_,_,_,_,ht⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  refine RelCT.seq (two_post (two_map (fun L : RowLayout => (L, L.n - 1))
      (fun L s h => ⟨by dsimp only; have := L.hn; omega,h⟩) (row_body_ct ha hb ha1 ha2 hb1 hb2))
    (Ψ := fun L s => LoopState ps a b L L.n s) fun L s h => WP.mono
      (row_fw ha hb ha1 ha2 hb1 hb2 L (L.n - 1) s (by have := L.hn; omega) h)
      fun t ⟨_,_,h3⟩ => by have := L.hn; rw [show L.n - 1 + 1 = L.n by omega] at h3; exact h3 rfl) ?_
  refine two_post (two_taint [.rsi] ?_ (by taint_decide)) end_fw
  rintro L s t ⟨_,_,_,_,_,hs⟩ ⟨_,_,_,_,_,ht⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.po.trans ht.po.symm

end VG.Proof.Bignum.X86_64.AdxRect8
