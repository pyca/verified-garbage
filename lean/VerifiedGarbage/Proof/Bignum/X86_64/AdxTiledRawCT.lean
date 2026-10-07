import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRowsCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRaw

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

def Ready (L : Layout) (s : State) : Prop :=
  GoodL L s ∧ s.gpr .r8=off L.B (slot L.w aAcc+16) ∧ s.gpr .rbx=BitVec.ofNat 64 L.w

theorem pins_good : Pins GoodL [.rdi] := by
  rintro L s t ⟨mi,hs⟩ ⟨mj,ht⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.rdi.trans ht.rdi.symm

theorem setup_fw {b : Nat} (hb : b<8) (L : Layout) (s : State) (h : GoodL L s) :
    WP isa (.block (Adx.setup b)) s (Ready L) := by
  obtain ⟨mi,hg⟩ := h
  exact WP.mono (adxSetup_ok hg.scr hg.rdi hg.hdr L.hZ hb) fun _ ⟨_,_,p,w,m,k⟩ =>
    ⟨⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,m ▸ hg.hdr⟩,p,w⟩

theorem zero_fw (L : Layout) (s : State) (h : Ready L s) : WP isa Adx.zeroWin s (GoodL L) := by
  obtain ⟨⟨mi,hg⟩,p,w⟩ := h
  have pads := AdxHeader.pads_bound L.hZ
  have hw := L.hw
  refine WP.mono (zeroWin_ok hg.scr p w (by omega)
    (by unfold AdxHeader.highPad at pads; omega)) fun t ⟨_,o,k⟩ => ?_
  exact ⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,hg.hdr.of_outside o (by unfold slot; omega)⟩

theorem save_fw (L : Layout) (s : State) (h : GoodL L s) : WP isa AdxHeader.save s (GoodL L) := by
  obtain ⟨mi,hg⟩ := h
  refine WP.mono (AdxHeader.save_ok hg.scr hg.rdi hg.hdr L.hZ) fun t ⟨_,_,f,k⟩ => ?_
  have o : Outside L.B (slot L.w aAcc) (16*L.w+32) s.mem t.mem := by
    intro x hx
    apply f x
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp only [] <;> unfold AdxHeader.highPad at * <;> omega
  exact ⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,hg.hdr.of_outside o (by unfold slot; omega)⟩

theorem raw_ct {a b : Nat} (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {h₁ h₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup b)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a b)) h₂).isSome=true) :
    RelCT isa (Two GoodL) (AdxTiledProduct.rawProduct a b) (fun _ _ => True) := by
  unfold AdxTiledProduct.rawProduct
  refine RelCT.seq (two_piece [.rdi] pins_good hS (setup_fw hb)) ?_
  refine RelCT.seq (two_piece [.r8,.rbx] ?_ (by taint_decide) zero_fw) ?_
  · intro L s t hs ht r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.2.1.trans ht.2.1.symm
    · exact hs.2.2.trans ht.2.2.symm
  have mapGood : ∀ L s, GoodL L s → GoodW ⟨L.B,L.Z,L.w⟩ s := by
    rintro L s ⟨mi,hg⟩; exact ⟨mi,hg,L.hZ⟩
  refine RelCT.seq (two_post (two_map (fun L : Layout => (⟨L.B,L.Z,L.w⟩ : Ws)) mapGood AdxHeader.save_ct) save_fw) ?_
  exact RelCT.seq (rows_ct ha hb ha1 ha2 hb1 hb2 hR)
    (two_map (fun L : Layout => (⟨L.B,L.Z,L.w⟩ : Ws)) mapGood AdxHeader.restore_ct)

end VG.Proof.Bignum.X86_64.AdxTiledProduct
