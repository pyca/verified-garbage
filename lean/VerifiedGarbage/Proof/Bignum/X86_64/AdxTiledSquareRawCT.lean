import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRawCrossCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRaw

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout GoodV pins_goodV)

theorem rawCross_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp) (L : Layout) (s : State) (h : GoodV ps L s) :
    WP isa (AdxTiledSquare.rawCross ca) s (GoodV ps L) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  exact WP.mono (rawCross_ok hg.scr hg.rdi hg.hdr hv pa L.hZ L.hw L.hwN L.hn ha ha1 ha2)
    fun _ ⟨_,_,o,k⟩ => AdxTiledProduct.GoodV.of_outside ⟨⟨mi,hg⟩,hv⟩ o k

def Ready (ps : List (Nat × Nat)) (a : Nat) (L : Layout) (s : State) : Prop :=
  GoodV ps L s ∧ s.gpr .r8=off L.B (slot L.w aAcc+16) ∧
    s.gpr .r9=off L.B (slot L.w a) ∧ s.gpr .rbx=BitVec.ofNat 64 L.w

theorem setup_ready {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (L : Layout) (s : State)
    (h : GoodV ps L s) : WP isa (.block (Adx.setup ca)) s (Ready ps a L) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  exact WP.mono (adxSetupV_ok hg.scr hg.rdi hg.hdr L.hZ (hv.at pa) (hv.lt pa)) fun _ ⟨p9,_,p8,pbx,m,k⟩ =>
    ⟨⟨⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,m ▸ hg.hdr⟩,m ▸ hv⟩,p8,p9,pbx⟩

theorem raw_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp)
    {h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup ca)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) h₂).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) h₃).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledSquare.rawSquare ca) (fun _ _ => True) := by
  unfold AdxTiledSquare.rawSquare
  refine RelCT.seq (two_post (rawCross_ct pa ha ha1 ha2 hS hR hT) (rawCross_fw pa ha ha1 ha2)) ?_
  refine RelCT.seq (two_piece [.rdi] (pins_goodV ps) hS (setup_ready pa)) ?_
  refine two_taint [.rdi,.r8,.r9,.rbx] ?_ (by taint_decide)
  intro L s t hs ht r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact pins_goodV ps L s t hs.1 ht.1 .rdi (by simp)
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.2.2.1.trans ht.2.2.1.symm
  · exact hs.2.2.2.trans ht.2.2.2.symm

theorem raw_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp) (L : Layout) (s : State) (h : GoodV ps L s) :
    WP isa (AdxTiledSquare.rawSquare ca) s (GoodV ps L) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  exact WP.mono (rawSquare_ok hg.scr hg.rdi hg.hdr L.hZ L.hwN L.hn L.hw hv pa ha ha1 ha2)
    fun _ ⟨_,_,o,k⟩ => AdxTiledProduct.GoodV.of_outside ⟨⟨mi,hg⟩,hv⟩ o k

end VG.Proof.Bignum.X86_64.AdxTiledSquare
