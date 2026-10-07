import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRawCrossCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRaw

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout pins_good)

theorem rawCross_fw {a : Nat} (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    (L : Layout) (s : State) (h : AdxTiledProduct.GoodL L s) :
    WP isa (AdxTiledSquare.rawCross a) s (AdxTiledProduct.GoodL L) := by
  obtain ⟨mi,hg⟩ := h
  exact WP.mono (rawCross_ok hg.scr hg.rdi hg.hdr L.hZ L.hw L.hwN L.hn ha ha1 ha2)
    fun _ ⟨_,_,o,k⟩ => ⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,
      hg.hdr.of_outside o (by unfold slot; omega)⟩

def Ready (a : Nat) (L : Layout) (s : State) : Prop :=
  AdxTiledProduct.GoodL L s ∧ s.gpr .r8=off L.B (slot L.w aAcc+16) ∧
    s.gpr .r9=off L.B (slot L.w a) ∧ s.gpr .rbx=BitVec.ofNat 64 L.w

theorem setup_ready {a : Nat} (ha : a<8) (L : Layout) (s : State) (h : AdxTiledProduct.GoodL L s) :
    WP isa (.block (Adx.setup a)) s (Ready a L) := by
  obtain ⟨mi,hg⟩ := h
  exact WP.mono (adxSetup_ok hg.scr hg.rdi hg.hdr L.hZ ha) fun _ ⟨p9,_,p8,pbx,m,k⟩ =>
    ⟨⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,m ▸ hg.hdr⟩,p8,p9,pbx⟩

theorem raw_ct {a : Nat} (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup a)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a a)) h₂).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup a)) h₃).isSome=true) :
    RelCT isa (Two AdxTiledProduct.GoodL) (AdxTiledSquare.rawSquare a) (fun _ _ => True) := by
  unfold AdxTiledSquare.rawSquare
  refine RelCT.seq (two_post (rawCross_ct ha ha1 ha2 hS hR hT) (rawCross_fw ha ha1 ha2)) ?_
  refine RelCT.seq (two_piece [.rdi] AdxTiledProduct.pins_good hS (setup_ready ha)) ?_
  refine two_taint [.rdi,.r8,.r9,.rbx] ?_ (by taint_decide)
  intro L s t hs ht r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact AdxTiledProduct.pins_good L s t hs.1 ht.1 .rdi (by simp)
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.2.2.1.trans ht.2.2.1.symm
  · exact hs.2.2.2.trans ht.2.2.2.symm

theorem raw_fw {a : Nat} (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    (L : Layout) (s : State) (h : AdxTiledProduct.GoodL L s) :
    WP isa (AdxTiledSquare.rawSquare a) s (AdxTiledProduct.GoodL L) := by
  obtain ⟨mi,hg⟩ := h
  exact WP.mono (rawSquare_ok hg.scr hg.rdi hg.hdr L.hZ L.hwN L.hn L.hw ha ha1 ha2)
    fun _ ⟨_,_,o,k⟩ => ⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,
      hg.hdr.of_outside o (by unfold slot; omega)⟩

end VG.Proof.Bignum.X86_64.AdxTiledSquare
