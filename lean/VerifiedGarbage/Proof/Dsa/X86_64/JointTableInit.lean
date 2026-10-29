module

public import VerifiedGarbage.Proof.Dsa.X86_64.JointEntries

/-! # Initializing joint table pointers -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem jointTableInit_ok {t : State} {P : Addr} {w n g y : Nat} {minv : BitVec 64}
    (hc : JointCtx t P w n minv) (h : JointBuildValues t.mem P w n g y 0) :
    WP isa (.block Joint.tableInit) t fun v => JointBuildInv v P w n g y minv 0 v := by
  have hnow := hc.scrT.nowrap
  have hsmall : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega
  unfold Joint.tableInit
  refine WP.mono (tabInit_ok hc.exp) fun v ⟨hm, hk⟩ => ?_
  have o1 := writeW_outside t.mem P (d := 8 * Crt.sTab) (off P (slot w 8)) (by decide)
  have o2 := writeW_outside (t.mem.writeW (off P (8 * Crt.sTab)) (off P (slot w 8))) P
    (d := 8 * Crt.sEnt) (off P (slot w 8)) (by decide)
  rw [← hm] at o2
  have hf : Frm P (crtExpRanges w) t.mem v.mem :=
    (Frm.of_outside o1 (by simp [crtExpRanges])).trans
      (Frm.of_outside o2 (by simp [crtExpRanges, crtWinRanges]))
  have cv := hc.exp.of_frm hf hk.2.2 (hk.gpr (by decide))
  have vals : JointBuildValues v.mem P w n g y 0 := h.congr fun a ha => by
    have hab := slot_le (w := w) ha
    rw [o2.wv (Or.inr (hdr_lt_slot w a (by decide))) (by omega),
      o1.wv (Or.inr (hdr_lt_slot w a (by decide))) (by omega)]
  have h0 : JointBuildInv v P w n g y minv 0 v := by
    refine ⟨⟨⟨cv.good, cv.n, cv.inv⟩, cv.scrT⟩, vals, ?_, ?_, fun k hk => by omega,
      Frm.refl _ _ _, Keep.refl _ _⟩
    · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hm, word_writeW_self]
  exact h0

end VG.Proof.Dsa.X86_64
