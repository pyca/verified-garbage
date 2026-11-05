module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordShadowRun
public import VerifiedGarbage.Proof.Rsa.X86_64.KeyCtx

/-! # The validation context after a word reduction in extra scratch space -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The adapter leaves all original header words untouched. -/
theorem wordFrame_hdr {m m' : Mem} {B : Addr} {w i : Nat}
    (hf : Frm B (VG.Proof.Rsa.X86_64.WordValidation.ranges w) m m') (hi : i < 32) :
    word m' B (8 * i) = word m B (8 * i) := by
  apply hf.word_eq _ (by omega_using [hi])
  intro r hr
  simp only [VG.Proof.Rsa.X86_64.WordValidation.ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;>
    simp only [VG.Proof.Rsa.X86_64.WordValidation.start, slot, hdrBytes, CheckKey.aR] <;> omega_using [hi]

/-- Original header, public modulus and constant one survive the second workspace. -/
theorem KCtx.wordFrame {s t t' : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (h : KCtx s t B Z w minv N)
    (hz : VG.Proof.Rsa.X86_64.WordValidation.start w + VG.Proof.Rsa.X86_64.WordValidation.span w ≤ Z)
    (hf : Frm B (VG.Proof.Rsa.X86_64.WordValidation.ranges w) t.mem t'.mem) (hk : Keep mmRegs t t') :
    KCtx s t' B Z w minv N := by
  have hn := h.good.scr.nowrap
  have hb : ∀ r ∈ VG.Proof.Rsa.X86_64.WordValidation.ranges w, r.1 + r.2 ≤ Z := by
    intro r hr
    simp only [VG.Proof.Rsa.X86_64.WordValidation.ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [VG.Proof.Rsa.X86_64.WordValidation.start, slot, hdrBytes, CheckKey.aR] at hz ⊢
      omega_using [hz]
    · exact hz
  have hh := fun i hi => wordFrame_hdr hf (i := i) hi
  refine ⟨⟨h.good.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.good.rdi,
    ⟨(hh sW (by decide)).trans h.good.hdr.hw, (hh sMinv (by decide)).trans h.good.hdr.hminv,
      fun j hj => (hh (sArr j) (by unfold sArr; omega_using [hj])).trans (h.good.hdr.harr j hj)⟩⟩,
    h.hZ, h.w1, h.w2, fun i hi he => (hh i hi).trans (h.hdr i hi he), h.ins.trans (InScr.of_frm hf hb),
    hk.2.1.trans h.rd, hk.2.2.trans h.wr, ?_, ?_, (h.keep.trans hk).mono (by decide)⟩
  · rw [hf.wv_eq (by
      intro r hr
      simp only [VG.Proof.Rsa.X86_64.WordValidation.ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        simp only [VG.Proof.Rsa.X86_64.WordValidation.start, slot, hdrBytes, CheckKey.aR, aN] <;> omega_arith)
      (by have := h.hZ; simp only [slot, aN] at this ⊢; omega_using [this, hn]), h.n]
  · rw [hf.wv_eq (by
      intro r hr
      simp only [VG.Proof.Rsa.X86_64.WordValidation.ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        simp only [VG.Proof.Rsa.X86_64.WordValidation.start, slot, hdrBytes, CheckKey.aR, aOne] <;> omega_arith)
      (by have := h.hZ; simp only [slot, aOne] at this ⊢; omega_using [this, hn]), h.one]

end VG.Proof.Rsa.X86_64.Key
