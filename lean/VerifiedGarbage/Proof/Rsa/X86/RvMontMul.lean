module

public import VerifiedGarbage.Proof.Rsa.X86.RvMontFrame

/-! # Montgomery products return full key-array values -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem mmul_ok {g : Geo} {m : Nat} {s : State} (h : MR g m s) {o a b : Nat}
    (ho : MontIndex o) (ha : MontIndex a) (hb : MontIndex b) (ho0 : o ≠ mBase)
    (hA : num s.mem g.B g.w a < 2 ^ (64 * g.n)) (hB : num s.mem g.B g.w b < m) :
    WP isa (mmul g.n o a b) s fun t => MR g m t ∧
      Keep g.B g.w (montWrites o) [] s.mem t.mem ∧ Keeps opRegs s t ∧
      num t.mem g.B g.w o < m ∧
      num t.mem g.B g.w o * 2 ^ (64 * g.n) % m =
        num s.mem g.B g.w a * num s.mem g.B g.w b % m := by
  have head := h.ws.hdr_le
  have invFit : sInv + 4 ≤ g.Z := by unfold sInv hdr at *; omega
  have accLow : hdr ≤ arr g.w mAcc := Nat.le_add_right _ _
  have invSep : sInv + 4 ≤ arr g.w mAcc := by unfold sInv hdr at *; omega
  have tmpLow : hdr ≤ arr g.w mTmp := Nat.le_add_right _ _
  have invTmp : sInv + 4 ≤ arr g.w mTmp := by unfold sInv hdr at *; omega
  have sepA := mont_bytes_sep (g := g) ha.2.2
  have sepB := mont_bytes_sep (g := g) hb.2.2
  have eqA := words_eq_num hA
  have eqB := words_eq_num (Nat.lt_trans hB h.bound)
  unfold mmul
  refine WP.seq (WP.mono (VG.Proof.Mont.X86.Dynamic.mul_ok h.ws.workspace h.modulusReady
    invFit (.inl invSep) h.inverse (mont_layout h.ws ho ha hb)
    (by change wordsVal s.mem g.B (arr g.w b) g.n < m; rw [eqB]; exact hB)
    (by change arr g.w a + 8 * g.n ≤ arr g.w mTmp ∨ arr g.w mTmp + 4 ≤ arr g.w a
        have := h.positive; omega)
    (by change arr g.w b + 8 * g.n ≤ arr g.w mTmp ∨ arr g.w mTmp + 4 ≤ arr g.w b
        have := h.positive; omega)
    (.inl invTmp)) fun u ⟨ku, lt, value⟩ => ?_)
  have frame := mont_keep ku
  have rest := mont_rest ku
  have hu := h.keep frame (by simpa [montWrites, mTmp, mAcc, mBase] using ho0) rest
  refine WP.mono (clrTop_ok hu.ws ho.2.1) fun t ⟨_, kt, vt, rt⟩ => ?_
  refine ⟨hu.keep kt (by simpa using ho0) (rt.mono (by decide)),
    frame.trans (kt.mono (by simp [montWrites]) (by simp)), rest.trans (rt.mono (by decide)), ?_, ?_⟩
  · rw [vt]; exact lt
  · change wordsVal u.mem g.B (arr g.w o) g.n * 2 ^ (64 * g.n) % m =
        wordsVal s.mem g.B (arr g.w a) g.n * wordsVal s.mem g.B (arr g.w b) g.n % m at value
    rw [vt, value, eqA, eqB]

end VG.Proof.Rsa.X86.Recover
