module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopState
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain
import VerifiedGarbage.Proof.Framework.Omega

/-! Exhaustion terminates the primality loop before reading an incomplete draw. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

theorem loopExhausted_ok {P : PrimeParams} {s₀ s : State}
    {res : Option (Bool × List Byte)} {i uni used : Nat}
    (h : PrimeLoopState P s₀ res i uni used s) (hshort : P.rand.length < used + P.drawBytes) :
    WP isa (.seq (.block [movi .x3 0, sth .x3 kStat])
      (.block [ldh .x3 kStat, .subImm .x .x3 .x3 4])) s fun t =>
        isa.eval (.zero .x .x3) t = some false ∧ PrimeLoopEnd P s₀ res t := by
  have hr := VG.Proof.RsaKeyGen.mrLoop_step P.N P.checks (Spec.Rsa.splitTwos (P.N - 1)).1
    (Spec.Rsa.splitTwos (P.N - 1)).2 P.drawBytes P.rand i uni used h.go P.drawWidth (by have := P.drawMin; omega)
  have hnone : res = none := by
    rw [← h.rest]
    change Spec.RsaKeyGen.loop _ _ _ = _
    rw [hr, ite_eq_right (by omega)]
  have h256 := h.state.ready.ws.h256
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun u =>
      u.mem = s.mem.writeW (off P.B (8 * kStat)) (BitVec.ofNat 64 0)) (by
      brun [h.state.ready.ws.x0, hdr_enc (show kStat < 32 by decide),
        h.state.ready.ws.scr.st (d := 8 * kStat) (by simp only [kStat, sFn]; omega)]
      rfl) rfl rfl rfl) fun u ⟨hm, ku⟩ => ?_)
  have hf : Frm P.B [(8 * kStat, 8)] s.mem u.mem := by
    rw [hm]
    exact Frm.of_outside (writeW_outside _ P.B _ (d := 8 * kStat) (by decide)) (by simp)
  have k : Keep mmRegs s u := ku.mono (by decide)
  have hready := (h.state.ready.write_header (BitVec.ofNat 64 0) P.exponentRoom (i := kStat) (by decide)).of_words
    P.exponentRoom (fun _ _ => by change word u.mem _ _ = _; rw [hm]) ku.wr
      ((ku.gpr .x0 (by decide)).trans h.state.ready.ws.x0)
  have hused : word u.mem P.B (8 * kUsed) = BitVec.ofNat 64 used :=
    (hf.word_eq (by intro r hr; rw [List.mem_singleton.mp hr]; decide) (by decide)).trans h.state.used
  have hu := h.state.advance hready hused hf.work k
    (by intro r hr; rw [List.mem_singleton.mp hr]; change 256 ≤ P.Z; exact P.z256)
    (by
      intro j hj r hr; rw [List.mem_singleton.mp hr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hz : word u.mem P.B (8 * kStat) = BitVec.ofNat 64 0 := by rw [hm, word_writeW_self]
  have hend : PrimeLoopEnd P s₀ res u := by
    refine ⟨used, hu, h.usedBound, fun _ => hz, ?_, ?_, (h.keep.trans k).mono (by decide)⟩
    · intro b rest he; rw [hnone] at he; cases he
    · exact h.frame.trans (hf.work.mono (by simp [drawRoundRanges, sampleRoundRanges]))
  refine WP.mono (statCmp_ok hu.ready.ws (v := 0) (by decide) hz) fun t ⟨hzt, hmt, kt⟩ => ?_
  exact ⟨by simpa using hzt, hend.of_mem hmt (kt.mono (by decide))⟩

end VG.Proof.Dsa.AArch64.Generation
