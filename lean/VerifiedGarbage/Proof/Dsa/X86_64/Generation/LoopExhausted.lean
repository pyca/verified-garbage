module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopState
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrMain
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega

/-! # Exhaustion ends the primality loop without reading an incomplete draw -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen.X86_64

theorem loopExhausted_ok {P : PrimeParams} {mi : BitVec 64} {s₀ s : State}
    {res : Option (Bool × List Byte)} {i uni used : Nat}
    (h : PrimeLoopState P mi s₀ res i uni used s) (hshort : P.rand.length < used + P.drawBytes) :
    WP isa (.seq (.block [.mov32 .rax (.imm 0), .store (hdr kStat) .rax])
      (.block [.mov .rax (.mem (hdr kStat)), .alu .cmp .rax (.imm 4)])) s fun t =>
        isa.eval .e t = some false ∧ PrimeLoopEnd P mi s₀ res t := by
  have hr := VG.Proof.RsaKeyGen.mrLoop_step P.N P.checks (Spec.Rsa.splitTwos (P.N - 1)).1
    (Spec.Rsa.splitTwos (P.N - 1)).2 P.drawBytes P.rand i uni used h.go P.drawWidth (by have := P.drawMin; omega)
  have hnone : res = none := by
    rw [← h.rest]
    change Spec.RsaKeyGen.loop _ _ _ = _
    rw [hr, ite_eq_right (by omega)]
  have hst : InRegions s.wr (off P.B (8 * kStat)) 8 :=
    h.state.ready.good.scr.st (by have := hdr_lt_slot P.w 8 (show kStat < 32 by decide); have := P.dims.z; omega)
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun u =>
      u.mem = s.mem.writeW (off P.B (8 * kStat)) (BitVec.ofNat 64 0)) (by
    xrun [State.ea, hdr, hdrOff, h.state.ready.good.rdi, hst]; rfl) rfl) fun u ⟨hm, ku⟩ => ?_)
  have hf : Frm P.B [(8 * kStat, 8)] s.mem u.mem := by
    rw [hm]
    exact Frm.of_outside (writeW_outside _ P.B _ (d := 8 * kStat) (by decide)) (by simp)
  have k : Keep mmRegs s u := ku.mono (by decide)
  have hready := h.state.ready.of_frm P.dims hf k ((k.gpr (by decide)).trans h.state.ready.good.rdi)
    (by rng_disj) (by rng_disj) (by rng_disj)
  have hused : word u.mem P.B (8 * kUsed) = BitVec.ofNat 64 used := by
    rw [hf.word_eq (by rng_disj) (by decide : 8 * kUsed + 8 ≤ 2 ^ 64)]; exact h.state.used
  have hu := h.state.advance hready hused hf.work k
    (by simp only [List.mem_singleton, forall_eq]; change 240 ≤ P.Z; have := P.z256; omega) (by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> rng_disj)
  have hz : word u.mem P.B (8 * kStat) = BitVec.ofNat 64 0 := by rw [hm, word_writeW_self]
  have hend : PrimeLoopEnd P mi s₀ res u := by
    refine ⟨used, hu, h.usedBound, fun _ => hz, ?_, ?_, (h.keep.trans k).mono (by decide)⟩
    · intro b rest he; rw [hnone] at he; cases he
    · exact h.frame.trans (hf.work.mono (by simp [drawRoundRanges, sampleRoundRanges]))
  refine WP.mono (statCmp_ok hu.ready.good P.dims.z (v := 0) (by decide) hz) fun t ⟨hzt, hmt, kt⟩ => ?_
  exact ⟨by simp [eval, hzt], hend.of_mem hmt (kt.mono (by decide))⟩

end VG.Proof.Dsa.X86_64.Generation
