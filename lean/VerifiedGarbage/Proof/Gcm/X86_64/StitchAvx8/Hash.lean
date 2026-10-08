import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.GhLoad

/-!
# Hashing a complete prepared batch

All eight inputs are consumed in the order 1, …, 7, 0. The first product
does not depend on the old accumulators. Memory and the AES state registers
are preserved throughout.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Gcm.X86_64.StitchAvx8 (gh8 hash8 reduceFinal)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Gcm (Block)

def bufferBlock (s : State) (k : Nat) : Block :=
  s.mem.readW (s.ea (at_ .r11 (512 + 16 * k))) 128

def bufferPower (s : State) (k : Nat) : Block :=
  s.mem.readW (s.ea (at_ .r11 (16 * (8 + k)))) 128

private theorem input_frame {s t : State} (f : YFrame ghRegs s t) (k : Nat) :
    input t k = hashInput (bufferBlock s) (s.lane .xmm2 0) (k % 8) := by
  simp only [input, hashInput, bufferBlock, f.mem, State.ea, f.gpr,
    f.lane .xmm2 (by decide) 0 (by decide)]

private theorem power_frame {s t : State} (f : YFrame ghRegs s t) (k : Nat) :
    power t k = bufferPower s (k % 8) := by
  simp only [power, bufferPower, f.mem, State.ea, f.gpr]

theorem hashSteps_ok (s : State)
    (hp : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 (16 * (8 + k)))) 16)
    (hx : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 (512 + 16 * k))) 16)
    (n : Nat) (hn : n ≤ 8) :
    WP isa (.block ((List.range n).flatMap fun i => gh8 ((i + 1) % 8))) s fun t =>
      prod (t.proj 0) = (if n = 0 then prod (s.proj 0) else
        accN (bufferBlock s) (bufferPower s) (s.lane .xmm2 0) n) ∧ YFrame ghRegs s t := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, YFrame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨hacc, hf⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (gh8_ok t ((n + 1) % 8) (by
      rw [hf.rd, hf.wr]; simp only [State.ea, hf.gpr]; exact hp _ (Nat.mod_lt _ (by decide))) (by
      rw [hf.rd, hf.wr]; simp only [State.ea, hf.gpr]; exact hx _ (Nat.mod_lt _ (by decide))))
      fun u ⟨ha, hu⟩ => ⟨?_, hf.trans hu⟩
    rw [ha, input_frame hf, power_frame hf, Nat.mod_mod]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, accN_succ]
    by_cases hz : n = 0
    · subst n
      simp only [Nat.zero_add, Nat.reduceMod, ite_true, accN, List.range_zero, List.foldl_nil]
    · have hm : (n + 1) % 8 ≠ 1 := by omega
      rw [ite_eq_right hm, hacc, ite_eq_right hz]

/-- One complete GHASH batch and its final reduction. -/
theorem hash8_ok (s : State)
    (hp : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 (16 * (8 + k)))) 16)
    (hx : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 (512 + 16 * k))) 16)
    (hc : InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 784)) 16)
    (hv : s.mem.readW (s.ea (at_ .r11 784)) 128 = poly) :
    WP isa (.block hash8) s fun t =>
      t.lane .xmm2 0 = reduceB (accN (bufferBlock s) (bufferPower s) (s.lane .xmm2 0) 8) ∧
      YFrame (ghRegs ++ ([.xmm1, .xmm2, .xmm8, .xmm9, .xmm11] : List XReg)) s t := by
  rw [hash8, WP.block_append_iff]
  refine WP.mono (hashSteps_ok s hp hx 8 (by decide)) fun t ⟨ha, hf⟩ => ?_
  refine WP.mono (reduceFinal_ok t (by
    simpa only [hf.rd, hf.wr, State.ea, hf.gpr] using hc) (by
    simpa only [hf.mem, State.ea, hf.gpr] using hv)) fun u ⟨hu, hfu⟩ => ⟨?_, hf.comp hfu⟩
  simpa only [ha, Nat.reduceEqDiff, ite_false] using hu

end VG.Proof.Gcm.X86_64.StitchAvx8
