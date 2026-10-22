module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Tail
public import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx2Tail
import VerifiedGarbage.Proof.ChaCha20.X86_64.XorBufX
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# ChaCha20 on x86-64 with AVX2, the last bytes from `buf`

`Avx2Tail.fromBuf` XORs the keystream left in `buf` into the data by
`XorBuf.xorBufX 5`, 32 bytes at a time while at least 32 remain: with the
same hypotheses as `Avx512Tail.fromBuf_ok` (whose `xorBuf` does it eight
bytes at a time), all the data is done.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx2Tail

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.ChaCha20.X86_64.Avx2 (APre edp eL ebp edR D0 KS frR eL_lt)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (Done win win_sub not_win ea_win r9_not_calleeSaved)

/-- `fromBuf` of the `n` bytes left, from `buf`, where the data from byte `p`
holds bytes `p … p + n` of the keystream: then all the data is done. -/
theorem fromBufY_ok {s₀ : State} (hp : APre s₀) {p n : Nat} (hn : p + n = eL s₀) (hn256 : n ≤ 256) {s : State}
    (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 p) (hr9 : s.gpr .r9 = ebp s₀)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hkeep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r)
    (hdone : ∀ k < p, s.mem (edp s₀ + BitVec.ofNat 64 k) = D0 s₀ k ^^^ (KS s₀).getD k 0)
    (hrest : ∀ k < n, s.mem (edp s₀ + BitVec.ofNat 64 p + BitVec.ofNat 64 k) = D0 s₀ (p + k))
    (hks : ∀ k < n, s.mem (ebp s₀ + BitVec.ofNat 64 k) = (KS s₀).getD (p + k) 0)
    (hframe : Frame (frR s₀) s₀.mem s.mem) :
    WP isa Impl.ChaCha20.X86_64.Avx2Tail.fromBuf s (Done s₀) := by
  have hL := eL_lt s₀
  have sb : Region.Sub ⟨ebp s₀, n⟩ (Avx2.bufR (ebp s₀)) := Region.sub_prefix (by omega_arith)
  have hdb : (win s₀ p n).Disjoint ⟨ebp s₀, n⟩ := (hp.d_b.sub_left (win_sub (by omega_arith))).sub_right sb
  -- The data's address into `r10`, `buf`'s into `rsi`.
  refine WP.seq (WP.of_runBlock ⟨(s.setReg .r10 (s.gpr .rsi)).setReg .rsi (s.gpr .r9),
    by simp [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, gpr_setReg], ?_⟩)
  have g : ∀ r, r ≠ .r10 → r ≠ .rsi →
      ((s.setReg .r10 (s.gpr .rsi)).setReg .rsi (s.gpr .r9)).gpr r = s.gpr r := fun r a b => by
    simp [gpr_setReg, a, b]
  refine WP.mono (ChaCha20.X86_64.XorBufX.xorBufX_ok (w := 5) (by decide) (d := .r10) (by decide)
    (D := edp s₀ + BitVec.ofNat 64 p) (B := ebp s₀) (n := n)
    (by simp [gpr_setReg, hrsi]) (by simp [gpr_setReg, hr9]) (by rw [g _ (by decide) (by decide), hrdx])
    (by omega_arith) hdb
    ⟨edR s₀, by simp [wr_setReg, hwr, hp.wr], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    ⟨Avx2.bufR (ebp s₀), by simp [rd_setReg, wr_setReg, hrd, hwr, hp.wr], by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega_arith⟩)
    fun s' hq => ⟨?_, fun r hr => ?_, ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [hq.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g _ (by decide) (by decide), hr9]
  · obtain ⟨_, a, b, c⟩ := r9_not_calleeSaved hr
    have e : r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .rdi ∧ r ≠ .r10 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hq.keep r a b c e.1 e.2.1 e.2.2.1, g r e.2.2.2 e.2.1]; exact hkeep r hr
  · rw [hq.rd]; simp [rd_setReg, hrd]
  · rw [hq.wr]; simp [wr_setReg, hwr]
  · by_cases hkp : k < p
    · rw [hq.frame _ (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact not_win (by omega_arith) hk (.inl hkp))]
      simp only [mem_setReg]; exact hdone k hkp
    · rw [ea_win (p := p) (by omega_arith), hq.data (k - p) (by omega_arith)]
      simp only [mem_setReg]
      rw [hrest _ (by omega_arith), hks _ (by omega_arith), Nat.add_sub_cancel' (by omega_arith)]
  · refine hframe.trans (Frame.trans (by simp only [mem_setReg]; exact Frame.refl _ _) (hq.frame.sub fun r hr => ?_))
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨edR s₀, by simp, win_sub (by omega_arith)⟩

end VG.Proof.ChaCha20.X86_64.Avx2Tail
