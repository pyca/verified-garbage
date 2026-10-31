module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.KeyGroups
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: the word loop stores one schedule word and advances its public pointers.
/-! # POWER8 AES schedule-word store -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE

theorem loadWord_ok (d n : Reg) (s : State) (hn : n ≠ .r0)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr n) 4) :
    WP isa (.block [.load .w d n 0]) s fun t =>
      t.gpr d = (s.mem.readW (s.gpr n) 32).setWidth 64 ∧ Local [d] [] s t := by
  apply WP.of_runBlock
  rw [runBlock_cons, exec_load_w hn (by decide) (by simpa only [BitVec.add_zero] using hr), runStep_some, runBlock_nil]
  simp only [BitVec.add_zero, Option.some.injEq, exists_eq_left']
  exact ⟨RegUpd.gpr_write_self .., Local.write s d _⟩

structure WordStored (s t : State) : Prop where
  keep : Keep [.r0, .r8, .r9, .r10, .r11, .r12] s t
  mem : t.mem = s.mem.writeW (s.gpr .r11 + 4#64) ((s.gpr .r9).setWidth 32 ^^^ s.mem.readW (s.gpr .r10) 32)
  ptr10 : t.gpr .r10 = s.gpr .r10 + 4#64
  ptr11 : t.gpr .r11 = s.gpr .r11 + 4#64
  index : t.gpr .r12 = s.gpr .r12 + 4#64
  test : t.gpr .r0 = (s.gpr .r12 + 4#64) - s.gpr .r7

theorem wordStore_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .r10) 4)
    (hw : InRegions s.wr (s.gpr .r11 + 4#64) 4) :
    WP isa (.block Impl.Aes.PPC64LE.Crypto.wordStore) s (WordStored s) := by
  rw [Impl.Aes.PPC64LE.Crypto.wordStore]
  refine wp_lwz (by decide) (by decide) (by rw [BitVec.add_zero]) hr fun s₁ u₁ => ?_
  refine wp_xor fun s₂ u₂ => ?_
  refine wp_stw (by decide) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₂.wr, u₁.wr]; exact hw) fun s₃ u₃ => ?_
  refine wp_addi (by decide) (by decide) fun s₄ u₄ => wp_addi (by decide) (by decide) fun s₅ u₅ => ?_
  refine wp_addi (by decide) (by decide) fun s₆ u₆ => wp_sub fun s₇ u₇ => wp_nil ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₇.other _ hr.1, u₆.other _ hr.2.2.2.2.2, u₅.other _ hr.2.2.2.1,
      u₄.other _ hr.2.2.2.2.1, congrFun u₃.gpr r, u₂.other _ hr.2.2.1, u₁.other _ hr.2.1]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₁.gpr, u₁.other _ (by decide), u₂.mem, u₁.mem,
      BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), congrFun u₃.gpr .r10,
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, congrFun u₃.gpr .r11,
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), congrFun u₃.gpr .r12,
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₇.gpr, u₆.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₄.other _ (by decide), congrFun u₃.gpr .r12, congrFun u₃.gpr .r7,
      u₂.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), u₁.other _ (by decide)]

theorem next_mod {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) :
    (i+1)%nk = if i%nk+1 = nk then 0 else i%nk+1 := by
  rcases h3 with rfl | rfl | rfl <;> split <;> omega

theorem wordEnd_ok (s : State) {nk i total : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (hi : i < total)
    (h0 : s.gpr .r0 = BitVec.ofNat 64 (4*(i%nk+1)) - BitVec.ofNat 64 (4*nk))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 (4*(i%nk+1))) (h4 : s.gpr .r4 = BitVec.ofNat 64 (total-i)) :
    WP isa Impl.Aes.PPC64LE.Crypto.wordEnd s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 (4*((i+1)%nk)) ∧
      t.gpr .r4 = BitVec.ofNat 64 (total-(i+1)) ∧ Local [.r4, .r12] [] s t := by
  have hnk : 0 < nk ∧ nk ≤ 8 := by omega
  have hrem := Nat.mod_lt i hnk.1
  have he : eval (.zero .d .r0) s = some (decide (i%nk+1 = nk)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, h0]
    have hp : (4*(i%nk+1) = 4*nk) ↔ (i%nk+1 = nk) := by omega
    exact congrArg some ((Offset.ofNat_sub_ofNat_beq (by omega) (by omega)).trans (by rw [Bool.eq_iff_iff]; simpa only [decide_eq_true_iff] using hp))
  have hm := next_mod (i := i) h3
  rw [Impl.Aes.PPC64LE.Crypto.wordEnd]
  have branch : WP isa (.ite (.zero .d .r0) (.block [.li .r12 0]) (.block [])) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 (4*((i+1)%nk)) ∧ Local [.r12] [] s t := by
    by_cases hz : i%nk+1 = nk
    · refine WP.ite true (by simpa only [hz, decide_true] using he) (fun _ => ?_) (by simp)
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec,
        show 0 < 2^15 by decide, ite_true, Option.some.injEq, exists_eq_left']
      refine ⟨?_, Local.write s .r12 _⟩
      rw [RegUpd.gpr_write_self, hm, ite_eq_left hz, Nat.mul_zero]
    · refine WP.ite false (by simpa only [hz, decide_false] using he) (by simp) (fun _ => WP.block_nil ?_)
      exact ⟨by rw [h12, hm, ite_eq_right hz], Local.refl _ _ _⟩
  refine WP.seq (WP.mono branch fun u ⟨hv, he⟩ => ?_)
  apply WP.of_runBlock
  rw [runBlock_cons, exec_subi (by decide) (by decide), runStep_some, runBlock_nil]
  simp only [Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, (he.trans (Local.write u .r4 (u.gpr .r4 - BitVec.ofNat 64 1))).weaken (by simp [or_comm]) (by simp)⟩
  · rw [RegUpd.gpr_write, ite_eq_right (by decide)]; exact hv
  · rw [RegUpd.gpr_write_self, he.keep.gpr (by decide), h4, Offset.ofNat_sub_ofNat (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)

end VG.Proof.Aes.PPC64LE.Crypto
