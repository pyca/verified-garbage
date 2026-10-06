import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddChain
import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddClose
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Add

namespace VG.Proof.Bignum.X86_64.AdxDualAdd
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRotate8 (cols number cols_keep number_words)
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

theorem xorRax_ok (s : State) :
    WP isa (.block [.alu32 .xor .rax (.reg .rax)]) s fun t =>
      t.gpr .rax = 0 ∧ t.cf = some false ∧ t.of = some false ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, Option.bind_some,
    State.setReg32, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg_self, BitVec.xor_self]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

theorem addInput_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (hp : s.gpr .rsi = off B e) (he : e + 64 ≤ Z) :
    WP isa (.block AdxDualAdd.addInput) s fun t =>
      cols t + 2^512 * (t.gpr .rax).toNat =
        cols s + wv s.mem B e 8 + (s.gpr .rdx).toNat ∧
      (t.gpr .rax).toNat ≤ 2 ∧ t.cf = some false ∧ t.of = some false ∧
      Keeps [.rax,.rdx,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15] s t := by
  unfold AdxDualAdd.addInput
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (xorRax_ok s) fun a ⟨za,hca,hoa,ka⟩ => ?_
  rw [WP.block_append_iff]
  have srcA : ∀ k < 8, ∀ t, Keeps AdxDualAdd.regs a t →
      readSrc t (.mem (at_ .rsi (8*k))) = some (word s.mem B (e+8*k)) := by
    intro k hk t kt
    rw [kt.readMem (by simp [AdxDualAdd.regs, at_]) (by intro r h; nomatch h),
      ka.readMem (by simp [at_]) (by intro r h; nomatch h)]
    exact readSrc_word hs (AdxRotate8.ea_at hp (8*k)) (by omega)
  have srcB : ∀ k < 8, ∀ t, Keeps AdxDualAdd.regs a t →
      readSrc t (.reg (if k = 0 then .rdx else .rax)) =
        some (if k = 0 then s.gpr .rdx else 0) := by
    intro k _ t kt
    by_cases hk : k = 0
    · simp only [hk, ↓reduceIte, readSrc,
        kt.gpr (r := .rdx) (by decide), ka.gpr (r := .rdx) (by decide)]
    · simp only [hk, ↓reduceIte, readSrc, kt.gpr (r := .rax) (by decide), za]
  refine WP.mono (chain_ok a _ _ _ _ hca hoa srcA srcB
    (fun _ _ _ h => nomatch h) (fun _ _ _ h => nomatch h))
    fun b ⟨cb,ob,hcb,hob,eb,kb⟩ => ?_
  refine WP.mono (close_ok b hcb hob ((kb.gpr (by decide)).trans za))
    fun t ⟨et,hct,hot,kt⟩ => ?_
  rw [number_words, cols_keep ka.keep (by decide)] at eb
  simp only [number, Nat.reduceEqDiff, ↓reduceIte,
    show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero,
    Bool.toNat_false] at eb
  refine ⟨?_,?_,hct,hot,(ka.trans (kb.trans kt)).mono (by simp [AdxDualAdd.regs])⟩
  · rw [cols_keep kt.keep (by decide), et]
    exact eb
  · rw [et]; have bc := Bool.toNat_le cb; have bo := Bool.toNat_le ob; omega

end VG.Proof.Bignum.X86_64.AdxDualAdd
