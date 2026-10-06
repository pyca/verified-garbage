import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddWord

namespace VG.Proof.Bignum.X86_64.AdxDualAdd
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

theorem close_ok (s : State) {c o : Bool} (hc : s.cf = some c)
    (ho : s.of = some o) (hz : s.gpr .rax = 0) :
    WP isa (.block AdxDualAdd.close) s fun t =>
      (t.gpr .rax).toNat = c.toNat + o.toNat ∧
      t.cf = some false ∧ t.of = some false ∧ Keeps [.rdx, .rax] s t := by
  change WP isa (.block ([.mov32 .rdx (.imm 0)] ++
    AdxDualAdd.word .rax (.reg .rdx) (.reg .rdx))) s _
  rw [WP.block_append_iff]
  refine WP.mono (movZero_ok s .rdx) fun a ⟨za,ca,oa,ka⟩ => ?_
  have ha : readSrc a (.reg .rdx) = some (0 : BitVec 64) := congrArg some za
  have hb : ∀ t, Keeps [.rax] a t → readSrc t (.reg .rdx) = some (0 : BitVec 64) := by
    intro t kt
    exact congrArg some ((kt.gpr (by decide)).trans za)
  refine WP.mono (word_ok a ha hb (fun _ h => nomatch h) (fun _ h => nomatch h)
    (ca.trans hc) (oa.trans ho)) fun t ⟨ct,ot,hct,hot,et,kt⟩ => ?_
  rw [ka.gpr (r := .rax) (by decide), hz] at et
  simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add, Nat.add_zero] at et
  have bc := Bool.toNat_le c
  have bo := Bool.toNat_le o
  have ec : ct = false := Bool.toNat_eq_zero.mp (by omega)
  have eo : ot = false := Bool.toNat_eq_zero.mp (by omega)
  subst ct; subst ot
  simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at et
  exact ⟨et,hct,hot,(ka.trans kt).mono (by simp)⟩

end VG.Proof.Bignum.X86_64.AdxDualAdd
