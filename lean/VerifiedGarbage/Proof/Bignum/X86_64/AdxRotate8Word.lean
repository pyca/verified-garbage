import VerifiedGarbage.Impl.Bignum.X86_64.AdxRotate8
import VerifiedGarbage.Proof.Bignum.X86_64.AdxStep

/-! Numeric equations for a rotating ADX column, including both live flags. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

theorem word_ok (s : State) {k : Nat} {hi prev next : Reg} {v : BitVec 64} {c o : Bool}
    (hm : readSrc s (.mem (at_ .rbp (8 * k))) = some v)
    (hc : s.cf = some c) (ho : s.of = some o)
    (h1 : hi ≠ .rax) (h2 : prev ≠ hi) (h3 : prev ≠ .rax)
    (h4 : next ≠ hi) (h5 : next ≠ .rax) (h6 : next ≠ prev) :
    WP isa (.block (AdxRotate8.word k hi prev next)) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      (t.gpr prev).toNat + 2 ^ 64 * c'.toNat + 2 ^ 64 * (t.gpr hi).toNat +
        2 ^ 128 * o'.toNat =
      (s.gpr prev).toNat + (s.gpr .rdx).toNat * v.toNat + c.toNat +
        2 ^ 64 * (s.gpr next).toNat + 2 ^ 64 * o.toNat ∧ Keeps [hi, .rax, prev] s t := by
  rw [show AdxRotate8.word k hi prev next = ([.mulx hi .rax (.mem (at_ .rbp (8 * k)))] : List Instr) ++
    (([.adcx prev (.reg .rax)] : List Instr) ++ [.adox hi (.reg next)]) from rfl, WP.block_append_iff]
  refine WP.mono (mulx_ok s hm (fun _ h => nomatch h) h1) fun a ⟨ea, ca, oa, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adcx_ok a (src := .reg .rax) rfl (fun _ h => nomatch h) (ca.trans hc))
    fun b ⟨cb, hcb, hob, eb, kb⟩ => ?_
  refine WP.mono (adox_ok b (src := .reg next) rfl (fun _ h => nomatch h) (hob.trans (oa.trans ho)))
    fun t ⟨ot, hot, hct, et, kt⟩ => ?_
  refine ⟨cb, ot, hct.trans hcb, hot, ?_, (ka.trans (kb.trans kt)).mono (by simp)⟩
  have ep : a.gpr prev = s.gpr prev := ka.gpr (by simp [h2, h3])
  have en : b.gpr next = s.gpr next := (kb.gpr (by simp [h6])).trans (ka.gpr (by simp [h4, h5]))
  have eh : b.gpr hi = a.gpr hi := kb.gpr (by simp [Ne.symm h2])
  have eo : t.gpr prev = b.gpr prev := kt.gpr (by simp [h2])
  rw [ep] at eb
  rw [en, eh] at et
  rw [eo]
  omega

theorem close_ok (s : State) {c o : Bool} (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block AdxRotate8.close) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      (t.gpr .r15).toNat + 2 ^ 64 * c'.toNat + 2 ^ 64 * o'.toNat =
        (s.gpr .r15).toNat + c.toNat + o.toNat ∧ Keeps [.rax, .r15] s t := by
  rw [show AdxRotate8.close = ([.mov32 .rax (.imm 0)] : List Instr) ++
    (([.adox .r15 (.reg .rax)] : List Instr) ++ [.adcx .r15 (.reg .rax)]) from rfl, WP.block_append_iff]
  refine WP.mono (movZero_ok s .rax) fun a ⟨za, ca, oa, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adox_ok a (src := .reg .rax) rfl (fun _ h => nomatch h) (oa.trans ho))
    fun b ⟨ob, hob, hcb, eb, kb⟩ => ?_
  refine WP.mono (adcx_ok b (src := .reg .rax) rfl (fun _ h => nomatch h) (hcb.trans (ca.trans hc)))
    fun t ⟨ct, hct, hot, et, kt⟩ => ?_
  refine ⟨ct, ob, hct, hot.trans hob, ?_, (ka.trans (kb.trans kt)).mono (by simp)⟩
  have ep : a.gpr .r15 = s.gpr .r15 := ka.gpr (by decide)
  have zb : b.gpr .rax = 0 := (kb.gpr (by decide)).trans za
  rw [ep, za] at eb
  rw [zb] at et
  simp only [show (0 : BitVec 64).toNat = 0 from rfl] at eb et
  omega
end VG.Proof.Bignum.X86_64.AdxRotate8
