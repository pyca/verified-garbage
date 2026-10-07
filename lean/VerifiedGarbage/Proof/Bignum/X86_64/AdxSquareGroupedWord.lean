import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquareGrouped
import VerifiedGarbage.Proof.Bignum.X86_64.AdxStep

/-! Exact equations for the two independent live carry chains of a square. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareGrouped
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

theorem word_ok (s : State) {dst addend : Reg} {c o : Bool}
    (hne : addend ≠ dst) (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block (AdxSquareGrouped.word dst addend)) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      (t.gpr dst).toNat + 2 ^ 64 * (c'.toNat + o'.toNat) =
        2 * (s.gpr dst).toNat + (s.gpr addend).toNat + c.toNat + o.toNat ∧
      Keeps [dst] s t := by
  rw [show AdxSquareGrouped.word dst addend =
    ([.adcx dst (.reg dst)] : List Instr) ++ [.adox dst (.reg addend)] from rfl,
    WP.block_append_iff]
  refine WP.mono (adcx_ok s (dst := dst) (src := .reg dst) rfl
    (fun _ h => nomatch h) hc) fun a ⟨ca, hca, hoa, ea, ka⟩ => ?_
  refine WP.mono (adox_ok a (dst := dst) (src := .reg addend) rfl
    (fun _ h => nomatch h) (hoa.trans ho)) fun t ⟨ot, hot, hct, et, kt⟩ => ?_
  refine ⟨ca, ot, hct.trans hca, hot, ?_, (ka.trans kt).mono (by simp)⟩
  rw [ka.gpr (r := addend) (by simpa using hne)] at et
  omega

theorem addPair_ok (s : State) {c o : Bool} (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block AdxSquareGrouped.addPair) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat +
          2 ^ 128 * (c'.toNat + o'.toNat) =
        2 * ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat) +
          (s.gpr .rcx).toNat + 2 ^ 64 * (s.gpr .rax).toNat + c.toNat + o.toNat ∧
      Keeps [.r11, .r12] s t := by
  unfold AdxSquareGrouped.addPair
  rw [WP.block_append_iff]
  refine WP.mono (word_ok s (dst := .r11) (addend := .rcx) (by decide) hc ho)
    fun a ⟨ca, oa, hca, hoa, ea, ka⟩ => ?_
  refine WP.mono (word_ok a (dst := .r12) (addend := .rax) (by decide) hca hoa)
    fun t ⟨ct, ot, hct, hot, et, kt⟩ => ?_
  refine ⟨ct, ot, hct, hot, ?_, (ka.trans kt).mono (by simp)⟩
  rw [ka.gpr (by decide : Reg.rax ∉ _), ka.gpr (by decide : Reg.r12 ∉ _)] at et
  rw [kt.gpr (by decide : Reg.r11 ∉ _)]
  omega

/-- Two cross-product words are doubled while adding one diagonal square.
Both outgoing flags remain explicit, so the next pair can consume them. -/
theorem pair_ok (s : State) {c o : Bool} (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block AdxSquareGrouped.pair) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat +
          2 ^ 128 * (c'.toNat + o'.toNat) =
        2 * ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat) +
          (s.gpr .rdx).toNat * (s.gpr .rdx).toNat + c.toNat + o.toNat ∧
      Keeps [.rax, .rcx, .r11, .r12] s t := by
  unfold AdxSquareGrouped.pair
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (mulx_ok s (hi := .rax) (lo := .rcx) (src := .reg .rdx) rfl
    (fun _ h => nomatch h) (by decide)) fun a ⟨ea, ca, oa, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (word_ok a (dst := .r11) (addend := .rcx) (by decide)
    (ca.trans hc) (oa.trans ho)) fun b ⟨cb, ob, hcb, hob, eb, kb⟩ => ?_
  refine WP.mono (word_ok b (dst := .r12) (addend := .rax) (by decide) hcb hob)
    fun t ⟨ct, ot, hct, hot, et, kt⟩ => ?_
  refine ⟨ct, ot, hct, hot, ?_, (ka.trans (kb.trans kt)).mono (by simp)⟩
  rw [ka.gpr (by decide : Reg.r11 ∉ _)] at eb
  rw [kb.gpr (by decide : Reg.rax ∉ _), kb.gpr (by decide : Reg.r12 ∉ _),
    ka.gpr (by decide : Reg.r12 ∉ _)] at et
  rw [kt.gpr (by decide : Reg.r11 ∉ _)]
  omega

end VG.Proof.Bignum.X86_64.AdxSquareGrouped
