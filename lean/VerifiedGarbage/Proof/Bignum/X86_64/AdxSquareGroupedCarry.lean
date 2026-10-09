import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareGroupedWord
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonal

namespace VG.Proof.Bignum.X86_64.AdxSquareGrouped
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- Adding the previous group's carry to a single-limb square cannot
    overflow its two-limb representation. -/
theorem square_carry_lt (x : BitVec 64) {carry : Nat} (hc : carry ≤ 2) :
    x.toNat * x.toNat + carry < 2 ^ 128 := by
  have h := Nat.mul_self_le_mul_self (show x.toNat ≤ 2 ^ 64 - 1 by have := x.isLt; omega)
  omega

theorem inject_values (s : State) :
    WP isa (.block AdxSquareGrouped.injectCarry) s fun t =>
      t.gpr .rcx = s.gpr .rcx + s.gpr .r15 ∧
      t.gpr .rax = s.gpr .rax + (BitVec.ofBool (decide
        (2 ^ 64 ≤ (s.gpr .rcx).toNat + (s.gpr .r15).toNat))).setWidth 64 ∧
      t.mem = s.mem ∧ Keep [.rcx, .rax] s t := by
  refine WP.mono (WP.keep [.rcx, .rax] (Q := fun t =>
      t.gpr .rcx = s.gpr .rcx + s.gpr .r15 ∧
      t.gpr .rax = s.gpr .rax + (BitVec.ofBool (decide
        (2 ^ 64 ≤ (s.gpr .rcx).toNat + (s.gpr .r15).toNat))).setWidth 64 ∧
      t.mem = s.mem) ?_ rfl) fun t ⟨h,k⟩ => ⟨h.1,h.2.1,h.2.2,k⟩
  unfold AdxSquareGrouped.injectCarry
  xrun [] <;> simp

theorem inject_ok (s : State)
    (hbound : (s.gpr .rcx).toNat + 2 ^ 64 * (s.gpr .rax).toNat +
      (s.gpr .r15).toNat < 2 ^ 128) :
    WP isa (.block AdxSquareGrouped.injectCarry) s fun t =>
      (t.gpr .rcx).toNat + 2 ^ 64 * (t.gpr .rax).toNat =
        (s.gpr .rcx).toNat + 2 ^ 64 * (s.gpr .rax).toNat + (s.gpr .r15).toNat ∧
      Keeps [.rcx, .rax] s t := by
  refine WP.mono (inject_values s) fun t ⟨hl, hh, hm, hk⟩ => ?_
  refine ⟨?_, hk.1, hm, hk.2⟩
  let c := decide (2 ^ 64 ≤ (s.gpr .rcx).toNat + (s.gpr .r15).toNat)
  have he := adc_carry (s.gpr .rcx) (s.gpr .r15) false
  simp at he
  have hhi : (s.gpr .rax).toNat + c.toNat < 2 ^ 64 := by
    change (s.gpr .rcx + s.gpr .r15).toNat + 2 ^ 64 * c.toNat = _ at he
    omega
  rw [hl, hh]
  simp only [BitVec.toNat_add, toNat_ofBool64]
  change _ + 2 ^ 64 * (((s.gpr .rax).toNat + c.toNat) % 2 ^ 64) = _
  rw [Nat.mod_eq_of_lt hhi]
  dsimp [c] at *
  omega

theorem initialPair_ok (s : State) (hc : (s.gpr .r15).toNat ≤ 2) :
    WP isa (.block AdxSquareGrouped.initialPair) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧ t.gpr .rsi = 0 ∧
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat +
          2 ^ 128 * (c'.toNat + o'.toNat) =
        2 * ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat) +
          (s.gpr .rdx).toNat * (s.gpr .rdx).toNat + (s.gpr .r15).toNat ∧
      Keeps [.rax, .rcx, .rsi, .r11, .r12] s t := by
  unfold AdxSquareGrouped.initialPair
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (mulx_ok s (hi := .rax) (lo := .rcx) (src := .reg .rdx) rfl
    (fun _ h => nomatch h) (by decide)) fun a ⟨ea, _, _, ka⟩ => ?_
  have bound : (a.gpr .rcx).toNat + 2 ^ 64 * (a.gpr .rax).toNat +
      (a.gpr .r15).toNat < 2 ^ 128 := by
    rw [ea, ka.gpr (by decide : Reg.r15 ∉ _)]
    exact square_carry_lt _ hc
  rw [WP.block_append_iff]
  refine WP.mono (inject_ok a bound) fun b ⟨eb, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (xorRsi_ok b) fun d ⟨zd, cd, od, kd⟩ => ?_
  refine WP.mono (addPair_ok d cd od) fun t ⟨ct, ot, hct, hot, et, kt⟩ => ?_
  have kad := ka.trans (kb.trans kd)
  refine ⟨ct, ot, hct, hot, (kt.gpr (by decide)).trans zd, ?_,
    (kad.trans kt).mono (by decide)⟩
  rw [kad.gpr (by decide : Reg.r11 ∉ _), kad.gpr (by decide : Reg.r12 ∉ _),
    kd.gpr (by decide : Reg.rcx ∉ _), kd.gpr (by decide : Reg.rax ∉ _)] at et
  rw [ka.gpr (by decide : Reg.r15 ∉ _)] at eb
  simp only [Bool.toNat_false, Nat.add_zero] at et
  omega

theorem close_ok (s : State) {c o : Bool} (hz : s.gpr .rsi = 0)
    (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block AdxSquareGrouped.close) s fun t =>
      (t.gpr .r15).toNat = c.toNat + o.toNat ∧
      (t.gpr .r15).toNat ≤ 2 ∧ Keeps [.r15] s t := by
  rw [show AdxSquareGrouped.close = ([.mov32 .r15 (.imm 0)] : List Instr) ++
    (([.adcx .r15 (.reg .rsi)] : List Instr) ++ [.adox .r15 (.reg .rsi)]) from rfl,
    WP.block_append_iff]
  refine WP.mono (movZero_ok s .r15) fun a ⟨za, ca, oa, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adcx_ok a (dst := .r15) (src := .reg .rsi) rfl
    (fun _ h => nomatch h) (ca.trans hc)) fun b ⟨cb, _, ob, eb, kb⟩ => ?_
  refine WP.mono (adox_ok b (dst := .r15) (src := .reg .rsi) rfl
    (fun _ h => nomatch h) (ob.trans (oa.trans ho))) fun t ⟨ot, _, _, et, kt⟩ => ?_
  have za' : a.gpr .rsi = 0 := (ka.gpr (by decide)).trans hz
  have zb' : b.gpr .rsi = 0 := (kb.gpr (by decide)).trans za'
  rw [za, za'] at eb
  rw [zb'] at et
  have hb := Bool.toNat_le c
  have ho' := Bool.toNat_le o
  simp only [show (0 : BitVec 64).toNat = 0 from rfl] at eb et
  refine ⟨?_, ?_, (ka.trans (kb.trans kt)).mono (by decide)⟩ <;> omega

end VG.Proof.Bignum.X86_64.AdxSquareGrouped
