import VerifiedGarbage.Impl.Bignum.X86_64.R2Adx
import VerifiedGarbage.Proof.Bignum.X86_64.AdxStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock

/-!
# `R² mod m` by word steps with ADX: a word of `t = x 2^64 + q̂ mc`

`R2Adx.word` (`Impl/Bignum/X86_64/R2Adx.lean`): `lo + 2^64 hiN = q̂ mc[i]`,
`lo + hiP + OF` by `adox` and `prev + lo + CF` by `adcx`, stored over word
`i` of `x` once that word is read into `next` (`word_ok`).
-/

namespace VG.Proof.Bignum.X86_64.R2a

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.R2Adx
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

/-- `mov QWORD PTR [rbx + 8 r15 + 8 k], src`: the flags unchanged. -/
theorem storeX_ok {s : State} {B : Addr} {Z e j k : Nat} {src : Reg} (hs : Scr s B Z)
    (hbx : s.gpr .rbx = off B e) (h15 : s.gpr .r15 = BitVec.ofNat 64 j) (hZ : e + 8 * j + 8 * k + 8 ≤ Z) :
    WP isa (.block [.store (ix .rbx .r15 (8 * k)) src]) s fun t =>
      t.mem = s.mem.writeW (off B (e + 8 * j + 8 * k)) (s.gpr src) ∧ t.cf = s.cf ∧ t.of = s.of ∧
        t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_ixk s hbx h15 k, hs.st hZ,
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- The high half of a product of two words is at most `2^64 - 2`. -/
theorem hi_le {lo hi a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : lo + 2 ^ 64 * hi = a * b) :
    hi ≤ 2 ^ 64 - 2 := by
  have : a * b ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have : 2 ^ 64 * hi ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by omega
  by_contra hc
  have : 2 ^ 64 * (2 ^ 64 - 1) ≤ 2 ^ 64 * hi := Nat.mul_le_mul_left _ (by omega)
  omega

/-- Word `k` of a tile at word `j`: `t[j + k] + 2^64 (hiN + OF + CF) = prev + hiP + OF + CF + q̂ mc[j + k]`,
the word of `x` read before the store into `next`. -/
theorem word_ok {s : State} {B : Addr} {Z ex ec j k : Nat} {prev next hiP hiN : Reg} {c o : Bool}
    (hs : Scr s B Z) (hbx : s.gpr .rbx = off B ex) (hsi : s.gpr .rsi = off B ec)
    (h15 : s.gpr .r15 = BitVec.ofNat 64 j) (hX : ex + 8 * j + 8 * k + 8 ≤ Z) (hC : ec + 8 * j + 8 * k + 8 ≤ Z)
    (hc : s.cf = some c) (ho : s.of = some o)
    (d1 : hiN ≠ .r11) (d2 : hiP ≠ .r11) (d4 : next ≠ .r11) (d5 : next ≠ hiN) (d6 : prev ≠ .r11)
    (d7 : prev ≠ hiN) (d8 : prev ≠ next) (d9 : hiN ≠ .rbx) (d10 : hiN ≠ .r15) (d11 : next ≠ .rbx)
    (d12 : next ≠ .r15) (d14 : prev ≠ .rbx) (d15 : prev ≠ .r15) (d16 : hiP ≠ hiN) :
    WP isa (.block (R2Adx.word k prev next hiP hiN)) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      (word t.mem B (ex + 8 * j + 8 * k)).toNat + 2 ^ 64 * ((t.gpr hiN).toNat + o'.toNat + c'.toNat) =
        (s.gpr prev).toNat + (s.gpr hiP).toNat + o.toNat + c.toNat +
          (s.gpr .rdx).toNat * (word s.mem B (ec + 8 * j + 8 * k)).toNat ∧
      (t.gpr hiN).toNat ≤ 2 ^ 64 - 2 ∧
      t.gpr next = word s.mem B (ex + 8 * j + 8 * k) ∧
      t.mem = s.mem.writeW (off B (ex + 8 * j + 8 * k)) (word t.mem B (ex + 8 * j + 8 * k)) ∧
      Keep [hiN, .r11, next, prev] s t := by
  have hn := hs.nowrap
  rw [show R2Adx.word k prev next hiP hiN = ([.mulx hiN .r11 (.mem (ix .rsi .r15 (8 * k)))] : List Instr) ++
    (([.adox .r11 (.reg hiP)] : List Instr) ++ (([.mov next (.mem (ix .rbx .r15 (8 * k)))] : List Instr) ++
      (([.adcx prev (.reg .r11)] : List Instr) ++ ([.store (ix .rbx .r15 (8 * k)) prev] : List Instr)))) from rfl,
    WP.block_append_iff]
  refine WP.mono (mulx_ok s (readSrc_word hs (ea_ixk s hsi h15 k) hC) (fun _ h => nomatch h) d1)
    fun s₁ ⟨e₁, c₁, o₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adox_ok s₁ (src := .reg hiP) rfl (fun _ h => nomatch h) (o₁.trans ho))
    fun s₂ ⟨o', ho₂, hc₂, e₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  have hbx₂ : s₂.gpr .rbx = off B ex := by
    rw [k₂.gpr (by simp), k₁.gpr (by simp [Ne.symm d9])]; exact hbx
  have h15₂ : s₂.gpr .r15 = BitVec.ofNat 64 j := by
    rw [k₂.gpr (by simp), k₁.gpr (by simp [Ne.symm d10])]; exact h15
  have hs₂ : Scr s₂ B Z := hs.congr (k₂.2.2.2.trans k₁.2.2.2)
  have hm₂ : s₂.mem = s.mem := k₂.2.1.trans k₁.2.1
  refine WP.mono (movMem_ok s₂ (dst := next) (readSrc_word hs₂ (ea_ixk s₂ hbx₂ h15₂ k) hX))
    fun s₃ ⟨e₃, c₃, o₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adcx_ok s₃ (src := .reg .r11) rfl (fun _ h => nomatch h) (c₃.trans (hc₂.trans (c₁.trans hc))))
    fun s₄ ⟨c', hc₄, ho₄, e₄, k₄⟩ => ?_
  have hbx₄ : s₄.gpr .rbx = off B ex := by rw [k₄.gpr (by simp [Ne.symm d14]), k₃.gpr (by simp [Ne.symm d11])]; exact hbx₂
  have h15₄ : s₄.gpr .r15 = BitVec.ofNat 64 j := by
    rw [k₄.gpr (by simp [Ne.symm d15]), k₃.gpr (by simp [Ne.symm d12])]; exact h15₂
  have hs₄ : Scr s₄ B Z := hs₂.congr (k₄.2.2.2.trans k₃.2.2.2)
  refine WP.mono (storeX_ok (src := prev) hs₄ hbx₄ h15₄ hX) fun t ⟨hm, hct, hot, hg, hrd, hwr⟩ => ?_
  -- The registers.
  have r11₃ : s₃.gpr .r11 = s₂.gpr .r11 := k₃.gpr (by simp [Ne.symm d4])
  have hiN₄ : s₄.gpr hiN = s₁.gpr hiN := by
    rw [k₄.gpr (by simp [Ne.symm d7]), k₃.gpr (by simp [Ne.symm d5]), k₂.gpr (by simp [d1])]
  have hiP₁ : s₁.gpr hiP = s.gpr hiP := k₁.gpr (by simp [d16, d2])
  have prev₃ : s₃.gpr prev = s.gpr prev := by
    rw [k₃.gpr (by simp [d8]), k₂.gpr (by simp [d6]), k₁.gpr (by simp [d7, d6])]
  have hword : word t.mem B (ex + 8 * j + 8 * k) = s₄.gpr prev := by
    rw [hm]; exact word_writeW_self _ _ _ _
  refine ⟨c', o', hct.trans hc₄, hot.trans (ho₄.trans (o₃.trans ho₂)), ?_, ?_, ?_, by rw [hword, hm, k₄.2.1, k₃.2.1, hm₂], ?_⟩
  · rw [hword, hg, hiN₄]
    rw [prev₃, r11₃] at e₄
    rw [hiP₁] at e₂
    have := hi_le (s.gpr .rdx).isLt (word s.mem B (ec + 8 * j + 8 * k)).isLt e₁
    omega
  · rw [hg, hiN₄]; exact hi_le (s.gpr .rdx).isLt (word s.mem B (ec + 8 * j + 8 * k)).isLt e₁
  · rw [hg, k₄.gpr (by simp [Ne.symm d8]), e₃, hm₂]
  · refine ⟨fun r hr => ?_, hrd.trans (k₄.2.2.1.trans (k₃.2.2.1.trans (k₂.2.2.1.trans k₁.2.2.1))),
      hwr.trans (k₄.2.2.2.trans (k₃.2.2.2.trans (k₂.2.2.2.trans k₁.2.2.2)))⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hg, k₄.gpr (by simp [hr.2.2.2]), k₃.gpr (by simp [hr.2.2.1]), k₂.gpr (by simp [hr.2.1]),
      k₁.gpr (by simp [hr.1, hr.2.1])]

end VG.Proof.Bignum.X86_64.R2a
