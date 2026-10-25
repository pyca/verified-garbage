module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Mont.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# Montgomery arithmetic on PPC64LE: the parts of a row of the multiplication

`macs rs src rd dst k` adds `r9 · [rs + src]` (its low `k` words) and the
carry word `r0` to the words at `[r3 + rd]`, stored at `[r3 + dst]`, at or
below them, and leaves the carry word in `r0` (`macs_ok`). Around the steps,
the carry word added into the top two words of the accumulator (`topB_ok`),
the multiplier `q` of the modulus and its first step (`qStart_ok`), and the
carry word added into the top two words, stored one word down (`topQ_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont.PPC64LE VG.Proof.Mont

theorem wp_append {l₁ l₂ : List Instr} {s : State} {Q : State → Prop}
    (h : WP isa (.block l₁) s (fun s₁ => WP isa (.block l₂) s₁ Q)) : WP isa (.block (l₁ ++ l₂)) s Q :=
  WP.block_append h

theorem wordsVal_append (m : Mem) (base : Addr) (d j k : Nat) :
    wordsVal m base d (j + k) = wordsVal m base d j + 2 ^ (64 * j) * wordsVal m base (d + 8 * j) k := by
  induction j generalizing d with
  | zero => simp only [wordsVal, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero]
  | succ j ih =>
    rw [Nat.add_right_comm, wordsVal, ih, wordsVal, pow64_succ, show d + 8 + 8 * j = d + 8 * (j + 1) by omega_arith,
      Nat.mul_add, Nat.mul_assoc]
    omega_arith

/-- A word stored at `o` leaves the word at `d`, apart from it. -/
theorem word_writeW_ne {m : Mem} {base : Addr} {o d : Nat} (v : BitVec 64) (hsep : d + 8 ≤ o ∨ o + 8 ≤ d)
    (ho : o + 8 ≤ 2 ^ 64) (hd : d + 8 ≤ 2 ^ 64) : word (m.writeW (off base o) v) base d = word m base d :=
  (writeW_outside m base v ho).word (by omega_arith) hd

theorem macs_succ (rs : Reg) (src rd dst k : Nat) :
    macs rs src rd dst (k + 1) = macs rs src rd dst k ++ macStep rs src rd dst k := by
  simp only [macs, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The low `k` words of `[r3 + rd] + r9 · [rs + src] + r0` to `[r3 + dst]`
(`dst ≤ rd`, `[rs + src]` `K + src` bytes into the working space, apart
from the words written), the carry word to `r0`. -/
theorem macs_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {rs : Reg} {K src rd dst W : Nat}
    (hb : At s base rs K) (h3 : At s base .r3 0) (hrs : rs ∉ [.r0, .r10, .r11])
    (hsrc4 : src % 4 = 0) (hrd4 : rd % 4 = 0) (hdst4 : dst % 4 = 0)
    (hbW : K + src + 8 * W ≤ size) (hrdW : rd + 8 * W ≤ size) (hdW : dst + 8 * W ≤ size) (hle : dst ≤ rd)
    (hsep : K + src + 8 * W ≤ dst ∨ dst + 8 * W ≤ K + src) :
    ∀ {k : Nat}, k ≤ W →
    WP isa (.block (macs rs src rd dst k)) s fun u =>
      Outside base dst (8 * k) s.mem u.mem ∧
      wordsVal u.mem base dst k + 2 ^ (64 * k) * (u.gpr .r0).toNat =
        wordsVal s.mem base rd k + (s.gpr .r9).toNat * wordsVal s.mem base (K + src) k + (s.gpr .r0).toNat ∧
      Kp [.r0, .r10, .r11] s u
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, by simp [wordsVal], Kp.refl _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [macs_succ]
    refine wp_append (WP.mono (macs_ok hs hb h3 hrs hsrc4 hrd4 hdst4 hbW hrdW hdW hle hsep (k := k) (by omega_arith))
      fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    refine WP.mono (macStep_ok (K₁.ws hs) (K₁.at hb hrs) (K₁.at h3) hrs hsrc4 hrd4 hdst4 (j := k)
      (by omega_arith) (by omega_arith) (by omega_arith)) fun u ⟨lo, m₂, c₂, K₂⟩ => ?_
    rw [K₁.g (r := .r9)] at c₂
    have yk : word s₁.mem base (K + (src + 8 * k)) = word s.mem base (K + src + 8 * k) := by
      rw [← Nat.add_assoc]; exact O₁.word (by omega_arith) (by omega_arith)
    have tk : word s₁.mem base (rd + 8 * k) = word s.mem base (rd + 8 * k) := O₁.word (by omega_arith) (by omega_arith)
    rw [yk, tk] at c₂
    have W := writeW_outside s₁.mem base (d := dst + 8 * k) lo (by omega_arith)
    rw [← m₂] at W
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega_arith)).trans (W.mono (by omega_arith) (by omega_arith)), ?_, K₁.trans K₂⟩
    rw [wordsVal_succ_top, wordsVal_succ_top, wordsVal_succ_top, W.wordsVal (by omega_arith) (by omega_arith), m₂,
      word_writeW_self, pow64_succ]
    generalize 2 ^ (64 * k) = P at *
    have e := congrArg (P * ·) c₂
    simp only [Nat.mul_add] at e
    grind

/-- The carry word `r0` added to the word at `[r3 + d]`, the carry out to
`r12`. -/
theorem topB_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0) {d : Nat}
    (hd4 : d % 4 = 0) (hd : d + 8 ≤ size) :
    WP isa (.block [.load .d .r10 wb d, .addc .r10 .r10 .r0, .store .d .r10 wb d, .li .r12 0,
        .addze .r12 .r12]) s fun u =>
      Outside base d 8 s.mem u.mem ∧
      (word u.mem base d).toNat + 2 ^ 64 * (u.gpr .r12).toNat = (word s.mem base d).toNat + (s.gpr .r0).toNat ∧
      Kp [.r10, .r12] s u := by
  have hn := hs.nowrap
  have hs15 := hs.small
  refine wp_step (ld0_ok hs h3 (by decide) hd4 hd) ?_
  refine wp_step exec_addc ?_
  refine wp_step (std_ok ((hs.write _ _).writeCarry _ _) ((h3.write _).writeCarry _) (by decide) hd4 (d := d)
    (by omega_arith)) ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_addze (WP.block_nil ?_)
  simp only [write_gpr, writeCarry_gpr, write_mem, RegUpd.mem_writeCarry, RegUpd.ca_writeCarry, RegUpd.ca_write,
    reduceCtorEq, ite_false, ite_true, Nat.zero_add]
  refine ⟨writeW_outside _ base _ (by omega_arith), ?_, ?_⟩
  · rw [word_writeW_self]
    simp only [BitVec.toNat_ofNat]
    have := ca_split (v := (word s.mem base d).toNat + (s.gpr .r0).toNat)
      (by have := (word s.mem base d).isLt; have := (s.gpr .r0).isLt; omega_arith)
    generalize (decide (2 ^ 64 ≤ (word s.mem base d).toNat + (s.gpr .r0).toNat)).toNat = c at *
    omega_arith
  · refine ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, writeCarry_gpr, hr.1, hr.2, ite_false]

/-- `q = [r3 + a] · [r3 + mi] mod 2⁶⁴` to `r9`, and the first step of its
row: `[r3 + a] + q m₀` (`m₀` at `[r7]`), whose low word is dropped and high
word goes to `r0`. -/
theorem qStart_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {K a mi : Nat} (h7 : At s base .r7 K) (ha4 : a % 4 = 0) (hmi4 : mi % 4 = 0)
    (ha : a + 8 ≤ size) (hmi : mi + 8 ≤ size) (hK : K + 8 ≤ size) :
    WP isa (.block [.load .d .r11 wb a, .load .d .r10 wb mi, .mul .r9 .r11 .r10, .load .d .r10 .r7 0,
        .mulhu .r0 .r9 .r10, .mul .r10 .r9 .r10, .addc .r10 .r10 .r11, .addze .r0 .r0]) s fun u =>
      (u.gpr .r9).toNat = (word s.mem base a).toNat * (word s.mem base mi).toNat % 2 ^ 64 ∧
      (∃ lo, lo < 2 ^ 64 ∧ lo + 2 ^ 64 * (u.gpr .r0).toNat =
        (u.gpr .r9).toNat * (word s.mem base K).toNat + (word s.mem base a).toNat) ∧
      u.mem = s.mem ∧ Kp [.r0, .r9, .r10, .r11] s u := by
  have hs15 := hs.small
  refine wp_step (ld0_ok hs h3 (by decide) ha4 ha) ?_
  refine wp_step (ld0_ok (hs.write _ _) (h3.write _) (by decide) hmi4 hmi) ?_
  refine wp_step exec_mul ?_
  refine wp_step (ld_ok (((hs.write _ _).write _ _).write _ _) (((h7.write _).write _).write _) (by decide)
    (by decide) (d := 0) (by omega_arith)) ?_
  refine wp_step exec_mulhu ?_
  refine wp_step exec_mul ?_
  refine wp_step exec_addc ?_
  refine wp_step exec_addze (WP.block_nil ?_)
  simp only [write_gpr, writeCarry_gpr, write_mem, RegUpd.mem_writeCarry, RegUpd.ca_writeCarry,
    reduceCtorEq, ite_false, ite_true, Nat.add_zero, BitVec.toNat_mul]
  refine ⟨trivial, ?_, trivial, ?_⟩
  · generalize hq : (word s.mem base a).toNat * (word s.mem base mi).toNat % 2 ^ 64 = q
    generalize hm : word s.mem base K = m0
    generalize ht : word s.mem base a = t
    have hq64 : q < 2 ^ 64 := hq ▸ Nat.mod_lt _ (by decide)
    have hP : q * m0.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by have := m0.isLt; omega_arith)
    simp only [BitVec.toNat_ofNat]
    have := t.isLt
    have := ca_split (v := q * m0.toNat % 2 ^ 64 + t.toNat) (by omega_arith)
    generalize (decide (2 ^ 64 ≤ q * m0.toNat % 2 ^ 64 + t.toNat)).toNat = c at *
    refine ⟨(q * m0.toNat % 2 ^ 64 + t.toNat) % 2 ^ 64, Nat.mod_lt _ (by decide), ?_⟩
    omega_arith
  · refine ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, writeCarry_gpr, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- The carry word `r0` added to the word at `[r3 + f]` and the top word
`r12`, stored one word down (at `e = f - 8`), with the carry out in CA. -/
theorem topQ_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0) {e f : Nat}
    (hf : f = e + 8) (he4 : e % 4 = 0) (hd : f + 8 ≤ size) :
    WP isa (.block [.load .d .r10 wb f, .addc .r10 .r10 .r0, .store .d .r10 wb e, .addze .r12 .r12,
        .store .d .r12 wb f]) s fun u =>
      Outside base e 16 s.mem u.mem ∧
      (word u.mem base e).toNat + 2 ^ 64 * (word u.mem base f).toNat + 2 ^ 128 * u.ca.toNat =
        (word s.mem base f).toNat + 2 ^ 64 * (s.gpr .r12).toNat + (s.gpr .r0).toNat ∧
      Kp [.r10, .r12] s u := by
  subst hf
  have hn := hs.nowrap
  have hs15 := hs.small
  refine wp_step (ld0_ok hs h3 (by decide) (by omega_arith) (by omega_arith)) ?_
  refine wp_step exec_addc ?_
  refine wp_step (std_ok ((hs.write _ _).writeCarry _ _) ((h3.write _).writeCarry _) (by decide) he4 (d := e)
    (by omega_arith)) ?_
  refine wp_step exec_addze ?_
  refine wp_step (std_ok ((((hs.write _ _).writeCarry _ _).store _).writeCarry _ _)
    ((((h3.write _).writeCarry _).store _).writeCarry _) (by decide) (by omega_arith) (d := e + 8)
    (by omega_arith)) (WP.block_nil ?_)
  simp only [write_gpr, writeCarry_gpr, write_mem, RegUpd.mem_writeCarry, RegUpd.ca_writeCarry,
    reduceCtorEq, ite_false, ite_true, Nat.zero_add]
  generalize hv : (word s.mem base (e + 8)).toNat + (s.gpr .r0).toNat = v
  have W₀ := writeW_outside s.mem base (d := e) (BitVec.ofNat 64 v) (by omega_arith)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [(writeW_outside _ base _ (by omega_arith)) x (by omega_arith), W₀ x (by omega_arith)]
  · rw [word_writeW_ne _ (by omega_arith) (by omega_arith) (by omega_arith), word_writeW_self, word_writeW_self]
    simp only [BitVec.toNat_ofNat]
    have h1 := ca_split (v := v) (by have := (word s.mem base (e + 8)).isLt; have := (s.gpr .r0).isLt; omega_arith)
    generalize (decide (2 ^ 64 ≤ v)).toNat = c at *
    have := (s.gpr .r12).isLt
    have h2 := ca_split (v := (s.gpr .r12).toNat + c) (by omega_arith)
    generalize (decide (2 ^ 64 ≤ (s.gpr .r12).toNat + c)).toNat = c' at *
    omega_arith
  · refine ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, writeCarry_gpr, hr.1, hr.2, ite_false]

end VG.Proof.Mont.PPC64LE
