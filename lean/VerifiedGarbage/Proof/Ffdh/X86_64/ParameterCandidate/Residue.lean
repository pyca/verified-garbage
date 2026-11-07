module

public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Residue
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.ModE
import VerifiedGarbage.Proof.Bignum.X86_64.Row
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual

/-! # FFDH parameter candidates on x86-64: exact small remainders -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Proof.RsaKeyGen.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- An addition whose carry is added back: congruent modulo 2^64 − 1. -/
theorem endAround_bv (a b : BitVec 64) :
    (a + b + BitVec.signExtend 64 (0 : BitVec 32) +
      (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64).toNat % (2 ^ 64 - 1) =
      (a.toNat + b.toNat) % (2 ^ 64 - 1) := by
  have ha := a.isLt
  have hb := b.isLt
  rw [show BitVec.signExtend 64 (0 : BitVec 32) = 0#64 from by decide, BitVec.add_zero]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat
  · simp only [h, decide_true, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool,
      Bool.toNat_true]
    omega
  · simp only [h, decide_false, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool,
      Bool.toNat_false]
    omega

/-- One word of `fold`: word `w − 1 − j` into RSI, modulo 2^64 − 1. -/
theorem foldWord_ok {s : State} {B : Addr} {Z d w j : Nat} (hs : Scr s B Z) (h8 : s.gpr .r8 = off B d)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h14 : s.gpr .r14 = BitVec.ofNat 64 j) (hj : j < w)
    (hd : d + 8 * w ≤ Z) :
    WP isa (.block foldWord) s fun t =>
      (t.gpr .rsi).toNat % (2 ^ 64 - 1) =
        ((s.gpr .rsi).toNat + (word s.mem B (d + 8 * (w - 1 - j))).toNat) % (2 ^ 64 - 1) ∧
      t.mem = s.mem ∧ Keep [.rax, .rsi] s t := by
  have hn := hs.nowrap
  have hix : s.gpr .r12 - 1 - s.gpr .r14 = BitVec.ofNat 64 (w - 1 - j) := by
    rw [h12, h14]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have : (1 : BitVec 64).toNat = 1 := rfl
    rw [this]; omega_arith
  refine WP.mono (WP.keep [.rax, .rsi] (Q := fun t =>
    (t.gpr .rsi).toNat % (2 ^ 64 - 1) =
        ((s.gpr .rsi).toNat + (word s.mem B (d + 8 * (w - 1 - j))).toNat) % (2 ^ 64 - 1) ∧
      t.mem = s.mem) ?_ rfl) fun t ⟨⟨h, hm⟩, k⟩ => ⟨h, hm, k⟩
  unfold foldWord
  xrun [State.ea, ix, addr0 h8 hix, hs.ld (show d + 8 * (w - 1 - j) + 8 ≤ Z by omega_arith), sx_ofNat]
  exact endAround_bv _ _

/-- After `j` words of `fold`. -/
structure FoldInv (s₀ : State) (B : Addr) (d w : Nat) (j : Nat) (t : State) : Prop where
  val : (t.gpr .rsi).toNat % (2 ^ 64 - 1) = hiw s₀.mem B d w (w - j) % (2 ^ 64 - 1)
  mem : t.mem = s₀.mem
  r8 : t.gpr .r8 = s₀.gpr .r8
  r12 : t.gpr .r12 = s₀.gpr .r12
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  keep : Keep [.rax, .rsi, .r14] s₀ t

/-- The words of the number at `d` into RSI = 0, modulo 2^64 − 1. -/
theorem foldWords_ok {s : State} {B : Addr} {Z d w : Nat} (hs : Scr s B Z) (h8 : s.gpr .r8 = off B d)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h14 : s.gpr .r14 = BitVec.ofNat 64 0) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hd : d + 8 * w ≤ Z) (hsi : s.gpr .rsi = 0) :
    WP isa (.loop (.seq (.block foldWord) (.block [.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)])) .ne)
      s fun t => (t.gpr .rsi).toNat % (2 ^ 64 - 1) = wv s.mem B d w % (2 ^ 64 - 1) ∧ t.mem = s.mem ∧
        Keep [.rax, .rsi, .r14] s t := by
  refine wp_upto (a := 0) (N := w) (by omega_using [hw]) (FoldInv s B d w) ?_
    (fun t hI => ⟨?_, hI.mem, hI.keep⟩)
    ⟨by rw [hsi, Nat.sub_zero]; unfold hiw; rw [Nat.sub_self]; simp [wv], rfl, rfl, rfl, h14,
      Keep.refl _ _⟩
  · intro j _ hj t hI
    refine WP.seq (WP.mono (foldWord_ok (hs.congr hI.keep.2.2) (hI.r8.trans h8) (hI.r12.trans h12)
      hI.r14 hj hd) fun t₁ ⟨h1, hm₁, k₁⟩ => ?_)
    refine WP.mono (count_ok t₁ ((k₁.gpr (by decide)).trans hI.r14)
      ((k₁.gpr (by decide)).trans (hI.r12.trans h12)) (by omega_using [hw', hj]) (by omega_using [hw']))
      fun t' ⟨hz, h14', hm', k'⟩ => ⟨hz, ⟨?_, by rw [hm', hm₁, hI.mem],
        (k'.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hI.r8),
        (k'.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hI.r12), h14',
        ((hI.keep.trans k₁).trans k').mono (by decide)⟩⟩
    rw [k'.gpr (by decide), h1, hI.mem, Nat.add_mod, hI.val, ← Nat.add_mod,
      hiw_step s.mem B d w (w - (j + 1)) (by omega_using [hj]),
      show w - (j + 1) + 1 = w - j by omega_using [hj], show w - 1 - j = w - (j + 1) by omega_using []]
    generalize hiw s.mem B d w (w - j) = H
    generalize (word s.mem B (d + 8 * (w - (j + 1)))).toNat = W
    omega
  · rw [hI.val, Nat.sub_self]; unfold hiw; simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero]

/-! ## Membership of a small remainder -/

theorem memberStep_ok {s : State} {r v : Nat} {acc : Bool} (hr : r < 2 ^ 31) (hv : v < 2 ^ 31)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 r) (hcx : s.gpr .rcx = 1)
    (hax : s.gpr .rax = if acc then 1 else 0) :
    WP isa (.block (memberStep v)) s fun t =>
      (t.gpr .rax = if (acc || decide (r = v)) then 1 else 0) ∧ t.gpr .rsi = s.gpr .rsi ∧
        t.gpr .rcx = s.gpr .rcx ∧ t.mem = s.mem ∧ Keep [.rsi, .rax] s t := by
  refine WP.mono (WP.keep [.rsi, .rax] (Q := fun t =>
    (t.gpr .rax = if (acc || decide (r = v)) then 1 else 0) ∧ t.gpr .rsi = s.gpr .rsi ∧
      t.gpr .rcx = s.gpr .rcx ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨ha, hs, hc, hm⟩, k⟩ => ⟨ha, hs, hc, hm, k.mono (by decide)⟩
  have hz := ofNat_sub_beq (j := r) (N := v) (by omega_arith) (by omega_arith)
  unfold memberStep
  by_cases h : r = v
  · xrun [hsi, hcx, hax, sx_ofNat hv, hz, h, execCmov, eval]
    cases acc <;> simp
  · xrun [hsi, hcx, hax, sx_ofNat hv, hz, h, execCmov, eval]
    cases acc <;> simp

theorem memberSteps_ok {r : Nat} (hr : r < 2 ^ 31) :
    ∀ (vals : List Nat) (_ : ∀ v ∈ vals, v < 2 ^ 31) {acc : Bool} {s : State}
      (_ : s.gpr .rsi = BitVec.ofNat 64 r) (_ : s.gpr .rcx = 1) (_ : s.gpr .rax = if acc then 1 else 0),
      WP isa (.block (vals.flatMap memberStep)) s fun t =>
        (t.gpr .rax = if (acc || decide (r ∈ vals)) then 1 else 0) ∧ t.gpr .rsi = s.gpr .rsi ∧
          t.gpr .rcx = s.gpr .rcx ∧ t.mem = s.mem ∧ Keep [.rsi, .rax] s t
  | [], _, acc, s, _, _, hax => WP.block_nil ⟨by simpa using hax, rfl, rfl, rfl, Keep.refl _ _⟩
  | v :: vs, hvals, acc, s, hsi, hcx, hax => by
    rw [List.flatMap_cons]
    refine WP.block_append (WP.mono (memberStep_ok hr (hvals v (by simp)) hsi hcx hax)
      fun u ⟨hu, hus, huc, hum, k⟩ => ?_)
    refine WP.mono (memberSteps_ok hr vs (fun w hw => hvals w (by simp [hw])) (hus.trans hsi)
      (huc.trans hcx) hu) fun t ⟨ht, hts, htc, htm, k'⟩ => ?_
    refine ⟨?_, hts.trans hus, htc.trans huc, htm.trans hum, (k.trans k').mono (by decide)⟩
    rw [ht]
    by_cases h1 : r = v <;> by_cases h2 : r ∈ vs <;> cases acc <;> simp [h1, h2]

/-- `memberFlag vals`: RAX is 1 if the remainder in RSI is one of `vals`, else 0. -/
theorem memberFlag_ok {s : State} {r : Nat} {vals : List Nat} (hr : r < 2 ^ 31)
    (hvals : ∀ v ∈ vals, v < 2 ^ 31) (hsi : s.gpr .rsi = BitVec.ofNat 64 r) :
    WP isa (.block (memberFlag vals)) s fun t =>
      (t.gpr .rax = if decide (r ∈ vals) then 1 else 0) ∧ t.mem = s.mem ∧ Keep [.rsi, .rax, .rcx] s t := by
  unfold memberFlag
  refine WP.block_append ?_
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun u => u.gpr .rax = (if false then 1 else 0) ∧
    u.gpr .rcx = 1 ∧ u.gpr .rsi = s.gpr .rsi ∧ u.mem = s.mem) (by xrun) rfl)
    fun u ⟨⟨hua, huc, hus, hum⟩, k⟩ => ?_
  refine WP.mono (memberSteps_ok hr vals hvals (hus.trans hsi) huc hua)
    fun v ⟨hva, _, _, hvm, k'⟩ => ⟨by simpa only [Bool.false_or] using hva, hvm.trans hum,
      (k.trans k').mono (by decide)⟩

private theorem and_mask (x : BitVec 64) (k : Nat) (hk : k < 31) :
    (x &&& BitVec.signExtend 64 (BitVec.ofNat 32 (2 ^ k - 1))).toNat = x.toNat % 2 ^ k := by
  have h1 : 2 ^ k - 1 < 2 ^ 31 := by
    have := Nat.pow_lt_pow_right (a := 2) (by decide) hk; omega
  rw [sx_ofNat h1, BitVec.toNat_and, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have : (2 : Nat) ^ 31 < 2 ^ 64 := by decide
                         omega),
    Nat.and_two_pow_sub_one_eq_mod]

/-- `lowCheck (2 ^ k - 1)`: ZF is whether RAX is 1 and the low word at R8 is 3
modulo `2 ^ k`. -/
theorem lowCheck_ok {s : State} {b : Bool} (k : Nat) (hk : 2 ≤ k) (hk' : k < 31)
    (hrd : InRegions (s.rd ++ s.wr) (s.gpr .r8) 8) (hax : s.gpr .rax = if b then 1 else 0) :
    WP isa (.block (lowCheck (2 ^ k - 1))) s fun t =>
      t.zf = some (b && decide ((s.mem.readW (s.gpr .r8) 64).toNat % 2 ^ k = 3)) ∧ t.mem = s.mem ∧
        Keep [.rax, .rcx, .rdx] s t := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t =>
    t.zf = some (b && decide ((s.mem.readW (s.gpr .r8) 64).toNat % 2 ^ k = 3)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hz, hm⟩, kk⟩ => ⟨hz, hm, kk⟩
  have h4 : 4 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) hk; simpa using this
  have hlow : ((s.mem.readW (s.gpr .r8) 64 &&& BitVec.signExtend 64 (BitVec.ofNat 32 (2 ^ k - 1))) -
      (3 : BitVec 64) == 0) = decide ((s.mem.readW (s.gpr .r8) 64).toNat % 2 ^ k = 3) := by
    rw [sub_beq_zero]
    by_cases h : (s.mem.readW (s.gpr .r8) 64).toNat % 2 ^ k = 3
    · simp only [h, decide_true, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq; rw [and_mask _ _ hk', h]; rfl
    · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro he; apply h; rw [← and_mask _ _ hk', he]; rfl
  unfold lowCheck
  cases b <;> by_cases h : (s.mem.readW (s.gpr .r8) 64).toNat % 2 ^ k = 3 <;>
    xrun [State.ea, at0, hrd, hax, sx_ofNat (show 3 < 2 ^ 31 by decide), hlow, h, execCmov, eval,
      BitVec.add_zero, show BitVec.ofInt 64 0 = 0#64 from rfl, Bool.not_true, Bool.not_false]

/-- One `foldStep k`: RSI := RSI mod 2^k + RSI / 2^k. -/
theorem foldStep_ok (k : Nat) (hk : k = 8 ∨ k = 16 ∨ k = 32) (s : State) :
    WP isa (.block (foldStep k)) s fun t =>
      (t.gpr .rsi).toNat = (s.gpr .rsi).toNat % 2 ^ k + (s.gpr .rsi).toNat / 2 ^ k ∧ t.mem = s.mem ∧
        Keep [.rdx, .rsi] s t := by
  refine WP.mono (WP.keep [.rdx, .rsi] (Q := fun t =>
    (t.gpr .rsi).toNat = (s.gpr .rsi).toNat % 2 ^ k + (s.gpr .rsi).toNat / 2 ^ k ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨h, hm⟩, kk⟩ => ⟨h, hm, kk⟩
  have hx := (s.gpr .rsi).isLt
  unfold foldStep
  rcases hk with rfl | rfl | rfl <;> xrun <;>
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow] <;> omega

/-- `reduce255`: RSI := RSI mod 255. -/
theorem reduce255_ok (s : State) :
    WP isa (.block reduce255) s fun t => (t.gpr .rsi).toNat = (s.gpr .rsi).toNat % 255 ∧ t.mem = s.mem ∧
      Keep [.rdx, .rsi] s t := by
  have hx := (s.gpr .rsi).isLt
  unfold reduce255
  refine WP.block_append (WP.block_append (WP.block_append (WP.block_append
    (WP.mono (foldStep_ok 32 (by decide) s) fun u₁ ⟨h₁, m₁, k₁⟩ => ?_) ) ) )
  refine WP.mono (foldStep_ok 16 (by decide) u₁) fun u₂ ⟨h₂, m₂, k₂⟩ => ?_
  refine WP.mono (foldStep_ok 8 (by decide) u₂) fun u₃ ⟨h₃, m₃, k₃⟩ => ?_
  refine WP.mono (foldStep_ok 8 (by decide) u₃) fun u₄ ⟨h₄, m₄, k₄⟩ => ?_
  have hv : (u₄.gpr .rsi).toNat % 255 = (s.gpr .rsi).toNat % 255 ∧ (u₄.gpr .rsi).toNat < 264 := by
    rw [h₄, h₃, h₂, h₁]
    generalize (s.gpr .rsi).toNat = x at hx ⊢
    omega
  refine WP.mono (WP.keep [.rdx, .rsi] (Q := fun t =>
    (t.gpr .rsi).toNat = (s.gpr .rsi).toNat % 255 ∧ t.mem = u₄.mem) ?_ rfl)
    fun t ⟨⟨h, hm⟩, kk⟩ => ⟨h, hm.trans (m₄.trans (m₃.trans (m₂.trans m₁))),
      ((((k₁.trans k₂).trans k₃).trans k₄).trans kk).mono (by decide)⟩
  obtain ⟨hmod, hlt⟩ := hv
  have h255 : BitVec.signExtend 64 (255 : BitVec 32) = BitVec.ofNat 64 255 := by decide
  have hy := (u₄.gpr .rsi).isLt
  have hc : (BitVec.ofNat 64 255).toNat = 255 := rfl
  generalize hu : u₄.gpr .rsi = y at hmod hlt hy
  by_cases h : y.toNat < 255
  · have hd : decide (y.toNat < (BitVec.ofNat 64 255).toNat) = true := by rw [hc]; exact decide_eq_true h
    xrun [hu, h255, execCmov, eval, hd]
    omega
  · have hd : decide (y.toNat < (BitVec.ofNat 64 255).toNat) = false := by rw [hc]; exact decide_eq_false h
    xrun [hu, h255, execCmov, eval, hd]
    rw [BitVec.toNat_sub, hc]
    omega

/-- The candidate in aN, its words folded modulo 2^64 − 1, in RSI; R8 is
aN's base. -/
theorem fold_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa fold s fun t =>
      (t.gpr .rsi).toNat % (2 ^ 64 - 1) = wv s.mem B (slot w aN) w % (2 ^ 64 - 1) ∧
        t.gpr .r8 = off B (slot w aN) ∧ t.mem = s.mem ∧ Keep [.r12, .r8, .rsi, .r14, .rax] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  unfold fold
  refine WP.seq (WP.mono (WP.keep [.r12, .r8, .rsi, .r14]
    (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B (slot w aN) ∧ t.gpr .rsi = 0 ∧ t.gpr .r14 = BitVec.ofNat 64 0 ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide), hg.hdr.hw,
      hg.hdr.harr aN (by decide)]) rfl) fun u ⟨⟨h12, h8, hsi, h14, hm⟩, k⟩ => ?_)
  refine WP.mono (foldWords_ok (hg.scr.congr k.2.2) h8 h12 h14 hw hw'
    (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith) hsi)
    fun v ⟨hv, hvm, kv⟩ => ⟨by rw [hv, hm], by rw [kv.gpr (by decide), h8], hvm.trans hm,
      (k.trans kv).mono (by decide)⟩

/-! ## The generators' congruences, with the small primes of p and q -/

/-- What the generator check accepts: p ≡ 3 mod 8 and `allowed2` modulo 255,
or p ≡ 3 mod 4 and `allowed5` modulo 255. -/
def screen (generator p : Nat) : Bool :=
  if generator = 2 then decide (p % 8 = 3) && decide (p % 255 ∈ allowed2)
  else decide (p % 4 = 3) && decide (p % 255 ∈ allowed5)

theorem allowed2_lt : ∀ v ∈ allowed2, v < 2 ^ 31 := by decide +kernel
theorem allowed5_lt : ∀ v ∈ allowed5, v < 2 ^ 31 := by decide +kernel

private theorem low_mod {m : Mem} {p : Addr} {d n k : Nat} (hn : 1 ≤ n) (hk : k ≤ 64) :
    (m.readW (off p d) 64).toNat % 2 ^ k = wv m p d n % 2 ^ k := by
  obtain ⟨n, rfl⟩ : ∃ n', n = 1 + n' := ⟨n - 1, by omega⟩
  rw [wv_add]
  simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.mul_one]
  have hd : 2 ^ k ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 hk
  obtain ⟨c, hc⟩ := hd
  rw [hc, Nat.mul_assoc, Nat.add_mul_mod_self_left]

theorem generatorCode_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {vals : List Nat} {k : Nat}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hvals : ∀ v ∈ vals, v < 2 ^ 31) (hk : 2 ≤ k) (hk' : k < 31) :
    WP isa (.seq fold (.block (reduce255 ++ memberFlag vals ++ lowCheck (2 ^ k - 1)))) s fun t =>
      t.zf = some (decide (wv s.mem B (slot w aN) w % 255 ∈ vals) &&
        decide (wv s.mem B (slot w aN) w % 2 ^ k = 3)) ∧
      t.mem = s.mem ∧ Keep [.rbx, .r12, .r8, .rsi, .r14, .rax, .rcx, .rdx, .rbp, .r13] s t := by
  refine WP.seq (WP.mono (fold_ok hg hZ hw hw') fun u₀ ⟨hv₀, h8₀, hm₀, k₀⟩ => ?_)
  refine WP.block_append (WP.block_append (WP.mono (reduce255_ok u₀) fun u ⟨hv', hm', k'⟩ => ?_))
  have hv : (u.gpr .rsi).toNat = wv s.mem B (slot w aN) w % 255 := by
    rw [hv', ← Nat.mod_mod_of_dvd _ (show 255 ∣ 2 ^ 64 - 1 by decide), hv₀,
      Nat.mod_mod_of_dvd _ (show 255 ∣ 2 ^ 64 - 1 by decide)]
  have h8 : u.gpr .r8 = off B (slot w aN) := (k'.gpr (by decide)).trans h8₀
  have hm : u.mem = s.mem := hm'.trans hm₀
  have k₁ : Keep [.rbx, .r12, .r8, .rsi, .r14, .rax, .rcx, .rdx, .rbp, .r13] s u :=
    (k₀.trans k').mono (by decide)
  have hsi : u.gpr .rsi = BitVec.ofNat 64 (wv s.mem B (slot w aN) w % 255) := by
    rw [← hv, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (memberFlag_ok (by omega_arith) hvals hsi) fun v ⟨hva, hvm, kv⟩ => ?_
  have hrd : InRegions (v.rd ++ v.wr) (v.gpr .r8) 8 := by
    rw [kv.gpr (by decide), h8, kv.2.1, kv.2.2, k₁.2.1, k₁.2.2]
    exact hg.scr.ld (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith)
  refine WP.mono (lowCheck_ok k hk hk' hrd hva) fun t ⟨hz, htm, kt⟩ =>
    ⟨?_, htm.trans (hvm.trans hm), ((k₁.trans kv).trans kt).mono (by decide)⟩
  rw [hz, kv.gpr (by decide), h8, hvm, hm, low_mod hw (by omega)]

private theorem allowed2_shape : ∀ r < 255, r ∈ allowed2 → r % 3 = 2 := by decide +kernel
private theorem allowed5_shape : ∀ r < 255, r ∈ allowed5 → r % 5 = 2 ∨ r % 5 = 3 := by decide +kernel

/-- The accepted remainders have the generator's congruence. -/
theorem screen_shape {bits generator p : Nat} (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192)
    (hbits : Spec.RsaKeyGen.bitLength p = bits) (hgen : generator = 2 ∨ generator = 5) :
    (Spec.Ffdh.generationShape bits generator p && screen generator p) = screen generator p := by
  rcases hgen with rfl | rfl
  · by_cases h : p % 8 = 3 ∧ p % 255 ∈ allowed2
    · have h3 := allowed2_shape _ (Nat.mod_lt _ (by decide)) h.2
      have : p % 24 = 11 := by have := Nat.mod_mod_of_dvd p (show 3 ∣ 255 by decide); omega
      simp [Spec.Ffdh.generationShape, screen, hb1, hb2, hbits, h.1, h.2, this]
    · have : screen 2 p = false := by
        simp only [screen, ite_true, Bool.and_eq_false_iff, decide_eq_false_iff_not]
        by_cases h1 : p % 8 = 3
        · exact Or.inr fun h2 => h ⟨h1, h2⟩
        · exact Or.inl h1
      rw [this, Bool.and_false]
  · by_cases h : p % 4 = 3 ∧ p % 255 ∈ allowed5
    · have h5 := allowed5_shape _ (Nat.mod_lt _ (by decide)) h.2
      have : p % 10 = 3 ∨ p % 10 = 7 := by have := Nat.mod_mod_of_dvd p (show 5 ∣ 255 by decide); omega
      simp [Spec.Ffdh.generationShape, screen, hb1, hb2, hbits, h.1, h.2, this]
    · have : screen 5 p = false := by
        simp only [screen, show (5 : Nat) ≠ 2 from by decide, ite_false, Bool.and_eq_false_iff,
          decide_eq_false_iff_not]
        by_cases h1 : p % 4 = 3
        · exact Or.inr fun h2 => h ⟨h1, h2⟩
        · exact Or.inl h1
      rw [this, Bool.and_false]

/-- The public generator selector implements `screen`, after the candidate's exact-width proof. -/
theorem generatorCheck_ok {s : State} {B : Addr} {Z w bits generator : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192)
    (hbits : Spec.RsaKeyGen.bitLength (wv s.mem B (slot w aN) w) = bits)
    (hgen : generator = 2 ∨ generator = 5) (hreg : s.gpr .rdx = BitVec.ofNat 64 generator) :
    WP isa generatorCheck s fun t => t.zf = some (Spec.Ffdh.generationShape bits generator
        (wv s.mem B (slot w aN) w) && screen generator (wv s.mem B (slot w aN) w)) ∧
      t.mem = s.mem ∧ Keep [.rbx, .r12, .r8, .rsi, .r14, .rax, .rcx, .rdx, .rbp, .r13] s t := by
  rw [screen_shape hb1 hb2 hbits hgen]
  rcases hgen with rfl | rfl
  · unfold generatorCheck
    refine WP.seq (WP.mono (WP.keep [.rdx] (Q := fun u => u.zf = some true ∧ u.mem = s.mem)
      (by xrun [hreg]) rfl) fun u ⟨⟨hz, hm⟩, k⟩ => ?_)
    have hgu : Good u B Z w minv := ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
      by rw [hm]; exact hg.hdr⟩
    refine WP.ite true (by simp [eval, hz]) ?_ (fun h => by simp at h)
    intro _
    exact WP.mono (generatorCode_ok (k := 3) hgu hZ hw hw' allowed2_lt (by decide) (by decide))
      fun t ⟨hz', hm', k'⟩ =>
      ⟨by rw [hz', hm]; simp only [screen, ite_true, Bool.and_comm, show (2 : Nat) ^ 3 = 8 from rfl], hm'.trans hm,
        (k.trans k').mono (by decide)⟩
  · unfold generatorCheck
    refine WP.seq (WP.mono (WP.keep [.rdx] (Q := fun u => u.zf = some false ∧ u.mem = s.mem)
      (by xrun [hreg]) rfl) fun u ⟨⟨hz, hm⟩, k⟩ => ?_)
    have hgu : Good u B Z w minv := ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
      by rw [hm]; exact hg.hdr⟩
    refine WP.ite false (by simp [eval, hz]) (fun h => by simp at h) ?_
    intro _
    exact WP.mono (generatorCode_ok (k := 2) hgu hZ hw hw' allowed5_lt (by decide) (by decide))
      fun t ⟨hz', hm', k'⟩ =>
      ⟨by rw [hz', hm]; simp only [screen, show (5 : Nat) ≠ 2 from by decide, ite_false, Bool.and_comm,
          show (2 : Nat) ^ 2 = 4 from rfl],
        hm'.trans hm, (k.trans k').mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
