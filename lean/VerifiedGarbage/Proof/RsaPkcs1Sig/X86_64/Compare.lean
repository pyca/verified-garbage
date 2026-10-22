module

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Encode
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Ct.Common
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Encode

/-!
# Comparing two buffers on x86-64

`compare_ok`: `compare` leaves 0 in `rdx` exactly when the `n` bytes at
`rdi` and `rsi` are equal, and changes neither memory nor any register but
`rax`, `rdx`, `r10` and `r11`. A multiple of 8 bytes is compared a word at a
time (`word_step`), any other length a byte at a time (`compare_step`),
where `rdx` is the OR of the differences (`Proof.Ct.diff`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.Ct

/-- The registers `compare` writes. -/
def cmpClob : List Reg := [.rax, .rdx, .r10, .r11]

/-- The `n` bytes at `a` and `b` are equal. -/
def EqBytes (m : Mem) (a b : Addr) (n : Nat) : Prop :=
  ∀ i < n, m (a + BitVec.ofNat 64 i) = m (b + BitVec.ofNat 64 i)

/-- After `i` bytes. -/
def CInv (s₀ : State) (i : Nat) (s : State) : Prop :=
  Keep cmpClob s₀ s ∧ s.mem = s₀.mem ∧ s.gpr .r11 = BitVec.ofNat 64 i ∧
    s.gpr .rdx = (diff s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi) i).setWidth 64

/-- After `j` words. -/
def WInv (s₀ : State) (j : Nat) (s : State) : Prop :=
  Keep cmpClob s₀ s ∧ s.mem = s₀.mem ∧ s.gpr .r11 = BitVec.ofNat 64 (8 * j) ∧
    (s.gpr .rdx = 0 ↔ EqBytes s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi) (8 * j))

theorem ea_ix (s : State) (b i : Reg) :
    s.ea { base := b, index := some i } = s.gpr b + s.gpr i := by
  simp [State.ea]

theorem setWidth_byte_eq_zero' (d : Byte) : d.setWidth 64 = 0 ↔ d = 0 := by
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq; have := congrArg BitVec.toNat h; have := d.isLt; simp at *; omega
  · rintro rfl; rfl

theorem or_eq_zero64 {x y : BitVec 64} : x ||| y = 0 ↔ x = 0 ∧ y = 0 := BitVec.or_eq_zero_iff

theorem xor_eq_zero64 {x y : BitVec 64} : x ^^^ y = 0 ↔ x = y := BitVec.xor_eq_zero_iff

theorem readW64_eq_iff (m : Mem) (a b : Addr) :
    m.readW a 64 = m.readW b 64 ↔ EqBytes m a b 8 := by
  have e : ∀ c, (m.readW c 64).toNat = (m.read c 8).toNat := fun c => by
    simp only [Mem.readW, BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (m.read c 8).isLt
  rw [← BitVec.toNat_inj, e, e, BitVec.toNat_inj]
  constructor
  · intro h i hi; rw [← Mem.extractLsb'_read m a hi, ← Mem.extractLsb'_read m b hi, h]
  · intro h; exact Mem.read_eq_of_bytes fun i hi => by rw [h i hi, Mem.extractLsb'_read m b hi]

theorem eqBytes_succ8 (m : Mem) (a b : Addr) (j : Nat) :
    EqBytes m a b (8 * (j + 1)) ↔
      EqBytes m a b (8 * j) ∧ EqBytes m (a + BitVec.ofNat 64 (8 * j)) (b + BitVec.ofNat 64 (8 * j)) 8 := by
  have hc : ∀ (c : Addr) i, c + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 i = c + BitVec.ofNat 64 (8 * j + i) :=
    fun c i => by rw [BitVec.add_assoc, BitVec.ofNat_add]
  simp only [EqBytes, hc]
  constructor
  · intro h; exact ⟨fun i hi => h i (by omega), fun i hi => h _ (by omega)⟩
  · intro ⟨h₁, h₂⟩ i hi
    by_cases hl : i < 8 * j
    · exact h₁ i hl
    · have := h₂ (i - 8 * j) (by omega); rwa [Nat.add_sub_cancel' (by omega)] at this

theorem compare_step {s₀ s : State} {n : Nat}
    (hr : ∀ i < n, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi + BitVec.ofNat 64 i) 1 ∧
      InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 i) 1)
    (i : Nat) (hi : i < n) (h : CInv s₀ i s) :
    WP isa (.block cmpByte) s fun t =>
      CInv s₀ (i + 1) t ∧ t.zf = some (BitVec.ofNat 64 (i + 1) == s₀.gpr .rcx) := by
  obtain ⟨hk, hm, hx, ha⟩ := h
  have hdi := hk.gpr (r := .rdi) (by decide)
  have hsi := hk.gpr (r := .rsi) (by decide)
  have hcx := hk.gpr (r := .rcx) (by decide)
  have hA : InRegions (s.rd ++ s.wr) (s₀.gpr .rdi + BitVec.ofNat 64 i) 1 := by
    rw [hk.2.1, hk.2.2]; exact (hr i hi).1
  have hB : InRegions (s.rd ++ s.wr) (s₀.gpr .rsi + BitVec.ofNat 64 i) 1 := by
    rw [hk.2.1, hk.2.2]; exact (hr i hi).2
  have hadd : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
    rw [BitVec.ofNat_add]; rfl
  refine WP.mono (WP.keep cmpClob (Q := fun t => t.mem = s₀.mem ∧
      t.gpr .r11 = BitVec.ofNat 64 (i + 1) ∧
      t.gpr .rdx = (diff s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi) (i + 1)).setWidth 64 ∧
      t.zf = some (BitVec.ofNat 64 (i + 1) == s₀.gpr .rcx)) ?_ (by rfl)) ?_
  · xrun [cmpByte, ea_ix, hA, hB, hm, ha, hx, hdi, hsi, hcx, hadd, sub_beq64, ← BitVec.setWidth_xor,
      ← BitVec.setWidth_or, diff]
  · intro t ⟨⟨hm', hx', ha', hz⟩, hk'⟩
    exact ⟨⟨(hk.trans hk').mono (by simp [cmpClob]), hm', hx', ha'⟩, hz⟩

theorem word_step {s₀ s : State} {n : Nat}
    (hr : ∀ j, 8 * j < n → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi + BitVec.ofNat 64 (8 * j)) 8 ∧
      InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 (8 * j)) 8)
    (j : Nat) (hj : 8 * j < n) (h : WInv s₀ j s) :
    WP isa (.block cmpWord) s fun t =>
      WInv s₀ (j + 1) t ∧ t.zf = some (BitVec.ofNat 64 (8 * (j + 1)) == s₀.gpr .rcx) := by
  obtain ⟨hk, hm, hx, ha⟩ := h
  have hdi := hk.gpr (r := .rdi) (by decide)
  have hsi := hk.gpr (r := .rsi) (by decide)
  have hcx := hk.gpr (r := .rcx) (by decide)
  have hA : InRegions (s.rd ++ s.wr) (s₀.gpr .rdi + BitVec.ofNat 64 (8 * j)) 8 := by
    rw [hk.2.1, hk.2.2]; exact (hr j hj).1
  have hB : InRegions (s.rd ++ s.wr) (s₀.gpr .rsi + BitVec.ofNat 64 (8 * j)) 8 := by
    rw [hk.2.1, hk.2.2]; exact (hr j hj).2
  have hadd : BitVec.ofNat 64 (8 * j) + 8 = BitVec.ofNat 64 (8 * (j + 1)) := by
    rw [Nat.mul_succ, BitVec.ofNat_add]; rfl
  refine WP.mono (WP.keep cmpClob (Q := fun t => t.mem = s₀.mem ∧
      t.gpr .r11 = BitVec.ofNat 64 (8 * (j + 1)) ∧
      t.gpr .rdx = s.gpr .rdx ||| (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (8 * j)) 64 ^^^
        s₀.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * j)) 64) ∧
      t.zf = some (BitVec.ofNat 64 (8 * (j + 1)) == s₀.gpr .rcx)) ?_ (by rfl)) ?_
  · xrun [cmpWord, ea_ix, hA, hB, hm, hx, hdi, hsi, hcx, hadd, sub_beq64]
  · intro t ⟨⟨hm', hx', ha', hz⟩, hk'⟩
    refine ⟨⟨(hk.trans hk').mono (by simp [cmpClob]), hm', hx', ?_⟩, hz⟩
    rw [ha', or_eq_zero64, xor_eq_zero64, readW64_eq_iff, ha, eqBytes_succ8]

theorem compare_ok {s₀ : State} {n : Nat} (hn : n = (s₀.gpr .rcx).toNat) (hn0 : 0 < n)
    (hr : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi) n ∧ InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi) n) :
    WP isa compare s₀ fun t => Keep cmpClob s₀ t ∧ t.mem = s₀.mem ∧
      (t.gpr .rdx = 0 ↔ EqBytes s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi) n) := by
  have hn64 : n < 2 ^ 64 := hn ▸ (s₀.gpr .rcx).isLt
  have start : WP isa (.block [.mov32 .r11 (.imm 0), .mov32 .rdx (.imm 0), .mov .rax (.reg .rcx), .alu .and .rax (.imm 7)]) s₀
      fun t => t.zf = some (decide (n % 8 = 0)) ∧ CInv s₀ 0 t := by
    refine WP.mono (WP.keep cmpClob (Q := fun t => t.zf = some (decide (n % 8 = 0)) ∧ t.mem = s₀.mem ∧
      t.gpr .r11 = 0 ∧ t.gpr .rdx = 0) (by
        xrun
        rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
        have e : (s₀.gpr .rcx &&& BitVec.signExtend 64 (7 : BitVec 32)).toNat = n % 8 := by
          rw [BitVec.toNat_and, ← hn, show (BitVec.signExtend 64 (7 : BitVec 32)).toNat = 2 ^ 3 - 1 from rfl,
            Nat.and_two_pow_sub_one_eq_mod]
        rw [← BitVec.toNat_inj, e]; exact Iff.rfl) (by rfl))
      fun t ⟨⟨hz, hm, h11, hdx⟩, hk⟩ => ⟨hz, hk, hm, h11, by rw [hdx]; rfl⟩
  refine WP.seq (WP.mono start fun t ⟨hz, h0⟩ => ?_)
  refine WP.ite (decide (n % 8 = 0)) (by simp only [eval, hz]) (fun h8 => ?_) (fun h8 => ?_)
  · replace h8 := of_decide_eq_true h8
    have hw : ∀ j, 8 * j < n → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi + BitVec.ofNat 64 (8 * j)) 8 ∧
        InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 (8 * j)) 8 := fun j hj =>
      ⟨CallLay.inRegions_sub hr.1 (by omega) hn64, CallLay.inRegions_sub hr.2 (by omega) hn64⟩
    have w0 : WInv s₀ 0 t := ⟨h0.1, h0.2.1, h0.2.2.1, by
      rw [h0.2.2.2]; exact ⟨fun _ i hi => absurd hi (by omega), fun _ => rfl⟩⟩
    refine WP.mono (Q := WInv s₀ (n / 8)) ?_ fun u hu => ⟨hu.1, hu.2.1, by
      rw [hu.2.2.2, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h8)]⟩
    refine WP.loop (M := isa) (fun rem u => ∃ j, 8 * j < n ∧ rem = n / 8 - j ∧ WInv s₀ j u) ?_ (n / 8) t
      ⟨0, by omega, by omega, w0⟩
    intro rem u ⟨j, hj, hrem, hinv⟩
    refine WP.mono (word_step hw j hj hinv) fun u' ⟨hout, hz'⟩ => ?_
    by_cases he : 8 * (j + 1) = n
    · left
      refine ⟨?_, by rwa [show n / 8 = j + 1 by omega]⟩
      have : BitVec.ofNat 64 (8 * (j + 1)) = s₀.gpr .rcx := by rw [he, hn]; simp
      simp [eval, hz', this]
    · right
      have hne : BitVec.ofNat 64 (8 * (j + 1)) ≠ s₀.gpr .rcx := by
        intro hh
        have := congrArg BitVec.toNat hh
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact he (by omega)
      refine ⟨?_, n / 8 - (j + 1), by omega, j + 1, by omega, rfl, hout⟩
      simp [eval, hz', hne]
  · replace h8 := of_decide_eq_false h8
    have hb : ∀ i < n, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi + BitVec.ofNat 64 i) 1 ∧
        InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 i) 1 := fun i hi =>
      ⟨CallLay.inRegions_sub hr.1 (by omega) hn64, CallLay.inRegions_sub hr.2 (by omega) hn64⟩
    refine WP.mono (Q := CInv s₀ n) ?_ fun u hu => ⟨hu.1, hu.2.1, by
      rw [hu.2.2.2, setWidth_byte_eq_zero', diff_zero]; rfl⟩
    refine WP.loop (M := isa) (fun rem u => ∃ j, j < n ∧ rem = n - j ∧ CInv s₀ j u) ?_ n t
      ⟨0, hn0, rfl, h0⟩
    intro rem u ⟨j, hj, hrem, hinv⟩
    refine WP.mono (compare_step hb j hj hinv) fun u' ⟨hout, hz'⟩ => ?_
    by_cases he : j + 1 = n
    · left
      refine ⟨?_, (by simpa only [he] using hout)⟩
      have : BitVec.ofNat 64 (j + 1) = s₀.gpr .rcx := by rw [he, hn]; simp
      simp [eval, hz', this]
    · right
      have hne : BitVec.ofNat 64 (j + 1) ≠ s₀.gpr .rcx := by
        intro hh
        have := congrArg BitVec.toNat hh
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact he (by omega)
      refine ⟨?_, n - (j + 1), by omega, j + 1, by omega, rfl, hout⟩
      simp [eval, hz', hne]

end VG.Proof.RsaPkcs1Sig.X86_64
