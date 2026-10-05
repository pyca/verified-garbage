import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Encode
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Ct.Common
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Comparing two buffers on x86-64

`compare_ok`: `compare` leaves in `rdx` the OR of the differences of the
`n` bytes at `rdi` and `rsi` (`Proof.Ct.diff`), which is zero exactly when
they are equal, and changes neither memory nor any register but `rax`,
`rdx`, `r10` and `r11`.
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.Ct

/-- The registers `compare` writes. -/
def cmpClob : List Reg := [.rax, .rdx, .r10, .r11]

/-- After `i` bytes. -/
def CInv (s₀ : State) (i : Nat) (s : State) : Prop :=
  Keep cmpClob s₀ s ∧ s.mem = s₀.mem ∧ s.gpr .r11 = BitVec.ofNat 64 i ∧
    s.gpr .rdx = (diff s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi) i).setWidth 64

theorem ea_ix (s : State) (b i : Reg) :
    s.ea { base := b, index := some i } = s.gpr b + s.gpr i := by
  simp [State.ea]

theorem compare_step {s₀ s : State} {n : Nat}
    (hr : ∀ i < n, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi + BitVec.ofNat 64 i) 1 ∧
      InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 i) 1)
    (i : Nat) (hi : i < n) (h : CInv s₀ i s) :
    WP isa (.block [.movzx8 .rax { base := .rdi, index := some .r11 },
      .movzx8 .r10 { base := .rsi, index := some .r11 }, .alu .xor .rax (.reg .r10),
      .alu .or .rdx (.reg .rax), .alu .add .r11 (.imm 1), .alu .cmp .r11 (.reg .rcx)]) s fun t =>
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
  · xrun [ea_ix, hA, hB, hm, ha, hx, hdi, hsi, hcx, hadd, sub_beq64, ← BitVec.setWidth_xor,
      ← BitVec.setWidth_or, diff]
  · intro t ⟨⟨hm', hx', ha', hz⟩, hk'⟩
    exact ⟨⟨(hk.trans hk').mono (by simp [cmpClob]), hm', hx', ha'⟩, hz⟩

theorem compare_ok {s₀ : State} {n : Nat} (hn : n = (s₀.gpr .rcx).toNat) (hn0 : 0 < n)
    (hr : ∀ i < n, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi + BitVec.ofNat 64 i) 1 ∧
      InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 i) 1) :
    WP isa compare s₀ fun t => Keep cmpClob s₀ t ∧ t.mem = s₀.mem ∧
      t.gpr .rdx = (diff s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi) n).setWidth 64 := by
  have start : WP isa (.block [.mov32 .r11 (.imm 0), .mov32 .rdx (.imm 0)]) s₀ (CInv s₀ 0) := by
    refine WP.mono (WP.keep cmpClob (Q := fun t => t.mem = s₀.mem ∧ t.gpr .r11 = 0 ∧ t.gpr .rdx = 0)
      (by xrun) (by rfl)) fun t ⟨⟨hm, h11, hdx⟩, hk⟩ => ⟨hk, hm, h11, by rw [hdx]; rfl⟩
  refine WP.seq (WP.mono start fun t h0 => ?_)
  refine WP.mono (Q := CInv s₀ n) ?_ fun u hu => ⟨hu.1, hu.2.1, hu.2.2.2⟩
  refine WP.loop (M := isa) (fun rem u => ∃ j, j < n ∧ rem = n - j ∧ CInv s₀ j u) ?_ n t
    ⟨0, hn0, rfl, h0⟩
  intro rem u ⟨j, hj, hrem, hinv⟩
  refine WP.mono (compare_step hr j hj hinv) fun u' ⟨hout, hz⟩ => ?_
  by_cases he : j + 1 = n
  · left
    refine ⟨?_, (by simpa only [he] using hout)⟩
    have : BitVec.ofNat 64 (j + 1) = s₀.gpr .rcx := by rw [he, hn]; simp
    simp [eval, hz, this]
  · right
    have hne : BitVec.ofNat 64 (j + 1) ≠ s₀.gpr .rcx := by
      intro hh
      have := congrArg BitVec.toNat hh
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s₀.gpr .rcx).isLt; omega)] at this
      exact he (by omega)
    refine ⟨?_, n - (j + 1), by omega, j + 1, by omega, rfl, hout⟩
    simp [eval, hz, hne]

end VG.Proof.RsaPkcs1Sig.X86_64
