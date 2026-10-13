module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.Pre
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.XorSplitVerified
public import VerifiedGarbage.Proof.Framework.X86_64.InlineCalls

/-!
# ChaCha20-Poly1305 with the data's first bytes from `src`, x86-64: the encryption

`cryptSplit` (`Impl/ChaCha20Poly1305/X86_64/SealSplit.lean`) is `crypt` with
`vg_chacha20_xor_avx512` but for the call encrypting the data after its
first `mm` bytes, which becomes the code of `vg_chacha20_xor_split_avx512`
inline, reading the bytes `[mm, src_len)` from `src`: it writes to the data
the encryption of `PTs` (`cryptSplit_ok`). The inline code runs from its
contract (`xorSplitX86_64`), with the state's permissions narrowed to its
regions, its calls' return addresses within the 24 bytes below `rsp` that
`seal`'s call takes (`WP.inlineSp`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Split

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.SealSplit
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20 (stateAt keystream)

theorem sub_ofNat_ofNat {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 (a - b) = BitVec.ofNat 64 b := by
  rw [Offset.ofNat_sub_ofNat (by omega), show a - (a - b) = b by omega]

/-- `stackArgAddr s₀ j`, as `rsp + 8 (j + 1)`. -/
theorem argAddr_eq (s₀ : State) (j : Nat) :
    off (s₀.gpr .rsp) (8 * (j + 1)) = stackArgAddr s₀ j := by
  rw [off_eq]; rfl

theorem in_arg2 {s₀ : State} (hT : SPre s₀) {s : State} (hrd : s.rd = s₀.rd) {j : Nat} (hj : j = 2 ∨ j = 3) :
    InRegions (s.rd ++ s.wr) (stackArgAddr s₀ j) 8 := by
  refine ⟨arg2R s₀, by rw [hrd]; simp [hT.g2], ?_⟩
  rcases hj with rfl | rfl
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [stackArgAddr]
    rw [show s₀.gpr .rsp + BitVec.ofNat 64 (8 * (3 + 1)) = s₀.gpr .rsp + BitVec.ofNat 64 (8 * (2 + 1)) +
      BitVec.ofNat 64 8 by rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
    exact Offset.contains_base _ (by lit_omega) (by lit_omega)

/-- The arguments of `vg_chacha20_xor_split_avx512` for the data after its
first `m` bytes. -/
structure SArgs (s₀ : State) (m : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = off (cx s₀) 64
  rsi : s.gpr .rsi = sp s₀ + BitVec.ofNat 64 m
  rdx : s.gpr .rdx = BitVec.ofNat 64 (SL s₀ - m)
  rcx : s.gpr .rcx = off (dp s₀) m
  r8 : s.gpr .r8 = BitVec.ofNat 64 (L s₀ - m)
  r9 : s.gpr .r9 = off (cx s₀) 128

set_option simprocs false in
/-- `splitArgs`, after `cryptArgsM`. -/
theorem splitArgs_ok {s₀ : State} (hT : SPre s₀) {m : Nat} {s : State} (h : XArgsM s₀ m s)
    (hrd : s.rd = s₀.rd) (hS2 : s.mem.readW (stackArgAddr s₀ 2) 64 = stackArg s₀ 2)
    (hS3 : s.mem.readW (stackArgAddr s₀ 3) 64 = stackArg s₀ 3) :
    WP isa (.block splitArgs) s fun s' => SArgs s₀ m s' ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  have hL9 := (s₀.gpr .r9).isLt
  have hle := h.le
  have hSL := (stackArg s₀ 3).isLt
  have hm : m < 2 ^ 64 := by simp only [L] at hle; omega
  have ra : s.gpr .rsi - s.gpr .r14 = BitVec.ofNat 64 m := by
    rw [h.rsi, h.r14, off_eq, BitVec.add_sub_cancel_left]
  have i2 := in_arg2 hT hrd (.inl rfl)
  have i3 := in_arg2 hT hrd (.inr rfl)
  have e2 : off (s.gpr .rsp) 24 = stackArgAddr s₀ 2 := by rw [h.rsp]; exact argAddr_eq s₀ 2
  have e3 : off (s.gpr .rsp) 32 = stackArgAddr s₀ 3 := by rw [h.rsp]; exact argAddr_eq s₀ 3
  apply WP.of_runBlock
  simp only [splitArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    execCmov, eval, State.load64, ea_at, arithFlags, State.setReg, State.setReg32, State.setFlags,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left', reduceCtorEq, ↓reduceIte, e2, e3,
    i2, i3, hS2, hS3, ra]
  have ec : (stackArg s₀ 3).toNat = SL s₀ := rfl
  have em : (BitVec.ofNat 64 m).toNat = m := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  simp only [ec, em]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_, trivial, trivial, trivial⟩
  · simp [h.rdi]
  · simp
  · by_cases hcn : SL s₀ < m
    · simp only [hcn, decide_true, ↓reduceIte, Nat.sub_eq_zero_of_le (Nat.le_of_lt hcn)]; rfl
    · simp only [hcn, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [show stackArg s₀ 3 = BitVec.ofNat 64 (SL s₀) by simp [SL]]
      exact Offset.ofNat_sub_ofNat (by omega)
  · simp [h.rsi]
  · simp [h.rdx]
  · simp [h.rcx]
  · have := calleeSaved_ne hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end VG.Proof.ChaCha20Poly1305.X86_64.Split
