import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Contract
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Base
import VerifiedGarbage.Impl.AesGcm.X86_64.BlocksTo

/-!
# AES-GCM on whole blocks out of place, x86-64: the setting

Untrusted: everything here is checked by Lean. The arguments of the entry
state `s` (`K`, `C`, `Y`, `Src`, `n`, `Dst`, `S`), their regions, and the
facts of `blocksToPreM` by name (`BT`); the entry, which keeps the arguments
in `scratch` (`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.BlocksTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo
open VG.Impl.AesGcm.X86_64.Blocks (argCtx argRounds argCtr argY argN)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

section
variable (s : State)

abbrev K : Addr := s.gpr .rdi
abbrev C : Addr := s.gpr .rdx
abbrev Y : Addr := s.gpr .rcx
abbrev Src : Addr := s.gpr .r8
abbrev n : Nat := (s.gpr .r9).toNat
abbrev Dst : Addr := stackArg s 0
abbrev S : Addr := stackArg s 2
abbrev SP : Addr := s.gpr .rsp
abbrev cR : Region := ⟨C s, 16⟩
abbrev yR : Region := ⟨Y s, 16⟩
abbrev srcR : Region := ⟨Src s, n s * 16⟩
abbrev dR : Region := ⟨Dst s, n s * 16⟩
abbrev sR : Region := ⟨S s, 2112⟩
/-- The stack arguments `dst`, `dst_n` and `scratch`. -/
abbrev aR : Region := ⟨SP s + BitVec.ofNat 64 8, 24⟩
/-- What the code writes: the counter, `Y`, the output and `scratch`. -/
abbrev wR : List Region := [cR s, yR s, dR s, sR s]
/-- The stack the calls use. -/
abbrev tR : Region := below (SP s) 24

end

/-- The key context, of kind `M`. -/
abbrev kR (M : CtxMode) (s : State) : Region := ⟨K s, M.len⟩

/-- `blocksToPreM M`, by name (with the output's length `dst_n` replaced by
`n`, which it equals). -/
structure BT (M : CtxMode) (s : State) : Prop where
  rd : s.rd = [kR M s, srcR s, aR s]
  wr : s.wr = wR s
  dn : stackArg s 1 = s.gpr .r9
  k_c : (kR M s).Disjoint (cR s)
  k_y : (kR M s).Disjoint (yR s)
  k_d : (kR M s).Disjoint (dR s)
  k_s : (kR M s).Disjoint (sR s)
  c_y : (cR s).Disjoint (yR s)
  c_r : (cR s).Disjoint (srcR s)
  c_d : (cR s).Disjoint (dR s)
  c_s : (cR s).Disjoint (sR s)
  c_a : (cR s).Disjoint (aR s)
  y_r : (yR s).Disjoint (srcR s)
  y_d : (yR s).Disjoint (dR s)
  y_s : (yR s).Disjoint (sR s)
  y_a : (yR s).Disjoint (aR s)
  r_d : (srcR s).Disjoint (dR s)
  r_s : (srcR s).Disjoint (sR s)
  d_s : (dR s).Disjoint (sR s)
  d_a : (dR s).Disjoint (aR s)
  s_a : (sR s).Disjoint (aR s)
  t_c : (⟨SP s, 8⟩ : Region).Disjoint (cR s)
  t_y : (⟨SP s, 8⟩ : Region).Disjoint (yR s)
  t_d : (⟨SP s, 8⟩ : Region).Disjoint (dR s)
  t_s : (⟨SP s, 8⟩ : Region).Disjoint (sR s)
  b_k : (tR s).Disjoint (kR M s)
  b_c : (tR s).Disjoint (cR s)
  b_y : (tR s).Disjoint (yR s)
  b_r : (tR s).Disjoint (srcR s)
  b_d : (tR s).Disjoint (dR s)
  b_s : (tR s).Disjoint (sR s)
  w_k : (K s).toNat + M.len ≤ 2 ^ 64
  w_c : (C s).toNat + 16 ≤ 2 ^ 64
  w_y : (Y s).toNat + 16 ≤ 2 ^ 64
  w_r : (Src s).toNat + n s * 16 ≤ 2 ^ 64
  w_d : (Dst s).toNat + n s * 16 ≤ 2 ^ 64
  w_s : (S s).toNat + 2112 ≤ 2 ^ 64
  w_t : 24 ≤ (SP s).toNat
  w_sp : (SP s).toNat + 32 ≤ 2 ^ 64
  rounds : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14
  ok : M.ok s.mem (K s)

theorem BT.ofM {M : CtxMode} {s : State} (h : Proof.AesGcm.blocksToPreM M s) : BT M s := by
  simp only [Proof.AesGcm.blocksToPreM, Proof.AesGcm.args, Proof.AesGcm.arg, Proof.AesGcm.ret,
    Proof.AesGcm.stk24, Proof.AesGcm.rounds] at h
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂,
    a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂, a₃₃, a₃₄, a₃₅, a₃₆, a₃₇, a₃₈, a₃₉, a₄₀, a₄₁⟩ := h
  rw [hA] at a₁ a₁₂ a₁₆ a₂₀ a₂₁
  rw [a₃] at a₂ a₆ a₁₀ a₁₄ a₁₇ a₁₉ a₂₀ a₂₄ a₃₀ a₃₆
  exact ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂,
    a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂, a₃₃, a₃₄, a₃₅, a₃₆, a₃₇, a₃₈, a₃₉, a₄₀, a₄₁⟩

/-! ## The arguments kept -/

/-- The arguments kept in `scratch` at `S`: the plaintext, the number of
blocks and the output of what is left after `q` blocks. -/
structure Kept (s : State) (q : Nat) (m : Mem) : Prop where
  ctx : m.readW (S s) 64 = K s
  rounds : m.readW (S s + BitVec.ofNat 64 8) 64 = s.gpr .rsi
  ctr : m.readW (S s + BitVec.ofNat 64 16) 64 = C s
  y : m.readW (S s + BitVec.ofNat 64 24) 64 = Y s
  src : m.readW (S s + BitVec.ofNat 64 32) 64 = Src s + BitVec.ofNat 64 (16 * q)
  n : m.readW (S s + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (n s - q)
  dst : m.readW (S s + BitVec.ofNat 64 48) 64 = Dst s + BitVec.ofNat 64 (16 * q)

/-- The slots of the arguments kept. -/
abbrev kR' (s : State) : Region := ⟨S s, 56⟩

section
variable {M : CtxMode} {s : State} (hp : BT M s)
include hp

theorem s_in {d k : Nat} (h : d + k ≤ 2112) : InRegions s.wr (S s + BitVec.ofNat 64 d) k :=
  in_off (rs := s.wr) (by rw [hp.wr]; exact covers_of_mem (by simp)) h (by decide)

theorem s_in' {d k : Nat} (h : d + k ≤ 2112) : InRegions (s.rd ++ s.wr) (S s + BitVec.ofNat 64 d) k :=
  in_left (s_in hp h)

/-- The stack argument `i` (of three) is readable. -/
theorem a_in {i : Nat} (hi : i < 3) : InRegions (s.rd ++ s.wr) (SP s + BitVec.ofNat 64 (8 * (i + 1))) 8 :=
  ⟨aR s, by rw [hp.rd]; simp, Offset.contains _ (by omega) (by omega) (by have := hp.w_sp; omega)⟩

omit hp in
/-- The slots of the arguments are in `scratch`, apart from the powers. -/
theorem kR'_sub : (kR' s).Sub (sR s) := Region.sub_prefix (by decide)

/-- What a frame of the regions written keeps: the stack arguments. -/
theorem keep_a {m m' : Mem} (hf : Frame (wR s) m m') {i : Nat} (hi : i < 3) :
    m'.readW (SP s + BitVec.ofNat 64 (8 * (i + 1))) 64 = m.readW (SP s + BitVec.ofNat 64 (8 * (i + 1))) 64 :=
  hf.readW (r := ⟨SP s + BitVec.ofNat 64 (8 * (i + 1)), 8⟩) (Region.contains_self _ _) (fun r hr => by
    have hs : Region.Sub ⟨SP s + BitVec.ofNat 64 (8 * (i + 1)), 8⟩ (aR s) := by
      have e : SP s + BitVec.ofNat 64 (8 * (i + 1)) = SP s + BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * i) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
      rw [e]; exact Offset.sub_base _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.c_a.symm.sub_left hs
    · exact hp.y_a.symm.sub_left hs
    · exact hp.d_a.symm.sub_left hs
    · exact hp.s_a.symm.sub_left hs) (by decide)

/-- The return address, through a frame of the regions written. -/
theorem keep_r {m m' : Mem} (hf : Frame (wR s) m m') : m'.readW (SP s) 64 = m.readW (SP s) 64 :=
  hf.readW (r := ⟨SP s, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.t_c
    · exact hp.t_y
    · exact hp.t_d
    · exact hp.t_s) (by decide)

omit hp in
theorem arg_eq (i : Nat) : s.mem.readW (SP s + BitVec.ofNat 64 (8 * (i + 1))) 64 = stackArg s i := rfl

/-- The entry: the arguments kept, with `scratch` in `r11` and `dst` in `r10`. -/
theorem entry_ok : WP isa (.block entry) s fun s₁ => s₁.gpr .r11 = S s ∧
    s₁.gpr .r10 = Dst s ∧ (∀ r, r ≠ .r11 → r ≠ .r10 → s₁.gpr r = s.gpr r) ∧
    Kept s 0 s₁.mem ∧ Frame [kR' s] s.mem s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have w₁ := s_in hp (show 0 + 8 ≤ 2112 by decide)
  have w₂ := s_in hp (show 8 + 8 ≤ 2112 by decide)
  have w₃ := s_in hp (show 16 + 8 ≤ 2112 by decide)
  have w₄ := s_in hp (show 24 + 8 ≤ 2112 by decide)
  have w₅ := s_in hp (show 32 + 8 ≤ 2112 by decide)
  have w₆ := s_in hp (show 40 + 8 ≤ 2112 by decide)
  have w₇ := s_in hp (show 48 + 8 ≤ 2112 by decide)
  have a₀ : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 := a_in hp (i := 0) (by decide)
  have a₂ : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 24) 8 := a_in hp (i := 2) (by decide)
  have e₀ : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 = Dst s := rfl
  have e₂ : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 24) 64 = S s := rfl
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2112 → d + 8 ≤ 2112 →
      Mem.Sep (S s + BitVec.ofNat 64 a) (64 / 8) (S s + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep _ h (by omega) (by omega)
  have s₁₂ := sep 0 8 (by decide) (by decide) (by decide)
  have s₁₃ := sep 0 16 (by decide) (by decide) (by decide)
  have s₁₄ := sep 0 24 (by decide) (by decide) (by decide)
  have s₁₅ := sep 0 32 (by decide) (by decide) (by decide)
  have s₁₆ := sep 0 40 (by decide) (by decide) (by decide)
  have s₁₇ := sep 0 48 (by decide) (by decide) (by decide)
  simp only [BitVec.add_zero] at s₁₂ s₁₃ s₁₄ s₁₅ s₁₆ s₁₇
  have s₂₃ := sep 8 16 (by decide) (by decide) (by decide)
  have s₂₄ := sep 8 24 (by decide) (by decide) (by decide)
  have s₂₅ := sep 8 32 (by decide) (by decide) (by decide)
  have s₂₆ := sep 8 40 (by decide) (by decide) (by decide)
  have s₂₇ := sep 8 48 (by decide) (by decide) (by decide)
  have s₃₄ := sep 16 24 (by decide) (by decide) (by decide)
  have s₃₅ := sep 16 32 (by decide) (by decide) (by decide)
  have s₃₆ := sep 16 40 (by decide) (by decide) (by decide)
  have s₃₇ := sep 16 48 (by decide) (by decide) (by decide)
  have s₄₅ := sep 24 32 (by decide) (by decide) (by decide)
  have s₄₆ := sep 24 40 (by decide) (by decide) (by decide)
  have s₄₇ := sep 24 48 (by decide) (by decide) (by decide)
  have s₅₆ := sep 32 40 (by decide) (by decide) (by decide)
  have s₅₇ := sep 32 48 (by decide) (by decide) (by decide)
  have s₆₇ := sep 40 48 (by decide) (by decide) (by decide)
  have hn : BitVec.ofNat 64 (n s - 0) = s.gpr .r9 := by simp
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [entry, argCtx, argRounds, argCtr, argY, argSrc, argN, argDst]
    xrun [a₀, a₂, e₀, e₂, w₁, w₂, w₃, w₄, w₅, w₆, w₇],
    ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · intro r hr hr'; simp [gpr_setReg, hr, hr']
  all_goals try simp (disch := first | decide | with_reducible assumption) only [gpr_setReg, ite_true, reduceCtorEq, ↓reduceIte,
    Mem.readW_writeW_self64, Mem.readW_writeW_sep, Nat.mul_zero, BitVec.add_zero, hn]
  · have c : ∀ d, d + 8 ≤ 56 → (kR' s).Contains (S s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₂ => Offset.contains_base _ h₂ (by omega)
    have c0 : (kR' s).Contains (S s) (64 / 8) := by simpa using c 0 (by decide)
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW
      (List.mem_singleton_self _) _ (c 8 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 16 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 24 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 32 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 40 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 48 (by decide))

end

end VG.Proof.AesGcm.X86_64.BlocksTo
