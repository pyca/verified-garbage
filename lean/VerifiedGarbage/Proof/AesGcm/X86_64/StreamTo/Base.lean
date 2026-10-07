import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Contract
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Base
import VerifiedGarbage.Impl.AesGcm.X86_64.StreamTo

/-!
# AES-GCM streaming encryption out of place, x86-64: the setting

Untrusted: everything here is checked by Lean. The arguments of the entry
state `s` (`K`, `St`, `AL`, `TL`, `Src`, `L`, `Dst`, `W`), their regions, and
the facts of `streamToPreM` by name (`SP'`); the entry, which keeps the
arguments in `work` (`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.StreamTo
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

section
variable (s : State)

abbrev K : Addr := s.gpr .rdi
abbrev St : Addr := s.gpr .rdx
abbrev AL : BitVec 64 := s.gpr .rcx
abbrev TL : BitVec 64 := s.gpr .r8
abbrev Src : Addr := s.gpr .r9
abbrev L : Nat := (stackArg s 0).toNat
abbrev Dst : Addr := stackArg s 1
abbrev W : Addr := stackArg s 3
abbrev SP : Addr := s.gpr .rsp
abbrev stR : Region := ⟨St s, 80⟩
abbrev srcR : Region := ⟨Src s, L s⟩
abbrev dR : Region := ⟨Dst s, L s⟩
abbrev wkR : Region := ⟨W s, 2192⟩
/-- The stack arguments `len`, `dst`, `dst_len` and `work`. -/
abbrev aR : Region := ⟨SP s + BitVec.ofNat 64 8, 32⟩
/-- What the code writes: the state, the output and `work`. -/
abbrev wR : List Region := [stR s, dR s, wkR s]
/-- The stack the calls use. -/
abbrev tR : Region := below (SP s) 2624

end

/-- The key context, of kind `M`. -/
abbrev kR (M : CtxMode) (s : State) : Region := ⟨K s, M.len⟩

/-- `streamToPreM M`, by name (with the output's length `dst_len` replaced
by `len`, which it equals). -/
structure SP' (M : CtxMode) (s : State) : Prop where
  rd : s.rd = [kR M s, srcR s, aR s]
  wr : s.wr = wR s
  dl : stackArg s 2 = stackArg s 0
  k_st : (kR M s).Disjoint (stR s)
  k_d : (kR M s).Disjoint (dR s)
  k_w : (kR M s).Disjoint (wkR s)
  st_r : (stR s).Disjoint (srcR s)
  st_d : (stR s).Disjoint (dR s)
  st_w : (stR s).Disjoint (wkR s)
  st_a : (stR s).Disjoint (aR s)
  r_d : (srcR s).Disjoint (dR s)
  r_w : (srcR s).Disjoint (wkR s)
  d_w : (dR s).Disjoint (wkR s)
  d_a : (dR s).Disjoint (aR s)
  w_a : (wkR s).Disjoint (aR s)
  t_st : (⟨SP s, 8⟩ : Region).Disjoint (stR s)
  t_d : (⟨SP s, 8⟩ : Region).Disjoint (dR s)
  t_w : (⟨SP s, 8⟩ : Region).Disjoint (wkR s)
  b_k : (tR s).Disjoint (kR M s)
  b_st : (tR s).Disjoint (stR s)
  b_r : (tR s).Disjoint (srcR s)
  b_d : (tR s).Disjoint (dR s)
  b_w : (tR s).Disjoint (wkR s)
  w_k : (K s).toNat + M.len ≤ 2 ^ 64
  w_st : (St s).toNat + 80 ≤ 2 ^ 64
  w_r : (Src s).toNat + L s ≤ 2 ^ 64
  w_d : (Dst s).toNat + L s ≤ 2 ^ 64
  w_w : (W s).toNat + 2192 ≤ 2 ^ 64
  w_t : 2624 ≤ (SP s).toNat
  w_sp : (SP s).toNat + 40 ≤ 2 ^ 64
  rounds : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14
  ok : M.ok s.mem (K s)

theorem SP'.ofM {M : CtxMode} {s : State} (h : Proof.AesGcm.streamToPreM M s) : SP' M s := by
  simp only [Proof.AesGcm.streamToPreM, Proof.AesGcm.args, Proof.AesGcm.arg, Proof.AesGcm.ret,
    Proof.AesGcm.stkS, Proof.AesGcm.rounds] at h
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂,
    a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂⟩ := h
  rw [hA] at a₁ a₁₀ a₁₄ a₁₅
  rw [a₃] at a₂ a₅ a₈ a₁₁ a₁₃ a₁₄ a₁₇ a₂₂ a₂₇
  exact ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂,
    a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂⟩

/-! ## The arguments kept -/

/-- The arguments kept in `work` at `W`, with `o` bytes done. -/
structure Kept (s : State) (o : Nat) (m : Mem) : Prop where
  ctx : m.readW (W s) 64 = K s
  rounds : m.readW (W s + BitVec.ofNat 64 8) 64 = s.gpr .rsi
  st : m.readW (W s + BitVec.ofNat 64 16) 64 = St s
  aad : m.readW (W s + BitVec.ofNat 64 24) 64 = AL s
  tl : m.readW (W s + BitVec.ofNat 64 32) 64 = TL s
  src : m.readW (W s + BitVec.ofNat 64 40) 64 = Src s
  len : m.readW (W s + BitVec.ofNat 64 48) 64 = stackArg s 0
  dst : m.readW (W s + BitVec.ofNat 64 56) 64 = Dst s
  done : m.readW (W s + BitVec.ofNat 64 64) 64 = BitVec.ofNat 64 o

/-- The slots of the arguments kept. -/
abbrev kR' (s : State) : Region := ⟨W s, 72⟩

/-- The working space of `vg_aes_gcm_encrypt_blocks_to`. -/
abbrev scR (s : State) : Region := ⟨W s + BitVec.ofNat 64 80, 2112⟩

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

theorem w_in {d k : Nat} (h : d + k ≤ 2192) : InRegions s.wr (W s + BitVec.ofNat 64 d) k :=
  in_off (rs := s.wr) (by rw [hp.wr]; exact covers_of_mem (by simp)) h (by decide)

theorem w_in' {d k : Nat} (h : d + k ≤ 2192) : InRegions (s.rd ++ s.wr) (W s + BitVec.ofNat 64 d) k :=
  in_left (w_in hp h)

/-- The stack argument `i` (of four) is readable. -/
theorem a_in {i : Nat} (hi : i < 4) : InRegions (s.rd ++ s.wr) (SP s + BitVec.ofNat 64 (8 * (i + 1))) 8 :=
  ⟨aR s, by rw [hp.rd]; simp, Offset.contains _ (by omega) (by omega) (by have := hp.w_sp; omega)⟩

omit hp in
theorem kR'_sub : (kR' s).Sub (wkR s) := Region.sub_prefix (by decide)

omit hp in
theorem scR_sub : (scR s).Sub (wkR s) := Offset.sub_base _ (by decide)

omit hp in
theorem kR'_scR : (kR' s).Disjoint (scR s) := Offset.base_disjoint _ (by decide) (by decide)

/-- What a frame of the regions written and the stack below keeps: the
stack arguments. -/
theorem keep_a {m m' : Mem} (hf : Frame (wR s ++ [tR s]) m m') {i : Nat} (hi : i < 4) :
    m'.readW (SP s + BitVec.ofNat 64 (8 * (i + 1))) 64 = m.readW (SP s + BitVec.ofNat 64 (8 * (i + 1))) 64 :=
  hf.readW (r := ⟨SP s + BitVec.ofNat 64 (8 * (i + 1)), 8⟩) (Region.contains_self _ _) (fun r hr => by
    have hs : Region.Sub ⟨SP s + BitVec.ofNat 64 (8 * (i + 1)), 8⟩ (aR s) := by
      have e : SP s + BitVec.ofNat 64 (8 * (i + 1)) = SP s + BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * i) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
      rw [e]; exact Offset.sub_base _ (by omega)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact hp.st_a.symm.sub_left hs
    · exact hp.d_a.symm.sub_left hs
    · exact hp.w_a.symm.sub_left hs
    · exact (Offset.disjoint_below (SP s) (n := 2624) (d := 8 * (i + 1)) (k := 8) (by omega)).sub_left
        (fun _ h => h)) (by decide)

/-- The return address, through a frame of the regions written. -/
theorem keep_r {m m' : Mem} (hf : Frame (wR s) m m') : m'.readW (SP s) 64 = m.readW (SP s) 64 :=
  hf.readW (r := ⟨SP s, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.t_st
    · exact hp.t_d
    · exact hp.t_w) (by decide)

omit hp in
theorem arg_eq (i : Nat) : s.mem.readW (SP s + BitVec.ofNat 64 (8 * (i + 1))) 64 = stackArg s i := rfl

/-- The entry: the arguments kept, with `work` in `r11`, and none done. -/
theorem entry_ok : WP isa (.block entry) s fun s₁ => s₁.gpr .r11 = W s ∧
    (∀ r, r ≠ .r11 → r ≠ .rax → r ≠ .r10 → s₁.gpr r = s.gpr r) ∧
    Kept s 0 s₁.mem ∧ Frame [kR' s] s.mem s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 72 → InRegions s.wr (W s + BitVec.ofNat 64 d) (64 / 8) := fun d h => w_in hp (by omega)
  have a₀ : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 := a_in hp (i := 0) (by decide)
  have a₁ : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 16) 8 := a_in hp (i := 1) (by decide)
  have a₃ : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 32) 8 := a_in hp (i := 3) (by decide)
  have e₀ : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s 0 := rfl
  have e₁ : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 16) 64 = Dst s := rfl
  have e₃ : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 32) 64 = W s := rfl
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 72 → d + 8 ≤ 72 →
      Mem.Sep (W s + BitVec.ofNat 64 a) (64 / 8) (W s + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep _ h (by omega) (by have := hp.w_w; omega)
  have s0 : ∀ d, 8 ≤ d → d + 8 ≤ 72 → Mem.Sep (W s) (64 / 8) (W s + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => by
    have := sep 0 d (by omega) (by decide) h₂; simpa using this
  have s₀₁ := s0 8 (by decide) (by decide)
  have s₀₂ := s0 16 (by decide) (by decide)
  have s₀₃ := s0 24 (by decide) (by decide)
  have s₀₄ := s0 32 (by decide) (by decide)
  have s₀₅ := s0 40 (by decide) (by decide)
  have s₀₆ := s0 48 (by decide) (by decide)
  have s₀₇ := s0 56 (by decide) (by decide)
  have s₀₈ := s0 64 (by decide) (by decide)
  have s₁₂ := sep 8 16 (by decide) (by decide) (by decide)
  have s₁₃ := sep 8 24 (by decide) (by decide) (by decide)
  have s₁₄ := sep 8 32 (by decide) (by decide) (by decide)
  have s₁₅ := sep 8 40 (by decide) (by decide) (by decide)
  have s₁₆ := sep 8 48 (by decide) (by decide) (by decide)
  have s₁₇ := sep 8 56 (by decide) (by decide) (by decide)
  have s₁₈ := sep 8 64 (by decide) (by decide) (by decide)
  have s₂₃ := sep 16 24 (by decide) (by decide) (by decide)
  have s₂₄ := sep 16 32 (by decide) (by decide) (by decide)
  have s₂₅ := sep 16 40 (by decide) (by decide) (by decide)
  have s₂₆ := sep 16 48 (by decide) (by decide) (by decide)
  have s₂₇ := sep 16 56 (by decide) (by decide) (by decide)
  have s₂₈ := sep 16 64 (by decide) (by decide) (by decide)
  have s₃₄ := sep 24 32 (by decide) (by decide) (by decide)
  have s₃₅ := sep 24 40 (by decide) (by decide) (by decide)
  have s₃₆ := sep 24 48 (by decide) (by decide) (by decide)
  have s₃₇ := sep 24 56 (by decide) (by decide) (by decide)
  have s₃₈ := sep 24 64 (by decide) (by decide) (by decide)
  have s₄₅ := sep 32 40 (by decide) (by decide) (by decide)
  have s₄₆ := sep 32 48 (by decide) (by decide) (by decide)
  have s₄₇ := sep 32 56 (by decide) (by decide) (by decide)
  have s₄₈ := sep 32 64 (by decide) (by decide) (by decide)
  have s₅₆ := sep 40 48 (by decide) (by decide) (by decide)
  have s₅₇ := sep 40 56 (by decide) (by decide) (by decide)
  have s₅₈ := sep 40 64 (by decide) (by decide) (by decide)
  have s₆₇ := sep 48 56 (by decide) (by decide) (by decide)
  have s₆₈ := sep 48 64 (by decide) (by decide) (by decide)
  have s₇₈ := sep 56 64 (by decide) (by decide) (by decide)
  have hz : BitVec.setWidth 64 (BitVec.ofNat 32 0) = BitVec.ofNat 64 0 := by decide
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [entry, wCtx, wRounds, wState, wAad, wTlen, wSrc, wLen, wDst, wDone]
    xrun [a₀, a₁, a₃, e₀, e₁, e₃, w 0 (by decide), w 8 (by decide), w 16 (by decide), w 24 (by decide), w 32 (by decide),
      w 40 (by decide), w 48 (by decide), w 56 (by decide), w 64 (by decide)],
    ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · intro r hr hr' hr''; simp [gpr_setReg, hr, hr', hr'']
  all_goals try simp (disch := first | decide | with_reducible assumption) only [gpr_setReg, ite_true,
    reduceCtorEq, ↓reduceIte, Mem.readW_writeW_self64, Mem.readW_writeW_sep, BitVec.add_zero, mem_setReg, hz]
  · have c : ∀ d, d + 8 ≤ 72 → (kR' s).Contains (W s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₂ => Offset.contains_base _ h₂ (by have := hp.w_w; omega)
    have c0 : (kR' s).Contains (W s) (64 / 8) := by simpa using c 0 (by decide)
    exact (((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW
      (List.mem_singleton_self _) _ (c 8 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 16 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 24 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 32 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 40 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 48 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 56 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 64 (by decide))

end

end VG.Proof.AesGcm.X86_64.StreamTo
