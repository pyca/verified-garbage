import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerifyCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Variant
import VerifiedGarbage.Impl.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Dec

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Base`. -/
section

/-!
# AES-GCM on whole blocks, x86-64: the setting

Untrusted: everything here is checked by Lean. The arguments of the entry
state `s` (`K`, `C`, `Y`, `D`, `n`, `S`), their regions, and the facts of
`blocksPre` by name (`BP`); the entry, which keeps the arguments in
`scratch` (`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Spec.Gcm (Block blockAt blocksAt)

section
variable (s : State)

abbrev K : Addr := s.gpr .rdi
abbrev C : Addr := s.gpr .rdx
abbrev Y : Addr := s.gpr .rcx
abbrev D : Addr := s.gpr .r8
abbrev n : Nat := (s.gpr .r9).toNat
abbrev S : Addr := stackArg s 0
abbrev SP : Addr := s.gpr .rsp
abbrev kR : Region := ⟨VG.Proof.AesGcm.X86_64.Blocks.K s, 256⟩
abbrev cR : Region := ⟨VG.Proof.AesGcm.X86_64.Blocks.C s, 16⟩
abbrev yR : Region := ⟨VG.Proof.AesGcm.X86_64.Blocks.Y s, 16⟩
abbrev dR : Region := ⟨VG.Proof.AesGcm.X86_64.Blocks.D s, VG.Proof.AesGcm.X86_64.Blocks.n s * 16⟩
abbrev sR : Region := ⟨VG.Proof.AesGcm.X86_64.Blocks.S s, 2112⟩
/-- The stack argument `scratch`. -/
abbrev aR : Region := ⟨VG.Proof.AesGcm.X86_64.Blocks.SP s + BitVec.ofNat 64 8, 8⟩
/-- What the code writes: the counter, `Y`, the data and `scratch`. -/
abbrev wR : List Region := [VG.Proof.AesGcm.X86_64.Blocks.cR s, VG.Proof.AesGcm.X86_64.Blocks.yR s, VG.Proof.AesGcm.X86_64.Blocks.dR s, VG.Proof.AesGcm.X86_64.Blocks.sR s]

end

/-- `blocksPre`, by name. -/
structure BP (s : State) : Prop where
  rd : s.rd = [VG.Proof.AesGcm.X86_64.Blocks.kR s, VG.Proof.AesGcm.X86_64.Blocks.aR s]
  wr : s.wr = VG.Proof.AesGcm.X86_64.Blocks.wR s
  k_c : (VG.Proof.AesGcm.X86_64.Blocks.kR s).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.cR s)
  k_y : (VG.Proof.AesGcm.X86_64.Blocks.kR s).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.yR s)
  k_d : (VG.Proof.AesGcm.X86_64.Blocks.kR s).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.dR s)
  k_s : (VG.Proof.AesGcm.X86_64.Blocks.kR s).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.sR s)
  c_y : (VG.Proof.AesGcm.X86_64.Blocks.cR s).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.yR s)
  c_d : (VG.Proof.AesGcm.X86_64.Blocks.cR s).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.dR s)
  c_s : (VG.Proof.AesGcm.X86_64.Blocks.cR s).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.sR s)
  c_a : (VG.Proof.AesGcm.X86_64.Blocks.cR s).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.aR s)
  y_d : (VG.Proof.AesGcm.X86_64.Blocks.yR s).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.dR s)
  y_s : (VG.Proof.AesGcm.X86_64.Blocks.yR s).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.sR s)
  y_a : (VG.Proof.AesGcm.X86_64.Blocks.yR s).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.aR s)
  d_s : (VG.Proof.AesGcm.X86_64.Blocks.dR s).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.sR s)
  d_a : (VG.Proof.AesGcm.X86_64.Blocks.dR s).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.aR s)
  s_a : (VG.Proof.AesGcm.X86_64.Blocks.sR s).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.aR s)
  r_c : (⟨VG.Proof.AesGcm.X86_64.Blocks.SP s, 8⟩ : Region).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.cR s)
  r_y : (⟨VG.Proof.AesGcm.X86_64.Blocks.SP s, 8⟩ : Region).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.yR s)
  r_d : (⟨VG.Proof.AesGcm.X86_64.Blocks.SP s, 8⟩ : Region).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.dR s)
  r_s : (⟨VG.Proof.AesGcm.X86_64.Blocks.SP s, 8⟩ : Region).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.sR s)
  t_k : (below (VG.Proof.AesGcm.X86_64.Blocks.SP s) 8).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.kR s)
  t_c : (below (VG.Proof.AesGcm.X86_64.Blocks.SP s) 8).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.cR s)
  t_y : (below (VG.Proof.AesGcm.X86_64.Blocks.SP s) 8).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.yR s)
  t_d : (below (VG.Proof.AesGcm.X86_64.Blocks.SP s) 8).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.dR s)
  t_s : (below (VG.Proof.AesGcm.X86_64.Blocks.SP s) 8).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.sR s)
  w_k : (VG.Proof.AesGcm.X86_64.Blocks.K s).toNat + 256 ≤ 2 ^ 64
  w_c : (VG.Proof.AesGcm.X86_64.Blocks.C s).toNat + 16 ≤ 2 ^ 64
  w_y : (VG.Proof.AesGcm.X86_64.Blocks.Y s).toNat + 16 ≤ 2 ^ 64
  w_d : (VG.Proof.AesGcm.X86_64.Blocks.D s).toNat + VG.Proof.AesGcm.X86_64.Blocks.n s * 16 ≤ 2 ^ 64
  w_s : (VG.Proof.AesGcm.X86_64.Blocks.S s).toNat + 2112 ≤ 2 ^ 64
  w_sp : (VG.Proof.AesGcm.X86_64.Blocks.SP s).toNat + 16 ≤ 2 ^ 64
  rounds : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14

theorem BP.of {s : State} (h : Proof.AesGcm.blocksPre s) : VG.Proof.AesGcm.X86_64.Blocks.BP s := by
  simp only [Proof.AesGcm.blocksPre, Proof.AesGcm.args, Proof.AesGcm.arg, Proof.AesGcm.ret, Proof.AesGcm.stk,
    Proof.AesGcm.rounds] at h
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at h
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂, a₂₃,
    a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂⟩ := h
  exact ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂, a₂₃,
    a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂⟩

/-! ## The arguments kept -/

/-- The arguments kept in `scratch` at `S`: the data and the number of blocks
of what is left after `q` blocks. -/
structure Kept (s : State) (q : Nat) (m : Mem) : Prop where
  ctx : m.readW (VG.Proof.AesGcm.X86_64.Blocks.S s) 64 = VG.Proof.AesGcm.X86_64.Blocks.K s
  rounds : m.readW (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 8) 64 = s.gpr .rsi
  ctr : m.readW (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 16) 64 = VG.Proof.AesGcm.X86_64.Blocks.C s
  y : m.readW (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 24) 64 = VG.Proof.AesGcm.X86_64.Blocks.Y s
  data : m.readW (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 32) 64 = VG.Proof.AesGcm.X86_64.Blocks.D s + BitVec.ofNat 64 (16 * q)
  n : m.readW (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (VG.Proof.AesGcm.X86_64.Blocks.n s - q)

/-- The slots of the arguments kept. -/
abbrev kR' (s : State) : Region := ⟨VG.Proof.AesGcm.X86_64.Blocks.S s, 48⟩

section
variable {s : State} (hp : VG.Proof.AesGcm.X86_64.Blocks.BP s)
include hp

theorem s_in {d k : Nat} (h : d + k ≤ 2112) : InRegions s.wr (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 d) k :=
  in_off (rs := s.wr) (by rw [hp.wr]; exact covers_of_mem (by simp)) h (by decide)

theorem s_in' {d k : Nat} (h : d + k ≤ 2112) : InRegions (s.rd ++ s.wr) (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 d) k :=
  in_left (VG.Proof.AesGcm.X86_64.Blocks.s_in hp h)

theorem a_in : InRegions (s.rd ++ s.wr) (VG.Proof.AesGcm.X86_64.Blocks.SP s + BitVec.ofNat 64 8) 8 :=
  ⟨VG.Proof.AesGcm.X86_64.Blocks.aR s, by rw [hp.rd]; simp, Region.contains_self _ _⟩

omit hp in
/-- The slots of the arguments are in `scratch`, apart from the powers. -/
theorem kR'_sub : (VG.Proof.AesGcm.X86_64.Blocks.kR' s).Sub (VG.Proof.AesGcm.X86_64.Blocks.sR s) := Region.sub_prefix (by decide)

/-- What a frame of the regions written keeps: the stack argument and the
return address. -/
theorem keep_a {m m' : Mem} (hf : Frame (VG.Proof.AesGcm.X86_64.Blocks.wR s) m m') : m'.readW (VG.Proof.AesGcm.X86_64.Blocks.SP s + BitVec.ofNat 64 8) 64 =
    m.readW (VG.Proof.AesGcm.X86_64.Blocks.SP s + BitVec.ofNat 64 8) 64 :=
  hf.readW (r := VG.Proof.AesGcm.X86_64.Blocks.aR s) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.c_a.symm
    · exact hp.y_a.symm
    · exact hp.d_a.symm
    · exact hp.s_a.symm) (by decide)

theorem keep_r {m m' : Mem} (hf : Frame (VG.Proof.AesGcm.X86_64.Blocks.wR s) m m') : m'.readW (VG.Proof.AesGcm.X86_64.Blocks.SP s) 64 = m.readW (VG.Proof.AesGcm.X86_64.Blocks.SP s) 64 :=
  hf.readW (r := ⟨VG.Proof.AesGcm.X86_64.Blocks.SP s, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.r_c
    · exact hp.r_y
    · exact hp.r_d
    · exact hp.r_s) (by decide)

/-- The key context, through a frame of the regions written. -/
theorem keep_k {m m' : Mem} (hf : Frame (VG.Proof.AesGcm.X86_64.Blocks.wR s) m m') {d k : Nat} (h : d + k ≤ 256) :
    Spec.Aes.bytesAt m' (VG.Proof.AesGcm.X86_64.Blocks.K s + BitVec.ofNat 64 d) k = Spec.Aes.bytesAt m (VG.Proof.AesGcm.X86_64.Blocks.K s + BitVec.ofNat 64 d) k :=
  bytesAt_frame hf (fun r hr => by
    have hs : Region.Sub ⟨VG.Proof.AesGcm.X86_64.Blocks.K s + BitVec.ofNat 64 d, k⟩ (VG.Proof.AesGcm.X86_64.Blocks.kR s) := Offset.sub_base _ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.k_c.sub_left hs
    · exact hp.k_y.sub_left hs
    · exact hp.k_d.sub_left hs
    · exact hp.k_s.sub_left hs) (by omega)

omit hp in
theorem arg_eq : s.mem.readW (VG.Proof.AesGcm.X86_64.Blocks.SP s + BitVec.ofNat 64 8) 64 = VG.Proof.AesGcm.X86_64.Blocks.S s := rfl

/-- The entry: the arguments kept, with `scratch` in `r11`. -/
theorem entry_ok : WP isa (.block entry) s fun s₁ => s₁.gpr .r11 = VG.Proof.AesGcm.X86_64.Blocks.S s ∧ (∀ r, r ≠ .r11 → s₁.gpr r = s.gpr r) ∧
    VG.Proof.AesGcm.X86_64.Blocks.Kept s 0 s₁.mem ∧ Frame [VG.Proof.AesGcm.X86_64.Blocks.kR' s] s.mem s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have w₁ := VG.Proof.AesGcm.X86_64.Blocks.s_in hp (show 0 + 8 ≤ 2112 by decide)
  have w₂ := VG.Proof.AesGcm.X86_64.Blocks.s_in hp (show 8 + 8 ≤ 2112 by decide)
  have w₃ := VG.Proof.AesGcm.X86_64.Blocks.s_in hp (show 16 + 8 ≤ 2112 by decide)
  have w₄ := VG.Proof.AesGcm.X86_64.Blocks.s_in hp (show 24 + 8 ≤ 2112 by decide)
  have w₅ := VG.Proof.AesGcm.X86_64.Blocks.s_in hp (show 32 + 8 ≤ 2112 by decide)
  have w₆ := VG.Proof.AesGcm.X86_64.Blocks.s_in hp (show 40 + 8 ≤ 2112 by decide)
  have a₀ := VG.Proof.AesGcm.X86_64.Blocks.a_in hp
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2112 → d + 8 ≤ 2112 →
      Mem.Sep (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 a) (64 / 8) (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep _ h (by omega) (by omega)
  have s₁₂ := sep 0 8 (by decide) (by decide) (by decide)
  have s₁₃ := sep 0 16 (by decide) (by decide) (by decide)
  have s₁₄ := sep 0 24 (by decide) (by decide) (by decide)
  have s₁₅ := sep 0 32 (by decide) (by decide) (by decide)
  have s₁₆ := sep 0 40 (by decide) (by decide) (by decide)
  simp only [BitVec.add_zero] at s₁₂ s₁₃ s₁₄ s₁₅ s₁₆
  have s₂₃ := sep 8 16 (by decide) (by decide) (by decide)
  have s₂₄ := sep 8 24 (by decide) (by decide) (by decide)
  have s₂₅ := sep 8 32 (by decide) (by decide) (by decide)
  have s₂₆ := sep 8 40 (by decide) (by decide) (by decide)
  have s₃₄ := sep 16 24 (by decide) (by decide) (by decide)
  have s₃₅ := sep 16 32 (by decide) (by decide) (by decide)
  have s₃₆ := sep 16 40 (by decide) (by decide) (by decide)
  have s₄₅ := sep 24 32 (by decide) (by decide) (by decide)
  have s₄₆ := sep 24 40 (by decide) (by decide) (by decide)
  have s₅₆ := sep 32 40 (by decide) (by decide) (by decide)
  have hn : BitVec.ofNat 64 (VG.Proof.AesGcm.X86_64.Blocks.n s - 0) = s.gpr .r9 := by simp
  apply WP.of_runBlock
  refine ⟨_, by simp only [entry, argCtx, argRounds, argCtr, argY, argData, argN]; xrun [a₀, VG.Proof.AesGcm.X86_64.Blocks.arg_eq, w₁, w₂, w₃, w₄, w₅, w₆],
    ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · intro r hr; simp [gpr_setReg, hr]
  all_goals try simp (disch := first | decide | assumption) only [gpr_setReg, ite_true, reduceCtorEq, ↓reduceIte,
    Mem.readW_writeW_self64, Mem.readW_writeW_sep, Nat.mul_zero, BitVec.add_zero, hn]
  · have c : ∀ d, 0 ≤ d → d + 8 ≤ 48 → (VG.Proof.AesGcm.X86_64.Blocks.kR' s).Contains (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d _ h₂ => Offset.contains_base _ h₂ (by omega)
    have c0 : (VG.Proof.AesGcm.X86_64.Blocks.kR' s).Contains (VG.Proof.AesGcm.X86_64.Blocks.S s) (64 / 8) := by simpa using c 0 (by decide) (by decide)
    exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW
      (List.mem_singleton_self _) _ (c 8 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 16 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 24 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 32 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 40 (by decide) (by decide))

end

end VG.Proof.AesGcm.X86_64.Blocks

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Mid`. -/
section

/-!
# AES-GCM on whole blocks, x86-64: after the first blocks

Untrusted: everything here is checked by Lean. `Mid s q k ys` holds once the
first `q` blocks are encrypted (or decrypted) and `ys` hashed, with the
arguments kept for the rest after `k` blocks: after the entry (`mid_entry`,
with `q = k = 0`), and after `rest` (`rest_ok`, `k = q`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

section
variable (s : State)

abbrev R : Nat := (s.gpr .rsi).toNat
abbrev ciph : Block → Block := ctxCiph s.mem (VG.Proof.AesGcm.X86_64.Blocks.K s) (VG.Proof.AesGcm.X86_64.Blocks.R s)
abbrev cb : Block := blockAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.C s)
abbrev hk : Block := ctxH s.mem (VG.Proof.AesGcm.X86_64.Blocks.K s)
abbrev y₀ : Block := blockAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.Y s)
/-- Where the data left after `q` blocks starts. -/
abbrev dq (q : Nat) : Addr := VG.Proof.AesGcm.X86_64.Blocks.D s + BitVec.ofNat 64 (16 * q)

end

/-- The first `q` blocks done and `ys` hashed, the arguments kept for what
is left after `k` blocks. -/
structure Mid (s : State) (q k : Nat) (ys : List Block) (st : State) : Prop where
  q_le : q ≤ VG.Proof.AesGcm.X86_64.Blocks.n s
  rsp : st.gpr .rsp = VG.Proof.AesGcm.X86_64.Blocks.SP s
  saved : ∀ r ∈ calleeSaved, st.gpr r = s.gpr r
  rd : st.rd = s.rd
  wr : st.wr = s.wr
  kept : VG.Proof.AesGcm.X86_64.Blocks.Kept s k st.mem
  frame : Frame (VG.Proof.AesGcm.X86_64.Blocks.wR s) s.mem st.mem
  data : blocksAt st.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q = ctr32 (VG.Proof.AesGcm.X86_64.Blocks.ciph s) (VG.Proof.AesGcm.X86_64.Blocks.cb s) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q)
  rest : blocksAt st.mem (VG.Proof.AesGcm.X86_64.Blocks.dq s q) (VG.Proof.AesGcm.X86_64.Blocks.n s - q) = blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.dq s q) (VG.Proof.AesGcm.X86_64.Blocks.n s - q)
  ctr : blockAt st.mem (VG.Proof.AesGcm.X86_64.Blocks.C s) = Nat.repeat inc32 q (VG.Proof.AesGcm.X86_64.Blocks.cb s)
  y : blockAt st.mem (VG.Proof.AesGcm.X86_64.Blocks.Y s) = ghashFrom (VG.Proof.AesGcm.X86_64.Blocks.hk s) (VG.Proof.AesGcm.X86_64.Blocks.y₀ s) ys

section
variable {s : State} (hp : VG.Proof.AesGcm.X86_64.Blocks.BP s)
include hp

/-- The slots of the arguments are apart from the other regions written. -/
theorem kR'_disj : ∀ r ∈ [VG.Proof.AesGcm.X86_64.Blocks.cR s, VG.Proof.AesGcm.X86_64.Blocks.yR s, VG.Proof.AesGcm.X86_64.Blocks.dR s], (VG.Proof.AesGcm.X86_64.Blocks.kR' s).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.c_s.sub_right (VG.Proof.AesGcm.X86_64.Blocks.kR'_sub (s := s))).symm
  · exact (hp.y_s.sub_right (VG.Proof.AesGcm.X86_64.Blocks.kR'_sub (s := s))).symm
  · exact (hp.d_s.sub_right (VG.Proof.AesGcm.X86_64.Blocks.kR'_sub (s := s))).symm

omit hp in
theorem Kept.frame {k : Nat} {m m' : Mem} (h : VG.Proof.AesGcm.X86_64.Blocks.Kept s k m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (VG.Proof.AesGcm.X86_64.Blocks.kR' s).Disjoint r) : VG.Proof.AesGcm.X86_64.Blocks.Kept s k m' := by
  have e : ∀ d, d + 8 ≤ 48 → m'.readW (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 d) 64 = m.readW (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 d) 64 :=
    fun d h₁ => hf.readW (Offset.contains_base _ h₁ (by omega)) hd (by decide)
  have e0 : m'.readW (VG.Proof.AesGcm.X86_64.Blocks.S s) 64 = m.readW (VG.Proof.AesGcm.X86_64.Blocks.S s) 64 := by simpa using e 0 (by decide)
  exact ⟨by rw [e0]; exact h.ctx, by rw [e 8 (by decide)]; exact h.rounds,
    by rw [e 16 (by decide)]; exact h.ctr, by rw [e 24 (by decide)]; exact h.y,
    by rw [e 32 (by decide)]; exact h.data, by rw [e 40 (by decide)]; exact h.n⟩

omit hp in
/-- A frame of `scratch`'s slots keeps a block apart from them. -/
theorem block_kR' {m m' : Mem} (hf : Frame [VG.Proof.AesGcm.X86_64.Blocks.kR' s] m m') {p : Addr} (hd : (⟨p, 16⟩ : Region).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.kR' s)) :
    blockAt m' p = blockAt m p :=
  blockAt_frame hf fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd

theorem mid_entry {s₁ : State} (hg : ∀ r, r ≠ .r11 → s₁.gpr r = s.gpr r)
    (hk : VG.Proof.AesGcm.X86_64.Blocks.Kept s 0 s₁.mem) (hf : Frame [VG.Proof.AesGcm.X86_64.Blocks.kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    VG.Proof.AesGcm.X86_64.Blocks.Mid s 0 0 [] s₁ := by
  have hfw : Frame (VG.Proof.AesGcm.X86_64.Blocks.wR s) s.mem s₁.mem :=
    hf.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesGcm.X86_64.Blocks.sR s, by simp, VG.Proof.AesGcm.X86_64.Blocks.kR'_sub⟩
  refine ⟨Nat.zero_le _, hg _ (by decide), fun r hr => hg r ?_, hrd, hwr, hk, hfw, rfl, ?_, ?_, ?_⟩
  · intro e; subst e; simp [calleeSaved] at hr
  · simp only [VG.Proof.AesGcm.X86_64.Blocks.dq, Nat.mul_zero, BitVec.add_zero, Nat.sub_zero]
    have hd : (⟨VG.Proof.AesGcm.X86_64.Blocks.D s, 16 * VG.Proof.AesGcm.X86_64.Blocks.n s⟩ : Region).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.kR' s) := by
      rw [Nat.mul_comm]; exact (VG.Proof.AesGcm.X86_64.Blocks.kR'_disj hp (VG.Proof.AesGcm.X86_64.Blocks.dR s) (by simp)).symm
    exact blocksAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) (by
      have := hp.w_d; omega)
  · exact VG.Proof.AesGcm.X86_64.Blocks.block_kR' hf (VG.Proof.AesGcm.X86_64.Blocks.kR'_disj hp _ (by simp)).symm
  · exact VG.Proof.AesGcm.X86_64.Blocks.block_kR' hf (VG.Proof.AesGcm.X86_64.Blocks.kR'_disj hp _ (by simp)).symm

/-- `Mid` through a frame of `scratch`'s slots that keeps the registers but
`r11`, `r8` and `rax`. -/
theorem Mid.slots {q k k' : Nat} {ys : List Block} {st st' : State} (h : VG.Proof.AesGcm.X86_64.Blocks.Mid s q k ys st)
    (hg : ∀ r, r ≠ .r11 → r ≠ .r8 → r ≠ .rax → st'.gpr r = st.gpr r) (hk : VG.Proof.AesGcm.X86_64.Blocks.Kept s k' st'.mem)
    (hf : Frame [VG.Proof.AesGcm.X86_64.Blocks.kR' s] st.mem st'.mem) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) : VG.Proof.AesGcm.X86_64.Blocks.Mid s q k' ys st' := by
  have hfw : Frame (VG.Proof.AesGcm.X86_64.Blocks.wR s) st.mem st'.mem :=
    hf.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesGcm.X86_64.Blocks.sR s, by simp, VG.Proof.AesGcm.X86_64.Blocks.kR'_sub⟩
  refine ⟨h.q_le, by rw [hg _ (by decide) (by decide) (by decide), h.rsp], fun r hr => ?_, hrd.trans h.rd,
    hwr.trans h.wr, hk, h.frame.trans hfw, ?_, ?_, ?_, ?_⟩
  · rw [hg r (fun e => by subst e; simp [calleeSaved] at hr) (fun e => by subst e; simp [calleeSaved] at hr)
      (fun e => by subst e; simp [calleeSaved] at hr), h.saved r hr]
  · rw [← h.data]
    exact blocksAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (VG.Proof.AesGcm.X86_64.Blocks.kR'_disj hp (VG.Proof.AesGcm.X86_64.Blocks.dR s) (by simp)).symm.sub_left (Region.sub_prefix (by have := h.q_le; omega)))
      (by have := hp.w_d; have := h.q_le; omega)
  · rw [← h.rest]
    exact blocksAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (VG.Proof.AesGcm.X86_64.Blocks.kR'_disj hp (VG.Proof.AesGcm.X86_64.Blocks.dR s) (by simp)).symm.sub_left (Offset.sub_base (VG.Proof.AesGcm.X86_64.Blocks.D s) (by have := h.q_le; omega)))
      (by have := hp.w_d; have := h.q_le; omega)
  · rw [← h.ctr]; exact VG.Proof.AesGcm.X86_64.Blocks.block_kR' hf (VG.Proof.AesGcm.X86_64.Blocks.kR'_disj hp _ (by simp)).symm
  · rw [← h.y]; exact VG.Proof.AesGcm.X86_64.Blocks.block_kR' hf (VG.Proof.AesGcm.X86_64.Blocks.kR'_disj hp _ (by simp)).symm

/-- `rest`: the arguments of the `n mod 16` blocks after the first
`16 ⌊n / 16⌋`. -/
theorem rest_ok {q : Nat} (hq : q = VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16) {ys : List Block} {st : State} (h : VG.Proof.AesGcm.X86_64.Blocks.Mid s q 0 ys st) :
    WP isa (.block rest) st (VG.Proof.AesGcm.X86_64.Blocks.Mid s q q ys) := by
  have hn : VG.Proof.AesGcm.X86_64.Blocks.n s < 2 ^ 64 := (s.gpr .r9).isLt
  have a₀ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact VG.Proof.AesGcm.X86_64.Blocks.a_in hp
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 8) 64 = VG.Proof.AesGcm.X86_64.Blocks.S s := by
    rw [h.rsp, VG.Proof.AesGcm.X86_64.Blocks.keep_a hp h.frame]; rfl
  have r₅ : InRegions (st.rd ++ st.wr) (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 32) 8 := by rw [h.rd, h.wr]; exact VG.Proof.AesGcm.X86_64.Blocks.s_in' hp (by decide)
  have r₆ : InRegions (st.rd ++ st.wr) (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact VG.Proof.AesGcm.X86_64.Blocks.s_in' hp (by decide)
  have w₅ : InRegions st.wr (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 32) 8 := by rw [h.wr]; exact VG.Proof.AesGcm.X86_64.Blocks.s_in hp (by decide)
  have w₆ : InRegions st.wr (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 40) 8 := by rw [h.wr]; exact VG.Proof.AesGcm.X86_64.Blocks.s_in hp (by decide)
  have kd := h.kept.data
  have kn := h.kept.n
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.sub_zero] at kd kn
  have e15 := and15 (BitVec.ofNat 64 (VG.Proof.AesGcm.X86_64.Blocks.n s))
  rw [toNat_ofNat_of_lt hn, imm_eq (by decide)] at e15
  have esub : BitVec.ofNat 64 (VG.Proof.AesGcm.X86_64.Blocks.n s) - BitVec.ofNat 64 (VG.Proof.AesGcm.X86_64.Blocks.n s % 16) = BitVec.ofNat 64 q := by
    rw [hq]; exact ofNat_sub (Nat.mod_le _ _) hn
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2112 → d + 8 ≤ 2112 →
      Mem.Sep (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 a) (64 / 8) (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep _ h (by omega) (by omega)
  have kp : ∀ d, d + 8 ≤ 32 → ∀ v w : BitVec 64,
      ((st.mem.writeW (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 32) v).writeW (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 40) w).readW
        (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 d) 64 = st.mem.readW (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 d) 64 := fun d h₁ v w => by
    rw [Mem.readW_writeW_sep (sep d 40 (.inl (by omega)) (by omega) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 32 (.inl (by omega)) (by omega) (by decide)) (by decide)]
  apply WP.of_runBlock
  refine ⟨_, by simp only [rest, argData, argN]; xrun [a₀, hS, r₅, r₆, w₅, w₆, kn, e15, esub, times16_val, kd], ?_⟩
  refine h.slots hp (fun r h1 h2 h3 => by simp [gpr_setReg, gpr_arithFlags, h1, h2, h3]) ?_ ?_ rfl rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := kp 0 (by decide); simp only [BitVec.add_zero] at this; rw [this]; exact h.kept.ctx
    · rw [kp 8 (by decide)]; exact h.kept.rounds
    · rw [kp 16 (by decide)]; exact h.kept.ctr
    · rw [kp 24 (by decide)]; exact h.kept.y
    · rw [Mem.readW_writeW_sep (sep 32 40 (.inl (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64, BitVec.add_comm]
    · rw [Mem.readW_writeW_self64, hq]; congr 1; omega
  · have c : ∀ d, d + 8 ≤ 48 → (VG.Proof.AesGcm.X86_64.Blocks.kR' s).Contains (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ => Offset.contains_base _ h₁ (by omega)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 32 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 40 (by decide))

end

end VG.Proof.AesGcm.X86_64.Blocks

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Tail`. -/
section

/-!
# AES-GCM on whole blocks, x86-64: the blocks left

Untrusted: everything here is checked by Lean. From `Mid s q q ys`, the
`n - q` blocks left, if any, are encrypted with `vg_aes_ctr32` and hashed
with `vg_ghash` (`encTail_ok`), or hashed and then decrypted (`decTail_ok`),
with the arguments reloaded from `scratch` for each call (`ctrArgs_ok`,
`ghArgs_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

/-- A prefix of a region that `rs` covers. -/
theorem covers_prefix {b : Addr} {k L : Nat} {rs : List Region} (h : Covers [⟨b, L⟩] rs) (hk : k ≤ L) :
    Covers [⟨b, k⟩] rs := fun a m ⟨r, hr, hc⟩ => by
  simp only [List.mem_singleton] at hr; subst hr
  exact h a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩

/-- `covers_off` without a bound on the region's length. -/
theorem covers_off' {p : Addr} {k d m : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + m ≤ k)
    (hd' : d < 2 ^ 64) : Covers [⟨p + BitVec.ofNat 64 d, m⟩] rs := by
  intro a j ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  refine h a j ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [Region.Contains] at hc ⊢
  have e : a - p = (a - (p + BitVec.ofNat 64 d)) + BitVec.ofNat 64 d := by
    rw [Offset.sub_add_eq]; exact (BitVec.sub_add_cancel _ _).symm
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) hd']
  have := Nat.mod_le ((a - (p + BitVec.ofNat 64 d)).toNat + d) (2 ^ 64)
  omega

/-- What the calls need of the state: the stack pointer, the permissions, the
arguments kept for what is left after `q` blocks, and `scratch` on the stack. -/
structure Ready (s : State) (q : Nat) (st : State) : Prop where
  rsp : st.gpr .rsp = VG.Proof.AesGcm.X86_64.Blocks.SP s
  rd : st.rd = s.rd
  wr : st.wr = s.wr
  kept : VG.Proof.AesGcm.X86_64.Blocks.Kept s q st.mem
  arg : st.mem.readW (VG.Proof.AesGcm.X86_64.Blocks.SP s + BitVec.ofNat 64 8) 64 = VG.Proof.AesGcm.X86_64.Blocks.S s

/-- What the calls' working space is. -/
abbrev S5 (s : State) : Addr := VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 64

section
variable {s : State} (hp : VG.Proof.AesGcm.X86_64.Blocks.BP s)
include hp

theorem cov_k : Covers [VG.Proof.AesGcm.X86_64.Blocks.kR s] (s.rd ++ s.wr) := covers_of_mem (by rw [hp.rd]; simp)
theorem cov_c : Covers [VG.Proof.AesGcm.X86_64.Blocks.cR s] s.wr := covers_of_mem (by rw [hp.wr]; simp)
theorem cov_y : Covers [VG.Proof.AesGcm.X86_64.Blocks.yR s] s.wr := covers_of_mem (by rw [hp.wr]; simp)
theorem cov_d : Covers [VG.Proof.AesGcm.X86_64.Blocks.dR s] s.wr := covers_of_mem (by rw [hp.wr]; simp)
theorem cov_s : Covers [VG.Proof.AesGcm.X86_64.Blocks.sR s] s.wr := covers_of_mem (by rw [hp.wr]; simp)

omit hp in
/-- The data left after `q` blocks is in the data. -/
theorem dq_sub {q : Nat} (hq : q ≤ VG.Proof.AesGcm.X86_64.Blocks.n s) : Region.Sub ⟨VG.Proof.AesGcm.X86_64.Blocks.dq s q, 16 * (VG.Proof.AesGcm.X86_64.Blocks.n s - q)⟩ (VG.Proof.AesGcm.X86_64.Blocks.dR s) :=
  Offset.sub_base _ (by omega)

omit hp in
theorem s5_sub {k : Nat} (hk : k ≤ 2048) : Region.Sub ⟨VG.Proof.AesGcm.X86_64.Blocks.S5 s, k⟩ (VG.Proof.AesGcm.X86_64.Blocks.sR s) := Offset.sub_base _ (by omega)

/-- The head of `tail`: `r8` the number of blocks left, `ZF` if none. -/
theorem tailHead_ok {q : Nat} {ys : List Block} {st : State} (h : VG.Proof.AesGcm.X86_64.Blocks.Mid s q q ys st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 8)), .mov .r8 (.mem (at_ .r11 argN)), .alu .test .r8 (.reg .r8)])
      st fun st' => VG.Proof.AesGcm.X86_64.Blocks.Mid s q q ys st' ∧ st'.zf = some (decide (VG.Proof.AesGcm.X86_64.Blocks.n s - q = 0)) := by
  have hn : VG.Proof.AesGcm.X86_64.Blocks.n s < 2 ^ 64 := (s.gpr .r9).isLt
  have a₀ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact VG.Proof.AesGcm.X86_64.Blocks.a_in hp
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 8) 64 = VG.Proof.AesGcm.X86_64.Blocks.S s := by rw [h.rsp, VG.Proof.AesGcm.X86_64.Blocks.keep_a hp h.frame]; rfl
  have r₆ : InRegions (st.rd ++ st.wr) (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact VG.Proof.AesGcm.X86_64.Blocks.s_in' hp (by decide)
  have hz := and_self_beq (show VG.Proof.AesGcm.X86_64.Blocks.n s - q < 2 ^ 64 by omega)
  apply WP.of_runBlock
  refine ⟨_, by simp only [argN]; xrun [a₀, hS, r₆, h.kept.n], ?_, by simp only [zf_arithFlags, hz]⟩
  exact h.slots hp (fun r h1 h2 h3 => by simp [gpr_setReg, gpr_arithFlags, h1, h2]) h.kept (Frame.refl _ _) rfl rfl

theorem Mid.ready {q k : Nat} {ys : List Block} {st : State} (h : VG.Proof.AesGcm.X86_64.Blocks.Mid s q k ys st) : VG.Proof.AesGcm.X86_64.Blocks.Ready s k st :=
  ⟨h.rsp, h.rd, h.wr, h.kept, by rw [VG.Proof.AesGcm.X86_64.Blocks.keep_a hp h.frame]; rfl⟩

/-- The arguments of `vg_aes_ctr32` on the `n - q` blocks left. -/
theorem ctrArgs_ok {q : Nat} {st : State} (h : VG.Proof.AesGcm.X86_64.Blocks.Ready s q st) (hq : q < VG.Proof.AesGcm.X86_64.Blocks.n s) :
    WP isa (.block ctrArgs) st fun st' => CtrCall st' (VG.Proof.AesGcm.X86_64.Blocks.K s) (VG.Proof.AesGcm.X86_64.Blocks.C s) (VG.Proof.AesGcm.X86_64.Blocks.dq s q) (VG.Proof.AesGcm.X86_64.Blocks.S5 s) (VG.Proof.AesGcm.X86_64.Blocks.R s) (VG.Proof.AesGcm.X86_64.Blocks.n s - q) ∧
      VG.Proof.AesGcm.X86_64.Blocks.Ready s q st' ∧ (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem := by
  have hn : VG.Proof.AesGcm.X86_64.Blocks.n s < 2 ^ 64 := (s.gpr .r9).isLt
  have hw := hp.w_d
  have a₀ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact VG.Proof.AesGcm.X86_64.Blocks.a_in hp
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 8) 64 = VG.Proof.AesGcm.X86_64.Blocks.S s := by rw [h.rsp, h.arg]
  have r₁ : InRegions (st.rd ++ st.wr) (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 0) 8 := by rw [h.rd, h.wr]; exact VG.Proof.AesGcm.X86_64.Blocks.s_in' hp (by decide)
  have kc0 : st.mem.readW (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 0) 64 = VG.Proof.AesGcm.X86_64.Blocks.K s := by simpa using h.kept.ctx
  have r₂ : InRegions (st.rd ++ st.wr) (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 8) 8 := by rw [h.rd, h.wr]; exact VG.Proof.AesGcm.X86_64.Blocks.s_in' hp (by decide)
  have r₃ : InRegions (st.rd ++ st.wr) (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 16) 8 := by rw [h.rd, h.wr]; exact VG.Proof.AesGcm.X86_64.Blocks.s_in' hp (by decide)
  have r₅ : InRegions (st.rd ++ st.wr) (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 32) 8 := by rw [h.rd, h.wr]; exact VG.Proof.AesGcm.X86_64.Blocks.s_in' hp (by decide)
  have r₆ : InRegions (st.rd ++ st.wr) (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact VG.Proof.AesGcm.X86_64.Blocks.s_in' hp (by decide)
  have hdq : Region.Sub ⟨VG.Proof.AesGcm.X86_64.Blocks.dq s q, 16 * (VG.Proof.AesGcm.X86_64.Blocks.n s - q)⟩ (VG.Proof.AesGcm.X86_64.Blocks.dR s) := VG.Proof.AesGcm.X86_64.Blocks.dq_sub (by omega)
  have p240 : Region.Sub ⟨VG.Proof.AesGcm.X86_64.Blocks.K s, 240⟩ (VG.Proof.AesGcm.X86_64.Blocks.kR s) := Region.sub_prefix (by decide)
  have s48 : Region.Sub ⟨VG.Proof.AesGcm.X86_64.Blocks.S5 s, 2048⟩ (VG.Proof.AesGcm.X86_64.Blocks.sR s) := VG.Proof.AesGcm.X86_64.Blocks.s5_sub (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [ctrArgs, argCtx, argRounds, argCtr, argData, argN]
    xrun [a₀, hS, r₁, r₂, r₃, r₅, r₆, kc0, h.kept.rounds, h.kept.ctr, h.kept.data, h.kept.n], ?_⟩
  refine ⟨⟨by simp [gpr_setReg], by simp [gpr_setReg, VG.Proof.AesGcm.X86_64.Blocks.R], by simp [gpr_setReg], by simp [gpr_setReg, VG.Proof.AesGcm.X86_64.Blocks.dq],
    by simp [gpr_setReg], by simp [gpr_setReg, gpr_arithFlags, VG.Proof.AesGcm.X86_64.Blocks.S5], hp.rounds, ?_,
    hp.k_c.sub_left p240, (hp.k_d.sub_left p240).sub_right hdq, (hp.k_s.sub_left p240).sub_right s48,
    hp.c_d.sub_right hdq, hp.c_s.sub_right s48, (hp.d_s.sub_left hdq).sub_right s48, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨by simp [gpr_setReg, gpr_arithFlags, h.rsp], h.rd, h.wr, h.kept, h.arg⟩, fun r hr => ?_, rfl⟩
  · simp only [VG.Proof.AesGcm.X86_64.Blocks.dq, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := Nat.mod_le ((VG.Proof.AesGcm.X86_64.Blocks.D s).toNat + 16 * q % 2 ^ 64) (2 ^ 64)
    rw [Nat.mod_eq_of_lt (a := 16 * q) (by omega)]; omega
  all_goals try simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ↓reduceIte, h.rsp]
  · exact hp.t_k.sub_right p240
  · exact hp.t_c
  · exact hp.t_d.sub_right hdq
  · exact hp.t_s.sub_right s48
  · simp only [rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, h.rd, h.wr]
    refine covers_cons (VG.Proof.AesGcm.X86_64.Blocks.covers_prefix (VG.Proof.AesGcm.X86_64.Blocks.cov_k hp) (by decide)) (covers_cons (covers_left (VG.Proof.AesGcm.X86_64.Blocks.cov_c hp))
      (covers_cons (covers_left (VG.Proof.AesGcm.X86_64.Blocks.covers_off' (VG.Proof.AesGcm.X86_64.Blocks.cov_d hp) (by omega) (by omega)))
        (covers_left (covers_off (VG.Proof.AesGcm.X86_64.Blocks.cov_s hp) (by decide) (by decide)))))
  · simp only [wr_setReg, wr_arithFlags, h.wr]
    exact covers_cons (VG.Proof.AesGcm.X86_64.Blocks.cov_c hp) (covers_cons (VG.Proof.AesGcm.X86_64.Blocks.covers_off' (VG.Proof.AesGcm.X86_64.Blocks.cov_d hp) (by omega) (by omega))
      (covers_off (VG.Proof.AesGcm.X86_64.Blocks.cov_s hp) (by decide) (by decide)))
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]

/-- The data is not all of memory: the key context is apart from it. -/
theorem n16_lt : VG.Proof.AesGcm.X86_64.Blocks.n s * 16 < 2 ^ 64 := by
  have hw := hp.w_d
  refine Nat.lt_of_not_le fun hge => hp.k_d (VG.Proof.AesGcm.X86_64.Blocks.K s) ?_ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [Region.Contains]
    have := (VG.Proof.AesGcm.X86_64.Blocks.K s - VG.Proof.AesGcm.X86_64.Blocks.D s).isLt
    omega

/-- The arguments of `vg_ghash` on the `n - q` blocks left. -/
theorem ghArgs_ok {q : Nat} {st : State} (h : VG.Proof.AesGcm.X86_64.Blocks.Ready s q st) (hq : q < VG.Proof.AesGcm.X86_64.Blocks.n s) :
    WP isa (.block ghArgs) st fun st' => GhCall st' (VG.Proof.AesGcm.X86_64.Blocks.K s + BitVec.ofNat 64 240) (VG.Proof.AesGcm.X86_64.Blocks.Y s) (VG.Proof.AesGcm.X86_64.Blocks.dq s q) (VG.Proof.AesGcm.X86_64.Blocks.S5 s) (VG.Proof.AesGcm.X86_64.Blocks.n s - q) ∧
      VG.Proof.AesGcm.X86_64.Blocks.Ready s q st' ∧ (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem := by
  have hn : VG.Proof.AesGcm.X86_64.Blocks.n s < 2 ^ 64 := (s.gpr .r9).isLt
  have hw := hp.w_d
  have h16 := VG.Proof.AesGcm.X86_64.Blocks.n16_lt hp
  have a₀ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact VG.Proof.AesGcm.X86_64.Blocks.a_in hp
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 8) 64 = VG.Proof.AesGcm.X86_64.Blocks.S s := by rw [h.rsp, h.arg]
  have r₁ : InRegions (st.rd ++ st.wr) (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 0) 8 := by rw [h.rd, h.wr]; exact VG.Proof.AesGcm.X86_64.Blocks.s_in' hp (by decide)
  have kc0 : st.mem.readW (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 0) 64 = VG.Proof.AesGcm.X86_64.Blocks.K s := by simpa using h.kept.ctx
  have r₄ : InRegions (st.rd ++ st.wr) (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 24) 8 := by rw [h.rd, h.wr]; exact VG.Proof.AesGcm.X86_64.Blocks.s_in' hp (by decide)
  have r₅ : InRegions (st.rd ++ st.wr) (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 32) 8 := by rw [h.rd, h.wr]; exact VG.Proof.AesGcm.X86_64.Blocks.s_in' hp (by decide)
  have r₆ : InRegions (st.rd ++ st.wr) (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact VG.Proof.AesGcm.X86_64.Blocks.s_in' hp (by decide)
  have hdq : Region.Sub ⟨VG.Proof.AesGcm.X86_64.Blocks.dq s q, 16 * (VG.Proof.AesGcm.X86_64.Blocks.n s - q)⟩ (VG.Proof.AesGcm.X86_64.Blocks.dR s) := VG.Proof.AesGcm.X86_64.Blocks.dq_sub (by omega)
  have pH : Region.Sub ⟨VG.Proof.AesGcm.X86_64.Blocks.K s + BitVec.ofNat 64 240, 16⟩ (VG.Proof.AesGcm.X86_64.Blocks.kR s) := Offset.sub_base _ (by decide)
  have s16 : Region.Sub ⟨VG.Proof.AesGcm.X86_64.Blocks.S5 s, 256⟩ (VG.Proof.AesGcm.X86_64.Blocks.sR s) := VG.Proof.AesGcm.X86_64.Blocks.s5_sub (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [ghArgs, argCtx, argY, argData, argN]
    xrun [a₀, hS, r₁, r₄, r₅, r₆, kc0, h.kept.y, h.kept.data, h.kept.n], ?_⟩
  refine ⟨⟨by simp [gpr_setReg, gpr_arithFlags], by simp [gpr_setReg], by simp [gpr_setReg, VG.Proof.AesGcm.X86_64.Blocks.dq],
    by simp [gpr_setReg], by simp [gpr_setReg, gpr_arithFlags, VG.Proof.AesGcm.X86_64.Blocks.S5], by omega,
    hp.k_y.sub_left pH, (hp.k_s.sub_left pH).sub_right s16, hp.y_d.sub_right hdq, hp.y_s.sub_right s16,
    (hp.d_s.sub_left hdq).sub_right s16, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨by simp [gpr_setReg, gpr_arithFlags, h.rsp], h.rd, h.wr, h.kept, h.arg⟩, fun r hr => ?_, rfl⟩
  all_goals try simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ↓reduceIte, h.rsp]
  · exact hp.t_k.sub_right pH
  · exact hp.t_y
  · exact hp.t_d.sub_right hdq
  · exact hp.t_s.sub_right s16
  · simp only [rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, h.rd, h.wr]
    refine covers_cons (covers_off (VG.Proof.AesGcm.X86_64.Blocks.cov_k hp) (by decide) (by decide))
      (covers_cons (covers_left (VG.Proof.AesGcm.X86_64.Blocks.covers_off' (VG.Proof.AesGcm.X86_64.Blocks.cov_d hp) (by omega) (by omega)))
      (covers_cons (covers_left (VG.Proof.AesGcm.X86_64.Blocks.cov_y hp)) (covers_left (covers_off (VG.Proof.AesGcm.X86_64.Blocks.cov_s hp) (by decide) (by decide)))))
  · simp only [wr_setReg, wr_arithFlags, h.wr]
    exact covers_cons (VG.Proof.AesGcm.X86_64.Blocks.cov_y hp) (covers_off (VG.Proof.AesGcm.X86_64.Blocks.cov_s hp) (by decide) (by decide))
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]

end

end VG.Proof.AesGcm.X86_64.Blocks

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Fin`. -/
section

/-!
# AES-GCM on whole blocks, x86-64: the end

Untrusted: everything here is checked by Lean. From `Mid s q q ys`, `tail`
calls `vg_aes_ctr32` and `vg_ghash` on the blocks left (if any), and
the counter mode and GHASH of the two parts make those of all the blocks
(`ctr32_append`, `ghashFrom_append`): `encTail_ok`, `decTail_ok`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- `scratch` on the stack is apart from the return addresses of calls. -/
theorem arg_below (SP : Addr) : (⟨SP + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint (below SP 8) :=
  Offset.disjoint_below SP (n := 8) (d := 8) (k := 8) (by decide)

/-- A region apart from what a call of `vg_aes_ctr32` or `vg_ghash` on the
blocks left writes. -/
structure Apart (s : State) (q : Nat) (r : Region) : Prop where
  c : r.Disjoint (VG.Proof.AesGcm.X86_64.Blocks.cR s)
  y : r.Disjoint (VG.Proof.AesGcm.X86_64.Blocks.yR s)
  d : r.Disjoint ⟨VG.Proof.AesGcm.X86_64.Blocks.dq s q, 16 * (VG.Proof.AesGcm.X86_64.Blocks.n s - q)⟩
  s5 : r.Disjoint ⟨VG.Proof.AesGcm.X86_64.Blocks.S5 s, 2048⟩
  t : r.Disjoint (below (VG.Proof.AesGcm.X86_64.Blocks.SP s) 8)

/-- The calls of `tail`, for `n - q > 0` blocks left after `Mid`. -/
structure Calls (s : State) (q : Nat) (st st₂ st₃ st₄ st₅ : State) : Prop where
  m₂ : st₂.mem = st.mem
  f₃ : Frame [VG.Proof.AesGcm.X86_64.Blocks.cR s, (⟨VG.Proof.AesGcm.X86_64.Blocks.dq s q, 16 * (VG.Proof.AesGcm.X86_64.Blocks.n s - q)⟩ : Region), ⟨VG.Proof.AesGcm.X86_64.Blocks.S5 s, 2048⟩, below (VG.Proof.AesGcm.X86_64.Blocks.SP s) 8] st₂.mem st₃.mem
  m₄ : st₄.mem = st₃.mem
  f₅ : Frame [VG.Proof.AesGcm.X86_64.Blocks.yR s, (⟨VG.Proof.AesGcm.X86_64.Blocks.S5 s, 256⟩ : Region), below (VG.Proof.AesGcm.X86_64.Blocks.SP s) 8] st₄.mem st₅.mem
  saved : ∀ r ∈ calleeSaved, st₅.gpr r = st.gpr r

section
variable {s : State} (hp : VG.Proof.AesGcm.X86_64.Blocks.BP s)
include hp

omit hp in
theorem Apart.ctr {q : Nat} {r : Region} (h : VG.Proof.AesGcm.X86_64.Blocks.Apart s q r) :
    ∀ r' ∈ [VG.Proof.AesGcm.X86_64.Blocks.cR s, (⟨VG.Proof.AesGcm.X86_64.Blocks.dq s q, 16 * (VG.Proof.AesGcm.X86_64.Blocks.n s - q)⟩ : Region), ⟨VG.Proof.AesGcm.X86_64.Blocks.S5 s, 2048⟩, below (VG.Proof.AesGcm.X86_64.Blocks.SP s) 8], r.Disjoint r' := by
  intro r' hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h.c, h.d, h.s5, h.t]

omit hp in
theorem Apart.gh {q : Nat} {r : Region} (h : VG.Proof.AesGcm.X86_64.Blocks.Apart s q r) :
    ∀ r' ∈ [VG.Proof.AesGcm.X86_64.Blocks.yR s, (⟨VG.Proof.AesGcm.X86_64.Blocks.S5 s, 256⟩ : Region), below (VG.Proof.AesGcm.X86_64.Blocks.SP s) 8], r.Disjoint r' := by
  intro r' hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h.y, h.s5.sub_right (Region.sub_prefix (by decide)), h.t]

theorem apart_kR' {q : Nat} (hq : q ≤ VG.Proof.AesGcm.X86_64.Blocks.n s) : VG.Proof.AesGcm.X86_64.Blocks.Apart s q (VG.Proof.AesGcm.X86_64.Blocks.kR' s) where
  c := VG.Proof.AesGcm.X86_64.Blocks.kR'_disj hp _ (by simp)
  y := VG.Proof.AesGcm.X86_64.Blocks.kR'_disj hp _ (by simp)
  d := (VG.Proof.AesGcm.X86_64.Blocks.kR'_disj hp (VG.Proof.AesGcm.X86_64.Blocks.dR s) (by simp)).sub_right (VG.Proof.AesGcm.X86_64.Blocks.dq_sub hq)
  s5 := Offset.base_disjoint (VG.Proof.AesGcm.X86_64.Blocks.S s) (e := 64) (n := 2048) (k := 48) (by decide) (by decide)
  t := (hp.t_s.sub_right VG.Proof.AesGcm.X86_64.Blocks.kR'_sub).symm

theorem apart_a {q : Nat} (hq : q ≤ VG.Proof.AesGcm.X86_64.Blocks.n s) : VG.Proof.AesGcm.X86_64.Blocks.Apart s q (VG.Proof.AesGcm.X86_64.Blocks.aR s) where
  c := hp.c_a.symm
  y := hp.y_a.symm
  d := hp.d_a.symm.sub_right (VG.Proof.AesGcm.X86_64.Blocks.dq_sub hq)
  s5 := hp.s_a.symm.sub_right (VG.Proof.AesGcm.X86_64.Blocks.s5_sub (by decide))
  t := VG.Proof.AesGcm.X86_64.Blocks.arg_below _

theorem apart_ret {q : Nat} (hq : q ≤ VG.Proof.AesGcm.X86_64.Blocks.n s) : VG.Proof.AesGcm.X86_64.Blocks.Apart s q ⟨VG.Proof.AesGcm.X86_64.Blocks.SP s, 8⟩ where
  c := hp.r_c
  y := hp.r_y
  d := hp.r_d.sub_right (VG.Proof.AesGcm.X86_64.Blocks.dq_sub hq)
  s5 := hp.r_s.sub_right (VG.Proof.AesGcm.X86_64.Blocks.s5_sub (by decide))
  t := ret_below _

theorem apart_k {q : Nat} (hq : q ≤ VG.Proof.AesGcm.X86_64.Blocks.n s) : VG.Proof.AesGcm.X86_64.Blocks.Apart s q (VG.Proof.AesGcm.X86_64.Blocks.kR s) where
  c := hp.k_c
  y := hp.k_y
  d := hp.k_d.sub_right (VG.Proof.AesGcm.X86_64.Blocks.dq_sub hq)
  s5 := hp.k_s.sub_right (VG.Proof.AesGcm.X86_64.Blocks.s5_sub (by decide))
  t := hp.t_k.symm

theorem apart_c : (VG.Proof.AesGcm.X86_64.Blocks.cR s).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.yR s) ∧ (VG.Proof.AesGcm.X86_64.Blocks.cR s).Disjoint ⟨VG.Proof.AesGcm.X86_64.Blocks.S5 s, 256⟩ ∧
    (VG.Proof.AesGcm.X86_64.Blocks.cR s).Disjoint (below (VG.Proof.AesGcm.X86_64.Blocks.SP s) 8) :=
  ⟨hp.c_y, hp.c_s.sub_right (VG.Proof.AesGcm.X86_64.Blocks.s5_sub (by decide)), hp.t_c.symm⟩

/-- The first `q` blocks are apart from what the calls write. -/
theorem apart_dq {q : Nat} (hq : q ≤ VG.Proof.AesGcm.X86_64.Blocks.n s) : VG.Proof.AesGcm.X86_64.Blocks.Apart s q ⟨VG.Proof.AesGcm.X86_64.Blocks.D s, 16 * q⟩ where
  c := hp.c_d.symm.sub_left (Region.sub_prefix (by omega))
  y := hp.y_d.symm.sub_left (Region.sub_prefix (by omega))
  d := Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.w_d; omega)
  s5 := (hp.d_s.sub_left (Region.sub_prefix (by omega))).sub_right (VG.Proof.AesGcm.X86_64.Blocks.s5_sub (by decide))
  t := hp.t_d.symm.sub_left (Region.sub_prefix (by omega))

omit hp in
/-- Ready through a call that writes apart from it. -/
theorem Ready.frame {q : Nat} {st st' : State} (h : VG.Proof.AesGcm.X86_64.Blocks.Ready s q st) {rs : List Region}
    (hf : Frame rs st.mem st'.mem) (hk : ∀ r ∈ rs, (VG.Proof.AesGcm.X86_64.Blocks.kR' s).Disjoint r) (ha : ∀ r ∈ rs, (VG.Proof.AesGcm.X86_64.Blocks.aR s).Disjoint r)
    (hsp : st'.gpr .rsp = st.gpr .rsp) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) : VG.Proof.AesGcm.X86_64.Blocks.Ready s q st' :=
  ⟨hsp.trans h.rsp, hrd.trans h.rd, hwr.trans h.wr, h.kept.frame hf hk,
    by rw [hf.readW (Region.contains_self _ _) ha (by decide)]; exact h.arg⟩

/-- The key schedule, through a frame apart from the key context. -/
theorem keep_sch {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hd : ∀ r' ∈ rs, (VG.Proof.AesGcm.X86_64.Blocks.kR s).Disjoint r') :
    Spec.Aes.bytesAt m' (VG.Proof.AesGcm.X86_64.Blocks.K s) (16 * (VG.Proof.AesGcm.X86_64.Blocks.R s + 1)) = Spec.Aes.bytesAt m (VG.Proof.AesGcm.X86_64.Blocks.K s) (16 * (VG.Proof.AesGcm.X86_64.Blocks.R s + 1)) := by
  have hRb : 16 * (VG.Proof.AesGcm.X86_64.Blocks.R s + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> simp only [VG.Proof.AesGcm.X86_64.Blocks.R, h] <;> decide
  exact bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by have := hp.w_k; omega)

theorem wR_k : ∀ r ∈ VG.Proof.AesGcm.X86_64.Blocks.wR s, (VG.Proof.AesGcm.X86_64.Blocks.kR s).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [hp.k_c, hp.k_y, hp.k_d, hp.k_s]

omit hp in
theorem length_blocksAt (m : Mem) (p : Addr) (k : Nat) : (blocksAt m p k).length = k := by simp [blocksAt]

omit hp in
/-- The blocks at `D` split after `q`. -/
theorem blocksAt_split (m : Mem) {q : Nat} (hq : q ≤ VG.Proof.AesGcm.X86_64.Blocks.n s) :
    blocksAt m (VG.Proof.AesGcm.X86_64.Blocks.D s) (VG.Proof.AesGcm.X86_64.Blocks.n s) = blocksAt m (VG.Proof.AesGcm.X86_64.Blocks.D s) q ++ blocksAt m (VG.Proof.AesGcm.X86_64.Blocks.dq s q) (VG.Proof.AesGcm.X86_64.Blocks.n s - q) := by
  rw [← Proof.Gcm.blocksAt_add, Nat.add_sub_cancel' hq]

/-- What the function returns with, when encrypting. -/
def EncDone (s s' : State) : Prop := gprPreserved s s' ∧ Proof.AesGcm.encryptBlocksX86_64.post s s'

/-- What the function returns with, when decrypting. -/
def DecDone (s s' : State) : Prop := gprPreserved s s' ∧ Proof.AesGcm.decryptBlocksX86_64.post s s'

omit hp in
/-- A region apart from what the calls write is kept. -/
theorem Calls.keep {q : Nat} {st st₂ st₃ st₄ st₅ : State} (c : VG.Proof.AesGcm.X86_64.Blocks.Calls s q st st₂ st₃ st₄ st₅) {r : Region}
    (ha : VG.Proof.AesGcm.X86_64.Blocks.Apart s q r) {p : Addr} {k : Nat} (hs : Region.Sub ⟨p, k⟩ r) (hk : k ≤ 2 ^ 64) :
    Spec.Aes.bytesAt st₅.mem p k = Spec.Aes.bytesAt st.mem p k := by
  rw [bytesAt_frame c.f₅ (fun r' hr' => (ha.gh r' hr').sub_left hs) hk, c.m₄,
    bytesAt_frame c.f₃ (fun r' hr' => (ha.ctr r' hr').sub_left hs) hk, c.m₂]

/-- `tail` from `Mid s q q ys`: its calls, if any blocks are left. -/
theorem tail_calls (first second : Prog isa) {q : Nat} {ys : List Block} {st : State} (h : VG.Proof.AesGcm.X86_64.Blocks.Mid s q q ys st)
    {Q : State → Prop} (h0 : ∀ st₁, VG.Proof.AesGcm.X86_64.Blocks.Mid s q q ys st₁ → VG.Proof.AesGcm.X86_64.Blocks.n s - q = 0 → Q st₁)
    (hc : ∀ st₁, VG.Proof.AesGcm.X86_64.Blocks.Mid s q q ys st₁ → q < VG.Proof.AesGcm.X86_64.Blocks.n s → WP isa (.seq first second) st₁ Q) :
    WP isa (tail first second) st Q := by
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.Blocks.tailHead_ok hp h) fun st₁ ⟨M, hz⟩ => ?_)
  refine WP.ite (decide (VG.Proof.AesGcm.X86_64.Blocks.n s - q = 0)) (by simp only [eval, hz]) (fun e => ?_) (fun e => ?_)
  · simp only [decide_eq_true_eq] at e
    exact WP.block_nil (h0 st₁ M e)
  · exact hc st₁ M (by simp at e; omega)

/-- The data left is apart from what `vg_ghash` writes. -/
theorem dq_gh {q : Nat} (hq : q ≤ VG.Proof.AesGcm.X86_64.Blocks.n s) :
    ∀ r ∈ [VG.Proof.AesGcm.X86_64.Blocks.yR s, (⟨VG.Proof.AesGcm.X86_64.Blocks.S5 s, 256⟩ : Region), below (VG.Proof.AesGcm.X86_64.Blocks.SP s) 8], (⟨VG.Proof.AesGcm.X86_64.Blocks.dq s q, 16 * (VG.Proof.AesGcm.X86_64.Blocks.n s - q)⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.y_d.symm.sub_left (VG.Proof.AesGcm.X86_64.Blocks.dq_sub hq)
  · exact (hp.d_s.sub_left (VG.Proof.AesGcm.X86_64.Blocks.dq_sub hq)).sub_right (VG.Proof.AesGcm.X86_64.Blocks.s5_sub (by decide))
  · exact hp.t_d.symm.sub_left (VG.Proof.AesGcm.X86_64.Blocks.dq_sub hq)

/-- `Y` is apart from what `vg_aes_ctr32` writes. -/
theorem y_ctr {q : Nat} (hq : q ≤ VG.Proof.AesGcm.X86_64.Blocks.n s) :
    ∀ r ∈ [VG.Proof.AesGcm.X86_64.Blocks.cR s, (⟨VG.Proof.AesGcm.X86_64.Blocks.dq s q, 16 * (VG.Proof.AesGcm.X86_64.Blocks.n s - q)⟩ : Region), ⟨VG.Proof.AesGcm.X86_64.Blocks.S5 s, 2048⟩, below (VG.Proof.AesGcm.X86_64.Blocks.SP s) 8], (VG.Proof.AesGcm.X86_64.Blocks.yR s).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.c_y.symm
  · exact hp.y_d.sub_right (VG.Proof.AesGcm.X86_64.Blocks.dq_sub hq)
  · exact hp.y_s.sub_right (VG.Proof.AesGcm.X86_64.Blocks.s5_sub (by decide))
  · exact hp.t_y.symm

/-- The counter is apart from what `vg_ghash` writes. -/
theorem c_gh : ∀ r ∈ [VG.Proof.AesGcm.X86_64.Blocks.yR s, (⟨VG.Proof.AesGcm.X86_64.Blocks.S5 s, 256⟩ : Region), below (VG.Proof.AesGcm.X86_64.Blocks.SP s) 8], (VG.Proof.AesGcm.X86_64.Blocks.cR s).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.c_y
  · exact hp.c_s.sub_right (VG.Proof.AesGcm.X86_64.Blocks.s5_sub (by decide))
  · exact hp.t_c.symm

omit hp in
/-- The hash subkey is in the key context. -/
theorem h_sub : Region.Sub ⟨VG.Proof.AesGcm.X86_64.Blocks.K s + BitVec.ofNat 64 240, 16⟩ (VG.Proof.AesGcm.X86_64.Blocks.kR s) := Offset.sub_base _ (by decide)

/-- The encryption of the blocks left, from `Mid`. -/
theorem encCalls_ok (v : GcmImpl) {q : Nat} {st₁ : State}
    (M : VG.Proof.AesGcm.X86_64.Blocks.Mid s q q (ctr32 (VG.Proof.AesGcm.X86_64.Blocks.ciph s) (VG.Proof.AesGcm.X86_64.Blocks.cb s) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q)) st₁) (hlt : q < VG.Proof.AesGcm.X86_64.Blocks.n s) :
    WP isa (.seq (ctrCall v.callees.ctr) (ghCall v.callees.gh)) st₁ (VG.Proof.AesGcm.X86_64.Blocks.EncDone s) := by
  have hq := M.q_le
  have hw := hp.w_d
  have h16 := VG.Proof.AesGcm.X86_64.Blocks.n16_lt hp
  refine WP.seq (WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.Blocks.ctrArgs_ok hp (M.ready hp) hlt) fun st₂ ⟨hc, R₂, sv₂, m₂⟩ =>
    WP.mono (ctr_call v.ctr hc) fun st₃ g => ?_))
  have f₃ := g.frame
  rw [R₂.rsp] at f₃
  have R₃ : VG.Proof.AesGcm.X86_64.Blocks.Ready s q st₃ := R₂.frame f₃ (fun r hr => (VG.Proof.AesGcm.X86_64.Blocks.apart_kR' hp hq).ctr r hr)
    (fun r hr => (VG.Proof.AesGcm.X86_64.Blocks.apart_a hp hq).ctr r hr) (g.saved _ (by decide)) g.rd g.wr
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.Blocks.ghArgs_ok hp R₃ hlt) fun st₄ ⟨hg, R₄, sv₄, m₄⟩ =>
    WP.mono (gh_call v.gh hg) fun st₅ g' => ?_)
  have f₅ := g'.frame
  rw [R₄.rsp] at f₅
  have c : VG.Proof.AesGcm.X86_64.Blocks.Calls s q st₁ st₂ st₃ st₄ st₅ := ⟨m₂, f₃, m₄, f₅, fun r hr => by
    rw [g'.saved r hr, sv₄ r hr, g.saved r hr, sv₂ r hr]⟩
  -- What the calls compute.
  have hK : Spec.Aes.bytesAt st₂.mem (VG.Proof.AesGcm.X86_64.Blocks.K s) (16 * (VG.Proof.AesGcm.X86_64.Blocks.R s + 1)) = Spec.Aes.bytesAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.K s) (16 * (VG.Proof.AesGcm.X86_64.Blocks.R s + 1)) := by
    rw [m₂]; exact VG.Proof.AesGcm.X86_64.Blocks.keep_sch hp M.frame (VG.Proof.AesGcm.X86_64.Blocks.wR_k hp)
  have hC₂ : blockAt st₂.mem (VG.Proof.AesGcm.X86_64.Blocks.C s) = Nat.repeat inc32 q (VG.Proof.AesGcm.X86_64.Blocks.cb s) := by rw [m₂]; exact M.ctr
  have hD₂ : blocksAt st₂.mem (VG.Proof.AesGcm.X86_64.Blocks.dq s q) (VG.Proof.AesGcm.X86_64.Blocks.n s - q) = blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.dq s q) (VG.Proof.AesGcm.X86_64.Blocks.n s - q) := by rw [m₂]; exact M.rest
  have out₃ := g.out
  rw [hK, hC₂, hD₂] at out₃
  have hx : blocksAt st₄.mem (VG.Proof.AesGcm.X86_64.Blocks.dq s q) (VG.Proof.AesGcm.X86_64.Blocks.n s - q) =
      ctr32 (VG.Proof.AesGcm.X86_64.Blocks.ciph s) (Nat.repeat inc32 q (VG.Proof.AesGcm.X86_64.Blocks.cb s)) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.dq s q) (VG.Proof.AesGcm.X86_64.Blocks.n s - q)) := by rw [m₄]; exact out₃
  have hH : blockAt st₄.mem (VG.Proof.AesGcm.X86_64.Blocks.K s + BitVec.ofNat 64 240) = VG.Proof.AesGcm.X86_64.Blocks.hk s := by
    rw [m₄, blockAt_frame f₃ fun r hr => ((VG.Proof.AesGcm.X86_64.Blocks.apart_k hp hq).ctr r hr).sub_left (VG.Proof.AesGcm.X86_64.Blocks.h_sub (s := s)), m₂,
      blockAt_frame M.frame fun r hr => (VG.Proof.AesGcm.X86_64.Blocks.wR_k hp r hr).sub_left (VG.Proof.AesGcm.X86_64.Blocks.h_sub (s := s))]; rfl
  have hY : blockAt st₄.mem (VG.Proof.AesGcm.X86_64.Blocks.Y s) = ghashFrom (VG.Proof.AesGcm.X86_64.Blocks.hk s) (VG.Proof.AesGcm.X86_64.Blocks.y₀ s) (ctr32 (VG.Proof.AesGcm.X86_64.Blocks.ciph s) (VG.Proof.AesGcm.X86_64.Blocks.cb s) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q)) := by
    rw [m₄, blockAt_frame f₃ (VG.Proof.AesGcm.X86_64.Blocks.y_ctr hp hq), m₂]; exact M.y
  have hfirst : blocksAt st₅.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q = ctr32 (VG.Proof.AesGcm.X86_64.Blocks.ciph s) (VG.Proof.AesGcm.X86_64.Blocks.cb s) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q) := by
    rw [← M.data]
    exact blocksAt_frame f₅ (fun r hr => ((VG.Proof.AesGcm.X86_64.Blocks.apart_dq hp hq).gh r hr)) (by omega) |>.trans (by
      rw [m₄]; exact (blocksAt_frame f₃ (fun r hr => ((VG.Proof.AesGcm.X86_64.Blocks.apart_dq hp hq).ctr r hr)) (by omega)).trans (by rw [m₂]))
  have hsecond : blocksAt st₅.mem (VG.Proof.AesGcm.X86_64.Blocks.dq s q) (VG.Proof.AesGcm.X86_64.Blocks.n s - q) =
      ctr32 (VG.Proof.AesGcm.X86_64.Blocks.ciph s) (Nat.repeat inc32 q (VG.Proof.AesGcm.X86_64.Blocks.cb s)) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.dq s q) (VG.Proof.AesGcm.X86_64.Blocks.n s - q)) := by
    rw [blocksAt_frame f₅ (VG.Proof.AesGcm.X86_64.Blocks.dq_gh hp hq) (by omega), hx]
  have hall : ctr32 (VG.Proof.AesGcm.X86_64.Blocks.ciph s) (VG.Proof.AesGcm.X86_64.Blocks.cb s) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) (VG.Proof.AesGcm.X86_64.Blocks.n s)) =
      ctr32 (VG.Proof.AesGcm.X86_64.Blocks.ciph s) (VG.Proof.AesGcm.X86_64.Blocks.cb s) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q) ++
        ctr32 (VG.Proof.AesGcm.X86_64.Blocks.ciph s) (Nat.repeat inc32 q (VG.Proof.AesGcm.X86_64.Blocks.cb s)) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.dq s q) (VG.Proof.AesGcm.X86_64.Blocks.n s - q)) := by
    rw [VG.Proof.AesGcm.X86_64.Blocks.blocksAt_split s.mem hq, Proof.Gcm.ctr32_append, VG.Proof.AesGcm.X86_64.Blocks.length_blocksAt]
  refine ⟨⟨fun r hr => by rw [c.saved r hr, M.saved r hr], ?_⟩, ?_, ?_, ?_⟩
  · show st₅.mem.readW (VG.Proof.AesGcm.X86_64.Blocks.SP s) 64 = s.mem.readW (VG.Proof.AesGcm.X86_64.Blocks.SP s) 64
    rw [f₅.readW (Region.contains_self _ _) ((VG.Proof.AesGcm.X86_64.Blocks.apart_ret hp hq).gh) (by decide), m₄,
      f₃.readW (Region.contains_self _ _) ((VG.Proof.AesGcm.X86_64.Blocks.apart_ret hp hq).ctr) (by decide), m₂, VG.Proof.AesGcm.X86_64.Blocks.keep_r hp M.frame]
  · show blocksAt st₅.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) (VG.Proof.AesGcm.X86_64.Blocks.n s) = ctr32 (VG.Proof.AesGcm.X86_64.Blocks.ciph s) (VG.Proof.AesGcm.X86_64.Blocks.cb s) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) (VG.Proof.AesGcm.X86_64.Blocks.n s))
    rw [VG.Proof.AesGcm.X86_64.Blocks.blocksAt_split st₅.mem hq, hfirst, hsecond, hall]
  · show blockAt st₅.mem (VG.Proof.AesGcm.X86_64.Blocks.C s) = Nat.repeat inc32 (VG.Proof.AesGcm.X86_64.Blocks.n s) (VG.Proof.AesGcm.X86_64.Blocks.cb s)
    rw [blockAt_frame f₅ (VG.Proof.AesGcm.X86_64.Blocks.c_gh hp), m₄, g.ctr, hC₂, ← Proof.Gcm.repeat_add, Nat.sub_add_cancel hq]
  · show blockAt st₅.mem (VG.Proof.AesGcm.X86_64.Blocks.Y s) = ghashFrom (VG.Proof.AesGcm.X86_64.Blocks.hk s) (VG.Proof.AesGcm.X86_64.Blocks.y₀ s) (ctr32 (VG.Proof.AesGcm.X86_64.Blocks.ciph s) (VG.Proof.AesGcm.X86_64.Blocks.cb s) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) (VG.Proof.AesGcm.X86_64.Blocks.n s)))
    rw [g'.out, hH, hY, hx, ← Proof.Gcm.ghashFrom_append, hall]

/-- The decryption of the blocks left, from `Mid`: hashed, then decrypted. -/
theorem decCalls_ok (v : GcmImpl) {q : Nat} {st₁ : State}
    (M : VG.Proof.AesGcm.X86_64.Blocks.Mid s q q (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q) st₁) (hlt : q < VG.Proof.AesGcm.X86_64.Blocks.n s) :
    WP isa (.seq (ghCall v.callees.gh) (ctrCall v.callees.ctr)) st₁ (VG.Proof.AesGcm.X86_64.Blocks.DecDone s) := by
  have hq := M.q_le
  have hw := hp.w_d
  have h16 := VG.Proof.AesGcm.X86_64.Blocks.n16_lt hp
  refine WP.seq (WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.Blocks.ghArgs_ok hp (M.ready hp) hlt) fun st₂ ⟨hg, R₂, sv₂, m₂⟩ =>
    WP.mono (gh_call v.gh hg) fun st₃ g => ?_))
  have f₃ := g.frame
  rw [R₂.rsp] at f₃
  have R₃ : VG.Proof.AesGcm.X86_64.Blocks.Ready s q st₃ := R₂.frame f₃ (fun r hr => (VG.Proof.AesGcm.X86_64.Blocks.apart_kR' hp hq).gh r hr)
    (fun r hr => (VG.Proof.AesGcm.X86_64.Blocks.apart_a hp hq).gh r hr) (g.saved _ (by decide)) g.rd g.wr
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.Blocks.ctrArgs_ok hp R₃ hlt) fun st₄ ⟨hc, R₄, sv₄, m₄⟩ =>
    WP.mono (ctr_call v.ctr hc) fun st₅ g' => ?_)
  have f₅ := g'.frame
  rw [R₄.rsp] at f₅
  have hP₂ : blocksAt st₂.mem (VG.Proof.AesGcm.X86_64.Blocks.dq s q) (VG.Proof.AesGcm.X86_64.Blocks.n s - q) = blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.dq s q) (VG.Proof.AesGcm.X86_64.Blocks.n s - q) := by rw [m₂]; exact M.rest
  have hH : blockAt st₂.mem (VG.Proof.AesGcm.X86_64.Blocks.K s + BitVec.ofNat 64 240) = VG.Proof.AesGcm.X86_64.Blocks.hk s := by
    rw [m₂, blockAt_frame M.frame fun r hr => (VG.Proof.AesGcm.X86_64.Blocks.wR_k hp r hr).sub_left (VG.Proof.AesGcm.X86_64.Blocks.h_sub (s := s))]; rfl
  have hY₂ : blockAt st₂.mem (VG.Proof.AesGcm.X86_64.Blocks.Y s) = ghashFrom (VG.Proof.AesGcm.X86_64.Blocks.hk s) (VG.Proof.AesGcm.X86_64.Blocks.y₀ s) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q) := by rw [m₂]; exact M.y
  have hK : Spec.Aes.bytesAt st₄.mem (VG.Proof.AesGcm.X86_64.Blocks.K s) (16 * (VG.Proof.AesGcm.X86_64.Blocks.R s + 1)) = Spec.Aes.bytesAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.K s) (16 * (VG.Proof.AesGcm.X86_64.Blocks.R s + 1)) := by
    rw [m₄, VG.Proof.AesGcm.X86_64.Blocks.keep_sch hp f₃ (fun r hr => (VG.Proof.AesGcm.X86_64.Blocks.apart_k hp hq).gh r hr), m₂]; exact VG.Proof.AesGcm.X86_64.Blocks.keep_sch hp M.frame (VG.Proof.AesGcm.X86_64.Blocks.wR_k hp)
  have hC₄ : blockAt st₄.mem (VG.Proof.AesGcm.X86_64.Blocks.C s) = Nat.repeat inc32 q (VG.Proof.AesGcm.X86_64.Blocks.cb s) := by
    rw [m₄, blockAt_frame f₃ (VG.Proof.AesGcm.X86_64.Blocks.c_gh hp), m₂]; exact M.ctr
  have hD₄ : blocksAt st₄.mem (VG.Proof.AesGcm.X86_64.Blocks.dq s q) (VG.Proof.AesGcm.X86_64.Blocks.n s - q) = blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.dq s q) (VG.Proof.AesGcm.X86_64.Blocks.n s - q) := by
    rw [m₄, blocksAt_frame f₃ (VG.Proof.AesGcm.X86_64.Blocks.dq_gh hp hq) (by omega)]; exact hP₂
  have out₅ := g'.out
  rw [hK, hC₄, hD₄] at out₅
  have hfirst : blocksAt st₅.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q = ctr32 (VG.Proof.AesGcm.X86_64.Blocks.ciph s) (VG.Proof.AesGcm.X86_64.Blocks.cb s) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q) := by
    rw [← M.data, blocksAt_frame f₅ (fun r hr => ((VG.Proof.AesGcm.X86_64.Blocks.apart_dq hp hq).ctr r hr)) (by omega), m₄,
      blocksAt_frame f₃ (fun r hr => ((VG.Proof.AesGcm.X86_64.Blocks.apart_dq hp hq).gh r hr)) (by omega), m₂]
  refine ⟨⟨fun r hr => by rw [g'.saved r hr, sv₄ r hr, g.saved r hr, sv₂ r hr, M.saved r hr], ?_⟩, ?_, ?_, ?_⟩
  · show st₅.mem.readW (VG.Proof.AesGcm.X86_64.Blocks.SP s) 64 = s.mem.readW (VG.Proof.AesGcm.X86_64.Blocks.SP s) 64
    rw [f₅.readW (Region.contains_self _ _) ((VG.Proof.AesGcm.X86_64.Blocks.apart_ret hp hq).ctr) (by decide), m₄,
      f₃.readW (Region.contains_self _ _) ((VG.Proof.AesGcm.X86_64.Blocks.apart_ret hp hq).gh) (by decide), m₂, VG.Proof.AesGcm.X86_64.Blocks.keep_r hp M.frame]
  · show blocksAt st₅.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) (VG.Proof.AesGcm.X86_64.Blocks.n s) = ctr32 (VG.Proof.AesGcm.X86_64.Blocks.ciph s) (VG.Proof.AesGcm.X86_64.Blocks.cb s) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) (VG.Proof.AesGcm.X86_64.Blocks.n s))
    rw [VG.Proof.AesGcm.X86_64.Blocks.blocksAt_split st₅.mem hq, hfirst, out₅, VG.Proof.AesGcm.X86_64.Blocks.blocksAt_split s.mem hq, Proof.Gcm.ctr32_append, VG.Proof.AesGcm.X86_64.Blocks.length_blocksAt]; rfl
  · show blockAt st₅.mem (VG.Proof.AesGcm.X86_64.Blocks.C s) = Nat.repeat inc32 (VG.Proof.AesGcm.X86_64.Blocks.n s) (VG.Proof.AesGcm.X86_64.Blocks.cb s)
    rw [g'.ctr, hC₄, ← Proof.Gcm.repeat_add, Nat.sub_add_cancel hq]
  · show blockAt st₅.mem (VG.Proof.AesGcm.X86_64.Blocks.Y s) = ghashFrom (VG.Proof.AesGcm.X86_64.Blocks.hk s) (VG.Proof.AesGcm.X86_64.Blocks.y₀ s) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) (VG.Proof.AesGcm.X86_64.Blocks.n s))
    rw [blockAt_frame f₅ (VG.Proof.AesGcm.X86_64.Blocks.y_ctr hp hq), m₄, g.out, hH, hY₂, hP₂, ← Proof.Gcm.ghashFrom_append,
      ← VG.Proof.AesGcm.X86_64.Blocks.blocksAt_split s.mem hq]

end

end VG.Proof.AesGcm.X86_64.Blocks

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Stitch`. -/
section

/-!
# AES-GCM on whole blocks, x86-64: the first `16 ⌊n / 16⌋` blocks in one pass

Untrusted: everything here is checked by Lean. After the entry, if there are
at least 16 blocks, `r9` becomes `16 ⌊n / 16⌋` (`split_ok`), which with the
other arguments still in their registers meets what the interleaved loops
need (`spre_of`); their result is `Mid` with `q = 16 ⌊n / 16⌋`
(`mid_of_post`). With fewer, `q = 0` (`stitchE_ok`, `stitchD_ok`); then `rest`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

/-- The registers the entry leaves as they were. -/
def argRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]

theorem contains_prefix (a : Addr) {k L : Nat} (h : k ≤ L) : (⟨a, L⟩ : Region).Contains a k := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

section
variable {s : State} (hp : VG.Proof.AesGcm.X86_64.Blocks.BP s)
include hp

omit hp in
/-- `r9 := 16 ⌊r9 / 16⌋`, and `r11` at the powers. -/
theorem split_ok {s₁ : State} (h9 : s₁.gpr .r9 = s.gpr .r9) :
    WP isa (.block [.mov .rax (.reg .r9), .alu .and .rax (imm 15), .alu .sub .r9 (.reg .rax),
      .alu .add .r11 (imm 64)]) s₁ fun s₃ =>
      s₃.gpr .r9 = BitVec.ofNat 64 (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16) ∧ s₃.gpr .r11 = s₁.gpr .r11 + BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .r11 → s₃.gpr r = s₁.gpr r) ∧
      s₃.mem = s₁.mem ∧ s₃.rd = s₁.rd ∧ s₃.wr = s₁.wr := by
  have hn : VG.Proof.AesGcm.X86_64.Blocks.n s < 2 ^ 64 := (s.gpr .r9).isLt
  have e15 := and15 (s.gpr .r9)
  rw [imm_eq (by decide)] at e15
  have esub : s.gpr .r9 - BitVec.ofNat 64 (VG.Proof.AesGcm.X86_64.Blocks.n s % 16) = BitVec.ofNat 64 (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16) := by
    rw [← ofNat_sub (Nat.mod_le _ _) hn]; simp
  apply WP.of_runBlock
  refine ⟨_, by xrun [h9, e15, esub], ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags]
  · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- What the interleaved loops need, from the arguments in their registers
and `r9 = 16 ⌊n / 16⌋`. -/
theorem spre_of {s₃ : State} (h16 : 16 ≤ VG.Proof.AesGcm.X86_64.Blocks.n s) (h9 : s₃.gpr .r9 = BitVec.ofNat 64 (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16))
    (hg : ∀ r ∈ VG.Proof.AesGcm.X86_64.Blocks.argRegs, s₃.gpr r = s.gpr r) (h11 : s₃.gpr .r11 = VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 64) (hrd : s₃.rd = s.rd)
    (hwr : s₃.wr = s.wr) : Gcm.X86_64.Stitch.SPre s₃ := by
  have hn : VG.Proof.AesGcm.X86_64.Blocks.n s < 2 ^ 64 := (s.gpr .r9).isLt
  have hq : (s₃.gpr .r9).toNat = VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16 := by rw [h9, toNat_ofNat_of_lt (by omega)]
  have hqn : 16 * (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16) ≤ VG.Proof.AesGcm.X86_64.Blocks.n s * 16 := by omega
  have pd : Region.Sub ⟨VG.Proof.AesGcm.X86_64.Blocks.D s, 16 * (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16)⟩ (VG.Proof.AesGcm.X86_64.Blocks.dR s) := Region.sub_prefix hqn
  have ps : Region.Sub ⟨VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 64, 256⟩ (VG.Proof.AesGcm.X86_64.Blocks.sR s) := Offset.sub_base _ (by decide)
  have hws := hp.w_s
  have ts : (VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 64).toNat = (VG.Proof.AesGcm.X86_64.Blocks.S s).toNat + 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [Nat.reducePow, Nat.reduceMod]; omega
  have ek : s₃.gpr .rdi = VG.Proof.AesGcm.X86_64.Blocks.K s := hg _ (by simp [VG.Proof.AesGcm.X86_64.Blocks.argRegs])
  have er : s₃.gpr .rsi = s.gpr .rsi := hg _ (by simp [VG.Proof.AesGcm.X86_64.Blocks.argRegs])
  have ec : s₃.gpr .rdx = VG.Proof.AesGcm.X86_64.Blocks.C s := hg _ (by simp [VG.Proof.AesGcm.X86_64.Blocks.argRegs])
  have ey : s₃.gpr .rcx = VG.Proof.AesGcm.X86_64.Blocks.Y s := hg _ (by simp [VG.Proof.AesGcm.X86_64.Blocks.argRegs])
  have ed : s₃.gpr .r8 = VG.Proof.AesGcm.X86_64.Blocks.D s := hg _ (by simp [VG.Proof.AesGcm.X86_64.Blocks.argRegs])
  have wr : s.wr = VG.Proof.AesGcm.X86_64.Blocks.wR s := hp.wr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [Gcm.X86_64.Stitch.nr, Gcm.X86_64.Stitch.nb, Gcm.X86_64.Stitch.kp,
    Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.dp, Gcm.X86_64.Stitch.pp,
    Gcm.X86_64.Stitch.kR, Gcm.X86_64.Stitch.cR, Gcm.X86_64.Stitch.yR, Gcm.X86_64.Stitch.dR,
    Gcm.X86_64.Stitch.pR, ek, er, ec, ey, ed, h11, hq, hrd, hwr]
  exacts [hp.rounds, by omega, by omega, ⟨VG.Proof.AesGcm.X86_64.Blocks.kR s, by rw [hp.rd]; simp, Region.contains_self _ _⟩,
    ⟨VG.Proof.AesGcm.X86_64.Blocks.cR s, by rw [wr]; simp, Region.contains_self _ _⟩, ⟨VG.Proof.AesGcm.X86_64.Blocks.yR s, by rw [wr]; simp, Region.contains_self _ _⟩,
    ⟨VG.Proof.AesGcm.X86_64.Blocks.dR s, by rw [wr]; simp, VG.Proof.AesGcm.X86_64.Blocks.contains_prefix _ hqn⟩, ⟨VG.Proof.AesGcm.X86_64.Blocks.sR s, by rw [wr]; simp, Offset.contains_base _ (by decide) (by decide)⟩,
    hp.k_d.symm.sub_left pd, hp.c_d.symm.sub_left pd, hp.y_d.symm.sub_left pd,
    (hp.d_s.sub_left pd).sub_right ps, hp.k_s.symm.sub_left ps, hp.c_s.symm.sub_left ps,
    hp.y_s.symm.sub_left ps, hp.c_y, hp.k_c.symm, hp.k_y.symm, by have := hp.w_d; omega, hp.w_k,
    by rw [ts]; omega]

/-- The hash subkey is apart from `scratch`'s slots. -/
theorem kR'_disj' : (⟨VG.Proof.AesGcm.X86_64.Blocks.K s + 240, 16⟩ : Region).Disjoint (VG.Proof.AesGcm.X86_64.Blocks.kR' s) :=
  (hp.k_s.sub_right VG.Proof.AesGcm.X86_64.Blocks.kR'_sub).sub_left (Offset.sub_base (d := 240) _ (by decide))

/-- The data from block `q` on, apart from the first `q` blocks and from the
other regions written. -/
theorem rest_disj {q : Nat} (hq : q ≤ VG.Proof.AesGcm.X86_64.Blocks.n s) :
    ∀ r ∈ [VG.Proof.AesGcm.X86_64.Blocks.cR s, VG.Proof.AesGcm.X86_64.Blocks.yR s, (⟨VG.Proof.AesGcm.X86_64.Blocks.D s, 16 * q⟩ : Region), (⟨VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 64, 256⟩ : Region)],
      (⟨VG.Proof.AesGcm.X86_64.Blocks.dq s q, 16 * (VG.Proof.AesGcm.X86_64.Blocks.n s - q)⟩ : Region).Disjoint r := by
  have hsub : Region.Sub ⟨VG.Proof.AesGcm.X86_64.Blocks.dq s q, 16 * (VG.Proof.AesGcm.X86_64.Blocks.n s - q)⟩ (VG.Proof.AesGcm.X86_64.Blocks.dR s) := Offset.sub_base _ (by omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.c_d.symm.sub_left hsub
  · exact hp.y_d.symm.sub_left hsub
  · exact Offset.disjoint_base _ (Nat.le_refl _) (by have := hp.w_d; omega)
  · exact (hp.d_s.sub_left hsub).sub_right (Offset.sub_base _ (by decide))

/-- `Mid` after the interleaved loops, from what they leave. -/
theorem mid_of_post {s₃ s₄ : State} (h9 : s₃.gpr .r9 = BitVec.ofNat 64 (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16))
    (hg : ∀ r ∈ VG.Proof.AesGcm.X86_64.Blocks.argRegs, s₃.gpr r = s.gpr r) (hcs : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r)
    (h11 : s₃.gpr .r11 = VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 64)
    (hrd : s₃.rd = s.rd) (hwr : s₃.wr = s.wr) (hkp : VG.Proof.AesGcm.X86_64.Blocks.Kept s 0 s₃.mem) (hf₃ : Frame [VG.Proof.AesGcm.X86_64.Blocks.kR' s] s.mem s₃.mem)
    (data : blocksAt s₄.mem (s₃.gpr .r8) (s₃.gpr .r9).toNat = ctr32 (Gcm.X86_64.Stitch.ciph s₃)
      (blockAt s₃.mem (s₃.gpr .rdx)) (blocksAt s₃.mem (s₃.gpr .r8) (s₃.gpr .r9).toNat))
    (ctr : blockAt s₄.mem (s₃.gpr .rdx) = Nat.repeat inc32 (s₃.gpr .r9).toNat (blockAt s₃.mem (s₃.gpr .rdx)))
    (frame : Frame [Gcm.X86_64.Stitch.cR s₃, Gcm.X86_64.Stitch.yR s₃, Gcm.X86_64.Stitch.dR s₃,
      Gcm.X86_64.Stitch.pR s₃] s₃.mem s₄.mem)
    (gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s₃.gpr r)
    (rd : s₄.rd = s₃.rd) (wr : s₄.wr = s₃.wr) {ys : List Block}
    (y : blockAt s₃.mem (VG.Proof.AesGcm.X86_64.Blocks.K s + 240) = VG.Proof.AesGcm.X86_64.Blocks.hk s → blockAt s₃.mem (VG.Proof.AesGcm.X86_64.Blocks.Y s) = VG.Proof.AesGcm.X86_64.Blocks.y₀ s →
      blocksAt s₃.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16) = blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16) →
      blocksAt s₄.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16) = ctr32 (VG.Proof.AesGcm.X86_64.Blocks.ciph s) (VG.Proof.AesGcm.X86_64.Blocks.cb s) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16)) →
      blockAt s₄.mem (VG.Proof.AesGcm.X86_64.Blocks.Y s) = ghashFrom (VG.Proof.AesGcm.X86_64.Blocks.hk s) (VG.Proof.AesGcm.X86_64.Blocks.y₀ s) ys) :
    VG.Proof.AesGcm.X86_64.Blocks.Mid s (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16) 0 ys s₄ := by
  have hn : VG.Proof.AesGcm.X86_64.Blocks.n s < 2 ^ 64 := (s.gpr .r9).isLt
  generalize hq : VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16 = q at *
  have hqn : q ≤ VG.Proof.AesGcm.X86_64.Blocks.n s := by omega
  have hq9 : (s₃.gpr .r9).toNat = q := by rw [h9, toNat_ofNat_of_lt (by omega)]
  have ek : s₃.gpr .rdi = VG.Proof.AesGcm.X86_64.Blocks.K s := hg _ (by simp [VG.Proof.AesGcm.X86_64.Blocks.argRegs])
  have er : s₃.gpr .rsi = s.gpr .rsi := hg _ (by simp [VG.Proof.AesGcm.X86_64.Blocks.argRegs])
  have ec : s₃.gpr .rdx = VG.Proof.AesGcm.X86_64.Blocks.C s := hg _ (by simp [VG.Proof.AesGcm.X86_64.Blocks.argRegs])
  have ey : s₃.gpr .rcx = VG.Proof.AesGcm.X86_64.Blocks.Y s := hg _ (by simp [VG.Proof.AesGcm.X86_64.Blocks.argRegs])
  have ed : s₃.gpr .r8 = VG.Proof.AesGcm.X86_64.Blocks.D s := hg _ (by simp [VG.Proof.AesGcm.X86_64.Blocks.argRegs])
  simp only [Gcm.X86_64.Stitch.cR, Gcm.X86_64.Stitch.yR, Gcm.X86_64.Stitch.dR, Gcm.X86_64.Stitch.pR,
    Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.dp, Gcm.X86_64.Stitch.pp,
    Gcm.X86_64.Stitch.nb, ec, ey, ed, h11, hq9] at frame
  rw [ed, hq9, ec] at data
  rw [ec, hq9] at ctr
  simp only [Gcm.X86_64.Stitch.ciph, Gcm.X86_64.Stitch.sch, Gcm.X86_64.Stitch.nr, Gcm.X86_64.Stitch.kp, ek,
    er] at data
  have kd : ∀ r ∈ [VG.Proof.AesGcm.X86_64.Blocks.kR' s], (VG.Proof.AesGcm.X86_64.Blocks.kR s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.k_s.sub_right VG.Proof.AesGcm.X86_64.Blocks.kR'_sub
  have hRb : 16 * (VG.Proof.AesGcm.X86_64.Blocks.R s + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> simp only [VG.Proof.AesGcm.X86_64.Blocks.R, h] <;> decide
  have eK : Spec.Aes.bytesAt s₃.mem (VG.Proof.AesGcm.X86_64.Blocks.K s) (16 * (VG.Proof.AesGcm.X86_64.Blocks.R s + 1)) = Spec.Aes.bytesAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.K s) (16 * (VG.Proof.AesGcm.X86_64.Blocks.R s + 1)) :=
    bytesAt_frame hf₃ (fun r hr => (kd r hr).sub_left (Region.sub_prefix hRb)) (by omega)
  have eC : blockAt s₃.mem (VG.Proof.AesGcm.X86_64.Blocks.C s) = VG.Proof.AesGcm.X86_64.Blocks.cb s := VG.Proof.AesGcm.X86_64.Blocks.block_kR' hf₃ (VG.Proof.AesGcm.X86_64.Blocks.kR'_disj hp _ (by simp)).symm
  have pd : Region.Sub ⟨VG.Proof.AesGcm.X86_64.Blocks.D s, 16 * q⟩ (VG.Proof.AesGcm.X86_64.Blocks.dR s) := Region.sub_prefix (by omega)
  have eD : blocksAt s₃.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q = blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q := blocksAt_frame hf₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (VG.Proof.AesGcm.X86_64.Blocks.kR'_disj hp (VG.Proof.AesGcm.X86_64.Blocks.dR s) (by simp)).symm.sub_left pd)
    (by have := hp.w_d; omega)
  rw [eK, eC, eD] at data
  rw [eC] at ctr
  have y' := y (VG.Proof.AesGcm.X86_64.Blocks.block_kR' hf₃ (VG.Proof.AesGcm.X86_64.Blocks.kR'_disj' hp)) (VG.Proof.AesGcm.X86_64.Blocks.block_kR' hf₃ (VG.Proof.AesGcm.X86_64.Blocks.kR'_disj hp _ (by simp)).symm) eD data
  have sk : Region.Disjoint (VG.Proof.AesGcm.X86_64.Blocks.kR' s) ⟨VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 64, 256⟩ :=
    Offset.base_disjoint _ (by decide) (by have := hp.w_s; omega)
  have fk : ∀ r ∈ [VG.Proof.AesGcm.X86_64.Blocks.cR s, VG.Proof.AesGcm.X86_64.Blocks.yR s, (⟨VG.Proof.AesGcm.X86_64.Blocks.D s, 16 * q⟩ : Region), (⟨VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 64, 256⟩ : Region)],
      (VG.Proof.AesGcm.X86_64.Blocks.kR' s).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact VG.Proof.AesGcm.X86_64.Blocks.kR'_disj hp _ (by simp)
    · exact VG.Proof.AesGcm.X86_64.Blocks.kR'_disj hp _ (by simp)
    · exact (VG.Proof.AesGcm.X86_64.Blocks.kR'_disj hp (VG.Proof.AesGcm.X86_64.Blocks.dR s) (by simp)).sub_right pd
    · exact sk
  have fw : Frame (VG.Proof.AesGcm.X86_64.Blocks.wR s) s.mem s₄.mem := by
    refine (hf₃.sub fun r hr => ?_).trans (frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesGcm.X86_64.Blocks.sR s, by simp, VG.Proof.AesGcm.X86_64.Blocks.kR'_sub⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨VG.Proof.AesGcm.X86_64.Blocks.cR s, by simp, fun _ h => h⟩
      · exact ⟨VG.Proof.AesGcm.X86_64.Blocks.yR s, by simp, fun _ h => h⟩
      · exact ⟨VG.Proof.AesGcm.X86_64.Blocks.dR s, by simp, pd⟩
      · exact ⟨VG.Proof.AesGcm.X86_64.Blocks.sR s, by simp, Offset.sub_base _ (by decide)⟩
  have hw := hp.w_d
  refine ⟨hqn, ?_, fun r hr => ?_, rd.trans hrd, wr.trans hwr, hkp.frame frame fk, fw, data, ?_, ctr, y'⟩
  · rw [gpr _ (by decide) (by decide) (by decide) (by decide)]; exact hg _ (by simp [VG.Proof.AesGcm.X86_64.Blocks.argRegs])
  · have hr' : r ≠ .rax ∧ r ≠ .rdx ∧ r ≠ .r9 ∧ r ≠ .r10 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [gpr r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2]; exact hcs r hr
  · rw [blocksAt_frame frame (VG.Proof.AesGcm.X86_64.Blocks.rest_disj hp hqn) (by omega)]
    exact blocksAt_frame hf₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (VG.Proof.AesGcm.X86_64.Blocks.kR'_disj hp (VG.Proof.AesGcm.X86_64.Blocks.dR s) (by simp)).symm.sub_left (Offset.sub_base _ (by omega))) (by omega)

omit hp in
/-- `cmp r9, 16`. -/
theorem cmp16_ok {s₁ : State} (h9 : s₁.gpr .r9 = s.gpr .r9) :
    WP isa (.block [.alu .cmp .r9 (imm 16)]) s₁ fun s₂ => s₂.gpr = s₁.gpr ∧ s₂.mem = s₁.mem ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ s₂.cf = some (decide (VG.Proof.AesGcm.X86_64.Blocks.n s < 16)) := by
  have e16 : BitVec.signExtend 64 (BitVec.ofNat 32 16) = 16 := by decide
  apply WP.of_runBlock
  simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags,
    isa, e16, h9, Option.bind_some, Option.some.injEq, exists_eq_left']
  simp

/-- The interleaved part and `rest`, from the state after the entry, given
what the loops leave (`post`) as `Mid` for the blocks hashed `ys q`. -/
theorem stitch_ok {piece : Prog isa} {Post : State → State → Prop} {ys : Nat → List Block}
    (hys : ys 0 = [])
    (hpiece : ∀ s₃, Gcm.X86_64.Stitch.SPre s₃ → WP isa piece s₃ (Post s₃))
    (hpost : ∀ s₃ s₄, s₃.gpr .r9 = BitVec.ofNat 64 (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16) → (∀ r ∈ VG.Proof.AesGcm.X86_64.Blocks.argRegs, s₃.gpr r = s.gpr r) →
      (∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r) → s₃.gpr .r11 = VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 64 → s₃.rd = s.rd →
      s₃.wr = s.wr →
      VG.Proof.AesGcm.X86_64.Blocks.Kept s 0 s₃.mem → Frame [VG.Proof.AesGcm.X86_64.Blocks.kR' s] s.mem s₃.mem → Post s₃ s₄ → VG.Proof.AesGcm.X86_64.Blocks.Mid s (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16) 0 (ys (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16)) s₄)
    {s₁ : State} (h11 : s₁.gpr .r11 = VG.Proof.AesGcm.X86_64.Blocks.S s) (hg : ∀ r, r ≠ .r11 → s₁.gpr r = s.gpr r) (hk : VG.Proof.AesGcm.X86_64.Blocks.Kept s 0 s₁.mem)
    (hf : Frame [VG.Proof.AesGcm.X86_64.Blocks.kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    WP isa (stitchPart piece) s₁ (VG.Proof.AesGcm.X86_64.Blocks.Mid s (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16) 0 (ys (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16))) := by
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.Blocks.cmp16_ok (hg _ (by decide))) fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)
  refine WP.ite (decide (VG.Proof.AesGcm.X86_64.Blocks.n s < 16)) (by simp only [eval, cf₂]) (fun h => ?_) (fun h => ?_)
  · have h0 : VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16 = 0 := by simp at h; omega
    rw [h0, hys]
    refine WP.block_nil (VG.Proof.AesGcm.X86_64.Blocks.mid_entry hp (fun r hr => by rw [g₂]; exact hg r hr) (by rw [m₂]; exact hk)
      (by rw [m₂]; exact hf) (rd₂.trans hrd) (wr₂.trans hwr))
  · have h16 : 16 ≤ VG.Proof.AesGcm.X86_64.Blocks.n s := by simp at h; omega
    refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.Blocks.split_ok (s := s) (by rw [g₂]; exact hg _ (by decide)))
      fun s₃ ⟨h9, h11₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
    have ga : ∀ r ∈ VG.Proof.AesGcm.X86_64.Blocks.argRegs, s₃.gpr r = s.gpr r := fun r hr => by
      simp only [VG.Proof.AesGcm.X86_64.Blocks.argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [g₃ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide), g₂,
        hg r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    have gc : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := fun r hr => by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [g₃ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), g₂,
        hg r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    have g11 : s₃.gpr .r11 = VG.Proof.AesGcm.X86_64.Blocks.S s + BitVec.ofNat 64 64 := by rw [h11₃, g₂, h11]
    have rd₃' : s₃.rd = s.rd := rd₃.trans (rd₂.trans hrd)
    have wr₃' : s₃.wr = s.wr := wr₃.trans (wr₂.trans hwr)
    have hk₃ : VG.Proof.AesGcm.X86_64.Blocks.Kept s 0 s₃.mem := by rw [m₃, m₂]; exact hk
    have hf₃ : Frame [VG.Proof.AesGcm.X86_64.Blocks.kR' s] s.mem s₃.mem := by rw [m₃, m₂]; exact hf
    exact WP.mono (hpiece s₃ (VG.Proof.AesGcm.X86_64.Blocks.spre_of hp h16 h9 ga g11 rd₃' wr₃')) fun s₄ hP =>
      hpost s₃ s₄ h9 ga gc g11 rd₃' wr₃' hk₃ hf₃ hP

/-- Encryption: the blocks hashed are those written. -/
theorem stitchE_ok {enc dec : Prog isa} (hS : Gcm.X86_64.Stitch.StitchOk enc dec) {s₁ : State} (h11 : s₁.gpr .r11 = VG.Proof.AesGcm.X86_64.Blocks.S s) (hg : ∀ r, r ≠ .r11 → s₁.gpr r = s.gpr r)
    (hk : VG.Proof.AesGcm.X86_64.Blocks.Kept s 0 s₁.mem) (hf : Frame [VG.Proof.AesGcm.X86_64.Blocks.kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    WP isa (stitchPart enc) s₁
      (VG.Proof.AesGcm.X86_64.Blocks.Mid s (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16) 0
        (ctr32 (VG.Proof.AesGcm.X86_64.Blocks.ciph s) (VG.Proof.AesGcm.X86_64.Blocks.cb s) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16)))) :=
  VG.Proof.AesGcm.X86_64.Blocks.stitch_ok hp (ys := fun q => ctr32 (VG.Proof.AesGcm.X86_64.Blocks.ciph s) (VG.Proof.AesGcm.X86_64.Blocks.cb s) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q)) rfl
    (fun _ h => hS.1 _ h)
    (fun s₃ s₄ h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP => by
      refine VG.Proof.AesGcm.X86_64.Blocks.mid_of_post hp h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP.data hP.ctr hP.frame hP.gpr hP.rd hP.wr
        fun eH eY _ eD => ?_
      have hn : VG.Proof.AesGcm.X86_64.Blocks.n s < 2 ^ 64 := (s.gpr .r9).isLt
      have hy := hP.y
      simp only [Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.hk, Gcm.X86_64.Stitch.y₀, Gcm.X86_64.Stitch.kp,
        Gcm.X86_64.Stitch.dp, Gcm.X86_64.Stitch.nb, h9, ga _ (by simp [VG.Proof.AesGcm.X86_64.Blocks.argRegs] : Reg.rcx ∈ argRegs),
        ga _ (by simp [VG.Proof.AesGcm.X86_64.Blocks.argRegs] : Reg.rdi ∈ argRegs), ga _ (by simp [VG.Proof.AesGcm.X86_64.Blocks.argRegs] : Reg.r8 ∈ argRegs),
        toNat_ofNat_of_lt (show VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16 < 2 ^ 64 by omega)] at hy
      rw [hy, eH, eY, eD])
    h11 hg hk hf hrd hwr

/-- Decryption: the blocks hashed are those read. -/
theorem stitchD_ok {enc dec : Prog isa} (hS : Gcm.X86_64.Stitch.StitchOk enc dec) {s₁ : State} (h11 : s₁.gpr .r11 = VG.Proof.AesGcm.X86_64.Blocks.S s) (hg : ∀ r, r ≠ .r11 → s₁.gpr r = s.gpr r)
    (hk : VG.Proof.AesGcm.X86_64.Blocks.Kept s 0 s₁.mem) (hf : Frame [VG.Proof.AesGcm.X86_64.Blocks.kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    WP isa (stitchPart dec) s₁
      (VG.Proof.AesGcm.X86_64.Blocks.Mid s (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16) 0
        (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16))) :=
  VG.Proof.AesGcm.X86_64.Blocks.stitch_ok hp (ys := fun q => blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q) rfl
    (fun _ h => hS.2 _ h)
    (fun s₃ s₄ h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP => by
      refine VG.Proof.AesGcm.X86_64.Blocks.mid_of_post hp h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP.data hP.ctr hP.frame hP.gpr hP.rd hP.wr
        fun eH eY eD _ => ?_
      have hn : VG.Proof.AesGcm.X86_64.Blocks.n s < 2 ^ 64 := (s.gpr .r9).isLt
      have hy := hP.y
      simp only [Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.hk, Gcm.X86_64.Stitch.y₀, Gcm.X86_64.Stitch.kp,
        Gcm.X86_64.Stitch.dp, Gcm.X86_64.Stitch.nb, h9, ga _ (by simp [VG.Proof.AesGcm.X86_64.Blocks.argRegs] : Reg.rcx ∈ argRegs),
        ga _ (by simp [VG.Proof.AesGcm.X86_64.Blocks.argRegs] : Reg.rdi ∈ argRegs), ga _ (by simp [VG.Proof.AesGcm.X86_64.Blocks.argRegs] : Reg.r8 ∈ argRegs),
        toNat_ofNat_of_lt (show VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16 < 2 ^ 64 by omega)] at hy
      rw [hy, eH, eY, eD])
    h11 hg hk hf hrd hwr

end

end VG.Proof.AesGcm.X86_64.Blocks

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Fn`. -/
section

/-!
# AES-GCM on whole blocks, x86-64: correctness

Untrusted: everything here is checked by Lean. The entry, the first
`16 ⌊n / 16⌋` blocks in one pass (with `stitch`), and the rest
(`encrypt_wp`, `decrypt_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

section
variable {s : State} (hp : VG.Proof.AesGcm.X86_64.Blocks.BP s)
include hp

/-- With nothing left, `Mid` is the end, when encrypting. -/
theorem encDone_of {q : Nat} {st : State} (M : VG.Proof.AesGcm.X86_64.Blocks.Mid s q q (ctr32 (VG.Proof.AesGcm.X86_64.Blocks.ciph s) (VG.Proof.AesGcm.X86_64.Blocks.cb s) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q)) st)
    (h0 : VG.Proof.AesGcm.X86_64.Blocks.n s - q = 0) : VG.Proof.AesGcm.X86_64.Blocks.EncDone s st := by
  have hq : q = VG.Proof.AesGcm.X86_64.Blocks.n s := by have := M.q_le; omega
  subst hq
  exact ⟨⟨M.saved, VG.Proof.AesGcm.X86_64.Blocks.keep_r hp M.frame⟩, M.data, M.ctr, M.y⟩

/-- With nothing left, `Mid` is the end, when decrypting. -/
theorem decDone_of {q : Nat} {st : State} (M : VG.Proof.AesGcm.X86_64.Blocks.Mid s q q (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q) st) (h0 : VG.Proof.AesGcm.X86_64.Blocks.n s - q = 0) :
    VG.Proof.AesGcm.X86_64.Blocks.DecDone s st := by
  have hq : q = VG.Proof.AesGcm.X86_64.Blocks.n s := by have := M.q_le; omega
  subst hq
  exact ⟨⟨M.saved, VG.Proof.AesGcm.X86_64.Blocks.keep_r hp M.frame⟩, M.data, M.ctr, M.y⟩

end

theorem encrypt_wp (v : GcmImpl) (st : Option StitchImpl) {s : State} (hpre : Proof.AesGcm.blocksPre s) :
    WP isa (encrypt v.callees.ctr v.callees.gh (st.map (·.enc))) s (VG.Proof.AesGcm.X86_64.Blocks.EncDone s) := by
  have hp := BP.of hpre
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.Blocks.entry_ok hp) fun s₁ ⟨h11, hg, hk, hf, hrd, hwr⟩ => ?_)
  have tl : ∀ q st, VG.Proof.AesGcm.X86_64.Blocks.Mid s q q (ctr32 (VG.Proof.AesGcm.X86_64.Blocks.ciph s) (VG.Proof.AesGcm.X86_64.Blocks.cb s) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q)) st →
      WP isa (tail (ctrCall v.callees.ctr) (ghCall v.callees.gh)) st (VG.Proof.AesGcm.X86_64.Blocks.EncDone s) := fun q st M =>
    VG.Proof.AesGcm.X86_64.Blocks.tail_calls hp _ _ M (fun _ M' h0 => VG.Proof.AesGcm.X86_64.Blocks.encDone_of hp M' h0) fun _ M' hlt => VG.Proof.AesGcm.X86_64.Blocks.encCalls_ok hp v M' hlt
  cases st with
  | none => exact WP.seq (WP.block_nil (tl 0 s₁ (VG.Proof.AesGcm.X86_64.Blocks.mid_entry hp hg hk hf hrd hwr)))
  | some p => exact WP.seq (WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.Blocks.stitchE_ok hp p.ok h11 hg hk hf hrd hwr) fun st M =>
      WP.mono (VG.Proof.AesGcm.X86_64.Blocks.rest_ok hp rfl M) fun st' M' => tl _ st' M'))

theorem decrypt_wp (v : GcmImpl) (st : Option StitchImpl) {s : State} (hpre : Proof.AesGcm.blocksPre s) :
    WP isa (decrypt v.callees.ctr v.callees.gh (st.map (·.dec))) s (VG.Proof.AesGcm.X86_64.Blocks.DecDone s) := by
  have hp := BP.of hpre
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.Blocks.entry_ok hp) fun s₁ ⟨h11, hg, hk, hf, hrd, hwr⟩ => ?_)
  have tl : ∀ q st, VG.Proof.AesGcm.X86_64.Blocks.Mid s q q (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q) st →
      WP isa (tail (ghCall v.callees.gh) (ctrCall v.callees.ctr)) st (VG.Proof.AesGcm.X86_64.Blocks.DecDone s) := fun q st M =>
    VG.Proof.AesGcm.X86_64.Blocks.tail_calls hp _ _ M (fun _ M' h0 => VG.Proof.AesGcm.X86_64.Blocks.decDone_of hp M' h0) fun _ M' hlt => VG.Proof.AesGcm.X86_64.Blocks.decCalls_ok hp v M' hlt
  cases st with
  | none => exact WP.seq (WP.block_nil (tl 0 s₁ (VG.Proof.AesGcm.X86_64.Blocks.mid_entry hp hg hk hf hrd hwr)))
  | some p => exact WP.seq (WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.Blocks.stitchD_ok hp p.ok h11 hg hk hf hrd hwr) fun st M =>
      WP.mono (VG.Proof.AesGcm.X86_64.Blocks.rest_ok hp rfl M) fun st' M' => tl _ st' M'))

end VG.Proof.AesGcm.X86_64.Blocks

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.CT`. -/
section

/-!
# AES-GCM on whole blocks, x86-64: constant time

Untrusted: everything here is checked by Lean. Two runs from states with the
same public arguments go through the same pieces: each load of `scratch`
from the stack gives both the same pointer (`rel_r11`), after which the taint
analysis checks the piece from it and `rsp`; the interleaved loops are checked
from the arguments in their registers; the branch on the blocks left agrees
(`tailHead_ok`); and the calls get the same public arguments (`ctr_rel`,
`gh_rel`), from what correctness says of each run (`rel_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Spec.Gcm (Block blockAt blocksAt ctr32)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- `scratch`, loaded from the stack into `r11`. -/
theorem loadR11_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 8))]) s fun s' =>
      s'.gpr .r11 = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 ∧ ∀ r, r ≠ .r11 → s'.gpr r = s.gpr r := by
  refine WP.of_runBlock ⟨_, by xrun [hr], ?_, ?_⟩
  · simp [gpr_setReg]
  · intro r a; simp [gpr_setReg, a]

theorem loadR11_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .r11 (.mem (at_ .rsp 8))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

/-- A block that first loads `scratch` into `r11`, from states that agree on
`rs` (with `rsp`) and hold the same pointer there, checked from `r11` and
`rs`. -/
theorem rel_r11 {P : State → State → Prop} {l₀ l : List Instr}
    (hl : l₀ = ([.mov .r11 (.mem (at_ .rsp 8))] : List Instr) ++ l) (rs rs' : List Reg) (hrs : .rsp ∈ rs)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hS : ∀ s₁ s₂, P s₁ s₂ → s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 8) 64 =
      s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 8) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 8) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 8) 8)
    (hc : ∃ hc, ((taint.check (Taint.ofRegs (.r11 :: rs)) (.block l) hc).map fun τ' =>
      (RegSet.ofList rs').subset τ'.regs && (!false || τ'.flags)) = some true) :
    RelCT isa P (.block l₀) fun s₁ s₂ => ∀ r ∈ rs', s₁.gpr r = s₂.gpr r := by
  subst hl
  have l₁ := RelCT.wpDep (rel_taint (P := P) [.rsp] (fun s₁ s₂ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hag _ _ h _ hrs) VG.Proof.AesGcm.X86_64.Blocks.loadR11_check)
    (F := fun (σ s' : State) => s'.gpr .r11 = σ.mem.readW (σ.gpr .rsp + BitVec.ofNat 64 8) 64 ∧
      ∀ r, r ≠ .r11 → s'.gpr r = σ.gpr r)
    fun s₁ s₂ h => ⟨VG.Proof.AesGcm.X86_64.Blocks.loadR11_ok (hS _ _ h).2.1, VG.Proof.AesGcm.X86_64.Blocks.loadR11_ok (hS _ _ h).2.2⟩
  refine rel_block_split (RelCT.seq l₁ ((rel_regs (.r11 :: rs) rs' false (fun s₁ s₂ h r hr => ?_) hc).mono
    (fun _ _ h => h) fun _ _ h => h.1))
  obtain ⟨-, σ₁, σ₂, hσ, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ := h
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [a₁, a₂]; exact (hS _ _ hσ).1
  · by_cases hx : r = .r11
    · subst hx; rw [a₁, a₂]; exact (hS _ _ hσ).1
    · rw [b₁ r hx, b₂ r hx]; exact hag _ _ hσ r hr

section
variable {s : State} (hp : VG.Proof.AesGcm.X86_64.Blocks.BP s)
include hp

/-- `Ready` after `ctrCall`. -/
theorem ctrCall_ready (c : Ctr32Impl) {q : Nat} {st : State} (h : VG.Proof.AesGcm.X86_64.Blocks.Ready s q st) (hq : q < VG.Proof.AesGcm.X86_64.Blocks.n s) :
    WP isa (ctrCall ⟨c.callee.name, c.callee.code⟩) st (VG.Proof.AesGcm.X86_64.Blocks.Ready s q) :=
  WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.Blocks.ctrArgs_ok hp h hq) fun st₂ ⟨hc, R₂, _, _⟩ => WP.mono (ctr_call c hc) fun st₃ g => by
    have f₃ := g.frame
    rw [R₂.rsp] at f₃
    exact R₂.frame f₃ (fun r hr => (VG.Proof.AesGcm.X86_64.Blocks.apart_kR' hp (q := q) (by omega)).ctr r hr) (fun r hr => (VG.Proof.AesGcm.X86_64.Blocks.apart_a hp (q := q) (by omega)).ctr r hr)
      (g.saved _ (by decide)) g.rd g.wr)

/-- `Ready` after `ghCall`. -/
theorem ghCall_ready (g : GhashImpl) {q : Nat} {st : State} (h : VG.Proof.AesGcm.X86_64.Blocks.Ready s q st) (hq : q < VG.Proof.AesGcm.X86_64.Blocks.n s) :
    WP isa (ghCall g.fn) st (VG.Proof.AesGcm.X86_64.Blocks.Ready s q) :=
  WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.Blocks.ghArgs_ok hp h hq) fun st₂ ⟨hc, R₂, _, _⟩ => WP.mono (gh_call g hc) fun st₃ g' => by
    have f₃ := g'.frame
    rw [R₂.rsp] at f₃
    exact R₂.frame f₃ (fun r hr => (VG.Proof.AesGcm.X86_64.Blocks.apart_kR' hp (q := q) (by omega)).gh r hr) (fun r hr => (VG.Proof.AesGcm.X86_64.Blocks.apart_a hp (q := q) (by omega)).gh r hr)
      (g'.saved _ (by decide)) g'.rd g'.wr)

end

/-! ## Two runs -/

/-- What two entry states with the same public arguments share. -/
structure Pub (s₀ s₀' : State) : Prop where
  k : VG.Proof.AesGcm.X86_64.Blocks.K s₀' = VG.Proof.AesGcm.X86_64.Blocks.K s₀
  rsi : s₀'.gpr .rsi = s₀.gpr .rsi
  c : VG.Proof.AesGcm.X86_64.Blocks.C s₀' = VG.Proof.AesGcm.X86_64.Blocks.C s₀
  y : VG.Proof.AesGcm.X86_64.Blocks.Y s₀' = VG.Proof.AesGcm.X86_64.Blocks.Y s₀
  d : VG.Proof.AesGcm.X86_64.Blocks.D s₀' = VG.Proof.AesGcm.X86_64.Blocks.D s₀
  r9 : s₀'.gpr .r9 = s₀.gpr .r9
  sp : VG.Proof.AesGcm.X86_64.Blocks.SP s₀' = VG.Proof.AesGcm.X86_64.Blocks.SP s₀
  sc : VG.Proof.AesGcm.X86_64.Blocks.S s₀' = VG.Proof.AesGcm.X86_64.Blocks.S s₀

theorem Pub.of {s₀ s₀' : State} (h : Proof.AesGcm.blocksPub s₀ s₀') : VG.Proof.AesGcm.X86_64.Blocks.Pub s₀ s₀' :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.1.symm,
    h.2.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.2.symm⟩

theorem Pub.en {s₀ s₀' : State} (pb : VG.Proof.AesGcm.X86_64.Blocks.Pub s₀ s₀') : VG.Proof.AesGcm.X86_64.Blocks.n s₀' = VG.Proof.AesGcm.X86_64.Blocks.n s₀ := by simp only [VG.Proof.AesGcm.X86_64.Blocks.n, pb.r9]
theorem Pub.eR {s₀ s₀' : State} (pb : VG.Proof.AesGcm.X86_64.Blocks.Pub s₀ s₀') : VG.Proof.AesGcm.X86_64.Blocks.R s₀' = VG.Proof.AesGcm.X86_64.Blocks.R s₀ := by simp only [VG.Proof.AesGcm.X86_64.Blocks.R, pb.rsi]
theorem Pub.edq {s₀ s₀' : State} (pb : VG.Proof.AesGcm.X86_64.Blocks.Pub s₀ s₀') (q : Nat) : VG.Proof.AesGcm.X86_64.Blocks.dq s₀' q = VG.Proof.AesGcm.X86_64.Blocks.dq s₀ q := by simp only [VG.Proof.AesGcm.X86_64.Blocks.dq, pb.d]
theorem Pub.es5 {s₀ s₀' : State} (pb : VG.Proof.AesGcm.X86_64.Blocks.Pub s₀ s₀') : VG.Proof.AesGcm.X86_64.Blocks.S5 s₀' = VG.Proof.AesGcm.X86_64.Blocks.S5 s₀ := by simp only [VG.Proof.AesGcm.X86_64.Blocks.S5, pb.sc]

theorem tailHead_check : ∃ hc, ((taint.check (Taint.ofRegs [.r11, .rsp])
    (.block [.mov .r8 (.mem (at_ .r11 argN)), .alu .test .r8 (.reg .r8)]) hc).map fun τ' =>
      (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

/-- The registers of the arguments, which the entry keeps. -/
def args : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]

theorem entry_check : ∃ hc, ((taint.check (Taint.ofRegs (.r11 :: VG.Proof.AesGcm.X86_64.Blocks.args)) (.block entry.tail) hc).map fun τ' =>
    (RegSet.ofList (.r11 :: VG.Proof.AesGcm.X86_64.Blocks.args)).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem rest_check : ∃ hc, ((taint.check (Taint.ofRegs [.r11, .rsp]) (.block rest.tail) hc).map fun τ' =>
    (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem nil_check : ∃ hc, ((taint.check (Taint.ofRegs (.r11 :: VG.Proof.AesGcm.X86_64.Blocks.args)) (.block []) hc).map
    fun τ' => (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem ctrArgs_check : ∃ hc, ((taint.check (Taint.ofRegs [.r11, .rsp]) (.block ctrArgs.tail) hc).map fun τ' =>
    (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem ghArgs_check : ∃ hc, ((taint.check (Taint.ofRegs [.r11, .rsp]) (.block ghArgs.tail) hc).map fun τ' =>
    (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

section
variable {s₀ s₀' : State} (hp : VG.Proof.AesGcm.X86_64.Blocks.BP s₀) (hp' : VG.Proof.AesGcm.X86_64.Blocks.BP s₀') (pb : VG.Proof.AesGcm.X86_64.Blocks.Pub s₀ s₀')
include hp hp' pb

/-- Loading `scratch` from the stack, in two runs that are `Ready`. -/
theorem ready_hS {q q' : Nat} {s₁ s₂ : State} (h₁ : VG.Proof.AesGcm.X86_64.Blocks.Ready s₀ q s₁) (h₂ : VG.Proof.AesGcm.X86_64.Blocks.Ready s₀' q' s₂) :
    s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 8) 64 = s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 8) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 8) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 8) 8 := by
  refine ⟨by rw [h₁.rsp, h₂.rsp, h₁.arg, h₂.arg, pb.sc], ?_, ?_⟩
  · rw [h₁.rd, h₁.wr, h₁.rsp]; exact VG.Proof.AesGcm.X86_64.Blocks.a_in hp
  · rw [h₂.rd, h₂.wr, h₂.rsp]; exact VG.Proof.AesGcm.X86_64.Blocks.a_in hp'

omit hp hp' in
theorem ready_rsp {q q' : Nat} {s₁ s₂ : State} (h₁ : VG.Proof.AesGcm.X86_64.Blocks.Ready s₀ q s₁) (h₂ : VG.Proof.AesGcm.X86_64.Blocks.Ready s₀' q' s₂) :
    ∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rsp, h₂.rsp, pb.sp]

/-- `ctrCall`, in two runs `Ready` for the same blocks left. -/
theorem ctrCall_rel (c : Ctr32Impl) {q : Nat} (hq : q < VG.Proof.AesGcm.X86_64.Blocks.n s₀) :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.Blocks.Ready s₀ q s₁ ∧ VG.Proof.AesGcm.X86_64.Blocks.Ready s₀' q s₂) (ctrCall ⟨c.callee.name, c.callee.code⟩)
      fun s₁ s₂ => VG.Proof.AesGcm.X86_64.Blocks.Ready s₀ q s₁ ∧ VG.Proof.AesGcm.X86_64.Blocks.Ready s₀' q s₂ := by
  have hq' : q < VG.Proof.AesGcm.X86_64.Blocks.n s₀' := by rw [pb.en]; exact hq
  have a := rel_wp (VG.Proof.AesGcm.X86_64.Blocks.rel_r11 (l₀ := ctrArgs) (l := ctrArgs.tail) rfl (P := fun s₁ s₂ => VG.Proof.AesGcm.X86_64.Blocks.Ready s₀ q s₁ ∧ VG.Proof.AesGcm.X86_64.Blocks.Ready s₀' q s₂) [.rsp] [.rsp]
      (by simp) (fun _ _ h => VG.Proof.AesGcm.X86_64.Blocks.ready_rsp pb h.1 h.2) (fun _ _ h => VG.Proof.AesGcm.X86_64.Blocks.ready_hS hp hp' pb h.1 h.2) VG.Proof.AesGcm.X86_64.Blocks.ctrArgs_check)
    (fun _ _ h => h) (G₁ := fun st' => CtrCall st' (VG.Proof.AesGcm.X86_64.Blocks.K s₀) (VG.Proof.AesGcm.X86_64.Blocks.C s₀) (VG.Proof.AesGcm.X86_64.Blocks.dq s₀ q) (VG.Proof.AesGcm.X86_64.Blocks.S5 s₀) (VG.Proof.AesGcm.X86_64.Blocks.R s₀) (VG.Proof.AesGcm.X86_64.Blocks.n s₀ - q) ∧ VG.Proof.AesGcm.X86_64.Blocks.Ready s₀ q st')
    (G₂ := fun st' => CtrCall st' (VG.Proof.AesGcm.X86_64.Blocks.K s₀') (VG.Proof.AesGcm.X86_64.Blocks.C s₀') (VG.Proof.AesGcm.X86_64.Blocks.dq s₀' q) (VG.Proof.AesGcm.X86_64.Blocks.S5 s₀') (VG.Proof.AesGcm.X86_64.Blocks.R s₀') (VG.Proof.AesGcm.X86_64.Blocks.n s₀' - q) ∧ VG.Proof.AesGcm.X86_64.Blocks.Ready s₀' q st')
    (fun _ h => WP.mono (VG.Proof.AesGcm.X86_64.Blocks.ctrArgs_ok hp h hq) fun _ h => ⟨h.1, h.2.1⟩)
    (fun _ h => WP.mono (VG.Proof.AesGcm.X86_64.Blocks.ctrArgs_ok hp' h hq') fun _ h => ⟨h.1, h.2.1⟩)
  refine (rel_wp (RelCT.seq a (ctr_rel c fun s₁ s₂ h => ?_)) (fun _ _ h => h) (fun _ h => VG.Proof.AesGcm.X86_64.Blocks.ctrCall_ready hp c h hq)
    (fun _ h => VG.Proof.AesGcm.X86_64.Blocks.ctrCall_ready hp' c h hq')).mono (fun _ _ h => h) fun _ _ h => h.2
  obtain ⟨hr, ⟨c₁, -⟩, ⟨c₂, -⟩⟩ := h
  rw [pb.k, pb.c, pb.edq, pb.es5, pb.eR, pb.en] at c₂
  exact ⟨_, _, _, _, _, _, c₁, c₂, hr _ (List.mem_singleton_self _)⟩

/-- `ghCall`, in two runs `Ready` for the same blocks left. -/
theorem ghCall_rel (g : GhashImpl) {q : Nat} (hq : q < VG.Proof.AesGcm.X86_64.Blocks.n s₀) :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.Blocks.Ready s₀ q s₁ ∧ VG.Proof.AesGcm.X86_64.Blocks.Ready s₀' q s₂) (ghCall g.fn)
      fun s₁ s₂ => VG.Proof.AesGcm.X86_64.Blocks.Ready s₀ q s₁ ∧ VG.Proof.AesGcm.X86_64.Blocks.Ready s₀' q s₂ := by
  have hq' : q < VG.Proof.AesGcm.X86_64.Blocks.n s₀' := by rw [pb.en]; exact hq
  have a := rel_wp (VG.Proof.AesGcm.X86_64.Blocks.rel_r11 (l₀ := ghArgs) (l := ghArgs.tail) rfl (P := fun s₁ s₂ => VG.Proof.AesGcm.X86_64.Blocks.Ready s₀ q s₁ ∧ VG.Proof.AesGcm.X86_64.Blocks.Ready s₀' q s₂) [.rsp] [.rsp]
      (by simp) (fun _ _ h => VG.Proof.AesGcm.X86_64.Blocks.ready_rsp pb h.1 h.2) (fun _ _ h => VG.Proof.AesGcm.X86_64.Blocks.ready_hS hp hp' pb h.1 h.2) VG.Proof.AesGcm.X86_64.Blocks.ghArgs_check)
    (fun _ _ h => h) (G₁ := fun st' => GhCall st' (VG.Proof.AesGcm.X86_64.Blocks.K s₀ + BitVec.ofNat 64 240) (VG.Proof.AesGcm.X86_64.Blocks.Y s₀) (VG.Proof.AesGcm.X86_64.Blocks.dq s₀ q) (VG.Proof.AesGcm.X86_64.Blocks.S5 s₀) (VG.Proof.AesGcm.X86_64.Blocks.n s₀ - q) ∧ VG.Proof.AesGcm.X86_64.Blocks.Ready s₀ q st')
    (G₂ := fun st' => GhCall st' (VG.Proof.AesGcm.X86_64.Blocks.K s₀' + BitVec.ofNat 64 240) (VG.Proof.AesGcm.X86_64.Blocks.Y s₀') (VG.Proof.AesGcm.X86_64.Blocks.dq s₀' q) (VG.Proof.AesGcm.X86_64.Blocks.S5 s₀') (VG.Proof.AesGcm.X86_64.Blocks.n s₀' - q) ∧
      VG.Proof.AesGcm.X86_64.Blocks.Ready s₀' q st')
    (fun _ h => WP.mono (VG.Proof.AesGcm.X86_64.Blocks.ghArgs_ok hp h hq) fun _ h => ⟨h.1, h.2.1⟩)
    (fun _ h => WP.mono (VG.Proof.AesGcm.X86_64.Blocks.ghArgs_ok hp' h hq') fun _ h => ⟨h.1, h.2.1⟩)
  refine (rel_wp (RelCT.seq a (gh_rel g fun s₁ s₂ h => ?_)) (fun _ _ h => h) (fun _ h => VG.Proof.AesGcm.X86_64.Blocks.ghCall_ready hp g h hq)
    (fun _ h => VG.Proof.AesGcm.X86_64.Blocks.ghCall_ready hp' g h hq')).mono (fun _ _ h => h) fun _ _ h => h.2
  obtain ⟨hr, ⟨c₁, -⟩, ⟨c₂, -⟩⟩ := h
  rw [pb.k, pb.y, pb.edq, pb.es5, pb.en] at c₂
  exact ⟨_, _, _, _, _, c₁, c₂, hr _ (List.mem_singleton_self _)⟩

/-- `tail`, from two runs at the same point. -/
theorem tail_rel {first second : Prog isa}
    (h₁ : ∀ q, q < VG.Proof.AesGcm.X86_64.Blocks.n s₀ → RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.Blocks.Ready s₀ q s₁ ∧ VG.Proof.AesGcm.X86_64.Blocks.Ready s₀' q s₂) first
      fun s₁ s₂ => VG.Proof.AesGcm.X86_64.Blocks.Ready s₀ q s₁ ∧ VG.Proof.AesGcm.X86_64.Blocks.Ready s₀' q s₂)
    (h₂ : ∀ q, q < VG.Proof.AesGcm.X86_64.Blocks.n s₀ → RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.Blocks.Ready s₀ q s₁ ∧ VG.Proof.AesGcm.X86_64.Blocks.Ready s₀' q s₂) second
      fun s₁ s₂ => VG.Proof.AesGcm.X86_64.Blocks.Ready s₀ q s₁ ∧ VG.Proof.AesGcm.X86_64.Blocks.Ready s₀' q s₂)
    {q : Nat} {ys ys' : List Block} :
    RelCT isa (fun s₁ s₂ => VG.Proof.AesGcm.X86_64.Blocks.Mid s₀ q q ys s₁ ∧ VG.Proof.AesGcm.X86_64.Blocks.Mid s₀' q q ys' s₂) (tail first second) fun _ _ => True := by
  have a := rel_wp (VG.Proof.AesGcm.X86_64.Blocks.rel_r11 (l₀ := [.mov .r11 (.mem (at_ .rsp 8)), .mov .r8 (.mem (at_ .r11 argN)),
      .alu .test .r8 (.reg .r8)]) (l := [.mov .r8 (.mem (at_ .r11 argN)), .alu .test .r8 (.reg .r8)]) rfl
      (P := fun s₁ s₂ => VG.Proof.AesGcm.X86_64.Blocks.Mid s₀ q q ys s₁ ∧ VG.Proof.AesGcm.X86_64.Blocks.Mid s₀' q q ys' s₂) [.rsp] [.rsp] (by simp)
      (fun _ _ h => VG.Proof.AesGcm.X86_64.Blocks.ready_rsp pb (h.1.ready hp) (h.2.ready hp'))
      (fun _ _ h => VG.Proof.AesGcm.X86_64.Blocks.ready_hS hp hp' pb (h.1.ready hp) (h.2.ready hp')) VG.Proof.AesGcm.X86_64.Blocks.tailHead_check)
    (fun _ _ h => h) (fun _ h => VG.Proof.AesGcm.X86_64.Blocks.tailHead_ok hp h) (fun _ h => VG.Proof.AesGcm.X86_64.Blocks.tailHead_ok hp' h)
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.2.1.2, h.2.2.2, pb.en]) ?_ ?_)
  · exact (rel_taint [] (fun _ _ _ r hr => by cases hr) ⟨_, by taint_decide⟩).mono (fun _ _ h => h) fun _ _ h => h
  · by_cases hlt : q < VG.Proof.AesGcm.X86_64.Blocks.n s₀
    · exact (RelCT.seq (h₁ q hlt) (h₂ q hlt)).mono (fun _ _ h => ⟨h.1.2.1.1.ready hp, h.1.2.2.1.ready hp'⟩)
        fun _ _ _ => trivial
    · intro s₁ s₂ _ _ _ _ h
      have e := h.1.2.1.2
      rw [h.2] at e
      simp only [Option.some.injEq, Bool.false_eq, decide_eq_false_iff_not] at e
      exact absurd (by omega) e

/-- What the entry leaves. -/
def EntryPost (s₀ s₁ : State) : Prop :=
  s₁.gpr .r11 = VG.Proof.AesGcm.X86_64.Blocks.S s₀ ∧ (∀ r, r ≠ .r11 → s₁.gpr r = s₀.gpr r) ∧ VG.Proof.AesGcm.X86_64.Blocks.Kept s₀ 0 s₁.mem ∧ Frame [VG.Proof.AesGcm.X86_64.Blocks.kR' s₀] s₀.mem s₁.mem ∧
    s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr

/-- The entry, in two runs. -/
theorem entry_rel : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun s₁ s₂ =>
    (∀ r ∈ .r11 :: VG.Proof.AesGcm.X86_64.Blocks.args, s₁.gpr r = s₂.gpr r) ∧ VG.Proof.AesGcm.X86_64.Blocks.EntryPost s₀ s₁ ∧ VG.Proof.AesGcm.X86_64.Blocks.EntryPost s₀' s₂ := by
  have ea : ∀ r ∈ VG.Proof.AesGcm.X86_64.Blocks.args, s₀.gpr r = s₀'.gpr r := by
    intro r hr
    simp only [VG.Proof.AesGcm.X86_64.Blocks.args, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pb.k.symm, pb.rsi.symm, pb.c.symm, pb.y.symm, pb.d.symm, pb.r9.symm, pb.sp.symm]
  refine rel_wp (VG.Proof.AesGcm.X86_64.Blocks.rel_r11 (l₀ := entry) (l := entry.tail) rfl VG.Proof.AesGcm.X86_64.Blocks.args (.r11 :: VG.Proof.AesGcm.X86_64.Blocks.args) (by simp [VG.Proof.AesGcm.X86_64.Blocks.args])
    (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ea) (fun _ _ h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by rw [VG.Proof.AesGcm.X86_64.Blocks.arg_eq, VG.Proof.AesGcm.X86_64.Blocks.arg_eq, pb.sc], VG.Proof.AesGcm.X86_64.Blocks.a_in hp, VG.Proof.AesGcm.X86_64.Blocks.a_in hp'⟩) VG.Proof.AesGcm.X86_64.Blocks.entry_check)
    (fun _ _ h => h) (fun s h => by subst h; exact VG.Proof.AesGcm.X86_64.Blocks.entry_ok hp) (fun s h => by subst h; exact VG.Proof.AesGcm.X86_64.Blocks.entry_ok hp')

/-- The interleaved part (or nothing) and `rest`, in two runs. -/
theorem part_rel (piece : Option (Prog isa)) {ys : State → Nat → List Block}
    (hys : ∀ s, ys s 0 = [])
    (hc : ∀ p, piece = some p → ∃ hc, ((taint.check (Taint.ofRegs (.r11 :: VG.Proof.AesGcm.X86_64.Blocks.args)) (stitchPart p) hc).map
      fun τ' => (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true)
    (hw : ∀ p, piece = some p → ∀ {s : State}, VG.Proof.AesGcm.X86_64.Blocks.BP s → ∀ {s₁ : State}, VG.Proof.AesGcm.X86_64.Blocks.EntryPost s s₁ →
      WP isa (stitchPart p) s₁ (VG.Proof.AesGcm.X86_64.Blocks.Mid s (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16) 0 (ys s (VG.Proof.AesGcm.X86_64.Blocks.n s - VG.Proof.AesGcm.X86_64.Blocks.n s % 16)))) :
    RelCT isa (fun s₁ s₂ => (∀ r ∈ .r11 :: VG.Proof.AesGcm.X86_64.Blocks.args, s₁.gpr r = s₂.gpr r) ∧ VG.Proof.AesGcm.X86_64.Blocks.EntryPost s₀ s₁ ∧ VG.Proof.AesGcm.X86_64.Blocks.EntryPost s₀' s₂)
      (head piece)
      fun s₁ s₂ => ∃ q, VG.Proof.AesGcm.X86_64.Blocks.Mid s₀ q q (ys s₀ q) s₁ ∧ VG.Proof.AesGcm.X86_64.Blocks.Mid s₀' q q (ys s₀' q) s₂ := by
  cases piece with
  | none =>
    refine ((rel_regs (.r11 :: VG.Proof.AesGcm.X86_64.Blocks.args) [.rsp] false (fun _ _ h => h.1) VG.Proof.AesGcm.X86_64.Blocks.nil_check).wp
      (F₁ := VG.Proof.AesGcm.X86_64.Blocks.Mid s₀ 0 0 (ys s₀ 0)) (F₂ := VG.Proof.AesGcm.X86_64.Blocks.Mid s₀' 0 0 (ys s₀' 0)) fun s₁ s₂ h => ⟨WP.block_nil ?_,
        WP.block_nil ?_⟩).mono (fun _ _ h => h) fun _ _ h => ⟨0, h.2.1, h.2.2⟩
    · obtain ⟨-, ⟨-, b, c, d, e, f⟩, -⟩ := h; rw [hys]; exact VG.Proof.AesGcm.X86_64.Blocks.mid_entry hp b c d e f
    · obtain ⟨-, -, ⟨-, b, c, d, e, f⟩⟩ := h; rw [hys]; exact VG.Proof.AesGcm.X86_64.Blocks.mid_entry hp' b c d e f
  | some p =>
    have a := rel_wp (P := fun s₁ s₂ => (∀ r ∈ .r11 :: VG.Proof.AesGcm.X86_64.Blocks.args, s₁.gpr r = s₂.gpr r) ∧ VG.Proof.AesGcm.X86_64.Blocks.EntryPost s₀ s₁ ∧
        VG.Proof.AesGcm.X86_64.Blocks.EntryPost s₀' s₂) (rel_regs (.r11 :: VG.Proof.AesGcm.X86_64.Blocks.args) [.rsp] false (fun _ _ h => h.1) (hc p rfl)) (fun _ _ h => h.2)
      (fun _ h => hw p rfl hp h) (fun _ h => hw p rfl hp' h)
    have b := rel_wp (VG.Proof.AesGcm.X86_64.Blocks.rel_r11 (l₀ := rest) (l := rest.tail) rfl
      (P := fun s₁ s₂ => (∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r) ∧
        VG.Proof.AesGcm.X86_64.Blocks.Mid s₀ (VG.Proof.AesGcm.X86_64.Blocks.n s₀ - VG.Proof.AesGcm.X86_64.Blocks.n s₀ % 16) 0 (ys s₀ (VG.Proof.AesGcm.X86_64.Blocks.n s₀ - VG.Proof.AesGcm.X86_64.Blocks.n s₀ % 16)) s₁ ∧
        VG.Proof.AesGcm.X86_64.Blocks.Mid s₀' (VG.Proof.AesGcm.X86_64.Blocks.n s₀' - VG.Proof.AesGcm.X86_64.Blocks.n s₀' % 16) 0 (ys s₀' (VG.Proof.AesGcm.X86_64.Blocks.n s₀' - VG.Proof.AesGcm.X86_64.Blocks.n s₀' % 16)) s₂) [.rsp] [.rsp] (by simp)
      (fun _ _ h => h.1) (fun _ _ h => VG.Proof.AesGcm.X86_64.Blocks.ready_hS hp hp' pb (h.2.1.ready hp) (h.2.2.ready hp')) VG.Proof.AesGcm.X86_64.Blocks.rest_check)
      (fun _ _ h => h.2) (fun _ h => VG.Proof.AesGcm.X86_64.Blocks.rest_ok hp rfl h) (fun _ h => VG.Proof.AesGcm.X86_64.Blocks.rest_ok hp' rfl h)
    refine (RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => ⟨h.1.1, h.2⟩) b).mono (fun _ _ h => h)
      fun _ _ h => ⟨VG.Proof.AesGcm.X86_64.Blocks.n s₀ - VG.Proof.AesGcm.X86_64.Blocks.n s₀ % 16, h.2.1, ?_⟩
    rw [← pb.en]; exact h.2.2

end

theorem encrypt_ct (v : GcmImpl) (st : Option StitchImpl) :
    ConstantTime isa Proof.AesGcm.encryptBlocksX86_64.pre Proof.AesGcm.encryptBlocksX86_64.pub
      (encrypt v.callees.ctr v.callees.gh (st.map (·.enc))) := by
  refine ct_of_rel fun s₀ s₀' h h' hq => ?_
  have hp := BP.of h
  have hp' := BP.of h'
  have pb := Pub.of hq
  refine RelCT.seq (VG.Proof.AesGcm.X86_64.Blocks.entry_rel hp hp' pb) (RelCT.seq (VG.Proof.AesGcm.X86_64.Blocks.part_rel hp hp' pb (st.map (·.enc))
    (ys := fun s q => ctr32 (VG.Proof.AesGcm.X86_64.Blocks.ciph s) (VG.Proof.AesGcm.X86_64.Blocks.cb s) (blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q)) (fun _ => rfl)
    (fun _ e => by obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.1 e; exact i.encP.ct)
    fun _ e {_} hp {_} h => by
      obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.1 e
      obtain ⟨a, b, c, d, e, f⟩ := h; exact VG.Proof.AesGcm.X86_64.Blocks.stitchE_ok hp i.ok a b c d e f) ?_)
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, M₁, M₂⟩ e₁ e₂
  exact VG.Proof.AesGcm.X86_64.Blocks.tail_rel hp hp' pb (fun q hq => VG.Proof.AesGcm.X86_64.Blocks.ctrCall_rel hp hp' pb v.ctr hq) (fun q hq => VG.Proof.AesGcm.X86_64.Blocks.ghCall_rel hp hp' pb v.gh hq)
    _ _ _ _ _ _ ⟨M₁, M₂⟩ e₁ e₂

theorem decrypt_ct (v : GcmImpl) (st : Option StitchImpl) :
    ConstantTime isa Proof.AesGcm.decryptBlocksX86_64.pre Proof.AesGcm.decryptBlocksX86_64.pub
      (decrypt v.callees.ctr v.callees.gh (st.map (·.dec))) := by
  refine ct_of_rel fun s₀ s₀' h h' hq => ?_
  have hp := BP.of h
  have hp' := BP.of h'
  have pb := Pub.of hq
  refine RelCT.seq (VG.Proof.AesGcm.X86_64.Blocks.entry_rel hp hp' pb) (RelCT.seq (VG.Proof.AesGcm.X86_64.Blocks.part_rel hp hp' pb (st.map (·.dec))
    (ys := fun s q => blocksAt s.mem (VG.Proof.AesGcm.X86_64.Blocks.D s) q) (fun _ => rfl)
    (fun _ e => by obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.1 e; exact i.decP.ct)
    fun _ e {_} hp {_} h => by
      obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.1 e
      obtain ⟨a, b, c, d, e, f⟩ := h; exact VG.Proof.AesGcm.X86_64.Blocks.stitchD_ok hp i.ok a b c d e f) ?_)
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, M₁, M₂⟩ e₁ e₂
  exact VG.Proof.AesGcm.X86_64.Blocks.tail_rel hp hp' pb (fun q hq => VG.Proof.AesGcm.X86_64.Blocks.ghCall_rel hp hp' pb v.gh hq) (fun q hq => VG.Proof.AesGcm.X86_64.Blocks.ctrCall_rel hp hp' pb v.ctr hq)
    _ _ _ _ _ _ ⟨M₁, M₂⟩ e₁ e₂

end VG.Proof.AesGcm.X86_64.Blocks

end
