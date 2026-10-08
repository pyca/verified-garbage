import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Contract
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Mid
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Impl.AesGcm.X86_64.SealGather
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: the setting

Untrusted: everything here is checked by Lean. The arguments of the entry
state `s` (`K`, `Nn`, `NL`, `Ad`, `AL`, `Src`, `Cnt`, `Dst`, `L`, `Tg`,
`W`), their regions, and the facts of `sealGatherPreM` by name (`SG`); the
slots of `work` the code keeps the arguments and its progress in (`Kept`),
and the entry, which fills them (`entry1_ok`, `entry2_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gathered gatheredLen)

section
variable (s : State)

abbrev K : Addr := s.gpr .rdi
abbrev Nn : Addr := s.gpr .rdx
abbrev NL : Nat := (s.gpr .rcx).toNat
abbrev Ad : Addr := s.gpr .r8
abbrev AL : BitVec 64 := s.gpr .r9
abbrev Src : Addr := stackArg s 0
abbrev Cnt : Nat := (stackArg s 1).toNat
abbrev Dst : Addr := stackArg s 2
abbrev L : Nat := (stackArg s 3).toNat
abbrev Tg : Addr := stackArg s 4
abbrev W : Addr := stackArg s 5
abbrev SP : Addr := s.gpr .rsp
/-- The streaming state, in `work`. -/
abbrev St : Addr := W s + BitVec.ofNat 64 104

abbrev nR : Region := ⟨Nn s, NL s⟩
abbrev aR : Region := ⟨Ad s, (AL s).toNat⟩
/-- The descriptors. -/
abbrev dsR : Region := ⟨Src s, Cnt s * 16⟩
/-- The slices they list. -/
abbrev lsR : List Region := Sig.listed 64 s.mem .u8 (Src s) (Cnt s)
/-- The stack arguments. -/
abbrev argR : Region := ⟨SP s + BitVec.ofNat 64 8, 48⟩
abbrev dR : Region := ⟨Dst s, L s⟩
abbrev tgR : Region := ⟨Tg s, 16⟩
abbrev wkR : Region := ⟨W s, 184⟩
abbrev stR : Region := ⟨St s, 80⟩
/-- The slots kept. -/
abbrev kpR : Region := ⟨W s, 104⟩
/-- What the code writes: the output, the tag and `work`. -/
abbrev wR : List Region := [dR s, tgR s, wkR s]
/-- The stack the calls use. -/
abbrev tR : Region := below (SP s) 4888

/-- The bytes of the first `i` slices, and their number. -/
abbrev pt (i : Nat) : List Byte := gathered 64 s.mem (Src s) i
abbrev gl (i : Nat) : Nat := gatheredLen 64 s.mem (Src s) i

end

/-- The key context, of kind `M`. -/
abbrev kR (M : CtxMode) (s : State) : Region := ⟨K s, M.len⟩

/-- `sealGatherPreM`, by name. -/
structure SG (M : CtxMode) (s : State) : Prop where
  rd : s.rd = [kR M s, nR s, aR s, dsR s] ++ lsR s ++ [argR s]
  wr : s.wr = wR s
  k_d : (kR M s).Disjoint (dR s)
  k_t : (kR M s).Disjoint (tgR s)
  k_w : (kR M s).Disjoint (wkR s)
  n_d : (nR s).Disjoint (dR s)
  n_t : (nR s).Disjoint (tgR s)
  n_w : (nR s).Disjoint (wkR s)
  a_d : (aR s).Disjoint (dR s)
  a_t : (aR s).Disjoint (tgR s)
  a_w : (aR s).Disjoint (wkR s)
  ds_d : (dsR s).Disjoint (dR s)
  ds_t : (dsR s).Disjoint (tgR s)
  ds_w : (dsR s).Disjoint (wkR s)
  ls : ∀ r ∈ lsR s, r.Disjoint (dR s) ∧ r.Disjoint (tgR s) ∧ r.Disjoint (wkR s)
  d_t : (dR s).Disjoint (tgR s)
  d_w : (dR s).Disjoint (wkR s)
  t_w : (tgR s).Disjoint (wkR s)
  d_a : (dR s).Disjoint (argR s)
  t_a : (tgR s).Disjoint (argR s)
  w_a : (wkR s).Disjoint (argR s)
  r_d : (⟨SP s, 8⟩ : Region).Disjoint (dR s)
  r_t : (⟨SP s, 8⟩ : Region).Disjoint (tgR s)
  r_w : (⟨SP s, 8⟩ : Region).Disjoint (wkR s)
  b_k : (tR s).Disjoint (kR M s)
  b_n : (tR s).Disjoint (nR s)
  b_a : (tR s).Disjoint (aR s)
  b_ds : (tR s).Disjoint (dsR s)
  b_ls : ∀ r ∈ lsR s, (tR s).Disjoint r
  b_d : (tR s).Disjoint (dR s)
  b_t : (tR s).Disjoint (tgR s)
  b_w : (tR s).Disjoint (wkR s)
  w_k : (K s).toNat + M.len ≤ 2 ^ 64
  w_n : (Nn s).toNat + NL s ≤ 2 ^ 64
  w_ad : (Ad s).toNat + (AL s).toNat ≤ 2 ^ 64
  w_ds : (Src s).toNat + Cnt s * 16 ≤ 2 ^ 64
  w_ls : ∀ r ∈ lsR s, r.base.toNat + r.len ≤ 2 ^ 64
  w_d : (Dst s).toNat + L s ≤ 2 ^ 64
  w_t : (Tg s).toNat + 16 ≤ 2 ^ 64
  w_w : (W s).toNat + 184 ≤ 2 ^ 64
  w_sp : 4888 ≤ (SP s).toNat
  w_sp' : (SP s).toNat + 56 ≤ 2 ^ 64
  rounds : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14
  glen : gl s (Cnt s) = L s
  ok : M.ok s.mem (K s)

theorem SG.ofM {M : CtxMode} {s : State} (h : Proof.AesGcm.sealGatherPreM M s) : SG M s := by
  simp only [Proof.AesGcm.sealGatherPreM, Proof.AesGcm.args, Proof.AesGcm.arg, Proof.AesGcm.ret,
    Proof.AesGcm.stkG, Proof.AesGcm.slicesG, Proof.AesGcm.rounds] at h
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂,
    a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂, a₃₃, a₃₄, a₃₅, a₃₆, a₃₇, a₃₈, a₃₉, a₄₀, a₄₁, a₄₂, a₄₃, a₄₄,
    a₄₅⟩ := h
  rw [hA] at a₁ a₁₉ a₂₀ a₂₁
  exact ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂,
    a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂, a₃₃, a₃₄, a₃₅, a₃₆, a₃₇, a₃₈, a₃₉, a₄₀, a₄₁, a₄₂, a₄₃,
    a₄₄, a₄₅⟩

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## The slots kept -/

/-- The slots of `work` at `W`: the arguments, the descriptor of slice `i`,
the `Cnt - i` slices left and the bytes of the first `i`, the length `ap`
of the additional data so far, and 16 zero bytes. -/
structure Kept (s : State) (ap : BitVec 64) (i : Nat) (m : Mem) : Prop where
  ctx : m.readW (W s + BitVec.ofNat 64 0) 64 = K s
  rounds : m.readW (W s + BitVec.ofNat 64 8) 64 = s.gpr .rsi
  aad : m.readW (W s + BitVec.ofNat 64 16) 64 = Ad s
  alen : m.readW (W s + BitVec.ofNat 64 24) 64 = AL s
  dst : m.readW (W s + BitVec.ofNat 64 32) 64 = Dst s
  len : m.readW (W s + BitVec.ofNat 64 40) 64 = stackArg s 3
  tag : m.readW (W s + BitVec.ofNat 64 48) 64 = Tg s
  desc : m.readW (W s + BitVec.ofNat 64 56) 64 = Src s + BitVec.ofNat 64 (16 * i)
  left : m.readW (W s + BitVec.ofNat 64 64) 64 = BitVec.ofNat 64 (Cnt s - i)
  off : m.readW (W s + BitVec.ofNat 64 72) 64 = BitVec.ofNat 64 (gl s i)
  alenP : m.readW (W s + BitVec.ofNat 64 80) 64 = ap
  z₀ : m.readW (W s + BitVec.ofNat 64 88) 64 = 0
  z₁ : m.readW (W s + BitVec.ofNat 64 96) 64 = 0

/-- A word written at an offset of `p` leaves the words at the others. -/
theorem readW_writeW_off {m : Mem} {p : Addr} {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (p + BitVec.ofNat 64 d) v).readW (p + BitVec.ofNat 64 e) 64 = m.readW (p + BitVec.ofNat 64 e) 64 :=
  Mem.readW_writeW_sep (Offset.sep p (d := e) (n := 8) (e := d) (k := 8) (h.elim .inr .inl) he hd) (by decide)

theorem Kept.frame {s : State} {ap : BitVec 64} {i : Nat} {m m' : Mem} (h : Kept s ap i m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (kpR s).Disjoint r) :
    Kept s ap i m' := by
  have k : ∀ d, d + 8 ≤ 104 → m'.readW (W s + BitVec.ofNat 64 d) 64 = m.readW (W s + BitVec.ofNat 64 d) 64 :=
    fun d hd' => hf.readW (Offset.contains_base _ hd' (by omega)) hd (by decide)
  exact ⟨by rw [k 0 (by decide)]; exact h.ctx, by rw [k 8 (by decide)]; exact h.rounds,
    by rw [k 16 (by decide)]; exact h.aad, by rw [k 24 (by decide)]; exact h.alen,
    by rw [k 32 (by decide)]; exact h.dst, by rw [k 40 (by decide)]; exact h.len,
    by rw [k 48 (by decide)]; exact h.tag, by rw [k 56 (by decide)]; exact h.desc,
    by rw [k 64 (by decide)]; exact h.left, by rw [k 72 (by decide)]; exact h.off,
    by rw [k 80 (by decide)]; exact h.alenP, by rw [k 88 (by decide)]; exact h.z₀,
    by rw [k 96 (by decide)]; exact h.z₁⟩

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

theorem w_in {d k : Nat} (h : d + k ≤ 184) : InRegions s.wr (W s + BitVec.ofNat 64 d) k :=
  in_off (rs := s.wr) (by rw [hp.wr]; exact covers_of_mem (by simp)) h (by decide)

theorem w_in' {d k : Nat} (h : d + k ≤ 184) : InRegions (s.rd ++ s.wr) (W s + BitVec.ofNat 64 d) k :=
  in_left (w_in hp h)

/-- The stack argument `i` (of six) is readable. -/
theorem a_in {i : Nat} (hi : i < 6) : InRegions (s.rd ++ s.wr) (SP s + BitVec.ofNat 64 (8 * (i + 1))) 8 :=
  ⟨argR s, by rw [hp.rd]; simp, Offset.contains _ (by omega) (by omega) (by have := hp.w_sp'; omega)⟩

omit hp in
theorem kpR_sub : (kpR s).Sub (wkR s) := Region.sub_prefix (by decide)

omit hp in
theorem stR_sub : (stR s).Sub (wkR s) := Offset.sub_base _ (by decide)

omit hp in
theorem kpR_stR : (kpR s).Disjoint (stR s) := Offset.base_disjoint _ (by decide) (by decide)

/-- The stack arguments, through a frame of the regions written and the stack. -/
theorem keep_a {m m' : Mem} (hf : Frame (wR s ++ [tR s]) m m') {i : Nat} (hi : i < 6) :
    m'.readW (SP s + BitVec.ofNat 64 (8 * (i + 1))) 64 = m.readW (SP s + BitVec.ofNat 64 (8 * (i + 1))) 64 :=
  hf.readW (r := ⟨SP s + BitVec.ofNat 64 (8 * (i + 1)), 8⟩) (Region.contains_self _ _) (fun r hr => by
    have hs : Region.Sub ⟨SP s + BitVec.ofNat 64 (8 * (i + 1)), 8⟩ (argR s) := by
      have e : SP s + BitVec.ofNat 64 (8 * (i + 1)) = SP s + BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * i) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
      rw [e]; exact Offset.sub_base _ (by omega)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact hp.d_a.symm.sub_left hs
    · exact hp.t_a.symm.sub_left hs
    · exact hp.w_a.symm.sub_left hs
    · exact (Offset.disjoint_below (SP s) (n := 4888) (d := 8 * (i + 1)) (k := 8)
        (by have := hp.w_sp'; omega)).sub_left (fun _ h => h)) (by decide)

omit hp in
theorem arg_eq (i : Nat) : s.mem.readW (SP s + BitVec.ofNat 64 (8 * (i + 1))) 64 = stackArg s i := rfl

/-- The return address is apart from what the code writes. -/
theorem ret_disj : ∀ r ∈ wR s ++ [tR s], (⟨SP s, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl
  exacts [hp.r_d, hp.r_t, hp.r_w, Offset.base_disjoint_below _ (by have := hp.w_sp'; omega)]

/-- `work`, from the stack, through a frame of the regions written and the stack. -/
theorem keep_w {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) :
    m.readW (SP s + BitVec.ofNat 64 48) 64 = W s :=
  keep_a hp hf (i := 5) (by decide)

/-- The first entry block: `work` into `r11`, and the arguments in registers
kept, with `src` and `src_count`. -/
theorem entry1_ok : WP isa (.block entry1) s fun s₁ => s₁.gpr .r11 = W s ∧
    (∀ r, r ≠ .r11 → r ≠ .rax → r ≠ .r10 → s₁.gpr r = s.gpr r) ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 0) 64 = K s ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 8) 64 = s.gpr .rsi ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 16) 64 = Ad s ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 24) 64 = AL s ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 56) 64 = Src s ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 64) 64 = stackArg s 1 ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 80) 64 = AL s ∧
    Frame [kpR s] s.mem s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 104 → InRegions s.wr (W s + BitVec.ofNat 64 d) (64 / 8) := fun d h => w_in hp (by omega)
  have a₀ : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 := a_in hp (i := 0) (by decide)
  have a₁ : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 16) 8 := a_in hp (i := 1) (by decide)
  have a₅ : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 48) 8 := a_in hp (i := 5) (by decide)
  have e₀ : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s 0 := rfl
  have e₁ : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 16) 64 = stackArg s 1 := rfl
  have e₅ : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 48) 64 = W s := rfl
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [entry1, gCtx, gRounds, gAad, gAlen, gAlenP, gDesc, gLeft]
    xrun [a₀, a₁, a₅, e₀, e₁, e₅, w 0 (by decide), w 8 (by decide), w 16 (by decide), w 24 (by decide),
      w 80 (by decide), w 56 (by decide), w 64 (by decide)],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · intro r hr hr' hr''; simp [gpr_setReg, hr, hr', hr'']
  all_goals try simp (disch := decide) only [gpr_setReg, ite_true, reduceCtorEq, ↓reduceIte,
    Mem.readW_writeW_self64, readW_writeW_off]
  · have c : ∀ d, d + 8 ≤ 104 → (kpR s).Contains (W s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₂ => Offset.contains_base _ h₂ (by omega)
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 8 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 16 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 24 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 80 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 56 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 64 (by decide))

omit hp in
theorem gl_zero : gl s 0 = 0 := by simp [gl, gatheredLen, Sig.listed]

/-- The second entry block: `dst`, `len` and `tag` kept, nothing done, the
zeros, and the arguments of `vg_aes_gcm_stream_init(ctx, nonce, nonce_len,
state)`. -/
theorem entry2_ok {s₁ : State} (h11 : s₁.gpr .r11 = W s)
    (hg : ∀ r, r ≠ .r11 → r ≠ .rax → r ≠ .r10 → s₁.gpr r = s.gpr r)
    (c₀ : s₁.mem.readW (W s + BitVec.ofNat 64 0) 64 = K s)
    (c₁ : s₁.mem.readW (W s + BitVec.ofNat 64 8) 64 = s.gpr .rsi)
    (c₂ : s₁.mem.readW (W s + BitVec.ofNat 64 16) 64 = Ad s)
    (c₃ : s₁.mem.readW (W s + BitVec.ofNat 64 24) 64 = AL s)
    (c₇ : s₁.mem.readW (W s + BitVec.ofNat 64 56) 64 = Src s)
    (c₈ : s₁.mem.readW (W s + BitVec.ofNat 64 64) 64 = stackArg s 1)
    (c₁₀ : s₁.mem.readW (W s + BitVec.ofNat 64 80) 64 = AL s)
    (hf : Frame [kpR s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    WP isa (.block entry2) s₁ fun s₂ => Kept s (AL s) 0 s₂.mem ∧ Frame [kpR s] s.mem s₂.mem ∧
      s₂.gpr .rdi = K s ∧ s₂.gpr .rsi = Nn s ∧ s₂.gpr .rdx = s.gpr .rcx ∧ s₂.gpr .rcx = St s ∧
      s₂.gpr .r11 = W s ∧ s₂.gpr .rsp = SP s ∧ (∀ r ∈ calleeSaved, s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 104 → InRegions s₁.wr (W s + BitVec.ofNat 64 d) (64 / 8) := fun d h => by
    rw [hwr]; exact w_in hp (by omega)
  have hsp : s₁.gpr .rsp = SP s := hg _ (by decide) (by decide) (by decide)
  have aIn : ∀ i, i < 6 → InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1))) 8 :=
    fun i hi => by rw [hrd, hwr, hsp]; exact a_in hp hi
  have aEq : ∀ i, i < 6 → s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1))) 64 = stackArg s i :=
    fun i hi => by
      rw [hsp]
      refine (hf.readW (r := ⟨SP s + BitVec.ofNat 64 (8 * (i + 1)), 8⟩) (Region.contains_self _ _)
        (fun r hr => ?_) (by decide)).trans (arg_eq i)
      simp only [List.mem_singleton] at hr; subst hr
      have e : SP s + BitVec.ofNat 64 (8 * (i + 1)) = SP s + BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * i) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
      exact (hp.w_a.symm.sub_left (by rw [e]; exact Offset.sub_base _ (by omega))).sub_right kpR_sub
  have a₂ := aIn 2 (by decide)
  have a₃ := aIn 3 (by decide)
  have a₄ := aIn 4 (by decide)
  have e₂ := aEq 2 (by decide)
  have e₃ := aEq 3 (by decide)
  have e₄ := aEq 4 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at a₂ a₃ a₄ e₂ e₃ e₄
  have hz : BitVec.setWidth 64 (BitVec.ofNat 32 0) = BitVec.ofNat 64 0 := by decide
  have i104 := imm_eq (n := 104) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [entry2, gDst, gLen, gTag, gOff, gZero, gState, imm]
    xrun [a₂, a₃, a₄, e₂, e₃, e₄, h11, hz, i104, w 32 (by decide), w 40 (by decide), w 48 (by decide),
      w 72 (by decide), w 88 (by decide), w 96 (by decide)],
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp (disch := decide) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, ite_true,
    reduceCtorEq, ↓reduceIte, Mem.readW_writeW_self64, readW_writeW_off, c₀, c₁, c₂, c₃, c₇, c₈, c₁₀]
  · simp
  · rw [Nat.sub_zero]; exact (ofNat_toNat _).symm
  · rw [gl_zero]
  · rfl
  · rfl
  · have c : ∀ d, d + 8 ≤ 104 → (kpR s).Contains (W s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₂ => Offset.contains_base _ h₂ (by omega)
    exact (((((((hf.writeW (List.mem_singleton_self _) _ (c 32 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 40 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 48 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 72 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 88 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 96 (by decide))))
  · exact hg _ (by decide) (by decide) (by decide)
  · exact hg _ (by decide) (by decide) (by decide)
  · exact hg _ (by decide) (by decide) (by decide)
  · exact h11
  · exact hsp
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ↓reduceIte] <;>
      exact hg _ (by decide) (by decide) (by decide)
  all_goals simp [rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg, hrd, hwr]

end

end VG.Proof.AesGcm.X86_64.Gather
