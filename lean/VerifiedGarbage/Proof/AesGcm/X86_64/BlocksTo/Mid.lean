import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Base
import VerifiedGarbage.Proof.Gcm.Split

/-!
# AES-GCM on whole blocks out of place, x86-64: after the first blocks

Untrusted: everything here is checked by Lean. `Mid s q k` holds once the
first `q` blocks of the plaintext are encrypted into the output and hashed,
with the arguments kept for the rest after `k` blocks: after the entry
(`mid_entry`, with `q = k = 0`), and after `rest` (`rest_ok`, `k = q`). The
plaintext is never written: every region written is apart from it
(`src_keep`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.BlocksTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo
open VG.Impl.AesGcm.X86_64.Blocks (argCtx argRounds argCtr argY argN)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

section
variable (s : State)

abbrev R : Nat := (s.gpr .rsi).toNat
abbrev ciph : Block → Block := ctxCiph s.mem (K s) (R s)
abbrev cb : Block := blockAt s.mem (C s)
abbrev hk : Block := ctxH s.mem (K s)
abbrev y₀ : Block := blockAt s.mem (Y s)
/-- Where the plaintext and the output left after `q` blocks start. -/
abbrev sq (q : Nat) : Addr := Src s + BitVec.ofNat 64 (16 * q)
abbrev dq (q : Nat) : Addr := Dst s + BitVec.ofNat 64 (16 * q)
/-- The ciphertext of the first `q` blocks. -/
abbrev ct (q : Nat) : List Block := ctr32 (ciph s) (cb s) (blocksAt s.mem (Src s) q)

end

/-- The first `q` blocks encrypted into the output and hashed, the arguments
kept for what is left after `k` blocks. -/
structure Mid (s : State) (q k : Nat) (st : State) : Prop where
  q_le : q ≤ n s
  rsp : st.gpr .rsp = SP s
  saved : ∀ r ∈ calleeSaved, st.gpr r = s.gpr r
  rd : st.rd = s.rd
  wr : st.wr = s.wr
  kept : Kept s k st.mem
  frame : Frame (wR s) s.mem st.mem
  data : blocksAt st.mem (Dst s) q = ct s q
  ctr : blockAt st.mem (C s) = Nat.repeat inc32 q (cb s)
  y : blockAt st.mem (Y s) = ghashFrom (hk s) (y₀ s) (ct s q)

section
variable {M : CtxMode} {s : State} (hp : BT M s)
include hp

/-- The slots of the arguments are apart from the other regions written. -/
theorem kR'_disj : ∀ r ∈ [cR s, yR s, dR s], (kR' s).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.c_s.sub_right (kR'_sub (s := s))).symm
  · exact (hp.y_s.sub_right (kR'_sub (s := s))).symm
  · exact (hp.d_s.sub_right (kR'_sub (s := s))).symm

/-- The plaintext is apart from everything written. -/
theorem src_wR : ∀ r ∈ wR s, (srcR s).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [hp.c_r.symm, hp.y_r.symm, hp.r_d, hp.r_s]

/-- The plaintext, through a frame of the regions written. -/
theorem src_keep {m m' : Mem} (hf : Frame (wR s) m m') {q k : Nat} (hqk : q + k ≤ n s) :
    blocksAt m' (sq s q) k = blocksAt m (sq s q) k :=
  blocksAt_frame hf (fun r hr => by
    rw [Nat.mul_comm]
    exact (src_wR hp r hr).sub_left (Offset.sub_base _ (by omega))) (by have := hp.w_r; omega)

/-- The key schedule, through a frame of the regions written. -/
theorem keep_sch {m m' : Mem} (hf : Frame (wR s) m m') :
    Spec.Aes.bytesAt m' (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt m (K s) (16 * (R s + 1)) := by
  have hRb : 16 * (R s + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> simp only [R, h] <;> decide
  exact bytesAt_frame hf (fun r hr => by
    have hs : Region.Sub ⟨K s, 16 * (R s + 1)⟩ (kR M s) := Region.sub_prefix (Nat.le_trans hRb M.ge)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.k_c.sub_left hs
    · exact hp.k_y.sub_left hs
    · exact hp.k_d.sub_left hs
    · exact hp.k_s.sub_left hs) (by have := hp.w_k; have := M.ge; omega)

/-- The hash subkey, through a frame of the regions written. -/
theorem keep_h {m m' : Mem} (hf : Frame (wR s) m m') :
    blockAt m' (K s + BitVec.ofNat 64 240) = blockAt m (K s + BitVec.ofNat 64 240) :=
  blockAt_frame hf (fun r hr => by
    have hs : Region.Sub ⟨K s + BitVec.ofNat 64 240, 16⟩ (kR M s) := Offset.sub_base _ (by have := M.ge; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.k_c.sub_left hs
    · exact hp.k_y.sub_left hs
    · exact hp.k_d.sub_left hs
    · exact hp.k_s.sub_left hs)

omit hp in
theorem Kept.frame {k : Nat} {m m' : Mem} (h : Kept s k m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (kR' s).Disjoint r) : Kept s k m' := by
  have e : ∀ d, d + 8 ≤ 56 → m'.readW (S s + BitVec.ofNat 64 d) 64 = m.readW (S s + BitVec.ofNat 64 d) 64 :=
    fun d h₁ => hf.readW (Offset.contains_base _ h₁ (by omega)) hd (by decide)
  have e0 : m'.readW (S s) 64 = m.readW (S s) 64 := by simpa using e 0 (by decide)
  exact ⟨by rw [e0]; exact h.ctx, by rw [e 8 (by decide)]; exact h.rounds,
    by rw [e 16 (by decide)]; exact h.ctr, by rw [e 24 (by decide)]; exact h.y,
    by rw [e 32 (by decide)]; exact h.src, by rw [e 40 (by decide)]; exact h.n,
    by rw [e 48 (by decide)]; exact h.dst⟩

omit hp in
/-- A frame of `scratch`'s slots keeps a block apart from them. -/
theorem block_kR' {m m' : Mem} (hf : Frame [kR' s] m m') {p : Addr} (hd : (⟨p, 16⟩ : Region).Disjoint (kR' s)) :
    blockAt m' p = blockAt m p :=
  blockAt_frame hf fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd

omit hp in
theorem frame_kR' {m m' : Mem} (hf : Frame [kR' s] m m') : Frame (wR s) m m' :=
  hf.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨sR s, by simp, kR'_sub⟩

theorem mid_entry {s₁ : State} (hsp : s₁.gpr .rsp = s.gpr .rsp)
    (hcs : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r)
    (hk : Kept s 0 s₁.mem) (hf : Frame [kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    Mid s 0 0 s₁ :=
  ⟨Nat.zero_le _, hsp, hcs, hrd, hwr, hk, frame_kR' hf, rfl,
    block_kR' hf (kR'_disj hp _ (by simp)).symm, block_kR' hf (kR'_disj hp _ (by simp)).symm⟩

/-- `Mid` through a frame of `scratch`'s slots that keeps the stack pointer
and the callee-saved registers. -/
theorem Mid.slots {q k k' : Nat} {st st' : State} (h : Mid s q k st)
    (hsp : st'.gpr .rsp = st.gpr .rsp) (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) (hk : Kept s k' st'.mem)
    (hf : Frame [kR' s] st.mem st'.mem) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) : Mid s q k' st' := by
  refine ⟨h.q_le, by rw [hsp, h.rsp], fun r hr => by rw [hcs r hr, h.saved r hr], hrd.trans h.rd,
    hwr.trans h.wr, hk, h.frame.trans (frame_kR' hf), ?_, ?_, ?_⟩
  · rw [← h.data]
    exact blocksAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [Nat.mul_comm]
      exact (kR'_disj hp (dR s) (by simp)).symm.sub_left (Region.sub_prefix (by have := h.q_le; omega)))
      (by have := hp.w_d; have := h.q_le; omega)
  · rw [← h.ctr]; exact block_kR' hf (kR'_disj hp _ (by simp)).symm
  · rw [← h.y]; exact block_kR' hf (kR'_disj hp _ (by simp)).symm

/-- `rest`: the arguments of the `n mod 16` blocks after the first
`16 ⌊n / 16⌋`. -/
theorem rest_ok {q : Nat} (hq : q = n s - n s % 16) {st : State} (h : Mid s q 0 st) :
    WP isa (.block rest) st (Mid s q q) := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have a₂ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 2) (by decide)
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s := by
    rw [h.rsp, show (24 : Nat) = 8 * (2 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  have r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 32) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₇ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 48) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have w₅ : InRegions st.wr (S s + BitVec.ofNat 64 32) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have w₆ : InRegions st.wr (S s + BitVec.ofNat 64 40) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have w₇ : InRegions st.wr (S s + BitVec.ofNat 64 48) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have kr := h.kept.src
  have kn := h.kept.n
  have kd := h.kept.dst
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.sub_zero] at kr kn kd
  have e15 := and15 (BitVec.ofNat 64 (n s))
  rw [toNat_ofNat_of_lt hn, imm_eq (by decide)] at e15
  have esub : BitVec.ofNat 64 (n s) - BitVec.ofNat 64 (n s % 16) = BitVec.ofNat 64 q := by
    rw [hq]; exact ofNat_sub (Nat.mod_le _ _) hn
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2112 → d + 8 ≤ 2112 →
      Mem.Sep (S s + BitVec.ofNat 64 a) (64 / 8) (S s + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep _ h (by omega) (by omega)
  have s₅₇ := sep 32 48 (by decide) (by decide) (by decide)
  have s₅₆ := sep 32 40 (by decide) (by decide) (by decide)
  have s₆₇ := sep 40 48 (by decide) (by decide) (by decide)
  have s₇₅ := sep 48 32 (by decide) (by decide) (by decide)
  have kp : ∀ d, d + 8 ≤ 32 → ∀ u v w : BitVec 64,
      (((st.mem.writeW (S s + BitVec.ofNat 64 32) u).writeW (S s + BitVec.ofNat 64 48) v).writeW
        (S s + BitVec.ofNat 64 40) w).readW (S s + BitVec.ofNat 64 d) 64 =
        st.mem.readW (S s + BitVec.ofNat 64 d) 64 := fun d h₁ u v w => by
    rw [Mem.readW_writeW_sep (sep d 40 (.inl (by omega)) (by omega) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 48 (.inl (by omega)) (by omega) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 32 (.inl (by omega)) (by omega) (by decide)) (by decide)]
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [rest, argSrc, argN, argDst]
    xrun [a₂, hS, r₅, r₆, r₇, w₅, w₆, w₇, kn, e15, esub, times16_val, kr, kd, s₅₇, s₅₆, s₆₇, s₇₅,
      Mem.readW_writeW_sep, Mem.readW_writeW_self64], ?_⟩
  refine h.slots hp (by simp [gpr_setReg, gpr_arithFlags]) (fun r hr => ?_) ?_ ?_ rfl rfl
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := kp 0 (by decide); simp only [BitVec.add_zero] at this; rw [this]; exact h.kept.ctx
    · rw [kp 8 (by decide)]; exact h.kept.rounds
    · rw [kp 16 (by decide)]; exact h.kept.ctr
    · rw [kp 24 (by decide)]; exact h.kept.y
    · rw [Mem.readW_writeW_sep (sep 32 40 (.inl (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (sep 32 48 (.inl (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64, BitVec.add_comm]
    · rw [Mem.readW_writeW_self64, hq]; congr 1; omega
    · rw [Mem.readW_writeW_sep (sep 48 40 (.inr (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64, BitVec.add_comm]
  · have c : ∀ d, d + 8 ≤ 56 → (kR' s).Contains (S s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ => Offset.contains_base _ h₁ (by omega)
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 32 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 48 (by decide))).writeW (List.mem_singleton_self _) _ (c 40 (by decide))

end

end VG.Proof.AesGcm.X86_64.BlocksTo
