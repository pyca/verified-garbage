import VerifiedGarbage.Proof.Sha512.X86.Sse
import VerifiedGarbage.Proof.Sha512.X86.Rounds

/-!
# SHA-512 on x86 (32-bit) with SSE2: the rounds

The invariant of the rounds (`RInv`): the working variables but `a` and `e`
in their slots, `a`, `e` and `b ⊕ c` in the registers of their roles, and the
message-schedule window. `round_ok` and `schedule_ok` instantiate the
symbolic runs of `Sse.lean` for round `t`.
-/

namespace VG.Proof.Sha512.X86

open VG VG.X86 VG.Impl.Sha512.X86
open VG.Spec.Sha512 (HashValue Word Block W K)
open VG.Proof.Sha256.X86.Stream (contains_addr addr_sep)
open VG.Proof.Sha512.Word64 (hi_append_lo)

/-! ## Memory -/

theorem readW64_write_ne (m : Mem) {b : BitVec 32} {o o' : Nat} (v : BitVec 64)
    (h : b.toNat + o + 8 ≤ 2 ^ 32) (h' : b.toNat + o' + 8 ≤ 2 ^ 32) (hs : o + 8 ≤ o' ∨ o' + 8 ≤ o) :
    (m.writeW (addr b o) v).readW (addr b o') 64 = m.readW (addr b o') 64 :=
  Mem.readW_writeW_sep (addr_sep h' h hs.symm) (by decide)

/-- `rd64`, the word as two halves, is the 64-bit word. -/
theorem rd64_eq_readW (m : Mem) {b : BitVec 32} {o : Nat} (h : b.toNat + o + 8 ≤ 2 ^ 32) :
    rd64 m b o = m.readW (addr b o) 64 := by
  rw [rd64, Word64.readW64, addr_eq (x := b) (k := o + 4) (by omega), addr_eq (x := b) (k := o) (by omega),
    ← Offset.add_ofNat_add_ofNat]
  rfl

/-! ## Offsets and registers -/

theorem vOff_lt (t k : Nat) : vOff t k + 8 ≤ 64 := by simp only [vOff]; omega

theorem wOff_lt (j : Nat) : wOff j + 8 ≤ 192 := by simp only [wOff]; omega

theorem vw_sep (t k j : Nat) : vOff t k + 8 ≤ wOff j := by simp only [vOff, wOff]; omega

theorem vOff_sep (t : Nat) {i j : Nat} (hi : i < 8) (hj : j < 8) (h : i ≠ j) :
    vOff t i + 8 ≤ vOff t j ∨ vOff t j + 8 ≤ vOff t i := by
  simp only [vOff]; omega

theorem vOff_succ (t k : Nat) (hk : k < 7) : vOff (t + 1) (k + 1) = vOff t k := by
  simp only [vOff]; omega

theorem wOff_sep {i j : Nat} (h : i % 16 ≠ j % 16) : wOff i + 8 ≤ wOff j ∨ wOff j + 8 ≤ wOff i := by
  simp only [wOff]; omega

theorem xr_mod (t k : Nat) : xr t k = xr (t % 2) k := by simp only [xr, Nat.mod_mod]

theorem xr_nodup (t : Nat) : [xr t 0, xr t 1, xr t 2, xr t 3, xr t 4, xr t 5, X, Y].Nodup := by
  have key : ∀ p < 2, [xr p 0, xr p 1, xr p 2, xr p 3, xr p 4, xr p 5, X, Y].Nodup := by decide
  simp only [xr_mod t]
  exact key _ (Nat.mod_lt _ (by decide))

theorem xr_nodup_sched (t : Nat) : [xr t 3, xr t 4, X, Y].Nodup := by
  have key : ∀ p < 2, [xr p 3, xr p 4, X, Y].Nodup := by decide
  simp only [xr_mod t]
  exact key _ (Nat.mod_lt _ (by decide))

theorem xr_succ (t k : Nat) (hk : k < 3) : xr (t + 1) k = xr t (k + 3) := by
  have key : ∀ p < 2, ∀ k < 3, xr (p + 1) k = xr p (k + 3) := by decide
  rw [xr_mod t, xr_mod (t + 1), show (t + 1) % 2 = (t % 2 + 1) % 2 by omega, ← xr_mod]
  exact key _ (Nat.mod_lt _ (by decide)) k hk

/-- The registers of roles 0–2 are none of the schedule's temporaries. -/
theorem xr_sched_ne (t k : Nat) (hk : k < 3) :
    xr t k ≠ xr t 3 ∧ xr t k ≠ xr t 4 ∧ xr t k ≠ X ∧ xr t k ≠ Y := by
  have key : ∀ p < 2, ∀ k < 3, xr p k ≠ xr p 3 ∧ xr p k ≠ xr p 4 ∧ xr p k ≠ X ∧ xr p k ≠ Y := by decide
  rw [xr_mod t k, xr_mod t 3, xr_mod t 4]
  exact key _ (Nat.mod_lt _ (by decide)) k hk

/-! ## The invariant -/

/-- The part of the scratch region the rounds write. -/
abbrev workR (scr : BitVec 32) : Region := ⟨scr.setWidth 64, 192⟩

/-- Where the scratch buffer is: at `scr` (in `esi`), writable. -/
structure Ctx (scr : BitVec 32) (s : State) : Prop where
  esi : s.gpr .esi = scr
  fit : scr.toNat + 224 ≤ 2 ^ 32
  mem : ⟨scr.setWidth 64, 224⟩ ∈ s.wr

theorem Ctx.out {scr : BitVec 32} {s : State} (c : Ctx scr s) {o : Nat} (ho : o + 8 ≤ 224) :
    InRegions s.wr (addr (s.gpr .esi) o) 8 :=
  ⟨_, c.mem, by rw [c.esi]; exact contains_addr ho (by decide) c.fit⟩

theorem Ctx.inp {scr : BitVec 32} {s : State} (c : Ctx scr s) {o : Nat} (ho : o + 8 ≤ 224) :
    InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) o) 8 :=
  mem_rd (c.out ho)

/-- What holds between rounds, before round `t`, from `s₀`, with the
message-schedule window holding the words `Wⱼ` for `u - 16 ≤ j < max u 16`. -/
structure RInv (scr : BitVec 32) (H : HashValue) (M : Block) (s₀ : State) (u t : Nat) (s : State) :
    Prop where
  vars : ∀ k (hk : k < 8), k ≠ 0 → k ≠ 4 → s.mem.readW (addr scr (vOff t k)) 64 = (Spec.Sha512.rounds H M t)[k]
  xa : qword (s.xmm (xr t 0)) 0 = (Spec.Sha512.rounds H M t)[0]
  xe : qword (s.xmm (xr t 1)) 0 = (Spec.Sha512.rounds H M t)[4]
  xbc : qword (s.xmm (xr t 2)) 0 = (Spec.Sha512.rounds H M t)[1] ^^^ (Spec.Sha512.rounds H M t)[2]
  win : ∀ j, j < max u 16 → u ≤ j + 16 → s.mem.readW (addr scr (wOff j)) 64 = W M j
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [workR scr] s₀.mem s.mem

theorem Ctx.of_rinv {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {u t : Nat}
    (c : Ctx scr s₀) (hI : RInv scr H M s₀ u t s) : Ctx scr s :=
  ⟨(hI.gpr _ (by decide) (by decide) (by decide)).trans c.esi, c.fit, hI.wr ▸ c.mem⟩

theorem frame_writeW {scr : BitVec 32} {m m' : Mem} (h : Frame [workR scr] m m') (hfit : scr.toNat + 224 ≤ 2 ^ 32)
    {o : Nat} (ho : o + 8 ≤ 192) (v : BitVec 64) : Frame [workR scr] m (m'.writeW (addr scr o) v) :=
  h.writeW (by simp) v (contains_addr ho (by decide) (by omega))

/-! ## A round -/

theorem round_word (v : HashValue) (k w : Word) :
    t1Of v[7] (Impl.Sha512.X86.hi k ++ Impl.Sha512.X86.lo k) w v[4] v[5] v[6] =
      v[7] + Spec.Sha512.bsig1 v[4] + Spec.Sha512.ch v[4] v[5] v[6] + k + w := by
  rw [t1Of, show Impl.Sha512.X86.hi k ++ Impl.Sha512.X86.lo k = k from hi_append_lo k, bsig1_chain,
    ← ch_eq]
  simp only [BitVec.add_assoc, BitVec.add_comm, add_left_comm]

theorem round_ok {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {t : Nat}
    (c : Ctx scr s) (hI : RInv scr H M s₀ (t + 1) t s) :
    WP isa (.block (round t)) s (RInv scr H M s₀ (t + 1) (t + 1)) := by
  set v := Spec.Sha512.rounds H M t with hv
  have hw : s.mem.readW (addr scr (wOff t)) 64 = W M t := hI.win t (by omega) (by omega)
  have fit := c.fit
  have vl := vOff_lt t
  refine WP.mono (roundW_ok _ _ _ _ _ _ _ _ (K t) _ _ _ _ _ _ (xr_nodup t) s
    (c.inp (by have := vl 1; omega)) (c.inp (by have := vl 3; omega)) (c.inp (by have := vl 5; omega))
    (c.inp (by have := vl 6; omega)) (c.inp (by have := vl 7; omega)) (c.inp (by have := wOff_lt t; omega))
    (c.out (by have := vl 0; omega)) (c.out (by have := vl 4; omega))) fun s' h => ?_
  obtain ⟨hT, hNE, hAB, hx, hg, hm, hrd, hwr⟩ := h
  have h1 := hI.vars 1 (by decide) (by decide) (by decide)
  have h3 := hI.vars 3 (by decide) (by decide) (by decide)
  have h5 := hI.vars 5 (by decide) (by decide) (by decide)
  have h6 := hI.vars 6 (by decide) (by decide) (by decide)
  have h7 := hI.vars 7 (by decide) (by decide) (by decide)
  simp only [c.esi, h1, h3, h5, h6, h7, hw, hI.xa, hI.xe, hI.xbc] at hT hNE hAB hm
  have hnext : Spec.Sha512.rounds H M (t + 1) = roundKW v (K t) (W M t) := by
    rw [rounds_succ, round_eq]
  have e04 := vOff_sep t (i := 0) (j := 4) (by decide) (by decide) (by decide)
  -- The new memory, at the offsets of the working variables and the window.
  have rm : ∀ o, o + 8 ≤ 192 → (vOff t 0 + 8 ≤ o ∨ o + 8 ≤ vOff t 0) →
      (vOff t 4 + 8 ≤ o ∨ o + 8 ≤ vOff t 4) → s'.mem.readW (addr scr o) 64 = s.mem.readW (addr scr o) 64 := fun o ho h0 h4 => by
    rw [hm, readW64_write_ne _ _ (by have := vl 4; omega) (by omega) h4,
      readW64_write_ne _ _ (by have := vl 0; omega) (by omega) h0]
  refine ⟨fun k hk h0 h4 => ?_, ?_, ?_, ?_, fun j hj hj' => ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
  · rw [hnext]
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    rw [vOff_succ t i (by omega)]
    by_cases hi0 : i = 0
    · subst hi0
      rw [hm, Mem.readW_writeW_sep (addr_sep (by have := vl 0; omega) (by have := vl 4; omega) e04)
        (by decide), Mem.readW_writeW_self64]
      rfl
    by_cases hi4 : i = 4
    · subst hi4
      rw [hm, Mem.readW_writeW_self64]
      rfl
    · rw [rm _ (by have := vl i; omega) (vOff_sep t (by decide) (by omega) (Ne.symm hi0))
        (vOff_sep t (by decide) (by omega) (Ne.symm hi4)), hI.vars i (by omega) hi0 hi4]
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 5 ∨ i = 6) with rfl | rfl | rfl | rfl <;> rfl
  · rw [xr_succ t 0 (by decide), hT, hnext, roundKW_0, round_word, bsig0_chain, BitVec.and_comm,
      maj_xor]
    simp only [hv, BitVec.add_assoc]
  · rw [xr_succ t 1 (by decide), hNE, hnext, roundKW_4, round_word]
  · rw [xr_succ t 2 (by decide), hAB, hnext, roundKW_1, roundKW_2]
  · rw [rm _ (wOff_lt j) (.inl (vw_sep t 0 j)) (.inl (vw_sep t 4 j))]
    exact hI.win j hj hj'
  · rw [hg r h1, hI.gpr r h1 h2 h3]
  · rw [hrd, hI.rd]
  · rw [hwr, hI.wr]
  · rw [hm]
    exact frame_writeW (frame_writeW hI.frame fit (by have := vl 0; omega) _) fit
      (by have := vl 4; omega) _

/-! ## A step of the message schedule -/

theorem schedule_ok {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {t : Nat}
    (c : Ctx scr s) (hI : RInv scr H M s₀ t t s) (h16 : 16 ≤ t) :
    WP isa (.block (schedule t)) s (RInv scr H M s₀ (t + 1) t) := by
  have fit := c.fit
  have e : ∀ i, 1 ≤ i → i ≤ 16 → s.mem.readW (addr scr (wOff (t + 16 - i))) 64 = W M (t - i) := fun i hi hi' => by
    rw [show wOff (t + 16 - i) = wOff (t - i) by simp only [wOff]; omega]
    exact hI.win _ (by omega) (by omega)
  have w' : ∀ j, wOff j + 8 ≤ 224 := fun j => by have := wOff_lt j; omega
  refine WP.mono (scheduleW_ok _ _ _ _ _ _ (xr_nodup_sched t) s (c.inp (w' _)) (c.inp (w' _))
    (c.inp (w' _)) (c.inp (w' _)) (c.out (w' _))) fun s' ⟨hx, hg, hm, hrd, hwr⟩ => ?_
  simp only [c.esi] at hm
  have e16 : s.mem.readW (addr scr (wOff t)) 64 = W M (t - 16) := by
    rw [← e 16 (by omega) (by omega), show t + 16 - 16 = t by omega]
  rw [show t + 14 = t + 16 - 2 by omega, show t + 9 = t + 16 - 7 by omega,
    show t + 1 = t + 16 - 15 by omega, e 2 (by omega) (by omega), e 7 (by omega) (by omega),
    e 15 (by omega) (by omega), e16, ssig1_chain, ssig0_chain, ← W_ge M h16] at hm
  have rm : ∀ o, o + 8 ≤ 224 → (wOff t + 8 ≤ o ∨ o + 8 ≤ wOff t) → s'.mem.readW (addr scr o) 64 = s.mem.readW (addr scr o) 64 :=
    fun o ho h => by rw [hm, readW64_write_ne _ _ (by have := w' t; omega) (by omega) h]
  have xk : ∀ k < 3, s'.xmm (xr t k) = s.xmm (xr t k) := fun k hk => by
    obtain ⟨n3, n4, nx, ny⟩ := xr_sched_ne t k hk
    exact hx _ n3 n4 nx ny
  refine ⟨fun k hk h0 h4 => ?_, by rw [xk 0 (by decide)]; exact hI.xa, by rw [xk 1 (by decide)]; exact hI.xe,
    by rw [xk 2 (by decide)]; exact hI.xbc, fun j hj hj' => ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
  · rw [rm _ (by have := vOff_lt t k; omega) (.inr (vw_sep t k t))]
    exact hI.vars k hk h0 h4
  · by_cases hjt : j = t
    · subst hjt; rw [hm, Mem.readW_writeW_self64]
    · rw [rm _ (w' j) (wOff_sep (by omega))]
      exact hI.win j (by omega) (by omega)
  · rw [hg, hI.gpr r h1 h2 h3]
  · rw [hrd, hI.rd]
  · rw [hwr, hI.wr]
  · rw [hm]; exact frame_writeW hI.frame fit (wOff_lt t) _

theorem step_ok {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {t : Nat}
    (c₀ : Ctx scr s₀) (hI : RInv scr H M s₀ t t s) :
    WP isa (.block (step t)) s (RInv scr H M s₀ (t + 1) (t + 1)) := by
  have c := c₀.of_rinv hI
  unfold step
  by_cases h16 : t < 16
  · simp only [h16, ↓reduceIte]
    exact round_ok c { hI with win := fun j hj hj' => hI.win j (by omega) (by omega) }
  · simp only [h16, ↓reduceIte]
    rw [WP.block_append_iff]
    exact WP.mono (schedule_ok c hI (by omega)) fun s' h => round_ok (c₀.of_rinv h) h

theorem rounds_ok {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State}
    (c₀ : Ctx scr s₀) (hI : RInv scr H M s₀ 0 0 s) :
    ∀ t, WP isa (rounds t) s (RInv scr H M s₀ t t) := by
  intro t
  induction t with
  | zero => exact WP.block_nil hI
  | succ t ih => exact WP.seq (WP.mono ih fun s' h => step_ok c₀ h)

end VG.Proof.Sha512.X86
