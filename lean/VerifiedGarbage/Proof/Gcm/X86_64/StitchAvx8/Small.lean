module

import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.TailD
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemLoopOneD
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Tail

/-!
# The pipeline's loops on fewer blocks than it takes

With a prepared key context, `StitchAvx8.encRS` and `decRS` take fewer than 16
blocks, from 1 on, without the pipeline (`StitchAvx8.small`): from the state
the setup leaves (`Ready`), `ksTail` stores the keystream of the eight
counters it prepared at `scratch + 384`; from 9 blocks on, the next eight
counters are prepared (`prepTemplates_ok`), their keystream stored at
`scratch + 512`, and the powers `H'⁹` … `H'¹⁵` copied from the key context
below the setup's `H'⁸` … `H'` (`highs_ok`). From there (`KsDone`), the
blocks go through `StitchZH`'s loop as the blocks after the pipeline's do
(`Tail.lean`), with the keystream at `r11 + 768` once `r11` is moved down
384 bytes, and the powers `H'ⁿ` … `H'` at `scratch + 256 - 16 n`, for
powers whose products add up to `GHASH` (`SmallLaw`, which `Ok.lean`
proves).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (ksTail highs smallSetup small prepCounter prepOff tailEnd finish)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Spec.Gcm (Block inc32 blockAt ghashFrom)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq)
open VG.Proof.Aes.X86_64.AesNi (ea_at)
open VG.Proof.Gcm.X86_64.Pclmul (prod reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (poly)

/-- `H'ᵏ`, for `k` from 1 to 15: the setup's `P (8 - k)` up to `H'⁸`, and
the prepared key context's above it. -/
def smallPow (s₀ : State) (P : Nat → Block) (k : Nat) : Block :=
  if k ≤ 8 then P (8 - k) else s₀.mem.readW (kp s₀ + BitVec.ofNat 64 (prepOff k)) 128

/-- What the products of `r ≤ 15` blocks with the powers `smallPow` add up
to: `GHASH` over the blocks (`Ok.lean` proves it of the setup's powers). -/
def SmallLaw (s₀ : State) (P : Nat → Block) : Prop :=
  ∀ r, 1 ≤ r → r ≤ 15 → ∀ (X : Nat → Block) (y : Block),
    reduceB (StitchZH.accR X (fun j => smallPow s₀ P (r - j)) y r) = ghashFrom (hk s₀) y ((List.range r).map X)

/-! ## The powers above `H'⁸` -/

/-- One power: loaded from `rdi + a` into `xmm12`, stored to `r11 + b`. -/
theorem highPair_ok (t : State) (a b : Nat)
    (hin : InRegions (t.rd ++ t.wr) (t.gpr .rdi + BitVec.ofNat 64 a) 16)
    (hw : InRegions t.wr (t.gpr .r11 + BitVec.ofNat 64 b) 16) :
    WP isa (.block [.vmovdquLoad .l128 .xmm12 (at_ .rdi a), .vmovdquStore .l128 (at_ .r11 b) .xmm12]) t fun u =>
      u.mem = t.mem.writeW (t.gpr .r11 + BitVec.ofNat 64 b) (t.mem.readW (t.gpr .rdi + BitVec.ofNat 64 a) 128) ∧
      u.gpr = t.gpr ∧ (∀ r, r ≠ .xmm12 → u.lane r 0 = t.lane r 0) ∧ u.rd = t.rd ∧ u.wr = t.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.load128, State.store128_eq, ea_at,
    gpr_setV, mem_setV, rd_setV, wr_setV, hin, hw, Option.map_some,
    Option.some.injEq, exists_eq_left', BitVec.ofInt_natCast, State.setMem_mem, State.setMem_gpr,
    State.setMem_rd, State.setMem_wr, State.setMem_xmm, State.lane, xmm_setV, ↓reduceIte]
  exact ⟨trivial, trivial, fun r hr => by simp only [hr, ↓reduceIte], trivial, trivial⟩

/-- The first `n` of `highs`' seven pairs, with the working space at `p` and
the key context at `k`: the powers they copy, from the key context as it
was, which nothing they write overlaps. -/
theorem highsN_ok (s : State) (p k : Addr) (hr11 : s.gpr .r11 = p) (hrdi : s.gpr .rdi = k)
    (hin : ∀ i < 7, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 (prepOff (i + 9))) 16)
    (hw : ∀ i < 7, InRegions s.wr (p + BitVec.ofNat 64 (112 - 16 * i)) 16)
    (hd : ∀ i < 7, Region.Disjoint ⟨p + BitVec.ofNat 64 16, 112⟩ ⟨k + BitVec.ofNat 64 (prepOff (i + 9)), 16⟩)
    (hwrap : p.toNat + 1024 ≤ 2 ^ 64) :
    ∀ n ≤ 7, WP isa (.block ((List.range n).flatMap fun i =>
      [.vmovdquLoad .l128 .xmm12 (at_ .rdi (prepOff (i + 9))), .vmovdquStore .l128 (at_ .r11 (112 - 16 * i)) .xmm12]))
      s fun t =>
      (∀ i < n, t.mem.readW (p + BitVec.ofNat 64 (112 - 16 * i)) 128 =
        s.mem.readW (k + BitVec.ofNat 64 (prepOff (i + 9))) 128) ∧
      Frame [⟨p + BitVec.ofNat 64 16, 112⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm12 → t.lane r 0 = s.lane r 0) ∧ t.rd = s.rd ∧ t.wr = s.wr
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (by omega), Frame.refl _ _, rfl, fun _ _ => rfl, rfl, rfl⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (highsN_ok s p k hr11 hrdi hin hw hd hwrap n (by omega)) fun t ⟨v, f, g, l, rd, wr⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (highPair_ok t _ _ (by rw [g, rd, wr, hrdi]; exact hin n (by omega))
      (by rw [g, wr, hr11]; exact hw n (by omega))) fun u ⟨um, ug, ul, urd, uwr⟩ => ?_
    rw [g, hrdi, hr11] at um
    have hval : t.mem.readW (k + BitVec.ofNat 64 (prepOff (n + 9))) 128 =
        s.mem.readW (k + BitVec.ofNat 64 (prepOff (n + 9))) 128 := by
      refine f.readW (r := ⟨k + BitVec.ofNat 64 (prepOff (n + 9)), 16⟩) (Region.contains_self _ _)
        (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst r
      exact (hd n (by omega)).symm
    refine ⟨fun i hi => ?_, ?_, ug.trans g, fun r hr => (ul r hr).trans (l r hr), urd.trans rd, uwr.trans wr⟩
    · rw [um]
      by_cases he : i = n
      · subst he; rw [Mem.readW_writeW_self _ _ 16 _ (by decide), hval]
      · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)]
        exact v i (by omega)
    · rw [um]
      exact f.writeW (List.mem_singleton_self _) _ (Offset.contains p (by omega) (by omega) (by omega))

/-! ## The working space -/

/-- A write of `n` bytes at `scratch + d` keeps what the working space holds
outside them. -/
theorem scratch_read {s₀ : State} {d n : Nat} {m m' : Mem} (hf : Frame [⟨pp s₀ + BitVec.ofNat 64 d, n⟩] m m')
    (hdn : d + n ≤ 1024) (e k : Nat) (hd : e + k ≤ d ∨ d + n ≤ e) (hek : e + k ≤ 1024) :
    m'.readW (pp s₀ + BitVec.ofNat 64 e) (8 * k) = m.readW (pp s₀ + BitVec.ofNat 64 e) (8 * k) := by
  apply hf.readW (r := ⟨pp s₀ + BitVec.ofNat 64 e, k⟩)
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact Offset.disjoint (pp s₀) hd (by omega) (by omega)
  · omega

/-- A write to the working space outside what `Env` keeps there (the powers
at 128 … 255, the constants and saved values at 768 … 823) keeps `Env`. -/
theorem Env.scratchFrame {s₀ u v : State} {P : Nat → Block} {d n : Nat}
    (hd : d + n ≤ 128 ∨ (256 ≤ d ∧ d + n ≤ 768) ∨ 824 ≤ d) (hn : d + n ≤ 1024) (h : Env s₀ P u)
    (hf : Frame [⟨pp s₀ + BitVec.ofNat 64 d, n⟩] u.mem v.mem)
    (hg : v.gpr = u.gpr) (hrd : v.rd = u.rd) (hwr : v.wr = u.wr) : Env s₀ P v :=
  ⟨by rw [hg]; exact h.rdi, by rw [hg]; exact h.rsi, by rw [hg]; exact h.rcx,
    by rw [hg]; exact h.r11, by rw [hg]; exact h.r10,
    fun r h1 h2 h3 h4 h5 h6 => by rw [hg]; exact h.other r h1 h2 h3 h4 h5 h6,
    h.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨pR s₀, by simp, Offset.sub_base _ hn⟩),
    fun k hk => (scratch_read hf hn (128 + 16 * k) 16 (by omega) (by omega)).trans (h.powers k hk),
    (scratch_read hf hn 768 16 (by omega) (by omega)).trans h.mask,
    (scratch_read hf hn 784 16 (by omega) (by omega)).trans h.poly,
    (scratch_read hf hn 800 8 (by omega) (by omega)).trans h.rounds,
    (scratch_read hf hn 808 8 (by omega) (by omega)).trans h.data,
    (scratch_read hf hn 816 8 (by omega) (by omega)).trans h.saved,
    by rw [hrd]; exact h.rd, by rw [hwr]; exact h.wr⟩

/-! ## The keystream and the powers -/

/-- What the front of `small` leaves, from a state `s` after the setup: the
keystream of the blocks at `scratch + 384`, and their powers below `H'`. -/
structure KsDone (s₀ : State) (P : Nat → Block) (s u : State) : Prop where
  env : Env s₀ P u
  ks : ∀ j < nb s₀, blockAt u.mem (pp s₀ + BitVec.ofNat 64 (384 + 16 * j)) = ciph s₀ (Nat.repeat inc32 j (cb s₀))
  pw : ∀ k, 1 ≤ k → k ≤ nb s₀ → u.mem.readW (pp s₀ + BitVec.ofNat 64 (256 - 16 * k)) 128 = smallPow s₀ P k
  frame : Frame [pR s₀] s.mem u.mem
  gpr : ∀ q, q ≠ .rax → u.gpr q = s.gpr q
  y : u.lane .xmm2 0 = s.lane .xmm2 0

/-- `cmp r9, 9`. -/
theorem cmpNine_ok (s : State) :
    WP isa (.block [.alu .cmp .r9 (.imm 9)]) s fun s' =>
      s'.cf = some (decide ((s.gpr .r9).toNat < 9)) ∧ s'.gpr = s.gpr ∧ (∀ r l, s'.lane r l = s.lane r l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e9 : BitVec.signExtend 64 (9 : BitVec 32) = BitVec.ofNat 64 9 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    e9, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial, fun _ _ => rfl, trivial, trivial, trivial⟩

/-- The powers up to `H'⁸` are the setup's. -/
theorem Env.lowPow {s₀ s : State} {P : Nat → Block} (h : Env s₀ P s) {k : Nat} (h1 : 1 ≤ k) (h8 : k ≤ 8) :
    s.mem.readW (pp s₀ + BitVec.ofNat 64 (256 - 16 * k)) 128 = smallPow s₀ P k := by
  simp only [smallPow, h8, ↓reduceIte]
  rw [show 256 - 16 * k = 128 + 16 * (8 - k) by omega]
  exact h.powers _ (by omega)

/-- The front of `small`, up to its loop `R`: from the state the setup
leaves, `KsDone`. -/
theorem smallFront_ok {s₀ s : State} {lo : Nat} {P : Nat → Block} (hp : SPrePrepared s₀ lo)
    (hR : Ready s₀ P s) (hlt : nb s₀ < 16) {R : Prog isa} {Q : State → Prop}
    (hk : ∀ u, KsDone s₀ P s u → WP isa R u Q) :
    WP isa (.seq (ksTail (nr s₀) 384) (.seq (.block [.alu .cmp .r9 (.imm 9)])
      (.seq (.ite .b (.block []) (.seq (.block ((List.range 8).flatMap prepCounter))
        (.seq (ksTail (nr s₀) 512) (.block highs)))) R))) s Q := by
  have hb := hp.base
  have hwp := hb.wrap_p
  refine WP.seq (WP.mono (ksTail_ok hb (.inl rfl) hR.env hR.templates)
    fun s₁ ⟨hE₁, hks₁, hF₁, hg₁, hy₁, hrd₁, hwr₁⟩ => ?_)
  refine WP.seq (WP.mono (cmpNine_ok s₁) fun s₂ ⟨cf₂, g₂, l₂, m₂, rd₂, wr₂⟩ => ?_)
  have h9 : s₁.gpr .r9 = s₀.gpr .r9 := by rw [hg₁, hR.remaining]
  rw [h9] at cf₂
  have hE₂ : Env s₀ P s₂ := hE₁.move (fun r _ _ _ _ => by rw [g₂]) m₂ rd₂ wr₂
  have hF₂ : Frame [pR s₀] s.mem s₂.mem := by
    rw [m₂]
    exact hF₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨pR s₀, by simp, Offset.sub_base _ (by decide)⟩
  have hks₂ : ∀ j < 8, blockAt s₂.mem (pp s₀ + BitVec.ofNat 64 (384 + 16 * j)) =
      ciph s₀ (Nat.repeat inc32 j (cb s₀)) := fun j hj => by
    rw [m₂]; simpa only [Nat.zero_add] using hks₁ j hj
  refine WP.seq (WP.mono (Q := KsDone s₀ P s) ?_ fun u hu => hk u hu)
  refine WP.ite (decide (nb s₀ < 9)) (by simp only [eval, cf₂]) (fun h => ?_) (fun h => ?_)
  · -- Up to 8 blocks: the first keystream and the setup's powers.
    have h8 : nb s₀ < 9 := by simpa using h
    exact WP.block_nil ⟨hE₂, fun j hj => hks₂ j (by omega), fun k h1 hk => hE₂.lowPow h1 (by omega), hF₂,
      fun q _ => by rw [g₂, hg₁], by rw [l₂, hy₁]⟩
  -- From 9 blocks: the next eight counters, their keystream, and `H'⁹` … `H'¹⁵`.
  have h9' : 9 ≤ nb s₀ := by simp at h; omega
  have hv₂ : (s₂.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (0 + 8) := by
    rw [g₂, hg₁, hR.counter]; rfl
  have hT₂ : Templates s₀ 0 0 s₂.mem := m₂ ▸ hR.templates.frame hF₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 640, 128⟩ ⟨pp s₀ + BitVec.ofNat 64 384, 128⟩
    exact Offset.disjoint (pp s₀) (.inr (by omega)) (by omega) (by omega))
  have hprep : ((List.range 8).flatMap prepCounter) = (List.range 8).flatMap fun i => prepCounter (0 + i) := by
    simp only [Nat.zero_add]
  rw [hprep]
  refine WP.seq (WP.mono (prepTemplates_ok hb 0 0 8 (by omega) s₂ hE₂ hT₂ hv₂) fun s₃ ⟨hE₃, hT₃, hB₃, hC₃⟩ => ?_)
  have hT₃' : Templates s₀ 8 0 s₃.mem := Templates.next (c := 0) (by simpa only [Nat.zero_add] using hT₃)
  refine WP.seq (WP.mono (ksTail_ok hb (.inr (.inl rfl)) hE₃ hT₃')
    fun s₄ ⟨hE₄, hks₄, hF₄, hg₄, hy₄, hrd₄, hwr₄⟩ => ?_)
  refine WP.mono (highsN_ok s₄ (pp s₀) (kp s₀) hE₄.r11 hE₄.rdi (fun i hi => ?_) (fun i hi => ?_)
    (fun i hi => ?_) hwp 7 (by decide)) fun s₅ ⟨hv₅, hF₅, hg₅, hl₅, hrd₅, hwr₅⟩ => ?_
  · rw [hE₄.rd, hE₄.wr]
    exact in_sub hp.k_in (by simp only [prepOff]; split <;> omega)
  · rw [hE₄.wr]; exact in_sub hb.p_in (by omega)
  · exact (hp.p_k.sub_left (Offset.sub_base (pp s₀) (d := 16) (n := 112) (k := 1024) (by decide))).sub_right
      (Offset.sub_base (kp s₀) (by simp only [prepOff]; split <;> omega))
  have hE₅ : Env s₀ P s₅ := hE₄.scratchFrame (d := 16) (n := 112) (by omega) (by omega) hF₅ hg₅ hrd₅ hwr₅
  have hpR : ∀ {d n : Nat}, d + n ≤ 1024 → Region.Sub ⟨pp s₀ + BitVec.ofNat 64 d, n⟩ (pR s₀) :=
    fun h => Offset.sub_base _ h
  refine ⟨hE₅, fun j hj => ?_, fun k h1 hk => ?_, ?_, fun q hq => ?_, ?_⟩
  · -- The keystream.
    rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame hF₅ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact Offset.disjoint (pp s₀) (.inr (by omega)) (by omega) (by omega))]
    by_cases hj8 : j < 8
    · rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame hF₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          exact Offset.disjoint (pp s₀) (.inl (by omega)) (by omega) (by omega)),
        VG.Proof.Aes.X86_64.AesNi.blockAt_frame hC₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (384 + 16 * j), 16⟩ ⟨pp s₀ + BitVec.ofNat 64 640, 128⟩
          exact Offset.disjoint (pp s₀) (.inl (by omega)) (by omega) (by omega))]
      exact hks₂ j hj8
    · have := hks₄ (j - 8) (by omega)
      rw [ksAddr, show 512 + 16 * (j - 8) = 384 + 16 * j by omega, show 8 + (j - 8) = j by omega] at this
      exact this
  · -- The powers.
    by_cases hk8 : k ≤ 8
    · exact hE₅.lowPow h1 hk8
    · have hv := hv₅ (k - 9) (by omega)
      rw [show 112 - 16 * (k - 9) = 256 - 16 * k by omega, show k - 9 + 9 = k by omega] at hv
      rw [hv]
      simp only [smallPow, hk8, ↓reduceIte]
      refine hE₄.frame.readW (r := ⟨kp s₀ + BitVec.ofNat 64 (prepOff k), 16⟩) (Region.contains_self _ _)
        (fun r hr => ?_) (by decide)
      have hsub : Region.Sub ⟨kp s₀ + BitVec.ofNat 64 (prepOff k), 16⟩ (kPR s₀) :=
        Offset.sub_base _ (by simp only [prepOff]; split <;> omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.d_k.symm.sub_left hsub
      · exact hp.p_k.symm.sub_left hsub
  · -- Only the working space is written.
    have hS : ∀ (R : Region), Region.Sub R (pR s₀) → ∀ r ∈ [R], ∃ r' ∈ [pR s₀], Region.Sub r r' :=
      fun R hR r hr => ⟨pR s₀, List.mem_singleton_self _, by simp only [List.mem_singleton] at hr; subst r; exact hR⟩
    exact ((hF₂.trans (hC₃.sub (hS _ (hpR (d := 640) (n := 128) (by decide))))).trans
      (hF₄.sub (hS _ (hpR (by decide))))).trans (hF₅.sub (hS _ (hpR (by decide))))
  · rw [hg₅, hg₄, hB₃.gpr q hq, g₂, hg₁]
  · rw [hl₅ _ (by decide), hy₄, show State.lane s₃ .xmm2 0 = State.lane s₂ .xmm2 0 by
      simp only [State.lane, hB₃.xmm, hB₃.ymmHi], l₂, hy₁]

/-! ## Before and after the loop -/

theorem smallSetup_ok (s : State) {t : Nat} (ht : t ≤ 15) (h9 : s.gpr .r9 = BitVec.ofNat 64 t)
    (hin0 : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 768) 16)
    (hin1 : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 784) 16) :
    WP isa (.block smallSetup) s fun u =>
      u.gpr .r10 = BitVec.ofNat 64 (16 * 0) ∧
      u.gpr .rax = s.gpr .r11 + BitVec.ofNat 64 (256 - 16 * t) ∧
      u.gpr .r9 = BitVec.ofNat 64 (16 + t) ∧ u.gpr .r11 = s.gpr .r11 - BitVec.ofNat 64 384 ∧
      (u.gpr .r8).setWidth 32 = (s.gpr .r8).setWidth 32 + BitVec.ofNat 32 t ∧
      (∀ q, q ≠ .r10 → q ≠ .rax → q ≠ .r9 → q ≠ .r11 → q ≠ .r8 → u.gpr q = s.gpr q) ∧
      u.lane .xmm0 0 = s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 768) 128 ∧
      u.lane .xmm1 0 = s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 784) 128 ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → u.lane r 0 = s.lane r 0) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = BitVec.ofNat 64 16 := by decide
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have e384 : BitVec.signExtend 64 (384 : BitVec 32) = BitVec.ofNat 64 384 := by decide
  have sh : BitVec.ofNat 64 t <<< 4 = BitVec.ofNat 64 (16 * t) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show t < 2 ^ 64 by omega)]
    omega
  have hax : s.gpr .r11 + 256 - BitVec.ofNat 64 (16 * t) = s.gpr .r11 + BitVec.ofNat 64 (256 - 16 * t) := by
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl, Offset.ofNat_sub_ofNat (by omega)]
  have a9 : BitVec.ofNat 64 t + BitVec.ofNat 64 16 = BitVec.ofNat 64 (16 + t) := by
    rw [← BitVec.ofNat_add]; congr 1; omega
  have hin0' : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((768 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast]; exact hin0
  have hin1' : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((784 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast]; exact hin1
  have w32 : (BitVec.ofNat 64 t).setWidth 32 = BitVec.ofNat 32 t := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  apply WP.of_runBlock
  simp only [smallSetup, runBlock_cons, runStep_some, runBlock_nil, exec, isa, execAlu, execAlu32, execShift,
    show 1 ≤ 4 ∧ 4 ≤ 63 from by decide, and_self, readSrc, readSrc32,
    State.setReg32, State.load128, ea_at, gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg, mem_arithFlags,
    mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags, wr_setFlags,
    gpr_setV, mem_setV, rd_setV, wr_setV, e16, e256, e384, State.lane, xmm_setV,
    xmm_setReg, xmm_arithFlags, xmm_setFlags,
    setWidth_setWidth_32, w32, hax, reduceCtorEq, ↓reduceIte, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', h9, a9, sh, hin0', hin1']
  exact ⟨by decide, trivial, trivial, trivial, trivial,
    fun q h1 h2 h3 h4 h5 => by simp only [h1, h2, h3, h4, h5, ↓reduceIte],
    by rw [BitVec.ofInt_natCast], by rw [BitVec.ofInt_natCast],
    fun r h0 h1 => by simp only [h0, h1, ↓reduceIte], trivial⟩

/-- `add r11, 384`. -/
theorem add384_ok (s : State) :
    WP isa (.block [.alu .add .r11 (.imm 384)]) s fun s₁ =>
      s₁.gpr .r11 = s.gpr .r11 + BitVec.ofNat 64 384 ∧ (∀ q, q ≠ .r11 → s₁.gpr q = s.gpr q) ∧
      (∀ r l, s₁.lane r l = s.lane r l) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have e384 : BitVec.signExtend 64 (384 : BitVec 32) = BitVec.ofNat 64 384 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa, e384, gpr_setReg,
    gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
    ↓reduceIte, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩

/-- The keystream of block `j`, from `r11` moved down 384 bytes. -/
theorem ksAddr_small (p : Addr) (j : Nat) :
    p - BitVec.ofNat 64 384 + BitVec.ofNat 64 (768 + 16 * j) = p + BitVec.ofNat 64 (384 + 16 * j) := by
  rw [show 768 + 16 * j = 384 + (384 + 16 * j) by omega, ← Offset.add_add, BitVec.sub_add_cancel]

/-! ## Encryption -/

/-- Encryption of 1 to 15 blocks, from the state the setup leaves. -/
theorem smallE_ok {s₀ s : State} {lo : Nat} {P : Nat → Block} (hp : SPrePrepared s₀ lo)
    (hlaw : SmallLaw s₀ P) (hR : Ready s₀ P s) (h1 : 1 ≤ nb s₀) (hlt : nb s₀ < 16) :
    WP isa (small (nr s₀) false) s (EPost s₀) := by
  have hb := hp.base
  have hw := hb.wrap_d
  have hwp := hb.wrap_p
  simp only [small, Bool.false_eq_true, ↓reduceIte]
  refine smallFront_ok hp hR hlt fun u hu => ?_
  have h9u : u.gpr .r9 = BitVec.ofNat 64 (nb s₀) := by
    rw [hu.gpr _ (by decide), hR.remaining]
    simp only [nb, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hE := hu.env
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (smallSetup_ok u (t := nb s₀) (by omega) h9u
    (by rw [hE.rd, hE.wr, hE.r11]; exact in_rdwr (in_sub hb.p_in (by decide)))
    (by rw [hE.rd, hE.wr, hE.r11]; exact in_rdwr (in_sub hb.p_in (by decide))))
    fun s₃ ⟨a10, aax, a9, a11, a8, ag, a0, a1, al, am, ard, awr⟩ => ?_
  refine WP.mono (StitchAvx.zero_ok s₃) fun s₄ ⟨p₄, f₄⟩ => ?_
  have hd0 : bAddr s₀ 0 = dp s₀ := by simp only [bAddr, Nat.mul_zero, BitVec.add_zero]
  let E : StitchZH.REnv := ⟨nb s₀, .rdx, bAddr s₀ 0, bAddr s₀ 0, pp s₀ - BitVec.ofNat 64 384,
    pp s₀ + BitVec.ofNat 64 (256 - 16 * nb s₀), s₄.mem, s₄.gpr, s₄.rd, s₄.wr, s₄.lane .xmm2 0⟩
  have rd₄ : s₄.rd = s₀.rd := by rw [f₄.rd, ard, hE.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [f₄.wr, awr, hE.wr]
  have m₄ : s₄.mem = u.mem := by rw [f₄.mem, am]
  have rdx₄ : s₄.gpr .rdx = bAddr s₀ 0 := by
    rw [f₄.gpr, ag _ (by decide) (by decide) (by decide) (by decide) (by decide), hu.gpr _ (by decide),
      hR.cursor, hd0]
  have hEok : E.Ok :=
    { r1 := h1, r15 := show nb s₀ ≤ 15 by omega, gS := rdx₄, gA := rdx₄
      gP := by show s₄.gpr .r11 = _; rw [f₄.gpr, a11, hE.r11]
      gW := by show s₄.gpr .rax = _; rw [f₄.gpr, aax, hE.r11]
      src9 := show Reg.rdx ≠ .r9 by decide
      src10 := show Reg.rdx ≠ .r10 by decide
      inS := fun j (hj : j < nb s₀) => by
        show InRegions (s₄.rd ++ s₄.wr) (bAddr s₀ 0 + BitVec.ofNat 64 (16 * j)) 16
        rw [rd₄, wr₄, bAddr_add]
        exact in_rdwr (in_sub hb.d_in (by omega))
      inK := fun j (hj : j < nb s₀) => by
        show InRegions (s₄.rd ++ s₄.wr) (pp s₀ - BitVec.ofNat 64 384 + BitVec.ofNat 64 (768 + 16 * j)) 16
        rw [rd₄, wr₄, ksAddr_small]
        exact in_rdwr (in_sub hb.p_in (by omega))
      inD := fun j (hj : j < nb s₀) => by
        show InRegions s₄.wr (bAddr s₀ 0 + BitVec.ofNat 64 (16 * j)) 16
        rw [wr₄, bAddr_add]
        exact in_sub hb.d_in (by omega)
      inW := fun j (hj : j < nb s₀) => by
        show InRegions (s₄.rd ++ s₄.wr)
          (pp s₀ + BitVec.ofNat 64 (256 - 16 * nb s₀) + BitVec.ofNat 64 (16 * j)) 16
        rw [rd₄, wr₄, Offset.add_add]
        exact in_rdwr (in_sub hb.p_in (by omega))
      dS := fun j (hj : j < nb s₀) i hi => by
        show Region.Disjoint ⟨bAddr s₀ 0 + BitVec.ofNat 64 (16 * j), 16⟩ ⟨bAddr s₀ 0, 16 * i⟩
        rw [bAddr_add]
        exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
      dK := fun j (hj : j < nb s₀) => by
        show Region.Disjoint ⟨pp s₀ - BitVec.ofNat 64 384 + BitVec.ofNat 64 (768 + 16 * j), 16⟩
          ⟨bAddr s₀ 0, 16 * nb s₀⟩
        rw [ksAddr_small]
        exact (hb.d_p.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
      dW := fun j (hj : j < nb s₀) => by
        show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (256 - 16 * nb s₀) + BitVec.ofNat 64 (16 * j), 16⟩
          ⟨bAddr s₀ 0, 16 * nb s₀⟩
        rw [Offset.add_add]
        exact (hb.d_p.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega)) }
  have hI₄ : StitchZH.RInv E 0 s₄ :=
    { le := Nat.zero_le _
      r10 := by rw [f₄.gpr]; exact a10
      r9 := by show s₄.gpr .r9 = _; rw [f₄.gpr, a9, Nat.sub_zero]
      gpr := fun _ _ _ => rfl, rd := rfl, wr := rfl
      frame := Frame.refl _ _
      ct := fun j hj => absurd hj (Nat.not_lt_zero _)
      prod := p₄
      y := by simp only [↓reduceIte]; rfl
      m0 := by rw [f₄.lane _ (by decide) 0 (by decide), a0, hE.r11]; exact hE.mask
      m1 := by rw [f₄.lane _ (by decide) 0 (by decide), a1, hE.r11]; exact hE.poly }
  refine WP.seq (WP.mono (StitchZH.remLoop_ok hEok hI₄) fun s₅ hI₅ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (tailEndWith_ok s₅ hb.rounds hI₅.m1 (add384_ok s₅))
    fun s₆ ⟨y₆, r11₆, r10₆, g₆, m₆, rd₆, wr₆⟩ => ?_
  -- What the loop leaves.
  have g₆₄ : ∀ q, q ≠ .r11 → q ≠ .r10 → q ≠ .r9 → s₆.gpr q = s₄.gpr q := fun q h11 h10 h9' => by
    rw [g₆ q h11 h10, hI₅.gpr q h9' h10]
  have hR₀ : Region.Sub ⟨bAddr s₀ 0, 16 * nb s₀⟩ (dR s₀) :=
    Offset.sub_base (dp s₀) (d := 16 * 0) (n := 16 * nb s₀) (k := 16 * nb s₀) (by omega)
  have hF : Frame [⟨bAddr s₀ 0, 16 * nb s₀⟩] u.mem s₆.mem := by
    rw [m₆, ← m₄]; exact hI₅.frame
  have hE₆ : Env s₀ P s₆ := hE.dataWrite hb hR₀ hF (fun q h1 h2 h3 h4 => by
      by_cases h11 : q = .r11
      · subst h11
        rw [r11₆, hI₅.gpr _ (by decide) (by decide)]
        show s₄.gpr .r11 + _ = _
        rw [f₄.gpr, a11, BitVec.sub_add_cancel]
      by_cases h10 : q = .r10
      · subst h10
        rw [r10₆, hI₅.gpr _ (by decide) (by decide)]
        show s₄.gpr .rdi + _ = _
        rw [f₄.gpr, ag _ (by decide) (by decide) (by decide) (by decide) (by decide), hE.rdi, hE.r10]
      · rw [g₆₄ q h11 h10 h4, f₄.gpr, ag q h10 h1 h4 h11 h3])
    (by rw [rd₆, hI₅.rd]; exact f₄.rd.trans ard)
    (by rw [wr₆, hI₅.wr]; exact f₄.wr.trans awr)
  -- The blocks the loop read.
  have hsrc : ∀ k < nb s₀, blockAt u.mem (bAddr s₀ k) = blk s₀ k := fun k hk => by
    rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame hu.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact hb.d_p.sub_left (Offset.sub_base (dp s₀) (d := 16 * k) (n := 16) (k := 16 * nb s₀) (by omega))),
      ← srcBlk_false]
    exact hR.src hb k hk
  have hX : ∀ j < nb s₀, E.X j = ctb s₀ j := fun j hj => by
    show blockAt s₄.mem (bAddr s₀ 0 + BitVec.ofNat 64 (16 * j)) ^^^
      blockAt s₄.mem (pp s₀ - BitVec.ofNat 64 384 + BitVec.ofNat 64 (768 + 16 * j)) = _
    rw [m₄, bAddr_add, Nat.zero_add, hsrc j hj, ksAddr_small, hu.ks j hj]
  have hT : ∀ j < nb s₀, E.T j = smallPow s₀ P (nb s₀ - j) := fun j hj => by
    show s₄.mem.readW (pp s₀ + BitVec.ofNat 64 (256 - 16 * nb s₀) + BitVec.ofNat 64 (16 * j)) 128 = _
    rw [m₄, Offset.add_add, show 256 - 16 * nb s₀ + 16 * j = 256 - 16 * (nb s₀ - j) by omega]
    exact hu.pw _ (by omega) (by omega)
  refine WP.mono (finish_complete (ix := false) hb false hE₆
    (fun k hk => ⟨fun _ => ?_, fun hk' => absurd hk (by omega)⟩) ?_ ?_) fun t ht => ?_
  · have ct := hI₅.ct k hk
    rw [show E.aD k = bAddr s₀ k by
      show bAddr s₀ 0 + BitVec.ofNat 64 (16 * k) = _; rw [bAddr_add, Nat.zero_add], ← m₆] at ct
    rw [ct, hX k hk]
  · rw [g₆₄ _ (by decide) (by decide) (by decide), f₄.gpr, a8, hu.gpr _ (by decide), hR.counter,
      BitVec.add_assoc, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, BitVec.ofNat_add_ofNat,
      Nat.add_comm 8]
  · rw [y₆, hI₅.prod, StitchZH.accR_congr _ (nb s₀) hX hT, hlaw _ h1 (by omega)]
    have hy : E.y = y₀ s₀ := by
      show s₄.lane .xmm2 0 = _
      rw [f₄.lane _ (by decide) 0 (by decide), al _ (by decide) (by decide), hu.y, hR.hash]
    rw [hy]
    rfl
  · simpa only [Post, Bool.false_eq_true, ↓reduceIte] using ht.1

/-! ## Decryption -/

/-- Decryption of 1 to 15 blocks, from the state the setup leaves. -/
theorem smallD_ok {s₀ s : State} {lo : Nat} {P : Nat → Block} (hp : SPrePrepared s₀ lo)
    (hlaw : SmallLaw s₀ P) (hR : Ready s₀ P s) (h1 : 1 ≤ nb s₀) (hlt : nb s₀ < 16) :
    WP isa (small (nr s₀) true) s (DPost s₀) := by
  have hb := hp.base
  have hw := hb.wrap_d
  have hwp := hb.wrap_p
  simp only [small, ↓reduceIte]
  refine smallFront_ok hp hR hlt fun u hu => ?_
  have h9u : u.gpr .r9 = BitVec.ofNat 64 (nb s₀) := by
    rw [hu.gpr _ (by decide), hR.remaining]
    simp only [nb, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hE := hu.env
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (smallSetup_ok u (t := nb s₀) (by omega) h9u
    (by rw [hE.rd, hE.wr, hE.r11]; exact in_rdwr (in_sub hb.p_in (by decide)))
    (by rw [hE.rd, hE.wr, hE.r11]; exact in_rdwr (in_sub hb.p_in (by decide))))
    fun s₃ ⟨a10, aax, a9, a11, a8, ag, a0, a1, al, am, ard, awr⟩ => ?_
  refine WP.mono (StitchAvx.zero_ok s₃) fun s₄ ⟨p₄, f₄⟩ => ?_
  have hd0 : bAddr s₀ 0 = dp s₀ := by simp only [bAddr, Nat.mul_zero, BitVec.add_zero]
  let E : StitchZH.REnv := ⟨nb s₀, .rdx, bAddr s₀ 0, bAddr s₀ 0, pp s₀ - BitVec.ofNat 64 384,
    pp s₀ + BitVec.ofNat 64 (256 - 16 * nb s₀), s₄.mem, s₄.gpr, s₄.rd, s₄.wr, s₄.lane .xmm2 0⟩
  have rd₄ : s₄.rd = s₀.rd := by rw [f₄.rd, ard, hE.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [f₄.wr, awr, hE.wr]
  have m₄ : s₄.mem = u.mem := by rw [f₄.mem, am]
  have rdx₄ : s₄.gpr .rdx = bAddr s₀ 0 := by
    rw [f₄.gpr, ag _ (by decide) (by decide) (by decide) (by decide) (by decide), hu.gpr _ (by decide),
      hR.cursor, hd0]
  have hEok : E.Ok :=
    { r1 := h1, r15 := show nb s₀ ≤ 15 by omega, gS := rdx₄, gA := rdx₄
      gP := by show s₄.gpr .r11 = _; rw [f₄.gpr, a11, hE.r11]
      gW := by show s₄.gpr .rax = _; rw [f₄.gpr, aax, hE.r11]
      src9 := show Reg.rdx ≠ .r9 by decide
      src10 := show Reg.rdx ≠ .r10 by decide
      inS := fun j (hj : j < nb s₀) => by
        show InRegions (s₄.rd ++ s₄.wr) (bAddr s₀ 0 + BitVec.ofNat 64 (16 * j)) 16
        rw [rd₄, wr₄, bAddr_add]
        exact in_rdwr (in_sub hb.d_in (by omega))
      inK := fun j (hj : j < nb s₀) => by
        show InRegions (s₄.rd ++ s₄.wr) (pp s₀ - BitVec.ofNat 64 384 + BitVec.ofNat 64 (768 + 16 * j)) 16
        rw [rd₄, wr₄, ksAddr_small]
        exact in_rdwr (in_sub hb.p_in (by omega))
      inD := fun j (hj : j < nb s₀) => by
        show InRegions s₄.wr (bAddr s₀ 0 + BitVec.ofNat 64 (16 * j)) 16
        rw [wr₄, bAddr_add]
        exact in_sub hb.d_in (by omega)
      inW := fun j (hj : j < nb s₀) => by
        show InRegions (s₄.rd ++ s₄.wr)
          (pp s₀ + BitVec.ofNat 64 (256 - 16 * nb s₀) + BitVec.ofNat 64 (16 * j)) 16
        rw [rd₄, wr₄, Offset.add_add]
        exact in_rdwr (in_sub hb.p_in (by omega))
      dS := fun j (hj : j < nb s₀) i hi => by
        show Region.Disjoint ⟨bAddr s₀ 0 + BitVec.ofNat 64 (16 * j), 16⟩ ⟨bAddr s₀ 0, 16 * i⟩
        rw [bAddr_add]
        exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
      dK := fun j (hj : j < nb s₀) => by
        show Region.Disjoint ⟨pp s₀ - BitVec.ofNat 64 384 + BitVec.ofNat 64 (768 + 16 * j), 16⟩
          ⟨bAddr s₀ 0, 16 * nb s₀⟩
        rw [ksAddr_small]
        exact (hb.d_p.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
      dW := fun j (hj : j < nb s₀) => by
        show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (256 - 16 * nb s₀) + BitVec.ofNat 64 (16 * j), 16⟩
          ⟨bAddr s₀ 0, 16 * nb s₀⟩
        rw [Offset.add_add]
        exact (hb.d_p.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega)) }
  have hI₄ : StitchZH.RInvD E 0 s₄ :=
    { le := Nat.zero_le _
      r10 := by rw [f₄.gpr]; exact a10
      r9 := by show s₄.gpr .r9 = _; rw [f₄.gpr, a9, Nat.sub_zero]
      gpr := fun _ _ _ => rfl, rd := rfl, wr := rfl
      frame := Frame.refl _ _
      ct := fun j hj => absurd hj (Nat.not_lt_zero _)
      prod := p₄
      y := by simp only [↓reduceIte]; rfl
      m0 := by rw [f₄.lane _ (by decide) 0 (by decide), a0, hE.r11]; exact hE.mask
      m1 := by rw [f₄.lane _ (by decide) 0 (by decide), a1, hE.r11]; exact hE.poly }
  refine WP.seq (WP.mono (StitchZH.remLoopD1_ok hEok hI₄) fun s₅ hI₅ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (tailEndWith_ok s₅ hb.rounds hI₅.m1 (add384_ok s₅))
    fun s₆ ⟨y₆, r11₆, r10₆, g₆, m₆, rd₆, wr₆⟩ => ?_
  -- What the loop leaves.
  have g₆₄ : ∀ q, q ≠ .r11 → q ≠ .r10 → q ≠ .r9 → s₆.gpr q = s₄.gpr q := fun q h11 h10 h9' => by
    rw [g₆ q h11 h10, hI₅.gpr q h9' h10]
  have hR₀ : Region.Sub ⟨bAddr s₀ 0, 16 * nb s₀⟩ (dR s₀) :=
    Offset.sub_base (dp s₀) (d := 16 * 0) (n := 16 * nb s₀) (k := 16 * nb s₀) (by omega)
  have hF : Frame [⟨bAddr s₀ 0, 16 * nb s₀⟩] u.mem s₆.mem := by
    rw [m₆, ← m₄]; exact hI₅.frame
  have hE₆ : Env s₀ P s₆ := hE.dataWrite hb hR₀ hF (fun q h1 h2 h3 h4 => by
      by_cases h11 : q = .r11
      · subst h11
        rw [r11₆, hI₅.gpr _ (by decide) (by decide)]
        show s₄.gpr .r11 + _ = _
        rw [f₄.gpr, a11, BitVec.sub_add_cancel]
      by_cases h10 : q = .r10
      · subst h10
        rw [r10₆, hI₅.gpr _ (by decide) (by decide)]
        show s₄.gpr .rdi + _ = _
        rw [f₄.gpr, ag _ (by decide) (by decide) (by decide) (by decide) (by decide), hE.rdi, hE.r10]
      · rw [g₆₄ q h11 h10 h4, f₄.gpr, ag q h10 h1 h4 h11 h3])
    (by rw [rd₆, hI₅.rd]; exact f₄.rd.trans ard)
    (by rw [wr₆, hI₅.wr]; exact f₄.wr.trans awr)
  -- The blocks the loop read.
  have hsrc : ∀ k < nb s₀, blockAt u.mem (bAddr s₀ k) = blk s₀ k := fun k hk => by
    rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame hu.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact hb.d_p.sub_left (Offset.sub_base (dp s₀) (d := 16 * k) (n := 16) (k := 16 * nb s₀) (by omega))),
      ← srcBlk_false]
    exact hR.src hb k hk
  have hB : ∀ j < nb s₀, E.H j = blk s₀ j := fun j hj => by
    show blockAt s₄.mem (bAddr s₀ 0 + BitVec.ofNat 64 (16 * j)) = _
    rw [m₄, bAddr_add, Nat.zero_add, hsrc j hj]
  have hX : ∀ j < nb s₀, E.X j = ctb s₀ j := fun j hj => by
    show blockAt s₄.mem (bAddr s₀ 0 + BitVec.ofNat 64 (16 * j)) ^^^
      blockAt s₄.mem (pp s₀ - BitVec.ofNat 64 384 + BitVec.ofNat 64 (768 + 16 * j)) = _
    rw [m₄, bAddr_add, Nat.zero_add, hsrc j hj, ksAddr_small, hu.ks j hj]
  have hT : ∀ j < nb s₀, E.T j = smallPow s₀ P (nb s₀ - j) := fun j hj => by
    show s₄.mem.readW (pp s₀ + BitVec.ofNat 64 (256 - 16 * nb s₀) + BitVec.ofNat 64 (16 * j)) 128 = _
    rw [m₄, Offset.add_add, show 256 - 16 * nb s₀ + 16 * j = 256 - 16 * (nb s₀ - j) by omega]
    exact hu.pw _ (by omega) (by omega)
  refine WP.mono (finish_complete (ix := false) hb true hE₆
    (fun k hk => ⟨fun _ => ?_, fun hk' => absurd hk (by omega)⟩) ?_ ?_) fun t ht => ?_
  · have ct := hI₅.ct k hk
    rw [show E.aD k = bAddr s₀ k by
      show bAddr s₀ 0 + BitVec.ofNat 64 (16 * k) = _; rw [bAddr_add, Nat.zero_add], ← m₆] at ct
    rw [ct, hX k hk]
  · rw [g₆₄ _ (by decide) (by decide) (by decide), f₄.gpr, a8, hu.gpr _ (by decide), hR.counter,
      BitVec.add_assoc, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, BitVec.ofNat_add_ofNat,
      Nat.add_comm 8]
  · rw [y₆, hI₅.prod, StitchZH.accR_congr _ (nb s₀) hB hT, hlaw _ h1 (by omega)]
    have hy : E.y = y₀ s₀ := by
      show s₄.lane .xmm2 0 = _
      rw [f₄.lane _ (by decide) 0 (by decide), al _ (by decide) (by decide), hu.y, hR.hash]
    rw [hy]
    rfl
  · simpa only [Post, ↓reduceIte] using ht.1

end VG.Proof.Gcm.X86_64.StitchAvx8
