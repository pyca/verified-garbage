import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.VerifyAdd
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowCT

/-!
# Ed25519 verification with AVX512_IFMA: the windows in the lanes

A position of `Ifma.windows` is a doubling (`vdbl`) and its digits' additions (`vaddDigit`,
`vaddBase`), as one of `windows` is, with the point in the lanes, where every doubling
computes `T`: the invariants are `windows`' (`WindowSlide`), with the point in the lanes.
-/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Ifma VG.Proof.Ed25519
  VG.Proof.Ed25519.X86_64 Edwards
open VG.Impl.X25519.X86_64.Ifma (KM K19 KB0 KB1)
open VG.Proof.X25519.X86_64 (Outside off clob Keeps)
open VG.Proof.X25519.X86_64.Ifma (lanes fe5 fe5_congr)
open VG.Proof.Poly1305.X86_64.Avx2 (qw)

/-- A block of scalar instructions keeps the vector registers. -/
theorem WP.vk {is : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block is) s Q)
    (hc : is.all scalarI = true := by decide) :
    WP isa (.block is) s fun t => Q t ∧ t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi :=
  WP.vecKeep (c := .block is) hc h

/-- The constants are kept by anything that changes only bytes below them. -/
theorem EConsts.below {m m' : Mem} {base : Addr} (hk : EConsts m base) {o n : Nat}
    (h : Outside base o n m m') (hon : o + n ≤ 1664) : EConsts m' base := by
  have w : ∀ d, 1664 ≤ d → d + 8 ≤ 4096 →
      VG.Proof.X25519.X86_64.Ifma.mq m' base d = VG.Proof.X25519.X86_64.Ifma.mq m base d :=
    fun d h1 h2 => by
      rw [VG.Proof.X25519.X86_64.Ifma.mq_eq_word, VG.Proof.X25519.X86_64.Ifma.mq_eq_word]
      exact h.word (by omega) (by omega)
  refine ⟨⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩, fun l hl => ?_,
    fun l hl => ?_, fun l hl => ?_⟩
  · rw [w _ (by simp only [KM]; omega) (by simp only [KM]; omega)]; exact hk.km l hl
  · rw [w _ (by simp only [K19]; omega) (by simp only [K19]; omega)]; exact hk.k19 l hl
  · rw [w _ (by simp only [KB0]; omega) (by simp only [KB0]; omega)]; exact hk.kb0 l hl
  · rw [w _ (by simp only [KB1]; omega) (by simp only [KB1]; omega)]; exact hk.kb1 l hl
  · rw [w _ (by simp only [EK13]; omega) (by simp only [EK13]; omega)]; exact hk.k13 l hl
  · rw [w _ (by simp only [EK26]; omega) (by simp only [EK26]; omega)]; exact hk.k26 l hl
  · rw [w _ (by simp only [EK39]; omega) (by simp only [EK39]; omega)]; exact hk.k39 l hl

/-! ## Positions -/

/-- What a position in the lanes may change: `LKeep`'s, and the counter. -/
structure BKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → r ≠ .rsi → t.gpr r = s.gpr r
  r11 : t.gpr .r11 = s.gpr .r11
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 56 1288 s.mem t.mem
  d : env t.mem base 16 = env s.mem base 16

theorem BKeep.refl (base : Addr) (s : State) : BKeep base s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _, rfl⟩

theorem BKeep.trans {base : Addr} {s t u : State} (h : BKeep base s t) (k : BKeep base t u) :
    BKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.r11.trans h.r11, k.rd.trans h.rd,
    k.wr.trans h.wr, h.mem.trans k.mem, k.d.trans h.d⟩

theorem BKeep.of_lkeep {base : Addr} {s t : State} (h : LKeep base s t) : BKeep base s t :=
  ⟨h.gpr, h.r11, h.rd, h.wr, h.mem.mono (by decide) (by decide), h.slot 16⟩

theorem BKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ (r ∈ clob ∧ r ≠ .r11)) : BKeep base s t :=
  BKeep.of_lkeep (LKeep.of_keeps h hrs)

theorem BKeep.byte {base : Addr} {s t : State} (h : BKeep base s t) : ByteKeep base s t :=
  ⟨h.gpr, h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩

theorem BKeep.consts {base : Addr} {s t : State} (h : BKeep base s t) (hk : EConsts s.mem base) :
    EConsts t.mem base := hk.below h.mem (by decide)

/-- `batchBegin`: the counter moved down, and what it keeps. -/
theorem vbatchBegin_ok {s : State} {base : Addr} (hs : Scratch s base) (j : Nat)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block batchBegin) s fun t => t.mem.readW (off base 56) 64 = BitVec.ofNat 64 j ∧
      BKeep base s t ∧ t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi :=
  WP.mono (WP.vk (batchBegin_ok hs j hc)) fun _ ⟨⟨_, av, ag, ar, aw, am⟩, ax, ay⟩ =>
    ⟨av, ⟨fun r _ hb _ => ag r hb, ag _ (by decide), ar, aw, am.mono (by decide) (by decide),
      by rw [header_env am]⟩, ax, ay⟩

/-! ## The invariants in the lanes -/

/-- `WinAt`'s, with the point in the lanes (with `T`), its limbs small, and the constants. -/
structure VAt (s₀ : State) (base kp sp T : Addr) (A : EPoint dZ) (fA fB : Nat → Nat) (v : EPoint dZ)
    (c : Nat) (s : State) : Prop where
  ctx : WinCtx base kp sp T A s
  d : env s.mem base 16 = Spec.Ed25519.d
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 c
  digits : DigitsAre s.mem base fA fB
  value : Rep (lanePt s) v
  small : Small s
  consts : EConsts s.mem base
  keep : BKeep base s₀ s

theorem VAt.of_keep {s₀ s t : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat}
    {v v' : EPoint dZ} {c c' : Nat} (h : VAt s₀ base kp sp T A fA fB v c s) (k : BKeep base s t)
    (hc : t.mem.readW (off base 56) 64 = BitVec.ofNat 64 c') (hv : Rep (lanePt t) v') (hsm : Small t) :
    VAt s₀ base kp sp T A fA fB v' c' t :=
  ⟨h.ctx.of_byte k.byte, by rw [k.d]; exact h.d, hc, h.digits.of_byte k.byte.mem, hv, hsm,
    k.consts h.consts, h.keep.trans k⟩

theorem VAt.congr {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat}
    {v v' : EPoint dZ} {c : Nat} (h : VAt s₀ base kp sp T A fA fB v c s) (e : v = v') :
    VAt s₀ base kp sp T A fA fB v' c s := e ▸ h

/-- Scalar code keeping the counter, the lanes and what a position keeps. -/
theorem VAt.of_scalar {s₀ s t : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat}
    {v : EPoint dZ} {c : Nat} (h : VAt s₀ base kp sp T A fA fB v c s) {rs : List Reg} (k : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ (r ∈ clob ∧ r ≠ .r11)) (hx : t.xmm = s.xmm)
    (hy : t.ymmHi = s.ymmHi) : VAt s₀ base kp sp T A fA fB v c t :=
  have ⟨pt, st⟩ := lanePt_vec hx hy
  h.of_keep (BKeep.of_keeps k hrs) (by rw [k.2.1]; exact h.counter) (by rw [pt]; exact h.value) (st h.small)

/-- After position `p`. -/
abbrev VLoop (s₀ : State) (base kp sp T : Addr) (A : EPoint dZ) (fA fB : Nat → Nat) (top p : Nat)
    (s : State) : Prop :=
  VAt s₀ base kp sp T A fA fB (winVal A fA fB top p) p s

/-- Skipping, with the counter at `q`: the digits from `q` to `top` are zero. -/
structure VSkip (s₀ : State) (base kp sp T : Addr) (A : EPoint dZ) (fA fB : Nat → Nat) (top q : Nat)
    (s : State) : Prop where
  loop : VLoop s₀ base kp sp T A fA fB top q s
  zero : ∀ j, q ≤ j → j ≤ top → fA j = 0 ∧ fB j = 0
  pos : 0 < q
  le : q ≤ top + 1

/-! ## A position -/

/-- `k`'s digit at `p` added. -/
theorem vaddA_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {v : EPoint dZ}
    {top p : Nat} (hdg : Digits fA fB top) (hp : p ≤ top) (h : VAt s₀ base kp sp T A fA fB v p s) :
    WP isa (.seq (.block (digitAt 0)) (vaddDigit 5376)) s
      (VAt s₀ base kp sp T A fA fB (v + (Recode.dec (fA p)) • A) p) := by
  refine WP.seq (WP.mono (WP.vk (digitAt_ok h.ctx.scratch (by have := hdg.top; omega) (by decide) h.counter))
    fun a ⟨⟨ab, az, ka⟩, ax, ay⟩ => ?_)
  rw [(h.digits p (by have := hdg.top; omega)).1] at ab az
  have ha := h.of_scalar ka (by decide) ax ay
  refine WP.mono (vaddDigit_ok ha.ctx.scratch ha.consts ha.small (by decide) (by decide) ha.ctx.aTab (fA p)
    (hdg.a p) ab az ha.value) fun t ⟨tr, tsm, kt⟩ => ?_
  exact ha.of_keep (BKeep.of_lkeep kt) (kt.win.counter.trans ha.counter) tr tsm

/-- `S`'s digit at `p` added. -/
theorem vaddB_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {v : EPoint dZ}
    {top p : Nat} (hdg : Digits fA fB top) (hp : p ≤ top) (h : VAt s₀ base kp sp T A fA fB v p s) :
    WP isa (.seq (.block (digitAt 1)) vaddBase) s
      (VAt s₀ base kp sp T A fA fB (v + (Recode.dec (fB p)) • (-baseAff)) p) := by
  refine WP.seq (WP.mono (WP.vk (digitAt_ok h.ctx.scratch (by have := hdg.top; omega) (by decide) h.counter))
    fun a ⟨⟨ab, az, ka⟩, ax, ay⟩ => ?_)
  rw [(h.digits p (by have := hdg.top; omega)).2] at ab az
  have ha := h.of_scalar ka (by decide) ax ay
  refine WP.mono (vaddBase_ok ha.ctx.scratch ha.consts ha.small ha.ctx.bHeader ha.ctx.bTab (fB p) (hdg.b p)
    ab az ha.value) fun t ⟨tr, tsm, kt⟩ => ?_
  exact ha.of_keep (BKeep.of_lkeep kt) (kt.win.counter.trans ha.counter) tr tsm

/-- The digits at `p` added. -/
theorem vaddsAt_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {v : EPoint dZ}
    {top p : Nat} (hdg : Digits fA fB top) (hp : p ≤ top) (h : VAt s₀ base kp sp T A fA fB v p s) :
    WP isa vaddsAt s
      (VAt s₀ base kp sp T A fA fB (v + (Recode.dec (fA p)) • A + (Recode.dec (fB p)) • (-baseAff)) p) := by
  rw [vaddsAt]
  apply WP.assoc
  exact WP.seq (WP.mono (vaddA_ok hdg hp h) fun _ ha => vaddB_ok hdg hp ha)

/-- The doubling. -/
theorem vdblAt_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {v : EPoint dZ}
    {c : Nat} (h : VAt s₀ base kp sp T A fA fB v c s) :
    WP isa (.block vdbl) s (VAt s₀ base kp sp T A fA fB ((2 : Int) • v) c) := by
  refine WP.mono (vdbl_wp h.ctx.scratch.rdi (ctx_of h.ctx.scratch) h.consts h.small)
    fun b ⟨bg, brd, bwr, bo, bsm, bp⟩ => ?_
  have kb : LKeep base s b := ⟨fun r _ _ _ => by rw [bg], by rw [bg], brd, bwr, bo⟩
  exact h.of_keep (BKeep.of_lkeep kb) (kb.win.counter.trans h.counter)
    (by rw [bp, two_zsmul]; exact dblPoint_rep h.value.proj) bsm

/-- The position below: from after `p + 1` to after `p`, ZF set if `p` is zero. -/
theorem vstepAt_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top p : Nat}
    (hdg : Digits fA fB top) (hp : p ≤ top) (h : VLoop s₀ base kp sp T A fA fB top (p + 1) s) :
    WP isa vstepAt s fun t => t.zf = some (decide (p = 0)) ∧ VLoop s₀ base kp sp T A fA fB top p t := by
  rw [vstepAt]
  refine WP.seq (WP.mono (vbatchBegin_ok h.ctx.scratch p h.counter) fun a ⟨ac, ka, ax, ay⟩ => ?_)
  obtain ⟨pa, sa⟩ := lanePt_vec ax ay
  have ha : VAt s₀ base kp sp T A fA fB (winVal A fA fB top (p + 1)) p a :=
    h.of_keep ka ac (by rw [pa]; exact h.value) (sa h.small)
  refine WP.seq (WP.mono (vdblAt_ok ha) fun b hb => ?_)
  refine WP.seq (WP.mono (vaddsAt_ok hdg hp hb) fun c hc => ?_)
  refine WP.mono (WP.vk (counterTest_ok hc.ctx.scratch (by have := hdg.top; omega) hc.counter))
    fun t ⟨⟨tz, kt⟩, tx, ty⟩ => ⟨tz, (hc.of_scalar kt (by decide) tx ty).congr ?_⟩
  rw [winVal_step A fA fB hp]

/-! ## Skipping the leading zero digits -/

/-- A step of the skipping, below `p + 1`, as `skipTop_ok`. -/
theorem vskipTop_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top p : Nat}
    (hdg : Digits fA fB top) (h : VSkip s₀ base kp sp T A fA fB top (p + 1) s) :
    WP isa skipTop s fun t => t.zf = some (skipStops fA fB p) ∧
      (skipStops fA fB p = true → VAt s₀ base kp sp T A fA fB ((2 : Int) • winVal A fA fB top (p + 1)) p t) ∧
      (skipStops fA fB p = false → VSkip s₀ base kp sp T A fA fB top p t) := by
  have hle := h.le
  have hl := h.loop
  have h0 : winVal A fA fB top (p + 1) = 0 := winVal_zero h.zero
  rw [skipTop]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (vbatchBegin_ok hl.ctx.scratch p hl.counter) fun a ⟨ac, ka, ax, ay⟩ => ?_
  obtain ⟨pa, sa⟩ := lanePt_vec ax ay
  have ha : VAt s₀ base kp sp T A fA fB 0 p a :=
    hl.of_keep ka ac (by rw [pa, ← h0]; exact hl.value) (sa hl.small)
  refine WP.mono (WP.vk (digitsAt_ok ha.ctx.scratch (by have := hdg.top; omega) ha.counter))
    fun b ⟨⟨bz, kb⟩, bx, bw⟩ => ?_
  rw [(ha.digits p (by have := hdg.top; omega)).1, (ha.digits p (by have := hdg.top; omega)).2] at bz
  have hb := ha.of_scalar kb (by decide) bx bw
  have e2 : (0 : EPoint dZ) = (2 : Int) • winVal A fA fB top (p + 1) := by rw [h0, smul_zero]
  refine WP.ite (!decide (fA p = 0 ∧ fB p = 0)) (by simp only [eval, bz, Option.map_some])
    (fun hz => ?_) (fun hz => ?_)
  · have hst : skipStops fA fB p = true := by
      simp only [skipStops, hz, Bool.true_or]
    refine WP.mono (WP.vk (cmpSelf_ok b)) fun t ⟨⟨tz, kt⟩, tx, ty⟩ => ⟨by rw [tz, hst],
      fun _ => (hb.of_scalar kt (by decide) tx ty).congr e2, fun hf => absurd hf (by rw [hst]; decide)⟩
  · have hz0 : fA p = 0 ∧ fB p = 0 := by simpa using hz
    refine WP.mono (WP.vk (counterTest_ok hb.ctx.scratch (by have := hdg.top; omega) hb.counter))
      fun t ⟨⟨tz, kt⟩, tx, ty⟩ => ?_
    have ht := hb.of_scalar kt (by decide) tx ty
    have hst : skipStops fA fB p = decide (p = 0) := by
      simp only [skipStops, hz0, and_self, decide_true, Bool.not_true, Bool.false_or]
    by_cases hp0 : p = 0
    · subst hp0
      exact ⟨by rw [tz, hst], fun _ => ht.congr e2, fun hf => absurd hf (by rw [hst]; decide)⟩
    · have hz' : ∀ j, p ≤ j → j ≤ top → fA j = 0 ∧ fB j = 0 := fun j h1 h2 => by
        rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
        · exact hz0
        · exact h.zero j (by omega) h2
      exact ⟨by rw [tz, hst], fun hs => absurd hs (by rw [hst]; simp [hp0]),
        fun _ => ⟨ht.congr (winVal_zero hz').symm, hz', by omega, by omega⟩⟩

/-- The windows in the lanes, from one above `top` to after position 0, `vstore` aside. -/
theorem vloops_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top : Nat}
    (hdg : Digits fA fB top) (h : VSkip s₀ base kp sp T A fA fB top (top + 1) s) {Q : State → Prop}
    (hq : ∀ t, VLoop s₀ base kp sp T A fA fB top 0 t → WP isa (.block vstore) t Q) :
    WP isa (.seq (.loop skipTop .ne) (.seq vaddsAt (.seq (.block batchTest)
      (.seq (.ite .ne (.loop vstepAt .ne) (.block [])) (.block vstore))))) s Q := by
  refine WP.seq (WP.mono (show WP isa (.loop skipTop .ne) s fun t =>
      ∃ p, p ≤ top ∧ VAt s₀ base kp sp T A fA fB ((2 : Int) • winVal A fA fB top (p + 1)) p t by
    apply WP.loop (fun q t => VSkip s₀ base kp sp T A fA fB top q t) (n := top + 1)
    · intro q t ht
      obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := ht.pos; omega : q ≠ 0)
      have hle := ht.le
      refine WP.mono (vskipTop_ok hdg ht) fun u ⟨uz, ut, uf⟩ => ?_
      cases hs : skipStops fA fB p
      · exact Or.inr ⟨by simp only [eval, uz, hs, Option.map_some, Bool.not_false], p, by omega, uf hs⟩
      · exact Or.inl ⟨by simp only [eval, uz, hs, Option.map_some, Bool.not_true], p, by omega, ut hs⟩
    · exact h) fun a ⟨p, hp, ha⟩ => ?_)
  refine WP.seq (WP.mono (vaddsAt_ok hdg hp ha) fun b hb => ?_)
  have hb' : VLoop s₀ base kp sp T A fA fB top p b := hb.congr (by rw [winVal_step A fA fB hp])
  refine WP.seq (WP.mono (WP.vk (counterTest_ok hb'.ctx.scratch (by have := hdg.top; omega) hb'.counter))
    fun c ⟨⟨cz, kc⟩, cx, cy⟩ => ?_)
  have hc := hb'.of_scalar kc (by decide) cx cy
  refine WP.seq ?_
  refine WP.ite (!decide (p = 0)) (by simp only [eval, cz, Option.map_some]) (fun hz => ?_) (fun hz => ?_)
  · have hp0 : p ≠ 0 := by simpa using hz
    refine WP.mono (show WP isa (.loop vstepAt .ne) c (VLoop s₀ base kp sp T A fA fB top 0) by
      apply WP.loop (fun n t => VLoop s₀ base kp sp T A fA fB top n t ∧ 0 < n ∧ n ≤ top) (n := p)
      · intro n t ⟨ht, hn0, hn⟩
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
        refine WP.mono (vstepAt_ok hdg (by omega) ht) fun u ⟨uz, hu⟩ => ?_
        by_cases hm : m = 0
        · subst hm
          exact Or.inl ⟨by simp only [eval, uz, decide_true, Option.map_some, Bool.not_true], hu⟩
        · exact Or.inr ⟨by simp only [eval, uz, decide_eq_false hm, Option.map_some, Bool.not_false],
            m, by omega, hu, by omega, by omega⟩
      · exact ⟨hc, by omega, hp⟩) hq
  · have hp0 : p = 0 := by simpa using hz
    subst hp0
    exact WP.block_nil (hq c hc)

/-! ## Into the lanes and back -/

/-- Before the windows: the constants, and slots 0–3 in the lanes. -/
theorem wprep_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block (VG.Impl.X25519.X86_64.Ifma.consts ++ vload)) s fun t =>
      (∀ r, r ∉ clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 1664 224 s.mem t.mem ∧ EConsts t.mem base ∧ Small t ∧
      lanePt t = point (env s.mem base) 0 1 2 3 := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.consts_wp s)
    fun s₁ ⟨ha, hc, hd, hb, h8, h9, h10, _, _, g₁, m₁, rd₁, wr₁, _, _, _⟩ => ?_
  have hs₁ : Scratch s₁ base := ⟨by rw [g₁ _ (by decide)]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  refine WP.mono (vload_wp hs₁.rdi (ctx_of hs₁) ha hc hd hb h8 h9 h10) fun t ⟨g₂, rd₂, wr₂, o₂, k₂, u₂⟩ => ?_
  refine ⟨fun r hr => by rw [g₂, g₁ r (fun h => hr (cregs_clob r h))], by rw [rd₂, rd₁], by rw [wr₂, wr₁],
    by rw [← m₁]; exact o₂, k₂, fun l hl i hi => by have := (u₂ l hl i hi).2; omega, ?_⟩
  have e : ∀ l (hl : l < 4), fe5 (lanes t 0 l) = env s.mem base ⟨l, by omega⟩ := fun l hl => by
    rw [fe5_congr (fun i hi => (u₂ l hl i hi).1), fe5_load, m₁]; rfl
  simp only [lanePt, point]
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]
  rfl

/-- The MXCSR prologue: saving it into `r11`, then `0x1FBF` into it. -/
def mxSave : List Instr := [.stmxcsr (VG.Impl.X25519.X86_64.sc EMX), .mov32 .r11 (.mem (VG.Impl.X25519.X86_64.sc EMX)),
  .alu32 .and .r11 (.imm 0xFFFF)]
def mxLoad : List Instr := [.mov32 .rax (.imm 0x1FBF), .store32 (VG.Impl.X25519.X86_64.sc (EMX + 4)) .rax,
  .ldmxcsr (VG.Impl.X25519.X86_64.sc (EMX + 4)), .lfence]
/-- The MXCSR epilogue: MXCSR back from `r11`. -/
def mxRestore : List Instr := [.store32 (VG.Impl.X25519.X86_64.sc EMX) .r11,
  .ldmxcsr (VG.Impl.X25519.X86_64.sc EMX)]

theorem withMx_eq (c : Prog isa) : withMx c =
    .seq (.block mxSave) (.seq (.seq (.block mxLoad) (.seq c (.block [.lfence]))) (.block mxRestore)) := rfl

/-- A run in the lanes, from `s₃`, entered from a run started in `s₀` satisfying `R₀`: what has
been kept since `s₀`, `r11` the saved MXCSR, whose reserved bits are clear, and `Q s₃`. -/
def VRun (R₀ : State → Prop) (base : Addr) (Q : State → State → Prop) (x : State) : Prop :=
  ∃ s₀ s₃, R₀ s₀ ∧ ByteKeep base s₀ s₃ ∧ ((s₃.gpr .r11).setWidth 32).extractLsb' 16 16 = 0 ∧ Q s₃ x

theorem VRun.mono {R₀ : State → Prop} {base : Addr} {Q Q' : State → State → Prop} {x y : State}
    (h : VRun R₀ base Q x) (hq : ∀ s₃, Q s₃ x → Q' s₃ y) : VRun R₀ base Q' y :=
  let ⟨s₀, s₃, r₀, k, m, q⟩ := h; ⟨s₀, s₃, r₀, k, m, hq s₃ q⟩

/-- Into the lanes, and the MXCSR prologue: the skipping's start. -/
theorem enter_ok {R₀ : State → Prop} {s : State} {base kp sp T : Addr} {A : EPoint dZ}
    {fA fB : Nat → Nat} {top : Nat} (h : StartRun R₀ base kp sp T A fA fB top s) :
    WP isa (.block (VG.Impl.X25519.X86_64.Ifma.consts ++ vload)) s fun s₁ => s₁.gpr .rdi = base ∧
      WP isa (.block mxSave) s₁ fun s₂ => s₂.gpr .rdi = base ∧
        WP isa (.block mxLoad) s₂
          (VRun R₀ base fun s₃ => VSkip s₃ base kp sp T A fA fB top (top + 1)) := by
  obtain ⟨s₀, r₀, hk⟩ := h
  have h := hk.loop
  have hs := h.ctx.scratch
  refine WP.mono (wprep_ok hs) fun s₁ ⟨g₁, rd₁, wr₁, o₁, k₁, sm₁, p₁⟩ => ?_
  have hs₁ : Scratch s₁ base := ⟨by rw [g₁ _ (by decide)]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  refine ⟨hs₁.rdi, WP.mono (save_wp hs₁) fun s₂ ⟨g₂, r11₂, k₂⟩ => ?_⟩
  have hs₂ : Scratch s₂ base := ⟨by rw [g₂ _ (by decide)]; exact hs₁.rdi, by rw [k₂.wr]; exact hs₁.wr, hs.nowrap⟩
  refine ⟨hs₂.rdi, WP.mono (load_wp hs₂) fun s₃ ⟨g₃, k₃⟩ => ?_⟩
  have q₃ : ∀ x l, qw s₃ x l = qw s₁ x l := fun x l => by rw [k₃.qw_eq, k₂.qw_eq]
  have m₃ : Outside base 56 1832 s.mem s₃.mem :=
    ((o₁.mono (by decide) (by decide)).trans (k₂.mem.mono (by decide) (by decide))).trans
      (k₃.mem.mono (by decide) (by decide))
  have k₀₃ : ByteKeep base s s₃ := ⟨fun r hc _ _ => by
      rw [g₃ r (fun e => hc (e ▸ by decide)), g₂ r (fun e => hc (e ▸ by decide)), g₁ r hc],
    by rw [k₃.rd, k₂.rd, rd₁], by rw [k₃.wr, k₂.wr, wr₁], m₃⟩
  have m₃' : Outside base 1600 288 s.mem s₃.mem :=
    ((o₁.mono (by decide) (by decide)).trans (k₂.mem.mono (by simp only [EMX]; omega) (by simp only [EMX]; omega))).trans
      (k₃.mem.mono (by simp only [EMX]; omega) (by simp only [EMX]; omega))
  refine ⟨s₀, s₃, r₀, h.keep.trans k₀₃, by rw [g₃ _ (by decide), r11₂]; exact and_ffff _, ?_⟩
  refine ⟨⟨h.ctx.of_byte k₀₃, ?_, ?_, h.digits.of_byte k₀₃.mem, ?_,
    fun l hl i hi => by rw [lanes_qw q₃]; exact sm₁ l hl i hi, (k₁.outsideMx k₂.mem).outsideMx k₃.mem,
    BKeep.refl _ _⟩, hk.zero, hk.pos, hk.le⟩
  · rw [show env s₃.mem base 16 = env s.mem base 16 from
      Outside_F m₃' (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega))]
    exact h.d
  · exact (m₃'.word (Or.inl (by decide)) (by decide)).trans h.counter
  · rw [lanePt_qw q₃, p₁, winVal_zero hk.zero]; exact hk.full

/-- Back into slots 0–3, and the MXCSR epilogue. -/
theorem exit_ok {R₀ : State → Prop} {w : State} {base kp sp T : Addr} {A : EPoint dZ}
    {fA fB : Nat → Nat} {top : Nat}
    (h : VRun R₀ base (fun s₃ => VLoop s₃ base kp sp T A fA fB top 0) w) :
    WP isa (.block vstore) w fun t₀ => t₀.gpr .rdi = base ∧
      WP isa (.block [.lfence]) t₀ fun t₁ => t₁.gpr .rdi = base ∧
        WP isa (.block mxRestore) t₁ (LoopRun R₀ base kp sp T A fA fB top 0) := by
  obtain ⟨s₀, s₃, r₀, k₀₃, m₃, hw⟩ := h
  have hsw : Scratch w base := hw.ctx.scratch
  refine WP.mono (vstore_wp hsw.rdi (ctx_of hsw) hw.consts hw.small) fun t₀ ⟨tg, trd, twr, tou, tf⟩ => ?_
  have hs₀ : Scratch t₀ base := ⟨by rw [tg]; exact hsw.rdi, by rw [twr]; exact hsw.wr, hsw.nowrap⟩
  refine ⟨hs₀.rdi, WP.mono (lfence_wp t₀) fun t₁ e₁ => ?_⟩
  subst e₁
  refine ⟨hs₀.rdi, ?_⟩
  refine WP.mono (restore_wp hs₀ (by rw [tg, hw.keep.r11]; exact m₃)) fun t ⟨g₈, k₈⟩ => ?_
  have pt : point (env t.mem base) 0 1 2 3 = lanePt w := by
    simp only [point, lanePt, env, VG.Impl.Ed25519.X86_64.offset]
    rw [← tf 0 (by decide), ← tf 1 (by decide), ← tf 2 (by decide), ← tf 3 (by decide),
      Outside_F k₈.mem (by decide) (Or.inl (by decide)), Outside_F k₈.mem (by decide) (Or.inl (by decide)),
      Outside_F k₈.mem (by decide) (Or.inl (by decide)), Outside_F k₈.mem (by decide) (Or.inl (by decide))]
    rfl
  have mwt : Outside base 64 1544 w.mem t.mem :=
    (tou.mono (by decide) (by decide)).trans (k₈.mem.mono (by simp only [EMX]; omega) (by simp only [EMX]; omega))
  have kwt : ByteKeep base w t := ⟨fun r _ _ _ => by rw [g₈, tg], by rw [k₈.rd, trd], by rw [k₈.wr, twr],
    mwt.mono (by decide) (by decide)⟩
  have kst : ByteKeep base s₃ t := hw.keep.byte.trans kwt
  refine ⟨s₀, r₀, hw.ctx.of_byte kwt, ?_, ?_, hw.digits.of_byte kwt.mem, by rw [pt]; exact hw.value.proj,
    k₀₃.trans kst⟩
  · rw [show env t.mem base 16 = env t₁.mem base 16 from
        Outside_F k₈.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset, EMX]; omega)),
      show env t₁.mem base 16 = env w.mem base 16 from
        Outside_F tou (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega))]
    exact hw.d
  · exact (mwt.word (Or.inl (by decide)) (by decide)).trans hw.counter

/-- `Ifma.windows` keeps the windows' invariant, from one above `top` to after position 0. -/
theorem windows_ok {R₀ : State → Prop} {s : State} {base kp sp T : Addr} {A : EPoint dZ}
    {fA fB : Nat → Nat} {top : Nat} (hdg : Digits fA fB top) (h : StartRun R₀ base kp sp T A fA fB top s) :
    WP isa Impl.Ed25519.X86_64.Ifma.windows s (LoopRun R₀ base kp sp T A fA fB top 0) := by
  rw [Impl.Ed25519.X86_64.Ifma.windows, withMx_eq]
  refine WP.seq (WP.mono (enter_ok h) fun s₁ ⟨_, h₁⟩ => WP.seq (WP.mono h₁ fun s₂ ⟨_, h₂⟩ => ?_))
  refine WP.seq (WP.seq (WP.mono h₂ fun s₃ h₃ => ?_))
  obtain ⟨s₀, s₃', r₀, k₀, m₀, v₃⟩ := h₃
  refine WP.seq (vloops_ok hdg v₃ fun w hw => ?_)
  exact WP.mono (exit_ok ⟨s₀, s₃', r₀, k₀, m₀, hw⟩) fun _ ⟨_, h₄⟩ => WP.mono h₄ fun _ ⟨_, h₅⟩ => h₅

end VG.Proof.Ed25519.X86_64.Ifma
