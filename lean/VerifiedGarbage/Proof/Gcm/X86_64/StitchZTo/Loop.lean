import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup

/-!
# The out-of-place AVX-512 loop: the setup, the loop of one group, the stores

As `StitchZ/Loop.lean` does in place. `setupCTo_ok`: the end of the setup
loads `Y` and makes the counters and the increment as `Stitch.setupC`, and
leaves `src - dst` in `r8` and `dst` in `rdx`; with the powers stored before
it (`setupTTo_ok`, `Ready2To`) and the four lanes after it (`setupZTo_ok`),
the state the loop starts from (`ReadyTo`).

`EInvTo s₀ P e s`: `e` groups of sixteen blocks are encrypted (`AInvTo`),
the ciphertext of the first `e - 1` hashed into `Y`; `rdx` points to output
group `e - 1`, the next to hash. `bodyTo_ok`: a body encrypts group `e`
(`batchTo_ok`) while it hashes the output of group `e - 1` between its
rounds (`StitchZ.gq_ok`), which it does not write (`StitchZ.QG.data`, for
the in-place view `dst s₀`). `finalTo_ok`: the stores after the loops, and
the contract (`EPostTo`).
-/

namespace VG.Proof.Gcm.X86_64.StitchZTo

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo EPostTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch hk y₀
  dp dR pR cR yR bAddr addr_eq in_sub in_sub_int in_rdwr ite_t ite_f ghash_append16 blockAt_writeW_sep'
  storesK_ok pregs_get blockAt_outP)
open VG.Proof.Gcm.X86_64.StitchZ (GEnv QG gRegs gRegs_ok gq_ok QG.data keepP nextE_ok FinOk ghRun_ok ghFin
  store16Z_ok State.zlane_setV256 paddd_two_two lane0_zlane lane1_zlane shuf44_0 shuf44_1 shuf44_2 shuf44_3)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY storesK pregs)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Impl.Gcm.X86_64.StitchZ (gq setupZ lastG)
open VG.Impl.Gcm.X86_64.StitchZTo (setupCTo firstTo bodyTo)
open VG.Proof.Gcm.X86_64.Vpclmul (getLsbD_one8)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Proof.Aes.X86_64.VaesZ (four)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-! ## The setup -/

theorem setupCTo_ok (s : State) (h0 : ∀ l < 2, s.lane .xmm0 l = revMask)
    (hy : InRegions s.wr (s.gpr .rcx) 16) (hc : InRegions s.wr (s.gpr .rdx) 16) :
    WP isa (.block setupCTo) s fun s' =>
      s'.lane .xmm2 0 = blockAt s.mem (s.gpr .rcx) ∧ s'.lane .xmm2 1 = 0 ∧
      (∀ l < 2, s'.lane .xmm14 l = Nat.repeat inc32 l (blockAt s.mem (s.gpr .rdx))) ∧
      (∀ l < 2, s'.lane .xmm15 l = VG.Proof.Aes.X86_64.Vaes.two) ∧
      s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * (s.gpr .rsi).toNat) ∧
      s'.gpr .rax = s.gpr .rdx ∧ s'.gpr .rdx = s.gpr .r10 ∧ s'.gpr .r8 = s.gpr .r8 - s.gpr .r10 ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      (∀ r, r ≠ .xmm2 → r ≠ .xmm13 → r ≠ .xmm14 → r ≠ .xmm15 → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hy' : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hy
  have hc' : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hc
  have m0 := h0 0 (by decide)
  simp only [State.lane, ite_true] at m0
  apply WP.of_runBlock
  simp only [setupCTo, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setV, State.setReg, State.load128, State.lane,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, hy', hc', VBinOp.sse, getLsbD_one8, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', m0]
  refine ⟨?_, trivial, fun l hl => ?_, fun l hl => ?_, ?_, trivial, trivial, trivial, fun r h1 h2 h3 h4 => ?_,
    fun r h2 h13 h14 h15 l hl => ?_, trivial, trivial, trivial⟩
  · rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact (VG.Proof.Gcm.X86_64.blockAt_eq _ _).symm
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp only [ite_true]
      rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact (VG.Proof.Gcm.X86_64.blockAt_eq _ _).symm
    · simp only [Nat.one_ne_zero, ite_false]
      rw [BitVec.ofInt_natCast, BitVec.add_zero, ← VG.Proof.Gcm.X86_64.blockAt_eq]
      exact VG.Proof.Aes.X86_64.AesNi.paddd_one _
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · bv_omega
  · simp [h1, h2, h3, h4]
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [h2, h13, h14, h15]

/-- After the powers are stored and `setupCTo`: the two lanes. -/
structure Ready2To (s₀ : State) (P : Nat → Nat → Block) (s : State) : Prop where
  ctr : ∀ l < 2, s.lane .xmm14 l = Nat.repeat inc32 l (cb s₀)
  msk : ∀ l < 2, s.lane .xmm0 l = revMask
  inc : ∀ l < 2, s.lane .xmm15 l = VG.Proof.Aes.X86_64.Vaes.two
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = y₀ s₀
  y1 : s.lane .xmm2 1 = 0
  rdi : s.gpr .rdi = kp s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r10 : s.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  r8 : s.gpr .r8 = sp s₀ - op s₀
  rdx : s.gpr .rdx = op s₀
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  frame : Frame [pR s₀] s₀.mem s.mem
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The setup after the powers: they are stored in the working space, then
`Y`, the counter, the increment and the pointers. -/
theorem setupTTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {s₁ : State}
    (l0 : ∀ l < 2, s₁.lane .xmm0 l = revMask) (l1 : ∀ l < 2, s₁.lane .xmm1 l = poly)
    (g₁ : ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) (m₁ : s₁.mem = s₀.mem) (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr) :
    WP isa (.block (storesK .r11 pregs 0 ++ setupCTo)) s₁ (Ready2To s₀ fun k l => s₁.lane (preg16 k) l) := by
  have hwp := hp.wrap_p
  have hr11 : s₁.gpr .r11 = pp s₀ := g₁ _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storesK_ok .r11 pregs 0 s₁ (fun k hk => by
      rw [wr₁, hr11]; exact in_sub_int hp.p_in (by simp [pregs] at hk; omega))
    (by rw [hr11]; simp [pregs]; omega)) fun s₂ ⟨sv, fr, g₂, rd₂, wr₂, l₂⟩ => ?_
  rw [hr11, Nat.mul_zero, BitVec.add_zero, show 32 * pregs.length = 256 from rfl, m₁] at fr
  replace fr : Frame [pR s₀] s₀.mem s₂.mem := fr.sub fun r hr => ⟨pR s₀, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩
  have hp₂ : ∀ {p : Addr}, Region.Disjoint ⟨p, 16⟩ (pR s₀) → blockAt s₂.mem p = blockAt s₀.mem p :=
    fun hd => by rw [blockAt_outP fr hd]
  refine WP.mono (setupCTo_ok s₂ (fun l hl => by rw [l₂]; exact l0 l hl)
    (by rw [wr₂, wr₁, g₂, g₁ _ (by decide)]; exact hp.y_in)
    (by rw [wr₂, wr₁, g₂, g₁ _ (by decide)]; exact hp.c_in))
    fun s₃ ⟨y0, y1, c14, c15, r10, rax, rdx, r8, gk, lk, m₃, rd₃, wr₃⟩ => ?_
  have gs : ∀ r, r ≠ .rax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, g₁ r hr]
  refine ⟨fun l hl => ?_, fun l hl => ?_, c15,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl, l₂]; exact l1 l hl,
    by rw [y0, gs _ (by decide), hp₂ (hp.p_y.symm)], y1,
    by rw [gk _ (by decide) (by decide) (by decide) (by decide), gs _ (by decide)],
    by rw [gk _ (by decide) (by decide) (by decide) (by decide), gs _ (by decide)],
    by rw [r10, gs _ (by decide), gs _ (by decide)],
    by rw [r8, gs _ (by decide), gs _ (by decide)],
    by rw [rdx, gs _ (by decide)], by rw [rax, gs _ (by decide)],
    fun r h1 h2 h3 h4 => by rw [gk r h1 h2 h3 h4, gs r h1], by rw [m₃]; exact fr, fun k hk l hl => ?_,
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  · rw [c14 l hl, gs _ (by decide), hp₂ hp.p_c.symm]
  · rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl, l₂]; exact l0 l hl
  · rw [m₃, show pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l) = s₁.gpr .r11 + BitVec.ofNat 64 (32 * (0 + k) + 16 * l)
      by rw [hr11, Nat.zero_add], sv k (by simp [pregs]; omega) l hl, pregs_get]

/-- The state the loop starts from. -/
structure ReadyTo (s₀ : State) (P : Nat → Nat → Block) (s : State) : Prop where
  a : AInvTo s₀ 0 s
  rdx : s.gpr .rdx = op s₀
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 4, s.zlane .xmm1 l = poly
  y : s.zlane .xmm2 0 = y₀ s₀
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

/-- The four lanes, from the two (as `StitchZ.setupZ_ok`). -/
theorem setupZTo_ok {s₀ : State} {P : Nat → Nat → Block} {s : State} (hR : Ready2To s₀ P s) :
    WP isa (.block setupZ) s (ReadyTo s₀ fun k l => P (2 * k + l / 2) (l % 2)) := by
  refine WP.mono (WP.zframe (is := setupZ) (rs := [.xmm13, .xmm14, .xmm15, .xmm15, .xmm0, .xmm1, .xmm2]) (by decide)
    (Q := fun s' => (∀ l < 4, s'.zlane .xmm14 l = Nat.repeat inc32 l (cb s₀)) ∧ (∀ l < 4, s'.zlane .xmm0 l = revMask) ∧
      (∀ l < 4, s'.zlane .xmm15 l = four) ∧ (∀ l < 4, s'.zlane .xmm1 l = poly) ∧ s'.zlane .xmm2 0 = s.lane .xmm2 0 ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0)) ?_) fun s' ⟨⟨c14, m0, i15, p1, y0, y1⟩, f⟩ => ?_
  · have c0 : s.xmm .xmm14 = Nat.repeat inc32 0 (cb s₀) := by
      have h := hR.ctr 0 (by decide); simp only [State.lane, ite_true] at h; exact h
    have c1 : s.ymmHi .xmm14 = Nat.repeat inc32 1 (cb s₀) := by
      have h := hR.ctr 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
    have i0 : s.xmm .xmm15 = VG.Proof.Aes.X86_64.Vaes.two := by
      have h := hR.inc 0 (by decide); simp only [State.lane, ite_true] at h; exact h
    have i1 : s.ymmHi .xmm15 = VG.Proof.Aes.X86_64.Vaes.two := by
      have h := hR.inc 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
    have m0 : s.xmm .xmm0 = revMask := by
      have h := hR.msk 0 (by decide); simp only [State.lane, ite_true] at h; exact h
    have m1 : s.ymmHi .xmm0 = revMask := by
      have h := hR.msk 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
    have p0 : s.xmm .xmm1 = poly := by
      have h := hR.m1 0 (by decide); simp only [State.lane, ite_true] at h; exact h
    have p1 : s.ymmHi .xmm1 = poly := by
      have h := hR.m1 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
    rw [setupZ]
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_,
      fun l hl => ?_, ?_, fun l hl1 hl4 => ?_⟩⟩
    all_goals simp only [VOp.exec]
    all_goals try rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
    all_goals try omega
    all_goals simp (disch := decide) only [lane0_zlane, lane1_zlane, State.zlane_setV_ne, zlane_vshufi32x4,
      State.zlane_setV256, State.zlane_setV128, shuf44_0, shuf44_1, shuf44_2, shuf44_3, reduceCtorEq,
      ↓reduceIte, VBinOp.sse, Nat.one_ne_zero]
    all_goals simp only [State.zlane, State.lane, ite_true, ite_false, Nat.one_ne_zero,
      show (0 : Nat) < 2 by decide, show (1 : Nat) < 2 by decide]
    all_goals first
      | exact c0 | exact c1 | exact m0 | exact m1 | exact p0 | exact p1
      | (rw [c0, i0, VG.Proof.Aes.X86_64.Vaes.paddd_two]; rfl)
      | (rw [c1, i1, VG.Proof.Aes.X86_64.Vaes.paddd_two]; rfl)
      | (rw [i0]; exact paddd_two_two) | (rw [i1]; exact paddd_two_two)
  · refine ⟨⟨Nat.zero_le _, fun l hl => by rw [c14 l hl, Nat.zero_add], m0, i15, by rw [f.gpr]; exact hR.rdi,
      by rw [f.gpr]; exact hR.rsi, by rw [f.gpr]; exact hR.r10, by rw [f.gpr]; exact hR.r8,
      by rw [f.mem]; exact hR.frame.mono fun r hr => by simp at hr ⊢; exact Or.inr hr,
      fun k hk => absurd hk (Nat.not_lt_zero _), by rw [f.rd]; exact hR.rd, by rw [f.wr]; exact hR.wr⟩,
      by rw [f.gpr]; exact hR.rdx, by rw [f.gpr]; exact hR.rax,
      fun r h1 h2 h3 h4 => by rw [f.gpr]; exact hR.gpr r h1 h2 h3 h4,
      fun k hk l hl => ?_, p1, by rw [y0]; exact hR.y, y1⟩
    rw [f.mem, show 64 * k + 16 * l = 32 * (2 * k + l / 2) + 16 * (l % 2) by omega]
    exact hR.pw _ (by omega) _ (by omega)

/-! ## The loop of one group -/

structure EInvTo (s₀ : State) (P : Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInvTo s₀ (16 * e) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (op s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 4, s.zlane .xmm1 l = poly
  y : s.zlane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map (ctbT s₀))
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

/-- The powers in the working space are kept by the output written. -/
theorem keepPTo {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {c : Nat} (hc : c + 16 ≤ nb s₀) {m m' : Mem}
    (hf : Frame [⟨oAddr s₀ c, 256⟩] m m') {k l : Nat} (hk : k < 4) (hl : l < 4) :
    m'.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = m.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 :=
  keepP hp.toD hc hf hk hl

/-- What hashing output group `e - 1` needs, from `rdx` pointing to it with
its blocks below `c` encrypted. -/
theorem genv {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} {e c : Nat} {s : State}
    (hA : AInvTo s₀ c s) (h1e : 1 ≤ e) (hec : 16 * e ≤ c)
    (hrdx : (s.gpr .rdx).toNat = (op s₀).toNat + 256 * (e - 1)) (hr11 : s.gpr .r11 = pp s₀)
    (hpw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l) :
    GEnv (dst s₀) 0 (s.gpr .rdx) (fun i => ctbT s₀ (16 * (e - 1) + i)) P s :=
  { rdx := rfl
    r11 := hr11
    xs := fun i _ hi => by
      rw [show s.gpr .rdx + BitVec.ofNat 64 (16 * i) = oAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega),
        hA.blocks _ (by omega)]
    pv := hpw
    ina := fun k hk => by
      have := hA.le
      rw [hA.rd, hA.wr, BitVec.ofInt_natCast,
        show s.gpr .rdx + BitVec.ofNat 64 (64 * k) = op s₀ + BitVec.ofNat 64 (256 * (e - 1) + 64 * k) from
          addr_eq (by omega)]
      exact in_rdwr (in_sub hp.o_in (by omega))
    inp := fun k hk => by
      rw [hA.rd, hA.wr]
      exact in_rdwr (in_sub_int hp.p_in (by omega))
    m0 := hA.msk }

theorem bodyTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {e : Nat} (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInvTo s₀ P e s) :
    WP isa bodyTo s fun s' => EInvTo s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) := by
  have hd := hp.toD
  have hnb := nb_dst s₀
  have hw := hp.wrap_o
  have h1e := hI.one
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctbT s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (op s₀).toNat + 256 * (e - 1) := hI.rdx
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hE₁ : GEnv (dst s₀) 0 a X P s := genv hp hI.a h1e (by omega) hI.rdx hr11 hI.pw
  have hrdx₁ : (s.gpr .rdx).toNat + 64 * 4 = (op s₀).toNat + 16 * (16 * e) := by
    show a.toNat + _ = _; omega
  -- The group, with the loads of the previous group after rounds 1–4 and the reduction after round 5.
  refine WP.seq (WP.mono (batchTo_ok hp gq gRegs gRegs_ok (QG (dst s₀) (fun _ => 0) a X P yl)
    (gq_ok (s₀ := dst s₀) (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.zero_le _))
    (fun j t t' h f => h.zframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hd (by omega) (by omega) ha (fun i _ hi => by omega) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 4) (by omega) hI.a hrdx₁
    ⟨hE₁, hI.m1, by rw [ite_f (by decide)]; exact ⟨fun h => absurd h (by decide), fun l hl => rfl⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  refine WP.mono (nextE_ok s₂) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, h1', h2⟩ := hQ₂
  rw [ite_t (by decide)] at h2
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₂]
  have hA' : AInvTo s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 16 by omega]
    exact hA₂.gpr2 fg fl fm frd fwr
  have hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1 - 1)) := by
    rw [hg₂, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega) (by omega)]
    congr 1; omega
  refine ⟨⟨hA', by omega, ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 h5 => by rw [gk r h2 h4]; exact hI.gpr r h1 h2 h3 h4 h5,
    fun k hk l hl => by rw [fm, keepPTo hp (by omega) hm₂ hk hl]; exact hI.pw k hk l hl,
    fun l hl => by rw [fl]; exact h1' l hl, ?_,
    fun l h1 h4 => by rw [fl]; exact h2.2 l h1 h4⟩, ?_⟩
  · rw [frdx, hg₂, BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (by show a.toNat + 256 < 2 ^ 64; omega)]
    show a.toNat + 256 = _
    rw [ha, show e + 1 - 1 = (e - 1) + 1 by omega, Nat.mul_succ, Nat.add_assoc]
  · rw [fl, h2.1, hf X yl hI.y1,
      show e + 1 - 1 = (e - 1) + 1 by omega, ghash_append16, ← hI.y]
  · rw [fcf, hr9, toNat_ofNat_lt (by omega), show e + 1 - 1 = e by omega]

/-- The first group, with nothing between its rounds. -/
theorem firstTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} {s : State}
    (hR : ReadyTo s₀ P s) : WP isa firstTo s (EInvTo s₀ P 1) := by
  have hd := hp.toD
  have h16 := hp.nb16
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ ZFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, ZFrame.refl _ _⟩
  refine WP.mono (batchTo_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 0) (j := 0) (by omega) hR.a
    (by rw [hR.rdx]) trivial) fun s₁ ⟨hA₁, _, hg₁, hl₁, hm₁⟩ => ?_
  have lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → ∀ l < 4, s₁.zlane r l = s.zlane r l :=
    fun r h13 h14 hr l hl => hl₁ r h13 h14 hr (by simp) l hl
  refine ⟨by simpa using hA₁, Nat.le_refl _, by rw [hg₁, hR.rdx]; simp, ?_, by rw [hg₁]; exact hR.rax,
    fun r h1 h2 h3 _ h5 => by rw [hg₁]; exact hR.gpr r h1 h2 h3 h5,
    fun k hk l hl => by rw [keepPTo hp (by omega) hm₁ hk hl]; exact hR.pw k hk l hl,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) l hl]; exact hR.m1 l hl,
    by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide), hR.y]; simp [ghashFrom],
    fun l h1 h4 => by rw [lk _ (by decide) (by decide) (by decide) l h4]; exact hR.y1 l h1 h4⟩
  rw [hg₁, hR.gpr _ (by decide) (by decide) (by decide) (by decide)]; simp

/-- `cmp r9, 32`. -/
theorem cmpE_ok {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (hI : EInvTo s₀ P e s) :
    WP isa (.block [.alu .cmp .r9 (.imm 32)]) s fun s' =>
      EInvTo s₀ P e s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e - 1) < 32)) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  have hr9 := hI.r9
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    hr9, e32, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨{ hI with a := { hI.a with } }, ?_⟩
  rw [toNat_ofNat_lt (by omega)]; rfl

/-! ## The stores -/

/-- The output, after all of it is encrypted. -/
theorem blocks_ctr32To {s₀ : State} {m : Mem} (hb : ∀ k < nb s₀, blockAt m (oAddr s₀ k) = ctbT s₀ k) :
    blocksAt m (op s₀) (nb s₀) = Spec.Gcm.ctr32 (ciph s₀) (cb s₀) (blocksAt s₀.mem (sp s₀) (nb s₀)) := by
  apply List.ext_getElem
  · simp [blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream]
  · intro k h₁ h₂
    have hk : k < nb s₀ := by simpa [blocksAt] using h₁
    simp only [blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream, List.getElem_map, List.getElem_range,
      List.getElem_zipWith, List.length_map, List.length_range]
    exact hb k hk

theorem finalTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {e : Nat} (he : nb s₀ = 16 * e) {s : State} (hI : EInvTo s₀ P e s) :
    WP isa (.block (storeCtr ++ lastG ++ storeY)) s (EPostTo s₀) := by
  have hw := hp.wrap_o
  have hwp := hp.wrap_p
  have h1e := hI.one
  have hm0 : s.lane .xmm0 0 = revMask := by rw [← State.zlane_lt2 _ _ (by decide)]; exact hI.a.msk 0 (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (store16Z_ok .xmm13 .xmm14 .rax s hm0 (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  have cD : ∀ k < nb s₀, Region.Disjoint ⟨oAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.o_c.sub_left (Offset.sub_base _ (by omega))
  have cP : ∀ k < 4, ∀ l < 4, Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l), 16⟩ (cR s₀) :=
    fun k hk l hl => hp.p_c.sub_left (Offset.sub_base _ (by omega))
  rw [hI.rax] at m₁
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctbT s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (op s₀).toNat + 256 * (e - 1) := hI.rdx
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [lastG, List.append_assoc]
  rw [WP.block_append_iff]
  have hE₂ : GEnv (dst s₀) 0 a X P s₁ :=
    { rdx := by rw [g₁]
      r11 := by rw [g₁]; exact hr11
      xs := fun i _ hi => by
        rw [m₁, show a + BitVec.ofNat 64 (16 * i) = oAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega),
          blockAt_writeW_sep' (cD _ (by omega)) rfl, hI.a.blocks _ (by omega)]
      pv := fun k hk l hl => by
        rw [m₁, Mem.readW_writeW_sep ((cP k hk l hl).sep (Region.contains_self _ _) (Region.contains_self _ _))
          (by decide)]
        exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [rd₁, wr₁, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (64 * k) = op s₀ + BitVec.ofNat 64 (256 * (e - 1) + 64 * k) from
            addr_eq (by omega)]
        exact in_rdwr (in_sub hp.o_in (by omega))
      inp := fun k hk => by
        rw [rd₁, wr₁, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := fun l hl => by rw [l₁ _ (by decide) l hl]; exact hI.a.msk l hl }
  refine WP.mono (ghRun_ok (yl := yl) 4 (Nat.le_refl _) s₁ hE₂
    (fun l hl => by rw [l₁ _ (by decide) l hl])) fun s₃ ⟨hE₃, p₃, _, f₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ghFin hE₃ (fun l hl => by
      rw [f₃.zlane _ (by decide) l hl, l₁ _ (by decide) l hl]; exact hI.m1 l hl))
    fun s₄ ⟨_, y4, _, f₄⟩ => ?_
  rw [p₃ (by decide) 0 (by decide), p₃ (by decide) 1 (by decide), p₃ (by decide) 2 (by decide),
    p₃ (by decide) 3 (by decide)] at y4
  have hm0₄ : s₄.lane .xmm0 0 = revMask := by
    rw [← State.zlane_lt2 _ _ (by decide), f₄.zlane _ (by decide) 0 (by decide), f₃.zlane _ (by decide) 0 (by decide),
      l₁ _ (by decide) 0 (by decide)]; exact hI.a.msk 0 (by decide)
  have g₄ : s₄.gpr = s.gpr := by rw [f₄.gpr, f₃.gpr, g₁]
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl,
    WP.block_append_iff]
  have hrcx : s.gpr .rcx = yp s₀ := hI.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)
  refine WP.mono (store16Z_ok .xmm2 .xmm2 .rcx s₄ hm0₄ (by
      rw [g₄, f₄.wr, f₃.wr, wr₁, hI.a.wr, hrcx]
      exact hp.y_in)) fun s₅ ⟨m₅, g₅, rd₅, wr₅, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [g₄, hrcx] at m₅
  have m₄ : s₄.mem = s₁.mem := by rw [f₄.mem, f₃.mem]
  rw [m₄, m₁] at m₅
  have yD : ∀ k < nb s₀, Region.Disjoint ⟨oAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.o_y.sub_left (Offset.sub_base _ (by omega))
  have hb : ∀ k < nb s₀, blockAt s₅.mem (oAddr s₀ k) = ctbT s₀ k := fun k hk => by
    rw [m₅, blockAt_writeW_sep' (yD k hk) rfl, blockAt_writeW_sep' (cD k hk) rfl]
    exact hI.a.blocks k (by omega)
  refine ⟨blocks_ctr32To hb, ?_, ?_, ?_, ?_, by
      show s₅.rd = _; rw [rd₅, f₄.rd, f₃.rd, rd₁, hI.a.rd], by
      show s₅.wr = _; rw [wr₅, f₄.wr, f₃.wr, wr₁, hI.a.wr]⟩
  · show blockAt s₅.mem (cp s₀) = _
    rw [m₅, blockAt_writeW_sep' hp.c_y rfl, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (by decide),
      hI.a.ctr 0 (by decide), Nat.add_zero, he]
  · show blockAt s₅.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s₅.mem (op s₀) (nb s₀))
    rw [show blocksAt s₅.mem (op s₀) (nb s₀) = (List.range (16 * e)).map (ctbT s₀) from by
        rw [← he]; simp only [blocksAt]
        exact List.map_congr_left fun k hk => hb k (by simpa using hk),
      m₅, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (by decide), y4]
    refine (hf X yl hI.y1).trans ?_
    rw [show 16 * e = 16 * ((e - 1) + 1) by congr 1; omega, ghash_append16]
    exact congrArg (fun y => ghashFrom (hk s₀) y ((List.range 16).map X)) hI.y
  · show Frame _ s₀.mem s₅.mem
    rw [m₅]
    exact ((hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := yR s₀) (by simp) _
      (Region.contains_self _ _)
  · intro r h1 h2 h3 h4 h5
    show s₅.gpr r = _
    rw [g₅, g₄]; exact hI.gpr r h1 h2 h3 h4 h5

end VG.Proof.Gcm.X86_64.StitchZTo
