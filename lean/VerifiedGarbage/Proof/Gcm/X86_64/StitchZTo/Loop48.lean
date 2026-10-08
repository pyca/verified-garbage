import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop48

/-!
# The out-of-place AVX-512 loop: 48 blocks at a time

As `StitchZ/Loop48.lean` does in place. `body48To_ok`: three groups
encrypted (`batchTo_ok`) while the output of the three before them is hashed
between their rounds (`StitchZ.gq48_ok`, kept by the output written:
`StitchZ.QG48.data`, for the in-place view `dst s₀`), with one reduction
(`EInv3To`, which `bigRestTo_ok` starts from `EInvTo` after the first group,
the tables of 48 blocks and two more groups, and ends by hashing two of the
three groups left one at a time, back to `EInvTo`). `encTailGTo_ok` is the
loop after the setup, for any code `bigC` of 256 blocks on that ends in
`EInvTo` (`bigTo_ok`, and `bigPTo_ok` in `StitchZTo/LoopP.lean`).
-/

namespace VG.Proof.Gcm.X86_64.StitchZTo

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Stitch (storeCtr storeY)
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo EPostTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch hk y₀
  dp dR pR cR yR bAddr addr_eq in_sub in_sub_int in_rdwr ite_t ite_f ghash_append16)
open VG.Proof.Gcm.X86_64.StitchZ (GEnv GEnv48 QG48 gRegs48 gRegs48_ok gq48_ok QG48.data QG48.next keepW T48
  FinOk FinOk48 ghRun_ok ghFin adv_ok next48_ok cmp_ok reload_ok ghash_append48 pw16 pow48_ok)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZ (gq48 pow48 lastG adv tab)
open VG.Impl.Gcm.X86_64.StitchZTo (batchTo bodyTo body48To bigRestTo bigTo firstTo)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-! ## Hashing one group at a time -/

/-- The encryption state with `c` blocks encrypted and the first `e - 1`
groups hashed: `EInvTo` when `c = 16 e`. -/
structure EGenTo (s₀ : State) (P : Nat → Nat → Block) (e c : Nat) (s : State) : Prop where
  a : AInvTo s₀ c s
  one : 1 ≤ e
  ec : 16 * e ≤ c
  rdx : (s.gpr .rdx).toNat = (op s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 4, s.zlane .xmm1 l = poly
  y : s.zlane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map (ctbT s₀))
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

/-- Group `e - 1` hashed (after the loop of three groups: `lastG`). -/
theorem lastGTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {e c : Nat} {s : State} (hI : EGenTo s₀ P e c s) :
    WP isa (.block lastG) s fun s' =>
      s'.zlane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (ctbT s₀)) ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧
      ZFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2] s s' := by
  have h1e := hI.one
  let X : Nat → Block := fun i => ctbT s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have hE : GEnv (dst s₀) 0 (s.gpr .rdx) X P s :=
    genv hp hI.a h1e hI.ec hI.rdx (hI.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)) hI.pw
  rw [lastG, WP.block_append_iff]
  refine WP.mono (ghRun_ok (yl := yl) 4 (Nat.le_refl _) s hE (fun _ _ => rfl)) fun s₃ ⟨hE₃, p₃, _, f₃⟩ => ?_
  refine WP.mono (ghFin hE₃ (fun l hl => by rw [f₃.zlane _ (by decide) l hl]; exact hI.m1 l hl))
    fun s₄ ⟨_, y4, y1, f₄⟩ => ⟨?_, y1, (f₃.comp f₄).mono (by decide)⟩
  rw [y4, p₃ (by decide) 0 (by decide), p₃ (by decide) 1 (by decide), p₃ (by decide) 2 (by decide),
    p₃ (by decide) 3 (by decide)]
  refine (hf X yl hI.y1).trans ?_
  rw [show 16 * e = 16 * ((e - 1) + 1) by congr 1; omega, ghash_append16]
  exact congrArg (fun y => ghashFrom (hk s₀) y ((List.range 16).map X)) hI.y

/-- Group `e - 1` hashed, and the next. -/
theorem drainStepTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {e c : Nat} (hc : 16 * (e + 1) ≤ c) {s : State} (hI : EGenTo s₀ P e c s) :
    WP isa (.block (lastG ++ adv)) s (EGenTo s₀ P (e + 1) c) := by
  have hw := hp.wrap_o
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hcn := hI.a.le
  have h1e := hI.one
  rw [WP.block_append_iff]
  refine WP.mono (lastGTo_ok hp hf hI) fun s₁ ⟨y₁, y1₁, f₁⟩ => ?_
  refine WP.mono (adv_ok s₁) fun s' ⟨frdx, fr9, fg, fl, fm, frd, fwr⟩ => ?_
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, f₁.gpr]
  refine ⟨(hI.a.zframe f₁ (by decide) (by decide) (by decide)).gpr2 fg fl fm frd fwr, by omega, hc, ?_, ?_,
    by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 h5 => by rw [gk r h2 h4]; exact hI.gpr r h1 h2 h3 h4 h5,
    fun k hk l hl => by rw [fm, f₁.mem]; exact hI.pw k hk l hl,
    fun l hl => by rw [fl, f₁.zlane _ (by decide) l hl]; exact hI.m1 l hl,
    by rw [fl, y₁, show e + 1 - 1 = e by omega], fun l h1 h4 => by rw [fl]; exact y1₁ l h1 h4⟩
  · rw [frdx, f₁.gpr, BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (by rw [hI.rdx]; omega), hI.rdx, show e + 1 - 1 = (e - 1) + 1 by omega, Nat.mul_succ,
      Nat.add_assoc]
  · rw [fr9, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega) (by omega)]
    congr 1; omega

theorem EGenTo.einv {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (h : EGenTo s₀ P e (16 * e) s) :
    EInvTo s₀ P e s :=
  ⟨h.a, h.one, h.rdx, h.r9, h.rax, h.gpr, h.pw, h.m1, h.y, h.y1⟩

/-! ## The loop of three groups -/

/-- `e + 2` groups encrypted, the first `e - 1` hashed, the powers of 48
blocks and the reduction constant in the working space; `rdx` points to
output group `e - 1`, the first of the three to hash. -/
structure EInv3To (s₀ : State) (T : Nat → Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInvTo s₀ (16 * (e + 2)) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (op s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pv : ∀ g < 3, ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l
  pm : ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly
  y : s.zlane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map (ctbT s₀))
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

theorem body48To_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {T : Nat → Nat → Nat → Block}
    (hT : FinOk48 (hk s₀) T) {e : Nat} (he : 16 * (e + 5) ≤ nb s₀) {s : State} (hI : EInv3To s₀ T e s) :
    WP isa body48To s fun s' => EInv3To s₀ T (e + 3) s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e + 2) < 96)) := by
  have hd := hp.toD
  have hnb := nb_dst s₀
  have hw := hp.wrap_o
  have h1e := hI.one
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctbT s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (op s₀).toNat + 256 * (e - 1) := hI.rdx
  have hE : GEnv48 (dst s₀) 0 a X T s :=
    { rdx := rfl
      r11 := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
      xs := fun i _ hi => by
        rw [show a + BitVec.ofNat 64 (16 * i) = oAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega),
          hI.a.blocks _ (by omega)]
      pv := hI.pv
      pm := hI.pm
      ina := fun o ho => by
        rw [hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 o = op s₀ + BitVec.ofNat 64 (256 * (e - 1) + o) from addr_eq (by omega)]
        exact in_rdwr (in_sub hp.o_in (by omega))
      inp := fun o ho => by
        rw [hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := hI.a.msk }
  let Q : Nat → Nat → State → Prop := QG48 (dst s₀) (fun _ => 0) a X T yl
  have hgq : ∀ b < 3, ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → Q b j t →
      WP isa (.block (gq48 b j)) t fun t' => Q b (j + 1) t' ∧ ZFrame gRegs48 t t' := fun b hb =>
    gq48_ok (s₀ := dst s₀) hb (fun _ => Nat.le_refl _) (Nat.zero_le _) (Nat.zero_le _)
  have hq : ∀ b j t t', Q b j t → ZFrame (.xmm13 :: .xmm14 :: aregs) t t' → Q b j t' :=
    fun _ _ _ _ h f => h.zframe f (by decide)
  have hqx : ∀ b c, c + 16 ≤ nb s₀ → 16 * (e - 1) + 48 ≤ c → ∀ t t', Q b 10 t → t'.gpr = t.gpr → t'.rd = t.rd →
      t'.wr = t.wr → (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, t'.zlane r l = t.zlane r l) →
      Frame [⟨oAddr s₀ c, 256⟩] t.mem t'.mem → Q b 10 t' :=
    fun _ _ hc hc' _ _ h hg hrd hwr hl hf =>
      QG48.data hd (by omega) (g := e - 1) (by omega) ha (fun i _ hi => by omega) h hg hrd hwr hl hf
  have hQ₀ : Q 0 1 s := ⟨hE, by
    rw [ite_f (by decide)]; exact ⟨fun h => absurd h (by decide), fun _ _ _ => rfl⟩⟩
  -- Group `e + 2`, hashing group `e - 1`.
  refine WP.seq (WP.mono (batchTo_ok hp (gq48 0) gRegs48 gRegs48_ok (Q 0) (hgq 0 (by decide)) (hq 0)
    (hqx 0 _ (by omega) (by omega)) (c := 16 * (e + 2)) (j := 12) (by omega) hI.a
    (by show a.toNat + _ = _; omega) hQ₀) fun s₁ ⟨hA₁, hQ₁, hg₁, _, _⟩ => ?_)
  refine WP.seq (WP.mono (batchTo_ok hp (gq48 1) gRegs48 gRegs48_ok (Q 1) (hgq 1 (by decide)) (hq 1)
    (hqx 1 _ (by omega) (by omega)) (c := 16 * (e + 2) + 16) (j := 16) (by omega) hA₁
    (by rw [hg₁]; show a.toNat + _ = _; omega) (hQ₁.next (by decide) (Nat.le_refl _)))
    fun s₂ ⟨hA₂, hQ₂, hg₂, _, _⟩ => ?_)
  refine WP.seq (WP.mono (batchTo_ok hp (gq48 2) gRegs48 gRegs48_ok (Q 2) (hgq 2 (by decide)) (hq 2)
    (hqx 2 _ (by omega) (by omega)) (c := 16 * (e + 2) + 16 + 16) (j := 20) (by omega) hA₂
    (by rw [hg₂, hg₁]; show a.toNat + _ = _; omega) (hQ₂.next (by decide) (Nat.le_refl _)))
    fun s₃ ⟨hA₃, hQ₃, hg₃, _, _⟩ => ?_)
  refine WP.mono (next48_ok s₃ 96 96 (by decide)) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨hE₃, h2⟩ := hQ₃
  rw [ite_t (by decide)] at h2
  have g₃ : s₃.gpr = s.gpr := by rw [hg₃, hg₂, hg₁]
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, g₃]
  have hr9 : s₃.gpr .r9 - 48 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 3 - 1)) := by
    rw [g₃, hI.r9, show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl, ofNat_sub_ofNat (by omega) (by omega)]
    congr 1; omega
  refine ⟨⟨by rw [show 16 * (e + 3 + 2) = 16 * (e + 2) + 16 + 16 + 16 by omega]; exact hA₃.gpr2 fg fl fm frd fwr,
    by omega, ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 h5 => by rw [gk r h2 h4]; exact hI.gpr r h1 h2 h3 h4 h5,
    fun g hg k hk l hl => by rw [fm]; exact hE₃.pv g hg k hk l hl, fun l hl => by rw [fm]; exact hE₃.pm l hl,
    ?_, fun l h1 h4 => by rw [fl]; exact h2.2 l h1 h4⟩, ?_⟩
  · rw [frdx, g₃, BitVec.toNat_add, show (768 : BitVec 64).toNat = 768 from rfl,
      Nat.mod_eq_of_lt (by show a.toNat + 768 < 2 ^ 64; omega)]
    show a.toNat + 768 = _
    rw [ha, show e + 3 - 1 = (e - 1) + 3 by omega]; omega
  · rw [fl, h2.1, hT X yl hI.y1, show 16 * (e + 3 - 1) = 16 * (e - 1) + 48 by omega, ghash_append48, ← hI.y]
  · rw [fcf, hr9, toNat_ofNat_lt (by omega), show e + 3 - 1 = e + 2 by omega]
    rfl

theorem loop48To_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {T : Nat → Nat → Nat → Block}
    (hT : FinOk48 (hk s₀) T) {s : State} (hI : EInv3To s₀ T 1 s) (h96 : 96 ≤ nb s₀) :
    WP isa (.loop body48To .ae) s fun s' => ∃ e, nb s₀ - 16 * (e - 1) < 96 ∧ EInv3To s₀ T e s' := by
  have hm := hp.nbm
  let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 5) ≤ nb s₀ ∧ EInv3To s₀ T e s
  have hstep : ∀ m s, I m s → WP isa body48To s (fun s' =>
      (eval .ae s' = some false ∧ ∃ e, nb s₀ - 16 * (e - 1) < 96 ∧ EInv3To s₀ T e s') ∨
      (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨e, rfl, he, hI⟩
    refine WP.mono (body48To_ok hp hT he hI) fun s' ⟨hI', hcf'⟩ => ?_
    by_cases hlt : nb s₀ - 16 * (e + 2) < 96
    · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
        e + 3, by omega, hI'⟩
    · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - 16 * (e + 3), by omega, e + 3, rfl, by omega, hI'⟩
  exact WP.loop (M := isa) I hstep (nb s₀ - 16 * 1) s ⟨1, rfl, by omega, hI⟩

/-! ## The tables of 48 blocks -/

/-- The encryption state kept by writes to the working space alone. -/
theorem AInvTo.pow {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {c : Nat} {s s' : State} (h : AInvTo s₀ c s)
    (hf : Frame [pR s₀] s.mem s'.mem) (hg : s'.gpr = s.gpr) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hl : ∀ r, r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 → r ≠ .xmm12 → ∀ l < 4,
      s'.zlane r l = s.zlane r l) : AInvTo s₀ c s' := by
  have hw := hp.wrap_o
  have k : ∀ r ∈ ([.xmm14, .xmm0, .xmm15] : List XReg), ∀ l < 4, s'.zlane r l = s.zlane r l := by
    intro r hr l hl'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hl _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl'
  refine ⟨h.le, fun l hl' => by rw [k _ (by decide) l hl']; exact h.ctr l hl',
    fun l hl' => by rw [k _ (by decide) l hl']; exact h.msk l hl',
    fun l hl' => by rw [k _ (by decide) l hl']; exact h.inc l hl',
    by rw [hg]; exact h.rdi, by rw [hg]; exact h.rsi, by rw [hg]; exact h.r10, by rw [hg]; exact h.r8,
    h.frame.trans (hf.sub fun r hr => ⟨pR s₀, by simp, fun a ha => by
      simp only [List.mem_singleton] at hr; subst hr; exact ha⟩),
    fun k hk => ?_, by rw [hrd]; exact h.rd, by rw [hwr]; exact h.wr⟩
  rw [blockAt_frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.o_p.sub_left (Offset.sub_base _ (by have := h.le; omega))]
  exact h.blocks k hk

/-- `pow48`, from the sixteen powers `P` in the working space. -/
theorem powSetupTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} {c : Nat} {s : State}
    (hA : AInvTo s₀ c s) (hr11 : s.gpr .r11 = pp s₀)
    (hpw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l)
    (h1 : ∀ l < 4, s.zlane .xmm1 l = poly) :
    WP isa (.block pow48) s fun s' => AInvTo s₀ c s' ∧
      (∀ g < 3, ∀ k < 4, ∀ l < 4, s'.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T48 P g k l) ∧
      (∀ l < 4, s'.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 → r ≠ .xmm12 → ∀ l < 4,
        s'.zlane r l = s.zlane r l) := by
  refine WP.mono (pow48_ok s (by rw [hr11, hA.wr]; exact hp.p_in) h1)
    fun s' ⟨t0, t1, t2, tm, fr, g, rd, wr, x⟩ => ?_
  rw [hr11] at t0 t1 t2 tm fr
  have pw : ∀ k < 4, ∀ l < 4, pw16 s k l = P k l := fun k hk l hl => by
    show s.mem.readW (s.gpr .r11 + _) 128 = _; rw [hr11]; exact hpw k hk l hl
  refine ⟨hA.pow hp fr g rd wr x, fun g' hg' k hk l hl => ?_, tm, g, x⟩
  rcases (by omega : g' = 0 ∨ g' = 1 ∨ g' = 2) with rfl | rfl | rfl
  · rw [show tab 0 + 64 * k + 16 * l = 512 + 64 * k + 16 * l from rfl, t2 k hk l hl, pw k hk l hl,
      pw 0 (by decide) 0 (by decide)]
    simp only [T48, Nat.reduceEqDiff, ↓reduceIte]
  · rw [show tab 1 + 64 * k + 16 * l = 256 + 64 * k + 16 * l from rfl, t1 k hk l hl, pw k hk l hl,
      pw 0 (by decide) 0 (by decide)]
    simp only [T48, Nat.reduceEqDiff, ↓reduceIte]
  · rw [show tab 2 + 64 * k + 16 * l = 64 * k + 16 * l by simp only [tab]; omega, t0 k hk l hl, pw k hk l hl]
    simp only [T48, ↓reduceIte]

/-- The tables kept by the output written. -/
theorem keepTTo {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {T : Nat → Nat → Nat → Block} {c : Nat}
    (hc : c + 16 ≤ nb s₀) {m m' : Mem} (hf : Frame [⟨oAddr s₀ c, 256⟩] m m')
    (hv : ∀ g < 3, ∀ k < 4, ∀ l < 4, m.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l)
    (hm : ∀ l < 4, m.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) :
    (∀ g < 3, ∀ k < 4, ∀ l < 4, m'.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l) ∧
    (∀ l < 4, m'.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) :=
  have kw : ∀ {o}, o + 16 ≤ 1024 → m'.readW (pp s₀ + BitVec.ofNat 64 o) 128 = m.readW (pp s₀ + BitVec.ofNat 64 o) 128 :=
    fun ho => keepW hp.toD hc hf ho
  ⟨fun g hg k hk l hl => by rw [kw (by simp only [tab]; omega)]; exact hv g hg k hk l hl,
    fun l hl => by rw [kw (by omega)]; exact hm l hl⟩

/-! ## From 256 blocks on -/

/-- What `bigTo` does after the tables: the next two groups, the loop, and
two of the three groups left to hash, for any tables `T` whose last is `P`. -/
theorem bigRestTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {T : Nat → Nat → Nat → Block} (hT : FinOk48 (hk s₀) T) (hT2 : ∀ k l, T 2 k l = P k l)
    (h256 : 256 ≤ nb s₀) {s s₁ : State} (hI : EInvTo s₀ P 1 s) (hA₁ : AInvTo s₀ (16 * 1) s₁)
    (hv₁ : ∀ g < 3, ∀ k < 4, ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l)
    (hm₁ : ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) (hg₁ : s₁.gpr = s.gpr)
    (hl₁ : ∀ l < 4, s₁.zlane .xmm2 l = s.zlane .xmm2 l) :
    WP isa bigRestTo s₁ fun s' => ∃ e, EInvTo s₀ P e s' := by
  have none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ ZFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, ZFrame.refl _ _⟩
  refine WP.seq (WP.mono (batchTo_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 16 * 1) (j := 4) (by omega) hA₁
    (by have := hI.rdx; rw [hg₁]; omega) trivial) fun s₂ ⟨hA₂, _, hg₂, hl₂, hf₂⟩ => ?_)
  obtain ⟨hv₂, hm₂⟩ := keepTTo hp (by omega) hf₂ hv₁ hm₁
  refine WP.seq (WP.mono (batchTo_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 16 * 1 + 16) (j := 8) (by omega) hA₂
    (by have := hI.rdx; rw [hg₂, hg₁]; omega) trivial) fun s₃ ⟨hA₃, _, hg₃, hl₃, hf₃⟩ => ?_)
  obtain ⟨hv₃, hm₃⟩ := keepTTo hp (by omega) hf₃ hv₂ hm₂
  have g₃ : s₃.gpr = s.gpr := by rw [hg₃, hg₂, hg₁]
  have l₃ : ∀ l < 4, s₃.zlane .xmm2 l = s.zlane .xmm2 l := fun l hl => by
    rw [hl₃ _ (by decide) (by decide) (by decide) (by simp) l hl, hl₂ _ (by decide) (by decide) (by decide) (by simp) l hl,
      hl₁ l hl]
  have hI₃ : EInv3To s₀ T 1 s₃ :=
    ⟨hA₃, Nat.le_refl _, by rw [g₃]; exact hI.rdx, by rw [g₃]; exact hI.r9, by rw [g₃]; exact hI.rax,
      fun r h1 h2 h3 h4 h5 => by rw [g₃]; exact hI.gpr r h1 h2 h3 h4 h5, hv₃, hm₃,
      by rw [l₃ 0 (by decide)]; exact hI.y, fun l h1 h4 => by rw [l₃ l h4]; exact hI.y1 l h1 h4⟩
  refine WP.seq (WP.mono (loop48To_ok hp hT hI₃ (by omega)) fun s₄ ⟨e, hex, hI₄⟩ => ?_)
  -- The reduction constant, and two of the three groups left to hash.
  have h1e := hI₄.one
  have hr11₄ : s₄.gpr .r11 = pp s₀ := hI₄.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (reload_ok hp.toD s₄ hr11₄ hI₄.a.wr hI₄.pm) fun s₅ ⟨p₅, f₅⟩ => ?_
  have hG : EGenTo s₀ P e (16 * (e + 2)) s₅ :=
    ⟨hI₄.a.zframe f₅ (by decide) (by decide) (by decide), h1e, by omega, by rw [f₅.gpr]; exact hI₄.rdx,
      by rw [f₅.gpr]; exact hI₄.r9, by rw [f₅.gpr]; exact hI₄.rax,
      fun r h1 h2 h3 h4 h5 => by rw [f₅.gpr]; exact hI₄.gpr r h1 h2 h3 h4 h5,
      fun k hk l hl => by
        have h := hI₄.pv 2 (by decide) k hk l hl
        rw [show tab 2 + 64 * k + 16 * l = 64 * k + 16 * l by simp only [tab]; omega] at h
        rw [f₅.mem, h, hT2],
      p₅, by rw [f₅.zlane _ (by decide) 0 (by decide)]; exact hI₄.y,
      fun l h1 h4 => by rw [f₅.zlane _ (by decide) l h4]; exact hI₄.y1 l h1 h4⟩
  rw [List.append_assoc (lastG ++ adv) lastG adv, WP.block_append_iff]
  refine WP.mono (drainStepTo_ok hp hf (by omega) hG) fun s₆ hG₆ => ?_
  refine WP.mono (drainStepTo_ok hp hf (by omega) hG₆) fun s₇ hG₇ => ⟨e + 1 + 1, ?_⟩
  exact EGenTo.einv (by rw [show 16 * (e + 1 + 1) = 16 * (e + 2) by omega]; exact hG₇)

/-- `bigTo`: from the first group encrypted to all but up to two groups, all
but the last encrypted group hashed. -/
theorem bigTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hT : FinOk48 (hk s₀) (T48 P)) (h256 : 256 ≤ nb s₀) {s : State} (hI : EInvTo s₀ P 1 s) :
    WP isa bigTo s fun s' => ∃ e, EInvTo s₀ P e s' := by
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
  exact WP.seq (WP.mono (powSetupTo_ok hp (c := 16 * 1) hI.a hr11 hI.pw hI.m1)
    fun s₁ ⟨hA₁, hv₁, hm₁, hg₁, hl₁⟩ => bigRestTo_ok hp hf hT (fun k l => by simp only [T48, ↓reduceIte]) h256 hI
      hA₁ hv₁ hm₁ hg₁ fun l hl => hl₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl)

theorem EInvTo.of_eq {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s s' : State} (h : EInvTo s₀ P e s)
    (hg : s'.gpr = s.gpr) (hl : ∀ r l, s'.zlane r l = s.zlane r l) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : EInvTo s₀ P e s' :=
  ⟨h.a.gpr2 (fun r _ _ => by rw [hg]) hl hm hrd hwr, h.one, by rw [hg]; exact h.rdx, by rw [hg]; exact h.r9,
    by rw [hg]; exact h.rax, fun r h1 h2 h3 h4 h5 => by rw [hg]; exact h.gpr r h1 h2 h3 h4 h5,
    fun k hk l hl' => by rw [hm]; exact h.pw k hk l hl', fun l hl' => by rw [hl]; exact h.m1 l hl',
    by rw [hl]; exact h.y, fun l h1 h4 => by rw [hl]; exact h.y1 l h1 h4⟩

/-- The loop of one group, from any number of groups encrypted. -/
theorem loopETo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {e : Nat} {s : State} (hI : EInvTo s₀ P e s) (hcf : s.cf = some (decide (nb s₀ - 16 * (e - 1) < 32))) :
    WP isa (.ite .b (.block []) (.loop bodyTo .ae)) s fun s' => ∃ e, nb s₀ = 16 * e ∧ EInvTo s₀ P e s' := by
  have hm := hp.nbm
  have h1e := hI.one
  have hle := hI.a.le
  have fin : ∀ e, nb s₀ - 16 * (e - 1) < 32 → ∀ t, EInvTo s₀ P e t → ∃ e, nb s₀ = 16 * e ∧ EInvTo s₀ P e t :=
    fun e he t hI => ⟨e, by have := hI.a.le; have := hI.one; omega, hI⟩
  refine WP.ite (decide (nb s₀ - 16 * (e - 1) < 32)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil (fin e (by simpa using h) s hI)
  · let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ EInvTo s₀ P e s
    have hstep : ∀ m s, I m s → WP isa bodyTo s (fun s' =>
        (eval .ae s' = some false ∧ ∃ e, nb s₀ = 16 * e ∧ EInvTo s₀ P e s') ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨e, rfl, he, hI⟩
      refine WP.mono (bodyTo_ok hp hf he hI) fun s' ⟨hI', hcf'⟩ => ?_
      by_cases hlt : nb s₀ - 16 * e < 32
      · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
          fin (e + 1) (by simpa using hlt) s' hI'⟩
      · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
          nb s₀ - 16 * (e + 1), by have := hI.one; omega, e + 1, rfl, by omega, hI'⟩
    exact WP.loop (M := isa) I hstep (nb s₀ - 16 * e) s ⟨e, rfl, by simp at h; omega, hI⟩

/-- The encryption after the setup, for any code `bigC` of 256 blocks on. -/
theorem encTailGTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {bigC : Prog isa} (hbig : ∀ s, 256 ≤ nb s₀ → EInvTo s₀ P 1 s → WP isa bigC s fun s' => ∃ e, EInvTo s₀ P e s')
    {s : State} (hR : ReadyTo s₀ P s) :
    WP isa (.seq firstTo (.seq (.block [.alu .cmp .r9 (.imm 256)]) (.seq (.ite .b (.block []) bigC)
      (.seq (.block [.alu .cmp .r9 (.imm 32)])
        (.seq (.ite .b (.block []) (.loop bodyTo .ae)) (.block (storeCtr ++ lastG ++ storeY))))))) s (EPostTo s₀) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.seq (WP.mono (firstTo_ok hp hR) fun s₂ hI₂ => ?_)
  refine WP.seq (WP.mono (cmp_ok s₂ 256 256 (by decide)) fun s₃ ⟨hcf, g, l, m, rd, wr⟩ => ?_)
  have hI₃ := hI₂.of_eq g l m rd wr
  rw [hI₂.r9, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by decide)] at hcf
  refine WP.seq (WP.mono (WP.ite (Q := fun s' => ∃ e, EInvTo s₀ P e s') (decide (nb s₀ - 16 * (1 - 1) < 256))
    (by simp only [eval, hcf]) (fun _ => WP.block_nil ⟨1, hI₃⟩)
    (fun h => hbig _ (by simp at h; omega) hI₃)) fun s₄ ⟨e, hI₄⟩ => ?_)
  refine WP.seq (WP.mono (cmpE_ok hI₄) fun s₅ ⟨hI₅, hcf₅⟩ => ?_)
  exact WP.seq (WP.mono (loopETo_ok hp hf hI₅ hcf₅) fun s₆ ⟨e, he, hI₆⟩ => finalTo_ok hp hf he hI₆)

end VG.Proof.Gcm.X86_64.StitchZTo
