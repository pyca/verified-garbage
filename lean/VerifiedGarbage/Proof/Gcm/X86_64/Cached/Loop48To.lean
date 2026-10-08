import VerifiedGarbage.Proof.Gcm.X86_64.Cached.LoopTo
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop48

/-! # Cached-key GCM: the 48-block loops and their tails -/

namespace VG.Proof.Gcm.X86_64.StitchZHTo
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
open VG.Impl.Gcm.X86_64.StitchZHTo (batchTo bodyTo body48To bigRestTo firstTo)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

open VG.Proof.Gcm.X86_64.StitchZTo hiding batchTo_ok bodyTo_ok firstTo_ok body48To_ok loop48To_ok bigRestTo_ok loopETo_ok encTailGTo_ok
open VG.Proof.Gcm.X86_64.StitchZH (gq48_keeps)

theorem body48To_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {T : Nat → Nat → Nat → Block}
    (hT : FinOk48 (hk s₀) T) {e : Nat} (he : 16 * (e + 5) ≤ nb s₀) {s : State} (hI : EInv3To s₀ T e s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa body48To s fun s' => EInv3To s₀ T (e + 3) s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e + 2) < 96)) ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  suffices h : WP isa body48To s fun s' => EInv3To s₀ T (e + 3) s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e + 2) < 96)) from
    WP.mono (WP.hkeepCode (by rfl) (by decide +kernel) h)
      (fun t ⟨⟨hi, hz⟩, hh⟩ => ⟨hi, hz, hCache.keep hh (hi.a.keys hp)⟩)

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
    (hqx 0 _ (by omega) (by omega)) (c := 16 * (e + 2)) (j := 12) (by omega) hI.a hCache (gq48_keeps 0)
    (by show a.toNat + _ = _; omega) hQ₀) fun s₁ ⟨hA₁, hQ₁, hg₁, _, _, hCache₁⟩ => ?_)
  refine WP.seq (WP.mono (batchTo_ok hp (gq48 1) gRegs48 gRegs48_ok (Q 1) (hgq 1 (by decide)) (hq 1)
    (hqx 1 _ (by omega) (by omega)) (c := 16 * (e + 2) + 16) (j := 16) (by omega) hA₁ hCache₁ (gq48_keeps 1)
    (by rw [hg₁]; show a.toNat + _ = _; omega) (hQ₁.next (by decide) (Nat.le_refl _)))
    fun s₂ ⟨hA₂, hQ₂, hg₂, _, _, hCache₂⟩ => ?_)
  refine WP.seq (WP.mono (batchTo_ok hp (gq48 2) gRegs48 gRegs48_ok (Q 2) (hgq 2 (by decide)) (hq 2)
    (hqx 2 _ (by omega) (by omega)) (c := 16 * (e + 2) + 16 + 16) (j := 20) (by omega) hA₂ hCache₂ (gq48_keeps 2)
    (by rw [hg₂, hg₁]; show a.toNat + _ = _; omega) (hQ₂.next (by decide) (Nat.le_refl _)))
    fun s₃ ⟨hA₃, hQ₃, hg₃, _, _, _⟩ => ?_)
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
    (hT : FinOk48 (hk s₀) T) {s : State} (hI : EInv3To s₀ T 1 s) (h96 : 96 ≤ nb s₀)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.loop body48To .ae) s fun s' => ∃ e, nb s₀ - 16 * (e - 1) < 96 ∧ EInv3To s₀ T e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  suffices h : WP isa (.loop body48To .ae) s fun s' => ∃ e, nb s₀ - 16 * (e - 1) < 96 ∧ EInv3To s₀ T e s' from
    WP.mono (WP.hkeepCode (by rfl) (by decide +kernel) h)
      (fun t ⟨⟨e, he, hi⟩, hh⟩ => ⟨e, he, hi, hCache.keep hh (hi.a.keys hp)⟩)

  have hm := hp.nbm
  let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 5) ≤ nb s₀ ∧ EInv3To s₀ T e s ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s
  have hstep : ∀ m s, I m s → WP isa body48To s (fun s' =>
      (eval .ae s' = some false ∧ ∃ e, nb s₀ - 16 * (e - 1) < 96 ∧ EInv3To s₀ T e s') ∨
      (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨e, rfl, he, hI, hCI⟩
    refine WP.mono (body48To_ok hp hT he hI hCI) fun s' ⟨hI', hcf', hCI'⟩ => ?_
    by_cases hlt : nb s₀ - 16 * (e + 2) < 96
    · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
        e + 3, by omega, hI'⟩
    · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - 16 * (e + 3), by omega, e + 3, rfl, by omega, hI', hCI'⟩
  exact WP.loop (M := isa) I hstep (nb s₀ - 16 * 1) s ⟨1, rfl, by omega, hI, hCache⟩

theorem bigRestTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {T : Nat → Nat → Nat → Block} (hT : FinOk48 (hk s₀) T) (hT2 : ∀ k l, T 2 k l = P k l)
    (h256 : 256 ≤ nb s₀) {s s₁ : State} (hI : EInvTo s₀ P 1 s) (hA₁ : AInvTo s₀ (16 * 1) s₁)
    (hv₁ : ∀ g < 3, ∀ k < 4, ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l)
    (hm₁ : ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) (hg₁ : s₁.gpr = s.gpr)
    (hl₁ : ∀ l < 4, s₁.zlane .xmm2 l = s.zlane .xmm2 l)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s₁) :
    WP isa bigRestTo s₁ fun s' => ∃ e, EInvTo s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  suffices h : WP isa bigRestTo s₁ fun s' => ∃ e, EInvTo s₀ P e s' from
    WP.mono (WP.hkeepCode (by rfl) (by decide +kernel) h)
      (fun t ⟨⟨e, hi⟩, hh⟩ => ⟨e, hi, hCache.keep hh (hi.a.keys hp)⟩)

  have none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ ZFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, ZFrame.refl _ _⟩
  refine WP.seq (WP.mono (batchTo_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 16 * 1) (j := 4) (by omega) hA₁ hCache (fun _ => rfl)
    (by have := hI.rdx; rw [hg₁]; omega) trivial) fun s₂ ⟨hA₂, _, hg₂, hl₂, hf₂, hCache₂⟩ => ?_)
  obtain ⟨hv₂, hm₂⟩ := keepTTo hp (by omega) hf₂ hv₁ hm₁
  refine WP.seq (WP.mono (batchTo_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 16 * 1 + 16) (j := 8) (by omega) hA₂ hCache₂ (fun _ => rfl)
    (by have := hI.rdx; rw [hg₂, hg₁]; omega) trivial) fun s₃ ⟨hA₃, _, hg₃, hl₃, hf₃, hCache₃⟩ => ?_)
  obtain ⟨hv₃, hm₃⟩ := keepTTo hp (by omega) hf₃ hv₂ hm₂
  have g₃ : s₃.gpr = s.gpr := by rw [hg₃, hg₂, hg₁]
  have l₃ : ∀ l < 4, s₃.zlane .xmm2 l = s.zlane .xmm2 l := fun l hl => by
    rw [hl₃ _ (by decide) (by decide) (by decide) (by simp) l hl, hl₂ _ (by decide) (by decide) (by decide) (by simp) l hl,
      hl₁ l hl]
  have hI₃ : EInv3To s₀ T 1 s₃ :=
    ⟨hA₃, Nat.le_refl _, by rw [g₃]; exact hI.rdx, by rw [g₃]; exact hI.r9, by rw [g₃]; exact hI.rax,
      fun r h1 h2 h3 h4 h5 => by rw [g₃]; exact hI.gpr r h1 h2 h3 h4 h5, hv₃, hm₃,
      by rw [l₃ 0 (by decide)]; exact hI.y, fun l h1 h4 => by rw [l₃ l h4]; exact hI.y1 l h1 h4⟩
  refine WP.seq (WP.mono (loop48To_ok hp hT hI₃ (by omega) hCache₃) fun s₄ ⟨e, hex, hI₄, _⟩ => ?_)
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

theorem loopETo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {e : Nat} {s : State} (hI : EInvTo s₀ P e s) (hcf : s.cf = some (decide (nb s₀ - 16 * (e - 1) < 32)))
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.ite .b (.block []) (.loop bodyTo .ae)) s fun s' => ∃ e, nb s₀ = 16 * e ∧ EInvTo s₀ P e s' := by
  have hm := hp.nbm
  have h1e := hI.one
  have hle := hI.a.le
  have fin : ∀ e, nb s₀ - 16 * (e - 1) < 32 → ∀ t, EInvTo s₀ P e t → ∃ e, nb s₀ = 16 * e ∧ EInvTo s₀ P e t :=
    fun e he t hI => ⟨e, by have := hI.a.le; have := hI.one; omega, hI⟩
  refine WP.ite (decide (nb s₀ - 16 * (e - 1) < 32)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil (fin e (by simpa using h) s hI)
  · let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ EInvTo s₀ P e s ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s
    have hstep : ∀ m s, I m s → WP isa bodyTo s (fun s' =>
        (eval .ae s' = some false ∧ ∃ e, nb s₀ = 16 * e ∧ EInvTo s₀ P e s') ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨e, rfl, he, hI, hCI⟩
      refine WP.mono (bodyTo_ok hp hf he hI hCI) fun s' ⟨hI', hcf', hCI'⟩ => ?_
      by_cases hlt : nb s₀ - 16 * e < 32
      · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
          fin (e + 1) (by simpa using hlt) s' hI'⟩
      · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
          nb s₀ - 16 * (e + 1), by have := hI.one; omega, e + 1, rfl, by omega, hI', hCI'⟩
    exact WP.loop (M := isa) I hstep (nb s₀ - 16 * e) s ⟨e, rfl, by simp at h; omega, hI, hCache⟩

theorem encTailGTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {bigC : Prog isa} (hbig : ∀ s, 256 ≤ nb s₀ → EInvTo s₀ P 1 s → VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s → WP isa bigC s fun s' => ∃ e, EInvTo s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s')
    {s : State} (hR : ReadyTo s₀ P s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.seq firstTo (.seq (.block [.alu .cmp .r9 (.imm 256)]) (.seq (.ite .b (.block []) bigC)
      (.seq (.block [.alu .cmp .r9 (.imm 32)])
        (.seq (.ite .b (.block []) (.loop bodyTo .ae)) (.block (storeCtr ++ lastG ++ storeY))))))) s (EPostTo s₀) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.seq (WP.mono (firstTo_ok hp hR hCache) fun s₂ ⟨hI₂, hCache₂⟩ => ?_)
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp_ok s₂ 256 256 (by decide))) fun s₃ ⟨⟨hcf, g, l, m, rd, wr⟩, hh⟩ => ?_)
  have hI₃ := hI₂.of_eq g l m rd wr
  have hCache₃ := hCache₂.keep hh (hI₃.a.keys hp)
  rw [hI₂.r9, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by decide)] at hcf
  refine WP.seq (WP.mono (WP.ite (Q := fun s' => ∃ e, EInvTo s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s') (decide (nb s₀ - 16 * (1 - 1) < 256))
    (by simp only [eval, hcf]) (fun _ => WP.block_nil ⟨1, hI₃, hCache₃⟩)
    (fun h => hbig _ (by simp at h; omega) hI₃ hCache₃)) fun s₄ ⟨e, hI₄, hCache₄⟩ => ?_)
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmpE_ok hI₄)) fun s₅ ⟨⟨hI₅, hcf₅⟩, hh₅⟩ => ?_)
  exact WP.seq (WP.mono (loopETo_ok hp hf hI₅ hcf₅ (hCache₄.keep hh₅ (hI₅.a.keys hp))) fun s₆ ⟨e, he, hI₆⟩ => finalTo_ok hp hf he hI₆)

end VG.Proof.Gcm.X86_64.StitchZHTo
