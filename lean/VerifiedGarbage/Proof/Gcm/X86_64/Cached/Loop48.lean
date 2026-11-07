module

import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop48
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
public import VerifiedGarbage.Proof.Framework.X86_64.HighKeep
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Keep
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # Cached-key GCM: the 48-block loops and their tails -/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH
open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Stitch (storeCtr storeY)
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost DPost nb nr kp pp cp yp cb dp dR pR cR yR bAddr blk ctb ciph
  sch hk y₀ ite_t ite_f addr_eq in_sub in_sub_int in_rdwr ghash_append16 ghash16)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB prod toNat_ofNat_lt ofNat_sub_ofNat ea_at)
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZ (gq gq48 tab lastG adv)
open VG.Impl.Gcm.X86_64.StitchZH (batch first body body48 bigRest dbody dbody48)
open VG.Proof.Gcm.X86_64.StitchZ hiding batch_ok body_ok first_ok dbody_ok bodyM_ok firstM_ok body48M_ok loop48M_ok
  bigRest_ok bigRestM_ok loopE_ok encTailG_ok dbody48_ok loopD48_ok bigDRest_ok loopD_ok decTailG_ok
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame run_sep Keys)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

theorem tail48_keeps :
    (Instr.vmovdqu32Load .xmm1 (at_ .r11 832) :: (lastG ++ adv ++ lastG ++ adv)).all Instr.keepsH = true := rfl

theorem body48_keeps (ld : Bool) : (body48 ld).all Instr.keepsH = true := by
  have h0 := batch_keeps 12 (gq48 0) (gq48_keeps 0) false ld
  have h1 := batch_keeps 16 (gq48 1) (gq48_keeps 1) false ld
  have h2 := batch_keeps 20 (gq48 2) (gq48_keeps 2) false ld
  simp_all [body48, Code.all, Instr.keepsH]

theorem body48M_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {T : Nat → Nat → Nat → Block}
    (hT : FinOk48 (hk s₀) T) {e : Nat} (he : 16 * (e + 5) ≤ nb s₀) {s : State} (hI : EInv3M ix s₀ T e s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (body48 ix) s fun s' => EInv3M ix s₀ T (e + 3) s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e + 2) < 96)) ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  suffices h : WP isa (body48 ix) s fun s' => EInv3M ix s₀ T (e + 3) s' ∧
      s'.cf = some (decide (nb s₀ - 16 * (e + 2) < 96)) from
    WP.mono (WP.hkeepCode (by rfl) (body48_keeps ix) h)
      (fun t ⟨⟨hi, hz⟩, hh⟩ => ⟨hi, hz, hCache.keep hh (hi.a.keys hp)⟩)

  have hw := hp.wrap_w
  have h1e := hI.one
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctb s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (Stitch.wp ix s₀).toNat + 256 * (e - 1) := hI.rdx
  have hE : GEnv48 s₀ 0 a X T s := genv48M hp hI
  let Q : Nat → Nat → State → Prop := QG48 s₀ (fun _ => 0) a X T yl
  have hgq : ∀ b < 3, ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → Q b j t →
      WP isa (.block (gq48 b j)) t fun t' => Q b (j + 1) t' ∧ ZFrame gRegs48 t t' := fun b hb =>
    gq48_ok hb (fun _ => Nat.le_refl _) (Nat.zero_le _) (Nat.zero_le _)
  have hq : ∀ b j t t', Q b j t → ZFrame (.xmm13 :: .xmm14 :: aregs) t t' → Q b j t' :=
    fun _ _ _ _ h f => h.zframe f (by decide)
  have hqx : ∀ b c, c + 16 ≤ nb s₀ → 16 * (e - 1) + 48 ≤ c → ∀ t t', Q b 10 t → t'.gpr = t.gpr → t'.rd = t.rd →
      t'.wr = t.wr → (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, t'.zlane r l = t.zlane r l) →
      Frame [⟨Stitch.wAddr ix s₀ c, 256⟩] t.mem t'.mem → Q b 10 t' :=
    fun _ _ hc hc' _ _ h hg hrd hwr hl hf =>
      QG48.keepW ha (fun i _ hi => Offset.disjoint _ (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith))
        (hp.w_p.symm.sub_right (Offset.sub_base _ (by omega_arith))) h hg hrd hwr hl hf
  have hQ₀ : Q 0 1 s := ⟨hE, by
    rw [ite_f (by decide)]; exact ⟨fun h => absurd h (by decide), fun _ _ _ => rfl⟩⟩
  have hr8 : ix = true → s.gpr .r8 = if ix then dp s₀ - Stitch.op s₀ else Stitch.op s₀ - dp s₀ := fun hi => by
    subst hi; exact hI.r8 rfl
  -- Group `e + 2`, hashing group `e - 1`.
  refine WP.seq (WP.mono (batchM_ok (st := false) (ld := ix) hp (by cases ix <;> rfl) id (gq48 0) gRegs48 gRegs48_ok
    (Q 0) (hgq 0 (by decide)) (hq 0)
    (hqx 0 _ (by omega_arith) (by omega_arith)) (c := 16 * (e + 2)) (j := 12) (by omega_arith) hI.a hCache
    (gq48_keeps 0) hr8 (by show a.toNat + _ = _; omega_arith) hQ₀) fun s₁ ⟨hA₁, hQ₁, hg₁, _, _, hCache₁⟩ => ?_)
  refine WP.seq (WP.mono (batchM_ok (st := false) (ld := ix) hp (by cases ix <;> rfl) id (gq48 1) gRegs48 gRegs48_ok
    (Q 1) (hgq 1 (by decide)) (hq 1)
    (hqx 1 _ (by omega_arith) (by omega_arith)) (c := 16 * (e + 2) + 16) (j := 16) (by omega_arith) hA₁ hCache₁
    (gq48_keeps 1) (fun hi => by rw [hg₁]; exact hr8 hi)
    (by rw [hg₁]; show a.toNat + _ = _; omega_arith) (hQ₁.next (by decide) (Nat.le_refl _)))
    fun s₂ ⟨hA₂, hQ₂, hg₂, _, _, hCache₂⟩ => ?_)
  refine WP.seq (WP.mono (batchM_ok (st := false) (ld := ix) hp (by cases ix <;> rfl) id (gq48 2) gRegs48 gRegs48_ok
    (Q 2) (hgq 2 (by decide)) (hq 2)
    (hqx 2 _ (by omega_arith) (by omega_arith)) (c := 16 * (e + 2) + 16 + 16) (j := 20) (by omega_arith) hA₂ hCache₂
    (gq48_keeps 2) (fun hi => by rw [hg₂, hg₁]; exact hr8 hi)
    (by rw [hg₂, hg₁]; show a.toNat + _ = _; omega_arith) (hQ₂.next (by decide) (Nat.le_refl _)))
    fun s₃ ⟨hA₃, hQ₃, hg₃, _, _, _⟩ => ?_)
  refine WP.mono (next48_ok s₃ 96 96 (by decide)) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨hE₃, h2⟩ := hQ₃
  rw [ite_t (by decide)] at h2
  have g₃ : s₃.gpr = s.gpr := by rw [hg₃, hg₂, hg₁]
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, g₃]
  have hr9 : s₃.gpr .r9 - 48 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 3 - 1)) := by
    rw [g₃, hI.r9, show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl, ofNat_sub_ofNat (by omega_arith) (by omega_arith)]
    congr 1; omega_arith
  refine ⟨⟨by rw [show 16 * (e + 3 + 2) = 16 * (e + 2) + 16 + 16 + 16 by omega_arith]; exact hA₃.gpr2 fg fl fm frd fwr,
    by omega_arith, ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun hi => by rw [gk _ (by decide) (by decide)]; exact hI.r8 hi,
    fun r h1 h2 h3 h4 h5 => by rw [gk r h2 h4]; exact hI.gpr r h1 h2 h3 h4 h5,
    fun g hg k hk l hl => by rw [fm]; exact hE₃.pv g hg k hk l hl, fun l hl => by rw [fm]; exact hE₃.pm l hl,
    ?_, fun l h1 h4 => by rw [fl]; exact h2.2 l h1 h4⟩, ?_⟩
  · rw [frdx, g₃, BitVec.toNat_add, show (768 : BitVec 64).toNat = 768 from rfl,
      Nat.mod_eq_of_lt (by show a.toNat + 768 < 2 ^ 64; omega_arith)]
    show a.toNat + 768 = _
    rw [ha, show e + 3 - 1 = (e - 1) + 3 by omega_arith]; omega_arith
  · rw [fl, h2.1, hT X yl hI.y1, show 16 * (e + 3 - 1) = 16 * (e - 1) + 48 by omega_arith, ghash_append48, ← hI.y]
  · rw [fcf, hr9, toNat_ofNat_lt (by omega_arith), show e + 3 - 1 = e + 2 by omega_arith]
    rfl

theorem loop48M_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {T : Nat → Nat → Nat → Block}
    (hT : FinOk48 (hk s₀) T) {s : State} (hI : EInv3M ix s₀ T 1 s) (h96 : 96 ≤ nb s₀)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.loop (body48 ix) .ae) s fun s' => ∃ e, nb s₀ - 16 * (e - 1) < 96 ∧ EInv3M ix s₀ T e s' ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 5) ≤ nb s₀ ∧ EInv3M ix s₀ T e s ∧
    VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s
  have hstep : ∀ m s, I m s → WP isa (body48 ix) s (fun s' =>
      (eval .ae s' = some false ∧ ∃ e, nb s₀ - 16 * (e - 1) < 96 ∧ EInv3M ix s₀ T e s' ∧
        VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s') ∨
      (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨e, rfl, he, hI, hCI⟩
    refine WP.mono (body48M_ok hp hT he hI hCI) fun s' ⟨hI', hcf', hCI'⟩ => ?_
    by_cases hlt : nb s₀ - 16 * (e + 2) < 96
    · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
        e + 3, by omega_arith, hI', hCI'⟩
    · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - 16 * (e + 3), by omega_arith, e + 3, rfl, by omega_arith, hI', hCI'⟩
  exact WP.loop (M := isa) I hstep (nb s₀ - 16 * 1) s ⟨1, rfl, by omega_arith, hI, hCache⟩

/-- `StitchZ.bigRestM_ok` with the round keys cached. -/
theorem bigRestM_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {P : Nat → Nat → Block}
    (hf : FinOk (hk s₀) P) {T : Nat → Nat → Nat → Block} (hT : FinOk48 (hk s₀) T) (hT2 : ∀ k l, T 2 k l = P k l)
    (h96 : 96 ≤ nb s₀) {s s₁ : State} (hI : EInvM ix s₀ P 1 s) (hA₁ : AInvM ix s₀ (16 * 1) s₁)
    (hv₁ : ∀ g < 3, ∀ k < 4, ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l)
    (hm₁ : ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) (hg₁ : s₁.gpr = s.gpr)
    (hl₁ : ∀ l < 4, s₁.zlane .xmm2 l = s.zlane .xmm2 l)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s₁) :
    WP isa (bigRest ix) s₁ fun s' => ∃ e, EInvM ix s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  have hw := hp.wrap_w
  have none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ ZFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, ZFrame.refl _ _⟩
  have hr8 : ix = true → s.gpr .r8 = if ix then dp s₀ - Stitch.op s₀ else Stitch.op s₀ - dp s₀ := fun hi => by
    subst hi; exact hI.r8 rfl
  unfold bigRest
  refine WP.seq (WP.mono (batchM_ok (st := false) (ld := ix) hp (by cases ix <;> rfl) id (fun _ => []) [] (by simp)
    (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 16 * 1) (j := 4) (by omega_arith) hA₁ hCache
    (fun _ => rfl) (fun hi => by rw [hg₁]; exact hr8 hi)
    (by have := hI.rdx; rw [hg₁]; omega_arith) trivial) fun s₂ ⟨hA₂, _, hg₂, hl₂, hf₂, hCache₂⟩ => ?_)
  obtain ⟨hv₂, hm₂⟩ := keepTM hp (by omega_arith) hf₂ hv₁ hm₁
  refine WP.seq (WP.mono (batchM_ok (st := false) (ld := ix) hp (by cases ix <;> rfl) id (fun _ => []) [] (by simp)
    (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 16 * 1 + 16) (j := 8) (by omega_arith) hA₂ hCache₂
    (fun _ => rfl) (fun hi => by rw [hg₂, hg₁]; exact hr8 hi)
    (by have := hI.rdx; rw [hg₂, hg₁]; omega_arith) trivial) fun s₃ ⟨hA₃, _, hg₃, hl₃, hf₃, hCache₃⟩ => ?_)
  obtain ⟨hv₃, hm₃⟩ := keepTM hp (by omega_arith) hf₃ hv₂ hm₂
  have g₃ : s₃.gpr = s.gpr := by rw [hg₃, hg₂, hg₁]
  have l₃ : ∀ l < 4, s₃.zlane .xmm2 l = s.zlane .xmm2 l := fun l hl => by
    rw [hl₃ _ (by decide) (by decide) (by decide) (by simp) l hl, hl₂ _ (by decide) (by decide) (by decide) (by simp) l hl,
      hl₁ l hl]
  have hI₃ : EInv3M ix s₀ T 1 s₃ :=
    ⟨hA₃, Nat.le_refl _, by rw [g₃]; exact hI.rdx, by rw [g₃]; exact hI.r9, by rw [g₃]; exact hI.rax,
      fun hi => by rw [g₃]; exact hI.r8 hi,
      fun r h1 h2 h3 h4 h5 => by rw [g₃]; exact hI.gpr r h1 h2 h3 h4 h5, hv₃, hm₃,
      by rw [l₃ 0 (by decide)]; exact hI.y, fun l h1 h4 => by rw [l₃ l h4]; exact hI.y1 l h1 h4⟩
  refine WP.seq (WP.mono (loop48M_ok hp hT hI₃ (by omega_arith) hCache₃) fun s₄ ⟨e, hex, hI₄, hCache₄⟩ => ?_)
  -- The reduction constant, and two of the three groups left to hash.
  exact WP.mono (WP.hkeep tail48_keeps (tail48M_ok hp hf hT2 hI₄))
    fun t ⟨⟨e', hI'⟩, hh⟩ => ⟨e', hI', hCache₄.keep hh (hI'.a.keys hp)⟩

theorem bigRest_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {T : Nat → Nat → Nat → Block} (hT : FinOk48 (hk s₀) T) (hT2 : ∀ k l, T 2 k l = P k l)
    (h96 : 96 ≤ nb s₀) {s s₁ : State} (hI : EInv s₀ P 1 s) (hA₁ : AInv s₀ (16 * 1) s₁)
    (hv₁ : ∀ g < 3, ∀ k < 4, ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l)
    (hm₁ : ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) (hg₁ : s₁.gpr = s.gpr)
    (hl₁ : ∀ l < 4, s₁.zlane .xmm2 l = s.zlane .xmm2 l)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s₁) :
    WP isa bigRest s₁ fun s' => ∃ e, EInv s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' :=
  WP.mono (bigRestM_ok (Stitch.SPre.toM hp) hf hT hT2 h96 hI.toM hA₁.toM hv₁ hm₁ hg₁ hl₁ hCache)
    fun _ ⟨e, h, hk⟩ => ⟨e, h.toEInv, hk⟩

/-- The loop of groups of sixteen, for any number of blocks: it stops with
fewer than 32 left, the last group still to hash. -/
theorem loopERM_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {e : Nat} {s : State} (hI : EInvM ix s₀ P e s) (hcf : s.cf = some (decide (nb s₀ - 16 * (e - 1) < 32)))
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.ite .b (.block []) (.loop (body ix) .ae)) s fun s' => ∃ e, nb s₀ - 16 * (e - 1) < 32 ∧
      EInvM ix s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  have h1e := hI.one
  have hle := hI.a.le
  refine WP.ite (decide (nb s₀ - 16 * (e - 1) < 32)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil ⟨e, by simpa using h, hI, hCache⟩
  · let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ EInvM ix s₀ P e s ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s
    have hstep : ∀ m s, I m s → WP isa (body ix) s (fun s' =>
        (eval .ae s' = some false ∧ ∃ e, nb s₀ - 16 * (e - 1) < 32 ∧ EInvM ix s₀ P e s' ∧
          VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s') ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨e, rfl, he, hI, hCI⟩
      refine WP.mono (bodyM_ok hp hf he hI hCI) fun s' ⟨hI', hcf', hCI'⟩ => ?_
      by_cases hlt : nb s₀ - 16 * e < 32
      · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
          e + 1, by simpa using hlt, hI', hCI'⟩
      · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
          nb s₀ - 16 * (e + 1), by have := hI.one; omega_arith, e + 1, rfl, by omega_arith, hI', hCI'⟩
    exact WP.loop (M := isa) I hstep (nb s₀ - 16 * e) s ⟨e, rfl, by simp at h; omega_arith, hI, hCache⟩

theorem loopER_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e : Nat}
    {s : State} (hI : EInv s₀ P e s) (hcf : s.cf = some (decide (nb s₀ - 16 * (e - 1) < 32)))
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.ite .b (.block []) (.loop body .ae)) s fun s' => ∃ e, nb s₀ - 16 * (e - 1) < 32 ∧
      EInv s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' :=
  WP.mono (loopERM_ok (Stitch.SPre.toM hp) hf hI.toM hcf hCache) fun _ ⟨e, he, h, hk⟩ => ⟨e, he, h.toEInv, hk⟩

theorem loopE_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e : Nat} {s : State}
    (hI : EInv s₀ P e s) (hcf : s.cf = some (decide (nb s₀ - 16 * (e - 1) < 32)))
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.ite .b (.block []) (.loop body .ae)) s fun s' => ∃ e, nb s₀ = 16 * e ∧ EInv s₀ P e s' :=
  WP.mono (loopER_ok hp hf hI hcf hCache) fun _ ⟨e, he, hI', _⟩ =>
    ⟨e, by have := hI'.a.le; have := hI'.one; omega_arith, hI'⟩

theorem dbody48_keeps (ix : Bool) : (dbody48 ix).all Instr.keepsH = true := by
  have h0 := batch_keeps 0 (gq48 0) (gq48_keeps 0) ix
  have h1 := batch_keeps 4 (gq48 1) (gq48_keeps 1) ix
  have h2 := batch_keeps 8 (gq48 2) (gq48_keeps 2) ix
  simp_all [dbody48, Code.all, Instr.keepsH]

theorem dbody48M_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {T : Nat → Nat → Nat → Block} (hT : FinOk48 (hk s₀) T) {e : Nat}
    (he : 16 * (e + 3) ≤ nb s₀) {s : State} (hI : DInv3M ix s₀ T e s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (dbody48 ix) s fun s' => DInv3M ix s₀ T (e + 3) s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e + 3) < 48)) ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  suffices h : WP isa (dbody48 ix) s fun s' => DInv3M ix s₀ T (e + 3) s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e + 3) < 48)) from
    WP.mono (WP.hkeepCode (by rfl) (dbody48_keeps ix) h)
      (fun t ⟨⟨hi, hz⟩, hh⟩ => ⟨hi, hz, hCache.keep hh (hi.a.keys hp)⟩)

  have hw := hp.wrap_d
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => blk s₀ (16 * e + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * e := by
    show (s.gpr .rdx).toNat = _
    rw [hI.rdx, BitVec.toNat_add, toNat_ofNat_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  have hE : GEnv48 s₀ 0 a X T s :=
    { rdx := rfl
      r11 := hI.gpr .r11 (by decide) (by decide) (fun _ => by decide) (by decide) (by decide)
      xs := fun i _ hi => by
        rw [show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * e + i) from addr_eq (by omega_arith),
          hI.a.src _ (by omega_arith) (by omega_arith)]
      pv := hI.pv
      pm := hI.pm
      ina := fun o ho => by
        rw [hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 o = dp s₀ + BitVec.ofNat 64 (256 * e + o) from addr_eq (by omega_arith)]
        exact in_sub hp.d_in (by omega_arith)
      inp := fun o ho => by
        rw [hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega_arith))
      m0 := hI.a.msk }
  let Q : Nat → Nat → State → Prop := fun b => QG48 s₀ (loD48 b) a X T yl b
  have hgq : ∀ b < 3, ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → Q b j t →
      WP isa (.block (gq48 b j)) t fun t' => Q b (j + 1) t' ∧ ZFrame gRegs48 t t' := fun b hb =>
    gq48_ok hb (fun j => by simp only [loD48]; split <;> split <;> omega_arith)
      (by simp only [loD48]; rw [ite_t (by decide)])
      (by simp only [loD48]; rw [ite_t (by decide)]; omega_arith)
  have hq : ∀ b j t t', Q b j t → ZFrame (.xmm13 :: .xmm14 :: aregs) t t' → Q b j t' :=
    fun _ _ _ _ h f => h.zframe f (by decide)
  have hqx : ∀ b, 16 * (e + b) + 16 ≤ nb s₀ → ∀ t t', Q b 10 t → t'.gpr = t.gpr → t'.rd = t.rd →
      t'.wr = t.wr → (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, t'.zlane r l = t.zlane r l) →
      Frame [⟨Stitch.wAddr ix s₀ (16 * (e + b)), 256⟩] t.mem t'.mem → Q b 10 t' :=
    fun b hc _ _ h hg hrd hwr hl hf =>
      QG48.keepM hp hc (g := e) (by omega_arith) ha (fun _ i hi _ => by
        simp only [loD48] at hi; rw [ite_f (by decide)] at hi; omega_arith) h hg hrd hwr hl hf
  have hnx : ∀ b, loD48 b 10 ≤ loD48 (b + 1) 1 := fun b => by
    simp only [loD48]; rw [ite_f (by decide), ite_t (by decide)]
  have hQ₀ : Q 0 1 s := ⟨hE.mono (Nat.zero_le _), by
    rw [ite_f (by decide)]; exact ⟨fun h => absurd h (by decide), fun _ _ _ => rfl⟩⟩
  -- Each group is hashed after rounds 1 and 3, before its blocks are decrypted.
  refine WP.seq (WP.mono (batchM_ok (ld := false) hp (by cases ix <;> rfl) (fun h => absurd h (by decide)) (gq48 0) gRegs48 gRegs48_ok (Q 0) (hgq 0 (by decide)) (hq 0)
    (hqx 0 (by omega_arith)) (c := 16 * (e + 0)) (j := 0) (by omega_arith) (by simpa using hI.a) hCache (gq48_keeps 0)
    hI.r8 (by show a.toNat + _ = (dp s₀).toNat + _; omega_arith) hQ₀) fun s₁ ⟨hA₁, hQ₁, hg₁, _, _, hCache₁⟩ => ?_)
  refine WP.seq (WP.mono (batchM_ok (ld := false) hp (by cases ix <;> rfl) (fun h => absurd h (by decide)) (gq48 1) gRegs48 gRegs48_ok (Q 1) (hgq 1 (by decide)) (hq 1)
    (hqx 1 (by omega_arith)) (c := 16 * (e + 1)) (j := 4) (by omega_arith)
    (by rw [show 16 * (e + 1) = 16 * (e + 0) + 16 by omega_arith]; exact hA₁) hCache₁ (gq48_keeps 1)
    (fun hi => by rw [hg₁]; exact hI.r8 hi) (by rw [hg₁]; show a.toNat + _ = (dp s₀).toNat + _; omega_arith) (hQ₁.next (by decide) (hnx 0)))
    fun s₂ ⟨hA₂, hQ₂, hg₂, _, _, hCache₂⟩ => ?_)
  refine WP.seq (WP.mono (batchM_ok (ld := false) hp (by cases ix <;> rfl) (fun h => absurd h (by decide)) (gq48 2) gRegs48 gRegs48_ok (Q 2) (hgq 2 (by decide)) (hq 2)
    (hqx 2 (by omega_arith)) (c := 16 * (e + 2)) (j := 8) (by omega_arith)
    (by rw [show 16 * (e + 2) = 16 * (e + 1) + 16 by omega_arith]; exact hA₂) hCache₂ (gq48_keeps 2)
    (fun hi => by rw [hg₂, hg₁]; exact hI.r8 hi) (by rw [hg₂, hg₁]; show a.toNat + _ = (dp s₀).toNat + _; omega_arith) (hQ₂.next (by decide) (hnx 1)))
    fun s₃ ⟨hA₃, hQ₃, hg₃, _, _, _⟩ => ?_)
  refine WP.mono (next48_ok s₃ 48 48 (by decide)) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨hE₃, h2⟩ := hQ₃
  rw [ite_t (by decide)] at h2
  have g₃ : s₃.gpr = s.gpr := by rw [hg₃, hg₂, hg₁]
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, g₃]
  have hr9 : s₃.gpr .r9 - 48 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 3)) := by
    rw [g₃, hI.r9, show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl, ofNat_sub_ofNat (by omega_arith) (by omega_arith)]
    congr 1
  refine ⟨⟨by rw [show 16 * (e + 3) = 16 * (e + 2) + 16 by omega_arith]; exact hA₃.gpr2 fg fl fm frd fwr,
    ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun hi => by rw [gk _ (by decide) (by decide)]; exact hI.r8 hi,
    fun r h1 h2 h3 h4 h5 => by rw [gk r h2 h4]; exact hI.gpr r h1 h2 h3 h4 h5,
    fun g hg k hk l hl => by rw [fm]; exact hE₃.pv g hg k hk l hl, fun l hl => by rw [fm]; exact hE₃.pm l hl,
    ?_, fun l h1 h4 => by rw [fl]; exact h2.2 l h1 h4⟩, ?_⟩
  · rw [frdx, g₃, hI.rdx, BitVec.add_assoc, show (768 : BitVec 64) = BitVec.ofNat 64 768 from rfl,
      ← BitVec.ofNat_add, show 256 * e + 768 = 256 * (e + 3) by omega_arith]
  · rw [fl, h2.1, hT X yl hI.y1, show 16 * (e + 3) = 16 * e + 48 by omega_arith, ghash_append48, ← hI.y]
  · rw [fcf, hr9, toNat_ofNat_lt (by omega_arith)]
    rfl

theorem loopD48M_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {T : Nat → Nat → Nat → Block} (hT : FinOk48 (hk s₀) T) {s : State}
    (hI : DInv3M ix s₀ T 0 s) (h48 : 48 ≤ nb s₀)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.loop (dbody48 ix) .ae) s fun s' => ∃ e, nb s₀ - 16 * e < 48 ∧ DInv3M ix s₀ T e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  suffices h : WP isa (.loop (dbody48 ix) .ae) s fun s' => ∃ e, nb s₀ - 16 * e < 48 ∧ DInv3M ix s₀ T e s' from
    WP.mono (WP.hkeepCode (by rfl) (by simpa [Code.all] using dbody48_keeps ix) h)
      (fun t ⟨⟨e, he, hi⟩, hh⟩ => ⟨e, he, hi, hCache.keep hh (hi.a.keys hp)⟩)

  let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 3) ≤ nb s₀ ∧ DInv3M ix s₀ T e s ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s
  have hstep : ∀ m s, I m s → WP isa (dbody48 ix) s (fun s' =>
      (eval .ae s' = some false ∧ ∃ e, nb s₀ - 16 * e < 48 ∧ DInv3M ix s₀ T e s') ∨
      (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨e, rfl, he, hI, hCI⟩
    refine WP.mono (dbody48M_ok hp hT he hI hCI) fun s' ⟨hI', hcf', hCI'⟩ => ?_
    by_cases hlt : nb s₀ - 16 * (e + 3) < 48
    · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
        e + 3, hlt, hI'⟩
    · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - 16 * (e + 3), by omega_arith, e + 3, rfl, by omega_arith, hI', hCI'⟩
  exact WP.loop (M := isa) I hstep (nb s₀) s ⟨0, by simp, by omega_arith, hI, hCache⟩

theorem bigDRestM_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {P : Nat → Nat → Block} {T : Nat → Nat → Nat → Block}
    (hT : FinOk48 (hk s₀) T) (hT2 : ∀ k l, T 2 k l = P k l) (h96 : 96 ≤ nb s₀) {s s₁ : State}
    (hI : DInvM ix s₀ P 0 s) (hA₁ : AInvM ix s₀ (16 * 0) s₁)
    (hv₁ : ∀ g < 3, ∀ k < 4, ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l)
    (hm₁ : ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) (hg₁ : s₁.gpr = s.gpr)
    (hl₁ : ∀ l < 4, s₁.zlane .xmm2 l = s.zlane .xmm2 l)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s₁) :
    WP isa (.seq (.loop (dbody48 ix) .ae) (.block [.vmovdqu32Load .xmm1 (at_ .r11 832)])) s₁
      fun s' => ∃ e, DInvM ix s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  suffices h : WP isa (.seq (.loop (dbody48 ix) .ae) (.block [.vmovdqu32Load .xmm1 (at_ .r11 832)])) s₁
      fun s' => ∃ e, DInvM ix s₀ P e s' from
    WP.mono (WP.hkeepCode (by rfl) (by simpa [Code.all, Instr.keepsH] using dbody48_keeps ix) h)
      (fun t ⟨⟨e, hi⟩, hh⟩ => ⟨e, hi, hCache.keep hh (hi.a.keys hp)⟩)

  have hI₁ : DInv3M ix s₀ T 0 s₁ :=
    ⟨hA₁, by rw [hg₁]; exact hI.rdx, by rw [hg₁]; exact hI.r9, by rw [hg₁]; exact hI.rax,
      fun hi => by rw [hg₁]; exact hI.r8 hi,
      fun r h1 h2 h3 h4 h5 => by rw [hg₁]; exact hI.gpr r h1 h2 h3 h4 h5, hv₁, hm₁,
      by rw [hl₁ 0 (by decide)]; exact hI.y, fun l h1 h4 => by rw [hl₁ l h4]; exact hI.y1 l h1 h4⟩
  refine WP.seq (WP.mono (loopD48M_ok hp hT hI₁ (by omega_arith) hCache) fun s₂ ⟨e, _, hI₂, _⟩ => ?_)
  have hr11₂ : s₂.gpr .r11 = pp s₀ := hI₂.gpr .r11 (by decide) (by decide) (fun _ => by decide) (by decide) (by decide)
  refine WP.mono (reloadM_ok hp s₂ hr11₂ hI₂.a.wr hI₂.pm) fun s₃ ⟨p₃, f₃⟩ => ⟨e, ?_⟩
  exact ⟨hI₂.a.zframe f₃ (by decide) (by decide) (by decide), by rw [f₃.gpr]; exact hI₂.rdx,
    by rw [f₃.gpr]; exact hI₂.r9, by rw [f₃.gpr]; exact hI₂.rax, fun hi => by rw [f₃.gpr]; exact hI₂.r8 hi,
    fun r h1 h2 h3 h4 h5 => by rw [f₃.gpr]; exact hI₂.gpr r h1 h2 h3 h4 h5,
    fun k hk l hl => by
      have h := hI₂.pv 2 (by decide) k hk l hl
      rw [show tab 2 + 64 * k + 16 * l = 64 * k + 16 * l by simp only [tab]; omega_arith] at h
      rw [f₃.mem, h, hT2],
    p₃, by rw [f₃.zlane _ (by decide) 0 (by decide)]; exact hI₂.y,
    fun l h1 h4 => by rw [f₃.zlane _ (by decide) l h4]; exact hI₂.y1 l h1 h4⟩

theorem dbody48_ok {s₀ : State} (hp : SPre s₀) {T : Nat → Nat → Nat → Block} (hT : FinOk48 (hk s₀) T) {e : Nat}
    (he : 16 * (e + 3) ≤ nb s₀) {s : State} (hI : DInv3 s₀ T e s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa dbody48 s fun s' => DInv3 s₀ T (e + 3) s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e + 3) < 48)) ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' :=
  WP.mono (dbody48M_ok (Stitch.SPre.toM hp) hT he hI.toM hCache) fun _ ⟨h, hc, hk⟩ => ⟨h.toDInv3, hc, hk⟩

theorem loopD48_ok {s₀ : State} (hp : SPre s₀) {T : Nat → Nat → Nat → Block} (hT : FinOk48 (hk s₀) T) {s : State}
    (hI : DInv3 s₀ T 0 s) (h48 : 48 ≤ nb s₀)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (.loop dbody48 .ae) s fun s' => ∃ e, nb s₀ - 16 * e < 48 ∧ DInv3 s₀ T e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' :=
  WP.mono (loopD48M_ok (Stitch.SPre.toM hp) hT hI.toM h48 hCache) fun _ ⟨e, he, h, hk⟩ => ⟨e, he, h.toDInv3, hk⟩

theorem bigDRest_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} {T : Nat → Nat → Nat → Block}
    (hT : FinOk48 (hk s₀) T) (hT2 : ∀ k l, T 2 k l = P k l) (h96 : 96 ≤ nb s₀) {s s₁ : State}
    (hI : DInv s₀ P 0 s) (hA₁ : AInv s₀ (16 * 0) s₁)
    (hv₁ : ∀ g < 3, ∀ k < 4, ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l)
    (hm₁ : ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) (hg₁ : s₁.gpr = s.gpr)
    (hl₁ : ∀ l < 4, s₁.zlane .xmm2 l = s.zlane .xmm2 l)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s₁) :
    WP isa (.seq (.loop dbody48 .ae) (.block [.vmovdqu32Load .xmm1 (at_ .r11 832)])) s₁
      fun s' => ∃ e, DInv s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' :=
  WP.mono (bigDRestM_ok (Stitch.SPre.toM hp) hT hT2 h96 hI.toM hA₁.toM hv₁ hm₁ hg₁ hl₁ hCache)
    fun _ ⟨e, h, hk⟩ => ⟨e, h.toDInv, hk⟩

end VG.Proof.Gcm.X86_64.StitchZH
