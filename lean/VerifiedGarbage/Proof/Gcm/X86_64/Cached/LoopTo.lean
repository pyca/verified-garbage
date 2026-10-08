import VerifiedGarbage.Proof.Gcm.X86_64.Cached.AesTo
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop

/-! # Cached-key GCM groups with distinct input and output buffers -/

namespace VG.Proof.Gcm.X86_64.StitchZHTo
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
open VG.Impl.Gcm.X86_64.StitchZHTo (firstTo bodyTo)
open VG.Proof.Gcm.X86_64.StitchZTo hiding batchTo_ok bodyTo_ok firstTo_ok
open VG.Proof.Gcm.X86_64.StitchZH (gq_keeps)
open VG.Proof.Gcm.X86_64.Vpclmul (getLsbD_one8)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Proof.Aes.X86_64.VaesZ (four)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

theorem bodyTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {e : Nat} (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInvTo s₀ P e s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa bodyTo s fun s' => EInvTo s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  suffices h : WP isa bodyTo s fun s' => EInvTo s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) from
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
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hE₁ : GEnv (dst s₀) 0 a X P s := genv hp hI.a h1e (by omega) hI.rdx hr11 hI.pw
  have hrdx₁ : (s.gpr .rdx).toNat + 64 * 4 = (op s₀).toNat + 16 * (16 * e) := by
    show a.toNat + _ = _; omega
  -- The group, with the loads of the previous group after rounds 1–4 and the reduction after round 5.
  refine WP.seq (WP.mono (batchTo_ok hp gq gRegs gRegs_ok (QG (dst s₀) (fun _ => 0) a X P yl)
    (gq_ok (s₀ := dst s₀) (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.zero_le _))
    (fun j t t' h f => h.zframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hd (by omega) (by omega) ha (fun i _ hi => by omega) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 4) (by omega) hI.a hCache gq_keeps hrdx₁
    ⟨hE₁, hI.m1, by rw [ite_f (by decide)]; exact ⟨fun h => absurd h (by decide), fun l hl => rfl⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂, _⟩ => ?_)
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

theorem firstTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} {s : State}
    (hR : ReadyTo s₀ P s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) : WP isa firstTo s fun t => EInvTo s₀ P 1 t ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) t := by
  suffices h : WP isa firstTo s (EInvTo s₀ P 1) from
    WP.mono (WP.hkeepCode (by rfl) (by decide +kernel) h)
      (fun t ⟨hi, hh⟩ => ⟨hi, hCache.keep hh (hi.a.keys hp)⟩)

  have hd := hp.toD
  have h16 := hp.nb16
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ ZFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, ZFrame.refl _ _⟩
  refine WP.mono (batchTo_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 0) (j := 0) (by omega) hR.a hCache (fun _ => rfl)
    (by rw [hR.rdx]) trivial) fun s₁ ⟨hA₁, _, hg₁, hl₁, hm₁, _⟩ => ?_
  have lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → ∀ l < 4, s₁.zlane r l = s.zlane r l :=
    fun r h13 h14 hr l hl => hl₁ r h13 h14 hr (by simp) l hl
  refine ⟨by simpa using hA₁, Nat.le_refl _, by rw [hg₁, hR.rdx]; simp, ?_, by rw [hg₁]; exact hR.rax,
    fun r h1 h2 h3 _ h5 => by rw [hg₁]; exact hR.gpr r h1 h2 h3 h5,
    fun k hk l hl => by rw [keepPTo hp (by omega) hm₁ hk hl]; exact hR.pw k hk l hl,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) l hl]; exact hR.m1 l hl,
    by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide), hR.y]; simp [ghashFrom],
    fun l h1 h4 => by rw [lk _ (by decide) (by decide) (by decide) l h4]; exact hR.y1 l h1 h4⟩
  rw [hg₁, hR.gpr _ (by decide) (by decide) (by decide) (by decide)]; simp

end VG.Proof.Gcm.X86_64.StitchZHTo
