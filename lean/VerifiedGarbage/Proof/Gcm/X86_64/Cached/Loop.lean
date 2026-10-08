import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop

/-! # GCM groups with cached round keys -/

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost DPost StitchOk nb nr kp pp cp yp cb dp dR pR cR yR bAddr blk ctb ciph
  sch hk y₀ ite_t ite_f addr_eq in_sub in_sub_int in_rdwr ghash_append16 ghash16 blockAt_writeW_sep' blocks_ctr32)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Gcm.X86_64.StitchZ (gq ghLoad ord setupZ lastG fin)
open VG.Impl.Gcm.X86_64.StitchZH (batch body first dbody)
open VG.Proof.Gcm.X86_64.StitchZ hiding batch_ok body_ok first_ok dbody_ok
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame run_sep Keys)
open VG.Proof.Aes.X86_64.VaesZ (four)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

theorem body_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInv s₀ P e s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa body s fun s' => EInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  suffices h : WP isa body s fun s' => EInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) from
    WP.mono (WP.hkeepCode (by rfl) (by decide +kernel) h)
      (fun t ⟨⟨hi, hz⟩, hh⟩ => ⟨hi, hz, hCache.keep hh (hi.a.keys hp)⟩)

  have hw := hp.wrap_d
  have h1e := hI.one
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctb s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * (e - 1) := hI.rdx
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  have f₁ : ZFrame [.xmm8, .xmm9, .xmm10] s s := ZFrame.refl _ _
  have hE₁ : GEnv s₀ 0 a X P s :=
    { rdx := by rw [f₁.gpr]
      r11 := by rw [f₁.gpr, hr11]
      xs := fun i _ hi => by
        rw [f₁.mem, show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega),
          hI.a.blocks _ (by omega)]
        simp only [show 16 * (e - 1) + i < 16 * e by omega, ite_true]
        rfl
      pv := fun k hk l hl => by rw [f₁.mem]; exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (64 * k) = dp s₀ + BitVec.ofNat 64 (256 * (e - 1) + 64 * k) from
            addr_eq (by omega)]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inp := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := fun l hl => by rw [f₁.zlane _ (by decide) l hl]; exact hI.a.msk l hl }
  have hA₁ := hI.a.zframe f₁ (by decide) (by decide) (by decide)
  have hrdx₁ : (s.gpr .rdx).toNat + 64 * 4 = (dp s₀).toNat + 16 * (16 * e) := by
    rw [f₁.gpr]; show a.toNat + _ = _; omega
  -- The group, with the loads of the previous group after rounds 1–4 and the reduction after round 5.
  refine WP.seq (WP.mono (batch_ok hp gq gRegs gRegs_ok (QG s₀ (fun _ => 0) a X P yl)
    (gq_ok (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.zero_le _))
    (fun j t t' h f => h.zframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hp (by omega) (by omega) ha (fun i _ hi => by omega) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 4) (by omega) hA₁ hCache gq_keeps hrdx₁
    ⟨hE₁, fun l hl => by
      rw [f₁.zlane _ (by decide) l hl]; exact hI.m1 l hl,
      by rw [ite_f (by decide)]
         exact ⟨fun h => absurd h (by decide), fun l hl => by rw [f₁.zlane _ (by decide) l hl]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂, _⟩ => ?_)
  refine WP.mono (nextE_ok s₂) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, h1', h2⟩ := hQ₂
  rw [ite_t (by decide)] at h2
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₂, f₁.gpr]
  have hA' : AInv s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 16 by omega]
    exact ⟨hA₂.le, fun l hl => by rw [fl]; exact hA₂.ctr l hl, fun l hl => by rw [fl]; exact hA₂.msk l hl,
      fun l hl => by rw [fl]; exact hA₂.inc l hl,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₂.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.r10, by rw [fm]; exact hA₂.frame,
      fun k hk => by rw [fm]; exact hA₂.blocks k hk, by rw [frd]; exact hA₂.rd, by rw [fwr]; exact hA₂.wr⟩
  have hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1 - 1)) := by
    rw [hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega) (by omega)]
    congr 1; omega
  refine ⟨⟨hA', by omega, ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun k hk l hl => by rw [fm, keepP hp (by omega) hm₂ hk hl, f₁.mem]; exact hI.pw k hk l hl,
    fun l hl => by rw [fl]; exact h1' l hl, ?_,
    fun l h1 h4 => by rw [fl]; exact h2.2 l h1 h4⟩, ?_⟩
  · rw [frdx, hg₂, f₁.gpr, BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (by show a.toNat + 256 < 2 ^ 64; omega)]
    show a.toNat + 256 = _
    rw [ha, show e + 1 - 1 = (e - 1) + 1 by omega, Nat.mul_succ, Nat.add_assoc]
  · rw [fl, h2.1, hf X yl hI.y1,
      show e + 1 - 1 = (e - 1) + 1 by omega, ghash_append16, ← hI.y]
  · rw [fcf, hr9, toNat_ofNat_lt (by omega), show e + 1 - 1 = e by omega]

theorem first_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} {s : State} (hR : Ready s₀ P s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa first s fun t => EInv s₀ P 1 t ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) t := by
  suffices h : WP isa first s (EInv s₀ P 1) from
    WP.mono (WP.hkeepCode (by rfl) (by decide +kernel) h)
      (fun t ⟨hi, hh⟩ => ⟨hi, hCache.keep hh (hi.a.keys hp)⟩)

  have hwp := hp.wrap_p
  have hwd := hp.wrap_d
  have h16 := hp.nb16
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ ZFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, ZFrame.refl _ _⟩
  refine WP.mono (batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 0) (j := 0) (by omega) hR.a hCache (fun _ => rfl)
    (by rw [hR.rdx]) trivial) fun s₁ ⟨hA₁, _, hg₁, hl₁, hm₁, _⟩ => ?_
  have lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → ∀ l < 4, s₁.zlane r l = s.zlane r l :=
    fun r h13 h14 hr l hl => hl₁ r h13 h14 hr (by simp) l hl
  refine ⟨by simpa using hA₁, Nat.le_refl _, by rw [hg₁, hR.rdx]; simp, ?_, by rw [hg₁]; exact hR.rax,
    fun r h1 h2 _ h4 => by rw [hg₁]; exact hR.gpr r h1 h2 h4,
    fun k hk l hl => by rw [keepP hp (by omega) hm₁ hk hl]; exact hR.pw k hk l hl,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) l hl]; exact hR.m1 l hl,
    by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide), hR.y]; simp [ghashFrom],
    fun l h1 h4 => by rw [lk _ (by decide) (by decide) (by decide) l h4]; exact hR.y1 l h1 h4⟩
  rw [hg₁, hR.gpr _ (by decide) (by decide) (by decide)]; simp

theorem dbody_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : DInv s₀ P e s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa dbody s fun s' => DInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e + 1) < 16)) ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  suffices h : WP isa dbody s fun s' => DInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e + 1) < 16)) from
    WP.mono (WP.hkeepCode (by rfl) (by decide +kernel) h)
      (fun t ⟨⟨hi, hz⟩, hh⟩ => ⟨hi, hz, hCache.keep hh (hi.a.keys hp)⟩)

  have hw := hp.wrap_d
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => blk s₀ (16 * e + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * e := by
    show (s.gpr .rdx).toNat = _
    rw [hI.rdx, BitVec.toNat_add, toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  have f₁ : ZFrame [.xmm8, .xmm9, .xmm10] s s := ZFrame.refl _ _
  have hE₁ : GEnv s₀ 0 a X P s :=
    { rdx := by rw [f₁.gpr]
      r11 := by rw [f₁.gpr, hr11]
      xs := fun i _ hi => by
        rw [f₁.mem, show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * e + i) from addr_eq (by omega),
          hI.a.blocks _ (by omega)]
        simp only [show ¬ 16 * e + i < 16 * e by omega, ite_false]
        rfl
      pv := fun k hk l hl => by rw [f₁.mem]; exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (64 * k) = dp s₀ + BitVec.ofNat 64 (256 * e + 64 * k) from addr_eq (by omega)]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inp := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := fun l hl => by rw [f₁.zlane _ (by decide) l hl]; exact hI.a.msk l hl }
  have hA₁ := hI.a.zframe f₁ (by decide) (by decide) (by decide)
  -- The group is hashed after rounds 1–4, before its blocks are decrypted, and reduced after round 5.
  refine WP.seq (WP.mono (batch_ok hp gq gRegs gRegs_ok (QG s₀ loD a X P yl)
    (gq_ok (fun j => by simp only [loD]; split <;> split <;> omega) (fun j hj1 hj4 => by
      simp only [loD, show j < 5 by omega, ite_true]; exact Nat.zero_le _))
    (fun j t t' h f => h.zframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hp (by omega) (by omega) ha
      (fun i hi _ => by have : 16 ≤ i := hi; omega) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 0) (by omega) hA₁ hCache gq_keeps (by rw [f₁.gpr]; show a.toNat + _ = _; omega)
    ⟨hE₁, fun l hl => by
      rw [f₁.zlane _ (by decide) l hl]; exact hI.m1 l hl,
      by rw [ite_f (by decide)]
         exact ⟨fun h => absurd h (by decide), fun l hl => by rw [f₁.zlane _ (by decide) l hl]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂, _⟩ => ?_)
  refine WP.mono (nextD_ok s₂) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, h1', h2⟩ := hQ₂
  rw [ite_t (by decide)] at h2
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₂, f₁.gpr]
  have hA' : AInv s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 16 by omega]
    exact ⟨hA₂.le, fun l hl => by rw [fl]; exact hA₂.ctr l hl, fun l hl => by rw [fl]; exact hA₂.msk l hl,
      fun l hl => by rw [fl]; exact hA₂.inc l hl,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₂.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.r10, by rw [fm]; exact hA₂.frame,
      fun k hk => by rw [fm]; exact hA₂.blocks k hk, by rw [frd]; exact hA₂.rd, by rw [fwr]; exact hA₂.wr⟩
  have hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1)) := by
    rw [hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega) (by omega)]
    congr 1
  refine ⟨⟨hA', ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun k hk l hl => by rw [fm, keepP hp (by omega) hm₂ hk hl, f₁.mem]; exact hI.pw k hk l hl,
    fun l hl => by rw [fl]; exact h1' l hl, ?_,
    fun l h1 h4 => by rw [fl]; exact h2.2 l h1 h4⟩, ?_⟩
  · rw [frdx, hg₂, f₁.gpr, hI.rdx, BitVec.add_assoc, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl,
      ← BitVec.ofNat_add, Nat.mul_succ]
  · rw [fl, h2.1]
    refine (hf X yl hI.y1).trans ?_
    rw [ghash_append16]
    exact congrArg (fun y => ghashFrom (hk s₀) y ((List.range 16).map X)) hI.y
  · rw [fcf, hr9, toNat_ofNat_lt (by omega)]

end VG.Proof.Gcm.X86_64.StitchZH
