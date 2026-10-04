import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Loop

/-!
# Interleaved counter mode and GHASH in AVX: decryption

`DInv s₀ P e s`: `e` groups are decrypted (`AInv`) and hashed into `Y` (the
blocks as they were: the ciphertext); `rdx` points to group `e`. `dbody_ok`:
a body hashes group `e` while it decrypts it (`group_ok`), each batch
reading its own four blocks during its rounds, before it overwrites them.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.StitchAvx (aregs group ordD dbody dec)
open VG.Impl.Gcm.X86_64.Stitch (storeCtr storeY)
open VG.Proof.Gcm.X86_64.Stitch (SPre DPost nr cp yp dp nb pp cR yR dR pR hk y₀ bAddr blk ctb addr_eq
  ghash_append16 nextD_ok store16_ok blocks_ctr32 blockAt_writeW_sep')
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

structure DInv (s₀ : State) (P : Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInv s₀ (16 * e) s
  rdx : s.gpr .rdx = dp s₀ + BitVec.ofNat 64 (256 * e)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * e)
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 16, s.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 = P k
  m1 : s.lane .xmm1 0 = poly
  y : s.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (blk s₀))

/-- Which blocks of the group the GHASH loads to come still read: before
round 5 of batch `b`, its own and those after; then those after. -/
abbrev loD (b j : Nat) : Nat := if j < 5 then 4 * b else 4 * b + 4

theorem ordD_ok : ∀ b < 4, ∀ j, 1 ≤ j → j ≤ 4 → ordD (4 * b + j - 1) < 16 ∧ loD b j ≤ ordD (4 * b + j - 1) := by
  intro b hb j h1 h4
  simp only [ordD, loD, show j < 5 by omega, ite_true]
  constructor <;> split <;> (try split) <;> omega

theorem dbody_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Block} (hf : FinOk ordD (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : DInv s₀ P e s) :
    WP isa dbody s fun s' => DInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e + 1) < 16)) := by
  have hw := hp.wrap_d
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  have ha : a.toNat = (dp s₀).toNat + 256 * e := by
    show (s.gpr .rdx).toNat = _
    rw [hI.rdx, BitVec.toNat_add, toNat_ofNat' (by omega), Nat.mod_eq_of_lt (by omega)]
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (zero_ok s) fun s₁ ⟨z₁, f₁⟩ => ?_)
  have hA₁ := hI.a.yframe f₁ (by decide) (by decide) (by decide)
  have hE₁ := genv_of (P := P) hp hA₁ (g := e) (by omega) ha (by rw [f₁.gpr]) (by rw [f₁.gpr, hr11])
    (fun k hk => by rw [f₁.mem]; exact hI.pw k hk)
  let X : Nat → Block := fun i => blockAt s₁.mem (bAddr s₀ (16 * e + i))
  have hX : ∀ i < 16, X i = blk s₀ (16 * e + i) := fun i hi => by
    simp only [X]; rw [hA₁.blocks _ (by omega)]; simp only [show ¬ 16 * e + i < 16 * e by omega, ite_false]
  refine WP.seq (WP.mono (group_ok (lo := loD) (y := s.lane .xmm2 0) hp
    (fun b j => by simp only [loD]; split <;> split <;> omega)
    (fun b => by simp only [loD, show ¬ (10 < 5) by decide, show 1 < 5 by decide, ite_false, ite_true]; omega)
    ordD_ok
    (fun b _ i hi _ => by simp only [loD, show ¬ (10 < 5) by decide, ite_false] at hi; omega)
    (by omega) (by omega) ha hA₁ (j := 0)
    (by rw [f₁.gpr]; show a.toNat + _ = _; omega)
    ⟨hE₁, by rw [f₁.lane _ (by decide) 0 (by decide)]; exact hI.m1,
      by rw [ite_f (by decide)]; exact ⟨z₁, by rw [f₁.lane _ (by decide) 0 (by decide)]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  refine WP.mono (nextD_ok s₂) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, h1₂, h2⟩ := hQ₂
  rw [ite_t ⟨rfl, by decide⟩] at h2
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₂, f₁.gpr]
  have hA' : AInv s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 16 by omega]
    exact ⟨hA₂.le, by rw [fl]; exact hA₂.ctr, by rw [fl]; exact hA₂.msk, by rw [fl]; exact hA₂.inc,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₂.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.r10, by rw [fm]; exact hA₂.frame,
      fun k hk => by rw [fm]; exact hA₂.blocks k hk, by rw [frd]; exact hA₂.rd, by rw [fwr]; exact hA₂.wr⟩
  have hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1)) := by
    rw [hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  refine ⟨⟨hA', ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun k hk => by rw [fm, keepP hp (by omega) hm₂ hk, f₁.mem]; exact hI.pw k hk,
    by rw [fl]; exact h1₂, ?_⟩, ?_⟩
  · rw [frdx, hg₂, f₁.gpr, hI.rdx, BitVec.add_assoc, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl,
      ← BitVec.ofNat_add, Nat.mul_succ]
  · rw [fl, h2]
    refine (hf _ _).trans ?_
    rw [ghash_append16, ← hI.y]
    exact congrArg _ (List.map_congr_left fun i hi => hX i (List.mem_range.mp hi))
  · rw [fcf, hr9, toNat_ofNat' (by omega)]

theorem dfinal_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Block} {e : Nat} (he : nb s₀ = 16 * e) {s : State}
    (hI : DInv s₀ P e s) : WP isa (.block (storeCtr ++ storeY)) s (DPost s₀) := by
  have hw := hp.wrap_d
  have hm0 : s.lane .xmm0 0 = revMask := hI.a.msk
  rw [WP.block_append_iff]
  refine WP.mono (store16_ok .xmm13 .xmm14 .rax s hm0 (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  rw [hI.rax] at m₁
  have hrcx : s.gpr .rcx = yp s₀ := hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl, WP.block_append_iff]
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx s₁ (by rw [l₁ _ (by decide) 0 (by decide)]; exact hm0)
      (by rw [g₁, wr₁, hI.a.wr, hrcx]; exact hp.y_in)) fun s₂ ⟨m₂, g₂, rd₂, wr₂, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [g₁, hrcx, m₁, l₁ _ (by decide) 0 (by decide)] at m₂
  have cD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega))
  have yD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega))
  have hb : ∀ k < nb s₀, blockAt s₂.mem (bAddr s₀ k) = ctb s₀ k := fun k hk => by
    rw [m₂, blockAt_writeW_sep' (yD k hk) rfl, blockAt_writeW_sep' (cD k hk) rfl, hI.a.blocks k hk]
    simp only [show k < 16 * e by omega, ite_true]
  refine ⟨blocks_ctr32 hb, ?_, ?_, ?_, ?_, by show s₂.rd = _; rw [rd₂, rd₁, hI.a.rd],
    by show s₂.wr = _; rw [wr₂, wr₁, hI.a.wr]⟩
  · show blockAt s₂.mem (cp s₀) = _
    rw [m₂, blockAt_writeW_sep' hp.c_y rfl, VG.Proof.Gcm.X86_64.blockAt_store, hI.a.ctr, he]
  · show blockAt s₂.mem (yp s₀) = _
    rw [m₂, VG.Proof.Gcm.X86_64.blockAt_store, hI.y, he]
    rfl
  · show Frame _ s₀.mem s₂.mem
    rw [m₂]
    exact ((hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := yR s₀) (by simp) _
      (Region.contains_self _ _)
  · intro r h1 h2 h3 h4
    show s₂.gpr r = _
    rw [g₂, g₁]; exact hI.gpr r h1 h2 h3 h4

/-- The decryption after the setup. -/
theorem decTail_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Block} (hf : FinOk ordD (hk s₀) P) {s : State}
    (hR : Ready s₀ P s) :
    WP isa (.seq (.loop dbody .ae) (.block (storeCtr ++ storeY))) s (DPost s₀) := by
  have hm := hp.nbm
  have h16 := hp.nb16
  have hI₁ : DInv s₀ P 0 s :=
    ⟨hR.a, by rw [hR.rdx]; simp, by rw [hR.gpr _ (by decide) (by decide) (by decide)]; simp, hR.rax,
      fun r h1 h2 _ h4 => hR.gpr r h1 h2 h4, hR.pw, hR.m1, by rw [hR.y]; simp [ghashFrom]⟩
  let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ DInv s₀ P e s
  have hstep : ∀ m s, I m s → WP isa dbody s (fun s' =>
      (eval .ae s' = some false ∧ ∃ e, nb s₀ = 16 * e ∧ DInv s₀ P e s') ∨
      (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨e, rfl, he, hI⟩
    refine WP.mono (dbody_ok hp hf he hI) fun s' ⟨hI', hcf'⟩ => ?_
    by_cases hlt : nb s₀ - 16 * (e + 1) < 16
    · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
        e + 1, by omega, hI'⟩
    · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - 16 * (e + 1), by omega, e + 1, rfl, by omega, hI'⟩
  exact WP.seq (WP.mono (WP.loop (M := isa) I hstep (nb s₀) s ⟨0, by simp, by omega, hI₁⟩)
    fun s₂ ⟨e, he, hI₂⟩ => dfinal_ok hp he hI₂)

end VG.Proof.Gcm.X86_64.StitchAvx
