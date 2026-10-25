module
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Loop

import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Enc

/-!
# AES-GCM-SIV's interleaved loop: from the setup on

`Ready s₀ P s`: after the setup, nothing is deciphered (`AInv s₀ 0`), the
powers `P` are in the working space, `Y` in `xmm2`, `rdx` points to the data
(`setupT_ok`, after the powers are computed, which `Stitch/Ok.lean` proves in
the field). `first_ok`: the first group is deciphered (`EInv s₀ P 1`).
`decTail_ok`: the loop after the setup, for any powers whose products add up
to `GHASH` (`FinOk`), as AES-GCM's encryption (`Proof/Gcm/X86_64/Stitch/Enc.lean`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86_64.Stitch

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (storesK pregs ordE)
open VG.Impl.AesGcmSiv.X86_64Stitch (setupC first batch body ghLoad storeCtr lastG storeY)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod toNat_ofNat_lt)
open VG.Proof.Gcm.X86_64.Vpclmul (zero_lanes)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Stitch (addr_eq in_sub in_sub_int in_rdwr FinOk accN storesK_ok pregs_get store16_ok
  ghash_append16)
open VG.Proof.Aes.X86_64.AesNi (Keys)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom)

structure Ready (s₀ : State) (P : Nat → Nat → Block) (s : State) : Prop where
  a : AInv s₀ 0 s
  rdx : s.gpr .rdx = dp s₀
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = y₀ s₀
  y1 : s.lane .xmm2 1 = 0

theorem pregs_get : ∀ k (h : k < pregs.length), pregs[k] = preg16 k := by decide

/-- Bytes outside the working space are kept by writes to it. -/
theorem bytesAt_outP {s₀ : State} {m m' : Mem} {p : Addr} {n : Nat} (hf : Frame [pR s₀] m m')
    (hd : Region.Disjoint ⟨p, n⟩ (pR s₀)) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hn

theorem blockAt_outP {s₀ : State} {m m' : Mem} {p : Addr} (hf : Frame [pR s₀] m m')
    (hd : Region.Disjoint ⟨p, 16⟩ (pR s₀)) : blockAt m' p = blockAt m p :=
  Proof.AesGcm.X86_64.blockAt_frame hf fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd

theorem readW_outP {s₀ : State} {m m' : Mem} {p : Addr} (hf : Frame [pR s₀] m m')
    (hd : Region.Disjoint ⟨p, 16⟩ (pR s₀)) : m'.readW p 128 = m.readW p 128 :=
  hf.readW (r := ⟨p, 16⟩) (Region.contains_self _ _)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) (by decide)

/-- The setup after the powers (`setupG`): they are stored in the working
space, then `Y`, the counter, the increment and the pointers. -/
theorem setupT_ok {s₀ : State} (hp : SPre s₀) {s₁ : State} (l0 : ∀ l < 2, s₁.lane .xmm0 l = revMask)
    (l1 : ∀ l < 2, s₁.lane .xmm1 l = poly) (g₁ : ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) (m₁ : s₁.mem = s₀.mem)
    (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr) :
    WP isa (.block (storesK .r11 pregs 0 ++ setupC)) s₁ (Ready s₀ fun k l => s₁.lane (preg16 k) l) := by
  have hwp := hp.wrap_p
  have hwd := hp.wrap_d
  have hr11 : s₁.gpr .r11 = pp s₀ := g₁ _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storesK_ok .r11 pregs 0 s₁ (fun k hk => by
      rw [wr₁, hr11]; exact in_sub_int hp.p_in (by simp [pregs] at hk; omega_arith))
    (by rw [hr11]; simp [pregs]; omega_arith)) fun s₂ ⟨sv, fr, g₂, rd₂, wr₂, l₂⟩ => ?_
  rw [hr11, Nat.mul_zero, BitVec.add_zero, show 32 * pregs.length = 256 from rfl, m₁] at fr
  replace fr : Frame [pR s₀] s₀.mem s₂.mem := fr.sub fun r hr => ⟨pR s₀, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩
  have hp₂ : ∀ {p : Addr}, Region.Disjoint ⟨p, 16⟩ (pR s₀) → blockAt s₂.mem p = blockAt s₀.mem p :=
    fun hd => by rw [blockAt_outP fr hd]
  have hpw₂ : ∀ {p : Addr}, Region.Disjoint ⟨p, 16⟩ (pR s₀) → s₂.mem.readW p 128 = s₀.mem.readW p 128 :=
    fun hd => by rw [readW_outP fr hd]
  have hpb₂ : ∀ {p : Addr}, Region.Disjoint ⟨p, 16⟩ (pR s₀) → bytesAt s₂.mem p 16 = bytesAt s₀.mem p 16 :=
    fun hd => by rw [bytesAt_outP fr hd (by decide)]
  refine WP.mono (setupC_ok s₂ (fun l hl => by rw [l₂]; exact l0 l hl)
    (by rw [wr₂, wr₁, g₂, g₁ _ (by decide)]; exact hp.y_in)
    (by rw [wr₂, wr₁, g₂, g₁ _ (by decide)]; exact hp.c_in))
    fun s₃ ⟨y0, y1, c140, c141, c15, r10, rax, rdx, gk, lk, m₃, rd₃, wr₃⟩ => ?_
  have gs : ∀ r, r ≠ .rax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, g₁ r hr]
  refine ⟨⟨Nat.zero_le _, fun l hl => ?_, fun l hl => ?_, c15, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_, ?_⟩,
    by rw [rdx, gs _ (by decide)], by rw [rax, gs _ (by decide)],
    fun r h1 h2 h3 => by rw [gk r h1 h2 h3, gs r h1], fun k hk l hl => ?_,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl, l₂]; exact l1 l hl,
    by rw [y0, gs _ (by decide), hp₂ (hp.p_y.symm)], y1⟩
  · have hd : s₂.mem.readW (s₂.gpr .rdx) 128 = d₀ s₀ := by rw [gs _ (by decide), hpw₂ hp.p_c.symm]
    rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
    · rw [c140, hd, ctrX₀]
    · rw [c141, hd]
      conv => lhs; rw [← ctrX₀ s₀, ctrX, paddd_one, ← BitVec.ofNat_add]
  · rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl, l₂]; exact l0 l hl
  · rw [gk _ (by decide) (by decide) (by decide), gs _ (by decide)]
  · rw [gk _ (by decide) (by decide) (by decide), gs _ (by decide)]
  · rw [r10, gs _ (by decide), gs _ (by decide)]
  · rw [m₃]; exact fr.mono fun r hr => by simp at hr ⊢; exact Or.inr hr
  · rw [m₃, hpb₂ (hp.d_p.sub_left (Offset.sub_base _ (by omega_arith)))]
    simp only [Nat.not_lt_zero, ite_false]
  · rw [rd₃, rd₂, rd₁]
  · rw [wr₃, wr₂, wr₁]
  · rw [m₃, show pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l) = s₁.gpr .r11 + BitVec.ofNat 64 (32 * (0 + k) + 16 * l)
      by rw [hr11, Nat.zero_add], sv k (by simp [pregs]; omega_arith) l hl, pregs_get]

/-- The first group: two batches, with nothing between their rounds. -/
theorem first_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} {s : State} (hR : Ready s₀ P s) :
    WP isa first s (EInv s₀ P 1) := by
  have hwp := hp.wrap_p
  have hwd := hp.wrap_d
  have h16 := hp.nb16
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ YFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, YFrame.refl _ _⟩
  refine WP.seq (WP.mono (batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 0) (j := 0) (by omega_arith) hR.a
    (by rw [hR.rdx]) trivial) fun s₁ ⟨hA₁, _, hg₁, hl₁, hm₁⟩ => ?_)
  refine WP.mono (batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 0 + 8) (j := 4) (by omega_arith) hA₁
    (by rw [hg₁, hR.rdx]) trivial) fun s₂ ⟨hA₂, _, hg₂, hl₂, hm₂⟩ => ?_
  have dP : ∀ c, c + 8 ≤ nb s₀ → ∀ r' ∈ [(⟨bAddr s₀ c, 128⟩ : Region)], (pR s₀).Disjoint r' := fun c hc r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega_arith))
  have lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ VG.Impl.Gcm.X86_64.Stitch.aregs → ∀ l < 2,
      s₂.lane r l = s.lane r l := fun r h13 h14 hr l hl => by
    rw [hl₂ r h13 h14 hr (by simp) l hl, hl₁ r h13 h14 hr (by simp) l hl]
  have gk : s₂.gpr = s.gpr := by rw [hg₂, hg₁]
  refine ⟨by simpa using hA₂, Nat.le_refl _, by rw [gk, hR.rdx]; simp, ?_, by rw [gk]; exact hR.rax,
    fun r h1 h2 _ h4 => by rw [gk]; exact hR.gpr r h1 h2 h4, fun k hk l hl => ?_,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) l hl]; exact hR.m1 l hl,
    by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide), hR.y]; simp [ghashFrom],
    by rw [lk _ (by decide) (by decide) (by decide) 1 (by decide)]; exact hR.y1⟩
  · rw [gk, hR.gpr _ (by decide) (by decide) (by decide)]; simp
  · rw [hm₂.readW (r := pR s₀) (Offset.contains_base _ (by omega_arith) (by omega_arith)) (dP _ (by omega_arith)) (by decide),
      hm₁.readW (r := pR s₀) (Offset.contains_base _ (by omega_arith) (by omega_arith)) (dP _ (by omega_arith)) (by decide)]
    exact hR.pw k hk l hl

/-! ## The loop -/

/-- `cmp r9, 32`. -/
theorem cmpE_ok {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (hI : EInv s₀ P e s) :
    WP isa (.block [.alu .cmp .r9 (.imm 32)]) s fun s' =>
      EInv s₀ P e s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e - 1) < 32)) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  have hr9 := hI.r9
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    hr9, e32, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨{ hI with a := { hI.a with } }, ?_⟩
  rw [toNat_ofNat_lt (by omega_arith)]; rfl

theorem loopE_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {s : State}
    (hI : EInv s₀ P 1 s) (hcf : s.cf = some (decide (nb s₀ - 16 * (1 - 1) < 32))) :
    WP isa (.ite .b (.block []) (.loop body .ae)) s fun s' => ∃ e, nb s₀ = 16 * e ∧ EInv s₀ P e s' := by
  have fin : ∀ e, nb s₀ - 16 * (e - 1) < 32 → ∀ t, EInv s₀ P e t → ∃ e, nb s₀ = 16 * e ∧ EInv s₀ P e t :=
    fun e he t hI => ⟨e, by have := hI.a.le; have := hI.one; omega_arith, hI⟩
  refine WP.ite (decide (nb s₀ - 16 * (1 - 1) < 32)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil (fin 1 (by simpa using h) s hI)
  · let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ EInv s₀ P e s
    have hstep : ∀ m s, I m s → WP isa body s (fun s' =>
        (eval .ae s' = some false ∧ ∃ e, nb s₀ = 16 * e ∧ EInv s₀ P e s') ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨e, rfl, he, hI⟩
      refine WP.mono (body_ok hp hf he hI) fun s' ⟨hI', hcf'⟩ => ?_
      by_cases hlt : nb s₀ - 16 * e < 32
      · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
          fin (e + 1) (by simpa using hlt) s' hI'⟩
      · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
          nb s₀ - 16 * (e + 1), by have := hI.one; omega_arith, e + 1, rfl, by omega_arith, hI'⟩
    exact WP.loop (M := isa) I hstep (nb s₀ - 16 * 1) s ⟨1, rfl, by simp at h; omega_arith, hI⟩

/-! ## The last group, and the stores -/

/-- The loads `0 … n − 1` of the order of an encryption body. -/
theorem ghRun_ok {s₀ : State} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block} {yl : Nat → Block} :
    ∀ n, n ≤ 8 → ∀ s, GEnv s₀ 0 a X P s → (∀ l < 2, prod (s.proj l) = Prod.zero) →
      (∀ l < 2, s.lane .xmm2 l = yl l) →
      WP isa (.block ((List.range n).flatMap fun i => ghLoad (ordE i))) s fun s' => GEnv s₀ 0 a X P s' ∧
        (∀ l < 2, prod (s'.proj l) = accN ordE X P yl l n) ∧ (∀ l < 2, s'.lane .xmm2 l = yl l) ∧
        YFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s'
  | 0, _, s, hE, hz, hy => by
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨hE, fun l hl => by rw [hz l hl]; rfl, hy, YFrame.refl _ _⟩
  | n + 1, hn, s, hE, hz, hy => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ghRun_ok n (by omega_arith) s hE hz hy) fun s₁ ⟨hE₁, p₁, y₁, f₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hk : ordE n < 8 := by
      rcases (by omega_arith : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact WP.mono (ghStep hk (Nat.zero_le _) hE₁ p₁ y₁) fun s' ⟨hE', p', y', f'⟩ => ⟨hE', p', y', f₁.trans f'⟩

/-! ## The whole loop -/

/-- `vmovdqu [rax], xmm14`: the counter block stored, as it is. -/
theorem storeCtr_ok (s : State) (hin : InRegions s.wr (s.gpr .rax) 16) :
    WP isa (.block storeCtr) s fun s' => s'.mem = s.mem.writeW (s.gpr .rax) (s.lane .xmm14 0) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r l, s'.lane r l = s.lane r l) := by
  have hin' : InRegions s.wr (s.gpr .rax + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact hin
  apply WP.of_runBlock
  simp only [storeCtr, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.store128_eq,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, hin', ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [BitVec.ofInt_natCast, BitVec.add_zero]; simp [State.lane], rfl, rfl, rfl, fun _ _ => rfl⟩

/-- A 16-byte write's frame. -/
theorem frame_write16 (m : Mem) (p : Addr) (v : BitVec 128) : Frame [⟨p, 16⟩] m (m.writeW p v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem final_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {e : Nat}
    (he : nb s₀ = 16 * e) {s : State} (hI : EInv s₀ P e s) :
    WP isa (.block (storeCtr ++ lastG ++ storeY)) s (DPost s₀) := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  have h1e := hI.one
  have hm0 : s.lane .xmm0 0 = revMask := hI.a.msk 0 (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (storeCtr_ok s (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  -- The counter's memory is neither the data nor the working space.
  have cD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega_arith))
  have cP : ∀ k < 8, ∀ l < 2, Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l), 16⟩ (cR s₀) :=
    fun k hk l hl => hp.p_c.sub_left (Offset.sub_base _ (by omega_arith))
  rw [hI.rax] at m₁
  have fC : Frame [cR s₀] s.mem s₁.mem := by rw [m₁]; exact frame_write16 _ _ _
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => Spec.GcmSiv.ofBytes (ctb s₀ (16 * (e - 1) + i))
  let yl : Nat → Block := fun l => s.lane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * (e - 1) := hI.rdx
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  simp only [lastG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_lanes s₁) fun s₂ ⟨z₂, f₂, _⟩ => ?_
  have hE₂ : GEnv s₀ 0 a X P s₂ :=
    { rdx := by rw [f₂.gpr, g₁]
      r11 := by rw [f₂.gpr, g₁, hr11]
      xs := fun i _ hi => by
        rw [f₂.mem, show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega_arith),
          fC.readW (r := ⟨bAddr s₀ (16 * (e - 1) + i), 16⟩) (Region.contains_self _ _)
            (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact cD _ (by omega_arith)) (by decide),
          readW_ofBytes, hI.a.blocks _ (by omega_arith)]
        simp only [show 16 * (e - 1) + i < 16 * e by omega_arith, ite_true]
        rfl
      pv := fun k hk l hl => by
        rw [f₂.mem, fC.readW (r := ⟨pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l), 16⟩) (Region.contains_self _ _)
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact cP k hk l hl) (by decide)]
        exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₂.rd, f₂.wr, rd₁, wr₁, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (32 * k) = dp s₀ + BitVec.ofNat 64 (256 * (e - 1) + 32 * k) from
            addr_eq (by omega_arith)]
        exact in_rdwr (in_sub hp.d_in (by omega_arith))
      inp := fun k hk => by
        rw [f₂.rd, f₂.wr, rd₁, wr₁, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega_arith)) }
  rw [WP.block_append_iff]
  refine WP.mono (ghRun_ok (yl := yl) 8 (Nat.le_refl _) s₂ hE₂ z₂
    (fun l hl => by rw [f₂.lane _ (by decide) l hl, l₁])) fun s₃ ⟨hE₃, p₃, _, f₃⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (ghFin hE₃ (fun l hl => by
      rw [f₃.lane _ (by decide) l hl, f₂.lane _ (by decide) l hl, l₁]; exact hI.m1 l hl))
    fun s₄ ⟨_, y4, _, f₄⟩ => ?_
  rw [p₃ 0 (by decide), p₃ 1 (by decide)] at y4
  have hm0₄ : s₄.lane .xmm0 0 = revMask := by
    rw [f₄.lane _ (by decide) 0 (by decide), f₃.lane _ (by decide) 0 (by decide),
      f₂.lane _ (by decide) 0 (by decide), l₁]; exact hm0
  have g₄ : s₄.gpr = s.gpr := by rw [f₄.gpr, f₃.gpr, f₂.gpr, g₁]
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl,
    WP.block_append_iff]
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx s₄ hm0₄ (by
      rw [g₄, f₄.wr, f₃.wr, f₂.wr, wr₁, hI.a.wr, hI.gpr _ (by decide) (by decide) (by decide) (by decide)]
      exact hp.y_in)) fun s₅ ⟨m₅, g₅, rd₅, wr₅, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  have hrcx : s.gpr .rcx = yp s₀ := hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  rw [g₄, hrcx] at m₅
  have m₄ : s₄.mem = s₁.mem := by rw [f₄.mem, f₃.mem, f₂.mem]
  rw [m₄, m₁] at m₅
  -- The final memory: the counter, then `Y`, written.
  have fY : Frame [yR s₀] s₁.mem s₅.mem := by rw [m₅, ← m₁]; exact frame_write16 _ _ _
  have yD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega_arith))
  have hb : ∀ k < nb s₀, bytesAt s₅.mem (bAddr s₀ k) 16 = ctb s₀ k := fun k hk => by
    rw [Proof.AesGcm.X86_64.bytesAt_frame fY (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact yD k hk) (by decide),
      Proof.AesGcm.X86_64.bytesAt_frame fC (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact cD k hk) (by decide),
      hI.a.blocks k hk]
    simp only [show k < 16 * e by omega_arith, ite_true]
  refine ⟨hb, ?_, ?_, ?_, ?_, by
      show s₅.rd = _; rw [rd₅, f₄.rd, f₃.rd, f₂.rd, rd₁, hI.a.rd], by
      show s₅.wr = _; rw [wr₅, f₄.wr, f₃.wr, f₂.wr, wr₁, hI.a.wr]⟩
  · show bytesAt s₅.mem (cp s₀) 16 = _
    rw [Proof.AesGcm.X86_64.bytesAt_frame fY (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.c_y) (by decide),
      m₁, bytesAt_writeW128, hI.a.ctr 0 (by decide), Nat.add_zero, he, le16_ctrX (rest₀ s₀)]
  · show blockAt s₅.mem (yp s₀) = _
    rw [m₅, VG.Proof.Gcm.X86_64.blockAt_store, y4]
    refine (hf X yl hI.y1).trans ?_
    rw [he, show 16 * e = 16 * ((e - 1) + 1) by congr 1; omega_arith, ghash_append16]
    exact congrArg (fun y => ghashFrom (hk s₀) y ((List.range 16).map X)) hI.y
  · show Frame _ s₀.mem s₅.mem
    rw [m₅]
    exact ((hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := yR s₀) (by simp) _
      (Region.contains_self _ _)
  · intro r h1 h2 h3 h4
    show s₅.gpr r = _
    rw [g₅, g₄]; exact hI.gpr r h1 h2 h3 h4

/-- The loop after the setup. -/
theorem decTail_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block}
    (hf : FinOk ordE (hk s₀) P) {s : State} (hR : Ready s₀ P s) :
    WP isa (.seq first (.seq (.block [.alu .cmp .r9 (.imm 32)])
      (.seq (.ite .b (.block []) (.loop body .ae)) (.block (storeCtr ++ lastG ++ storeY))))) s (DPost s₀) := by
  refine WP.seq (WP.mono (first_ok hp hR) fun s₂ hI₂ => ?_)
  refine WP.seq (WP.mono (cmpE_ok hI₂) fun s₃ ⟨hI₃, hcf⟩ => ?_)
  exact WP.seq (WP.mono (loopE_ok hp hm hf hI₃ hcf) fun s₄ ⟨e, he, hI₄⟩ => final_ok hp hf he hI₄)

end VG.Proof.AesGcmSiv.X86_64.Stitch
