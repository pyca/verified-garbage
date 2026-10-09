import VerifiedGarbage.Proof.Gcm.X86_64.StitchTo.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Enc
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop

/-!
# The out-of-place VAES loop: the loop of one group, and the stores

As `Stitch/Loop.lean` and `Stitch/Enc.lean` do in place. The setup is
`StitchZTo.setupTTo_ok`'s (`Ready2To`), from which the loop starts
(`ReadyTo.ofReady2`).

`EInvTo s₀ P e s`: `e` groups of sixteen blocks are encrypted (`AInvTo`),
the ciphertext of the first `e - 1` hashed into `Y`; `rdx` points to output
group `e - 1`, the next to hash. `bodyTo_ok`: a body encrypts group `e`
(two batches, `batchTo_ok`) while it hashes the output of group `e - 1`
between their rounds (`Stitch.gq_ok`), which they do not write
(`Stitch.QG.data`, for the in-place view `dst s₀`). `finalTo_ok`: the
stores after the loop, and the contract (`EPostTo`).
-/

namespace VG.Proof.Gcm.X86_64.StitchTo

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo EPostTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch hk y₀
  dp dR pR cR yR bAddr addr_eq in_sub in_sub_int in_rdwr ite_t ite_f ghash_append16 blockAt_writeW_sep'
  GEnv QG gRegs gRegs_ok gq_ok QG.data nextE_ok FinOk ghRun_ok ghFin store16_ok)
open VG.Proof.Gcm.X86_64.StitchZTo (dst sAddr pblk ctbT oAddr Ready2To blocks_ctr32To)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs gA gB ordE storeCtr lastG storeY)
open VG.Impl.Gcm.X86_64.StitchTo (firstTo bodyTo)
open VG.Proof.Gcm.X86_64.Vpclmul (zero_lanes)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-! ## The state the loop starts from -/

structure ReadyTo (s₀ : State) (P : Nat → Nat → Block) (s : State) : Prop where
  a : AInvTo s₀ 0 s
  rdx : s.gpr .rdx = op s₀
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = y₀ s₀
  y1 : s.lane .xmm2 1 = 0

theorem ReadyTo.ofReady2 {s₀ : State} {P : Nat → Nat → Block} {s : State} (h : Ready2To s₀ P s) :
    ReadyTo s₀ P s :=
  ⟨⟨Nat.zero_le _, fun l hl => by rw [h.ctr l hl, Nat.zero_add], h.msk, h.inc, h.rdi, h.rsi, h.r10, h.r8,
    h.frame.mono fun r hr => by simp at hr ⊢; exact Or.inr hr, fun k hk => absurd hk (Nat.not_lt_zero _),
    h.rd, h.wr⟩, h.rdx, h.rax, h.gpr, h.pw, h.m1, h.y, h.y1⟩

/-! ## The loop of one group -/

structure EInvTo (s₀ : State) (P : Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInvTo s₀ (16 * e) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (op s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map (ctbT s₀))
  y1 : s.lane .xmm2 1 = 0

/-- The powers in the working space are kept by the output written. -/
theorem keepP {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {c : Nat} (hc : c + 8 ≤ nb s₀) {m m' : Mem}
    (hf : Frame [⟨oAddr s₀ c, 128⟩] m m') {k l : Nat} (hk : k < 8) (hl : l < 2) :
    m'.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = m.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 := by
  have hw := hp.wrap_o
  have hwp := hp.wrap_p
  exact hf.readW (r := pR s₀) (Offset.contains_base _ (by omega) (by omega))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.o_p.symm.sub_right (Offset.sub_base _ (by omega))) (by decide)

/-- What hashing output group `e - 1` needs, from `rdx` pointing to it with
its blocks below `c` encrypted. -/
theorem genv {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} {e c : Nat} {s : State}
    (hA : AInvTo s₀ c s) (h1e : 1 ≤ e) (hec : 16 * e ≤ c)
    (hrdx : (s.gpr .rdx).toNat = (op s₀).toNat + 256 * (e - 1)) (hr11 : s.gpr .r11 = pp s₀)
    (hpw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l) :
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
        show s.gpr .rdx + BitVec.ofNat 64 (32 * k) = op s₀ + BitVec.ofNat 64 (256 * (e - 1) + 32 * k) from
          addr_eq (by omega)]
      exact in_rdwr (in_sub hp.o_in (by omega))
    inp := fun k hk => by
      rw [hA.rd, hA.wr]
      exact in_rdwr (in_sub_int hp.p_in (by omega))
    m0 := hA.msk }

theorem bodyTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block}
    (hf : FinOk ordE (hk s₀) P) {e : Nat} (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInvTo s₀ P e s) :
    WP isa bodyTo s fun s' => EInvTo s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) := by
  have hd := hp.toD
  have hnb := VG.Proof.Gcm.X86_64.StitchZTo.nb_dst s₀
  have hw := hp.wrap_o
  have h1e := hI.one
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctbT s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.lane .xmm2 l
  have ha : a.toNat = (op s₀).toNat + 256 * (e - 1) := hI.rdx
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (zero_lanes s) fun s₁ ⟨z₁, f₁, _⟩ => ?_)
  have hA₁ := hI.a.yframe f₁ (by decide) (by decide) (by decide)
  have hE₁ : GEnv (dst s₀) 0 a X P s₁ := by
    have h := genv (P := P) hp hA₁ h1e (by omega) (by rw [f₁.gpr]; exact hI.rdx) (by rw [f₁.gpr]; exact hr11)
      (fun k hk l hl => by rw [f₁.mem]; exact hI.pw k hk l hl)
    rwa [f₁.gpr] at h
  have hrdx₁ : (s₁.gpr .rdx).toNat + 32 * 8 = (op s₀).toNat + 16 * (16 * e) := by
    rw [f₁.gpr]; show a.toNat + _ = _; omega
  have hsepA : ∀ c, 16 * e ≤ c → ∀ i, 0 ≤ i → i < 16 → ¬ (c ≤ 16 * (e - 1) + i ∧ 16 * (e - 1) + i < c + 8) :=
    fun c hc i _ hi => by omega
  -- The first batch, with loads 1–4 of the previous group.
  refine WP.seq (WP.mono (batchTo_ok hp gA gRegs gRegs_ok (QG (dst s₀) (fun _ => 0) a X P yl ordE 0 false)
    (gq_ok (s₀ := dst s₀) (fun _ => Nat.le_refl _) (fun j hj1 hj4 => by
      rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, Nat.zero_le _⟩) (fun h => absurd h (by decide)))
    (fun j t t' h f => h.yframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hd (by omega) (by omega) ha (hsepA _ (Nat.le_refl _)) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 8) (by omega) hA₁ hrdx₁
    ⟨hE₁, fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact hI.m1 l hl,
      by rw [ite_f (by decide)]
         exact ⟨fun l hl => z₁ l hl, fun l hl => by rw [f₁.lane _ (by decide) l hl]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  have hrdx₂ : (s₂.gpr .rdx).toNat + 32 * 12 = (op s₀).toNat + 16 * (16 * e + 8) := by
    rw [hg₂, f₁.gpr]; show a.toNat + _ = _; omega
  have hQ₂' : QG (dst s₀) (fun _ => 0) a X P yl ordE 4 true 1 s₂ := by
    obtain ⟨hE, h1, h2⟩ := hQ₂
    rw [ite_f (by decide)] at h2
    exact ⟨hE, h1, by rw [ite_f (by decide)]; exact h2⟩
  -- The second batch, with loads 5–7 and 0 of the previous group, and the reduction.
  refine WP.seq (WP.mono (batchTo_ok hp gB gRegs gRegs_ok (QG (dst s₀) (fun _ => 0) a X P yl ordE 4 true)
    (gq_ok (s₀ := dst s₀) (fun _ => Nat.le_refl _) (fun j hj1 hj4 => by
      rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, Nat.zero_le _⟩) (fun _ => rfl))
    (fun j t t' h f => h.yframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hd (by omega) (by omega) ha (hsepA _ (by omega)) h hg hrd hwr hl hf)
    (c := 16 * e + 8) (j := 12) (by omega) hA₂ hrdx₂ hQ₂')
    fun s₃ ⟨hA₃, hQ₃, hg₃, hl₃, hm₃⟩ => ?_)
  refine WP.mono (nextE_ok s₃) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, _, h2⟩ := hQ₃
  rw [ite_t ⟨rfl, by decide⟩] at h2
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₃, hg₂, f₁.gpr]
  have lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ gRegs → ∀ l < 2, s'.lane r l = s.lane r l :=
    fun r h13 h14 ha' hg' l hl => by
      rw [fl r l, hl₃ r h13 h14 ha' hg' l hl, hl₂ r h13 h14 ha' hg' l hl,
        f₁.lane r (by simp only [gRegs, List.mem_cons, not_or] at hg' ⊢; simp_all) l hl]
  have hA' : AInvTo s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 8 + 8 by omega]
    exact ⟨hA₃.le, fun l hl => by rw [fl]; exact hA₃.ctr l hl, fun l hl => by rw [fl]; exact hA₃.msk l hl,
      fun l hl => by rw [fl]; exact hA₃.inc l hl,
      by rw [fg _ (by decide) (by decide)]; exact hA₃.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₃.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₃.r10, by rw [fg _ (by decide) (by decide)]; exact hA₃.r8,
      by rw [fm]; exact hA₃.frame, fun k hk => by rw [fm]; exact hA₃.blocks k hk, by rw [frd]; exact hA₃.rd,
      by rw [fwr]; exact hA₃.wr⟩
  have hr9 : s₃.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1 - 1)) := by
    rw [hg₃, hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega) (by omega)]
    congr 1; omega
  refine ⟨⟨hA', by omega, ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 h5 => by rw [gk r h2 h4]; exact hI.gpr r h1 h2 h3 h4 h5,
    fun k hk l hl => by
      rw [fm, keepP hp (by omega) hm₃ hk hl, keepP hp (by omega) hm₂ hk hl, f₁.mem]; exact hI.pw k hk l hl,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl]; exact hI.m1 l hl, ?_,
    by rw [fl]; exact h2.2⟩, ?_⟩
  · rw [frdx, hg₃, hg₂, f₁.gpr, BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (by show a.toNat + 256 < 2 ^ 64; omega)]
    show a.toNat + 256 = _
    rw [ha, show e + 1 - 1 = (e - 1) + 1 by omega, Nat.mul_succ, Nat.add_assoc]
  · rw [fl, h2.1, hf X yl hI.y1,
      show e + 1 - 1 = (e - 1) + 1 by omega, ghash_append16, ← hI.y]
  · rw [fcf, hr9, toNat_ofNat_lt (by omega), show e + 1 - 1 = e by omega]

/-- The first group: two batches, with nothing between their rounds. -/
theorem firstTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} {s : State}
    (hR : ReadyTo s₀ P s) : WP isa firstTo s (EInvTo s₀ P 1) := by
  have h16 := hp.nb16
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ YFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, YFrame.refl _ _⟩
  refine WP.seq (WP.mono (batchTo_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 0) (j := 0) (by omega) hR.a
    (by rw [hR.rdx]) trivial) fun s₁ ⟨hA₁, _, hg₁, hl₁, hm₁⟩ => ?_)
  refine WP.mono (batchTo_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 0 + 8) (j := 4) (by omega) hA₁
    (by rw [hg₁, hR.rdx]) trivial) fun s₂ ⟨hA₂, _, hg₂, hl₂, hm₂⟩ => ?_
  have lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → ∀ l < 2, s₂.lane r l = s.lane r l :=
    fun r h13 h14 hr l hl => by rw [hl₂ r h13 h14 hr (by simp) l hl, hl₁ r h13 h14 hr (by simp) l hl]
  have gk : s₂.gpr = s.gpr := by rw [hg₂, hg₁]
  refine ⟨by simpa using hA₂, Nat.le_refl _, by rw [gk, hR.rdx]; simp, ?_, by rw [gk]; exact hR.rax,
    fun r h1 h2 h3 _ h5 => by rw [gk]; exact hR.gpr r h1 h2 h3 h5,
    fun k hk l hl => by
      rw [keepP hp (by omega) hm₂ hk hl, keepP hp (by omega) hm₁ hk hl]; exact hR.pw k hk l hl,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) l hl]; exact hR.m1 l hl,
    by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide), hR.y]; simp [ghashFrom],
    by rw [lk _ (by decide) (by decide) (by decide) 1 (by decide)]; exact hR.y1⟩
  rw [gk, hR.gpr _ (by decide) (by decide) (by decide) (by decide)]; simp

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

theorem loopE_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block}
    (hf : FinOk ordE (hk s₀) P) {s : State}
    (hI : EInvTo s₀ P 1 s) (hcf : s.cf = some (decide (nb s₀ - 16 * (1 - 1) < 32))) :
    WP isa (.ite .b (.block []) (.loop bodyTo .ae)) s fun s' => ∃ e, nb s₀ = 16 * e ∧ EInvTo s₀ P e s' := by
  have fin : ∀ e, nb s₀ - 16 * (e - 1) < 32 → ∀ t, EInvTo s₀ P e t → ∃ e, nb s₀ = 16 * e ∧ EInvTo s₀ P e t :=
    fun e he t hI => ⟨e, by have := hI.a.le; have := hI.one; omega, hI⟩
  refine WP.ite (decide (nb s₀ - 16 * (1 - 1) < 32)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil (fin 1 (by simpa using h) s hI)
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
    exact WP.loop (M := isa) I hstep (nb s₀ - 16 * 1) s ⟨1, rfl, by simp at h; omega, hI⟩

/-! ## The stores -/

theorem finalTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block}
    (hf : FinOk ordE (hk s₀) P) {e : Nat} (he : nb s₀ = 16 * e) {s : State} (hI : EInvTo s₀ P e s) :
    WP isa (.block (storeCtr ++ lastG ++ storeY)) s (EPostTo s₀) := by
  have hw := hp.wrap_o
  have hwp := hp.wrap_p
  have h1e := hI.one
  have hm0 : s.lane .xmm0 0 = revMask := hI.a.msk 0 (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (store16_ok .xmm13 .xmm14 .rax s hm0 (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  have cD : ∀ k < nb s₀, Region.Disjoint ⟨oAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.o_c.sub_left (Offset.sub_base _ (by omega))
  have cP : ∀ k < 8, ∀ l < 2, Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l), 16⟩ (cR s₀) :=
    fun k hk l hl => hp.p_c.sub_left (Offset.sub_base _ (by omega))
  rw [hI.rax] at m₁
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctbT s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.lane .xmm2 l
  have ha : a.toNat = (op s₀).toNat + 256 * (e - 1) := hI.rdx
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [lastG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_lanes s₁) fun s₂ ⟨z₂, f₂, _⟩ => ?_
  have hE₂ : GEnv (dst s₀) 0 a X P s₂ :=
    { rdx := by rw [f₂.gpr, g₁]
      r11 := by rw [f₂.gpr, g₁]; exact hr11
      xs := fun i _ hi => by
        rw [f₂.mem, m₁, show a + BitVec.ofNat 64 (16 * i) = oAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega),
          blockAt_writeW_sep' (cD _ (by omega)) rfl, hI.a.blocks _ (by omega)]
      pv := fun k hk l hl => by
        rw [f₂.mem, m₁, Mem.readW_writeW_sep ((cP k hk l hl).sep (Region.contains_self _ _) (Region.contains_self _ _))
          (by decide)]
        exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₂.rd, f₂.wr, rd₁, wr₁, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (32 * k) = op s₀ + BitVec.ofNat 64 (256 * (e - 1) + 32 * k) from
            addr_eq (by omega)]
        exact in_rdwr (in_sub hp.o_in (by omega))
      inp := fun k hk => by
        rw [f₂.rd, f₂.wr, rd₁, wr₁, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := fun l hl => by rw [f₂.lane _ (by decide) l hl, l₁ _ (by decide) l hl]; exact hI.a.msk l hl }
  rw [WP.block_append_iff]
  refine WP.mono (ghRun_ok (yl := yl) 8 (Nat.le_refl _) s₂ hE₂ z₂
    (fun l hl => by rw [f₂.lane _ (by decide) l hl, l₁ _ (by decide) l hl])) fun s₃ ⟨hE₃, p₃, _, f₃⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (ghFin hE₃ (fun l hl => by
      rw [f₃.lane _ (by decide) l hl, f₂.lane _ (by decide) l hl, l₁ _ (by decide) l hl]; exact hI.m1 l hl))
    fun s₄ ⟨_, y4, _, f₄⟩ => ?_
  rw [p₃ 0 (by decide), p₃ 1 (by decide)] at y4
  have hm0₄ : s₄.lane .xmm0 0 = revMask := by
    rw [f₄.lane _ (by decide) 0 (by decide), f₃.lane _ (by decide) 0 (by decide),
      f₂.lane _ (by decide) 0 (by decide), l₁ _ (by decide) 0 (by decide)]; exact hm0
  have g₄ : s₄.gpr = s.gpr := by rw [f₄.gpr, f₃.gpr, f₂.gpr, g₁]
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl,
    WP.block_append_iff]
  have hrcx : s.gpr .rcx = yp s₀ := hI.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx s₄ hm0₄ (by
      rw [g₄, f₄.wr, f₃.wr, f₂.wr, wr₁, hI.a.wr, hrcx]
      exact hp.y_in)) fun s₅ ⟨m₅, g₅, rd₅, wr₅, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [g₄, hrcx] at m₅
  have m₄ : s₄.mem = s₁.mem := by rw [f₄.mem, f₃.mem, f₂.mem]
  rw [m₄, m₁] at m₅
  have yD : ∀ k < nb s₀, Region.Disjoint ⟨oAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.o_y.sub_left (Offset.sub_base _ (by omega))
  have hb : ∀ k < nb s₀, blockAt s₅.mem (oAddr s₀ k) = ctbT s₀ k := fun k hk => by
    rw [m₅, blockAt_writeW_sep' (yD k hk) rfl, blockAt_writeW_sep' (cD k hk) rfl]
    exact hI.a.blocks k (by omega)
  refine ⟨blocks_ctr32To hb, ?_, ?_, ?_, ?_, by
      show s₅.rd = _; rw [rd₅, f₄.rd, f₃.rd, f₂.rd, rd₁, hI.a.rd], by
      show s₅.wr = _; rw [wr₅, f₄.wr, f₃.wr, f₂.wr, wr₁, hI.a.wr]⟩
  · show blockAt s₅.mem (cp s₀) = _
    rw [m₅, blockAt_writeW_sep' hp.c_y rfl, VG.Proof.Gcm.X86_64.blockAt_store, hI.a.ctr 0 (by decide),
      Nat.add_zero, he]
  · show blockAt s₅.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s₅.mem (op s₀) (nb s₀))
    rw [show blocksAt s₅.mem (op s₀) (nb s₀) = (List.range (16 * e)).map (ctbT s₀) from by
        rw [← he]; simp only [blocksAt]
        exact List.map_congr_left fun k hk => hb k (by simpa using hk),
      m₅, VG.Proof.Gcm.X86_64.blockAt_store, y4]
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

/-- The encryption after the setup. -/
theorem encTailTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block}
    (hf : FinOk ordE (hk s₀) P) {s : State} (hR : ReadyTo s₀ P s) :
    WP isa (.seq firstTo (.seq (.block [.alu .cmp .r9 (.imm 32)])
      (.seq (.ite .b (.block []) (.loop bodyTo .ae)) (.block (storeCtr ++ lastG ++ storeY))))) s
      (EPostTo s₀) := by
  refine WP.seq (WP.mono (firstTo_ok hp hR) fun s₂ hI₂ => ?_)
  refine WP.seq (WP.mono (cmpE_ok hI₂) fun s₃ ⟨hI₃, hcf⟩ => ?_)
  exact WP.seq (WP.mono (loopE_ok hp hm hf hI₃ hcf) fun s₄ ⟨e, he, hI₄⟩ => finalTo_ok hp hf he hI₄)

end VG.Proof.Gcm.X86_64.StitchTo
