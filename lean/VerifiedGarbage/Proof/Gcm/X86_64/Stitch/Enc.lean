module

import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Group
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes

/-! ### `Gcm.X86_64.Stitch.Loop`, which this module and modules that import it used -/

section

/-!
# Interleaved counter mode and GHASH: the encryption loop

`EInv s₀ P e s`: `e` groups of sixteen blocks are encrypted (`AInv`), the
first `e - 1` hashed into `Y` (in `xmm2`), the powers `P` in the working
space; `rdx` points to group `e - 1`, the next to hash. `body_ok`: a body
encrypts group `e` (two batches, `batch_ok`) while it hashes group `e - 1`
between their rounds (`gq_ok`), which they do not write (`QG.data`, the
in-place case of `QG.keepM`). It is
proven for any powers whose products add up to `GHASH` (`FinOk`), without
the field, which only `Stitch/Ok.lean` imports.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Proof.Gcm.X86_64.Vpclmul (zero_lanes)
open VG.Impl.Gcm.X86_64.Stitch (aregs batch gA gB body gq ordE)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame run_sep)
open VG.Spec.Gcm (Block blockAt ghashFrom inc32)

/-! ## The GHASH state, kept by the data written -/

/-- The GHASH state is kept by a write apart from the blocks still to read
and from the working space. -/
theorem QG.keepW {s₀ : State} {lo : Nat → Nat} {a : Addr} {X : Nat → Block}
    {P : Nat → Nat → Block} {yl : Nat → Block} {ord : Nat → Nat} {base : Nat} {fin : Bool} {j g : Nat}
    {R : Region} {b : Addr} (ha : a.toNat = b.toNat + 256 * g)
    (hsep : ∀ i, lo j ≤ i → i < 16 → Region.Disjoint ⟨b + BitVec.ofNat 64 (16 * (16 * g + i)), 16⟩ R)
    (hP : (pR s₀).Disjoint R)
    {t t' : State} (h : QG s₀ lo a X P yl ord base fin j t) (hgpr : t'.gpr = t.gpr) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hlane : ∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 2, t'.lane r l = t.lane r l)
    (hf : Frame [R] t.mem t'.mem) : QG s₀ lo a X P yl ord base fin j t' := by
  obtain ⟨hE, h1, h2⟩ := h
  obtain kp : ∀ l < 2, prod (t'.proj l) = prod (t.proj l) := fun l hl => by
    simp only [prod, State.proj_xmm, hlane .xmm8 (by decide) (by decide) l hl, hlane .xmm9 (by decide) (by decide) l hl,
      hlane .xmm10 (by decide) (by decide) l hl]
  refine ⟨⟨by rw [hgpr]; exact hE.rdx, by rw [hgpr]; exact hE.r11, fun i hi hi' => ?_, fun k hk l hl => ?_,
    fun k hk => by rw [hrd, hwr]; exact hE.ina k hk, fun k hk => by rw [hrd, hwr]; exact hE.inp k hk,
    fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact hE.m0 l hl⟩,
    fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact h1 l hl, ?_⟩
  · have e : a + BitVec.ofNat 64 (16 * i) = b + BitVec.ofNat 64 (16 * (16 * g + i)) := addr_eq (by omega_using [ha])
    rw [e, blockAt_frame hf fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact hsep i hi hi']
    have := hE.xs i hi hi'
    rwa [e] at this
  · rw [hf.readW (r := pR s₀) (Offset.contains_base _ (by omega_using [hk, hl]) (by omega_using [hk, hl]))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hP) (by decide)]
    exact hE.pv k hk l hl
  · split
    · rw [ite_t (by assumption)] at h2
      exact ⟨by rw [hlane _ (by decide) (by decide) 0 (by decide)]; exact h2.1,
        by rw [hlane _ (by decide) (by decide) 1 (by decide)]; exact h2.2⟩
    · rw [ite_f (by assumption)] at h2
      exact ⟨fun l hl => by rw [kp l hl]; exact h2.1 l hl,
        fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact h2.2 l hl⟩

/-- The GHASH state is kept by the output written, `QG.keepW`: in place,
blocks `c … c + 7` of the data, which the GHASH loads still to come do not
read; out of place, the output, apart from the data. -/
theorem QG.keepM {ix : Bool} {s₀ : State} (hp : LPre ix s₀) {lo : Nat → Nat} {a : Addr} {X : Nat → Block}
    {P : Nat → Nat → Block} {yl : Nat → Block} {ord : Nat → Nat} {base : Nat} {fin : Bool} {j c g : Nat}
    (hc : c + 8 ≤ nb s₀) (hg : 16 * g + 16 ≤ nb s₀) (ha : a.toNat = (dp s₀).toNat + 256 * g)
    (hsep : ix = false → ∀ i, lo j ≤ i → i < 16 → ¬ (c ≤ 16 * g + i ∧ 16 * g + i < c + 8))
    {t t' : State} (h : QG s₀ lo a X P yl ord base fin j t) (hgpr : t'.gpr = t.gpr) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hlane : ∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 2, t'.lane r l = t.lane r l)
    (hf : Frame [⟨wAddr ix s₀ c, 128⟩] t.mem t'.mem) : QG s₀ lo a X P yl ord base fin j t' := by
  have hw := hp.wrap_d
  have hww := hp.wrap_w
  refine QG.keepW ha (fun i hi hi' => ?_) (hp.w_p.symm.sub_right (Offset.sub_base _ (by omega_using [hc]))) h hgpr hrd hwr
    hlane hf
  cases ix
  · intro x h₁ h₂
    exact run_sep hw (by omega_using [hg, hi']) hc (hsep rfl i hi hi') h₁ h₂
  · exact ((hp.d_w rfl).sub_left (Offset.sub_base _ (by omega_using [hg, hi']))).sub_right (Offset.sub_base _ (by omega_using [hc]))

theorem QG.data {s₀ : State} (hp : SPre s₀) {lo : Nat → Nat} {a : Addr} {X : Nat → Block}
    {P : Nat → Nat → Block} {yl : Nat → Block} {ord : Nat → Nat} {base : Nat} {fin : Bool} {j c g : Nat}
    (hc : c + 8 ≤ nb s₀) (hg : 16 * g + 16 ≤ nb s₀) (ha : a.toNat = (dp s₀).toNat + 256 * g)
    (hsep : ∀ i, lo j ≤ i → i < 16 → ¬ (c ≤ 16 * g + i ∧ 16 * g + i < c + 8))
    {t t' : State} (h : QG s₀ lo a X P yl ord base fin j t) (hgpr : t'.gpr = t.gpr) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hlane : ∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 2, t'.lane r l = t.lane r l)
    (hf : Frame [⟨bAddr s₀ c, 128⟩] t.mem t'.mem) : QG s₀ lo a X P yl ord base fin j t' :=
  QG.keepM hp.toM hc hg ha (fun _ => hsep) h hgpr hrd hwr hlane hf

/-- What a batch writes, an output pair of eight blocks, is in the output. -/
theorem frame_w {ix : Bool} {s₀ : State} (hp : LPre ix s₀) {c : Nat} (hc : c + 8 ≤ nb s₀) {m m' : Mem}
    (h : Frame [⟨wAddr ix s₀ c, 128⟩] m m') : Frame [wR ix s₀] m m' :=
  h.sub fun r hr => ⟨wR ix s₀, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr
    exact fun a ha => VG.Proof.Aes.X86_64.AesNi.run_in hp.wrap_w hc (n := 8) ha⟩

/-- Two postconditions of the same code from the same state: its run is
deterministic. -/
theorem wp_and {c : Prog isa} {s : State} {Q R : State → Prop} (h₁ : WP isa c s Q) (h₂ : WP isa c s R) :
    WP isa c s fun s' => Q s' ∧ R s' := by
  obtain ⟨t₁, s₁, e₁, q₁⟩ := h₁
  obtain ⟨t₂, s₂, e₂, q₂⟩ := h₂
  obtain ⟨_, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, s₁, e₁, q₁, q₂⟩

/-! ## The encryption loop -/

structure EInv (s₀ : State) (P : Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInv s₀ (16 * e) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (dp s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map (ctb s₀))
  y1 : s.lane .xmm2 1 = 0

/-- `EInv`, in place or out of place: the output's blocks hashed, `rdx` at
the output's group `e - 1`, and, out of place, the distance from the output
to the data in `r8`. -/
structure EInvM (ix : Bool) (s₀ : State) (P : Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInvM ix s₀ (16 * e) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (wp ix s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  r8 : ix = true → s.gpr .r8 = dp s₀ - op s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → (ix = true → r ≠ .r8) → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map (ctb s₀))
  y1 : s.lane .xmm2 1 = 0

theorem EInv.toM {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (h : EInv s₀ P e s) :
    EInvM false s₀ P e s :=
  ⟨h.a.toM, h.one, h.rdx, h.r9, h.rax, fun h' => absurd h' (by decide),
    fun r h1 h2 _ h4 h5 => h.gpr r h1 h2 h4 h5, h.pw, h.m1, h.y, h.y1⟩

theorem EInvM.toEInv {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (h : EInvM false s₀ P e s) :
    EInv s₀ P e s :=
  ⟨h.a.toAInv, h.one, h.rdx, h.r9, h.rax, fun r h1 h2 h4 h5 => h.gpr r h1 h2 (fun h' => absurd h' (by decide)) h4 h5,
    h.pw, h.m1, h.y, h.y1⟩

/-- `bodyM_ok`, and what the body writes: the output. -/
theorem bodyM_okF {ix : Bool} {s₀ : State} (hp : LPre ix s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInvM ix s₀ P e s) :
    WP isa (body ix) s fun s' => (EInvM ix s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32))) ∧
      Frame [wR ix s₀] s.mem s'.mem := by
  have hw := hp.wrap_w
  have h1e := hI.one
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctb s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.lane .xmm2 l
  have ha : a.toNat = (wp ix s₀).toNat + 256 * (e - 1) := hI.rdx
  obtain hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (fun _ => by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (zero_lanes s) fun s₁ ⟨z₁, f₁, _⟩ => ?_)
  obtain hE₁ : GEnv s₀ 0 a X P s₁ :=
    { rdx := by rw [f₁.gpr]
      r11 := by rw [f₁.gpr, hr11]
      xs := fun i _ hi => by
        rw [f₁.mem, show a + BitVec.ofNat 64 (16 * i) = wAddr ix s₀ (16 * (e - 1) + i) from addr_eq (by omega_arith),
          hI.a.out _ (by omega_arith)]
      pv := fun k hk l hl => by rw [f₁.mem]; exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (32 * k) = wp ix s₀ + BitVec.ofNat 64 (256 * (e - 1) + 32 * k) from
            addr_eq (by omega_arith)]
        exact in_rdwr (in_sub hp.w_in (by omega_arith))
      inp := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega_arith))
      m0 := fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact hI.a.msk l hl }
  obtain hA₁ := hI.a.yframe f₁ (by decide) (by decide) (by decide)
  obtain hrdx₁ : (s₁.gpr .rdx).toNat + 32 * 8 = (wp ix s₀).toNat + 16 * (16 * e) := by
    rw [f₁.gpr]; show a.toNat + _ = _; omega_arith
  obtain hr8₁ : ix = true → s₁.gpr .r8 = if ix then dp s₀ - op s₀ else op s₀ - dp s₀ := fun hi => by
    subst hi; rw [f₁.gpr]; exact hI.r8 rfl
  -- The output written is apart from the previous group, which the loads read.
  obtain hsepA : ∀ c, 16 * e ≤ c → c + 8 ≤ nb s₀ → ∀ i, 0 ≤ i → i < 16 →
      Region.Disjoint ⟨wp ix s₀ + BitVec.ofNat 64 (16 * (16 * (e - 1) + i)), 16⟩ ⟨wAddr ix s₀ c, 128⟩ :=
    fun c hc hc' i _ hi => Offset.disjoint _ (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  obtain hP : ∀ c, c + 8 ≤ nb s₀ → (pR s₀).Disjoint ⟨wAddr ix s₀ c, 128⟩ := fun c hc =>
    hp.w_p.symm.sub_right (Offset.sub_base _ (by omega_arith))
  -- The first batch, with loads 1–4 of the previous group.
  refine WP.seq (WP.mono (batchM_ok (st := false) (ld := ix) hp (by cases ix <;> rfl) id gA gRegs gRegs_ok (QG s₀ (fun _ => 0) a X P yl ordE 0 false)
    (gq_ok (fun _ => Nat.le_refl _) (fun j hj1 hj4 => by
      rcases (by omega_arith : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, Nat.zero_le _⟩) (fun h => absurd h (by decide)))
    (fun j t t' h f => h.yframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.keepW ha (fun i hi hi' => hsepA _ (Nat.le_refl _) (by omega_arith) i hi hi')
      (hP _ (by omega_arith)) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 8) (by omega_arith) hA₁ hr8₁ hrdx₁
    ⟨hE₁, fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact hI.m1 l hl,
      by rw [ite_f (by decide)]
         exact ⟨fun l hl => z₁ l hl, fun l hl => by rw [f₁.lane _ (by decide) l hl]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  obtain hrdx₂ : (s₂.gpr .rdx).toNat + 32 * 12 = (wp ix s₀).toNat + 16 * (16 * e + 8) := by
    rw [hg₂, f₁.gpr]; show a.toNat + _ = _; omega_arith
  obtain hQ₂' : QG s₀ (fun _ => 0) a X P yl ordE 4 true 1 s₂ := by
    obtain ⟨hE, h1, h2⟩ := hQ₂
    rw [ite_f (by decide)] at h2
    exact ⟨hE, h1, by rw [ite_f (by decide)]; exact h2⟩
  -- The second batch, with loads 5–7 and 0 of the previous group, and the reduction.
  refine WP.seq (WP.mono (batchM_ok (st := false) (ld := ix) hp (by cases ix <;> rfl) id gB gRegs gRegs_ok (QG s₀ (fun _ => 0) a X P yl ordE 4 true)
    (gq_ok (fun _ => Nat.le_refl _) (fun j hj1 hj4 => by
      rcases (by omega_arith : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, Nat.zero_le _⟩) (fun _ => rfl))
    (fun j t t' h f => h.yframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.keepW ha (fun i hi hi' => hsepA _ (by omega_arith) (by omega_arith) i hi hi')
      (hP _ (by omega_arith)) h hg hrd hwr hl hf)
    (c := 16 * e + 8) (j := 12) (by omega_arith) hA₂ (fun hi => by rw [hg₂]; exact hr8₁ hi) hrdx₂ hQ₂')
    fun s₃ ⟨hA₃, hQ₃, hg₃, hl₃, hm₃⟩ => ?_)
  refine WP.mono (nextE_ok s₃) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, _, h2⟩ := hQ₃
  rw [ite_t ⟨rfl, by decide⟩] at h2
  -- The memory of the powers is kept.
  obtain dP : ∀ c, c + 8 ≤ nb s₀ → ∀ r' ∈ [(⟨wAddr ix s₀ c, 128⟩ : Region)], (pR s₀).Disjoint r' := fun c hc r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hP c hc
  obtain keepP : ∀ k < 8, ∀ l < 2, s'.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 =
      s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 :=
    fun k hk l hl => by
      rw [fm, hm₃.readW (r := pR s₀) (Offset.contains_base _ (by omega_arith) (by omega_arith)) (dP _ (by omega_arith)) (by decide),
        hm₂.readW (r := pR s₀) (Offset.contains_base _ (by omega_arith) (by omega_arith)) (dP _ (by omega_arith)) (by decide), f₁.mem]
  obtain gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₃, hg₂, f₁.gpr]
  obtain lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ gRegs → ∀ l < 2, s'.lane r l = s.lane r l :=
    fun r h13 h14 ha' hg' l hl => by
      rw [fl r l, hl₃ r h13 h14 ha' hg' l hl, hl₂ r h13 h14 ha' hg' l hl,
        f₁.lane r (fun h => hg' (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl <;> decide)) l hl]
  obtain hA' : AInvM ix s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 8 + 8 by omega_arith]
    exact ⟨hA₃.le, fun l hl => by rw [fl]; exact hA₃.ctr l hl, fun l hl => by rw [fl]; exact hA₃.msk l hl,
      fun l hl => by rw [fl]; exact hA₃.inc l hl,
      by rw [fg _ (by decide) (by decide)]; exact hA₃.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₃.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₃.r10, by rw [fm]; exact hA₃.frame,
      fun k hk => by rw [fm]; exact hA₃.out k hk, fun k hk hc => by rw [fm]; exact hA₃.src k hk hc,
      by rw [frd]; exact hA₃.rd, by rw [fwr]; exact hA₃.wr⟩
  obtain hr9 : s₃.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1 - 1)) := by
    rw [hg₃, hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega_arith) (by omega_arith)]
    congr 1; omega_arith
  obtain fr : Frame [wR ix s₀] s.mem s'.mem := by
    rw [fm, ← f₁.mem]
    exact (frame_w hp (by omega_arith) hm₂).trans (frame_w hp (by omega_arith) hm₃)
  refine ⟨⟨⟨hA', by omega_arith, ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun hi => by rw [gk _ (by decide) (by decide)]; exact hI.r8 hi,
    fun r h1 h2 h3 h4 h5 => by rw [gk r h2 h4]; exact hI.gpr r h1 h2 h3 h4 h5,
    fun k hk l hl => by rw [keepP k hk l hl]; exact hI.pw k hk l hl,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl]; exact hI.m1 l hl, ?_,
    by rw [fl]; exact h2.2⟩, ?_⟩, fr⟩
  · rw [frdx, hg₃, hg₂, f₁.gpr, BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (by show a.toNat + 256 < 2 ^ 64; omega_arith)]
    show a.toNat + 256 = _
    rw [ha, show e + 1 - 1 = (e - 1) + 1 by omega_arith, Nat.mul_succ, Nat.add_assoc]
  · rw [fl, h2.1, hf X yl hI.y1,
      show e + 1 - 1 = (e - 1) + 1 by omega_arith, ghash_append16, ← hI.y]
  · rw [fcf, hr9, toNat_ofNat_lt (by omega_arith), show e + 1 - 1 = e by omega_arith]

theorem bodyM_ok {ix : Bool} {s₀ : State} (hp : LPre ix s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInvM ix s₀ P e s) :
    WP isa (body ix) s fun s' => EInvM ix s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) :=
  WP.mono (bodyM_okF hp hf he hI) fun _ h => h.1

/-- `body_ok`, and what the body writes: the data. -/
theorem body_okF {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInv s₀ P e s) :
    WP isa body s fun s' => (EInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32))) ∧
      Frame [dR s₀] s.mem s'.mem :=
  WP.mono (bodyM_okF hp.toM hf he hI.toM) fun _ ⟨⟨h, hc⟩, f⟩ =>
    ⟨⟨h.toEInv, hc⟩, f.sub fun r hr => ⟨dR s₀, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩⟩

theorem body_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInv s₀ P e s) :
    WP isa body s fun s' => EInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) :=
  WP.mono (bodyM_ok hp.toM hf he hI.toM) fun _ ⟨h, hc⟩ => ⟨h.toEInv, hc⟩

end VG.Proof.Gcm.X86_64.Stitch

end

end

/-!
# Interleaved counter mode and GHASH: encryption

`Ready s₀ P s`: after the setup, nothing is encrypted (`AInv s₀ 0`), the
powers `P` are in the working space, `Y` in `xmm2`, `rdx` points to the data
(`setupT_ok`, after the powers are computed, which `Stitch/Ok.lean` proves in
the field). `first_ok`: the first group is encrypted (`EInv s₀ P 1`).
`encTail_ok`: the encryption after the setup, for any powers whose products
add up to `GHASH` (`FinOk`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (storesK pregs setupC first batch body ghLoad ordE storeCtr lastG storeY)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod toNat_ofNat_lt)
open VG.Proof.Gcm.X86_64.Vpclmul (zero_lanes)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

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

/-- A block outside the working space is kept by writes to it. -/
theorem blockAt_outP {s₀ : State} {m m' : Mem} {p : Addr} (hf : Frame [pR s₀] m m')
    (hd : Region.Disjoint ⟨p, 16⟩ (pR s₀)) : blockAt m' p = blockAt m p :=
  blockAt_frame hf fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd

/-- The setup after the powers (`setupG`): they are stored in the working
space, then `Y`, the counter, the increment and the pointers. -/
theorem setupT_okF {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) {s₁ : State} (l0 : ∀ l < 2, s₁.lane .xmm0 l = revMask)
    (l1 : ∀ l < 2, s₁.lane .xmm1 l = poly) (g₁ : ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) (m₁ : s₁.mem = s₀.mem)
    (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr) :
    WP isa (.block (storesK .r11 pregs 0 ++ setupC)) s₁ fun s =>
      Ready s₀ (fun k l => s₁.lane (preg16 k) l) s ∧ Frame [⟨pp s₀, 256⟩] s₀.mem s.mem := by
  have hwp := hp.wrap_p
  have hwd := hp.wrap_d
  obtain hr11 : s₁.gpr .r11 = pp s₀ := g₁ _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storesK_ok .r11 pregs 0 s₁ (fun k hk => by
      rw [wr₁, hr11]; exact in_sub_int hp.p_in (by simp [pregs] at hk; omega_arith))
    (by rw [hr11]; simp [pregs]; omega_arith)) fun s₂ ⟨sv, fr, g₂, rd₂, wr₂, l₂⟩ => ?_
  rw [hr11, Nat.mul_zero, BitVec.add_zero, show 32 * pregs.length = 256 from rfl, m₁] at fr
  have frS := fr
  replace fr : Frame [pR s₀] s₀.mem s₂.mem := fr.sub fun r hr => ⟨pR s₀, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩
  obtain hp₂ : ∀ {p : Addr}, Region.Disjoint ⟨p, 16⟩ (pR s₀) → blockAt s₂.mem p = blockAt s₀.mem p :=
    fun hd => by rw [blockAt_outP fr hd]
  refine WP.mono (setupC_ok s₂ (fun l hl => by rw [l₂]; exact l0 l hl)
    (by rw [wr₂, wr₁, g₂, g₁ _ (by decide)]; exact hp.y_in)
    (by rw [wr₂, wr₁, g₂, g₁ _ (by decide)]; exact hp.c_in))
    fun s₃ ⟨y0, y1, c14, c15, r10, rax, rdx, gk, lk, m₃, rd₃, wr₃⟩ => ?_
  obtain gs : ∀ r, r ≠ .rax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, g₁ r hr]
  refine ⟨?_, by rw [m₃]; exact frS⟩
  refine ⟨⟨Nat.zero_le _, fun l hl => ?_, fun l hl => ?_, c15, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_, ?_⟩,
    by rw [rdx, gs _ (by decide)], by rw [rax, gs _ (by decide)],
    fun r h1 h2 h3 => by rw [gk r h1 h2 h3, gs r h1], fun k hk l hl => ?_,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl, l₂]; exact l1 l hl,
    by rw [y0, gs _ (by decide), hp₂ (hp.p_y.symm)], y1⟩
  · rw [c14 l hl, gs _ (by decide), hp₂ hp.p_c.symm, Nat.zero_add]
  · rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl, l₂]; exact l0 l hl
  · rw [gk _ (by decide) (by decide) (by decide), gs _ (by decide)]
  · rw [gk _ (by decide) (by decide) (by decide), gs _ (by decide)]
  · rw [r10, gs _ (by decide), gs _ (by decide)]
  · rw [m₃]; exact fr.mono fun r hr => by simp at hr ⊢; exact Or.inr hr
  · rw [m₃, hp₂ (hp.d_p.sub_left (Offset.sub_base _ (by omega_arith)))]
    simp only [Nat.not_lt_zero, ite_false]
  · rw [rd₃, rd₂, rd₁]
  · rw [wr₃, wr₂, wr₁]
  · rw [m₃, show pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l) = s₁.gpr .r11 + BitVec.ofNat 64 (32 * (0 + k) + 16 * l)
      by rw [hr11, Nat.zero_add], sv k (by simp [pregs]; omega_arith) l hl, pregs_get]

theorem setupT_ok {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) {s₁ : State} (l0 : ∀ l < 2, s₁.lane .xmm0 l = revMask)
    (l1 : ∀ l < 2, s₁.lane .xmm1 l = poly) (g₁ : ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) (m₁ : s₁.mem = s₀.mem)
    (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr) :
    WP isa (.block (storesK .r11 pregs 0 ++ setupC)) s₁ (Ready s₀ fun k l => s₁.lane (preg16 k) l) :=
  WP.mono (setupT_okF hp l0 l1 g₁ m₁ rd₁ wr₁) fun _ h => h.1

/-- `Ready`, in place or out of place: `rdx` at the output, and, out of
place, the distance from the output to the data in `r8`. -/
structure ReadyM (ix : Bool) (s₀ : State) (P : Nat → Nat → Block) (s : State) : Prop where
  a : AInvM ix s₀ 0 s
  rdx : s.gpr .rdx = wp ix s₀
  r8 : ix = true → s.gpr .r8 = dp s₀ - op s₀
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → (ix = true → r ≠ .r8) → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = y₀ s₀
  y1 : s.lane .xmm2 1 = 0

theorem Ready.toM {s₀ : State} {P : Nat → Nat → Block} {s : State} (h : Ready s₀ P s) : ReadyM false s₀ P s :=
  ⟨h.a.toM, h.rdx, fun h' => absurd h' (by decide), h.rax, fun r h1 h2 _ h4 => h.gpr r h1 h2 h4, h.pw, h.m1, h.y, h.y1⟩

/-- `EPost`, in place or out of place, with the output block by block. -/
structure EPostM (ix : Bool) (s₀ s : State) : Prop where
  data : ∀ k < nb s₀, blockAt s.mem (wAddr ix s₀ k) = ctb s₀ k
  ctr : blockAt s.mem (cp s₀) = Nat.repeat inc32 (nb s₀) (cb s₀)
  y : blockAt s.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) ((List.range (nb s₀)).map (ctb s₀))
  frame : Frame [cR s₀, yR s₀, wR ix s₀, pR s₀] s₀.mem s.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → (ix = true → r ≠ .r8) → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The output as blocks: the hashed ones. -/
theorem EPostM.blocks {ix : Bool} {s₀ s : State} (h : EPostM ix s₀ s) :
    blocksAt s.mem (wp ix s₀) (nb s₀) = (List.range (nb s₀)).map (ctb s₀) := by
  simp only [blocksAt]
  exact List.map_congr_left fun k hk => h.data k (by simpa using hk)

theorem EPostM.toEPost {s₀ s : State} (h : EPostM false s₀ s) : EPost s₀ s :=
  ⟨blocks_ctr32 h.data, h.ctr, by rw [h.y]; exact congrArg _ h.blocks.symm, h.frame,
    fun r h1 h2 h4 h5 => h.gpr r h1 h2 (fun h' => absurd h' (by decide)) h4 h5, h.rd, h.wr⟩

/-- The first group: two batches, with nothing between their rounds. -/
theorem firstM_okF {ix : Bool} {s₀ : State} (hp : LPre ix s₀) (h16 : 16 ≤ nb s₀) {P : Nat → Nat → Block} {s : State}
    (hR : ReadyM ix s₀ P s) :
    WP isa (first ix) s fun s' => EInvM ix s₀ P 1 s' ∧ Frame [wR ix s₀] s.mem s'.mem := by
  have hwp := hp.wrap_p
  have hwd := hp.wrap_w
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  obtain none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ YFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, YFrame.refl _ _⟩
  obtain hr8 : ix = true → s.gpr .r8 = if ix then dp s₀ - op s₀ else op s₀ - dp s₀ := fun hi => by
    subst hi; exact hR.r8 rfl
  refine WP.seq (WP.mono (batchM_ok (st := false) (ld := ix) hp (by cases ix <;> rfl) id (fun _ => []) [] (by simp)
    (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 0) (j := 0) (by omega_arith) hR.a hr8
    (by rw [hR.rdx]) trivial) fun s₁ ⟨hA₁, _, hg₁, hl₁, hm₁⟩ => ?_)
  refine WP.mono (batchM_ok (st := false) (ld := ix) hp (by cases ix <;> rfl) id (fun _ => []) [] (by simp)
    (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 0 + 8) (j := 4) (by omega_arith) hA₁
    (fun hi => by rw [hg₁]; exact hr8 hi) (by rw [hg₁, hR.rdx]) trivial) fun s₂ ⟨hA₂, _, hg₂, hl₂, hm₂⟩ => ?_
  obtain dP : ∀ c, c + 8 ≤ nb s₀ → ∀ r' ∈ [(⟨wAddr ix s₀ c, 128⟩ : Region)], (pR s₀).Disjoint r' := fun c hc r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.w_p.symm.sub_right (Offset.sub_base _ (by omega_arith))
  obtain lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ VG.Impl.Gcm.X86_64.Stitch.aregs → ∀ l < 2,
      s₂.lane r l = s.lane r l := fun r h13 h14 hr l hl => by
    rw [hl₂ r h13 h14 hr (by simp) l hl, hl₁ r h13 h14 hr (by simp) l hl]
  obtain gk : s₂.gpr = s.gpr := by rw [hg₂, hg₁]
  refine ⟨?_, (frame_w hp (by omega_arith) hm₁).trans (frame_w hp (by omega_arith) hm₂)⟩
  refine ⟨by simpa using hA₂, Nat.le_refl _, by rw [gk, hR.rdx]; simp, ?_, by rw [gk]; exact hR.rax,
    fun hi => by rw [gk]; exact hR.r8 hi, fun r h1 h2 h3 _ h5 => by rw [gk]; exact hR.gpr r h1 h2 h3 h5, fun k hk l hl => ?_,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) l hl]; exact hR.m1 l hl,
    by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide), hR.y]; simp [ghashFrom],
    by rw [lk _ (by decide) (by decide) (by decide) 1 (by decide)]; exact hR.y1⟩
  · rw [gk, hR.gpr _ (by decide) (by decide) (fun _ => by decide) (by decide)]; simp
  · rw [hm₂.readW (r := pR s₀) (Offset.contains_base _ (by omega_arith) (by omega_arith)) (dP _ (by omega_arith)) (by decide),
      hm₁.readW (r := pR s₀) (Offset.contains_base _ (by omega_arith) (by omega_arith)) (dP _ (by omega_arith)) (by decide)]
    exact hR.pw k hk l hl

theorem firstM_ok {ix : Bool} {s₀ : State} (hp : LPre ix s₀) (h16 : 16 ≤ nb s₀) {P : Nat → Nat → Block} {s : State}
    (hR : ReadyM ix s₀ P s) :
    WP isa (first ix) s (EInvM ix s₀ P 1) :=
  WP.mono (firstM_okF hp h16 hR) fun _ h => h.1

/-! ## The loop -/

/-- `cmp r9, 32`, which writes no memory. -/
theorem cmpEM_okF {ix : Bool} {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (hI : EInvM ix s₀ P e s) :
    WP isa (.block [.alu .cmp .r9 (.imm 32)]) s fun s' =>
      (EInvM ix s₀ P e s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e - 1) < 32))) ∧ s'.mem = s.mem := by
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  obtain e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  have hr9 := hI.r9
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    hr9, e32, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨{ hI with a := { hI.a with } }, ?_⟩, trivial⟩
  rw [toNat_ofNat_lt (by omega_arith)]; rfl

theorem cmpEM_ok {ix : Bool} {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (hI : EInvM ix s₀ P e s) :
    WP isa (.block [.alu .cmp .r9 (.imm 32)]) s fun s' =>
      EInvM ix s₀ P e s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e - 1) < 32)) :=
  WP.mono (cmpEM_okF hI) fun _ h => h.1

/-- The loop, from any group `e₀` on, and what it writes: the output. -/
theorem loopEM_from_okF {ix : Bool} {s₀ : State} (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block} (hp : LPre ix s₀)
    (hf : FinOk ordE (hk s₀) P) {e₀ : Nat} {s : State}
    (hI : EInvM ix s₀ P e₀ s) (hcf : s.cf = some (decide (nb s₀ - 16 * (e₀ - 1) < 32))) :
    WP isa (.ite .b (.block []) (.loop (body ix) .ae)) s fun s' =>
      (∃ e, nb s₀ = 16 * e ∧ EInvM ix s₀ P e s') ∧ Frame [wR ix s₀] s.mem s'.mem := by
  obtain fin : ∀ e, nb s₀ - 16 * (e - 1) < 32 → ∀ t, EInvM ix s₀ P e t → Frame [wR ix s₀] s.mem t.mem →
      (∃ e, nb s₀ = 16 * e ∧ EInvM ix s₀ P e t) ∧ Frame [wR ix s₀] s.mem t.mem :=
    fun e he t hI hF => ⟨⟨e, by have := hI.a.le; have := hI.one; omega_arith, hI⟩, hF⟩
  refine WP.ite (decide (nb s₀ - 16 * (e₀ - 1) < 32)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil (fin e₀ (by simpa using h) s hI (Frame.refl _ _))
  · let I : Nat → State → Prop := fun m t => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ EInvM ix s₀ P e t ∧
      Frame [wR ix s₀] s.mem t.mem
    obtain hstep : ∀ m t, I m t → WP isa (body ix) t (fun s' =>
        (eval .ae s' = some false ∧ ((∃ e, nb s₀ = 16 * e ∧ EInvM ix s₀ P e s') ∧ Frame [wR ix s₀] s.mem s'.mem)) ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m t ⟨e, rfl, he, hI, hF⟩
      refine WP.mono (bodyM_okF hp hf he hI) fun s' ⟨⟨hI', hcf'⟩, hF'⟩ => ?_
      by_cases hlt : nb s₀ - 16 * e < 32
      · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
          fin (e + 1) (by simpa using hlt) s' hI' (hF.trans hF')⟩
      · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
          nb s₀ - 16 * (e + 1), by have := hI.one; omega_arith, e + 1, rfl, by omega_arith, hI', hF.trans hF'⟩
    have := hI.one; have := hI.a.le
    exact WP.loop (M := isa) I hstep (nb s₀ - 16 * e₀) s ⟨e₀, rfl, by simp at h; omega_arith, hI, Frame.refl _ _⟩

/-- The loop, from any group `e₀` on. -/
theorem loopEM_from_ok {ix : Bool} {s₀ : State} (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block} (hp : LPre ix s₀)
    (hf : FinOk ordE (hk s₀) P) {e₀ : Nat} {s : State}
    (hI : EInvM ix s₀ P e₀ s) (hcf : s.cf = some (decide (nb s₀ - 16 * (e₀ - 1) < 32))) :
    WP isa (.ite .b (.block []) (.loop (body ix) .ae)) s fun s' => ∃ e, nb s₀ = 16 * e ∧ EInvM ix s₀ P e s' :=
  WP.mono (loopEM_from_okF hm hp hf hI hcf) fun _ h => h.1

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
    obtain hk : ordE n < 8 := by
      rcases (by omega_arith : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact WP.mono (ghStep hk (Nat.zero_le _) hE₁ p₁ y₁) fun s' ⟨hE', p', y', f'⟩ => ⟨hE', p', y', f₁.trans f'⟩

/-! ## The whole encryption -/

theorem finalM_okF {ix : Bool} {s₀ : State} (hp : LPre ix s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P)
    {e : Nat} (he : nb s₀ = 16 * e) {s : State} (hI : EInvM ix s₀ P e s) :
    WP isa (.block (storeCtr ++ lastG ++ storeY)) s fun s' => EPostM ix s₀ s' ∧ Frame [cR s₀, yR s₀] s.mem s'.mem := by
  have hw := hp.wrap_w
  have hwp := hp.wrap_p
  have h1e := hI.one
  obtain hm0 : s.lane .xmm0 0 = revMask := hI.a.msk 0 (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (store16_ok .xmm13 .xmm14 .rax s hm0 (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  -- The counter's memory is neither the data nor the working space.
  obtain cD : ∀ k < nb s₀, Region.Disjoint ⟨wAddr ix s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.w_c.sub_left (Offset.sub_base _ (by omega_arith))
  obtain cP : ∀ k < 8, ∀ l < 2, Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l), 16⟩ (cR s₀) := fun k hk l hl =>
    hp.p_c.sub_left (Offset.sub_base _ (by omega_arith))
  rw [hI.rax] at m₁
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctb s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.lane .xmm2 l
  have ha : a.toNat = (wp ix s₀).toNat + 256 * (e - 1) := hI.rdx
  obtain hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (fun _ => by decide) (by decide) (by decide)
  simp only [lastG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_lanes s₁) fun s₂ ⟨z₂, f₂, _⟩ => ?_
  obtain hE₂ : GEnv s₀ 0 a X P s₂ :=
    { rdx := by rw [f₂.gpr, g₁]
      r11 := by rw [f₂.gpr, g₁, hr11]
      xs := fun i _ hi => by
        rw [f₂.mem, m₁, show a + BitVec.ofNat 64 (16 * i) = wAddr ix s₀ (16 * (e - 1) + i) from addr_eq (by omega_arith),
          blockAt_writeW_sep' (cD _ (by omega_arith)) rfl, hI.a.out _ (by omega_arith)]
      pv := fun k hk l hl => by
        rw [f₂.mem, m₁, Mem.readW_writeW_sep ((cP k hk l hl).sep (Region.contains_self _ _) (Region.contains_self _ _))
          (by decide)]
        exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₂.rd, f₂.wr, rd₁, wr₁, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (32 * k) = wp ix s₀ + BitVec.ofNat 64 (256 * (e - 1) + 32 * k) from
            addr_eq (by omega_arith)]
        exact in_rdwr (in_sub hp.w_in (by omega_arith))
      inp := fun k hk => by
        rw [f₂.rd, f₂.wr, rd₁, wr₁, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega_arith))
      m0 := fun l hl => by rw [f₂.lane _ (by decide) l hl, l₁ _ (by decide) l hl]; exact hI.a.msk l hl }
  rw [WP.block_append_iff]
  refine WP.mono (ghRun_ok (yl := yl) 8 (Nat.le_refl _) s₂ hE₂ z₂
    (fun l hl => by rw [f₂.lane _ (by decide) l hl, l₁ _ (by decide) l hl])) fun s₃ ⟨hE₃, p₃, _, f₃⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (ghFin hE₃ (fun l hl => by
      rw [f₃.lane _ (by decide) l hl, f₂.lane _ (by decide) l hl, l₁ _ (by decide) l hl]; exact hI.m1 l hl))
    fun s₄ ⟨_, y4, _, f₄⟩ => ?_
  rw [p₃ 0 (by decide), p₃ 1 (by decide)] at y4
  obtain hm0₄ : s₄.lane .xmm0 0 = revMask := by
    rw [f₄.lane _ (by decide) 0 (by decide), f₃.lane _ (by decide) 0 (by decide),
      f₂.lane _ (by decide) 0 (by decide), l₁ _ (by decide) 0 (by decide)]; exact hm0
  obtain g₄ : s₄.gpr = s.gpr := by rw [f₄.gpr, f₃.gpr, f₂.gpr, g₁]
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl,
    WP.block_append_iff]
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx s₄ hm0₄ (by
      rw [g₄, f₄.wr, f₃.wr, f₂.wr, wr₁, hI.a.wr, hI.gpr _ (by decide) (by decide) (fun _ => by decide) (by decide) (by decide)]
      exact hp.y_in)) fun s₅ ⟨m₅, g₅, rd₅, wr₅, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  obtain hrcx : s.gpr .rcx = yp s₀ := hI.gpr _ (by decide) (by decide) (fun _ => by decide) (by decide) (by decide)
  rw [g₄, hrcx] at m₅
  obtain m₄ : s₄.mem = s₁.mem := by rw [f₄.mem, f₃.mem, f₂.mem]
  rw [m₄, m₁] at m₅
  -- The final memory: the counter, then `Y`, written.
  obtain yD : ∀ k < nb s₀, Region.Disjoint ⟨wAddr ix s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.w_y.sub_left (Offset.sub_base _ (by omega_arith))
  obtain hb : ∀ k < nb s₀, blockAt s₅.mem (wAddr ix s₀ k) = ctb s₀ k := fun k hk => by
    rw [m₅, blockAt_writeW_sep' (yD k hk) rfl, blockAt_writeW_sep' (cD k hk) rfl]
    exact hI.a.out k (by omega_arith)
  refine ⟨?_, by
    show Frame _ s.mem s₅.mem
    rw [m₅]
    exact ((Frame.refl _ _).writeW (r := cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := yR s₀) (by simp) _
      (Region.contains_self _ _)⟩
  refine ⟨hb, ?_, ?_, ?_, ?_, by
      show s₅.rd = _; rw [rd₅, f₄.rd, f₃.rd, f₂.rd, rd₁, hI.a.rd], by
      show s₅.wr = _; rw [wr₅, f₄.wr, f₃.wr, f₂.wr, wr₁, hI.a.wr]⟩
  · show blockAt s₅.mem (cp s₀) = _
    rw [m₅, blockAt_writeW_sep' hp.c_y rfl, VG.Proof.Gcm.X86_64.blockAt_store, hI.a.ctr 0 (by decide), Nat.add_zero, he]
  · show blockAt s₅.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) ((List.range (nb s₀)).map (ctb s₀))
    rw [he, m₅, VG.Proof.Gcm.X86_64.blockAt_store, y4]
    refine (hf X yl hI.y1).trans ?_
    rw [show 16 * e = 16 * ((e - 1) + 1) by congr 1; omega_arith, ghash_append16]
    exact congrArg (fun y => ghashFrom (hk s₀) y ((List.range 16).map X)) hI.y
  · show Frame _ s₀.mem s₅.mem
    rw [m₅]
    exact ((hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := yR s₀) (by simp) _
      (Region.contains_self _ _)
  · intro r h1 h2 h3 h4 h5
    show s₅.gpr r = _
    rw [g₅, g₄]; exact hI.gpr r h1 h2 h3 h4 h5

theorem finalM_ok {ix : Bool} {s₀ : State} (hp : LPre ix s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P)
    {e : Nat} (he : nb s₀ = 16 * e) {s : State} (hI : EInvM ix s₀ P e s) :
    WP isa (.block (storeCtr ++ lastG ++ storeY)) s (EPostM ix s₀) :=
  WP.mono (finalM_okF hp hf he hI) fun _ h => h.1

/-- The encryption after the setup, and what it writes: the counter, `Y` and
the output. -/
theorem encTailM_okF {ix : Bool} {s₀ : State} (hp : LPre ix s₀) (h16 : 16 ≤ nb s₀) (hm : nb s₀ % 16 = 0)
    {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {s : State} (hR : ReadyM ix s₀ P s) :
    WP isa (.seq (first ix) (.seq (.block [.alu .cmp .r9 (.imm 32)])
      (.seq (.ite .b (.block []) (.loop (body ix) .ae)) (.block (storeCtr ++ lastG ++ storeY))))) s fun s' =>
      EPostM ix s₀ s' ∧ Frame [cR s₀, yR s₀, wR ix s₀] s.mem s'.mem := by
  refine WP.seq (WP.mono (firstM_okF hp h16 hR) fun s₂ ⟨hI₂, f₂⟩ => ?_)
  refine WP.seq (WP.mono (cmpEM_okF hI₂) fun s₃ ⟨⟨hI₃, hcf⟩, m₃⟩ => ?_)
  refine WP.seq (WP.mono (loopEM_from_okF hm hp hf hI₃ hcf) fun s₄ ⟨⟨e, he, hI₄⟩, f₄⟩ => ?_)
  refine WP.mono (finalM_okF hp hf he hI₄) fun s₅ ⟨h, f₅⟩ => ⟨h, ?_⟩
  obtain sw : ∀ r ∈ [wR ix s₀], r ∈ [cR s₀, yR s₀, wR ix s₀] := fun r hr => by simp at hr; simp [hr]
  rw [m₃] at f₄
  exact ((f₂.mono sw).trans (f₄.mono sw)).trans (f₅.mono fun r hr => by simp at hr; rcases hr with h | h <;> simp [h])

/-- The encryption after the setup. -/
theorem encTailM_ok {ix : Bool} {s₀ : State} (hp : LPre ix s₀) (h16 : 16 ≤ nb s₀) (hm : nb s₀ % 16 = 0)
    {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {s : State} (hR : ReadyM ix s₀ P s) :
    WP isa (.seq (first ix) (.seq (.block [.alu .cmp .r9 (.imm 32)])
      (.seq (.ite .b (.block []) (.loop (body ix) .ae)) (.block (storeCtr ++ lastG ++ storeY))))) s (EPostM ix s₀) := by
  refine WP.seq (WP.mono (firstM_ok hp h16 hR) fun s₂ hI₂ => ?_)
  refine WP.seq (WP.mono (cmpEM_ok hI₂) fun s₃ ⟨hI₃, hcf⟩ => ?_)
  exact WP.seq (WP.mono (loopEM_from_ok hm hp hf hI₃ hcf) fun s₄ ⟨e, he, hI₄⟩ => finalM_ok hp hf he hI₄)


/-! ## In place -/

theorem first_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} {s : State} (hR : Ready s₀ P s) :
    WP isa first s (EInv s₀ P 1) :=
  WP.mono (firstM_ok hp.toM hp.nb16 hR.toM) fun _ h => h.toEInv

theorem cmpE_ok {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (hI : EInv s₀ P e s) :
    WP isa (.block [.alu .cmp .r9 (.imm 32)]) s fun s' =>
      EInv s₀ P e s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e - 1) < 32)) :=
  WP.mono (cmpEM_ok hI.toM) fun _ ⟨h, hc⟩ => ⟨h.toEInv, hc⟩

theorem loopE_from_ok {s₀ : State} (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block} (hp : SPre s₀)
    (hf : FinOk ordE (hk s₀) P) {e₀ : Nat} {s : State}
    (hI : EInv s₀ P e₀ s) (hcf : s.cf = some (decide (nb s₀ - 16 * (e₀ - 1) < 32))) :
    WP isa (.ite .b (.block []) (.loop body .ae)) s fun s' => ∃ e, nb s₀ = 16 * e ∧ EInv s₀ P e s' :=
  WP.mono (loopEM_from_ok hm hp.toM hf hI.toM hcf) fun _ ⟨e, he, h⟩ => ⟨e, he, h.toEInv⟩

theorem loopE_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {s : State}
    (hI : EInv s₀ P 1 s) (hcf : s.cf = some (decide (nb s₀ - 16 * (1 - 1) < 32))) :
    WP isa (.ite .b (.block []) (.loop body .ae)) s fun s' => ∃ e, nb s₀ = 16 * e ∧ EInv s₀ P e s' :=
  loopE_from_ok hm hp hf hI hcf

theorem final_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {e : Nat}
    (he : nb s₀ = 16 * e) {s : State} (hI : EInv s₀ P e s) :
    WP isa (.block (storeCtr ++ lastG ++ storeY)) s (EPost s₀) :=
  WP.mono (finalM_ok hp.toM hf he hI.toM) fun _ h => h.toEPost

theorem first_okF {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} {s : State} (hR : Ready s₀ P s) :
    WP isa first s fun s' => EInv s₀ P 1 s' ∧ Frame [dR s₀] s.mem s'.mem :=
  WP.mono (firstM_okF hp.toM hp.nb16 hR.toM) fun _ ⟨h, f⟩ => ⟨h.toEInv, f⟩

theorem cmpE_okF {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (hI : EInv s₀ P e s) :
    WP isa (.block [.alu .cmp .r9 (.imm 32)]) s fun s' =>
      (EInv s₀ P e s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e - 1) < 32))) ∧ s'.mem = s.mem :=
  WP.mono (cmpEM_okF hI.toM) fun _ ⟨⟨h, hc⟩, m⟩ => ⟨⟨h.toEInv, hc⟩, m⟩

theorem final_okF {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {e : Nat}
    (he : nb s₀ = 16 * e) {s : State} (hI : EInv s₀ P e s) :
    WP isa (.block (storeCtr ++ lastG ++ storeY)) s fun s' => EPost s₀ s' ∧ Frame [cR s₀, yR s₀] s.mem s'.mem :=
  WP.mono (finalM_okF hp.toM hf he hI.toM) fun _ ⟨h, f⟩ => ⟨h.toEPost, f⟩

/-- The encryption after the setup, and what it writes. -/
theorem encTail_okF {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {s : State}
    (hR : Ready s₀ P s) :
    WP isa (.seq first (.seq (.block [.alu .cmp .r9 (.imm 32)])
      (.seq (.ite .b (.block []) (.loop body .ae)) (.block (storeCtr ++ lastG ++ storeY))))) s fun s' =>
      EPost s₀ s' ∧ Frame [cR s₀, yR s₀, dR s₀] s.mem s'.mem :=
  WP.mono (encTailM_okF hp.toM hp.nb16 hm hf hR.toM) fun _ ⟨h, f⟩ => ⟨h.toEPost, f⟩

/-- The encryption after the setup. -/
theorem encTail_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {s : State}
    (hR : Ready s₀ P s) :
    WP isa (.seq first (.seq (.block [.alu .cmp .r9 (.imm 32)])
      (.seq (.ite .b (.block []) (.loop body .ae)) (.block (storeCtr ++ lastG ++ storeY))))) s (EPost s₀) :=
  WP.mono (encTailM_ok hp.toM hp.nb16 hm hf hR.toM) fun _ h => h.toEPost

end VG.Proof.Gcm.X86_64.Stitch
