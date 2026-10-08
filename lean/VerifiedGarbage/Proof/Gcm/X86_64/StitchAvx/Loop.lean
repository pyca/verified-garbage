import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Gh

/-!
# Interleaved counter mode and GHASH in AVX: the loops

`group_ok`: a group of four batches (`batch_ok`), with the GHASH work of an
order between their rounds (`gq_ok`), which the data they write does not
undo (`QG.data`). The loops are proven for any powers `P` in the working
space whose products add up to `GHASH` over sixteen blocks (`FinOk`, which
`Proof/Gcm/X86_64/StitchAvx/Ok.lean` proves of the powers the setup
stores), from the state the setup leaves (`Ready`):

* encryption (`encTail_ok`): `EInv s₀ P e s`: `e` groups are encrypted
  (`AInv`), the first `e − 1` hashed into `Y`; `rdx` points to group `e − 1`,
  the next to hash, which a body hashes while it encrypts group `e`
  (`body_ok`); the last group is hashed alone (`final_ok`);
* decryption (`decTail_ok`): `DInv s₀ P e s`: `e` groups are decrypted and
  hashed (the blocks as they were); `rdx` points to group `e`, which a body
  hashes while it decrypts it, each batch reading its own blocks before
  overwriting them (`dbody_ok`).
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB prod)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.StitchAvx (aregs batch gq group ordE ordD first body dbody ghLoad lastG)
open VG.Impl.Gcm.X86_64.Stitch (storeCtr storeY)
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost DPost kp nr cp yp dp nb pp kR cR yR dR pR sch ciph cb hk y₀ bAddr
  blk ctb in_sub in_sub_int in_rdwr addr_eq ghash_append16 nextE_ok nextD_ok store16_ok blocks_ctr32
  blockAt_writeW_sep')
open VG.Proof.Aes.X86_64.AesNi (Keys blockAt_frame)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

theorem toNat_ofNat' {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## A group -/

/-- One batch of a group, the `b`-th of four. -/
theorem batchG_ok {s₀ : State} (hp : SPre s₀) {ord : Nat → Nat} {lo : Nat → Nat} {a : Addr}
    {X P : Nat → Block} {y : Block} {g c b j : Nat} {fin : Bool} (hfin : fin = true → b = 3)
    (hmono : ∀ j', lo j' ≤ lo (j' + 1))
    (hrd : ∀ j', 1 ≤ j' → j' ≤ 4 → ord (4 * b + j' - 1) < 16 ∧ lo j' ≤ ord (4 * b + j' - 1))
    (hsep : ∀ i, lo 10 ≤ i → i < 16 → ¬ (c ≤ 16 * g + i ∧ 16 * g + i < c + 4))
    (hc : c + 4 ≤ nb s₀) (hg : 16 * g + 16 ≤ nb s₀) (ha : a.toNat = (dp s₀).toNat + 256 * g)
    {s : State} (hI : AInv s₀ c s) (hrdx : (s.gpr .rdx).toNat + 16 * j = (dp s₀).toNat + 16 * c)
    (hQ : QG s₀ lo a X P y ord (4 * b) fin 1 s) :
    WP isa (batch j (gq ord (4 * b) fin)) s fun s' => AInv s₀ (c + 4) s' ∧
      QG s₀ lo a X P y ord (4 * b) fin 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ gRegs → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      Frame [⟨bAddr s₀ c, 64⟩] s.mem s'.mem :=
  batch_ok hp _ gRegs gRegs_ok (QG s₀ lo a X P y ord (4 * b) fin)
    (gq_ok hmono hrd (fun h => by rw [hfin h]))
    (fun _ _ _ h f => h.yframe f (by decide))
    (fun _ _ h hg' hrd' hwr hl hf => QG.data hp hc hg ha hsep h hg' hrd' hwr hl hf) hc hI hrdx hQ

theorem QG.next {s₀ : State} {lo lo' : Nat → Nat} {a : Addr} {X P : Nat → Block} {y : Block}
    {ord : Nat → Nat} {base base' : Nat} {fin : Bool} {s : State}
    (h : QG s₀ lo a X P y ord base false 10 s) (hl : lo 10 ≤ lo' 1) (hb : base' = base + 4) :
    QG s₀ lo' a X P y ord base' fin 1 s := by
  obtain ⟨hE, h1, h2⟩ := h
  rw [ite_f (by simp)] at h2
  refine ⟨hE.mono hl, h1, ?_⟩
  rw [ite_f (by omega), hb]
  exact h2

theorem frame_group {s₀ : State} {c b : Nat} {m m' : Mem} (h : Frame [⟨bAddr s₀ (c + 4 * b), 64⟩] m m')
    (hb : b < 4) : Frame [⟨bAddr s₀ c, 256⟩] m m' :=
  h.sub fun r hr => ⟨_, List.mem_cons_self, by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩

theorem group_ok {s₀ : State} (hp : SPre s₀) {ord : Nat → Nat} {lo : Nat → Nat → Nat} {a : Addr}
    {X P : Nat → Block} {y : Block} {g c j : Nat}
    (hmono : ∀ b j', lo b j' ≤ lo b (j' + 1)) (hnext : ∀ b, lo b 10 ≤ lo (b + 1) 1)
    (hrd : ∀ b < 4, ∀ j', 1 ≤ j' → j' ≤ 4 → ord (4 * b + j' - 1) < 16 ∧ lo b j' ≤ ord (4 * b + j' - 1))
    (hsep : ∀ b < 4, ∀ i, lo b 10 ≤ i → i < 16 → ¬ (c + 4 * b ≤ 16 * g + i ∧ 16 * g + i < c + 4 * b + 4))
    (hc : c + 16 ≤ nb s₀) (hg : 16 * g + 16 ≤ nb s₀) (ha : a.toNat = (dp s₀).toNat + 256 * g)
    {s : State} (hI : AInv s₀ c s) (hrdx : (s.gpr .rdx).toNat + 16 * j = (dp s₀).toNat + 16 * c)
    (hQ : QG s₀ (lo 0) a X P y ord 0 false 1 s) :
    WP isa (group ord j) s fun s' => AInv s₀ (c + 16) s' ∧ QG s₀ (lo 3) a X P y ord 12 true 10 s' ∧
      s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ gRegs → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      Frame [⟨bAddr s₀ c, 256⟩] s.mem s'.mem := by
  have hs : ∀ b < 4, ∀ i, lo b 10 ≤ i → i < 16 →
      ¬ (c + 4 * b ≤ 16 * g + i ∧ 16 * g + i < c + 4 * b + 4) := hsep
  refine WP.seq (WP.mono (batchG_ok (b := 0) (fin := false) hp (fun h => absurd h (by decide)) (hmono 0)
    (hrd 0 (by decide)) (by simpa using hs 0 (by decide)) (by omega) hg ha hI (j := j) hrdx hQ)
    fun s₁ ⟨hA₁, hQ₁, hg₁, hl₁, hm₁⟩ => ?_)
  refine WP.seq (WP.mono (batchG_ok (b := 1) (fin := false) hp (fun h => absurd h (by decide)) (hmono 1)
    (hrd 1 (by decide)) (hs 1 (by decide)) (by omega) hg ha hA₁ (j := j + 4) (by rw [hg₁]; omega)
    (QG.next hQ₁ (hnext 0) rfl)) fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  refine WP.seq (WP.mono (batchG_ok (b := 2) (fin := false) hp (fun h => absurd h (by decide)) (hmono 2)
    (hrd 2 (by decide)) (by simpa [Nat.add_assoc] using hs 2 (by decide)) (by omega) hg ha hA₂ (j := j + 8)
    (by rw [hg₂, hg₁]; omega) (QG.next hQ₂ (hnext 1) rfl)) fun s₃ ⟨hA₃, hQ₃, hg₃, hl₃, hm₃⟩ => ?_)
  refine WP.mono (batchG_ok (b := 3) (fin := true) hp (fun _ => rfl) (hmono 3)
    (hrd 3 (by decide)) (by simpa [Nat.add_assoc] using hs 3 (by decide)) (by omega) hg ha hA₃ (j := j + 12)
    (by rw [hg₃, hg₂, hg₁]; omega) (QG.next hQ₃ (hnext 2) rfl)) fun s₄ ⟨hA₄, hQ₄, hg₄, hl₄, hm₄⟩ => ?_
  refine ⟨by simpa [Nat.add_assoc] using hA₄, hQ₄, by rw [hg₄, hg₃, hg₂, hg₁],
    fun r h13 h14 ha' hg' l hl => by
      rw [hl₄ r h13 h14 ha' hg' l hl, hl₃ r h13 h14 ha' hg' l hl, hl₂ r h13 h14 ha' hg' l hl,
        hl₁ r h13 h14 ha' hg' l hl], ?_⟩
  exact (frame_group (b := 0) (by simpa using hm₁) (by decide)).trans
    ((frame_group (b := 1) hm₂ (by decide)).trans
      ((frame_group (b := 2) (by simpa [Nat.add_assoc] using hm₃) (by decide)).trans
        (frame_group (b := 3) (by simpa [Nat.add_assoc] using hm₄) (by decide))))

/-- Clear the product. -/
theorem zero_ok (s : State) :
    WP isa (.block Impl.Gcm.X86_64.StitchAvx.zero) s fun s' => prod (s'.proj 0) = Prod.zero ∧
      YFrame [.xmm8, .xmm9, .xmm10] s s' := by
  refine WP.mono (WP.lane0 (ss := Impl.Gcm.X86_64.Pclmul.zero) rfl (Pclmul.zero_ok (s.proj 0)))
    fun s' ⟨⟨z, o⟩, hi, hg⟩ => ⟨z, hg rfl, by simpa using o.mem, by simpa using o.rd, by simpa using o.wr,
      fun r hr l hl => ?_⟩
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · simpa using o.xmm r hr
  · refine hi r ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h8, h9, h10⟩ := hr
    simp [Impl.Gcm.X86_64.StitchAvx.zero, vdst, h8, h9, h10]

/-- What the products of a group, in the order `ord`, add up to, for the
powers `P`. -/
def FinOk (ord : Nat → Nat) (H : Block) (P : Nat → Block) : Prop :=
  ∀ X y, reduceB (accN ord X P y 16) = ghashFrom H y ((List.range 16).map X)

/-- What the setup leaves: nothing encrypted, the powers `P` in the working
space, `Y` in `xmm2`, `rdx` pointing to the data. -/
structure Ready (s₀ : State) (P : Nat → Block) (s : State) : Prop where
  a : AInv s₀ 0 s
  rdx : s.gpr .rdx = dp s₀
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 16, s.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 = P k
  m1 : s.lane .xmm1 0 = poly
  y : s.lane .xmm2 0 = y₀ s₀

/-- The powers are kept by the data written. -/
theorem keepP {s₀ : State} (hp : SPre s₀) {c : Nat} {m m' : Mem} (hc : c + 16 ≤ nb s₀)
    (hf : Frame [⟨bAddr s₀ c, 256⟩] m m') {k : Nat} (hk : k < 16) :
    m'.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 = m.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 :=
  hf.readW (r := pR s₀) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.d_p.symm.sub_right (Offset.sub_base _ (by have := hp.wrap_d; omega))) (by decide)

/-- `GEnv` of group `g`, at `a`, from the encryption after `c` blocks. -/
theorem genv_of {s₀ : State} (hp : SPre s₀) {P : Nat → Block} {c g : Nat} {a : Addr} {s : State}
    (hA : AInv s₀ c s) (hg : 16 * g + 16 ≤ nb s₀) (ha : a.toNat = (dp s₀).toNat + 256 * g)
    (hrdx : s.gpr .rdx = a) (hr11 : s.gpr .r11 = pp s₀)
    (hpw : ∀ k < 16, s.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 = P k) :
    GEnv s₀ 0 a (fun i => blockAt s.mem (bAddr s₀ (16 * g + i))) P s :=
  have hw := hp.wrap_d
  { rdx := hrdx
    r11 := hr11
    xs := fun i _ hi => by rw [show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * g + i) from addr_eq (by omega)]
    pv := hpw
    ina := fun k hk => by
      rw [hA.rd, hA.wr, BitVec.ofInt_natCast,
        show a + BitVec.ofNat 64 (16 * k) = dp s₀ + BitVec.ofNat 64 (256 * g + 16 * k) from addr_eq (by omega)]
      exact in_rdwr (in_sub hp.d_in (by omega))
    inp := fun k hk => by
      rw [hA.rd, hA.wr]
      exact in_rdwr (in_sub_int hp.p_in (by omega))
    m0 := hA.msk }

/-! ## Encryption -/

structure EInv (s₀ : State) (P : Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInv s₀ (16 * e) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (dp s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 16, s.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 = P k
  m1 : s.lane .xmm1 0 = poly
  y : s.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map (ctb s₀))

theorem ordE_lt (i : Nat) : ordE i < 16 := Nat.mod_lt _ (by decide)

theorem body_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Block} (hf : FinOk ordE (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInv s₀ P e s) :
    WP isa body s fun s' => EInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) := by
  have hw := hp.wrap_d
  have h1e := hI.one
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  have ha : a.toNat = (dp s₀).toNat + 256 * (e - 1) := hI.rdx
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (zero_ok s) fun s₁ ⟨z₁, f₁⟩ => ?_)
  have hA₁ := hI.a.yframe f₁ (by decide) (by decide) (by decide)
  have hE₁ := genv_of (P := P) hp hA₁ (g := e - 1) (by omega) ha (by rw [f₁.gpr]) (by rw [f₁.gpr, hr11])
    (fun k hk => by rw [f₁.mem]; exact hI.pw k hk)
  let X : Nat → Block := fun i => blockAt s₁.mem (bAddr s₀ (16 * (e - 1) + i))
  have hX : ∀ i < 16, X i = ctb s₀ (16 * (e - 1) + i) := fun i hi => by
    simp only [X]; rw [hA₁.blocks _ (by omega)]; simp only [show 16 * (e - 1) + i < 16 * e by omega, ite_true]
  refine WP.seq (WP.mono (group_ok (lo := fun _ _ => 0) (y := s.lane .xmm2 0) hp (fun _ _ => Nat.le_refl _)
    (fun _ => Nat.le_refl _) (fun b _ j' _ _ => ⟨ordE_lt _, Nat.zero_le _⟩)
    (fun b _ i _ hi => by omega) (by omega) (by omega) ha hA₁ (j := 16)
    (by rw [f₁.gpr]; show a.toNat + _ = _; omega)
    ⟨hE₁, by rw [f₁.lane _ (by decide) 0 (by decide)]; exact hI.m1,
      by rw [ite_f (by decide)]; exact ⟨z₁, by rw [f₁.lane _ (by decide) 0 (by decide)]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  refine WP.mono (nextE_ok s₂) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, h1₂, h2⟩ := hQ₂
  rw [ite_t ⟨rfl, by decide⟩] at h2
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₂, f₁.gpr]
  have hA' : AInv s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 16 by omega]
    exact ⟨hA₂.le, by rw [fl]; exact hA₂.ctr, by rw [fl]; exact hA₂.msk, by rw [fl]; exact hA₂.inc,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₂.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.r10, by rw [fm]; exact hA₂.frame,
      fun k hk => by rw [fm]; exact hA₂.blocks k hk, by rw [frd]; exact hA₂.rd, by rw [fwr]; exact hA₂.wr⟩
  have hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1 - 1)) := by
    rw [hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      Offset.ofNat_sub_ofNat (by omega)]
    congr 1; omega
  refine ⟨⟨hA', by omega, ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun k hk => by rw [fm, keepP hp (by omega) hm₂ hk, f₁.mem]; exact hI.pw k hk,
    by rw [fl]; exact h1₂, ?_⟩, ?_⟩
  · rw [frdx, hg₂, f₁.gpr, BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (by show a.toNat + 256 < 2 ^ 64; omega)]
    show a.toNat + 256 = _
    rw [ha, show e + 1 - 1 = (e - 1) + 1 by omega, Nat.mul_succ, Nat.add_assoc]
  · rw [fl, h2]
    refine (hf _ _).trans ?_
    rw [show e + 1 - 1 = (e - 1) + 1 by omega, ghash_append16, ← hI.y]
    exact congrArg _ (List.map_congr_left fun i hi => hX i (List.mem_range.mp hi))
  · rw [fcf, hr9, toNat_ofNat' (by omega), show e + 1 - 1 = e by omega]

/-- The first group: four batches, with nothing between their rounds. -/
theorem first_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Block} {s : State} (hR : Ready s₀ P s) :
    WP isa first s (EInv s₀ P 1) := by
  have hwd := hp.wrap_d
  have h16 := hp.nb16
  have none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ YFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, YFrame.refl _ _⟩
  have bt := fun (c j : Nat) (t : State) (hc : c + 4 ≤ nb s₀) (hA : AInv s₀ c t)
      (hrdx : (t.gpr .rdx).toNat + 16 * j = (dp s₀).toNat + 16 * c) =>
    batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none (fun _ _ _ _ _ => trivial)
      (fun _ _ _ _ _ _ _ _ => trivial) (c := c) (j := j) hc hA hrdx trivial
  have hr : (s.gpr .rdx).toNat = (dp s₀).toNat := by rw [hR.rdx]
  refine WP.seq (WP.mono (bt 0 0 s (by omega) hR.a (by omega)) fun s₁ ⟨hA₁, _, hg₁, hl₁, hm₁⟩ => ?_)
  refine WP.seq (WP.mono (bt 4 4 s₁ (by omega) hA₁ (by rw [hg₁]; omega)) fun s₂ ⟨hA₂, _, hg₂, hl₂, hm₂⟩ => ?_)
  refine WP.seq (WP.mono (bt 8 8 s₂ (by omega) hA₂ (by rw [hg₂, hg₁]; omega)) fun s₃ ⟨hA₃, _, hg₃, hl₃, hm₃⟩ => ?_)
  refine WP.mono (bt 12 12 s₃ (by omega) hA₃ (by rw [hg₃, hg₂, hg₁]; omega)) fun s₄ ⟨hA₄, _, hg₄, hl₄, hm₄⟩ => ?_
  have lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → ∀ l < 2, s₄.lane r l = s.lane r l := fun r h13 h14 hr l hl => by
    rw [hl₄ r h13 h14 hr (by simp) l hl, hl₃ r h13 h14 hr (by simp) l hl, hl₂ r h13 h14 hr (by simp) l hl,
      hl₁ r h13 h14 hr (by simp) l hl]
  have gk : s₄.gpr = s.gpr := by rw [hg₄, hg₃, hg₂, hg₁]
  have hm : Frame [⟨bAddr s₀ 0, 256⟩] s.mem s₄.mem :=
    (frame_group (b := 0) hm₁ (by decide)).trans ((frame_group (b := 1) hm₂ (by decide)).trans
      ((frame_group (b := 2) hm₃ (by decide)).trans (frame_group (b := 3) hm₄ (by decide))))
  refine ⟨hA₄, Nat.le_refl _, by rw [gk, hR.rdx]; simp, ?_, by rw [gk]; exact hR.rax,
    fun r h1 h2 _ h4 => by rw [gk]; exact hR.gpr r h1 h2 h4, fun k hk => ?_,
    by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide)]; exact hR.m1,
    by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide), hR.y]; simp [ghashFrom]⟩
  · rw [gk, hR.gpr _ (by decide) (by decide) (by decide)]; simp
  · rw [keepP hp (by omega) hm hk]; exact hR.pw k hk

/-- `cmp r9, 32`. -/
theorem cmpE_ok {s₀ : State} {P : Nat → Block} {e : Nat} {s : State} (hI : EInv s₀ P e s) :
    WP isa (.block [.alu .cmp .r9 (.imm 32)]) s fun s' =>
      EInv s₀ P e s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e - 1) < 32)) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  have hr9 := hI.r9
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    hr9, e32, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨{ hI with a := { hI.a with } }, ?_⟩
  rw [toNat_ofNat' (by omega)]; rfl

theorem loopE_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Block} (hf : FinOk ordE (hk s₀) P) {s : State}
    (hI : EInv s₀ P 1 s) (hcf : s.cf = some (decide (nb s₀ - 16 * (1 - 1) < 32))) :
    WP isa (.ite .b (.block []) (.loop body .ae)) s fun s' => ∃ e, nb s₀ = 16 * e ∧ EInv s₀ P e s' := by
  have hm := hp.nbm
  have fin : ∀ e, nb s₀ - 16 * (e - 1) < 32 → ∀ t, EInv s₀ P e t → ∃ e, nb s₀ = 16 * e ∧ EInv s₀ P e t :=
    fun e he t hI => ⟨e, by have := hI.a.le; have := hI.one; omega, hI⟩
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
          nb s₀ - 16 * (e + 1), by have := hI.one; omega, e + 1, rfl, by omega, hI'⟩
    exact WP.loop (M := isa) I hstep (nb s₀ - 16 * 1) s ⟨1, rfl, by simp at h; omega, hI⟩

/-- The loads `0 … n − 1` of the order of an encryption group. -/
theorem ghRun_ok {s₀ : State} {a : Addr} {X : Nat → Block} {P : Nat → Block} {y : Block} :
    ∀ n, n ≤ 16 → ∀ s, GEnv s₀ 0 a X P s → prod (s.proj 0) = Prod.zero → s.lane .xmm2 0 = y →
      WP isa (.block ((List.range n).flatMap fun i => ghLoad (ordE i))) s fun s' => GEnv s₀ 0 a X P s' ∧
        prod (s'.proj 0) = accN ordE X P y n ∧ s'.lane .xmm2 0 = y ∧ YFrame gl s s'
  | 0, _, s, hE, hz, hy => by
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨hE, hz, hy, YFrame.refl _ _⟩
  | n + 1, hn, s, hE, hz, hy => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ghRun_ok n (by omega) s hE hz hy) fun s₁ ⟨hE₁, p₁, y₁, f₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (ghStep (ordE_lt n) (Nat.zero_le _) hE₁ p₁ y₁) fun s' ⟨hE', p', y', f'⟩ => ⟨hE', p', y', f₁.trans f'⟩

theorem final_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Block} (hf : FinOk ordE (hk s₀) P) {e : Nat}
    (he : nb s₀ = 16 * e) {s : State} (hI : EInv s₀ P e s) :
    WP isa (.block (storeCtr ++ lastG ++ storeY)) s (EPost s₀) := by
  have hw := hp.wrap_d
  have h1e := hI.one
  have hm0 : s.lane .xmm0 0 = revMask := hI.a.msk
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (store16_ok .xmm13 .xmm14 .rax s hm0 (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  have cD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega))
  have cP : ∀ k < 16, Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (16 * k), 16⟩ (cR s₀) := fun k hk =>
    hp.p_c.sub_left (Offset.sub_base _ (by omega))
  rw [hI.rax] at m₁
  let a := s.gpr .rdx
  have ha : a.toNat = (dp s₀).toNat + 256 * (e - 1) := hI.rdx
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  simp only [lastG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s₁) fun s₂ ⟨z₂, f₂⟩ => ?_
  let X : Nat → Block := fun i => ctb s₀ (16 * (e - 1) + i)
  have hE₂ : GEnv s₀ 0 a X P s₂ :=
    { rdx := by rw [f₂.gpr, g₁]
      r11 := by rw [f₂.gpr, g₁, hr11]
      xs := fun i _ hi => by
        rw [f₂.mem, m₁, show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega),
          blockAt_writeW_sep' (cD _ (by omega)) rfl, hI.a.blocks _ (by omega)]
        simp only [show 16 * (e - 1) + i < 16 * e by omega, ite_true, X]
      pv := fun k hk => by
        rw [f₂.mem, m₁, Mem.readW_writeW_sep ((cP k hk).sep (Region.contains_self _ _) (Region.contains_self _ _))
          (by decide)]
        exact hI.pw k hk
      ina := fun k hk => by
        rw [f₂.rd, f₂.wr, rd₁, wr₁, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (16 * k) = dp s₀ + BitVec.ofNat 64 (256 * (e - 1) + 16 * k) from
            addr_eq (by omega)]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inp := fun k hk => by
        rw [f₂.rd, f₂.wr, rd₁, wr₁, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := by rw [f₂.lane _ (by decide) 0 (by decide), l₁ _ (by decide) 0 (by decide)]; exact hm0 }
  rw [WP.block_append_iff]
  refine WP.mono (ghRun_ok (y := s.lane .xmm2 0) 16 (Nat.le_refl _) s₂ hE₂ z₂
    (by rw [f₂.lane _ (by decide) 0 (by decide), l₁ _ (by decide) 0 (by decide)])) fun s₃ ⟨hE₃, p₃, _, f₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ghFin hE₃ (by
      rw [f₃.lane _ (by decide) 0 (by decide), f₂.lane _ (by decide) 0 (by decide), l₁ _ (by decide) 0 (by decide)]
      exact hI.m1)) fun s₄ ⟨_, y4, f₄⟩ => ?_
  rw [p₃] at y4
  have hm0₄ : s₄.lane .xmm0 0 = revMask := by
    rw [f₄.lane _ (by decide) 0 (by decide), f₃.lane _ (by decide) 0 (by decide),
      f₂.lane _ (by decide) 0 (by decide), l₁ _ (by decide) 0 (by decide)]; exact hm0
  have g₄ : s₄.gpr = s.gpr := by rw [f₄.gpr, f₃.gpr, f₂.gpr, g₁]
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl, WP.block_append_iff]
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx s₄ hm0₄ (by
      rw [g₄, f₄.wr, f₃.wr, f₂.wr, wr₁, hI.a.wr, hI.gpr _ (by decide) (by decide) (by decide) (by decide)]
      exact hp.y_in)) fun s₅ ⟨m₅, g₅, rd₅, wr₅, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  have hrcx : s.gpr .rcx = yp s₀ := hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  rw [g₄, hrcx] at m₅
  have m₄ : s₄.mem = s₁.mem := by rw [f₄.mem, f₃.mem, f₂.mem]
  rw [m₄, m₁] at m₅
  have yD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega))
  have hb : ∀ k < nb s₀, blockAt s₅.mem (bAddr s₀ k) = ctb s₀ k := fun k hk => by
    rw [m₅, blockAt_writeW_sep' (yD k hk) rfl, blockAt_writeW_sep' (cD k hk) rfl, hI.a.blocks k hk]
    simp only [show k < 16 * e by omega, ite_true]
  refine ⟨blocks_ctr32 hb, ?_, ?_, ?_, ?_, by
      show s₅.rd = _; rw [rd₅, f₄.rd, f₃.rd, f₂.rd, rd₁, hI.a.rd], by
      show s₅.wr = _; rw [wr₅, f₄.wr, f₃.wr, f₂.wr, wr₁, hI.a.wr]⟩
  · show blockAt s₅.mem (cp s₀) = _
    rw [m₅, blockAt_writeW_sep' hp.c_y rfl, VG.Proof.Gcm.X86_64.blockAt_store, hI.a.ctr, he]
  · show blockAt s₅.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s₅.mem (dp s₀) (nb s₀))
    rw [show blocksAt s₅.mem (dp s₀) (nb s₀) = (List.range (16 * e)).map (ctb s₀) from by
        rw [← he]; simp only [blocksAt]
        exact List.map_congr_left fun k hk => hb k (by simpa using hk),
      m₅, VG.Proof.Gcm.X86_64.blockAt_store, y4, hf, show 16 * e = 16 * ((e - 1) + 1) by omega,
      ghash_append16, ← hI.y]
  · show Frame _ s₀.mem s₅.mem
    rw [m₅]
    exact ((hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := yR s₀) (by simp) _
      (Region.contains_self _ _)
  · intro r h1 h2 h3 h4
    show s₅.gpr r = _
    rw [g₅, g₄]; exact hI.gpr r h1 h2 h3 h4

/-- The encryption after the setup. -/
theorem encTail_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Block} (hf : FinOk ordE (hk s₀) P) {s : State}
    (hR : Ready s₀ P s) :
    WP isa (.seq first (.seq (.block [.alu .cmp .r9 (.imm 32)])
      (.seq (.ite .b (.block []) (.loop body .ae)) (.block (storeCtr ++ lastG ++ storeY))))) s (EPost s₀) := by
  refine WP.seq (WP.mono (first_ok hp hR) fun s₂ hI₂ => ?_)
  refine WP.seq (WP.mono (cmpE_ok hI₂) fun s₃ ⟨hI₃, hcf⟩ => ?_)
  exact WP.seq (WP.mono (loopE_ok hp hf hI₃ hcf) fun s₄ ⟨e, he, hI₄⟩ => final_ok hp hf he hI₄)

end VG.Proof.Gcm.X86_64.StitchAvx
