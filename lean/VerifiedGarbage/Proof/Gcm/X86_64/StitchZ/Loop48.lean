import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Gh48

/-!
# Interleaved counter mode and GHASH with AVX-512: 48 blocks at a time

`body48_ok`: three groups encrypted (`batch_ok`) while the three groups
before them, encrypted in the iteration before, are hashed between their
rounds (`gq48_ok`), with one reduction (`EInv3`, which `big_ok` starts from
`EInv` after the first group, the powers `pow48` stores and two more groups,
and ends by hashing two of the three groups left one at a time, back to
`EInv`). `dbody48_ok` and `bigD_ok` are the same for decryption, which hashes
each group during its own rounds. `encTail_ok` and `decTail_ok` are the
loops after the setup: from 256 blocks on the loops of three groups, then
those of one (`Loop.lean`), for any powers whose products add up to `GHASH`
(`FinOk`, and for the powers `T48 P` computed from them, `FinOk48`), without
the field: `StitchZ/Ok.lean` proves those and `StitchOk` of `StitchZ.enc`
and `StitchZ.dec` (`stitch_ok`).
-/

namespace VG.Proof.Gcm.X86_64.StitchZ

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Stitch (storeCtr storeY)
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost DPost nb nr kp pp cp yp cb dp dR pR cR yR bAddr blk ctb ciph
  sch hk y₀ ite_t ite_f addr_eq in_sub in_sub_int in_rdwr ghash_append16 ghash16)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB prod toNat_ofNat_lt ofNat_sub_ofNat ea_at)
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZ (batch body body48 dbody dbody48 gq48 pow48 big bigD lastG adv tab first)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame run_sep Keys)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-- The powers of 48 blocks, from the sixteen `P` of the setup: group `g`'s
are `P` times `H'³²⁻¹⁶ᵍ` (`pow48`). -/
def T48 (P : Nat → Nat → Block) (g k l : Nat) : Block :=
  if g = 2 then P k l else if g = 1 then reduceB (Prod.zero.acc (P k l) (P 0 0))
  else reduceB (Prod.zero.acc (P k l) (reduceB (Prod.zero.acc (P 0 0) (P 0 0))))

/-- The blocks of 48 kept by writes elsewhere in the data, the powers by any
in the data. -/
theorem QG48.data {s₀ : State} (hp : SPre s₀) {lo : Nat → Nat} {a : Addr} {X : Nat → Block}
    {T : Nat → Nat → Nat → Block} {yl : Nat → Block} {b j c g : Nat}
    (hc : c + 16 ≤ nb s₀) (hg : 16 * g + 48 ≤ nb s₀) (ha : a.toNat = (dp s₀).toNat + 256 * g)
    (hsep : ∀ i, lo j ≤ i → i < 48 → ¬ (c ≤ 16 * g + i ∧ 16 * g + i < c + 16))
    {t t' : State} (h : QG48 s₀ lo a X T yl b j t) (hgpr : t'.gpr = t.gpr) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hlane : ∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, t'.zlane r l = t.zlane r l)
    (hf : Frame [⟨bAddr s₀ c, 256⟩] t.mem t'.mem) : QG48 s₀ lo a X T yl b j t' := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  obtain ⟨hE, h2⟩ := h
  have kp : ∀ l < 4, prod (t'.zproj l) = prod (t.zproj l) := fun l hl => by
    simp only [prod, State.zproj_xmm, hlane .xmm8 (by decide) (by decide) l hl,
      hlane .xmm9 (by decide) (by decide) l hl, hlane .xmm10 (by decide) (by decide) l hl]
  have kpw : ∀ o, o + 16 ≤ 1024 → t'.mem.readW (pp s₀ + BitVec.ofNat 64 o) 128 = t.mem.readW (pp s₀ + BitVec.ofNat 64 o) 128 :=
    fun o ho => hf.readW (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega))) (by decide)
  refine ⟨⟨by rw [hgpr]; exact hE.rdx, by rw [hgpr]; exact hE.r11, fun i hi hi' => ?_,
    fun g' hg' k hk l hl => by rw [kpw _ (by simp only [tab]; omega)]; exact hE.pv g' hg' k hk l hl,
    fun l hl => by rw [kpw _ (by omega)]; exact hE.pm l hl,
    fun o ho => by rw [hrd, hwr]; exact hE.ina o ho, fun o ho => by rw [hrd, hwr]; exact hE.inp o ho,
    fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact hE.m0 l hl⟩, ?_⟩
  · have e : a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * g + i) := addr_eq (by omega)
    rw [e, blockAt_frame hf fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      intro x h₁ h₂
      exact run_sep hw (by omega) hc (hsep i hi hi') h₁ h₂]
    have := hE.xs i hi hi'
    rwa [e] at this
  · split
    · rw [ite_t (by assumption)] at h2
      exact ⟨by rw [hlane _ (by decide) (by decide) 0 (by decide)]; exact h2.1,
        fun l h1 h4 => by rw [hlane _ (by decide) (by decide) l h4]; exact h2.2 l h1 h4⟩
    · rw [ite_f (by assumption)] at h2
      exact ⟨fun hj l hl => by rw [kp l hl]; exact h2.1 hj l hl,
        fun hj l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact h2.2 hj l hl⟩

/-- The next group of three, whose first pair's powers are those of the
products done. -/
theorem QG48.next {s₀ : State} {lo lo' : Nat → Nat} {a : Addr} {X : Nat → Block} {T : Nat → Nat → Nat → Block}
    {yl : Nat → Block} {b : Nat} {s : State} (h : QG48 s₀ lo a X T yl b 10 s) (hb : b < 2)
    (hl : lo 10 ≤ lo' 1) : QG48 s₀ lo' a X T yl (b + 1) 1 s := by
  obtain ⟨hE, h2⟩ := h
  rw [ite_f (by omega)] at h2
  refine ⟨hE.mono hl, ?_⟩
  rw [ite_f (by omega)]
  have e : np (b + 1) 1 = np b 10 := by
    simp only [np]; rw [ite_t (by decide), ite_f (by decide), ite_f (by decide)]; omega
  rw [e]; exact h2

theorem ghash_append48 (h y : Block) (f : Nat → Block) (g : Nat) :
    ghashFrom h y ((List.range (16 * g + 48)).map f) =
      ghashFrom h (ghashFrom h y ((List.range (16 * g)).map f)) ((List.range 48).map fun i => f (16 * g + i)) := by
  rw [List.range_add, List.map_append, List.map_map]
  simp only [ghashFrom, List.foldl_append]
  rfl

/-- The encryption state kept by changes of `rdx` and `r9` alone. -/
theorem AInv.gpr2 {s₀ : State} {c : Nat} {s s' : State} (h : AInv s₀ c s)
    (hg : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) (hl : ∀ r l, s'.zlane r l = s.zlane r l)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : AInv s₀ c s' :=
  ⟨h.le, fun l hl' => by rw [hl]; exact h.ctr l hl', fun l hl' => by rw [hl]; exact h.msk l hl',
    fun l hl' => by rw [hl]; exact h.inc l hl',
    by rw [hg _ (by decide) (by decide)]; exact h.rdi, by rw [hg _ (by decide) (by decide)]; exact h.rsi,
    by rw [hg _ (by decide) (by decide)]; exact h.r10, by rw [hm]; exact h.frame,
    fun k hk => by rw [hm]; exact h.blocks k hk, by rw [hrd]; exact h.rd, by rw [hwr]; exact h.wr⟩

/-- The encryption state kept by `pow48`, which writes only the working space. -/
theorem AInv.pow {s₀ : State} (hp : SPre s₀) {c : Nat} {s s' : State} (h : AInv s₀ c s)
    (hf : Frame [pR s₀] s.mem s'.mem) (hg : s'.gpr = s.gpr) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hl : ∀ r, r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 → r ≠ .xmm12 → ∀ l < 4,
      s'.zlane r l = s.zlane r l) : AInv s₀ c s' := by
  have hw := hp.wrap_d
  have k : ∀ r ∈ ([.xmm14, .xmm0, .xmm15] : List XReg), ∀ l < 4, s'.zlane r l = s.zlane r l := by
    intro r hr l hl'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hl _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl'
  refine ⟨h.le, fun l hl' => by rw [k _ (by decide) l hl']; exact h.ctr l hl',
    fun l hl' => by rw [k _ (by decide) l hl']; exact h.msk l hl',
    fun l hl' => by rw [k _ (by decide) l hl']; exact h.inc l hl',
    by rw [hg]; exact h.rdi, by rw [hg]; exact h.rsi, by rw [hg]; exact h.r10,
    h.frame.trans (hf.sub fun r hr => ⟨pR s₀, by simp, fun a ha => by
      simp only [List.mem_singleton] at hr; subst hr; exact ha⟩),
    fun k hk => ?_, by rw [hrd]; exact h.rd, by rw [hwr]; exact h.wr⟩
  rw [blockAt_frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.d_p.sub_left (Offset.sub_base _ (by omega))]
  exact h.blocks k hk

/-- A word of the working space, kept by the data written. -/
theorem keepW {s₀ : State} (hp : SPre s₀) {c : Nat} (hc : c + 16 ≤ nb s₀) {m m' : Mem}
    (hf : Frame [⟨bAddr s₀ c, 256⟩] m m') {o : Nat} (ho : o + 16 ≤ 1024) :
    m'.readW (pp s₀ + BitVec.ofNat 64 o) 128 = m.readW (pp s₀ + BitVec.ofNat 64 o) 128 := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  exact hf.readW (r := pR s₀) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega))) (by decide)

/-- `add rdx, 256`, `sub r9, 16`. -/
theorem adv_ok (s : State) :
    WP isa (.block adv) s fun s' => s'.gpr .rdx = s.gpr .rdx + 256 ∧ s'.gpr .r9 = s.gpr .r9 - 16 ∧
      (∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ (∀ r l, s'.zlane r l = s.zlane r l) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  apply WP.of_runBlock
  simp only [adv, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e256, e16,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

/-- The end of a body of three groups: `add rdx, 768`, `sub r9, 48`, `cmp r9, n`. -/
theorem next48_ok (s : State) (i : BitVec 32) (n : Nat) (hi : BitVec.signExtend 64 i = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .add .rdx (.imm 768), .alu .sub .r9 (.imm 48), .alu .cmp .r9 (.imm i)]) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 768 ∧ s'.gpr .r9 = s.gpr .r9 - 48 ∧
        s'.cf = some (decide ((s.gpr .r9 - 48).toNat < (BitVec.ofNat 64 n).toNat)) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ (∀ r l, s'.zlane r l = s.zlane r l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e768 : BitVec.signExtend 64 (768 : BitVec 32) = 768 := by decide
  have e48 : BitVec.signExtend 64 (48 : BitVec 32) = 48 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e768, e48, hi,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, trivial, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

/-- `cmp r9, n`. -/
theorem cmp_ok (s : State) (i : BitVec 32) (n : Nat) (hi : BitVec.signExtend 64 i = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .cmp .r9 (.imm i)]) s fun s' =>
      s'.cf = some (decide ((s.gpr .r9).toNat < (BitVec.ofNat 64 n).toNat)) ∧ s'.gpr = s.gpr ∧
        (∀ r l, s'.zlane r l = s.zlane r l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    hi, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun _ _ => rfl, trivial, trivial, trivial⟩

/-! ## Hashing one group at a time -/

/-- The encryption state with `c` blocks encrypted and the first `e - 1`
groups hashed: `EInv` when `c = 16 e`. -/
structure EGen (s₀ : State) (P : Nat → Nat → Block) (e c : Nat) (s : State) : Prop where
  a : AInv s₀ c s
  one : 1 ≤ e
  ec : 16 * e ≤ c
  rdx : (s.gpr .rdx).toNat = (dp s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 4, s.zlane .xmm1 l = poly
  y : s.zlane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map (ctb s₀))
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

/-- Group `e - 1` hashed (after the loop of three groups: `lastG`). -/
theorem lastG_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e c : Nat}
    {s : State} (hI : EGen s₀ P e c s) :
    WP isa (.block lastG) s fun s' =>
      s'.zlane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (ctb s₀)) ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧
      ZFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2] s s' := by
  have hw := hp.wrap_d
  have hA := hI.a
  have h1e := hI.one
  have hec := hI.ec
  have hc := hA.le
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctb s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * (e - 1) := hI.rdx
  have hE : GEnv s₀ 0 a X P s :=
    { rdx := rfl
      r11 := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
      xs := fun i _ hi => by
        rw [show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega),
          hA.blocks _ (by omega)]
        simp only [show 16 * (e - 1) + i < c by omega, ite_true]
        rfl
      pv := hI.pw
      ina := fun k hk => by
        rw [hA.rd, hA.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (64 * k) = dp s₀ + BitVec.ofNat 64 (256 * (e - 1) + 64 * k) from
            addr_eq (by omega)]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inp := fun k hk => by
        rw [hA.rd, hA.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := hA.msk }
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
theorem drainStep_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e c : Nat}
    (hc : 16 * (e + 1) ≤ c) {s : State} (hI : EGen s₀ P e c s) :
    WP isa (.block (lastG ++ adv)) s (EGen s₀ P (e + 1) c) := by
  have hw := hp.wrap_d
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hcn := hI.a.le
  have h1e := hI.one
  rw [WP.block_append_iff]
  refine WP.mono (lastG_ok hp hf hI) fun s₁ ⟨y₁, y1₁, f₁⟩ => ?_
  refine WP.mono (adv_ok s₁) fun s' ⟨frdx, fr9, fg, fl, fm, frd, fwr⟩ => ?_
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, f₁.gpr]
  refine ⟨(hI.a.zframe f₁ (by decide) (by decide) (by decide)).gpr2 fg fl fm frd fwr, by omega, hc, ?_, ?_,
    by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun k hk l hl => by rw [fm, f₁.mem]; exact hI.pw k hk l hl,
    fun l hl => by rw [fl, f₁.zlane _ (by decide) l hl]; exact hI.m1 l hl,
    by rw [fl, y₁, show e + 1 - 1 = e by omega], fun l h1 h4 => by rw [fl]; exact y1₁ l h1 h4⟩
  · rw [frdx, f₁.gpr, BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (by rw [hI.rdx]; omega), hI.rdx, show e + 1 - 1 = (e - 1) + 1 by omega, Nat.mul_succ,
      Nat.add_assoc]
  · rw [fr9, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega) (by omega)]
    congr 1; omega

theorem EGen.einv {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (h : EGen s₀ P e (16 * e) s) :
    EInv s₀ P e s :=
  ⟨h.a, h.one, h.rdx, h.r9, h.rax, h.gpr, h.pw, h.m1, h.y, h.y1⟩

/-! ## The encryption loop of three groups -/

/-- `e + 2` groups encrypted, the first `e - 1` hashed, the powers of 48
blocks and the reduction constant in the working space; `rdx` points to
group `e - 1`, the first of the three to hash. -/
structure EInv3 (s₀ : State) (T : Nat → Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInv s₀ (16 * (e + 2)) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (dp s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pv : ∀ g < 3, ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l
  pm : ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly
  y : s.zlane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map (ctb s₀))
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

theorem body48_ok {s₀ : State} (hp : SPre s₀) {T : Nat → Nat → Nat → Block} (hT : FinOk48 (hk s₀) T) {e : Nat}
    (he : 16 * (e + 5) ≤ nb s₀) {s : State} (hI : EInv3 s₀ T e s) :
    WP isa body48 s fun s' => EInv3 s₀ T (e + 3) s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e + 2) < 96)) := by
  have hw := hp.wrap_d
  have h1e := hI.one
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctb s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * (e - 1) := hI.rdx
  have hE : GEnv48 s₀ 0 a X T s :=
    { rdx := rfl
      r11 := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
      xs := fun i _ hi => by
        rw [show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega),
          hI.a.blocks _ (by omega)]
        simp only [show 16 * (e - 1) + i < 16 * (e + 2) by omega, ite_true]
        rfl
      pv := hI.pv
      pm := hI.pm
      ina := fun o ho => by
        rw [hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 o = dp s₀ + BitVec.ofNat 64 (256 * (e - 1) + o) from addr_eq (by omega)]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inp := fun o ho => by
        rw [hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := hI.a.msk }
  let Q : Nat → Nat → State → Prop := QG48 s₀ (fun _ => 0) a X T yl
  have hgq : ∀ b < 3, ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → Q b j t →
      WP isa (.block (gq48 b j)) t fun t' => Q b (j + 1) t' ∧ ZFrame gRegs48 t t' := fun b hb =>
    gq48_ok hb (fun _ => Nat.le_refl _) (Nat.zero_le _) (Nat.zero_le _)
  have hq : ∀ b j t t', Q b j t → ZFrame (.xmm13 :: .xmm14 :: aregs) t t' → Q b j t' :=
    fun _ _ _ _ h f => h.zframe f (by decide)
  have hqx : ∀ b c, c + 16 ≤ nb s₀ → 16 * (e - 1) + 48 ≤ c → ∀ t t', Q b 10 t → t'.gpr = t.gpr → t'.rd = t.rd →
      t'.wr = t.wr → (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, t'.zlane r l = t.zlane r l) →
      Frame [⟨bAddr s₀ c, 256⟩] t.mem t'.mem → Q b 10 t' :=
    fun _ _ hc hc' _ _ h hg hrd hwr hl hf =>
      QG48.data hp hc (g := e - 1) (by omega) ha (fun i _ hi => by omega) h hg hrd hwr hl hf
  have hQ₀ : Q 0 1 s := ⟨hE, by
    rw [ite_f (by decide)]; exact ⟨fun h => absurd h (by decide), fun _ _ _ => rfl⟩⟩
  -- Group `e + 2`, hashing group `e - 1`.
  refine WP.seq (WP.mono (batch_ok hp (gq48 0) gRegs48 gRegs48_ok (Q 0) (hgq 0 (by decide)) (hq 0)
    (hqx 0 _ (by omega) (by omega)) (c := 16 * (e + 2)) (j := 12) (by omega) hI.a
    (by show a.toNat + _ = _; omega) hQ₀) fun s₁ ⟨hA₁, hQ₁, hg₁, _, _⟩ => ?_)
  refine WP.seq (WP.mono (batch_ok hp (gq48 1) gRegs48 gRegs48_ok (Q 1) (hgq 1 (by decide)) (hq 1)
    (hqx 1 _ (by omega) (by omega)) (c := 16 * (e + 2) + 16) (j := 16) (by omega) hA₁
    (by rw [hg₁]; show a.toNat + _ = _; omega) (hQ₁.next (by decide) (Nat.le_refl _)))
    fun s₂ ⟨hA₂, hQ₂, hg₂, _, _⟩ => ?_)
  refine WP.seq (WP.mono (batch_ok hp (gq48 2) gRegs48 gRegs48_ok (Q 2) (hgq 2 (by decide)) (hq 2)
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
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun g hg k hk l hl => by rw [fm]; exact hE₃.pv g hg k hk l hl, fun l hl => by rw [fm]; exact hE₃.pm l hl,
    ?_, fun l h1 h4 => by rw [fl]; exact h2.2 l h1 h4⟩, ?_⟩
  · rw [frdx, g₃, BitVec.toNat_add, show (768 : BitVec 64).toNat = 768 from rfl,
      Nat.mod_eq_of_lt (by show a.toNat + 768 < 2 ^ 64; omega)]
    show a.toNat + 768 = _
    rw [ha, show e + 3 - 1 = (e - 1) + 3 by omega]; omega
  · rw [fl, h2.1, hT X yl hI.y1, show 16 * (e + 3 - 1) = 16 * (e - 1) + 48 by omega, ghash_append48, ← hI.y]
  · rw [fcf, hr9, toNat_ofNat_lt (by omega), show e + 3 - 1 = e + 2 by omega]
    rfl

theorem loop48_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) {T : Nat → Nat → Nat → Block} (hT : FinOk48 (hk s₀) T) {s : State}
    (hI : EInv3 s₀ T 1 s) (h96 : 96 ≤ nb s₀) :
    WP isa (.loop body48 .ae) s fun s' => ∃ e, nb s₀ - 16 * (e - 1) < 96 ∧ EInv3 s₀ T e s' := by
  let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 5) ≤ nb s₀ ∧ EInv3 s₀ T e s
  have hstep : ∀ m s, I m s → WP isa body48 s (fun s' =>
      (eval .ae s' = some false ∧ ∃ e, nb s₀ - 16 * (e - 1) < 96 ∧ EInv3 s₀ T e s') ∨
      (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨e, rfl, he, hI⟩
    refine WP.mono (body48_ok hp hT he hI) fun s' ⟨hI', hcf'⟩ => ?_
    by_cases hlt : nb s₀ - 16 * (e + 2) < 96
    · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
        e + 3, by omega, hI'⟩
    · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - 16 * (e + 3), by omega, e + 3, rfl, by omega, hI'⟩
  exact WP.loop (M := isa) I hstep (nb s₀ - 16 * 1) s ⟨1, rfl, by omega, hI⟩

/-! ## The powers, and the reduction constant reloaded -/

/-- `pow48`, from the sixteen powers `P` in the working space. -/
theorem powSetup_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} {c : Nat} {s : State} (hA : AInv s₀ c s)
    (hr11 : s.gpr .r11 = pp s₀)
    (hpw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l)
    (h1 : ∀ l < 4, s.zlane .xmm1 l = poly) :
    WP isa (.block pow48) s fun s' => AInv s₀ c s' ∧
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

/-- The tables kept by the data written. -/
theorem keepT {s₀ : State} (hp : SPre s₀) {T : Nat → Nat → Nat → Block} {c : Nat} (hc : c + 16 ≤ nb s₀) {m m' : Mem}
    (hf : Frame [⟨bAddr s₀ c, 256⟩] m m')
    (hv : ∀ g < 3, ∀ k < 4, ∀ l < 4, m.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l)
    (hm : ∀ l < 4, m.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) :
    (∀ g < 3, ∀ k < 4, ∀ l < 4, m'.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l) ∧
    (∀ l < 4, m'.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) :=
  ⟨fun g hg k hk l hl => by rw [keepW hp hc hf (by simp only [tab]; omega)]; exact hv g hg k hk l hl,
    fun l hl => by rw [keepW hp hc hf (by omega)]; exact hm l hl⟩

/-- The reduction constant reloaded from `scratch + 832`. -/
theorem reload_ok {s₀ : State} (hp : SPre s₀) (s : State) (hr11 : s.gpr .r11 = pp s₀)
    (hwr : s.wr = s₀.wr) (hm : ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) :
    WP isa (.block [.vmovdqu32Load .xmm1 (at_ .r11 832)]) s fun s' =>
      (∀ l < 4, s'.zlane .xmm1 l = poly) ∧ ZFrame [.xmm1] s s' := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((832 : Nat) : Int)) 64 := by
    rw [hr11, hwr]; exact in_rdwr (in_sub_int hp.p_in (by decide))
  rw [WP.block_cons_iff]
  refine ⟨ldZ s .xmm1 (s.gpr .r11 + BitVec.ofInt 64 ((832 : Nat) : Int)),
    by simp only [isa, exec, State.load512, ea_at, hin, ite_true, Option.map_some], WP.block_nil ⟨fun l hl => ?_,
      ⟨rfl, rfl, rfl, rfl, fun r hr l hl => ldZ_zlane_ne _ _ (fun h => hr (by simp [h])) hl⟩⟩⟩
  rw [ldZ_zlane _ _ _ hl, ofInt_add_ofNat, hr11]; exact hm l hl

/-! ## From 256 blocks on -/

/-- What `big` does after the tables: the next two groups, the loop, and two
of the three groups left to hash, for any tables `T` whose last is `P`. -/
theorem bigRest_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {T : Nat → Nat → Nat → Block} (hT : FinOk48 (hk s₀) T) (hT2 : ∀ k l, T 2 k l = P k l)
    (h256 : 256 ≤ nb s₀) {s s₁ : State} (hI : EInv s₀ P 1 s) (hA₁ : AInv s₀ (16 * 1) s₁)
    (hv₁ : ∀ g < 3, ∀ k < 4, ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l)
    (hm₁ : ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) (hg₁ : s₁.gpr = s.gpr)
    (hl₁ : ∀ l < 4, s₁.zlane .xmm2 l = s.zlane .xmm2 l) :
    WP isa (.seq (batch 4 fun _ => []) (.seq (batch 8 fun _ => [])
      (.seq (.loop body48 .ae) (.block (.vmovdqu32Load .xmm1 (at_ .r11 832) :: (lastG ++ adv ++ lastG ++ adv))))))
      s₁ fun s' => ∃ e, EInv s₀ P e s' := by
  have hw := hp.wrap_d
  have none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ ZFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, ZFrame.refl _ _⟩
  refine WP.seq (WP.mono (batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 16 * 1) (j := 4) (by omega) hA₁
    (by have := hI.rdx; rw [hg₁]; omega) trivial) fun s₂ ⟨hA₂, _, hg₂, hl₂, hf₂⟩ => ?_)
  obtain ⟨hv₂, hm₂⟩ := keepT hp (by omega) hf₂ hv₁ hm₁
  refine WP.seq (WP.mono (batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 16 * 1 + 16) (j := 8) (by omega) hA₂
    (by have := hI.rdx; rw [hg₂, hg₁]; omega) trivial) fun s₃ ⟨hA₃, _, hg₃, hl₃, hf₃⟩ => ?_)
  obtain ⟨hv₃, hm₃⟩ := keepT hp (by omega) hf₃ hv₂ hm₂
  have g₃ : s₃.gpr = s.gpr := by rw [hg₃, hg₂, hg₁]
  have l₃ : ∀ l < 4, s₃.zlane .xmm2 l = s.zlane .xmm2 l := fun l hl => by
    rw [hl₃ _ (by decide) (by decide) (by decide) (by simp) l hl, hl₂ _ (by decide) (by decide) (by decide) (by simp) l hl,
      hl₁ l hl]
  have hI₃ : EInv3 s₀ T 1 s₃ :=
    ⟨hA₃, Nat.le_refl _, by rw [g₃]; exact hI.rdx, by rw [g₃]; exact hI.r9, by rw [g₃]; exact hI.rax,
      fun r h1 h2 h3 h4 => by rw [g₃]; exact hI.gpr r h1 h2 h3 h4, hv₃, hm₃,
      by rw [l₃ 0 (by decide)]; exact hI.y, fun l h1 h4 => by rw [l₃ l h4]; exact hI.y1 l h1 h4⟩
  refine WP.seq (WP.mono (loop48_ok hp hm hT hI₃ (by omega)) fun s₄ ⟨e, hex, hI₄⟩ => ?_)
  -- The reduction constant, and two of the three groups left to hash.
  have h1e := hI₄.one
  have hr11₄ : s₄.gpr .r11 = pp s₀ := hI₄.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (reload_ok hp s₄ hr11₄ hI₄.a.wr hI₄.pm) fun s₅ ⟨p₅, f₅⟩ => ?_
  have hG : EGen s₀ P e (16 * (e + 2)) s₅ :=
    ⟨hI₄.a.zframe f₅ (by decide) (by decide) (by decide), h1e, by omega, by rw [f₅.gpr]; exact hI₄.rdx,
      by rw [f₅.gpr]; exact hI₄.r9, by rw [f₅.gpr]; exact hI₄.rax,
      fun r h1 h2 h3 h4 => by rw [f₅.gpr]; exact hI₄.gpr r h1 h2 h3 h4,
      fun k hk l hl => by
        have h := hI₄.pv 2 (by decide) k hk l hl
        rw [show tab 2 + 64 * k + 16 * l = 64 * k + 16 * l by simp only [tab]; omega] at h
        rw [f₅.mem, h, hT2],
      p₅, by rw [f₅.zlane _ (by decide) 0 (by decide)]; exact hI₄.y,
      fun l h1 h4 => by rw [f₅.zlane _ (by decide) l h4]; exact hI₄.y1 l h1 h4⟩
  rw [List.append_assoc (lastG ++ adv) lastG adv, WP.block_append_iff]
  refine WP.mono (drainStep_ok hp hf (by omega) hG) fun s₆ hG₆ => ?_
  refine WP.mono (drainStep_ok hp hf (by omega) hG₆) fun s₇ hG₇ => ⟨e + 1 + 1, ?_⟩
  exact EGen.einv (by rw [show 16 * (e + 1 + 1) = 16 * (e + 2) by omega]; exact hG₇)

/-- `big`: from the first group encrypted to all but up to two groups, all
but the last encrypted group hashed. -/
theorem big_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hT : FinOk48 (hk s₀) (T48 P)) (h256 : 256 ≤ nb s₀) {s : State} (hI : EInv s₀ P 1 s) :
    WP isa big s fun s' => ∃ e, EInv s₀ P e s' := by
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  exact WP.seq (WP.mono (powSetup_ok hp (c := 16 * 1) hI.a hr11 hI.pw hI.m1)
    fun s₁ ⟨hA₁, hv₁, hm₁, hg₁, hl₁⟩ => bigRest_ok hp hm hf hT (fun k l => by simp only [T48, ↓reduceIte]) h256 hI hA₁
      hv₁ hm₁ hg₁ fun l hl => hl₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl)

theorem EInv.of_eq {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s s' : State} (h : EInv s₀ P e s)
    (hg : s'.gpr = s.gpr) (hl : ∀ r l, s'.zlane r l = s.zlane r l) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : EInv s₀ P e s' :=
  ⟨h.a.gpr2 (fun r _ _ => by rw [hg]) hl hm hrd hwr, h.one, by rw [hg]; exact h.rdx, by rw [hg]; exact h.r9,
    by rw [hg]; exact h.rax, fun r h1 h2 h3 h4 => by rw [hg]; exact h.gpr r h1 h2 h3 h4,
    fun k hk l hl' => by rw [hm]; exact h.pw k hk l hl', fun l hl' => by rw [hl]; exact h.m1 l hl',
    by rw [hl]; exact h.y, fun l h1 h4 => by rw [hl]; exact h.y1 l h1 h4⟩

/-- The loop of one group, from any number of groups encrypted. -/
theorem loopE_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e : Nat} {s : State}
    (hI : EInv s₀ P e s) (hcf : s.cf = some (decide (nb s₀ - 16 * (e - 1) < 32))) :
    WP isa (.ite .b (.block []) (.loop body .ae)) s fun s' => ∃ e, nb s₀ = 16 * e ∧ EInv s₀ P e s' := by
  have h1e := hI.one
  have hle := hI.a.le
  have fin : ∀ e, nb s₀ - 16 * (e - 1) < 32 → ∀ t, EInv s₀ P e t → ∃ e, nb s₀ = 16 * e ∧ EInv s₀ P e t :=
    fun e he t hI => ⟨e, by have := hI.a.le; have := hI.one; omega, hI⟩
  refine WP.ite (decide (nb s₀ - 16 * (e - 1) < 32)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil (fin e (by simpa using h) s hI)
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
    exact WP.loop (M := isa) I hstep (nb s₀ - 16 * e) s ⟨e, rfl, by simp at h; omega, hI⟩

/-- The encryption after the setup. -/
theorem encTailG_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {bigC : Prog isa} (hbig : ∀ s, 256 ≤ nb s₀ → EInv s₀ P 1 s → WP isa bigC s fun s' => ∃ e, EInv s₀ P e s')
    {s : State} (hR : Ready s₀ P s) :
    WP isa (.seq first (.seq (.block [.alu .cmp .r9 (.imm 256)]) (.seq (.ite .b (.block []) bigC)
      (.seq (.block [.alu .cmp .r9 (.imm 32)])
        (.seq (.ite .b (.block []) (.loop body .ae)) (.block (storeCtr ++ lastG ++ storeY))))))) s (EPost s₀) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.seq (WP.mono (first_ok hp hR) fun s₂ hI₂ => ?_)
  refine WP.seq (WP.mono (cmp_ok s₂ 256 256 (by decide)) fun s₃ ⟨hcf, g, l, m, rd, wr⟩ => ?_)
  have hI₃ := hI₂.of_eq g l m rd wr
  rw [hI₂.r9, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by decide)] at hcf
  refine WP.seq (WP.mono (WP.ite (Q := fun s' => ∃ e, EInv s₀ P e s') (decide (nb s₀ - 16 * (1 - 1) < 256))
    (by simp only [eval, hcf]) (fun _ => WP.block_nil ⟨1, hI₃⟩)
    (fun h => hbig _ (by simp at h; omega) hI₃)) fun s₄ ⟨e, hI₄⟩ => ?_)
  refine WP.seq (WP.mono (cmpE_ok hI₄) fun s₅ ⟨hI₅, hcf₅⟩ => ?_)
  exact WP.seq (WP.mono (loopE_ok hp hm hf hI₅ hcf₅) fun s₆ ⟨e, he, hI₆⟩ => final_ok hp hf he hI₆)

/-- The encryption after the setup. -/
theorem encTail_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hT : FinOk48 (hk s₀) (T48 P)) {s : State} (hR : Ready s₀ P s) :
    WP isa (.seq first (.seq (.block [.alu .cmp .r9 (.imm 256)]) (.seq (.ite .b (.block []) big)
      (.seq (.block [.alu .cmp .r9 (.imm 32)])
        (.seq (.ite .b (.block []) (.loop body .ae)) (.block (storeCtr ++ lastG ++ storeY))))))) s (EPost s₀) :=
  encTailG_ok hp hm hf (fun _ h256 hI => big_ok hp hm hf hT h256 hI) hR

/-! ## Decryption -/

/-- `e` groups hashed and decrypted, the powers of 48 blocks and the
reduction constant in the working space; `rdx` points to group `e`. -/
structure DInv3 (s₀ : State) (T : Nat → Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInv s₀ (16 * e) s
  rdx : s.gpr .rdx = dp s₀ + BitVec.ofNat 64 (256 * e)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * e)
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pv : ∀ g < 3, ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l
  pm : ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly
  y : s.zlane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (blk s₀))
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

/-- Which of the 48 blocks the GHASH loads to come still read during group
`b`: from group `b` on until its loads are done, after round 3. -/
abbrev loD48 (b j : Nat) : Nat := if j < 4 then 16 * b else 16 * (b + 1)

theorem dbody48_ok {s₀ : State} (hp : SPre s₀) {T : Nat → Nat → Nat → Block} (hT : FinOk48 (hk s₀) T) {e : Nat}
    (he : 16 * (e + 3) ≤ nb s₀) {s : State} (hI : DInv3 s₀ T e s) :
    WP isa dbody48 s fun s' => DInv3 s₀ T (e + 3) s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e + 3) < 48)) := by
  have hw := hp.wrap_d
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => blk s₀ (16 * e + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * e := by
    show (s.gpr .rdx).toNat = _
    rw [hI.rdx, BitVec.toNat_add, toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hE : GEnv48 s₀ 0 a X T s :=
    { rdx := rfl
      r11 := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
      xs := fun i _ hi => by
        rw [show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * e + i) from addr_eq (by omega),
          hI.a.blocks _ (by omega)]
        simp only [show ¬ 16 * e + i < 16 * e by omega, ite_false]
        rfl
      pv := hI.pv
      pm := hI.pm
      ina := fun o ho => by
        rw [hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 o = dp s₀ + BitVec.ofNat 64 (256 * e + o) from addr_eq (by omega)]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inp := fun o ho => by
        rw [hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := hI.a.msk }
  let Q : Nat → Nat → State → Prop := fun b => QG48 s₀ (loD48 b) a X T yl b
  have hgq : ∀ b < 3, ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → Q b j t →
      WP isa (.block (gq48 b j)) t fun t' => Q b (j + 1) t' ∧ ZFrame gRegs48 t t' := fun b hb =>
    gq48_ok hb (fun j => by simp only [loD48]; split <;> split <;> omega)
      (by simp only [loD48]; rw [ite_t (by decide)])
      (by simp only [loD48]; rw [ite_t (by decide)]; omega)
  have hq : ∀ b j t t', Q b j t → ZFrame (.xmm13 :: .xmm14 :: aregs) t t' → Q b j t' :=
    fun _ _ _ _ h f => h.zframe f (by decide)
  have hqx : ∀ b, 16 * (e + b) + 16 ≤ nb s₀ → ∀ t t', Q b 10 t → t'.gpr = t.gpr → t'.rd = t.rd →
      t'.wr = t.wr → (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, t'.zlane r l = t.zlane r l) →
      Frame [⟨bAddr s₀ (16 * (e + b)), 256⟩] t.mem t'.mem → Q b 10 t' :=
    fun b hc _ _ h hg hrd hwr hl hf =>
      QG48.data hp hc (g := e) (by omega) ha (fun i hi _ => by
        simp only [loD48] at hi; rw [ite_f (by decide)] at hi; omega) h hg hrd hwr hl hf
  have hnx : ∀ b, loD48 b 10 ≤ loD48 (b + 1) 1 := fun b => by
    simp only [loD48]; rw [ite_f (by decide), ite_t (by decide)]
  have hQ₀ : Q 0 1 s := ⟨hE.mono (Nat.zero_le _), by
    rw [ite_f (by decide)]; exact ⟨fun h => absurd h (by decide), fun _ _ _ => rfl⟩⟩
  -- Each group is hashed after rounds 1 and 3, before its blocks are decrypted.
  refine WP.seq (WP.mono (batch_ok hp (gq48 0) gRegs48 gRegs48_ok (Q 0) (hgq 0 (by decide)) (hq 0)
    (hqx 0 (by omega)) (c := 16 * (e + 0)) (j := 0) (by omega) (by simpa using hI.a)
    (by show a.toNat + _ = _; omega) hQ₀) fun s₁ ⟨hA₁, hQ₁, hg₁, _, _⟩ => ?_)
  refine WP.seq (WP.mono (batch_ok hp (gq48 1) gRegs48 gRegs48_ok (Q 1) (hgq 1 (by decide)) (hq 1)
    (hqx 1 (by omega)) (c := 16 * (e + 1)) (j := 4) (by omega)
    (by rw [show 16 * (e + 1) = 16 * (e + 0) + 16 by omega]; exact hA₁)
    (by rw [hg₁]; show a.toNat + _ = _; omega) (hQ₁.next (by decide) (hnx 0)))
    fun s₂ ⟨hA₂, hQ₂, hg₂, _, _⟩ => ?_)
  refine WP.seq (WP.mono (batch_ok hp (gq48 2) gRegs48 gRegs48_ok (Q 2) (hgq 2 (by decide)) (hq 2)
    (hqx 2 (by omega)) (c := 16 * (e + 2)) (j := 8) (by omega)
    (by rw [show 16 * (e + 2) = 16 * (e + 1) + 16 by omega]; exact hA₂)
    (by rw [hg₂, hg₁]; show a.toNat + _ = _; omega) (hQ₂.next (by decide) (hnx 1)))
    fun s₃ ⟨hA₃, hQ₃, hg₃, _, _⟩ => ?_)
  refine WP.mono (next48_ok s₃ 48 48 (by decide)) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨hE₃, h2⟩ := hQ₃
  rw [ite_t (by decide)] at h2
  have g₃ : s₃.gpr = s.gpr := by rw [hg₃, hg₂, hg₁]
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, g₃]
  have hr9 : s₃.gpr .r9 - 48 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 3)) := by
    rw [g₃, hI.r9, show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl, ofNat_sub_ofNat (by omega) (by omega)]
    congr 1
  refine ⟨⟨by rw [show 16 * (e + 3) = 16 * (e + 2) + 16 by omega]; exact hA₃.gpr2 fg fl fm frd fwr,
    ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun g hg k hk l hl => by rw [fm]; exact hE₃.pv g hg k hk l hl, fun l hl => by rw [fm]; exact hE₃.pm l hl,
    ?_, fun l h1 h4 => by rw [fl]; exact h2.2 l h1 h4⟩, ?_⟩
  · rw [frdx, g₃, hI.rdx, BitVec.add_assoc, show (768 : BitVec 64) = BitVec.ofNat 64 768 from rfl,
      ← BitVec.ofNat_add, show 256 * e + 768 = 256 * (e + 3) by omega]
  · rw [fl, h2.1, hT X yl hI.y1, show 16 * (e + 3) = 16 * e + 48 by omega, ghash_append48, ← hI.y]
  · rw [fcf, hr9, toNat_ofNat_lt (by omega)]
    rfl

theorem loopD48_ok {s₀ : State} (hp : SPre s₀) {T : Nat → Nat → Nat → Block} (hT : FinOk48 (hk s₀) T) {s : State}
    (hI : DInv3 s₀ T 0 s) (h48 : 48 ≤ nb s₀) :
    WP isa (.loop dbody48 .ae) s fun s' => ∃ e, nb s₀ - 16 * e < 48 ∧ DInv3 s₀ T e s' := by
  let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 3) ≤ nb s₀ ∧ DInv3 s₀ T e s
  have hstep : ∀ m s, I m s → WP isa dbody48 s (fun s' =>
      (eval .ae s' = some false ∧ ∃ e, nb s₀ - 16 * e < 48 ∧ DInv3 s₀ T e s') ∨
      (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨e, rfl, he, hI⟩
    refine WP.mono (dbody48_ok hp hT he hI) fun s' ⟨hI', hcf'⟩ => ?_
    by_cases hlt : nb s₀ - 16 * (e + 3) < 48
    · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
        e + 3, hlt, hI'⟩
    · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - 16 * (e + 3), by omega, e + 3, rfl, by omega, hI'⟩
  exact WP.loop (M := isa) I hstep (nb s₀) s ⟨0, by simp, by omega, hI⟩

/-- What `bigD` does after the tables, for any tables `T` whose last is `P`. -/
theorem bigDRest_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} {T : Nat → Nat → Nat → Block}
    (hT : FinOk48 (hk s₀) T) (hT2 : ∀ k l, T 2 k l = P k l) (h256 : 256 ≤ nb s₀) {s s₁ : State}
    (hI : DInv s₀ P 0 s) (hA₁ : AInv s₀ (16 * 0) s₁)
    (hv₁ : ∀ g < 3, ∀ k < 4, ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l)
    (hm₁ : ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) (hg₁ : s₁.gpr = s.gpr)
    (hl₁ : ∀ l < 4, s₁.zlane .xmm2 l = s.zlane .xmm2 l) :
    WP isa (.seq (.loop dbody48 .ae) (.block [.vmovdqu32Load .xmm1 (at_ .r11 832)])) s₁
      fun s' => ∃ e, DInv s₀ P e s' := by
  have hI₁ : DInv3 s₀ T 0 s₁ :=
    ⟨hA₁, by rw [hg₁]; exact hI.rdx, by rw [hg₁]; exact hI.r9, by rw [hg₁]; exact hI.rax,
      fun r h1 h2 h3 h4 => by rw [hg₁]; exact hI.gpr r h1 h2 h3 h4, hv₁, hm₁,
      by rw [hl₁ 0 (by decide)]; exact hI.y, fun l h1 h4 => by rw [hl₁ l h4]; exact hI.y1 l h1 h4⟩
  refine WP.seq (WP.mono (loopD48_ok hp hT hI₁ (by omega)) fun s₂ ⟨e, _, hI₂⟩ => ?_)
  have hr11₂ : s₂.gpr .r11 = pp s₀ := hI₂.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  refine WP.mono (reload_ok hp s₂ hr11₂ hI₂.a.wr hI₂.pm) fun s₃ ⟨p₃, f₃⟩ => ⟨e, ?_⟩
  exact ⟨hI₂.a.zframe f₃ (by decide) (by decide) (by decide), by rw [f₃.gpr]; exact hI₂.rdx,
    by rw [f₃.gpr]; exact hI₂.r9, by rw [f₃.gpr]; exact hI₂.rax,
    fun r h1 h2 h3 h4 => by rw [f₃.gpr]; exact hI₂.gpr r h1 h2 h3 h4,
    fun k hk l hl => by
      have h := hI₂.pv 2 (by decide) k hk l hl
      rw [show tab 2 + 64 * k + 16 * l = 64 * k + 16 * l by simp only [tab]; omega] at h
      rw [f₃.mem, h, hT2],
    p₃, by rw [f₃.zlane _ (by decide) 0 (by decide)]; exact hI₂.y,
    fun l h1 h4 => by rw [f₃.zlane _ (by decide) l h4]; exact hI₂.y1 l h1 h4⟩

/-- `bigD`: from nothing decrypted to all but up to two groups. -/
theorem bigD_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hT : FinOk48 (hk s₀) (T48 P))
    (h256 : 256 ≤ nb s₀) {s : State} (hI : DInv s₀ P 0 s) :
    WP isa bigD s fun s' => ∃ e, DInv s₀ P e s' := by
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  exact WP.seq (WP.mono (powSetup_ok hp hI.a hr11 hI.pw hI.m1) fun s₁ ⟨hA₁, hv₁, hm₁, hg₁, hl₁⟩ =>
    bigDRest_ok hp hT (fun k l => by simp only [T48, ↓reduceIte]) h256 hI hA₁ hv₁ hm₁ hg₁
      fun l hl => hl₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl)

theorem DInv.of_eq {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s s' : State} (h : DInv s₀ P e s)
    (hg : s'.gpr = s.gpr) (hl : ∀ r l, s'.zlane r l = s.zlane r l) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : DInv s₀ P e s' :=
  ⟨h.a.gpr2 (fun r _ _ => by rw [hg]) hl hm hrd hwr, by rw [hg]; exact h.rdx, by rw [hg]; exact h.r9,
    by rw [hg]; exact h.rax, fun r h1 h2 h3 h4 => by rw [hg]; exact h.gpr r h1 h2 h3 h4,
    fun k hk l hl' => by rw [hm]; exact h.pw k hk l hl', fun l hl' => by rw [hl]; exact h.m1 l hl',
    by rw [hl]; exact h.y, fun l h1 h4 => by rw [hl]; exact h.y1 l h1 h4⟩

/-- The loop of one group, from any number of groups decrypted. -/
theorem loopD_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e : Nat} {s : State}
    (hI : DInv s₀ P e s) (hcf : s.cf = some (decide (nb s₀ - 16 * e < 16))) :
    WP isa (.ite .b (.block []) (.loop dbody .ae)) s fun s' => ∃ e, nb s₀ = 16 * e ∧ DInv s₀ P e s' := by
  have hle := hI.a.le
  refine WP.ite (decide (nb s₀ - 16 * e < 16)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil ⟨e, by simp at h; omega, hI⟩
  · let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ DInv s₀ P e s
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
    exact WP.loop (M := isa) I hstep (nb s₀ - 16 * e) s ⟨e, rfl, by simp at h; omega, hI⟩

/-- The decryption after the setup. -/
theorem decTailG_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {bigC : Prog isa} (hbig : ∀ s, 256 ≤ nb s₀ → DInv s₀ P 0 s → WP isa bigC s fun s' => ∃ e, DInv s₀ P e s')
    {s : State} (hR : Ready s₀ P s) :
    WP isa (.seq (.block [.alu .cmp .r9 (.imm 256)]) (.seq (.ite .b (.block []) bigC)
      (.seq (.block [.alu .cmp .r9 (.imm 16)])
        (.seq (.ite .b (.block []) (.loop dbody .ae)) (.block (storeCtr ++ storeY)))))) s (DPost s₀) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hI₁ : DInv s₀ P 0 s :=
    ⟨hR.a, by rw [hR.rdx]; simp, by rw [hR.gpr _ (by decide) (by decide) (by decide)]; simp, hR.rax,
      fun r h1 h2 _ h4 => hR.gpr r h1 h2 h4, hR.pw, hR.m1, by rw [hR.y]; simp [ghashFrom], hR.y1⟩
  refine WP.seq (WP.mono (cmp_ok s 256 256 (by decide)) fun s₂ ⟨hcf, g, l, m, rd, wr⟩ => ?_)
  have hI₂ := hI₁.of_eq g l m rd wr
  rw [hI₁.r9, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by decide)] at hcf
  refine WP.seq (WP.mono (WP.ite (Q := fun s' => ∃ e, DInv s₀ P e s') (decide (nb s₀ - 16 * 0 < 256))
    (by simp only [eval, hcf]) (fun _ => WP.block_nil ⟨0, hI₂⟩)
    (fun h => hbig _ (by simp at h; omega) hI₂)) fun s₃ ⟨e, hI₃⟩ => ?_)
  refine WP.seq (WP.mono (cmp_ok s₃ 16 16 (by decide)) fun s₄ ⟨hcf₄, g₄, l₄, m₄, rd₄, wr₄⟩ => ?_)
  have hI₄ := hI₃.of_eq g₄ l₄ m₄ rd₄ wr₄
  rw [hI₃.r9, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by decide)] at hcf₄
  exact WP.seq (WP.mono (loopD_ok hp hm hf hI₄ hcf₄) fun s₅ ⟨e, he, hI₅⟩ => dfinal_ok hp he hI₅)

/-- The decryption after the setup. -/
theorem decTail_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hT : FinOk48 (hk s₀) (T48 P)) {s : State} (hR : Ready s₀ P s) :
    WP isa (.seq (.block [.alu .cmp .r9 (.imm 256)]) (.seq (.ite .b (.block []) bigD)
      (.seq (.block [.alu .cmp .r9 (.imm 16)])
        (.seq (.ite .b (.block []) (.loop dbody .ae)) (.block (storeCtr ++ storeY)))))) s (DPost s₀) :=
  decTailG_ok hp hm hf (fun _ h256 hI => bigD_ok hp hT h256 hI) hR

end VG.Proof.Gcm.X86_64.StitchZ
