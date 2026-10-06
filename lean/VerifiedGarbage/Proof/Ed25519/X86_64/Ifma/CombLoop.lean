import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombAdd
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombSelect
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLoop
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep

/-!
# Ed25519's comb with AVX512_IFMA: a step

A step of `Ifma.combStep`, as `combStep_ok` proves one of `combStep`: the
four doublings and `[G]B` before the even digits (`vdbl4`, `gEntry`), then the
digit's table entry, selected (`vselect`), negated for a negative digit and
added to the point in the lanes (`ventry`).
-/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Ifma VG.Proof.Ed25519
  VG.Proof.Ed25519.X86_64 Edwards
open VG.Impl.X25519.X86_64.Ifma (KM K19 KB0 KB1 OPL OPV kb ord y ld)
open VG.Proof.X25519.X86_64.Ifma (lanes fe5 fe5_congr vm vm_gpr vm_rd vm_wr Ctx run_ok symOf symOf_eq Sym T envOf
  envOf_m envOf_v mq)
open VG.Proof.X25519.X86_64 (Outside F off)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

/-! ## The sum -/

/-- The sum the lanes compute is `pointAdd` with a cached point. -/
theorem vAddPt_cache (P q : Spec.Ed25519.Point) :
    vAddPt P (cache q) = Spec.Ed25519.pointAdd P q := by
  simp only [vAddPt, cache, Spec.Ed25519.pointAdd]
  congr 1 <;> grind

/-! ## Four doublings -/

/-- The doublings' invariant, with `n` left. -/
structure DInv (s : State) (base : Addr) (a : EPoint dZ) (n : Nat) (t : State) : Prop where
  pos : 0 < n
  le : n ≤ 4
  rdi : t.gpr .rdi = base
  rsi : t.gpr .rsi = BitVec.ofNat 64 n
  gpr : ∀ r, r ≠ .rsi → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 1024 320 s.mem t.mem
  consts : EConsts t.mem base
  small : Small t
  rep : Rep (lanePt t) ((2 ^ (4 - n) : Nat) • a)

theorem vdbl4_ok {s : State} {base : Addr} (hs : Scratch s base) (hk : EConsts s.mem base) (hx : Small s)
    {a : EPoint dZ} (ha : Rep (lanePt s) a) :
    WP isa vdbl4 s fun t => (∀ r, r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 1024 320 s.mem t.mem ∧ Small t ∧ Rep (lanePt t) ((16 : Nat) • a) := by
  rw [vdbl4]
  refine WP.seq (WP.mono (mov32_wp s .rsi 4) fun s₁ ⟨r₁, g₁, m₁, rd₁, wr₁, q₁⟩ => ?_)
  have h₁ : DInv s base a 4 s₁ :=
    ⟨by decide, by decide, by rw [g₁ _ (by decide)]; exact hs.rdi, r₁, g₁, rd₁, wr₁,
      by rw [m₁]; exact Outside.refl _ _ _ _, by rw [m₁]; exact hk,
      fun l hl i hi => by rw [lanes_qw q₁]; exact hx l hl i hi, by rw [lanePt_qw q₁]; simpa using ha⟩
  refine WP.loop (DInv s base a) (fun n t h => ?_) 4 s₁ h₁
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.pos; omega : n ≠ 0)
  have hst : Scratch t base := ⟨h.rdi, by rw [h.wr]; exact hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (vdbl_wp h.rdi (ctx_of hst) h.consts h.small) fun u ⟨ug, urd, uwr, uo, usm, up⟩ => ?_
  refine WP.mono (dec_wp u k (by have := h.le; omega) (by rw [ug]; exact h.rsi)) fun w ⟨wc, wz, kw, wq⟩ => ?_
  have wr' : w.gpr .rdi = base := by rw [kw.1 _ (by decide), ug]; exact h.rdi
  have wg : ∀ r, r ≠ .rsi → w.gpr r = s.gpr r := fun r hr' => by
    rw [kw.1 _ (by simpa using hr'), ug]; exact h.gpr r hr'
  have wrd : w.rd = s.rd := by rw [kw.2.2.1, urd]; exact h.rd
  have wwr : w.wr = s.wr := by rw [kw.2.2.2, uwr]; exact h.wr
  have wm : Outside base 1024 320 s.mem w.mem := by rw [kw.2.1]; exact h.mem.trans uo
  have wk : EConsts w.mem base := by rw [kw.2.1]; exact h.consts.outside uo
  have wsm : Small w := by intro l hl i hi; rw [lanes_qw wq]; exact usm l hl i hi
  have wp : Rep (lanePt w) ((2 ^ (4 - k) : Nat) • a) := by
    rw [lanePt_qw wq, up, show 4 - k = (4 - (k + 1)) + 1 by have := h.le; omega, pow_succ, mul_nsmul,
      two_nsmul]
    exact dblPoint_rep h.rep.proj
  by_cases hk0 : k = 0
  · subst hk0
    exact Or.inl ⟨by simp only [eval, wz, decide_true, Option.map_some, Bool.not_true], wg, wrd, wwr, wm, wsm,
      by simpa using wp⟩
  · exact Or.inr ⟨by simp only [eval, wz, decide_eq_false hk0, Option.map_some, Bool.not_false],
      k, by omega, ⟨by omega, by have := h.le; omega, wr', wc, wg, wrd, wwr, wm, wk, wsm, wp⟩⟩

/-! ## `[G]B`'s entry -/

def gloadS : Sym := symOf [ld 11 (offset 9), ld 12 (offset 10), ld 13 (offset 11)]

theorem gloadS_regs : gloadS.reg 11 = .ld (offset 9) ∧ gloadS.reg 12 = .ld (offset 10) ∧
    gloadS.reg 13 = .ld (offset 11) := by decide +kernel
theorem gloadS_keep : ∀ r < 11, gloadS.reg r = .reg r := by decide +kernel
theorem gloadS_st : gloadS.st = [] := by decide +kernel

/-- `gEntry`: `rax = rcx = 0`, and the words of slots 9–11 in `ymm11–ymm13`. -/
theorem gEntry_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block gEntry) s fun t => t.gpr .rax = 0 ∧ t.gpr .rcx = 0 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ k < 4, qw t (xr 11) k = mq s.mem base (offset 9 + 8 * k) ∧
        qw t (xr 12) k = mq s.mem base (offset 10 + 8 * k) ∧ qw t (xr 13) k = mq s.mem base (offset 11 + 8 * k)) ∧
      (∀ r < 11, ∀ l < 4, qw t (xr r) l = qw s (xr r) l) := by
  rw [gEntry, show ([.mov32 .rax (.imm 0), .mov32 .rcx (.imm 0), ld 11 (offset 9), ld 12 (offset 10),
      ld 13 (offset 11)] : List Instr) = [.mov32 .rax (.imm 0)] ++ [.mov32 .rcx (.imm 0)] ++
      [ld 11 (offset 9), ld 12 (offset 10), ld 13 (offset 11)] from rfl, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (mov32_wp s .rax 0) fun s₁ ⟨a₁, g₁, m₁, rd₁, wr₁, q₁⟩ => ?_
  refine WP.mono (mov32_wp s₁ .rcx 0) fun s₂ ⟨a₂, g₂, m₂, rd₂, wr₂, q₂⟩ => ?_
  have hs₂ : Scratch s₂ base :=
    ⟨by rw [g₂ _ (by decide), g₁ _ (by decide)]; exact hs.rdi, by rw [wr₂, wr₁]; exact hs.wr, hs.nowrap⟩
  have e : Sym.init.run [ld 11 (offset 9), ld 12 (offset 10), ld 13 (offset 11)] = some gloadS :=
    symOf_eq _ _
  refine WP.mono (run_ok (ctx_of hs₂) e) fun t h => ?_
  have tg : t.gpr = s₂.gpr := h.gpr
  have tm : t.mem = s₂.mem := by rw [h.mem, gloadS_st]; rfl
  refine ⟨by rw [tg, g₂ _ (by decide), a₁]; rfl, by rw [tg, a₂]; rfl,
    fun r h1 h2 => by rw [tg, g₂ r h2, g₁ r h1], by rw [tm, m₂, m₁], by rw [h.rd, rd₂, rd₁],
    by rw [h.wr, wr₂, wr₁], fun k hk => ?_, fun r hr l hl => ?_⟩
  · have e : ∀ r d, r < 16 → gloadS.reg r = .ld d → qw t (xr r) k = mq s.mem base (d + 8 * k) :=
      fun r d hr hd => by
        rw [h.reg _ k hk, VG.Proof.X25519.X86_64.Ifma.xi_xr r hr, hd]
        simp only [T.eval, mq, m₂, m₁, hs₂.rdi]
    exact ⟨e 11 _ (by decide) gloadS_regs.1, e 12 _ (by decide) gloadS_regs.2.1,
      e 13 _ (by decide) gloadS_regs.2.2⟩
  · rw [h.keep (by omega) hl (gloadS_keep r hr), q₂, q₁]

/-! ## The flags of the digit -/

/-- `rax = 1` for a zero magnitude, and the sign's mask into `rcx`. -/
theorem combFlags_ok {s : State} {base : Addr} (hs : Scratch s base) {a : Nat} (ha : a < 2 ^ 64)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 a) {m : BitVec 64} (hm : s.mem.readW (off base combSignMask) 64 = m) :
    WP isa (.block combFlags) s fun t => t.gpr .rax = (if a = 0 then 1 else 0) ∧ t.gpr .rcx = m ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hM : (BitVec.ofNat 64 a - BitVec.ofNat 64 a - BitVec.setWidth 64 (BitVec.ofBool
      (decide ((BitVec.ofNat 64 a).toNat < (BitVec.signExtend 64 (1 : BitVec 32)).toNat)))) &&&
      BitVec.signExtend 64 (1 : BitVec 32) = if a = 0 then 1 else 0 := by
    by_cases h : a = 0
    · subst h; decide
    · have h1 : (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 := by decide
      rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, decide_eq_false (by omega),
        ite_eq_right_iff.mpr (fun h2 => absurd h2 h)]
      simp
  rw [combFlags, show ([.mov .rax (.reg .r8), .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax),
      .alu .and .rax (.imm 1), .mov .rcx (.mem (Impl.X25519.X86_64.sc combSignMask))] : List Instr) =
      [.mov .rax (.reg .r8), .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 1)] ++
      [.mov .rcx (.mem (Impl.X25519.X86_64.sc combSignMask))] from rfl, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov .rax (.reg .r8), .alu .cmp .rax (.imm 1),
      .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 1)]) s fun t =>
      t.gpr .rax = (if a = 0 then 1 else 0) ∧ VG.Proof.X25519.X86_64.Keeps [.rax] s t by
    erun [h8, hM]
    refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨a₁, k₁⟩ => ?_
  have hs₁ : Scratch s₁ base := hs.of_keeps k₁ (by decide)
  refine WP.mono (loadSignMask_ok hs₁ (by rw [k₁.2.1]; exact hm)) fun t ⟨c₂, k₂⟩ =>
    ⟨by rw [k₂.1 _ (by decide), a₁], c₂, fun r h1 h2 => by
      rw [k₂.1 r (by simpa using h2), k₁.1 r (by simpa using h1)], by rw [k₂.2.1, k₁.2.1],
      by rw [k₂.2.2.1, k₁.2.2.1], by rw [k₂.2.2.2, k₁.2.2.2]⟩

/-! ## The entry's value -/

theorem val4_feWord (v : Spec.X25519.Fe) :
    VG.Proof.X25519.toFe ((feWord v 0).toNat + 2 ^ 64 * (feWord v 1).toNat + 2 ^ 128 * (feWord v 2).toNat +
      2 ^ 192 * (feWord v 3).toNat) = v := by
  have := feWord_val v
  simp only [VG.Proof.X25519.X86_64.val4] at this
  rw [this, VG.Proof.X25519.toFe_self]

theorem ite_zero_toNat (p : Prop) [Decidable p] : (if p then (0 : BitVec 64).toNat else 0) = 0 := by
  split <;> rfl

/-- The entry `vselect` and `combFlags` leave: `combCached`'s fields. -/
theorem entryOf_tbl {s : State} {j a : Nat}
    (hq : ∀ c < 3, ∀ k < 4, qw s (xr (11 + c)) k = if 1 ≤ a then feWord (combField j a c) k else 0)
    (hax : s.gpr .rax = if a = 0 then 1 else 0) :
    entryOf s = ⟨combField j a 0, combField j a 1, combField j a 2, 2⟩ := by
  have w : ∀ c < 3, erowFe s c = combField j a c := fun c hc => by
    simp only [erowFe]
    by_cases h1 : 1 ≤ a
    · have hr : ∀ k < 4, erow (envOf s) c k = (feWord (combField j a c) k).toNat := fun k hk => by
        have hk' := hq c hc k hk
        rw [ite_eq_left_of_eq_true _ _ (eq_true h1)] at hk'
        rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;>
          simp only [erow, envOf, hk', hax, show a ≠ 0 by omega, ↓reduceIte, ite_zero_toNat, Nat.or_zero]
      rw [hr 0 (by decide), hr 1 (by decide), hr 2 (by decide), hr 3 (by decide), val4_feWord]
    · obtain rfl : a = 0 := by omega
      have hr : ∀ k < 4, erow (envOf s) c k = if c < 2 ∧ k = 0 then 1 else 0 := fun k hk => by
        have hk' := hq c hc k hk
        rw [ite_eq_right_of_eq_false _ _ (eq_false h1)] at hk'
        rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;>
          rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;>
          simp only [erow, envOf, hk', hax, ↓reduceIte] <;> rfl
      rw [hr 0 (by decide), hr 1 (by decide), hr 2 (by decide), hr 3 (by decide)]
      rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> rfl
  simp only [entryOf, w 0 (by decide), w 1 (by decide), w 2 (by decide)]

/-- The entry's row `c` loaded from the slot at `o`, with `rax = 0`. -/
theorem erowFe_slot {s : State} {m : Mem} {base : Addr} {o c : Nat} (hc : c < 3) (hax : s.gpr .rax = 0)
    (hq : ∀ k < 4, qw s (xr (11 + c)) k = mq m base (o + 8 * k)) : erowFe s c = F m base o := by
  simp only [erowFe]
  have e : ∀ k < 4, erow (envOf s) c k = (mq m base (o + 8 * k)).toNat := fun k hk => by
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;>
      simp only [erow, envOf, ← hq k hk, hax, ite_zero_toNat, Nat.or_zero, Nat.add_zero]
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]
  rfl

/-! ## The loop's invariant -/

/-- What the loop needs of the state `s₀` it starts from. -/
structure LoopPre (s₀ : State) (base T : Addr) (S : Nat) : Prop where
  scratch : Scratch s₀ base
  consts : EConsts s₀.mem base
  k2 : F s₀.mem base K2 = 2
  g0 : F s₀.mem base (offset 9) = combGCached.X
  g1 : F s₀.mem base (offset 10) = combGCached.Y
  g2 : F s₀.mem base (offset 11) = combGCached.Z
  bits : ∀ q < 256, s₀.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)
  tbl : CombTbl s₀ T
  far : TblFar base T

/-- What the loop keeps of `s₀`: the registers but `rbx`, `rsi` and `clob` (whose `r11` holds
the saved MXCSR, kept too), the regions, the memory but the products' operands and the
sign's mask (bytes `1024–1343` of the scratch), and the statics. -/
structure VFrame (s₀ : State) (base : Addr) (s : State) : Prop where
  gpr : ∀ r, r ≠ .rbx → r ≠ .rsi → r ∉ VG.Proof.X25519.X86_64.clob → s.gpr r = s₀.gpr r
  r11 : s.gpr .r11 = s₀.gpr .r11
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base 1024 320 s₀.mem s.mem
  syms : s.syms = s₀.syms

theorem VFrame.refl (s₀ : State) (base : Addr) : VFrame s₀ base s₀ :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _, rfl⟩

theorem VFrame.step {s₀ s t : State} {base : Addr} {rs : List Reg} (h : VFrame s₀ base s)
    (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ (r ∈ VG.Proof.X25519.X86_64.clob ∧ r ≠ .r11))
    (hg : ∀ r, r ∉ rs → t.gpr r = s.gpr r) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hm : Outside base 1024 320 s.mem t.mem) (hsy : t.syms = s.syms) : VFrame s₀ base t :=
  ⟨fun r h1 h2 h3 => (hg r fun hr => by
      rcases hrs r hr with e | e | ⟨e, _⟩
      · exact h1 e
      · exact h2 e
      · exact h3 e).trans (h.gpr r h1 h2 h3),
    (hg _ fun hr => by
      rcases hrs _ hr with e | e | ⟨_, e⟩
      · exact absurd e (by decide)
      · exact absurd e (by decide)
      · exact e rfl).trans h.r11,
    hrd.trans h.rd, hwr.trans h.wr, h.mem.trans hm, hsy.trans h.syms⟩

theorem VFrame.keeps {s₀ s t : State} {base : Addr} {rs : List Reg} (h : VFrame s₀ base s)
    (k : VG.Proof.X25519.X86_64.Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ (r ∈ VG.Proof.X25519.X86_64.clob ∧ r ≠ .r11))
    (hsy : t.syms = s.syms) : VFrame s₀ base t :=
  h.step hrs k.1 k.2.2.1 k.2.2.2 (by rw [k.2.1]; exact Outside.refl _ _ _ _) hsy

theorem VFrame.keep {s₀ s : State} {base : Addr} (h : VFrame s₀ base s) : PowersKeep base 56 7368 s₀ s :=
  ⟨fun r h1 h2 h3 => h.gpr r h1 h2 h3, h.rd, h.wr, (TableFrame.table h.mem).mono (by decide) (by decide)⟩

theorem VFrame.scratch {s₀ s : State} {base T : Addr} {S : Nat} (hp : LoopPre s₀ base T S)
    (h : VFrame s₀ base s) (hr : s.gpr .rdi = base) : Scratch s base :=
  ⟨hr, by rw [h.wr]; exact hp.scratch.wr, hp.scratch.nowrap⟩

theorem VFrame.tbl {s₀ s : State} {base T : Addr} {S : Nat} (hp : LoopPre s₀ base T S)
    (h : VFrame s₀ base s) : CombTbl s T :=
  hp.tbl.keep hp.far h.keep h.syms

theorem VFrame.consts {s₀ s : State} {base T : Addr} {S : Nat} (hp : LoopPre s₀ base T S)
    (h : VFrame s₀ base s) : EConsts s.mem base :=
  hp.consts.outside h.mem

theorem VFrame.k2 {s₀ s : State} {base T : Addr} {S : Nat} (hp : LoopPre s₀ base T S)
    (h : VFrame s₀ base s) : F s.mem base K2 = 2 := by
  rw [Outside_F h.mem (by decide) (Or.inl (by decide))]; exact hp.k2

theorem VFrame.bits {s₀ s : State} {base T : Addr} {S : Nat} (hp : LoopPre s₀ base T S)
    (h : VFrame s₀ base s) : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2) :=
  fun q hq => by rw [h.mem _ (Or.inl (by rw [bits_far hq]; omega))]; exact hp.bits q hq

/-- The loop's invariant after `c` steps, with the point in the lanes `[v]B`. -/
structure VInv (s₀ : State) (base : Addr) (c : Nat) (v : ℤ) (s : State) : Prop where
  bound : c ≤ 64
  rdi : s.gpr .rdi = base
  counter : s.gpr .rbx = BitVec.ofNat 64 c
  frame : VFrame s₀ base s
  small : Small s
  value : Rep (lanePt s) (v • baseAff)

theorem lanes0_eq {s t : State} (h : ∀ r < 5, ∀ l < 4, qw t (xr r) l = qw s (xr r) l) :
    lanePt t = lanePt s ∧ (Small s → Small t) := by
  have e : ∀ l < 4, ∀ i < 5, lanes t 0 l i = lanes s 0 l i := fun l hl i hi => by
    simp only [lanes, Nat.zero_add]; rw [h i hi l hl]
  refine ⟨?_, fun hs l hl i hi => by rw [e l hl i hi]; exact hs l hl i hi⟩
  simp only [lanePt]
  rw [fe5_congr (e 0 (by decide)), fe5_congr (e 1 (by decide)), fe5_congr (e 2 (by decide)),
    fe5_congr (e 3 (by decide))]

theorem lanes0_vec {s t : State} (hx : t.xmm = s.xmm) (hy : t.ymmHi = s.ymmHi) :
    ∀ r < 5, ∀ l < 4, qw t (xr r) l = qw s (xr r) l := fun _ _ _ _ => qw_of hx hy _ _

/-- Before the even digits: four doublings, then `[G]B` added. -/
theorem vstepG_ok {s₀ a : State} {base T : Addr} {S c : Nat} {v : ℤ} (hp : LoopPre s₀ base T S)
    (h : VInv s₀ base c v a) :
    WP isa (.seq vdbl4 (.block (gEntry ++ ventry))) a fun b => VInv s₀ base c (16 * v + combGVal) b := by
  have hsa := h.frame.scratch hp h.rdi
  refine WP.seq (WP.mono_syms (vdbl4_ok hsa (h.frame.consts hp) h.small h.value)
    fun b₁ ⟨g₁, rd₁, wr₁, o₁, sm₁, rep₁⟩ sy₁ => ?_)
  have f₁ : VFrame s₀ base b₁ := h.frame.step (rs := [.rsi]) (by decide) (fun r hr => g₁ r (by simpa using hr))
    rd₁ wr₁ o₁ sy₁
  have hs₁ : Scratch b₁ base := f₁.scratch hp (by rw [g₁ _ (by decide)]; exact h.rdi)
  rw [WP.block_append_iff]
  refine WP.mono_syms (gEntry_ok hs₁) fun b₂ ⟨ax₂, cx₂, g₂, m₂, rd₂, wr₂, q₂, k₂⟩ sy₂ => ?_
  have f₂ : VFrame s₀ base b₂ := f₁.step (rs := [.rax, .rcx]) (by decide)
    (fun r hr => g₂ r (fun e => hr (by simp [e])) (fun e => hr (by simp [e]))) rd₂ wr₂
    (by rw [m₂]; exact Outside.refl _ _ _ _) sy₂
  have hs₂ : Scratch b₂ base := f₂.scratch hp (by rw [g₂ _ (by decide) (by decide)]; exact hs₁.rdi)
  obtain ⟨p₂, sm₂⟩ := lanes0_eq (s := b₁) (t := b₂) fun r hr l hl => k₂ r (by omega) l hl
  have m9 : F b₁.mem base (offset 9) = F s₀.mem base (offset 9) := Outside_F f₁.mem (by decide) (Or.inl (by decide))
  have m10 : F b₁.mem base (offset 10) = F s₀.mem base (offset 10) :=
    Outside_F f₁.mem (by decide) (Or.inl (by decide))
  have m11 : F b₁.mem base (offset 11) = F s₀.mem base (offset 11) :=
    Outside_F f₁.mem (by decide) (Or.inl (by decide))
  have he : entryOf b₂ = combGCached := by
    simp only [entryOf]
    rw [erowFe_slot (c := 0) (by decide) ax₂ fun k hk => (q₂ k hk).1,
      erowFe_slot (c := 1) (by decide) ax₂ fun k hk => (q₂ k hk).2.1,
      erowFe_slot (c := 2) (by decide) ax₂ fun k hk => (q₂ k hk).2.2,
      m9, m10, m11, hp.g0, hp.g1, hp.g2]
    rfl
  refine WP.mono_syms (ventry_wp (b := false) hs₂.rdi (ctx_of hs₂) (f₂.consts hp) (sm₂ sm₁) (f₂.k2 hp)
    (by rw [cx₂]; rfl)) fun b₃ ⟨g₃, rd₃, wr₃, o₃, sm₃, p₃⟩ sy₃ => ?_
  have f₃ : VFrame s₀ base b₃ := f₂.step (rs := []) (by decide) (fun r _ => by rw [g₃]) rd₃ wr₃ o₃ sy₃
  refine ⟨h.bound, by rw [g₃]; exact hs₂.rdi, ?_, f₃, sm₃, ?_⟩
  · rw [g₃, g₂ _ (by decide) (by decide), g₁ _ (by decide)]; exact h.counter
  · rw [p₃, p₂, he, show negIf false combGCached = combGCached from rfl, combGCached_eq, vAddPt_cache,
      ← zsmul_16]
    exact pointAdd_rep rep₁ combG_ok

theorem combCached_T (j a : Nat) : (combCached j a).T = 2 := by
  simp only [combCached]; split <;> rfl

/-- The digit's entry of its table, negated for a negative digit, added. -/
theorem vstepD_ok {s₀ b : State} {base T : Addr} {S c : Nat} {v : ℤ} (hp : LoopPre s₀ base T S)
    (h : VInv s₀ base c v b) (hc : c < 64) :
    WP isa (.seq combIndex (.block (combDigit ++ combSign ++ ([.mov .r8 (.reg .rax), .mov .rdx (.reg .rbx),
      .alu .and .rdx (.imm 31)] : List Instr) ++ vselect ++ combFlags ++ ventry ++
      ([.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 64)] : List Instr)))) b fun t =>
      t.zf = some (decide (c + 1 = 64)) ∧
        VInv s₀ base (c + 1) (sdig S (combIdx c) * 256 ^ (c % 32) + v) t := by
  have hsb := h.frame.scratch hp h.rdi
  refine WP.seq (WP.mono_syms (WP.vecKeep (by decide) (combIndex_ok b hc h.counter))
    fun e ⟨⟨ec, ke⟩, ex, ey⟩ esy => ?_)
  have fe : VFrame s₀ base e := h.frame.keeps ke (by decide) esy
  have hse : Scratch e base := hsb.of_keeps ke (by decide)
  have hn : nib S (combIdx c) < 16 := Nat.mod_lt _ (by decide)
  have hmag : mag (nib S (combIdx c)) < 9 := by unfold mag; split <;> omega
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono_syms (WP.vecKeep (by decide) (combDigit_ok (S := S) hse (combIdx_lt hc) ec (fe.bits hp)))
    fun f ⟨⟨fax, kf⟩, fx, fy⟩ fsy => ?_
  have ff : VFrame s₀ base f := fe.keeps kf (by decide) fsy
  have hsf : Scratch f base := hse.of_keeps kf (by decide)
  rw [WP.block_append_iff]
  refine WP.mono_syms (WP.vecKeep (by decide) (combSign_ok (n := nib S (combIdx c)) hsf hn fax))
    fun f' ⟨⟨f'ax, f'm, f'g, f'r, f'w, f'mem⟩, f'x, f'y⟩ f'sy => ?_
  have ff' : VFrame s₀ base f' := ff.step (rs := [.rax, .rdx]) (by decide)
    (fun r hr => f'g r (fun e => hr (by simp [e])) (fun e => hr (by simp [e]))) f'r f'w
    (f'mem.mono (by simp only [combSignMask]; omega) (by simp only [combSignMask]; omega)) f'sy
  have hsf' : Scratch f' base := ⟨(f'g _ (by decide) (by decide)).trans hsf.rdi, f'w ▸ hsf.wr, hsf.nowrap⟩
  have f'c : f'.gpr .rbx = BitVec.ofNat 64 c := by
    rw [f'g _ (by decide) (by decide), kf.1 _ (by decide), ke.1 _ (by decide)]; exact h.counter
  rw [WP.block_append_iff]
  refine WP.mono_syms (WP.vecKeep (by decide) (combMagIdx_ok f' hc f'ax f'c))
    fun g ⟨⟨g8, gx, kg⟩, gxx, gyy⟩ gsy => ?_
  have fg : VFrame s₀ base g := ff'.keeps kg (by decide) gsy
  have hsg : Scratch g base := hsf'.of_keeps kg (by decide)
  rw [WP.block_append_iff]
  refine WP.mono_syms (vselect_ok (fg.tbl hp) (Nat.mod_lt _ (by decide)) (by omega) gx g8)
    fun u ⟨uq, ku⟩ usy => ?_
  have fu : VFrame s₀ base u := fg.step (rs := [.rax, .rcx, .rdx]) (by decide) ku.gpr ku.rd ku.wr
    (by rw [ku.mem]; exact Outside.refl _ _ _ _) usy
  have hsu : Scratch u base := fu.scratch hp (by rw [ku.gpr _ (by decide)]; exact hsg.rdi)
  have usm : u.mem.readW (off base combSignMask) 64 = signMask (nib S (combIdx c)) := by
    rw [ku.mem, kg.2.1]; exact f'm
  rw [WP.block_append_iff]
  refine WP.mono_syms (WP.vecKeep (by decide) (combFlags_ok hsu (a := mag (nib S (combIdx c))) (by omega)
    (by rw [ku.gpr _ (by decide)]; exact g8) usm)) fun u' ⟨⟨u'ax, u'cx, u'g, u'm, u'rd, u'wr⟩, u'x, u'y⟩ u'sy => ?_
  have fu' : VFrame s₀ base u' := fu.step (rs := [.rax, .rcx]) (by decide)
    (fun r hr => u'g r (fun e => hr (by simp [e])) (fun e => hr (by simp [e]))) u'rd u'wr
    (by rw [u'm]; exact Outside.refl _ _ _ _) u'sy
  have hsu' : Scratch u' base := fu'.scratch hp (by rw [u'g _ (by decide) (by decide)]; exact hsu.rdi)
  -- The lanes of the point, kept since `b`.
  have l₁ := lanes0_vec ex ey; have l₂ := lanes0_vec fx fy; have l₃ := lanes0_vec f'x f'y
  have l₄ := lanes0_vec gxx gyy; have l₆ := lanes0_vec u'x u'y
  have l₅ : ∀ r < 5, ∀ l < 4, qw u (xr r) l = qw g (xr r) l := fun r hr l hl => ku.qw _ (by
    simp only [selRegs, not_or, not_exists, not_and]
    refine ⟨fun e => ?_, fun c' hc' e => ?_, fun e => ?_⟩ <;>
    · have := congrArg VG.Proof.Poly1305.X86_64.Avx2.xi e
      rw [VG.Proof.X25519.X86_64.Ifma.xi_xr _ (by omega), VG.Proof.X25519.X86_64.Ifma.xi_xr _ (by omega)] at this
      omega) l hl
  have hl : ∀ r < 5, ∀ l < 4, qw u' (xr r) l = qw b (xr r) l := fun r hr l hl =>
    (l₆ r hr l hl).trans ((l₅ r hr l hl).trans ((l₄ r hr l hl).trans ((l₃ r hr l hl).trans
      ((l₂ r hr l hl).trans (l₁ r hr l hl)))))
  obtain ⟨pu', smu'⟩ := lanes0_eq hl
  -- The entry.
  have hq' : ∀ c' < 3, ∀ k < 4, qw u' (xr (11 + c')) k = if 1 ≤ mag (nib S (combIdx c)) then
      feWord (combField (c % 32) (mag (nib S (combIdx c))) c') k else 0 := fun c' hc' k hk => by
    rw [qw_of u'x u'y]; exact uq c' hc' k hk
  have hentry := entryOf_tbl hq' u'ax
  rw [WP.block_append_iff]
  refine WP.mono_syms (ventry_wp (b := decide (nib S (combIdx c) < 8)) hsu'.rdi (ctx_of hsu') (fu'.consts hp)
    (smu' h.small) (fu'.k2 hp) (by rw [u'cx, signMask_eq])) fun w ⟨wg, wrd, wwr, wo, wsm, wp⟩ wsy => ?_
  have fw : VFrame s₀ base w := fu'.step (rs := []) (by decide) (fun r _ => by rw [wg]) wrd wwr wo wsy
  have wc : w.gpr .rbx = BitVec.ofNat 64 c := by
    rw [wg, u'g _ (by decide) (by decide), ku.gpr _ (by decide), kg.1 _ (by decide)]; exact f'c
  refine WP.mono_syms (WP.vecKeep (by decide) (rbxNext64_ok w c hc wc)) fun t ⟨⟨tc, tz, kt⟩, tx, ty⟩ tsy =>
    ⟨tz, by omega, by rw [kt.1 _ (by decide), wg]; exact hsu'.rdi, tc, fw.keeps kt (by decide) tsy,
      (lanes0_eq (lanes0_vec tx ty)).2 wsm, ?_⟩
  rw [(lanes0_eq (lanes0_vec tx ty)).1, wp, pu', hentry]
  obtain ⟨q₀, hq₀, hrq₀⟩ := combCached_ok (c % 32) (mag (nib S (combIdx c))) (Nat.mod_lt _ (by decide)) hmag
  have hcc : (⟨combField (c % 32) (mag (nib S (combIdx c))) 0, combField (c % 32) (mag (nib S (combIdx c))) 1,
      combField (c % 32) (mag (nib S (combIdx c))) 2, 2⟩ : Spec.Ed25519.Point) = cache q₀ := by
    rw [← hq₀, ← combCached_T (c % 32) (mag (nib S (combIdx c)))]
    rfl
  let q := if nib S (combIdx c) < 8 then negPoint q₀ else q₀
  have hneg : negIf (decide (nib S (combIdx c) < 8)) (cache q₀) = cache q := by
    by_cases hlt : nib S (combIdx c) < 8
    · simp only [hlt, decide_true, negIf, ↓reduceIte, q]
      exact VG.Proof.Ed25519.X86_64.negCached_cache q₀
    · simp only [hlt, decide_false, negIf, Bool.false_eq_true, ↓reduceIte, q]
  have hrq : Rep q ((sdig S (combIdx c) * 256 ^ (c % 32)) • baseAff) := by
    by_cases hlt : nib S (combIdx c) < 8
    · simp only [hlt, ↓reduceIte, q]
      have e : sdig S (combIdx c) * 256 ^ (c % 32) = -(((mag (nib S (combIdx c)) * 256 ^ (c % 32) : Nat) : ℤ)) := by
        simp only [sdig, mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega : nib S (combIdx c) ≤ 8)]; ring
      rw [e, neg_smul, natCast_zsmul]
      exact hrq₀.neg
    · simp only [hlt, ↓reduceIte, q]
      have e : sdig S (combIdx c) * 256 ^ (c % 32) = (((mag (nib S (combIdx c)) * 256 ^ (c % 32) : Nat) : ℤ)) := by
        simp only [sdig, mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega : 8 ≤ nib S (combIdx c))]; ring
      rw [e, natCast_zsmul]
      exact hrq₀
  rw [hcc, hneg, vAddPt_cache, add_smul, add_comm]
  exact pointAdd_rep h.value hrq

/-- A step of the loop. -/
theorem vstep_ok {s₀ s : State} {base T : Addr} {S c : Nat} (hp : LoopPre s₀ base T S)
    (h : VInv s₀ base c (combVal S c) s) (hc : c < 64) :
    WP isa Impl.Ed25519.X86_64.Ifma.combStep s fun t =>
      t.zf = some (decide (c + 1 = 64)) ∧ VInv s₀ base (c + 1) (combVal S (c + 1)) t := by
  rw [Impl.Ed25519.X86_64.Ifma.combStep]
  refine WP.seq (WP.mono_syms (WP.vecKeep (by decide) (rbxCmp_ok s c 32 hc (by decide) h.counter))
    fun a ⟨⟨az, ag, am, ar, aw⟩, ax, ay⟩ asy => ?_)
  have ha : VInv s₀ base c (combVal S c) a :=
    ⟨h.bound, by rw [ag]; exact h.rdi, by rw [ag]; exact h.counter,
      h.frame.step (rs := []) (by decide) (fun r _ => by rw [ag]) ar aw (by rw [am]; exact Outside.refl _ _ _ _)
        asy, (lanes0_eq (lanes0_vec ax ay)).2 h.small, by rw [(lanes0_eq (lanes0_vec ax ay)).1]; exact h.value⟩
  refine WP.seq (WP.mono (show WP isa (.ite .e (.seq vdbl4 (.block (gEntry ++ ventry))) (.block [])) a
      fun b => VInv s₀ base c (if c = 32 then 16 * combVal S c + combGVal else combVal S c) b from
    WP.ite (decide (c = 32)) (by simp only [eval, az])
      (fun hy => by
        rw [ite_eq_left_of_eq_true _ _ (eq_true (of_decide_eq_true hy))]
        exact vstepG_ok hp ha)
      (fun hn => by
        rw [ite_eq_right_of_eq_false _ _ (eq_false (of_decide_eq_false hn))]
        exact WP.block_nil ha)) fun b hb => ?_)
  exact WP.mono (vstepD_ok hp hb hc) fun t ⟨tz, ht⟩ => ⟨tz, by rw [← combIdx_nib S c hc]; exact ht⟩

end VG.Proof.Ed25519.X86_64.Ifma
