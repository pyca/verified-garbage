module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.WotsChain
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Tree
public import VerifiedGarbage.Proof.SlhDsa.LevelsSpec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.SlhDsa.Lemmas

/-!
# SLH-DSA on AArch64: `levels`, its entry, prologue and alignment

As on x86-64 (`Proof/SlhDsa/X86_64/LevelsCorrect.lean`), in the style of
`wotsLeaves4`'s proof (`WotsBase.lean`): the facts of the entry state the
proof uses (`Entry`), what holds at every point of the code (`Base`: the
registers that hold `scratch` and the nodes, the caller's registers in
frame 3, the parameters in frame 3, and the frame of what the function may
change), the prologue, and the alignment of the three shifted values to the
first height (`align`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Levels

open VG VG.AArch64 VG.AArch64.Steps VG.Proof.SlhDsa.AArch64.Blocks VG.Proof.SlhDsa.AArch64.Wots4
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64

/-! ## The layout, as numbers -/

theorem oSave3_eq (i : Nat) : Layout.oSave 3 i = 1408 + 8 * i := rfl
theorem oVar3_eq (i : Nat) : Layout.oVar 3 i = 1496 + 8 * i := rfl
theorem oFrame3_eq : Layout.oFrame 3 = 1408 := rfl
theorem var_eq (i : Nat) : Tree.var i = 1496 + 8 * i := rfl

/-! ## The entry state -/

variable (p : Params)

/-- What the proof uses of the entry state `σ`: `scratch` `S`, the
authentication path `AU`, `idx`, the number `c = 2^h` of nodes, the first
height `z₀`, and the parameters of frame 3. -/
structure Entry (σ : State) (S AU : Addr) (idx c h z₀ : Nat) (pkSeed a16 : List Byte) : Prop where
  x0 : σ.gpr .x0 = S
  x1 : σ.gpr .x1 = at' S Layout.oN
  x2 : σ.gpr .x2 = BitVec.ofNat 64 c
  x3 : σ.gpr .x3 = BitVec.ofNat 64 z₀
  x4 : σ.gpr .x4 = AU
  x5 : σ.gpr .x5 = BitVec.ofNat 64 idx
  reg : Regions σ S [] ⟨AU, h * p.n⟩
  env : Env p σ.mem S pkSeed a16
  h_pos : 1 ≤ h
  h_le : z₀ + h ≤ 14
  cnt : c = 2 ^ h
  cap : (c + 8) * p.n ≤ 32 * Layout.nodeSlots
  idx32 : idx < 2 ^ 32
  v0 : (varAt σ.mem S 3 0).toNat < 2 ^ 32
  v1 : (varAt σ.mem S 3 1).toNat < 2 ^ 32
  v2 : (varAt σ.mem S 3 2).toNat < 2 ^ 32
  v3 : (varAt σ.mem S 3 3).toNat < 2 ^ 32

/-- What `levels` may change: the contract's, and the path. -/
abbrev lch (S AU : Addr) (c h : Nat) : List Region :=
  levelsChanges p S (at' S Layout.oN) c ++ [⟨AU, h * p.n⟩]

variable {p} {σ : State} {S AU : Addr} {idx c h z₀ : Nat} {pkSeed a16 : List Byte}

/-- What holds at every point of the code, from the entry state `σ`. -/
structure Base (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  x19 : s.gpr .x19 = S
  x20 : s.gpr .x20 = at' S Layout.oN
  x28 : s.gpr .x28 = σ.gpr .x28
  saved : ∀ i < 10, s.mem.readW (at' S (Layout.oSave 3 i)) 64 = σ.gpr (Tree.saved.getD i .x19)
  vars : ∀ i < 4, s.mem.readW (at' S (Layout.oVar 3 i)) 64 = σ.mem.readW (at' S (Layout.oVar 3 i)) 64
  frame : Frame (lch p S AU c h) σ.mem s.mem

namespace Entry

variable (hE : Entry p σ S AU idx c h z₀ pkSeed a16)
include hE

theorem scr_mem {s : State} (hw : s.wr = σ.wr) : (⟨S, 65536⟩ : Region) ∈ s.wr := by
  rw [hw, hE.reg.wr_eq]; exact List.mem_cons_self ..

/-- A range of `scratch` is writable. -/
theorem inScr {s : State} (hw : s.wr = σ.wr) {o n : Nat} (h : o + n ≤ 65536) : InRegions s.wr (at' S o) n :=
  ⟨⟨S, 65536⟩, hE.scr_mem hw, Offset.contains_base S h (by
    have := hE.reg.scr_fit; simp only [scratchLen] at this; omega_using [this, h])⟩

theorem inScr' {s : State} (hw : s.wr = σ.wr) {o n : Nat} (h : o + n ≤ 65536) :
    InRegions (s.rd ++ s.wr) (at' S o) n := by
  obtain ⟨r, hr', hc⟩ := hE.inScr hw h
  exact ⟨r, List.mem_append_right _ hr', hc⟩

theorem scr_fit : S.toNat + 65536 ≤ 2 ^ 64 := by have := hE.reg.scr_fit; simpa [scratchLen] using this

/-- A range of the path is writable. -/
theorem inAU {s : State} (hw : s.wr = σ.wr) {o n : Nat} (hl : o + n ≤ h * p.n) (hn : 0 < n) :
    InRegions s.wr (AU + BitVec.ofNat 64 o) n :=
  ⟨⟨AU, h * p.n⟩, by rw [hw, hE.reg.wr_eq]; simp, Offset.contains_base AU hl (by
    have hf := hE.reg.out_fit; simp only at hf; omega_using [hf, hl, hn])⟩

/-- A range of the path and one of `scratch` below `oSigTmp`. -/
theorem dAU {o l a m : Nat} (hl : o + l ≤ h * p.n) (ha : a + m ≤ Layout.oSigTmp) :
    Region.Disjoint ⟨AU + BitVec.ofNat 64 o, l⟩ ⟨at' S a, m⟩ :=
  (hE.reg.out_scr.sub_left (Offset.sub_base AU hl)).sub_right (Offset.sub_base S ha)

theorem c_le (hz : Sz p) : c ≤ 2 ^ 13 := by
  have := hE.cap; rw [nodeSlots_eq] at this
  have h16 : (c + 8) * 16 ≤ (c + 8) * p.n := Nat.mul_le_mul_left _ hz.n16
  have hc := hE.cnt
  omega_using [this, h16, hc]

theorem nodes_fit : Layout.oN + (c + 8) * p.n ≤ 29120 := by
  have := hE.cap; rw [nodeSlots_eq] at this; rw [oN_eq]; omega_using [this]

end Entry

/-! ## `Base`, through writes -/

/-- The callee-saved registers `levels` keeps fixed. -/
abbrev LR : List Reg := [.x19, .x20, .x28]

theorem lr_mem {r : Reg} (h : r ∈ LR) : r = .x19 ∨ r = .x20 ∨ r = .x28 := by
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using h

/-- The saved registers and the parameters, in frame 3. -/
abbrev frameR (S : Addr) : Region := ⟨at' S 1408, 128⟩

theorem Base.regs {hE : Entry p σ S AU idx c h z₀ pkSeed a16} {t t' : State} (hb : Base hE t)
    (hm : t'.mem = t.mem) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hg : ∀ r ∈ LR, t'.gpr r = t.gpr r) : Base hE t' :=
  ⟨by rw [hrd, hb.rd], by rw [hwr, hb.wr], by rw [hsp, hb.sp], by rw [hg _ (by simp), hb.x19],
    by rw [hg _ (by simp), hb.x20], by rw [hg _ (by simp), hb.x28],
    fun i hi => by rw [hm, hb.saved i hi], fun i hi => by rw [hm, hb.vars i hi], by rw [hm]; exact hb.frame⟩

/-- `Base` through a change of memory in ranges of `lch` away from frame 3. -/
theorem Base.ofFrame {hE : Entry p σ S AU idx c h z₀ pkSeed a16} {t t' : State} (hb : Base hE t)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hg : ∀ r ∈ LR, t'.gpr r = t.gpr r)
    {rs : List Region} (hf : Frame rs t.mem t'.mem) (hs : ∀ r ∈ rs, ∃ R ∈ lch p S AU c h, Region.Sub r R)
    (hsv : ∀ r ∈ rs, Region.Disjoint (frameR S) r) : Base hE t' :=
  ⟨by rw [hrd, hb.rd], by rw [hwr, hb.wr], by rw [hsp, hb.sp], by rw [hg _ (by simp), hb.x19],
    by rw [hg _ (by simp), hb.x20], by rw [hg _ (by simp), hb.x28],
    fun i hi => by
      rw [hf.readW (r := ⟨at' S (Layout.oSave 3 i), 8⟩) (by simp [Region.Contains])
        (fun r hr => (hsv r hr).sub_left (by
          rw [oSave3_eq]; exact Offset.sub S (by omega_using []) (by omega_using [hi]))) (by decide), hb.saved i hi],
    fun i hi => by
      rw [hf.readW (r := ⟨at' S (Layout.oVar 3 i), 8⟩) (by simp [Region.Contains])
        (fun r hr => (hsv r hr).sub_left (by
          rw [oVar3_eq]; exact Offset.sub S (by omega_using []) (by omega_using [hi]))) (by decide), hb.vars i hi],
    hb.frame.trans (hf.sub hs)⟩

/-! ## The prologue -/

/-- The parameters of frame 3, at entry. -/
abbrev capB (σ : State) (S : Addr) : Nat := (varAt σ.mem S 3 0).toNat
abbrev baseA (σ : State) (S : Addr) : Nat := (varAt σ.mem S 3 1).toNat
abbrev tyA (σ : State) (S : Addr) : Nat := (varAt σ.mem S 3 2).toNat
abbrev kpA (σ : State) (S : Addr) : Nat := (varAt σ.mem S 3 3).toNat

theorem shr1 {x : Nat} (hx : x < 2 ^ 64) : BitVec.ofNat 64 x >>> 1 = BitVec.ofNat 64 (x / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega_using [hx])]

theorem div_pow_succ (x m : Nat) : x / 2 ^ m / 2 = x / 2 ^ (m + 1) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

/-- The shifted values at the `m`-th step of the alignment, and the other
registers of the prologue. -/
structure SH (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (m : Nat) (t : State) : Prop where
  base : Base hE t
  vk : VK t σ
  x21 : t.gpr .x21 = AU
  x22 : t.gpr .x22 = BitVec.ofNat 64 z₀
  x23 : t.gpr .x23 = BitVec.ofNat 64 c
  x25 : t.gpr .x25 = BitVec.ofNat 64 (idx / 2 ^ m)
  x26 : t.gpr .x26 = BitVec.ofNat 64 (capB σ S / 2 ^ m)
  x27 : t.gpr .x27 = BitVec.ofNat 64 (baseA σ S / 2 ^ (m + 1))
  fr : Frame [frameR S] σ.mem t.mem

theorem saveRegs_eq3 : saveRegs 3 .x0 Tree.saved =
    (List.range 10).map fun i => .str .x (Tree.saved.getD i .x19) .x0 (Layout.oSave 3 0 + 8 * i) := rfl

theorem pro_eq : Tree.pro = saveRegs 3 .x0 Tree.saved ++
    ([.addImm .x .x19 .x0 0, .addImm .x .x20 .x1 0, .addImm .x .x23 .x2 0, .addImm .x .x22 .x3 0,
      .addImm .x .x21 .x4 0, .addImm .x .x25 .x5 0, .ldr .x .x26 .x19 1496, .ldr .x .x27 .x19 1504,
      .lsr .x .x27 .x27 1] : List Instr) := rfl

theorem varAt_ofNat (m : Mem) (S : Addr) (f i : Nat) : m.readW (at' S (Layout.oVar f i)) 64 =
    BitVec.ofNat 64 (varAt m S f i).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl

theorem pro_ok (hE : Entry p σ S AU idx c h z₀ pkSeed a16) : WP isa (.block Tree.pro) σ (SH hE 0) := by
  rw [pro_eq]
  refine wp_vk rfl ?_
  refine WP.block_append (WP.mono (?_ : WP isa (.block (saveRegs 3 .x0 Tree.saved)) σ fun t =>
    t.gpr = σ.gpr ∧ t.sp = σ.sp ∧ t.rd = σ.rd ∧ t.wr = σ.wr ∧
      (∀ i < 10, t.mem.readW (at' S (Layout.oSave 3 i)) 64 = σ.gpr (Tree.saved.getD i .x19)) ∧
      Frame [⟨at' S 1408, 80⟩] σ.mem t.mem) fun t ht => ?_)
  · rw [saveRegs_eq3]
    refine wp_range_map 10 (P := fun j t => t.gpr = σ.gpr ∧ t.sp = σ.sp ∧ t.rd = σ.rd ∧ t.wr = σ.wr ∧
      (∀ i < j, t.mem.readW (at' S (Layout.oSave 3 i)) 64 = σ.gpr (Tree.saved.getD i .x19)) ∧
      Frame [⟨at' S 1408, 80⟩] σ.mem t.mem)
      ⟨rfl, rfl, rfl, rfl, fun i hi => absurd hi (by omega_using []), Frame.refl _ _⟩ fun j hj t ht => ?_
    refine wp_str (a := at' S (Layout.oSave 3 j)) ⟨by rw [oSave3_eq]; omega_using [], by rw [oSave3_eq]; omega_using [hj]⟩
      (by rw [ht.1, hE.x0, oSave3_eq, oSave3_eq])
      (hE.inScr ht.2.2.2.1 (by rw [oSave3_eq]; omega_using [hj])) fun t' u => WP.block_nil ?_
    obtain ⟨hg, hsp, hrd, hwr, hsv, hf⟩ := ht
    refine ⟨by rw [u.gpr, hg], by rw [u.sp, hsp], by rw [u.rd, hrd], by rw [u.wr, hwr], fun i hi => ?_, ?_⟩
    · rw [u.mem]
      by_cases e : i = j
      · subst e; rw [Mem.readW_writeW_self64, hg]
      · rw [Mem.readW_writeW_sep (Offset.sep S (by rw [oSave3_eq, oSave3_eq]; omega_using [e, hi, hj])
          (by rw [oSave3_eq]; omega_using [hi, hj]) (by rw [oSave3_eq]; omega_using [hj])) (by decide),
          hsv i (by omega_using [hi, e])]
    · rw [u.mem]
      refine hf.writeW (List.mem_singleton_self _) _ ?_
      rw [oSave3_eq]
      exact Offset.contains S (by omega_using []) (by omega_using [hj]) (by omega_using [hj])
  obtain ⟨hg, hsp, hrd, hwr, hsv, hf⟩ := ht
  have hfit := hE.scr_fit
  refine wp_addImm (by decide) fun t₁ u₁ => wp_addImm (by decide) fun t₂ u₂ => wp_addImm (by decide) fun t₃ u₃ =>
    wp_addImm (by decide) fun t₄ u₄ => wp_addImm (by decide) fun t₅ u₅ => wp_addImm (by decide) fun t₆ u₆ => ?_
  have h19 : t₆.gpr .x19 = S := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, hg, hE.x0, add0]
  have hm₆ : t₆.mem = t.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hfr : Frame (lch p S AU c h) σ.mem t.mem := hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨at' S (Layout.oFrame 3), Layout.frameLen⟩, by simp [lch, levelsChanges],
      by rw [oFrame3_eq, frameLen_eq]; exact Region.sub_prefix (by decide)⟩
  have hvars : ∀ i < 4, t.mem.readW (at' S (Layout.oVar 3 i)) 64 = σ.mem.readW (at' S (Layout.oVar 3 i)) 64 :=
    fun i hi => hf.readW (r := ⟨at' S (Layout.oVar 3 i), 8⟩) (by simp [Region.Contains])
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Entry.dscr (Or.inr (by rw [oVar3_eq]; omega_using [])) (by rw [oVar3_eq]; omega_using [hi]) (by decide))
      (by decide)
  refine wp_ldr (a := at' S (Layout.oVar 3 0)) ⟨by decide, by decide⟩ (by rw [h19]; rfl)
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrd, hwr]
        exact hE.inScr' rfl (by rw [oVar3_eq]; omega_using [])) fun t₇ u₇ => ?_
  refine wp_ldr (a := at' S (Layout.oVar 3 1)) ⟨by decide, by decide⟩ (by rw [u₇.other _ (by decide), h19]; rfl)
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrd, hwr]
        exact hE.inScr' rfl (by rw [oVar3_eq]; omega_using [])) fun t₈ u₈ => ?_
  refine wp_lsr (by decide) fun t₉ u₉ => WP.block_nil fun hvk => ?_
  have hm₉ : t₉.mem = t.mem := by rw [u₉.mem, u₈.mem, u₇.mem, hm₆]
  have g6 : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x23 → r ≠ .x22 → r ≠ .x21 → r ≠ .x25 → t₆.gpr r = σ.gpr r :=
    fun r a b c d e f => by
      rw [u₆.other _ f, u₅.other _ e, u₄.other _ d, u₃.other _ c, u₂.other _ b, u₁.other _ a, hg]
  have keep : ∀ r, r ≠ .x26 → r ≠ .x27 → t₉.gpr r = t₆.gpr r := fun r a b => by
    rw [u₉.other _ b, u₈.other _ b, u₇.other _ a]
  refine ⟨⟨by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hrd],
      by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hwr],
      by rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hsp],
      by rw [keep _ (by decide) (by decide), h19],
      by rw [keep _ (by decide) (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hg, hE.x1, add0],
      by rw [keep _ (by decide) (by decide), g6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)],
      fun i hi => by rw [hm₉, hsv i hi], fun i hi => by rw [hm₉, hvars i hi], by rw [hm₉]; exact hfr⟩,
    hvk,
    by rw [keep _ (by decide) (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg, hE.x4, add0],
    by rw [keep _ (by decide) (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg, hE.x3, add0],
    by rw [keep _ (by decide) (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hg, hE.x2, add0],
    by rw [keep _ (by decide) (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg, hE.x5, add0, Nat.pow_zero,
      Nat.div_one], ?_, ?_, ?_⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, hm₆, hvars 0 (by decide), varAt_ofNat,
      Nat.pow_zero, Nat.div_one]
  · rw [u₉.gpr, u₈.gpr, u₇.mem, hm₆, hvars 1 (by decide), varAt_ofNat, shr1 (BitVec.isLt _), Nat.zero_add,
      Nat.pow_one]
  · rw [hm₉]
    exact hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩

/-! ## The alignment to the first height -/

theorem eval_z {s : State} {r : Reg} {a : Nat} (h : s.gpr r = BitVec.ofNat 64 a) (ha : a < 2 ^ 64) :
    isa.eval (.zero .x r) s = some (decide (a = 0)) := by
  show some ((s.gpr r).setWidth 64 == 0) = _
  rw [BitVec.setWidth_eq, h]
  by_cases e : a = 0
  · subst e; rfl
  · rw [decide_eq_false e]
    have : BitVec.ofNat 64 a ≠ 0 := fun h' => e (by
      have := congrArg BitVec.toNat h'; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at this)
    simpa using this

theorem align_ok (hE : Entry p σ S AU idx c h z₀ pkSeed a16) {t : State} (ht : SH hE 0 t) :
    WP isa Tree.align t (SH hE z₀) := by
  have hz : z₀ < 15 := by have := hE.h_le; omega_using [this]
  refine WP.ite (decide (z₀ = 0)) (eval_z ht.x22 (by omega_using [hz])) (fun e => ?_) (fun e => ?_)
  · have : z₀ = 0 := of_decide_eq_true e
    subst this; exact WP.block_nil ht
  · have hz0 : z₀ ≠ 0 := of_decide_eq_false e
    refine WP.seq (wp_vk rfl (wp_addImm (by decide) fun t₁ u₁ => WP.block_nil fun hv₁ => ?_))
    have hb₁ : Base hE t₁ := ht.base.regs u₁.mem u₁.rd u₁.wr u₁.sp fun r hr => u₁.other _ (by
      rcases lr_mem hr with rfl | rfl | rfl <;> decide)
    refine WP.loop (M := isa) (Inv := fun n (u : State) => 1 ≤ n ∧ n ≤ z₀ ∧ SH hE (z₀ - n) u ∧ u.gpr .x9 = BitVec.ofNat 64 n)
      (fun n u hI => ?_) z₀ t₁ ⟨by omega_using [hz0], Nat.le_refl _, ?_, ?_⟩
    rotate_left
    · rw [Nat.sub_self]
      exact ⟨hb₁, VK.trans hv₁ ht.vk, by rw [u₁.other _ (by decide), ht.x21],
        by rw [u₁.other _ (by decide), ht.x22], by rw [u₁.other _ (by decide), ht.x23],
        by rw [u₁.other _ (by decide), ht.x25], by rw [u₁.other _ (by decide), ht.x26],
        by rw [u₁.other _ (by decide), ht.x27], by rw [u₁.mem]; exact ht.fr⟩
    · rw [u₁.gpr, ht.x22, add0]
    obtain ⟨h₁, h₂, hu, h9⟩ := hI
    refine wp_vk rfl ?_
    refine wp_lsr (by decide) fun v₁ w₁ => wp_lsr (by decide) fun v₂ w₂ => wp_lsr (by decide) fun v₃ w₃ =>
      wp_subImm (by decide) fun v₄ w₄ => WP.block_nil fun hvk => ?_
    have hb : Base hE v₄ := hu.base.regs (by rw [w₄.mem, w₃.mem, w₂.mem, w₁.mem]) (by rw [w₄.rd, w₃.rd, w₂.rd, w₁.rd])
      (by rw [w₄.wr, w₃.wr, w₂.wr, w₁.wr]) (by rw [w₄.sp, w₃.sp, w₂.sp, w₁.sp]) fun r hr => by
        rcases lr_mem hr with rfl | rfl | rfl <;>
          rw [w₄.other _ (by decide), w₃.other _ (by decide), w₂.other _ (by decide), w₁.other _ (by decide)]
    have hm : z₀ - n + 1 = z₀ - (n - 1) := by omega_using [h₁, h₂]
    have hidx := hE.idx32
    have hcap : capB σ S < 2 ^ 32 := hE.v0
    have hbase : baseA σ S < 2 ^ 32 := hE.v1
    have hs : SH hE (z₀ - (n - 1)) v₄ := ⟨hb, VK.trans hvk hu.vk,
      by rw [w₄.other _ (by decide), w₃.other _ (by decide), w₂.other _ (by decide), w₁.other _ (by decide), hu.x21],
      by rw [w₄.other _ (by decide), w₃.other _ (by decide), w₂.other _ (by decide), w₁.other _ (by decide), hu.x22],
      by rw [w₄.other _ (by decide), w₃.other _ (by decide), w₂.other _ (by decide), w₁.other _ (by decide), hu.x23],
      by rw [w₄.other _ (by decide), w₃.other _ (by decide), w₂.other _ (by decide), w₁.gpr, hu.x25,
        shr1 (by have := Nat.div_le_self idx (2 ^ (z₀ - n)); omega_using [this, hidx]), div_pow_succ, hm],
      by rw [w₄.other _ (by decide), w₃.other _ (by decide), w₂.gpr, w₁.other _ (by decide), hu.x26,
        shr1 (by have := Nat.div_le_self (capB σ S) (2 ^ (z₀ - n)); omega_using [this, hcap]), div_pow_succ, hm],
      by rw [w₄.other _ (by decide), w₃.gpr, w₂.other _ (by decide), w₁.other _ (by decide), hu.x27,
        shr1 (by have := Nat.div_le_self (baseA σ S) (2 ^ (z₀ - n + 1)); omega_using [this, hbase]), div_pow_succ, hm],
      by rw [w₄.mem, w₃.mem, w₂.mem, w₁.mem]; exact hu.fr⟩
    have h9' : v₄.gpr .x9 = BitVec.ofNat 64 n - BitVec.ofNat 64 1 := by
      rw [w₄.gpr, w₃.other _ (by decide), w₂.other _ (by decide), w₁.other _ (by decide), h9]
    have ev := eval_nz h9' (by omega_using [h₂, hz]) (by decide)
    by_cases e1 : n = 1
    · subst e1
      exact Or.inl ⟨by rw [ev]; rfl, by simpa using hs⟩
    · refine Or.inr ⟨by rw [ev, decide_eq_false e1]; rfl, n - 1, by omega_using [h₁], by omega_using [h₁, e1],
        by omega_using [h₂], hs, ?_⟩
      rw [h9']
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_using [h₁, h₂, hz]

end VG.Proof.SlhDsa.AArch64.Levels
