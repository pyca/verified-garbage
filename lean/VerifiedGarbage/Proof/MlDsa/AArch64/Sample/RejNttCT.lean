import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Common
import VerifiedGarbage.Proof.MlKem.AArch64.Sample
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd2
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Proof.MlDsa.Sample.Signs
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge`. -/
section

/-!
# ML-DSA on AArch64: the sampling functions' SHAKE

What the sampling functions share (`Impl/MlDsa/AArch64/Sample/Common.lean`),
for any of them: a call is described by `Sp` (the message, its length, the
working space, the output polynomial and the parameter kept in `x27`), whose
regions are laid out as `SpOk` says. From the prologue on, `Env` holds: the
registers of the layout, the caller's callee-saved registers (in their
registers or saved in the working space), and the memory changed only in the
output, the working space and the stack below `sp`. `sponge` then leaves
`outlen` bytes of SHAKE of the message at `scratch + 840` (`sponge_ok`);
`epi_ok` restores the registers.
-/

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo Kept wp_nil wp_mov wp_movz wp_addImm wp_subImm wp_strx
  wp_ldrx wp_strw wp_x only_write write_x_gpr ptr_add ptr_zero sep_off contains_off in_regions
  in_rd_wr in_rd toNat_imm toNat_sub_n absorb_callWith pad_callWith squeeze_callWith stk count_loop)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)
open VG.Proof.MlDsa.Sample (padded coeffAddr polyR coeff_contains)
open VG.Spec.Sha3 (bytesAt stateAt Repr rates shakeSuffix)

/-- A call of a sampling function. -/
structure Sp where
  /-- The message hashed. -/
  sd : Addr
  len : Nat
  /-- `scratch`. -/
  scr : Addr
  /-- The output polynomial. -/
  a : Addr
  /-- The parameter, in `x27`. -/
  prm : BitVec 64

namespace Sp
variable (P : VG.Proof.MlDsa.AArch64.Sample.Sp)
/-- `scratch + off`. -/
abbrev at' (off : Nat) : Addr := P.scr + BitVec.ofNat 64 off
abbrev scrR : Region := ⟨P.scr, 2048⟩
abbrev sdR : Region := ⟨P.sd, P.len⟩
/-- The message. -/
abbrev msg (σ : State) : List Byte := bytesAt σ.mem P.sd P.len
end Sp

/-- The regions of a call from the entry state `σ`. -/
structure SpOk (P : VG.Proof.MlDsa.AArch64.Sample.Sp) (σ : State) : Prop where
  rd : σ.rd = [P.sdR]
  wr : σ.wr = [polyR P.a, P.scrR]
  sd_a : P.sdR.Disjoint (polyR P.a)
  sd_scr : P.sdR.Disjoint P.scrR
  a_scr : (polyR P.a).Disjoint P.scrR
  sp16 : 16 ≤ σ.sp.toNat
  stk_sd : (below σ.sp 16).Disjoint P.sdR
  stk_a : (below σ.sp 16).Disjoint (polyR P.a)
  stk_scr : (below σ.sp 16).Disjoint P.scrR
  len_lt : P.len < 2 ^ 64

/-- What holds from the prologue on, relative to the entry state `σ`. -/
structure Env (P : VG.Proof.MlDsa.AArch64.Sample.Sp) (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  x25 : s.gpr .x25 = P.scr
  x26 : s.gpr .x26 = P.a
  x27 : s.gpr .x27 = P.prm
  cs : ∀ r ∈ preserved, r ≠ .x25 → r ≠ .x26 → r ≠ .x27 → r ≠ .x30 → s.gpr r = σ.gpr r
  saved : s.mem.readW (P.at' 2016) 64 = σ.gpr .x25 ∧ s.mem.readW (P.at' 2024) 64 = σ.gpr .x26 ∧
    s.mem.readW (P.at' 2032) 64 = σ.gpr .x27 ∧ s.mem.readW (P.at' 2040) 64 = σ.gpr .x30
  frame : Frame [polyR P.a, P.scrR, below σ.sp 16] σ.mem s.mem
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (σ.v r).extractLsb' 0 64

theorem mem2 {α : Type} {a b x : α} (h : x ∈ [a, b]) : x = a ∨ x = b := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (List.mem_singleton.mp h)

theorem mem3 {α : Type} {a b c x : α} (h : x ∈ [a, b, c]) : x = a ∨ x = b ∨ x = c := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (VG.Proof.MlDsa.AArch64.Sample.mem2 h)

theorem mem4 {α : Type} {a b c d x : α} (h : x ∈ [a, b, c, d]) : x = a ∨ x = b ∨ x = c ∨ x = d := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (VG.Proof.MlDsa.AArch64.Sample.mem3 h)

/-! ## Regions -/

section
variable {P : VG.Proof.MlDsa.AArch64.Sample.Sp}

theorem sub_scr {a n : Nat} (h : a + n ≤ 2048) : Region.Sub ⟨P.at' a, n⟩ P.scrR := Offset.sub_base _ h

theorem sub_scr0 {n : Nat} (h : n ≤ 2048) : Region.Sub ⟨P.scr, n⟩ P.scrR := Region.sub_prefix h

theorem disj_scr {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ 2048) (hb : b + m ≤ 2048) :
    Region.Disjoint ⟨P.at' a, n⟩ ⟨P.at' b, m⟩ := Offset.disjoint _ h (by omega) (by omega)

theorem contains_scr {a n : Nat} (h : a + n ≤ 2048) : P.scrR.Contains (P.at' a) n :=
  Offset.contains_base _ h (by omega)

theorem at_zero : P.at' 0 = P.scr := ptr_zero _

theorem at_add (a b : Nat) : P.at' a + BitVec.ofNat 64 b = P.at' (a + b) := ptr_add _ _ _

variable {σ : State} (hp : VG.Proof.MlDsa.AArch64.Sample.SpOk P σ)
include hp

theorem sd_scr' {a n : Nat} (h : a + n ≤ 2048) : P.sdR.Disjoint ⟨P.at' a, n⟩ :=
  hp.sd_scr.sub_right (VG.Proof.MlDsa.AArch64.Sample.sub_scr h)

theorem stk_scr' {a n : Nat} (h : a + n ≤ 2048) : (below σ.sp 16).Disjoint ⟨P.at' a, n⟩ :=
  hp.stk_scr.sub_right (VG.Proof.MlDsa.AArch64.Sample.sub_scr h)

theorem a_scr' {a n : Nat} (h : a + n ≤ 2048) : (polyR P.a).Disjoint ⟨P.at' a, n⟩ :=
  hp.a_scr.sub_right (VG.Proof.MlDsa.AArch64.Sample.sub_scr h)

/-- The regions, from the prologue on. -/
theorem regions {s : State} (he : VG.Proof.MlDsa.AArch64.Sample.Env P σ s) : s.rd ++ s.wr = [P.sdR, polyR P.a, P.scrR] := by
  rw [he.rd, he.wr, hp.rd, hp.wr]; rfl

theorem inScr {s : State} (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 2048) :
    InRegions s.wr (P.at' a) n := by
  rw [hw, hp.wr]
  exact in_regions (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (VG.Proof.MlDsa.AArch64.Sample.contains_scr h)

theorem inScrRd {s : State} (hr : s.rd = σ.rd) (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 2048) :
    InRegions (s.rd ++ s.wr) (P.at' a) n := by
  rw [hr]; exact in_rd_wr (VG.Proof.MlDsa.AArch64.Sample.inScr hp hw h)

theorem inA {s : State} (hw : s.wr = σ.wr) {i : Nat} (hi : i < 256) :
    InRegions s.wr (coeffAddr P.a i) 4 := by
  rw [hw, hp.wr]
  exact in_regions (List.mem_cons_self ..) (coeff_contains _ hi)

theorem cov_scr {s : State} (hw : s.wr = σ.wr) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ off, r.base = P.at' off ∧ off + r.len ≤ 2048) : Covers rs s.wr :=
  Covers.of_sub fun r hr => by
    obtain ⟨off, hb, hl⟩ := h r hr
    exact ⟨P.scrR, by rw [hw, hp.wr]; simp, off, hb, hl⟩

omit hp in
theorem cov_rd {s : State} {rs : List Region} (h : Covers rs s.wr) : Covers rs (s.rd ++ s.wr) :=
  fun a n hi => in_rd_wr (h a n hi)

/-- The message is not written. -/
theorem sd_frame {m : Mem} (hf : Frame [polyR P.a, P.scrR, below σ.sp 16] σ.mem m) :
    bytesAt m P.sd P.len = P.msg σ :=
  MlKem.bytesAt_frame hf (fun r hr => by
    rcases VG.Proof.MlDsa.AArch64.Sample.mem3 hr with rfl | rfl | rfl
    exacts [hp.sd_a, hp.sd_scr, hp.stk_sd.symm]) (Nat.le_of_lt hp.len_lt)

omit hp in
/-- The saved registers are apart from the parts of `scratch` below them. -/
theorem sv_disj {off n : Nat} (h : off + n ≤ 2016) :
    Region.Disjoint ⟨P.at' 2016, 32⟩ ⟨P.at' off, n⟩ := VG.Proof.MlDsa.AArch64.Sample.disj_scr (.inr h) (by omega) (by omega)

omit hp in
theorem sv_frame {m m' : Mem} (h : m.readW (P.at' 2016) 64 = σ.gpr .x25 ∧ m.readW (P.at' 2024) 64 = σ.gpr .x26 ∧
      m.readW (P.at' 2032) 64 = σ.gpr .x27 ∧ m.readW (P.at' 2040) 64 = σ.gpr .x30)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨P.at' 2016, 32⟩ r) :
    m'.readW (P.at' 2016) 64 = σ.gpr .x25 ∧ m'.readW (P.at' 2024) 64 = σ.gpr .x26 ∧
      m'.readW (P.at' 2032) 64 = σ.gpr .x27 ∧ m'.readW (P.at' 2040) 64 = σ.gpr .x30 := by
  have e : ∀ k, k < 4 → m'.readW (P.at' (2016 + 8 * k)) 64 = m.readW (P.at' (2016 + 8 * k)) 64 :=
    fun k hk => by
      refine hf.readW (r := ⟨P.at' 2016, 32⟩) ?_ hd (by decide)
      rw [← VG.Proof.MlDsa.AArch64.Sample.at_add]
      exact contains_off (by omega) (by decide)
  exact ⟨(e 0 (by decide)).trans h.1, (e 1 (by decide)).trans h.2.1, (e 2 (by decide)).trans h.2.2.1,
    (e 3 (by decide)).trans h.2.2.2⟩

/-- A call that writes parts of `scratch` below the saved registers, and the
stack below `sp`, keeps `Env`. -/
theorem Env.call {s s' : State} (he : VG.Proof.MlDsa.AArch64.Sample.Env P σ s) {rs : List Region} (hk : Kept rs s s')
    (hrs : ∀ r ∈ rs, (∃ off n, r = ⟨P.at' off, n⟩ ∧ off + n ≤ 2016) ∨ r = below s.sp 16) :
    VG.Proof.MlDsa.AArch64.Sample.Env P σ s' := by
  have hd : ∀ r ∈ rs, Region.Disjoint ⟨P.at' 2016, 32⟩ r := fun r hr => by
    rcases hrs r hr with ⟨off, n, rfl, h⟩ | rfl
    · exact VG.Proof.MlDsa.AArch64.Sample.sv_disj h
    · rw [he.sp]; exact (VG.Proof.MlDsa.AArch64.Sample.stk_scr' hp (a := 2016) (n := 32) (by omega)).symm
  refine ⟨by rw [hk.rd, he.rd], by rw [hk.wr, he.wr], by rw [hk.sp, he.sp],
    by rw [hk.cs _ (by decide) (by decide), he.x25], by rw [hk.cs _ (by decide) (by decide), he.x26],
    by rw [hk.cs _ (by decide) (by decide), he.x27],
    fun r hr h25 h26 h27 h30 => by rw [hk.cs r hr h30, he.cs r hr h25 h26 h27 h30],
    VG.Proof.MlDsa.AArch64.Sample.sv_frame he.saved hk.frame hd, he.frame.trans (hk.frame.sub fun r hr => ?_), fun r hr => (hk.vcs r hr).trans (he.vcs r hr)⟩
  rcases hrs r hr with ⟨off, n, rfl, h⟩ | rfl
  · exact ⟨P.scrR, by simp, VG.Proof.MlDsa.AArch64.Sample.sub_scr (by omega)⟩
  · exact ⟨below σ.sp 16, by simp, by rw [he.sp]; exact fun _ h => h⟩

/-- Code that writes only registers that are not callee-saved, and the
output polynomial, keeps `Env`. -/
theorem Env.keepA {s s' : State} (he : VG.Proof.MlDsa.AArch64.Sample.Env P σ s) {regs : List Reg} (hk : Keep regs s s')
    (hf : Frame [polyR P.a] s.mem s'.mem) (hr : ∀ r ∈ regs, r ∉ preserved := by decide) :
    VG.Proof.MlDsa.AArch64.Sample.Env P σ s' :=
  ⟨by rw [hk.rd, he.rd], by rw [hk.wr, he.wr], by rw [hk.sp, he.sp],
    by rw [hk.get .x25 (fun h' => hr _ h' (by decide)), he.x25],
    by rw [hk.get .x26 (fun h' => hr _ h' (by decide)), he.x26],
    by rw [hk.get .x27 (fun h' => hr _ h' (by decide)), he.x27],
    fun r hp' h25 h26 h27 h30 => by rw [hk.get r (fun h' => hr _ h' hp'), he.cs r hp' h25 h26 h27 h30],
    VG.Proof.MlDsa.AArch64.Sample.sv_frame he.saved hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (VG.Proof.MlDsa.AArch64.Sample.a_scr' hp (a := 2016) (n := 32) (by omega)).symm),
    he.frame.trans (hf.mono (by simp)), fun r hr => (hk.vcs r hr).trans (he.vcs r hr)⟩

end

/-- Code that writes only registers that are not callee-saved keeps `Env`. -/
theorem Env.keep {P : VG.Proof.MlDsa.AArch64.Sample.Sp} {σ s s' : State} (he : VG.Proof.MlDsa.AArch64.Sample.Env P σ s) {regs : List Reg} (hk : Keep regs s s')
    (hm : s'.mem = s.mem) (hr : ∀ r ∈ regs, r ∉ preserved := by decide) : VG.Proof.MlDsa.AArch64.Sample.Env P σ s' :=
  ⟨by rw [hk.rd, he.rd], by rw [hk.wr, he.wr], by rw [hk.sp, he.sp],
    by rw [hk.get .x25 (fun h' => hr _ h' (by decide)), he.x25],
    by rw [hk.get .x26 (fun h' => hr _ h' (by decide)), he.x26],
    by rw [hk.get .x27 (fun h' => hr _ h' (by decide)), he.x27],
    fun r hp' h25 h26 h27 h30 => by rw [hk.get r (fun h' => hr _ h' hp'), he.cs r hp' h25 h26 h27 h30],
    by rw [hm]; exact he.saved, by rw [hm]; exact he.frame, fun r hr => (hk.vcs r hr).trans (he.vcs r hr)⟩

/-! ## The prologue -/

/-- The entry of `sponge`: the message in `x3` and its length in `x4`. -/
structure J0 (P : VG.Proof.MlDsa.AArch64.Sample.Sp) (σ s : State) : Prop where
  env : VG.Proof.MlDsa.AArch64.Sample.Env P σ s
  x3 : s.gpr .x3 = P.sd
  x4 : (s.gpr .x4).toNat = P.len

/-- The prologue, for any instructions that set the parameter and the
length. -/
theorem pro_ok {P : VG.Proof.MlDsa.AArch64.Sample.Sp} {σ : State} (hp : VG.Proof.MlDsa.AArch64.Sample.SpOk P σ) {scr a : Reg} {prm len : Instr}
    (hscr : σ.gpr scr = P.scr) (ha : σ.gpr a = P.a) (ha25 : a ≠ .x25) (hsd : σ.gpr .x0 = P.sd)
    (hprm : ∀ s : State, (∀ r, r ≠ .x25 → r ≠ .x26 → s.gpr r = σ.gpr r) →
      ∃ s', exec prm s = some s' ∧ Only [.x27] s s' ∧ s'.gpr .x27 = P.prm)
    (hlen : ∀ s : State, (∀ r, r ≠ .x25 → r ≠ .x26 → r ≠ .x27 → r ≠ .x3 → s.gpr r = σ.gpr r) →
      ∃ s', exec len s = some s' ∧ Only [.x4] s s' ∧ (s'.gpr .x4).toNat = P.len) :
    WP isa (.block (pro scr a prm len)) σ (VG.Proof.MlDsa.AArch64.Sample.J0 P σ) := by
  unfold pro
  refine wp_strx (a := P.at' 2016) (by decide) (by rw [hscr]) (VG.Proof.MlDsa.AArch64.Sample.inScr hp rfl (by omega)) fun s₁ h₁ => ?_
  refine wp_strx (a := P.at' 2024) (by decide) (by rw [h₁.gpr, hscr])
    (by rw [h₁.wr]; exact VG.Proof.MlDsa.AArch64.Sample.inScr hp rfl (by omega)) fun s₂ h₂ => ?_
  refine wp_strx (a := P.at' 2032) (by decide) (by rw [h₂.gpr, h₁.gpr, hscr])
    (by rw [h₂.wr, h₁.wr]; exact VG.Proof.MlDsa.AArch64.Sample.inScr hp rfl (by omega)) fun s₃ h₃ => ?_
  refine wp_strx (a := P.at' 2040) (by decide) (by rw [h₃.gpr, h₂.gpr, h₁.gpr, hscr])
    (by rw [h₃.wr, h₂.wr, h₁.wr]; exact VG.Proof.MlDsa.AArch64.Sample.inScr hp rfl (by omega)) fun s₄ h₄ => ?_
  have g₄ : ∀ r, s₄.gpr r = σ.gpr r := fun r => by rw [h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr]
  refine wp_mov fun s₅ h₅ e₅ => wp_mov fun s₆ h₆ e₆ => ?_
  obtain ⟨s₇, x₇, h₇, e₇⟩ := hprm s₆ fun r h25 h26 => by
    rw [h₆.get r (by simpa using h26), h₅.get r (by simpa using h25), g₄]
  refine Proof.MlKem.AArch64.WP.cons x₇ (wp_mov fun s₈ h₈ e₈ => ?_)
  obtain ⟨s₉, x₉, h₉, e₉⟩ := hlen s₈ fun r h25 h26 h27 h3 => by
    rw [h₈.get r (by simpa using h3), h₇.get r (by simpa using h27), h₆.get r (by simpa using h26),
      h₅.get r (by simpa using h25), g₄]
  refine Proof.MlKem.AArch64.WP.cons x₉ (wp_nil ?_)
  have k₉ := (((h₅.keep.trans h₆.keep).trans h₇.keep).trans h₈.keep).trans h₉.keep
  have m₉ : s₉.mem = (((σ.mem.writeW (P.at' 2016) (σ.gpr .x25)).writeW (P.at' 2024)
      (σ.gpr .x26)).writeW (P.at' 2032) (σ.gpr .x27)).writeW (P.at' 2040) (σ.gpr .x30) := by
    rw [h₉.mem, h₈.mem, h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem, h₃.gpr, h₂.gpr, h₁.gpr]
  have sep : ∀ a b, 2016 ≤ a → a + 8 ≤ b → b + 8 ≤ 2048 →
      Mem.Sep (P.at' a) (64 / 8) (P.at' b) (64 / 8) := fun a b h1 h2 h3 =>
    Offset.sep _ (.inl h2) (by omega) (by omega)
  refine ⟨⟨by rw [k₉.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd], by rw [k₉.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr],
    by rw [k₉.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp], ?_, ?_, ?_, ?_, ?_, ?_,
      fun r hr => by rw [k₉.vcs r hr, h₄.vcs r hr, h₃.vcs r hr, h₂.vcs r hr, h₁.vcs r hr]⟩, ?_, ?_⟩
  · rw [h₉.get .x25, h₈.get .x25, h₇.get .x25, h₆.get .x25, e₅, g₄, hscr]
  · rw [h₉.get .x26, h₈.get .x26, h₇.get .x26, e₆, h₅.get a (by simpa using ha25), g₄, ha]
  · rw [h₉.get .x27, h₈.get .x27, e₇]
  · intro r hr h25 h26 h27 _
    have h3 : r ≠ .x3 := fun e => by subst e; revert hr; decide
    have h4 : r ≠ .x4 := fun e => by subst e; revert hr; decide
    rw [h₉.get r (by simpa using h4), h₈.get r (by simpa using h3), h₇.get r (by simpa using h27),
      h₆.get r (by simpa using h26), h₅.get r (by simpa using h25), g₄]
  · rw [m₉]
    refine ⟨?_, ?_, ?_, Mem.readW_writeW_self64 _ _ _⟩
    · rw [Mem.readW_writeW_sep (sep 2016 2040 (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep 2016 2032 (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep 2016 2024 (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep (sep 2024 2040 (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep 2024 2032 (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep (sep 2032 2040 (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self64]
  · rw [m₉]
    have hm : P.scrR ∈ [polyR P.a, P.scrR, below σ.sp 16] := by simp
    exact ((((Frame.refl _ _).writeW hm _ (VG.Proof.MlDsa.AArch64.Sample.contains_scr (by omega))).writeW hm _
      (VG.Proof.MlDsa.AArch64.Sample.contains_scr (by omega))).writeW hm _ (VG.Proof.MlDsa.AArch64.Sample.contains_scr (by omega))).writeW hm _ (VG.Proof.MlDsa.AArch64.Sample.contains_scr (by omega))
  · rw [h₉.get .x3, e₈, h₇.get .x0, h₆.get .x0, h₅.get .x0, g₄, hsd]
  · exact e₉

/-! ## The sponge -/

/-- The zeros of the Keccak state at `x25`. -/
def zst (n : Nat) : List Instr := (List.range n).map fun k => .str .x .x9 .x25 (8 * k)

theorem zst_ok {P : VG.Proof.MlDsa.AArch64.Sample.Sp} {σ : State} (hp : VG.Proof.MlDsa.AArch64.Sample.SpOk P σ) :
    ∀ n ≤ 25, ∀ {s : State}, s.gpr .x9 = 0 → s.gpr .x25 = P.scr → s.wr = σ.wr →
      WP isa (.block (VG.Proof.MlDsa.AArch64.Sample.zst n)) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp ∧ (∀ k < n, s'.mem.readW (P.at' (8 * k)) 64 = 0) ∧
        Frame [⟨P.scr, 200⟩] s.mem s'.mem
  | 0, _, s, _, _, _ => wp_nil ⟨rfl, rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _),
      Frame.refl _ _⟩
  | n + 1, hn, s, h9, h25, hw => by
    rw [VG.Proof.MlDsa.AArch64.Sample.zst, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.zst_ok hp n (by omega) h9 h25 hw) fun s₁ ⟨g₁, r₁, w₁, p₁, z₁, f₁⟩ => ?_
    refine wp_strx (a := P.at' (8 * n)) (by constructor <;> omega) (by rw [g₁, h25])
      (by rw [w₁]; exact VG.Proof.MlDsa.AArch64.Sample.inScr hp hw (by omega)) fun s₂ h₂ => wp_nil ?_
    refine ⟨by rw [h₂.gpr, g₁], by rw [h₂.rd, r₁], by rw [h₂.wr, w₁], by rw [h₂.sp, p₁],
      fun k hk => ?_, ?_⟩
    · rw [h₂.mem, g₁, h9]
      by_cases e : k = n
      · subst e; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide)]
        exact z₁ k (by omega)
    · rw [h₂.mem]
      refine f₁.writeW (List.mem_singleton_self _) _ ?_
      rw [← VG.Proof.MlDsa.AArch64.Sample.at_zero (P := P)]
      exact Offset.contains _ (by omega) (by omega) (by omega)

theorem stateAt_zero {m : Mem} {p : Addr}
    (h : ∀ k < 25, m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = 0) : stateAt m p = Spec.Sha3.zero := by
  refine Vector.ext fun i hi => ?_
  simp only [stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
  exact h i hi

theorem toNat_movz {n : Nat} (h : n < 2 ^ 16) : ((BitVec.ofNat 16 n).setWidth 64).toNat = n := by
  rw [toNat_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem rate_pos {rate : Nat} (h : rate ∈ rates) : 0 < rate := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem rate_lt {rate : Nat} (h : rate ∈ rates) : rate < 2 ^ 16 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

/-- After zeroing the state: the arguments of `absorb`. -/
structure J1 (rate : Nat) (P : VG.Proof.MlDsa.AArch64.Sample.Sp) (σ s : State) : Prop where
  env : VG.Proof.MlDsa.AArch64.Sample.Env P σ s
  zero : stateAt s.mem P.scr = Spec.Sha3.zero
  x0 : s.gpr .x0 = P.scr
  x1 : (s.gpr .x1).toNat = rate
  x2 : (s.gpr .x2).toNat = 0
  x3 : s.gpr .x3 = P.sd
  x4 : (s.gpr .x4).toNat = P.len
  x5 : s.gpr .x5 = P.at' 200

section
variable {P : VG.Proof.MlDsa.AArch64.Sample.Sp} {σ : State} (hp : VG.Proof.MlDsa.AArch64.Sample.SpOk P σ)
include hp

theorem blk1_ok {rate : Nat} (hr : rate < 2 ^ 16) {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.J0 P σ s) :
    WP isa (.block (zeroSt ++ absArgs rate)) s (VG.Proof.MlDsa.AArch64.Sample.J1 rate P σ) := by
  unfold zeroSt
  refine wp_movz fun s₁ h₁ e₁ => ?_
  rw [List.append_eq, WP.block_append_iff]
  have e1 := h.env.keep h₁.keep h₁.mem
  refine WP.mono (WP.preservedV (VG.Proof.MlDsa.AArch64.Sample.zst_ok hp 25 (by decide) (by rw [e₁]; rfl) e1.x25 e1.wr) (hc := by lit_decide))
    fun s₂ ⟨⟨g₂, r₂, w₂, p₂, z₂, f₂⟩, vc₂⟩ => ?_
  have e2 : VG.Proof.MlDsa.AArch64.Sample.Env P σ s₂ := ⟨by rw [r₂, e1.rd], by rw [w₂, e1.wr], by rw [p₂, e1.sp], by rw [g₂, e1.x25],
    by rw [g₂, e1.x26], by rw [g₂, e1.x27], fun r hr a b c d => by rw [g₂, e1.cs r hr a b c d],
    VG.Proof.MlDsa.AArch64.Sample.sv_frame e1.saved f₂ (fun r hr => by
      rw [List.mem_singleton.mp hr, ← VG.Proof.MlDsa.AArch64.Sample.at_zero (P := P)]; exact VG.Proof.MlDsa.AArch64.Sample.sv_disj (by omega)),
    e1.frame.trans (f₂.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨P.scrR, by simp, VG.Proof.MlDsa.AArch64.Sample.sub_scr0 (by omega)⟩), fun r hr => (vc₂ r hr).trans (e1.vcs r hr)⟩
  refine wp_mov fun s₃ h₃ e₃ => wp_movz fun s₄ h₄ e₄ => wp_movz fun s₅ h₅ e₅ =>
    wp_addImm (by decide) fun s₆ h₆ e₆ => wp_nil ?_
  have k₆ := ((h₃.keep.trans h₄.keep).trans h₅.keep).trans h₆.keep
  have e6 := e2.keep k₆ (by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem])
  refine ⟨e6, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem]
    exact VG.Proof.MlDsa.AArch64.Sample.stateAt_zero fun k hk => z₂ k hk
  · rw [h₆.get .x0, h₅.get .x0, h₄.get .x0, e₃, e2.x25]
  · rw [h₆.get .x1, h₅.get .x1, e₄]; exact VG.Proof.MlDsa.AArch64.Sample.toNat_movz hr
  · rw [h₆.get .x2, e₅]; rfl
  · rw [h₆.get .x3, h₅.get .x3, h₄.get .x3, h₃.get .x3, g₂, h₁.get .x3, h.x3]
  · rw [h₆.get .x4, h₅.get .x4, h₄.get .x4, h₃.get .x4, g₂, h₁.get .x4, h.x4]
  · rw [e₆, h₅.get .x25, h₄.get .x25, h₃.get .x25, e2.x25]

/-- After absorbing the message. -/
structure J2 (rate : Nat) (P : VG.Proof.MlDsa.AArch64.Sample.Sp) (σ s : State) : Prop where
  env : VG.Proof.MlDsa.AArch64.Sample.Env P σ s
  repr : Repr s.mem P.scr rate (P.msg σ)
  x0 : (s.gpr .x0).toNat = P.len % rate

theorem call1With_ok (v : Proof.Sha3.AArch64.Permutation) {rate : Nat} (hr : rate ∈ rates) {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.J1 rate P σ s) :
    WP isa (.call ("vg_keccak_absorb_scratch" ++ v.callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith v.callee)) s (VG.Proof.MlDsa.AArch64.Sample.J2 rate P σ) := by
  have hsp := h.env.sp
  refine absorb_callWith v (st := P.scr) (sc := P.at' 200) h.x0 h.x1 h.x2 h.x3 h.x4 h.x5 hr
    (VG.Proof.MlDsa.AArch64.Sample.rate_pos hr)
    (by rw [← VG.Proof.MlDsa.AArch64.Sample.at_zero (P := P)]; exact VG.Proof.MlDsa.AArch64.Sample.disj_scr (.inl (by omega)) (by omega) (by omega))
    (hp.sd_scr.sub_right (VG.Proof.MlDsa.AArch64.Sample.sub_scr0 (by omega))) (VG.Proof.MlDsa.AArch64.Sample.sd_scr' hp (by omega))
    (by rw [hsp]; exact hp.sp16) (by rw [stk, hsp]; exact hp.stk_scr.sub_right (VG.Proof.MlDsa.AArch64.Sample.sub_scr0 (by omega)))
    (by rw [stk, hsp]; exact hp.stk_sd) (by rw [stk, hsp]; exact VG.Proof.MlDsa.AArch64.Sample.stk_scr' hp (by omega)) ?_
    (VG.Proof.MlDsa.AArch64.Sample.cov_scr hp h.env.wr ?_) fun s' hk hrep hx => ⟨Env.call hp h.env hk ?_, ?_, ?_⟩
  · rw [VG.Proof.MlDsa.AArch64.Sample.regions hp h.env]
    refine Covers.of_sub fun r hr => ?_
    rcases VG.Proof.MlDsa.AArch64.Sample.mem3 hr with rfl | rfl | rfl
    · exact ⟨P.sdR, by simp, 0, (ptr_zero _).symm, by simp⟩
    · exact ⟨P.scrR, by simp, 0, (ptr_zero _).symm, by simp⟩
    · exact ⟨P.scrR, by simp, 200, rfl, by simp⟩
  · intro r hr
    rcases VG.Proof.MlDsa.AArch64.Sample.mem2 hr with rfl | rfl
    · exact ⟨0, (VG.Proof.MlDsa.AArch64.Sample.at_zero).symm, by simp⟩
    · exact ⟨200, rfl, by simp⟩
  · intro r hr
    rcases VG.Proof.MlDsa.AArch64.Sample.mem3 hr with rfl | rfl | rfl
    · exact .inl ⟨0, 200, by rw [VG.Proof.MlDsa.AArch64.Sample.at_zero], by omega⟩
    · exact .inl ⟨200, 640, rfl, by omega⟩
    · exact .inr rfl
  · have := hrep [] (MlKem.repr_nil h.zero) (by simp)
    rwa [List.nil_append, VG.Proof.MlDsa.AArch64.Sample.sd_frame hp h.env.frame] at this
  · rw [hx, Nat.zero_add]

/-- The arguments of `pad`. -/
structure J3 (rate : Nat) (P : VG.Proof.MlDsa.AArch64.Sample.Sp) (σ s : State) : Prop where
  env : VG.Proof.MlDsa.AArch64.Sample.Env P σ s
  repr : Repr s.mem P.scr rate (P.msg σ)
  x0 : s.gpr .x0 = P.scr
  x1 : (s.gpr .x1).toNat = rate
  x2 : (s.gpr .x2).toNat = P.len % rate
  x3 : (s.gpr .x3).setWidth 8 = shakeSuffix
  x4 : s.gpr .x4 = P.at' 200

omit hp in
theorem blk2_ok {rate : Nat} (hr : rate ∈ rates) {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.J2 rate P σ s) :
    WP isa (.block (padArgs rate)) s (VG.Proof.MlDsa.AArch64.Sample.J3 rate P σ) := by
  refine wp_mov fun s₁ h₁ e₁ => wp_mov fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ => wp_movz fun s₄ h₄ e₄ =>
    wp_addImm (by decide) fun s₅ h₅ e₅ => wp_nil ?_
  have k₅ := (((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep
  have m₅ : s₅.mem = s.mem := by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨h.env.keep k₅ m₅, by rw [m₅]; exact h.repr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h₅.get .x0, h₄.get .x0, h₃.get .x0, e₂, h₁.get .x25, h.env.x25]
  · rw [h₅.get .x1, h₄.get .x1, e₃]; exact VG.Proof.MlDsa.AArch64.Sample.toNat_movz (VG.Proof.MlDsa.AArch64.Sample.rate_lt hr)
  · rw [h₅.get .x2, h₄.get .x2, h₃.get .x2, h₂.get .x2, e₁, h.x0]
  · rw [h₅.get .x3, e₄]; decide
  · rw [e₅, h₄.get .x25, h₃.get .x25, h₂.get .x25, h₁.get .x25, h.env.x25]

/-- After padding. -/
structure J4 (rate : Nat) (P : VG.Proof.MlDsa.AArch64.Sample.Sp) (σ s : State) : Prop where
  env : VG.Proof.MlDsa.AArch64.Sample.Env P σ s
  st : stateAt s.mem P.scr = padded rate shakeSuffix (P.msg σ)

theorem call2With_ok (v : Proof.Sha3.AArch64.Permutation) {rate : Nat} (hr : rate ∈ rates) {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.J3 rate P σ s) :
    WP isa (.call ("vg_keccak_pad_scratch" ++ v.callee.suffix) (Impl.Sha3.AArch64.Stream.padWith v.callee)) s (VG.Proof.MlDsa.AArch64.Sample.J4 rate P σ) := by
  have hsp := h.env.sp
  have cw : Covers [⟨P.scr, 200⟩, ⟨P.at' 200, 640⟩] s.wr := VG.Proof.MlDsa.AArch64.Sample.cov_scr hp h.env.wr fun r hr => by
    rcases VG.Proof.MlDsa.AArch64.Sample.mem2 hr with rfl | rfl
    · exact ⟨0, (VG.Proof.MlDsa.AArch64.Sample.at_zero).symm, by simp⟩
    · exact ⟨200, rfl, by simp⟩
  refine pad_callWith v (st := P.scr) (sc := P.at' 200) h.x0 h.x1 h.x2 h.x4 hr
    (Nat.mod_lt _ (VG.Proof.MlDsa.AArch64.Sample.rate_pos hr))
    (by rw [← VG.Proof.MlDsa.AArch64.Sample.at_zero (P := P)]; exact VG.Proof.MlDsa.AArch64.Sample.disj_scr (.inl (by omega)) (by omega) (by omega))
    (by rw [hsp]; exact hp.sp16) (by rw [stk, hsp]; exact hp.stk_scr.sub_right (VG.Proof.MlDsa.AArch64.Sample.sub_scr0 (by omega)))
    (by rw [stk, hsp]; exact VG.Proof.MlDsa.AArch64.Sample.stk_scr' hp (by omega)) (VG.Proof.MlDsa.AArch64.Sample.cov_rd cw) cw fun s' hk hst =>
      ⟨Env.call hp h.env hk ?_, ?_⟩
  · intro r hr
    rcases VG.Proof.MlDsa.AArch64.Sample.mem3 hr with rfl | rfl | rfl
    · exact .inl ⟨0, 200, by rw [VG.Proof.MlDsa.AArch64.Sample.at_zero], by omega⟩
    · exact .inl ⟨200, 640, rfl, by omega⟩
    · exact .inr rfl
  · have := hst (P.msg σ) h.repr (by rw [MlKem.bytesAt_length])
    rw [h.x3] at this
    exact this

/-- The arguments of `squeeze`. -/
structure J5 (rate outlen : Nat) (P : VG.Proof.MlDsa.AArch64.Sample.Sp) (σ s : State) : Prop where
  env : VG.Proof.MlDsa.AArch64.Sample.Env P σ s
  st : stateAt s.mem P.scr = padded rate shakeSuffix (P.msg σ)
  x0 : s.gpr .x0 = P.scr
  x1 : (s.gpr .x1).toNat = rate
  x2 : (s.gpr .x2).toNat = 0
  x3 : s.gpr .x3 = P.at' 840
  x4 : (s.gpr .x4).toNat = outlen
  x5 : s.gpr .x5 = P.at' 200

omit hp in
theorem blk3_ok {rate outlen : Nat} (hr : rate ∈ rates) (ho : outlen < 2 ^ 16) {s : State}
    (h : VG.Proof.MlDsa.AArch64.Sample.J4 rate P σ s) : WP isa (.block (sqzArgs rate outlen)) s (VG.Proof.MlDsa.AArch64.Sample.J5 rate outlen P σ) := by
  refine wp_mov fun s₁ h₁ e₁ => wp_movz fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ =>
    wp_addImm (by decide) fun s₄ h₄ e₄ => wp_movz fun s₅ h₅ e₅ => wp_addImm (by decide) fun s₆ h₆ e₆ =>
    wp_nil ?_
  have k₆ := ((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans h₆.keep
  have m₆ : s₆.mem = s.mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have g25 : ∀ {u : State}, Keep [.x0, .x1, .x2, .x3, .x4, .x5] s u → u.gpr .x25 = P.scr :=
    fun hk => by rw [hk.get .x25, h.env.x25]
  refine ⟨h.env.keep k₆ m₆, by rw [m₆]; exact h.st, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h₆.get .x0, h₅.get .x0, h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁, h.env.x25]
  · rw [h₆.get .x1, h₅.get .x1, h₄.get .x1, h₃.get .x1, e₂]; exact VG.Proof.MlDsa.AArch64.Sample.toNat_movz (VG.Proof.MlDsa.AArch64.Sample.rate_lt hr)
  · rw [h₆.get .x2, h₅.get .x2, h₄.get .x2, e₃]; rfl
  · rw [h₆.get .x3, h₅.get .x3, e₄, g25 ((h₁.keep.trans h₂.keep).trans h₃.keep).mono]
  · rw [h₆.get .x4, e₅]; exact VG.Proof.MlDsa.AArch64.Sample.toNat_movz ho
  · rw [e₆, h₅.get .x25, h₄.get .x25, h₃.get .x25, h₂.get .x25, h₁.get .x25, h.env.x25]

/-- After squeezing: the output. -/
structure J6 (rate outlen : Nat) (P : VG.Proof.MlDsa.AArch64.Sample.Sp) (σ s : State) : Prop where
  env : VG.Proof.MlDsa.AArch64.Sample.Env P σ s
  out : bytesAt s.mem (P.at' 840) outlen =
    Spec.Sha3.squeezeFrom rate (padded rate shakeSuffix (P.msg σ)) 0 outlen

theorem call3With_ok (v : Proof.Sha3.AArch64.Permutation) {rate outlen : Nat} (hr : rate ∈ rates) (ho : 840 + outlen ≤ 2016) {s : State}
    (h : VG.Proof.MlDsa.AArch64.Sample.J5 rate outlen P σ s) :
    WP isa (.call ("vg_keccak_squeeze_scratch" ++ v.callee.suffix) (Impl.Sha3.AArch64.Stream.squeezeWith v.callee)) s (VG.Proof.MlDsa.AArch64.Sample.J6 rate outlen P σ) := by
  have hsp := h.env.sp
  have cw : Covers [⟨P.scr, 200⟩, ⟨P.at' 840, outlen⟩, ⟨P.at' 200, 640⟩] s.wr :=
    VG.Proof.MlDsa.AArch64.Sample.cov_scr hp h.env.wr fun r hr => by
      rcases VG.Proof.MlDsa.AArch64.Sample.mem3 hr with rfl | rfl | rfl
      · exact ⟨0, (VG.Proof.MlDsa.AArch64.Sample.at_zero).symm, by simp⟩
      · exact ⟨840, rfl, by simp; omega⟩
      · exact ⟨200, rfl, by simp⟩
  refine squeeze_callWith v (st := P.scr) (out := P.at' 840) (sc := P.at' 200) h.x0 h.x1 h.x2 h.x3 h.x4 h.x5 hr
    (Nat.zero_le _)
    (by rw [← VG.Proof.MlDsa.AArch64.Sample.at_zero (P := P)]; exact VG.Proof.MlDsa.AArch64.Sample.disj_scr (.inl (by omega)) (by omega) (by omega))
    (by rw [← VG.Proof.MlDsa.AArch64.Sample.at_zero (P := P)]; exact VG.Proof.MlDsa.AArch64.Sample.disj_scr (.inl (by omega)) (by omega) (by omega))
    (VG.Proof.MlDsa.AArch64.Sample.disj_scr (.inr (by omega)) (by omega) (by omega))
    (by rw [hsp]; exact hp.sp16) (by rw [stk, hsp]; exact hp.stk_scr.sub_right (VG.Proof.MlDsa.AArch64.Sample.sub_scr0 (by omega)))
    (by rw [stk, hsp]; exact VG.Proof.MlDsa.AArch64.Sample.stk_scr' hp (by omega)) (by rw [stk, hsp]; exact VG.Proof.MlDsa.AArch64.Sample.stk_scr' hp (by omega))
    (VG.Proof.MlDsa.AArch64.Sample.cov_rd cw) cw fun s' hk hout _ _ => ⟨Env.call hp h.env hk ?_, ?_⟩
  · intro r hr
    rcases VG.Proof.MlDsa.AArch64.Sample.mem4 hr with rfl | rfl | rfl | rfl
    · exact .inl ⟨0, 200, by rw [VG.Proof.MlDsa.AArch64.Sample.at_zero], by omega⟩
    · exact .inl ⟨840, outlen, rfl, ho⟩
    · exact .inl ⟨200, 640, rfl, by omega⟩
    · exact .inr rfl
  · rw [hout, h.st]

/-- The sponge, from `J0`: `outlen` bytes of SHAKE at `scratch + 840`. -/
theorem spongeWith_ok (v : Proof.Sha3.AArch64.Permutation) {rate outlen : Nat} (hr : rate ∈ rates) (ho : 840 + outlen ≤ 2016) {s : State}
    (h : VG.Proof.MlDsa.AArch64.Sample.J0 P σ s) : WP isa (spongeWith v.callee rate outlen) s (VG.Proof.MlDsa.AArch64.Sample.J6 rate outlen P σ) :=
  WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.blk1_ok hp (VG.Proof.MlDsa.AArch64.Sample.rate_lt hr) h) fun _ h1 =>
    WP.seq (WP.mono ((VG.Proof.MlDsa.AArch64.Sample.call1With_ok (v := v)) hp hr h1) fun _ h2 => WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.blk2_ok hr h2) fun _ h3 =>
      WP.seq (WP.mono ((VG.Proof.MlDsa.AArch64.Sample.call2With_ok (v := v)) hp hr h3) fun _ h4 =>
        WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.blk3_ok hr (by omega) h4) fun _ h5 => (VG.Proof.MlDsa.AArch64.Sample.call3With_ok (v := v)) hp hr ho h5)))))

theorem sponge_ok {rate outlen : Nat} (hr : rate ∈ rates) (ho : 840 + outlen ≤ 2016) {s : State}
    (h : VG.Proof.MlDsa.AArch64.Sample.J0 P σ s) : WP isa (sponge rate outlen) s (VG.Proof.MlDsa.AArch64.Sample.J6 rate outlen P σ) :=
  VG.Proof.MlDsa.AArch64.Sample.spongeWith_ok (v := .scalar) hp hr ho h

/-! ## The epilogue -/

/-- The epilogue: `x30`, `x26`, `x27` and `x25` restored; with `Env`, the
calling convention's obligations. -/
theorem epi_ok {s : State} (he : VG.Proof.MlDsa.AArch64.Sample.Env P σ s) :
    WP isa (.block epi) s fun s' => abiPreserved σ s' ∧ s'.mem = s.mem ∧
      Keep [.x30, .x26, .x27, .x25] s s' := by
  have in8 : ∀ {u : State}, u.rd = σ.rd → u.wr = σ.wr → ∀ {off : Nat}, off + 8 ≤ 2048 →
      InRegions (u.rd ++ u.wr) (P.at' off) 8 := fun hr hw _ h' => VG.Proof.MlDsa.AArch64.Sample.inScrRd hp hr hw h'
  refine wp_ldrx (a := P.at' 2040) (by decide) (by rw [he.x25]) (in8 he.rd he.wr (by omega))
    fun s₁ h₁ e₁ => ?_
  refine wp_ldrx (a := P.at' 2024) (by decide) (by rw [h₁.get .x25, he.x25])
    (in8 (by rw [h₁.rd, he.rd]) (by rw [h₁.wr, he.wr]) (by omega)) fun s₂ h₂ e₂ => ?_
  refine wp_ldrx (a := P.at' 2032) (by decide) (by rw [h₂.get .x25, h₁.get .x25, he.x25])
    (in8 (by rw [h₂.rd, h₁.rd, he.rd]) (by rw [h₂.wr, h₁.wr, he.wr]) (by omega)) fun s₃ h₃ e₃ => ?_
  refine wp_ldrx (a := P.at' 2016) (by decide) (by rw [h₃.get .x25, h₂.get .x25, h₁.get .x25, he.x25])
    (in8 (by rw [h₃.rd, h₂.rd, h₁.rd, he.rd]) (by rw [h₃.wr, h₂.wr, h₁.wr, he.wr]) (by omega))
    fun s₄ h₄ e₄ => wp_nil ?_
  have k₄ := ((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep
  have m₄ : s₄.mem = s.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have sv := he.saved
  refine ⟨⟨fun r hr => ?_, by rw [k₄.sp, he.sp], fun r hr => (k₄.vcs r hr).trans (he.vcs r hr)⟩, m₄, k₄⟩
  by_cases h30 : r = .x30
  · subst h30; rw [h₄.get .x30, h₃.get .x30, h₂.get .x30, e₁]; exact sv.2.2.2
  by_cases h26 : r = .x26
  · subst h26; rw [h₄.get .x26, h₃.get .x26, e₂, h₁.mem]; exact sv.2.1
  by_cases h27 : r = .x27
  · subst h27; rw [h₄.get .x27, e₃, h₂.mem, h₁.mem]; exact sv.2.2.1
  by_cases h25 : r = .x25
  · subst h25; rw [e₄, h₃.mem, h₂.mem, h₁.mem]; exact sv.1
  rw [k₄.gpr r (by simp [h30, h25, h26, h27]), he.cs r hr h25 h26 h27 h30]

end

end VG.Proof.MlDsa.AArch64.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero`. -/
section

/-!
# ML-DSA on AArch64: the output polynomial set to zeros

`zeroPoly` stores zero to the 256 coefficients of the output polynomial
(`zeroPoly_ok`), and writes nothing else but `x3`, `x4` and `x9`.
-/

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_mov wp_movz wp_addImm wp_subImm wp_strw ptr_zero
  toNat_sub_n count_loop)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample (coeffAddr polyR coeff_contains coeffAt_writeW)
open VG.Spec.MlDsa (coeffAt)

/-- After `k` coefficients set to zero. -/
structure ZInv (aP : Addr) (s₁ : State) (k : Nat) (u : State) : Prop where
  keep : Keep [.x3, .x4] s₁ u
  x3 : u.gpr .x3 = coeffAddr aP k
  x4 : (u.gpr .x4).toNat = 256 - k
  zero : ∀ i < k, coeffAt u.mem aP i = 0
  frame : Frame [polyR aP] s₁.mem u.mem

theorem zero_step {aP : Addr} {s₁ : State} (hw : ∀ i < 256, InRegions s₁.wr (coeffAddr aP i) 4)
    (h9 : s₁.gpr .x9 = 0) {k : Nat} (hk : k < 256) {u : State} (h : VG.Proof.MlDsa.AArch64.Sample.ZInv aP s₁ k u) :
    WP isa (.block [.str .w .x9 .x3 0, .addImm .x .x3 .x3 4, .subImm .x .x4 .x4 1]) u
      fun u' => VG.Proof.MlDsa.AArch64.Sample.ZInv aP s₁ (k + 1) u' ∧ ((u'.gpr .x4).toNat ≠ 0 ↔ k + 1 ≠ 256) := by
  refine wp_strw (a := coeffAddr aP k) (by decide) (by rw [h.x3, ptr_zero]) (by rw [h.keep.wr]; exact hw k hk)
    fun u₁ h₁ => wp_addImm (by decide) fun u₂ h₂ e₂ => wp_subImm (by decide) fun u₃ h₃ e₃ => wp_nil ?_
  have c4 : (u₂.gpr .x4).toNat = 256 - k := by rw [h₂.get .x4, h₁.gpr, h.x4]
  have v4 : (u₃.gpr .x4).toNat = 256 - (k + 1) := by
    rw [e₃, toNat_sub_n (by rw [c4]; simp; omega), c4]
    simp
    omega
  have m₃ : u₃.mem = u.mem.writeW (coeffAddr aP k) ((u.gpr .x9).setWidth 32) := by
    rw [h₃.mem, h₂.mem, h₁.mem]
  have z : (u.gpr .x9).setWidth 32 = 0 := by rw [h.keep.get .x9, h9]; rfl
  refine ⟨⟨(h.keep.trans ((h₁.keep.trans h₂.keep).trans h₃.keep)).mono, ?_, v4, fun i hi => ?_, ?_⟩,
    by rw [v4]; omega⟩
  · rw [h₃.get .x3, e₂, h₁.gpr, h.x3, coeffAddr, coeffAddr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · rw [m₃, z, coeffAt_writeW _ _ (by omega) hk]
    split
    · rfl
    · exact h.zero i (by omega)
  · rw [m₃]
    exact h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ hk)

/-- The coefficients of `a` set to zeros. -/
theorem zeroPoly_ok {aP : Addr} {s : State} (hw : ∀ i < 256, InRegions s.wr (coeffAddr aP i) 4)
    (h26 : s.gpr .x26 = aP) :
    WP isa zeroPoly s fun u => Keep [.x9, .x3, .x4] s u ∧ (∀ i < 256, coeffAt u.mem aP i = 0) ∧
      Frame [polyR aP] s.mem u.mem := by
  refine WP.seq (wp_movz fun s₁ h₁ e₁ => wp_mov fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ => wp_nil ?_)
  have k₃ := (h₁.keep.trans h₂.keep).trans h₃.keep
  have z9 : s₃.gpr .x9 = 0 := by rw [h₃.get .x9, h₂.get .x9, e₁]; rfl
  have i₀ : VG.Proof.MlDsa.AArch64.Sample.ZInv aP s₃ 0 s₃ := ⟨Keep.refl _ _,
    by rw [h₃.get .x3, e₂, h₁.get .x26, h26, coeffAddr, Nat.mul_zero, ptr_zero],
    by rw [e₃]; rfl, fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
  refine WP.mono (count_loop (by decide) (VG.Proof.MlDsa.AArch64.Sample.ZInv aP s₃)
    (fun k hk u hu => VG.Proof.MlDsa.AArch64.Sample.zero_step (by rw [k₃.wr]; exact hw) z9 hk hu) i₀) fun s₄ h₄ => ?_
  refine ⟨(k₃.trans h₄.keep).mono, h₄.zero, ?_⟩
  rw [← show s₃.mem = s.mem by rw [h₃.mem, h₂.mem, h₁.mem]]
  exact h₄.frame

end VG.Proof.MlDsa.AArch64.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttLoop`. -/
section

/-!
# ML-DSA on AArch64: the loop of `vg_mldsa_rej_ntt_poly`

The 336 iterations of the loop on the 1008 bytes `X` at `bP` store the
coefficients that `rnFold` samples from them at `aP` (`loop_ok`): iteration
`t` starts from `LAt t`, with those of the first `3t` bytes stored. A
coefficient is stored as coefficient `j` whether it is accepted or not
(`Stored` constrains only the first `j`). The loop reads only the output, and
writes only `a`.
-/

namespace VG.Proof.MlDsa.AArch64.Sample.RejNtt

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_mov wp_movz wp_movk1 wp_addImm wp_subImm wp_strw
  wp_ldrb wp_sub wp_add wp_lsr wp_lsl wp_and ptr_zero ptr_add toNat_sub_n toNat_add_n toNat_lsl_n
  toNat_and_mask toNat_byte toNat_lsr count_loop eval_zero eq_zero_iff)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (coeffAt Zq q)
open VG.Spec.Sha3 (bytesAt)

/-- What the loop needs of the state it starts from: the 1008 bytes `X` at
`bP = x25 + 840`, which it may read, and `a` at `aP = x26`, which it may
write. -/
structure LPre (X : List Byte) (bP aP : Addr) (s : State) : Prop where
  buf : ∀ p < 1008, s.mem (bP + BitVec.ofNat 64 p) = X.getD p 0
  inb : ∀ p < 1008, InRegions (s.rd ++ s.wr) (bP + BitVec.ofNat 64 p) 1
  ina : ∀ i < 256, InRegions s.wr (coeffAddr aP i) 4
  disj : (⟨bP, 1008⟩ : Region).Disjoint (polyR aP)
  x25 : s.gpr .x25 + BitVec.ofNat 64 840 = bP
  x26 : s.gpr .x26 = aP

/-- The coefficients sampled from the first `3t` bytes. -/
abbrev Lt (X : List Byte) (t : Nat) : List Zq := rnFold [] (X.take (3 * t))

theorem Lt_length_le (X : List Byte) (t : Nat) : (VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt X t).length ≤ 256 := rnFold_length_le (by simp) _

/-- The registers the loop writes. -/
abbrev lRegs : List Reg := [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x13, .x14, .x15]

/-- At the start of iteration `t`, from the loop's entry state `s₀`. -/
structure LAt (X : List Byte) (bP aP : Addr) (s₀ : State) (t : Nat) (s : State) : Prop where
  keep : Keep VG.Proof.MlDsa.AArch64.Sample.RejNtt.lRegs s₀ s
  frame : Frame [polyR aP] s₀.mem s.mem
  x2 : s.gpr .x2 = bP + BitVec.ofNat 64 (3 * t)
  x3 : s.gpr .x3 = coeffAddr aP (VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt X t).length
  x4 : (s.gpr .x4).toNat = 256 - (VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt X t).length
  x5 : (s.gpr .x5).toNat = 336 - t
  x9 : (s.gpr .x9).toNat = q
  x10 : (s.gpr .x10).toNat = 127
  st : Stored s.mem aP (VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt X t)

theorem q_eq : q = 8380417 := rfl

/-- The byte `p` of the output, in any state of the loop. -/
theorem LAt.byte {X : List Byte} {bP aP : Addr} {s₀ : State} (hp : VG.Proof.MlDsa.AArch64.Sample.RejNtt.LPre X bP aP s₀) {t : Nat} {s : State}
    (h : VG.Proof.MlDsa.AArch64.Sample.RejNtt.LAt X bP aP s₀ t s) {p : Nat} (hp' : p < 1008) : s.mem (bP + BitVec.ofNat 64 p) = X.getD p 0 := by
  rw [← hp.buf p hp']
  exact h.frame _ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact hp.disj _ (Offset.contains_base _ (by omega) (by omega))

theorem take_add_three (L : List Byte) {i : Nat} (h : i + 3 ≤ L.length) :
    L.take (i + 3) = L.take i ++ [L.getD i 0, L.getD (i + 1) 0, L.getD (i + 2) 0] := by
  rw [List.take_add, List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega)]
  simp only [List.take_succ_cons, List.take_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < L.length by omega), List.getElem?_eq_getElem (show i + 1 < L.length by omega),
    List.getElem?_eq_getElem (show i + 2 < L.length by omega), Option.getD_some]

/-- `v - b` of numbers below `2⁶³`, negative exactly when `v < b`. -/
theorem lt_bit {a b : BitVec 64} {v w : Nat} (ha : a.toNat = v) (hb : b.toNat = w) (hv : v < 2 ^ 63)
    (hw : w < 2 ^ 63) : ((a - b) >>> 63).toNat = if v < w then 1 else 0 := by
  rw [toNat_lsr, BitVec.toNat_sub, ha, hb]
  split <;> omega

/-- A coefficient stored past the ones sampled keeps them. -/
theorem stored_past {m : Mem} {p : Addr} {L : List Zq} (h : Stored m p L) {k : Nat} (hk : L.length ≤ k)
    (hk' : k < 256) (v : BitVec 32) : Stored (m.writeW (coeffAddr p k) v) p L := fun i hi => by
  rw [coeffAt_writeW _ _ (by omega) hk', ite_eq_right (by omega)]
  exact h i hi

/-- The value of the 3 bytes `b₀, b₁, b₂` at `x2` into `x11`. -/
theorem chunk_ok {s : State} {b₀ b₁ b₂ : Byte}
    (h₀ : s.mem (s.gpr .x2) = b₀) (h₁ : s.mem (s.gpr .x2 + 1) = b₁) (h₂ : s.mem (s.gpr .x2 + 2) = b₂)
    (i₀ : InRegions (s.rd ++ s.wr) (s.gpr .x2) 1) (i₁ : InRegions (s.rd ++ s.wr) (s.gpr .x2 + 1) 1)
    (i₂ : InRegions (s.rd ++ s.wr) (s.gpr .x2 + 2) 1) (h10 : (s.gpr .x10).toNat = 127) :
    WP isa (.block rnChunk) s fun s' => Only [.x6, .x7, .x8, .x2, .x5, .x11] s s' ∧
      s'.gpr .x2 = s.gpr .x2 + 3 ∧ s'.gpr .x5 = s.gpr .x5 - 1 ∧ (s'.gpr .x11).toNat = rnZ b₀ b₁ b₂ := by
  refine wp_ldrb (a := s.gpr .x2) (by decide) (ptr_zero _) i₀ fun s₁ o₁ e₁ => ?_
  refine wp_ldrb (a := s.gpr .x2 + 1) (by decide) (by rw [o₁.get .x2]; rfl) (by rw [o₁.rd, o₁.wr]; exact i₁)
    fun s₂ o₂ e₂ => ?_
  refine wp_ldrb (a := s.gpr .x2 + 2) (by decide) (by rw [o₂.get .x2, o₁.get .x2]; rfl)
    (by rw [o₂.rd, o₂.wr, o₁.rd, o₁.wr]; exact i₂) fun s₃ o₃ e₃ => ?_
  refine wp_addImm (by decide) fun s₄ o₄ e₄ => wp_subImm (by decide) fun s₅ o₅ e₅ => wp_and fun s₆ o₆ e₆ =>
    wp_lsl (by decide) fun s₇ o₇ e₇ => wp_lsl (by decide) fun s₈ o₈ e₈ => wp_add fun s₉ o₉ e₉ =>
    wp_add fun s₁₀ o₁₀ e₁₀ => wp_nil ?_
  have k := (((((((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆).trans o₇).trans o₈).trans
    o₉).trans o₁₀).mono (rs' := [.x6, .x7, .x8, .x2, .x5, .x11]) (by decide)
  have hb : b₀.toNat < 256 := b₀.isLt
  have hb1 : b₁.toNat < 256 := b₁.isLt
  have hb2 : b₂.toNat < 256 := b₂.isLt
  have v6 : (s₈.gpr .x6).toNat = b₀.toNat := by
    rw [o₈.get .x6, o₇.get .x6, o₆.get .x6, o₅.get .x6, o₄.get .x6, o₃.get .x6, o₂.get .x6, e₁,
      toNat_byte, h₀]
  have c7 : (s₇.gpr .x7).toNat = b₁.toNat := by
    rw [o₇.get .x7, o₆.get .x7, o₅.get .x7, o₄.get .x7, o₃.get .x7, e₂, toNat_byte, o₁.mem, h₁]
  have v7 : (s₈.gpr .x7).toNat = 256 * b₁.toNat := by
    have hl : (s₇.gpr .x7).toNat * 2 ^ 8 < 2 ^ 64 := by rw [c7]; simp only [Nat.reducePow]; omega
    rw [e₈, toNat_lsl_n hl, c7]
    omega
  have v8a : (s₆.gpr .x8).toNat = b₂.toNat % 128 := by
    have m : (s₅.gpr .x10).toNat = 2 ^ 7 - 1 := by
      rw [o₅.get .x10, o₄.get .x10, o₃.get .x10, o₂.get .x10, o₁.get .x10, h10]
    rw [e₆, toNat_and_mask _ _ m, o₅.get .x8, o₄.get .x8, e₃, toNat_byte, o₂.mem, o₁.mem, h₂]
  have v8 : (s₇.gpr .x8).toNat = 65536 * (b₂.toNat % 128) := by
    have hl : (s₆.gpr .x8).toNat * 2 ^ 16 < 2 ^ 64 := by rw [v8a]; simp only [Nat.reducePow]; omega
    rw [e₇, toNat_lsl_n hl, v8a]
    omega
  refine ⟨k, by rw [o₁₀.get .x2, o₉.get .x2, o₈.get .x2, o₇.get .x2, o₆.get .x2, o₅.get .x2, e₄,
    o₃.get .x2, o₂.get .x2, o₁.get .x2]; rfl,
    by rw [o₁₀.get .x5, o₉.get .x5, o₈.get .x5, o₇.get .x5, o₆.get .x5, e₅, o₄.get .x5, o₃.get .x5,
      o₂.get .x5, o₁.get .x5]; rfl, ?_⟩
  have v11 : (s₉.gpr .x11).toNat = b₀.toNat + 256 * b₁.toNat := by
    rw [e₉, toNat_add_n (by rw [v6, v7]; omega), v6, v7]
  rw [e₁₀, toNat_add_n (by rw [v11, o₉.get .x8, o₈.get .x8, v8]; omega), v11, o₉.get .x8, o₈.get .x8, v8]
  unfold rnZ; omega


/-- The coefficients after trying the value `z`. -/
abbrev acc (L : List Zq) (z : Nat) : List Zq := if z < q then L ++ [Fin.ofNat q z] else L

theorem acc_length (L : List Zq) (z : Nat) : (VG.Proof.MlDsa.AArch64.Sample.RejNtt.acc L z).length = L.length + if z < q then 1 else 0 := by
  unfold VG.Proof.MlDsa.AArch64.Sample.RejNtt.acc; split <;> simp

/-- Storing `x11` as coefficient `j`, and counting it if it is less than
`q`. -/
theorem accept_ok {aP : Addr} {L : List Zq} {z : Nat} {u : State} (hz : (u.gpr .x11).toNat = z)
    (hz' : z < 2 ^ 23) (h9 : (u.gpr .x9).toNat = q) (h3 : u.gpr .x3 = coeffAddr aP L.length)
    (h4 : (u.gpr .x4).toNat = 256 - L.length) (hl : L.length < 256) (hst : Stored u.mem aP L)
    (hw : InRegions u.wr (coeffAddr aP L.length) 4) :
    WP isa (.block rnAccept) u fun u' => Keep [.x3, .x4, .x13, .x14, .x15] u u' ∧
      Frame [polyR aP] u.mem u'.mem ∧ u'.gpr .x3 = coeffAddr aP (VG.Proof.MlDsa.AArch64.Sample.RejNtt.acc L z).length ∧
      (u'.gpr .x4).toNat = 256 - (VG.Proof.MlDsa.AArch64.Sample.RejNtt.acc L z).length ∧ Stored u'.mem aP (VG.Proof.MlDsa.AArch64.Sample.RejNtt.acc L z) := by
  refine wp_sub fun u₁ h₁ e₁ => wp_lsr (by decide) fun u₂ h₂ e₂ => ?_
  have v14 : (u₂.gpr .x14).toNat = if z < q then 1 else 0 := by
    rw [e₂, e₁]; exact VG.Proof.MlDsa.AArch64.Sample.RejNtt.lt_bit hz h9 (by omega) (by rw [VG.Proof.MlDsa.AArch64.Sample.RejNtt.q_eq]; omega)
  refine wp_strw (a := coeffAddr aP L.length) (by decide)
    (by rw [h₂.get .x3, h₁.get .x3, h3, ptr_zero]) (by rw [h₂.wr, h₁.wr]; exact hw) fun u₃ h₃ =>
    wp_lsl (by decide) fun u₄ h₄ e₄ => wp_add fun u₅ h₅ e₅ => wp_sub fun u₆ h₆ e₆ => wp_nil ?_
  have k₆ := (((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans
    h₆.keep).mono (rs' := [.x3, .x4, .x13, .x14, .x15]) (by decide)
  have m₆ : u₆.mem = u.mem.writeW (coeffAddr aP L.length) ((u.gpr .x11).setWidth 32) := by
    rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.get .x11, h₁.get .x11, h₂.mem, h₁.mem]
  have x14 : u₅.gpr .x14 = u₂.gpr .x14 := by rw [h₅.get .x14, h₄.get .x14, h₃.gpr]
  have x15 : u₄.gpr .x15 = BitVec.ofNat 64 (4 * if z < q then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    have hl : (u₃.gpr .x14).toNat * 2 ^ 2 < 2 ^ 64 := by rw [h₃.gpr, v14]; split <;> decide
    rw [e₄, toNat_lsl_n hl, h₃.gpr, v14, BitVec.toNat_ofNat]
    split <;> decide
  have c4 : (u₅.gpr .x4).toNat = 256 - L.length := by
    rw [h₅.get .x4, h₄.get .x4, h₃.gpr, h₂.get .x4, h₁.get .x4, h4]
  refine ⟨k₆, ?_, ?_, ?_, ?_⟩
  · rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hl)
  · rw [h₆.get .x3, e₅, h₄.get .x3, h₃.gpr, h₂.get .x3, h₁.get .x3, h3, x15, coeffAddr, coeffAddr,
      ptr_add, VG.Proof.MlDsa.AArch64.Sample.RejNtt.acc_length, Nat.mul_add]
  · have hx : (u₅.gpr .x14).toNat ≤ (u₅.gpr .x4).toNat := by rw [x14, v14, c4]; split <;> omega
    rw [e₆, toNat_sub_n hx, c4, x14, v14, VG.Proof.MlDsa.AArch64.Sample.RejNtt.acc_length]
    omega
  · rw [m₆]
    unfold VG.Proof.MlDsa.AArch64.Sample.RejNtt.acc
    split
    · rename_i hq
      have hw : (u.gpr .x11).setWidth 32 = zw (Fin.ofNat q z) := by
        apply BitVec.eq_of_toNat_eq
        rw [zw_toNat, BitVec.toNat_setWidth, hz, Fin.val_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt hq]
      rw [hw]; exact stored_snoc hst hl _
    · exact VG.Proof.MlDsa.AArch64.Sample.RejNtt.stored_past hst (Nat.le_refl _) hl _

/-- An iteration, from `LAt t`. -/
theorem step_ok {X : List Byte} (hX : X.length = 1008) {bP aP : Addr} {s₀ : State} (hp : VG.Proof.MlDsa.AArch64.Sample.RejNtt.LPre X bP aP s₀)
    {t : Nat} (ht : t < 336) {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.RejNtt.LAt X bP aP s₀ t s) :
    WP isa rnBody s fun s' => VG.Proof.MlDsa.AArch64.Sample.RejNtt.LAt X bP aP s₀ (t + 1) s' ∧ ((s'.gpr .x5).toNat ≠ 0 ↔ t + 1 ≠ 336) := by
  have hin : ∀ k < 3, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 k) 1 := fun k hk => by
    rw [h.keep.rd, h.keep.wr, h.x2, ptr_add]; exact hp.inb _ (by omega)
  have hb : ∀ k < 3, s.mem (s.gpr .x2 + BitVec.ofNat 64 k) = X.getD (3 * t + k) 0 := fun k hk => by
    rw [h.x2, ptr_add]; exact h.byte hp (by omega)
  have e0 : s.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 0 := (ptr_zero _).symm
  have hL : VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt X (t + 1) = rnStep (VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt X t) (X.getD (3 * t) 0) (X.getD (3 * t + 1) 0) (X.getD (3 * t + 2) 0) := by
    simp only [VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt]
    rw [show 3 * (t + 1) = 3 * t + 3 by omega, VG.Proof.MlDsa.AArch64.Sample.RejNtt.take_add_three _ (by rw [hX]; omega),
      rnFold_snoc _ (by rw [List.length_take, hX]; omega)]
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejNtt.chunk_ok (b₀ := X.getD (3 * t) 0) (b₁ := X.getD (3 * t + 1) 0)
    (b₂ := X.getD (3 * t + 2) 0) (by rw [e0, hb 0 (by omega)]; rfl) (hb 1 (by omega)) (hb 2 (by omega))
    (by rw [e0]; exact hin 0 (by omega)) (hin 1 (by omega)) (hin 2 (by omega)) h.x10)
    fun s₁ ⟨o₁, x2, x5, x11⟩ => ?_)
  have hz : rnZ (X.getD (3 * t) 0) (X.getD (3 * t + 1) 0) (X.getD (3 * t + 2) 0) < 2 ^ 23 := by
    unfold rnZ
    have := (X.getD (3 * t) 0).isLt
    have := (X.getD (3 * t + 1) 0).isLt
    simp only [Nat.reducePow] at *
    omega
  have g3 : s₁.gpr .x3 = s.gpr .x3 := o₁.get .x3
  have g4 : s₁.gpr .x4 = s.gpr .x4 := o₁.get .x4
  have g9 : s₁.gpr .x9 = s.gpr .x9 := o₁.get .x9
  have g10 : s₁.gpr .x10 = s.gpr .x10 := o₁.get .x10
  have n2 : s₁.gpr .x2 = bP + BitVec.ofNat 64 (3 * (t + 1)) := by
    rw [x2, h.x2, show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl, ptr_add, Nat.mul_succ]
  have n5 : (s₁.gpr .x5).toNat = 336 - (t + 1) := by
    rw [x5, toNat_sub_n (by rw [h.x5]; simp; omega), h.x5]; simp; omega
  have c : (s₁.gpr .x5).toNat ≠ 0 ↔ t + 1 ≠ 336 := by rw [n5]; omega
  have hl := VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt_length_le X t
  by_cases hf : (VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt X t).length = 256
  · refine WP.ite true (by rw [VG.Proof.MlKem.AArch64.eval_zero, eq_zero_iff, g4, h.x4, hf]; rfl) (fun _ => wp_nil ?_)
      (fun h => nomatch h)
    have e : VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt X (t + 1) = VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt X t := by
      rw [hL, rnStep, ite_eq_right (by simp only [VG.Spec.MlDsa.n]; omega)]
    exact ⟨⟨(h.keep.trans o₁.keep).mono, by rw [o₁.mem]; exact h.frame, n2, by rw [e, g3, h.x3],
      by rw [e, g4, h.x4], n5, by rw [g9, h.x9], by rw [g10, h.x10],
      by rw [e, o₁.mem]; exact h.st⟩, c⟩
  · refine WP.ite false (by rw [VG.Proof.MlKem.AArch64.eval_zero, eq_zero_iff, g4, h.x4]; simp; omega)
      (fun h => nomatch h) (fun _ => WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejNtt.accept_ok (L := VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt X t) (aP := aP) x11 hz (by rw [g9, h.x9])
        (by rw [g3, h.x3]) (by rw [g4, h.x4]) (by omega) (by rw [o₁.mem]; exact h.st)
        (by rw [o₁.wr, h.keep.wr]; exact hp.ina _ (by omega))) fun s₂ ⟨k₂, f₂, x3, x4, st⟩ => ?_)
    have e : VG.Proof.MlDsa.AArch64.Sample.RejNtt.acc (VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt X t) (rnZ (X.getD (3 * t) 0) (X.getD (3 * t + 1) 0) (X.getD (3 * t + 2) 0)) =
        VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt X (t + 1) := by
      rw [hL, rnStep, ite_eq_left (by simp only [VG.Spec.MlDsa.n]; omega)]
    rw [e] at x3 x4 st
    exact ⟨⟨((h.keep.trans o₁.keep).trans k₂).mono, h.frame.trans (by rw [← o₁.mem]; exact f₂),
      by rw [k₂.get .x2, n2], x3, x4, by rw [k₂.get .x5, n5], by rw [k₂.get .x9, g9, h.x9],
      by rw [k₂.get .x10, g10, h.x10], st⟩, by rw [k₂.get .x5]; exact c⟩


/-- `q` into `r`. -/
theorem movQ_ok {r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [r] s s' → (s'.gpr r).toNat = q → WP isa (.block is) s' Q) :
    WP isa (.block (movQ r ++ is)) s Q := by
  refine wp_movz fun s₁ h₁ e₁ => wp_movk1 fun s₂ h₂ e₂ => k s₂ ((h₁.trans h₂).mono fun _ h => by
    simp only [List.mem_append, List.mem_singleton, or_self] at h; simp [h]) ?_
  rw [e₂, e₁]; rfl

/-- The 336 iterations, from the loop's setup: the coefficients `rnFold`
samples from the 1008 bytes stored. -/
theorem loop_ok {X : List Byte} (hX : X.length = 1008) {bP aP : Addr} {s₀ : State} (hp : VG.Proof.MlDsa.AArch64.Sample.RejNtt.LPre X bP aP s₀) :
    WP isa rnLoop s₀ (VG.Proof.MlDsa.AArch64.Sample.RejNtt.LAt X bP aP s₀ 336) := by
  refine WP.seq (wp_addImm (by decide) fun s₁ h₁ e₁ => wp_mov fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ =>
    wp_movz fun s₄ h₄ e₄ => VG.Proof.MlDsa.AArch64.Sample.RejNtt.movQ_ok fun s₅ h₅ e₅ => wp_movz fun s₆ h₆ e₆ => wp_nil ?_)
  have k₆ := (((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans h₆.keep)
  have m₆ : s₆.mem = s₀.mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have i₀ : VG.Proof.MlDsa.AArch64.Sample.RejNtt.LAt X bP aP s₀ 0 s₆ := ⟨k₆.mono, by rw [m₆]; exact Frame.refl _ _,
    by rw [h₆.get .x2, h₅.get .x2, h₄.get .x2, h₃.get .x2, h₂.get .x2, e₁, hp.x25, Nat.mul_zero, ptr_zero],
    by rw [h₆.get .x3, h₅.get .x3, h₄.get .x3, h₃.get .x3, e₂, h₁.get .x26, hp.x26]
       simp [coeffAddr, VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt, rnFold],
    by rw [h₆.get .x4, h₅.get .x4, h₄.get .x4, e₃]; simp [VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt, rnFold],
    by rw [h₆.get .x5, h₅.get .x5, e₄]; rfl, by rw [h₆.get .x9, e₅],
    by rw [e₆]; rfl, by simp only [VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt, Nat.mul_zero, List.take_zero, rnFold]; exact stored_nil _ _⟩
  exact count_loop (by decide) (VG.Proof.MlDsa.AArch64.Sample.RejNtt.LAt X bP aP s₀) (fun t ht s h => VG.Proof.MlDsa.AArch64.Sample.RejNtt.step_ok hX hp ht h) i₀

/-- The coefficients sampled from the 1008 bytes, after the loop. -/
theorem Lt_336 {X : List Byte} (hX : X.length = 1008) : VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt X 336 = rnFold [] X := by
  simp only [VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt]; rw [List.take_of_length_le (by rw [hX])]

end VG.Proof.MlDsa.AArch64.Sample.RejNtt

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rel`. -/
section

/-!
# ML-DSA on AArch64: constant time of the sampling functions, piece by piece

Two runs of a sampling function, from entry states `σ₁` and `σ₂` that satisfy
the precondition and agree on what is public, are related at each point by
what correctness proves of each (`Rel2 Pre Pub J`: `J σᵢ sᵢ`). A piece of code
leaks the same in both runs, and takes them from `J` to `J'`, if the taint
analysis proves it constant time from registers that `J` makes equal
(`relTaint`), or if it only touches memory on which both runs agree, where
`memTaint` does (`relMem`); by determinism, the runs then end in states that
correctness describes (`relStep`).
-/

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64

/-- Two runs, from entry states `σ₁` and `σ₂` related by `Pre` and `Pub`,
in the states that `J` describes. -/
def Rel2 (Pre : State → Prop) (Pub : State → State → Prop) (J : State → State → Prop)
    (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂, Pre σ₁ ∧ Pre σ₂ ∧ Pub σ₁ σ₂ ∧ J σ₁ s₁ ∧ J σ₂ s₂

section
variable {Pre : State → Prop} {Pub : State → State → Prop}

/-- A piece that leaks the same from runs related by `J`, and takes each
run from `J` to `J'`. -/
theorem relStep {J J' : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, Pre σ → J σ s → WP isa c s (J' σ))
    (ht : RelCT isa (VG.Proof.MlDsa.AArch64.Sample.Rel2 Pre Pub J) c fun _ _ => True) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sample.Rel2 Pre Pub J) c (VG.Proof.MlDsa.AArch64.Sample.Rel2 Pre Pub J') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hq, j₁, j₂⟩ := h
  refine ⟨(ht _ _ _ _ _ _ ⟨σ₁, σ₂, p₁, p₂, hq, j₁, j₂⟩ e₁ e₂).1, σ₁, σ₂, p₁, p₂, hq, ?_, ?_⟩
  · obtain ⟨_, _, f, g⟩ := hw σ₁ s₁ p₁ j₁
    obtain ⟨-, rfl⟩ := Exec.det e₁ f
    exact g
  · obtain ⟨_, _, f, g⟩ := hw σ₂ s₂ p₂ j₂
    obtain ⟨-, rfl⟩ := Exec.det e₂ f
    exact g

/-- Code the taint analysis proves constant time from the registers `rs`,
which agree in runs related by `J`. -/
theorem relTaint {J : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ σ₁ σ₂ s₁ s₂, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → J σ₁ s₁ → J σ₂ s₂ →
      s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sample.Rel2 Pre Pub J) c fun _ _ => True :=
  RelCT.taint (A := taint) _ (fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, j₁, j₂⟩ =>
    let ⟨hsp, hrs⟩ := hr σ₁ σ₂ s₁ s₂ p₁ p₂ hq j₁ j₂
    Proof.MlKem.AArch64.agree_of hsp hrs) h

theorem vectorRelTaint {J : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ σ₁ σ₂ s₁ s₂, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → J σ₁ s₁ → J σ₂ s₂ →
      s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    {hc : VG.Taint.Hint VectorTaint.T} (h : (VectorTaint.taint.check (VectorTaint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sample.Rel2 Pre Pub J) c fun _ _ => True :=
  VectorTaint.relCT _ (fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, j₁, j₂⟩ =>
    let ⟨hsp, hrs⟩ := hr σ₁ σ₂ s₁ s₂ p₁ p₂ hq j₁ j₂
    Proof.MlKem.AArch64.agree_of hsp hrs) h

/-- `relStep` of `relTaint`. -/
theorem relTaintStep {J J' : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hw : ∀ σ s, Pre σ → J σ s → WP isa c s (J' σ))
    (hr : ∀ σ₁ σ₂ s₁ s₂, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → J σ₁ s₁ → J σ₂ s₂ →
      s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sample.Rel2 Pre Pub J) c (VG.Proof.MlDsa.AArch64.Sample.Rel2 Pre Pub J') :=
  VG.Proof.MlDsa.AArch64.Sample.relStep hw (VG.Proof.MlDsa.AArch64.Sample.relTaint rs hr h)

theorem vectorRelTaintStep {J J' : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hw : ∀ σ s, Pre σ → J σ s → WP isa c s (J' σ))
    (hr : ∀ σ₁ σ₂ s₁ s₂, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → J σ₁ s₁ → J σ₂ s₂ →
      s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    {hc : VG.Taint.Hint VectorTaint.T} (h : (VectorTaint.taint.check (VectorTaint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sample.Rel2 Pre Pub J) c (VG.Proof.MlDsa.AArch64.Sample.Rel2 Pre Pub J') :=
  VG.Proof.MlDsa.AArch64.Sample.relStep hw (VectorTaint.relRegs rs (fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, j₁, j₂⟩ =>
    hr σ₁ σ₂ s₁ s₂ p₁ p₂ hq j₁ j₂) h)

/-- Code that runs, with permissions only on the regions `rd σ` and `wr σ`
(the same in both runs), on memory both runs agree on there: `memTaint`
proves it constant time from the registers `rs`, which agree. -/
theorem relMem {J : State → State → Prop} {c : Prog isa} (rd wr : State → List Region) (rs : List Reg)
    (hrw : ∀ σ₁ σ₂, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → rd σ₁ = rd σ₂ ∧ wr σ₁ = wr σ₂)
    (hc : ∀ σ s, Pre σ → J σ s → Covers (rd σ ++ wr σ) (s.rd ++ s.wr) ∧ Covers (wr σ) s.wr)
    (hx : ∀ σ s, Pre σ → J σ s → ∃ t s', Exec isa c (s.withRegions (rd σ) (wr σ)) t s')
    (hr : ∀ σ₁ σ₂ s₁ s₂, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → J σ₁ s₁ → J σ₂ s₂ →
      s₁.sp = s₂.sp ∧ (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧
      ∀ x, InRegions (rd σ₁ ++ wr σ₁) x 1 → s₁.mem x = s₂.mem x)
    {hint : VG.Taint.Hint memTaint.T} (h : (memTaint.check (Taint.ofRegs rs) c hint).isSome = true) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sample.Rel2 Pre Pub J) c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hq, j₁, j₂⟩ := hP
  obtain ⟨erd, ewr⟩ := hrw σ₁ σ₂ p₁ p₂ hq
  refine RelCT.narrow (P := fun a b => a = s₁ ∧ b = s₂) (rd σ₁) (wr σ₁)
    (fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      refine ⟨hc σ₁ a p₁ j₁, ?_⟩
      rw [erd, ewr]; exact hc σ₂ b p₂ j₂)
    (fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      refine ⟨hx σ₁ a p₁ j₁, ?_⟩
      rw [erd, ewr]; exact hx σ₂ b p₂ j₂)
    (RelCT.taint (A := memTaint) (Taint.ofRegs rs) (fun u₁ u₂ hu => ?_) h) s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂
  obtain ⟨a, b, ⟨rfl, rfl⟩, rfl, rfl⟩ := hu
  obtain ⟨hsp, hrs, hm⟩ := hr σ₁ σ₂ a b p₁ p₂ hq j₁ j₂
  exact ⟨Proof.MlKem.AArch64.agree_of hsp hrs, rfl, rfl, fun x hx => hm x hx⟩

end

end VG.Proof.MlDsa.AArch64.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNtt`. -/
section

/-!
# ML-DSA on AArch64: `vg_mldsa_rej_ntt_poly`

Correctness: the function runs in pieces, the prologue (`J0`), the sponge,
whose output is `G(ρ, 1008)` (`J6`), `a` set to zeros, the loop, which stores
the coefficients `rnFold` samples from it (`RejNttLoop.lean`), and the end,
which returns whether there are 256 of them. The postcondition of the contract
follows from the prefix lemmas (`rejNTT_some`, `rejNTT_none`).

Constant time up to the seed, relating two runs piece by piece (`Rel.lean`):
the prologue, the sponge, the zeros and the end by the taint analysis, from
registers that correctness makes equal in both runs; the loop by `memTaint`,
since both runs have the same output (a function of the seed, which the
contract lets the function leak) and zeros in `a`, and the loop touches
nothing else.
-/

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep only_write wp_nil wp_subImm wp_lsr ptr_add toNat_lsr toNat_sub_n agree_of)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q G PolyIs coeffAt)
open VG.Spec.Sha3 (bytesAt shakeSuffix)

/-- `vg_mldsa_rej_ntt_poly(seed = x0, a = x1, scratch = x2) -> w0`, with 16
bytes of stack below `sp`: the contract the proof is written against. -/
def rnK : Contract isa where
  pre s :=
    let seed : Region := ⟨s.gpr .x0, 34⟩
    let a : Region := ⟨s.gpr .x1, 1024⟩
    let scratch : Region := ⟨s.gpr .x2, 2048⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [seed] ∧ s.wr = [a, scratch] ∧ seed.Disjoint a ∧ seed.Disjoint scratch ∧
    a.Disjoint scratch ∧ 16 ≤ s.sp.toNat ∧ stack.Disjoint seed ∧ stack.Disjoint a ∧
    stack.Disjoint scratch
  post s s' :=
    (s'.gpr .x0).setWidth 32 =
        (if (rnFold [] (VG.Spec.MlDsa.G (bytesAt s.mem (s.gpr .x0) 34) 1008)).length = 256 then 1 else 0) ∧
      ((rnFold [] (VG.Spec.MlDsa.G (bytesAt s.mem (s.gpr .x0) 34) 1008)).length = 256 →
        PolyIs s'.mem (s.gpr .x1) (toPoly (rnFold [] (VG.Spec.MlDsa.G (bytesAt s.mem (s.gpr .x0) 34) 1008))))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp ∧ bytesAt s₁.mem (s₁.gpr .x0) 34 = bytesAt s₂.mem (s₂.gpr .x0) 34

namespace RejNtt

/-- The call. -/
abbrev spOf (σ : State) : VG.Proof.MlDsa.AArch64.Sample.Sp := ⟨σ.gpr .x0, 34, σ.gpr .x2, σ.gpr .x1, 0⟩

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := VG.Spec.MlDsa.G ((VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOf σ).msg σ) 1008

theorem X_length (σ : State) : (VG.Proof.MlDsa.AArch64.Sample.RejNtt.X σ).length = 1008 := VG.Proof.MlDsa.Sample.G_length _ _

theorem spOk {σ : State} (hp : rnK.pre σ) : VG.Proof.MlDsa.AArch64.Sample.SpOk (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2, by show (34 : Nat) < 2 ^ 64; decide⟩

theorem pro_ok {σ : State} (hp : rnK.pre σ) :
    WP isa (.block (pro .x2 .x1 (.movz .x .x27 0 0) (.movz .x .x4 34 0))) σ (VG.Proof.MlDsa.AArch64.Sample.J0 (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOf σ) σ) :=
  Sample.pro_ok (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOk hp) rfl rfl (by decide) rfl
    (fun s _ => ⟨_, rfl, only_write _ _ _ _, by rfl⟩)
    (fun s _ => ⟨_, rfl, only_write _ _ _ _, by rfl⟩)

/-- After the sponge, and `a` set to zeros. -/
structure Z (σ s : State) : Prop where
  env : VG.Proof.MlDsa.AArch64.Sample.Env (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOf σ) σ s
  out : bytesAt s.mem ((VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOf σ).at' 840) 1008 = VG.Proof.MlDsa.AArch64.Sample.RejNtt.X σ
  zero : ∀ i < 256, coeffAt s.mem (σ.gpr .x1) i = 0

theorem zero_ok {σ s : State} (hp : rnK.pre σ) (h : VG.Proof.MlDsa.AArch64.Sample.J6 168 1008 (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOf σ) σ s) :
    WP isa zeroPoly s (VG.Proof.MlDsa.AArch64.Sample.RejNtt.Z σ) :=
  WP.mono (VG.Proof.MlDsa.AArch64.Sample.zeroPoly_ok (fun i hi => VG.Proof.MlDsa.AArch64.Sample.inA (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOk hp) h.env.wr hi) h.env.x26) fun u ⟨k, z, f⟩ =>
    ⟨h.env.keepA (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOk hp) k f, by
      rw [MlKem.bytesAt_frame f (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (VG.Proof.MlDsa.AArch64.Sample.a_scr' (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOk hp) (by omega)).symm) (by omega), h.out,
        (VG.Proof.MlDsa.Sample.G_eq _ _).symm], z⟩

theorem lpre {σ s : State} (hp : rnK.pre σ) (h : VG.Proof.MlDsa.AArch64.Sample.RejNtt.Z σ s) :
    RejNtt.LPre (VG.Proof.MlDsa.AArch64.Sample.RejNtt.X σ) ((VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOf σ).at' 840) (σ.gpr .x1) s :=
  ⟨fun p hp' => by rw [← h.out, MlKem.bytesAt_getD _ _ hp'],
    fun p hp' => by rw [VG.Proof.MlDsa.AArch64.Sample.at_add]; exact VG.Proof.MlDsa.AArch64.Sample.inScrRd (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOk hp) h.env.rd h.env.wr (by omega),
    fun i hi => VG.Proof.MlDsa.AArch64.Sample.inA (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOk hp) h.env.wr hi, (VG.Proof.MlDsa.AArch64.Sample.a_scr' (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOk hp) (by omega)).symm,
    by rw [h.env.x25], h.env.x26⟩

/-- After the loop. -/
structure LP (σ s : State) : Prop where
  env : VG.Proof.MlDsa.AArch64.Sample.Env (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOf σ) σ s
  x4 : (s.gpr .x4).toNat = 256 - (rnFold [] (VG.Proof.MlDsa.AArch64.Sample.RejNtt.X σ)).length
  st : Stored s.mem (σ.gpr .x1) (rnFold [] (VG.Proof.MlDsa.AArch64.Sample.RejNtt.X σ))

theorem loopP_ok {σ s : State} (hp : rnK.pre σ) (h : VG.Proof.MlDsa.AArch64.Sample.RejNtt.Z σ s) : WP isa rnLoop s (VG.Proof.MlDsa.AArch64.Sample.RejNtt.LP σ) :=
  WP.mono (RejNtt.loop_ok (VG.Proof.MlDsa.AArch64.Sample.RejNtt.X_length σ) (VG.Proof.MlDsa.AArch64.Sample.RejNtt.lpre hp h)) fun u hu => by
    have x4 := hu.x4
    have st := hu.st
    rw [RejNtt.Lt_336 (VG.Proof.MlDsa.AArch64.Sample.RejNtt.X_length σ)] at x4 st
    exact ⟨h.env.keepA (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOk hp) hu.keep hu.frame, x4, st⟩

/-- The end: the postcondition, and the calling convention. -/
theorem end_ok {σ s : State} (hp : rnK.pre σ) (h : VG.Proof.MlDsa.AArch64.Sample.RejNtt.LP σ s) :
    WP isa (.block (retZ ++ epi)) s fun s' => abiPreserved σ s' ∧ rnK.post σ s' := by
  rw [retZ, List.cons_append, List.cons_append, List.nil_append]
  refine wp_subImm (by decide) fun s₁ h₁ e₁ => wp_lsr (by decide) fun s₂ h₂ e₂ => ?_
  have hl := rnFold_length_le (a := ([] : List Zq)) (by simp) (VG.Proof.MlDsa.AArch64.Sample.RejNtt.X σ)
  have v0 : (s₂.gpr .x0).toNat = if (rnFold [] (VG.Proof.MlDsa.AArch64.Sample.RejNtt.X σ)).length = 256 then 1 else 0 := by
    have one : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [e₂, toNat_lsr, e₁, BitVec.toNat_sub, h.x4, one]
    simp only [VG.Spec.MlDsa.n, Nat.reducePow] at hl ⊢
    split <;> omega
  have e1 := (h.env.keep (h₁.keep.trans h₂.keep) (by rw [h₂.mem, h₁.mem]))
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.epi_ok (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOk hp) e1) fun s' ⟨abi, m, k⟩ => ⟨abi, ?_, fun hf => ?_⟩
  · rw [k.get .x0]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, v0]
    split <;> rfl
  · rw [m, h₂.mem, h₁.mem]
    exact stored_polyIs h.st hf

theorem correctWith (v : Proof.Sha3.AArch64.Permutation) (σ : State) (hp : rnK.pre σ) :
    ∃ t s', Exec isa (rejNTTWith v.callee) σ t s' ∧ abiPreserved σ s' ∧ rnK.post σ s' :=
  WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejNtt.pro_ok hp) fun _ h1 =>
    WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.spongeWith_ok (v := v) (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOk hp) (rate := 168) (outlen := 1008) (by decide) (by decide) h1)
      fun _ h2 => WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejNtt.zero_ok hp h2) fun _ h3 =>
        WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejNtt.loopP_ok hp h3) fun _ h4 => VG.Proof.MlDsa.AArch64.Sample.RejNtt.end_ok hp h4))))

theorem correct (σ : State) (hp : rnK.pre σ) :
    ∃ t s', Exec isa rejNTT σ t s' ∧ abiPreserved σ s' ∧ rnK.post σ s' :=
  VG.Proof.MlDsa.AArch64.Sample.RejNtt.correctWith .scalar σ hp

end RejNtt

end VG.Proof.MlDsa.AArch64.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT`. -/
section

/-!
# ML-DSA on AArch64: `vg_mldsa_rej_ntt_poly`, constant time and verified

Two runs whose seeds and pointers agree leak the same (`RejNtt.ct`), piece by
piece (`Rel.lean`), and the shared contract follows from `rnK`
(`rejNTT_verified`).
-/

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q G PolyIs coeffAt)
open VG.Spec.Sha3 (bytesAt)

/-- Registers whose values are equal. -/
theorem regs_eq {s₁ s₂ : State} {rs : List Reg} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    ∀ r ∈ rs, s₁.gpr r = s₂.gpr r := h

theorem toNat_inj {a b : BitVec 64} {n : Nat} (ha : a.toNat = n) (hb : b.toNat = n) : a = b :=
  BitVec.eq_of_toNat_eq (ha.trans hb.symm)

/-- The bytes of a polynomial of zeros are zero. -/
theorem byte_zero {m : Mem} {p : Addr} (h : ∀ i < 256, coeffAt m p i = 0) {y : Addr}
    (hy : (polyR p).Contains y 1) : m y = 0 :=
  Proof.MlKem.AArch64.Sample.byte_zero (p := p) (fun i hi => h i hi) hy

namespace RejNtt

/-- The loop's regions. -/
abbrev lrd (σ : State) : List Region := [⟨(VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOf σ).at' 840, 1008⟩]
abbrev lwr (σ : State) : List Region := [polyR (σ.gpr .x1)]

theorem pub_msg {σ₁ σ₂ : State} (hq : rnK.pub σ₁ σ₂) : (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOf σ₁).msg σ₁ = (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOf σ₂).msg σ₂ := hq.2.2.2.2

theorem pub_eq {σ₁ σ₂ : State} (hq : rnK.pub σ₁ σ₂) : VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOf σ₁ = VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOf σ₂ := by
  rw [VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOf, VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOf, hq.1, hq.2.1, hq.2.2.1]

theorem X_eq {σ₁ σ₂ : State} (hq : rnK.pub σ₁ σ₂) : VG.Proof.MlDsa.AArch64.Sample.RejNtt.X σ₁ = VG.Proof.MlDsa.AArch64.Sample.RejNtt.X σ₂ := by
  simp only [VG.Proof.MlDsa.AArch64.Sample.RejNtt.X, Sp.msg]; rw [hq.2.2.2.2]

theorem loop_ct : RelCT isa (VG.Proof.MlDsa.AArch64.Sample.Rel2 rnK.pre rnK.pub VG.Proof.MlDsa.AArch64.Sample.RejNtt.Z) rnLoop fun _ _ => True := by
  refine VG.Proof.MlDsa.AArch64.Sample.relMem VG.Proof.MlDsa.AArch64.Sample.RejNtt.lrd VG.Proof.MlDsa.AArch64.Sample.RejNtt.lwr [.x25, .x26]
    (fun σ₁ σ₂ _ _ hq => by simp [VG.Proof.MlDsa.AArch64.Sample.RejNtt.lrd, VG.Proof.MlDsa.AArch64.Sample.RejNtt.lwr, VG.Proof.MlDsa.AArch64.Sample.RejNtt.pub_eq hq, hq.2.1]) (fun σ s hp h => ?_)
    (fun σ s hp h => ?_) (fun σ₁ σ₂ s₁ s₂ p₁ p₂ hq h₁ h₂ => ?_) (by taint_decide)
  · rw [VG.Proof.MlDsa.AArch64.Sample.regions (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOk hp) h.env]
    refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
    · rcases VG.Proof.MlDsa.AArch64.Sample.mem2 hr with rfl | rfl
      · exact ⟨(VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOf σ).scrR, by simp, 840, rfl, by simp⟩
      · exact ⟨polyR (σ.gpr .x1), by simp, 0, (Proof.MlKem.AArch64.ptr_zero _).symm, by simp⟩
    · rw [List.mem_singleton.mp hr, h.env.wr, (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOk hp).wr]
      exact ⟨polyR (σ.gpr .x1), by simp, 0, (Proof.MlKem.AArch64.ptr_zero _).symm, by simp⟩
  · have l := VG.Proof.MlDsa.AArch64.Sample.RejNtt.lpre hp h
    obtain ⟨t, u, e, -⟩ := RejNtt.loop_ok (VG.Proof.MlDsa.AArch64.Sample.RejNtt.X_length σ) (s₀ := s.withRegions (VG.Proof.MlDsa.AArch64.Sample.RejNtt.lrd σ) (VG.Proof.MlDsa.AArch64.Sample.RejNtt.lwr σ))
      ⟨l.buf, fun p hp' => Proof.MlKem.AArch64.in_rd (Proof.MlKem.AArch64.in_regions
        (List.mem_singleton_self _) (Offset.contains_base _ (by omega) (by omega))),
        fun i hi => Proof.MlKem.AArch64.in_regions (List.mem_singleton_self _) (coeff_contains _ hi),
        l.disj, l.x25, l.x26⟩
    exact ⟨t, u, e⟩
  · refine ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.1], fun r hr => ?_, fun x hx => ?_⟩
    · rcases VG.Proof.MlDsa.AArch64.Sample.mem2 hr with rfl | rfl
      · rw [h₁.env.x25, h₂.env.x25, VG.Proof.MlDsa.AArch64.Sample.RejNtt.pub_eq hq]
      · rw [h₁.env.x26, h₂.env.x26, VG.Proof.MlDsa.AArch64.Sample.RejNtt.pub_eq hq]
    · obtain ⟨R, hR, hc⟩ := hx
      rcases VG.Proof.MlDsa.AArch64.Sample.mem2 hR with rfl | rfl
      · obtain ⟨p, hp', rfl⟩ := Proof.MlKem.AArch64.Sample.at_off hc
        rw [← MlKem.bytesAt_getD s₁.mem _ hp', h₁.out, VG.Proof.MlDsa.AArch64.Sample.RejNtt.pub_eq hq, ← MlKem.bytesAt_getD s₂.mem _ hp', h₂.out, VG.Proof.MlDsa.AArch64.Sample.RejNtt.X_eq hq]
      · rw [VG.Proof.MlDsa.AArch64.Sample.byte_zero h₁.zero hc, VG.Proof.MlDsa.AArch64.Sample.byte_zero h₂.zero (by rw [← hq.2.1]; exact hc)]

theorem regs3 {s₁ s₂ : State} {a b c : Reg} (ha : s₁.gpr a = s₂.gpr a) (hb : s₁.gpr b = s₂.gpr b)
    (hc : s₁.gpr c = s₂.gpr c) : ∀ r ∈ [a, b, c], s₁.gpr r = s₂.gpr r := fun r hr => by
  rcases VG.Proof.MlDsa.AArch64.Sample.mem3 hr with rfl | rfl | rfl <;> with_reducible assumption

theorem ctWith (v : Proof.Sha3.AArch64.Permutation) : ConstantTime isa rnK.pre rnK.pub (rejNTTWith v.callee) := by
  obtain ⟨hint, hhint⟩ := v.mldsaNttTaint
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.mono (Q := fun _ _ => True) (P := VG.Proof.MlDsa.AArch64.Sample.Rel2 rnK.pre rnK.pub fun σ s => s = σ)
    ?_ (fun s₁ s₂ h => ⟨s₁, s₂, h.1, h.2.1, h.2.2, rfl, rfl⟩) fun _ _ _ => trivial)
  refine RelCT.seq (VG.Proof.MlDsa.AArch64.Sample.relTaintStep (J' := fun σ => VG.Proof.MlDsa.AArch64.Sample.J0 (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOf σ) σ) [.x0, .x1, .x2]
    (fun σ s hp h => by subst h; exact VG.Proof.MlDsa.AArch64.Sample.RejNtt.pro_ok hp) (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      subst h₁ h₂; exact ⟨hq.2.2.2.1, VG.Proof.MlDsa.AArch64.Sample.RejNtt.regs3 hq.1 hq.2.1 hq.2.2.1⟩) (by taint_decide)) ?_
  refine RelCT.seq (VG.Proof.MlDsa.AArch64.Sample.vectorRelTaintStep (J' := fun σ => VG.Proof.MlDsa.AArch64.Sample.J6 168 1008 (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOf σ) σ) [.x25, .x26, .x27, .x3, .x4]
    (fun σ s hp h => VG.Proof.MlDsa.AArch64.Sample.spongeWith_ok (v := v) (VG.Proof.MlDsa.AArch64.Sample.RejNtt.spOk hp) (by decide) (by decide) h) (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      refine ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.1], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.env.x25, h₂.env.x25, VG.Proof.MlDsa.AArch64.Sample.RejNtt.pub_eq hq]
      · rw [h₁.env.x26, h₂.env.x26, VG.Proof.MlDsa.AArch64.Sample.RejNtt.pub_eq hq]
      · rw [h₁.env.x27, h₂.env.x27, VG.Proof.MlDsa.AArch64.Sample.RejNtt.pub_eq hq]
      · rw [h₁.x3, h₂.x3, VG.Proof.MlDsa.AArch64.Sample.RejNtt.pub_eq hq]
      · exact VG.Proof.MlDsa.AArch64.Sample.toNat_inj h₁.x4 h₂.x4) hhint) ?_
  refine RelCT.seq (VG.Proof.MlDsa.AArch64.Sample.relTaintStep (J' := VG.Proof.MlDsa.AArch64.Sample.RejNtt.Z) [.x26] (fun σ s hp h => VG.Proof.MlDsa.AArch64.Sample.RejNtt.zero_ok hp h)
    (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.1], fun r hr => by
      rw [List.mem_singleton.mp hr, h₁.env.x26, h₂.env.x26, VG.Proof.MlDsa.AArch64.Sample.RejNtt.pub_eq hq]⟩) (by taint_decide)) ?_
  refine RelCT.seq (VG.Proof.MlDsa.AArch64.Sample.relStep (J' := VG.Proof.MlDsa.AArch64.Sample.RejNtt.LP) (fun σ s hp h => VG.Proof.MlDsa.AArch64.Sample.RejNtt.loopP_ok hp h) VG.Proof.MlDsa.AArch64.Sample.RejNtt.loop_ct) ?_
  exact VG.Proof.MlDsa.AArch64.Sample.relTaint [.x25] (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.1],
    fun r hr => by rw [List.mem_singleton.mp hr, h₁.env.x25, h₂.env.x25, VG.Proof.MlDsa.AArch64.Sample.RejNtt.pub_eq hq]⟩) (by taint_decide)

theorem ct : ConstantTime isa rnK.pre rnK.pub rejNTT :=
  VG.Proof.MlDsa.AArch64.Sample.RejNtt.ctWith .scalar

end RejNtt

end VG.Proof.MlDsa.AArch64.Sample

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (G)
open VG.Spec.Sha3 (bytesAt)

/-- A state satisfying the precondition. -/
def rnSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 34⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem rejNTT_verifiedWith (v : Proof.Sha3.AArch64.Permutation) :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sample.rejNTTWith v.callee) (Spec.MlDsa.rejNTTContract AArch64.abi 16) :=
  Verified.of_correct (RejNtt.correctWith v) (RejNtt.ctWith v)
    { pre := by sig_implies_pre [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, VG.Proof.MlDsa.AArch64.Sample.rnK, AArch64.abi,
        AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, VG.Proof.MlDsa.AArch64.Sample.rnK, AArch64.abi, AArch64.argRegs]
        dsimp only [VG.Proof.MlDsa.AArch64.Sample.rnK] at h
        obtain ⟨hr, hp⟩ := h
        by_cases hf : (rnFold [] (VG.Spec.MlDsa.G (bytesAt s.mem (s.gpr .x0) 34) 1008)).length = 256
        · rw [ifT hf] at hr
          obtain ⟨hred, hpoly⟩ := hp hf
          exact ⟨fun _ => hred, .inl ⟨hr, { Spec.MlDsa.minBounds with rejNTT := 1008 }, by
            show Spec.MlDsa.rejNTTPoly 1008 _ = _
            rw [rejNTT_some hf, hpoly]⟩⟩
        · rw [ifF hf] at hr
          exact ⟨fun h1 => absurd (hr.symm.trans h1) (by decide),
            .inr ⟨hr, rejNTT_none (B := 1008) (by decide) (by decide) hf⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, VG.Proof.MlDsa.AArch64.Sample.rnK, AArch64.abi, AArch64.argRegs] at h
        obtain ⟨hsp, hb, hx0, hx1, hx2⟩ := h
        exact ⟨hx0, hx1, hx2, hsp, VG.Proof.MlKem.map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, VG.Proof.MlDsa.AArch64.Sample.rnK, AArch64.abi,
        AArch64.argRegs] [rnSat] using VG.Proof.MlDsa.AArch64.Sample.rnSat }

theorem rejNTT_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Sample.rejNTT (Spec.MlDsa.rejNTTContract AArch64.abi 16) :=
  VG.Proof.MlDsa.AArch64.Sample.rejNTT_verifiedWith .scalar

end VG.Proof.MlDsa.AArch64.Sample

end
