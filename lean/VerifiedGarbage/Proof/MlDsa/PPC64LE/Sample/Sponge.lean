module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.Common
public import VerifiedGarbage.Proof.MlKem.PPC64LE.KCall
public import VerifiedGarbage.Proof.MlDsa.Sample.Hash
public import VerifiedGarbage.Proof.MlDsa.Sample.Mem
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Verified
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.CT
meta import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.Common
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.KCall
meta import VerifiedGarbage.Proof.MlDsa.Sample.Hash
meta import VerifiedGarbage.Proof.MlDsa.Sample.Mem
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Verified
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.CT

/-!
# ML-DSA on PPC64LE: the sampling functions' SHAKE

What the sampling functions share (`Impl/MlDsa/PPC64LE/Sample/Common.lean`),
for any of them, as on 32-bit ARM (`Proof/MlDsa/Arm/Sample/Sponge.lean`): a
call is described by `Sp` (the message, its length, the working space
`scratch` and the output polynomial), whose regions are laid out as `SpOk`
says of the entry state. From the prologue on, `Env` holds: `r30` is the
output polynomial and `r31` the working space, our caller's `r27`–`r31` and
`lr` are saved at `scratch + 2000`, the callee-saved registers but those are
our caller's, and the memory has changed only in the output polynomial, the
working space and the 48 bytes below the stack pointer. `sponge` then leaves
`outlen` bytes of SHAKE of the message at `scratch + 840` (`sponge_ok`, from
`J0` to `J6`), keeping the callee-saved registers, and two runs of it from
calls that agree leak the same (`sponge_ct`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample

open VG VG.PPC64LE
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Proof.MlKem.PPC64LE (AbsorbArgs PadArgs SqueezeArgs absorb_call pad_call squeeze_call absorb_pre
  pad_pre squeeze_pre ce_gpr relct_noMem noMem)
open VG.Proof.MlKem.PPC64LE.Sample (zeroLanes_ok stateAt_zero shakeSuffix64 gpr_write_pres readW_writeW_off
  taint_block relct_wp)
open VG.Impl.MlKem.PPC64LE (zeroState)
open VG.Spec.Sha3 (bytesAt stateAt rates squeezeFrom Repr)
open VG.Proof.MlDsa.Sample (padded polyR)

/-- A call of a sampling function. -/
structure Sp where
  /-- The message hashed. -/
  sd : Addr
  len : Nat
  /-- `scratch`. -/
  scr : Addr
  /-- The output polynomial. -/
  a : Addr

namespace Sp
variable (P : Sp)
/-- `scratch + off`. -/
abbrev at' (off : Nat) : Addr := P.scr + BitVec.ofNat 64 off
abbrev scrR : Region := ⟨P.scr, 2048⟩
abbrev sdR : Region := ⟨P.sd, P.len⟩
abbrev aR : Region := polyR P.a
/-- The message. -/
abbrev msg (σ : State) : List Byte := bytesAt σ.mem P.sd P.len
end Sp

/-- The regions of a call, from the entry state `σ`. -/
structure SpOk (P : Sp) (σ : State) : Prop where
  rd : P.sdR ∈ σ.rd
  wr : σ.wr = [P.aR, P.scrR]
  sd_a : P.sdR.Disjoint P.aR
  sd_scr : P.sdR.Disjoint P.scrR
  a_scr : P.aR.Disjoint P.scrR
  b_sd : (below σ.sp 48).Disjoint P.sdR
  b_a : (below σ.sp 48).Disjoint P.aR
  b_scr : (below σ.sp 48).Disjoint P.scrR
  len_lt : P.len < 2 ^ 64
  fa : P.a.toNat + 1024 ≤ 2 ^ 64
  fscr : P.scr.toNat + 2048 ≤ 2 ^ 64
  sp48 : 48 ≤ σ.sp.toNat

/-- What holds from the prologue on, relative to the entry state `σ`. -/
structure Env (P : Sp) (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  r30 : s.gpr .r30 = P.a
  r31 : s.gpr .r31 = P.scr
  cs : ∀ r ∈ preserved, r ≠ .r27 → r ≠ .r28 → r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → s.gpr r = σ.gpr r
  s27 : s.mem.readW (P.at' 2000) 64 = σ.gpr .r27
  s28 : s.mem.readW (P.at' 2008) 64 = σ.gpr .r28
  s29 : s.mem.readW (P.at' 2016) 64 = σ.gpr .r29
  s30 : s.mem.readW (P.at' 2024) 64 = σ.gpr .r30
  s31 : s.mem.readW (P.at' 2032) 64 = σ.gpr .r31
  slr : s.mem.readW (P.at' 2040) 64 = σ.lr
  frame : Frame [P.aR, P.scrR, below σ.sp 48] σ.mem s.mem

/-- Where a piece of code may write, keeping `Env`: the working space below
the saved registers, the output polynomial and the 48 bytes below the stack
pointer. -/
def Sp.Wr (P : Sp) (σ : State) (r : Region) : Prop :=
  Region.Sub r ⟨P.scr, 2000⟩ ∨ Region.Sub r P.aR ∨ Region.Sub r (below σ.sp 48)

theorem pres_of {r : Reg} (h : r ∈ preserved) : r ≠ .r0 := by
  rintro rfl; exact absurd h (by decide)

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

omit hp in
theorem sub_scr {a n : Nat} (h : a + n ≤ 2048) : Region.Sub ⟨P.at' a, n⟩ P.scrR := Offset.sub_base _ h

/-- A part of the working space is writable. -/
theorem inScr {s : State} (hwr : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 2048) :
    InRegions s.wr (P.at' a) n := by
  rw [hwr, hp.wr]
  exact ⟨P.scrR, by simp, Offset.contains_base _ h (by have := hp.fscr; omega)⟩

theorem inScrRd {s : State} (hwr : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 2048) :
    InRegions (s.rd ++ s.wr) (P.at' a) n := by
  obtain ⟨r, hr, hc⟩ := inScr hp hwr h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- The saved registers are apart from where code may write. -/
theorem sav_disj {r : Region} (h : P.Wr σ r) : (⟨P.at' 2000, 48⟩ : Region).Disjoint r := by
  have := hp.fscr
  rcases h with h | h | h
  · exact (Offset.disjoint_base P.scr (d := 2000) (n := 48) (k := 2000) (Nat.le_refl _) (by omega)).sub_right h
  · exact (hp.a_scr.sub_right (sub_scr (a := 2000) (n := 48) (by omega))).symm.sub_right h
  · exact (hp.b_scr.sub_right (sub_scr (a := 2000) (n := 48) (by omega))).symm.sub_right h

/-- A saved doubleword through writes where code may write. -/
theorem sav_read {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hrs : ∀ r ∈ rs, P.Wr σ r) {d : Nat}
    (h₁ : 2000 ≤ d) (h₂ : d + 8 ≤ 2048) : m'.readW (P.at' d) 64 = m.readW (P.at' d) 64 :=
  hf.readW (Offset.contains _ h₁ (by omega) (by have := hp.fscr; omega)) (fun r hr => sav_disj hp (hrs r hr))
    (by decide)

/-- `Env` after writes where code may write, keeping the callee-saved registers. -/
theorem Env.step {s s' : State} (he : Env P σ s) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hrs : ∀ r ∈ rs, P.Wr σ r) (gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r) (rd : s'.rd = s.rd)
    (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : Env P σ s' := by
  refine ⟨rd.trans he.rd, wr.trans he.wr, sp.trans he.sp, (gp _ (by decide)).trans he.r30,
    (gp _ (by decide)).trans he.r31, fun r hr a b c d e => (gp r hr).trans (he.cs r hr a b c d e),
    (sav_read hp hf hrs (by omega) (by omega)).trans he.s27, (sav_read hp hf hrs (by omega) (by omega)).trans he.s28,
    (sav_read hp hf hrs (by omega) (by omega)).trans he.s29, (sav_read hp hf hrs (by omega) (by omega)).trans he.s30,
    (sav_read hp hf hrs (by omega) (by omega)).trans he.s31, (sav_read hp hf hrs (by omega) (by omega)).trans he.slr,
    he.frame.trans (hf.sub fun r hr => ?_)⟩
  rcases hrs r hr with h | h | h
  · exact ⟨P.scrR, by simp, fun x hx => Region.sub_prefix (base := P.scr) (by decide : 2000 ≤ 2048) x (h x hx)⟩
  · exact ⟨P.aR, by simp, h⟩
  · exact ⟨below σ.sp 48, by simp, h⟩

/-- `Env` after a block that writes no memory and no callee-saved register. -/
theorem Env.regs {s s' : State} (he : Env P σ s) (hm : s'.mem = s.mem) (gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : Env P σ s' :=
  he.step hp (rs := []) (by rw [hm]; exact Frame.refl _ _) (fun _ h => absurd h List.not_mem_nil) gp rd wr sp

/-- The message is not written. -/
theorem msg_frame {s : State} (he : Env P σ s) : bytesAt s.mem P.sd P.len = P.msg σ :=
  MlKem.bytesAt_frame he.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.sd_a, hp.sd_scr, hp.b_sd.symm]) (by have := hp.len_lt; omega)

omit hp in
/-- A part of the working space below the saved registers. -/
theorem wr_scr {a n : Nat} (h : a + n ≤ 2000) : P.Wr σ ⟨P.at' a, n⟩ := .inl (Offset.sub_base _ h)

omit hp in
theorem wr_scr0 {n : Nat} (h : n ≤ 2000) : P.Wr σ ⟨P.scr, n⟩ := .inl (Region.sub_prefix h)

omit hp in
theorem wr_below {s : State} (h : s.sp = σ.sp) : P.Wr σ (below s.sp 48) := .inr (.inr (by rw [h]; exact fun _ h => h))

end

/-! ## The sponge -/

/-- The registers of the sponge's arguments: the message in `r29` and its
length in `r28`. -/
structure J0 (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  r29 : s.gpr .r29 = P.sd
  r28 : s.gpr .r28 = BitVec.ofNat 64 P.len

theorem J0.step {P : Sp} {σ s s' : State} (hp : SpOk P σ) (h : J0 P σ s) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hrs : ∀ r ∈ rs, P.Wr σ r) (gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : J0 P σ s' :=
  ⟨h.env.step hp hf hrs gp rd wr sp, (gp _ (by decide)).trans h.r29, (gp _ (by decide)).trans h.r28⟩

theorem J0.regs {P : Sp} {σ s s' : State} (hp : SpOk P σ) (h : J0 P σ s) (hm : s'.mem = s.mem)
    (gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) :
    J0 P σ s' :=
  ⟨h.env.regs hp hm gp rd wr sp, (gp _ (by decide)).trans h.r29, (gp _ (by decide)).trans h.r28⟩

/-- After zeroing the state: the arguments of `absorb`. -/
structure J1 (rate : Nat) (P : Sp) (σ s₀ s : State) : Prop where
  j0 : J0 P σ s
  gp : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  zero : stateAt s.mem P.scr = Spec.Sha3.zero
  args : AbsorbArgs s P.scr P.sd (P.at' 200) rate 0 P.len

theorem rate_pos {rate : Nat} (h : rate ∈ rates) : 0 < rate := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem rate_lt {rate : Nat} (h : rate ∈ rates) : rate < 32768 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem st_disj : Region.Disjoint ⟨P.scr, 200⟩ ⟨P.at' 200, 640⟩ :=
  Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.fscr; omega)

theorem stk_scr {s : State} (hsp : s.sp = σ.sp) {o n : Nat} (h : o + n ≤ 2048) :
    (below s.sp 48).Disjoint ⟨P.at' o, n⟩ := by
  rw [hsp]; exact hp.b_scr.sub_right (sub_scr h)

theorem stk_scr0 {s : State} (hsp : s.sp = σ.sp) {n : Nat} (h : n ≤ 2048) :
    (below s.sp 48).Disjoint ⟨P.scr, n⟩ := by
  rw [hsp]; exact hp.b_scr.sub_right (Region.sub_prefix h)

theorem absArgs_of {rate : Nat} (hr : rate ∈ rates) {s : State} (he : Env P σ s) (g3 : s.gpr .r3 = P.scr)
    (g4 : s.gpr .r4 = BitVec.ofNat 64 rate) (g5 : s.gpr .r5 = BitVec.ofNat 64 0) (g6 : s.gpr .r6 = P.sd)
    (g7 : s.gpr .r7 = BitVec.ofNat 64 P.len) (g8 : s.gpr .r8 = P.at' 200) :
    AbsorbArgs s P.scr P.sd (P.at' 200) rate 0 P.len :=
  { r3 := g3, r4 := g4, r5 := g5, r6 := g6, r7 := g7, r8 := g8
    hrate := hr, hpos := rate_pos hr, hlen := hp.len_lt, sp48 := by rw [he.sp]; exact hp.sp48
    st_scr := st_disj hp
    d_st := hp.sd_scr.sub_right (Region.sub_prefix (by decide))
    d_scr := hp.sd_scr.sub_right (sub_scr (by decide))
    k_st := stk_scr0 hp he.sp (by decide)
    k_d := by rw [he.sp]; exact hp.b_sd
    k_scr := stk_scr hp he.sp (by decide) }

/-- What a call writes in the working space is covered. -/
theorem covScr {s : State} (hwr : s.wr = σ.wr) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ off, r.base = P.scr + BitVec.ofNat 64 off ∧ off + r.len ≤ 2048) : Covers rs s.wr :=
  Covers.of_sub fun r hr => by
    obtain ⟨off, hb, hl⟩ := h r hr
    exact ⟨P.scrR, by rw [hwr, hp.wr]; simp, off, hb, hl⟩

theorem covScrRd {s : State} (hwr : s.wr = σ.wr) (hrd : s.rd = σ.rd) {rd rs : List Region}
    (hd : ∀ r ∈ rd, r = P.sdR)
    (h : ∀ r ∈ rs, ∃ off, r.base = P.scr + BitVec.ofNat 64 off ∧ off + r.len ≤ 2048) :
    Covers (rd ++ rs) (s.rd ++ s.wr) :=
  Covers.of_sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · rw [hd r hr]
      exact ⟨P.sdR, List.mem_append_left _ (by rw [hrd]; exact hp.rd), 0, (BitVec.add_zero _).symm, by simp⟩
    · obtain ⟨off, hb, hl⟩ := h r hr
      exact ⟨P.scrR, List.mem_append_right _ (by rw [hwr, hp.wr]; simp), off, hb, hl⟩

/-- The arguments of `absorb`, after zeroing the state. -/
theorem blk1_ok {rate : Nat} (hr : rate ∈ rates) {s : State} (h : J0 P σ s) :
    WP isa (.block (absArgs rate)) s (J1 rate P σ s) := by
  have hrl := rate_lt hr
  unfold absArgs zeroState
  rw [List.append_assoc, List.cons_append, List.nil_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (Q := fun s1 => s1 = s.write .r0 (BitVec.ofNat 64 0)) (by prun []) fun s1 e1 => ?_
  subst e1
  have e31 : (s.write .r0 (BitVec.ofNat 64 0)).gpr .r31 = P.scr := by
    rw [RegUpd.gpr_write_of_ne (s := s) _ (by decide)]; exact h.env.r31
  rw [WP.block_append_iff]
  refine WP.mono (zeroLanes_ok .r31 (by decide) (by rw [RegUpd.gpr_write_self]; rfl) fun k hk => by
    rw [e31, RegUpd.wr_write, h.env.wr]; exact inScr hp rfl (by omega)) fun s2 h2 => ?_
  have hf := h2.frame
  have hz := h2.zero
  rw [e31] at hf hz
  have k2 : ∀ r, r ≠ .r0 → s2.gpr r = s.gpr r := fun r hr => by
    rw [h2.gpr, RegUpd.gpr_write_of_ne (s := s) _ hr]
  have j2 : J0 P σ s2 := h.step hp (rs := [⟨P.scr, 200⟩]) (by rw [RegUpd.mem_write] at hf; exact hf)
    (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact wr_scr0 (by decide))
    (fun r hr => k2 r (pres_of hr)) h2.rd h2.wr h2.sp
  have g29 := j2.r29
  have g28 := j2.r28
  have g31 := j2.env.r31
  have hblk : WP isa (.block [mov .r3 .r31, .li .r4 rate, .li .r5 0, mov .r6 .r29, mov .r7 .r28,
      .addi .r8 .r31 200]) s2 fun t => t.gpr .r3 = P.scr ∧ t.gpr .r4 = BitVec.ofNat 64 rate ∧
        t.gpr .r5 = BitVec.ofNat 64 0 ∧ t.gpr .r6 = P.sd ∧ t.gpr .r7 = BitVec.ofNat 64 P.len ∧
        t.gpr .r8 = P.at' 200 ∧ (∀ r ∈ preserved, t.gpr r = s2.gpr r) ∧ t.mem = s2.mem ∧ t.rd = s2.rd ∧
        t.wr = s2.wr ∧ t.sp = s2.sp := by
    prun [g29, g28, g31, hrl]
    simp only [true_and, and_true]
    pres_tac
  refine WP.mono hblk fun t ⟨g3, g4, g5, g6, g7, g8, gp, m, rd, wr, sp⟩ => ?_
  have j : J0 P σ t := j2.regs hp m gp rd wr sp
  exact ⟨j, fun r hr => (gp r hr).trans (k2 r (pres_of hr)), by rw [m]; exact stateAt_zero hz,
    absArgs_of hp hr j.env g3 g4 g5 g6 g7 g8⟩

end

/-- After absorbing the message. -/
structure J2 (rate : Nat) (P : Sp) (σ s₀ s : State) : Prop where
  j0 : J0 P σ s
  gp : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  repr : Repr s.mem P.scr rate (P.msg σ)
  r3 : (s.gpr .r3).toNat = P.len % rate

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem call1_ok {rate : Nat} {s₀ s : State} (h : J1 rate P σ s₀ s) :
    WP isa callAbsorb s (J2 rate P σ s₀) := by
  have he := h.j0.env
  refine absorb_call h.args (covScrRd hp he.wr he.rd (fun r hr => by rw [List.mem_singleton] at hr; exact hr)
      fun r hr => ?_) (covScr hp he.wr fun r hr => ?_) fun s' rd wr sp gp hf hrep h3 => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨0, (BitVec.add_zero _).symm, by simp⟩, ⟨200, rfl, by simp⟩]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨0, (BitVec.add_zero _).symm, by simp⟩, ⟨200, rfl, by simp⟩]
  refine ⟨h.j0.step hp hf (fun r hr => ?_) gp rd wr sp, fun r hr => (gp r hr).trans (h.gp r hr), ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [wr_scr0 (by decide), wr_scr (by decide), wr_below he.sp]
  · have := hrep [] (MlKem.repr_nil h.zero) (by simp)
    rwa [List.nil_append, msg_frame hp he] at this
  · rw [h3, Nat.zero_add]

end

theorem cov_abs (P : Sp) (σ : State) (hp : SpOk P σ) {rate : Nat} {s₀ a : State} (h : J1 rate P σ s₀ a) :
    Covers ([P.sdR] ++ [⟨P.scr, 200⟩, ⟨P.at' 200, 640⟩]) (a.rd ++ a.wr) ∧
      Covers [⟨P.scr, 200⟩, ⟨P.at' 200, 640⟩] a.wr := by
  have he := h.j0.env
  refine ⟨covScrRd hp he.wr he.rd (fun r hr => by rw [List.mem_singleton] at hr; exact hr) fun r hr => ?_,
    covScr hp he.wr fun r hr => ?_⟩ <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨0, (BitVec.add_zero _).symm, by simp⟩, ⟨200, rfl, by simp⟩]

/-- The arguments of `pad`. -/
structure J3 (rate : Nat) (P : Sp) (σ s₀ s : State) : Prop where
  j0 : J0 P σ s
  gp : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  repr : Repr s.mem P.scr rate (P.msg σ)
  r6 : s.gpr .r6 = BitVec.ofNat 64 0x1f
  args : PadArgs s P.scr (P.at' 200) rate (P.len % rate)

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem blk2_ok {rate : Nat} (hr : rate ∈ rates) {s₀ s : State} (h : J2 rate P σ s₀ s) :
    WP isa (.block (padArgs rate)) s (J3 rate P σ s₀) := by
  have hrl := rate_lt hr
  have he := h.j0.env
  have g31 := he.r31
  have hm : P.len % rate < 2 ^ 64 := by have := Nat.mod_lt P.len (rate_pos hr); omega
  have e3 : s.gpr .r3 = BitVec.ofNat 64 (P.len % rate) := BitVec.eq_of_toNat_eq (by
    rw [h.r3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := P.len % rate) hm])
  have hblk : WP isa (.block (padArgs rate)) s fun t => t.gpr .r3 = P.scr ∧ t.gpr .r4 = BitVec.ofNat 64 rate ∧
      t.gpr .r5 = BitVec.ofNat 64 (P.len % rate) ∧ t.gpr .r6 = BitVec.ofNat 64 0x1f ∧ t.gpr .r7 = P.at' 200 ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [padArgs, e3, g31, hrl]
    simp only [true_and, and_true]
    pres_tac
  refine WP.mono hblk fun t ⟨g3, g4, g5, g6, g7, gp, m, rd, wr, sp⟩ => ?_
  have j : J0 P σ t := h.j0.regs hp m gp rd wr sp
  exact ⟨j, fun r hr => (gp r hr).trans (h.gp r hr), by rw [m]; exact h.repr, g6,
    { r3 := g3, r4 := g4, r5 := g5, r7 := g7, hrate := hr, hpos := Nat.mod_lt _ (rate_pos hr)
      sp48 := by rw [j.env.sp]; exact hp.sp48, st_scr := st_disj hp, k_st := stk_scr0 hp j.env.sp (by decide)
      k_scr := stk_scr hp j.env.sp (by decide) }⟩

theorem cov_k {s : State} (he : Env P σ s) :
    Covers ([] ++ [⟨P.scr, 200⟩, ⟨P.at' 200, 640⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨P.scr, 200⟩, ⟨P.at' 200, 640⟩] s.wr := by
  refine ⟨covScrRd hp he.wr he.rd (rd := []) (fun r hr => absurd hr List.not_mem_nil) fun r hr => ?_,
    covScr hp he.wr fun r hr => ?_⟩ <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨0, (BitVec.add_zero _).symm, by simp⟩, ⟨200, rfl, by simp⟩]

end

/-- After padding. -/
structure J4 (rate : Nat) (P : Sp) (σ s₀ s : State) : Prop where
  j0 : J0 P σ s
  gp : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  st : stateAt s.mem P.scr = padded rate Spec.Sha3.shakeSuffix (P.msg σ)

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem call2_ok {rate : Nat} {s₀ s : State} (h : J3 rate P σ s₀ s) : WP isa callPad s (J4 rate P σ s₀) := by
  have j := h.j0
  refine pad_call h.args (cov_k hp j.env).1 (cov_k hp j.env).2 fun s' rd' wr' sp' gp' hf hst => ?_
  refine ⟨j.step hp hf (fun r hr => ?_) gp' rd' wr' sp', fun r hr => (gp' r hr).trans (h.gp r hr), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [wr_scr0 (by decide), wr_scr (by decide), wr_below j.env.sp]
  · rw [hst (P.msg σ) h.repr (by rw [MlKem.bytesAt_length]), h.r6, shakeSuffix64]

end

/-- The arguments of `squeeze`. -/
structure J5 (rate outlen : Nat) (P : Sp) (σ s₀ s : State) : Prop where
  j0 : J0 P σ s
  gp : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  st : stateAt s.mem P.scr = padded rate Spec.Sha3.shakeSuffix (P.msg σ)
  args : SqueezeArgs s P.scr (P.at' 840) (P.at' 200) rate 0 outlen

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem blk3_ok {rate outlen : Nat} (hr : rate ∈ rates) (ho : 840 + outlen ≤ 2000) {s₀ s : State}
    (h : J4 rate P σ s₀ s) : WP isa (.block (sqzArgs rate outlen)) s (J5 rate outlen P σ s₀) := by
  have hrl := rate_lt hr
  have hol : outlen < 32768 := by omega
  have he := h.j0.env
  have g31 := he.r31
  have hblk : WP isa (.block (sqzArgs rate outlen)) s fun t => t.gpr .r3 = P.scr ∧
      t.gpr .r4 = BitVec.ofNat 64 rate ∧ t.gpr .r5 = BitVec.ofNat 64 0 ∧ t.gpr .r6 = P.at' 840 ∧
      t.gpr .r7 = BitVec.ofNat 64 outlen ∧ t.gpr .r8 = P.at' 200 ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [sqzArgs, g31, hrl, hol]
    simp only [true_and, and_true]
    pres_tac
  refine WP.mono hblk fun t ⟨g3, g4, g5, g6, g7, g8, gp, m, rd, wr, sp⟩ => ?_
  have j : J0 P σ t := h.j0.regs hp m gp rd wr sp
  have fs := hp.fscr
  exact ⟨j, fun r hr => (gp r hr).trans (h.gp r hr), by rw [m]; exact h.st,
    { r3 := g3, r4 := g4, r5 := g5, r6 := g6, r7 := g7, r8 := g8, hrate := hr, hpos := Nat.zero_le _
      hlen := by omega, sp48 := by rw [j.env.sp]; exact hp.sp48
      st_o := Offset.base_disjoint _ (by omega) (by omega), st_scr := st_disj hp
      o_scr := Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
      k_st := stk_scr0 hp j.env.sp (by decide), k_o := stk_scr hp j.env.sp (by omega)
      k_scr := stk_scr hp j.env.sp (by decide) }⟩

theorem cov_sq {outlen : Nat} (ho : 840 + outlen ≤ 2000) {s : State} (he : Env P σ s) :
    Covers ([] ++ [⟨P.scr, 200⟩, ⟨P.at' 840, outlen⟩, ⟨P.at' 200, 640⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨P.scr, 200⟩, ⟨P.at' 840, outlen⟩, ⟨P.at' 200, 640⟩] s.wr := by
  refine ⟨covScrRd hp he.wr he.rd (rd := []) (fun r hr => absurd hr List.not_mem_nil) fun r hr => ?_,
    covScr hp he.wr fun r hr => ?_⟩ <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [⟨0, (BitVec.add_zero _).symm, by simp⟩, ⟨840, rfl, by simp; omega⟩, ⟨200, rfl, by simp⟩]

end

/-- After squeezing: the output. -/
structure J6 (rate outlen : Nat) (P : Sp) (σ s₀ s : State) : Prop where
  j0 : J0 P σ s
  gp : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  out : bytesAt s.mem (P.at' 840) outlen = squeezeFrom rate (padded rate Spec.Sha3.shakeSuffix (P.msg σ)) 0 outlen

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem call3_ok {rate outlen : Nat} (ho : 840 + outlen ≤ 2000) {s₀ s : State} (h : J5 rate outlen P σ s₀ s) :
    WP isa callSqueeze s (J6 rate outlen P σ s₀) := by
  have j := h.j0
  refine squeeze_call h.args (cov_sq hp ho j.env).1 (cov_sq hp ho j.env).2 fun s' rd' wr' sp' gp' hf hout _ _ => ?_
  refine ⟨j.step hp hf (fun r hr => ?_) gp' rd' wr' sp', fun r hr => (gp' r hr).trans (h.gp r hr), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [wr_scr0 (by decide), wr_scr (by omega), wr_scr (by decide), wr_below j.env.sp]
  · rw [hout, h.st]

/-- The sponge, from `J0`: `outlen` bytes of SHAKE (of rate `rate`) of the
message at `scratch + 840`, the callee-saved registers kept. -/
theorem sponge_ok {rate outlen : Nat} (hr : rate ∈ rates) (ho : 840 + outlen ≤ 2000) {s : State}
    (h : J0 P σ s) : WP isa (sponge rate outlen) s (J6 rate outlen P σ s) :=
  WP.seq (WP.seq (WP.mono (blk1_ok hp hr h) fun _ h1 => WP.mono (call1_ok hp h1) fun _ h2 =>
    WP.seq (WP.seq (WP.mono (blk2_ok hp hr h2) fun _ h3 => WP.mono (call2_ok hp h3) fun _ h4 =>
      WP.seq (WP.mono (blk3_ok hp hr ho h4) fun _ h5 => call3_ok hp ho h5)))))

end

/-! ## Constant time

Two runs, from entry states `σ₁` and `σ₂` whose calls agree (the same `P`,
and the same stack pointer), each related to its own entry state by the
invariants of the correctness proof. -/

theorem zero_ct {R : State → State → Prop} (hsp : ∀ a b, R a b → a.sp = b.sp)
    (h31 : ∀ a b, R a b → a.gpr .r31 = b.gpr .r31) : RelCT isa R (.block (zeroState .r31)) fun _ _ => True :=
  taint_block [.r31] hsp (fun a b hab r hr => by rw [List.mem_singleton] at hr; subst hr; exact h31 a b hab)
    (by taint_decide)

theorem absArgs_ct {R : State → State → Prop} (rate : Nat) (hsp : ∀ a b, R a b → a.sp = b.sp)
    (h31 : ∀ a b, R a b → a.gpr .r31 = b.gpr .r31) : RelCT isa R (.block (absArgs rate)) fun _ _ => True :=
  RelCT.block_append (RelCT.seq (R := fun _ _ => True) (zero_ct hsp h31) (relct_noMem rfl))

theorem env_sp {P : Sp} {σ₁ σ₂ a b : State} (hsp : σ₁.sp = σ₂.sp) (h₁ : Env P σ₁ a) (h₂ : Env P σ₂ b) :
    a.sp = b.sp := by
  rw [h₁.sp, h₂.sp, hsp]

section
variable {P : Sp} {σ₁ σ₂ : State} (hp₁ : SpOk P σ₁) (hp₂ : SpOk P σ₂) (hsp : σ₁.sp = σ₂.sp)
include hp₁ hp₂ hsp

/-- The sponge leaks the same in both runs. -/
theorem sponge_ct {rate outlen : Nat} (hr : rate ∈ rates) (ho : 840 + outlen ≤ 2000) :
    RelCT isa (fun a b => J0 P σ₁ a ∧ J0 P σ₂ b) (sponge rate outlen) fun _ _ => True := by
  -- `absorb`
  refine RelCT.seq (R := fun a b => (∃ x, J2 rate P σ₁ x a) ∧ (∃ y, J2 rate P σ₂ y b)) ?_ ?_
  · refine RelCT.seq (R := fun a b => (∃ x, J1 rate P σ₁ x a) ∧ (∃ y, J1 rate P σ₂ y b))
      (relct_wp (absArgs_ct rate (fun a b hab => env_sp hsp hab.1.env hab.2.env)
        (fun a b hab => by rw [hab.1.env.r31, hab.2.env.r31])) fun a b hab =>
        ⟨WP.mono (blk1_ok hp₁ hr hab.1) fun _ h => ⟨_, h⟩, WP.mono (blk1_ok hp₂ hr hab.2) fun _ h => ⟨_, h⟩⟩) ?_
    refine relct_wp ?_ fun a b ⟨⟨x, ha⟩, ⟨y, hb⟩⟩ =>
      ⟨WP.mono (call1_ok hp₁ ha) fun _ h => ⟨_, h⟩, WP.mono (call1_ok hp₂ hb) fun _ h => ⟨_, h⟩⟩
    refine RelCT.call (k := Proof.Sha3.absorbPPC64LE) Proof.Sha3.PPC64LE.Stream.absorb_correct
      Proof.Sha3.PPC64LE.Stream.absorb_ct [P.sdR] [⟨P.scr, 200⟩, ⟨P.at' 200, 640⟩] fun a b ⟨⟨x, ha⟩, ⟨y, hb⟩⟩ => ?_
    have c₁ := cov_abs P σ₁ hp₁ ha
    have c₂ := cov_abs P σ₂ hp₂ hb
    refine ⟨absorb_pre ha.args, absorb_pre hb.args, ?_, c₁.1, c₁.2, c₂.1, c₂.2⟩
    simp only [Proof.Sha3.absorbPPC64LE, ce_gpr _ _ _ (by decide : Reg.r3 ∉ linkRegs),
      ce_gpr _ _ _ (by decide : Reg.r4 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.r5 ∉ linkRegs),
      ce_gpr _ _ _ (by decide : Reg.r6 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.r7 ∉ linkRegs),
      ce_gpr _ _ _ (by decide : Reg.r8 ∉ linkRegs), State.withRegions_sp, State.callEntry_sp,
      ha.args.r3, ha.args.r4, ha.args.r5, ha.args.r6, ha.args.r7, ha.args.r8, hb.args.r3, hb.args.r4,
      hb.args.r5, hb.args.r6, hb.args.r7, hb.args.r8, env_sp hsp ha.j0.env hb.j0.env, and_self]
  -- `pad`
  refine RelCT.seq (R := fun a b => (∃ x, J4 rate P σ₁ x a) ∧ (∃ y, J4 rate P σ₂ y b)) ?_ ?_
  · refine RelCT.seq (R := fun a b => (∃ x, J3 rate P σ₁ x a) ∧ (∃ y, J3 rate P σ₂ y b))
      (relct_wp (relct_noMem rfl) fun a b ⟨⟨x, ha⟩, ⟨y, hb⟩⟩ =>
        ⟨WP.mono (blk2_ok hp₁ hr ha) fun _ h => ⟨_, h⟩, WP.mono (blk2_ok hp₂ hr hb) fun _ h => ⟨_, h⟩⟩) ?_
    refine relct_wp ?_ fun a b ⟨⟨x, ha⟩, ⟨y, hb⟩⟩ =>
      ⟨WP.mono (call2_ok hp₁ ha) fun _ h => ⟨_, h⟩, WP.mono (call2_ok hp₂ hb) fun _ h => ⟨_, h⟩⟩
    refine RelCT.call (k := Proof.Sha3.padPPC64LE) Proof.Sha3.PPC64LE.Stream.pad_correct
      Proof.Sha3.PPC64LE.Stream.pad_ct [] [⟨P.scr, 200⟩, ⟨P.at' 200, 640⟩] fun a b ⟨⟨x, ha⟩, ⟨y, hb⟩⟩ => ?_
    have c₁ := cov_k hp₁ ha.j0.env
    have c₂ := cov_k hp₂ hb.j0.env
    refine ⟨pad_pre ha.args, pad_pre hb.args, ?_, c₁.1, c₁.2, c₂.1, c₂.2⟩
    simp only [Proof.Sha3.padPPC64LE, ce_gpr _ _ _ (by decide : Reg.r3 ∉ linkRegs),
      ce_gpr _ _ _ (by decide : Reg.r4 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.r5 ∉ linkRegs),
      ce_gpr _ _ _ (by decide : Reg.r7 ∉ linkRegs), State.withRegions_sp, State.callEntry_sp,
      ha.args.r3, ha.args.r4, ha.args.r5, ha.args.r7, hb.args.r3, hb.args.r4, hb.args.r5, hb.args.r7,
      env_sp hsp ha.j0.env hb.j0.env, and_self]
  -- `squeeze`
  refine RelCT.seq (R := fun a b => (∃ x, J5 rate outlen P σ₁ x a) ∧ (∃ y, J5 rate outlen P σ₂ y b))
    (relct_wp (relct_noMem rfl) fun a b ⟨⟨x, ha⟩, ⟨y, hb⟩⟩ =>
      ⟨WP.mono (blk3_ok hp₁ hr ho ha) fun _ h => ⟨_, h⟩, WP.mono (blk3_ok hp₂ hr ho hb) fun _ h => ⟨_, h⟩⟩) ?_
  refine RelCT.call (k := Proof.Sha3.squeezePPC64LE) Proof.Sha3.PPC64LE.Stream.squeeze_correct
    Proof.Sha3.PPC64LE.Stream.squeeze_ct [] [⟨P.scr, 200⟩, ⟨P.at' 840, outlen⟩, ⟨P.at' 200, 640⟩]
    fun a b ⟨⟨x, ha⟩, ⟨y, hb⟩⟩ => ?_
  have c₁ := cov_sq hp₁ ho ha.j0.env
  have c₂ := cov_sq hp₂ ho hb.j0.env
  refine ⟨squeeze_pre ha.args, squeeze_pre hb.args, ?_, c₁.1, c₁.2, c₂.1, c₂.2⟩
  simp only [Proof.Sha3.squeezePPC64LE, ce_gpr _ _ _ (by decide : Reg.r3 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.r4 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.r5 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.r6 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.r7 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.r8 ∉ linkRegs), State.withRegions_sp, State.callEntry_sp,
    ha.args.r3, ha.args.r4, ha.args.r5, ha.args.r6, ha.args.r7, ha.args.r8, hb.args.r3, hb.args.r4,
    hb.args.r5, hb.args.r6, hb.args.r7, hb.args.r8, env_sp hsp ha.j0.env hb.j0.env, and_self]

end

end VG.Proof.MlDsa.PPC64LE.Sample
