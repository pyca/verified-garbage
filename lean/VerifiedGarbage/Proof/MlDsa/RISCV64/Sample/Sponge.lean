module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.Sample
public import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Calls
public import VerifiedGarbage.Proof.MlDsa.Sample.Hash
public import VerifiedGarbage.Proof.MlDsa.Sample.Mem
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.CallsCT
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Contracts
meta import VerifiedGarbage.Impl.MlDsa.RISCV64.Sample
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Calls
meta import VerifiedGarbage.Proof.MlDsa.Sample.Hash
meta import VerifiedGarbage.Proof.MlDsa.Sample.Mem
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
meta import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
meta import VerifiedGarbage.Proof.MlKem.KPke
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Wp
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.CallsCT
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Contracts

/-!
# ML-DSA on RISC-V: the sampling functions' SHAKE

As on PPC64LE (`Proof/MlDsa/PPC64LE/Sample/Sponge.lean`), with the sponge
called as `vg_mlkem_sample_ntt` calls it (`Proof/MlKem/RISCV64/Sample.lean`):
a call is described by `Sp` (the message, its length, the working space
`scratch` and the output polynomial), whose regions are laid out as `SpOk`
says of the entry state. From the prologue on, `Env` holds: `s10` is the
output polynomial and `s11` the working space, our caller's `s7`–`s11` and
`ra` are saved at `scratch + 2000`, the callee-saved registers but those are
our caller's, and the memory has changed only in the output polynomial, the
working space and the 1168 bytes below the stack pointer. `sponge` then
leaves `outlen` bytes of SHAKE of the message at `scratch + 840`
(`sponge_ok`, from `J0` to `J6`), keeping the callee-saved registers, and
two runs of it from calls that agree leak the same (`sponge_ct`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sample

open VG VG.RISCV64
open VG.Impl.MlDsa.RISCV64.Sample
open VG.Impl.Sha3.RISCV64.Stream (mov)
open VG.Proof.Sha3.RISCV64.Stream (AbsorbArgs PadArgs SqueezeArgs absorb_call pad_call squeeze_call
  absorbCall_ct padCall_ct squeezeCall_ct)
open VG.Proof.MlKem.RISCV64.Sample (zeroLanes_ok stateAt_zero shakeSuffix64 readW_writeW_off taint_block relct_wp)
open VG.Impl.MlKem.RISCV64 (zeroState)
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

/-- The stack the Keccak functions use. -/
abbrev STK (σ : State) : Region := below σ.sp 1168

/-- The regions of a call, from the entry state `σ`. -/
structure SpOk (P : Sp) (σ : State) : Prop where
  rd : P.sdR ∈ σ.rd
  wr : σ.wr = [P.aR, P.scrR]
  sd_a : P.sdR.Disjoint P.aR
  sd_scr : P.sdR.Disjoint P.scrR
  a_scr : P.aR.Disjoint P.scrR
  b_sd : (STK σ).Disjoint P.sdR
  b_a : (STK σ).Disjoint P.aR
  b_scr : (STK σ).Disjoint P.scrR
  len_lt : P.len < 2 ^ 64
  fa : P.a.toNat + 1024 ≤ 2 ^ 64
  fscr : P.scr.toNat + 2048 ≤ 2 ^ 64
  al : σ.sp.toNat % 16 = 0
  sp1168 : 1168 ≤ σ.sp.toNat
  alA : P.a.toNat % 4 = 0
  alS : P.scr.toNat % 8 = 0

/-- What holds from the prologue on, relative to the entry state `σ`. -/
structure Env (P : Sp) (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  s10 : s.gpr .s10 = P.a
  s11 : s.gpr .s11 = P.scr
  cs : ∀ r ∈ preserved, r ≠ .s7 → r ≠ .s8 → r ≠ .s9 → r ≠ .s10 → r ≠ .s11 → s.gpr r = σ.gpr r
  v7 : s.mem.readW (P.at' 2000) 64 = σ.gpr .s7
  v8 : s.mem.readW (P.at' 2008) 64 = σ.gpr .s8
  v9 : s.mem.readW (P.at' 2016) 64 = σ.gpr .s9
  v10 : s.mem.readW (P.at' 2024) 64 = σ.gpr .s10
  v11 : s.mem.readW (P.at' 2032) 64 = σ.gpr .s11
  vra : s.mem.readW (P.at' 2040) 64 = σ.gpr .ra
  frame : Frame [P.aR, P.scrR, STK σ] σ.mem s.mem

/-- Where a piece of code may write, keeping `Env`: the working space below
the saved registers, the output polynomial and the stack below the stack
pointer. -/
def Sp.Wr (P : Sp) (σ : State) (r : Region) : Prop :=
  Region.Sub r ⟨P.scr, 2000⟩ ∨ Region.Sub r P.aR ∨ Region.Sub r (STK σ)

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

/-- A doubleword of the working space is aligned. -/
theorem scr_al {o : Nat} (h : o % 8 = 0) : (P.at' o).toNat % 8 = 0 := by
  have := hp.alS
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

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
  refine ⟨rd.trans he.rd, wr.trans he.wr, sp.trans he.sp, (gp _ (by decide)).trans he.s10,
    (gp _ (by decide)).trans he.s11, fun r hr a b c d e => (gp r hr).trans (he.cs r hr a b c d e),
    (sav_read hp hf hrs (by omega) (by omega)).trans he.v7, (sav_read hp hf hrs (by omega) (by omega)).trans he.v8,
    (sav_read hp hf hrs (by omega) (by omega)).trans he.v9, (sav_read hp hf hrs (by omega) (by omega)).trans he.v10,
    (sav_read hp hf hrs (by omega) (by omega)).trans he.v11, (sav_read hp hf hrs (by omega) (by omega)).trans he.vra,
    he.frame.trans (hf.sub fun r hr => ?_)⟩
  rcases hrs r hr with h | h | h
  · exact ⟨P.scrR, by simp, fun x hx => Region.sub_prefix (base := P.scr) (by decide : 2000 ≤ 2048) x (h x hx)⟩
  · exact ⟨P.aR, by simp, h⟩
  · exact ⟨STK σ, by simp, h⟩

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
theorem wr_below {s : State} (h : s.sp = σ.sp) : P.Wr σ (below s.sp 1168) :=
  .inr (.inr (by rw [h]; exact fun _ h => h))

end

/-! ## The sponge -/

/-- The registers of the sponge's arguments: the message in `s9` and its
length in `s8`. -/
structure J0 (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  s9 : s.gpr .s9 = P.sd
  s8 : s.gpr .s8 = BitVec.ofNat 64 P.len

theorem J0.step {P : Sp} {σ s s' : State} (hp : SpOk P σ) (h : J0 P σ s) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hrs : ∀ r ∈ rs, P.Wr σ r) (gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : J0 P σ s' :=
  ⟨h.env.step hp hf hrs gp rd wr sp, (gp _ (by decide)).trans h.s9, (gp _ (by decide)).trans h.s8⟩

theorem J0.regs {P : Sp} {σ s s' : State} (hp : SpOk P σ) (h : J0 P σ s) (hm : s'.mem = s.mem)
    (gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) :
    J0 P σ s' :=
  ⟨h.env.regs hp hm gp rd wr sp, (gp _ (by decide)).trans h.s9, (gp _ (by decide)).trans h.s8⟩

/-- After zeroing the state: the arguments of `absorb`. -/
structure J1 (rate : Nat) (P : Sp) (σ s₀ s : State) : Prop where
  j0 : J0 P σ s
  gp : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  zero : stateAt s.mem P.scr = Spec.Sha3.zero
  args : AbsorbArgs s P.scr P.sd rate 0 P.len

theorem rate_pos {rate : Nat} (h : rate ∈ rates) : 0 < rate := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem rate_lt {rate : Nat} (h : rate ∈ rates) : rate < 2048 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem stk_scr {s : State} (hsp : s.sp = σ.sp) {o n : Nat} (h : o + n ≤ 2048) :
    (below s.sp 1168).Disjoint ⟨P.at' o, n⟩ := by
  rw [hsp]; exact hp.b_scr.sub_right (sub_scr h)

theorem stk_scr0 {s : State} (hsp : s.sp = σ.sp) {n : Nat} (h : n ≤ 2048) :
    (below s.sp 1168).Disjoint ⟨P.scr, n⟩ := by
  rw [hsp]; exact hp.b_scr.sub_right (Region.sub_prefix h)

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

omit hp in
/-- The state, at the start of the working space. -/
theorem st0 : ∀ r ∈ [(⟨P.scr, 200⟩ : Region)], ∃ off, r.base = P.scr + BitVec.ofNat 64 off ∧ off + r.len ≤ 2048 :=
  fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩

theorem cov_abs {s : State} (he : Env P σ s) :
    Covers ([P.sdR] ++ [⟨P.scr, 200⟩]) (s.rd ++ s.wr) ∧ Covers [⟨P.scr, 200⟩] s.wr :=
  ⟨covScrRd hp he.wr he.rd (fun r hr => by rw [List.mem_singleton] at hr; exact hr) st0,
    covScr hp he.wr st0⟩

theorem cov_pad {s : State} (he : Env P σ s) :
    Covers ([] ++ [⟨P.scr, 200⟩]) (s.rd ++ s.wr) ∧ Covers [⟨P.scr, 200⟩] s.wr :=
  ⟨covScrRd hp he.wr he.rd (rd := []) (fun _ hr => absurd hr List.not_mem_nil) st0, covScr hp he.wr st0⟩

theorem cov_sq {outlen : Nat} (ho : 840 + outlen ≤ 2000) {s : State} (he : Env P σ s) :
    Covers ([] ++ [⟨P.scr, 200⟩, ⟨P.at' 840, outlen⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨P.scr, 200⟩, ⟨P.at' 840, outlen⟩] s.wr := by
  refine ⟨covScrRd hp he.wr he.rd (rd := []) (fun r hr => absurd hr List.not_mem_nil) fun r hr => ?_,
    covScr hp he.wr fun _ hr => ?_⟩ <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨0, (BitVec.add_zero _).symm, by simp⟩, ⟨840, rfl, by simp; omega⟩]

theorem absArgs_of {rate : Nat} (hr : rate ∈ rates) {s : State} (he : Env P σ s) (g0 : s.gpr .a0 = P.scr)
    (g1 : s.gpr .a1 = BitVec.ofNat 64 rate) (g2 : s.gpr .a2 = BitVec.ofNat 64 0) (g3 : s.gpr .a3 = P.sd)
    (g4 : s.gpr .a4 = BitVec.ofNat 64 P.len) : AbsorbArgs s P.scr P.sd rate 0 P.len :=
  { a0 := g0, a1 := g1, a2 := g2, a3 := g3, a4 := g4
    hrate := hr, hpos := rate_pos hr, hlen := hp.len_lt, al := by rw [he.sp]; exact hp.al
    sp := by rw [he.sp]; exact hp.sp1168
    d_st := hp.sd_scr.sub_right (Region.sub_prefix (by decide))
    k_st := stk_scr0 hp he.sp (by decide)
    k_d := by rw [he.sp]; exact hp.b_sd }

/-- The arguments of `absorb`, after zeroing the state. -/
theorem blk1_ok {rate : Nat} (hr : rate ∈ rates) {s : State} (h : J0 P σ s) :
    WP isa (.block (absArgs rate)) s (J1 rate P σ s) := by
  have hrl := rate_lt hr
  have g11 := h.env.s11
  unfold absArgs zeroState
  rw [List.append_assoc, List.cons_append, List.nil_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (Q := fun s1 => s1 = s.write .t0 0) (by crun []) fun s1 e1 => ?_
  subst e1
  have e11 : (s.write .t0 0).gpr .s11 = P.scr := by rw [RegUpd.gpr_write_of_ne _ _ (by decide)]; exact g11
  rw [WP.block_append_iff]
  refine WP.mono (zeroLanes_ok .s11 (RegUpd.gpr_write_self _ _ _)
    (fun k hk => by rw [e11]; exact inScr hp (by rw [RegUpd.wr_write]; exact h.env.wr) (by omega))
    (fun k hk => by rw [e11]; exact scr_al hp (by omega))) fun s2 h2 => ?_
  have hf := h2.frame
  have hz := h2.zero
  rw [e11] at hf hz
  have k2 : ∀ r, r ≠ .t0 → s2.gpr r = s.gpr r := fun r hr => by
    rw [h2.gpr, RegUpd.gpr_write_of_ne _ _ hr]
  have j2 : J0 P σ s2 := h.step hp (rs := [⟨P.scr, 200⟩]) hf
    (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact wr_scr0 (by decide))
    (fun r hr => k2 r (by rintro rfl; simp [preserved] at hr)) h2.rd h2.wr h2.sp
  have g9 := j2.s9
  have g8 := j2.s8
  have g11' := j2.env.s11
  have hblk : WP isa (.block [mov .a0 .s11, .li .a1 rate, .li .a2 0, mov .a3 .s9, mov .a4 .s8]) s2 fun t =>
      t.mem = s2.mem ∧ t.gpr .a0 = P.scr ∧ t.gpr .a1 = BitVec.ofNat 64 rate ∧ t.gpr .a2 = BitVec.ofNat 64 0 ∧
        t.gpr .a3 = P.sd ∧ t.gpr .a4 = BitVec.ofNat 64 P.len ∧ (∀ r ∈ preserved, t.gpr r = s2.gpr r) ∧
        t.rd = s2.rd ∧ t.wr = s2.wr ∧ t.sp = s2.sp := by
    mrun [mov, g9, g8, g11', hrl, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  refine WP.mono hblk fun t ⟨m, g0, g1, g2, g3, g4, gp, rd, wr, sp⟩ => ?_
  have j : J0 P σ t := j2.regs hp m gp rd wr sp
  exact ⟨j, fun r hr => (gp r hr).trans (k2 r (by rintro rfl; simp [preserved] at hr)),
    by rw [m]; exact stateAt_zero hz, absArgs_of hp hr j.env g0 g1 g2 g3 g4⟩

end

/-- After absorbing the message. -/
structure J2 (rate : Nat) (P : Sp) (σ s₀ s : State) : Prop where
  j0 : J0 P σ s
  gp : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  repr : Repr s.mem P.scr rate (P.msg σ)
  a0 : (s.gpr .a0).toNat = P.len % rate

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem call1_ok {rate : Nat} {s₀ s : State} (h : J1 rate P σ s₀ s) :
    WP isa callAbsorb s (J2 rate P σ s₀) := by
  have he := h.j0.env
  refine absorb_call h.args (cov_abs hp he).1 (cov_abs hp he).2 fun s' rd wr sp gp hf hrep h0 => ?_
  refine ⟨h.j0.step hp hf (fun r hr => ?_) gp rd wr sp, fun r hr => (gp r hr).trans (h.gp r hr), ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [wr_scr0 (by decide), wr_below he.sp]
  · have := hrep [] (MlKem.repr_nil h.zero) (by simp)
    rwa [List.nil_append, msg_frame hp he] at this
  · rw [h0, Nat.zero_add]

end

/-- The arguments of `pad`. -/
structure J3 (rate : Nat) (P : Sp) (σ s₀ s : State) : Prop where
  j0 : J0 P σ s
  gp : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  repr : Repr s.mem P.scr rate (P.msg σ)
  a3 : s.gpr .a3 = BitVec.ofNat 64 0x1f
  args : PadArgs s P.scr rate (P.len % rate)

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem blk2_ok {rate : Nat} (hr : rate ∈ rates) {s₀ s : State} (h : J2 rate P σ s₀ s) :
    WP isa (.block (padArgs rate)) s (J3 rate P σ s₀) := by
  have hrl := rate_lt hr
  have he := h.j0.env
  have g11 := he.s11
  have hm : P.len % rate < 2 ^ 64 := by have := Nat.mod_lt P.len (rate_pos hr); omega
  have e0 : s.gpr .a0 = BitVec.ofNat 64 (P.len % rate) := BitVec.eq_of_toNat_eq (by
    rw [h.a0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := P.len % rate) hm])
  have hblk : WP isa (.block (padArgs rate)) s fun t => t.mem = s.mem ∧ t.gpr .a0 = P.scr ∧
      t.gpr .a1 = BitVec.ofNat 64 rate ∧ t.gpr .a2 = BitVec.ofNat 64 (P.len % rate) ∧
      t.gpr .a3 = BitVec.ofNat 64 0x1f ∧ (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp := by
    mrun [padArgs, mov, e0, g11, hrl, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  refine WP.mono hblk fun t ⟨m, g0, g1, g2, g3, gp, rd, wr, sp⟩ => ?_
  have j : J0 P σ t := h.j0.regs hp m gp rd wr sp
  exact ⟨j, fun r hr => (gp r hr).trans (h.gp r hr), by rw [m]; exact h.repr, g3,
    { a0 := g0, a1 := g1, a2 := g2, hrate := hr, hpos := Nat.mod_lt _ (rate_pos hr)
      al := by rw [j.env.sp]; exact hp.al, sp := by rw [j.env.sp]; exact hp.sp1168
      k_st := stk_scr0 hp j.env.sp (by decide) }⟩

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
  refine pad_call h.args (cov_pad hp j.env).1 (cov_pad hp j.env).2 fun s' rd' wr' sp' gp' hf hst => ?_
  refine ⟨j.step hp hf (fun r hr => ?_) gp' rd' wr' sp', fun r hr => (gp' r hr).trans (h.gp r hr), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [wr_scr0 (by decide), wr_below j.env.sp]
  · rw [hst (P.msg σ) h.repr (by rw [MlKem.bytesAt_length]), h.a3, shakeSuffix64]

end

/-- The arguments of `squeeze`. -/
structure J5 (rate outlen : Nat) (P : Sp) (σ s₀ s : State) : Prop where
  j0 : J0 P σ s
  gp : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  st : stateAt s.mem P.scr = padded rate Spec.Sha3.shakeSuffix (P.msg σ)
  args : SqueezeArgs s P.scr (P.at' 840) rate 0 outlen

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem blk3_ok {rate outlen : Nat} (hr : rate ∈ rates) (ho : 840 + outlen ≤ 2000) {s₀ s : State}
    (h : J4 rate P σ s₀ s) : WP isa (.block (sqzArgs rate outlen)) s (J5 rate outlen P σ s₀) := by
  have hrl := rate_lt hr
  have hol : outlen < 2048 := by omega
  have he := h.j0.env
  have g11 := he.s11
  have hblk : WP isa (.block (sqzArgs rate outlen)) s fun t => t.mem = s.mem ∧ t.gpr .a0 = P.scr ∧
      t.gpr .a1 = BitVec.ofNat 64 rate ∧ t.gpr .a2 = BitVec.ofNat 64 0 ∧ t.gpr .a3 = P.at' 840 ∧
      t.gpr .a4 = BitVec.ofNat 64 outlen ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    mrun [sqzArgs, mov, g11, hrl, hol, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  refine WP.mono hblk fun t ⟨m, g0, g1, g2, g3, g4, gp, rd, wr, sp⟩ => ?_
  have j : J0 P σ t := h.j0.regs hp m gp rd wr sp
  have fs := hp.fscr
  exact ⟨j, fun r hr => (gp r hr).trans (h.gp r hr), by rw [m]; exact h.st,
    { a0 := g0, a1 := g1, a2 := g2, a3 := g3, a4 := g4, hrate := hr, hpos := Nat.zero_le _
      hlen := by omega, al := by rw [j.env.sp]; exact hp.al, sp := by rw [j.env.sp]; exact hp.sp1168
      st_o := Offset.base_disjoint _ (by omega) (by omega)
      k_st := stk_scr0 hp j.env.sp (by decide), k_o := stk_scr hp j.env.sp (by omega) }⟩

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
    rcases hr with rfl | rfl | rfl
    exacts [wr_scr0 (by decide), wr_scr (by omega), wr_below j.env.sp]
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
    (h11 : ∀ a b, R a b → a.gpr .s11 = b.gpr .s11) : RelCT isa R (.block (zeroState .s11)) fun _ _ => True :=
  taint_block [.s11] hsp (fun a b hab r hr => by rw [List.mem_singleton] at hr; subst hr; exact h11 a b hab)
    (by taint_decide)

theorem absArgs_ct {R : State → State → Prop} (rate : Nat) (hsp : ∀ a b, R a b → a.sp = b.sp)
    (h11 : ∀ a b, R a b → a.gpr .s11 = b.gpr .s11) : RelCT isa R (.block (absArgs rate)) fun _ _ => True :=
  RelCT.block_append (RelCT.seq (R := fun _ _ => True) (zero_ct hsp h11) (Pack.relct_noMem rfl))

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
        (fun a b hab => by rw [hab.1.env.s11, hab.2.env.s11])) fun a b hab =>
        ⟨WP.mono (blk1_ok hp₁ hr hab.1) fun _ h => ⟨_, h⟩, WP.mono (blk1_ok hp₂ hr hab.2) fun _ h => ⟨_, h⟩⟩) ?_
    refine relct_wp ?_ fun a b ⟨⟨x, ha⟩, ⟨y, hb⟩⟩ =>
      ⟨WP.mono (call1_ok hp₁ ha) fun _ h => ⟨_, h⟩, WP.mono (call1_ok hp₂ hb) fun _ h => ⟨_, h⟩⟩
    exact absorbCall_ct fun a b ⟨⟨x, ha⟩, ⟨y, hb⟩⟩ => ⟨env_sp hsp ha.j0.env hb.j0.env, ha.args, hb.args,
      (cov_abs hp₁ ha.j0.env).1, (cov_abs hp₁ ha.j0.env).2, (cov_abs hp₂ hb.j0.env).1, (cov_abs hp₂ hb.j0.env).2⟩
  -- `pad`
  refine RelCT.seq (R := fun a b => (∃ x, J4 rate P σ₁ x a) ∧ (∃ y, J4 rate P σ₂ y b)) ?_ ?_
  · refine RelCT.seq (R := fun a b => (∃ x, J3 rate P σ₁ x a) ∧ (∃ y, J3 rate P σ₂ y b))
      (relct_wp (Pack.relct_noMem rfl) fun a b ⟨⟨x, ha⟩, ⟨y, hb⟩⟩ =>
        ⟨WP.mono (blk2_ok hp₁ hr ha) fun _ h => ⟨_, h⟩, WP.mono (blk2_ok hp₂ hr hb) fun _ h => ⟨_, h⟩⟩) ?_
    refine relct_wp ?_ fun a b ⟨⟨x, ha⟩, ⟨y, hb⟩⟩ =>
      ⟨WP.mono (call2_ok hp₁ ha) fun _ h => ⟨_, h⟩, WP.mono (call2_ok hp₂ hb) fun _ h => ⟨_, h⟩⟩
    exact padCall_ct fun a b ⟨⟨x, ha⟩, ⟨y, hb⟩⟩ => ⟨env_sp hsp ha.j0.env hb.j0.env, ha.args, hb.args,
      (cov_pad hp₁ ha.j0.env).1, (cov_pad hp₁ ha.j0.env).2, (cov_pad hp₂ hb.j0.env).1, (cov_pad hp₂ hb.j0.env).2⟩
  -- `squeeze`
  refine RelCT.seq (R := fun a b => (∃ x, J5 rate outlen P σ₁ x a) ∧ (∃ y, J5 rate outlen P σ₂ y b))
    (relct_wp (Pack.relct_noMem rfl) fun a b ⟨⟨x, ha⟩, ⟨y, hb⟩⟩ =>
      ⟨WP.mono (blk3_ok hp₁ hr ho ha) fun _ h => ⟨_, h⟩, WP.mono (blk3_ok hp₂ hr ho hb) fun _ h => ⟨_, h⟩⟩) ?_
  exact squeezeCall_ct fun a b ⟨⟨x, ha⟩, ⟨y, hb⟩⟩ => ⟨env_sp hsp ha.j0.env hb.j0.env, ha.args, hb.args,
    (cov_sq hp₁ ho ha.j0.env).1, (cov_sq hp₁ ho ha.j0.env).2, (cov_sq hp₂ ho hb.j0.env).1,
    (cov_sq hp₂ ho hb.j0.env).2⟩

end

end VG.Proof.MlDsa.RISCV64.Sample
