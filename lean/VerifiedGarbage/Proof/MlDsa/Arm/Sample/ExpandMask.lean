import VerifiedGarbage.Impl.MlDsa.Arm.Sample.Common
import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
import VerifiedGarbage.Proof.MlDsa.Sample.Signs
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.Unpack
import VerifiedGarbage.Impl.MlDsa.Arm.Sample.ExpandMask
import VerifiedGarbage.Proof.Framework.Arm.Inline

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sample.Sponge`. -/
section

/-!
# ML-DSA on 32-bit ARM: the sampling functions' SHAKE

What the sampling functions share (`Impl/MlDsa/Arm/Sample/Common.lean`), for
any of them: a call is described by `Sp` (the message, its length, the working
space `scratch`, the output polynomial and the parameter), whose regions are
laid out as `SpOk` says of the entry state. From the prologue on, `Env` holds:
`r5` is the output polynomial and `r6` the working space, our caller's
`r4`–`r11` and `lr` are saved at `scratch + 2012`, and the memory has changed
only in the output polynomial, the working space and the 8 bytes below the
stack pointer. `sponge` then leaves `outlen` bytes of SHAKE of the message at
`scratch + 840` (`sponge_ok`, from `J0` to `J6`), and two runs of it from
calls that agree leak the same (`sponge_ct`).
-/

namespace VG.Proof.MlDsa.Arm.Sample

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Arm.RegUpd (gpr_setReg_self gpr_setReg_of_ne)
open VG.Proof.MlKem.Arm.Sample (Regs regs_cs zeroWords_ok stateAt_zero fit_add)
open VG.Impl.MlDsa.Arm.Sample
open VG.Impl.MlKem.Arm (absorbCall padCall squeezeCall zeroState savedRegs)
open VG.Spec.Sha3 (bytesAt stateAt rates squeezeFrom)
open VG.Proof.MlDsa.Sample (padded polyR)

/-- A call of a sampling function. -/
structure Sp where
  /-- The message hashed. -/
  sd : BitVec 32
  len : Nat
  /-- `scratch`. -/
  scr : BitVec 32
  /-- The output polynomial. -/
  a : BitVec 32
  /-- The parameter, in `r7`. -/
  prm : BitVec 32

namespace Sp
variable (P : VG.Proof.MlDsa.Arm.Sample.Sp)
/-- `scratch`, as an address. -/
abbrev S : Addr := State.addr P.scr
/-- `scratch + off`. -/
abbrev at' (off : Nat) : Addr := P.S + BitVec.ofNat 64 off
/-- The output polynomial, as an address. -/
abbrev A : Addr := State.addr P.a
abbrev scrR : Region := ⟨P.S, 2048⟩
abbrev sdR : Region := ⟨State.addr P.sd, P.len⟩
abbrev aR : Region := polyR P.A
/-- The message. -/
abbrev msg (σ : State) : List Byte := bytesAt σ.mem (State.addr P.sd) P.len
end Sp

/-- The regions of a call, from the entry state `σ`. -/
structure SpOk (P : VG.Proof.MlDsa.Arm.Sample.Sp) (σ : State) : Prop where
  rd : P.sdR ∈ σ.rd
  wr : σ.wr = [P.aR, P.scrR]
  sd_a : P.sdR.Disjoint P.aR
  sd_scr : P.sdR.Disjoint P.scrR
  a_scr : P.aR.Disjoint P.scrR
  b_sd : (below σ 8).Disjoint P.sdR
  b_a : (below σ 8).Disjoint P.aR
  b_scr : (below σ 8).Disjoint P.scrR
  fsd : P.sd.toNat + P.len ≤ 2 ^ 32
  len_lt : P.len < 2 ^ 32
  fa : P.a.toNat + 1024 ≤ 2 ^ 32
  fscr : P.scr.toNat + 2048 ≤ 2 ^ 32
  sp8 : 8 ≤ σ.sp.toNat

/-- What holds from the prologue on, relative to the entry state `σ`. -/
structure Env (P : VG.Proof.MlDsa.Arm.Sample.Sp) (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  r5 : s.gpr .r5 = P.a
  r6 : s.gpr .r6 = P.scr
  sav : VG.Proof.MlKem.Arm.Saved s.mem (P.at' 2012) σ.gpr
  savlr : s.mem.readW (P.at' 2044) 32 = σ.gpr .lr
  frame : Frame [P.aR, P.scrR, below σ 8] σ.mem s.mem

/-- Where a piece of code may write, keeping `Env`: the working space below
the saved registers, the output polynomial and the 8 bytes below the stack
pointer. -/
def Sp.Wr (P : VG.Proof.MlDsa.Arm.Sample.Sp) (σ : State) (r : Region) : Prop :=
  Region.Sub r ⟨P.S, 2012⟩ ∨ Region.Sub r P.aR ∨ Region.Sub r (below σ 8)

theorem below_eq {σ s : State} (h : s.sp = σ.sp) : below s 8 = below σ 8 := by simp only [below, h]

section
variable {P : VG.Proof.MlDsa.Arm.Sample.Sp} {σ : State} (hp : VG.Proof.MlDsa.Arm.Sample.SpOk P σ)
include hp

/-- A 32-bit address in the working space. -/
theorem at_eq {k : Nat} (hk : k < 2048) : State.addr (P.scr + BitVec.ofNat 32 k) = P.at' k :=
  addr_add (by have := hp.fscr; omega)

theorem regA_at {k : Nat} (hk : k < 2048) (n : Nat) : regA (P.scr + BitVec.ofNat 32 k) n = ⟨P.at' k, n⟩ := by
  simp only [regA, VG.Proof.MlDsa.Arm.Sample.at_eq hp hk]

omit hp in
theorem sub_scr {a n : Nat} (h : a + n ≤ 2048) : Region.Sub ⟨P.at' a, n⟩ P.scrR := Offset.sub_base _ h

omit hp in
theorem sub_scr0 {n : Nat} (h : n ≤ 2048) : Region.Sub ⟨P.S, n⟩ P.scrR := Region.sub_prefix h

theorem inScr {s : State} (he : VG.Proof.MlDsa.Arm.Sample.Env P σ s) {a n : Nat} (h : a + n ≤ 2048) : InRegions s.wr (P.at' a) n := by
  rw [he.wr, hp.wr]
  exact ⟨P.scrR, by simp, Offset.contains_base _ h (by omega)⟩

theorem inScrRd {s : State} (he : VG.Proof.MlDsa.Arm.Sample.Env P σ s) {a n : Nat} (h : a + n ≤ 2048) :
    InRegions (s.rd ++ s.wr) (P.at' a) n := by
  obtain ⟨r, hr, hc⟩ := VG.Proof.MlDsa.Arm.Sample.inScr hp he h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- Regions at offsets of the working space are within the writable regions. -/
theorem covScr {s : State} (he : VG.Proof.MlDsa.Arm.Sample.Env P σ s) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ off, r.base = P.S + BitVec.ofNat 64 off ∧ off + r.len ≤ 2048) : Covers rs s.wr :=
  Covers.of_sub fun r hr => by
    obtain ⟨off, hb, hl⟩ := h r hr
    exact ⟨P.scrR, by rw [he.wr, hp.wr]; simp, off, hb, hl⟩

theorem covScrRd {s : State} (he : VG.Proof.MlDsa.Arm.Sample.Env P σ s) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ off, r.base = P.S + BitVec.ofNat 64 off ∧ off + r.len ≤ 2048) :
    Covers rs (s.rd ++ s.wr) := fun x n hi => by
  obtain ⟨r, hr, hc⟩ := VG.Proof.MlDsa.Arm.Sample.covScr hp he h x n hi
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- The saved registers are apart from where code may write. -/
theorem sav_disj {r : Region} (h : P.Wr σ r) : (⟨P.at' 2012, 36⟩ : Region).Disjoint r := by
  rcases h with h | h | h
  · exact (Offset.disjoint_base P.S (d := 2012) (n := 36) (k := 2012) (Nat.le_refl _) (by omega)).sub_right h
  · exact (hp.a_scr.sub_right (VG.Proof.MlDsa.Arm.Sample.sub_scr (a := 2012) (n := 36) (by omega))).symm.sub_right h
  · exact (hp.b_scr.sub_right (VG.Proof.MlDsa.Arm.Sample.sub_scr (a := 2012) (n := 36) (by omega))).symm.sub_right h

/-- `Env` after writes where code may write. -/
theorem Env.step {s s' : State} (he : VG.Proof.MlDsa.Arm.Sample.Env P σ s) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hrs : ∀ r ∈ rs, P.Wr σ r) (g5 : s'.gpr .r5 = s.gpr .r5) (g6 : s'.gpr .r6 = s.gpr .r6)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : VG.Proof.MlDsa.Arm.Sample.Env P σ s' := by
  refine ⟨rd.trans he.rd, wr.trans he.wr, sp.trans he.sp, g5.trans he.r5, g6.trans he.r6, fun i hi => ?_, ?_, ?_⟩
  · rw [hf.readW (r := ⟨P.at' 2012, 36⟩) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => VG.Proof.MlDsa.Arm.Sample.sav_disj hp (hrs r hr)) (by decide)]
    exact he.sav i hi
  · rw [hf.readW (r := ⟨P.at' 2012, 36⟩) (Offset.contains P.S (by omega) (by omega) (by omega))
      (fun r hr => VG.Proof.MlDsa.Arm.Sample.sav_disj hp (hrs r hr)) (by decide)]
    exact he.savlr
  · refine he.frame.trans (hf.sub fun r hr => ?_)
    rcases hrs r hr with h | h | h
    · exact ⟨P.scrR, by simp, fun x hx => VG.Proof.MlDsa.Arm.Sample.sub_scr0 (P := P) (n := 2012) (by omega) x (h x hx)⟩
    · exact ⟨P.aR, by simp, h⟩
    · exact ⟨below σ 8, by simp, h⟩

/-- `Env` after a call that keeps the callee-saved registers and writes where
code may write. -/
theorem Env.kept {s s' : State} (he : VG.Proof.MlDsa.Arm.Sample.Env P σ s) {rs : List Region} (hk : Kept rs s s')
    (hrs : ∀ r ∈ rs, P.Wr σ r) : VG.Proof.MlDsa.Arm.Sample.Env P σ s' :=
  he.step hp hk.frame hrs (hk.cs .r5 (by decide) (by decide)) (hk.cs .r6 (by decide) (by decide)) hk.rd hk.wr hk.sp

omit hp in
/-- `Env` after a block that writes no memory and none of `r4`–`r11`. -/
theorem Env.regs {s s' : State} (he : VG.Proof.MlDsa.Arm.Sample.Env P σ s) (hr : Regs s s') : VG.Proof.MlDsa.Arm.Sample.Env P σ s' :=
  ⟨hr.rd.trans he.rd, hr.wr.trans he.wr, hr.sp.trans he.sp, (hr.cs .r5 (by decide) (by decide)).trans he.r5,
    (hr.cs .r6 (by decide) (by decide)).trans he.r6, by rw [hr.mem]; exact he.sav, by rw [hr.mem]; exact he.savlr,
    by rw [hr.mem]; exact he.frame⟩

/-- The message is not written. -/
theorem msg_frame {s : State} (he : VG.Proof.MlDsa.Arm.Sample.Env P σ s) : bytesAt s.mem (State.addr P.sd) P.len = P.msg σ :=
  MlKem.bytesAt_frame he.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.sd_a, hp.sd_scr, hp.b_sd.symm]) (by have := hp.len_lt; omega)

omit hp in
/-- A part of the working space below the saved registers. -/
theorem wr_scr {a n : Nat} (h : a + n ≤ 2012) : P.Wr σ ⟨P.at' a, n⟩ :=
  .inl (Offset.sub_base _ h)

omit hp in
theorem wr_scr0 {n : Nat} (h : n ≤ 2012) : P.Wr σ ⟨P.S, n⟩ := .inl (Region.sub_prefix h)

omit hp in
theorem wr_below {s : State} (h : s.sp = σ.sp) : P.Wr σ (below s 8) := .inr (.inr (by rw [VG.Proof.MlDsa.Arm.Sample.below_eq h]; exact fun _ h => h))

end

/-! ## The sponge -/

/-- The registers of the sponge's arguments: the parameter in `r7`, the
message in `r8` and its length in `r9`. -/
structure J0 (P : VG.Proof.MlDsa.Arm.Sample.Sp) (σ s : State) : Prop where
  env : VG.Proof.MlDsa.Arm.Sample.Env P σ s
  r7 : s.gpr .r7 = P.prm
  r8 : s.gpr .r8 = P.sd
  r9 : s.gpr .r9 = BitVec.ofNat 32 P.len

/-- `J0` after a block that writes no memory and none of `r4`–`r11`. -/
theorem J0.regs {P : VG.Proof.MlDsa.Arm.Sample.Sp} {σ s s' : State} (h : VG.Proof.MlDsa.Arm.Sample.J0 P σ s) (hr : Regs s s') : VG.Proof.MlDsa.Arm.Sample.J0 P σ s' :=
  ⟨h.env.regs hr, (hr.cs .r7 (by decide) (by decide)).trans h.r7, (hr.cs .r8 (by decide) (by decide)).trans h.r8,
    (hr.cs .r9 (by decide) (by decide)).trans h.r9⟩

theorem J0.kept {P : VG.Proof.MlDsa.Arm.Sample.Sp} {σ s s' : State} (hp : VG.Proof.MlDsa.Arm.Sample.SpOk P σ) (h : VG.Proof.MlDsa.Arm.Sample.J0 P σ s) {rs : List Region} (hk : Kept rs s s')
    (hrs : ∀ r ∈ rs, P.Wr σ r) : VG.Proof.MlDsa.Arm.Sample.J0 P σ s' :=
  ⟨h.env.kept hp hk hrs, (hk.cs .r7 (by decide) (by decide)).trans h.r7,
    (hk.cs .r8 (by decide) (by decide)).trans h.r8, (hk.cs .r9 (by decide) (by decide)).trans h.r9⟩

/-- After zeroing the state: the arguments of `absorb`. -/
structure J1 (rate : Nat) (P : VG.Proof.MlDsa.Arm.Sample.Sp) (σ s : State) : Prop where
  j0 : VG.Proof.MlDsa.Arm.Sample.J0 P σ s
  zero : stateAt s.mem P.S = Spec.Sha3.zero
  args : AbsorbArgs s P.scr (P.scr + BitVec.ofNat 32 200) P.sd rate 0 P.len

theorem rate_pos {rate : Nat} (h : rate ∈ rates) : 0 < rate := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

section
variable {P : VG.Proof.MlDsa.Arm.Sample.Sp} {σ : State} (hp : VG.Proof.MlDsa.Arm.Sample.SpOk P σ)
include hp

theorem absArgs_of {rate : Nat} (hr : rate ∈ rates) {s : State} (he : VG.Proof.MlDsa.Arm.Sample.Env P σ s) (g0 : s.gpr .r0 = P.scr)
    (g1 : s.gpr .r1 = BitVec.ofNat 32 rate) (g2 : s.gpr .r2 = BitVec.ofNat 32 0) (g3 : s.gpr .r3 = P.sd)
    (g12 : s.gpr .r12 = BitVec.ofNat 32 P.len) (glr : s.gpr .lr = P.scr + BitVec.ofNat 32 200) :
    AbsorbArgs s P.scr (P.scr + BitVec.ofNat 32 200) P.sd rate 0 P.len := by
  have fs := hp.fscr
  have eb := VG.Proof.MlDsa.Arm.Sample.below_eq he.sp
  exact {
    r0 := g0, r1 := g1, r2 := g2, r3 := g3, r12 := g12, lr := glr
    hrate := hr, hpos := VG.Proof.MlDsa.Arm.Sample.rate_pos hr, hlen := hp.len_lt, sp := by rw [he.sp]; exact hp.sp8
    fst := fit_le (by decide) fs, fdata := hp.fsd, fscr := fit_add (fit_le (by decide) fs) (by decide) (by decide)
    d_st_scr := by rw [VG.Proof.MlDsa.Arm.Sample.regA_at hp (by decide)]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)
    d_data_st := hp.sd_scr.sub_right (VG.Proof.MlDsa.Arm.Sample.sub_scr0 (by decide))
    d_data_scr := by rw [VG.Proof.MlDsa.Arm.Sample.regA_at hp (by decide)]; exact hp.sd_scr.sub_right (VG.Proof.MlDsa.Arm.Sample.sub_scr (by decide))
    b_st := by rw [eb]; exact hp.b_scr.sub_right (VG.Proof.MlDsa.Arm.Sample.sub_scr0 (by decide))
    b_scr := by rw [eb, VG.Proof.MlDsa.Arm.Sample.regA_at hp (by decide)]; exact hp.b_scr.sub_right (VG.Proof.MlDsa.Arm.Sample.sub_scr (by decide))
    b_data := by rw [eb]; exact hp.b_sd
    cw := by
      rw [VG.Proof.MlDsa.Arm.Sample.regA_at hp (by decide)]
      refine VG.Proof.MlDsa.Arm.Sample.covScr hp he fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [⟨0, (add_ofNat_zero _).symm, by simp⟩, ⟨200, rfl, by simp⟩]
    cr := fun x n ⟨r, hr, hc⟩ => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_left _ (by rw [he.rd]; exact hp.rd), hc⟩ }

end

theorem movs_ok {rate : Nat} (er : encodable (BitVec.ofNat 32 rate) = true) (s : State) :
    WP isa (.block [.mov .r0 (.reg .r6), .mov .r1 (.imm (BitVec.ofNat 32 rate)), .mov .r2 (.imm 0),
      .mov .r3 (.reg .r8), .mov .r12 (.reg .r9), .dp .add .lr .r6 (.imm 200)]) s fun s' =>
      Regs s s' ∧ s'.gpr .r0 = s.gpr .r6 ∧ s'.gpr .r1 = BitVec.ofNat 32 rate ∧ s'.gpr .r2 = BitVec.ofNat 32 0 ∧
        s'.gpr .r3 = s.gpr .r8 ∧ s'.gpr .r12 = s.gpr .r9 ∧ s'.gpr .lr = s.gpr .r6 + BitVec.ofNat 32 200 := by
  run_block [er, and_self, and_true]
  refine ⟨regs_cs _ ?_, by simp⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem mov12_ok (s : State) :
    WP isa (.block [.mov .r12 (.imm 0)]) s fun s' => s'.gpr = (s.setReg .r12 0).gpr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block []

theorem ne_r12 {r : Reg} (hr : r ∈ preserved) : r ≠ .r12 := by
  rintro rfl; exact absurd hr (by decide)

section
variable {P : VG.Proof.MlDsa.Arm.Sample.Sp} {σ : State} (hp : VG.Proof.MlDsa.Arm.Sample.SpOk P σ)
include hp

theorem blk1_ok {rate : Nat} (hr : rate ∈ rates) (er : encodable (BitVec.ofNat 32 rate) = true) {s : State}
    (h : VG.Proof.MlDsa.Arm.Sample.J0 P σ s) : WP isa (.block (absArgs rate)) s (VG.Proof.MlDsa.Arm.Sample.J1 rate P σ) := by
  unfold absArgs zeroState
  rw [List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.Arm.Sample.mov12_ok s) fun s1 ⟨g1, m1, rd1, wr1, sp1⟩ => ?_
  rw [WP.block_append_iff]
  have k1 : ∀ r ∈ preserved, s1.gpr r = s.gpr r := fun r hr => by
    rw [g1, gpr_setReg_of_ne _ _ (VG.Proof.MlDsa.Arm.Sample.ne_r12 hr)]
  have e6 : s1.gpr .r6 = P.scr := (k1 .r6 (by decide)).trans h.env.r6
  refine WP.mono (zeroWords_ok .r6 (s₁ := s1) (by rw [g1, gpr_setReg_self])
    (by rw [e6]; exact fit_le (by decide) hp.fscr)
    fun k hk => by rw [e6, wr1]; exact VG.Proof.MlDsa.Arm.Sample.inScr hp h.env (by omega)) fun s2 h2 => ?_
  refine WP.mono (VG.Proof.MlDsa.Arm.Sample.movs_ok er s2) fun s3 ⟨R3, g0, g1', g2, g3, g12, glr⟩ => ?_
  have k3 : ∀ r ∈ preserved, r ≠ .lr → s3.gpr r = s.gpr r := fun r hr hl => by
    rw [R3.cs r hr hl, h2.gpr, k1 r hr]
  have e2 : ∀ r ∈ preserved, s2.gpr r = s.gpr r := fun r hr => by rw [h2.gpr, k1 r hr]
  have fr : Frame [⟨P.S, 200⟩] s.mem s3.mem := by
    rw [R3.mem, ← m1]
    have := h2.frame
    rwa [e6] at this
  have he : VG.Proof.MlDsa.Arm.Sample.Env P σ s3 := h.env.step hp fr (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact VG.Proof.MlDsa.Arm.Sample.wr_scr0 (by decide))
    (k3 .r5 (by decide) (by decide)) (k3 .r6 (by decide) (by decide))
    (by rw [R3.rd, h2.rd, rd1]) (by rw [R3.wr, h2.wr, wr1]) (by rw [R3.sp, h2.sp, sp1])
  have hz := h2.zero
  rw [e6] at hz
  refine ⟨⟨he, (k3 .r7 (by decide) (by decide)).trans h.r7, (k3 .r8 (by decide) (by decide)).trans h.r8,
    (k3 .r9 (by decide) (by decide)).trans h.r9⟩, by rw [R3.mem]; exact stateAt_zero hz,
    VG.Proof.MlDsa.Arm.Sample.absArgs_of hp hr he (by rw [g0, e2 .r6 (by decide), h.env.r6]) g1' g2
      (by rw [g3, e2 .r8 (by decide), h.r8]) (by rw [g12, e2 .r9 (by decide), h.r9])
      (by rw [glr, e2 .r6 (by decide), h.env.r6])⟩

end


/-- After absorbing the message. -/
structure J2 (rate : Nat) (P : VG.Proof.MlDsa.Arm.Sample.Sp) (σ s : State) : Prop where
  j0 : VG.Proof.MlDsa.Arm.Sample.J0 P σ s
  repr : Spec.Sha3.Repr s.mem P.S rate (P.msg σ)
  r0 : s.gpr .r0 = BitVec.ofNat 32 (P.len % rate)

section
variable {P : VG.Proof.MlDsa.Arm.Sample.Sp} {σ : State} (hp : VG.Proof.MlDsa.Arm.Sample.SpOk P σ)
include hp

omit hp in
/-- What `absorb`, `pad` and `squeeze` write, where code may write. -/
theorem wr_calls {s : State} (he : VG.Proof.MlDsa.Arm.Sample.Env P σ s) {rs : List Region}
    (h : ∀ r ∈ rs, (∃ a n, a + n ≤ 2012 ∧ r = ⟨P.at' a, n⟩) ∨ (∃ n, n ≤ 2012 ∧ r = ⟨P.S, n⟩) ∨ r = below s 8) :
    ∀ r ∈ rs, P.Wr σ r := fun r hr => by
  rcases h r hr with ⟨a, n, hn, rfl⟩ | ⟨n, hn, rfl⟩ | rfl
  exacts [VG.Proof.MlDsa.Arm.Sample.wr_scr hn, VG.Proof.MlDsa.Arm.Sample.wr_scr0 hn, VG.Proof.MlDsa.Arm.Sample.wr_below he.sp]

theorem call1_ok {rate : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.Sample.J1 rate P σ s) :
    WP isa absorbCall s (VG.Proof.MlDsa.Arm.Sample.J2 rate P σ) := by
  refine absorb_ok h.args fun s' hk hr h0 => ⟨h.j0.kept hp hk (VG.Proof.MlDsa.Arm.Sample.wr_calls h.j0.env fun r hr => ?_), ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inl ⟨200, by decide, rfl⟩)
    · exact .inl ⟨200, 640, by decide, VG.Proof.MlDsa.Arm.Sample.regA_at hp (by decide) _⟩
    · exact .inr (.inr rfl)
  · have := hr [] (MlKem.repr_nil h.zero) (by simp)
    rwa [List.nil_append, VG.Proof.MlDsa.Arm.Sample.msg_frame hp h.j0.env] at this
  · apply BitVec.eq_of_toNat_eq
    have := Nat.mod_lt P.len (VG.Proof.MlDsa.Arm.Sample.rate_pos h.args.hrate)
    have := rates_lt h.args.hrate
    rw [h0, Nat.zero_add, toNat_ofNat32 (by omega)]

end

/-- The arguments of `pad`. -/
structure J3 (rate : Nat) (P : VG.Proof.MlDsa.Arm.Sample.Sp) (σ s : State) : Prop where
  j0 : VG.Proof.MlDsa.Arm.Sample.J0 P σ s
  repr : Spec.Sha3.Repr s.mem P.S rate (P.msg σ)
  args : PadArgs s P.scr (P.scr + BitVec.ofNat 32 200) rate (P.len % rate) 0x1f

theorem pmovs_ok {rate : Nat} (er : encodable (BitVec.ofNat 32 rate) = true) (s : State) :
    WP isa (.block (padArgs rate)) s fun s' =>
      Regs s s' ∧ s'.gpr .r0 = s.gpr .r6 ∧ s'.gpr .r1 = BitVec.ofNat 32 rate ∧ s'.gpr .r2 = s.gpr .r0 ∧
        s'.gpr .r3 = 0x1f ∧ s'.gpr .lr = s.gpr .r6 + BitVec.ofNat 32 200 := by
  run_block [padArgs, er, and_self, and_true]
  refine ⟨regs_cs _ ?_, by simp⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

section
variable {P : VG.Proof.MlDsa.Arm.Sample.Sp} {σ : State} (hp : VG.Proof.MlDsa.Arm.Sample.SpOk P σ)
include hp

theorem blk2_ok {rate : Nat} (hr : rate ∈ rates) (er : encodable (BitVec.ofNat 32 rate) = true) {s : State}
    (h : VG.Proof.MlDsa.Arm.Sample.J2 rate P σ s) : WP isa (.block (padArgs rate)) s (VG.Proof.MlDsa.Arm.Sample.J3 rate P σ) := by
  refine WP.mono (VG.Proof.MlDsa.Arm.Sample.pmovs_ok er s) fun s' ⟨R, g0, g1, g2, g3, glr⟩ => ?_
  have he := h.j0.env.regs R
  have fs := hp.fscr
  have eb := VG.Proof.MlDsa.Arm.Sample.below_eq he.sp
  refine ⟨h.j0.regs R, by rw [R.mem]; exact h.repr, {
    r0 := by rw [g0, h.j0.env.r6], r1 := g1, r2 := by rw [g2, h.r0], r3 := g3,
    lr := by rw [glr, h.j0.env.r6]
    hrate := hr, hpos := Nat.mod_lt _ (VG.Proof.MlDsa.Arm.Sample.rate_pos hr), sp := by rw [he.sp]; exact hp.sp8
    fst := fit_le (by decide) fs, fscr := fit_add (fit_le (by decide) fs) (by decide) (by decide)
    d_st_scr := by rw [VG.Proof.MlDsa.Arm.Sample.regA_at hp (by decide)]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)
    b_st := by rw [eb]; exact hp.b_scr.sub_right (VG.Proof.MlDsa.Arm.Sample.sub_scr0 (by decide))
    b_scr := by rw [eb, VG.Proof.MlDsa.Arm.Sample.regA_at hp (by decide)]; exact hp.b_scr.sub_right (VG.Proof.MlDsa.Arm.Sample.sub_scr (by decide))
    cw := by
      rw [VG.Proof.MlDsa.Arm.Sample.regA_at hp (by decide)]
      refine VG.Proof.MlDsa.Arm.Sample.covScr hp he fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [⟨0, (add_ofNat_zero _).symm, by simp⟩, ⟨200, rfl, by simp⟩] }⟩

end

/-- After padding. -/
structure J4 (rate : Nat) (P : VG.Proof.MlDsa.Arm.Sample.Sp) (σ s : State) : Prop where
  j0 : VG.Proof.MlDsa.Arm.Sample.J0 P σ s
  st : stateAt s.mem P.S = padded rate Spec.Sha3.shakeSuffix (P.msg σ)

section
variable {P : VG.Proof.MlDsa.Arm.Sample.Sp} {σ : State} (hp : VG.Proof.MlDsa.Arm.Sample.SpOk P σ)
include hp

theorem call2_ok {rate : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.Sample.J3 rate P σ s) : WP isa padCall s (VG.Proof.MlDsa.Arm.Sample.J4 rate P σ) := by
  refine pad_ok h.args fun s' hk hst => ⟨h.j0.kept hp hk (VG.Proof.MlDsa.Arm.Sample.wr_calls h.j0.env fun r hr => ?_), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inl ⟨200, by decide, rfl⟩)
    · exact .inl ⟨200, 640, by decide, VG.Proof.MlDsa.Arm.Sample.regA_at hp (by decide) _⟩
    · exact .inr (.inr rfl)
  · rw [hst (P.msg σ) h.repr (by rw [MlKem.bytesAt_length]), MlKem.shakeSuffix32]

end

/-- The arguments of `squeeze`. -/
structure J5 (rate outlen : Nat) (P : VG.Proof.MlDsa.Arm.Sample.Sp) (σ s : State) : Prop where
  j4 : VG.Proof.MlDsa.Arm.Sample.J4 rate P σ s
  args : SqueezeArgs s P.scr (P.scr + BitVec.ofNat 32 200) (P.scr + BitVec.ofNat 32 840) rate 0 outlen

theorem smovs_ok {rate outlen : Nat} (er : encodable (BitVec.ofNat 32 rate) = true)
    (eo : encodable (BitVec.ofNat 32 outlen) = true) (s : State) :
    WP isa (.block (sqzArgs rate outlen)) s fun s' =>
      Regs s s' ∧ s'.gpr .r0 = s.gpr .r6 ∧ s'.gpr .r1 = BitVec.ofNat 32 rate ∧ s'.gpr .r2 = BitVec.ofNat 32 0 ∧
        s'.gpr .r3 = s.gpr .r6 + BitVec.ofNat 32 840 ∧ s'.gpr .r12 = BitVec.ofNat 32 outlen ∧
        s'.gpr .lr = s.gpr .r6 + BitVec.ofNat 32 200 := by
  run_block [sqzArgs, er, eo, and_self, and_true]
  refine ⟨regs_cs _ ?_, by simp⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

section
variable {P : VG.Proof.MlDsa.Arm.Sample.Sp} {σ : State} (hp : VG.Proof.MlDsa.Arm.Sample.SpOk P σ)
include hp

theorem blk3_ok {rate outlen : Nat} (hr : rate ∈ rates) (ho : 840 + outlen ≤ 2012)
    (er : encodable (BitVec.ofNat 32 rate) = true) (eo : encodable (BitVec.ofNat 32 outlen) = true) {s : State}
    (h : VG.Proof.MlDsa.Arm.Sample.J4 rate P σ s) : WP isa (.block (sqzArgs rate outlen)) s (VG.Proof.MlDsa.Arm.Sample.J5 rate outlen P σ) := by
  refine WP.mono (VG.Proof.MlDsa.Arm.Sample.smovs_ok er eo s) fun s' ⟨R, g0, g1, g2, g3, g12, glr⟩ => ?_
  have he := h.j0.env.regs R
  have fs := hp.fscr
  have eb := VG.Proof.MlDsa.Arm.Sample.below_eq he.sp
  refine ⟨⟨h.j0.regs R, by rw [R.mem]; exact h.st⟩, {
    r0 := by rw [g0, h.j0.env.r6], r1 := g1, r2 := g2, r3 := by rw [g3, h.j0.env.r6], r12 := g12,
    lr := by rw [glr, h.j0.env.r6]
    hrate := hr, hpos := Nat.zero_le _, hlen := by omega, sp := by rw [he.sp]; exact hp.sp8
    fst := fit_le (by decide) fs, fscr := fit_add (fit_le (by decide) fs) (by decide) (by decide)
    fout := by rw [BitVec.toNat_add, toNat_ofNat32 (by decide)]; omega
    d_st_out := by rw [VG.Proof.MlDsa.Arm.Sample.regA_at hp (by decide)]; exact Offset.base_disjoint _ (by omega) (by omega)
    d_st_scr := by rw [VG.Proof.MlDsa.Arm.Sample.regA_at hp (by decide)]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)
    d_out_scr := by
      rw [VG.Proof.MlDsa.Arm.Sample.regA_at hp (by decide), VG.Proof.MlDsa.Arm.Sample.regA_at hp (by decide)]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
    b_st := by rw [eb]; exact hp.b_scr.sub_right (VG.Proof.MlDsa.Arm.Sample.sub_scr0 (by decide))
    b_out := by rw [eb, VG.Proof.MlDsa.Arm.Sample.regA_at hp (by decide)]; exact hp.b_scr.sub_right (VG.Proof.MlDsa.Arm.Sample.sub_scr (by omega))
    b_scr := by rw [eb, VG.Proof.MlDsa.Arm.Sample.regA_at hp (by decide)]; exact hp.b_scr.sub_right (VG.Proof.MlDsa.Arm.Sample.sub_scr (by decide))
    cw := by
      rw [VG.Proof.MlDsa.Arm.Sample.regA_at hp (by decide), VG.Proof.MlDsa.Arm.Sample.regA_at hp (by decide)]
      refine VG.Proof.MlDsa.Arm.Sample.covScr hp he fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [⟨0, (add_ofNat_zero _).symm, by simp⟩, ⟨840, rfl, by simp; omega⟩, ⟨200, rfl, by simp⟩] }⟩

end

/-- After squeezing: the output, and the parameter in `r7`. -/
structure J6 (rate outlen : Nat) (P : VG.Proof.MlDsa.Arm.Sample.Sp) (σ s : State) : Prop where
  env : VG.Proof.MlDsa.Arm.Sample.Env P σ s
  r7 : s.gpr .r7 = P.prm
  out : bytesAt s.mem (P.at' 840) outlen =
    squeezeFrom rate (padded rate Spec.Sha3.shakeSuffix (P.msg σ)) 0 outlen

section
variable {P : VG.Proof.MlDsa.Arm.Sample.Sp} {σ : State} (hp : VG.Proof.MlDsa.Arm.Sample.SpOk P σ)
include hp

theorem call3_ok {rate outlen : Nat} (ho : 840 + outlen ≤ 2012) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.J5 rate outlen P σ s) :
    WP isa squeezeCall s (VG.Proof.MlDsa.Arm.Sample.J6 rate outlen P σ) := by
  refine squeeze_ok h.args fun s' hk hout _ _ => ?_
  have j0 := h.j4.j0.kept hp hk (VG.Proof.MlDsa.Arm.Sample.wr_calls h.j4.j0.env fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact .inr (.inl ⟨200, by decide, rfl⟩)
    · exact .inl ⟨840, outlen, by omega, VG.Proof.MlDsa.Arm.Sample.regA_at hp (by decide) _⟩
    · exact .inl ⟨200, 640, by decide, VG.Proof.MlDsa.Arm.Sample.regA_at hp (by decide) _⟩
    · exact .inr (.inr rfl))
  refine ⟨j0.env, j0.r7, ?_⟩
  rw [← VG.Proof.MlDsa.Arm.Sample.at_eq hp (by decide), hout, show State.addr P.scr = P.S from rfl, h.j4.st]

/-- The sponge, from `J0`: `outlen` bytes of SHAKE (of rate `rate`) of the
message at `scratch + 840`. -/
theorem sponge_ok {rate outlen : Nat} (hr : rate ∈ rates) (ho : 840 + outlen ≤ 2012)
    (er : encodable (BitVec.ofNat 32 rate) = true) (eo : encodable (BitVec.ofNat 32 outlen) = true) {s : State}
    (h : VG.Proof.MlDsa.Arm.Sample.J0 P σ s) : WP isa (sponge rate outlen) s (VG.Proof.MlDsa.Arm.Sample.J6 rate outlen P σ) :=
  WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.blk1_ok hp hr er h) fun _ h1 =>
    WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.call1_ok hp h1) fun _ h2 => WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.blk2_ok hp hr er h2) fun _ h3 =>
      WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.call2_ok hp h3) fun _ h4 => WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.blk3_ok hp hr ho er eo h4) fun _ h5 =>
        VG.Proof.MlDsa.Arm.Sample.call3_ok hp ho h5)))))

end


/-! ## Constant time

Two runs, from entry states `σ₁` and `σ₂` whose calls agree (the same `P`,
and the same stack pointer), each related to its own entry state by the
invariants of the correctness proof. -/

/-- Code the taint analysis proves constant time from the registers `rs`,
which hold the same values in runs related by `R`. -/
theorem taintRel {R : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, R x y → ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa R c fun _ _ => True :=
  RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs rs) (fun a b hab => Taint.agree_ofRegs (hr a b hab)) h

/-- A piece that leaks the same in both runs, with what correctness says of
each. -/
theorem relW {c : Prog isa} {R : State → State → Prop} {F₁ F₂ : State → Prop}
    (hct : RelCT isa R c fun _ _ => True) (hw : ∀ a b, R a b → WP isa c a F₁ ∧ WP isa c b F₂) :
    RelCT isa R c fun a b => F₁ a ∧ F₂ b :=
  (hct.wp hw).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩

/-- `rs` hold the same values in both runs. -/
theorem env_regs {P : VG.Proof.MlDsa.Arm.Sample.Sp} {σ₁ σ₂ a b : State} (e₁ : VG.Proof.MlDsa.Arm.Sample.Env P σ₁ a) (e₂ : VG.Proof.MlDsa.Arm.Sample.Env P σ₂ b) :
    a.gpr .r5 = b.gpr .r5 ∧ a.gpr .r6 = b.gpr .r6 := ⟨by rw [e₁.r5, e₂.r5], by rw [e₁.r6, e₂.r6]⟩

theorem j0_regs {P : VG.Proof.MlDsa.Arm.Sample.Sp} {σ₁ σ₂ a b : State} (h₁ : VG.Proof.MlDsa.Arm.Sample.J0 P σ₁ a) (h₂ : VG.Proof.MlDsa.Arm.Sample.J0 P σ₂ b) :
    ∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9], a.gpr r = b.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [(VG.Proof.MlDsa.Arm.Sample.env_regs h₁.env h₂.env).1, (VG.Proof.MlDsa.Arm.Sample.env_regs h₁.env h₂.env).2, by rw [h₁.r7, h₂.r7],
    by rw [h₁.r8, h₂.r8], by rw [h₁.r9, h₂.r9]]


section
variable {P : VG.Proof.MlDsa.Arm.Sample.Sp} {σ₁ σ₂ : State} (hp₁ : VG.Proof.MlDsa.Arm.Sample.SpOk P σ₁) (hp₂ : VG.Proof.MlDsa.Arm.Sample.SpOk P σ₂) (hsp : σ₁.sp = σ₂.sp)
include hp₁ hp₂ hsp

/-- The sponge leaks the same in both runs. The blocks are proven constant
time by the taint analysis (`c1`, `c2`, `c3`: `by taint_decide` for the
rate and length used). -/
theorem sponge_ct {rate outlen : Nat} (hr : rate ∈ rates) (ho : 840 + outlen ≤ 2012)
    (er : encodable (BitVec.ofNat 32 rate) = true) (eo : encodable (BitVec.ofNat 32 outlen) = true)
    {h1 h2 h3 : VG.Taint.Hint VG.Arm.taint.T}
    (c1 : (VG.Arm.taint.check (Taint.ofRegs [.r5, .r6, .r7, .r8, .r9]) (.block (absArgs rate)) h1).isSome = true)
    (c2 : (VG.Arm.taint.check (Taint.ofRegs [.r0, .r5, .r6]) (.block (padArgs rate)) h2).isSome = true)
    (c3 : (VG.Arm.taint.check (Taint.ofRegs [.r5, .r6]) (.block (sqzArgs rate outlen)) h3).isSome = true) :
    RelCT isa (fun a b => VG.Proof.MlDsa.Arm.Sample.J0 P σ₁ a ∧ VG.Proof.MlDsa.Arm.Sample.J0 P σ₂ b) (sponge rate outlen)
      (fun a b => VG.Proof.MlDsa.Arm.Sample.J6 rate outlen P σ₁ a ∧ VG.Proof.MlDsa.Arm.Sample.J6 rate outlen P σ₂ b) := by
  refine RelCT.seq (VG.Proof.MlDsa.Arm.Sample.relW (VG.Proof.MlDsa.Arm.Sample.taintRel _ (fun a b h => VG.Proof.MlDsa.Arm.Sample.j0_regs h.1 h.2) c1)
    fun a b h => ⟨VG.Proof.MlDsa.Arm.Sample.blk1_ok hp₁ hr er h.1, VG.Proof.MlDsa.Arm.Sample.blk1_ok hp₂ hr er h.2⟩) ?_
  refine RelCT.seq (VG.Proof.MlDsa.Arm.Sample.relW (absorb_ct fun a b h => ⟨by rw [h.1.j0.env.sp, h.2.j0.env.sp, hsp], _, _, _, _, _, _,
      h.1.args, h.2.args⟩) fun a b h => ⟨VG.Proof.MlDsa.Arm.Sample.call1_ok hp₁ h.1, VG.Proof.MlDsa.Arm.Sample.call1_ok hp₂ h.2⟩) ?_
  refine RelCT.seq (VG.Proof.MlDsa.Arm.Sample.relW (VG.Proof.MlDsa.Arm.Sample.taintRel _ (fun a b h r hr' => ?_) c2)
    fun a b h => ⟨VG.Proof.MlDsa.Arm.Sample.blk2_ok hp₁ hr er h.1, VG.Proof.MlDsa.Arm.Sample.blk2_ok hp₂ hr er h.2⟩) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    exacts [by rw [h.1.r0, h.2.r0], (VG.Proof.MlDsa.Arm.Sample.env_regs h.1.j0.env h.2.j0.env).1, (VG.Proof.MlDsa.Arm.Sample.env_regs h.1.j0.env h.2.j0.env).2]
  refine RelCT.seq (VG.Proof.MlDsa.Arm.Sample.relW (pad_ct fun a b h => ⟨by rw [h.1.j0.env.sp, h.2.j0.env.sp, hsp], _, _, _, _, _,
      h.1.args, h.2.args⟩) fun a b h => ⟨VG.Proof.MlDsa.Arm.Sample.call2_ok hp₁ h.1, VG.Proof.MlDsa.Arm.Sample.call2_ok hp₂ h.2⟩) ?_
  refine RelCT.seq (VG.Proof.MlDsa.Arm.Sample.relW (VG.Proof.MlDsa.Arm.Sample.taintRel _ (fun a b h r hr' => ?_) c3)
    fun a b h => ⟨VG.Proof.MlDsa.Arm.Sample.blk3_ok hp₁ hr ho er eo h.1, VG.Proof.MlDsa.Arm.Sample.blk3_ok hp₂ hr ho er eo h.2⟩) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    exacts [(VG.Proof.MlDsa.Arm.Sample.env_regs h.1.j0.env h.2.j0.env).1, (VG.Proof.MlDsa.Arm.Sample.env_regs h.1.j0.env h.2.j0.env).2]
  exact VG.Proof.MlDsa.Arm.Sample.relW (squeeze_ct fun a b h => ⟨by rw [h.1.j4.j0.env.sp, h.2.j4.j0.env.sp, hsp], _, _, _, _, _, _,
      h.1.args, h.2.args⟩) fun a b h => ⟨VG.Proof.MlDsa.Arm.Sample.call3_ok hp₁ ho h.1, VG.Proof.MlDsa.Arm.Sample.call3_ok hp₂ ho h.2⟩

end

end VG.Proof.MlDsa.Arm.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sample.Pro`. -/
section

/-!
# ML-DSA on 32-bit ARM: the sampling functions' prologue and epilogue

The prologue (`pro`) saves our caller's `r4`–`r11` and `lr` in the working
space and sets up the layout: from what it leaves, `J0` holds (`pro_ok`, for
any registers, and `pro_rn`, `pro_rb`, `pro_ball` for the three ways the
functions call it). The epilogue (`epi`) restores them: with `Env`, the
calling convention's obligations hold at the end (`epi_ok`, `retEpi_ok`, which
also returns `j >> 8`). The pieces of the loops: `storeJ` stores the next
coefficient `a[j]` (`storeJ_ok`), `jFull` tests `j ≥ 256` (`jFull_ok`), `step`
advances (`step_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Sample

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Arm.RegUpd (gpr_setReg_self gpr_setReg_of_ne sp_setReg mem_setReg)
open VG.Proof.MlKem.Arm.Sample (Regs regs_cs)
open VG.Impl.MlDsa.Arm.Sample
open VG.Impl.MlKem.Arm (saveRegs restoreRegs savedRegs)
open VG.Spec.MlDsa (Zq)
open VG.Proof.MlDsa.Sample (coeffAddr coeff_contains Stored stored_snoc zw)

/-! ## The prologue -/

theorem savedRegs_preserved : ∀ i < 8, savedRegs.getD i .r4 ∈ preserved := by decide

section
variable {P : VG.Proof.MlDsa.Arm.Sample.Sp} {σ : State} (hp : VG.Proof.MlDsa.Arm.Sample.SpOk P σ)
include hp

/-- A part of the working space, in the writable regions of the entry state. -/
theorem inScrσ {a n : Nat} (h : a + n ≤ 2048) : InRegions σ.wr (P.at' a) n := by
  rw [hp.wr]
  exact ⟨P.scrR, by simp, Offset.contains_base _ h (by omega)⟩

/-- The prologue, from a state `s` that differs from the entry state `σ`
only in registers that are not callee-saved, given what its moves leave. -/
theorem pro_ok {scr a msg : Reg} {prm len : Op2} {s : State} (hm : s.mem = σ.mem) (hrd : s.rd = σ.rd)
    (hwr : s.wr = σ.wr) (hsp : s.sp = σ.sp) (hcs : ∀ r ∈ preserved, s.gpr r = σ.gpr r)
    (hscr : s.gpr scr = P.scr)
    (hmv : ∀ t : State, t.gpr = s.gpr → WP isa (.block [.mov .r5 (.reg a), .mov .r6 (.reg scr), .mov .r7 prm,
      .mov .r8 (.reg msg), .mov .r9 len]) t fun t' => t'.gpr .r5 = P.a ∧ t'.gpr .r6 = P.scr ∧
        t'.gpr .r7 = P.prm ∧ t'.gpr .r8 = P.sd ∧ t'.gpr .r9 = BitVec.ofNat 32 P.len ∧ t'.mem = t.mem ∧
        t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp) :
    WP isa (.block (pro scr a prm len msg)) s (VG.Proof.MlDsa.Arm.Sample.J0 P σ) := by
  have fs := hp.fscr
  unfold pro
  rw [WP.block_append_iff]
  refine WP.mono (saveRegs_ok scr (off := 2012) (by decide) (by rw [hscr]; omega) fun i hi => by
    rw [hscr, add_ofNat_add, hwr]; exact VG.Proof.MlDsa.Arm.Sample.inScrσ hp (by omega)) fun s1 h1 => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  have ea : State.addr (s1.gpr scr + BitVec.ofNat 32 (2012 + 32)) = P.at' 2044 := by
    rw [h1.gpr, hscr]; exact VG.Proof.MlDsa.Arm.Sample.at_eq hp (by decide)
  refine WP.mono (Q := fun s2 => s2 = { s1 with mem := s1.mem.writeW (P.at' 2044) (s1.gpr .lr) }) ?_
    fun s2 e2 => ?_
  · apply WP.of_runBlock
    rw [runBlock_cons, exec_str (by decide) (by rw [ea, h1.wr, hwr]; exact VG.Proof.MlDsa.Arm.Sample.inScrσ hp (by omega)), runStep_some,
      runBlock_nil]
    exact ⟨_, rfl, by rw [ea]⟩
  subst e2
  refine WP.mono (hmv _ h1.gpr) fun s3 ⟨g5, g6, g7, g8, g9, m3, rd3, wr3, sp3⟩ => ⟨⟨?_, ?_, ?_, g5, g6, ?_, ?_, ?_⟩,
    g7, g8, g9⟩
  · rw [rd3, h1.rd, hrd]
  · rw [wr3, h1.wr, hwr]
  · rw [sp3, h1.sp, hsp]
  · intro i hi
    have hs := h1.saved i hi
    rw [hscr, add_ofNat_add] at hs
    rw [m3]
    show (s1.mem.writeW _ _).readW _ _ = _
    rw [add_ofNat_add, Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide), hs,
      hcs _ (VG.Proof.MlDsa.Arm.Sample.savedRegs_preserved i hi)]
  · rw [m3]
    show (s1.mem.writeW _ _).readW _ _ = _
    rw [Mem.readW_writeW_self32, h1.gpr, hcs .lr (by decide)]
  · rw [m3, ← hm]
    show Frame _ s.mem (s1.mem.writeW _ _)
    have f1 := h1.frame
    rw [hscr] at f1
    refine (f1.sub fun r hr => ⟨P.scrR, by simp, ?_⟩).writeW (r := P.scrR) (by simp) _
      (Offset.contains_base _ (d := 2044) (by omega) (by omega))
    rw [List.mem_singleton] at hr; subst hr
    exact VG.Proof.MlDsa.Arm.Sample.sub_scr (by omega)

/-- The prologue of `vg_mldsa_rej_ntt_poly`: `seed = r0`, `a = r1`,
`scratch = r2`. -/
theorem pro_rn (h0 : σ.gpr .r0 = P.sd) (h1 : σ.gpr .r1 = P.a) (h2 : σ.gpr .r2 = P.scr) (hprm : P.prm = 0)
    (hlen : P.len = 34) : WP isa (.block (pro .r2 .r1 (.imm 0) (.imm 34) .r0)) σ (VG.Proof.MlDsa.Arm.Sample.J0 P σ) :=
  VG.Proof.MlDsa.Arm.Sample.pro_ok hp rfl rfl rfl rfl (fun _ _ => rfl) h2 fun t ht => by
    run_block [ht, h0, h1, h2, hprm, hlen, and_self, and_true]

/-- The prologue of `vg_mldsa_rej_bounded_poly` and
`vg_mldsa_expand_mask_poly`: `seed = r0`, the parameter in `r1`, `a = r2`,
`scratch = r3`. -/
theorem pro_rb (h0 : σ.gpr .r0 = P.sd) (h1 : σ.gpr .r1 = P.prm) (h2 : σ.gpr .r2 = P.a) (h3 : σ.gpr .r3 = P.scr)
    (hlen : P.len = 66) : WP isa (.block (pro .r3 .r2 (.reg .r1) (.imm 66) .r0)) σ (VG.Proof.MlDsa.Arm.Sample.J0 P σ) :=
  VG.Proof.MlDsa.Arm.Sample.pro_ok hp rfl rfl rfl rfl (fun _ _ => rfl) h3 fun t ht => by
    run_block [ht, h0, h1, h2, h3, hlen, and_self, and_true]

/-- The prologue of `vg_mldsa_sample_in_ball`: `ctilde = r0`, its length in
`r1`, `tau = r2`, `c = r3` and `scratch` the first stack argument, loaded
into `r12`. -/
theorem pro_ball (h0 : σ.gpr .r0 = P.sd) (h1 : σ.gpr .r1 = BitVec.ofNat 32 P.len) (h2 : σ.gpr .r2 = P.prm)
    (h3 : σ.gpr .r3 = P.a) (hs : stackArg σ 0 = P.scr)
    (hin : InRegions (σ.rd ++ σ.wr) (stackArgAddr σ 0) 4) :
    WP isa (.block (.ldrSp .r12 0 :: pro .r12 .r3 (.reg .r2) (.reg .r1) .r0)) σ (VG.Proof.MlDsa.Arm.Sample.J0 P σ) := by
  rw [← List.singleton_append, WP.block_append_iff]
  have hin' : InRegions (σ.rd ++ σ.wr) (State.addr (σ.sp + BitVec.ofNat 32 0)) 4 := hin
  have hs' : σ.mem.readW (State.addr (σ.sp + BitVec.ofNat 32 0)) 32 = P.scr := hs
  refine WP.mono (Q := fun s => s = σ.setReg .r12 P.scr) (by
    apply WP.of_runBlock
    rw [runBlock_cons]
    simp only [exec, show (0 : Nat) < 4096 from by decide, ite_true, State.load32, hin', Option.map_some, hs',
      runStep_some, runBlock_nil]
    exact ⟨_, rfl, rfl⟩) fun s e => ?_
  subst e
  refine VG.Proof.MlDsa.Arm.Sample.pro_ok hp rfl rfl rfl rfl (fun r hr => gpr_setReg_of_ne _ _ (VG.Proof.MlDsa.Arm.Sample.ne_r12 hr)) (gpr_setReg_self _ _ _)
    fun t ht => ?_
  have g : ∀ r, r ≠ .r12 → t.gpr r = σ.gpr r := fun r hr => by rw [ht, gpr_setReg_of_ne _ _ hr]
  have g12 : t.gpr .r12 = P.scr := by rw [ht, gpr_setReg_self]
  have g0 := g .r0 (by decide)
  have g1 := g .r1 (by decide)
  have g2 := g .r2 (by decide)
  have g3 := g .r3 (by decide)
  run_block [g0, g1, g2, g3, g12, h0, h1, h2, h3, and_self, and_true]

end


/-! ## The epilogue -/

theorem preserved_saved : ∀ r ∈ preserved, r ≠ .lr → ∃ i < 8, savedRegs.getD i .r4 = r := by decide

section
variable {P : VG.Proof.MlDsa.Arm.Sample.Sp} {σ : State} (hp : VG.Proof.MlDsa.Arm.Sample.SpOk P σ)
include hp

/-- The epilogue: our caller's registers restored, `r0` and the memory
unchanged. -/
theorem epi_ok {s : State} (he : VG.Proof.MlDsa.Arm.Sample.Env P σ s) :
    WP isa (.block epi) s fun s' => abiPreserved σ s' ∧ s'.mem = s.mem ∧ s'.gpr .r0 = s.gpr .r0 := by
  have fs := hp.fscr
  unfold epi
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (Q := fun s1 => s1 = s.setReg .r3 P.scr) (by
    apply WP.of_runBlock
    simp only [runBlock_cons, exec, Op2.eval, Option.map_some, runStep_some, runBlock_nil, he.r6]
    exact ⟨_, rfl, rfl⟩) fun s1 e1 => ?_
  subst e1
  have g3 : (s.setReg .r3 P.scr).gpr .r3 = P.scr := gpr_setReg_self _ _ _
  rw [WP.block_append_iff]
  refine WP.mono (restoreRegs_ok .r3 (by decide) (off := 2012) (by decide) (by rw [g3]; omega)
    (g := σ.gpr) (by rw [g3]; exact he.sav) fun i hi => by
      rw [g3, add_ofNat_add]; exact VG.Proof.MlDsa.Arm.Sample.inScrRd hp he (by omega)) fun s2 h2 => ?_
  have e3 : s2.gpr .r3 = P.scr := by rw [h2.other .r3 (by decide), g3]
  have ea : State.addr (s2.gpr .r3 + BitVec.ofNat 32 (2012 + 32)) = P.at' 2044 := by
    rw [e3]; exact VG.Proof.MlDsa.Arm.Sample.at_eq hp (by decide)
  refine WP.mono (Q := fun s3 => s3 = s2.setReg .lr (s2.mem.readW (P.at' 2044) 32)) (by
    apply WP.of_runBlock
    rw [runBlock_cons, exec_ldr (by decide) (by rw [ea, h2.rd, h2.wr]; exact VG.Proof.MlDsa.Arm.Sample.inScrRd hp he (by omega)),
      runStep_some, runBlock_nil, ea]
    exact ⟨_, rfl, rfl⟩) fun s3 e3' => ?_
  subst e3'
  refine ⟨⟨fun r hr => ?_, by rw [sp_setReg, h2.sp]; exact he.sp⟩, by rw [mem_setReg, h2.mem]; rfl, ?_⟩
  · by_cases e : r = .lr
    · subst e
      rw [gpr_setReg_self, h2.mem]; exact he.savlr
    · obtain ⟨i, hi, rfl⟩ := VG.Proof.MlDsa.Arm.Sample.preserved_saved r hr e
      rw [gpr_setReg_of_ne _ _ e]; exact h2.loaded i hi
  · rw [gpr_setReg_of_ne _ _ (by decide), h2.other .r0 (by decide), gpr_setReg_of_ne _ _ (by decide)]

/-- The end of a sampling function that returns whether `j` (in `r2`) is 256. -/
theorem retEpi_ok {s : State} (he : VG.Proof.MlDsa.Arm.Sample.Env P σ s) {j : Nat} (hj : s.gpr .r2 = BitVec.ofNat 32 j) (hj' : j ≤ 256) :
    WP isa (.block (retJ ++ epi)) s fun s' =>
      s'.gpr .r0 = (if j = 256 then 1 else 0) ∧ s'.mem = s.mem ∧ abiPreserved σ s' := by
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun s1 => s1 = s.setReg .r0 (s.gpr .r2 >>> 8)) (by
    apply WP.of_runBlock
    set_option linter.unusedSimpArgs false in
    simp only [retJ, runBlock_cons, exec, Op2.eval, Option.map_some, runStep_some, runBlock_nil]
    exact ⟨_, rfl, rfl⟩) fun s1 e1 => ?_
  subst e1
  have he1 : VG.Proof.MlDsa.Arm.Sample.Env P σ (s.setReg .r0 (s.gpr .r2 >>> 8)) :=
    he.regs ⟨fun r hr _ => gpr_setReg_of_ne _ _ (by rintro rfl; exact absurd hr (by decide)), rfl, rfl, rfl, rfl⟩
  refine WP.mono (VG.Proof.MlDsa.Arm.Sample.epi_ok hp he1) fun s' ⟨ha, hm, h0⟩ => ⟨?_, hm, ha⟩
  rw [h0, gpr_setReg_self, hj, MlKem.Arm.Sample.ret_val hj']

/-- The end of a sampling function that returns nothing. -/
theorem epi_ok' {s : State} (he : VG.Proof.MlDsa.Arm.Sample.Env P σ s) :
    WP isa (.block epi) s fun s' => s'.mem = s.mem ∧ abiPreserved σ s' :=
  WP.mono (VG.Proof.MlDsa.Arm.Sample.epi_ok hp he) fun _ h => ⟨h.2.1, h.1⟩

end

/-! ## Pieces of the loops -/

/-- The sign bit of `x - y`, compared with zero: `Z` is `y ≤ x`. -/
theorem sgn_z {x y : BitVec 32} (hx : x.toNat < 2 ^ 31) (hy : y.toNat < 2 ^ 31) :
    ((x - y) >>> 31 - 0 == 0) = decide (y.toNat ≤ x.toNat) := by
  by_cases h : y.toNat ≤ x.toNat
  · have e : (x - y) >>> 31 = 0 := by bv_omega
    rw [e, decide_eq_true h]; rfl
  · have e : (x - y) >>> 31 = 1 := by bv_omega
    rw [e, decide_eq_false h]; rfl

/-- `r11 ← x - y`, its sign bit, compared with zero: `Z` is `y ≤ x`. -/
theorem sgn_ok (s : State) (x : Reg) (op : Op2) {y : BitVec 32} (hy : op.eval s = some y)
    (hx : (s.gpr x).toNat < 2 ^ 31) (hy' : y.toNat < 2 ^ 31) :
    WP isa (.block [.dp .sub .r11 x op, .mov .r11 (.shifted .r11 .lsr 31), .cmp .r11 (.imm 0)]) s fun s' =>
      s'.z = decide (y.toNat ≤ (s.gpr x).toNat) ∧ (∀ r, r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e := VG.Proof.MlDsa.Arm.Sample.sgn_z hx hy'
  apply WP.of_runBlock
  rw [runBlock_cons, show exec (.dp .sub .r11 x op) s = some (s.setReg .r11 (s.gpr x - y)) by
    simp only [exec, hy, Option.map_some], runStep_some]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    Op2.eval, isa, State.setReg, subFlags, ite_true, Option.map_some, Option.some.injEq,
    exists_eq_left', e, and_self, and_true, true_and]
  exact fun r hr => by simp [hr]

/-- `jFull`: `Z` is `j ≥ 256`, for `j` (in `r2`) less than `2³¹`. -/
theorem jFull_ok (s : State) {j : Nat} (hj : s.gpr .r2 = BitVec.ofNat 32 j) (hj' : j < 2 ^ 31) :
    WP isa (.block jFull) s fun s' =>
      s'.z = decide (256 ≤ j) ∧ (∀ r, r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have ht : (s.gpr .r2).toNat = j := by rw [hj, toNat_ofNat32 (by omega)]
  refine WP.mono (VG.Proof.MlDsa.Arm.Sample.sgn_ok s .r2 (.imm 256) (y := 256) rfl (by omega) (by decide)) fun s' h => ⟨?_, h.2⟩
  rw [h.1, ht]; rfl

/-- `step k`: `r0 ← r0 + k`, `r3 ← r3 - 1`, `Z` if it is zero. -/
theorem step_ok (s : State) {k : Nat} (ek : encodable (BitVec.ofNat 32 k) = true) :
    WP isa (.block (VG.Impl.MlDsa.Arm.Sample.step k)) s fun s' =>
      s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 k ∧ s'.gpr .r3 = s.gpr .r3 - 1 ∧ s'.z = (s.gpr .r3 - 1 == 0) ∧
        (∀ r, r ≠ .r0 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp := by
  run_block [VG.Impl.MlDsa.Arm.Sample.step, ek, and_self, and_true, true_and]
  exact fun r h0 h3 => by simp [h0, h3]

theorem shl2 (j : Nat) : BitVec.ofNat 32 j <<< 2 = BitVec.ofNat 32 (4 * j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

section
variable {P : VG.Proof.MlDsa.Arm.Sample.Sp} {σ : State} (hp : VG.Proof.MlDsa.Arm.Sample.SpOk P σ)
include hp

theorem addr_aJ {j : Nat} (hj : j < 256) :
    State.addr (P.a + BitVec.ofNat 32 j <<< 2 + BitVec.ofNat 32 0) = VG.Proof.MlDsa.Sample.coeffAddr P.A j := by
  rw [VG.Proof.MlDsa.Arm.Sample.shl2]; exact addr_coeff hp.fa (by omega) hj

/-- `storeJ v`: `a[j] ← v`, `j ← j + 1`, for `j < 256` in `r2`. -/
theorem storeJ_ok {s : State} (he : VG.Proof.MlDsa.Arm.Sample.Env P σ s) {v : Reg} (hv : v ≠ .r11) {j : Nat}
    (hj : s.gpr .r2 = BitVec.ofNat 32 j) (hj' : j < 256) :
    WP isa (.block (storeJ v)) s fun s' =>
      s'.mem = s.mem.writeW (VG.Proof.MlDsa.Sample.coeffAddr P.A j) (s.gpr v) ∧ s'.gpr .r2 = BitVec.ofNat 32 (j + 1) ∧
        (∀ r, r ≠ .r2 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        s'.z = s.z ∧ VG.Proof.MlDsa.Arm.Sample.Env P σ s' := by
  have ea := VG.Proof.MlDsa.Arm.Sample.addr_aJ hp hj'
  have hin : InRegions s.wr (VG.Proof.MlDsa.Sample.coeffAddr P.A j) 4 := by
    rw [he.wr, hp.wr]; exact ⟨P.aR, by simp, VG.Proof.MlDsa.Sample.coeff_contains _ hj'⟩
  have hv' : ¬ v = .r11 := hv
  refine WP.mono (Q := fun s' : State => s'.mem = s.mem.writeW (VG.Proof.MlDsa.Sample.coeffAddr P.A j) (s.gpr v) ∧
      s'.gpr .r2 = BitVec.ofNat 32 (j + 1) ∧ (∀ r, r ≠ .r2 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.z = s.z) ?_ fun s' h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
        h.2.2.2.2.2.1, h.2.2.2.2.2.2, he.step hp (rs := [P.aR]) (by
          rw [h.1]; exact (Frame.refl _ _).writeW (by simp) _ (VG.Proof.MlDsa.Sample.coeff_contains _ hj'))
          (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl fun _ h => h))
          (h.2.2.1 _ (by decide) (by decide)) (h.2.2.1 _ (by decide) (by decide)) h.2.2.2.1 h.2.2.2.2.1
          h.2.2.2.2.2.1⟩
  run_block [storeJ, hj, he.r5, ea, hin, hv', and_self, and_true, true_and]
  refine ⟨?_, fun r h2 h11 => ?_⟩
  · rw [BitVec.ofNat_add]; rfl
  · simp [h2, h11]

/-- Storing the next coefficient `x` of the list `L` stored at `a`. -/
theorem storeJ_stored {s : State} (he : VG.Proof.MlDsa.Arm.Sample.Env P σ s) {v : Reg} (hv : v ≠ .r11) {L : List Zq}
    (hj : s.gpr .r2 = BitVec.ofNat 32 L.length) (hL : L.length < 256) (hst : Stored s.mem P.A L) {x : Zq}
    (hx : s.gpr v = zw x) :
    WP isa (.block (storeJ v)) s fun s' =>
      Stored s'.mem P.A (L ++ [x]) ∧ s'.gpr .r2 = BitVec.ofNat 32 (L ++ [x]).length ∧
        (∀ r, r ≠ .r2 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.z = s.z ∧ VG.Proof.MlDsa.Arm.Sample.Env P σ s' ∧
        Frame [P.aR] s.mem s'.mem := by
  refine WP.mono (VG.Proof.MlDsa.Arm.Sample.storeJ_ok hp he hv hj hL) fun s' ⟨hm, h2, hr, _, _, _, hz, he'⟩ => ⟨?_, ?_, hr, hz, he', ?_⟩
  · rw [hm, hx]; exact stored_snoc hst hL x
  · rw [h2, List.length_append, List.length_singleton]
  · rw [hm]; exact (Frame.refl _ _).writeW (by simp) _ (VG.Proof.MlDsa.Sample.coeff_contains _ hL)

end


/-- `Env` after code that writes no memory and keeps `r5` and `r6`. -/
theorem Env.same {P : VG.Proof.MlDsa.Arm.Sample.Sp} {σ s s' : State} (he : VG.Proof.MlDsa.Arm.Sample.Env P σ s) (hm : s'.mem = s.mem) (g5 : s'.gpr .r5 = s.gpr .r5)
    (g6 : s'.gpr .r6 = s.gpr .r6) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : VG.Proof.MlDsa.Arm.Sample.Env P σ s' :=
  ⟨rd.trans he.rd, wr.trans he.wr, sp.trans he.sp, g5.trans he.r5, g6.trans he.r6, by rw [hm]; exact he.sav,
    by rw [hm]; exact he.savlr, by rw [hm]; exact he.frame⟩

end VG.Proof.MlDsa.Arm.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sample.ExpandMask`. -/
section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_expand_mask_poly`

The function runs in pieces: the prologue (`J0`), the sponge, whose output is
`H(ρ′, 640)` (`J6`), the branch on `γ₁`, and the loop of `vg_mldsa_bit_unpack`
for `c = 1 + bitlen (γ₁ - 1)` on the first `32c` bytes of output
(`Pack.unpackLoop_buFin_ok`, run from the state permitted only those bytes and
`a`, and widened to the function's permissions by `Exec.widen`), which are
`H(ρ′, 32c)` (`H_take`). It is constant time: the taint analysis proves each
piece but the sponge, whose proof is `sponge_ct`, from the pointers and `γ₁`.
-/

namespace VG.Proof.MlDsa.Arm.Sample.ExpandMask

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.Sample
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.Arm.Pack (unpackLoop buFin)
open VG.Spec.MlDsa (Zq q H PolyIs toRq bitUnpack bitlen)
open VG.Spec.Sha3 (bytesAt)

/-- The call, from the entry state: `seed = r0`, `gamma1 = r1`, `a = r2`,
`scratch = r3`. -/
abbrev spOf (σ : State) : VG.Proof.MlDsa.Arm.Sample.Sp := ⟨σ.gpr .r0, 66, σ.gpr .r3, σ.gpr .r2, σ.gpr .r1⟩

/-- `γ₁`. -/
abbrev gam (σ : State) : Nat := (σ.gpr .r1).toNat

/-- The seed. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (State.addr (σ.gpr .r0)) 66

/-- What the proofs need of the entry state. -/
structure Pre (σ : State) : Prop where
  ok : VG.Proof.MlDsa.Arm.Sample.SpOk (VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ) σ
  g : VG.Proof.MlDsa.Arm.Sample.ExpandMask.gam σ = 2 ^ 17 ∨ VG.Proof.MlDsa.Arm.Sample.ExpandMask.gam σ = 2 ^ 19

/-- What the function writes. -/
abbrev Out (σ : State) : Spec.MlDsa.Poly :=
  toRq (bitUnpack (VG.Spec.MlDsa.H (VG.Proof.MlDsa.Arm.Sample.ExpandMask.B σ) (32 * (1 + bitlen (VG.Proof.MlDsa.Arm.Sample.ExpandMask.gam σ - 1)))) (VG.Proof.MlDsa.Arm.Sample.ExpandMask.gam σ - 1) (VG.Proof.MlDsa.Arm.Sample.ExpandMask.gam σ))

/-- After the loop. -/
structure EDone (σ : State) (s : State) : Prop where
  env : VG.Proof.MlDsa.Arm.Sample.Env (VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ) σ s
  out : PolyIs s.mem (VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ).A (VG.Proof.MlDsa.Arm.Sample.ExpandMask.Out σ)

section
variable {σ : State} (hp : VG.Proof.MlDsa.Arm.Sample.SpOk (VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ) σ)
include hp

/-- The loop of `BitUnpack` for `(B, d, c, nb)`, from the output of the
sponge. -/
theorem loop_ok {Bv d c nb : Nat} (hs : Pack.Shape d c nb) (hB : encodable (BitVec.ofNat 32 Bv) = true)
    (hB19 : Bv ≤ 2 ^ 19) (hd : bitlen (Bv - 1 + Bv) = d) (h32 : 32 * d ≤ 640) {s : State}
    (h : VG.Proof.MlDsa.Arm.Sample.J6 136 640 (VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ) σ s) :
    WP isa (.seq (.block [.dp .add .r0 .r6 (.imm 840), .mov .r1 (.reg .r5)]) (unpackLoop (buFin Bv) d c nb)) s
      fun s' => VG.Proof.MlDsa.Arm.Sample.Env (VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ) σ s' ∧ PolyIs s'.mem (VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ).A (toRq (bitUnpack (VG.Spec.MlDsa.H (VG.Proof.MlDsa.Arm.Sample.ExpandMask.B σ) (32 * d)) (Bv - 1) Bv)) := by
  have fs := hp.fscr
  refine WP.seq (WP.mono (Q := fun s1 : State => s1.gpr .r0 = s.gpr .r6 + BitVec.ofNat 32 840 ∧ s1.gpr .r1 = s.gpr .r5 ∧
      s1.gpr .r5 = s.gpr .r5 ∧ s1.gpr .r6 = s.gpr .r6 ∧ s1.mem = s.mem ∧ s1.rd = s.rd ∧ s1.wr = s.wr ∧
      s1.sp = s.sp) (by run_block [and_self, and_true, true_and]; rfl) fun s1 ⟨g0, g1, g5, g6, m, rd, wr, sp⟩ => ?_)
  have e1 := h.env.same m g5 g6 rd wr sp
  have a0 : State.addr (s1.gpr .r0) = (VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ).at' 840 := by rw [g0, h.env.r6]; exact VG.Proof.MlDsa.Arm.Sample.at_eq hp (by omega)
  have a1 : State.addr (s1.gpr .r1) = (VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ).A := by rw [g1, h.env.r5]
  let src : Region := ⟨State.addr (s1.gpr .r0), 32 * d⟩
  let t := s1.withRegions [src] [polyR (State.addr (s1.gpr .r1))]
  have hsep : src.Disjoint (polyR (State.addr (s1.gpr .r1))) := by
    show Region.Disjoint ⟨State.addr (s1.gpr .r0), 32 * d⟩ (polyR (State.addr (s1.gpr .r1)))
    rw [a0, a1]; exact (hp.a_scr.sub_right (VG.Proof.MlDsa.Arm.Sample.sub_scr (a := 840) (n := 32 * d) (by omega))).symm
  have fit0 : (s1.gpr .r0).toNat + 32 * d ≤ 2 ^ 32 := by
    rw [g0, h.env.r6, BitVec.toNat_add, toNat_ofNat32 (by omega)]; omega
  have fit1 : (s1.gpr .r1).toNat + 1024 ≤ 2 ^ 32 := by rw [g1, h.env.r5]; exact hp.fa
  obtain ⟨tr, t', he, hpoly, hf, hk⟩ := Pack.unpackLoop_buFin_ok (s := t) (a := Bv - 1) hs hB hB19 hd
    (List.mem_append_left _ (List.mem_singleton_self _)) (List.mem_singleton_self _) hsep fit0 fit1
  have hc : Covers (t.rd ++ t.wr) (s1.rd ++ s1.wr) := by
    refine Covers.of_sub fun r hr => ?_
    simp only [t, State.withRegions_rd, State.withRegions_wr, List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨(VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ).scrR, List.mem_append_right _ (by rw [e1.wr, hp.wr]; simp), 840, a0, by show 840 + 32 * d ≤ 2048; omega⟩
    · exact ⟨(VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ).aR, List.mem_append_right _ (by rw [e1.wr, hp.wr]; simp), 0,
        by rw [a1]; exact (add_ofNat_zero _).symm, by simp⟩
  have hw : Covers t.wr s1.wr := by
    intro x k ⟨r, hr, hcr⟩
    simp only [t, State.withRegions_wr, List.mem_singleton] at hr
    subst hr
    rw [a1] at hcr
    exact ⟨(VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ).aR, by rw [e1.wr, hp.wr]; simp, hcr⟩
  have he' := Exec.widen he hc hw
  simp only [t, State.withRegions_withRegions, State.withRegions_self] at he'
  refine ⟨tr, _, he', ?_, ?_⟩
  · have hf' : Frame [(VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ).aR] s1.mem t'.mem := by
      have := hf
      simp only [t, State.withRegions_gpr, State.withRegions_mem] at this
      rw [a1] at this; exact this
    exact e1.step hp hf' (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl fun _ h => h))
      (hk.gpr (by decide)) (hk.gpr (by decide)) rfl rfl (hk.2.2.2)
  · show PolyIs t'.mem _ _
    rw [← a1]
    have eb : bytesAt t.mem (State.addr (t.gpr .r0)) (32 * d) = VG.Spec.MlDsa.H (VG.Proof.MlDsa.Arm.Sample.ExpandMask.B σ) (32 * d) := by
      show bytesAt s1.mem (State.addr (s1.gpr .r0)) (32 * d) = _
      rw [a0, m, ← MlKem.bytesAt_take _ _ (show 32 * d ≤ 640 by omega), h.out, ← VG.Proof.MlDsa.Sample.H_eq, VG.Proof.MlDsa.Sample.H_take _ (by omega)]
    rw [eb] at hpoly
    exact hpoly

/-- The branch on `γ₁` and the loop. -/
theorem tail_ok (hg : VG.Proof.MlDsa.Arm.Sample.ExpandMask.gam σ = 2 ^ 17 ∨ VG.Proof.MlDsa.Arm.Sample.ExpandMask.gam σ = 2 ^ 19) {s : State} (h : VG.Proof.MlDsa.Arm.Sample.J6 136 640 (VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ) σ s) :
    WP isa (.seq (.block [.cmp .r7 (.imm 0x20000)]) (.ite .eq (emLoop 18) (emLoop 20))) s (VG.Proof.MlDsa.Arm.Sample.ExpandMask.EDone σ) := by
  refine WP.seq (WP.mono (Q := fun s1 : State => s1.z = decide (VG.Proof.MlDsa.Arm.Sample.ExpandMask.gam σ = 2 ^ 17) ∧ s1.gpr = s.gpr ∧ s1.mem = s.mem ∧
      s1.rd = s.rd ∧ s1.wr = s.wr ∧ s1.sp = s.sp) ?_ fun s1 ⟨z1, g, m, rd, wr, sp⟩ => ?_)
  · have e : (s.gpr .r7 - 0x20000 == 0) = decide (VG.Proof.MlDsa.Arm.Sample.ExpandMask.gam σ = 2 ^ 17) := by
      rw [h.r7]
      show (σ.gpr .r1 - BitVec.ofNat 32 131072 == 0) = _
      rw [cmp_z _ 131072 (by decide)]
    run_block [e, and_self, and_true, true_and]
  have h1 : VG.Proof.MlDsa.Arm.Sample.J6 136 640 (VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ) σ s1 :=
    ⟨h.env.same m (by rw [g]) (by rw [g]) rd wr sp, by rw [g]; exact h.r7, by rw [m]; exact h.out⟩
  refine WP.ite s1.z rfl (fun e => ?_) (fun e => ?_)
  · have hγ : VG.Proof.MlDsa.Arm.Sample.ExpandMask.gam σ = 2 ^ 17 := by rw [z1] at e; simpa using e
    refine WP.mono (VG.Proof.MlDsa.Arm.Sample.ExpandMask.loop_ok hp (Bv := 131072) (c := 4) (nb := 9) (by constructor <;> decide) (by decide) (by decide)
      (by decide) (by decide) h1) fun s' ⟨he, hpo⟩ => ⟨he, ?_⟩
    rw [VG.Proof.MlDsa.Arm.Sample.ExpandMask.Out, hγ]; exact hpo
  · have hγ : VG.Proof.MlDsa.Arm.Sample.ExpandMask.gam σ = 2 ^ 19 := by rw [z1] at e; simp at e; omega
    refine WP.mono (VG.Proof.MlDsa.Arm.Sample.ExpandMask.loop_ok hp (Bv := 524288) (c := 2) (nb := 5) (by constructor <;> decide) (by decide) (by decide)
      (by decide) (by decide) h1) fun s' ⟨he, hpo⟩ => ⟨he, ?_⟩
    rw [VG.Proof.MlDsa.Arm.Sample.ExpandMask.Out, hγ]; exact hpo

end

/-- The function, from an entry state whose regions are those of a call. -/
theorem correct {σ : State} (hp : VG.Proof.MlDsa.Arm.Sample.ExpandMask.Pre σ) : WP isa Impl.MlDsa.Arm.Sample.expandMask σ fun s' =>
    PolyIs s'.mem (State.addr (σ.gpr .r2)) (VG.Proof.MlDsa.Arm.Sample.ExpandMask.Out σ) ∧ abiPreserved σ s' :=
  WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.pro_rb hp.ok rfl rfl rfl rfl rfl) fun _ h1 =>
    WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.sponge_ok hp.ok (rate := 136) (outlen := 640) (by decide) (by decide) (by decide) (by decide) h1)
      fun _ h2 => WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sample.ExpandMask.tail_ok hp.ok hp.g h2) fun _ h3 =>
        WP.mono (VG.Proof.MlDsa.Arm.Sample.epi_ok' hp.ok h3.env) fun _ ⟨hm, ha⟩ => ⟨by rw [hm]; exact h3.out, ha⟩)))

/-! ## Constant time -/

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  p₁ : VG.Proof.MlDsa.Arm.Sample.ExpandMask.Pre σ₁
  p₂ : VG.Proof.MlDsa.Arm.Sample.ExpandMask.Pre σ₂
  sp : σ₁.sp = σ₂.sp
  r0 : σ₁.gpr .r0 = σ₂.gpr .r0
  r1 : σ₁.gpr .r1 = σ₂.gpr .r1
  r2 : σ₁.gpr .r2 = σ₂.gpr .r2
  r3 : σ₁.gpr .r3 = σ₂.gpr .r3

theorem all_ct {σ₁ σ₂ : State} (two : VG.Proof.MlDsa.Arm.Sample.ExpandMask.Two σ₁ σ₂) :
    RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.Arm.Sample.expandMask fun _ _ => True := by
  have hP : VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ₁ = VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ₂ := by simp only [VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf, two.r0, two.r1, two.r2, two.r3]
  have ok₂ : VG.Proof.MlDsa.Arm.Sample.SpOk (VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ₁) σ₂ := hP ▸ two.p₂.ok
  refine RelCT.seq (R := fun a b => VG.Proof.MlDsa.Arm.Sample.J0 (VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ₁) σ₁ a ∧ VG.Proof.MlDsa.Arm.Sample.J0 (VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ₁) σ₂ b) (VG.Proof.MlDsa.Arm.Sample.relW (VG.Proof.MlDsa.Arm.Sample.taintRel [.r0, .r1, .r2, .r3]
      (fun a b h r hr => by
        rw [h.1, h.2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        exacts [two.r0, two.r1, two.r2, two.r3]) (by taint_decide))
    fun a b h => ⟨by rw [h.1]; exact VG.Proof.MlDsa.Arm.Sample.pro_rb two.p₁.ok rfl rfl rfl rfl rfl,
      by rw [h.2]; exact VG.Proof.MlDsa.Arm.Sample.pro_rb ok₂ two.r0.symm two.r1.symm two.r2.symm two.r3.symm rfl⟩) ?_
  refine RelCT.seq (R := fun a b => VG.Proof.MlDsa.Arm.Sample.J6 136 640 (VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ₁) σ₁ a ∧ VG.Proof.MlDsa.Arm.Sample.J6 136 640 (VG.Proof.MlDsa.Arm.Sample.ExpandMask.spOf σ₂) σ₂ b)
    ((VG.Proof.MlDsa.Arm.Sample.sponge_ct two.p₁.ok ok₂ two.sp (rate := 136) (outlen := 640) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide) (by taint_decide) (by taint_decide)).mono (fun _ _ h => h)
      fun a b h => ⟨h.1, hP ▸ h.2⟩) ?_
  refine RelCT.seq (R := fun a b => VG.Proof.MlDsa.Arm.Sample.ExpandMask.EDone σ₁ a ∧ VG.Proof.MlDsa.Arm.Sample.ExpandMask.EDone σ₂ b) (VG.Proof.MlDsa.Arm.Sample.relW (VG.Proof.MlDsa.Arm.Sample.taintRel [.r5, .r6, .r7]
      (fun a b h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.1.env.r5, h.2.env.r5, hP]
        · rw [h.1.env.r6, h.2.env.r6, hP]
        · rw [h.1.r7, h.2.r7, hP]) (by taint_decide))
    fun a b h => ⟨VG.Proof.MlDsa.Arm.Sample.ExpandMask.tail_ok two.p₁.ok two.p₁.g h.1, VG.Proof.MlDsa.Arm.Sample.ExpandMask.tail_ok two.p₂.ok two.p₂.g h.2⟩) ?_
  exact VG.Proof.MlDsa.Arm.Sample.taintRel [.r6] (fun a b h r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [h.1.env.r6, h.2.env.r6, hP]) (by taint_decide)

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlDsa.expandMaskContract Arm.abi 8).pre s) : VG.Proof.MlDsa.Arm.Sample.ExpandMask.Pre s := by
  sig_pre [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h8, -, hrd, hwr, d1, d2, d3, b1, b2, b3, f1, f2, f3, hg⟩ := h
  exact ⟨⟨by rw [hrd]; exact List.mem_singleton_self _, hwr, d1, d2, d3, b1, b2, b3, f1, by show (66 : Nat) < 2 ^ 32; decide, f2, f3, h8⟩, hg⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x20000 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.Arm.Sample.ExpandMask

namespace VG.Proof.MlDsa.Arm.Sample

open VG VG.Arm
open ExpandMask

theorem expandMask_verified :
    Verified Arm.target Impl.MlDsa.Arm.Sample.expandMask (Spec.MlDsa.expandMaskContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpoly, hpres⟩ := VG.Proof.MlDsa.Arm.Sample.ExpandMask.correct (VG.Proof.MlDsa.Arm.Sample.ExpandMask.pre_of hs)
    refine ⟨t, s', he, hpres, ?_⟩
    sig_post [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact hpoly
  · sig_pub [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at hpub
    obtain ⟨hsp, h0, h1, h2, h3⟩ := hpub
    exact (VG.Proof.MlDsa.Arm.Sample.ExpandMask.all_ct ⟨VG.Proof.MlDsa.Arm.Sample.ExpandMask.pre_of h₁, VG.Proof.MlDsa.Arm.Sample.ExpandMask.pre_of h₂, hsp, h0, h1, h2, h3⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨VG.Proof.MlDsa.Arm.Sample.ExpandMask.satState, ?_⟩
    sig_sat_check [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlDsa.Arm.Sample

end
