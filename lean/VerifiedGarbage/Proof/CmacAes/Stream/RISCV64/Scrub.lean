module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Aes.ScrubLocal
public import VerifiedGarbage.Impl.StackScratch.RISCV64
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
meta import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common
meta import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Align
meta import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.Cmac.Mem

/-! ### `CmacAes.Stream.RISCV64.Frame`, which only this module used -/

section

/-! ### `CmacAes.Stream.RISCV64.Verified`, which only this module used -/

section

/-! ### `CmacAes.Stream.RISCV64.Finish`, which only this module used -/

section

/-!
# Streaming AES-CMAC on RISCV64: `vg_cmac_aes_finish`

As on PPC64LE (`Proof/CmacAes/Stream/PPC64LE/Frame.lean`): the code copies
the chaining value to `out`, a byte at a time (`Bytes.copyBytes_ok`), saves
`ra` and `s1` in the scratch buffer at `sv2 S` (`Spill.save_ok`), and calls
`vg_cmac_aes_finalize` with the state as its key, `out` as its state and the
bytes held back as the last bytes; then restores the registers
(`Spill.restore_wp`). The code around the call is constant time by the taint
analysis, and the call by its own proof (`fin_rel`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacAes.Stream.RISCV64
open VG.Proof.AesCbc.RISCV64 (taintRegs wp_sp)
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, `out` (`O`), the scratch
buffer `S` and the rounds `R`. -/
structure HPre (s₀ : State) (St O S : Addr) (R : Nat) : Prop where
  a0 : s₀.gpr .a0 = St
  a3 : s₀.gpr .a3 = O
  a4 : s₀.gpr .a4 = S
  a1 : (s₀.gpr .a1).toNat = R
  rd : s₀.rd = []
  wr : s₀.wr = [⟨St, 304⟩, ⟨O, 16⟩, ⟨S, 2304⟩]
  st_o : (⟨St, 304⟩ : Region).Disjoint ⟨O, 16⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  o_s : (⟨O, 16⟩ : Region).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wO : O.toNat + 16 ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem HPre.of {s₀ : State} (h : finishRISCV64.pre s₀) :
    HPre s₀ (s₀.gpr .a0) (s₀.gpr .a3) (s₀.gpr .a4) (s₀.gpr .a1).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

/-! ## Before the call -/

theorem fin_bound : ∀ p ∈ finSaved, p.2 + 8 ≤ 16 := by decide

/-- What `finish` saves: the registers, with `t0` the slots' base. -/
abbrev finG (s₀ : State) (S : Addr) : Reg → BitVec 64 := (s₀.write .t0 (sv2 S)).gpr

/-- What the code before the call leaves. -/
structure HMid (s₀ : State) (St O S : Addr) (R : Nat) (s : State) : Prop where
  args : FArgs s St O (St + BitVec.ofNat 64 288) S (held (s₀.gpr .a2).toNat) R
  saved : Spill.Saved (sv2 S) (finG s₀ S) finSaved s.mem
  frame : Frame [⟨O, 16⟩, ⟨sv2 S, 16⟩] s₀.mem s.mem
  out : Spec.Aes.bytesAt s.mem O 16 = Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 272) 16
  s1 : s.gpr .s1 = S
  keep : ∀ r ∈ preserved, r ≠ .s1 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem HPre.fargs {s₀ s : State} {St O S : Addr} {R L : Nat} (hp : HPre s₀ St O S R) (hL : L ≤ 16)
    (a0 : s.gpr .a0 = St) (a1 : s.gpr .a1 = s₀.gpr .a1) (a2 : s.gpr .a2 = O)
    (a3 : s.gpr .a3 = St + BitVec.ofNat 64 288) (a4 : s.gpr .a4 = BitVec.ofNat 64 L)
    (a5 : s.gpr .a5 = S) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    FArgs s St O (St + BitVec.ofNat 64 288) S L R := by
  have hw := hp.wSt
  have pSt : Region.Sub ⟨St + BitVec.ofNat 64 288, L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_using [hL])
  exact
  { a0 := a0, a2 := a2, a3 := a3, a4 := a4, a5 := a5
    a1 := by rw [a1]; exact ofNat_toNat_eq hp.a1
    rounds := hp.rounds, len := hL
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left pSt
    ps := (hp.st_s.sub_left pSt).sub_right (Region.sub_prefix (by decide))
    sts := hp.o_s.sub_right (Region.sub_prefix (by decide))
    wrapK := by omega_using [hw]
    wrapSt := hp.wO
    wrapP := by rw [toNat_add_lt St hw (by decide)]; omega_using [hL, hw]
    wrapS := by have := hp.wS; omega_using [this]
    reads := by
      rw [rd, wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega_using [hL]⟩
      · exact ⟨⟨O, 16⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨O, 16⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩ }

/-- What the block before `lastLen` leaves: `HMid` but for `last_len`, which
is `count` in `a4`. -/
structure HMid₀ (s₀ : State) (St O S : Addr) (R : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = St
  a1 : s.gpr .a1 = s₀.gpr .a1
  a2 : s.gpr .a2 = O
  a3 : s.gpr .a3 = St + BitVec.ofNat 64 288
  a4 : s.gpr .a4 = s₀.gpr .a2
  a5 : s.gpr .a5 = S
  saved : Spill.Saved (sv2 S) (finG s₀ S) finSaved s.mem
  frame : Frame [⟨O, 16⟩, ⟨sv2 S, 16⟩] s₀.mem s.mem
  out : Spec.Aes.bytesAt s.mem O 16 = Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 272) 16
  s1 : s.gpr .s1 = S
  keep : ∀ r ∈ preserved, r ≠ .s1 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem finishPre_wp {s₀ : State} {St O S : Addr} {R : Nat} (hp : HPre s₀ St O S R) :
    WP isa (.block finishPre) s₀ (HMid₀ s₀ St O S R) := by
  have hw := hp.wSt
  have hwo := hp.wO
  have sw := hp.wS
  rw [finishPre]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  -- The chaining value to `out`.
  refine WP.mono (Bytes.copyBytes_ok (tmp := .t1) (src := .a0) (dst := .a3) (soff := 272) (doff := 0) (n := 16)
    (by decide) (by decide) (by decide) (by decide) (fun i hi => ?_) (fun i hi => ?_) (fun i hi hc => ?_))
    fun s₁ h₁ => ?_
  · rw [hp.rd, hp.wr, hp.a0]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [hp.wr, hp.a3]; exact ⟨⟨O, 16⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [hp.a3, hp.a0, BitVec.add_zero] at hc
    exact hp.st_o _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hc
  have hcp : Spec.Aes.bytesAt s₁.mem O 16 = Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 272) 16 := by
    apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
    intro j hj _
    simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at hj
    simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range]
    have := h₁.copied j hj
    rw [hp.a3, hp.a0, Nat.zero_add] at this
    rw [this, Offset.add_add]
  have f₁ : Frame [⟨O, 16⟩] s₀.mem s₁.mem := by
    have := h₁.frame; rwa [hp.a3, BitVec.add_zero] at this
  have g₁ (r : Reg) (hr : r ≠ .t1) : s₁.gpr r = s₀.gpr r := h₁.gpr r hr
  rw [WP.block_append_iff]
  refine WP.mono (savePtr2_ok .a4) fun s₂ e => ?_
  subst e
  rw [g₁ _ (by decide), hp.a4, show finSaved.map (fun (r, d) => Instr.store .d r .t0 d) = Spill.saveCode .t0 finSaved
    from rfl]
  have t₀ : (s₁.write .t0 (sv2 S)).gpr .t0 = sv2 S := RegUpd.gpr_write_self _ _ _
  have g₂ (r : Reg) (hr : r ≠ .t0) (h1 : r ≠ .t1) : (s₁.write .t0 (sv2 S)).gpr r = s₀.gpr r := by
    rw [RegUpd.gpr_write_of_ne _ _ hr, g₁ r h1]
  refine Spill.save_ok (b := .t0) (l := finSaved) (by rw [t₀]; exact Align.align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · rw [t₀]
    show InRegions s₁.wr _ 8
    rw [h₁.wr, hp.wr]
    exact ⟨⟨S, 2304⟩, by simp, sv2_contains S (by have := fin_bound p hp'; omega_using [this])⟩
  generalize hv : ({ (s₁.write .t0 (sv2 S)) with
    mem := Spill.saveMem (s₁.write .t0 (sv2 S)).mem ((s₁.write .t0 (sv2 S)).gpr .t0)
      (s₁.write .t0 (sv2 S)).gpr finSaved } : State) = v
  have gv (r : Reg) (hr : r ≠ .t0) (h1 : r ≠ .t1) : v.gpr r = s₀.gpr r := by rw [← hv]; exact g₂ r hr h1
  have mv : v.mem = Spill.saveMem s₁.mem (sv2 S) (s₁.write .t0 (sv2 S)).gpr finSaved := by
    rw [← hv]; show Spill.saveMem _ _ _ _ = _; rw [t₀, RegUpd.mem_write]
  have rdv : v.rd = s₀.rd := by rw [← hv]; show s₁.rd = _; rw [h₁.rd]
  have wrv : v.wr = s₀.wr := by rw [← hv]; show s₁.wr = _; rw [h₁.wr]
  have spv : v.sp = s₀.sp := by rw [← hv]; show s₁.sp = _; rw [h₁.sp]
  unfold Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ =>
    wp_addi (imm := 288) (by decide) fun s₉ u₉ => WP.block_nil ?_
  have fS : Frame [⟨sv2 S, 16⟩] s₁.mem v.mem := by
    rw [mv]; exact Spill.saveMem_frame_base (n := 16) fin_bound (by decide) _ _ _
  have m₉ : s₉.mem = v.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr h1 => ?_, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, gv, hp.a0]
  · simp (disch := decide) only [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, gv]
  · simp (disch := decide) only [u₉.other, u₈.gpr, u₇.other, u₆.other, u₅.other, gv, hp.a3]
  · simp (disch := decide) only [u₉.gpr, u₈.other, u₇.other, u₆.other, u₅.other, gv, hp.a0]
  · simp (disch := decide) only [u₉.other, u₈.other, u₇.gpr, u₆.other, u₅.other, gv]
  · simp (disch := decide) only [u₉.other, u₈.other, u₇.other, u₆.gpr, u₅.other, gv, hp.a4]
  · rw [m₉, mv]
    refine saved_congr (Spill.saveMem_saved (by decide) _ (sv2 S) _) fun p hp' => ?_
    simp only [finSaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · show (s₁.write .t0 (sv2 S)).gpr .ra = finG s₀ S .ra
      rw [RegUpd.gpr_write_of_ne _ _ (by decide), g₁ _ (by decide)]
      exact (RegUpd.gpr_write_of_ne _ _ (by decide)).symm
    · show (s₁.write .t0 (sv2 S)).gpr .s1 = finG s₀ S .s1
      rw [RegUpd.gpr_write_of_ne _ _ (by decide), g₁ _ (by decide)]
      exact (RegUpd.gpr_write_of_ne _ _ (by decide)).symm
  · rw [m₉]
    exact (f₁.mono (by simp)).trans (fS.mono (by simp))
  · rw [m₉, Proof.Cmac.bytesAt_frame16 fS (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.o_s.sub_right (by
        have := sv2_sub S (d := 0) (n := 16) (by decide); rwa [BitVec.add_zero] at this))]
    exact hcp
  · simp (disch := decide) only [u₉.other, u₈.other, u₇.other, u₆.other, u₅.gpr, gv, hp.a4]
  · obtain ⟨h0, h1', -, -, -, -, -, -, -, -, ha2, ha3, ha4, ha5, -⟩ := preserved_ne r hr
    rw [u₉.other _ ha3, u₈.other _ ha2, u₇.other _ ha4, u₆.other _ ha5, u₅.other _ h1, gv _ h0 h1']
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, rdv]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, wrv]
  · rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, spv]

theorem finPre_wp {s₀ : State} {St O S : Addr} {R : Nat} (hp : HPre s₀ St O S R) :
    WP isa finPre s₀ (HMid s₀ St O S R) := by
  refine WP.seq (WP.mono (finishPre_wp hp) fun s₁ h₁ => ?_)
  have hc := (s₀.gpr .a2).isLt
  have h2 : s₀.gpr .a2 = BitVec.ofNat 64 (s₀.gpr .a2).toNat := ofNat_toNat_eq rfl
  have ev := eval_zero_ofNat s₁ .a4 hc (by rw [h₁.a4]; exact h2)
  by_cases h0 : (s₀.gpr .a2).toNat = 0
  · refine WP.ite true (by rw [ev, h0]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨hp.fargs (held_le _) h₁.a0 h₁.a1 h₁.a2 h₁.a3 ?_ h₁.a5 h₁.rd h₁.wr, h₁.saved, h₁.frame, h₁.out,
      h₁.s1, h₁.keep, h₁.rd, h₁.wr, h₁.sp⟩
    rw [h₁.a4, h2, h0]; rfl
  · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
    have hne : s₀.gpr .a2 ≠ 0 := fun e => h0 (by rw [e]; rfl)
    refine wp_subi (imm := 1) (by decide) fun s₂ u₂ => wp_andi (by decide) fun s₃ u₃ =>
      wp_addi (imm := 1) (by decide) fun s₄ u₄ => WP.block_nil ?_
    have g (r : Reg) (a : r ≠ .a4) : s₄.gpr r = s₁.gpr r := by
      rw [u₄.other _ a, u₃.other _ a, u₂.other _ a]
    have hc : ∀ r ∈ preserved, r ≠ .a4 := by decide
    have m₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
    refine ⟨hp.fargs (held_le _) (by rw [g _ (by decide), h₁.a0])
      (by rw [g _ (by decide), h₁.a1]) (by rw [g _ (by decide), h₁.a2])
      (by rw [g _ (by decide), h₁.a3]) ?_ (by rw [g _ (by decide), h₁.a5])
      (by rw [u₄.rd, u₃.rd, u₂.rd, h₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, h₁.wr]),
      by rw [m₄]; exact h₁.saved, by rw [m₄]; exact h₁.frame, by rw [m₄]; exact h₁.out,
      by rw [g _ (by decide), h₁.s1],
      fun r hr h1 => by rw [g r (hc r hr), h₁.keep r hr h1],
      by rw [u₄.rd, u₃.rd, u₂.rd, h₁.rd], by rw [u₄.wr, u₃.wr, u₂.wr, h₁.wr],
      by rw [u₄.sp, u₃.sp, u₂.sp, h₁.sp]⟩
    rw [u₄.gpr, u₃.gpr, u₂.gpr, h₁.a4]
    exact held_bv _ hne

/-! ## The whole function -/

theorem finish_wp {s₀ : State} (h0 : finishRISCV64.pre s₀) :
    WP isa finish s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.sp = s₀.sp ∧ finishRISCV64.post s₀ s' := by
  have hp := HPre.of h0
  generalize s₀.gpr .a0 = St at hp
  generalize s₀.gpr .a3 = O at hp
  generalize s₀.gpr .a4 = S at hp
  generalize (s₀.gpr .a1).toNat = R at hp
  have hw := hp.wSt
  have sw := hp.wS
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (fin_call h₁.args) fun s₂ h₂ => ?_)
  have s1₂ : s₂.gpr .s1 = S := by rw [h₂.saved _ (by decide), h₁.s1]
  -- The slots, which the call does not write.
  have sv₂ : Spill.Saved (sv2 S) (finG s₀ S) finSaved s₂.mem := h₁.saved.frame h₂.frame fun p hp' r hr => by
    have := fin_bound p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.o_s.symm.sub_left (sv2_sub S (by omega_using [this]))
    · exact sv2_ws S (by omega_using [this])
  rw [finishPost, WP.block_append_iff]
  refine WP.mono (savePtr2_ok .s1) fun s₃ e => ?_
  subst e
  rw [s1₂, show finSaved.map (fun (r, d) => Instr.load .d r .t0 d) = Spill.restoreCode .t0 finSaved from rfl]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := finSaved) (B := sv2 S) (Align.align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) sv₂) fun s₄ r₄ => ?_
  · have := fin_bound p hp'
    show InRegions (s₂.rd ++ s₂.wr) _ 8
    rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hp.rd, hp.wr]
    exact ⟨⟨S, 2304⟩, by simp, sv2_contains S (by omega_using [this])⟩
  have g₀ (r : Reg) (hr : r ≠ .t0) : finG s₀ S r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · have h0 := (preserved_ne r hr).1
    rw [r₄.gpr_of (r := r) ?_, g₀ r h0]
    by_cases h1 : r = .s1
    · left; subst h1; decide
    · right; rw [RegUpd.gpr_write_of_ne _ _ h0, h₂.saved r hr, h₁.keep r hr h1, g₀ r h0]
  · rw [r₄.gpr (.ra, 0) (by decide), g₀ .ra (by decide)]
  · rw [r₄.sp, RegUpd.sp_write, h₂.sp, h₁.sp]
  · intro key msg hr hR hc hlen
    rw [hp.a0] at hr
    rw [Proof.Cmac.Stream.repr_iff] at hr
    obtain ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩ := hr
    have hn : (s₀.gpr .a2).toNat = msg.length := by rw [hc, toNat_ofNat hlen]
    show Spec.Aes.bytesAt s₄.mem (s₀.gpr .a3) 16 = _
    rw [hp.a3, r₄.mem, RegUpd.mem_write]
    have hR' : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.a1]; exact hR
    -- The state is unchanged before the call.
    have fSt : ∀ {d n : Nat}, d + n ≤ 304 → Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
      exact Proof.Cmac.bytesAt_frame h₁.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.st_o.sub_left (Offset.sub_base St hd)
        · exact (hp.st_s.sub_left (Offset.sub_base St hd)).sub_right
            (by have := sv2_sub S (d := 0) (n := 16) (by decide); rwa [BitVec.add_zero] at this))
        (by omega_using [hd])
    have hsch : Spec.Aes.bytesAt s₁.mem St (16 * (R + 1)) = Spec.Aes.expandKey key := by
      have := fSt (d := 0) (n := 16 * (R + 1)) (by rcases hp.rounds with h | h | h <;> omega_using [h])
      rw [BitVec.add_zero] at this; rw [this, hR']; exact hks
    have hciph : Spec.Cmac.aesWith R (Spec.Aes.bytesAt s₁.mem St (16 * (R + 1))) = Spec.Cmac.aes key := by
      rw [hsch, hR']; rfl
    have e₁ : Spec.Aes.bytesAt s₁.mem (St + 240) 32 = Spec.Aes.bytesAt s₀.mem (St + 240) 32 :=
      fSt (d := 240) (by decide)
    have e₂ : Spec.Aes.bytesAt s₁.mem O 16 = Spec.Aes.bytesAt s₀.mem (St + 272) 16 := h₁.out
    have e₃ : Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 288) (held (s₀.gpr .a2).toNat) =
        Spec.Aes.bytesAt s₀.mem (St + 288) (held msg.length) := by
      rw [hn]; exact fSt (by have := held_le msg.length; omega_using [this])
    obtain ⟨hm, hne, hst, happ⟩ := Proof.Cmac.Stream.repr_finish
      ((Proof.Cmac.Stream.repr_iff _ _ _ _).mpr ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩)
    have out := h₂.out (by rw [hciph, e₁]; exact hsk) _ hm (by rw [hn]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, e₃, happ, Proof.Cmac.Stream.aesCmac_eq]

/-! ## Constant time -/

theorem finish_rel {s₀ s₀' : State} (h0 : finishRISCV64.pre s₀)
    (h0' : finishRISCV64.pre s₀') (hq : finishRISCV64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finish fun _ _ => True := by
  obtain ⟨q3, q4, q5, q6, q7, qsp⟩ := hq
  have hp := HPre.of h0
  have hp' : HPre s₀' (s₀.gpr .a0) (s₀.gpr .a3) (s₀.gpr .a4) (s₀.gpr .a1).toNat := by
    rw [q3, q4, q6, q7]; exact HPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) finPre h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1]) (.block finishPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.a0, .a1, .a2, .a3, .a4]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨qsp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := fun (s : State) => HMid s₀ (s₀.gpr .a0) (s₀.gpr .a3) (s₀.gpr .a4) (s₀.gpr .a1).toNat s ∧
      s.sp = s₀.sp)
    (F₂ := fun (s : State) => HMid s₀' (s₀.gpr .a0) (s₀.gpr .a3) (s₀.gpr .a4) (s₀.gpr .a1).toNat s ∧
      s.sp = s₀'.sp) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨wp_sp (finPre_wp hp), wp_sp (finPre_wp hp')⟩
  have c := (fin_rel (P := fun s₁ s₂ =>
      (HMid s₀ (s₀.gpr .a0) (s₀.gpr .a3) (s₀.gpr .a4) (s₀.gpr .a1).toNat s₁ ∧ s₁.sp = s₀.sp) ∧
      (HMid s₀' (s₀.gpr .a0) (s₀.gpr .a3) (s₀.gpr .a4) (s₀.gpr .a1).toNat s₂ ∧ s₂.sp = s₀'.sp))
    fun s₁ s₂ h => ⟨h.1.1.args, by rw [q5]; exact h.2.1.args, by rw [h.1.2, h.2.2, qsp]⟩).wp
    (F₁ := fun (s : State) => s.gpr .s1 = s₀.gpr .a4 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .s1 = s₀.gpr .a4 ∧ s.sp = s₀'.sp) fun s₁ s₂ h =>
      ⟨WP.mono (fin_call h.1.1.args) fun _ hc =>
        ⟨by rw [hc.saved .s1 (by decide), h.1.1.s1], by rw [hc.sp, h.1.2]⟩,
       WP.mono (fin_call h.2.1.args) fun _ hc =>
        ⟨by rw [hc.saved .s1 (by decide), h.2.1.s1], by rw [hc.sp, h.2.2]⟩⟩
  have b := taintRegs
    (P := fun s₁ s₂ => (s₁.gpr .s1 = s₀.gpr .a4 ∧ s₁.sp = s₀.sp) ∧ (s₂.gpr .s1 = s₀.gpr .a4 ∧ s₂.sp = s₀'.sp))
    [.s1] (fun s₁ s₂ h => ⟨by rw [h.1.2, h.2.2, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.1, h.2.1]⟩) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem finish_ct : ConstantTime isa finishRISCV64.pre finishRISCV64.pub finish :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finish_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.RISCV64

end

end

/-! ### `CmacAes.Stream.RISCV64.AbsorbCorrect`, which only this module used -/

section

/-! ### `CmacAes.Stream.RISCV64.AbsorbBlocks`, which only this module used -/

section

/-!
# Streaming AES-CMAC on RISC-V: `vg_cmac_aes_absorb`'s straight-line code

What each piece of code between the copies and calls computes, in terms of
`count` (`c`) and `len` (`L`), as on PPC64LE
(`Proof/CmacAes/Stream/PPC64LE/AbsorbBlocks.lean`): the bytes held back
`h = held c`, the bytes copied after them `f = min L (16 - h)`, the data left
`L - f`, whether to chain the block held back (`b1`), the blocks chained
after it (`nb`), and the rest (`rest`); and the registers `absorb` saves at
`sv2 S`, where the functions it calls do not write.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacAes.Stream.RISCV64
open VG.Proof.Cmac.Stream (held held_le)

/-! ## The numbers -/

/-- The bytes copied after the `held c` held back. -/
def fOf (c L : Nat) : Nat := min L (16 - held c)

/-- The data left after them. -/
def leftOf (c L : Nat) : Nat := L - fOf c L

/-- The number of blocks the first call chains: the block held back, if data is left. -/
def b1Of (c L : Nat) : Nat := if leftOf c L = 0 then 0 else 1

/-- The number of blocks the second call chains: those of the data left but its
last 1 to 16 bytes. -/
def nbOf (c L : Nat) : Nat := if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16

/-- The bytes copied to the start of the bytes held back at the end. -/
def restOf (c L : Nat) : Nat := leftOf c L - 16 * nbOf c L

theorem f_le (c L : Nat) : fOf c L ≤ L ∧ fOf c L + held c ≤ 16 := by
  have := held_le c; unfold fOf; omega_using [this]

theorem nb_le (c L : Nat) : fOf c L + 16 * nbOf c L + restOf c L = L := by
  have := f_le c L; unfold restOf nbOf leftOf; split <;> omega_using [this]

/-! ## Arithmetic on registers -/

/-- `sltu` of two numbers. -/
theorem sltu_ofNat {m k : Nat} (hm : m < 2 ^ 64) (hk : k < 2 ^ 64) :
    (if BitVec.ofNat 64 m < BitVec.ofNat 64 k then (1 : BitVec 64) else 0) =
      BitVec.ofNat 64 (if m < k then 1 else 0) := by
  have : (BitVec.ofNat 64 m < BitVec.ofNat 64 k) ↔ m < k := by
    rw [BitVec.lt_def, toNat_ofNat hm, toNat_ofNat hk]
  by_cases h : m < k
  · simp only [this.mpr h, h, ↓reduceIte]; rfl
  · simp only [show ¬ (BitVec.ofNat 64 m < BitVec.ofNat 64 k) from fun h' => h (this.mp h'), h, ↓reduceIte]; rfl

/-- `16 nb` for the data left `x > 0`, as `addi -1; andi 15; sub` computes it. -/
theorem nb16_bv {x : Nat} (hx : 0 < x) (hx' : x < 2 ^ 64) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 1 - ((BitVec.ofNat 64 x - BitVec.ofNat 64 1) &&& BitVec.ofInt 64 15) =
      BitVec.ofNat 64 (16 * ((x - 1) / 16)) := by
  apply BitVec.eq_of_toNat_eq
  obtain e : (BitVec.ofNat 64 x - BitVec.ofNat 64 1).toNat = x - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega_using [hx, hx']
  rw [BitVec.toNat_sub, and15, e, BitVec.toNat_ofNat]
  omega_using []

/-! ## Saving the registers -/

/-- What `absorb` saves: the registers, with `t0` the slots' base. -/
abbrev absG (s₀ : State) (S : Addr) : Reg → BitVec 64 := (s₀.write .t0 (sv2 S)).gpr

/-- The memory after saving the registers at `sv2 S`. -/
abbrev absMem (s₀ : State) (S : Addr) : Mem := Spill.saveMem s₀.mem (sv2 S) (absG s₀ S) absSaved

theorem abs_bound : ∀ p ∈ absSaved, p.2 + 8 ≤ 56 := by decide

/-- Saving the registers changes only their slots. -/
theorem absMem_frame (s₀ : State) (S : Addr) : Frame [⟨sv2 S, 56⟩] s₀.mem (absMem s₀ S) :=
  Spill.saveMem_frame_base (n := 56) abs_bound (by decide) _ _ _

/-- What `save` leaves. -/
structure Saved₁ (s₀ : State) (S : Addr) (s : State) : Prop where
  s1 : s.gpr .s1 = s₀.gpr .a0
  s2 : s.gpr .s2 = s₀.gpr .a1
  s3 : s.gpr .s3 = s₀.gpr .a3
  s4 : s.gpr .s4 = s₀.gpr .a4
  s6 : s.gpr .s6 = S
  other : ∀ r, r ≠ .t0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → r ≠ .s6 → s.gpr r = s₀.gpr r
  mem : s.mem = absMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem save_wp (s₀ : State) {S : Addr} (hS : s₀.gpr .a5 = S)
    (hw : ∀ d, d + 8 ≤ 56 → InRegions s₀.wr (sv2 S + BitVec.ofNat 64 d) 8) :
    WP isa (.block save) s₀ (Saved₁ s₀ S) := by
  rw [save, List.append_assoc, WP.block_append_iff]
  refine WP.mono (savePtr2_ok .a5) fun s₁ e => ?_
  subst e
  rw [hS, show absSaved.map (fun (r, d) => Instr.store .d r .t0 d) = Spill.saveCode .t0 absSaved from rfl]
  obtain t₀ : (s₀.write .t0 (sv2 S)).gpr .t0 = sv2 S := RegUpd.gpr_write_self _ _ _
  have g₀ (r : Reg) (hr : r ≠ .t0) : (s₀.write .t0 (sv2 S)).gpr r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine Spill.save_ok (b := .t0) (l := absSaved) (by rw [t₀]; exact Align.align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · rw [t₀]; exact hw _ (abs_bound p hp')
  generalize ht : ({ (s₀.write .t0 (sv2 S)) with
    mem := Spill.saveMem (s₀.write .t0 (sv2 S)).mem ((s₀.write .t0 (sv2 S)).gpr .t0)
      (s₀.write .t0 (sv2 S)).gpr absSaved } : State) = t
  have gt (r : Reg) (hr : r ≠ .t0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact g₀ r hr
  obtain memt : t.mem = absMem s₀ S := by
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [t₀, RegUpd.mem_write]
  obtain rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  obtain wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  unfold Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    wp_mv fun s₅ u₅ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, fun r a b c d e f => ?_, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr, gt]
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other, gt]
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.gpr, u₂.other, u₁.other, gt]
  · simp (disch := decide) only [u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other, gt]
  · simp (disch := decide) only [u₅.gpr, u₄.other, u₃.other, u₂.other, u₁.other, gt, hS]
  · rw [u₅.other _ f, u₄.other _ e, u₃.other _ d, u₂.other _ c, u₁.other _ b, gt _ a]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, memt]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, rdt]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, wrt]

/-! ## `held`: the bytes held back -/

theorem held_wp {s : State} {c : Nat} (hc : c < 2 ^ 64) (hd : s.gpr .a2 = BitVec.ofNat 64 c) :
    WP isa held s fun s' => s'.gpr .t1 = BitVec.ofNat 64 (held c) ∧
      (∀ r, r ≠ .t1 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ev := eval_zero_ofNat s .a2 hc hd
  by_cases h0 : c = 0
  · subst h0
    refine WP.ite true (by rw [ev]; rfl) (fun _ => ?_) (fun h => by cases h)
    exact wp_li (imm := 0) (by decide) fun s₁ u₁ => WP.block_nil ⟨by rw [u₁.gpr]; rfl,
      fun r h => u₁.other r h, u₁.mem, u₁.rd, u₁.wr⟩
  · have hne : BitVec.ofNat 64 c ≠ 0 := fun e => h0 (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat hc] at this)
    refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
    refine wp_subi (imm := 1) (by decide) fun s₁ u₁ => wp_andi (by decide) fun s₂ u₂ =>
      wp_addi (imm := 1) (by decide) fun s₃ u₃ => WP.block_nil ⟨?_, fun r a => ?_, ?_, ?_, ?_⟩
    · rw [u₃.gpr, u₂.gpr, u₁.gpr, hd, held_bv _ hne, toNat_ofNat hc]
    · rw [u₃.other _ a, u₂.other _ a, u₁.other _ a]
    · rw [u₃.mem, u₂.mem, u₁.mem]
    · rw [u₃.rd, u₂.rd, u₁.rd]
    · rw [u₃.wr, u₂.wr, u₁.wr]

/-! ## `fill`: how many bytes to copy, and where -/

theorem clamp_wp {s : State} {L : Nat} (hL : L < 2 ^ 64) (h4 : s.gpr .s4 = BitVec.ofNat 64 L) :
    WP isa clamp s fun s' => s'.gpr .t2 = BitVec.ofNat 64 (min L 16) ∧
      (∀ r, r ≠ .t2 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_srl (by decide) fun s₁ u₁ => WP.block_nil ?_)
  obtain x2 : s₁.gpr .t2 = BitVec.ofNat 64 (L / 16) := by
    rw [u₁.gpr, h4, shr_ofNat hL]
  obtain ev := eval_zero_ofNat s₁ .t2 (by omega_using [hL]) x2
  by_cases hl : L < 16
  · have e : L / 16 = 0 := by omega_using [hl]
    refine WP.ite true (by rw [ev, e]; rfl) (fun _ => ?_) (fun h => by cases h)
    unfold Impl.AesCbc.RISCV64.mov
    refine wp_mv fun s₂ u₂ => WP.block_nil ⟨?_, fun r h => by rw [u₂.other _ h, u₁.other _ h],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
    rw [u₂.gpr, u₁.other _ (by decide), h4, Nat.min_eq_left (Nat.le_of_lt hl)]
  · have e : L / 16 ≠ 0 := by omega_using [hl]
    refine WP.ite false (by rw [ev]; simp [e]) (fun h => by cases h) fun _ => ?_
    refine wp_li (imm := 16) (by decide) fun s₂ u₂ => WP.block_nil ⟨?_, fun r h => by rw [u₂.other _ h, u₁.other _ h],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
    rw [u₂.gpr, Nat.min_eq_right (Nat.le_of_not_lt hl)]

theorem fill_wp {s : State} {St D : Addr} {c L : Nat} (hL : L < 2 ^ 64)
    (h1 : s.gpr .t1 = BitVec.ofNat 64 (held c)) (h4 : s.gpr .s4 = BitVec.ofNat 64 L)
    (hs1 : s.gpr .s1 = St) (hs3 : s.gpr .s3 = D) :
    WP isa fill s fun s' => s'.gpr .t2 = BitVec.ofNat 64 (fOf c L) ∧
      s'.gpr .a7 = BitVec.ofNat 64 (fOf c L) ∧ s'.gpr .t5 = St + BitVec.ofNat 64 (288 + held c) ∧
      s'.gpr .t6 = D ∧
      (∀ r, r ≠ .a7 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → r ≠ .t6 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hh := held_le c
  refine WP.seq (WP.mono (clamp_wp hL h4) fun s₁ ⟨x2₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (wp_li (imm := 16) (by decide) fun s₂ u₂ => wp_sub fun s₃ u₃ => wp_sltu fun s₄ u₄ =>
    WP.block_nil ?_)
  obtain x1₁ : s₁.gpr .t1 = BitVec.ofNat 64 (held c) := by rw [g₁ _ (by decide), h1]
  obtain x3₄ : s₄.gpr .t3 = BitVec.ofNat 64 (16 - held c) := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), x1₁, Offset.ofNat_sub_ofNat hh]
  obtain x2₄ : s₄.gpr .t2 = BitVec.ofNat 64 (min L 16) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), x2₁]
  obtain x4₄ : s₄.gpr .t4 = BitVec.ofNat 64 (if min L 16 < 16 - held c then 1 else 0) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), x2₁, u₃.gpr, u₂.gpr, u₂.other _ (by decide),
      x1₁, Offset.ofNat_sub_ofNat hh]
    exact sltu_ofNat (by omega_using []) (by omega_using [])
  have g₄ (r : Reg) (a : r ≠ .t3) (b : r ≠ .t4) : s₄.gpr r = s₁.gpr r := by
    rw [u₄.other _ b, u₃.other _ a, u₂.other _ a]
  obtain hf : fOf c L = min (min L 16) (16 - held c) := by unfold fOf; omega_using []
  obtain ev := eval_zero_ofNat s₄ .t4 (k := if min L 16 < 16 - held c then 1 else 0) (by split <;> omega_using []) x4₄
  refine WP.seq (WP.mono (Q := fun (s₅ : State) => s₅.gpr .t2 = BitVec.ofNat 64 (fOf c L) ∧
    (∀ r, r ≠ .t2 → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr) ?_
    fun s₅ h₅ => ?_)
  · by_cases hl : min L 16 < 16 - held c
    · refine WP.ite false (by rw [ev]; simp [hl]) (fun h => by cases h) fun _ => WP.block_nil ?_
      exact ⟨by rw [x2₄, hf, Nat.min_eq_left (Nat.le_of_lt hl)], fun _ _ => rfl, rfl, rfl, rfl⟩
    · refine WP.ite true (by rw [ev]; simp [hl]) (fun _ => ?_) (fun h => by cases h)
      unfold Impl.AesCbc.RISCV64.mov
      refine wp_mv fun s₅ u₅ => WP.block_nil ⟨?_, fun r h => u₅.other r h, u₅.mem, u₅.rd, u₅.wr⟩
      rw [u₅.gpr, x3₄, hf, Nat.min_eq_right (Nat.le_of_not_lt hl)]
  · obtain ⟨x2₅, g₅, m₅, rd₅, wr₅⟩ := h₅
    have g (r : Reg) (a : r ≠ .t2) (b : r ≠ .t3) (d : r ≠ .t4) : s₅.gpr r = s.gpr r := by
      rw [g₅ r a, g₄ r b d, g₁ r a]
    unfold Impl.AesCbc.RISCV64.mov
    refine wp_mv fun s₆ u₆ => wp_add fun s₇ u₇ => wp_addi (imm := 288) (by decide) fun s₈ u₈ =>
      wp_mv fun s₉ u₉ => WP.block_nil ⟨?_, ?_, ?_, ?_, fun r a b d e f h => ?_, ?_, ?_, ?_⟩
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), x2₅]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, x2₅]
    · rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.other _ (by decide), u₆.other _ (by decide),
        g .s1 (by decide) (by decide) (by decide), g .t1 (by decide) (by decide) (by decide), hs1, h1,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]
    · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        g .s3 (by decide) (by decide) (by decide), hs3]
    · rw [u₉.other _ h, u₈.other _ f, u₇.other _ f, u₆.other _ a, g r b d e]
    · rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅, u₄.mem, u₃.mem, u₂.mem, m₁]
    · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅, u₄.rd, u₃.rd, u₂.rd, rd₁]
    · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅, u₄.wr, u₃.wr, u₂.wr, wr₁]

/-! ## `chain1`: the arguments of the first call -/

theorem chain1_wp {s : State} {St D S : Addr} {f L : Nat} (hf : f ≤ L) (hL : L < 2 ^ 64)
    (h3 : s.gpr .s3 = D) (ha7 : s.gpr .a7 = BitVec.ofNat 64 f) (h4 : s.gpr .s4 = BitVec.ofNat 64 L)
    (hs1 : s.gpr .s1 = St) (hs6 : s.gpr .s6 = S) :
    WP isa chain1 s fun s' => s'.gpr .s3 = D + BitVec.ofNat 64 f ∧ s'.gpr .s4 = BitVec.ofNat 64 (L - f) ∧
      s'.gpr .a4 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧ s'.gpr .a0 = St ∧
      s'.gpr .a1 = s.gpr .s2 ∧ s'.gpr .a2 = St + BitVec.ofNat 64 272 ∧
      s'.gpr .a3 = St + BitVec.ofNat 64 288 ∧ s'.gpr .a5 = S ∧
      (∀ r ∈ preserved, r ≠ .s3 → r ≠ .s4 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_add fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_li (imm := 0) (by decide) fun s₃ u₃ => WP.block_nil ?_)
  obtain x4₃ : s₃.gpr .s4 = BitVec.ofNat 64 (L - f) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h4, u₁.other _ (by decide), ha7,
      Offset.ofNat_sub_ofNat hf]
  have g₃ (r : Reg) (a : r ≠ .s3) (b : r ≠ .s4) (c : r ≠ .a4) : s₃.gpr r = s.gpr r := by
    rw [u₃.other _ c, u₂.other _ b, u₁.other _ a]
  obtain ev := eval_zero_ofNat s₃ .s4 (k := L - f) (by omega_using [hL]) x4₃
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => s₄.gpr .a4 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧
    (∀ r, r ≠ .a4 → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr) ?_
    fun s₄ h₄ => ?_)
  · by_cases h0 : L - f = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [u₃.gpr]; simp [h0], fun _ _ => rfl, rfl, rfl, rfl⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine wp_li (imm := 1) (by decide) fun s₄ u₄ => WP.block_nil ⟨?_, fun r h => u₄.other r h, u₄.mem, u₄.rd, u₄.wr⟩
      rw [u₄.gpr]; simp [h0]
  · obtain ⟨x4₄, g₄, m₄, rd₄, wr₄⟩ := h₄
    have g (r : Reg) (a : r ≠ .s3) (b : r ≠ .s4) (c : r ≠ .a4) : s₄.gpr r = s.gpr r := by
      rw [g₄ r c, g₃ r a b c]
    unfold Impl.AesCbc.RISCV64.mov
    refine wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => wp_addi (imm := 272) (by decide) fun s₇ u₇ =>
      wp_addi (imm := 288) (by decide) fun s₈ u₈ => wp_mv fun s₉ u₉ =>
      WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr a b => ?_, ?_, ?_, ?_⟩
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), g₄ _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h3, ha7]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), g₄ _ (by decide), x4₃]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), x4₄]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.gpr, g .s1 (by decide) (by decide) (by decide), hs1]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
        u₅.other _ (by decide), g .s2 (by decide) (by decide) (by decide)]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
        u₅.other _ (by decide), g .s1 (by decide) (by decide) (by decide), hs1]
    · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), g .s1 (by decide) (by decide) (by decide), hs1]
    · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), g .s6 (by decide) (by decide) (by decide), hs6]
    · obtain ⟨-, -, -, -, -, -, -, -, n0, n1, n2, n3, n4, n5, -⟩ := preserved_ne r hr
      rw [u₉.other _ n5, u₈.other _ n3, u₇.other _ n2, u₆.other _ n1, u₅.other _ n0, g r a b n4]
    · rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄, u₃.mem, u₂.mem, u₁.mem]
    · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, rd₄, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr₄, u₃.wr, u₂.wr, u₁.wr]

/-! ## `chain2`: the arguments of the second call -/

theorem chain2_wp {s : State} {x : Nat} (hx : x < 2 ^ 64) (h4 : s.gpr .s4 = BitVec.ofNat 64 x) :
    WP isa chain2 s fun s' =>
      s'.gpr .s5 = BitVec.ofNat 64 (16 * (if x = 0 then 0 else (x - 1) / 16)) ∧
      s'.gpr .a4 = BitVec.ofNat 64 (if x = 0 then 0 else (x - 1) / 16) ∧ s'.gpr .a0 = s.gpr .s1 ∧
      s'.gpr .a1 = s.gpr .s2 ∧ s'.gpr .a2 = s.gpr .s1 + BitVec.ofNat 64 272 ∧
      s'.gpr .a3 = s.gpr .s3 ∧ s'.gpr .a5 = s.gpr .s6 ∧
      (∀ r ∈ preserved, r ≠ .s5 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_li (imm := 0) (by decide) fun s₁ u₁ => WP.block_nil ?_)
  obtain ev := eval_zero_ofNat s₁ .s4 hx (by rw [u₁.other _ (by decide), h4])
  refine WP.seq (WP.mono (Q := fun (s₂ : State) =>
    s₂.gpr .s5 = BitVec.ofNat 64 (16 * (if x = 0 then 0 else (x - 1) / 16)) ∧
    (∀ r, r ≠ .s5 → r ≠ .t1 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr) ?_ fun s₂ h₂ => ?_)
  · by_cases h0 : x = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [u₁.gpr]; simp [h0], fun _ _ _ => rfl, rfl, rfl, rfl⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine wp_subi (imm := 1) (by decide) fun s₂ u₂ => wp_andi (by decide) fun s₃ u₃ =>
        wp_sub fun s₄ u₄ => WP.block_nil ⟨?_, fun r a b => ?_, ?_, ?_, ?_⟩
      · rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h4]
        simp only [h0, ↓reduceIte]
        exact nb16_bv (by omega_using [h0]) hx
      · rw [u₄.other _ a, u₃.other _ b, u₂.other _ a]
      · rw [u₄.mem, u₃.mem, u₂.mem]
      · rw [u₄.rd, u₃.rd, u₂.rd]
      · rw [u₄.wr, u₃.wr, u₂.wr]
  · obtain ⟨x5₂, g₂, m₂, rd₂, wr₂⟩ := h₂
    have g (r : Reg) (a : r ≠ .s5) (b : r ≠ .t1) : s₂.gpr r = s.gpr r := by rw [g₂ r a b, u₁.other _ a]
    unfold Impl.AesCbc.RISCV64.mov
    refine wp_srl (by decide) fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
      wp_addi (imm := 272) (by decide) fun s₆ u₆ => wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ =>
      WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr a => ?_, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, x5₂]
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, x5₂]
      exact (shr_ofNat (by split <;> omega_arith)).trans (by congr 1; omega_using [])
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g]
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g]
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, g]
    · simp (disch := decide) only [u₈.other, u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, g]
    · simp (disch := decide) only [u₈.gpr, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g]
    · obtain ⟨-, n1, -, -, -, -, -, -, n0, na1, na2, na3, na4, na5, -⟩ := preserved_ne r hr
      rw [u₈.other _ na5, u₇.other _ na3, u₆.other _ na2, u₅.other _ na1, u₄.other _ n0, u₃.other _ na4, g r a n1]
    · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem]
    · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
    · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]

/-! ## `rest`: the arguments of the last copy -/

theorem rest_wp {s : State} {D : Addr} {a x n : Nat} (hn : 16 * n ≤ x)
    (h3 : s.gpr .s3 = D + BitVec.ofNat 64 a) (h5 : s.gpr .s5 = BitVec.ofNat 64 (16 * n))
    (h4 : s.gpr .s4 = BitVec.ofNat 64 x) :
    WP isa (.block rest) s fun s' => s'.gpr .s3 = D + BitVec.ofNat 64 (a + 16 * n) ∧
      s'.gpr .s4 = BitVec.ofNat 64 (x - 16 * n) ∧ s'.gpr .t5 = s.gpr .s1 + BitVec.ofNat 64 288 ∧
      s'.gpr .t6 = D + BitVec.ofNat 64 (a + 16 * n) ∧ s'.gpr .t2 = BitVec.ofNat 64 (x - 16 * n) ∧
      (∀ r ∈ preserved, r ≠ .s3 → r ≠ .s4 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain e : D + BitVec.ofNat 64 a + BitVec.ofNat 64 (16 * n) = D + BitVec.ofNat 64 (a + 16 * n) :=
    Offset.add_add _ _ _
  unfold rest Impl.AesCbc.RISCV64.mov
  refine wp_add fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_addi (imm := 288) (by decide) fun s₃ u₃ =>
    wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, fun r hr a b => ?_, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr, h3, h5, e]
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other, h4, h5]
    exact Offset.ofNat_sub_ofNat hn
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.gpr, u₂.other, u₁.other]
  · simp (disch := decide) only [u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.gpr, h3, h5, e]
  · simp (disch := decide) only [u₅.gpr, u₄.other, u₃.other, u₂.gpr, u₁.other, h4, h5]
    exact Offset.ofNat_sub_ofNat hn
  · obtain ⟨-, -, n2, -, -, n5, n6, -⟩ := preserved_ne r hr
    rw [u₅.other _ n2, u₄.other _ n6, u₃.other _ n5, u₂.other _ b, u₁.other _ a]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

end VG.Proof.CmacAes.Stream.RISCV64

end

end


/-!
# Streaming AES-CMAC on RISCV64: `vg_cmac_aes_absorb` is correct

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 16 - h)` bytes after them, and sets up the first call of
`vg_cmac_aes_update`, which chains the block held back if data is left
(`AMid₁`, `absorbPre_wp`). The second call chains the whole blocks of the
data left but its last 1 to 16 bytes (`nb`), and the last copy holds those
back. If no data is left (`len ≤ 16 - h`), the calls chain nothing and the
copy copies nothing, and the data is appended to the bytes held back
(`repr_fill`); otherwise `repr_chain`. As on PPC64LE (`Proof/CmacAes/Stream/PPC64LE/Frame.lean`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacAes.Stream.RISCV64 VG.WriteBytes
open VG.Proof.Cmac (bytesAt_frame)
open VG.Proof.AesCbc.RISCV64 (wp_sp)
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`,
the scratch buffer `S` and the rounds `R`. -/
structure APre (s₀ : State) (St D S : Addr) (L R : Nat) : Prop where
  a0 : s₀.gpr .a0 = St
  a3 : s₀.gpr .a3 = D
  a4 : (s₀.gpr .a4).toNat = L
  a5 : s₀.gpr .a5 = S
  a1 : (s₀.gpr .a1).toNat = R
  rd : s₀.rd = [⟨D, L⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 2304⟩]
  st_d : (⟨St, 304⟩ : Region).Disjoint ⟨D, L⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  d_s : (⟨D, L⟩ : Region).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wD : D.toNat + L ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem APre.of {s₀ : State} (h : absorbRISCV64.pre s₀) :
    APre s₀ (s₀.gpr .a0) (s₀.gpr .a3) (s₀.gpr .a5) (s₀.gpr .a4).toNat (s₀.gpr .a1).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

section
variable {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R)
include hp

theorem APre.lt : L < 2 ^ 64 := by rw [← hp.a4]; exact BitVec.isLt _

theorem APre.a4' : s₀.gpr .a4 = BitVec.ofNat 64 L := ofNat_toNat_eq hp.a4

theorem APre.a1' : s₀.gpr .a1 = BitVec.ofNat 64 R := ofNat_toNat_eq hp.a1

theorem APre.inSt {d n : Nat} (h : d + n ≤ 304) : InRegions s₀.wr (St + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ h (by have := hp.wSt; omega_using [h])⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact ⟨⟨D, L⟩, by simp, Offset.contains_base _ h (by have := hp.lt; omega_using [h, this])⟩

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the permissions of `s₀`. -/
theorem APre.uargs {s : State} {Dd : Addr} {n : Nat} (h3 : s.gpr .a0 = St)
    (h4 : s.gpr .a1 = s₀.gpr .a1) (h5 : s.gpr .a2 = St + BitVec.ofNat 64 272) (h6 : s.gpr .a3 = Dd)
    (h7 : s.gpr .a4 = BitVec.ofNat 64 n) (h8 : s.gpr .a5 = S)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 16 * n < 2 ^ 64)
    (hdc : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 272, 16⟩)
    (hds : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨S, 2176⟩) (hwrap : Dd.toNat + 16 * n ≤ 2 ^ 64)
    (hcov : ∃ r' ∈ ([⟨D, L⟩, ⟨St, 304⟩, ⟨S, 2304⟩] : List Region), ∃ off, Dd = r'.base + BitVec.ofNat 64 off ∧
      off + 16 * n ≤ r'.len) :
    UArgs s St (St + BitVec.ofNat 64 272) Dd S R n := by
  have hw := hp.wSt
  obtain c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  exact
  { a0 := h3, a2 := h5, a3 := h6, a4 := h7, a5 := h8, rounds := hp.rounds, hn := hn
    a1 := by rw [h4]; exact hp.a1'
    wc := Offset.base_disjoint St (by decide) (by omega_using [])
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    dc := hdc, ds := hds
    cs := (hp.st_s.sub_left c272).sub_right (Region.sub_prefix (by decide))
    wrapC := by rw [toNat_add_lt St hw (by decide)]; omega_using [hw]
    wrapD := hwrap
    wrapS := by have := hp.wS; omega_using [this]
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact hcov
      · exact ⟨⟨St, 304⟩, by simp, 272, rfl, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 272, rfl, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩ }

end

/-! ## Up to the first call -/

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) (St D S : Addr) (c L : Nat) : Mem :=
  writeBytes (absMem s₀ S) (St + BitVec.ofNat 64 (288 + held c))
    (Spec.Aes.bytesAt (absMem s₀ S) D (fOf c L))

/-- What the code before the first call leaves. -/
structure AMid₁ (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 64 272) (St + BitVec.ofNat 64 288) S R (b1Of (s₀.gpr .a2).toNat L)
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = s₀.gpr .a1
  s3 : s.gpr .s3 = D + BitVec.ofNat 64 (fOf (s₀.gpr .a2).toNat L)
  s4 : s.gpr .s4 = BitVec.ofNat 64 (leftOf (s₀.gpr .a2).toNat L)
  s6 : s.gpr .s6 = S
  other : ∀ r ∈ preserved, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → r ≠ .s6 → s.gpr r = s₀.gpr r
  mem : s.mem = m4 s₀ St D S (s₀.gpr .a2).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R) :
    WP isa absorbPre s₀ (AMid₁ s₀ St D S L R) := by
  generalize hc : (s₀.gpr .a2).toNat = c
  obtain hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  obtain hdx : s₀.gpr .a2 = BitVec.ofNat 64 c := ofNat_toNat_eq hc
  have hL := hp.lt
  have hw := hp.wSt
  have ⟨hfL, hfh⟩ := f_le c L
  obtain hh := held_le c
  refine WP.seq (WP.mono (save_wp s₀ hp.a5 fun d h => by
    rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, sv2_contains S (by omega_using [h])⟩) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (held_wp hcl (by
    rw [h₁.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hdx]))
    fun s₂ ⟨x1₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (fill_wp (St := St) (D := D) hL x1₂
    (by rw [g₂ _ (by decide), h₁.s4, hp.a4'])
    (by rw [g₂ _ (by decide), h₁.s1, hp.a0]) (by rw [g₂ _ (by decide), h₁.s3, hp.a3]))
    fun s₃ ⟨x2₃, x7₃, x5₃, x6₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  obtain dCp : Region.Sub ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩ ⟨St, 304⟩ :=
    Offset.sub_base St (by omega_using [hfh])
  refine WP.seq (WP.mono (copy_ok s₃ (P := D) (C := St + BitVec.ofNat 64 (288 + held c)) (L := fOf c L)
    (by omega_using [hfh]) x6₃ x5₃ x2₃
    (fun i hi => by rw [rd₃, wr₃, rd₂, wr₂, h₁.rd, h₁.wr]; exact hp.inD (by omega_using [hfL, hi]))
    (fun i hi => by rw [wr₃, wr₂, h₁.wr, Offset.add_add]; exact hp.inSt (by omega_using [hfh, hi]))
    ((hp.st_d.sub_left dCp).symm.sub_left (Region.sub_prefix hfL))) fun s₄ h₄ => ?_)
  -- The registers `chain1` reads, unchanged since `save`.
  have g (r : Reg) (a : r ≠ .a7) (b : r ≠ .t1) (c : r ≠ .t2) (d : r ≠ .t3) (e : r ≠ .t4) (f : r ≠ .t5)
      (h : r ≠ .t6) : s₄.gpr r = s₁.gpr r := by
    rw [h₄.other r c d f h, g₃ r a c d e f h, g₂ r b]
  refine WP.mono (chain1_wp (St := St) (S := S) hfL hL
    (by rw [g .s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.s3,
      hp.a3])
    (by rw [h₄.other _ (by decide) (by decide) (by decide) (by decide), x7₃])
    (by rw [g .s4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.s4,
      hp.a4'])
    (by rw [g .s1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.s1,
      hp.a0])
    (by rw [g .s6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.s6]))
    fun s₅ h₅ => ?_
  obtain ⟨x3₅, x4₅, xa4₅, xa0₅, xa1₅, xa2₅, xa3₅, xa5₅, sv₅, m₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (hr : r ∈ preserved) (a : r ≠ .s3) (b : r ≠ .s4) : s₅.gpr r = s₁.gpr r := by
    obtain ⟨-, n1, n2, n3, n4, n5, n6, -, -, -, -, -, -, -, -, n7⟩ := preserved_ne r hr
    rw [sv₅ r hr a b, g r n7 n1 n2 n3 n4 n5 n6]
  obtain hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃, rd₂, h₁.rd]
  obtain hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃, wr₂, h₁.wr]
  obtain hb1 : 16 * b1Of c L ≤ 16 := by unfold b1Of; split <;> omega_using []
  obtain c288 : Region.Sub ⟨St + BitVec.ofNat 64 288, 16 * b1Of c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_using [hb1])
  obtain m₀ : s₅.mem = m4 s₀ St D S c L := by rw [m₅, h₄.mem, m₃, m₂, h₁.mem, m4]
  subst hc
  refine ⟨hp.uargs xa0₅
      (by rw [xa1₅, g .s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        h₁.s2]) xa2₅ xa3₅
      (by rw [xa4₅, b1Of, leftOf]) xa5₅ hrd hwr (by omega_using [hb1])
      (Offset.disjoint St (by omega_using []) (by omega_using [hb1]) (by omega_using []))
      ((hp.st_s.sub_left c288).sub_right (Region.sub_prefix (by decide)))
      (by rw [toNat_add_lt St hw (by decide)]; omega_using [hw, hb1])
      ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega_using [hb1]⟩,
    by rw [k .s1 (by decide) (by decide) (by decide), h₁.s1, hp.a0],
    by rw [k .s2 (by decide) (by decide) (by decide), h₁.s2],
    x3₅, by rw [x4₅]; rfl, by rw [k .s6 (by decide) (by decide) (by decide), h₁.s6],
    fun r hr a b c d e => by
      rw [k r hr c d, h₁.other r (preserved_ne r hr).1 a b c d e],
    m₀, hrd, hwr⟩

/-! ## The whole function -/

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega_using [hi]) (by omega_using [hp, hi])) hc

/-- The slots, within the scratch buffer. -/
theorem slots_sub (S : Addr) : Region.Sub ⟨sv2 S, 56⟩ ⟨S, 2304⟩ := by
  have := sv2_sub S (d := 0) (n := 56) (by decide); rwa [BitVec.add_zero] at this

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 16 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 16 1 = [Spec.Aes.bytesAt m p 16] := by
  simp [Spec.Cmac.blocksAt]

theorem absorb_wp {s₀ : State} (h0 : absorbRISCV64.pre s₀) :
    WP isa absorb s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.sp = s₀.sp ∧ absorbRISCV64.post s₀ s' := by
  obtain hp := APre.of h0
  generalize s₀.gpr .a0 = St at hp
  generalize s₀.gpr .a3 = D at hp
  generalize s₀.gpr .a5 = S at hp
  generalize (s₀.gpr .a4).toNat = L at hp
  generalize (s₀.gpr .a1).toNat = R at hp
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .a2).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have hw := hp.wSt
  have hsw := hp.wS
  have ⟨hfL, hfh⟩ := f_le c L
  obtain hsum := nb_le c L
  obtain hh := held_le c
  refine WP.seq (WP.mono (wp_sp (absorbPre_wp hp)) fun s₅ ⟨h₅, sp₅⟩ => ?_)
  obtain ⟨args₅, x1₅, x2₅, x3₅, x4₅, x6₅, o₅, m₅, rd₅, wr₅⟩ := h₅
  rw [hc] at args₅ x3₅ x4₅ m₅
  refine WP.seq (WP.mono (upd_call args₅) fun s₆ h₆ => ?_)
  have k₆ (r : Reg) (hr : r ∈ preserved) : s₆.gpr r = s₅.gpr r := h₆.saved r hr
  refine WP.seq (WP.mono (wp_sp (chain2_wp (x := leftOf c L) (by unfold leftOf; omega_using [hL])
    (by rw [k₆ .s4 (by decide), x4₅]))) fun s₇ ⟨h₇, sp₇⟩ => ?_)
  obtain ⟨x5₇, xa4₇, xa0₇, xa1₇, xa2₇, xa3₇, xa5₇, sv₇, m₇, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at x5₇ xa4₇
  have k₇ (r : Reg) (hr : r ∈ preserved) (a : r ≠ .s5) : s₇.gpr r = s₅.gpr r := by
    rw [sv₇ r hr a, k₆ r hr]
  obtain dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L), 16 * nbOf c L⟩ ⟨D, L⟩ := Offset.sub_base D (by omega_using [hsum])
  obtain c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  obtain args₇ := hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf c L)) (n := nbOf c L)
    (by rw [xa0₇, k₆ .s1 (by decide), x1₅])
    (by rw [xa1₇, k₆ .s2 (by decide), x2₅])
    (by rw [xa2₇, k₆ .s1 (by decide), x1₅])
    (by rw [xa3₇, k₆ .s3 (by decide), x3₅]) xa4₇
    (by rw [xa5₇, k₆ .s6 (by decide), x6₅]) (by rw [rd₇, h₆.rd, rd₅])
    (by rw [wr₇, h₆.wr, wr₅]) (by omega_using [hL, hsum]) ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : nbOf c L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf c L)).isLt; omega_using []
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega_using [hsum, h0])]; omega_using [hsum, this])
    ⟨⟨D, L⟩, by simp, fOf c L, rfl, by simp; omega_using [hsum]⟩
  refine WP.seq (WP.mono (upd_call args₇) fun s₈ h₈ => ?_)
  have k₈ (r : Reg) (hr : r ∈ preserved) : s₈.gpr r = s₇.gpr r := h₈.saved r hr
  refine WP.seq (WP.mono (wp_sp (rest_wp (s := s₈) (D := D) (a := fOf c L) (x := leftOf c L) (n := nbOf c L)
    (by unfold leftOf; omega_using [hsum])
    (by rw [k₈ .s3 (by decide), k₇ .s3 (by decide) (by decide), x3₅])
    (by rw [k₈ .s5 (by decide), x5₇])
    (by rw [k₈ .s4 (by decide), k₇ .s4 (by decide) (by decide), x4₅]))) fun s₉ ⟨h₉, sp₉⟩ => ?_)
  obtain ⟨x3₉, x4₉, x5₉, x6₉, x2₉, sv₉, m₉, rd₉, wr₉⟩ := h₉
  obtain rd₉' : s₉.rd = s₀.rd := by rw [rd₉, h₈.rd, rd₇, h₆.rd, rd₅]
  obtain wr₉' : s₉.wr = s₀.wr := by rw [wr₉, h₈.wr, wr₇, h₆.wr, wr₅]
  obtain dR : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L), restOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega_using [hsum])
  obtain hrr : restOf c L ≤ 16 := by unfold restOf nbOf leftOf; split <;> omega_arith
  obtain sR : Region.Sub ⟨St + BitVec.ofNat 64 288, restOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_using [hrr])
  refine WP.seq (WP.mono (wp_sp (copy_ok s₉ (P := D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L))
    (C := St + BitVec.ofNat 64 288) (L := restOf c L) (by omega_using [hrr]) x6₉
    (by rw [x5₉, k₈ .s1 (by decide), k₇ .s1 (by decide) (by decide), x1₅]) x2₉
    (fun i hi => by rw [rd₉', wr₉', Offset.add_add]; exact hp.inD (by omega_using [hsum, hi]))
    (fun i hi => by rw [wr₉', Offset.add_add]; exact hp.inSt (by omega_using [hrr, hi]))
    ((hp.st_d.sub_left sR).symm.sub_left dR))) fun s₁₀ ⟨h₁₀, sp₁₀⟩ => ?_)
  obtain x6₁₀ : s₁₀.gpr .s6 = S := by
    rw [h₁₀.other _ (by decide) (by decide) (by decide) (by decide), sv₉ _ (by decide) (by decide) (by decide),
      k₈ .s6 (by decide), k₇ .s6 (by decide) (by decide), x6₅]
  -- The frames.
  obtain hlf : (Spec.Aes.bytesAt (absMem s₀ S) D (fOf c L)).length = fOf c L := Proof.Cmac.bytesAt_length _ _ _
  obtain hlr : (Spec.Aes.bytesAt s₉.mem (D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L)) (restOf c L)).length =
    restOf c L := Proof.Cmac.bytesAt_length _ _ _
  obtain fS : Frame [⟨sv2 S, 56⟩] s₀.mem (absMem s₀ S) := absMem_frame _ _
  obtain fC1 : Frame [⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩] (absMem s₀ S) s₅.mem := by
    rw [m₅, m4]; exact writeBytes_frame _ _ _ (by rw [hlf]; exact Region.contains_self _ _)
  have f6 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩] s₅.mem s₆.mem := h₆.frame
  obtain f8 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩] s₆.mem s₈.mem := by
    rw [← m₇]; exact h₈.frame
  obtain fC2 : Frame [⟨St + BitVec.ofNat 64 288, restOf c L⟩] s₈.mem s₁₀.mem := by
    rw [h₁₀.mem, m₉]
    exact writeBytes_frame _ _ _ (by rw [← m₉, hlr]; exact Region.contains_self _ _)
  let K : List Region := [⟨sv2 S, 56⟩, ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩,
    ⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩, ⟨St + BitVec.ofNat 64 288, restOf c L⟩]
  obtain F5 : Frame K s₀.mem s₅.mem := (fS.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  obtain F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  obtain F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  obtain F10 : Frame K s₀.mem s₁₀.mem := F8.trans (fC2.mono (by simp [K]))
  -- The slots, which only the saves write.
  obtain Fp : Frame K.tail (absMem s₀ S) s₁₀.mem :=
    ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
      ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
  obtain sv₁₀ : Spill.Saved (sv2 S) (absG s₀ S) absSaved s₁₀.mem :=
    (Spill.saveMem_saved (by decide) s₀.mem (sv2 S) _).frame Fp fun p hp' r hr => by
      obtain hb := abs_bound p hp'
      obtain sub : Region.Sub ⟨sv2 S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 2304⟩ := sv2_sub S (by omega_using [hb])
      simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hfh]))).symm.sub_left sub
      · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
      · exact sv2_ws S (by omega_using [hb])
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hrr]))).symm.sub_left sub
  rw [restore, WP.block_append_iff]
  refine WP.mono (savePtr2_ok .s6) fun s₁₁ e => ?_
  subst e
  rw [x6₁₀, show absSaved.map (fun (r, d) => Instr.load .d r .t0 d) = Spill.restoreCode .t0 absSaved from rfl]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := absSaved) (B := sv2 S) (Align.align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) sv₁₀) fun s₁₂ r₁₂ => ?_
  · have := abs_bound p hp'
    show InRegions (s₁₀.rd ++ s₁₀.wr) _ 8
    rw [h₁₀.rd, h₁₀.wr, rd₉', wr₉', hp.rd, hp.wr]
    exact ⟨⟨S, 2304⟩, by simp, sv2_contains S (by omega_using [this])⟩
  have g₀ (r : Reg) (hr : r ≠ .t0) : absG s₀ S r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · -- The registers, restored from their slots or never written.
    obtain h0 := (preserved_ne r hr).1
    rw [r₁₂.gpr_of (r := r) ?_, g₀ r h0]
    by_cases hv : r ∈ absSaved.map Prod.fst
    · left; exact hv
    · right
      obtain n1 : r ≠ .s1 := fun e => hv (by subst e; decide)
      obtain n2 : r ≠ .s2 := fun e => hv (by subst e; decide)
      obtain n3 : r ≠ .s3 := fun e => hv (by subst e; decide)
      obtain n4 : r ≠ .s4 := fun e => hv (by subst e; decide)
      obtain n5 : r ≠ .s5 := fun e => hv (by subst e; decide)
      obtain n6 : r ≠ .s6 := fun e => hv (by subst e; decide)
      obtain ⟨-, -, t2, t3, -, t5, t6, -⟩ := preserved_ne r hr
      rw [RegUpd.gpr_write_of_ne _ _ h0, h₁₀.other r t2 t3 t5 t6, sv₉ r hr n3 n4, k₈ r hr, k₇ r hr n5,
        o₅ r hr n1 n2 n3 n4 n6, g₀ r h0]
  · rw [r₁₂.gpr (.ra, 0) (by decide), g₀ .ra (by decide)]
  · rw [r₁₂.sp, RegUpd.sp_write, sp₁₀, sp₉, h₈.sp, sp₇, h₆.sp, sp₅]
  · intro key msg hr hR hcnt hlen
    rw [hp.a0] at hr
    show Spec.Cmac.Repr s₁₂.mem (s₀.gpr .a0) key (msg ++ Spec.Aes.bytesAt s₀.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat)
    rw [hp.a0, hp.a3, hp.a4, r₁₂.mem, RegUpd.mem_write]
    rw [hp.a4] at hlen
    obtain hcm : c = msg.length := by rw [← hc, hcnt, toNat_ofNat (by omega_using [hlen])]
    subst hcm
    obtain hRk : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.a1]; exact hR
    obtain hRb : 16 * (R + 1) ≤ 272 := by rcases hp.rounds with h | h | h <;> omega_using [h]
    obtain hsch := ((Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr).1.2.1
    rw [← hRk] at hsch
    -- The key and the data are in none of the regions written.
    obtain dK : ∀ r ∈ K, (⟨St, 272⟩ : Region).Disjoint r := by
      intro r hr
      simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (slots_sub S)
      · exact Offset.base_disjoint St (by omega_using []) (by omega_using [hfh])
      · exact Offset.base_disjoint St (by omega_using []) (by omega_using [])
      · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      · exact Offset.base_disjoint St (by omega_using []) (by omega_using [hrr])
    obtain dDat : ∀ r ∈ K, (⟨D, L⟩ : Region).Disjoint r := by
      intro r hr
      simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hp.d_s.sub_right (slots_sub S)
      · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_using [hfh]))
      · exact hp.st_d.symm.sub_right (Offset.sub_base St (by decide))
      · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
      · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_using [hrr]))
    obtain ciph : ∀ m : Mem, Frame K s₀.mem m →
        Spec.Cmac.aesWith R (Spec.Aes.bytesAt m St (16 * (R + 1))) = Spec.Cmac.aes key := fun m hf => by
      rw [bytesAt_frame hf (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega_using [hRb]), hsch,
        Spec.Cmac.aes, ← hRk]
    -- The data, wherever it is read.
    obtain dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ L →
        Spec.Aes.bytesAt m (D + BitVec.ofNat 64 a) b =
          ((Spec.Aes.bytesAt s₀.mem D L).drop a).take b := fun m hf a b hab => by
      rw [Proof.Cmac.Stream.bytesAt_offset m D hab, bytesAt_frame hf dDat (by omega_using [hL])]
    obtain fS' : Frame K s₀.mem (absMem s₀ S) := fS.mono (by simp [K])
    -- The chaining value.
    obtain cv5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 272) 16 := by
      rw [bytesAt_frame fC1 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_using []) (by omega_using []) (by omega_using [hfh]))
          (by decide),
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).sub_right (slots_sub S))
          (by decide)]
    obtain cv10 : Spec.Aes.bytesAt s₁₀.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₈.mem (St + BitVec.ofNat 64 272) 16 :=
      bytesAt_frame fC2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_using []) (by omega_using []) (by omega_using [hrr]))
        (by decide)
    have out6 := h₆.out
    rw [ciph _ F5] at out6
    have out8 := h₈.out
    rw [m₇, ciph _ F6] at out8
    obtain hk : ∀ i < 272, s₁₀.mem (St + BitVec.ofNat 64 i) = s₀.mem (St + BitVec.ofNat 64 i) :=
      fun i hi => frame_at F10 dK (by omega_using [hw]) hi
    obtain hdl : (Spec.Aes.bytesAt s₀.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    -- The bytes held back so far, and the first `f` bytes of data after them.
    obtain hb5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 288) (held msg.length + fOf msg.length L) =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 288) (held msg.length) ++
          (Spec.Aes.bytesAt s₀.mem D L).take (fOf msg.length L) := by
      obtain e := bytesAt_writeBytes (absMem s₀ S) (St + BitVec.ofNat 64 288) (held msg.length)
        (Spec.Aes.bytesAt (absMem s₀ S) D (fOf msg.length L)) (by rw [hlf]; omega_using [hfh])
      rw [hlf] at e
      rw [m₅, m4, ← Offset.add_add, e,
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hfh]))).sub_right (slots_sub S))
          (by omega_using [hfh])]
      refine congrArg (_ ++ ·) ?_
      have := dat _ fS' 0 (fOf msg.length L) (by omega_using [hfL])
      rwa [BitVec.add_zero, List.drop_zero] at this
    generalize hd : Spec.Aes.bytesAt s₀.mem D L = d at hdl hb5 dat ⊢
    by_cases hx : leftOf msg.length L = 0
    · -- Everything fits in the block held back.
      obtain hfL' : fOf msg.length L = L := by unfold leftOf at hx; omega_using [hfL, hx]
      obtain hb : b1Of msg.length L = 0 := by simp [b1Of, hx]
      obtain hn : nbOf msg.length L = 0 := by simp [nbOf, hx]
      obtain hr0 : restOf msg.length L = 0 := by simp [restOf, hn, hx]
      obtain m108 : s₁₀.mem = s₈.mem := by
        rw [h₁₀.mem, m₉, hr0, show Spec.Aes.bytesAt s₈.mem
          (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L)) 0 = [] from rfl, writeBytes_nil]
      refine Proof.Cmac.Stream.repr_fill hr hk (by rw [hdl]; have := (f_le msg.length L).2; omega_using [hfh, hfL']) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _
        rw [cv10, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
        exact cv5
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _
        obtain sub : Region.Sub ⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ ⟨St, 304⟩ :=
          Offset.sub_base St (by omega_using [hfh, hfL'])
        obtain dj : ∀ r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩],
            (⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ : Region).Disjoint r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint St (by omega_using []) (by omega_using [hfh, hfL']) (by omega_using [])
          · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
        have hb5' := hb5
        rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
        rw [m108, hdl, bytesAt_frame f8 dj (by omega_using [hfh, hfL']), bytesAt_frame f6 dj (by omega_using [hfh, hfL']), hb5']
    · -- The block held back is complete, and more blocks may follow.
      obtain hlt : 16 - held msg.length < L := by unfold leftOf fOf at hx; omega_using [hx]
      obtain hf' : fOf msg.length L = 16 - held msg.length := by unfold fOf; omega_using [hlt]
      obtain hb : b1Of msg.length L = 1 := by simp [b1Of, hx]
      obtain hn : nbOf msg.length L = Proof.Cmac.Stream.nblocks msg.length L := by
        simp only [nbOf, hx, ↓reduceIte]
        unfold leftOf Proof.Cmac.Stream.nblocks
        rw [hf']
      have hb5' := hb5
      rw [hf', Nat.add_sub_cancel' hh] at hb5'
      refine Proof.Cmac.Stream.repr_chain hr hk (by rw [hdl]; exact hlt) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ =
          Spec.Cmac.chain _ (Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _)
            ([Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _] ++ _)
        rw [cv10, out8, out6, hb, blocksAt_one, cv5, Proof.Cmac.chain_append, Proof.Cmac.Stream.blocksAt_eq,
          dat _ F6 _ _ (by omega_using [hsum]), hb5', hdl, hf', hn]
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = _
        obtain e := bytesAt_writeBytes_self s₈.mem (St + BitVec.ofNat 64 288)
          (xs := Spec.Aes.bytesAt s₈.mem (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L))
            (restOf msg.length L)) (by rw [Proof.Cmac.bytesAt_length]; omega_using [hrr])
        rw [Proof.Cmac.bytesAt_length] at e
        obtain hr' : d.length - (16 - held msg.length) - 16 * Proof.Cmac.Stream.nblocks msg.length d.length =
            restOf msg.length L := by
          rw [hdl, ← hn, ← hf']; rfl
        rw [hr', h₁₀.mem, m₉, e, dat _ F8 _ _ (by omega_using [hsum]),
          List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega_using []),
          List.drop_drop, hdl, ← hn, hf']

end VG.Proof.CmacAes.Stream.RISCV64

end

end

/-! ### `CmacAes.Stream.RISCV64.Init`, which only this module used -/

section

/-!
# Streaming AES-CMAC on RISC-V: `vg_cmac_aes_init`

As on PPC64LE (`Proof/CmacAes/Stream/PPC64LE/Frame.lean`): the code saves
`ra`, `s1`, `s2` and `s3` in the scratch buffer at `sv2 S`
(`Spill.save_ok`), expands the key into the state, derives the subkeys after
the schedule, zeroes the chaining value a byte at a time
(`Bytes.storeBytes_ok`) and restores the registers (`Spill.restore_wp`): the
state then represents the empty message. The code between the calls is
constant time by the taint analysis, and the calls by their own proofs
(`ek_rel`, `sub_rel`), their arguments pinned by `IMid₁` and `IMid₂`.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacAes.Stream.RISCV64
open VG.Proof.AesCbc.RISCV64 (taintRegs wp_sp)

/-- The precondition, by name: the state `St`, the key `Kp` of `KL` bytes
and the scratch buffer `S`. -/
structure IPre (s₀ : State) (St Kp S : Addr) (KL : Nat) : Prop where
  a0 : s₀.gpr .a0 = St
  a1 : s₀.gpr .a1 = Kp
  a2 : (s₀.gpr .a2).toNat = KL
  a3 : s₀.gpr .a3 = S
  rd : s₀.rd = [⟨Kp, KL⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 2304⟩]
  st_k : (⟨St, 304⟩ : Region).Disjoint ⟨Kp, KL⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  k_s : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32

theorem IPre.of {s₀ : State} (h : initRISCV64.pre s₀) :
    IPre s₀ (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a3) (s₀.gpr .a2).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

theorem IPre.rounds {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL) :
    KL / 4 + 6 = 10 ∨ KL / 4 + 6 = 12 ∨ KL / 4 + 6 = 14 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

/-- What the code saves: the registers, with `t0` the slots' base. -/
abbrev initG (s₀ : State) (S : Addr) : Reg → BitVec 64 := (s₀.write .t0 (sv2 S)).gpr

/-- The memory after saving the registers. -/
abbrev initMem (s₀ : State) (S : Addr) : Mem := Spill.saveMem s₀.mem (sv2 S) (initG s₀ S) initSaved

theorem init_bound : ∀ p ∈ initSaved, p.2 + 8 ≤ 32 := by decide

/-! ## Before the first call -/

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ : State) (St Kp S : Addr) (KL : Nat) (s : State) : Prop where
  args : EArgs s Kp St S KL
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  s3 : s.gpr .s3 = BitVec.ofNat 64 (KL / 4 + 6)
  other : ∀ r ∈ preserved, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s.gpr r = s₀.gpr r
  mem : s.mem = initMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initPre_wp {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL) :
    WP isa (.block initPre) s₀ (IMid₁ s₀ St Kp S KL) := by
  have sw := hp.wS
  obtain hKL : s₀.gpr .a2 = BitVec.ofNat 64 KL := ofNat_toNat_eq hp.a2
  rw [initPre, List.append_assoc, WP.block_append_iff]
  refine WP.mono (savePtr2_ok .a3) fun s₁ e => ?_
  subst e
  rw [hp.a3, show initSaved.map (fun (r, d) => Instr.store .d r .t0 d) = Spill.saveCode .t0 initSaved from rfl]
  obtain t₀ : (s₀.write .t0 (sv2 S)).gpr .t0 = sv2 S := RegUpd.gpr_write_self _ _ _
  have g₀ (r : Reg) (hr : r ≠ .t0) : (s₀.write .t0 (sv2 S)).gpr r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine Spill.save_ok (b := .t0) (l := initSaved) (by rw [t₀]; exact Align.align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · have := init_bound p hp'
    rw [t₀]
    show InRegions s₀.wr _ 8
    rw [hp.wr]
    exact ⟨⟨S, 2304⟩, by simp, sv2_contains S (by omega_using [this])⟩
  generalize ht : ({ (s₀.write .t0 (sv2 S)) with
    mem := Spill.saveMem (s₀.write .t0 (sv2 S)).mem ((s₀.write .t0 (sv2 S)).gpr .t0)
      (s₀.write .t0 (sv2 S)).gpr initSaved } : State) = t
  have gt (r : Reg) (hr : r ≠ .t0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact g₀ r hr
  obtain memt : t.mem = initMem s₀ S := by
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [t₀, RegUpd.mem_write]
  obtain rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  obtain wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  unfold Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_srl (by decide) fun s₃ u₃ =>
    wp_addi (imm := 6) (by decide) fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ =>
    wp_mv fun s₇ u₇ => WP.block_nil ?_
  obtain rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, rdt]
  obtain wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, wrt]
  obtain s1 : s₇.gpr .s1 = St := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr,
      gt, hp.a0]
  obtain s2 : s₇.gpr .s2 = S := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other,
      gt, hp.a3]
  obtain s3 : s₇.gpr .s3 = BitVec.ofNat 64 (KL / 4 + 6) := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.gpr, u₂.other, u₁.other,
      gt, hKL]
    exact rounds_bv hp.klen
  refine ⟨?_, s1, s2, s3, fun r hr h1 h2 h3 => ?_, ?_, rd₇, wr₇⟩
  · exact
    { a0 := by simp (disch := decide) only [u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, u₂.other,
          u₁.other, gt, hp.a1]
      a1 := by simp (disch := decide) only [u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, u₂.other,
          u₁.other, gt, hKL]
      a2 := by simp (disch := decide) only [u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other,
          u₁.gpr, gt, hp.a0]
      a3 := by simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other,
          u₁.other, gt, hp.a3]
      klen := hp.klen
      kw := hp.st_k.symm.sub_right (Region.sub_prefix (by decide))
      ks := hp.k_s.sub_right (Region.sub_prefix (by decide))
      ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      reads := by
        rw [rd₇, wr₇, hp.rd, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨Kp, KL⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₇, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩ }
  · obtain ⟨h0, -, -, -, -, -, -, -, ha0, ha1, ha2, -⟩ := preserved_ne r hr
    rw [u₇.other _ ha2, u₆.other _ ha1, u₅.other _ ha0, u₄.other _ h3, u₃.other _ h3, u₂.other _ h2,
      u₁.other _ h1, gt _ h0]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, memt]

/-! ## Between the calls -/

/-- What the code between the calls leaves. -/
structure IMid₂ (s₀ : State) (St S : Addr) (KL : Nat) (m : Mem) (s : State) : Prop where
  args : SArgs s St (St + BitVec.ofNat 64 240) S (KL / 4 + 6)
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  keep : ∀ r ∈ preserved, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s.gpr r = s₀.gpr r
  mem : s.mem = m
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initMid_wp {s₀ s : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL)
    (h1 : s.gpr .s1 = St) (h2 : s.gpr .s2 = S) (h3 : s.gpr .s3 = BitVec.ofNat 64 (KL / 4 + 6))
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hk : ∀ r ∈ preserved, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s.gpr r = s₀.gpr r) :
    WP isa (.block initMid) s (IMid₂ s₀ St S KL s.mem) := by
  have hw := hp.wSt
  obtain kSt : Region.Sub ⟨St + BitVec.ofNat 64 240, 32⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  unfold initMid Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_addi (imm := 240) (by decide) fun s₃ u₃ =>
    wp_mv fun s₄ u₄ => WP.block_nil ?_
  obtain rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, hrd]
  obtain wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hwr]
  refine ⟨?_, by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h1],
    by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h2],
    fun r hr a b c => ?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], rd₄, wr₄⟩
  · exact
    { a0 := by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.gpr, h1]
      a1 := by simp (disch := decide) only [u₄.other, u₃.other, u₂.gpr, u₁.other, h3]
      a2 := by simp (disch := decide) only [u₄.other, u₃.gpr, u₂.other, u₁.other, h1]
      a3 := by simp (disch := decide) only [u₄.gpr, u₃.other, u₂.other, u₁.other, h2]
      rounds := hp.rounds
      wk := Offset.base_disjoint St (by decide) (by omega_using [])
      ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      ks := (hp.st_s.sub_left kSt).sub_right (Region.sub_prefix (by decide))
      wrapK := by rw [toNat_add_lt St hw (by decide)]; omega_using [hw]
      wrapS := by have := hp.wS; omega_using [this]
      reads := by
        rw [rd₄, wr₄, hp.rd, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨St, 304⟩, by simp, 240, rfl, by simp⟩
        · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₄, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨St, 304⟩, by simp, 240, rfl, by simp⟩
        · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩ }
  · obtain ⟨-, -, -, -, -, -, -, -, ha0, ha1, ha2, ha3, -⟩ := preserved_ne r hr
    rw [u₄.other _ ha3, u₃.other _ ha2, u₂.other _ ha1, u₁.other _ ha0, hk r hr a b c]

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initRISCV64.pre s₀) :
    WP isa init s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.sp = s₀.sp ∧ initRISCV64.post s₀ s' := by
  obtain hp := IPre.of h0
  generalize s₀.gpr .a0 = St at hp
  generalize s₀.gpr .a1 = Kp at hp
  generalize s₀.gpr .a3 = S at hp
  generalize (s₀.gpr .a2).toNat = KL at hp
  have hw := hp.wSt
  have hsw := hp.wS
  refine WP.seq (WP.mono (wp_sp (initPre_wp hp)) fun s₁ ⟨h₁, sp₁⟩ => ?_)
  refine WP.seq (WP.mono (ek_call h₁.args) fun s₂ h₂ => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s₁.gpr r := h₂.saved r hr
  refine WP.seq (WP.mono (wp_sp (initMid_wp hp (by rw [g₂ _ (by decide), h₁.s1])
    (by rw [g₂ _ (by decide), h₁.s2]) (by rw [g₂ _ (by decide), h₁.s3]) (by rw [h₂.rd, h₁.rd])
    (by rw [h₂.wr, h₁.wr]) (fun r hr a b c => by rw [g₂ r hr, h₁.other r hr a b c]))) fun s₃ ⟨h₃, sp₃⟩ => ?_)
  refine WP.seq (WP.mono (wp_sp (sub_call h₃.args)) fun s₄ ⟨h₄, sp₄⟩ => ?_)
  have g₄ (r : Reg) (hr : r ∈ preserved) : s₄.gpr r = s₃.gpr r := h₄.saved r hr
  obtain s1₄ : s₄.gpr .s1 = St := by rw [g₄ _ (by decide), h₃.s1]
  obtain s2₄ : s₄.gpr .s2 = S := by rw [g₄ _ (by decide), h₃.s2]
  rw [initPost, List.append_assoc, WP.block_append_iff]
  refine WP.mono (Bytes.storeBytes_ok (tmp := .t1) (dst := .s1) (doff := 272) (bs := List.replicate 16 0)
    (by decide) (by decide) (by decide) (fun i hi => ?_)) fun s₅ h₅ => ?_
  · rw [h₄.wr, h₃.wr, hp.wr, s1₄]
    simp only [List.length_replicate] at hi
    exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  obtain s2₅ : s₅.gpr .s2 = S := by rw [h₅.gpr _ (by decide), s2₄]
  rw [WP.block_append_iff]
  refine WP.mono (savePtr2_ok .s2) fun s₆ e => ?_
  subst e
  rw [s2₅]
  -- The memory, step by step.
  obtain fz : Frame [⟨St + BitVec.ofNat 64 272, 16⟩] s₄.mem s₅.mem := by
    have := h₅.frame; rwa [s1₄, List.length_replicate] at this
  have f₂ : Frame [⟨St, 240⟩, ⟨S, 512⟩] s₁.mem s₂.mem := h₂.frame
  have f₄ : Frame [⟨St + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩] s₃.mem s₄.mem := h₄.frame
  have m₃ : s₃.mem = s₂.mem := h₃.mem
  -- The saved registers.
  have dSv (p : Reg × Nat) (hp' : p ∈ initSaved) (r : Region) (hr : r ∈ [⟨St, 240⟩, ⟨S, 512⟩,
      ⟨St + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩, ⟨St + BitVec.ofNat 64 272, 16⟩]) :
      (⟨sv2 S + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint r := by
    obtain hb := init_bound p hp'
    obtain sub : Region.Sub ⟨sv2 S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 2304⟩ := sv2_sub S (by omega_using [hb])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact (sv2_ws S (by omega_using [hb])).sub_right (Region.sub_prefix (by decide))
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
    · exact sv2_ws S (by omega_using [hb])
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
  obtain sv₁ : Spill.Saved (sv2 S) (initG s₀ S) initSaved s₁.mem := by
    rw [h₁.mem]; exact Spill.saveMem_saved (by decide) s₀.mem (sv2 S) _
  obtain sv₂ := sv₁.frame f₂ fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  rw [← m₃] at sv₂
  obtain sv₄ := sv₂.frame f₄ fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  obtain sv₅ := sv₄.frame fz fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; subst hr; simp)
  rw [show initSaved.map (fun (r, d) => Instr.load .d r .t0 d) = Spill.restoreCode .t0 initSaved from rfl]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := initSaved) (B := sv2 S) (Align.align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) sv₅) fun s₇ r₇ => ?_
  · have := init_bound p hp'
    show InRegions (s₅.rd ++ s₅.wr) _ 8
    rw [h₅.rd, h₅.wr, h₄.rd, h₄.wr, h₃.rd, h₃.wr, hp.rd, hp.wr]
    exact ⟨⟨S, 2304⟩, by simp, sv2_contains S (by omega_using [this])⟩
  have g₀ (r : Reg) (hr : r ≠ .t0) : initG s₀ S r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · have h0 := (preserved_ne r hr).1
    rw [r₇.gpr_of (r := r) ?_, g₀ r h0]
    by_cases hv : r = .s1 ∨ r = .s2 ∨ r = .s3
    · left; rcases hv with rfl | rfl | rfl <;> decide
    · right
      obtain ⟨-, h1, -⟩ := preserved_ne r hr
      rw [RegUpd.gpr_write_of_ne _ _ h0, h₅.gpr _ h1, g₄ r hr, h₃.keep r hr (fun e => hv (.inl e))
        (fun e => hv (.inr (.inl e))) (fun e => hv (.inr (.inr e))), g₀ r h0]
  · rw [r₇.gpr (.ra, 0) (by decide), g₀ .ra (by decide)]
  · rw [r₇.sp, RegUpd.sp_write, h₅.sp, sp₄, sp₃, h₂.sp, sp₁]
  · show Spec.Cmac.Repr s₇.mem (s₀.gpr .a0) (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat) []
    rw [hp.a0, hp.a1, hp.a2, Proof.Cmac.Stream.repr_iff, r₇.mem, RegUpd.mem_write]
    obtain f₁ : Frame [⟨sv2 S, 32⟩] s₀.mem s₁.mem := by
      rw [h₁.mem]
      have := Spill.saveMem_frame_base (l := initSaved) (n := 32) init_bound (by decide) s₀.mem (sv2 S) (initG s₀ S)
      exact this
    obtain hkey : Spec.Aes.bytesAt s₁.mem Kp KL = Spec.Aes.bytesAt s₀.mem Kp KL :=
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := sv2_sub S (d := 0) (n := 32) (by decide)
        rw [BitVec.add_zero] at this
        exact hp.k_s.sub_right this) (by have := hp.wK; omega_using [this])
    obtain hlen : (Spec.Aes.bytesAt s₀.mem Kp KL).length = KL := Proof.Cmac.bytesAt_length _ _ _
    have dSt (d n : Nat) (hd : d + n ≤ 272) (r : Region) (hr : r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩]) :
        (⟨St + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_using [hd]) (by omega_using [hd]) (by omega_using [])
    obtain hRb : 16 * (Spec.Aes.rounds (KL / 4) + 1) ≤ 240 := by
      have := hp.klen; simp only [Spec.Aes.rounds]; omega_using [this]
    -- The schedule, from the first call on.
    obtain sch : ∀ {d n : Nat}, d + n ≤ 240 → Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₂.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
      rw [Proof.Cmac.bytesAt_frame fz (dSt d n (by omega_using [hd])) (by omega_using [hd]),
        Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint St (by omega_using [hd]) (by omega_using [hd]) (by omega_using [])
          · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hd]))).sub_right (Region.sub_prefix (by decide)))
          (by omega_using [hd]), m₃]
    obtain hsch : Spec.Aes.bytesAt s₂.mem St (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem Kp KL) := by rw [h₂.out, hkey]
    refine ⟨⟨by rw [hlen]; exact hp.klen, ?_, ?_⟩, ?_, by simp [Proof.Cmac.Stream.held_zero, Spec.Aes.bytesAt]⟩
    · rw [hlen]
      have := sch (d := 0) (n := 16 * (Spec.Aes.rounds (KL / 4) + 1)) (by omega_using [hRb])
      rw [BitVec.add_zero] at this; rw [this, hsch]
    · have e : Spec.Aes.bytesAt s₅.mem (St + 240) 32 = Spec.Aes.bytesAt s₄.mem (St + 240) 32 :=
        Proof.Cmac.bytesAt_frame fz (dSt 240 32 (by decide)) (by decide)
      rw [e]
      refine h₄.out.trans ?_
      rw [m₃, show KL / 4 + 6 = Spec.Aes.rounds (KL / 4) from rfl, hsch]
      simp only [Spec.Cmac.aes, hlen]
    · refine (?_ : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 272) 16 = Spec.Cmac.zeros 16).trans rfl
      apply List.ext_getElem (by simp [Spec.Aes.bytesAt, Spec.Cmac.zeros])
      intro j h₁ _
      simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h₁
      simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, Spec.Cmac.zeros, List.getElem_replicate]
      have := h₅.stored j (by simpa using h₁)
      obtain hz : ∀ j < 16, (List.replicate 16 (0 : Nat)).getD j 0 = 0 := by decide
      rw [s1₄, ← Offset.add_add, hz j h₁] at this
      rw [this]; rfl

/-! ## Constant time -/

/-- What the call of `vg_aes_expand_key_scratch` leaves, for `initMid`. -/
structure IAfter (s₀ : State) (St S : Addr) (KL : Nat) (s : State) : Prop where
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  s3 : s.gpr .s3 = BitVec.ofNat 64 (KL / 4 + 6)
  keep : ∀ r ∈ preserved, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ek_after {s₀ s : State} {St Kp S : Addr} {KL : Nat} (h : IMid₁ s₀ St Kp S KL s) :
    WP isa ekCall s (IAfter s₀ St S KL) :=
  WP.mono (ek_call h.args) fun _ h₂ =>
    ⟨by rw [h₂.saved _ (by decide), h.s1], by rw [h₂.saved _ (by decide), h.s2],
      by rw [h₂.saved _ (by decide), h.s3], fun r hr a b c => by rw [h₂.saved r hr, h.other r hr a b c],
      by rw [h₂.rd, h.rd], by rw [h₂.wr, h.wr]⟩

theorem init_rel {s₀ s₀' : State} (h0 : initRISCV64.pre s₀) (h0' : initRISCV64.pre s₀')
    (hq : initRISCV64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') init fun _ _ => True := by
  obtain ⟨q3, q4, q5, q6, qsp⟩ := hq
  obtain hp := IPre.of h0
  obtain hp' : IPre s₀' (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a3) (s₀.gpr .a2).toNat := by
    rw [q3, q4, q5, q6]; exact IPre.of h0'
  generalize s₀.gpr .a0 = St at hp hp'
  generalize s₀.gpr .a1 = Kp at hp hp'
  generalize s₀.gpr .a3 = S at hp hp'
  generalize (s₀.gpr .a2).toNat = KL at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3]) (.block initPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1, .s2, .s3]) (.block initMid) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1, .s2]) (.block initPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.a0, .a1, .a2, .a3]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨qsp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := fun (s : State) => IMid₁ s₀ St Kp S KL s ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => IMid₁ s₀' St Kp S KL s ∧ s.sp = s₀'.sp) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨wp_sp (initPre_wp hp), wp_sp (initPre_wp hp')⟩
  obtain e := (ek_rel (P := fun a b => (IMid₁ s₀ St Kp S KL a ∧ a.sp = s₀.sp) ∧
      (IMid₁ s₀' St Kp S KL b ∧ b.sp = s₀'.sp))
    fun a b h => ⟨h.1.1.args, h.2.1.args, by rw [h.1.2, h.2.2, qsp]⟩).wp
    (F₁ := fun (s : State) => IAfter s₀ St S KL s ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => IAfter s₀' St S KL s ∧ s.sp = s₀'.sp) fun a b h =>
      ⟨WP.mono (wp_sp (ek_after h.1.1)) fun _ h' => ⟨h'.1, by rw [h'.2, h.1.2]⟩,
       WP.mono (wp_sp (ek_after h.2.1)) fun _ h' => ⟨h'.1, by rw [h'.2, h.2.2]⟩⟩
  obtain m := (taintRegs (P := fun a b => (IAfter s₀ St S KL a ∧ a.sp = s₀.sp) ∧
      (IAfter s₀' St S KL b ∧ b.sp = s₀'.sp)) [.s1, .s2, .s3]
    (fun a b h => by
      refine ⟨by rw [h.1.2, h.2.2, qsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.1.s1, h.2.1.s1]
      · rw [h.1.1.s2, h.2.1.s2]
      · rw [h.1.1.s3, h.2.1.s3]) hB).wp
    (F₁ := fun (s : State) => (∃ m, IMid₂ s₀ St S KL m s) ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => (∃ m, IMid₂ s₀' St S KL m s) ∧ s.sp = s₀'.sp)
    fun a b h =>
      ⟨WP.mono (wp_sp (initMid_wp hp h.1.1.s1 h.1.1.s2 h.1.1.s3 h.1.1.rd h.1.1.wr h.1.1.keep))
          fun _ h' => ⟨⟨_, h'.1⟩, by rw [h'.2, h.1.2]⟩,
       WP.mono (wp_sp (initMid_wp hp' h.2.1.s1 h.2.1.s2 h.2.1.s3 h.2.1.rd h.2.1.wr h.2.1.keep))
          fun _ h' => ⟨⟨_, h'.1⟩, by rw [h'.2, h.2.2]⟩⟩
  obtain sk := (sub_rel (P := fun a b => ((∃ m, IMid₂ s₀ St S KL m a) ∧ a.sp = s₀.sp) ∧
      ((∃ m, IMid₂ s₀' St S KL m b) ∧ b.sp = s₀'.sp))
    fun a b ⟨⟨⟨_, h₁⟩, sp₁⟩, ⟨⟨_, h₂⟩, sp₂⟩⟩ => ⟨h₁.args, h₂.args, by rw [sp₁, sp₂, qsp]⟩).wp
    (F₁ := fun (s : State) => s.gpr .s1 = St ∧ s.gpr .s2 = S ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .s1 = St ∧ s.gpr .s2 = S ∧ s.sp = s₀'.sp)
    fun a b ⟨⟨⟨_, h₁⟩, sp₁⟩, ⟨⟨_, h₂⟩, sp₂⟩⟩ =>
      ⟨WP.mono (sub_call h₁.args) fun _ h => ⟨by rw [h.saved _ (by decide), h₁.s1],
          by rw [h.saved _ (by decide), h₁.s2], by rw [h.sp, sp₁]⟩,
        WP.mono (sub_call h₂.args) fun _ h => ⟨by rw [h.saved _ (by decide), h₂.s1],
          by rw [h.saved _ (by decide), h₂.s2], by rw [h.sp, sp₂]⟩⟩
  have p := taintRegs
    (P := fun a b => (a.gpr .s1 = St ∧ a.gpr .s2 = S ∧ a.sp = s₀.sp) ∧
      b.gpr .s1 = St ∧ b.gpr .s2 = S ∧ b.sp = s₀'.sp) [.s1, .s2]
    (fun a b h => by
      refine ⟨by rw [h.1.2.2, h.2.2.2, qsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2.1, h.2.2.1]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((sk.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem init_ct : ConstantTime isa initRISCV64.pre initRISCV64.pub init :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (init_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.RISCV64

end

end

/-!
# Streaming AES-CMAC on RISCV64: constant time of `absorb`, and `Verified`

Two runs of `vg_cmac_aes_absorb` from states that agree on the public
arguments are related piece by piece (`RelCT`): the taint analysis covers
the code between the calls, from the registers the correctness proof pins
to values of the public arguments (`AMid₁`, `AAfter₁`, `AMid₂`, `AAfter₂`)
and the stack pointer, which no code changes (`wp_sp`), and each call of
`vg_cmac_aes_update` is constant time by its own proof (`upd_rel`).

Then correctness and constant time of the three functions, a state
satisfying each precondition, and the shared contracts with the working
space as an argument (`Proof/CmacAes/Stream/Scratch.lean`), with no stack:
a call stores nothing in memory, and each function saves the return address
in the working space.

As on PPC64LE (`Proof/CmacAes/Stream/PPC64LE/Frame.lean`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacAes.Stream.RISCV64
open VG.Proof.AesCbc.RISCV64 (taintRegs wp_sp)

/-! ## Constant time of `absorb` -/

/-- What the first call leaves, for `chain2`. -/
structure AAfter₁ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = s₀.gpr .a1
  s3 : s.gpr .s3 = D + BitVec.ofNat 64 (fOf (s₀.gpr .a2).toNat L)
  s4 : s.gpr .s4 = BitVec.ofNat 64 (leftOf (s₀.gpr .a2).toNat L)
  s6 : s.gpr .s6 = S
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem call1_after {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : AMid₁ s₀ St D S L R s) (hsp : s.sp = s₀.sp) : WP isa updCall s (AAfter₁ s₀ St D S L) :=
  WP.mono (upd_call h.args) fun _ h₆ =>
    ⟨by rw [h₆.saved .s1 (by decide), h.s1], by rw [h₆.saved .s2 (by decide), h.s2],
      by rw [h₆.saved .s3 (by decide), h.s3], by rw [h₆.saved .s4 (by decide), h.s4],
      by rw [h₆.saved .s6 (by decide), h.s6], by rw [h₆.sp, hsp], by rw [h₆.rd, h.rd],
      by rw [h₆.wr, h.wr]⟩

/-- What `chain2` leaves, for the second call. -/
structure AMid₂ (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 64 272) (D + BitVec.ofNat 64 (fOf (s₀.gpr .a2).toNat L)) S R
    (nbOf (s₀.gpr .a2).toNat L)
  s1 : s.gpr .s1 = St
  s5 : s.gpr .s5 = BitVec.ofNat 64 (16 * nbOf (s₀.gpr .a2).toNat L)
  s3 : s.gpr .s3 = D + BitVec.ofNat 64 (fOf (s₀.gpr .a2).toNat L)
  s4 : s.gpr .s4 = BitVec.ofNat 64 (leftOf (s₀.gpr .a2).toNat L)
  s6 : s.gpr .s6 = S
  sp : s.sp = s₀.sp

theorem chain2_mid {s₀ s : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R)
    (h : AAfter₁ s₀ St D S L s) : WP isa chain2 s (AMid₂ s₀ St D S L R) := by
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .a2).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have ⟨hfL, _⟩ := f_le c L
  have hsum := nb_le c L
  obtain ⟨x14₆, x15₆, x16₆, x17₆, x19₆, sp₆, rd₆, wr₆⟩ := h
  rw [hc] at x16₆ x17₆
  refine WP.mono (wp_sp (chain2_wp (x := leftOf c L) (by unfold leftOf; omega_using [hL]) x17₆)) fun s₇ ⟨h₇, sp₇⟩ => ?_
  obtain ⟨x18₇, x7₇, x3₇, x4₇, x5₇, x6₇, x8₇, sv₇, -, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at x18₇ x7₇
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  subst hc
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf (s₀.gpr .a2).toNat L), 16 * nbOf (s₀.gpr .a2).toNat L⟩
      ⟨D, L⟩ := Offset.sub_base D (by omega_using [hsum])
  refine ⟨hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf (s₀.gpr .a2).toNat L))
    (n := nbOf (s₀.gpr .a2).toNat L)
    (by rw [x3₇, x14₆]) (by rw [x4₇, x15₆]) (by rw [x5₇, x14₆]) (by rw [x6₇, x16₆]) x7₇
    (by rw [x8₇, x19₆]) (by rw [rd₇, rd₆]) (by rw [wr₇, wr₆]) (by omega_using [hL, hsum])
    ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : nbOf (s₀.gpr .a2).toNat L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf (s₀.gpr .a2).toNat L)).isLt; omega_using []
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega_using [hsum, h0])]; omega_using [hsum, this])
    ⟨⟨D, L⟩, by simp, fOf (s₀.gpr .a2).toNat L, rfl, by simp; omega_using [hsum]⟩,
    by rw [sv₇ .s1 (by decide) (by decide), x14₆], x18₇,
    by rw [sv₇ .s3 (by decide) (by decide), x16₆],
    by rw [sv₇ .s4 (by decide) (by decide), x17₆],
    by rw [sv₇ .s6 (by decide) (by decide), x19₆], by rw [sp₇, sp₆]⟩

/-- What the second call leaves, for `absorbPost`. -/
structure AAfter₂ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  s1 : s.gpr .s1 = St
  s5 : s.gpr .s5 = BitVec.ofNat 64 (16 * nbOf (s₀.gpr .a2).toNat L)
  s3 : s.gpr .s3 = D + BitVec.ofNat 64 (fOf (s₀.gpr .a2).toNat L)
  s4 : s.gpr .s4 = BitVec.ofNat 64 (leftOf (s₀.gpr .a2).toNat L)
  s6 : s.gpr .s6 = S
  sp : s.sp = s₀.sp

theorem call2_after {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : AMid₂ s₀ St D S L R s) : WP isa updCall s (AAfter₂ s₀ St D S L) :=
  WP.mono (upd_call h.args) fun _ h₈ =>
    ⟨by rw [h₈.saved .s1 (by decide), h.s1], by rw [h₈.saved .s5 (by decide), h.s5],
      by rw [h₈.saved .s3 (by decide), h.s3], by rw [h₈.saved .s4 (by decide), h.s4],
      by rw [h₈.saved .s6 (by decide), h.s6], by rw [h₈.sp, h.sp]⟩

theorem absorb_rel {s₀ s₀' : State} (h0 : absorbRISCV64.pre s₀) (h0' : absorbRISCV64.pre s₀')
    (hq : absorbRISCV64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') absorb fun _ _ => True := by
  obtain ⟨q3, q4, q5, q6, q7, q8, qsp⟩ := hq
  have hp := APre.of h0
  have hp' : APre s₀' (s₀.gpr .a0) (s₀.gpr .a3) (s₀.gpr .a5) (s₀.gpr .a4).toNat (s₀.gpr .a1).toNat := by
    rw [q3, q4, q6, q7, q8]; exact APre.of h0'
  generalize s₀.gpr .a0 = St at hp hp'
  generalize s₀.gpr .a3 = D at hp hp'
  generalize s₀.gpr .a5 = S at hp hp'
  generalize (s₀.gpr .a4).toNat = L at hp hp'
  generalize (s₀.gpr .a1).toNat = R at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) absorbPre h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1, .s2, .s3, .s4, .s6]) chain2 h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1, .s3, .s4, .s5, .s6]) absorbPost h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.a0, .a1, .a2, .a3, .a4, .a5]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨qsp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := fun (s : State) => AMid₁ s₀ St D S L R s ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => AMid₁ s₀' St D S L R s ∧ s.sp = s₀'.sp) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨wp_sp (absorbPre_wp hp), wp_sp (absorbPre_wp hp')⟩
  have c₁ := (upd_rel (P := fun a b => (AMid₁ s₀ St D S L R a ∧ a.sp = s₀.sp) ∧
      (AMid₁ s₀' St D S L R b ∧ b.sp = s₀'.sp))
    fun a b h => ⟨h.1.1.args, by rw [q5]; exact h.2.1.args, by rw [h.1.2, h.2.2, qsp]⟩).wp
    (F₁ := AAfter₁ s₀ St D S L) (F₂ := AAfter₁ s₀' St D S L) fun a b h =>
      ⟨call1_after h.1.1 h.1.2, call1_after h.2.1 h.2.2⟩
  have m := (taintRegs (P := fun a b => AAfter₁ s₀ St D S L a ∧ AAfter₁ s₀' St D S L b)
    [.s1, .s2, .s3, .s4, .s6]
    (fun a b h => by
      refine ⟨by rw [h.1.sp, h.2.sp, qsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.s1, h.2.s1]
      · rw [h.1.s2, h.2.s2, q4]
      · rw [h.1.s3, h.2.s3, q5]
      · rw [h.1.s4, h.2.s4, q5]
      · rw [h.1.s6, h.2.s6]) hB).wp
    (F₁ := AMid₂ s₀ St D S L R) (F₂ := AMid₂ s₀' St D S L R) fun a b h => ⟨chain2_mid hp h.1, chain2_mid hp' h.2⟩
  have c₂ := (upd_rel (P := fun a b => AMid₂ s₀ St D S L R a ∧ AMid₂ s₀' St D S L R b)
    fun a b h => ⟨h.1.args, by rw [q5]; exact h.2.args, by rw [h.1.sp, h.2.sp, qsp]⟩).wp
    (F₁ := AAfter₂ s₀ St D S L) (F₂ := AAfter₂ s₀' St D S L) fun a b h =>
      ⟨call2_after h.1, call2_after h.2⟩
  have p := taintRegs (P := fun a b => AAfter₂ s₀ St D S L a ∧ AAfter₂ s₀' St D S L b)
    [.s1, .s3, .s4, .s5, .s6]
    (fun a b h => by
      refine ⟨by rw [h.1.sp, h.2.sp, qsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.s1, h.2.s1]
      · rw [h.1.s3, h.2.s3, q5]
      · rw [h.1.s4, h.2.s4, q5]
      · rw [h.1.s5, h.2.s5, q5]
      · rw [h.1.s6, h.2.s6]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem absorb_ct : ConstantTime isa absorbRISCV64.pre absorbRISCV64.pub absorb :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (absorb_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

theorem init_correct (s : State) (hs : initRISCV64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ := init_wp hs
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

theorem absorb_correct (s : State) (hs : absorbRISCV64.pre s) :
    ∃ t s', Exec isa absorb s t s' ∧ abiPreserved s s' ∧ absorbRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ := absorb_wp hs
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

theorem finish_correct (s : State) (hs : finishRISCV64.pre s) :
    ∃ t s', Exec isa finish s t s' ∧ abiPreserved s s' ∧ finishRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ := finish_wp hs
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

/-- A state satisfying `vg_cmac_aes_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a2 => 16 | .a3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem init_verified : Verified RISCV64.target init (initScratchContract RISCV64.abi) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [initScratchContract, initScratchSig, Spec.Cmac.aesInitPre, Spec.Cmac.aesInitPost,
      initRISCV64, RISCV64.abi, RISCV64.argRegs] [initSat] using initSat)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition (with no data). -/
def absorbSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a3 => 0x3000 | .a5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem absorb_verified : Verified RISCV64.target absorb (absorbScratchContract RISCV64.abi) :=
  Verified.of_correct absorb_correct absorb_ct (by
    sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.aesAbsorbPre, Spec.Cmac.aesAbsorbPost,
      absorbRISCV64, RISCV64.abi, RISCV64.argRegs] [absorbSat] using absorbSat)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition. -/
def finishSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a3 => 0x2000 | .a4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 2304⟩]

theorem finish_verified : Verified RISCV64.target finish (finishScratchContract RISCV64.abi) :=
  Verified.of_correct finish_correct finish_ct (by
    sig_implies [finishScratchContract, finishScratchSig, Spec.Cmac.aesFinishPre, Spec.Cmac.aesFinishPost,
      finishRISCV64, RISCV64.abi, RISCV64.argRegs] [finishSat] using finishSat)

end VG.Proof.CmacAes.Stream.RISCV64

end

end

/-!
# Streaming AES-CMAC on RISC-V, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame of 2304 bytes that allocates it
(`Verified.stackScratchL`), all working space. Their code uses no other
stack: a call (`jal`) keeps the return address in `ra`, which they save in
the working space.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.RISCV64

open VG VG.RISCV64 VG.Impl.CmacAes.Stream.RISCV64

/-- A state satisfying `vg_cmac_aes_init`'s precondition, without the
working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 304⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.aesInitContract RISCV64.abi 2304).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, RISCV64.abi, RISCV64.argRegs] [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, without the
working space (and with no data). -/
def absorbFrameSat : State := { absorbSat with wr := [⟨0x1000, 304⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.aesAbsorbContract RISCV64.abi 2304).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, RISCV64.abi, RISCV64.argRegs] [absorbFrameSat, absorbSat]
    using absorbFrameSat

/-- A state satisfying `vg_cmac_aes_finish`'s precondition, without the
working space. -/
def finishFrameSat : State := { finishSat with wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.aesFinishContract RISCV64.abi 2304).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, RISCV64.abi, RISCV64.argRegs] [finishFrameSat, finishSat]
    using finishFrameSat

theorem init_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2304 .a3 init)
      (Spec.Cmac.aesInitContract RISCV64.abi 2304) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesInitPre RISCV64.abi.ptrBits)
    (post := Spec.Cmac.aesInitPost RISCV64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 2304) init_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.CmacAes.Stream.initPostOut_local _ vs m m₁ m₂ r hl)
    initFrameSat_pre

theorem absorb_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2304 .a5 absorb)
      (Spec.Cmac.aesAbsorbContract RISCV64.abi 2304) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesAbsorbPre RISCV64.abi.ptrBits)
    (post := Spec.Cmac.aesAbsorbPost RISCV64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 2304) absorb_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.CmacAes.Stream.absorbPostOut_local _ vs m m₁ m₂ r hl)
    absorbFrameSat_pre

theorem finish_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2304 .a4 finish)
      (Spec.Cmac.aesFinishContract RISCV64.abi 2304) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesFinishPre RISCV64.abi.ptrBits)
    (post := Spec.Cmac.aesFinishPost RISCV64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 2304) finish_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.CmacAes.Stream.finishPostOut_local _ vs m m₁ m₂ r hl)
    finishFrameSat_pre

end VG.Proof.CmacAes.Stream.RISCV64

end

end

/-!
# Streaming AES-CMAC on RISC-V, without secret residue

`vg_cmac_aes_init`, `vg_cmac_aes_absorb` and `vg_cmac_aes_finish`, each
followed by `Impl.Scrub.RISCV64.scrubTail` (`RISCV64.Scrub.scrubOf`), which
clears the caller-saved registers and the stack its frames used, their
2304 bytes of working space with it. Their postconditions read the memory
on return only within the state or the MAC (`RISCV64.Scrub.PostOut`), as on
x86-64 (`Proof/CmacAes/Stream/X86_64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Aes.ScrubLocal

/-! ## Postconditions -/

theorem finishOut (stack : Nat) :
    PostOut (Spec.Cmac.aesFinishContract RISCV64.abi stack) (Spec.Cmac.aesFinishSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [st, rd, ct, out], _ =>
      simp only [Spec.Cmac.aesFinishSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      intro key msg hr hro hc hlt
      show Spec.Aes.bytesAt m₂ out 16 = _
      rw [bytesAt_of0 hb.2 (by decide)]
      exact h key msg hr hro hc hlt

theorem initOut (stack : Nat) :
    PostOut (Spec.Cmac.aesInitContract RISCV64.abi stack) (Spec.Cmac.aesInitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [st, key, kl], _ =>
      simp only [Spec.Cmac.aesInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      exact Proof.CmacAes.Stream.repr_congr_304 (agree_le hb.1 (by decide)) h

theorem absorbOut (stack : Nat) :
    PostOut (Spec.Cmac.aesAbsorbContract RISCV64.abi stack) (Spec.Cmac.aesAbsorbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [st, rd, ct, dt, ln], _ =>
      simp only [Spec.Cmac.aesAbsorbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      intro key msg hr hro hc hlt
      exact Proof.CmacAes.Stream.repr_congr_304 (agree_le hb.1 (by decide)) (h key msg hr hro hc hlt)

/-! ## The registrations -/

/-- `vg_cmac_aes_init`. -/
def initReg : Registration Spec.Cmac.aesInitApi RISCV64.target :=
  scrubOf {
      code := Impl.StackScratch.RISCV64.withStackScratch 2304 .a3 Impl.CmacAes.Stream.RISCV64.init
      verified := Proof.CmacAes.Stream.RISCV64.init_framed }
    (initOut _)

/-- `vg_cmac_aes_absorb`. -/
def absorbReg : Registration Spec.Cmac.aesAbsorbApi RISCV64.target :=
  scrubOf {
      code := Impl.StackScratch.RISCV64.withStackScratch 2304 .a5 Impl.CmacAes.Stream.RISCV64.absorb
      verified := Proof.CmacAes.Stream.RISCV64.absorb_framed }
    (absorbOut _)

/-- `vg_cmac_aes_finish`. -/
def finishReg : Registration Spec.Cmac.aesFinishApi RISCV64.target :=
  scrubOf {
      code := Impl.StackScratch.RISCV64.withStackScratch 2304 .a4 Impl.CmacAes.Stream.RISCV64.finish
      verified := Proof.CmacAes.Stream.RISCV64.finish_framed }
    (finishOut _)

end VG.Proof.CmacAes.Stream.RISCV64.Scrub
