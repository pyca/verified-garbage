module

public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common
meta import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common
import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
meta import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Align
meta import VerifiedGarbage.Proof.Framework.RISCV64.Align
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Streaming AES-CMAC on RISCV64: `vg_cmac_aes_finish`

As on PPC64LE (`Proof/CmacAes/Stream/PPC64LE/Finish.lean`): the code copies
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
  have pSt : Region.Sub ⟨St + BitVec.ofNat 64 288, L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega)
  exact
  { a0 := a0, a2 := a2, a3 := a3, a4 := a4, a5 := a5
    a1 := by rw [a1]; exact ofNat_toNat_eq hp.a1
    rounds := hp.rounds, len := hL
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left pSt
    ps := (hp.st_s.sub_left pSt).sub_right (Region.sub_prefix (by decide))
    sts := hp.o_s.sub_right (Region.sub_prefix (by decide))
    wrapK := by omega
    wrapSt := hp.wO
    wrapP := by rw [toNat_add_lt St hw (by decide)]; omega
    wrapS := by have := hp.wS; omega
    reads := by
      rw [rd, wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega⟩
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
  · rw [hp.rd, hp.wr, hp.a0]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [hp.wr, hp.a3]; exact ⟨⟨O, 16⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [hp.a3, hp.a0, BitVec.add_zero] at hc
    exact hp.st_o _ (Offset.contains_base _ (by omega) (by omega)) hc
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
    exact ⟨⟨S, 2304⟩, by simp, sv2_contains S (by have := fin_bound p hp'; omega)⟩
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
    · exact hp.o_s.symm.sub_left (sv2_sub S (by omega))
    · exact sv2_ws S (by omega)
  rw [finishPost, WP.block_append_iff]
  refine WP.mono (savePtr2_ok .s1) fun s₃ e => ?_
  subst e
  rw [s1₂, show finSaved.map (fun (r, d) => Instr.load .d r .t0 d) = Spill.restoreCode .t0 finSaved from rfl]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := finSaved) (B := sv2 S) (Align.align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) sv₂) fun s₄ r₄ => ?_
  · have := fin_bound p hp'
    show InRegions (s₂.rd ++ s₂.wr) _ 8
    rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hp.rd, hp.wr]
    exact ⟨⟨S, 2304⟩, by simp, sv2_contains S (by omega)⟩
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
        (by omega)
    have hsch : Spec.Aes.bytesAt s₁.mem St (16 * (R + 1)) = Spec.Aes.expandKey key := by
      have := fSt (d := 0) (n := 16 * (R + 1)) (by rcases hp.rounds with h | h | h <;> omega)
      rw [BitVec.add_zero] at this; rw [this, hR']; exact hks
    have hciph : Spec.Cmac.aesWith R (Spec.Aes.bytesAt s₁.mem St (16 * (R + 1))) = Spec.Cmac.aes key := by
      rw [hsch, hR']; rfl
    have e₁ : Spec.Aes.bytesAt s₁.mem (St + 240) 32 = Spec.Aes.bytesAt s₀.mem (St + 240) 32 :=
      fSt (d := 240) (by decide)
    have e₂ : Spec.Aes.bytesAt s₁.mem O 16 = Spec.Aes.bytesAt s₀.mem (St + 272) 16 := h₁.out
    have e₃ : Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 288) (held (s₀.gpr .a2).toNat) =
        Spec.Aes.bytesAt s₀.mem (St + 288) (held msg.length) := by
      rw [hn]; exact fSt (by have := held_le msg.length; omega)
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
