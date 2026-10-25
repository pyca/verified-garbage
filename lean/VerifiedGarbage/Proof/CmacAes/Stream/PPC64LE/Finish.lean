module

public import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Common
meta import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Common
import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Streaming AES-CMAC on PPC64LE: `vg_cmac_aes_finish`

The code copies the chaining value to `out`, saves `r14` and the return
address in the scratch buffer (`Spill.save_ok`), and calls
`vg_cmac_aes_finalize` with the state as its key, `out` as its state and the
bytes held back as the last bytes; then restores the registers
(`Spill.restore_ok`). The code around the call is constant time by the taint
analysis, and the call by its own proof (`fin_rel`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.Stream.PPC64LE
open VG.Proof.AesCbc.PPC64LE (taintRegs wp_sp)
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, `out` (`O`), the scratch
buffer `S` and the rounds `R`. -/
structure HPre (s₀ : State) (St O S : Addr) (R : Nat) : Prop where
  r3 : s₀.gpr .r3 = St
  r6 : s₀.gpr .r6 = O
  r7 : s₀.gpr .r7 = S
  r4 : (s₀.gpr .r4).toNat = R
  rd : s₀.rd = []
  wr : s₀.wr = [⟨St, 304⟩, ⟨O, 16⟩, ⟨S, 2304⟩]
  st_o : (⟨St, 304⟩ : Region).Disjoint ⟨O, 16⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  o_s : (⟨O, 16⟩ : Region).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wO : O.toNat + 16 ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem HPre.of {s₀ : State} (h : finishPPC64LE.pre s₀) :
    HPre s₀ (s₀.gpr .r3) (s₀.gpr .r6) (s₀.gpr .r7) (s₀.gpr .r4).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

/-! ## Before the call -/

/-- The memory after copying the block at `p` to `o`, a doubleword at a time. -/
def copyMem (m : Mem) (o p : Addr) : Mem :=
  let m₁ := m.writeW o (m.readW p 64)
  m₁.writeW (o + BitVec.ofNat 64 8) (m₁.readW (p + BitVec.ofNat 64 8) 64)

theorem copyMem_frame (m : Mem) (o p : Addr) : Frame [⟨o, 16⟩] m (copyMem m o p) :=
  Proof.Cmac.frame_store2 _ _ _

theorem copyMem_bytes (m : Mem) {o p : Addr} (h : (⟨o, 16⟩ : Region).Disjoint ⟨p, 16⟩) :
    Spec.Aes.bytesAt (copyMem m o p) o 16 = Spec.Aes.bytesAt m p 16 := by
  have g : Frame [⟨o, 8⟩] m (m.writeW o (m.readW p 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  rw [copyMem, Proof.Cmac.bytesAt_store2,
    g.readW (r := ⟨p + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.sub_left (Region.sub_prefix (by decide))).sub_right
          (Offset.sub_base p (d := 8) (n := 8) (k := 16) (by decide)) |>.symm) (by decide),
    Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]

theorem fin_bound : ∀ p ∈ finSaved, 2176 ≤ p.2 ∧ p.2 + 8 ≤ 2192 := by decide

/-- What the code before the call leaves. -/
structure HMid (s₀ : State) (St O S : Addr) (R : Nat) (s : State) : Prop where
  args : FArgs s St O (St + BitVec.ofNat 64 288) S (held (s₀.gpr .r5).toNat) R
  saved : Spill.Saved S (saveG s₀) finSaved s.mem
  frame : Frame [⟨O, 16⟩, ⟨S + BitVec.ofNat 64 2176, 16⟩] s₀.mem s.mem
  out : Spec.Aes.bytesAt s.mem O 16 = Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 272) 16
  r14 : s.gpr .r14 = S
  keep : ∀ r ∈ preserved, r ≠ .r14 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem HPre.fargs {s₀ s : State} {St O S : Addr} {R L : Nat} (hp : HPre s₀ St O S R) (hL : L ≤ 16)
    (r3 : s.gpr .r3 = St) (r4 : s.gpr .r4 = s₀.gpr .r4) (r5 : s.gpr .r5 = O)
    (r6 : s.gpr .r6 = St + BitVec.ofNat 64 288) (r7 : s.gpr .r7 = BitVec.ofNat 64 L)
    (r8 : s.gpr .r8 = S) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    FArgs s St O (St + BitVec.ofNat 64 288) S L R := by
  have hw := hp.wSt
  have pSt : Region.Sub ⟨St + BitVec.ofNat 64 288, L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_arith)
  exact
  { r3 := r3, r5 := r5, r6 := r6, r7 := r7, r8 := r8
    r4 := by rw [r4]; exact ofNat_toNat_eq hp.r4
    rounds := hp.rounds, len := hL
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left pSt
    ps := (hp.st_s.sub_left pSt).sub_right (Region.sub_prefix (by decide))
    sts := hp.o_s.sub_right (Region.sub_prefix (by decide))
    wrapK := by omega_arith
    wrapSt := hp.wO
    wrapP := by rw [toNat_add_lt St hw (by decide)]; omega_arith
    wrapS := by have := hp.wS; omega_arith
    reads := by
      rw [rd, wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega_arith⟩
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
is `count` in `r7`. -/
structure HMid₀ (s₀ : State) (St O S : Addr) (R : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = St
  r4 : s.gpr .r4 = s₀.gpr .r4
  r5 : s.gpr .r5 = O
  r6 : s.gpr .r6 = St + BitVec.ofNat 64 288
  r7 : s.gpr .r7 = s₀.gpr .r5
  r8 : s.gpr .r8 = S
  saved : Spill.Saved S (saveG s₀) finSaved s.mem
  frame : Frame [⟨O, 16⟩, ⟨S + BitVec.ofNat 64 2176, 16⟩] s₀.mem s.mem
  out : Spec.Aes.bytesAt s.mem O 16 = Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 272) 16
  r14 : s.gpr .r14 = S
  keep : ∀ r ∈ preserved, r ≠ .r14 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finishPre_wp {s₀ : State} {St O S : Addr} {R : Nat} (hp : HPre s₀ St O S R) :
    WP isa (.block finishPre) s₀ (HMid₀ s₀ St O S R) := by
  have hw := hp.wSt
  have inSt (d : Nat) (hd : d + 8 ≤ 304) : InRegions (s₀.rd ++ s₀.wr) (St + BitVec.ofNat 64 d) 8 := by
    rw [hp.rd, hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  have inO (d : Nat) (hd : d + 8 ≤ 16) : InRegions s₀.wr (O + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨O, 16⟩, by simp, Offset.contains_base _ hd (by have := hp.wO; omega_arith)⟩
  have inS (d : Nat) (hd : d + 8 ≤ 2304) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ hd (by have := hp.wS; omega_arith)⟩
  rw [finishPre, show finSaved.map (fun (r, d) => Instr.store .d r .r7 d) = Spill.saveCode .r7 finSaved
    from rfl, List.append_assoc]
  refine WP.cons exec_mflr ?_
  generalize ht : s₀.write .r0 s₀.lr = t
  have gt (r : Reg) (hr : r ≠ .r0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact saveG_ne hr
  have t0 : t.gpr .r0 = s₀.lr := by rw [← ht]; exact saveG_r0 s₀
  have rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  have wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  have mt : t.mem = s₀.mem := by rw [← ht]; rfl
  refine wp_ld (a := St + BitVec.ofNat 64 272) (by decide) (by decide) (by rw [gt _ (by decide), hp.r3])
    (by rw [rdt, wrt]; exact inSt 272 (by decide)) fun s₁ u₁ => ?_
  refine wp_std (a := O) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), gt _ (by decide), hp.r6, BitVec.add_zero])
    (by rw [u₁.wr, wrt]; simpa using inO 0 (by decide)) fun s₂ u₂ => ?_
  refine wp_ld (a := St + BitVec.ofNat 64 272 + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), gt _ (by decide), hp.r3, Offset.add_add])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, rdt, wrt, Offset.add_add]; exact inSt 280 (by decide)) fun s₃ u₃ => ?_
  refine wp_std (a := O + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), gt _ (by decide), hp.r6])
    (by rw [u₃.wr, u₂.wr, u₁.wr, wrt]; exact inO 8 (by decide)) fun s₄ u₄ => ?_
  have g₄ (r : Reg) (hr : r ≠ .r9) : s₄.gpr r = t.gpr r := by
    rw [u₄.gpr, u₃.other _ hr, u₂.gpr, u₁.other _ hr]
  have m₄ : s₄.mem = copyMem s₀.mem O (St + BitVec.ofNat 64 272) := by
    rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, mt, copyMem]
  refine Spill.save_ok (b := .r7) (l := finSaved) (by decide) (by decide) (fun p hp' => ?_) ?_
  · have := fin_bound p hp'
    rw [g₄ _ (by decide), gt _ (by decide), hp.r7, u₄.wr, u₃.wr, u₂.wr, u₁.wr, wrt]; exact inS _ (by omega_arith)
  generalize hv : ({ s₄ with mem := Spill.saveMem s₄.mem (s₄.gpr .r7) s₄.gpr finSaved } : State) = v
  have gv (r : Reg) : v.gpr r = s₄.gpr r := by rw [← hv]
  have mv : v.mem = Spill.saveMem (copyMem s₀.mem O (St + BitVec.ofNat 64 272)) S s₄.gpr finSaved := by
    rw [← hv]; show Spill.saveMem _ _ _ _ = _; rw [m₄, g₄ _ (by decide), gt _ (by decide), hp.r7]
  have rdv : v.rd = s₀.rd := by rw [← hv]; show s₄.rd = _; rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, rdt]
  have wrv : v.wr = s₀.wr := by rw [← hv]; show s₄.wr = _; rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, wrt]
  unfold Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₅ u₅ => wp_mr fun s₆ u₆ => wp_mr fun s₇ u₇ => wp_mr fun s₈ u₈ =>
    wp_addi (by decide) (by decide) fun s₉ u₉ => wp_nil ?_
  have fS : Frame [⟨S + BitVec.ofNat 64 2176, 16⟩] (copyMem s₀.mem O (St + BitVec.ofNat 64 272)) v.mem := by
    rw [mv]; exact Spill.saveMem_frame (lo := 2176) (n := 16) fin_bound (by omega_arith) _ _ _
  have m₉ : s₉.mem = v.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr h14 => ?_, ?_, ?_⟩
  · simp (disch := decide) only [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, gv, g₄, gt, hp.r3]
  · simp (disch := decide) only [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, gv, g₄, gt]
  · simp (disch := decide) only [u₉.other, u₈.gpr, u₇.other, u₆.other, u₅.other, gv, g₄, gt, hp.r6]
  · simp (disch := decide) only [u₉.gpr, u₈.other, u₇.other, u₆.other, u₅.other, gv, g₄, gt, hp.r3]
  · simp (disch := decide) only [u₉.other, u₈.other, u₇.gpr, u₆.other, u₅.other, gv, g₄, gt]
  · simp (disch := decide) only [u₉.other, u₈.other, u₇.other, u₆.gpr, u₅.other, gv, g₄, gt, hp.r7]
  · rw [m₉, mv]
    refine saved_congr (Spill.saveMem_saved (by decide) _ S _) fun p hp' => ?_
    simp only [finSaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · show s₄.gpr .r0 = saveG s₀ .r0; rw [g₄ _ (by decide), t0, saveG_r0]
    · show s₄.gpr .r14 = saveG s₀ .r14; rw [g₄ _ (by decide), gt _ (by decide), saveG_ne (by decide)]
  · rw [m₉]
    exact ((copyMem_frame _ _ _).mono (by simp)).trans (fS.mono (by simp))
  · rw [m₉, Proof.Cmac.bytesAt_frame16 fS (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.o_s.sub_right (Offset.sub_base S (by decide)))]
    exact copyMem_bytes _ (hp.st_o.symm.sub_right (Offset.sub_base St (by decide)))
  · simp (disch := decide) only [u₉.other, u₈.other, u₇.other, u₆.other, u₅.gpr, gv, g₄, gt, hp.r7]
  · obtain ⟨h0, -, -, h5, h6, h7, h8, h9, -⟩ := preserved_ne r hr
    rw [u₉.other _ h6, u₈.other _ h5, u₇.other _ h7, u₆.other _ h8, u₅.other _ h14, gv, g₄ _ h9, gt _ h0]
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, rdv]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, wrv]

theorem finPre_wp {s₀ : State} {St O S : Addr} {R : Nat} (hp : HPre s₀ St O S R) :
    WP isa finPre s₀ (HMid s₀ St O S R) := by
  refine WP.seq (WP.mono (finishPre_wp hp) fun s₁ h₁ => ?_)
  have hc := (s₀.gpr .r5).isLt
  have h5 : s₀.gpr .r5 = BitVec.ofNat 64 (s₀.gpr .r5).toNat := ofNat_toNat_eq rfl
  have ev := eval_zero_ofNat s₁ .r7 hc (by rw [h₁.r7]; exact h5)
  by_cases h0 : (s₀.gpr .r5).toNat = 0
  · refine WP.ite true (by rw [ev, h0]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨hp.fargs (held_le _) h₁.r3 h₁.r4 h₁.r5 h₁.r6 ?_ h₁.r8 h₁.rd h₁.wr, h₁.saved, h₁.frame, h₁.out,
      h₁.r14, h₁.keep, h₁.rd, h₁.wr⟩
    rw [h₁.r7, h5, h0]; rfl
  · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
    have hne : s₀.gpr .r5 ≠ 0 := fun e => h0 (by rw [e]; rfl)
    refine wp_subi (by decide) (by decide) fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ =>
      wp_and fun s₄ u₄ => wp_addi (by decide) (by decide) fun s₅ u₅ => wp_nil ?_
    have g (r : Reg) (a : r ≠ .r7) (b : r ≠ .r9) : s₅.gpr r = s₁.gpr r := by
      rw [u₅.other _ a, u₄.other _ a, u₃.other _ b, u₂.other _ a]
    have hc : ∀ r ∈ preserved, r ≠ .r7 ∧ r ≠ .r9 := by decide
    have m₅ : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    refine ⟨hp.fargs (held_le _) (by rw [g _ (by decide) (by decide), h₁.r3])
      (by rw [g _ (by decide) (by decide), h₁.r4]) (by rw [g _ (by decide) (by decide), h₁.r5])
      (by rw [g _ (by decide) (by decide), h₁.r6]) ?_ (by rw [g _ (by decide) (by decide), h₁.r8])
      (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, h₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, h₁.wr]),
      by rw [m₅]; exact h₁.saved, by rw [m₅]; exact h₁.frame, by rw [m₅]; exact h₁.out,
      by rw [g _ (by decide) (by decide), h₁.r14],
      fun r hr h14 => by rw [g r (hc r hr).1 (hc r hr).2, h₁.keep r hr h14],
      by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, h₁.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, h₁.wr]⟩
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.gpr, h₁.r7]
    exact held_bv _ hne

/-! ## The whole function -/

theorem finish_wp {s₀ : State} (h0 : finishPPC64LE.pre s₀) :
    WP isa finish s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧
      finishPPC64LE.post s₀ s' := by
  have hp := HPre.of h0
  generalize s₀.gpr .r3 = St at hp
  generalize s₀.gpr .r6 = O at hp
  generalize s₀.gpr .r7 = S at hp
  generalize (s₀.gpr .r4).toNat = R at hp
  have hw := hp.wSt
  have sw := hp.wS
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (fin_call h₁.args) fun s₂ h₂ => ?_)
  have r14₂ : s₂.gpr .r14 = S := by rw [h₂.saved _ (by decide), h₁.r14]
  -- The slots, which the call does not write.
  have sv₂ : Spill.Saved S (saveG s₀) finSaved s₂.mem := h₁.saved.frame h₂.frame fun p hp' r hr => by
    have := fin_bound p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.o_s.symm.sub_left (Offset.sub_base S (by omega_arith))
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  rw [finishPost, show finSaved.map (fun (r, d) => Instr.load .d r .r14 d) = Spill.restoreCode .r14 finSaved
    from rfl]
  refine Spill.restore_ok (b := .r14) (l := finSaved) (by decide) r14₂ (by decide) (by decide)
    (fun p hp' => ?_) sv₂ fun s₃ r₃ => WP.cons exec_mtlr (wp_nil ⟨fun r hr => ?_, ?_, ?_⟩)
  · have := fin_bound p hp'
    rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hp.rd, hp.wr]
    exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · show s₃.gpr r = _
    rw [r₃.gpr_of (r := r) ?_, saveG_ne (preserved_ne r hr).1]
    by_cases h14 : r = .r14
    · left; subst h14; decide
    · right; rw [h₂.saved r hr, h₁.keep r hr h14, saveG_ne (preserved_ne r hr).1]
  · show s₃.gpr .r0 = _
    rw [r₃.gpr (.r0, 2184) (by decide)]; exact saveG_r0 s₀
  · intro key msg hr hR hc hlen
    rw [hp.r3] at hr
    rw [Proof.Cmac.Stream.repr_iff] at hr
    obtain ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩ := hr
    have hn : (s₀.gpr .r5).toNat = msg.length := by rw [hc, toNat_ofNat hlen]
    show Spec.Aes.bytesAt s₃.mem (s₀.gpr .r6) 16 = _
    rw [hp.r6, r₃.mem]
    have hR' : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.r4]; exact hR
    -- The state is unchanged before the call.
    have fSt : ∀ {d n : Nat}, d + n ≤ 304 → Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
      exact Proof.Cmac.bytesAt_frame h₁.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.st_o.sub_left (Offset.sub_base St hd)
        · exact (hp.st_s.sub_left (Offset.sub_base St hd)).sub_right (Offset.sub_base S (by decide)))
        (by omega_arith)
    have hsch : Spec.Aes.bytesAt s₁.mem St (16 * (R + 1)) = Spec.Aes.expandKey key := by
      have := fSt (d := 0) (n := 16 * (R + 1)) (by rcases hp.rounds with h | h | h <;> omega_arith)
      rw [BitVec.add_zero] at this; rw [this, hR']; exact hks
    have hciph : Spec.Cmac.aesWith R (Spec.Aes.bytesAt s₁.mem St (16 * (R + 1))) = Spec.Cmac.aes key := by
      rw [hsch, hR']; rfl
    have e₁ : Spec.Aes.bytesAt s₁.mem (St + 240) 32 = Spec.Aes.bytesAt s₀.mem (St + 240) 32 :=
      fSt (d := 240) (by decide)
    have e₂ : Spec.Aes.bytesAt s₁.mem O 16 = Spec.Aes.bytesAt s₀.mem (St + 272) 16 := h₁.out
    have e₃ : Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 288) (held (s₀.gpr .r5).toNat) =
        Spec.Aes.bytesAt s₀.mem (St + 288) (held msg.length) := by
      rw [hn]; exact fSt (by have := held_le msg.length; omega_arith)
    obtain ⟨hm, hne, hst, happ⟩ := Proof.Cmac.Stream.repr_finish
      ((Proof.Cmac.Stream.repr_iff _ _ _ _).mpr ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩)
    have out := h₂.out (by rw [hciph, e₁]; exact hsk) _ hm (by rw [hn]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, e₃, happ, Proof.Cmac.Stream.aesCmac_eq]

/-! ## Constant time -/

theorem finish_rel {s₀ s₀' : State} (h0 : finishPPC64LE.pre s₀)
    (h0' : finishPPC64LE.pre s₀') (hq : finishPPC64LE.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finish fun _ _ => True := by
  obtain ⟨q3, q4, q5, q6, q7, qsp⟩ := hq
  have hp := HPre.of h0
  have hp' : HPre s₀' (s₀.gpr .r3) (s₀.gpr .r6) (s₀.gpr .r7) (s₀.gpr .r4).toNat := by
    rw [q3, q4, q6, q7]; exact HPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) finPre h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r14]) (.block finishPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.r3, .r4, .r5, .r6, .r7]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨qsp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := fun (s : State) => HMid s₀ (s₀.gpr .r3) (s₀.gpr .r6) (s₀.gpr .r7) (s₀.gpr .r4).toNat s ∧
      s.sp = s₀.sp)
    (F₂ := fun (s : State) => HMid s₀' (s₀.gpr .r3) (s₀.gpr .r6) (s₀.gpr .r7) (s₀.gpr .r4).toNat s ∧
      s.sp = s₀'.sp) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨wp_sp (finPre_wp hp), wp_sp (finPre_wp hp')⟩
  have c := (fin_rel (P := fun s₁ s₂ =>
      (HMid s₀ (s₀.gpr .r3) (s₀.gpr .r6) (s₀.gpr .r7) (s₀.gpr .r4).toNat s₁ ∧ s₁.sp = s₀.sp) ∧
      (HMid s₀' (s₀.gpr .r3) (s₀.gpr .r6) (s₀.gpr .r7) (s₀.gpr .r4).toNat s₂ ∧ s₂.sp = s₀'.sp))
    fun s₁ s₂ h => ⟨h.1.1.args, by rw [q5]; exact h.2.1.args, by rw [h.1.2, h.2.2, qsp]⟩).wp
    (F₁ := fun (s : State) => s.gpr .r14 = s₀.gpr .r7 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .r14 = s₀.gpr .r7 ∧ s.sp = s₀'.sp) fun s₁ s₂ h =>
      ⟨WP.mono (fin_call h.1.1.args) fun _ hc =>
        ⟨by rw [hc.saved .r14 (by decide), h.1.1.r14], by rw [hc.sp, h.1.2]⟩,
       WP.mono (fin_call h.2.1.args) fun _ hc =>
        ⟨by rw [hc.saved .r14 (by decide), h.2.1.r14], by rw [hc.sp, h.2.2]⟩⟩
  have b := taintRegs
    (P := fun s₁ s₂ => (s₁.gpr .r14 = s₀.gpr .r7 ∧ s₁.sp = s₀.sp) ∧ (s₂.gpr .r14 = s₀.gpr .r7 ∧ s₂.sp = s₀'.sp))
    [.r14] (fun s₁ s₂ h => ⟨by rw [h.1.2, h.2.2, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.1, h.2.1]⟩) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem finish_ct : ConstantTime isa finishPPC64LE.pre finishPPC64LE.pub finish :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finish_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.PPC64LE
