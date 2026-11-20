module

public import VerifiedGarbage.Impl.StackScratch.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
meta import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
public import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Common
meta import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Mem

/-! ### `CmacAes.Stream.PPC64LE.Verified`, which only this module used -/

section

/-! ### `CmacAes.Stream.PPC64LE.Finish`, which only this module used -/

section

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
  wr : s₀.wr = [⟨St, 304⟩, ⟨O, 16⟩, ⟨S, 128⟩]
  st_o : (⟨St, 304⟩ : Region).Disjoint ⟨O, 16⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 128⟩
  o_s : (⟨O, 16⟩ : Region).Disjoint ⟨S, 128⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wO : O.toNat + 16 ≤ 2 ^ 64
  wS : S.toNat + 128 ≤ 2 ^ 64
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
  obtain g : Frame [⟨o, 8⟩] m (m.writeW o (m.readW p 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  rw [copyMem, Proof.Cmac.bytesAt_store2,
    g.readW (r := ⟨p + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.sub_left (Region.sub_prefix (by decide))).sub_right
          (Offset.sub_base p (d := 8) (n := 8) (k := 16) (by decide)) |>.symm) (by decide),
    Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]

theorem fin_bound : ∀ p ∈ finSaved, 64 ≤ p.2 ∧ p.2 + 8 ≤ 80 := by decide

/-- What the code before the call leaves. -/
structure HMid (s₀ : State) (St O S : Addr) (R : Nat) (s : State) : Prop where
  args : FArgs s St O (St + BitVec.ofNat 64 288) S (held (s₀.gpr .r5).toNat) R
  saved : Spill.Saved S (saveG s₀) finSaved s.mem
  frame : Frame [⟨O, 16⟩, ⟨S + BitVec.ofNat 64 64, 16⟩] s₀.mem s.mem
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
  obtain pSt : Region.Sub ⟨St + BitVec.ofNat 64 288, L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_arith)
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
      · exact ⟨⟨S, 128⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨O, 16⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 128⟩, by simp, 0, by simp, by simp⟩ }

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
  frame : Frame [⟨O, 16⟩, ⟨S + BitVec.ofNat 64 64, 16⟩] s₀.mem s.mem
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
  have inS (d : Nat) (hd : d + 8 ≤ 128) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ hd (by have := hp.wS; omega_arith)⟩
  rw [finishPre, show finSaved.map (fun (r, d) => Instr.store .d r .r7 d) = Spill.saveCode .r7 finSaved
    from rfl, List.append_assoc]
  refine WP.cons exec_mflr ?_
  generalize ht : s₀.write .r0 s₀.lr = t
  have gt (r : Reg) (hr : r ≠ .r0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact saveG_ne hr
  obtain t0 : t.gpr .r0 = s₀.lr := by rw [← ht]; exact saveG_r0 s₀
  obtain rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  obtain wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  obtain mt : t.mem = s₀.mem := by rw [← ht]; rfl
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
  obtain m₄ : s₄.mem = copyMem s₀.mem O (St + BitVec.ofNat 64 272) := by
    rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, mt, copyMem]
  refine Spill.save_ok (b := .r7) (l := finSaved) (by decide) (by decide) (fun p hp' => ?_) ?_
  · have := fin_bound p hp'
    rw [g₄ _ (by decide), gt _ (by decide), hp.r7, u₄.wr, u₃.wr, u₂.wr, u₁.wr, wrt]; exact inS _ (by omega_arith)
  generalize hv : ({ s₄ with mem := Spill.saveMem s₄.mem (s₄.gpr .r7) s₄.gpr finSaved } : State) = v
  have gv (r : Reg) : v.gpr r = s₄.gpr r := by rw [← hv]
  obtain mv : v.mem = Spill.saveMem (copyMem s₀.mem O (St + BitVec.ofNat 64 272)) S s₄.gpr finSaved := by
    rw [← hv]; show Spill.saveMem _ _ _ _ = _; rw [m₄, g₄ _ (by decide), gt _ (by decide), hp.r7]
  obtain rdv : v.rd = s₀.rd := by rw [← hv]; show s₄.rd = _; rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, rdt]
  obtain wrv : v.wr = s₀.wr := by rw [← hv]; show s₄.wr = _; rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, wrt]
  unfold Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₅ u₅ => wp_mr fun s₆ u₆ => wp_mr fun s₇ u₇ => wp_mr fun s₈ u₈ =>
    wp_addi (by decide) (by decide) fun s₉ u₉ => wp_nil ?_
  obtain fS : Frame [⟨S + BitVec.ofNat 64 64, 16⟩] (copyMem s₀.mem O (St + BitVec.ofNat 64 272)) v.mem := by
    rw [mv]; exact Spill.saveMem_frame (lo := 64) (n := 16) fin_bound (by omega_arith) _ _ _
  obtain m₉ : s₉.mem = v.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]
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
  obtain hc := (s₀.gpr .r5).isLt
  obtain h5 : s₀.gpr .r5 = BitVec.ofNat 64 (s₀.gpr .r5).toNat := ofNat_toNat_eq rfl
  obtain ev := eval_zero_ofNat s₁ .r7 hc (by rw [h₁.r7]; exact h5)
  by_cases h0 : (s₀.gpr .r5).toNat = 0
  · refine WP.ite true (by rw [ev, h0]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨hp.fargs (held_le _) h₁.r3 h₁.r4 h₁.r5 h₁.r6 ?_ h₁.r8 h₁.rd h₁.wr, h₁.saved, h₁.frame, h₁.out,
      h₁.r14, h₁.keep, h₁.rd, h₁.wr⟩
    rw [h₁.r7, h5, h0]; rfl
  · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
    obtain hne : s₀.gpr .r5 ≠ 0 := fun e => h0 (by rw [e]; rfl)
    refine wp_subi (by decide) (by decide) fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ =>
      wp_and fun s₄ u₄ => wp_addi (by decide) (by decide) fun s₅ u₅ => wp_nil ?_
    have g (r : Reg) (a : r ≠ .r7) (b : r ≠ .r9) : s₅.gpr r = s₁.gpr r := by
      rw [u₅.other _ a, u₄.other _ a, u₃.other _ b, u₂.other _ a]
    obtain hc : ∀ r ∈ preserved, r ≠ .r7 ∧ r ≠ .r9 := by decide
    obtain m₅ : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
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
  obtain hp := HPre.of h0
  generalize s₀.gpr .r3 = St at hp
  generalize s₀.gpr .r6 = O at hp
  generalize s₀.gpr .r7 = S at hp
  generalize (s₀.gpr .r4).toNat = R at hp
  have hw := hp.wSt
  have sw := hp.wS
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (fin_call h₁.args) fun s₂ h₂ => ?_)
  obtain r14₂ : s₂.gpr .r14 = S := by rw [h₂.saved _ (by decide), h₁.r14]
  -- The slots, which the call does not write.
  obtain sv₂ : Spill.Saved S (saveG s₀) finSaved s₂.mem := h₁.saved.frame h₂.frame fun p hp' r hr => by
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
    exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · show s₃.gpr r = _
    rw [r₃.gpr_of (r := r) ?_, saveG_ne (preserved_ne r hr).1]
    by_cases h14 : r = .r14
    · left; subst h14; decide
    · right; rw [h₂.saved r hr, h₁.keep r hr h14, saveG_ne (preserved_ne r hr).1]
  · show s₃.gpr .r0 = _
    rw [r₃.gpr (.r0, 72) (by decide)]; exact saveG_r0 s₀
  · intro key msg hr hR hc hlen
    rw [hp.r3] at hr
    rw [Proof.Cmac.Stream.repr_iff] at hr
    obtain ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩ := hr
    obtain hn : (s₀.gpr .r5).toNat = msg.length := by rw [hc, toNat_ofNat hlen]
    show Spec.Aes.bytesAt s₃.mem (s₀.gpr .r6) 16 = _
    rw [hp.r6, r₃.mem]
    obtain hR' : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.r4]; exact hR
    -- The state is unchanged before the call.
    obtain fSt : ∀ {d n : Nat}, d + n ≤ 304 → Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
      exact Proof.Cmac.bytesAt_frame h₁.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.st_o.sub_left (Offset.sub_base St hd)
        · exact (hp.st_s.sub_left (Offset.sub_base St hd)).sub_right (Offset.sub_base S (by decide)))
        (by omega_arith)
    obtain hsch : Spec.Aes.bytesAt s₁.mem St (16 * (R + 1)) = Spec.Aes.expandKey key := by
      have := fSt (d := 0) (n := 16 * (R + 1)) (by rcases hp.rounds with h | h | h <;> omega_arith)
      rw [BitVec.add_zero] at this; rw [this, hR']; exact hks
    obtain hciph : Spec.Cmac.aesWith R (Spec.Aes.bytesAt s₁.mem St (16 * (R + 1))) = Spec.Cmac.aes key := by
      rw [hsch, hR']; rfl
    obtain e₁ : Spec.Aes.bytesAt s₁.mem (St + 240) 32 = Spec.Aes.bytesAt s₀.mem (St + 240) 32 :=
      fSt (d := 240) (by decide)
    have e₂ : Spec.Aes.bytesAt s₁.mem O 16 = Spec.Aes.bytesAt s₀.mem (St + 272) 16 := h₁.out
    obtain e₃ : Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 288) (held (s₀.gpr .r5).toNat) =
        Spec.Aes.bytesAt s₀.mem (St + 288) (held msg.length) := by
      rw [hn]; exact fSt (by have := held_le msg.length; omega_arith)
    obtain ⟨hm, hne, hst, happ⟩ := Proof.Cmac.Stream.repr_finish
      ((Proof.Cmac.Stream.repr_iff _ _ _ _).mpr ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩)
    obtain out := h₂.out (by rw [hciph, e₁]; exact hsk) _ hm (by rw [hn]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, e₃, happ, Proof.Cmac.Stream.aesCmac_eq]

/-! ## Constant time -/

theorem finish_rel {s₀ s₀' : State} (h0 : finishPPC64LE.pre s₀)
    (h0' : finishPPC64LE.pre s₀') (hq : finishPPC64LE.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finish fun _ _ => True := by
  obtain ⟨q3, q4, q5, q6, q7, qsp⟩ := hq
  obtain hp := HPre.of h0
  obtain hp' : HPre s₀' (s₀.gpr .r3) (s₀.gpr .r6) (s₀.gpr .r7) (s₀.gpr .r4).toNat := by
    rw [q3, q4, q6, q7]; exact HPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) finPre h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r14]) (.block finishPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.r3, .r4, .r5, .r6, .r7]
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
  obtain c := (fin_rel (P := fun s₁ s₂ =>
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

end

end

/-! ### `CmacAes.Stream.PPC64LE.AbsorbCorrect`, which only this module used -/

section

/-! ### `CmacAes.Stream.PPC64LE.AbsorbBlocks`, which only this module used -/

section

/-!
# Streaming AES-CMAC on PPC64LE: `vg_cmac_aes_absorb`'s straight-line code

What each piece of code between the copies and calls computes, in terms of
`count` (`c`) and `len` (`L`), as on AArch64: the bytes held back
`h = held c`, the bytes copied after them `f = min L (16 - h)`, the data left
`L - f`, whether to chain the block held back (`b1`), the blocks chained
after it (`nb`), and the rest (`rest`); and the registers `absorb` saves at
`scratch + 64`, where the functions it calls do not write.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.Stream.PPC64LE
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

/-- The sign of `m - k`, for `m` and `k` of at most 16. -/
theorem lsr63 {m k : Nat} (hm : m ≤ 16) (hk : k ≤ 16) :
    (BitVec.ofNat 64 m - BitVec.ofNat 64 k) >>> 63 = BitVec.ofNat 64 (if m < k then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega_arith

/-- `16 nb` for the data left `x > 0`, as `subi 1; and 15; sub` computes it. -/
theorem nb16_bv {x : Nat} (hx : 0 < x) (hx' : x < 2 ^ 64) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 1 - ((BitVec.ofNat 64 x - BitVec.ofNat 64 1) &&& BitVec.ofNat 64 15) =
      BitVec.ofNat 64 (16 * ((x - 1) / 16)) := by
  apply BitVec.eq_of_toNat_eq
  obtain e : (BitVec.ofNat 64 x - BitVec.ofNat 64 1).toNat = x - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega_using [hx, hx']
  rw [BitVec.toNat_sub, and15, e, BitVec.toNat_ofNat]
  omega_using []

/-! ## Saving the registers -/

/-- The memory after saving the registers at `S + 64`. -/
abbrev absMem (s₀ : State) (S : Addr) : Mem := Spill.saveMem s₀.mem S (saveG s₀) saved

theorem abs_bound : ∀ p ∈ saved, 64 ≤ p.2 ∧ p.2 + 8 ≤ 120 := by decide

/-- Saving the registers changes only their slots. -/
theorem absMem_frame (s₀ : State) (S : Addr) :
    Frame [⟨S + BitVec.ofNat 64 64, 56⟩] s₀.mem (absMem s₀ S) :=
  Spill.saveMem_frame (lo := 64) (n := 56) abs_bound (by omega_using []) _ _ _

/-- What `save` leaves. -/
structure Saved₁ (s₀ : State) (S : Addr) (s : State) : Prop where
  r14 : s.gpr .r14 = s₀.gpr .r3
  r15 : s.gpr .r15 = s₀.gpr .r4
  r16 : s.gpr .r16 = s₀.gpr .r6
  r17 : s.gpr .r17 = s₀.gpr .r7
  r19 : s.gpr .r19 = S
  other : ∀ r, r ≠ .r0 → r ≠ .r14 → r ≠ .r15 → r ≠ .r16 → r ≠ .r17 → r ≠ .r19 → s.gpr r = s₀.gpr r
  mem : s.mem = absMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem save_wp (s₀ : State) {S : Addr} (hS : s₀.gpr .r8 = S)
    (hw : ∀ d, 64 ≤ d → d + 8 ≤ 120 → InRegions s₀.wr (S + BitVec.ofNat 64 d) 8) :
    WP isa (.block save) s₀ (Saved₁ s₀ S) := by
  rw [save, show saved.map (fun (r, d) => Instr.store .d r .r8 d) = Spill.saveCode .r8 saved from rfl]
  refine WP.cons exec_mflr (Spill.save_ok (b := .r8) (l := saved) (by decide) (by decide)
    (fun p hp' => ?_) ?_)
  · have := abs_bound p hp'
    show InRegions s₀.wr (s₀.gpr .r8 + BitVec.ofNat 64 p.2) 8
    rw [hS]; exact hw _ this.1 this.2
  generalize ht : ({ (s₀.write .r0 s₀.lr) with
    mem := (Spill.saveMem (s₀.write .r0 s₀.lr).mem ((s₀.write .r0 s₀.lr).gpr .r8) (s₀.write .r0 s₀.lr).gpr
      saved) } : State) = t
  have gt (r : Reg) (hr : r ≠ .r0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact saveG_ne hr
  obtain memt : t.mem = absMem s₀ S := by
    obtain e : (s₀.write .r0 s₀.lr).gpr .r8 = S := by rw [← hS]; exact saveG_ne (by decide)
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [e]; rfl
  obtain rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  obtain wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  unfold Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_mr fun s₄ u₄ =>
    wp_mr fun s₅ u₅ => wp_nil ⟨?_, ?_, ?_, ?_, ?_, fun r a b c d e f => ?_, ?_, ?_, ?_⟩
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

theorem held_wp {s : State} {c : Nat} (hc : c < 2 ^ 64) (hd : s.gpr .r5 = BitVec.ofNat 64 c) :
    WP isa held s fun s' => s'.gpr .r9 = BitVec.ofNat 64 (held c) ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ev := eval_zero_ofNat s .r5 hc hd
  by_cases h0 : c = 0
  · subst h0
    refine WP.ite true (by rw [ev]; rfl) (fun _ => ?_) (fun h => by cases h)
    exact wp_li (by decide) fun s₁ u₁ => wp_nil ⟨by rw [u₁.gpr]; rfl, fun r h _ => u₁.other r h, u₁.mem,
      u₁.rd, u₁.wr⟩
  · have hne : BitVec.ofNat 64 c ≠ 0 := fun e => h0 (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat hc] at this)
    refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
    refine wp_subi (by decide) (by decide) fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ =>
      wp_and fun s₃ u₃ => wp_addi (by decide) (by decide) fun s₄ u₄ => wp_nil ⟨?_, fun r a b => ?_, ?_, ?_, ?_⟩
    · rw [u₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, hd, held_bv _ hne, toNat_ofNat hc]
    · rw [u₄.other _ a, u₃.other _ a, u₂.other _ b, u₁.other _ a]
    · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-! ## `fill`: how many bytes to copy, and where -/

theorem clamp_wp {s : State} {L : Nat} (hL : L < 2 ^ 64) (h17 : s.gpr .r17 = BitVec.ofNat 64 L) :
    WP isa clamp s fun s' => s'.gpr .r10 = BitVec.ofNat 64 (min L 16) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_lsr (by decide) fun s₁ u₁ => wp_nil ?_)
  obtain x10 : s₁.gpr .r10 = BitVec.ofNat 64 (L / 16) := by
    rw [u₁.gpr, h17, shr_ofNat hL]
  obtain ev := eval_zero_ofNat s₁ .r10 (by omega_using [hL]) x10
  by_cases hl : L < 16
  · have e : L / 16 = 0 := by omega_using [hl]
    refine WP.ite true (by rw [ev, e]; rfl) (fun _ => ?_) (fun h => by cases h)
    unfold Impl.AesCbc.PPC64LE.mov
    refine wp_mr fun s₂ u₂ => wp_nil ⟨?_, fun r h => by rw [u₂.other _ h, u₁.other _ h],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
    rw [u₂.gpr, u₁.other _ (by decide), h17, Nat.min_eq_left (Nat.le_of_lt hl)]
  · have e : L / 16 ≠ 0 := by omega_using [hl]
    refine WP.ite false (by rw [ev]; simp [e]) (fun h => by cases h) fun _ => ?_
    refine wp_li (by decide) fun s₂ u₂ => wp_nil ⟨?_, fun r h => by rw [u₂.other _ h, u₁.other _ h],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
    rw [u₂.gpr, Nat.min_eq_right (Nat.le_of_not_lt hl)]

theorem fill_wp {s : State} {St D : Addr} {c L : Nat} (hL : L < 2 ^ 64)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (held c)) (h17 : s.gpr .r17 = BitVec.ofNat 64 L)
    (h14 : s.gpr .r14 = St) (h16 : s.gpr .r16 = D) :
    WP isa fill s fun s' => s'.gpr .r12 = BitVec.ofNat 64 (fOf c L) ∧
      s'.gpr .r8 = BitVec.ofNat 64 (fOf c L) ∧ s'.gpr .r10 = St + BitVec.ofNat 64 (288 + held c) ∧
      s'.gpr .r11 = D ∧
      (∀ r, r ≠ .r8 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hh := held_le c
  refine WP.seq (WP.mono (clamp_wp hL h17) fun s₁ ⟨x10₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (wp_li (by decide) fun s₂ u₂ => wp_sub fun s₃ u₃ => wp_sub fun s₄ u₄ =>
    wp_lsr (by decide) fun s₅ u₅ => wp_nil ?_)
  obtain x9₁ : s₁.gpr .r9 = BitVec.ofNat 64 (held c) := by rw [g₁ _ (by decide), h9]
  obtain x12₅ : s₅.gpr .r12 = BitVec.ofNat 64 (16 - held c) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), x9₁,
      Offset.ofNat_sub_ofNat hh]
  obtain x10₅ : s₅.gpr .r10 = BitVec.ofNat 64 (min L 16) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), x10₁]
  obtain x11₅ : s₅.gpr .r11 = BitVec.ofNat 64 (if min L 16 < 16 - held c then 1 else 0) := by
    rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), x10₁, u₃.gpr, u₂.gpr,
      u₂.other _ (by decide), x9₁, Offset.ofNat_sub_ofNat hh]
    exact lsr63 (by omega_using []) (by omega_using [])
  have g₅ (r : Reg) (a : r ≠ .r11) (b : r ≠ .r12) : s₅.gpr r = s₁.gpr r := by
    rw [u₅.other _ a, u₄.other _ a, u₃.other _ b, u₂.other _ b]
  obtain hf : fOf c L = min (min L 16) (16 - held c) := by unfold fOf; omega_using []
  obtain ev := eval_zero_ofNat s₅ .r11 (k := if min L 16 < 16 - held c then 1 else 0) (by split <;> omega_using []) x11₅
  refine WP.seq (WP.mono (Q := fun (s₆ : State) => s₆.gpr .r12 = BitVec.ofNat 64 (fOf c L) ∧
    (∀ r, r ≠ .r12 → s₆.gpr r = s₅.gpr r) ∧ s₆.mem = s₅.mem ∧ s₆.rd = s₅.rd ∧ s₆.wr = s₅.wr) ?_
    fun s₆ h₆ => ?_)
  · by_cases hl : min L 16 < 16 - held c
    · refine WP.ite false (by rw [ev]; simp [hl]) (fun h => by cases h) fun _ => ?_
      unfold Impl.AesCbc.PPC64LE.mov
      refine wp_mr fun s₆ u₆ => wp_nil ⟨?_, fun r h => u₆.other r h, u₆.mem, u₆.rd, u₆.wr⟩
      rw [u₆.gpr, x10₅, hf, Nat.min_eq_left (Nat.le_of_lt hl)]
    · refine WP.ite true (by rw [ev]; simp [hl]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [x12₅, hf, Nat.min_eq_right (Nat.le_of_not_lt hl)], fun _ _ => rfl, rfl, rfl, rfl⟩
  · obtain ⟨x12₆, g₆, m₆, rd₆, wr₆⟩ := h₆
    have g (r : Reg) (a : r ≠ .r12) (b : r ≠ .r11) (d : r ≠ .r10) : s₆.gpr r = s.gpr r := by
      rw [g₆ r a, g₅ r b a, g₁ r d]
    unfold Impl.AesCbc.PPC64LE.mov
    refine wp_mr fun s₇ u₇ => wp_add fun s₈ u₈ => wp_addi (by decide) (by decide) fun s₉ u₉ =>
      wp_mr fun s₁₀ u₁₀ => wp_nil ⟨?_, ?_, ?_, ?_, fun r a b d e => ?_, ?_, ?_, ?_⟩
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), x12₆]
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, x12₆]
    · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₇.other _ (by decide),
        g .r14 (by decide) (by decide) (by decide), g .r9 (by decide) (by decide) (by decide), h14, h9,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]
    · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        g .r16 (by decide) (by decide) (by decide), h16]
    · rw [u₁₀.other _ d, u₉.other _ b, u₈.other _ b, u₇.other _ a, g r e d b]
    · rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, m₆, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
    · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
    · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]

/-! ## `chain1`: the arguments of the first call -/

theorem chain1_wp {s : State} {St D S : Addr} {f L : Nat} (hf : f ≤ L) (hL : L < 2 ^ 64)
    (h16 : s.gpr .r16 = D) (h8 : s.gpr .r8 = BitVec.ofNat 64 f) (h17 : s.gpr .r17 = BitVec.ofNat 64 L)
    (h14 : s.gpr .r14 = St) (h19 : s.gpr .r19 = S) :
    WP isa chain1 s fun s' => s'.gpr .r16 = D + BitVec.ofNat 64 f ∧ s'.gpr .r17 = BitVec.ofNat 64 (L - f) ∧
      s'.gpr .r7 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧ s'.gpr .r3 = St ∧
      s'.gpr .r4 = s.gpr .r15 ∧ s'.gpr .r5 = St + BitVec.ofNat 64 272 ∧
      s'.gpr .r6 = St + BitVec.ofNat 64 288 ∧ s'.gpr .r8 = S ∧
      (∀ r ∈ preserved, r ≠ .r16 → r ≠ .r17 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_add fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ => wp_nil ?_)
  obtain x17₃ : s₃.gpr .r17 = BitVec.ofNat 64 (L - f) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h17, u₁.other _ (by decide), h8,
      Offset.ofNat_sub_ofNat hf]
  have g₃ (r : Reg) (a : r ≠ .r16) (b : r ≠ .r17) (c : r ≠ .r7) : s₃.gpr r = s.gpr r := by
    rw [u₃.other _ c, u₂.other _ b, u₁.other _ a]
  obtain ev := eval_zero_ofNat s₃ .r17 (k := L - f) (by omega_using [hL]) x17₃
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => s₄.gpr .r7 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧
    (∀ r, r ≠ .r7 → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr) ?_
    fun s₄ h₄ => ?_)
  · by_cases h0 : L - f = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [u₃.gpr]; simp [h0], fun _ _ => rfl, rfl, rfl, rfl⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine wp_li (by decide) fun s₄ u₄ => wp_nil ⟨?_, fun r h => u₄.other r h, u₄.mem, u₄.rd, u₄.wr⟩
      rw [u₄.gpr]; simp [h0]
  · obtain ⟨x7₄, g₄, m₄, rd₄, wr₄⟩ := h₄
    have g (r : Reg) (a : r ≠ .r16) (b : r ≠ .r17) (c : r ≠ .r7) : s₄.gpr r = s.gpr r := by
      rw [g₄ r c, g₃ r a b c]
    unfold Impl.AesCbc.PPC64LE.mov
    refine wp_mr fun s₅ u₅ => wp_mr fun s₆ u₆ => wp_addi (by decide) (by decide) fun s₇ u₇ =>
      wp_addi (by decide) (by decide) fun s₈ u₈ => wp_mr fun s₉ u₉ =>
      wp_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr a b => ?_, ?_, ?_, ?_⟩
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), g₄ _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h16, h8]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), g₄ _ (by decide), x17₃]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), x7₄]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.gpr, g .r14 (by decide) (by decide) (by decide), h14]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
        u₅.other _ (by decide), g .r15 (by decide) (by decide) (by decide)]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
        u₅.other _ (by decide), g .r14 (by decide) (by decide) (by decide), h14]
    · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), g .r14 (by decide) (by decide) (by decide), h14]
    · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), g .r19 (by decide) (by decide) (by decide), h19]
    · obtain ⟨-, n3, n4, n5, n6, n7, n8, -⟩ := preserved_ne r hr
      rw [u₉.other _ n8, u₈.other _ n6, u₇.other _ n5, u₆.other _ n4, u₅.other _ n3, g r a b n7]
    · rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄, u₃.mem, u₂.mem, u₁.mem]
    · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, rd₄, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr₄, u₃.wr, u₂.wr, u₁.wr]

/-! ## `chain2`: the arguments of the second call -/

theorem chain2_wp {s : State} {x : Nat} (hx : x < 2 ^ 64) (h17 : s.gpr .r17 = BitVec.ofNat 64 x) :
    WP isa chain2 s fun s' =>
      s'.gpr .r18 = BitVec.ofNat 64 (16 * (if x = 0 then 0 else (x - 1) / 16)) ∧
      s'.gpr .r7 = BitVec.ofNat 64 (if x = 0 then 0 else (x - 1) / 16) ∧ s'.gpr .r3 = s.gpr .r14 ∧
      s'.gpr .r4 = s.gpr .r15 ∧ s'.gpr .r5 = s.gpr .r14 + BitVec.ofNat 64 272 ∧
      s'.gpr .r6 = s.gpr .r16 ∧ s'.gpr .r8 = s.gpr .r19 ∧
      (∀ r ∈ preserved, r ≠ .r18 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => wp_nil ?_)
  obtain ev := eval_zero_ofNat s₁ .r17 hx (by rw [u₁.other _ (by decide), h17])
  refine WP.seq (WP.mono (Q := fun (s₂ : State) =>
    s₂.gpr .r18 = BitVec.ofNat 64 (16 * (if x = 0 then 0 else (x - 1) / 16)) ∧
    (∀ r, r ≠ .r18 → r ≠ .r9 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr) ?_ fun s₂ h₂ => ?_)
  · by_cases h0 : x = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [u₁.gpr]; simp [h0], fun _ _ _ => rfl, rfl, rfl, rfl⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine wp_subi (by decide) (by decide) fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ =>
        wp_and fun s₄ u₄ => wp_sub fun s₅ u₅ => wp_nil ⟨?_, fun r a b => ?_, ?_, ?_, ?_⟩
      · rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.gpr, u₃.other _ (by decide), u₂.gpr,
          u₁.other _ (by decide), h17]
        simp only [h0, ↓reduceIte]
        exact nb16_bv (by omega_using [h0]) hx
      · rw [u₅.other _ a, u₄.other _ b, u₃.other _ b, u₂.other _ a]
      · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
      · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd]
      · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr]
  · obtain ⟨x18₂, g₂, m₂, rd₂, wr₂⟩ := h₂
    have g (r : Reg) (a : r ≠ .r18) (b : r ≠ .r9) : s₂.gpr r = s.gpr r := by rw [g₂ r a b, u₁.other _ a]
    unfold Impl.AesCbc.PPC64LE.mov
    refine wp_lsr (by decide) fun s₃ u₃ => wp_mr fun s₄ u₄ => wp_mr fun s₅ u₅ =>
      wp_addi (by decide) (by decide) fun s₆ u₆ => wp_mr fun s₇ u₇ => wp_mr fun s₈ u₈ =>
      wp_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr a => ?_, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, x18₂]
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, x18₂]
      exact (shr_ofNat (by split <;> omega_arith)).trans (by congr 1; omega_using [])
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g]
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g]
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, g]
    · simp (disch := decide) only [u₈.other, u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, g]
    · simp (disch := decide) only [u₈.gpr, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g]
    · obtain ⟨-, n3, n4, n5, n6, n7, n8, n9, -⟩ := preserved_ne r hr
      rw [u₈.other _ n8, u₇.other _ n6, u₆.other _ n5, u₅.other _ n4, u₄.other _ n3, u₃.other _ n7, g r a n9]
    · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem]
    · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
    · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]

/-! ## `rest`: the arguments of the last copy -/

theorem rest_wp {s : State} {D : Addr} {a x n : Nat} (hn : 16 * n ≤ x)
    (h16 : s.gpr .r16 = D + BitVec.ofNat 64 a) (h18 : s.gpr .r18 = BitVec.ofNat 64 (16 * n))
    (h17 : s.gpr .r17 = BitVec.ofNat 64 x) :
    WP isa (.block rest) s fun s' => s'.gpr .r16 = D + BitVec.ofNat 64 (a + 16 * n) ∧
      s'.gpr .r17 = BitVec.ofNat 64 (x - 16 * n) ∧ s'.gpr .r10 = s.gpr .r14 + BitVec.ofNat 64 288 ∧
      s'.gpr .r11 = D + BitVec.ofNat 64 (a + 16 * n) ∧ s'.gpr .r12 = BitVec.ofNat 64 (x - 16 * n) ∧
      (∀ r ∈ preserved, r ≠ .r16 → r ≠ .r17 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain e : D + BitVec.ofNat 64 a + BitVec.ofNat 64 (16 * n) = D + BitVec.ofNat 64 (a + 16 * n) :=
    Offset.add_add _ _ _
  unfold rest Impl.AesCbc.PPC64LE.mov
  refine wp_add fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_addi (by decide) (by decide) fun s₃ u₃ =>
    wp_mr fun s₄ u₄ => wp_mr fun s₅ u₅ => wp_nil ⟨?_, ?_, ?_, ?_, ?_, fun r hr a b => ?_, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr, h16, h18, e]
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other, h17, h18]
    exact Offset.ofNat_sub_ofNat hn
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.gpr, u₂.other, u₁.other]
  · simp (disch := decide) only [u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.gpr, h16, h18, e]
  · simp (disch := decide) only [u₅.gpr, u₄.other, u₃.other, u₂.gpr, u₁.other, h17, h18]
    exact Offset.ofNat_sub_ofNat hn
  · obtain ⟨-, -, -, -, -, -, -, -, n10, n11, n12⟩ := preserved_ne r hr
    rw [u₅.other _ n12, u₄.other _ n11, u₃.other _ n10, u₂.other _ b, u₁.other _ a]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

end VG.Proof.CmacAes.Stream.PPC64LE

end

end


/-!
# Streaming AES-CMAC on PPC64LE: `vg_cmac_aes_absorb` is correct

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 16 - h)` bytes after them, and sets up the first call of
`vg_cmac_aes_update`, which chains the block held back if data is left
(`AMid₁`, `absorbPre_wp`). The second call chains the whole blocks of the
data left but its last 1 to 16 bytes (`nb`), and the last copy holds those
back. If no data is left (`len ≤ 16 - h`), the calls chain nothing and the
copy copies nothing, and the data is appended to the bytes held back
(`repr_fill`); otherwise `repr_chain`. As on AArch64.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.Stream.PPC64LE VG.WriteBytes
open VG.Proof.Cmac (bytesAt_frame)
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`,
the scratch buffer `S` and the rounds `R`. -/
structure APre (s₀ : State) (St D S : Addr) (L R : Nat) : Prop where
  r3 : s₀.gpr .r3 = St
  r6 : s₀.gpr .r6 = D
  r7 : (s₀.gpr .r7).toNat = L
  r8 : s₀.gpr .r8 = S
  r4 : (s₀.gpr .r4).toNat = R
  rd : s₀.rd = [⟨D, L⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 128⟩]
  st_d : (⟨St, 304⟩ : Region).Disjoint ⟨D, L⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 128⟩
  d_s : (⟨D, L⟩ : Region).Disjoint ⟨S, 128⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wD : D.toNat + L ≤ 2 ^ 64
  wS : S.toNat + 128 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem APre.of {s₀ : State} (h : absorbPPC64LE.pre s₀) :
    APre s₀ (s₀.gpr .r3) (s₀.gpr .r6) (s₀.gpr .r8) (s₀.gpr .r7).toNat (s₀.gpr .r4).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

section
variable {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R)
include hp

theorem APre.lt : L < 2 ^ 64 := by rw [← hp.r7]; exact BitVec.isLt _

theorem APre.r7' : s₀.gpr .r7 = BitVec.ofNat 64 L := ofNat_toNat_eq hp.r7

theorem APre.r4' : s₀.gpr .r4 = BitVec.ofNat 64 R := ofNat_toNat_eq hp.r4

theorem APre.inSt {d n : Nat} (h : d + n ≤ 304) : InRegions s₀.wr (St + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ h (by have := hp.wSt; omega_arith)⟩

theorem APre.inS {d n : Nat} (h : d + n ≤ 128) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ h (by have := hp.wS; omega_arith)⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact ⟨⟨D, L⟩, by simp, Offset.contains_base _ h (by have := hp.lt; omega_arith)⟩

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the permissions of `s₀`. -/
theorem APre.uargs {s : State} {Dd : Addr} {n : Nat} (h3 : s.gpr .r3 = St)
    (h4 : s.gpr .r4 = s₀.gpr .r4) (h5 : s.gpr .r5 = St + BitVec.ofNat 64 272) (h6 : s.gpr .r6 = Dd)
    (h7 : s.gpr .r7 = BitVec.ofNat 64 n) (h8 : s.gpr .r8 = S)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 16 * n < 2 ^ 64)
    (hdc : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 272, 16⟩)
    (hds : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨S, 64⟩) (hwrap : Dd.toNat + 16 * n ≤ 2 ^ 64)
    (hcov : ∃ r' ∈ ([⟨D, L⟩, ⟨St, 304⟩, ⟨S, 128⟩] : List Region), ∃ off, Dd = r'.base + BitVec.ofNat 64 off ∧
      off + 16 * n ≤ r'.len) :
    UArgs s St (St + BitVec.ofNat 64 272) Dd S R n := by
  have hw := hp.wSt
  obtain c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  exact
  { r3 := h3, r5 := h5, r6 := h6, r7 := h7, r8 := h8, rounds := hp.rounds, hn := hn
    r4 := by rw [h4]; exact hp.r4'
    wc := Offset.base_disjoint St (by decide) (by omega_arith)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    dc := hdc, ds := hds
    cs := (hp.st_s.sub_left c272).sub_right (Region.sub_prefix (by decide))
    wrapC := by rw [toNat_add_lt St hw (by decide)]; omega_arith
    wrapD := hwrap
    wrapS := by have := hp.wS; omega_arith
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact hcov
      · exact ⟨⟨St, 304⟩, by simp, 272, rfl, by simp⟩
      · exact ⟨⟨S, 128⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 272, rfl, by simp⟩
      · exact ⟨⟨S, 128⟩, by simp, 0, by simp, by simp⟩ }

end

/-! ## Up to the first call -/

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) (St D S : Addr) (c L : Nat) : Mem :=
  writeBytes (absMem s₀ S) (St + BitVec.ofNat 64 (288 + held c))
    (Spec.Aes.bytesAt (absMem s₀ S) D (fOf c L))

/-- What the code before the first call leaves. -/
structure AMid₁ (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 64 272) (St + BitVec.ofNat 64 288) S R (b1Of (s₀.gpr .r5).toNat L)
  r14 : s.gpr .r14 = St
  r15 : s.gpr .r15 = s₀.gpr .r4
  r16 : s.gpr .r16 = D + BitVec.ofNat 64 (fOf (s₀.gpr .r5).toNat L)
  r17 : s.gpr .r17 = BitVec.ofNat 64 (leftOf (s₀.gpr .r5).toNat L)
  r19 : s.gpr .r19 = S
  other : ∀ r ∈ preserved, r ≠ .r14 → r ≠ .r15 → r ≠ .r16 → r ≠ .r17 → r ≠ .r19 → s.gpr r = s₀.gpr r
  mem : s.mem = m4 s₀ St D S (s₀.gpr .r5).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R) :
    WP isa absorbPre s₀ (AMid₁ s₀ St D S L R) := by
  generalize hc : (s₀.gpr .r5).toNat = c
  obtain hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  obtain hdx : s₀.gpr .r5 = BitVec.ofNat 64 c := ofNat_toNat_eq hc
  have hL := hp.lt
  have hw := hp.wSt
  have ⟨hfL, hfh⟩ := f_le c L
  obtain hh := held_le c
  refine WP.seq (WP.mono (save_wp s₀ hp.r8 fun d _ h => hp.inS (by omega_arith)) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (held_wp hcl (by
    rw [h₁.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hdx]))
    fun s₂ ⟨x9₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (fill_wp (St := St) (D := D) hL x9₂
    (by rw [g₂ _ (by decide) (by decide), h₁.r17, hp.r7'])
    (by rw [g₂ _ (by decide) (by decide), h₁.r14, hp.r3]) (by rw [g₂ _ (by decide) (by decide), h₁.r16, hp.r6]))
    fun s₃ ⟨x12₃, x8₃, x10₃, x11₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  obtain dCp : Region.Sub ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩ ⟨St, 304⟩ :=
    Offset.sub_base St (by omega_arith)
  refine WP.seq (WP.mono (copy_ok s₃ (P := D) (C := St + BitVec.ofNat 64 (288 + held c)) (L := fOf c L)
    (by omega_arith) x11₃ x10₃ x12₃
    (fun i hi => by rw [rd₃, wr₃, rd₂, wr₂, h₁.rd, h₁.wr]; exact hp.inD (by omega_arith))
    (fun i hi => by rw [wr₃, wr₂, h₁.wr, Offset.add_add]; exact hp.inSt (by omega_arith))
    ((hp.st_d.sub_left dCp).symm.sub_left (Region.sub_prefix hfL))) fun s₄ h₄ => ?_)
  -- The registers `chain1` reads, unchanged since `save`.
  have g (r : Reg) (a : r ≠ .r8) (b : r ≠ .r9) (c : r ≠ .r10) (d : r ≠ .r11) (e : r ≠ .r12) :
      s₄.gpr r = s₁.gpr r := by
    rw [h₄.other r b c d e, g₃ r a c d e, g₂ r b c]
  refine WP.mono (chain1_wp (St := St) (S := S) hfL hL
    (by rw [g .r16 (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r16, hp.r6])
    (by rw [h₄.other _ (by decide) (by decide) (by decide) (by decide), x8₃])
    (by rw [g .r17 (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r17, hp.r7'])
    (by rw [g .r14 (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r14, hp.r3])
    (by rw [g .r19 (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r19]))
    fun s₅ h₅ => ?_
  obtain ⟨x16₅, x17₅, x7₅, x3₅, x4₅, x5₅, x6₅, x8₅, sv₅, m₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (hr : r ∈ preserved) (a : r ≠ .r16) (b : r ≠ .r17) : s₅.gpr r = s₁.gpr r := by
    obtain ⟨-, -, -, -, -, -, n8, n9, n10, n11, n12⟩ := preserved_ne r hr
    rw [sv₅ r hr a b, g r n8 n9 n10 n11 n12]
  obtain hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃, rd₂, h₁.rd]
  obtain hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃, wr₂, h₁.wr]
  obtain hb1 : 16 * b1Of c L ≤ 16 := by unfold b1Of; split <;> omega_arith
  obtain c288 : Region.Sub ⟨St + BitVec.ofNat 64 288, 16 * b1Of c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_arith)
  obtain m₀ : s₅.mem = m4 s₀ St D S c L := by rw [m₅, h₄.mem, m₃, m₂, h₁.mem, m4]
  subst hc
  refine ⟨hp.uargs x3₅
      (by rw [x4₅, g .r15 (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r15]) x5₅ x6₅
      (by rw [x7₅, b1Of, leftOf]) x8₅ hrd hwr (by omega_arith)
      (Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith))
      ((hp.st_s.sub_left c288).sub_right (Region.sub_prefix (by decide)))
      (by rw [toNat_add_lt St hw (by decide)]; omega_arith)
      ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega_arith⟩,
    by rw [k .r14 (by decide) (by decide) (by decide), h₁.r14, hp.r3],
    by rw [k .r15 (by decide) (by decide) (by decide), h₁.r15],
    x16₅, by rw [x17₅]; rfl, by rw [k .r19 (by decide) (by decide) (by decide), h₁.r19],
    fun r hr a b c d e => by
      rw [k r hr c d, h₁.other r (preserved_ne r hr).1 a b c d e],
    m₀, hrd, hwr⟩

/-! ## The whole function -/

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega_arith) (by omega_arith)) hc

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 16 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 16 1 = [Spec.Aes.bytesAt m p 16] := by
  simp [Spec.Cmac.blocksAt]

theorem absorb_wp {s₀ : State} (h0 : absorbPPC64LE.pre s₀) :
    WP isa absorb s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧
      absorbPPC64LE.post s₀ s' := by
  obtain hp := APre.of h0
  generalize s₀.gpr .r3 = St at hp
  generalize s₀.gpr .r6 = D at hp
  generalize s₀.gpr .r8 = S at hp
  generalize (s₀.gpr .r7).toNat = L at hp
  generalize (s₀.gpr .r4).toNat = R at hp
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .r5).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have hw := hp.wSt
  have hsw := hp.wS
  have ⟨hfL, hfh⟩ := f_le c L
  obtain hsum := nb_le c L
  obtain hh := held_le c
  refine WP.seq (WP.mono (absorbPre_wp hp) fun s₅ h₅ => ?_)
  obtain ⟨args₅, x14₅, x15₅, x16₅, x17₅, x19₅, o₅, m₅, rd₅, wr₅⟩ := h₅
  rw [hc] at args₅ x16₅ x17₅ m₅
  refine WP.seq (WP.mono (upd_call args₅) fun s₆ h₆ => ?_)
  have k₆ (r : Reg) (hr : r ∈ preserved) : s₆.gpr r = s₅.gpr r := h₆.saved r hr
  refine WP.seq (WP.mono (chain2_wp (x := leftOf c L) (by unfold leftOf; omega_arith)
    (by rw [k₆ .r17 (by decide), x17₅])) fun s₇ h₇ => ?_)
  obtain ⟨x18₇, x7₇, x3₇, x4₇, x5₇, x6₇, x8₇, sv₇, m₇, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at x18₇ x7₇
  have k₇ (r : Reg) (hr : r ∈ preserved) (a : r ≠ .r18) : s₇.gpr r = s₅.gpr r := by
    rw [sv₇ r hr a, k₆ r hr]
  obtain dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L), 16 * nbOf c L⟩ ⟨D, L⟩ := Offset.sub_base D (by omega_arith)
  obtain c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  obtain args₇ := hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf c L)) (n := nbOf c L)
    (by rw [x3₇, k₆ .r14 (by decide), x14₅])
    (by rw [x4₇, k₆ .r15 (by decide), x15₅])
    (by rw [x5₇, k₆ .r14 (by decide), x14₅])
    (by rw [x6₇, k₆ .r16 (by decide), x16₅]) x7₇
    (by rw [x8₇, k₆ .r19 (by decide), x19₅]) (by rw [rd₇, h₆.rd, rd₅])
    (by rw [wr₇, h₆.wr, wr₅]) (by omega_arith) ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : nbOf c L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf c L)).isLt; omega_arith
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega_arith)]; omega_arith)
    ⟨⟨D, L⟩, by simp, fOf c L, rfl, by simp; omega_arith⟩
  refine WP.seq (WP.mono (upd_call args₇) fun s₈ h₈ => ?_)
  have k₈ (r : Reg) (hr : r ∈ preserved) : s₈.gpr r = s₇.gpr r := h₈.saved r hr
  refine WP.seq (WP.mono (rest_wp (s := s₈) (D := D) (a := fOf c L) (x := leftOf c L) (n := nbOf c L)
    (by unfold leftOf; omega_arith)
    (by rw [k₈ .r16 (by decide), k₇ .r16 (by decide) (by decide), x16₅])
    (by rw [k₈ .r18 (by decide), x18₇])
    (by rw [k₈ .r17 (by decide), k₇ .r17 (by decide) (by decide), x17₅])) fun s₉ h₉ => ?_)
  obtain ⟨x16₉, x17₉, x10₉, x11₉, x12₉, sv₉, m₉, rd₉, wr₉⟩ := h₉
  obtain rd₉' : s₉.rd = s₀.rd := by rw [rd₉, h₈.rd, rd₇, h₆.rd, rd₅]
  obtain wr₉' : s₉.wr = s₀.wr := by rw [wr₉, h₈.wr, wr₇, h₆.wr, wr₅]
  obtain dR : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L), restOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega_arith)
  obtain hrr : restOf c L ≤ 16 := by unfold restOf nbOf leftOf; split <;> omega_arith
  obtain sR : Region.Sub ⟨St + BitVec.ofNat 64 288, restOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_arith)
  refine WP.seq (WP.mono (copy_ok s₉ (P := D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L))
    (C := St + BitVec.ofNat 64 288) (L := restOf c L) (by omega_arith) x11₉
    (by rw [x10₉, k₈ .r14 (by decide), k₇ .r14 (by decide) (by decide), x14₅]) x12₉
    (fun i hi => by rw [rd₉', wr₉', Offset.add_add]; exact hp.inD (by omega_arith))
    (fun i hi => by rw [wr₉', Offset.add_add]; exact hp.inSt (by omega_arith))
    ((hp.st_d.sub_left sR).symm.sub_left dR)) fun s₁₀ h₁₀ => ?_)
  obtain x19₁₀ : s₁₀.gpr .r19 = S := by
    rw [h₁₀.other _ (by decide) (by decide) (by decide) (by decide), sv₉ _ (by decide) (by decide) (by decide),
      k₈ .r19 (by decide), k₇ .r19 (by decide) (by decide), x19₅]
  -- The frames.
  obtain hlf : (Spec.Aes.bytesAt (absMem s₀ S) D (fOf c L)).length = fOf c L := Proof.Cmac.bytesAt_length _ _ _
  obtain hlr : (Spec.Aes.bytesAt s₉.mem (D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L)) (restOf c L)).length =
    restOf c L := Proof.Cmac.bytesAt_length _ _ _
  obtain fS : Frame [⟨S + BitVec.ofNat 64 64, 56⟩] s₀.mem (absMem s₀ S) := absMem_frame _ _
  obtain fC1 : Frame [⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩] (absMem s₀ S) s₅.mem := by
    rw [m₅, m4]; exact writeBytes_frame _ _ _ (by rw [hlf]; exact Region.contains_self _ _)
  have f6 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 64⟩] s₅.mem s₆.mem := h₆.frame
  obtain f8 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 64⟩] s₆.mem s₈.mem := by
    rw [← m₇]; exact h₈.frame
  obtain fC2 : Frame [⟨St + BitVec.ofNat 64 288, restOf c L⟩] s₈.mem s₁₀.mem := by
    rw [h₁₀.mem, m₉]
    exact writeBytes_frame _ _ _ (by rw [← m₉, hlr]; exact Region.contains_self _ _)
  let K : List Region := [⟨S + BitVec.ofNat 64 64, 56⟩, ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩,
    ⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 64⟩, ⟨St + BitVec.ofNat 64 288, restOf c L⟩]
  obtain F5 : Frame K s₀.mem s₅.mem := (fS.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  obtain F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  obtain F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  obtain F10 : Frame K s₀.mem s₁₀.mem := F8.trans (fC2.mono (by simp [K]))
  -- The slots, which only the saves write.
  obtain Fp : Frame K.tail (absMem s₀ S) s₁₀.mem :=
    ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
      ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
  obtain sv₁₀ : Spill.Saved S (saveG s₀) saved s₁₀.mem :=
    (Spill.saveMem_saved (by decide) s₀.mem S _).frame Fp fun p hp' r hr => by
      obtain hb := abs_bound p hp'
      obtain sub : Region.Sub ⟨S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 128⟩ := Offset.sub_base S (by omega_arith)
      simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_arith))).symm.sub_left sub
      · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
      · exact Offset.disjoint_base S (by omega_arith) (by omega_arith)
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_arith))).symm.sub_left sub
  rw [restore, show saved.map (fun (r, d) => Instr.load .d r .r19 d) = Spill.restoreCode .r19 saved from rfl]
  refine Spill.restore_ok (b := .r19) (l := saved) (by decide) x19₁₀ (by decide) (by decide)
    (fun p hp' => ?_) sv₁₀ fun s₁₁ r₁₁ => WP.cons exec_mtlr (wp_nil ⟨fun r hr => ?_, ?_, ?_⟩)
  · have := abs_bound p hp'
    rw [h₁₀.rd, h₁₀.wr, rd₉', wr₉']; exact in_wr (hp.inS (by omega_arith))
  · -- The registers, restored from their slots or never written.
    show s₁₁.gpr r = _
    rw [r₁₁.gpr_of (r := r) ?_, saveG_ne (preserved_ne r hr).1]
    by_cases hv : r ∈ saved.map Prod.fst
    · left; exact hv
    · right
      obtain n14 : r ≠ .r14 := fun e => hv (by subst e; decide)
      obtain n15 : r ≠ .r15 := fun e => hv (by subst e; decide)
      obtain n16 : r ≠ .r16 := fun e => hv (by subst e; decide)
      obtain n17 : r ≠ .r17 := fun e => hv (by subst e; decide)
      obtain n18 : r ≠ .r18 := fun e => hv (by subst e; decide)
      obtain n19 : r ≠ .r19 := fun e => hv (by subst e; decide)
      obtain ⟨h0, -, -, -, -, -, -, n9, n10, n11, n12⟩ := preserved_ne r hr
      rw [h₁₀.other r n9 n10 n11 n12, sv₉ r hr n16 n17, k₈ r hr, k₇ r hr n18, o₅ r hr n14 n15 n16 n17 n19,
        saveG_ne h0]
  · show s₁₁.gpr .r0 = _
    rw [r₁₁.gpr (.r0, 64) (by decide)]; exact saveG_r0 s₀
  · intro key msg hr hR hcnt hlen
    rw [hp.r3] at hr
    show Spec.Cmac.Repr s₁₁.mem (s₀.gpr .r3) key (msg ++ Spec.Aes.bytesAt s₀.mem (s₀.gpr .r6) (s₀.gpr .r7).toNat)
    rw [hp.r3, hp.r6, hp.r7, r₁₁.mem]
    rw [hp.r7] at hlen
    obtain hcm : c = msg.length := by rw [← hc, hcnt, toNat_ofNat (by omega_arith)]
    subst hcm
    obtain hRk : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.r4]; exact hR
    obtain hRb : 16 * (R + 1) ≤ 272 := by rcases hp.rounds with h | h | h <;> omega_arith
    obtain hsch := ((Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr).1.2.1
    rw [← hRk] at hsch
    -- The key and the data are in none of the regions written.
    obtain dK : ∀ r ∈ K, (⟨St, 272⟩ : Region).Disjoint r := by
      intro r hr
      simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base S (by decide))
      · exact Offset.base_disjoint St (by omega_arith) (by omega_arith)
      · exact Offset.base_disjoint St (by omega_arith) (by omega_arith)
      · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      · exact Offset.base_disjoint St (by omega_arith) (by omega_arith)
    obtain dDat : ∀ r ∈ K, (⟨D, L⟩ : Region).Disjoint r := by
      intro r hr
      simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hp.d_s.sub_right (Offset.sub_base S (by decide))
      · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_arith))
      · exact hp.st_d.symm.sub_right (Offset.sub_base St (by decide))
      · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
      · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_arith))
    obtain ciph : ∀ m : Mem, Frame K s₀.mem m →
        Spec.Cmac.aesWith R (Spec.Aes.bytesAt m St (16 * (R + 1))) = Spec.Cmac.aes key := fun m hf => by
      rw [bytesAt_frame hf (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega_arith), hsch,
        Spec.Cmac.aes, ← hRk]
    -- The data, wherever it is read.
    obtain dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ L →
        Spec.Aes.bytesAt m (D + BitVec.ofNat 64 a) b =
          ((Spec.Aes.bytesAt s₀.mem D L).drop a).take b := fun m hf a b hab => by
      rw [Proof.Cmac.Stream.bytesAt_offset m D hab, bytesAt_frame hf dDat (by omega_arith)]
    obtain fS' : Frame K s₀.mem (absMem s₀ S) := fS.mono (by simp [K])
    -- The chaining value.
    obtain cv5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 272) 16 := by
      rw [bytesAt_frame fC1 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith))
          (by decide),
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).sub_right (Offset.sub_base S (by decide)))
          (by decide)]
    obtain cv10 : Spec.Aes.bytesAt s₁₀.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₈.mem (St + BitVec.ofNat 64 272) 16 :=
      bytesAt_frame fC2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith))
        (by decide)
    have out6 := h₆.out
    rw [ciph _ F5] at out6
    have out8 := h₈.out
    rw [m₇, ciph _ F6] at out8
    obtain hk : ∀ i < 272, s₁₀.mem (St + BitVec.ofNat 64 i) = s₀.mem (St + BitVec.ofNat 64 i) :=
      fun i hi => frame_at F10 dK (by omega_arith) hi
    obtain hdl : (Spec.Aes.bytesAt s₀.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    -- The bytes held back so far, and the first `f` bytes of data after them.
    obtain hb5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 288) (held msg.length + fOf msg.length L) =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 288) (held msg.length) ++
          (Spec.Aes.bytesAt s₀.mem D L).take (fOf msg.length L) := by
      obtain e := bytesAt_writeBytes (absMem s₀ S) (St + BitVec.ofNat 64 288) (held msg.length)
        (Spec.Aes.bytesAt (absMem s₀ S) D (fOf msg.length L)) (by rw [hlf]; omega_arith)
      rw [hlf] at e
      rw [m₅, m4, ← Offset.add_add, e,
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by omega_arith))).sub_right (Offset.sub_base S (by decide)))
          (by omega_arith)]
      refine congrArg (_ ++ ·) ?_
      have := dat _ fS' 0 (fOf msg.length L) (by omega_arith)
      rwa [BitVec.add_zero, List.drop_zero] at this
    generalize hd : Spec.Aes.bytesAt s₀.mem D L = d at hdl hb5 dat ⊢
    by_cases hx : leftOf msg.length L = 0
    · -- Everything fits in the block held back.
      obtain hfL' : fOf msg.length L = L := by unfold leftOf at hx; omega_arith
      obtain hb : b1Of msg.length L = 0 := by simp [b1Of, hx]
      obtain hn : nbOf msg.length L = 0 := by simp [nbOf, hx]
      obtain hr0 : restOf msg.length L = 0 := by simp [restOf, hn, hx]
      obtain m108 : s₁₀.mem = s₈.mem := by
        rw [h₁₀.mem, m₉, hr0, show Spec.Aes.bytesAt s₈.mem
          (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L)) 0 = [] from rfl, writeBytes_nil]
      refine Proof.Cmac.Stream.repr_fill hr hk (by rw [hdl]; have := (f_le msg.length L).2; omega_arith) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _
        rw [cv10, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
        exact cv5
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _
        obtain sub : Region.Sub ⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ ⟨St, 304⟩ :=
          Offset.sub_base St (by omega_arith)
        obtain dj : ∀ r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 64⟩],
            (⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ : Region).Disjoint r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith)
          · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
        have hb5' := hb5
        rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
        rw [m108, hdl, bytesAt_frame f8 dj (by omega_arith), bytesAt_frame f6 dj (by omega_arith), hb5']
    · -- The block held back is complete, and more blocks may follow.
      obtain hlt : 16 - held msg.length < L := by unfold leftOf fOf at hx; omega_arith
      obtain hf' : fOf msg.length L = 16 - held msg.length := by unfold fOf; omega_arith
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
          dat _ F6 _ _ (by omega_arith), hb5', hdl, hf', hn]
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = _
        obtain e := bytesAt_writeBytes_self s₈.mem (St + BitVec.ofNat 64 288)
          (xs := Spec.Aes.bytesAt s₈.mem (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L))
            (restOf msg.length L)) (by rw [Proof.Cmac.bytesAt_length]; omega_arith)
        rw [Proof.Cmac.bytesAt_length] at e
        obtain hr' : d.length - (16 - held msg.length) - 16 * Proof.Cmac.Stream.nblocks msg.length d.length =
            restOf msg.length L := by
          rw [hdl, ← hn, ← hf']; rfl
        rw [hr', h₁₀.mem, m₉, e, dat _ F8 _ _ (by omega_arith),
          List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega_arith),
          List.drop_drop, hdl, ← hn, hf']

end VG.Proof.CmacAes.Stream.PPC64LE

end

end

/-! ### `CmacAes.Stream.PPC64LE.Init`, which only this module used -/

section

/-!
# Streaming AES-CMAC on PPC64LE: `vg_cmac_aes_init`

The code saves `r14`, `r15`, `r16` and the return address in the scratch
buffer (`Spill.save_ok`), expands the key into the state, derives the
subkeys after the schedule, zeroes the chaining value and restores the
registers (`Spill.restore_ok`): the state then represents the empty message.
The code between the calls is constant time by the taint analysis, and the
calls by their own proofs (`ek_rel`, `sub_rel`), their arguments pinned by
`IMid₁` and `IMid₂`.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.Stream.PPC64LE
open VG.Proof.AesCbc.PPC64LE (taintRegs wp_sp)

/-- The precondition, by name: the state `St`, the key `Kp` of `KL` bytes
and the scratch buffer `S`. -/
structure IPre (s₀ : State) (St Kp S : Addr) (KL : Nat) : Prop where
  r3 : s₀.gpr .r3 = St
  r4 : s₀.gpr .r4 = Kp
  r5 : (s₀.gpr .r5).toNat = KL
  r6 : s₀.gpr .r6 = S
  rd : s₀.rd = [⟨Kp, KL⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 128⟩]
  st_k : (⟨St, 304⟩ : Region).Disjoint ⟨Kp, KL⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 128⟩
  k_s : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 128⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wS : S.toNat + 128 ≤ 2 ^ 64
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32

theorem IPre.of {s₀ : State} (h : initPPC64LE.pre s₀) :
    IPre s₀ (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r6) (s₀.gpr .r5).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

theorem IPre.rounds {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL) :
    KL / 4 + 6 = 10 ∨ KL / 4 + 6 = 12 ∨ KL / 4 + 6 = 14 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

/-- The memory after saving the registers. -/
abbrev initMem (s₀ : State) (S : Addr) : Mem := Spill.saveMem s₀.mem S (saveG s₀) initSaved

theorem init_bound : ∀ p ∈ initSaved, 64 ≤ p.2 ∧ p.2 + 8 ≤ 96 := by decide

/-! ## Before the first call -/

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ : State) (St Kp S : Addr) (KL : Nat) (s : State) : Prop where
  args : EArgs s Kp St KL
  r14 : s.gpr .r14 = St
  r15 : s.gpr .r15 = S
  r16 : s.gpr .r16 = BitVec.ofNat 64 (KL / 4 + 6)
  other : ∀ r ∈ preserved, r ≠ .r14 → r ≠ .r15 → r ≠ .r16 → s.gpr r = s₀.gpr r
  mem : s.mem = initMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initPre_wp {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL) :
    WP isa (.block initPre) s₀ (IMid₁ s₀ St Kp S KL) := by
  have sw := hp.wS
  have inS (d : Nat) (h : d + 8 ≤ 128) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ h (by omega_arith)⟩
  obtain hKL : s₀.gpr .r5 = BitVec.ofNat 64 KL := ofNat_toNat_eq hp.r5
  rw [initPre, show initSaved.map (fun (r, d) => Instr.store .d r .r6 d) = Spill.saveCode .r6 initSaved from rfl]
  refine WP.cons exec_mflr (Spill.save_ok (b := .r6) (l := initSaved) (by decide) (by decide)
    (fun p hp' => ?_) ?_)
  · have := init_bound p hp'
    show InRegions s₀.wr (s₀.gpr .r6 + BitVec.ofNat 64 p.2) 8
    rw [hp.r6]; exact inS _ (by omega_arith)
  generalize ht : ({ (s₀.write .r0 s₀.lr) with
    mem := (Spill.saveMem (s₀.write .r0 s₀.lr).mem ((s₀.write .r0 s₀.lr).gpr .r6) (s₀.write .r0 s₀.lr).gpr
      initSaved) } : State) = t
  have gt (r : Reg) (hr : r ≠ .r0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact saveG_ne hr
  obtain memt : t.mem = initMem s₀ S := by
    obtain e : (s₀.write .r0 s₀.lr).gpr .r6 = S := by rw [← hp.r6]; exact saveG_ne (by decide)
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [e]; rfl
  obtain rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  obtain wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  unfold Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_lsr (by decide) fun s₃ u₃ =>
    wp_addi (by decide) (by decide) fun s₄ u₄ => wp_mr fun s₅ u₅ => wp_mr fun s₆ u₆ =>
    wp_mr fun s₇ u₇ => wp_nil ?_
  obtain rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, rdt]
  obtain wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, wrt]
  obtain r14 : s₇.gpr .r14 = St := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr,
      gt, hp.r3]
  obtain r15 : s₇.gpr .r15 = S := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other,
      gt, hp.r6]
  obtain r16 : s₇.gpr .r16 = BitVec.ofNat 64 (KL / 4 + 6) := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.gpr, u₂.other, u₁.other,
      gt, hKL]
    exact rounds_bv hp.klen
  refine ⟨?_, r14, r15, r16, fun r hr h14 h15 h16 => ?_, ?_, rd₇, wr₇⟩
  · exact
    { r3 := by simp (disch := decide) only [u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, u₂.other,
          u₁.other, gt, hp.r4]
      r4 := by simp (disch := decide) only [u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, u₂.other,
          u₁.other, gt, hKL]
      r5 := by simp (disch := decide) only [u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other,
          u₁.gpr, gt, hp.r3]
      klen := hp.klen
      kw := hp.st_k.symm.sub_right (Region.sub_prefix (by decide))
      reads := by
        rw [rd₇, wr₇, hp.rd, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨Kp, KL⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₇, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩ }
  · obtain ⟨h0, -, h4, h5, -, -, -, -, -, -, -⟩ := preserved_ne r hr
    obtain ⟨-, h3, -⟩ := preserved_ne r hr
    rw [u₇.other _ h5, u₆.other _ h4, u₅.other _ h3, u₄.other _ h16, u₃.other _ h16, u₂.other _ h15,
      u₁.other _ h14, gt _ h0]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, memt]

/-! ## Between the calls -/

/-- What the code between the calls leaves. -/
structure IMid₂ (s₀ : State) (St S : Addr) (KL : Nat) (m : Mem) (s : State) : Prop where
  args : SArgs s St (St + BitVec.ofNat 64 240) S (KL / 4 + 6)
  r14 : s.gpr .r14 = St
  r15 : s.gpr .r15 = S
  keep : ∀ r ∈ preserved, r ≠ .r14 → r ≠ .r15 → r ≠ .r16 → s.gpr r = s₀.gpr r
  mem : s.mem = m
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initMid_wp {s₀ s : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL)
    (h14 : s.gpr .r14 = St) (h15 : s.gpr .r15 = S) (h16 : s.gpr .r16 = BitVec.ofNat 64 (KL / 4 + 6))
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hk : ∀ r ∈ preserved, r ≠ .r14 → r ≠ .r15 → r ≠ .r16 → s.gpr r = s₀.gpr r) :
    WP isa (.block initMid) s (IMid₂ s₀ St S KL s.mem) := by
  have hw := hp.wSt
  obtain kSt : Region.Sub ⟨St + BitVec.ofNat 64 240, 32⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  unfold initMid Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_addi (by decide) (by decide) fun s₃ u₃ =>
    wp_mr fun s₄ u₄ => wp_nil ?_
  obtain rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, hrd]
  obtain wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hwr]
  refine ⟨?_, by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h14],
    by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h15],
    fun r hr a b c => ?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], rd₄, wr₄⟩
  · exact
    { r3 := by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.gpr, h14]
      r4 := by simp (disch := decide) only [u₄.other, u₃.other, u₂.gpr, u₁.other, h16]
      r5 := by simp (disch := decide) only [u₄.other, u₃.gpr, u₂.other, u₁.other, h14]
      r6 := by simp (disch := decide) only [u₄.gpr, u₃.other, u₂.other, u₁.other, h15]
      rounds := hp.rounds
      wk := Offset.base_disjoint St (by decide) (by omega_arith)
      ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      ks := (hp.st_s.sub_left kSt).sub_right (Region.sub_prefix (by decide))
      wrapK := by rw [toNat_add_lt St hw (by decide)]; omega_arith
      wrapS := by have := hp.wS; omega_arith
      reads := by
        rw [rd₄, wr₄, hp.rd, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨St, 304⟩, by simp, 240, rfl, by simp⟩
        · exact ⟨⟨S, 128⟩, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₄, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨St, 304⟩, by simp, 240, rfl, by simp⟩
        · exact ⟨⟨S, 128⟩, by simp, 0, by simp, by simp⟩ }
  · obtain ⟨-, h3, h4, h5, h6, -⟩ := preserved_ne r hr
    rw [u₄.other _ h6, u₃.other _ h5, u₂.other _ h4, u₁.other _ h3, hk r hr a b c]

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initPPC64LE.pre s₀) :
    WP isa init s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧
      initPPC64LE.post s₀ s' := by
  obtain hp := IPre.of h0
  generalize s₀.gpr .r3 = St at hp
  generalize s₀.gpr .r4 = Kp at hp
  generalize s₀.gpr .r6 = S at hp
  generalize (s₀.gpr .r5).toNat = KL at hp
  have hw := hp.wSt
  have hsw := hp.wS
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ek_call h₁.args) fun s₂ h₂ => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s₁.gpr r := h₂.saved r hr
  refine WP.seq (WP.mono (initMid_wp hp (by rw [g₂ _ (by decide), h₁.r14])
    (by rw [g₂ _ (by decide), h₁.r15]) (by rw [g₂ _ (by decide), h₁.r16]) (by rw [h₂.rd, h₁.rd])
    (by rw [h₂.wr, h₁.wr]) (fun r hr a b c => by rw [g₂ r hr, h₁.other r hr a b c])) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (sub_call h₃.args) fun s₄ h₄ => ?_)
  have g₄ (r : Reg) (hr : r ∈ preserved) : s₄.gpr r = s₃.gpr r := h₄.saved r hr
  have inS (d : Nat) (hd : d + 8 ≤ 128) : InRegions s₄.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [h₄.wr, h₃.wr, hp.wr]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  have inSt (d : Nat) (hd : d + 8 ≤ 304) : InRegions s₄.wr (St + BitVec.ofNat 64 d) 8 := by
    rw [h₄.wr, h₃.wr, hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  obtain r14₄ : s₄.gpr .r14 = St := by rw [g₄ _ (by decide), h₃.r14]
  obtain r15₄ : s₄.gpr .r15 = S := by rw [g₄ _ (by decide), h₃.r15]
  rw [initPost, show initSaved.map (fun (r, d) => Instr.load .d r .r15 d) = Spill.restoreCode .r15 initSaved
    from rfl, List.append_assoc]
  refine wp_li (by decide) fun s₅ u₅ => ?_
  refine wp_std (a := St + BitVec.ofNat 64 272) (by decide) (by decide) (by rw [u₅.other _ (by decide), r14₄])
    (by rw [u₅.wr]; exact inSt 272 (by decide)) fun s₆ u₆ => ?_
  refine wp_std (a := St + BitVec.ofNat 64 280) (by decide) (by decide)
    (by rw [u₆.gpr, u₅.other _ (by decide), r14₄]) (by rw [u₆.wr, u₅.wr]; exact inSt 280 (by decide))
    fun s₇ u₇ => ?_
  -- The memory, step by step.
  obtain m₇ : s₇.mem = Proof.Cmac.zero2 s₄.mem (St + BitVec.ofNat 64 272) := by
    rw [u₇.mem, u₆.gpr, u₆.mem, u₅.gpr, u₅.mem, Proof.Cmac.zero2, Offset.add_add]; rfl
  obtain fz : Frame [⟨St + BitVec.ofNat 64 272, 16⟩] s₄.mem s₇.mem := by
    rw [m₇]; exact Proof.Cmac.frame_store2 _ _ _
  have f₂ : Frame [⟨St, 240⟩] s₁.mem s₂.mem := h₂.frame
  have f₄ : Frame [⟨St + BitVec.ofNat 64 240, 32⟩, ⟨S, 64⟩] s₃.mem s₄.mem := h₄.frame
  have m₃ : s₃.mem = s₂.mem := h₃.mem
  -- The saved registers.
  have dSv (r : Region) (hr : r ∈ [⟨St, 240⟩, ⟨St + BitVec.ofNat 64 240, 32⟩,
      ⟨S, 64⟩, ⟨St + BitVec.ofNat 64 272, 16⟩]) (d : Nat) (hd : 64 ≤ d) (hd' : d + 8 ≤ 128) :
      (⟨S + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    obtain sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 128⟩ := Offset.sub_base S hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base S (by omega_arith) (by omega_arith)
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
  have dSv' (p : Reg × Nat) (hp' : p ∈ initSaved) (r : Region) (hr : r ∈ [⟨St, 240⟩,
      ⟨St + BitVec.ofNat 64 240, 32⟩, ⟨S, 64⟩, ⟨St + BitVec.ofNat 64 272, 16⟩]) :
      (⟨S + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint r :=
    dSv r hr p.2 (init_bound p hp').1 (by have := init_bound p hp'; omega_arith)
  obtain sv₁ : Spill.Saved S (saveG s₀) initSaved s₁.mem := by
    rw [h₁.mem]; exact Spill.saveMem_saved (by decide) s₀.mem S _
  obtain sv₂ := sv₁.frame f₂ fun p hp' r hr => dSv' p hp' r (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  rw [← m₃] at sv₂
  obtain sv₄ := sv₂.frame f₄ fun p hp' r hr => dSv' p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  obtain sv₇ := sv₄.frame fz fun p hp' r hr => dSv' p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; subst hr; simp)
  obtain r15₇ : s₇.gpr .r15 = S := by rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), r15₄]
  refine Spill.restore_ok (b := .r15) (l := initSaved) (by decide) r15₇ (by decide) (by decide)
    (fun p hp' => ?_) sv₇ fun s₈ r₈ => WP.cons exec_mtlr (wp_nil ⟨fun r hr => ?_, ?_, ?_⟩)
  · have := init_bound p hp'
    rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr]; exact in_wr (inS _ (by omega_arith))
  · show s₈.gpr r = _
    rw [r₈.gpr_of (r := r) ?_, saveG_ne (preserved_ne r hr).1]
    by_cases hv : r = .r14 ∨ r = .r15 ∨ r = .r16
    · left; rcases hv with rfl | rfl | rfl <;> decide
    · right
      obtain ⟨h0, -, -, -, -, -, -, h9, -⟩ := preserved_ne r hr
      rw [u₇.gpr, u₆.gpr, u₅.other _ h9, g₄ r hr, h₃.keep r hr (fun e => hv (.inl e))
        (fun e => hv (.inr (.inl e))) (fun e => hv (.inr (.inr e))), saveG_ne h0]
  · show s₈.gpr .r0 = _
    rw [r₈.gpr (.r0, 88) (by decide)]; exact saveG_r0 s₀
  · show Spec.Cmac.Repr s₈.mem (s₀.gpr .r3) (Spec.Aes.bytesAt s₀.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat) []
    rw [hp.r3, hp.r4, hp.r5, Proof.Cmac.Stream.repr_iff, r₈.mem]
    obtain f₁ : Frame [⟨S + BitVec.ofNat 64 64, 32⟩] s₀.mem s₁.mem := by
      rw [h₁.mem]
      have := Spill.saveMem_frame (l := initSaved) (lo := 64) (n := 32) (fun p hp' => init_bound p hp')
        (by omega_arith) s₀.mem S (saveG s₀)
      exact this
    obtain hkey : Spec.Aes.bytesAt s₁.mem Kp KL = Spec.Aes.bytesAt s₀.mem Kp KL :=
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.k_s.sub_right (Offset.sub_base S (by decide))) (by have := hp.wK; omega_arith)
    obtain hlen : (Spec.Aes.bytesAt s₀.mem Kp KL).length = KL := Proof.Cmac.bytesAt_length _ _ _
    have dSt (d n : Nat) (hd : d + n ≤ 272) (r : Region) (hr : r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩]) :
        (⟨St + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith)
    obtain hRb : 16 * (Spec.Aes.rounds (KL / 4) + 1) ≤ 240 := by
      have := hp.klen; simp only [Spec.Aes.rounds]; omega_arith
    -- The schedule, from the first call on.
    obtain sch : ∀ {d n : Nat}, d + n ≤ 240 → Spec.Aes.bytesAt s₇.mem (St + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₂.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
      rw [Proof.Cmac.bytesAt_frame fz (dSt d n (by omega_arith)) (by omega_arith),
        Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith)
          · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_arith))).sub_right (Region.sub_prefix (by decide)))
          (by omega_arith), m₃]
    obtain hsch : Spec.Aes.bytesAt s₂.mem St (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem Kp KL) := by rw [h₂.out, hkey]
    refine ⟨⟨by rw [hlen]; exact hp.klen, ?_, ?_⟩, ?_, by simp [Proof.Cmac.Stream.held_zero, Spec.Aes.bytesAt]⟩
    · rw [hlen]
      have := sch (d := 0) (n := 16 * (Spec.Aes.rounds (KL / 4) + 1)) (by omega_arith)
      rw [BitVec.add_zero] at this; rw [this, hsch]
    · have e : Spec.Aes.bytesAt s₇.mem (St + 240) 32 = Spec.Aes.bytesAt s₄.mem (St + 240) 32 :=
        Proof.Cmac.bytesAt_frame fz (dSt 240 32 (by decide)) (by decide)
      rw [e]
      refine h₄.out.trans ?_
      rw [m₃, show KL / 4 + 6 = Spec.Aes.rounds (KL / 4) from rfl, hsch]
      simp only [Spec.Cmac.aes, hlen]
    · rw [m₇]; exact (Proof.Cmac.zero2_bytes _ _).trans rfl

/-! ## Constant time -/

/-- What the call of `vg_aes_expand_key_scratch` leaves, for `initMid`. -/
structure IAfter (s₀ : State) (St S : Addr) (KL : Nat) (s : State) : Prop where
  r14 : s.gpr .r14 = St
  r15 : s.gpr .r15 = S
  r16 : s.gpr .r16 = BitVec.ofNat 64 (KL / 4 + 6)
  keep : ∀ r ∈ preserved, r ≠ .r14 → r ≠ .r15 → r ≠ .r16 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ek_after {s₀ s : State} {St Kp S : Addr} {KL : Nat} (h : IMid₁ s₀ St Kp S KL s) :
    WP isa ekCall s (IAfter s₀ St S KL) :=
  WP.mono (ek_call h.args) fun _ h₂ =>
    ⟨by rw [h₂.saved _ (by decide), h.r14], by rw [h₂.saved _ (by decide), h.r15],
      by rw [h₂.saved _ (by decide), h.r16], fun r hr a b c => by rw [h₂.saved r hr, h.other r hr a b c],
      by rw [h₂.rd, h.rd], by rw [h₂.wr, h.wr]⟩

theorem init_rel {s₀ s₀' : State} (h0 : initPPC64LE.pre s₀) (h0' : initPPC64LE.pre s₀')
    (hq : initPPC64LE.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') init fun _ _ => True := by
  obtain ⟨q3, q4, q5, q6, qsp⟩ := hq
  obtain hp := IPre.of h0
  obtain hp' : IPre s₀' (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r6) (s₀.gpr .r5).toNat := by
    rw [q3, q4, q5, q6]; exact IPre.of h0'
  generalize s₀.gpr .r3 = St at hp hp'
  generalize s₀.gpr .r4 = Kp at hp hp'
  generalize s₀.gpr .r6 = S at hp hp'
  generalize (s₀.gpr .r5).toNat = KL at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6]) (.block initPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r14, .r15, .r16]) (.block initMid) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.r14, .r15]) (.block initPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.r3, .r4, .r5, .r6]
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
      (IAfter s₀' St S KL b ∧ b.sp = s₀'.sp)) [.r14, .r15, .r16]
    (fun a b h => by
      refine ⟨by rw [h.1.2, h.2.2, qsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.1.r14, h.2.1.r14]
      · rw [h.1.1.r15, h.2.1.r15]
      · rw [h.1.1.r16, h.2.1.r16]) hB).wp
    (F₁ := fun (s : State) => (∃ m, IMid₂ s₀ St S KL m s) ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => (∃ m, IMid₂ s₀' St S KL m s) ∧ s.sp = s₀'.sp)
    fun a b h =>
      ⟨WP.mono (wp_sp (initMid_wp hp h.1.1.r14 h.1.1.r15 h.1.1.r16 h.1.1.rd h.1.1.wr h.1.1.keep))
          fun _ h' => ⟨⟨_, h'.1⟩, by rw [h'.2, h.1.2]⟩,
       WP.mono (wp_sp (initMid_wp hp' h.2.1.r14 h.2.1.r15 h.2.1.r16 h.2.1.rd h.2.1.wr h.2.1.keep))
          fun _ h' => ⟨⟨_, h'.1⟩, by rw [h'.2, h.2.2]⟩⟩
  obtain sk := (sub_rel (P := fun a b => ((∃ m, IMid₂ s₀ St S KL m a) ∧ a.sp = s₀.sp) ∧
      ((∃ m, IMid₂ s₀' St S KL m b) ∧ b.sp = s₀'.sp))
    fun a b ⟨⟨⟨_, h₁⟩, sp₁⟩, ⟨⟨_, h₂⟩, sp₂⟩⟩ => ⟨h₁.args, h₂.args, by rw [sp₁, sp₂, qsp]⟩).wp
    (F₁ := fun (s : State) => s.gpr .r14 = St ∧ s.gpr .r15 = S ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .r14 = St ∧ s.gpr .r15 = S ∧ s.sp = s₀'.sp)
    fun a b ⟨⟨⟨_, h₁⟩, sp₁⟩, ⟨⟨_, h₂⟩, sp₂⟩⟩ =>
      ⟨WP.mono (sub_call h₁.args) fun _ h => ⟨by rw [h.saved _ (by decide), h₁.r14],
          by rw [h.saved _ (by decide), h₁.r15], by rw [h.sp, sp₁]⟩,
        WP.mono (sub_call h₂.args) fun _ h => ⟨by rw [h.saved _ (by decide), h₂.r14],
          by rw [h.saved _ (by decide), h₂.r15], by rw [h.sp, sp₂]⟩⟩
  have p := taintRegs
    (P := fun a b => (a.gpr .r14 = St ∧ a.gpr .r15 = S ∧ a.sp = s₀.sp) ∧
      b.gpr .r14 = St ∧ b.gpr .r15 = S ∧ b.sp = s₀'.sp) [.r14, .r15]
    (fun a b h => by
      refine ⟨by rw [h.1.2.2, h.2.2.2, qsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2.1, h.2.2.1]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((sk.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem init_ct : ConstantTime isa initPPC64LE.pre initPPC64LE.pub init :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (init_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.PPC64LE

end

end

/-!
# Streaming AES-CMAC on PPC64LE: constant time of `absorb`, and `Verified`

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
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.Stream.PPC64LE
open VG.Proof.AesCbc.PPC64LE (taintRegs wp_sp)

/-! ## Constant time of `absorb` -/

/-- What the first call leaves, for `chain2`. -/
structure AAfter₁ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  r14 : s.gpr .r14 = St
  r15 : s.gpr .r15 = s₀.gpr .r4
  r16 : s.gpr .r16 = D + BitVec.ofNat 64 (fOf (s₀.gpr .r5).toNat L)
  r17 : s.gpr .r17 = BitVec.ofNat 64 (leftOf (s₀.gpr .r5).toNat L)
  r19 : s.gpr .r19 = S
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem call1_after {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : AMid₁ s₀ St D S L R s) (hsp : s.sp = s₀.sp) : WP isa updCall s (AAfter₁ s₀ St D S L) :=
  WP.mono (upd_call h.args) fun _ h₆ =>
    ⟨by rw [h₆.saved .r14 (by decide), h.r14], by rw [h₆.saved .r15 (by decide), h.r15],
      by rw [h₆.saved .r16 (by decide), h.r16], by rw [h₆.saved .r17 (by decide), h.r17],
      by rw [h₆.saved .r19 (by decide), h.r19], by rw [h₆.sp, hsp], by rw [h₆.rd, h.rd],
      by rw [h₆.wr, h.wr]⟩

/-- What `chain2` leaves, for the second call. -/
structure AMid₂ (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 64 272) (D + BitVec.ofNat 64 (fOf (s₀.gpr .r5).toNat L)) S R
    (nbOf (s₀.gpr .r5).toNat L)
  r14 : s.gpr .r14 = St
  r18 : s.gpr .r18 = BitVec.ofNat 64 (16 * nbOf (s₀.gpr .r5).toNat L)
  r16 : s.gpr .r16 = D + BitVec.ofNat 64 (fOf (s₀.gpr .r5).toNat L)
  r17 : s.gpr .r17 = BitVec.ofNat 64 (leftOf (s₀.gpr .r5).toNat L)
  r19 : s.gpr .r19 = S
  sp : s.sp = s₀.sp

theorem chain2_mid {s₀ s : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R)
    (h : AAfter₁ s₀ St D S L s) : WP isa chain2 s (AMid₂ s₀ St D S L R) := by
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .r5).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have ⟨hfL, _⟩ := f_le c L
  have hsum := nb_le c L
  obtain ⟨x14₆, x15₆, x16₆, x17₆, x19₆, sp₆, rd₆, wr₆⟩ := h
  rw [hc] at x16₆ x17₆
  refine WP.mono (wp_sp (chain2_wp (x := leftOf c L) (by unfold leftOf; omega_arith) x17₆)) fun s₇ ⟨h₇, sp₇⟩ => ?_
  obtain ⟨x18₇, x7₇, x3₇, x4₇, x5₇, x6₇, x8₇, sv₇, -, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at x18₇ x7₇
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  subst hc
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf (s₀.gpr .r5).toNat L), 16 * nbOf (s₀.gpr .r5).toNat L⟩
      ⟨D, L⟩ := Offset.sub_base D (by omega_arith)
  refine ⟨hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf (s₀.gpr .r5).toNat L))
    (n := nbOf (s₀.gpr .r5).toNat L)
    (by rw [x3₇, x14₆]) (by rw [x4₇, x15₆]) (by rw [x5₇, x14₆]) (by rw [x6₇, x16₆]) x7₇
    (by rw [x8₇, x19₆]) (by rw [rd₇, rd₆]) (by rw [wr₇, wr₆]) (by omega_arith)
    ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : nbOf (s₀.gpr .r5).toNat L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf (s₀.gpr .r5).toNat L)).isLt; omega_arith
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega_arith)]; omega_arith)
    ⟨⟨D, L⟩, by simp, fOf (s₀.gpr .r5).toNat L, rfl, by simp; omega_arith⟩,
    by rw [sv₇ .r14 (by decide) (by decide), x14₆], x18₇,
    by rw [sv₇ .r16 (by decide) (by decide), x16₆],
    by rw [sv₇ .r17 (by decide) (by decide), x17₆],
    by rw [sv₇ .r19 (by decide) (by decide), x19₆], by rw [sp₇, sp₆]⟩

/-- What the second call leaves, for `absorbPost`. -/
structure AAfter₂ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  r14 : s.gpr .r14 = St
  r18 : s.gpr .r18 = BitVec.ofNat 64 (16 * nbOf (s₀.gpr .r5).toNat L)
  r16 : s.gpr .r16 = D + BitVec.ofNat 64 (fOf (s₀.gpr .r5).toNat L)
  r17 : s.gpr .r17 = BitVec.ofNat 64 (leftOf (s₀.gpr .r5).toNat L)
  r19 : s.gpr .r19 = S
  sp : s.sp = s₀.sp

theorem call2_after {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : AMid₂ s₀ St D S L R s) : WP isa updCall s (AAfter₂ s₀ St D S L) :=
  WP.mono (upd_call h.args) fun _ h₈ =>
    ⟨by rw [h₈.saved .r14 (by decide), h.r14], by rw [h₈.saved .r18 (by decide), h.r18],
      by rw [h₈.saved .r16 (by decide), h.r16], by rw [h₈.saved .r17 (by decide), h.r17],
      by rw [h₈.saved .r19 (by decide), h.r19], by rw [h₈.sp, h.sp]⟩

theorem absorb_rel {s₀ s₀' : State} (h0 : absorbPPC64LE.pre s₀) (h0' : absorbPPC64LE.pre s₀')
    (hq : absorbPPC64LE.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') absorb fun _ _ => True := by
  obtain ⟨q3, q4, q5, q6, q7, q8, qsp⟩ := hq
  have hp := APre.of h0
  have hp' : APre s₀' (s₀.gpr .r3) (s₀.gpr .r6) (s₀.gpr .r8) (s₀.gpr .r7).toNat (s₀.gpr .r4).toNat := by
    rw [q3, q4, q6, q7, q8]; exact APre.of h0'
  generalize s₀.gpr .r3 = St at hp hp'
  generalize s₀.gpr .r6 = D at hp hp'
  generalize s₀.gpr .r8 = S at hp hp'
  generalize (s₀.gpr .r7).toNat = L at hp hp'
  generalize (s₀.gpr .r4).toNat = R at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) absorbPre h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r14, .r15, .r16, .r17, .r19]) chain2 h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.r14, .r16, .r17, .r18, .r19]) absorbPost h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.r3, .r4, .r5, .r6, .r7, .r8]
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
    [.r14, .r15, .r16, .r17, .r19]
    (fun a b h => by
      refine ⟨by rw [h.1.sp, h.2.sp, qsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.r14, h.2.r14]
      · rw [h.1.r15, h.2.r15, q4]
      · rw [h.1.r16, h.2.r16, q5]
      · rw [h.1.r17, h.2.r17, q5]
      · rw [h.1.r19, h.2.r19]) hB).wp
    (F₁ := AMid₂ s₀ St D S L R) (F₂ := AMid₂ s₀' St D S L R) fun a b h => ⟨chain2_mid hp h.1, chain2_mid hp' h.2⟩
  have c₂ := (upd_rel (P := fun a b => AMid₂ s₀ St D S L R a ∧ AMid₂ s₀' St D S L R b)
    fun a b h => ⟨h.1.args, by rw [q5]; exact h.2.args, by rw [h.1.sp, h.2.sp, qsp]⟩).wp
    (F₁ := AAfter₂ s₀ St D S L) (F₂ := AAfter₂ s₀' St D S L) fun a b h =>
      ⟨call2_after h.1, call2_after h.2⟩
  have p := taintRegs (P := fun a b => AAfter₂ s₀ St D S L a ∧ AAfter₂ s₀' St D S L b)
    [.r14, .r16, .r17, .r18, .r19]
    (fun a b h => by
      refine ⟨by rw [h.1.sp, h.2.sp, qsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.r14, h.2.r14]
      · rw [h.1.r16, h.2.r16, q5]
      · rw [h.1.r17, h.2.r17, q5]
      · rw [h.1.r18, h.2.r18, q5]
      · rw [h.1.r19, h.2.r19]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem absorb_ct : ConstantTime isa absorbPPC64LE.pre absorbPPC64LE.pub absorb :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (absorb_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

theorem init_correct (s : State) (hs : initPPC64LE.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initPPC64LE.post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := init_wp hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem absorb_correct (s : State) (hs : absorbPPC64LE.pre s) :
    ∃ t s', Exec isa absorb s t s' ∧ abiPreserved s s' ∧ absorbPPC64LE.post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := absorb_wp hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem finish_correct (s : State) (hs : finishPPC64LE.pre s) :
    ∃ t s', Exec isa finish s t s' ∧ abiPreserved s s' ∧ finishPPC64LE.post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := finish_wp hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

/-- A state satisfying `vg_cmac_aes_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r5 => 16 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 128⟩]

theorem init_verified : Verified PPC64LE.target init (initScratchContract PPC64LE.abi (n := 16)) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [initScratchContract, initScratchSig, Spec.Cmac.aesInitPre, Spec.Cmac.aesInitPost,
      initPPC64LE, PPC64LE.abi, PPC64LE.argRegs] [initSat] using initSat)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition (with no data). -/
def absorbSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r6 => 0x3000 | .r8 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 128⟩]

theorem absorb_verified : Verified PPC64LE.target absorb (absorbScratchContract PPC64LE.abi (n := 16)) :=
  Verified.of_correct absorb_correct absorb_ct (by
    sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.aesAbsorbPre, Spec.Cmac.aesAbsorbPost,
      absorbPPC64LE, PPC64LE.abi, PPC64LE.argRegs] [absorbSat] using absorbSat)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition. -/
def finishSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r6 => 0x2000 | .r7 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 128⟩]

theorem finish_verified : Verified PPC64LE.target finish (finishScratchContract PPC64LE.abi (n := 16)) :=
  Verified.of_correct finish_correct finish_ct (by
    sig_implies [finishScratchContract, finishScratchSig, Spec.Cmac.aesFinishPre, Spec.Cmac.aesFinishPost,
      finishPPC64LE, PPC64LE.abi, PPC64LE.argRegs] [finishSat] using finishSat)

end VG.Proof.CmacAes.Stream.PPC64LE

end

end

/-!
# Streaming AES-CMAC on PPC64LE, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame of 160 bytes that allocates it
(`Verified.stackScratch`): the frame's 32-byte header and the 128 bytes of
working space. Their code uses no other stack: a call (`bl`) keeps the
return address in the link register, which they save in the working space.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.Stream.PPC64LE

/-- A state satisfying `vg_cmac_aes_init`'s precondition, without the
working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 304⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.aesInitContract PPC64LE.abi 160).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, PPC64LE.abi, PPC64LE.argRegs] [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, without the
working space (and with no data). -/
def absorbFrameSat : State := { absorbSat with wr := [⟨0x1000, 304⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.aesAbsorbContract PPC64LE.abi 160).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, PPC64LE.abi, PPC64LE.argRegs] [absorbFrameSat, absorbSat]
    using absorbFrameSat

/-- A state satisfying `vg_cmac_aes_finish`'s precondition, without the
working space. -/
def finishFrameSat : State := { finishSat with wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.aesFinishContract PPC64LE.abi 160).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, PPC64LE.abi, PPC64LE.argRegs] [finishFrameSat, finishSat]
    using finishFrameSat

theorem init_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 160 .r6 init)
      (Spec.Cmac.aesInitContract PPC64LE.abi 160) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64)
    (n := 16) (pre := Spec.Cmac.aesInitPre PPC64LE.abi.ptrBits)
    (post := Spec.Cmac.aesInitPost PPC64LE.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 160) init_verified (by decide) (by decide) (initPre_local _) (initPost_local _)
    (fun vs m m₁ m₂ r hl _ hb h => initPostOut_local _ vs m m₁ m₂ r hl hb h)
    initFrameSat_pre

theorem absorb_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 160 .r8 absorb)
      (Spec.Cmac.aesAbsorbContract PPC64LE.abi 160) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64)
    (n := 16) (pre := Spec.Cmac.aesAbsorbPre PPC64LE.abi.ptrBits)
    (post := Spec.Cmac.aesAbsorbPost PPC64LE.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 160) absorb_verified (by decide) (by decide) (absorbPre_local _) (absorbPost_local _)
    (fun vs m m₁ m₂ r hl _ hb h => absorbPostOut_local _ vs m m₁ m₂ r hl hb h)
    absorbFrameSat_pre

theorem finish_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 160 .r7 finish)
      (Spec.Cmac.aesFinishContract PPC64LE.abi 160) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64)
    (n := 16) (pre := Spec.Cmac.aesFinishPre PPC64LE.abi.ptrBits)
    (post := Spec.Cmac.aesFinishPost PPC64LE.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 160) finish_verified (by decide) (by decide) (finishPre_local _) (finishPost_local _)
    (fun vs m m₁ m₂ r hl _ hb h => finishPostOut_local _ vs m m₁ m₂ r hl hb h)
    finishFrameSat_pre

end VG.Proof.CmacAes.Stream.PPC64LE
