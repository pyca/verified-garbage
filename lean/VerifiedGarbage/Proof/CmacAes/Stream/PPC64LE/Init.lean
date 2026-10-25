module

public import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Common
meta import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
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
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 2304⟩]
  st_k : (⟨St, 304⟩ : Region).Disjoint ⟨Kp, KL⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  k_s : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
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

theorem init_bound : ∀ p ∈ initSaved, 2176 ≤ p.2 ∧ p.2 + 8 ≤ 2208 := by decide

/-! ## Before the first call -/

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ : State) (St Kp S : Addr) (KL : Nat) (s : State) : Prop where
  args : EArgs s Kp St S KL
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
  have inS (d : Nat) (h : d + 8 ≤ 2304) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ h (by omega_arith)⟩
  have hKL : s₀.gpr .r5 = BitVec.ofNat 64 KL := ofNat_toNat_eq hp.r5
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
  have memt : t.mem = initMem s₀ S := by
    have e : (s₀.write .r0 s₀.lr).gpr .r6 = S := by rw [← hp.r6]; exact saveG_ne (by decide)
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [e]; rfl
  have rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  have wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  unfold Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_lsr (by decide) fun s₃ u₃ =>
    wp_addi (by decide) (by decide) fun s₄ u₄ => wp_mr fun s₅ u₅ => wp_mr fun s₆ u₆ =>
    wp_mr fun s₇ u₇ => wp_nil ?_
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, rdt]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, wrt]
  have r14 : s₇.gpr .r14 = St := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr,
      gt, hp.r3]
  have r15 : s₇.gpr .r15 = S := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other,
      gt, hp.r6]
  have r16 : s₇.gpr .r16 = BitVec.ofNat 64 (KL / 4 + 6) := by
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
      r6 := by simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other,
          u₁.other, gt, hp.r6]
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
  have kSt : Region.Sub ⟨St + BitVec.ofNat 64 240, 32⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  unfold initMid Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_addi (by decide) (by decide) fun s₃ u₃ =>
    wp_mr fun s₄ u₄ => wp_nil ?_
  have rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, hrd]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hwr]
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
        · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₄, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨St, 304⟩, by simp, 240, rfl, by simp⟩
        · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩ }
  · obtain ⟨-, h3, h4, h5, h6, -⟩ := preserved_ne r hr
    rw [u₄.other _ h6, u₃.other _ h5, u₂.other _ h4, u₁.other _ h3, hk r hr a b c]

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initPPC64LE.pre s₀) :
    WP isa init s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧
      initPPC64LE.post s₀ s' := by
  have hp := IPre.of h0
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
  have inS (d : Nat) (hd : d + 8 ≤ 2304) : InRegions s₄.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [h₄.wr, h₃.wr, hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  have inSt (d : Nat) (hd : d + 8 ≤ 304) : InRegions s₄.wr (St + BitVec.ofNat 64 d) 8 := by
    rw [h₄.wr, h₃.wr, hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  have r14₄ : s₄.gpr .r14 = St := by rw [g₄ _ (by decide), h₃.r14]
  have r15₄ : s₄.gpr .r15 = S := by rw [g₄ _ (by decide), h₃.r15]
  rw [initPost, show initSaved.map (fun (r, d) => Instr.load .d r .r15 d) = Spill.restoreCode .r15 initSaved
    from rfl, List.append_assoc]
  refine wp_li (by decide) fun s₅ u₅ => ?_
  refine wp_std (a := St + BitVec.ofNat 64 272) (by decide) (by decide) (by rw [u₅.other _ (by decide), r14₄])
    (by rw [u₅.wr]; exact inSt 272 (by decide)) fun s₆ u₆ => ?_
  refine wp_std (a := St + BitVec.ofNat 64 280) (by decide) (by decide)
    (by rw [u₆.gpr, u₅.other _ (by decide), r14₄]) (by rw [u₆.wr, u₅.wr]; exact inSt 280 (by decide))
    fun s₇ u₇ => ?_
  -- The memory, step by step.
  have m₇ : s₇.mem = Proof.Cmac.zero2 s₄.mem (St + BitVec.ofNat 64 272) := by
    rw [u₇.mem, u₆.gpr, u₆.mem, u₅.gpr, u₅.mem, Proof.Cmac.zero2, Offset.add_add]; rfl
  have fz : Frame [⟨St + BitVec.ofNat 64 272, 16⟩] s₄.mem s₇.mem := by
    rw [m₇]; exact Proof.Cmac.frame_store2 _ _ _
  have f₂ : Frame [⟨St, 240⟩, ⟨S, 512⟩] s₁.mem s₂.mem := h₂.frame
  have f₄ : Frame [⟨St + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩] s₃.mem s₄.mem := h₄.frame
  have m₃ : s₃.mem = s₂.mem := h₃.mem
  -- The saved registers.
  have dSv (r : Region) (hr : r ∈ [⟨St, 240⟩, ⟨S, 512⟩, ⟨St + BitVec.ofNat 64 240, 32⟩,
      ⟨S, 2176⟩, ⟨St + BitVec.ofNat 64 272, 16⟩]) (d : Nat) (hd : 2176 ≤ d) (hd' : d + 8 ≤ 2304) :
      (⟨S + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    have sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 2304⟩ := Offset.sub_base S hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base S (by omega_arith) (by omega_arith)
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base S (by omega_arith) (by omega_arith)
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
  have dSv' (p : Reg × Nat) (hp' : p ∈ initSaved) (r : Region) (hr : r ∈ [⟨St, 240⟩, ⟨S, 512⟩,
      ⟨St + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩, ⟨St + BitVec.ofNat 64 272, 16⟩]) :
      (⟨S + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint r :=
    dSv r hr p.2 (init_bound p hp').1 (by have := init_bound p hp'; omega_arith)
  have sv₁ : Spill.Saved S (saveG s₀) initSaved s₁.mem := by
    rw [h₁.mem]; exact Spill.saveMem_saved (by decide) s₀.mem S _
  have sv₂ := sv₁.frame f₂ fun p hp' r hr => dSv' p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  rw [← m₃] at sv₂
  have sv₄ := sv₂.frame f₄ fun p hp' r hr => dSv' p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  have sv₇ := sv₄.frame fz fun p hp' r hr => dSv' p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; subst hr; simp)
  have r15₇ : s₇.gpr .r15 = S := by rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), r15₄]
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
    rw [r₈.gpr (.r0, 2200) (by decide)]; exact saveG_r0 s₀
  · show Spec.Cmac.Repr s₈.mem (s₀.gpr .r3) (Spec.Aes.bytesAt s₀.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat) []
    rw [hp.r3, hp.r4, hp.r5, Proof.Cmac.Stream.repr_iff, r₈.mem]
    have f₁ : Frame [⟨S + BitVec.ofNat 64 2176, 32⟩] s₀.mem s₁.mem := by
      rw [h₁.mem]
      have := Spill.saveMem_frame (l := initSaved) (lo := 2176) (n := 32) (fun p hp' => init_bound p hp')
        (by omega_arith) s₀.mem S (saveG s₀)
      exact this
    have hkey : Spec.Aes.bytesAt s₁.mem Kp KL = Spec.Aes.bytesAt s₀.mem Kp KL :=
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.k_s.sub_right (Offset.sub_base S (by decide))) (by have := hp.wK; omega_arith)
    have hlen : (Spec.Aes.bytesAt s₀.mem Kp KL).length = KL := Proof.Cmac.bytesAt_length _ _ _
    have dSt (d n : Nat) (hd : d + n ≤ 272) (r : Region) (hr : r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩]) :
        (⟨St + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith)
    have hRb : 16 * (Spec.Aes.rounds (KL / 4) + 1) ≤ 240 := by
      have := hp.klen; simp only [Spec.Aes.rounds]; omega_arith
    -- The schedule, from the first call on.
    have sch : ∀ {d n : Nat}, d + n ≤ 240 → Spec.Aes.bytesAt s₇.mem (St + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₂.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
      rw [Proof.Cmac.bytesAt_frame fz (dSt d n (by omega_arith)) (by omega_arith),
        Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith)
          · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_arith))).sub_right (Region.sub_prefix (by decide)))
          (by omega_arith), m₃]
    have hsch : Spec.Aes.bytesAt s₂.mem St (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
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
  have hp := IPre.of h0
  have hp' : IPre s₀' (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r6) (s₀.gpr .r5).toNat := by
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
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.r3, .r4, .r5, .r6]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨qsp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := fun (s : State) => IMid₁ s₀ St Kp S KL s ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => IMid₁ s₀' St Kp S KL s ∧ s.sp = s₀'.sp) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨wp_sp (initPre_wp hp), wp_sp (initPre_wp hp')⟩
  have e := (ek_rel (P := fun a b => (IMid₁ s₀ St Kp S KL a ∧ a.sp = s₀.sp) ∧
      (IMid₁ s₀' St Kp S KL b ∧ b.sp = s₀'.sp))
    fun a b h => ⟨h.1.1.args, h.2.1.args, by rw [h.1.2, h.2.2, qsp]⟩).wp
    (F₁ := fun (s : State) => IAfter s₀ St S KL s ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => IAfter s₀' St S KL s ∧ s.sp = s₀'.sp) fun a b h =>
      ⟨WP.mono (wp_sp (ek_after h.1.1)) fun _ h' => ⟨h'.1, by rw [h'.2, h.1.2]⟩,
       WP.mono (wp_sp (ek_after h.2.1)) fun _ h' => ⟨h'.1, by rw [h'.2, h.2.2]⟩⟩
  have m := (taintRegs (P := fun a b => (IAfter s₀ St S KL a ∧ a.sp = s₀.sp) ∧
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
  have sk := (sub_rel (P := fun a b => ((∃ m, IMid₂ s₀ St S KL m a) ∧ a.sp = s₀.sp) ∧
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
