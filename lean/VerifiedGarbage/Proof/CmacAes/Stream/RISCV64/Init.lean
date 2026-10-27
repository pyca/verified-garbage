module

public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common
meta import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Align
meta import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Streaming AES-CMAC on RISC-V: `vg_cmac_aes_init`

As on PPC64LE (`Proof/CmacAes/Stream/PPC64LE/Init.lean`): the code saves
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
  have hKL : s₀.gpr .a2 = BitVec.ofNat 64 KL := ofNat_toNat_eq hp.a2
  rw [initPre, List.append_assoc, WP.block_append_iff]
  refine WP.mono (savePtr2_ok .a3) fun s₁ e => ?_
  subst e
  rw [hp.a3, show initSaved.map (fun (r, d) => Instr.store .d r .t0 d) = Spill.saveCode .t0 initSaved from rfl]
  have t₀ : (s₀.write .t0 (sv2 S)).gpr .t0 = sv2 S := RegUpd.gpr_write_self _ _ _
  have g₀ (r : Reg) (hr : r ≠ .t0) : (s₀.write .t0 (sv2 S)).gpr r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine Spill.save_ok (b := .t0) (l := initSaved) (by rw [t₀]; exact Align.align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · have := init_bound p hp'
    rw [t₀]
    show InRegions s₀.wr _ 8
    rw [hp.wr]
    exact ⟨⟨S, 2304⟩, by simp, sv2_contains S (by omega)⟩
  generalize ht : ({ (s₀.write .t0 (sv2 S)) with
    mem := Spill.saveMem (s₀.write .t0 (sv2 S)).mem ((s₀.write .t0 (sv2 S)).gpr .t0)
      (s₀.write .t0 (sv2 S)).gpr initSaved } : State) = t
  have gt (r : Reg) (hr : r ≠ .t0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact g₀ r hr
  have memt : t.mem = initMem s₀ S := by
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [t₀, RegUpd.mem_write]
  have rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  have wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  unfold Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_srl (by decide) fun s₃ u₃ =>
    wp_addi (imm := 6) (by decide) fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ =>
    wp_mv fun s₇ u₇ => WP.block_nil ?_
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, rdt]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, wrt]
  have s1 : s₇.gpr .s1 = St := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr,
      gt, hp.a0]
  have s2 : s₇.gpr .s2 = S := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other,
      gt, hp.a3]
  have s3 : s₇.gpr .s3 = BitVec.ofNat 64 (KL / 4 + 6) := by
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
  have kSt : Region.Sub ⟨St + BitVec.ofNat 64 240, 32⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  unfold initMid Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_addi (imm := 240) (by decide) fun s₃ u₃ =>
    wp_mv fun s₄ u₄ => WP.block_nil ?_
  have rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, hrd]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hwr]
  refine ⟨?_, by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h1],
    by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h2],
    fun r hr a b c => ?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], rd₄, wr₄⟩
  · exact
    { a0 := by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.gpr, h1]
      a1 := by simp (disch := decide) only [u₄.other, u₃.other, u₂.gpr, u₁.other, h3]
      a2 := by simp (disch := decide) only [u₄.other, u₃.gpr, u₂.other, u₁.other, h1]
      a3 := by simp (disch := decide) only [u₄.gpr, u₃.other, u₂.other, u₁.other, h2]
      rounds := hp.rounds
      wk := Offset.base_disjoint St (by decide) (by omega)
      ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      ks := (hp.st_s.sub_left kSt).sub_right (Region.sub_prefix (by decide))
      wrapK := by rw [toNat_add_lt St hw (by decide)]; omega
      wrapS := by have := hp.wS; omega
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
  have hp := IPre.of h0
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
  have s1₄ : s₄.gpr .s1 = St := by rw [g₄ _ (by decide), h₃.s1]
  have s2₄ : s₄.gpr .s2 = S := by rw [g₄ _ (by decide), h₃.s2]
  rw [initPost, List.append_assoc, WP.block_append_iff]
  refine WP.mono (Bytes.storeBytes_ok (tmp := .t1) (dst := .s1) (doff := 272) (bs := List.replicate 16 0)
    (by decide) (by decide) (by decide) (fun i hi => ?_)) fun s₅ h₅ => ?_
  · rw [h₄.wr, h₃.wr, hp.wr, s1₄]
    simp only [List.length_replicate] at hi
    exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have s2₅ : s₅.gpr .s2 = S := by rw [h₅.gpr _ (by decide), s2₄]
  rw [WP.block_append_iff]
  refine WP.mono (savePtr2_ok .s2) fun s₆ e => ?_
  subst e
  rw [s2₅]
  -- The memory, step by step.
  have fz : Frame [⟨St + BitVec.ofNat 64 272, 16⟩] s₄.mem s₅.mem := by
    have := h₅.frame; rwa [s1₄, List.length_replicate] at this
  have f₂ : Frame [⟨St, 240⟩, ⟨S, 512⟩] s₁.mem s₂.mem := h₂.frame
  have f₄ : Frame [⟨St + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩] s₃.mem s₄.mem := h₄.frame
  have m₃ : s₃.mem = s₂.mem := h₃.mem
  -- The saved registers.
  have dSv (p : Reg × Nat) (hp' : p ∈ initSaved) (r : Region) (hr : r ∈ [⟨St, 240⟩, ⟨S, 512⟩,
      ⟨St + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩, ⟨St + BitVec.ofNat 64 272, 16⟩]) :
      (⟨sv2 S + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint r := by
    have hb := init_bound p hp'
    have sub : Region.Sub ⟨sv2 S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 2304⟩ := sv2_sub S (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact (sv2_ws S (by omega)).sub_right (Region.sub_prefix (by decide))
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
    · exact sv2_ws S (by omega)
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
  have sv₁ : Spill.Saved (sv2 S) (initG s₀ S) initSaved s₁.mem := by
    rw [h₁.mem]; exact Spill.saveMem_saved (by decide) s₀.mem (sv2 S) _
  have sv₂ := sv₁.frame f₂ fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  rw [← m₃] at sv₂
  have sv₄ := sv₂.frame f₄ fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  have sv₅ := sv₄.frame fz fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; subst hr; simp)
  rw [show initSaved.map (fun (r, d) => Instr.load .d r .t0 d) = Spill.restoreCode .t0 initSaved from rfl]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := initSaved) (B := sv2 S) (Align.align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) sv₅) fun s₇ r₇ => ?_
  · have := init_bound p hp'
    show InRegions (s₅.rd ++ s₅.wr) _ 8
    rw [h₅.rd, h₅.wr, h₄.rd, h₄.wr, h₃.rd, h₃.wr, hp.rd, hp.wr]
    exact ⟨⟨S, 2304⟩, by simp, sv2_contains S (by omega)⟩
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
    have f₁ : Frame [⟨sv2 S, 32⟩] s₀.mem s₁.mem := by
      rw [h₁.mem]
      have := Spill.saveMem_frame_base (l := initSaved) (n := 32) init_bound (by decide) s₀.mem (sv2 S) (initG s₀ S)
      exact this
    have hkey : Spec.Aes.bytesAt s₁.mem Kp KL = Spec.Aes.bytesAt s₀.mem Kp KL :=
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := sv2_sub S (d := 0) (n := 32) (by decide)
        rw [BitVec.add_zero] at this
        exact hp.k_s.sub_right this) (by have := hp.wK; omega)
    have hlen : (Spec.Aes.bytesAt s₀.mem Kp KL).length = KL := Proof.Cmac.bytesAt_length _ _ _
    have dSt (d n : Nat) (hd : d + n ≤ 272) (r : Region) (hr : r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩]) :
        (⟨St + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega) (by omega) (by omega)
    have hRb : 16 * (Spec.Aes.rounds (KL / 4) + 1) ≤ 240 := by
      have := hp.klen; simp only [Spec.Aes.rounds]; omega
    -- The schedule, from the first call on.
    have sch : ∀ {d n : Nat}, d + n ≤ 240 → Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₂.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
      rw [Proof.Cmac.bytesAt_frame fz (dSt d n (by omega)) (by omega),
        Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint St (by omega) (by omega) (by omega)
          · exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).sub_right (Region.sub_prefix (by decide)))
          (by omega), m₃]
    have hsch : Spec.Aes.bytesAt s₂.mem St (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem Kp KL) := by rw [h₂.out, hkey]
    refine ⟨⟨by rw [hlen]; exact hp.klen, ?_, ?_⟩, ?_, by simp [Proof.Cmac.Stream.held_zero, Spec.Aes.bytesAt]⟩
    · rw [hlen]
      have := sch (d := 0) (n := 16 * (Spec.Aes.rounds (KL / 4) + 1)) (by omega)
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
      have hz : ∀ j < 16, (List.replicate 16 (0 : Nat)).getD j 0 = 0 := by decide
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
  have hp := IPre.of h0
  have hp' : IPre s₀' (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a3) (s₀.gpr .a2).toNat := by
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
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.a0, .a1, .a2, .a3]
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
  have sk := (sub_rel (P := fun a b => ((∃ m, IMid₂ s₀ St S KL m a) ∧ a.sp = s₀.sp) ∧
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
