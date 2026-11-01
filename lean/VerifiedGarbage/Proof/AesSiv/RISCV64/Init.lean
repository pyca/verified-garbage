module

public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common
meta import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Impl.AesSiv.RISCV64
meta import VerifiedGarbage.Impl.AesSiv.RISCV64
public import VerifiedGarbage.Spec.Siv
meta import VerifiedGarbage.Spec.Siv
import VerifiedGarbage.Proof.AesSiv.Key
meta import VerifiedGarbage.Proof.AesSiv.Key
import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Frame
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
public import VerifiedGarbage.Proof.AesSiv.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch

/-!
# AES-SIV on RISC-V: `vg_aes_siv_init`

Untrusted: everything here is checked by Lean. The code saves `ra` and
`s1`–`s4` in the scratch buffer at `sv2 S` (`Spill.save_ok`), expands `K1`
into the context, derives its subkeys after the schedule, expands `K2`
after them and restores the registers (`Spill.restore_wp`): the context is
then the key's (`Proof.AesSiv.keyRepr_of`). The code between the calls is
constant time by the taint analysis, and the calls by their own proofs
(`ek_rel`, `sub_rel`), their arguments pinned by `IMid₁`, `IMid₂` and
`IMid₃`. Last, the shared contract, with the scratch buffer as a last
argument (`init_verified`) and in a frame on the stack (`init_framed`). As on
PPC64LE (`Proof/AesSiv/PPC64LE/Init.lean`), with the
registers saved as streaming AES-CMAC's `init` saves them
(`Proof/CmacAes/Stream/RISCV64/Init.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesSiv.RISCV64
open VG.Impl.CmacAes.Stream.RISCV64 (savePtr2)
open VG.Proof.CmacAes.Stream.RISCV64 (EArgs SArgs ek_call sub_call ek_rel sub_rel ofNat_toNat_eq toNat_add_lt
  preserved_ne in_wr sv2 sv2_add sv2_ws savePtr2_ok)
open VG.Proof.AesCbc.RISCV64 (taintRegs wp_sp)

/-- `vg_aes_siv_init(key = a0, key_len = a1, ctx = a2, scratch = a3)`, with
a 2560-byte scratch buffer. -/
def initRISCV64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let ctx : Region := ⟨s.gpr .a2, 512⟩
    let scr : Region := ⟨s.gpr .a3, 2560⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      ctx.Disjoint key ∧ ctx.Disjoint scr ∧ key.Disjoint scr ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 512 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + 2560 ≤ 2 ^ 64 ∧
      ((s.gpr .a1).toNat = 32 ∨ (s.gpr .a1).toNat = 48 ∨ (s.gpr .a1).toNat = 64)
  post s s' := Spec.Siv.KeyRepr s'.mem (s.gpr .a2) (Spec.Aes.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- The precondition, by name: the key `Kp` of `KL` bytes, the context `Ct`
and the scratch buffer `S`. -/
structure IPre (s₀ : State) (Kp Ct S : Addr) (KL : Nat) : Prop where
  a0 : s₀.gpr .a0 = Kp
  a1 : (s₀.gpr .a1).toNat = KL
  a2 : s₀.gpr .a2 = Ct
  a3 : s₀.gpr .a3 = S
  rd : s₀.rd = [⟨Kp, KL⟩]
  wr : s₀.wr = [⟨Ct, 512⟩, ⟨S, 2560⟩]
  ct_k : (⟨Ct, 512⟩ : Region).Disjoint ⟨Kp, KL⟩
  ct_s : (⟨Ct, 512⟩ : Region).Disjoint ⟨S, 2560⟩
  k_s : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 2560⟩
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wCt : Ct.toNat + 512 ≤ 2 ^ 64
  wS : S.toNat + 2560 ≤ 2 ^ 64
  klen : KL = 32 ∨ KL = 48 ∨ KL = 64

theorem IPre.of {s₀ : State} (h : initRISCV64.pre s₀) :
    IPre s₀ (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a1).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

/-- `r` lies at an offset within `big`. -/
abbrev InAt (r big : Region) : Prop := ∃ off, r.base = big.base + BitVec.ofNat 64 off ∧ off + r.len ≤ big.len

theorem InAt.base {p : Addr} {n k : Nat} (h : n ≤ k) : InAt ⟨p, n⟩ ⟨p, k⟩ := ⟨0, by simp, by simpa using h⟩

theorem InAt.off {p : Addr} {d n k : Nat} (h : d + n ≤ k) : InAt ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

/-! ## The slots of the saved registers -/

/-- A slot at `sv2 S + d`, within the scratch buffer. -/
theorem sv_sub (S : Addr) {d n : Nat} (h : d + n ≤ 121) :
    Region.Sub ⟨sv2 S + BitVec.ofNat 64 d, n⟩ ⟨S, 2560⟩ := by
  have := Align.pad_lt (S + BitVec.ofNat 64 2176)
  rw [sv2_add]; exact Offset.sub_base _ (by omega)

theorem sv_contains (S : Addr) {d n : Nat} (h : d + n ≤ 121) :
    (⟨S, 2560⟩ : Region).Contains (sv2 S + BitVec.ofNat 64 d) n := by
  have := Align.pad_lt (S + BitVec.ofNat 64 2176)
  rw [sv2_add]; exact Offset.contains_base _ (by omega) (by omega)

namespace IPre

variable {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL)
include hp

theorem half : KL / 2 = 16 ∨ KL / 2 = 24 ∨ KL / 2 = 32 := by rcases hp.klen with h | h | h <;> omega

theorem rounds : KL / 8 + 6 = 10 ∨ KL / 8 + 6 = 12 ∨ KL / 8 + 6 = 14 := by
  rcases hp.klen with h | h | h <;> omega

theorem sched_le : 16 * (KL / 8 + 6 + 1) ≤ 240 := by rcases hp.klen with h | h | h <;> omega

/-- Regions within the key, the context and the scratch buffer are covered
by the permissions. -/
theorem cover {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {rs ws : List Region}
    (hr : ∀ r ∈ rs, InAt r ⟨Kp, KL⟩ ∨ InAt r ⟨Ct, 512⟩ ∨ InAt r ⟨S, 2560⟩)
    (hw : ∀ r ∈ ws, InAt r ⟨Ct, 512⟩ ∨ InAt r ⟨S, 2560⟩) :
    Covers (rs ++ ws) (s.rd ++ s.wr) ∧ Covers ws s.wr := by
  rw [hrd, hwr, hp.rd, hp.wr]
  refine ⟨Covers.of_sub fun r h => ?_, Covers.of_sub fun r h => ?_⟩
  · rcases List.mem_append.mp h with h | h
    · rcases hr r h with h' | h' | h'
      · exact ⟨⟨Kp, KL⟩, by simp, h'⟩
      · exact ⟨⟨Ct, 512⟩, by simp, h'⟩
      · exact ⟨⟨S, 2560⟩, by simp, h'⟩
    · rcases hw r h with h' | h'
      · exact ⟨⟨Ct, 512⟩, by simp, h'⟩
      · exact ⟨⟨S, 2560⟩, by simp, h'⟩
  · rcases hw r h with h' | h'
    · exact ⟨⟨Ct, 512⟩, by simp, h'⟩
    · exact ⟨⟨S, 2560⟩, by simp, h'⟩

end IPre

theorem rounds_eq (KL : Nat) : Spec.Aes.rounds (KL / 2 / 4) = KL / 8 + 6 := by
  simp only [Spec.Aes.rounds]; omega

/-- The halves of the key. -/
theorem k1Sub (Kp : Addr) (KL : Nat) : Region.Sub ⟨Kp, KL / 2⟩ ⟨Kp, KL⟩ := Region.sub_prefix (by omega)

theorem k2Sub (Kp : Addr) (KL : Nat) : Region.Sub ⟨Kp + BitVec.ofNat 64 (KL / 2), KL / 2⟩ ⟨Kp, KL⟩ :=
  Offset.sub_base Kp (by omega)

theorem half_bv {KL : Nat} (h : KL = 32 ∨ KL = 48 ∨ KL = 64) :
    BitVec.ofNat 64 KL >>> 1 = BitVec.ofNat 64 (KL / 2) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem rounds_bv {KL : Nat} (h : KL = 32 ∨ KL = 48 ∨ KL = 64) :
    BitVec.ofNat 64 (KL / 2) >>> 2 + BitVec.ofNat 64 6 = BitVec.ofNat 64 (KL / 8 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

/-- What the code saves: the registers, with `t0` the slots' base. -/
abbrev initG (s₀ : State) (S : Addr) : Reg → BitVec 64 := (s₀.write .t0 (sv2 S)).gpr

/-- The memory after saving the registers. -/
abbrev initMem (s₀ : State) (S : Addr) : Mem := Spill.saveMem s₀.mem (sv2 S) (initG s₀ S) initSaved

theorem init_bound : ∀ p ∈ initSaved, p.2 + 8 ≤ 40 := by decide

/-! ## Before the first call -/

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (s : State) : Prop where
  args : EArgs s Kp Ct S (KL / 2)
  s1 : s.gpr .s1 = Kp
  s2 : s.gpr .s2 = BitVec.ofNat 64 (KL / 2)
  s3 : s.gpr .s3 = Ct
  s4 : s.gpr .s4 = S
  other : ∀ r ∈ preserved, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s.gpr r = s₀.gpr r
  mem : s.mem = initMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initPre_wp {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL) :
    WP isa (.block initPre) s₀ (IMid₁ s₀ Kp Ct S KL) := by
  have sw := hp.wS
  have hKL : s₀.gpr .a1 = BitVec.ofNat 64 KL := ofNat_toNat_eq hp.a1
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
    exact ⟨⟨S, 2560⟩, by simp, sv_contains S (by omega)⟩
  generalize ht : ({ (s₀.write .t0 (sv2 S)) with
    mem := Spill.saveMem (s₀.write .t0 (sv2 S)).mem ((s₀.write .t0 (sv2 S)).gpr .t0)
      (s₀.write .t0 (sv2 S)).gpr initSaved } : State) = t
  have gt (r : Reg) (hr : r ≠ .t0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact g₀ r hr
  have memt : t.mem = initMem s₀ S := by
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [t₀, RegUpd.mem_write]
  have rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  have wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  unfold Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₁ u₁ => wp_srl (by decide) fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    wp_mv fun s₅ u₅ => WP.block_nil ?_
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, rdt]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, wrt]
  have s2 : s₅.gpr .s2 = BitVec.ofNat 64 (KL / 2) := by
    simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other, gt, hKL]
    exact half_bv hp.klen
  have cv := hp.cover rd₅ wr₅ (rs := [⟨Kp, KL / 2⟩]) (ws := [⟨Ct, 240⟩, ⟨S, 512⟩])
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inl (InAt.base (by omega)))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl (InAt.base (by decide))
      · exact .inr (InAt.base (by decide)))
  refine ⟨?_, by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr, gt, hp.a0], s2,
    by simp (disch := decide) only [u₅.other, u₄.other, u₃.gpr, u₂.other, u₁.other, gt, hp.a2],
    by simp (disch := decide) only [u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other, gt, hp.a3],
    fun r hr h1 h2 h3 h4 => ?_, ?_, rd₅, wr₅⟩
  · exact
    { a0 := by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, gt, hp.a0]
      a1 := by rw [u₅.gpr, s2.symm, u₅.other .s2 (by decide)]
      a2 := by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, gt, hp.a2]
      a3 := by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, gt, hp.a3]
      klen := hp.half
      kw := hp.ct_k.symm.sub_left (k1Sub Kp KL) |>.sub_right (Region.sub_prefix (by decide))
      ks := (hp.k_s.sub_left (k1Sub Kp KL)).sub_right (Region.sub_prefix (by decide))
      ws := (hp.ct_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      reads := cv.1
      writes := cv.2 }
  · obtain ⟨h0, -, -, -, -, -, -, -, -, ha1, -⟩ := preserved_ne r hr
    rw [u₅.other _ ha1, u₄.other _ h4, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1, gt _ h0]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, memt]

/-! ## Between the calls -/

/-- What the code between the first two calls leaves. -/
structure IMid₂ (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (m : Mem) (s : State) : Prop where
  args : SArgs s Ct (Ct + BitVec.ofNat 64 240) S (KL / 8 + 6)
  s1 : s.gpr .s1 = Kp
  s2 : s.gpr .s2 = BitVec.ofNat 64 (KL / 2)
  s3 : s.gpr .s3 = Ct
  s4 : s.gpr .s4 = S
  keep : ∀ r ∈ preserved, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s.gpr r = s₀.gpr r
  mem : s.mem = m
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The registers the calls keep, and where they are. -/
structure IRegs (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (s : State) : Prop where
  s1 : s.gpr .s1 = Kp
  s2 : s.gpr .s2 = BitVec.ofNat 64 (KL / 2)
  s3 : s.gpr .s3 = Ct
  s4 : s.gpr .s4 = S
  keep : ∀ r ∈ preserved, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem IRegs.call {s₀ s s' : State} {Kp Ct S : Addr} {KL : Nat} (h : IRegs s₀ Kp Ct S KL s)
    (hs : ∀ r ∈ preserved, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    IRegs s₀ Kp Ct S KL s' :=
  ⟨by rw [hs _ (by decide), h.s1], by rw [hs _ (by decide), h.s2], by rw [hs _ (by decide), h.s3],
    by rw [hs _ (by decide), h.s4], fun r hr a b c d => by rw [hs r hr, h.keep r hr a b c d],
    by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

theorem IMid₁.regs {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (h : IMid₁ s₀ Kp Ct S KL s) :
    IRegs s₀ Kp Ct S KL s := ⟨h.s1, h.s2, h.s3, h.s4, h.other, h.rd, h.wr⟩

theorem initMid₁_wp {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL)
    (h : IRegs s₀ Kp Ct S KL s) : WP isa (.block initMid₁) s (IMid₂ s₀ Kp Ct S KL s.mem) := by
  have hw := hp.wCt
  have kCt : Region.Sub ⟨Ct + BitVec.ofNat 64 240, 32⟩ ⟨Ct, 512⟩ := Offset.sub_base Ct (by decide)
  unfold initMid₁ Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₁ u₁ => wp_srl (by decide) fun s₂ u₂ => wp_addi (imm := 6) (by decide) fun s₃ u₃ =>
    wp_addi (imm := 240) (by decide) fun s₄ u₄ => wp_mv fun s₅ u₅ => WP.block_nil ?_
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  have cv := hp.cover rd₅ wr₅ (rs := [⟨Ct, 240⟩]) (ws := [⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩])
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl (InAt.base (by decide))))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl (InAt.off (by decide))
      · exact .inr (InAt.base (by decide)))
  refine ⟨?_, by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.s1],
    by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.s2],
    by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.s3],
    by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.s4],
    fun r hr a b c d => ?_, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], rd₅, wr₅⟩
  · exact
    { a0 := by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr, h.s3]
      a1 := by
        simp (disch := decide) only [u₅.other, u₄.other, u₃.gpr, u₂.gpr, u₁.other, h.s2]
        exact rounds_bv hp.klen
      a2 := by simp (disch := decide) only [u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other, h.s3]
      a3 := by simp (disch := decide) only [u₅.gpr, u₄.other, u₃.other, u₂.other, u₁.other, h.s4]
      rounds := hp.rounds
      wk := Offset.base_disjoint Ct (by decide) (by omega)
      ws := (hp.ct_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      ks := (hp.ct_s.sub_left kCt).sub_right (Region.sub_prefix (by decide))
      wrapK := by rw [toNat_add_lt Ct hw (by decide)]; omega
      wrapS := by have := hp.wS; omega
      reads := cv.1
      writes := cv.2 }
  · obtain ⟨-, -, -, -, -, -, -, -, ha0, ha1, ha2, ha3, -⟩ := preserved_ne r hr
    rw [u₅.other _ ha3, u₄.other _ ha2, u₃.other _ ha1, u₂.other _ ha1, u₁.other _ ha0, h.keep r hr a b c d]

/-- What the code between the last two calls leaves. -/
structure IMid₃ (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (m : Mem) (s : State) : Prop where
  args : EArgs s (Kp + BitVec.ofNat 64 (KL / 2)) (Ct + BitVec.ofNat 64 272) S (KL / 2)
  s4 : s.gpr .s4 = S
  keep : ∀ r ∈ preserved, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s.gpr r = s₀.gpr r
  mem : s.mem = m
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initMid₂_wp {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL)
    (h : IRegs s₀ Kp Ct S KL s) : WP isa (.block initMid₂) s (IMid₃ s₀ Kp Ct S KL s.mem) := by
  have kCt : Region.Sub ⟨Ct + BitVec.ofNat 64 272, 240⟩ ⟨Ct, 512⟩ := Offset.sub_base Ct (by decide)
  unfold initMid₂ Impl.AesCbc.RISCV64.mov
  refine wp_add fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_addi (imm := 272) (by decide) fun s₃ u₃ =>
    wp_mv fun s₄ u₄ => WP.block_nil ?_
  have rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  have cv := hp.cover rd₄ wr₄ (rs := [⟨Kp + BitVec.ofNat 64 (KL / 2), KL / 2⟩])
    (ws := [⟨Ct + BitVec.ofNat 64 272, 240⟩, ⟨S, 512⟩])
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inl (InAt.off (by omega)))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl (InAt.off (by decide))
      · exact .inr (InAt.base (by decide)))
  refine ⟨?_, by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h.s4],
    fun r hr a b c d => ?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], rd₄, wr₄⟩
  · exact
    { a0 := by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.gpr, h.s1, h.s2]
      a1 := by simp (disch := decide) only [u₄.other, u₃.other, u₂.gpr, u₁.other, h.s2]
      a2 := by simp (disch := decide) only [u₄.other, u₃.gpr, u₂.other, u₁.other, h.s3]
      a3 := by simp (disch := decide) only [u₄.gpr, u₃.other, u₂.other, u₁.other, h.s4]
      klen := hp.half
      kw := (hp.ct_k.sub_left kCt).symm.sub_left (k2Sub Kp KL)
      ks := (hp.k_s.sub_left (k2Sub Kp KL)).sub_right (Region.sub_prefix (by decide))
      ws := (hp.ct_s.sub_left kCt).sub_right (Region.sub_prefix (by decide))
      reads := cv.1
      writes := cv.2 }
  · obtain ⟨-, -, -, -, -, -, -, -, ha0, ha1, ha2, ha3, -⟩ := preserved_ne r hr
    rw [u₄.other _ ha3, u₃.other _ ha2, u₂.other _ ha1, u₁.other _ ha0, h.keep r hr a b c d]

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initRISCV64.pre s₀) :
    WP isa init s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.sp = s₀.sp ∧ initRISCV64.post s₀ s' := by
  have hp := IPre.of h0
  generalize s₀.gpr .a0 = Kp at hp
  generalize s₀.gpr .a2 = Ct at hp
  generalize s₀.gpr .a3 = S at hp
  generalize (s₀.gpr .a1).toNat = KL at hp
  have hw := hp.wCt
  have hsw := hp.wS
  have hkw := hp.wK
  refine WP.seq (WP.mono (wp_sp (initPre_wp hp)) fun s₁ ⟨h₁, sp₁⟩ => ?_)
  refine WP.seq (WP.mono (ek_call h₁.args) fun s₂ h₂ => ?_)
  have R₂ := h₁.regs.call h₂.saved h₂.rd h₂.wr
  refine WP.seq (WP.mono (wp_sp (initMid₁_wp hp R₂)) fun s₃ ⟨h₃, sp₃⟩ => ?_)
  refine WP.seq (WP.mono (sub_call h₃.args) fun s₄ h₄ => ?_)
  have R₄ : IRegs s₀ Kp Ct S KL s₄ :=
    (⟨h₃.s1, h₃.s2, h₃.s3, h₃.s4, h₃.keep, h₃.rd, h₃.wr⟩ : IRegs s₀ Kp Ct S KL s₃).call h₄.saved h₄.rd h₄.wr
  refine WP.seq (WP.mono (wp_sp (initMid₂_wp hp R₄)) fun s₅ ⟨h₅, sp₅⟩ => ?_)
  refine WP.seq (WP.mono (ek_call h₅.args) fun s₆ h₆ => ?_)
  have s4₆ : s₆.gpr .s4 = S := by rw [h₆.saved _ (by decide), h₅.s4]
  rw [initPost, WP.block_append_iff]
  refine WP.mono (savePtr2_ok .s4) fun s₇ e => ?_
  subst e
  rw [s4₆]
  -- The memory, call by call.
  have f₂ : Frame [⟨Ct, 240⟩, ⟨S, 512⟩] s₁.mem s₂.mem := h₂.frame
  have f₄ : Frame [⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩] s₃.mem s₄.mem := h₄.frame
  have f₆ : Frame [⟨Ct + BitVec.ofNat 64 272, 240⟩, ⟨S, 512⟩] s₅.mem s₆.mem := h₆.frame
  have m₃ : s₃.mem = s₂.mem := h₃.mem
  have m₅ : s₅.mem = s₄.mem := h₅.mem
  -- The saved registers.
  have dSv (p : Reg × Nat) (hp' : p ∈ initSaved) (r : Region) (hr : r ∈ [⟨Ct, 240⟩, ⟨S, 512⟩,
      ⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩, ⟨Ct + BitVec.ofNat 64 272, 240⟩]) :
      (⟨sv2 S + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint r := by
    have hb := init_bound p hp'
    have sub : Region.Sub ⟨sv2 S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 2560⟩ := sv_sub S (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.ct_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact (sv2_ws S (by omega)).sub_right (Region.sub_prefix (by decide))
    · exact (hp.ct_s.sub_left (Offset.sub_base Ct (by decide))).symm.sub_left sub
    · exact sv2_ws S (by omega)
    · exact (hp.ct_s.sub_left (Offset.sub_base Ct (by decide))).symm.sub_left sub
  have sv₁ : Spill.Saved (sv2 S) (initG s₀ S) initSaved s₁.mem := by
    rw [h₁.mem]; exact Spill.saveMem_saved (by decide) s₀.mem (sv2 S) _
  have sv₂ := sv₁.frame f₂ fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  rw [← m₃] at sv₂
  have sv₄ := sv₂.frame f₄ fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  rw [← m₅] at sv₄
  have sv₆ := sv₄.frame f₆ fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  rw [show initSaved.map (fun (r, d) => Instr.load .d r .t0 d) = Spill.restoreCode .t0 initSaved from rfl]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := initSaved) (B := sv2 S) (Align.align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) sv₆) fun s₈ r₈ => ?_
  · have := init_bound p hp'
    show InRegions (s₆.rd ++ s₆.wr) _ 8
    rw [h₆.rd, h₆.wr, h₅.rd, h₅.wr, hp.rd, hp.wr]
    exact ⟨⟨S, 2560⟩, by simp, sv_contains S (by omega)⟩
  have g₀ (r : Reg) (hr : r ≠ .t0) : initG s₀ S r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · have h0 := (preserved_ne r hr).1
    rw [r₈.gpr_of (r := r) ?_, g₀ r h0]
    by_cases hv : r = .s1 ∨ r = .s2 ∨ r = .s3 ∨ r = .s4
    · left; rcases hv with rfl | rfl | rfl | rfl <;> decide
    · right
      rw [RegUpd.gpr_write_of_ne _ _ h0, h₆.saved r hr, h₅.keep r hr (fun e => hv (.inl e))
        (fun e => hv (.inr (.inl e))) (fun e => hv (.inr (.inr (.inl e)))) (fun e => hv (.inr (.inr (.inr e)))),
        g₀ r h0]
  · rw [r₈.gpr (.ra, 0) (by decide), g₀ .ra (by decide)]
  · rw [r₈.sp, RegUpd.sp_write, h₆.sp, sp₅, h₄.sp, sp₃, h₂.sp, sp₁]
  · show Spec.Siv.KeyRepr s₈.mem (s₀.gpr .a2) (Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)
    rw [hp.a0, hp.a2, hp.a1, r₈.mem, RegUpd.mem_write]
    -- The key, unchanged until the last call.
    have f₁ : Frame [⟨sv2 S, 40⟩] s₀.mem s₁.mem := by
      rw [h₁.mem]
      exact Spill.saveMem_frame_base (l := initSaved) (n := 40) init_bound (by decide) s₀.mem (sv2 S) (initG s₀ S)
    have svS : Region.Sub ⟨sv2 S, 40⟩ ⟨S, 2560⟩ := by
      have := sv_sub S (d := 0) (n := 40) (by decide); rwa [BitVec.add_zero] at this
    have dK : ∀ {d n : Nat}, d + n ≤ KL → ∀ r ∈ [⟨sv2 S, 40⟩, ⟨Ct, 240⟩, ⟨S, 512⟩,
        ⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩], (⟨Kp + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
      intro d n hd r hr
      have sub : Region.Sub ⟨Kp + BitVec.ofNat 64 d, n⟩ ⟨Kp, KL⟩ := Offset.sub_base Kp hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact (hp.k_s.sub_left sub).sub_right svS
      · exact (hp.ct_k.symm.sub_left sub).sub_right (Region.sub_prefix (by decide))
      · exact (hp.k_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
      · exact (hp.ct_k.symm.sub_left sub).sub_right (Offset.sub_base Ct (by decide))
      · exact (hp.k_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
    have key : ∀ {d n : Nat}, d + n ≤ KL → Spec.Aes.bytesAt s₅.mem (Kp + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₀.mem (Kp + BitVec.ofNat 64 d) n := fun {d n} hd => by
      have hl : n ≤ 2 ^ 64 := by omega
      rw [m₅, Proof.Cmac.bytesAt_frame f₄ (fun r hr => dK hd r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)) hl,
        m₃, Proof.Cmac.bytesAt_frame f₂ (fun r hr => dK hd r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)) hl,
        Proof.Cmac.bytesAt_frame f₁ (fun r hr => dK hd r (by
          simp only [List.mem_singleton] at hr ⊢; subst hr; simp)) hl]
    have key1 : Spec.Aes.bytesAt s₁.mem Kp (KL / 2) = Spec.Aes.bytesAt s₀.mem Kp (KL / 2) := by
      rw [Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.k_s.sub_left (k1Sub Kp KL)).sub_right svS) (by omega)]
    have hR := rounds_eq KL
    have hsl := hp.sched_le
    -- `K1`'s schedule, from the first call on.
    have dC1 : ∀ r ∈ [⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩, ⟨Ct + BitVec.ofNat 64 272, 240⟩, ⟨S, 512⟩],
        (⟨Ct, 16 * (KL / 8 + 6 + 1)⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Offset.base_disjoint Ct (by omega) (by omega)
      · exact (hp.ct_s.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by decide))
      · exact Offset.base_disjoint Ct (by omega) (by omega)
      · exact (hp.ct_s.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by decide))
    have sch₄ : Spec.Aes.bytesAt s₄.mem Ct (16 * (KL / 8 + 6 + 1)) =
        Spec.Aes.bytesAt s₂.mem Ct (16 * (KL / 8 + 6 + 1)) := by
      rw [Proof.Cmac.bytesAt_frame f₄ (fun r hr => dC1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp))
        (by omega), m₃]
    have sch₆ : Spec.Aes.bytesAt s₆.mem Ct (16 * (KL / 8 + 6 + 1)) =
        Spec.Aes.bytesAt s₂.mem Ct (16 * (KL / 8 + 6 + 1)) := by
      rw [Proof.Cmac.bytesAt_frame f₆ (fun r hr => dC1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp))
        (by omega), m₅, sch₄]
    have k1₂ : Spec.Aes.bytesAt s₂.mem Ct (16 * (KL / 8 + 6 + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem Kp (KL / 2)) := by
      have := h₂.out; rw [hR, key1] at this; exact this
    refine Proof.AesSiv.keyRepr_of hp.klen (by rw [hR, sch₆, k1₂]) ?_ ?_
    · have e : Spec.Aes.bytesAt s₆.mem (Ct + BitVec.ofNat 64 240) 32 =
          Spec.Aes.bytesAt s₄.mem (Ct + BitVec.ofNat 64 240) 32 := by
        rw [Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint Ct (by omega) (by omega) (by omega)
          · exact (hp.ct_s.sub_left (Offset.sub_base Ct (by decide))).sub_right (Region.sub_prefix (by decide)))
          (by decide), m₅]
      rw [e, h₄.out, m₃, k1₂]
    · have e := h₆.out
      rw [show KL / 2 / 4 = KL / 8 by omega] at e
      rw [show KL / 2 / 4 = KL / 8 by omega, e, key (d := KL / 2) (n := KL / 2) (by omega)]

/-! ## Constant time -/

theorem init_rel {s₀ s₀' : State} (h0 : initRISCV64.pre s₀) (h0' : initRISCV64.pre s₀')
    (hq : initRISCV64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') init fun _ _ => True := by
  obtain ⟨q0, q1, q2, q3, qsp⟩ := hq
  have hp := IPre.of h0
  have hp' : IPre s₀' (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a1).toNat := by
    rw [q0, q1, q2, q3]; exact IPre.of h0'
  generalize s₀.gpr .a0 = Kp at hp hp'
  generalize s₀.gpr .a2 = Ct at hp hp'
  generalize s₀.gpr .a3 = S at hp hp'
  generalize (s₀.gpr .a1).toNat = KL at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3]) (.block initPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1, .s2, .s3, .s4]) (.block initMid₁) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1, .s2, .s3, .s4]) (.block initMid₂) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hD⟩ : ∃ h, (taint.check (Taint.ofRegs [.s4]) (.block initPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  -- What each run keeps between the calls, with its stack pointer.
  let I (σ : State) (s : State) : Prop := IRegs σ Kp Ct S KL s ∧ s.sp = σ.sp
  have regs : ∀ {a b : State}, I s₀ a → I s₀' b → a.sp = b.sp ∧
      ∀ r ∈ ([.s1, .s2, .s3, .s4] : List Reg), a.gpr r = b.gpr r := fun h₁ h₂ => by
    refine ⟨by rw [h₁.2, h₂.2, qsp], fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.1.s1, h₂.1.s1]
    · rw [h₁.1.s2, h₂.1.s2]
    · rw [h₁.1.s3, h₂.1.s3]
    · rw [h₁.1.s4, h₂.1.s4]
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.a0, .a1, .a2, .a3]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨qsp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := fun (s : State) => IMid₁ s₀ Kp Ct S KL s ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => IMid₁ s₀' Kp Ct S KL s ∧ s.sp = s₀'.sp) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨wp_sp (initPre_wp hp), wp_sp (initPre_wp hp')⟩
  have e₁ := (ek_rel (P := fun a b => (IMid₁ s₀ Kp Ct S KL a ∧ a.sp = s₀.sp) ∧
      (IMid₁ s₀' Kp Ct S KL b ∧ b.sp = s₀'.sp))
    fun a b h => ⟨h.1.1.args, h.2.1.args, by rw [h.1.2, h.2.2, qsp]⟩).wp
    (F₁ := I s₀) (F₂ := I s₀') fun a b h =>
      ⟨WP.mono (ek_call h.1.1.args) fun _ h' => ⟨h.1.1.regs.call h'.saved h'.rd h'.wr, by rw [h'.sp, h.1.2]⟩,
       WP.mono (ek_call h.2.1.args) fun _ h' => ⟨h.2.1.regs.call h'.saved h'.rd h'.wr, by rw [h'.sp, h.2.2]⟩⟩
  have m₁ := (taintRegs (P := fun a b => I s₀ a ∧ I s₀' b) [.s1, .s2, .s3, .s4]
    (fun a b h => regs h.1 h.2) hB).wp
    (F₁ := fun (s : State) => (∃ m, IMid₂ s₀ Kp Ct S KL m s) ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => (∃ m, IMid₂ s₀' Kp Ct S KL m s) ∧ s.sp = s₀'.sp)
    fun a b h =>
      ⟨WP.mono (wp_sp (initMid₁_wp hp h.1.1)) fun _ h' => ⟨⟨_, h'.1⟩, by rw [h'.2, h.1.2]⟩,
       WP.mono (wp_sp (initMid₁_wp hp' h.2.1)) fun _ h' => ⟨⟨_, h'.1⟩, by rw [h'.2, h.2.2]⟩⟩
  have sk := (sub_rel (P := fun a b => ((∃ m, IMid₂ s₀ Kp Ct S KL m a) ∧ a.sp = s₀.sp) ∧
      ((∃ m, IMid₂ s₀' Kp Ct S KL m b) ∧ b.sp = s₀'.sp))
    fun a b ⟨⟨⟨_, h₁⟩, sp₁⟩, ⟨⟨_, h₂⟩, sp₂⟩⟩ => ⟨h₁.args, h₂.args, by rw [sp₁, sp₂, qsp]⟩).wp
    (F₁ := I s₀) (F₂ := I s₀')
    fun a b ⟨⟨⟨_, h₁⟩, sp₁⟩, ⟨⟨_, h₂⟩, sp₂⟩⟩ =>
      ⟨WP.mono (sub_call h₁.args) fun _ h => ⟨(⟨h₁.s1, h₁.s2, h₁.s3, h₁.s4, h₁.keep, h₁.rd, h₁.wr⟩ :
          IRegs s₀ Kp Ct S KL _).call h.saved h.rd h.wr, by rw [h.sp, sp₁]⟩,
        WP.mono (sub_call h₂.args) fun _ h => ⟨(⟨h₂.s1, h₂.s2, h₂.s3, h₂.s4, h₂.keep, h₂.rd, h₂.wr⟩ :
          IRegs s₀' Kp Ct S KL _).call h.saved h.rd h.wr, by rw [h.sp, sp₂]⟩⟩
  have m₂ := (taintRegs (P := fun a b => I s₀ a ∧ I s₀' b) [.s1, .s2, .s3, .s4]
    (fun a b h => regs h.1 h.2) hC).wp
    (F₁ := fun (s : State) => (∃ m, IMid₃ s₀ Kp Ct S KL m s) ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => (∃ m, IMid₃ s₀' Kp Ct S KL m s) ∧ s.sp = s₀'.sp)
    fun a b h =>
      ⟨WP.mono (wp_sp (initMid₂_wp hp h.1.1)) fun _ h' => ⟨⟨_, h'.1⟩, by rw [h'.2, h.1.2]⟩,
       WP.mono (wp_sp (initMid₂_wp hp' h.2.1)) fun _ h' => ⟨⟨_, h'.1⟩, by rw [h'.2, h.2.2]⟩⟩
  have e₂ := (ek_rel (P := fun a b => ((∃ m, IMid₃ s₀ Kp Ct S KL m a) ∧ a.sp = s₀.sp) ∧
      ((∃ m, IMid₃ s₀' Kp Ct S KL m b) ∧ b.sp = s₀'.sp))
    fun a b ⟨⟨⟨_, h₁⟩, sp₁⟩, ⟨⟨_, h₂⟩, sp₂⟩⟩ => ⟨h₁.args, h₂.args, by rw [sp₁, sp₂, qsp]⟩).wp
    (F₁ := fun (s : State) => s.gpr .s4 = S ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .s4 = S ∧ s.sp = s₀'.sp)
    fun a b ⟨⟨⟨_, h₁⟩, sp₁⟩, ⟨⟨_, h₂⟩, sp₂⟩⟩ =>
      ⟨WP.mono (ek_call h₁.args) fun _ h => ⟨by rw [h.saved _ (by decide), h₁.s4], by rw [h.sp, sp₁]⟩,
        WP.mono (ek_call h₂.args) fun _ h => ⟨by rw [h.saved _ (by decide), h₂.s4], by rw [h.sp, sp₂]⟩⟩
  have p := taintRegs
    (P := fun a b => (a.gpr .s4 = S ∧ a.sp = s₀.sp) ∧ b.gpr .s4 = S ∧ b.sp = s₀'.sp) [.s4]
    (fun a b h => by
      refine ⟨by rw [h.1.2, h.2.2, qsp], fun r hr => ?_⟩
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1, h.2.1]) hD
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((sk.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      ((m₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))))

theorem init_ct : ConstantTime isa initRISCV64.pre initRISCV64.pub init :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (init_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem init_correct (s : State) (hs : initRISCV64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ := init_wp hs
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

/-! ## The shared contract -/

/-- A state satisfying `vg_aes_siv_init`'s precondition: a 32-byte key at
`0x1000`, the context at `0x2000` and the scratch buffer at `0x3000`. -/
def initSat : State where
  gpr r := match r with | .a0 => 0x1000 | .a1 => 32 | .a2 => 0x2000 | .a3 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 512⟩, ⟨0x3000, 2560⟩]

theorem init_verified : Verified RISCV64.target init (Proof.AesSiv.initScratchContract RISCV64.abi) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, Spec.Siv.initPre,
      Spec.Siv.initPost, initRISCV64, RISCV64.abi, RISCV64.argRegs, List.getD] [initSat] using initSat)

/-- `initSat` without the scratch buffer. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 512⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Siv.initContract RISCV64.abi 2560).pre s := by
  implies_sat [Spec.Siv.initContract, Spec.Siv.initSig, Spec.Siv.initPre, Spec.Siv.initPost,
    RISCV64.abi, RISCV64.argRegs, List.getD] [initFrameSat, initSat] using initFrameSat

/-- `init` with its scratch buffer in a frame of 2560 bytes. -/
theorem init_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a3 init)
      (Spec.Siv.initContract RISCV64.abi 2560) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Siv.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Siv.initPre RISCV64.abi.ptrBits) (post := Spec.Siv.initPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2560) init_verified (by decide) (by decide) initFrameSat_pre

end VG.Proof.AesSiv.RISCV64
