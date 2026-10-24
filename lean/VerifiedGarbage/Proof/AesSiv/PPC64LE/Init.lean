module

public import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Common
meta import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Impl.AesSiv.PPC64LE
meta import VerifiedGarbage.Impl.AesSiv.PPC64LE
public import VerifiedGarbage.Spec.Siv
import VerifiedGarbage.Proof.AesSiv.Key
import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-SIV on PPC64LE: `vg_aes_siv_init`

Untrusted: everything here is checked by Lean. The code saves `r14`–`r17`
and the return address in the scratch buffer (`Spill.save_ok`), expands
`K1` into the context, derives its subkeys after the schedule, expands `K2`
after them and restores the registers (`Spill.restore_ok`): the context is
then the key's (`Proof.AesSiv.keyRepr_of`). The code between the calls is
constant time by the taint analysis, and the calls by their own proofs
(`ek_rel`, `sub_rel`), their arguments pinned by `IMid₁`, `IMid₂` and
`IMid₃`.
-/

@[expose] public section

namespace VG.Proof.AesSiv.PPC64LE

open VG VG.PPC64LE VG.Impl.AesSiv.PPC64LE
open VG.Proof.CmacAes.Stream.PPC64LE (EArgs SArgs ek_call sub_call ek_rel sub_rel ofNat_toNat_eq toNat_add_lt
  preserved_ne in_wr saveG saveG_ne saveG_r0)
open VG.Proof.AesCbc.PPC64LE (taintRegs wp_sp)

/-- `vg_aes_siv_init(key = r3, key_len = r4, ctx = r5, scratch = r6)`, with
a 2560-byte scratch buffer. -/
def initPPC64LE : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let ctx : Region := ⟨s.gpr .r5, 512⟩
    let scr : Region := ⟨s.gpr .r6, 2560⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      ctx.Disjoint key ∧ ctx.Disjoint scr ∧ key.Disjoint scr ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 512 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 2560 ≤ 2 ^ 64 ∧
      ((s.gpr .r4).toNat = 32 ∨ (s.gpr .r4).toNat = 48 ∨ (s.gpr .r4).toNat = 64)
  post s s' := Spec.Siv.KeyRepr s'.mem (s.gpr .r5) (Spec.Aes.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

/-- The precondition, by name: the key `Kp` of `KL` bytes, the context `Ct`
and the scratch buffer `S`. -/
structure IPre (s₀ : State) (Kp Ct S : Addr) (KL : Nat) : Prop where
  r3 : s₀.gpr .r3 = Kp
  r4 : (s₀.gpr .r4).toNat = KL
  r5 : s₀.gpr .r5 = Ct
  r6 : s₀.gpr .r6 = S
  rd : s₀.rd = [⟨Kp, KL⟩]
  wr : s₀.wr = [⟨Ct, 512⟩, ⟨S, 2560⟩]
  ct_k : (⟨Ct, 512⟩ : Region).Disjoint ⟨Kp, KL⟩
  ct_s : (⟨Ct, 512⟩ : Region).Disjoint ⟨S, 2560⟩
  k_s : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 2560⟩
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wCt : Ct.toNat + 512 ≤ 2 ^ 64
  wS : S.toNat + 2560 ≤ 2 ^ 64
  klen : KL = 32 ∨ KL = 48 ∨ KL = 64

theorem IPre.of {s₀ : State} (h : initPPC64LE.pre s₀) :
    IPre s₀ (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r4).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

/-- `r` lies at an offset within `big`. -/
abbrev InAt (r big : Region) : Prop := ∃ off, r.base = big.base + BitVec.ofNat 64 off ∧ off + r.len ≤ big.len

theorem InAt.base {p : Addr} {n k : Nat} (h : n ≤ k) : InAt ⟨p, n⟩ ⟨p, k⟩ := ⟨0, by simp, by simpa using h⟩

theorem InAt.off {p : Addr} {d n k : Nat} (h : d + n ≤ k) : InAt ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

namespace IPre

variable {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL)
include hp

theorem half : KL / 2 = 16 ∨ KL / 2 = 24 ∨ KL / 2 = 32 := by rcases hp.klen with h | h | h <;> omega

theorem rounds : KL / 8 + 6 = 10 ∨ KL / 8 + 6 = 12 ∨ KL / 8 + 6 = 14 := by
  rcases hp.klen with h | h | h <;> omega

theorem sched_le : 16 * (KL / 8 + 6 + 1) ≤ 240 := by rcases hp.klen with h | h | h <;> omega

theorem inS {s : State} (hw : s.wr = s₀.wr) {d : Nat} (h : d + 8 ≤ 2560) : InRegions s.wr (S + BitVec.ofNat 64 d) 8 := by
  rw [hw, hp.wr]; exact ⟨⟨S, 2560⟩, by simp, Offset.contains_base _ h (by have := hp.wS; omega)⟩

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

/-- The memory after saving the registers. -/
abbrev initMem (s₀ : State) (S : Addr) : Mem := Spill.saveMem s₀.mem S (saveG s₀) initSaved

theorem init_bound : ∀ p ∈ initSaved, 2176 ≤ p.2 ∧ p.2 + 8 ≤ 2216 := by decide

/-! ## Before the first call -/

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (s : State) : Prop where
  args : EArgs s Kp Ct S (KL / 2)
  r14 : s.gpr .r14 = Kp
  r15 : s.gpr .r15 = BitVec.ofNat 64 (KL / 2)
  r16 : s.gpr .r16 = Ct
  r17 : s.gpr .r17 = S
  other : ∀ r ∈ preserved, r ≠ .r14 → r ≠ .r15 → r ≠ .r16 → r ≠ .r17 → s.gpr r = s₀.gpr r
  mem : s.mem = initMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initPre_wp {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL) :
    WP isa (.block initPre) s₀ (IMid₁ s₀ Kp Ct S KL) := by
  have hKL : s₀.gpr .r4 = BitVec.ofNat 64 KL := ofNat_toNat_eq hp.r4
  rw [initPre, show initSaved.map (fun (r, d) => Instr.store .d r .r6 d) = Spill.saveCode .r6 initSaved from rfl]
  refine WP.cons exec_mflr (Spill.save_ok (b := .r6) (l := initSaved) (by decide) (by decide)
    (fun p hp' => ?_) ?_)
  · have := init_bound p hp'
    show InRegions s₀.wr (s₀.gpr .r6 + BitVec.ofNat 64 p.2) 8
    rw [hp.r6]; exact hp.inS rfl (by omega)
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
  refine wp_mr fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_mr fun s₄ u₄ =>
    wp_mr fun s₅ u₅ => wp_nil ?_
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, rdt]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, wrt]
  have r15 : s₅.gpr .r15 = BitVec.ofNat 64 (KL / 2) := by
    simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other, gt, hKL]
    exact half_bv hp.klen
  have cv := hp.cover rd₅ wr₅ (rs := [⟨Kp, KL / 2⟩]) (ws := [⟨Ct, 240⟩, ⟨S, 512⟩])
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inl (InAt.base (by omega)))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl (InAt.base (by decide))
      · exact .inr (InAt.base (by decide)))
  refine ⟨?_, by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr, gt, hp.r3], r15,
    by simp (disch := decide) only [u₅.other, u₄.other, u₃.gpr, u₂.other, u₁.other, gt, hp.r5],
    by simp (disch := decide) only [u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other, gt, hp.r6],
    fun r hr h14 h15 h16 h17 => ?_, ?_, rd₅, wr₅⟩
  · exact
    { r3 := by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, gt, hp.r3]
      r4 := by rw [u₅.gpr, ← u₅.other .r15 (by decide), r15]
      r5 := by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, gt, hp.r5]
      r6 := by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, gt, hp.r6]
      klen := hp.half
      kw := hp.ct_k.symm.sub_left (k1Sub Kp KL) |>.sub_right (Region.sub_prefix (by decide))
      ks := (hp.k_s.sub_left (k1Sub Kp KL)).sub_right (Region.sub_prefix (by decide))
      ws := (hp.ct_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      reads := cv.1
      writes := cv.2 }
  · obtain ⟨h0, h3, h4, h5, h6, -⟩ := preserved_ne r hr
    rw [u₅.other _ h4, u₄.other _ h17, u₃.other _ h16, u₂.other _ h15, u₁.other _ h14, gt _ h0]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, memt]

/-! ## Between the calls -/

/-- What the code between the first two calls leaves. -/
structure IMid₂ (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (m : Mem) (s : State) : Prop where
  args : SArgs s Ct (Ct + BitVec.ofNat 64 240) S (KL / 8 + 6)
  r14 : s.gpr .r14 = Kp
  r15 : s.gpr .r15 = BitVec.ofNat 64 (KL / 2)
  r16 : s.gpr .r16 = Ct
  r17 : s.gpr .r17 = S
  keep : ∀ r ∈ preserved, r ≠ .r14 → r ≠ .r15 → r ≠ .r16 → r ≠ .r17 → s.gpr r = s₀.gpr r
  mem : s.mem = m
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The registers the calls keep, and where they are. -/
structure IRegs (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (s : State) : Prop where
  r14 : s.gpr .r14 = Kp
  r15 : s.gpr .r15 = BitVec.ofNat 64 (KL / 2)
  r16 : s.gpr .r16 = Ct
  r17 : s.gpr .r17 = S
  keep : ∀ r ∈ preserved, r ≠ .r14 → r ≠ .r15 → r ≠ .r16 → r ≠ .r17 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem IRegs.call {s₀ s s' : State} {Kp Ct S : Addr} {KL : Nat} (h : IRegs s₀ Kp Ct S KL s)
    (hs : ∀ r ∈ preserved, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    IRegs s₀ Kp Ct S KL s' :=
  ⟨by rw [hs _ (by decide), h.r14], by rw [hs _ (by decide), h.r15], by rw [hs _ (by decide), h.r16],
    by rw [hs _ (by decide), h.r17], fun r hr a b c d => by rw [hs r hr, h.keep r hr a b c d],
    by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

theorem IMid₁.regs {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (h : IMid₁ s₀ Kp Ct S KL s) :
    IRegs s₀ Kp Ct S KL s := ⟨h.r14, h.r15, h.r16, h.r17, h.other, h.rd, h.wr⟩

theorem initMid₁_wp {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL)
    (h : IRegs s₀ Kp Ct S KL s) : WP isa (.block initMid₁) s (IMid₂ s₀ Kp Ct S KL s.mem) := by
  have hw := hp.wCt
  have kCt : Region.Sub ⟨Ct + BitVec.ofNat 64 240, 32⟩ ⟨Ct, 512⟩ := Offset.sub_base Ct (by decide)
  unfold initMid₁ Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ => wp_addi (by decide) (by decide) fun s₃ u₃ =>
    wp_addi (by decide) (by decide) fun s₄ u₄ => wp_mr fun s₅ u₅ => wp_nil ?_
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  have cv := hp.cover rd₅ wr₅ (rs := [⟨Ct, 240⟩]) (ws := [⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩])
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl (InAt.base (by decide))))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl (InAt.off (by decide))
      · exact .inr (InAt.base (by decide)))
  refine ⟨?_, by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.r14],
    by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.r15],
    by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.r16],
    by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.r17],
    fun r hr a b c d => ?_, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], rd₅, wr₅⟩
  · exact
    { r3 := by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr, h.r16]
      r4 := by
        simp (disch := decide) only [u₅.other, u₄.other, u₃.gpr, u₂.gpr, u₁.other, h.r15]
        exact rounds_bv hp.klen
      r5 := by simp (disch := decide) only [u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other, h.r16]
      r6 := by simp (disch := decide) only [u₅.gpr, u₄.other, u₃.other, u₂.other, u₁.other, h.r17]
      rounds := hp.rounds
      wk := Offset.base_disjoint Ct (by decide) (by omega)
      ws := (hp.ct_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      ks := (hp.ct_s.sub_left kCt).sub_right (Region.sub_prefix (by decide))
      wrapK := by rw [toNat_add_lt Ct hw (by decide)]; omega
      wrapS := by have := hp.wS; omega
      reads := cv.1
      writes := cv.2 }
  · obtain ⟨-, h3, h4, h5, h6, -⟩ := preserved_ne r hr
    rw [u₅.other _ h6, u₄.other _ h5, u₃.other _ h4, u₂.other _ h4, u₁.other _ h3, h.keep r hr a b c d]

/-- What the code between the last two calls leaves. -/
structure IMid₃ (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (m : Mem) (s : State) : Prop where
  args : EArgs s (Kp + BitVec.ofNat 64 (KL / 2)) (Ct + BitVec.ofNat 64 272) S (KL / 2)
  r17 : s.gpr .r17 = S
  keep : ∀ r ∈ preserved, r ≠ .r14 → r ≠ .r15 → r ≠ .r16 → r ≠ .r17 → s.gpr r = s₀.gpr r
  mem : s.mem = m
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initMid₂_wp {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL)
    (h : IRegs s₀ Kp Ct S KL s) : WP isa (.block initMid₂) s (IMid₃ s₀ Kp Ct S KL s.mem) := by
  have kCt : Region.Sub ⟨Ct + BitVec.ofNat 64 272, 240⟩ ⟨Ct, 512⟩ := Offset.sub_base Ct (by decide)
  unfold initMid₂ Impl.AesCbc.PPC64LE.mov
  refine wp_add fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_addi (by decide) (by decide) fun s₃ u₃ =>
    wp_mr fun s₄ u₄ => wp_nil ?_
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
  refine ⟨?_, by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h.r17],
    fun r hr a b c d => ?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], rd₄, wr₄⟩
  · exact
    { r3 := by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.gpr, h.r14, h.r15]
      r4 := by simp (disch := decide) only [u₄.other, u₃.other, u₂.gpr, u₁.other, h.r15]
      r5 := by simp (disch := decide) only [u₄.other, u₃.gpr, u₂.other, u₁.other, h.r16]
      r6 := by simp (disch := decide) only [u₄.gpr, u₃.other, u₂.other, u₁.other, h.r17]
      klen := hp.half
      kw := (hp.ct_k.sub_left kCt).symm.sub_left (k2Sub Kp KL)
      ks := (hp.k_s.sub_left (k2Sub Kp KL)).sub_right (Region.sub_prefix (by decide))
      ws := (hp.ct_s.sub_left kCt).sub_right (Region.sub_prefix (by decide))
      reads := cv.1
      writes := cv.2 }
  · obtain ⟨-, h3, h4, h5, h6, -⟩ := preserved_ne r hr
    rw [u₄.other _ h6, u₃.other _ h5, u₂.other _ h4, u₁.other _ h3, h.keep r hr a b c d]

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initPPC64LE.pre s₀) :
    WP isa init s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧
      initPPC64LE.post s₀ s' := by
  have hp := IPre.of h0
  generalize s₀.gpr .r3 = Kp at hp
  generalize s₀.gpr .r5 = Ct at hp
  generalize s₀.gpr .r6 = S at hp
  generalize (s₀.gpr .r4).toNat = KL at hp
  have hw := hp.wCt
  have hsw := hp.wS
  have hkw := hp.wK
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ek_call h₁.args) fun s₂ h₂ => ?_)
  have R₂ := h₁.regs.call h₂.saved h₂.rd h₂.wr
  refine WP.seq (WP.mono (initMid₁_wp hp R₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (sub_call h₃.args) fun s₄ h₄ => ?_)
  have R₄ : IRegs s₀ Kp Ct S KL s₄ :=
    (⟨h₃.r14, h₃.r15, h₃.r16, h₃.r17, h₃.keep, h₃.rd, h₃.wr⟩ : IRegs s₀ Kp Ct S KL s₃).call h₄.saved h₄.rd h₄.wr
  refine WP.seq (WP.mono (initMid₂_wp hp R₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (ek_call h₅.args) fun s₆ h₆ => ?_)
  have r17₆ : s₆.gpr .r17 = S := by rw [h₆.saved _ (by decide), h₅.r17]
  rw [initPost, show initSaved.map (fun (r, d) => Instr.load .d r .r17 d) = Spill.restoreCode .r17 initSaved
    from rfl]
  -- The memory, call by call.
  have f₂ : Frame [⟨Ct, 240⟩, ⟨S, 512⟩] s₁.mem s₂.mem := h₂.frame
  have f₄ : Frame [⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩] s₃.mem s₄.mem := h₄.frame
  have f₆ : Frame [⟨Ct + BitVec.ofNat 64 272, 240⟩, ⟨S, 512⟩] s₅.mem s₆.mem := h₆.frame
  have m₃ : s₃.mem = s₂.mem := h₃.mem
  have m₅ : s₅.mem = s₄.mem := h₅.mem
  -- The saved registers.
  have dSv (r : Region) (hr : r ∈ [⟨Ct, 240⟩, ⟨S, 512⟩, ⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩,
      ⟨Ct + BitVec.ofNat 64 272, 240⟩]) (d : Nat) (hd : 2176 ≤ d) (hd' : d + 8 ≤ 2560) :
      (⟨S + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    have sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 2560⟩ := Offset.sub_base S hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.ct_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base S (by omega) (by omega)
    · exact (hp.ct_s.sub_left (Offset.sub_base Ct (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base S (by omega) (by omega)
    · exact (hp.ct_s.sub_left (Offset.sub_base Ct (by decide))).symm.sub_left sub
  have dSv' (p : Reg × Nat) (hp' : p ∈ initSaved) (r : Region) (hr : r ∈ [⟨Ct, 240⟩, ⟨S, 512⟩,
      ⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩, ⟨Ct + BitVec.ofNat 64 272, 240⟩]) :
      (⟨S + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint r :=
    dSv r hr p.2 (init_bound p hp').1 (by have := init_bound p hp'; omega)
  have sv₁ : Spill.Saved S (saveG s₀) initSaved s₁.mem := by
    rw [h₁.mem]; exact Spill.saveMem_saved (by decide) s₀.mem S _
  have sv₂ := sv₁.frame f₂ fun p hp' r hr => dSv' p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  rw [← m₃] at sv₂
  have sv₄ := sv₂.frame f₄ fun p hp' r hr => dSv' p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  rw [← m₅] at sv₄
  have sv₆ := sv₄.frame f₆ fun p hp' r hr => dSv' p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  refine Spill.restore_ok (b := .r17) (l := initSaved) (by decide) r17₆ (by decide) (by decide)
    (fun p hp' => ?_) sv₆ fun s₇ r₇ => WP.cons exec_mtlr (wp_nil ⟨fun r hr => ?_, ?_, ?_⟩)
  · have := init_bound p hp'
    exact in_wr (hp.inS (by rw [h₆.wr, h₅.wr]) (by omega))
  · show s₇.gpr r = _
    rw [r₇.gpr_of (r := r) ?_, saveG_ne (preserved_ne r hr).1]
    by_cases hv : r = .r14 ∨ r = .r15 ∨ r = .r16 ∨ r = .r17
    · left; rcases hv with rfl | rfl | rfl | rfl <;> decide
    · right
      rw [h₆.saved r hr, h₅.keep r hr (fun e => hv (.inl e)) (fun e => hv (.inr (.inl e)))
        (fun e => hv (.inr (.inr (.inl e)))) (fun e => hv (.inr (.inr (.inr e))))]
      exact (saveG_ne (preserved_ne r hr).1).symm
  · show s₇.gpr .r0 = _
    rw [r₇.gpr (.r0, 2208) (by decide)]; exact saveG_r0 s₀
  · show Spec.Siv.KeyRepr s₇.mem (s₀.gpr .r5) (Spec.Aes.bytesAt s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat)
    rw [hp.r3, hp.r5, hp.r4, r₇.mem]
    -- The key, unchanged until the last call.
    have f₁ : Frame [⟨S + BitVec.ofNat 64 2176, 40⟩] s₀.mem s₁.mem := by
      rw [h₁.mem]
      exact Spill.saveMem_frame (l := initSaved) (lo := 2176) (n := 40) (fun p hp' => init_bound p hp')
        (by omega) s₀.mem S (saveG s₀)
    have dK : ∀ {d n : Nat}, d + n ≤ KL → ∀ r ∈ [⟨S + BitVec.ofNat 64 2176, 40⟩, ⟨Ct, 240⟩, ⟨S, 512⟩,
        ⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩], (⟨Kp + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
      intro d n hd r hr
      have sub : Region.Sub ⟨Kp + BitVec.ofNat 64 d, n⟩ ⟨Kp, KL⟩ := Offset.sub_base Kp hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact (hp.k_s.sub_left sub).sub_right (Offset.sub_base S (by decide))
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
      have := key (d := 0) (n := KL / 2) (by omega)
      rw [BitVec.add_zero] at this
      rw [Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.k_s.sub_left (k1Sub Kp KL)).sub_right (Offset.sub_base S (by decide))) (by omega)]
    have hR := rounds_eq KL
    have hsl := hp.sched_le
    -- `K1`'s schedule, from the first call on.
    have dC1 : ∀ r ∈ [⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩, ⟨Ct + BitVec.ofNat 64 272, 240⟩, ⟨S, 512⟩],
        (⟨Ct, 16 * (KL / 8 + 6 + 1)⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Offset.base_disjoint Ct (by have := hp.sched_le; omega) (by omega)
      · exact (hp.ct_s.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by decide))
      · exact Offset.base_disjoint Ct (by have := hp.sched_le; omega) (by omega)
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

theorem init_rel {s₀ s₀' : State} (h0 : initPPC64LE.pre s₀) (h0' : initPPC64LE.pre s₀')
    (hq : initPPC64LE.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') init fun _ _ => True := by
  obtain ⟨q3, q4, q5, q6, qsp⟩ := hq
  have hp := IPre.of h0
  have hp' : IPre s₀' (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r4).toNat := by
    rw [q3, q4, q5, q6]; exact IPre.of h0'
  generalize s₀.gpr .r3 = Kp at hp hp'
  generalize s₀.gpr .r5 = Ct at hp hp'
  generalize s₀.gpr .r6 = S at hp hp'
  generalize (s₀.gpr .r4).toNat = KL at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6]) (.block initPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r14, .r15, .r16, .r17]) (.block initMid₁) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.r14, .r15, .r16, .r17]) (.block initMid₂) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hD⟩ : ∃ h, (taint.check (Taint.ofRegs [.r17]) (.block initPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  -- What each run keeps between the calls, with its stack pointer.
  let I (σ : State) (s : State) : Prop := IRegs σ Kp Ct S KL s ∧ s.sp = σ.sp
  have regs : ∀ {a b : State}, I s₀ a → I s₀' b → a.sp = b.sp ∧
      ∀ r ∈ ([.r14, .r15, .r16, .r17] : List Reg), a.gpr r = b.gpr r := fun h₁ h₂ => by
    refine ⟨by rw [h₁.2, h₂.2, qsp], fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.1.r14, h₂.1.r14]
    · rw [h₁.1.r15, h₂.1.r15]
    · rw [h₁.1.r16, h₂.1.r16]
    · rw [h₁.1.r17, h₂.1.r17]
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.r3, .r4, .r5, .r6]
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
  have m₁ := (taintRegs (P := fun a b => I s₀ a ∧ I s₀' b) [.r14, .r15, .r16, .r17]
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
      ⟨WP.mono (sub_call h₁.args) fun _ h => ⟨(⟨h₁.r14, h₁.r15, h₁.r16, h₁.r17, h₁.keep, h₁.rd, h₁.wr⟩ :
          IRegs s₀ Kp Ct S KL _).call h.saved h.rd h.wr, by rw [h.sp, sp₁]⟩,
        WP.mono (sub_call h₂.args) fun _ h => ⟨(⟨h₂.r14, h₂.r15, h₂.r16, h₂.r17, h₂.keep, h₂.rd, h₂.wr⟩ :
          IRegs s₀' Kp Ct S KL _).call h.saved h.rd h.wr, by rw [h.sp, sp₂]⟩⟩
  have m₂ := (taintRegs (P := fun a b => I s₀ a ∧ I s₀' b) [.r14, .r15, .r16, .r17]
    (fun a b h => regs h.1 h.2) hC).wp
    (F₁ := fun (s : State) => (∃ m, IMid₃ s₀ Kp Ct S KL m s) ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => (∃ m, IMid₃ s₀' Kp Ct S KL m s) ∧ s.sp = s₀'.sp)
    fun a b h =>
      ⟨WP.mono (wp_sp (initMid₂_wp hp h.1.1)) fun _ h' => ⟨⟨_, h'.1⟩, by rw [h'.2, h.1.2]⟩,
       WP.mono (wp_sp (initMid₂_wp hp' h.2.1)) fun _ h' => ⟨⟨_, h'.1⟩, by rw [h'.2, h.2.2]⟩⟩
  have e₂ := (ek_rel (P := fun a b => ((∃ m, IMid₃ s₀ Kp Ct S KL m a) ∧ a.sp = s₀.sp) ∧
      ((∃ m, IMid₃ s₀' Kp Ct S KL m b) ∧ b.sp = s₀'.sp))
    fun a b ⟨⟨⟨_, h₁⟩, sp₁⟩, ⟨⟨_, h₂⟩, sp₂⟩⟩ => ⟨h₁.args, h₂.args, by rw [sp₁, sp₂, qsp]⟩).wp
    (F₁ := fun (s : State) => s.gpr .r17 = S ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .r17 = S ∧ s.sp = s₀'.sp)
    fun a b ⟨⟨⟨_, h₁⟩, sp₁⟩, ⟨⟨_, h₂⟩, sp₂⟩⟩ =>
      ⟨WP.mono (ek_call h₁.args) fun _ h => ⟨by rw [h.saved _ (by decide), h₁.r17], by rw [h.sp, sp₁]⟩,
        WP.mono (ek_call h₂.args) fun _ h => ⟨by rw [h.saved _ (by decide), h₂.r17], by rw [h.sp, sp₂]⟩⟩
  have p := taintRegs
    (P := fun a b => (a.gpr .r17 = S ∧ a.sp = s₀.sp) ∧ b.gpr .r17 = S ∧ b.sp = s₀'.sp) [.r17]
    (fun a b h => by
      refine ⟨by rw [h.1.2, h.2.2, qsp], fun r hr => ?_⟩
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1, h.2.1]) hD
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((sk.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      ((m₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))))

theorem init_ct : ConstantTime isa initPPC64LE.pre initPPC64LE.pub init :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (init_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem init_correct (s : State) (hs : initPPC64LE.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initPPC64LE.post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := init_wp hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

end VG.Proof.AesSiv.PPC64LE
