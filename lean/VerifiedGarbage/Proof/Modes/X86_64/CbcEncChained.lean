module

import VerifiedGarbage.Proof.Modes.X86_64.CbcEncLoop
public import VerifiedGarbage.Proof.Modes.X86_64.FbLoop
import VerifiedGarbage.Proof.Modes.CbcNext
public import VerifiedGarbage.Impl.Modes.X86_64.CbcChained
public import VerifiedGarbage.Proof.Modes.X86_64.Setup
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Modes.CbcEnc
import VerifiedGarbage.Proof.Modes.X86_64.Fb
import VerifiedGarbage.Proof.Modes.X86_64.Ctr
import VerifiedGarbage.Proof.Modes.X86_64.CbcGroup
import VerifiedGarbage.Proof.Modes.X86_64.Words
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep

/-!
# CBC encryption on x86-64 that updates the chaining value, for any core

`cbcEncryptChained_wp`: `c.cbcEncryptChained r` is `c.cbcEncrypt r`
(`cbcEncrypt_wp`), which also replaces the IV at `P` with the last
ciphertext block (`Spec.Cbc.next`): the IV's address stays in `ivX`, which
the core's `prepare` and `crypt` keep (`KeepsIv`, as for OFB and CFB), and
after the last block the buffer, which still holds it (`EDone.last`), is
copied back to the IV. `keepsIv_seq`, `keepsIv_ite` and `keepsIv_loop`
carry `KeepsIv` through the data loop.
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

/-! ## `KeepsIv` of composite code -/

theorem keepsIv_seq {a b : Prog isa} (ha : KeepsIv a) (hb : KeepsIv b) : KeepsIv (.seq a b) := by
  intro s t s' e hz
  cases e with
  | seq e₁ e₂ =>
    have h₁ := ha _ _ _ e₁ hz
    rw [hb _ _ _ e₂ (by rw [h₁]; exact hz), h₁]

theorem keepsIv_ite {cc : Cond} {a b : Prog isa} (ha : KeepsIv a) (hb : KeepsIv b) : KeepsIv (.ite cc a b) := by
  intro s t s' e hz
  cases e with
  | iteT _ e₁ => exact ha _ _ _ e₁ hz
  | iteF _ e₁ => exact hb _ _ _ e₁ hz

theorem keepsIv_loop {b : Prog isa} {cc : Cond} (hb : KeepsIv b) : KeepsIv (.loop b cc) := by
  intro s t s' e
  generalize hp : (Code.loop b cc : Prog isa) = p at e
  induction e with
  | icall | icallNext => cases hp
  | loopExit e₁ _ => cases hp; exact hb _ _ _ e₁
  | loopNext e₁ _ _ _ ih =>
    cases hp
    intro hz
    have h₁ := hb _ _ _ e₁ hz
    rw [ih rfl (by rw [h₁]; exact hz), h₁]
  | block => cases hp
  | seq => cases hp
  | iteT => cases hp
  | iteF => cases hp
  | call => cases hp
  | frame => cases hp

theorem keepsIv_cbcEncBlock {c : Core} (h : KeepsIv c.crypt) : KeepsIv c.cbcEncBlock := by
  have hOut : scalCode (.block c.encOut) = true := by
    simp only [scalCode, Core.encOut, List.all_append, flatMap_scal (copyW_scal _ _ _ _ _), Bool.true_and]; rfl
  exact keepsIv_seq (keepsIv_of_scal (flatMap_scal (copyW_scal _ _ _ _ _) _)) (keepsIv_seq h
    (keepsIv_seq (keepsIv_of_scal hOut) (keepsIv_seq (keepsIv_ite (keepsIv_of_scal rfl)
      (keepsIv_of_scal (flatMap_scal (xorW_scal _ _ _ _ _) _))) (keepsIv_of_scal rfl))))

/-! ## The whole function -/

variable {c : Core}

/-- After the blocks: `EDone`, the IV written as well. -/
structure EDoneC (cs : BlockSpec c) (s₀ : State) (m₀ : Mem) (B P D : Addr) (n : Nat) (k : cs.Key)
    (iv : List Byte) (s : State) : Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  saved : ∀ i < 6, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  data : DInv (8 * c.bw) m₀ s.mem D n n (cbcEncC (8 * c.bw) (cs.cipher k) m₀ D iv)
  frame : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩, ⟨P, 8 * c.bw⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s.mem
  ivOut : bytesAt s.mem P (8 * c.bw) = Spec.Cbc.next iv (Spec.Cbc.encrypt (cs.cipher k) iv (blocksOf (8 * c.bw) m₀ D n))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem cbcEncryptChained_wp (cs : BlockSpec c) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n)
    {s₀ : State} {B P D : Addr} {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B) (hP : s₀.gpr r.ctr = P)
    (hD : s₀.gpr r.data = D) (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.ctrSlots)
    (hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.wr)
    (hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s₀.wr) (sPS : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.ctrSlots⟩)
    (sDS : Region.Disjoint ⟨D, 8 * c.bw * n⟩ ⟨B, 8 * c.ctrSlots⟩)
    (sPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩) (fitD : D.toNat + 8 * c.bw * n ≤ 2 ^ 64)
    (hk : cs.KeyArgs s₀ [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] k)
    (hsc : KeepsIv c.prepare ∧ KeepsIv c.crypt) (hstk : StkOk c s₀ := by exact Or.inl rfl) :
    WP isa (c.cbcEncryptChained r) s₀ fun s' => (∀ x ∈ calleeSaved, s'.gpr x = s₀.gpr x) ∧
      blocksOf (8 * c.bw) s'.mem D n =
        Spec.Cbc.encrypt (cs.cipher k) (bytesAt s₀.mem P (8 * c.bw)) (blocksOf (8 * c.bw) s₀.mem D n) ∧
      bytesAt s'.mem P (8 * c.bw) = Spec.Cbc.next (bytesAt s₀.mem P (8 * c.bw))
        (Spec.Cbc.encrypt (cs.cipher k) (bytesAt s₀.mem P (8 * c.bw)) (blocksOf (8 * c.bw) s₀.mem D n)) ∧
      Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩, ⟨P, 8 * c.bw⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s'.mem ∧
      s'.rd = s₀.rd ∧
      s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG0 := hL.G_pos
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hL0 : 0 < 8 * c.bw := by omega_arith
  have hLG : 8 * c.bw ≤ 8 * c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hGb : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have h8n : 8 * n ≤ 8 * c.bw * n := Nat.mul_le_mul_right n (by omega_arith)
  have hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega_arith
  have hLn : 8 * c.bw * n = 8 * (c.bw * n) := Nat.mul_assoc _ _ _
  have hqr : ∀ {q r}, q < n → r < 8 * c.bw → 8 * c.bw * q + r < 8 * c.bw * n := fun hq hr => by
    have := idx_lt (L := 8 * c.bw) hq; omega_arith
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega_arith
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, db, -, -, -, dsb, dsp, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, lb, -, -, -, lsb, lsp, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  let S : Region := ⟨B, 8 * c.ctrSlots⟩
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  have subMode : Region.Sub (modeRegion c B) S := VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_arith)
  have subT : Region.Sub ⟨T, 8 * c.bw⟩ S := VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_arith)
  have dTP : Region.Disjoint ⟨T, 8 * c.bw⟩ ⟨P, 8 * c.bw⟩ := (sPS.sub_right subT).symm
  have inS : ∀ {d m : Nat}, d + m ≤ 8 * c.ctrSlots → InRegions s₀.wr (B + BitVec.ofNat 64 d) m := fun h =>
    ⟨_, hs.wr, VG.Offset.contains_base B h (by omega_arith)⟩
  -- The entry, and the IV's address to `ivX`.
  obtain ⟨sE, eE, b₁, sv₁, f₁, gE, rdE, wrE⟩ := entry_ok hsm hroom s₀ hB hs
  obtain ⟨s₁, eS, xS, gS, mS, rdS, wrS⟩ := movqX_ok sE Core.ivX r.ctr
  have g₁ : ∀ x, x ≠ sb → s₁.gpr x = s₀.gpr x := fun x h => by rw [gS, gE x h]
  have x₁ : s₁.xmm Core.ivX = (0 : BitVec 64) ++ P := by rw [xS, gE _ hr.ctr.1, hP]
  unfold Core.cbcEncryptChained
  refine WP.seq (WP.of_runBlock ⟨s₁, by rw [runBlock_app, eE, Option.bind_some, eS], ?_⟩)
  have b₁ : s₁.gpr sb = B := by rw [gS, b₁]
  have sv₁ : ∀ i < 6, s₁.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.gpr (Core.savedRegs.getD i .rbx) :=
    fun i hi => by rw [mS, sv₁ i hi]
  have f₁ : Frame [modeRegion c B] s₀.mem s₁.mem := by rw [mS]; exact f₁
  have rd₁ : s₁.rd = s₀.rd := by rw [rdS, rdE]
  have wr₁ : s₁.wr = s₀.wr := by rw [wrS, wrE]
  have sy₁ : s₁.syms = s₀.syms := by rw [runBlock_syms eS, runBlock_syms eE]
  have mP : ∀ u < 8 * c.bw, s₁.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu =>
    f₁.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact sPS.sub_right subMode) (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu
  have mD : ∀ i < 8 * c.bw * n, s₁.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi =>
    f₁.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right subMode) hn64 hi
  -- The IV into the first block.
  obtain ⟨s₂a, e₂a, z₂a, g₂a, m₂a, rd₂a, wr₂a⟩ := testSelf_ok s₁ r.n
  have hz₂ : s₂a.zf = some (decide (n = 0)) := by
    rw [z₂a, g₁ _ hr.n.1]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  let Qw : State → Prop := fun s₂ => s₂.gpr sb = B ∧ (∀ x, x ≠ .rax → s₂.gpr x = s₁.gpr x) ∧ s₂.rd = s₁.rd ∧
    s₂.wr = s₁.wr ∧ Frame [⟨D, 8 * c.bw * n⟩] s₁.mem s₂.mem ∧
    ∀ q < n, ∀ r < 8 * c.bw, s₂.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) =
      if q = 0 then s₀.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) ^^^ s₀.mem (P + BitVec.ofNat 64 r)
      else s₀.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r))
  have hw : WP isa (c.cbcWhiten r) s₁ Qw := by
    unfold Core.cbcWhiten
    refine WP.seq (WP.of_runBlock ⟨s₂a, e₂a, WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₂])
      (fun h0 => ?_) (fun h0 => ?_)⟩)
    · exact WP.block_nil ⟨by rw [g₂a, b₁], fun x _ => by rw [g₂a], rd₂a, wr₂a, by rw [m₂a]; exact Frame.refl _ _,
        fun q hq => by simp at h0; omega_arith⟩
    · have hn0 : 0 < n := by simp at h0; omega_arith
      have sub0 : Region.Sub ⟨D + BitVec.ofNat 64 (8 * c.bw * 0), 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ :=
        VG.Offset.sub_base D (idx_lt hn0)
      refine WP.mono (xorN_wp (k := c.bw) (P := D + BitVec.ofNat 64 (8 * c.bw * 0)) (Q := P)
        ⟨by rw [g₂a, g₁ _ hr.data.1, hD]; simp, by rw [g₂a, g₁ _ hr.ctr.1, hP]; simp, Ne.symm hr.data.2.1,
          Ne.symm hr.ctr.2.1, fun w hw' => ⟨_, by rw [wr₂a, wr₁]; exact hwD, by
            rw [addr_add]
            exact VG.Offset.contains_base D (by have := idx_lt (L := c.bw) hn0; omega_arith) (by omega_arith)⟩,
          fun w hw' => by
            rw [rd₂a, wr₂a, rd₁, wr₁]
            exact inRd ⟨_, hwP, VG.Offset.contains_base P (by omega_arith) (by omega_arith)⟩,
          sPD.symm.sub_left sub0, by omega_arith⟩) fun s₂ h₂ => ?_
      refine ⟨by rw [h₂.regs _ (by decide), g₂a, b₁], fun x hx => by rw [h₂.regs x hx, g₂a], by rw [h₂.rd, rd₂a],
        by rw [h₂.wr, wr₂a], ?_, fun q hq r hr => ?_⟩
      · rw [h₂.mem, m₂a]
        exact (over_frame _ _ _ _).sub fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_singleton_self _, sub0⟩
      rw [h₂.mem, m₂a, over_blk _ _ _ hn0 hq hr hn64]
      split
      · rename_i h; subst h; rw [addr_add, mD _ (hqr hq hr), mP r hr]
      · exact mD _ (hqr hq hr)
  have hwS : scalCode (c.cbcWhiten r) = true := by
    simp only [scalCode, Core.cbcWhiten, Bool.and_eq_true]
    exact ⟨rfl, rfl, flatMap_scal (xorW_scal _ _ _ _ _) _⟩
  refine WP.seq (WP.mono_syms (WP.vecKeep hwS hw) fun s₂ ⟨⟨b₂, g₂, rd₂, wr₂, f₂, d₂⟩, x₂, _⟩ sy₂ => ?_)
  -- The data's address and `n`.
  obtain ⟨s₃, e₃, dr₃, lr₃, g₃, m₃, rd₃, wr₃⟩ := ctrArgs_ok s₂ r hdn hdl
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have x₃ : s₃.xmm Core.ivX = (0 : BitVec 64) ++ P := by rw [runBlock_vec rfl e₃, x₂, x₁]
  have g₃' : ∀ x, x ≠ sb → x ≠ .rax → x ≠ c.dataReg → x ≠ c.leftReg → s₃.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 => by rw [g₃ x h3 h4, g₂ x h2, g₁ x h1]
  have b₃ : s₃.gpr sb = B := by rw [g₃ _ (Ne.symm dsb) (Ne.symm lsb), b₂]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, rd₁]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, wr₁]
  have f₃ : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s₃.mem := by
    rw [m₃]
    exact (f₁.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_cons_self, subMode⟩).trans
      (f₂.sub fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  have kr := keyRegs_ne cs.keyRegs_ok
  have hk₃ : cs.KeyArgs s₃ [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] k :=
    cs.keyArgs_congr hk (fun x hx => g₃' x (kr x hx).1 (kr x hx).2.1 (fun e => dk (e ▸ hx))
      (fun e => lk (e ▸ hx))) rd₃' wr₃'
      (by rw [runBlock_syms e₃, sy₂, sy₁]) f₃
  -- The key.
  refine WP.seq (WP.mono (WP.keepIv hsc.1 (by rw [x₃]; exact hi_zero_append _)
    (cs.prepare_wp b₃ ⟨by rw [wr₃']; exact hs.wr, hs.fit⟩ List.mem_cons_self hk₃))
    fun s₄ ⟨⟨ready₄, b₄, rsp₄, dr₄, lr₄, f₄, rd₄, wr₄⟩, x₄⟩ => ?_)
  rw [show s₃.gpr .rsp = s₀.gpr .rsp from g₃' _ (by decide) (by decide) (Ne.symm dsp) (Ne.symm lsp)] at f₄
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃']
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃']
  -- Any blocks?
  obtain ⟨s₅, e₅, z₅, g₅, m₅, rd₅, wr₅⟩ := testSelf_ok s₄ c.leftReg
  refine WP.seq (WP.of_runBlock ⟨s₅, e₅, ?_⟩)
  have x₅ : s₅.xmm Core.ivX = (0 : BitVec 64) ++ P := by rw [runBlock_vec rfl e₅, x₄, x₃]
  have left₅ : s₅.gpr c.leftReg = s₀.gpr r.n := by
    rw [g₅, lr₄, lr₃, g₂ _ hr.n.2.1, g₁ _ hr.n.1]
  have hz₅ : s₅.zf = some (decide (n = 0)) := by
    rw [z₅, ← g₅, left₅]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  have mem₅ : s₅.mem = s₄.mem := m₅
  have b₅ : s₅.gpr sb = B := by rw [g₅, b₄]
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by
    rw [g₅, rsp₄, g₃' _ (by decide) (by decide) (Ne.symm dsp) (Ne.symm lsp)]
  have rd₅' : s₅.rd = s₀.rd := by rw [rd₅, rd₄']
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄']
  let iv := bytesAt s₀.mem P (8 * c.bw)
  have hiv : iv.length = 8 * c.bw := by simp [iv, bytesAt]
  have hp : GPre c s₅ B D n (8 * c.bw) :=
    ⟨⟨by rw [wr₅']; exact hs.wr, hs.fit⟩, by rw [wr₅']; exact hwD, sDS, fitD, hstk.congr rsp₅ wr₅'⟩
  have dCore : ∀ x ∈ coreFrame c B (s₀.gpr .rsp), Region.Disjoint ⟨D, 8 * c.bw * n⟩ x :=
    hstk.coreFrame_disj (sDS.sub_right (Region.sub_prefix (by simp only [Core.ctrSlots]; omega_arith)))
      ⟨_, hwD, fun _ h => h⟩
  -- The IV as it was before the loop.
  have m₅P : ∀ u < 8 * c.bw, s₅.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu => by
    rw [mem₅, f₄.bytes (R := ⟨P, 8 * c.bw⟩) (hstk.coreFrame_disj
        (sPS.sub_right (Region.sub_prefix (by simp only [Core.ctrSlots]; omega_arith))) ⟨_, hwP, fun _ h => h⟩)
        (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu]
    exact f₃.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact sPS
        · exact sPD) (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu
  -- The blocks, and the last back to the IV.
  refine WP.seq (WP.mono (M := isa) (Q := EDoneC cs s₅ s₀.mem B P D n k iv)
    (WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₅]) (fun h0 => ?_) (fun h0 => ?_)) fun s₆ d₆ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    subst hn0
    refine WP.block_nil ⟨b₅, rfl, fun _ _ => rfl, fun i hi' => by rw [Nat.mul_zero] at hi'; omega_arith,
      Frame.refl _ _, ?_, rfl, rfl⟩
    rw [show blocksOf (8 * c.bw) s₀.mem D 0 = [] from rfl, show Spec.Cbc.encrypt (cs.cipher k) iv [] = [] from rfl,
      next_nil]
    exact bytesAt_of_getD hiv fun u hu => by rw [m₅P u hu]; exact (bytesAt_getD _ _ hu).symm
  · have hn0 : n ≠ 0 := by simpa using h0
    refine WP.seq (WP.mono (WP.keepIv (keepsIv_loop (keepsIv_cbcEncBlock hsc.2)) (by rw [x₅]; exact hi_zero_append _)
      (cbcEncLoop_wp cs (m₀ := s₀.mem) hiv hp ⟨b₅, rfl, cs.ready_frame ready₄ (by rw [mem₅]; exact Frame.refl [] _)
        (fun _ h => by simp at h) ⟨fun _ h => by simp at h, rd₅, wr₅, runBlock_syms e₅⟩ (fun r _ => by rw [g₅]),
        fun _ _ => rfl, ?_, ?_, by omega_arith, fun q hq r hr => ?_, Frame.refl _ _, rfl, rfl⟩))
      fun s₆ ⟨d₆, x₆⟩ => ?_)
    · rw [g₅, dr₄, dr₃, g₂ _ hr.data.2.1, g₁ _ hr.data.1, hD]; simp
    · rw [left₅, Nat.sub_zero, ← hn]; simp
    · rw [mem₅, f₄.bytes (R := ⟨D, 8 * c.bw * n⟩) dCore hn64 (hqr hq hr), m₃, d₂ q hq r hr, encByte,
        ite_eq_right (Nat.not_lt_zero _)]
      split
      · rw [cbcEncPrev, ite_eq_left rfl, bytesAt_getD _ _ hr]
      · rfl
    -- The buffer, the last ciphertext block, back to the IV.
    have rd₆ : s₆.rd = s₀.rd := by rw [d₆.rd, rd₅']
    have wr₆ : s₆.wr = s₀.wr := by rw [d₆.wr, wr₅']
    obtain ⟨s₇a, e₇a, ax₇a, o₇a, m₇a, rd₇a, wr₇a, -⟩ := movqR_ok s₆ .rax Core.ivX
    have ax₇ : s₇a.gpr .rax = P := by rw [ax₇a, x₆, x₅, extract_zero_append]
    refine WP.block_append (WP.of_runBlock ⟨s₇a, e₇a, WP.mono (copyN_wp (k := c.bw)
      (t := .rbp) (rd := .rax) (rs := sb) (od := 0) (os := 8 * c.buf) (P := P) (Q := T)
      ⟨by rw [ax₇]; simp, by rw [o₇a _ (by decide), d₆.base], by decide, by decide,
        fun w hw => by rw [wr₇a, wr₆]; exact ⟨_, hwP, VG.Offset.contains_base P (by omega_arith) (by omega_arith)⟩,
        fun w hw => by
          rw [rd₇a, wr₇a, rd₆, wr₆, addr_add]
          exact inRd (inS (by simp only [Core.ctrSlots]; omega_arith)),
        dTP.symm, by omega_arith⟩) fun s₇ h₇ => ?_⟩)
    have mem₇ : s₇.mem = over s₆.mem P (8 * c.bw) fun i => s₆.mem (T + BitVec.ofNat 64 i) := by rw [h₇.mem, m₇a]
    have f₇ : Frame [⟨P, 8 * c.bw⟩] s₆.mem s₇.mem := by rw [mem₇]; exact over_frame _ _ _ _
    refine ⟨by rw [h₇.regs _ (by decide), o₇a _ (by decide), d₆.base],
      by rw [h₇.regs _ (by decide), o₇a _ (by decide), d₆.rsp], fun i hi => ?_, fun i hi => ?_, ?_, ?_,
      by rw [h₇.rd, rd₇a, d₆.rd], by rw [h₇.wr, wr₇a, d₆.wr]⟩
    · rw [← d₆.saved i hi]
      exact f₇.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact (sPS.sub_right (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.ctrSlots by
          simp only [Core.ctrSlots]; omega_arith))).symm) (by decide)
    · rw [f₇.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact sPD.symm) hn64 hi]
      exact d₆.data i hi
    · exact (d₆.frame.mono fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_append_right _ hx).trans
        (f₇.mono fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · rw [next_encrypt _ _ _ _ hn0]
      refine bytesAt_of_getD (by generalize n - 1 = t; cases t <;> exact cs.cipher_len k _) fun u hu => ?_
      rw [mem₇, over_at hu (by omega_arith)]
      exact d₆.last hn0 u hu
  -- The exit.
  have hsv : ∀ i < 6, Core.savedRegs.getD i .rbx ≠ sb := by decide
  have hinj : ∀ i < 6, ∀ j < 6, Core.savedRegs.getD i .rbx = Core.savedRegs.getD j .rbx → i = j := by decide
  obtain ⟨s₈, e₈, v₈, o₈, m₈, rd₈, wr₈⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .rbx) 6 s₆
    d₆.base hsv hinj (fun i hi' => by
      rw [d₆.rd, d₆.wr, rd₅', wr₅']
      exact inRd (slot_wr hs.wr hN (by simp only [Core.ctrSlots]; omega_arith)))
  refine WP.of_runBlock ⟨s₈, e₈, fun x hx => ?_, ?_, ?_, ?_, by rw [rd₈, d₆.rd, rd₅'], by rw [wr₈, d₆.wr, wr₅']⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
    have hsaved : ∀ i < 6, s₈.gpr (Core.savedRegs.getD i .rbx) = s₀.gpr (Core.savedRegs.getD i .rbx) :=
      fun i hi' => by
        rw [v₈ i hi', d₆.saved i hi', mem₅, ← sv₁ i hi']
        refine (f₄.readW (Region.contains_self _ _) (hstk.coreFrame_disj
          (VG.Offset.disjoint_base B (by omega_arith) (by omega_arith)) ⟨_, hs.wr, VG.Offset.sub_base B
            (show 8 * (c.slots + i) + 8 ≤ 8 * c.ctrSlots by simp only [Core.ctrSlots]; omega_arith)⟩) (by decide)).trans ?_
        rw [m₃]
        exact f₂.readW (Region.contains_self _ _) (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx
          exact (sDS.sub_right (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.ctrSlots by
            simp only [Core.ctrSlots]; omega_arith))).symm) (by decide)
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved 0 (by decide)
    · exact hsaved 1 (by decide)
    · rw [o₈ _ (fun i hi' => by revert i; decide), d₆.rsp, rsp₅]
    · exact hsaved 2 (by decide)
    · exact hsaved 3 (by decide)
    · exact hsaved 4 (by decide)
    · exact hsaved 5 (by decide)
  · rw [m₈]; exact cbcEnc_of_dinv (cs.cipher_len k) d₆.data
  · rw [m₈]; exact d₆.ivOut
  · rw [m₈]
    refine ((((f₃.mono fun x hx => List.mem_append_left _ hx).trans
      (f₄.sub (coreFrame_sub (rs := [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩]) ⟨_, List.mem_cons_self,
        Region.sub_prefix (by simp only [Core.ctrSlots]; omega_arith)⟩))).mono fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_append_right _ hx)).trans ?_
    rw [← mem₅, ← rsp₅]
    exact d₆.frame

end VG.Proof.Modes.X86_64
