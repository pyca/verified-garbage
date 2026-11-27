module

import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Rc2.Scratch
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Rc2.PPC64LE.Stream.Lit
meta import VerifiedGarbage.Proof.Rc2.Scratch
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Impl.Rc2.PPC64LE.Stream
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Lookup
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Rc2.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.Rc2.PPC64LE.Stream
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Lookup
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.KeyVerified
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Rc2.Stream
meta import VerifiedGarbage.Proof.Rc2.Memory
meta import VerifiedGarbage.Proof.Rc2.CbcMemory
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Rc2.PPC64LE.Stream.Verified`, which only this module used -/

section

/-! ### `Rc2.PPC64LE.Stream.Init`, which only this module used -/

section

/-! ### `Rc2.PPC64LE.Stream.Checks`, which only this module used -/

section

/-!
# Streaming RC2-CBC on PPC64LE: `init`'s checks

`checks_run`: `r10` is zero exactly if the lengths are valid, and otherwise
`r3` holds the code of the first invalid one.
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE.Stream

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE.Stream

theorem bne_zero_toNat (y : BitVec 64) : (y != 0#64) = !decide (y.toNat = 0) := by
  have := ofNat_bne_zero (y.isLt)
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

theorem range_bne {x b : Nat} (hx : x < 2 ^ 64) (hb : b < 64) :
    ((BitVec.ofNat 64 x - 1#64) >>> b != 0#64) = !decide (1 ≤ x ∧ x ≤ 2 ^ b) := by
  rw [bne_zero_toNat]
  congr 1
  obtain hp : 2 ^ b ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega_using [hb])
  have hp1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hx]
  apply decide_eq_decide.mpr
  rw [Nat.div_eq_zero_iff]
  by_cases h : x = 0
  · subst h; omega_using [hp, hp1]
  · rw [show (2 ^ 64 - 1 % 2 ^ 64 + x) % 2 ^ 64 = x - 1 by omega_using [hx, h]]; omega_using [hp1, h]

/-- The code `checks` leaves in `r3` for invalid lengths. -/
def errCode (keyLen bits : Nat) : Nat :=
  if ¬(1 ≤ keyLen ∧ keyLen ≤ 128) then 1 else if ¬(1 ≤ bits ∧ bits ≤ 1024) then 2 else 3

/-- Valid lengths. -/
def valid (keyLen bits ivLen : Nat) : Prop := (1 ≤ keyLen ∧ keyLen ≤ 128) ∧ (1 ≤ bits ∧ bits ≤ 1024) ∧ ivLen = 8

instance (a b c : Nat) : Decidable (valid a b c) := by unfold valid; infer_instance

/-- Code without calls or writes of the link register keeps it. -/
theorem WP.keepLr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) (hn : c.noCalls = true)
    (hl : (instrs c).all (fun i => !i.writesLr) = true) : WP isa c s fun t => Q t ∧ t.lr = s.lr := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.lr he hn hl⟩

theorem checks_run (s : State) :
    WP isa checks s fun t => t.mem = s.mem ∧ Keep [.r3, .r10] s t ∧
      (t.gpr .r10 != 0#64) = !decide (valid (s.gpr .r4).toNat (s.gpr .r5).toNat (s.gpr .r7).toNat) ∧
      (¬valid (s.gpr .r4).toNat (s.gpr .r5).toNat (s.gpr .r7).toNat →
        t.gpr .r3 = BitVec.ofNat 64 (errCode (s.gpr .r4).toNat (s.gpr .r5).toNat)) ∧
      (valid (s.gpr .r4).toNat (s.gpr .r5).toNat (s.gpr .r7).toNat → t.gpr .r3 = s.gpr .r3) := by
  obtain e4 := (BitVec.ofNat_toNat 64 (s.gpr .r4)).trans (BitVec.setWidth_eq _)
  obtain e5 := (BitVec.ofNat_toNat 64 (s.gpr .r5)).trans (BitVec.setWidth_eq _)
  obtain e7 := (BitVec.ofNat_toNat 64 (s.gpr .r7)).trans (BitVec.setWidth_eq _)
  unfold checks
  apply WP.seq
  refine WP.mono (WP.keep [.r10] (c := .block [.subi .r10 .r4 1, .lsr .d .r10 .r10 7]) (Q := fun t =>
      t.gpr .r10 = (s.gpr .r4 - 1#64) >>> 7 ∧ t.mem = s.mem) (by rrun)
    (by rfl) rfl) fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  obtain c₁ := range_bne (x := (s.gpr .r4).toNat) (b := 7) (s.gpr .r4).isLt (by decide)
  rw [e4] at c₁
  refine WP.ite _ (by rw [eval_nonzero, a₁, c₁]) (fun h => ?_) (fun h => ?_)
  · have hk : ¬(1 ≤ (s.gpr .r4).toNat ∧ (s.gpr .r4).toNat ≤ 128) := by simp at h; omega_using [h]
    refine WP.mono (WP.keep [.r3] (c := .block [.li .r3 1]) (Q := fun t => t.gpr .r3 = 1#64 ∧ t.mem = t₁.mem)
      (by rrun) (by rfl) rfl) fun t ⟨⟨a, m⟩, k⟩ =>
      ⟨by rw [m, m₁], (k₁.trans k).mono (by simp), ?_, fun _ => ?_, fun hv => absurd hv.1 hk⟩
    · rw [k.gpr (by decide), a₁, c₁]
      simp [valid, hk]
    · rw [a]; simp [errCode, hk]
  · have hk : 1 ≤ (s.gpr .r4).toNat ∧ (s.gpr .r4).toNat ≤ 128 := by simpa using h
    apply WP.seq
    refine WP.mono (WP.keep [.r10] (c := .block [.subi .r10 .r5 1, .lsr .d .r10 .r10 10]) (Q := fun t =>
        t.gpr .r10 = (s.gpr .r5 - 1#64) >>> 10 ∧ t.mem = t₁.mem) (by rrun [k₁.gpr (show Reg.r5 ∉ [Reg.r10] by decide)])
      (by rfl) rfl) fun t₂ ⟨⟨a₂, m₂⟩, k₂⟩ => ?_
    obtain c₂ := range_bne (x := (s.gpr .r5).toNat) (b := 10) (s.gpr .r5).isLt (by decide)
    rw [e5] at c₂
    refine WP.ite _ (by rw [eval_nonzero, a₂, c₂]) (fun h => ?_) (fun h => ?_)
    · have hb : ¬(1 ≤ (s.gpr .r5).toNat ∧ (s.gpr .r5).toNat ≤ 1024) := by simp at h; omega_using [h]
      refine WP.mono (WP.keep [.r3] (c := .block [.li .r3 2]) (Q := fun t => t.gpr .r3 = 2#64 ∧ t.mem = t₂.mem)
        (by rrun) (by rfl) rfl) fun t ⟨⟨a, m⟩, k⟩ =>
        ⟨by rw [m, m₂, m₁], ((k₁.trans k₂).trans k).mono (by simp), ?_, fun _ => ?_, fun hv => absurd hv.2.1 hb⟩
      · rw [k.gpr (by decide), a₂, c₂]
        simp [valid, hb]
      · rw [a]; simp [errCode, hk, hb]
    · have hb : 1 ≤ (s.gpr .r5).toNat ∧ (s.gpr .r5).toNat ≤ 1024 := by simpa using h
      apply WP.seq
      refine WP.mono (WP.keep [.r10] (c := .block [.subi .r10 .r7 8]) (Q := fun t =>
          t.gpr .r10 = s.gpr .r7 - 8#64 ∧ t.mem = t₂.mem)
        (by rrun [k₂.gpr (show Reg.r7 ∉ [Reg.r10] by decide), k₁.gpr (show Reg.r7 ∉ [Reg.r10] by decide)])
        (by rfl) rfl) fun t₃ ⟨⟨a₃, m₃⟩, k₃⟩ => ?_
      obtain c₃ := sub_bne (x := (s.gpr .r7).toNat) (y := 8) (s.gpr .r7).isLt (by decide)
      rw [e7] at c₃
      refine WP.ite _ (by rw [eval_nonzero, a₃, c₃]) (fun h => ?_) (fun h => ?_)
      · have hi : (s.gpr .r7).toNat ≠ 8 := by simpa using h
        refine WP.mono (WP.keep [.r3] (c := .block [.li .r3 3]) (Q := fun t => t.gpr .r3 = 3#64 ∧ t.mem = t₃.mem)
          (by rrun) (by rfl) rfl) fun t ⟨⟨a, m⟩, k⟩ =>
          ⟨by rw [m, m₃, m₂, m₁], (((k₁.trans k₂).trans k₃).trans k).mono (by simp), ?_, fun _ => ?_,
            fun hv => absurd hv.2.2 hi⟩
        · rw [k.gpr (by decide), a₃, c₃]
          simp [valid, hi]
        · rw [a]; simp [errCode, hk, hb]
      · have hi : (s.gpr .r7).toNat = 8 := by simpa using h
        refine WP.block_nil ⟨by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by simp), ?_, fun hv => ?_,
          fun _ => by rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]⟩
        · rw [a₃, c₃]; simp [valid, hk, hb, hi]
        · exact absurd ⟨hk, hb, hi⟩ hv

end VG.Proof.Rc2.PPC64LE.Stream

end

end


/-! # Streaming RC2-CBC on PPC64LE: `init` -/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE.Stream

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE VG.Impl.Rc2.PPC64LE.Stream
open VG.Impl.Rc2.PPC64LE.Cbc (mov)

/-- `init`'s buffers: the key at `K` (`L` bytes), the IV at `V` (`N` bytes),
the context at `C` and the working space at `W`. -/
structure InitPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r3, (s.gpr .r4).toNat⟩, ⟨s.gpr .r6, (s.gpr .r7).toNat⟩]
  wr : s.wr = [⟨s.gpr .r8, 144⟩, ⟨s.gpr .r9, 576⟩]
  kC : (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, 144⟩
  kW : (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint ⟨s.gpr .r9, 576⟩
  vC : (⟨s.gpr .r6, (s.gpr .r7).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, 144⟩
  vW : (⟨s.gpr .r6, (s.gpr .r7).toNat⟩ : Region).Disjoint ⟨s.gpr .r9, 576⟩
  CW : (⟨s.gpr .r8, 144⟩ : Region).Disjoint ⟨s.gpr .r9, 576⟩

theorem expandKey_noFrames : expandKey.noFrames = true := by decide +kernel

theorem initBody_wp (s : State) (h : InitPre s)
    (hv : valid (s.gpr .r4).toNat (s.gpr .r5).toNat (s.gpr .r7).toNat) :
    WP isa initBody s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.lr = s.lr ∧ s'.gpr .r3 = 0#64 ∧
      Spec.Rc2.scheduleAt s'.mem (s.gpr .r8) =
        Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) (s.gpr .r5).toNat ∧
      Spec.Rc2.blockAt s'.mem (s.gpr .r8 + 128) = Spec.Rc2.blockAt s.mem (s.gpr .r6) := by
  obtain ⟨hk, hb, hi⟩ := hv
  obtain ⟨K, hK⟩ : ∃ K, s.gpr .r3 = K := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, s.gpr .r6 = V := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, s.gpr .r8 = C := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, s.gpr .r9 = W := ⟨_, rfl⟩
  obtain hrd := h.rd; have hwr := h.wr; have kC := h.kC; have kW := h.kW; have vC := h.vC; have vW := h.vW
  have CW := h.CW
  simp only [hK, hV, hC, hW] at hrd hwr kC kW vC vW CW
  rw [hK, hC, hV]
  obtain inW : ∀ d, d + 8 ≤ 576 → InRegions s.wr (W + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hwr]; exact ⟨⟨W, 576⟩, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  obtain inC : InRegions s.wr (C + 128) 8 := by
    rw [hwr]; exact ⟨⟨C, 144⟩, by simp, Offset.contains_base C (d := 128) (by omega_arith) (by omega_arith)⟩
  obtain inV : InRegions (s.rd ++ s.wr) V 8 := by
    rw [hrd]; exact ⟨⟨V, (s.gpr .r7).toNat⟩, by simp, by rw [hi]; exact Region.contains_self _ _⟩
  obtain cW : ∀ d, d + 8 ≤ 576 → (⟨W, 576⟩ : Region).Contains (W + BitVec.ofNat 64 d) 8 := fun d hd =>
    Offset.contains_base W hd (by omega_arith)
  obtain W512 := inW 512 (by decide)
  obtain W520 := inW 520 (by decide)
  -- frames
  obtain slot512 : Region.Sub ⟨W + BitVec.ofNat 64 512, 8⟩ ⟨W, 576⟩ := Offset.sub_base W (by omega_arith)
  obtain slot520 : Region.Sub ⟨W + BitVec.ofNat 64 520, 8⟩ ⟨W, 576⟩ := Offset.sub_base W (by omega_arith)
  obtain ivC : Region.Sub ⟨C + 128, 8⟩ ⟨C, 144⟩ := Offset.sub_base C (d := 128) (by omega_arith)
  unfold initBody withLr
  apply WP.seq
  refine WP.mono (WP.keep [.r0, .r25] (c := .block [.mflr .r0, .store .d .r0 .r9 512, .store .d .r25 .r9 520,
      mov .r25 .r9]) (Q := fun t => t.gpr .r25 = W ∧
      t.mem = (s.mem.writeW (W + BitVec.ofNat 64 512) s.lr).writeW (W + BitVec.ofNat 64 520) (s.gpr .r25))
    (by rrun [mov, hW, W512, W520]) (by rfl) rfl)
    fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  obtain F₁ : Frame [⟨W, 576⟩] s.mem t₁.mem := by
    rw [m₁]
    exact ((Frame.refl _ _).writeW (r := ⟨W, 576⟩) (by simp) _ (cW 512 (by decide))).writeW
      (r := ⟨W, 576⟩) (by simp) _ (cW 520 (by decide))
  obtain h6 : t₁.gpr .r6 = V := by rw [k₁.gpr (by decide), hV]
  obtain h8 : t₁.gpr .r8 = C := by rw [k₁.gpr (by decide), hC]
  obtain h9 : t₁.gpr .r9 = W := by rw [k₁.gpr (by decide), hW]
  obtain inV₁ : InRegions (t₁.rd ++ t₁.wr) V 8 := by rw [k₁.2.1, k₁.2.2]; exact inV
  obtain inC₁ : InRegions t₁.wr (C + 128#64) 8 := by rw [k₁.2.2]; exact inC
  apply WP.seq
  apply WP.seq
  refine WP.mono (WP.keep [.r6, .r7, .r10] (c := .block initArgs) (Q := fun t =>
      t.gpr .r6 = C ∧ t.gpr .r7 = W ∧ t.mem = t₁.mem.writeW (C + 128#64) (t₁.mem.readW V 64))
    (by unfold initArgs; rrun [mov, h6, h8, h9, inV₁, inC₁])
    (by rfl) rfl) fun t₂ ⟨⟨a6, a7, m₂⟩, k₂⟩ => ?_
  obtain k12 := k₁.trans k₂
  obtain h3 : t₂.gpr .r3 = K := by rw [k12.gpr (by decide), hK]
  obtain h4 : t₂.gpr .r4 = s.gpr .r4 := k12.gpr (by decide)
  obtain h5 : t₂.gpr .r5 = s.gpr .r5 := k12.gpr (by decide)
  obtain C128 : Region.Sub ⟨C, 128⟩ ⟨C, 144⟩ := Region.sub_prefix (by decide)
  obtain W512r : Region.Sub ⟨W, 512⟩ ⟨W, 576⟩ := Region.sub_prefix (by decide)
  apply WP.seq
  refine WP.call (k := keyC) expandKey_ok (rd := [⟨K, (s.gpr .r4).toNat⟩]) (wr := [⟨C, 128⟩, ⟨W, 512⟩]) ?_ ?_ ?_
    (fun t₃ rd₃ wr₃ _ F₃ P₃ _ post₃ => ?_) expandKey_noFrames
  · simp only [keyC, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr]
    rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
      State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), h3, h4, h5, a6, a7]
    exact ⟨rfl, rfl, kC.sub_right C128, kW.sub_right W512r, (CW.sub_left C128).sub_right W512r, hk.1, hk.2, hb.1, hb.2⟩
  · rw [k12.2.1, k12.2.2, hrd, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨C, 144⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨W, 576⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · rw [k12.2.2, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨C, 144⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨W, 576⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  -- after the call
  refine WP.mono (WP.keep [.r3] (c := .block [.li .r3 0]) (Q := fun t => t.gpr .r3 = 0#64 ∧ t.mem = t₃.mem)
    (by rrun) (by rfl) rfl) fun t₄ ⟨⟨a3, m₄⟩, k₄⟩ => ?_
  obtain h31 : t₄.gpr .r25 = W := by rw [k₄.gpr (by decide), P₃ _ (by decide), k₂.gpr (by decide), a₁]
  obtain F₂ : Frame [⟨C, 144⟩, ⟨W, 576⟩] s.mem t₂.mem := by
    rw [m₂]
    exact (F₁.mono (by simp)).writeW (r := ⟨C, 144⟩) (by simp) _ (Offset.contains_base C (d := 128) (by omega_arith) (by omega_arith))
  -- the slots, apart from the context and the called function's working space
  obtain slot : ∀ d, 512 ≤ d → d + 8 ≤ 576 → t₄.mem.readW (W + BitVec.ofNat 64 d) 64 = t₁.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    intro d hd hd'
    obtain sd : Region.Sub ⟨W + BitVec.ofNat 64 d, 8⟩ ⟨W, 576⟩ := Offset.sub_base W (by omega_arith)
    rw [m₄, F₃.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact (CW.sub_left C128).symm.sub_left sd
      · exact Offset.disjoint_base W (by omega_arith) (by omega_arith)) (by decide), m₂,
      Mem.readW_writeW_sep (((CW.sub_left ivC).symm.sub_left sd).sep (Region.contains_self _ _)
        (Region.contains_self _ _)) (by decide)]
  obtain e512 : t₄.mem.readW (W + 512#64) 64 = s.lr := by
    rw [slot 512 (by decide) (by decide), m₁, Mem.readW_writeW_sep (Offset.sep W (by omega_arith) (by omega_arith) (by omega_arith))
      (by decide), Mem.readW_writeW_self64]
  obtain e520 : t₄.mem.readW (W + 520#64) 64 = s.gpr .r25 := by
    rw [slot 520 (by decide) (by decide), m₁, Mem.readW_writeW_self64]
  obtain rw₄ : t₄.rd = s.rd ∧ t₄.wr = s.wr := ⟨by rw [k₄.2.1, rd₃, k12.2.1], by rw [k₄.2.2, wr₃, k12.2.2]⟩
  obtain in512 : InRegions (t₄.rd ++ t₄.wr) (W + 512#64) 8 := by
    rw [rw₄.1, rw₄.2]; obtain ⟨r, hr, hc⟩ := W512; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain in520 : InRegions (t₄.rd ++ t₄.wr) (W + 520#64) 8 := by
    rw [rw₄.1, rw₄.2]; obtain ⟨r, hr, hc⟩ := W520; exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep [.r0, .r25] (c := .block [.load .d .r0 .r25 512, .mtlr .r0, .load .d .r25 .r25 520])
      (Q := fun t => t.gpr .r25 = s.gpr .r25 ∧ t.lr = s.lr ∧ t.mem = t₄.mem)
    (by rrun [h31, e512, e520, in512, in520]) (by rfl) rfl)
    fun t₅ ⟨⟨a31, lr₅, m₅⟩, k₅⟩ => ⟨fun r hr => ?_, lr₅, by rw [k₅.gpr (by decide), a3], ?_, ?_⟩
  · by_cases h31' : r = .r25
    · subst h31'; exact a31
    · have hn : r ∉ [Reg.r0, .r25, .r6, .r7, .r10] := by revert hr h31'; revert r; decide
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      rw [k₅.gpr (by simp [hn]), k₄.gpr (by simp; intro e; subst e; revert hr; decide), P₃ r hr,
        k12.gpr (by simp [hn])]
  · have hB : Spec.Rc2.bytesAt t₂.mem K (s.gpr .r4).toNat = Spec.Rc2.bytesAt s.mem K (s.gpr .r4).toNat :=
      Proof.Rc2.bytesAt_frame F₂ K _ (by omega_arith) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact kC
        · exact kW)
    have := post₃
    simp only [keyC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem] at this
    rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
      State.callEntry_gpr _ (by decide), a6, h3, h4, h5, hB] at this
    rw [m₅, m₄]; exact this
  · have hiv : Spec.Rc2.blockAt t₃.mem (C + 128#64) = Spec.Rc2.blockAt t₂.mem (C + 128#64) :=
      Proof.Rc2.blockAt_frame F₃ _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact Offset.disjoint_base C (d := 128) (by omega_arith) (by omega_arith)
        · exact (CW.sub_left ivC).sub_right W512r)
    obtain hV₁ : Spec.Rc2.blockAt t₁.mem V = Spec.Rc2.blockAt s.mem V :=
      Proof.Rc2.blockAt_frame F₁ V (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r rfl
        rw [← hi]; exact vW)
    show Spec.Rc2.blockAt t₅.mem (C + 128#64) = _
    rw [m₅, m₄, hiv, m₂, Proof.Rc2.blockAt_store64, ← Proof.Rc2.blockAt_read64, hV₁]

/-- `init`'s postcondition. -/
def initPost (s s' : State) : Prop :=
  ∀ direction, match Spec.Rc2.initWithEffectiveBits
      (Spec.Rc2.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
      (Spec.Rc2.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat) direction (s.gpr .r5).toNat with
    | .ok c => BitVec.setWidth 32 (s'.gpr .r3) = 0 ∧ Spec.Rc2.contextAt s'.mem (s.gpr .r8) direction 0 = c
    | .error e => (BitVec.setWidth 32 (s'.gpr .r3)).toNat = e.code

theorem init_wp (s : State) (h : InitPre s) :
    WP isa init s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.lr = s.lr ∧ initPost s s' := by
  unfold init
  apply WP.seq
  refine WP.mono (WP.keepLr (checks_run s) (by decide) (by rw [← Code.allInstrs_eq]; decide))
    fun t₁ ⟨⟨m₁, k₁, c₁, e₁, v₁⟩, l₁⟩ => ?_
  obtain g : ∀ r, r ∉ [Reg.r3, .r10] → t₁.gpr r = s.gpr r := fun r hr => k₁.gpr hr
  obtain g4 := g .r4 (by decide); have g5 := g .r5 (by decide); have g6 := g .r6 (by decide)
  obtain g7 := g .r7 (by decide); have g8 := g .r8 (by decide); have g9 := g .r9 (by decide)
  refine WP.ite _ (by rw [eval_nonzero, c₁]) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hv : ¬valid (s.gpr .r4).toNat (s.gpr .r5).toNat (s.gpr .r7).toNat := by simpa using hb
    refine ⟨fun r hr => k₁.gpr (by revert hr; revert r; decide), l₁, ?_⟩
    refine Proof.Rc2.init_post_error ?_ hv
    rw [e₁ hv]
    unfold errCode
    split
    · rfl
    · split <;> rfl
  · have hv : valid (s.gpr .r4).toNat (s.gpr .r5).toNat (s.gpr .r7).toNat := by simpa using hb
    obtain g3 := v₁ hv
    obtain h' : InitPre t₁ := by
      obtain ⟨rd, wr, kC, kW, vC, vW, CW⟩ := h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [k₁.2.1, k₁.2.2, g3, g4, g6, g7, g8, g9] <;> with_reducible assumption
    refine WP.mono (initBody_wp t₁ h' (by rw [g4, g5, g7]; exact hv)) fun s' ⟨P, L, r3, S, V⟩ =>
      ⟨fun r hr => by rw [P r hr, k₁.gpr (by revert hr; revert r; decide)], L.trans l₁, ?_⟩
    rw [g3, g4, g5, g8, m₁] at S
    rw [g6, g8, m₁] at V
    exact Proof.Rc2.init_post hv.1 hv.2.1 hv.2.2 (by rw [r3]; rfl) S V

end VG.Proof.Rc2.PPC64LE.Stream

end

end

/-!
# Verified streaming RC2-CBC on PPC64LE

`init` meets the shared contract with their working space as
an argument (`Proof.Rc2.cbcInitScratchContract`),
and, in a frame that allocates the working space and zeroes it after the code
(`Verified.stackScratchWiped`), the contract of `Spec/Rc2/Contract.lean`. The
code uses no other stack.
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE.Stream

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE.Stream

/-- `init`'s contract as the code sees it. -/
def initC : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let iv : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let ctx : Region := ⟨s.gpr .r8, 144⟩
    let scr : Region := ⟨s.gpr .r9, 576⟩
    s.rd = [key, iv] ∧ s.wr = [ctx, scr] ∧ key.Disjoint ctx ∧ key.Disjoint scr ∧ iv.Disjoint ctx ∧
      iv.Disjoint scr ∧ ctx.Disjoint scr
  post s s' := initPost s s'
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.sp = s₂.sp

theorem init_ok (s : State) (hs : initC.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initC.post s s' := by
  obtain ⟨rd, wr, kC, kW, vC, vW, CW⟩ := hs
  obtain ⟨t, s', he, hp, hl, hq⟩ := init_wp s ⟨rd, wr, kC, kW, vC, vW, CW⟩
  exact ⟨t, s', he, ⟨hp, Exec.sp he, hl⟩, hq⟩

theorem agree {pub : State → State → Prop}
    (h : ∀ s₁ s₂, pub s₁ s₂ → s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.sp = s₂.sp) {pre : State → Prop} :
    ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9]) s₁ s₂ := by
  intro s₁ s₂ _ _ hp
  obtain ⟨p3, p4, p5, p6, p7, p8, p9, psp⟩ := h s₁ s₂ hp
  refine ⟨psp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem init_ct : ConstantTime isa initC.pre initC.pub init :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9])
    (agree fun _ _ h => h) (by taint_decide)

def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r6 => 0x2000 | .r8 => 0x3000 | .r9 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 144⟩, ⟨0x4000, 576⟩]

theorem init_verified : Verified target init (Proof.Rc2.cbcInitScratchContract abi) := by
  refine Verified.of_correct (k := initC) init_ok init_ct ?_
  sig_implies [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argRegs,
    initC, initPost] [initSat] using initSat

end VG.Proof.Rc2.PPC64LE.Stream

end

end

/-!
# Streaming RC2-CBC on PPC64LE, with its working space on the stack

`init` runs its code, proved with the working space as an
argument (`Verified.lean`), in a frame of 608 bytes that allocates it
(`Verified.stackScratchWiped`), and zero its 576 bytes before returning.
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE.Stream

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE.Stream

/-- A state satisfying `vg_rc2_cbc_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x3000, 144⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Rc2.cbcInitContract abi 608).pre s := by
  implies_sat [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, Spec.Rc2.cbcInitPost, abi, argRegs]
    [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r9 72 init)
      (Spec.Rc2.cbcInitContract abi 608) :=
  Verified.stackScratchWiped (sig := Spec.Rc2.cbcInitSig) (nm := "scratch") (e := .u64) (n := 72)
    (post := Spec.Rc2.cbcInitPost abi.ptrBits) (wa := true) (stack := 0) (bytes := 608) (words := 72)
    init_verified (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Rc2.cbcInitPost_local _)
    (Proof.Rc2.cbcInitPostOut_local _) initFrameSat_pre

end VG.Proof.Rc2.PPC64LE.Stream
