module

public import VerifiedGarbage.Impl.Rc2.RISCV64.Stream
public import VerifiedGarbage.Proof.Rc2.RISCV64.Run
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
public import VerifiedGarbage.Proof.Rc2.RISCV64.KeyVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Io
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Rc2.RISCV64.Lit

/-! ### `Rc2.RISCV64.Stream.Checks`, which only this module used -/

section

/-!
# Streaming RC2-CBC on RISCV64: `init`'s checks

`checks_run`: `t0` is zero exactly if the lengths are valid, and otherwise
`a0` holds the code of the first invalid one.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Stream

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64.Stream

theorem bne_zero_toNat (y : BitVec 64) : (y != (0 : BitVec 64)) = !decide (y.toNat = 0) := by
  have := ofNat_bne_zero' (y.isLt)
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

theorem range_bne {x b : Nat} (hx : x < 2 ^ 64) (hb : b < 64) :
    ((BitVec.ofNat 64 x - 1#64) >>> b != (0 : BitVec 64)) = !decide (1 ≤ x ∧ x ≤ 2 ^ b) := by
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

/-- The code `checks` leaves in `a0` for invalid lengths. -/
def errCode (keyLen bits : Nat) : Nat :=
  if ¬(1 ≤ keyLen ∧ keyLen ≤ 128) then 1 else if ¬(1 ≤ bits ∧ bits ≤ 1024) then 2 else 3

/-- Valid lengths. -/
def valid (keyLen bits ivLen : Nat) : Prop := (1 ≤ keyLen ∧ keyLen ≤ 128) ∧ (1 ≤ bits ∧ bits ≤ 1024) ∧ ivLen = 8

instance (a b c : Nat) : Decidable (valid a b c) := by unfold valid; infer_instance

theorem checks_run (s : State) :
    WP isa checks s fun t => t.mem = s.mem ∧ Keep [.a0, .t0] s t ∧
      (t.gpr .t0 != (0 : BitVec 64)) = !decide (valid (s.gpr .a1).toNat (s.gpr .a2).toNat (s.gpr .a4).toNat) ∧
      (¬valid (s.gpr .a1).toNat (s.gpr .a2).toNat (s.gpr .a4).toNat →
        t.gpr .a0 = BitVec.ofNat 64 (errCode (s.gpr .a1).toNat (s.gpr .a2).toNat)) ∧
      (valid (s.gpr .a1).toNat (s.gpr .a2).toNat (s.gpr .a4).toNat → t.gpr .a0 = s.gpr .a0) := by
  obtain e4 := (BitVec.ofNat_toNat 64 (s.gpr .a1)).trans (BitVec.setWidth_eq _)
  obtain e5 := (BitVec.ofNat_toNat 64 (s.gpr .a2)).trans (BitVec.setWidth_eq _)
  obtain e7 := (BitVec.ofNat_toNat 64 (s.gpr .a4)).trans (BitVec.setWidth_eq _)
  unfold checks
  apply WP.seq
  refine WP.mono (WP.keep [.t0] (c := .block [.addi .t0 .a1 (-1), .shift .srl .d .t0 .t0 7]) (Q := fun t =>
      t.gpr .t0 = (s.gpr .a1 - 1#64) >>> 7 ∧ t.mem = s.mem) (by rrun)
    (by rfl) rfl) fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  obtain c₁ := range_bne (x := (s.gpr .a1).toNat) (b := 7) (s.gpr .a1).isLt (by decide)
  rw [e4] at c₁
  refine WP.ite _ (by rw [Steps.eval_nonzero, a₁, c₁]) (fun h => ?_) (fun h => ?_)
  · have hk : ¬(1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 128) := by simp at h; omega_using [h]
    refine WP.mono (WP.keep [.a0] (c := .block [.li .a0 1]) (Q := fun t => t.gpr .a0 = 1#64 ∧ t.mem = t₁.mem)
      (by rrun) (by rfl) rfl) fun t ⟨⟨a, m⟩, k⟩ =>
      ⟨by rw [m, m₁], (k₁.trans k).mono (by simp), ?_, fun _ => ?_, fun hv => absurd hv.1 hk⟩
    · rw [k.gpr (by decide), a₁, c₁]
      simp [valid, hk]
    · rw [a]; simp [errCode, hk]
  · have hk : 1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 128 := by simpa using h
    apply WP.seq
    refine WP.mono (WP.keep [.t0] (c := .block [.addi .t0 .a2 (-1), .shift .srl .d .t0 .t0 10]) (Q := fun t =>
        t.gpr .t0 = (s.gpr .a2 - 1#64) >>> 10 ∧ t.mem = t₁.mem) (by rrun [k₁.gpr (show Reg.a2 ∉ [Reg.t0] by decide)])
      (by rfl) rfl) fun t₂ ⟨⟨a₂, m₂⟩, k₂⟩ => ?_
    obtain c₂ := range_bne (x := (s.gpr .a2).toNat) (b := 10) (s.gpr .a2).isLt (by decide)
    rw [e5] at c₂
    refine WP.ite _ (by rw [Steps.eval_nonzero, a₂, c₂]) (fun h => ?_) (fun h => ?_)
    · have hb : ¬(1 ≤ (s.gpr .a2).toNat ∧ (s.gpr .a2).toNat ≤ 1024) := by simp at h; omega_using [h]
      refine WP.mono (WP.keep [.a0] (c := .block [.li .a0 2]) (Q := fun t => t.gpr .a0 = 2#64 ∧ t.mem = t₂.mem)
        (by rrun) (by rfl) rfl) fun t ⟨⟨a, m⟩, k⟩ =>
        ⟨by rw [m, m₂, m₁], ((k₁.trans k₂).trans k).mono (by simp), ?_, fun _ => ?_, fun hv => absurd hv.2.1 hb⟩
      · rw [k.gpr (by decide), a₂, c₂]
        simp [valid, hb]
      · rw [a]; simp [errCode, hk, hb]
    · have hb : 1 ≤ (s.gpr .a2).toNat ∧ (s.gpr .a2).toNat ≤ 1024 := by simpa using h
      apply WP.seq
      refine WP.mono (WP.keep [.t0] (c := .block [.addi .t0 .a4 (-8)]) (Q := fun t =>
          t.gpr .t0 = s.gpr .a4 - 8#64 ∧ t.mem = t₂.mem)
        (by rrun [k₂.gpr (show Reg.a4 ∉ [Reg.t0] by decide), k₁.gpr (show Reg.a4 ∉ [Reg.t0] by decide)])
        (by rfl) rfl) fun t₃ ⟨⟨a₃, m₃⟩, k₃⟩ => ?_
      obtain c₃ := sub_bne (x := (s.gpr .a4).toNat) (y := 8) (s.gpr .a4).isLt (by decide)
      rw [e7] at c₃
      refine WP.ite _ (by rw [Steps.eval_nonzero, a₃, c₃]) (fun h => ?_) (fun h => ?_)
      · have hi : (s.gpr .a4).toNat ≠ 8 := by simpa using h
        refine WP.mono (WP.keep [.a0] (c := .block [.li .a0 3]) (Q := fun t => t.gpr .a0 = 3#64 ∧ t.mem = t₃.mem)
          (by rrun) (by rfl) rfl) fun t ⟨⟨a, m⟩, k⟩ =>
          ⟨by rw [m, m₃, m₂, m₁], (((k₁.trans k₂).trans k₃).trans k).mono (by simp), ?_, fun _ => ?_,
            fun hv => absurd hv.2.2 hi⟩
        · rw [k.gpr (by decide), a₃, c₃]
          simp [valid, hi]
        · rw [a]; simp [errCode, hk, hb]
      · have hi : (s.gpr .a4).toNat = 8 := by simpa using h
        refine WP.block_nil ⟨by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by simp), ?_, fun hv => ?_,
          fun _ => by rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]⟩
        · rw [a₃, c₃]; simp [valid, hk, hb, hi]
        · exact absurd ⟨hk, hb, hi⟩ hv

end VG.Proof.Rc2.RISCV64.Stream

end

end


/-! # Streaming RC2-CBC on RISCV64: `init` -/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Stream

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64 VG.Impl.Rc2.RISCV64.Stream
open VG.Impl.Rc2.RISCV64.Cbc (mov)

/-- `init`'s buffers: the key at `K` (`L` bytes), the IV at `V` (`N` bytes),
the context at `C` and the working space at `W`. -/
structure InitPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, (s.gpr .a1).toNat⟩, ⟨s.gpr .a3, (s.gpr .a4).toNat⟩]
  wr : s.wr = [⟨s.gpr .a5, 144⟩, ⟨s.gpr .a6, 576⟩]
  al : (s.gpr .a6).toNat % 8 = 0
  kC : (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint ⟨s.gpr .a5, 144⟩
  kW : (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint ⟨s.gpr .a6, 576⟩
  vC : (⟨s.gpr .a3, (s.gpr .a4).toNat⟩ : Region).Disjoint ⟨s.gpr .a5, 144⟩
  vW : (⟨s.gpr .a3, (s.gpr .a4).toNat⟩ : Region).Disjoint ⟨s.gpr .a6, 576⟩
  CW : (⟨s.gpr .a5, 144⟩ : Region).Disjoint ⟨s.gpr .a6, 576⟩

theorem expandKey_noFrames : expandKey.noFrames = true := by lit_decide

theorem initArgs_run (t₁ : State) {V C W : Addr} (h6 : t₁.gpr .a3 = V) (h8 : t₁.gpr .a5 = C)
    (h9 : t₁.gpr .a6 = W) (inV₁ : InRegions (t₁.rd ++ t₁.wr) V 8) (inC₁ : InRegions t₁.wr (C + 128#64) 8) :
    WP isa (.block initArgs) t₁ fun t => t.gpr .a3 = C ∧ t.gpr .a4 = W ∧
      t.mem = t₁.mem.writeW (C + 128#64) (t₁.mem.readW V 64) ∧ Keep [.t0, .a7, .t1, .t2, .a3, .a4] t₁ t := by
  unfold initArgs
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (Cbc.load64_run (d := .t0) (n := .a3) (p := V) (by decide) (by decide) (by decide) (by decide)
    (by decide) t₁ h6 inV₁) fun u₁ ⟨v₁, mu₁, ku₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t2] (c := .block [.addi .t2 .a5 128]) (Q := fun u => u.gpr .t2 = C + 128#64 ∧
      u.mem = u₁.mem) (by rrun [ku₁.gpr (show Reg.a5 ∉ [Reg.t0, .a7, .t1] by decide), h8]) (by rfl) rfl)
    fun u₂ ⟨⟨v₂, mu₂⟩, ku₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Cbc.store64_run (v := .t0) (n := .t2) (p := C + 128#64) (by decide) (by decide) (by decide) u₂ v₂
    (by rw [ku₂.2.2, ku₁.2.2]; exact inC₁)) fun u₃ ⟨mu₃, ku₃⟩ => ?_
  obtain k₃ := (ku₁.trans ku₂).trans ku₃
  obtain g5 : u₃.gpr .a5 = C := by rw [k₃.gpr (by decide), h8]
  obtain g6 : u₃.gpr .a6 = W := by rw [k₃.gpr (by decide), h9]
  refine WP.mono (WP.keep [.a3, .a4] (c := .block [mov .a3 .a5, mov .a4 .a6]) (Q := fun t => t.gpr .a3 = C ∧
      t.gpr .a4 = W ∧ t.mem = u₃.mem) (by rrun [mov, g5, g6]) (by rfl) rfl) fun t ⟨⟨a, b, m⟩, k⟩ =>
      ⟨a, b, ?_, (k₃.trans k).mono (by simp)⟩
  rw [m, mu₃, ku₂.gpr (by decide), v₁, mu₂, mu₁]

theorem initBody_wp (s : State) (h : InitPre s)
    (hv : valid (s.gpr .a1).toNat (s.gpr .a2).toNat (s.gpr .a4).toNat) :
    WP isa initBody s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.gpr .ra = s.gpr .ra ∧
      s'.gpr .a0 = 0#64 ∧
      Spec.Rc2.scheduleAt s'.mem (s.gpr .a5) =
        Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) (s.gpr .a2).toNat ∧
      Spec.Rc2.blockAt s'.mem (s.gpr .a5 + 128) = Spec.Rc2.blockAt s.mem (s.gpr .a3) := by
  obtain ⟨hk, hb, hi⟩ := hv
  obtain ⟨K, hK⟩ : ∃ K, s.gpr .a0 = K := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, s.gpr .a3 = V := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, s.gpr .a5 = C := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, s.gpr .a6 = W := ⟨_, rfl⟩
  obtain hrd := h.rd; have hwr := h.wr; have kC := h.kC; have kW := h.kW; have vC := h.vC; have vW := h.vW
  obtain CW := h.CW; have hal := h.al
  simp only [hK, hV, hC, hW] at hrd hwr kC kW vC vW CW hal
  rw [hK, hC, hV]
  obtain inW : ∀ d, d + 8 ≤ 576 → InRegions s.wr (W + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hwr]; exact ⟨⟨W, 576⟩, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  obtain inC : InRegions s.wr (C + 128) 8 := by
    rw [hwr]; exact ⟨⟨C, 144⟩, by simp, Offset.contains_base C (d := 128) (by omega_arith) (by omega_arith)⟩
  obtain inV : InRegions (s.rd ++ s.wr) V 8 := by
    rw [hrd]; exact ⟨⟨V, (s.gpr .a4).toNat⟩, by simp, by rw [hi]; exact Region.contains_self _ _⟩
  obtain cW : ∀ d, d + 8 ≤ 576 → (⟨W, 576⟩ : Region).Contains (W + BitVec.ofNat 64 d) 8 := fun d hd =>
    Offset.contains_base W hd (by omega_arith)
  obtain W512 := inW 512 (by decide)
  obtain W520 := inW 520 (by decide)
  -- frames
  obtain slot512 : Region.Sub ⟨W + BitVec.ofNat 64 512, 8⟩ ⟨W, 576⟩ := Offset.sub_base W (by omega_arith)
  obtain slot520 : Region.Sub ⟨W + BitVec.ofNat 64 520, 8⟩ ⟨W, 576⟩ := Offset.sub_base W (by omega_arith)
  obtain ivC : Region.Sub ⟨C + 128, 8⟩ ⟨C, 144⟩ := Offset.sub_base C (d := 128) (by omega_arith)
  obtain al512 := Spill.al8 hal (d := 512) (by decide)
  obtain al520 := Spill.al8 hal (d := 520) (by decide)
  unfold initBody withRa
  apply WP.seq
  refine WP.mono (WP.keep [.s7] (c := .block [.store .d .ra .a6 512, .store .d .s7 .a6 520, mov .s7 .a6])
      (Q := fun t => t.gpr .s7 = W ∧
      t.mem = (s.mem.writeW (W + BitVec.ofNat 64 512) (s.gpr .ra)).writeW (W + BitVec.ofNat 64 520) (s.gpr .s7))
    (by rrun [mov, hW, W512, W520, al512, al520]) (by rfl) rfl)
    fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  obtain F₁ : Frame [⟨W, 576⟩] s.mem t₁.mem := by
    rw [m₁]
    exact ((Frame.refl _ _).writeW (r := ⟨W, 576⟩) (by simp) _ (cW 512 (by decide))).writeW
      (r := ⟨W, 576⟩) (by simp) _ (cW 520 (by decide))
  obtain h6 : t₁.gpr .a3 = V := by rw [k₁.gpr (by decide), hV]
  obtain h8 : t₁.gpr .a5 = C := by rw [k₁.gpr (by decide), hC]
  obtain h9 : t₁.gpr .a6 = W := by rw [k₁.gpr (by decide), hW]
  obtain inV₁ : InRegions (t₁.rd ++ t₁.wr) V 8 := by rw [k₁.2.1, k₁.2.2]; exact inV
  obtain inC₁ : InRegions t₁.wr (C + 128#64) 8 := by rw [k₁.2.2]; exact inC
  apply WP.seq
  apply WP.seq
  refine WP.mono (initArgs_run t₁ h6 h8 h9 inV₁ inC₁) fun t₂ ⟨a6, a7, m₂, k₂⟩ => ?_
  obtain k12 := k₁.trans k₂
  obtain h3 : t₂.gpr .a0 = K := by rw [k12.gpr (by decide), hK]
  obtain h4 : t₂.gpr .a1 = s.gpr .a1 := k12.gpr (by decide)
  obtain h5 : t₂.gpr .a2 = s.gpr .a2 := k12.gpr (by decide)
  obtain C128 : Region.Sub ⟨C, 128⟩ ⟨C, 144⟩ := Region.sub_prefix (by decide)
  obtain W512r : Region.Sub ⟨W, 512⟩ ⟨W, 576⟩ := Region.sub_prefix (by decide)
  apply WP.seq
  refine WP.call (k := keyC) (expandKey_ok (by lit_decide) (by lit_decide)) (rd := [⟨K, (s.gpr .a1).toNat⟩]) (wr := [⟨C, 128⟩, ⟨W, 512⟩]) ?_ ?_ ?_
    (fun t₃ rd₃ wr₃ _ F₃ P₃ _ post₃ => ?_) expandKey_noFrames
  · simp only [keyC, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr]
    rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
      State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), h3, h4, h5, a6, a7]
    exact ⟨rfl, rfl, hal, kC.sub_right C128, kW.sub_right W512r, (CW.sub_left C128).sub_right W512r, hk.1, hk.2,
      hb.1, hb.2⟩
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
  refine WP.mono (WP.keep [.a0] (c := .block [.li .a0 0]) (Q := fun t => t.gpr .a0 = 0#64 ∧ t.mem = t₃.mem)
    (by rrun) (by rfl) rfl) fun t₄ ⟨⟨a3, m₄⟩, k₄⟩ => ?_
  obtain h31 : t₄.gpr .s7 = W := by rw [k₄.gpr (by decide), P₃ _ (by decide), k₂.gpr (by decide), a₁]
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
  obtain e512 : t₄.mem.readW (W + 512#64) 64 = s.gpr .ra := by
    rw [slot 512 (by decide) (by decide), m₁, Mem.readW_writeW_sep (Offset.sep W (by omega_arith) (by omega_arith) (by omega_arith))
      (by decide), Mem.readW_writeW_self64]
  obtain e520 : t₄.mem.readW (W + 520#64) 64 = s.gpr .s7 := by
    rw [slot 520 (by decide) (by decide), m₁, Mem.readW_writeW_self64]
  obtain rw₄ : t₄.rd = s.rd ∧ t₄.wr = s.wr := ⟨by rw [k₄.2.1, rd₃, k12.2.1], by rw [k₄.2.2, wr₃, k12.2.2]⟩
  obtain in512 : InRegions (t₄.rd ++ t₄.wr) (W + 512#64) 8 := by
    rw [rw₄.1, rw₄.2]; obtain ⟨r, hr, hc⟩ := W512; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain in520 : InRegions (t₄.rd ++ t₄.wr) (W + 520#64) 8 := by
    rw [rw₄.1, rw₄.2]; obtain ⟨r, hr, hc⟩ := W520; exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep [.ra, .s7] (c := .block [.load .d .ra .s7 512, .load .d .s7 .s7 520])
      (Q := fun t => t.gpr .s7 = s.gpr .s7 ∧ t.gpr .ra = s.gpr .ra ∧ t.mem = t₄.mem)
    (by rrun [h31, e512, e520, in512, in520, al512, al520]) (by rfl) rfl)
    fun t₅ ⟨⟨a31, lr₅, m₅⟩, k₅⟩ => ⟨fun r hr => ?_, lr₅, by rw [k₅.gpr (by decide), a3], ?_, ?_⟩
  · by_cases h31' : r = .s7
    · subst h31'; exact a31
    · have hn : r ∉ [Reg.ra, .s7, .t0, .a7, .t1, .t2, .a3, .a4] := by revert hr h31'; revert r; decide
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      rw [k₅.gpr (by simp [hn]), k₄.gpr (by simp; intro e; subst e; revert hr; decide), P₃ r hr,
        k12.gpr (by simp [hn])]
  · have hB : Spec.Rc2.bytesAt t₂.mem K (s.gpr .a1).toNat = Spec.Rc2.bytesAt s.mem K (s.gpr .a1).toNat :=
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
      (Spec.Rc2.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
      (Spec.Rc2.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat) direction (s.gpr .a2).toNat with
    | .ok c => BitVec.setWidth 32 (s'.gpr .a0) = 0 ∧ Spec.Rc2.contextAt s'.mem (s.gpr .a5) direction 0 = c
    | .error e => (BitVec.setWidth 32 (s'.gpr .a0)).toNat = e.code

theorem init_wp (s : State) (h : InitPre s) :
    WP isa init s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.gpr .ra = s.gpr .ra ∧
      initPost s s' := by
  unfold init
  apply WP.seq
  refine WP.mono (checks_run s) fun t₁ ⟨m₁, k₁, c₁, e₁, v₁⟩ => ?_
  obtain g : ∀ r, r ∉ [Reg.a0, .t0] → t₁.gpr r = s.gpr r := fun r hr => k₁.gpr hr
  obtain g4 := g .a1 (by decide); have g5 := g .a2 (by decide); have g6 := g .a3 (by decide)
  obtain g7 := g .a4 (by decide); have g8 := g .a5 (by decide); have g9 := g .a6 (by decide)
  refine WP.ite _ (by rw [Steps.eval_nonzero, c₁]) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hv : ¬valid (s.gpr .a1).toNat (s.gpr .a2).toNat (s.gpr .a4).toNat := by simpa using hb
    refine ⟨fun r hr => k₁.gpr (by revert hr; revert r; decide), k₁.gpr (by decide), ?_⟩
    refine Proof.Rc2.init_post_error ?_ hv
    rw [e₁ hv]
    unfold errCode
    split
    · rfl
    · split <;> rfl
  · have hv : valid (s.gpr .a1).toNat (s.gpr .a2).toNat (s.gpr .a4).toNat := by simpa using hb
    obtain g3 := v₁ hv
    obtain h' : InitPre t₁ := by
      obtain ⟨rd, wr, al, kC, kW, vC, vW, CW⟩ := h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [k₁.2.1, k₁.2.2, g3, g4, g6, g7, g8, g9] <;>
        with_reducible assumption
    refine WP.mono (initBody_wp t₁ h' (by rw [g4, g5, g7]; exact hv)) fun s' ⟨P, L, r3, S, V⟩ =>
      ⟨fun r hr => by rw [P r hr, k₁.gpr (by revert hr; revert r; decide)], by rw [L, k₁.gpr (by decide)], ?_⟩
    rw [g3, g4, g5, g8, m₁] at S
    rw [g6, g8, m₁] at V
    exact Proof.Rc2.init_post hv.1 hv.2.1 hv.2.2 (by rw [r3]; rfl) S V

end VG.Proof.Rc2.RISCV64.Stream
