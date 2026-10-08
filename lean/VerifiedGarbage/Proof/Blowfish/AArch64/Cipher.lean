import VerifiedGarbage.Proof.Blowfish.AArch64.Round
import VerifiedGarbage.Proof.Blowfish.Feistel

/-!
# The sixteen rounds on sixteen blocks

`cipher_run`: `cipher sch up`, with xL of sixteen blocks in `A` and xR in
`B`, leaves `feistel` of each (encryption if `up`, decryption otherwise):
its xL in `B` and its xR in `A`.
-/

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

/-- The P-array entry of round `m`. -/
def order (up : Bool) (m : Nat) : Nat := if up then m else 17 - m

theorem order_true : order true = id := rfl
theorem order_false : order false = (17 - ·) := rfl

theorem eval_nonzero (s : State) (r : Reg) {m : Nat} (h : s.gpr r = BitVec.ofNat 64 m)
    (hm : m < 2 ^ 64) : isa.eval (.nonzero .x r) s = some (m != 0) := by
  show some (s.read .x r != 0) = _
  simp only [State.read, BitVec.setWidth_eq, h]
  congr 1
  by_cases h0 : m = 0
  · subst h0; rfl
  · have : BitVec.ofNat 64 m ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm] at this
      simp at this; omega
    simp only [bne, beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h0]

/-- The P pointer after round `m`. -/
theorem x5_next (p : Addr) (up : Bool) {m : Nat} (hm : m < 17) :
    (if up then p + BitVec.ofNat 64 (4 * order up m) + 4 else p + BitVec.ofNat 64 (4 * order up m) - 4) =
      p + BitVec.ofNat 64 (4 * order up (m + 1)) := by
  cases up
  · simp only [order, Bool.false_eq_true, ite_false]
    rw [show 4 * (17 - m) = 4 * (17 - (m + 1)) + 4 by omega, ← Offset.add_add]
    exact BitVec.add_sub_cancel _ _
  · simp only [order, ite_true]
    rw [show 4 * (m + 1) = 4 * m + 4 by omega, ← Offset.add_add]; rfl

theorem order_lt (up : Bool) {m : Nat} (hm : m < 18) : order up m < 18 := by
  cases up <;> simp only [order, Bool.false_eq_true, ite_false, ite_true] <;> omega

structure CipherInv (s₀ : State) (sch : Reg) (up : Bool) (t : Nat) (u : State) : Prop where
  le : t ≤ 8
  a : ∀ n < 16, lane u.v aReg n =
    (iter (scheduleAt s₀.mem (s₀.gpr sch)) (order up) (2 * t) (lane s₀.v aReg n, lane s₀.v bReg n)).1
  b : ∀ n < 16, lane u.v bReg n =
    (iter (scheduleAt s₀.mem (s₀.gpr sch)) (order up) (2 * t) (lane s₀.v aReg n, lane s₀.v bReg n)).2
  x5 : u.gpr .x5 = s₀.gpr sch + BitVec.ofNat 64 (4 * order up (2 * t))
  x7 : u.gpr .x7 = BitVec.ofNat 64 (8 - t)
  only : Only [.x5, .x6, .x7] roundRegs s₀ u

theorem c_notin : c64 ∉ roundRegs ∧ c128 ∉ roundRegs := by decide

theorem pair_run {s₀ : State} {sch : Reg} (hS : SchedIn s₀ sch) (hc : Consts s₀)
    (hsch : sch ≠ .x5 ∧ sch ≠ .x6 ∧ sch ≠ .x7) (up : Bool) {t : Nat} (ht : t < 8) {u : State}
    (I : CipherInv s₀ sch up t u) :
    ∃ u', runBlock isa (roundPair sch up) u = some u' ∧ CipherInv s₀ sch up (t + 1) u' := by
  let K := scheduleAt s₀.mem (s₀.gpr sch)
  have hsc : u.gpr sch = s₀.gpr sch := I.only.g _ (by simp; exact ⟨hsch.1, hsch.2.1, hsch.2.2⟩)
  have hSu : ∀ {v : State}, Only [.x5, .x6, .x7] roundRegs s₀ v → SchedIn v sch ∧ Consts v ∧
      scheduleAt v.mem (v.gpr sch) = K := by
    intro v hv
    have hg : v.gpr sch = s₀.gpr sch := hv.g _ (by simp; exact ⟨hsch.1, hsch.2.1, hsch.2.2⟩)
    refine ⟨fun off n h => ?_, ⟨fun e he => ?_, fun e he => ?_⟩, by rw [hv.mem, hg]⟩
    · rw [hv.rd, hv.wr, hg]; exact hS off n h
    · rw [hv.v _ c_notin.1]; exact hc.1 e he
    · rw [hv.v _ c_notin.2]; exact hc.2 e he
  obtain ⟨hSu₀, hcu₀, Ku₀⟩ := hSu I.only
  obtain ⟨u₁, r₁, a₁, b₁, x5₁, o₁⟩ := round_run hSu₀ hcu₀ up halves_ab (order_lt up (by omega : 2 * t < 18))
    (by rw [I.x5, hsc]) ⟨hsch.1, hsch.2.1⟩
  have p₁ : Only [.x5, .x6, .x7] roundRegs s₀ u₁ := I.only.trans (o₁.mono (by simp) (fun _ h => h))
  obtain ⟨hSu₁, hcu₁, Ku₁⟩ := hSu p₁
  have x5₁' : u₁.gpr .x5 = u₁.gpr sch + BitVec.ofNat 64 (4 * order up (2 * t + 1)) := by
    rw [x5₁, I.x5, x5_next _ _ (by omega), p₁.g _ (by simp; exact ⟨hsch.1, hsch.2.1, hsch.2.2⟩)]
  obtain ⟨u₂, r₂, a₂, b₂, x5₂, o₂⟩ := round_run hSu₁ hcu₁ up halves_ba (order_lt up (by omega : 2 * t + 1 < 18))
    x5₁' ⟨hsch.1, hsch.2.1⟩
  have p₂ : Only [.x5, .x6, .x7] roundRegs s₀ u₂ := p₁.trans (o₂.mono (by simp) (fun _ h => h))
  let u₃ := u₂.write .x .x7 (u₂.read .x .x7 - BitVec.ofNat _ 1)
  have r₃ : runBlock isa [.subImm .x .x7 .x7 1] u₂ = some u₃ := by
    rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil]
  have hx7₂ : u₂.gpr .x7 = u.gpr .x7 := by
    rw [o₂.g _ (by simp), o₁.g _ (by simp)]
  refine ⟨u₃, VG.AArch64.Tbl.runBlock_cat_some (VG.AArch64.Tbl.runBlock_cat_some r₁ r₂) r₃, ?_⟩
  have st : ∀ n < 16, iter K (order up) (2 * (t + 1)) (lane s₀.v aReg n, lane s₀.v bReg n) =
      (lane u₂.v aReg n, lane u₂.v bReg n) := by
    intro n hn
    rw [show 2 * (t + 1) = (2 * t + 1) + 1 by omega, iter_succ, iter_succ]
    simp only [roundStep]
    rw [← I.a n hn, ← I.b n hn]
    refine Prod.ext ?_ ?_
    · show _ = lane u₂.v aReg n
      rw [b₂ n hn, a₁ n hn, b₁ n hn, Ku₁, Ku₀]
      dsimp only
      rw [BitVec.xor_comm (Spec.Blowfish.f K _) (lane u.v bReg n)]
      exact BitVec.xor_comm _ _
    · show _ = lane u₂.v bReg n
      rw [a₂ n hn, b₁ n hn, Ku₁, Ku₀]
      dsimp only
      rw [BitVec.xor_comm (Spec.Blowfish.f K _) (lane u.v bReg n)]
  refine ⟨by omega, fun n hn => by rw [st n hn]; rfl, fun n hn => by rw [st n hn]; rfl, ?_, ?_, ?_⟩
  · simp only [u₃, gpr_write_of_ne _ _ _ (by decide : Reg.x5 ≠ .x7)]
    rw [x5₂, x5₁, I.x5, x5_next _ _ (by omega), x5_next _ _ (by omega),
      show 2 * t + 1 + 1 = 2 * (t + 1) by omega]
  · simp only [u₃, gpr_write_self, State.read, BitVec.setWidth_eq]
    rw [hx7₂, I.x7, show 8 - t = (8 - (t + 1)) + 1 by omega, ← BitVec.ofNat_add_ofNat]
    exact BitVec.add_sub_cancel _ _
  · exact p₂.trans ⟨rfl, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [u₃, gpr_write_of_ne _ _ _ hr.2.2], fun _ _ => rfl⟩

/-- `x6 := Pᵢ₊₁` and `v0 := Pᵢ₊₁` in every word, then `H ^= v0`. -/
theorem xorP_run {s : State} {sch : Reg} (hS : SchedIn s sch) {i : Nat} (hi : i < 18) {H : Nat → VReg}
    (hinj : ∀ k < 4, ∀ k' < 4, k ≠ k' → H k ≠ H k') (hH : ∀ k < 4, H k ≠ .v0) :
    ∃ s', runBlock isa (([.ldr .w .x6 sch (pOff + 4 * i), .vop (.dup .s4 .v0 .x6)] : List Instr) ++ xorHalf H (fun _ => .v0)) s =
        some s' ∧
      (∀ n < 16, lane s'.v H n = lane s.v H n ^^^ pEntry (scheduleAt s.mem (s.gpr sch)) i) ∧
      Only [.x6] [.v0, H 0, H 1, H 2, H 3] s s' := by
  let p := pEntry (scheduleAt s.mem (s.gpr sch)) i
  have hp : InRegions (s.rd ++ s.wr) (s.gpr sch + BitVec.ofNat 64 (pOff + 4 * i)) 4 :=
    hS _ _ (by simp only [pOff]; omega)
  have hread : s.mem.readW (s.gpr sch + BitVec.ofNat 64 (pOff + 4 * i)) 32 = p :=
    (pEntry_read _ _ hi).symm
  let s₁ := s.write .w .x6 (s.mem.readW (s.gpr sch + BitVec.ofNat 64 (pOff + 4 * i)) 32)
  let s₂ := s₁.setV .v0 (let w := (s₁.gpr .x6).setWidth 32; ofVWords w w w w)
  have r₂ : runBlock isa [.ldr .w .x6 sch (pOff + 4 * i), .vop (.dup .s4 .v0 .x6)] s = some s₂ := by
    rw [runBlock_cons, exec_ldr_w (by simp only [pOff]; omega) hp, runStep_some, runBlock_cons,
      exec_dup4, runStep_some, runBlock_nil]
  have v0₂ : ∀ l < 4, vword (s₂.v .v0) l = p := by
    intro l hl
    simp only [s₂, v_setV_self]
    rw [vword_ofVWords _ _ _ _ hl]
    have : (s₁.gpr .x6).setWidth 32 = p := by
      simp only [s₁, gpr_write_self, ← hread]; exact BitVec.setWidth_setWidth_of_le _ (by omega) |>.trans (by simp)
    rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> exact this
  obtain ⟨s₃, r₃, v₃, o₃⟩ := xorHalf_run s₂ hinj (S := fun _ => .v0) fun k _ k' hk' => (hH k' hk').symm
  refine ⟨s₃, VG.AArch64.Tbl.runBlock_cat_some r₂ r₃, fun n hn => ?_, ?_⟩
  · simp only [lane]
    rw [v₃ _ (by omega), vword_xor, v0₂ _ (by omega)]
    exact congrArg (· ^^^ p) (congrArg (vword · _) (v_setV_of_ne _ _ (hH _ (by omega))))
  · refine (⟨rfl, fun r hr => ?_, fun r hr => ?_⟩ : Only [.x6] [.v0, H 0, H 1, H 2, H 3] s s₂).trans
      (o₃.mono (by simp) (fun r hr => List.mem_cons_of_mem _ hr))
    · simp only [List.mem_singleton] at hr
      simp only [s₂, s₁, gpr_setV, gpr_write_of_ne _ _ _ hr]
    · simp only [List.mem_cons, not_or] at hr
      exact v_setV_of_ne _ _ hr.1

theorem finish_eq (sch : Reg) (up : Bool) :
    finish sch up = (([.ldr .w .x6 sch (pOff + 4 * order up 16), .vop (.dup .s4 .v0 .x6)] : List Instr) ++
      xorHalf aReg (fun _ => .v0)) ++
      (([.ldr .w .x6 sch (pOff + 4 * order up 17), .vop (.dup .s4 .v0 .x6)] : List Instr) ++ xorHalf bReg (fun _ => .v0)) := by
  cases up <;> rfl

theorem cipher_run {s : State} {sch : Reg} (hS : SchedIn s sch) (hc : Consts s)
    (hsch : sch ≠ .x5 ∧ sch ≠ .x6 ∧ sch ≠ .x7) (up : Bool) :
    WP isa (cipher sch up) s fun s' =>
      (∀ n < 16, lane s'.v bReg n =
          (feistel (scheduleAt s.mem (s.gpr sch)) (order up) (lane s.v aReg n) (lane s.v bReg n)).1 ∧
        lane s'.v aReg n =
          (feistel (scheduleAt s.mem (s.gpr sch)) (order up) (lane s.v aReg n) (lane s.v bReg n)).2) ∧
      Only [.x5, .x6, .x7] roundRegs s s' := by
  let K := scheduleAt s.mem (s.gpr sch)
  have hsch' : ∀ r ∈ [Reg.x5, .x6, .x7], sch ≠ r := by simp; exact hsch
  -- the setup
  let s₁ := s.write .x .x5 (s.read .x sch + BitVec.ofNat _ (if up then 0 else 68))
  let s₂ := s₁.write .x .x7 ((8 : BitVec 16).setWidth 64 <<< (16 * 0))
  have r₂ : runBlock isa [.addImm .x .x5 sch (if up then 0 else 68), .movz .x .x7 8 0] s = some s₂ := by
    rw [runBlock_cons, exec_addImm_x (by cases up <;> decide), runStep_some, runBlock_cons]
    rfl
  have I₀ : CipherInv s sch up 0 s₂ := by
    refine ⟨by omega, fun n _ => rfl, fun n _ => rfl, ?_, rfl, ⟨rfl, fun r hr => ?_, fun _ _ => rfl⟩⟩
    · simp only [s₂, s₁, gpr_write_of_ne _ _ _ (by decide : Reg.x5 ≠ .x7), gpr_write_self, State.read,
        BitVec.setWidth_eq]
      cases up <;> rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [s₂, s₁, gpr_write_of_ne _ _ _ hr.2.2, gpr_write_of_ne _ _ _ hr.1]
  apply WP.seq
  refine WP.of_runBlock ⟨s₂, r₂, ?_⟩
  apply WP.seq
  -- the loop
  let Inv (m : Nat) (u : State) : Prop := ∃ t, t < 8 ∧ m = 8 - t ∧ CipherInv s sch up t u
  refine WP.mono (WP.loop (M := isa) (Q := CipherInv s sch up 8) Inv ?_ 8 s₂ (show Inv 8 s₂ from ⟨0, by omega, rfl, I₀⟩)) ?_
  · intro m u ⟨t, ht, hm, I⟩
    obtain ⟨u', r, I'⟩ := pair_run hS hc hsch up ht I
    refine WP.of_runBlock ⟨u', r, ?_⟩
    have flag := eval_nonzero u' .x7 I'.x7 (by omega)
    by_cases h : t + 1 = 8
    · left
      refine ⟨by rw [flag]; simp; omega, ?_⟩
      rw [← h]; exact I'
    · right
      refine ⟨by rw [flag]; simp; omega, 8 - (t + 1), by omega, t + 1, by omega, rfl, I'⟩
  · intro u I
    have hg : u.gpr sch = s.gpr sch := I.only.g _ (by simp; exact hsch)
    have hSu : SchedIn u sch := fun off n h => by rw [I.only.rd, I.only.wr, hg]; exact hS off n h
    obtain ⟨u₁, r₁, a₁, o₁⟩ := xorP_run hSu (order_lt up (by decide : 16 < 18)) (H := aReg)
      (by decide) (by decide)
    have hSu₁ : SchedIn u₁ sch := fun off n h => by
      rw [o₁.rd, o₁.wr, o₁.g _ (by simp; exact hsch.2.1)]; exact hSu off n h
    obtain ⟨u₂, r₂', b₂, o₂⟩ := xorP_run hSu₁ (order_lt up (by decide : 17 < 18)) (H := bReg)
      (by decide) (by decide)
    refine WP.of_runBlock ⟨u₂, by rw [finish_eq]; exact VG.AArch64.Tbl.runBlock_cat_some r₁ r₂', ?_⟩
    have K₁ : scheduleAt u₁.mem (u₁.gpr sch) = K := by
      rw [o₁.mem, o₁.g _ (by simp; exact hsch.2.1), I.only.mem, hg]
    have K₀ : scheduleAt u.mem (u.gpr sch) = K := by rw [I.only.mem, hg]
    refine ⟨fun n hn => ⟨?_, ?_⟩, ?_⟩
    · have nb : ∀ k < 4, bReg k ∉ [VReg.v0, aReg 0, aReg 1, aReg 2, aReg 3] := by decide
      have hb₁ : lane u₁.v bReg n = lane u.v bReg n := by
        simp only [lane]; rw [o₁.v _ (nb _ (by omega))]
      rw [b₂ n hn, K₁, feistel_eq, hb₁, I.b n hn]
    · have na : ∀ k < 4, aReg k ∉ [VReg.v0, bReg 0, bReg 1, bReg 2, bReg 3] := by decide
      simp only [lane] at a₁ ⊢
      rw [o₂.v _ (na _ (by omega)), a₁ n hn, K₀, feistel_eq]
      have := I.a n hn
      simp only [lane] at this
      rw [this]
    · exact I.only.trans ((o₁.mono (by simp) (by decide)).trans (o₂.mono (by simp) (by decide)))

end VG.Proof.Blowfish.AArch64
