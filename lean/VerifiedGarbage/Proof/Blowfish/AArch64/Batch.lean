module

public import VerifiedGarbage.Proof.Blowfish.AArch64.Round
public import VerifiedGarbage.Proof.Blowfish.Feistel
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Blowfish.AArch64.Exec
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem

/-! ### `Blowfish.AArch64.Cipher`, which only this module used -/

section

/-!
# The sixteen rounds on sixteen blocks

`cipher_run`: `cipher sch up`, with xL of sixteen blocks in `A` and xR in
`B`, leaves `feistel` of each (encryption if `up`, decryption otherwise):
its xL in `B` and its xR in `A`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

/-- The P-array entry of round `m`. -/
def order (up : Bool) (m : Nat) : Nat := if up then m else 17 - m

theorem order_true : order true = id := rfl
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
      simp at this; omega_using [h0, this]
    simp only [bne, beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h0]

/-- The P pointer after round `m`. -/
theorem x5_next (p : Addr) (up : Bool) {m : Nat} (hm : m < 17) :
    (if up then p + BitVec.ofNat 64 (4 * order up m) + 4 else p + BitVec.ofNat 64 (4 * order up m) - 4) =
      p + BitVec.ofNat 64 (4 * order up (m + 1)) := by
  cases up
  · simp only [order, Bool.false_eq_true, ite_false]
    rw [show 4 * (17 - m) = 4 * (17 - (m + 1)) + 4 by omega_using [hm], ← Offset.add_add]
    exact BitVec.add_sub_cancel _ _
  · simp only [order, ite_true]
    rw [show 4 * (m + 1) = 4 * m + 4 by omega_using [], ← Offset.add_add]; rfl

theorem order_lt (up : Bool) {m : Nat} (hm : m < 18) : order up m < 18 := by
  cases up <;> simp only [order, Bool.false_eq_true, ite_false, ite_true] <;> omega_arith

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
  obtain hsc : u.gpr sch = s₀.gpr sch := I.only.g _ (by simp; exact ⟨hsch.1, hsch.2.1, hsch.2.2⟩)
  obtain hSu : ∀ {v : State}, Only [.x5, .x6, .x7] roundRegs s₀ v → SchedIn v sch ∧ Consts v ∧
      scheduleAt v.mem (v.gpr sch) = K := by
    intro v hv
    obtain hg : v.gpr sch = s₀.gpr sch := hv.g _ (by simp; exact ⟨hsch.1, hsch.2.1, hsch.2.2⟩)
    refine ⟨fun off n h => ?_, ⟨fun e he => ?_, fun e he => ?_⟩, by rw [hv.mem, hg]⟩
    · rw [hv.rd, hv.wr, hg]; exact hS off n h
    · rw [hv.v _ c_notin.1]; exact hc.1 e he
    · rw [hv.v _ c_notin.2]; exact hc.2 e he
  obtain ⟨hSu₀, hcu₀, Ku₀⟩ := hSu I.only
  obtain ⟨u₁, r₁, a₁, b₁, x5₁, o₁⟩ := round_run hSu₀ hcu₀ up halves_ab (order_lt up (by omega_using [ht] : 2 * t < 18))
    (by rw [I.x5, hsc]) ⟨hsch.1, hsch.2.1⟩
  obtain p₁ : Only [.x5, .x6, .x7] roundRegs s₀ u₁ := I.only.trans (o₁.mono (by simp) (fun _ h => h))
  obtain ⟨hSu₁, hcu₁, Ku₁⟩ := hSu p₁
  obtain x5₁' : u₁.gpr .x5 = u₁.gpr sch + BitVec.ofNat 64 (4 * order up (2 * t + 1)) := by
    rw [x5₁, I.x5, x5_next _ _ (by omega_using [ht]), p₁.g _ (by simp; exact ⟨hsch.1, hsch.2.1, hsch.2.2⟩)]
  obtain ⟨u₂, r₂, a₂, b₂, x5₂, o₂⟩ := round_run hSu₁ hcu₁ up halves_ba (order_lt up (by omega_using [ht] : 2 * t + 1 < 18))
    x5₁' ⟨hsch.1, hsch.2.1⟩
  obtain p₂ : Only [.x5, .x6, .x7] roundRegs s₀ u₂ := p₁.trans (o₂.mono (by simp) (fun _ h => h))
  let u₃ := u₂.write .x .x7 (u₂.read .x .x7 - BitVec.ofNat _ 1)
  obtain r₃ : runBlock isa [.subImm .x .x7 .x7 1] u₂ = some u₃ := by
    rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil]
  obtain hx7₂ : u₂.gpr .x7 = u.gpr .x7 := by
    rw [o₂.g _ (by simp), o₁.g _ (by simp)]
  refine ⟨u₃, VG.AArch64.Tbl.runBlock_cat_some (VG.AArch64.Tbl.runBlock_cat_some r₁ r₂) r₃, ?_⟩
  obtain st : ∀ n < 16, iter K (order up) (2 * (t + 1)) (lane s₀.v aReg n, lane s₀.v bReg n) =
      (lane u₂.v aReg n, lane u₂.v bReg n) := by
    intro n hn
    rw [show 2 * (t + 1) = (2 * t + 1) + 1 by omega_using [], iter_succ, iter_succ]
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
  refine ⟨by omega_using [ht], fun n hn => by rw [st n hn]; rfl, fun n hn => by rw [st n hn]; rfl, ?_, ?_, ?_⟩
  · simp only [u₃, gpr_write_of_ne _ _ _ (by decide : Reg.x5 ≠ .x7)]
    rw [x5₂, x5₁, I.x5, x5_next _ _ (by omega_using [ht]), x5_next _ _ (by omega_using [ht]),
      show 2 * t + 1 + 1 = 2 * (t + 1) by omega_using []]
  · simp only [u₃, gpr_write_self, State.read, BitVec.setWidth_eq]
    rw [hx7₂, I.x7, show 8 - t = (8 - (t + 1)) + 1 by omega_using [ht], ← BitVec.ofNat_add_ofNat]
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
  obtain hp : InRegions (s.rd ++ s.wr) (s.gpr sch + BitVec.ofNat 64 (pOff + 4 * i)) 4 :=
    hS _ _ (by simp only [pOff]; omega_using [hi])
  obtain hread : s.mem.readW (s.gpr sch + BitVec.ofNat 64 (pOff + 4 * i)) 32 = p :=
    (pEntry_read _ _ hi).symm
  let s₁ := s.write .w .x6 (s.mem.readW (s.gpr sch + BitVec.ofNat 64 (pOff + 4 * i)) 32)
  let s₂ := s₁.setV .v0 (let w := (s₁.gpr .x6).setWidth 32; ofVWords w w w w)
  obtain r₂ : runBlock isa [.ldr .w .x6 sch (pOff + 4 * i), .vop (.dup .s4 .v0 .x6)] s = some s₂ := by
    rw [runBlock_cons, exec_ldr_w (by simp only [pOff]; omega_using [hi]) hp, runStep_some, runBlock_cons,
      exec_dup4, runStep_some, runBlock_nil]
  obtain v0₂ : ∀ l < 4, vword (s₂.v .v0) l = p := by
    intro l hl
    simp only [s₂, v_setV_self]
    rw [vword_ofVWords _ _ _ _ hl]
    have : (s₁.gpr .x6).setWidth 32 = p := by
      simp only [s₁, gpr_write_self, ← hread]; exact BitVec.setWidth_setWidth_of_le _ (by omega_using []) |>.trans (by simp)
    rcases (by omega_using [hl] : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> exact this
  obtain ⟨s₃, r₃, v₃, o₃⟩ := xorHalf_run s₂ hinj (S := fun _ => .v0) fun k _ k' hk' => (hH k' hk').symm
  refine ⟨s₃, VG.AArch64.Tbl.runBlock_cat_some r₂ r₃, fun n hn => ?_, ?_⟩
  · simp only [lane]
    rw [v₃ _ (by omega_using [hn]), vword_xor, v0₂ _ (by omega_using [])]
    exact congrArg (· ^^^ p) (congrArg (vword · _) (v_setV_of_ne _ _ (hH _ (by omega_using [hn]))))
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
  obtain hsch' : ∀ r ∈ [Reg.x5, .x6, .x7], sch ≠ r := by simp; exact hsch
  -- the setup
  let s₁ := s.write .x .x5 (s.read .x sch + BitVec.ofNat _ (if up then 0 else 68))
  let s₂ := s₁.write .x .x7 ((8 : BitVec 16).setWidth 64 <<< (16 * 0))
  obtain r₂ : runBlock isa [.addImm .x .x5 sch (if up then 0 else 68), .movz .x .x7 8 0] s = some s₂ := by
    rw [runBlock_cons, exec_addImm_x (by cases up <;> decide), runStep_some, runBlock_cons]
    rfl
  obtain I₀ : CipherInv s sch up 0 s₂ := by
    refine ⟨by omega_using [], fun n _ => rfl, fun n _ => rfl, ?_, rfl, ⟨rfl, fun r hr => ?_, fun _ _ => rfl⟩⟩
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
  refine WP.mono (WP.loop (M := isa) (Q := CipherInv s sch up 8) Inv ?_ 8 s₂ (show Inv 8 s₂ from ⟨0, by omega_using [], rfl, I₀⟩)) ?_
  · intro m u ⟨t, ht, hm, I⟩
    obtain ⟨u', r, I'⟩ := pair_run hS hc hsch up ht I
    refine WP.of_runBlock ⟨u', r, ?_⟩
    obtain flag := eval_nonzero u' .x7 I'.x7 (by omega_using [])
    by_cases h : t + 1 = 8
    · left
      refine ⟨by rw [flag]; simp; omega_using [h], ?_⟩
      rw [← h]; exact I'
    · right
      refine ⟨by rw [flag]; simp; omega_using [ht, h], 8 - (t + 1), by omega_using [ht, hm], t + 1, by omega_using [ht, h], rfl, I'⟩
  · intro u I
    obtain hg : u.gpr sch = s.gpr sch := I.only.g _ (by simp; exact hsch)
    obtain hSu : SchedIn u sch := fun off n h => by rw [I.only.rd, I.only.wr, hg]; exact hS off n h
    obtain ⟨u₁, r₁, a₁, o₁⟩ := xorP_run hSu (order_lt up (by decide : 16 < 18)) (H := aReg)
      (by decide) (by decide)
    obtain hSu₁ : SchedIn u₁ sch := fun off n h => by
      rw [o₁.rd, o₁.wr, o₁.g _ (by simp; exact hsch.2.1)]; exact hSu off n h
    obtain ⟨u₂, r₂', b₂, o₂⟩ := xorP_run hSu₁ (order_lt up (by decide : 17 < 18)) (H := bReg)
      (by decide) (by decide)
    refine WP.of_runBlock ⟨u₂, by rw [finish_eq]; exact VG.AArch64.Tbl.runBlock_cat_some r₁ r₂', ?_⟩
    obtain K₁ : scheduleAt u₁.mem (u₁.gpr sch) = K := by
      rw [o₁.mem, o₁.g _ (by simp; exact hsch.2.1), I.only.mem, hg]
    obtain K₀ : scheduleAt u.mem (u.gpr sch) = K := by rw [I.only.mem, hg]
    refine ⟨fun n hn => ⟨?_, ?_⟩, ?_⟩
    · have nb : ∀ k < 4, bReg k ∉ [VReg.v0, aReg 0, aReg 1, aReg 2, aReg 3] := by decide
      obtain hb₁ : lane u₁.v bReg n = lane u.v bReg n := by
        simp only [lane]; rw [o₁.v _ (nb _ (by omega_using [hn]))]
      rw [b₂ n hn, K₁, feistel_eq, hb₁, I.b n hn]
    · have na : ∀ k < 4, aReg k ∉ [VReg.v0, bReg 0, bReg 1, bReg 2, bReg 3] := by decide
      simp only [lane] at a₁ ⊢
      rw [o₂.v _ (na _ (by omega_using [hn])), a₁ n hn, K₀, feistel_eq]
      have := I.a n hn
      simp only [lane] at this
      rw [this]
    · exact I.only.trans ((o₁.mono (by simp) (by decide)).trans (o₂.mono (by simp) (by decide)))

end VG.Proof.Blowfish.AArch64

end

end


/-!
# A batch of sixteen blocks

`loadBatch_run`: the sixteen blocks at `x4` into `A` (xL) and `B` (xR), as
big-endian words. `storeBatch_run`: xL from `B` and xR from `A` back, as
blocks.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

/-- Word `w` of a reversed 16-byte load: the big-endian word at `4 w`, which
is half `w % 2` of block `w / 2`. -/
theorem vword_rev_read (m : Mem) (a : Addr) {w : Nat} (hw : w < 4) :
    vword (VRevOp.eval .rev32b (m.read a 16)) w =
      decodeWord (blockAt m (a + BitVec.ofNat 64 (8 * (w / 2)))) (4 * (w % 2)) := by
  refine word_ext fun b hb => ?_
  rw [← vbyte_word _ hb, vbyte_rev32b _ (by omega_arith), vbyte_read16 _ _ (by omega_arith), decodeWord_byte _ _ hb,
    blockAt_getD _ _ (by omega_arith), Offset.add_add,
    show 4 * ((4 * w + b) / 4) + (3 - (4 * w + b) % 4) = 8 * (w / 2) + (4 * (w % 2) + (3 - b)) by omega_arith]

theorem ldrq_run {t : State} (d : VReg) (n : Reg) {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions (t.rd ++ t.wr) (t.gpr n + BitVec.ofNat 64 off) 16) :
    ∃ t', runBlock isa [.ldrq d n off] t = some t' ∧
      t'.v d = t.mem.read (t.gpr n + BitVec.ofNat 64 off) 16 ∧ VOnly [d] t t' :=
  ⟨_, by rw [runBlock_cons, exec_ldrq ho h, runStep_some, runBlock_nil], v_setV_self _ _ _,
    VOnly.setV _ (by simp) _⟩

theorem vop_run {t : State} (op : VOp) (d : VReg) (x : BitVec 128) (h : exec (.vop op) t = some (t.setV d x)) :
    ∃ t', runBlock isa [.vop op] t = some t' ∧ t'.v d = x ∧ VOnly [d] t t' :=
  ⟨_, by rw [runBlock_cons, h, runStep_some, runBlock_nil], v_setV_self _ _ _, VOnly.setV _ (by simp) _⟩

/-- Chaining two steps that each change one register. -/
theorem cat_run {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ :=
  VG.AArch64.Tbl.runBlock_cat_some h₁ h₂

theorem ab_ne : ∀ k < 4, aReg k ≠ .v20 ∧ aReg k ≠ .v21 ∧ bReg k ≠ .v20 ∧ bReg k ≠ .v21 ∧ aReg k ≠ bReg k := by
  decide

/-- Blocks `4 k`…`4 k + 3` into word `k` of `A` and `B`. -/
theorem loadPair_run {s : State} {k : Nat} (hk : k < 4)
    (hR : ∀ j < 2, InRegions (s.rd ++ s.wr) (s.gpr .x4 + BitVec.ofNat 64 (32 * k + 16 * j)) 16) :
    ∃ s', runBlock isa (loadPair .x4 k) s = some s' ∧
      (∀ l < 4, vword (s'.v (aReg k)) l =
        decodeWord (blockAt s.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * (4 * k + l)))) 0) ∧
      (∀ l < 4, vword (s'.v (bReg k)) l =
        decodeWord (blockAt s.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * (4 * k + l)))) 4) ∧
      VOnly [.v20, .v21, aReg k, bReg k] s s' := by
  obtain ne := ab_ne k hk
  obtain ⟨s₁, r₁, v₁, o₁⟩ := ldrq_run (t := s) .v20 .x4 (off := 32 * k) (by omega_arith)
    (by have := hR 0 (by decide); simpa using this)
  obtain ⟨s₂, r₂, v₂, o₂⟩ := ldrq_run (t := s₁) .v21 .x4 (off := 32 * k + 16) (by omega_arith)
    (by rw [o₁.rd, o₁.wr, o₁.gpr]; exact hR 1 (by decide))
  obtain ⟨s₃, r₃, v₃, o₃⟩ := vop_run (t := s₂) (.rev .rev32b .v20 .v20) .v20 _ (exec_rev32b _ _ _)
  obtain ⟨s₄, r₄, v₄, o₄⟩ := vop_run (t := s₃) (.rev .rev32b .v21 .v21) .v21 _ (exec_rev32b _ _ _)
  obtain ⟨s₅, r₅, v₅, o₅⟩ := vop_run (t := s₄) (.perm .uzp1 .s4 (aReg k) .v20 .v21) (aReg k) _
    (exec_vperm _ _ _ _ _ _)
  obtain ⟨s₆, r₆, v₆, o₆⟩ := vop_run (t := s₅) (.perm .uzp2 .s4 (bReg k) .v20 .v21) (bReg k) _
    (exec_vperm _ _ _ _ _ _)
  -- the two reversed loads
  have m₁ : s₁.mem = s.mem := o₁.mem
  have g₁ : s₁.gpr = s.gpr := o₁.gpr
  obtain w20 : s₄.v .v20 = VRevOp.eval .rev32b (s.mem.read (s.gpr .x4 + BitVec.ofNat 64 (32 * k)) 16) := by
    rw [o₄.2 _ (by simp), v₃, o₂.2 _ (by simp), v₁]
  obtain w21 : s₄.v .v21 =
      VRevOp.eval .rev32b (s.mem.read (s.gpr .x4 + BitVec.ofNat 64 (32 * k + 16)) 16) := by
    rw [v₄, o₃.2 _ (by simp), v₂, m₁, g₁]
  obtain w20' : s₅.v .v20 = s₄.v .v20 := o₅.2 _ (by simp; exact ne.1.symm)
  obtain w21' : s₅.v .v21 = s₄.v .v21 := o₅.2 _ (by simp; exact ne.2.1.symm)
  refine ⟨s₆, cat_run r₁ (cat_run r₂ (cat_run r₃ (cat_run r₄ (cat_run r₅ r₆)))), ?_, ?_, ?_⟩
  · intro l hl
    rw [o₆.2 _ (by simp; exact ne.2.2.2.2), v₅, vword_uzp1 _ _ hl, w20, w21]
    split
    · rw [vword_rev_read _ _ (by omega_arith), Offset.add_add, show 32 * k + 8 * (2 * l / 2) = 8 * (4 * k + l) by omega_arith,
        show 4 * (2 * l % 2) = 0 by omega_arith]
    · rw [vword_rev_read _ _ (by omega_arith), Offset.add_add,
        show 32 * k + 16 + 8 * ((2 * l - 4) / 2) = 8 * (4 * k + l) by omega_arith,
        show 4 * ((2 * l - 4) % 2) = 0 by omega_arith]
  · intro l hl
    rw [v₆, w20', w21', vword_uzp2 _ _ hl, w20, w21]
    split
    · rw [vword_rev_read _ _ (by omega_arith), Offset.add_add,
        show 32 * k + 8 * ((2 * l + 1) / 2) = 8 * (4 * k + l) by omega_arith,
        show 4 * ((2 * l + 1) % 2) = 4 by omega_arith]
    · rw [vword_rev_read _ _ (by omega_arith), Offset.add_add,
        show 32 * k + 16 + 8 * ((2 * l + 1 - 4) / 2) = 8 * (4 * k + l) by omega_arith,
        show 4 * ((2 * l + 1 - 4) % 2) = 4 by omega_arith]
  · exact (((((VOnly.mono o₁ (by simp)).trans (VOnly.mono o₂ (by simp))).trans (VOnly.mono o₃ (by simp))).trans
      (VOnly.mono o₄ (by simp))).trans (VOnly.mono o₅ (by simp))).trans (VOnly.mono o₆ (by simp))

theorem loadPair_eq : (List.range 4).flatMap (loadPair .x4) =
    loadPair .x4 0 ++ (loadPair .x4 1 ++ (loadPair .x4 2 ++ (loadPair .x4 3 ++ []))) := rfl

/-- The sixteen blocks at `x4` into `A` (xL) and `B` (xR). -/
theorem loadBatch_run {s : State}
    (hR : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.gpr .x4 + BitVec.ofNat 64 (16 * k)) 16) :
    ∃ s', runBlock isa (loadBatch .x4) s = some s' ∧
      (∀ n < 16, lane s'.v aReg n = decodeWord (blockAt s.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * n))) 0) ∧
      (∀ n < 16, lane s'.v bReg n = decodeWord (blockAt s.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * n))) 4) ∧
      VOnly (.v20 :: .v21 :: halfRegs) s s' := by
  obtain hR' : ∀ {t : State}, VOnly (.v20 :: .v21 :: halfRegs) s t → ∀ k < 4, ∀ j < 2,
      InRegions (t.rd ++ t.wr) (t.gpr .x4 + BitVec.ofNat 64 (32 * k + 16 * j)) 16 := by
    intro t ht k hk j hj
    rw [ht.rd, ht.wr, ht.gpr, show 32 * k + 16 * j = 16 * (2 * k + j) by omega_arith]
    exact hR _ (by omega_arith)
  obtain sub : ∀ k < 4, ∀ r ∈ [VReg.v20, .v21, aReg k, bReg k], r ∈ VReg.v20 :: .v21 :: halfRegs := by decide
  obtain ⟨s₀, r₀, a₀, b₀, o₀⟩ := loadPair_run (s := s) (by decide : 0 < 4) (hR' (VOnly.refl _ _) 0 (by decide))
  obtain p₀ := VOnly.mono o₀ (sub 0 (by decide))
  obtain ⟨s₁, r₁, a₁, b₁, o₁⟩ := loadPair_run (s := s₀) (by decide : 1 < 4) (hR' p₀ 1 (by decide))
  obtain p₁ := p₀.trans (VOnly.mono o₁ (sub 1 (by decide)))
  obtain ⟨s₂, r₂, a₂, b₂, o₂⟩ := loadPair_run (s := s₁) (by decide : 2 < 4) (hR' p₁ 2 (by decide))
  obtain p₂ := p₁.trans (VOnly.mono o₂ (sub 2 (by decide)))
  obtain ⟨s₃, r₃, a₃, b₃, o₃⟩ := loadPair_run (s := s₂) (by decide : 3 < 4) (hR' p₂ 3 (by decide))
  obtain p₃ := p₂.trans (VOnly.mono o₃ (sub 3 (by decide)))
  refine ⟨s₃, by rw [loadBatch, loadPair_eq]; exact cat_run r₀ (cat_run r₁ (cat_run r₂ (cat_run r₃ runBlock_nil))),
    ?_, ?_, p₃⟩
  all_goals
    intro n hn
    obtain m₀ := o₀.mem; have m₁ := o₁.mem; have m₂ := o₂.mem
    obtain g₀ := o₀.gpr; have g₁ := o₁.gpr; have g₂ := o₂.gpr
    obtain pres : ∀ k < 4, ∀ k' < 4, k ≠ k' → aReg k ∉ [VReg.v20, .v21, aReg k', bReg k'] ∧
        bReg k ∉ [VReg.v20, .v21, aReg k', bReg k'] := by decide
    simp only [lane]
    rcases (by omega_arith : n / 4 = 0 ∨ n / 4 = 1 ∨ n / 4 = 2 ∨ n / 4 = 3) with h | h | h | h <;> rw [h]
  · rw [o₃.2 _ (pres 0 (by decide) 3 (by decide) (by decide)).1, o₂.2 _ (pres 0 (by decide) 2 (by decide) (by decide)).1, o₁.2 _ (pres 0 (by decide) 1 (by decide) (by decide)).1, a₀ _ (by omega_arith)]
    exact congrArg (decodeWord · 0) (congrArg _ (congrArg _ (congrArg _ (by omega_arith))))
  · rw [o₃.2 _ (pres 1 (by decide) 3 (by decide) (by decide)).1, o₂.2 _ (pres 1 (by decide) 2 (by decide) (by decide)).1, a₁ _ (by omega_arith), m₀, g₀]
    exact congrArg (decodeWord · 0) (congrArg _ (congrArg _ (congrArg _ (by omega_arith))))
  · rw [o₃.2 _ (pres 2 (by decide) 3 (by decide) (by decide)).1, a₂ _ (by omega_arith), m₁, g₁, m₀, g₀]
    exact congrArg (decodeWord · 0) (congrArg _ (congrArg _ (congrArg _ (by omega_arith))))
  · rw [a₃ _ (by omega_arith), m₂, g₂, m₁, g₁, m₀, g₀]
    exact congrArg (decodeWord · 0) (congrArg _ (congrArg _ (congrArg _ (by omega_arith))))
  · rw [o₃.2 _ (pres 0 (by decide) 3 (by decide) (by decide)).2, o₂.2 _ (pres 0 (by decide) 2 (by decide) (by decide)).2, o₁.2 _ (pres 0 (by decide) 1 (by decide) (by decide)).2, b₀ _ (by omega_arith)]
    exact congrArg (decodeWord · 4) (congrArg _ (congrArg _ (congrArg _ (by omega_arith))))
  · rw [o₃.2 _ (pres 1 (by decide) 3 (by decide) (by decide)).2, o₂.2 _ (pres 1 (by decide) 2 (by decide) (by decide)).2, b₁ _ (by omega_arith), m₀, g₀]
    exact congrArg (decodeWord · 4) (congrArg _ (congrArg _ (congrArg _ (by omega_arith))))
  · rw [o₃.2 _ (pres 2 (by decide) 3 (by decide) (by decide)).2, b₂ _ (by omega_arith), m₁, g₁, m₀, g₀]
    exact congrArg (decodeWord · 4) (congrArg _ (congrArg _ (congrArg _ (by omega_arith))))
  · rw [b₃ _ (by omega_arith), m₂, g₂, m₁, g₁, m₀, g₀]
    exact congrArg (decodeWord · 4) (congrArg _ (congrArg _ (congrArg _ (by omega_arith))))

/-! ## Storing -/

/-- Byte `j` (< 128) of the sixteen blocks whose halves are the words of `A`
and `B` (xL in `B`, xR in `A`). -/
def outByte (v : VReg → BitVec 128) (j : Nat) : Byte :=
  (encodeBlock (lane v bReg (j / 8)) (lane v aReg (j / 8))).getD (j % 8) 0

theorem write16_byte (m : Mem) (p : Addr) (x : BitVec 128) {o j : Nat} (ho : o + 16 ≤ 128) (hj : j < 128) :
    m.write (p + BitVec.ofNat 64 o) 16 x (p + BitVec.ofNat 64 j) =
      if o ≤ j ∧ j < o + 16 then vbyte x (j - o) else m (p + BitVec.ofNat 64 j) := by
  simp only [Mem.write, Offset.sub_toNat' p (show o < 2 ^ 64 by omega_arith) (show j < 2 ^ 64 by omega_arith)]
  by_cases h : o ≤ j
  · simp only [h, ite_true, true_and]
    by_cases h' : j < o + 16
    · simp only [show j - o < 16 by omega_arith, h', ite_true]; rfl
    · simp only [show ¬ j - o < 16 by omega_arith, h', ite_false]
  · simp only [h, ite_false, false_and]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]

/-- What `rev32 (zip1/zip2 .4s B A)` holds: byte `e` of it is byte `e % 8` of
block `2 o + e / 8` of the four in words `k` of `A` and `B`. -/
theorem stored_byte (Bk Ak : BitVec 128) {o e : Nat} (ho : o < 2) (he : e < 16) :
    vbyte (VRevOp.eval .rev32b (VPermOp.eval (if o = 0 then .zip1 else .zip2) .s4 Bk Ak)) e =
      (encodeBlock (vword Bk (2 * o + e / 8)) (vword Ak (2 * o + e / 8))).getD (e % 8) 0 := by
  rw [vbyte_rev32b _ he, vbyte_word _ (by omega_arith), encodeBlock_getD _ _ (by omega_arith)]
  obtain hw : (e / 4) / 2 = e / 8 := by omega_arith
  rcases (by omega_arith : o = 0 ∨ o = 1) with rfl | rfl
  · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), vword_zip1 _ _ (by omega_arith), hw]
    by_cases h : e % 8 < 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)), ite_eq_left_of_eq_true _ _ (eq_true h),
        show 3 - e % 4 = 3 - e % 8 by omega_arith, show 2 * 0 + e / 8 = e / 8 by omega_arith]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), ite_eq_right_of_eq_false _ _ (eq_false h),
        show 3 - e % 4 = 7 - e % 8 by omega_arith, show 2 * 0 + e / 8 = e / 8 by omega_arith]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)), vword_zip2 _ _ (by omega_arith), hw]
    by_cases h : e % 8 < 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)), ite_eq_left_of_eq_true _ _ (eq_true h),
        show 3 - e % 4 = 3 - e % 8 by omega_arith, show 2 * 1 + e / 8 = 2 + e / 8 by omega_arith]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), ite_eq_right_of_eq_false _ _ (eq_false h),
        show 3 - e % 4 = 7 - e % 8 by omega_arith, show 2 * 1 + e / 8 = 2 + e / 8 by omega_arith]

/-- Only the memory and the vector registers `vs` change. -/
structure MOnly (vs : List VReg) (s s' : State) : Prop where
  eq : s' = { s with v := s'.v, mem := s'.mem }
  v : ∀ r, r ∉ vs → s'.v r = s.v r

theorem MOnly.trans {vs : List VReg} {a b c : State} (h₁ : MOnly vs a b) (h₂ : MOnly vs b c) : MOnly vs a c := by
  refine ⟨?_, fun r hr => (h₂.v r hr).trans (h₁.v r hr)⟩
  rw [h₂.eq, h₁.eq]

theorem MOnly.ofV {vs : List VReg} {a b : State} (h : VOnly vs a b) : MOnly vs a b :=
  ⟨by rw [h.1], h.2⟩

theorem MOnly.gpr {vs : List VReg} {a b : State} (h : MOnly vs a b) : b.gpr = a.gpr := by rw [h.eq]
theorem MOnly.rd {vs : List VReg} {a b : State} (h : MOnly vs a b) : b.rd = a.rd := by rw [h.eq]
theorem MOnly.wr {vs : List VReg} {a b : State} (h : MOnly vs a b) : b.wr = a.wr := by rw [h.eq]
theorem MOnly.sp {vs : List VReg} {a b : State} (h : MOnly vs a b) : b.sp = a.sp := by rw [h.eq]

theorem strq_run {t : State} (d : VReg) (n : Reg) {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions t.wr (t.gpr n + BitVec.ofNat 64 off) 16) :
    ∃ t', runBlock isa [.strq d n off] t = some t' ∧
      t'.mem = t.mem.write (t.gpr n + BitVec.ofNat 64 off) 16 (t.v d) ∧ MOnly [] t t' :=
  ⟨{ t with mem := t.mem.write (t.gpr n + BitVec.ofNat 64 off) 16 (t.v d) },
    by rw [runBlock_cons, exec_strq ho h, runStep_some, runBlock_nil], rfl, ⟨rfl, fun _ _ => rfl⟩⟩

theorem storePair_run {s : State} {k : Nat} (hk : k < 4)
    (hW : ∀ j < 2, InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 (32 * k + 16 * j)) 16) :
    ∃ s', runBlock isa (storePair .x4 k) s = some s' ∧
      (∀ j < 128, s'.mem (s.gpr .x4 + BitVec.ofNat 64 j) =
        if 32 * k ≤ j ∧ j < 32 * k + 32 then outByte s.v j else s.mem (s.gpr .x4 + BitVec.ofNat 64 j)) ∧
      Frame [⟨s.gpr .x4, 128⟩] s.mem s'.mem ∧ MOnly [.v20, .v21] s s' := by
  obtain ne := ab_ne k hk
  obtain ⟨s₁, r₁, v₁, o₁⟩ := vop_run (t := s) (.perm .zip1 .s4 .v20 (bReg k) (aReg k)) .v20 _
    (exec_vperm _ _ _ _ _ _)
  obtain ⟨s₂, r₂, v₂, o₂⟩ := vop_run (t := s₁) (.perm .zip2 .s4 .v21 (bReg k) (aReg k)) .v21 _
    (exec_vperm _ _ _ _ _ _)
  obtain ⟨s₃, r₃, v₃, o₃⟩ := vop_run (t := s₂) (.rev .rev32b .v20 .v20) .v20 _ (exec_rev32b _ _ _)
  obtain ⟨s₄, r₄, v₄, o₄⟩ := vop_run (t := s₃) (.rev .rev32b .v21 .v21) .v21 _ (exec_rev32b _ _ _)
  obtain o₁₄ : VOnly [.v20, .v21] s s₄ := (((VOnly.mono o₁ (by simp)).trans (VOnly.mono o₂ (by simp))).trans
    (VOnly.mono o₃ (by simp))).trans (VOnly.mono o₄ (by simp))
  obtain ⟨s₅, r₅, m₅, o₅⟩ := strq_run (t := s₄) .v20 .x4 (off := 32 * k) (by omega_arith)
    (by rw [o₁₄.wr, o₁₄.gpr]; simpa using hW 0 (by decide))
  obtain ⟨s₆, r₆, m₆, o₆⟩ := strq_run (t := s₅) .v21 .x4 (off := 32 * k + 16) (by omega_arith)
    (by rw [o₅.wr, o₅.gpr, o₁₄.wr, o₁₄.gpr]; exact hW 1 (by decide))
  -- the values stored
  obtain x20 : s₄.v .v20 = VRevOp.eval .rev32b (VPermOp.eval .zip1 .s4 (s.v (bReg k)) (s.v (aReg k))) := by
    rw [o₄.2 _ (by simp), v₃, o₂.2 _ (by simp), v₁]
  obtain x21 : s₅.v .v21 = VRevOp.eval .rev32b (VPermOp.eval .zip2 .s4 (s.v (bReg k)) (s.v (aReg k))) := by
    rw [o₅.v _ (by simp), v₄, o₃.2 _ (by simp), v₂, o₁.2 _ (by simp; exact ne.2.2.1),
      o₁.2 _ (by simp; exact ne.1)]
  have g₄' : s₄.gpr = s.gpr := o₁₄.gpr
  obtain g₅' : s₅.gpr = s.gpr := by rw [o₅.gpr, g₄']
  obtain fr : Frame [⟨s.gpr .x4, 128⟩] s.mem s₆.mem := by
    rw [m₆, m₅, g₅', g₄', o₁₄.mem]
    exact ((Frame.refl _ _).write (List.mem_singleton.mpr rfl) _
      (Offset.contains_base _ (by omega_arith) (by omega_arith))).write (List.mem_singleton.mpr rfl) _
      (Offset.contains_base _ (by omega_arith) (by omega_arith))
  refine ⟨s₆, cat_run r₁ (cat_run r₂ (cat_run r₃ (cat_run r₄ (cat_run r₅ r₆)))), fun j hj => ?_, fr,
    (MOnly.ofV o₁₄).trans (o₅.trans o₆ |>.trans ⟨rfl, fun _ _ => rfl⟩ |> fun h => ⟨h.eq, fun r _ => h.v r (by simp)⟩)⟩
  have g₄ : s₄.gpr = s.gpr := o₁₄.gpr
  obtain g₅ : s₅.gpr = s.gpr := by rw [o₅.gpr, g₄]
  rw [m₆, g₅, show s.gpr .x4 + BitVec.ofNat 64 (32 * k + 16) = s.gpr .x4 + BitVec.ofNat 64 (32 * k + 16) from rfl,
    write16_byte _ _ _ (by omega_arith) hj, m₅, g₄, write16_byte _ _ _ (by omega_arith) hj, o₁₄.mem, x21, x20]
  obtain lane_k : ∀ (R : Nat → VReg) (e : Nat), e < 16 → ∀ o < 2,
      vword (s.v (R k)) (2 * o + e / 8) = lane s.v R (4 * k + (2 * o + e / 8)) := by
    intro R e he o ho
    simp only [lane]
    rw [show (4 * k + (2 * o + e / 8)) / 4 = k by omega_arith, show (4 * k + (2 * o + e / 8)) % 4 = 2 * o + e / 8 by omega_arith]
  by_cases h₂ : 32 * k + 16 ≤ j ∧ j < 32 * k + 16 + 16
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h₂), ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)),
      show VPermOp.zip2 = (if 1 = 0 then .zip1 else .zip2) from rfl, stored_byte _ _ (by decide) (by omega_arith),
      lane_k bReg _ (by omega_arith) 1 (by decide), lane_k aReg _ (by omega_arith) 1 (by decide), outByte,
      show 4 * k + (2 * 1 + (j - (32 * k + 16)) / 8) = j / 8 by omega_arith,
      show (j - (32 * k + 16)) % 8 = j % 8 by omega_arith]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h₂)]
    by_cases h₁ : 32 * k ≤ j ∧ j < 32 * k + 16
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h₁), ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)),
        show VPermOp.zip1 = (if 0 = 0 then .zip1 else .zip2) from rfl, stored_byte _ _ (by decide) (by omega_arith),
        lane_k bReg _ (by omega_arith) 0 (by decide), lane_k aReg _ (by omega_arith) 0 (by decide), outByte,
        show 4 * k + (2 * 0 + (j - 32 * k) / 8) = j / 8 by omega_arith,
        show (j - 32 * k) % 8 = j % 8 by omega_arith]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h₁), ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]

theorem storePair_eq : (List.range 4).flatMap (storePair .x4) =
    storePair .x4 0 ++ (storePair .x4 1 ++ (storePair .x4 2 ++ (storePair .x4 3 ++ []))) := rfl

theorem outByte_congr {v v' : VReg → BitVec 128} (h : ∀ r ∈ halfRegs, v' r = v r) (j : Nat) :
    outByte v' j = outByte v j := by
  obtain ha : ∀ n, lane v' aReg n = lane v aReg n := fun n => by
    simp only [lane]; rw [h _ (by
      rcases (by omega_arith : n / 4 = 0 ∨ n / 4 = 1 ∨ n / 4 = 2 ∨ n / 4 = 3 ∨ 4 ≤ n / 4) with e | e | e | e | e <;>
        simp [e, aReg, halfRegs])]
  obtain hb : ∀ n, lane v' bReg n = lane v bReg n := fun n => by
    simp only [lane]; rw [h _ (by
      rcases (by omega_arith : n / 4 = 0 ∨ n / 4 = 1 ∨ n / 4 = 2 ∨ n / 4 = 3 ∨ 4 ≤ n / 4) with e | e | e | e | e <;>
        simp [e, bReg, halfRegs])]
  simp only [outByte, ha, hb]

/-- The halves of the sixteen blocks back to the 128 bytes at `x4`. -/
theorem storeBatch_run {s : State}
    (hW : ∀ k < 8, InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 (16 * k)) 16) :
    ∃ s', runBlock isa (storeBatch .x4) s = some s' ∧
      (∀ j < 128, s'.mem (s.gpr .x4 + BitVec.ofNat 64 j) = outByte s.v j) ∧
      Frame [⟨s.gpr .x4, 128⟩] s.mem s'.mem ∧ MOnly [.v20, .v21] s s' := by
  obtain hW' : ∀ {t : State}, MOnly [.v20, .v21] s t → ∀ k < 4, ∀ j < 2,
      InRegions t.wr (t.gpr .x4 + BitVec.ofNat 64 (32 * k + 16 * j)) 16 := by
    intro t ht k hk j hj
    rw [ht.wr, ht.gpr, show 32 * k + 16 * j = 16 * (2 * k + j) by omega_arith]
    exact hW _ (by omega_arith)
  obtain hh : ∀ {t : State}, MOnly [.v20, .v21] s t → ∀ r ∈ halfRegs, t.v r = s.v r := fun ht r hr =>
    ht.v r (by revert r; decide)
  obtain ⟨s₀, r₀, m₀, f₀, o₀⟩ := storePair_run (s := s) (by decide : 0 < 4) (hW' ⟨rfl, fun _ _ => rfl⟩ 0 (by decide))
  obtain ⟨s₁, r₁, m₁, f₁, o₁⟩ := storePair_run (s := s₀) (by decide : 1 < 4) (hW' o₀ 1 (by decide))
  obtain p₁ := o₀.trans o₁
  obtain ⟨s₂, r₂, m₂, f₂, o₂⟩ := storePair_run (s := s₁) (by decide : 2 < 4) (hW' p₁ 2 (by decide))
  obtain p₂ := p₁.trans o₂
  obtain ⟨s₃, r₃, m₃, f₃, o₃⟩ := storePair_run (s := s₂) (by decide : 3 < 4) (hW' p₂ 3 (by decide))
  obtain p₃ := p₂.trans o₃
  obtain g₀ := o₀.gpr; have g₁ := p₁.gpr; have g₂ := p₂.gpr
  obtain b₀ := outByte_congr (hh o₀); have b₁ := outByte_congr (hh p₁); have b₂ := outByte_congr (hh p₂)
  obtain mem : ∀ j < 128, s₃.mem (s.gpr .x4 + BitVec.ofNat 64 j) = outByte s.v j := by
    intro j hj
    obtain e₃ := m₃ j hj; have e₂ := m₂ j hj; have e₁ := m₁ j hj; have e₀ := m₀ j hj
    rw [g₂] at e₃; rw [g₁] at e₂; rw [g₀] at e₁
    rw [e₃, b₂]
    split
    · rfl
    · rw [e₂, b₁]; split
      · rfl
      · rw [e₁, b₀]; split
        · rfl
        · rw [e₀]; split
          · rfl
          · omega_arith
  refine ⟨s₃, by rw [storeBatch, storePair_eq]; exact cat_run r₀ (cat_run r₁ (cat_run r₂ (cat_run r₃ runBlock_nil))),
    mem, ?_, p₃⟩
  rw [g₂] at f₃; rw [g₁] at f₂; rw [g₀] at f₁
  exact f₀.trans (f₁.trans (f₂.trans f₃))

/-! ## The batch -/

/-- A block's encryption (`up`) or decryption. -/
def blockOut (K : Schedule) (up : Bool) (b : Block) : Block :=
  if up then encryptBlock K b else decryptBlock K b

theorem blockOut_eq (K : Schedule) (up : Bool) (b : Block) :
    blockOut K up b = encodeBlock (feistel K (order up) (decodeWord b 0) (decodeWord b 4)).1
      (feistel K (order up) (decodeWord b 0) (decodeWord b 4)).2 := by
  cases up <;> rfl

structure BatchPost (up : Bool) (s s' : State) : Prop where
  out : ∀ n < 16, blockAt s'.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * n)) =
    blockOut (scheduleAt s.mem (s.gpr .x0)) up (blockAt s.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * n)))
  gpr : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨s.gpr .x4, 128⟩] s.mem s'.mem
  v : ∀ r, r ∉ roundRegs → s'.v r = s.v r

theorem io_sub : ∀ r ∈ (VReg.v20 :: .v21 :: halfRegs), r ∈ roundRegs := by decide

theorem batch_ok (up : Bool) {s : State} (hS : SchedIn s .x0) (hc : Consts s)
    (hW : ∀ k < 8, InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 (16 * k)) 16) :
    WP isa (batch up) s (BatchPost up s) := by
  let K := scheduleAt s.mem (s.gpr .x0)
  obtain ⟨s₁, r₁, a₁, b₁, o₁⟩ := loadBatch_run (s := s) fun k hk => by
    obtain ⟨r, hr, hc'⟩ := hW k hk; exact ⟨r, List.mem_append_right _ hr, hc'⟩
  rw [batch]
  apply WP.seq
  refine WP.of_runBlock ⟨s₁, r₁, ?_⟩
  obtain hS₁ : SchedIn s₁ .x0 := fun off n h => by rw [o₁.rd, o₁.wr, o₁.gpr]; exact hS off n h
  obtain hc₁ : Consts s₁ :=
    ⟨fun e he => by rw [o₁.2 _ (by decide)]; exact hc.1 e he, fun e he => by rw [o₁.2 _ (by decide)]; exact hc.2 e he⟩
  apply WP.seq
  refine WP.mono (cipher_run hS₁ hc₁ (by decide) up) ?_
  intro s₂ ⟨hl, o₂⟩
  obtain hW₂ : ∀ k < 8, InRegions s₂.wr (s₂.gpr .x4 + BitVec.ofNat 64 (16 * k)) 16 := fun k hk => by
    rw [o₂.wr, o₂.g _ (by simp), o₁.wr, o₁.gpr]; exact hW k hk
  obtain ⟨s₃, r₃, m₃, f₃, o₃⟩ := storeBatch_run hW₂
  refine WP.of_runBlock ⟨s₃, r₃, ?_⟩
  obtain g₂ : s₂.gpr .x4 = s.gpr .x4 := by rw [o₂.g _ (by simp), o₁.gpr]
  obtain K₁ : scheduleAt s₁.mem (s₁.gpr .x0) = K := by rw [o₁.mem, o₁.gpr]
  refine ⟨fun n hn => ?_, fun r h5 h6 h7 => ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · refine blockAt_eq _ _ _ fun i hi => ?_
    rw [← g₂, Offset.add_add, m₃ _ (by omega_arith), outByte, show (8 * n + i) / 8 = n by omega_arith,
      show (8 * n + i) % 8 = i by omega_arith, (hl n hn).1, (hl n hn).2, K₁, a₁ n hn, b₁ n hn, ← blockOut_eq, g₂]
  · rw [o₃.gpr, o₂.g _ (by simp; exact ⟨h5, h6, h7⟩), o₁.gpr]
  · rw [o₃.rd, o₂.rd, o₁.rd]
  · rw [o₃.wr, o₂.wr, o₁.wr]
  · rw [o₃.sp, o₂.sp, o₁.1]
  · rw [g₂] at f₃; rw [← o₁.mem, ← o₂.mem]; exact f₃
  · have n20 : r ∉ [VReg.v20, .v21] := fun h => hr (io_sub _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h <;> simp [h]))
    rw [o₃.v _ n20, o₂.v _ hr, o₁.2 _ (fun h => hr (io_sub _ h))]

end VG.Proof.Blowfish.AArch64
