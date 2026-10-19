module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Mul
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.PrepKey
public import VerifiedGarbage.Impl.AesGcm.AArch64.Prepared
public import Mathlib.Data.List.Induction
public import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# AES-GCM on AArch64: the prepared powers

Untrusted: everything here is checked by Lean. `Impl.AesGcm.AArch64.Prepared.powers`
writes the 8 prepared powers of the hash subkey at `ctx + 256`
(`powers_ok`): slot `j` (the 16 bytes at `ctx + 256 + 16 j`) holds
`pp H (slotPow j)`, `H^(j+2)` for even `j` and `Hʲ` for odd `j`. Each
iteration of the loop keeps `Inv`: the slots below `4 i` (and slot 1) are
written, and `v18` holds `H'⁴ⁱ` with its halves swapped (`step_ok`). The
algebra is the hypothesis `PrepPow` (`Pmull/PrepKey.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Prepared

open VG VG.AArch64 VG.Proof.Gcm.AArch64.Pmull
open VG.Proof.AesGcm.AArch64 (in_off covers_left)
open VG.Proof.AesGcm.AArch64.Fast (HKey)
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)
open VG.Impl.AesGcm.AArch64.Prepared (PL PS ES ET OS OT KS ld sq byH step setup powers)
open VG.Spec.Gcm (Block blockAt)

theorem ifp {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a :=
  ite_eq_left_iff.mpr fun h' => absurd h h'

theorem ifn {α : Sort _} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b :=
  ite_eq_right_iff.mpr fun h' => absurd h' h

/-- The power slot `j` holds: `H^(j+2)` for even `j`, `Hʲ` for odd `j`. -/
def slotPow (j : Nat) : Nat := if j % 2 = 0 then j + 2 else j

/-- The address of slot `j`. -/
def slot (Ctx : Addr) (j : Nat) : Addr := Ctx + BitVec.ofNat 64 (256 + 16 * j)

/-- The slots below `n`, and slot 1, hold their prepared powers. -/
def Slots (H : Block) (Ctx : Addr) (m : Mem) (n : Nat) : Prop :=
  ∀ j < 8, (j < n ∨ j = 1) → m.read (slot Ctx j) 16 = pp H (slotPow j)

theorem read_slot_write (m : Mem) (Ctx : Addr) {j k : Nat} (hj : j < 8) (hk : k < 8) (v : BitVec (8 * 16)) :
    (m.write (slot Ctx k) 16 v).read (slot Ctx j) 16 = if j = k then v else m.read (slot Ctx j) 16 := by
  by_cases h : j = k
  · subst h; rw [ifp rfl, read_write16]
  · rw [ifn h, slot, slot, Mem.read_write_sep (Offset.sep Ctx (by omega) (by omega) (by omega)) (by decide)]

theorem ofNat_sub_one {n : Nat} (h1 : 1 ≤ n) (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem slot_off (Ctx : Addr) {d j : Nat} (h : d = 256 + 16 * j) :
    Ctx + BitVec.ofNat 64 d = slot Ctx j := by rw [slot, h]

/-! ## The groups -/

theorem ld_ok (off : Nat) (s : State) (ho : off % 16 = 0) (ho' : off < 4096 * 16)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 off) 16) :
    WP isa (.block (ld off)) s fun s' =>
      s'.v PL = s.mem.read (s.gpr .x9 + BitVec.ofNat 64 off) 16 ∧ s'.v PS = ext8 (s'.v PL) (s'.v PL) ∧
        VOnly [PL, PS] s s' := by
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrq ho ho' hin, ?_⟩
  refine WP.mono (swap_ok PS PL _) fun s' ⟨w, o⟩ => ⟨?_, ?_, ?_⟩
  · rw [o.v PL (by decide), v_setV, ifp rfl]
  · rw [w, o.v PL (by decide)]
  · exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [o.v r (by simp only [List.mem_singleton]; exact hr.2), v_setV, ifn hr.1],
      o.gpr, o.mem, o.rd, o.wr, o.sp⟩

/-- `d ← mul(a, t)`, then `dt` its halves swapped. -/
theorem mulSwap_ok {d dt a sk t : VReg} (s : State) (ha : Free a) (hs : Free sk) (ht : Free t)
    (hdt : dt ≠ d) (hst : s.v sk = ext8 (s.v t) (s.v t)) (hc : s.v C = ofVDwords poly poly)
    {u : BitVec 128} (huv : mulV (s.v a) (s.v t) = ext8 u u) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.mul d a sk t ++ ([.vop (.ext dt d d 8)] : List Instr))) s
      fun s' => s'.v d = ext8 u u ∧ s'.v dt = u ∧ VOnly [LO, MID, HI, T, d, dt] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (mulV_ok d a sk t s ha hs ht hst hc) fun s₁ ⟨m₁, o₁⟩ => ?_
  refine WP.mono (swap_ok dt d s₁) fun s₂ ⟨w₂, o₂⟩ => ⟨?_, ?_, (o₁.trans o₂).weaken fun r hr => ?_⟩
  rotate_left 2
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (h | h | h | h | h) | h <;> subst h <;> simp
  · rw [o₂.v d (by simp only [List.mem_singleton]; exact fun e => hdt e.symm), m₁, huv]
  · rw [w₂, m₁, huv, ext8_ext8]

theorem sq_ok (hP : PrepPow) {H : Block} {k : Nat} {d dt : VReg} (s : State) (hdt : dt ≠ d)
    (hl : s.v PL = pp H k) (hs : s.v PS = ext8 (s.v PL) (s.v PL)) (hc : s.v C = ofVDwords poly poly) :
    WP isa (.block (sq d dt)) s fun s' =>
      s'.v d = ext8 (pp H (k + k)) (pp H (k + k)) ∧ s'.v dt = pp H (k + k) ∧
        VOnly [LO, MID, HI, T, d, dt] s s' :=
  mulSwap_ok s (by unfold Free; decide) (by unfold Free; decide) (by unfold Free; decide) hdt hs hc
    (by rw [hs, hl, hP.mul])

theorem byH_ok (hP : PrepPow) {H : Block} {k : Nat} {d dt a : VReg} (s : State) (ha : Free a)
    (hdt : dt ≠ d) (hk : HKey H s) (hv : s.v a = ext8 (pp H k) (pp H k)) :
    WP isa (.block (byH d dt a)) s fun s' =>
      s'.v d = ext8 (pp H (k + 1)) (pp H (k + 1)) ∧ s'.v dt = pp H (k + 1) ∧
        VOnly [LO, MID, HI, T, d, dt] s s' :=
  mulSwap_ok s ha (sReg_free 1) (tReg_free 1) hdt hk.sw hk.c (by rw [hv, hk.t, hP.key, hP.mul])

/-- Two powers stored at `x10 + o` and `x10 + o + 16`. -/
theorem st2_ok (a b : VReg) (o : Nat) (s : State) (ho : o % 16 = 0) (ho' : o + 16 < 4096 * 16)
    (w₀ : InRegions s.wr (s.gpr .x10 + BitVec.ofNat 64 o) 16)
    (w₁ : InRegions s.wr (s.gpr .x10 + BitVec.ofNat 64 (o + 16)) 16) :
    WP isa (.block [.strq a .x10 o, .strq b .x10 (o + 16)]) s fun s' =>
      s'.mem = (s.mem.write (s.gpr .x10 + BitVec.ofNat 64 o) 16 (s.v a)).write
        (s.gpr .x10 + BitVec.ofNat 64 (o + 16)) 16 (s.v b) ∧
      s'.v = s.v ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine WP.block_cons_iff.mpr ⟨_, exec_strq ho (by omega) w₀, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_strq (t := b) (n := .x10) (off := o + 16) (by omega) ho' (by exact w₁), ?_⟩
  exact WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The loop -/

/-- After `i` iterations, from `s₀` (the state before `setup`). -/
structure Inv (H : Block) (Ctx : Addr) (s₀ : State) (i : Nat) (s : State) : Prop where
  le : i ≤ 2
  x9 : s.gpr .x9 = Ctx + BitVec.ofNat 64 (256 + 32 * i)
  x10 : s.gpr .x10 = Ctx + BitVec.ofNat 64 (256 + 64 * i)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (2 - i)
  gpr : ∀ r ∉ [Reg.x0, .x5, .x6, .x7, .x9, .x10, .x11], s.gpr r = s₀.gpr r
  hk : HKey H s
  ks : s.v KS = ext8 (pp H (4 * i)) (pp H (4 * i))
  slots : Slots H Ctx s.mem (4 * i)
  frame : Frame [⟨Ctx + BitVec.ofNat 64 256, 128⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem frame_slot {Ctx : Addr} {s₀ : State} {m : Mem}
    (hf : Frame [⟨Ctx + BitVec.ofNat 64 256, 128⟩] s₀.mem m) {j : Nat} (hj : j < 8) (v : BitVec (8 * 16)) :
    Frame [⟨Ctx + BitVec.ofNat 64 256, 128⟩] s₀.mem (m.write (slot Ctx j) 16 v) :=
  hf.write (List.mem_singleton_self _) v (Offset.contains Ctx (by omega) (by omega) (by omega))

theorem step_ok (hP : PrepPow) {H : Block} {Ctx : Addr} {s₀ : State} {i : Nat} {s : State}
    (hc : Covers [⟨Ctx, 384⟩] s₀.wr) (hi : i < 2) (hI : Inv H Ctx s₀ i s) :
    WP isa (.block step) s (Inv H Ctx s₀ (i + 1)) := by
  have cw : Covers [⟨Ctx, 384⟩] s.wr := by rw [hI.wr]; exact hc
  have cr : Covers [⟨Ctx, 384⟩] (s.rd ++ s.wr) := covers_left cw
  simp only [step, List.append_assoc]
  -- `H'²ⁱ⁺¹`
  rw [WP.block_append_iff]
  have a₁ : s.gpr .x9 + BitVec.ofNat 64 16 = slot Ctx (2 * i + 1) := by
    rw [hI.x9, Offset.add_add, slot_off Ctx (j := 2 * i + 1) (by omega)]
  refine WP.mono (ld_ok 16 s (by decide) (by decide) (by rw [hI.x9, Offset.add_add]; exact in_off cr (by omega) (by decide)))
    fun s₁ ⟨l₁, w₁, o₁⟩ => ?_
  have p₁ : s₁.v PL = pp H (2 * i + 1) := by
    rw [l₁, a₁, hI.slots _ (by omega) (by omega), slotPow, ifn (by omega)]
  have hk₁ : HKey H s₁ := hI.hk.of_vonly o₁ (by decide) (by decide) (by decide)
  -- `H'⁴ⁱ⁺²`
  rw [WP.block_append_iff]
  refine WP.mono (sq_ok hP s₁ (by decide) p₁ w₁ hk₁.c) fun s₂ ⟨e₂, t₂, o₂⟩ => ?_
  have hk₂ : HKey H s₂ := hk₁.of_vonly o₂ (by decide) (by decide) (by decide)
  have k₂ : s₂.v KS = ext8 (pp H (4 * i)) (pp H (4 * i)) := by
    rw [o₂.v KS (by decide), o₁.v KS (by decide), hI.ks]
  -- `H'⁴ⁱ⁺¹`
  rw [WP.block_append_iff]
  refine WP.mono (byH_ok hP s₂ (by unfold Free; decide) (by decide) hk₂ k₂) fun s₃ ⟨e₃, t₃, o₃⟩ => ?_
  have hk₃ : HKey H s₃ := hk₂.of_vonly o₃ (by decide) (by decide) (by decide)
  have o₀₃ := (o₁.trans o₂).trans o₃
  have et₃ : s₃.v ET = pp H (4 * i + 2) := by
    rw [o₃.v ET (by decide), t₂, show 2 * i + 1 + (2 * i + 1) = 4 * i + 2 by omega]
  have g₃ : s₃.gpr = s.gpr := o₀₃.gpr
  -- the first two stores
  rw [WP.block_append_iff]
  have b₀ : s₃.gpr .x10 + BitVec.ofNat 64 0 = slot Ctx (4 * i) := by
    rw [g₃, hI.x10, Offset.add_add, slot_off Ctx (j := 4 * i) (by omega)]
  have b₁ : s₃.gpr .x10 + BitVec.ofNat 64 (0 + 16) = slot Ctx (4 * i + 1) := by
    rw [g₃, hI.x10, Offset.add_add, slot_off Ctx (j := 4 * i + 1) (by omega)]
  have cw₃ : Covers [⟨Ctx, 384⟩] s₃.wr := by rw [o₀₃.wr]; exact cw
  refine WP.mono (st2_ok ET OT 0 s₃ (by decide) (by decide)
      (by rw [b₀, slot]; exact in_off cw₃ (by omega) (by decide))
      (by rw [b₁, slot]; exact in_off cw₃ (by omega) (by decide)))
    fun s₄ ⟨m₄, v₄, g₄, rd₄, wr₄, sp₄⟩ => ?_
  rw [b₀, b₁] at m₄
  have hk₄ : HKey H s₄ := hk₃.of_v (by rw [v₄]) (by rw [v₄]) (by rw [v₄])
  -- `H'²ⁱ⁺²`, read after the stores
  rw [WP.block_append_iff]
  have a₅ : s₄.gpr .x9 + BitVec.ofNat 64 0 = slot Ctx (2 * i) := by
    rw [g₄, g₃, hI.x9, Offset.add_add, slot_off Ctx (j := 2 * i) (by omega)]
  have cr₄ : Covers [⟨Ctx, 384⟩] (s₄.rd ++ s₄.wr) := by rw [rd₄, wr₄, o₀₃.rd, o₀₃.wr]; exact cr
  refine WP.mono (ld_ok 0 s₄ (by decide) (by decide) (by rw [a₅, slot]; exact in_off cr₄ (by omega) (by decide)))
    fun s₅ ⟨l₅, w₅, o₅⟩ => ?_
  have p₅ : s₅.v PL = pp H (2 * i + 2) := by
    rw [l₅, a₅, m₄, read_slot_write _ _ (by omega) (by omega), ifn (by omega),
      read_slot_write _ _ (by omega) (by omega), o₀₃.mem]
    by_cases h0 : 2 * i = 4 * i
    · rw [ifp h0, et₃, show 4 * i + 2 = 2 * i + 2 by omega]
    · rw [ifn h0, hI.slots _ (by omega) (by omega), slotPow, ifp (by omega)]
  have hk₅ : HKey H s₅ := hk₄.of_vonly o₅ (by decide) (by decide) (by decide)
  -- `H'⁴ⁱ⁺⁴`
  rw [WP.block_append_iff]
  refine WP.mono (sq_ok hP s₅ (by decide) p₅ w₅ hk₅.c) fun s₆ ⟨e₆, t₆, o₆⟩ => ?_
  have hk₆ : HKey H s₆ := hk₅.of_vonly o₆ (by decide) (by decide) (by decide)
  have es₆ : s₆.v ES = ext8 (pp H (4 * i + 2)) (pp H (4 * i + 2)) := by
    rw [o₆.v ES (by decide), o₅.v ES (by decide), v₄, o₃.v ES (by decide), e₂,
      show 2 * i + 1 + (2 * i + 1) = 4 * i + 2 by omega]
  -- `H'⁴ⁱ⁺³`
  rw [WP.block_append_iff]
  refine WP.mono (byH_ok hP s₆ (by unfold Free; decide) (by decide) hk₆ es₆) fun s₇ ⟨e₇, t₇, o₇⟩ => ?_
  have hk₇ : HKey H s₇ := hk₆.of_vonly o₇ (by decide) (by decide) (by decide)
  have o₅₇ := (o₅.trans o₆).trans o₇
  have et₇ : s₇.v ET = pp H (4 * i + 4) := by
    rw [o₇.v ET (by decide), t₆, show 2 * i + 2 + (2 * i + 2) = 4 * i + 4 by omega]
  have ks₇ : s₇.v KS = ext8 (pp H (4 * (i + 1))) (pp H (4 * (i + 1))) := by
    rw [o₇.v KS (by decide), e₆, show 2 * i + 2 + (2 * i + 2) = 4 * (i + 1) by omega]
  have g₇ : s₇.gpr = s.gpr := by rw [o₅₇.gpr, g₄, g₃]
  have cw₇ : Covers [⟨Ctx, 384⟩] s₇.wr := by rw [o₅₇.wr, wr₄]; exact cw₃
  have c₀ : s₇.gpr .x10 + BitVec.ofNat 64 32 = slot Ctx (4 * i + 2) := by
    rw [g₇, hI.x10, Offset.add_add, slot_off Ctx (j := 4 * i + 2) (by omega)]
  have c₁ : s₇.gpr .x10 + BitVec.ofNat 64 48 = slot Ctx (4 * i + 3) := by
    rw [g₇, hI.x10, Offset.add_add, slot_off Ctx (j := 4 * i + 3) (by omega)]
  -- the last two stores and the pointers
  have hw₀ : InRegions s₇.wr (s₇.gpr .x10 + BitVec.ofNat 64 32) 16 := by
    rw [c₀, slot]; exact in_off cw₇ (by omega) (by decide)
  have hw₁ : InRegions s₇.wr (s₇.gpr .x10 + BitVec.ofNat 64 48) 16 := by
    rw [c₁, slot]; exact in_off cw₇ (by omega) (by decide)
  refine WP.block_cons_iff.mpr ⟨_, exec_strq (by decide) (by decide) hw₀, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_strq (t := OT) (n := .x10) (off := 48) (by decide) (by decide)
    (by exact hw₁), ?_⟩
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addImm (show 32 < 4096 by decide),
      exec_addImm (show 64 < 4096 by decide), exec_subImm (show 1 < 4096 by decide)]; rfl, ?_⟩
  refine ⟨by omega, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write_x, reduceCtorEq, ite_false, ite_true, g₇, hI.x9, Offset.add_add]
    rw [show 256 + 32 * i + 32 = 256 + 32 * (i + 1) by omega]
  · simp only [gpr_write_x, reduceCtorEq, ite_false, ite_true, g₇, hI.x10, Offset.add_add]
    rw [show 256 + 64 * i + 64 = 256 + 64 * (i + 1) by omega]
  · simp only [gpr_write_x, reduceCtorEq, ite_false, ite_true, g₇, hI.x11]
    rw [ofNat_sub_one (by omega) (by omega), show 2 - i - 1 = 2 - (i + 1) by omega]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write_x, hr.2.2.2.2.2.2, hr.2.2.2.2.2.1, hr.2.2.2.2.1, ite_false, g₇]
    exact hI.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hr)
  · exact hk₇.of_v rfl rfl rfl
  · exact ks₇
  · intro j hj hj'
    simp only [mem_write, c₀, c₁]
    rw [read_slot_write _ _ hj (by omega), read_slot_write _ _ hj (by omega), o₅₇.mem, m₄,
      read_slot_write _ _ hj (by omega), read_slot_write _ _ hj (by omega)]
    by_cases h3 : j = 4 * i + 3
    · rw [ifp h3, t₇, h3, slotPow, ifn (by omega)]
    rw [ifn h3]
    by_cases h2 : j = 4 * i + 2
    · rw [ifp h2, et₇, h2, slotPow, ifp (by omega)]
    rw [ifn h2]
    by_cases h1 : j = 4 * i + 1
    · rw [ifp h1, t₃, h1, slotPow, ifn (by omega)]
    rw [ifn h1]
    by_cases h0 : j = 4 * i
    · rw [ifp h0, et₃, h0, slotPow, ifp (by omega)]
    rw [ifn h0, o₀₃.mem]
    exact hI.slots j hj (by omega)
  · simp only [mem_write, c₀, c₁]
    rw [o₅₇.mem, m₄, o₀₃.mem]
    exact frame_slot (frame_slot (frame_slot (frame_slot hI.frame (by omega) _) (by omega) _) (by omega) _)
      (by omega) _
  · simp only [rd_write]; rw [o₅₇.rd, rd₄, o₀₃.rd, hI.rd]
  · simp only [wr_write]; rw [o₅₇.wr, wr₄, o₀₃.wr, hI.wr]
  · show s₇.sp = s₀.sp; rw [o₅₇.sp, sp₄, o₀₃.sp, hI.sp]

theorem bne2 : ∀ i < 2, (BitVec.ofNat 64 (2 - (i + 1)) != 0) = decide (2 - (i + 1) ≠ 0) := by decide

theorem loop_ok (hP : PrepPow) {H : Block} {Ctx : Addr} {s₀ : State} (hc : Covers [⟨Ctx, 384⟩] s₀.wr)
    {s : State} (hI : Inv H Ctx s₀ 0 s) :
    WP isa (.loop (.block step) (.nonzero .x .x11)) s (Inv H Ctx s₀ 2) := by
  let Inv1 : Nat → State → Prop := fun m s => ∃ i, m = 2 - i ∧ i < 2 ∧ Inv H Ctx s₀ i s
  have hstep : ∀ m s, Inv1 m s → WP isa (.block step) s (fun s' =>
      (eval (.nonzero .x .x11) s' = some false ∧ Inv H Ctx s₀ 2 s') ∨
      (eval (.nonzero .x .x11) s' = some true ∧ ∃ m' < m, Inv1 m' s')) := by
    rintro m s ⟨i, rfl, hi, hI⟩
    refine WP.mono (step_ok hP hc hi hI) fun s' hI' => ?_
    have hev : eval (.nonzero .x .x11) s' = some (decide (2 - (i + 1) ≠ 0)) := by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI'.x11, bne2 i hi]
    by_cases hlast : 2 - (i + 1) = 0
    · have : i + 1 = 2 := by omega
      exact .inl ⟨by rw [hev]; simp [hlast], this ▸ hI'⟩
    · exact .inr ⟨by rw [hev, decide_eq_true hlast], 2 - (i + 1), by omega, i + 1, rfl, by omega, hI'⟩
  exact WP.loop (M := isa) Inv1 hstep 2 s ⟨0, rfl, by decide, hI⟩

/-- `x⁻¹` with its halves swapped, from its two doublewords. -/
theorem ks_init (H : Block) (v : BitVec 128) :
    setLane (setLane v 64 0 ((0xc200#16).setWidth 64 <<< (16 * 3))) 64 1 ((1#16).setWidth 64 <<< (16 * 0)) =
      ext8 (pp H 0) (pp H 0) := by
  rw [setLane_pair, pp_zero]; decide

theorem setup_ok (hP : PrepPow) {H : Block} {Ctx : Addr} {s : State} (h21 : s.gpr .x1 = Ctx)
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) (hc : Covers [⟨Ctx, 384⟩] s.wr) :
    WP isa (.block setup) s (Inv H Ctx s 0) := by
  simp only [setup, List.append_assoc]
  refine WP.block_cons_iff.mpr ⟨_, exec_addImm (show 240 < 4096 by decide) s, ?_⟩
  generalize hs₁ : s.write .x .x0 (s.gpr .x1 + BitVec.ofNat 64 240) = s₁
  have x0₁ : s₁.gpr .x0 + BitVec.ofNat 64 0 = Ctx + BitVec.ofNat 64 240 := by
    rw [← hs₁, gpr_write_x, ifp rfl, h21]; exact BitVec.add_zero _
  have m₁ : s₁.mem = s.mem := by rw [← hs₁]; rfl
  have rd₁ : s₁.rd = s.rd := by rw [← hs₁]; rfl
  have wr₁ : s₁.wr = s.wr := by rw [← hs₁]; rfl
  have sp₁ : s₁.sp = s.sp := by rw [← hs₁]; rfl
  have g₁ : ∀ r, r ≠ .x0 → s₁.gpr r = s.gpr r := fun r hr => by rw [← hs₁, gpr_write_x, ifn hr]
  simp only [List.append_eq, List.nil_append]
  rw [WP.block_append_iff]
  refine WP.mono (Fast.key_ok (H := H)
      (by rw [x0₁, rd₁, wr₁]; exact in_off (covers_left hc) (by decide) (by decide)) (by rw [x0₁, m₁, hH]))
    fun s₂ ⟨hk₂, g₂, v₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  have x21₂ : s₂.gpr .x1 = Ctx := by rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide), h21]
  have w₂ : InRegions s₂.wr (s₂.gpr .x1 + BitVec.ofNat 64 272) 16 := by
    rw [x21₂, wr₂, wr₁]; exact in_off hc (by decide) (by decide)
  refine WP.block_cons_iff.mpr ⟨_, exec_strq (by decide) (by decide) w₂, ?_⟩
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_movz_x (show 16 * 3 < 64 by decide),
      exec_movz_x (show 16 * 0 < 64 by decide), exec_ins_d2 (show 0 < 2 by decide),
      exec_ins_d2 (show 1 < 2 by decide), exec_addImm (show 256 < 4096 by decide)]; rfl, ?_⟩
  have kt : s₂.v (tReg 1) = pp H 1 := by rw [hk₂.t, hP.key]
  refine ⟨by decide, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write_x, gpr_setV, reduceCtorEq, ite_false, ite_true, x21₂, Nat.mul_zero, Nat.add_zero]
  · simp only [gpr_write_x, gpr_setV, reduceCtorEq, ite_false, ite_true, x21₂, Nat.mul_zero, Nat.add_zero]
  · simp only [gpr_write_x, gpr_setV, ite_true]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write_x, gpr_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2, ite_false]
    rw [g₂ r hr.2.1 hr.2.2.1 hr.2.2.2.1, g₁ r hr.1]
  · refine ⟨?_, ?_, ?_⟩
    · simp only [v_write, v_setV, reduceCtorEq, ite_false]; exact hk₂.c
    · simp only [v_write, v_setV, reduceCtorEq, ite_false]; exact hk₂.t
    · simp only [v_write, v_setV, reduceCtorEq, ite_false]; exact hk₂.sw
  · simp only [v_write, v_setV, ite_true, gpr_write_x, gpr_setV, reduceCtorEq, ite_false, Nat.mul_zero]
    exact ks_init H _
  · intro j hj hj'
    have hj1 : j = 1 := by omega
    subst hj1
    simp only [mem_write, mem_setV]
    rw [x21₂, slot_off Ctx (j := 1) (show 272 = 256 + 16 * 1 by decide), read_write16, kt]
    rfl
  · simp only [mem_write, mem_setV]
    rw [m₂, m₁, x21₂]
    rw [show Ctx + BitVec.ofNat 64 272 = slot Ctx 1 from rfl]
    exact frame_slot (Frame.refl _ _) (by decide) _
  · simp only [rd_write, rd_setV]; rw [rd₂, rd₁]
  · simp only [wr_write, wr_setV]; rw [wr₂, wr₁]
  · show s₂.sp = s.sp; rw [sp₂, sp₁]

/-- The 8 prepared powers of the hash subkey at `ctx + 240`. -/
theorem powers_ok (hP : PrepPow) {H : Block} {Ctx : Addr} {s : State} (h21 : s.gpr .x1 = Ctx)
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) (hc : Covers [⟨Ctx, 384⟩] s.wr) :
    WP isa powers s (Inv H Ctx s 2) :=
  WP.seq (WP.mono (setup_ok hP h21 hH hc) fun _ hI => loop_ok hP hc hI)

end VG.Proof.AesGcm.AArch64.Prepared
