module

public import VerifiedGarbage.Impl.Rc4.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rc4.Scan64
import VerifiedGarbage.Proof.Rc4.Qword
import VerifiedGarbage.Proof.Rc4.Memory
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Spec.Rc4
public import VerifiedGarbage.TCB.RISCV64.Isa

/-! # RC4 on RISC-V: the table lookup, a doubleword at a time -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Proof.Rc4 VG.Proof.Rc4.Scan64

/-- Steps a block of the RC4 code (`mrun`). -/
syntax "rrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rrun) => `(tactic| rrun [])
  | `(tactic| rrun [$ls,*]) => `(tactic| mrun [$ls,*])

/-- An 8-byte aligned offset of an 8-byte aligned base. -/
theorem al_add {p : Addr} (hp : p.toNat % 8 = 0) {d : Nat} (hd : d % 8 = 0) (hd' : d < 2 ^ 64) :
    (p + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) hd']
  have := p.isLt
  omega

/-! ## Visiting the doublewords -/

theorem gather_step (s : State) (idx : Byte) {k : Nat} (hk : k < 32)
    (h4 : s.gpr .a4 = idx.setWidth 64) (h6 : s.gpr .t6 = 0#64) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .a7 + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block (gatherStep k)) s fun t =>
      t.gpr .t1 = s.gpr .t1 |||
        (if idx.toNat / 8 = k then s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 (8 * k)) 64 else 0) ∧
      t.gpr .a4 = s.gpr .a4 ∧ t.gpr .t6 = s.gpr .t6 ∧ t.gpr .a7 = s.gpr .a7 ∧ t.mem = s.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have hal' := al_add hal (d := 8 * k) (by omega) (by omega)
  unfold gatherStep rowMask isZero
  rrun [h4, h6, hr, hal', show 8 * k < 2048 by omega]
  rw [row_mask idx hk, and_allOnes_ite]; rfl

def GInv (s₀ : State) (idx : Byte) (k : Nat) (t : State) : Prop :=
  t.gpr .t1 = gather s₀.mem (s₀.gpr .a7) idx.toNat k ∧ t.gpr .a4 = s₀.gpr .a4 ∧
    t.gpr .t6 = s₀.gpr .t6 ∧ t.gpr .a7 = s₀.gpr .a7 ∧ t.mem = s₀.mem ∧ t.rd = s₀.rd ∧
    t.wr = s₀.wr

theorem gather_steps (s₀ : State) (idx : Byte) (h4 : s₀.gpr .a4 = idx.setWidth 64)
    (h6 : s₀.gpr .t6 = 0#64) (hal : (s₀.gpr .a7).toNat % 8 = 0)
    (hr : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .a7) 256) :
    ∀ n ≤ 32, ∀ s, GInv s₀ idx 0 s →
      WP isa (.block ((List.range n).flatMap gatherStep)) s (GInv s₀ idx n) := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun t ht => ?_
    obtain ⟨h1, h4', h6', hp, hm, hrd, hwr⟩ := ht
    have hq : InRegions (t.rd ++ t.wr) (t.gpr .a7 + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [hrd, hwr, hp]
      exact region_offset _ _ _ _ _ (by omega) (by omega) hr
    refine WP.mono (gather_step t idx (by omega) (h4'.trans h4) (h6'.trans h6) (by rw [hp]; exact hal)
      hq) fun u hu => ?_
    obtain ⟨u1, u4, u6, up, um, urd, uwr⟩ := hu
    refine ⟨?_, u4.trans h4', u6.trans h6', up.trans hp, um.trans hm, urd.trans hrd,
      uwr.trans hwr⟩
    rw [u1, h1, hp, hm, gather_succ]

/-! ## Picking the byte of the doubleword -/

theorem pick_step (s : State) (idx : Byte) {j : Nat} (hj : j < 8)
    (h4 : s.gpr .a4 = idx.setWidth 64) (h6 : s.gpr .t6 = 0#64) :
    WP isa (.block (pickStep j)) s fun t =>
      t.gpr .a5 = s.gpr .a5 ||| (if idx.toNat % 8 = j then s.gpr .t1 else 0) ∧
      t.gpr .t1 = s.gpr .t1 >>> 8 ∧
      t.gpr .a4 = s.gpr .a4 ∧ t.gpr .t6 = s.gpr .t6 ∧ t.gpr .a7 = s.gpr .a7 ∧ t.mem = s.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  unfold pickStep laneMask isZero
  rrun [h4, h6, show j < 2048 by omega]
  rw [lane_mask idx hj, and_allOnes_ite]; rfl

def PInv (s₀ : State) (q : BitVec 64) (L j : Nat) (t : State) : Prop :=
  t.gpr .a5 = pick q L j ∧ t.gpr .t1 = q >>> (8 * j) ∧ t.gpr .a4 = s₀.gpr .a4 ∧
    t.gpr .t6 = s₀.gpr .t6 ∧ t.gpr .a7 = s₀.gpr .a7 ∧ t.mem = s₀.mem ∧ t.rd = s₀.rd ∧
    t.wr = s₀.wr

theorem pick_steps (s₀ : State) (idx : Byte) (q : BitVec 64) (h4 : s₀.gpr .a4 = idx.setWidth 64)
    (h6 : s₀.gpr .t6 = 0#64) :
    ∀ n ≤ 8, ∀ s, PInv s₀ q (idx.toNat % 8) 0 s →
      WP isa (.block ((List.range n).flatMap pickStep)) s (PInv s₀ q (idx.toNat % 8) n) := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun t ht => ?_
    obtain ⟨hax, h1, h4', h6', hp, hm, hrd, hwr⟩ := ht
    refine WP.mono (pick_step t idx (by omega) (h4'.trans h4) (h6'.trans h6)) fun u hu => ?_
    obtain ⟨uax, u1, u4, u6, up, um, urd, uwr⟩ := hu
    refine ⟨?_, ?_, u4.trans h4', u6.trans h6', up.trans hp, um.trans hm, urd.trans hrd,
      uwr.trans hwr⟩
    · rw [uax, hax, h1, pick_succ]
    · rw [u1, h1, shr_byte]

/-! ## The lookup -/

theorem lookup_core (s : State) (idx : Byte) (h4 : s.gpr .a4 = idx.setWidth 64)
    (h6 : s.gpr .t6 = 0#64) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256) :
    WP isa (.block lookup) s fun t =>
      t.gpr .a5 = (s.mem (s.gpr .a7 + BitVec.ofNat 64 idx.toNat)).setWidth 64 ∧
      t.mem = s.mem := by
  have hn := idx.isLt
  simp only [lookup, List.append_assoc]
  rw [WP.block_append_iff]
  have h0 : WP isa (.block [.li .t1 0]) s (GInv s idx 0) := by
    rrun [GInv, gather, Nat.not_lt_zero, BitVec.ofNat_eq_ofNat]
  refine WP.mono h0 fun t ht => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gather_steps s idx h4 h6 hal hr 32 (by decide) t ht) fun u hu => ?_
  obtain ⟨u1, u4, u6, up, um, urd, uwr⟩ := hu
  let q := s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 (8 * (idx.toNat / 8))) 64
  have hq : u.gpr .t1 = q := by
    rw [u1]; unfold gather; rw [ite_eq_left (by omega)]
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.li .a5 0]) u (PInv s q (idx.toNat % 8) 0) := by
    rrun [PInv, pick, hq, u4, u6, up, um, urd, uwr, Nat.mul_zero, BitVec.ushiftRight_zero,
      Nat.not_lt_zero, BitVec.ofNat_eq_ofNat]
  refine WP.mono h1 fun v hv => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pick_steps s idx q h4 h6 8 (by decide) v hv) fun w hw => ?_
  obtain ⟨wax, _, _, _, _, wm, _, _⟩ := hw
  have hL : idx.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  rrun [wax, wm]
  unfold pick
  rw [low8, ite_eq_left hL, qword_byte _ _ hL, row_lane]

end VG.Proof.Rc4.RISCV64
