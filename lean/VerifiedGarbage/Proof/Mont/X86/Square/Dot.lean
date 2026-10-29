module

public import VerifiedGarbage.Proof.Mont.X86.Square.Packed
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Impl.Mont.X86.MulRt
public import VerifiedGarbage.Proof.Mont.Words32
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Mont.X86.Square.Step

-- Formerly `VerifiedGarbage/Proof/Mont/X86/Square/Control.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def ctl (r : Reg) : List Instr :=
  [.alu .add .ecx (.imm 4), .alu .sub .ebp (.imm 4), .alu .cmp .ecx (.reg r)]

def addPtr (s : State) (r : Reg) (v : BitVec 32) : State :=
  (arithFlags s (s.gpr r + v) (2^32 ≤ (s.gpr r).toNat+v.toNat)
    (addOverflow (s.gpr r) v (s.gpr r+v))).setReg r (s.gpr r+v)

def subPtr (s : State) (r : Reg) (v : BitVec 32) : State :=
  (arithFlags s (s.gpr r - v) ((s.gpr r).toNat < v.toNat)
    (subOverflow (s.gpr r) v (s.gpr r-v))).setReg r (s.gpr r-v)

def cmpReg (s : State) (l r : Reg) : State :=
  arithFlags s (s.gpr l-s.gpr r) ((s.gpr l).toNat < (s.gpr r).toNat)
    (subOverflow (s.gpr l) (s.gpr r) (s.gpr l-s.gpr r))

def ctlState (s : State) (r : Reg) : State := cmpReg (subPtr (addPtr s .ecx 4) .ebp 4) .ecx r

theorem run_ctl (s : State) (r : Reg) : runBlock isa (ctl r) s = some (ctlState s r) := by
  rfl

theorem ctl_values (s : State) (r : Reg) (hr : r = .ebp ∨ r = .ebx) :
    (ctlState s r).gpr .ecx = s.gpr .ecx + 4 ∧
    (ctlState s r).gpr .ebp = s.gpr .ebp - 4 ∧
    (ctlState s r).cf = some (decide ((s.gpr .ecx+4).toNat <
      (if r = .ebp then s.gpr .ebp-4 else s.gpr r).toNat)) ∧
    (ctlState s r).xmm = s.xmm ∧
    (ctlState s r).mem = s.mem ∧
    Keeps [.ecx, .ebp] s (ctlState s r) := by
  have g : ∀ j, (ctlState s r).gpr j =
      if j = .ebp then s.gpr .ebp-4 else if j = .ecx then s.gpr .ecx+4 else s.gpr j := by
    intro j
    simp [ctlState, cmpReg, subPtr, addPtr, arithFlags, State.setReg, State.setFlags]
  refine ⟨g .ecx, g .ebp, ?_, rfl, rfl, ?_⟩
  · rcases hr with rfl | rfl <;>
      simp [ctlState, cmpReg, subPtr, addPtr, arithFlags, State.setReg, State.setFlags]
  · refine ⟨?_, rfl, rfl⟩
    intro j hj
    rw [g]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp [hj.1, hj.2]

end VG.Proof.Mont.X86.Square
end

end

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def total (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => total f n + f n

def dotProd (s : State) (W : Addr) (x y i : Nat) : Nat :=
  w32 s.mem W (x+4*i) * w32 s.mem W (y-4*i)

structure DotI (s : State) (W : Addr) (L x y : Nat) (lo hi : BitVec 64) (i : Nat) (t : State) : Prop where
  ws : Ws t W L
  keep : Keeps [.eax, .edx, .ecx, .ebp] s t
  mem : t.mem = s.mem
  left : PtrAt t W .ecx (x+4*i)
  right : PtrAt t W .ebp (y-4*i)
  low : t.xmm .xmm0 = packed (lo + BitVec.ofNat 64 (total (fun j => dotProd s W x y j % 2^32) i))
  high : t.xmm .xmm1 = packed (hi + BitVec.ofNat 64 (total (fun j => dotProd s W x y j / 2^32) i))
  c3 : t.xmm .xmm3 = s.xmm .xmm3
  c7 : t.xmm .xmm7 = s.xmm .xmm7

theorem dotStep_ok {s t : State} {W : Addr} {L x y K i : Nat} {lo hi : BitVec 64}
    {r : Reg} (hr : r = .ebp ∨ r = .ebx) (inv : DotI s W L x y lo hi i t)
    (hiK : i < K) (hl : x+4*K < L) (hy : y+4 ≤ L) (hk : 4*K ≤ y)
    (cmp : ∀ j ≤ K, (W.toNat+x+4*j <
      if r = .ebp then W.toNat+(y-4*j) else (s.gpr .ebx).toNat) ↔ j<K) :
    WP isa (.block (VG.Impl.Mont.X86.Rt.Square.prod ++ ctl r)) t fun u =>
      DotI s W L x y lo hi (i+1) u ∧ u.cf = some (decide (i+1<K)) := by
  apply WP.block_append
  refine WP.mono (prod_ok inv.ws inv.left inv.right (by omega) (by omega)) fun p hp => ?_
  subst p
  let p := prodState t (t.mem.readW (off W (x+4*i)) 32) (t.mem.readW (off W (y-4*i)) 32)
  have vals := prod_values (t.mem.readW (off W (x+4*i)) 32) (t.mem.readW (off W (y-4*i)) 32) inv.low inv.high
  have frame := prod_frame t (t.mem.readW (off W (x+4*i)) 32) (t.mem.readW (off W (y-4*i)) 32)
  have ctrl := ctl_values p r hr
  apply WP.of_runBlock
  refine ⟨ctlState p r, run_ctl p r, ?_⟩
  have xp : PtrAt p W .ecx (x+4*i) := by rw [PtrAt, frame.1.1 _ (by decide)]; exact inv.left
  have yp : PtrAt p W .ebp (y-4*i) := by rw [PtrAt, frame.1.1 _ (by decide)]; exact inv.right
  have lptr : PtrAt (ctlState p r) W .ecx (x+4*(i+1)) := by
    rw [PtrAt, ctrl.1]
    simpa only [show (4 : BitVec 32).toNat = 4 from rfl, show x+4*i+4=x+4*(i+1) by omega] using ptr_add xp (4 : BitVec 32)
  have rptr : PtrAt (ctlState p r) W .ebp (y-4*(i+1)) := by
    rw [PtrAt, ctrl.2.1]
    simpa only [show (4 : BitVec 32).toNat = 4 from rfl, show y-4*i-4=y-4*(i+1) by omega] using
      ptr_sub yp (4 : BitVec 32) (by change 4 ≤ y-4*i; omega)
  have keep : Keeps [.eax, .edx, .ecx, .ebp] t (ctlState p r) :=
    (frame.1.mono (by decide)).trans (ctrl.2.2.2.2.2.mono (by decide))
  have mem : (ctlState p r).mem = s.mem := ctrl.2.2.2.2.1.trans (frame.2.trans inv.mem)
  have nw := inv.ws.nowrap
  refine ⟨⟨inv.ws.of_keeps keep, inv.keep.trans keep, mem, lptr, rptr, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [ctrl.2.2.2.1, vals.1, inv.mem]
    simp only [total, dotProd, w32, BitVec.ofNat_add, BitVec.add_assoc]
  · rw [ctrl.2.2.2.1, vals.2.1, inv.mem]
    simp only [total, dotProd, w32, BitVec.ofNat_add, BitVec.add_assoc]
  · rw [ctrl.2.2.2.1, vals.2.2.1, inv.c3]
  · rw [ctrl.2.2.2.1, vals.2.2.2, inv.c7]
  · rw [ctrl.2.2.1]
    congr 1
    have leftEq : (p.gpr .ecx+4).toNat = W.toNat+x+4*(i+1) := by
      have := lptr
      rw [PtrAt, ctrl.1, Nat.mod_eq_of_lt (by omega)] at this
      simpa only [Nat.add_assoc] using this
    rw [leftEq]
    by_cases re : r = .ebp
    · rw [ite_eq_left re]
      have rightEq : (p.gpr .ebp-4).toNat = W.toNat+(y-4*(i+1)) := by
        have := rptr
        rw [PtrAt, ctrl.2.1, Nat.mod_eq_of_lt (by omega)] at this
        exact this
      rw [rightEq]
      have h := cmp (i+1) (by omega)
      rw [ite_eq_left re] at h
      simp only [h]
    · rw [ite_eq_right re]
      obtain rfl : r = .ebx := hr.resolve_left re
      rw [frame.1.1 _ (by decide), inv.keep.1 _ (by decide)]
      have h := cmp (i+1) (by omega)
      simp only [show Reg.ebx ≠ Reg.ebp by decide, ↓reduceIte] at h
      simp only [h]

theorem dotLoop_ok {s : State} {W : Addr} {L x y K : Nat} {lo hi : BitVec 64}
    {r : Reg} (hr : r = .ebp ∨ r = .ebx) (ws : Ws s W L)
    (left : PtrAt s W .ecx x) (right : PtrAt s W .ebp y)
    (low : s.xmm .xmm0 = packed lo) (high : s.xmm .xmm1 = packed hi)
    (hK : 0 < K) (hl : x+4*K < L) (hy : y+4 ≤ L) (hk : 4*K ≤ y)
    (cmp : ∀ j ≤ K, (W.toNat+x+4*j <
      if r = .ebp then W.toNat+(y-4*j) else (s.gpr .ebx).toNat) ↔ j<K) :
    WP isa (.loop (.block (VG.Impl.Mont.X86.Rt.Square.prod ++ ctl r)) .b) s fun t =>
      DotI s W L x y lo hi K t := by
  have start : DotI s W L x y lo hi 0 s :=
    ⟨ws, Keeps.refl _ _, rfl, by simpa using left, by simpa using right,
      by simpa [total] using low, by simpa [total] using high, rfl, rfl⟩
  refine WP.loop (M := isa) (fun k t => ∃ i, i+k=K ∧ 0<k ∧ DotI s W L x y lo hi i t) ?_
    K s ⟨0, by omega, hK, start⟩
  intro k t ⟨i, sum, pos, inv⟩
  refine WP.mono (dotStep_ok hr inv (by omega) hl hy hk cmp) fun u ⟨iu, hz⟩ => ?_
  by_cases e : i+1=K
  · left
    refine ⟨?_, ?_⟩
    · change u.cf = some false
      simpa [e] using hz
    · simpa [e] using iu
  · right
    refine ⟨?_, k-1, by omega, i+1, by omega, by omega, iu⟩
    change u.cf = some true
    simpa [show i+1<K by omega] using hz

end VG.Proof.Mont.X86.Square
