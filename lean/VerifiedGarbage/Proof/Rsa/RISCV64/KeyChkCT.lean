module

public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkFn
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkFn
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# The checks of an RSA key on RISC-V: constant time

As on PPC64LE (`Proof/Rsa/PPC64LE/KcCkCT.lean`): two runs with the same
public data (`D`: the arguments, the stack arguments, `n` and `e`) are
related by `Two` (`Proof/Bignum/RISCV64/PreCT.lean`) at each step, both
satisfying the same predicate for the same data, which fixes the registers
the next piece's addresses and branches read; the pieces by the taint
analysis, what each run satisfies after each by correctness (`two_post`).
The taint analysis treats memory as secret, so the code is cut after each
load whose value an address or a branch reads: the working space's address,
the stack arguments, `n`'s first byte, and whether `e` and `n` are valid,
which the one branch tests (`RelCT.ite`). `fn_rel`: `KeyCheck.fn`, from the
function's own pieces (the moves, the valid branch).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.KeyCheck

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.RISCV64.Taint VG.Proof.Mont VG.Proof.Bignum.RISCV64
  VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs saved save restore mov)
open VG.Impl.Rsa.RISCV64.KeyCheck
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)
open VG.Proof.Bignum.RISCV64.Pub (sat)

/-! ## `save`, in two parts -/

/-- The stores of `save`, and the base into `s11`. -/
def save2 : List Instr :=
  (List.range 12).flatMap (fun i => [.store .d (saved i) .t0 (8 * i)]) ++ [mov .s11 .t0]

theorem save_eq (o : Nat) (moves : List Instr) :
    save o ++ moves = [.addSp .t0 0, .load .d .t0 .t0 o] ++ (save2 ++ moves) := by
  simp only [save, save2, List.append_assoc]

/-- `save`'s first part: the working space's address, the stack argument `i`, into `t0`. -/
theorem save1_ok (s₀ : State) {i : Nat} (hi : 8 * i < 2048)
    (hin : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ i) 8) (hal : (stackArgAddr s₀ i).toNat % 8 = 0) :
    WP isa (.block [.addSp .t0 0, .load .d .t0 .t0 (8 * i)]) s₀ fun s =>
      (s.gpr .t0 = stackArg s₀ i ∧ s.mem = s₀.mem ∧ s.sp = s₀.sp) ∧ Keep [.t0] s₀ s := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have e : s₀.sp + BitVec.ofNat 64 0 + BitVec.ofNat 64 (8 * i) = stackArgAddr s₀ i := by
    rw [add_ofNat_zero']; rfl
  have ha : ((s₀.write .t0 (s₀.sp + BitVec.ofNat 64 0)).gpr .t0 + BitVec.ofNat 64 (8 * i)).toNat % 8 = 0 := by
    rw [gpr_write_self, e]; exact hal
  have hin' : InRegions ((s₀.write .t0 (s₀.sp + BitVec.ofNat 64 0)).rd ++ (s₀.write .t0 (s₀.sp + BitVec.ofNat 64 0)).wr)
      ((s₀.write .t0 (s₀.sp + BitVec.ofNat 64 0)).gpr .t0 + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [gpr_write_self, e]; exact hin
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addSp (show 0 < 2048 by decide),
    exec_load_d hi ha hin', Option.some.injEq, exists_eq_left', gpr_write_self, e, mem_write, sp_write,
    and_true]
  first | rfl | exact ⟨rfl, rfl⟩

/-- `save`'s second part: the registers saved. -/
theorem save2_ok (s₀ : State) {B : Addr} {Z : Nat} (hs : Scr s₀ B Z) (hZ : 96 ≤ Z) {s₁ : State}
    (h : (s₁.gpr .t0 = B ∧ s₁.mem = s₀.mem ∧ s₁.sp = s₀.sp) ∧ Keep [.t0] s₀ s₁) :
    WP isa (.block save2) s₁ (Saved s₀ B) := by
  obtain ⟨⟨i0, im, isp⟩, k₁⟩ := h
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI s₀ B)
    (fun k s hk h => save_step s₀ hs hZ hk h) 12 (Nat.le_refl _) s₁
    ⟨k₁, i0, isp, by rw [im]; exact Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s h => ?_)
  have hw : s.gpr .t0 = B := h.t0
  apply WP.of_runBlock
  simp only [mov, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 0 by decide),
    BitVec.ofInt_ofNat, add_ofNat_zero', Option.some.injEq, exists_eq_left', hw]
  refine ⟨(h.keep.trans (Keep.write _ _ _)).mono (by decide), h.sp, ?_, ?_, h.out, h.saved⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (by decide)]; exact hw
  · rw [gpr_write, ite_eq_left_iff.mpr fun e => absurd rfl e]

/-! ## Two runs -/

theorem wp_true_of {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun _ => True := WP.mono h fun _ _ => trivial

theorem pins_of {α : Type} {Φ : α → State → Prop} {rs : List Reg} {f : α → Reg → BitVec 64}
    (h : ∀ a s, Φ a s → ∀ r ∈ rs, s.gpr r = f a r) : Pins Φ rs :=
  fun a s₁ s₂ h₁ h₂ r hr => (h a s₁ h₁ r hr).trans (h a s₂ h₂ r hr).symm

/-- `t0` holds 0 exactly when `e` and `n` are valid, after the tail. -/
theorem t0_iff (b : Bool) (x : BitVec 64) {P : Prop} (h : x = 0 ↔ P) :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0) + BitVec.ofNat 64 1) ||| x = 0 ↔
      (b = true ∧ P) := by
  rw [mask_add_one, h]

/-! ## A function's pieces -/

/-- What the constant-time proof of a key check needs to know of the
function: its precondition and public data, its working space and the
arguments its entry reads, and what its moves establish. -/
structure KC (β : Type) where
  Pre : State → Prop
  D : State → β
  B : State → Addr
  Z : State → Nat
  K : State → Nat
  E : State → Addr
  L : State → Nat
  N : State → Addr
  MV : State → State → Prop

variable {β : Type} (F : KC β)

abbrev KC.eN (s0 : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (F.E s0) (F.L s0))
abbrev KC.nB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (F.N s0) (F.K s0)
abbrev KC.ev (s0 : State) : Prop := Spec.Rsa.exponentValid (F.eN s0) = true
abbrev KC.mv (s0 : State) : Prop := Spec.Rsa.modulusValid (Spec.Rsa.os2ip (F.nB s0)) (F.K s0) = true
abbrev KC.mask (s0 : State) : BitVec 64 :=
  BitVec.ofNat 64 0 - BitVec.ofNat 64 (if Spec.Rsa.exponentValid (sat (F.eN s0)) then 1 else 0)

def KC.C0 (a : β) (s : State) : Prop := F.Pre s ∧ F.D s = a

/-- After the moves. -/
def KC.M2 (s0 v : State) : Prop :=
  F.MV s0 v ∧ KBase (F.B s0) (F.Z s0) s0 v ∧ v.gpr .a4 = off (F.E s0) 0 ∧
    v.gpr .a5 = BitVec.ofNat 64 (F.L s0) ∧ v.gpr .s1 = off (F.N s0) 0 ∧ v.gpr .s2 = BitVec.ofNat 64 (F.K s0)

def KC.S1 (a : β) (t : State) : Prop :=
  ∃ s0, F.C0 a s0 ∧ (t.gpr .t0 = F.B s0 ∧ t.mem = s0.mem ∧ t.sp = s0.sp) ∧ Keep [.t0] s0 t

def KC.S2 (a : β) (v : State) : Prop := ∃ s0, F.C0 a s0 ∧ F.M2 s0 v

def KC.S3 (a : β) (u : State) : Prop :=
  ∃ s0 v, F.C0 a s0 ∧ F.M2 s0 v ∧ (u.gpr .s7 = BitVec.ofNat 64 (sat (F.eN s0)) ∧ u.mem = v.mem) ∧
    Keep tailRegs v u

def KC.S4 (a : β) (y : State) : Prop :=
  ∃ s0 v, F.C0 a s0 ∧ F.M2 s0 v ∧ (y.gpr .a5 = F.mask s0 ∧ y.gpr .a4 = BitVec.ofNat 64 (sat (F.eN s0)) <<< 31 ∧
    y.gpr .s7 = off (F.N s0) 0 ∧ y.gpr .s8 = BitVec.ofNat 64 (F.K s0) ∧ y.mem = v.mem) ∧ Keep tailRegs v y

def KC.S5 (a : β) (z : State) : Prop :=
  ∃ s0 v, F.C0 a s0 ∧ F.M2 s0 v ∧ ((z.gpr .s0 = 0 ↔ ((F.nB s0).getD (F.K s0 - 1) 0).toNat % 2 = 1) ∧
    z.gpr .t4 = BitVec.ofNat 64 ((F.nB s0).getD 0 0).toNat ∧ z.gpr .a5 = F.mask s0 ∧
    z.gpr .a4 = BitVec.ofNat 64 (sat (F.eN s0)) <<< 31 ∧ z.gpr .s8 = BitVec.ofNat 64 (F.K s0) ∧ z.mem = v.mem) ∧
    Keep tailRegs v z

def KC.S6 (a : β) (z : State) : Prop :=
  ∃ s0 v, F.C0 a s0 ∧ F.M2 s0 v ∧ ((z.gpr .s0 = 0 ↔ F.mv s0) ∧ z.gpr .a5 = F.mask s0 ∧
    z.gpr .a4 = BitVec.ofNat 64 (sat (F.eN s0)) <<< 31 ∧ z.mem = v.mem) ∧ Keep tailRegs v z

def KC.S7 (a : β) (t : State) : Prop :=
  ∃ s0 v, F.C0 a s0 ∧ F.M2 s0 v ∧ ((t.gpr .t0 = 0 ↔ F.ev s0 ∧ F.mv s0) ∧
    t.gpr .a4 = BitVec.ofNat 64 (sat (F.eN s0)) <<< 31 ∧ t.mem = v.mem) ∧ Keep tailRegs v t

def KC.S8 (a : β) (u : State) : Prop := ∃ s0, F.C0 a s0 ∧ KBase (F.B s0) (F.Z s0) s0 u

/-- What the function's own proofs give. -/
structure KC.Ok (oS na : Nat) (moves : List Instr) (T : List (Prog isa)) (mvRegs : List Reg) : Prop where
  hk : ∀ s, F.Pre s → KPre s (F.B s) (F.Z s) (F.K s) oS na
  hm : ∀ s, F.Pre s → ∀ u, Saved s (F.B s) u → WP isa (.block moves) u fun v => F.MV s v ∧ v.mem = u.mem ∧
    v.rd = u.rd ∧ v.wr = u.wr ∧ v.gpr .s11 = u.gpr .s11 ∧ v.gpr .a4 = off (F.E s) 0 ∧
    v.gpr .a5 = BitVec.ofNat 64 (F.L s) ∧ v.gpr .s1 = off (F.N s) 0 ∧ v.gpr .s2 = BitVec.ofNat 64 (F.K s)
  hL : ∀ s, F.Pre s → 1 ≤ F.L s ∧ F.L s ≤ 1024
  hE : ∀ s, F.Pre s → (⟨F.E s, F.L s⟩ : Region) ∈ s.rd ∧ (⟨F.E s, F.L s⟩ : Region).Disjoint ⟨F.B s, F.Z s⟩ ∧
    (F.E s).toNat + F.L s ≤ 2 ^ 64
  hN : ∀ s, F.Pre s → (⟨F.N s, F.K s⟩ : Region) ∈ s.rd ∧ (⟨F.N s, F.K s⟩ : Region).Disjoint ⟨F.B s, F.Z s⟩ ∧
    (F.N s).toNat + F.K s ≤ 2 ^ 64
  hv : ∀ s, F.Pre s → ∀ v t, F.MV s v → Keep tailRegs v t → KBase (F.B s) (F.Z s) s t →
    t.gpr .a4 = BitVec.ofNat 64 (sat (F.eN s)) <<< 31 → F.ev s → F.mv s →
    WP isa (seqs T) t fun u => KBase (F.B s) (F.Z s) s u
  hsame : ∀ s t, F.Pre s → F.Pre t → F.D s = F.D t → F.B s = F.B t ∧ F.E s = F.E t ∧ F.N s = F.N t ∧
    F.L s = F.L t ∧ F.K s = F.K t ∧ Spec.Rsa.bytesAt s.mem (F.E s) (F.L s) = Spec.Rsa.bytesAt t.mem (F.E t) (F.L t) ∧
    F.nB s = F.nB t ∧ ∀ r ∈ argRegs, s.gpr r = t.gpr r
  hmv : ∀ s t v w, F.Pre s → F.Pre t → F.D s = F.D t → F.MV s v → F.MV t w → ∀ r ∈ mvRegs, v.gpr r = w.gpr r
  hmr : ∀ r ∈ mvRegs, r ∉ tailRegs

theorem KC.M2.base {F : KC β} {s0 v t : State} (h : F.M2 s0 v) (k : Keep tailRegs v t) (hm : t.mem = v.mem) :
    KBase (F.B s0) (F.Z s0) s0 t := h.2.1.of_regs k hm

theorem KC.M2.bytesE {F : KC β} {oS na : Nat} {moves : List Instr} {T : List (Prog isa)} {mvRegs : List Reg} {s0 v : State} (H : F.Ok oS na moves T mvRegs) (h0 : F.Pre s0) (h : F.M2 s0 v) :
    Spec.Rsa.bytesAt v.mem (F.E s0) (F.L s0) = Spec.Rsa.bytesAt s0.mem (F.E s0) (F.L s0) :=
  bytes_frame h.2.1 (H.hE s0 h0).2.1 (H.hE s0 h0).2.2

theorem KC.M2.bytesN {F : KC β} {oS na : Nat} {moves : List Instr} {T : List (Prog isa)} {mvRegs : List Reg} {s0 v : State} (H : F.Ok oS na moves T mvRegs) (h0 : F.Pre s0) (h : F.M2 s0 v) :
    Spec.Rsa.bytesAt v.mem (F.N s0) (F.K s0) = F.nB s0 :=
  bytes_frame h.2.1 (H.hN s0 h0).2.1 (H.hN s0 h0).2.2

end VG.Proof.Rsa.RISCV64.KeyCheck
