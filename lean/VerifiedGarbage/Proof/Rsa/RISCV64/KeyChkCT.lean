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

theorem argRegs_ne_t0 : ∀ r ∈ argRegs, r ∉ ([.t0] : List Reg) := by decide

theorem zero_of_eval {s : State} (h : isa.eval (.zero .t0) s = some true) : s.gpr .t0 = 0 := by
  rw [Steps.eval_zero] at h; simpa using h

theorem ne_of_eval {s : State} (h : isa.eval (.zero .t0) s = some false) : s.gpr .t0 ≠ 0 := by
  rw [Steps.eval_zero] at h; simpa using h

/-- `KeyCheck.fn` is constant time, from the function's pieces. -/
theorem fn_rel {oS na : Nat} {moves : List Instr} {loads body : List (Prog isa)} {mvRegs : List Reg}
    (H : F.Ok oS na moves ([setup, .block eArr] ++ loads ++ body ++ [.block ret]) mvRegs) (hoS : 8 * oS < 2048)
    {hc1 hc2 hc3 : VG.Taint.Hint taint.T}
    (hS1 : (taint.check (Taint.ofRegs []) (.block [.addSp .t0 0, .load .d .t0 .t0 (8 * oS)]) hc1).isSome = true)
    (hS2 : (taint.check (Taint.ofRegs (.t0 :: argRegs)) (.block (save2 ++ moves)) hc2).isSome = true)
    (hT : (taint.check (Taint.ofRegs (.s11 :: mvRegs))
      (seqs ([setup, .block eArr] ++ loads ++ body ++ [.block ret])) hc3).isSome = true) :
    RelCT isa (Two F.C0) (fn (8 * oS) moves loads body) fun _ _ => True := by
  have same : ∀ {a : β} {x y : State}, F.C0 a x → F.C0 a y → F.B x = F.B y ∧ F.E x = F.E y ∧ F.N x = F.N y ∧
      F.L x = F.L y ∧ F.K x = F.K y ∧
      Spec.Rsa.bytesAt x.mem (F.E x) (F.L x) = Spec.Rsa.bytesAt y.mem (F.E y) (F.L y) ∧
      F.nB x = F.nB y ∧ ∀ r ∈ argRegs, x.gpr r = y.gpr r :=
    fun hx hy => H.hsame _ _ hx.1 hy.1 (hx.2.trans hy.2.symm)
  have sameEv : ∀ {a : β} {x y : State}, F.C0 a x → F.C0 a y → (F.ev x ↔ F.ev y) := fun hx hy => by
    obtain ⟨-, -, -, -, -, he, -⟩ := same hx hy
    simp only [KC.ev, KC.eN, he]
  have sameMv : ∀ {a : β} {x y : State}, F.C0 a x → F.C0 a y → (F.mv x ↔ F.mv y) := fun hx hy => by
    obtain ⟨-, -, -, -, hk, -, hn, -⟩ := same hx hy
    simp only [KC.mv, hk, hn]
  have rdOf : ∀ {s0 v : State}, F.Pre s0 → KBase (F.B s0) (F.Z s0) s0 v → ∀ {P : Addr} {M : Nat},
      (⟨P, M⟩ : Region) ∈ s0.rd → P.toNat + M ≤ 2 ^ 64 → ∀ i < M, InRegions (v.rd ++ v.wr) (off P i) 1 :=
    fun _ bv _ _ hP wP i hi =>
      ⟨_, List.mem_append_left _ (by rw [bv.rd]; exact hP), Offset.contains_base _ (by omega) (by omega)⟩
  unfold fn
  rw [entry_eq, save_eq]
  refine RelCT.seq (R := Two F.S7) (RelCT.seq (R := Two F.S2) (RelCT.block_append
    (RelCT.seq (R := Two F.S1) ?_ ?_)) ?_) ?_
  · -- `save`'s first part.
    refine two_post (two_taint _ (fun _ _ _ _ _ r hr => absurd hr List.not_mem_nil) hS1) fun a s c0 => ?_
    have hp := H.hk s c0.1
    exact WP.mono (save1_ok s hoS (hp.arg_rd hp.hoS) (hp.arg_al hp.hoS)) fun t ⟨⟨t0, tm, tsp⟩, k⟩ =>
      ⟨s, c0, ⟨t0.trans hp.base, tm, tsp⟩, k⟩
  · -- `save`'s second part and the moves.
    refine two_post (two_taint _ ?_ hS2) fun a s ⟨s0, c0, ht⟩ => ?_
    · rintro a s₁ s₂ ⟨x, hx, ⟨tx, -, -⟩, kx⟩ ⟨y, hy, ⟨ty, -, -⟩, ky⟩ r hr
      have hs := same hx hy
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [tx, ty, hs.1]
      · rw [kx.gpr (argRegs_ne_t0 r hr), ky.gpr (argRegs_ne_t0 r hr), hs.2.2.2.2.2.2.2 r hr]
    have hp := H.hk s0 c0.1
    have hZ : 96 ≤ F.Z s0 := by have := hp.zk; omega
    rw [WP.block_append_iff]
    refine WP.mono (save2_ok s0 (Scr.of_mem hp.wr hp.nowrap hp.al) hZ ht) fun u hu => ?_
    have bu := KBase.of_saved hu hZ
    exact WP.mono (H.hm s0 c0.1 u hu) fun v ⟨mv, vm, vrd, vwr, v11, v4, v5, v1, v2⟩ =>
      ⟨s0, c0, mv, ⟨vrd.trans bu.rd, vwr.trans bu.wr, fun x hx => by rw [vm]; exact bu.frame x hx,
        fun i hi => by rw [vm]; exact bu.hdr i hi, v11.trans bu.s11⟩, v4, v5, v1, v2⟩
  · -- The tail.
    unfold tail
    rw [show VG.Impl.Bignum.RISCV64.Precompute.check =
      .seq (.block VG.Impl.Bignum.RISCV64.Precompute.check1) VG.Impl.Bignum.RISCV64.Precompute.check2 from rfl]
    refine RelCT.seq (R := Two F.S3) ?_ (RelCT.seq (R := Two F.S4) ?_
      (RelCT.seq (R := Two F.S6) (RelCT.seq (R := Two F.S5) ?_ ?_) ?_))
    · -- `readE`.
      refine two_post (two_taint [.a4, .a5] ?_ (by taint_decide)) fun a v ⟨s0, c0, m⟩ => ?_
      · rintro a s₁ s₂ ⟨x, hx, mx⟩ ⟨y, hy, my⟩ r hr
        have hs := same hx hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [mx.2.2.1, my.2.2.1, hs.2.1]
        · rw [mx.2.2.2.1, my.2.2.2.1, hs.2.2.2.1]
      have hL := H.hL s0 c0.1
      have hE := H.hE s0 c0.1
      refine WP.mono (Pub.readE_ok m.2.2.1 m.2.2.2.1 hL.1 (by omega) (rdOf c0.1 m.2.1 hE.1 hE.2.2))
        fun u ⟨⟨u7, um⟩, ku⟩ => ⟨s0, v, c0, m, ⟨by rw [u7, m.bytesE H c0.1], um⟩, ku.mono (by decide)⟩
    · -- `e` checked, and the moves to `check`.
      refine two_post (two_taint [.s1, .s2] ?_ (by taint_decide)) fun a u ⟨s0, v, c0, m, ⟨u7, um⟩, ku⟩ => ?_
      · rintro a s₁ s₂ ⟨x, vx, hx, mx, -, kx⟩ ⟨y, vy, hy, my, -, ky⟩ r hr
        have hs := same hx hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [kx.gpr (by decide), ky.gpr (by decide), mx.2.2.2.2.1, my.2.2.2.2.1, hs.2.2.1]
        · rw [kx.gpr (by decide), ky.gpr (by decide), mx.2.2.2.2.2, my.2.2.2.2.2, hs.2.2.2.2.1]
      have hsat : sat (F.eN s0) ≤ 2 ^ 33 := by unfold sat; omega
      refine WP.mono (tB_ok u7 hsat ((ku.gpr (by decide)).trans m.2.2.2.2.1) ((ku.gpr (by decide)).trans m.2.2.2.2.2))
        fun y ⟨⟨y5, y4, y7, y8, ym⟩, ky⟩ => ⟨s0, v, c0, m, ⟨y5, y4, y7, y8, ym.trans um⟩, (ku.trans ky).mono (by decide)⟩
    · -- `check`'s first part.
      refine two_post (two_taint [.s7, .s8] ?_ (by taint_decide)) fun a y ⟨s0, v, c0, m, ⟨y5, y4, y7, y8, ym⟩, ky⟩ => ?_
      · rintro a s₁ s₂ ⟨x, vx, hx, mx, ⟨-, -, x7, x8, -⟩, -⟩ ⟨y, vy, hy, my, ⟨-, -, z7, z8, -⟩, -⟩ r hr
        have hs := same hx hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [x7, z7, hs.2.2.1]
        · rw [x8, z8, hs.2.2.2.2.1]
      have hp := H.hk s0 c0.1
      have hN := H.hN s0 c0.1
      have hk := hp.k64
      have hlen : (F.nB s0).length = F.K s0 := by simp [KC.nB, Spec.Rsa.bytesAt]
      have hrd : ∀ i < F.K s0, InRegions (y.rd ++ y.wr) (off (F.N s0) i) 1 := fun i hi => by
        rw [ky.2.1, ky.2.2]; exact rdOf c0.1 m.2.1 hN.1 hN.2.2 i hi
      have eb := m.bytesN H c0.1
      refine WP.mono (check1_ok (nb := F.nB s0) y7 y8 hk hlen hrd fun i hi => by
          rw [← Pre.getD_of_lt (by omega), ym, ← eb]
          simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi])
        fun z ⟨⟨z0, z4, zm⟩, kz⟩ => ⟨s0, v, c0, m, ⟨by rw [z0, Pre.getD_of_lt (by omega)],
          by rw [z4, Pre.getD_of_lt (by omega)], by rw [kz.gpr (by decide), y5], by rw [kz.gpr (by decide), y4],
          by rw [kz.gpr (by decide), y8], zm.trans ym⟩, (ky.trans kz).mono (by decide)⟩
    · -- `check`'s second part.
      refine two_post (two_taint [.t4, .s8] ?_ (by taint_decide))
        fun a z ⟨s0, v, c0, m, ⟨z0, z4, z5, z4', z8, zm⟩, kz⟩ => ?_
      · rintro a s₁ s₂ ⟨x, vx, hx, mx, ⟨-, x4, -, -, x8, -⟩, -⟩ ⟨y, vy, hy, my, ⟨-, y4, -, -, y8, -⟩, -⟩ r hr
        have hs := same hx hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [x4, y4, hs.2.2.2.2.2.2.1]
        · rw [x8, y8, hs.2.2.2.2.1]
      have hp := H.hk s0 c0.1
      have hk := hp.k64
      have hk' := hp.k1024
      have hlen : (F.nB s0).length = F.K s0 := by simp [KC.nB, Spec.Rsa.bytesAt]
      refine WP.mono (check2_ok (nb := F.nB s0) z8 hk hk' hlen (by rw [z0, Pre.getD_of_lt (by omega)])
        (by rw [z4, Pre.getD_of_lt (by omega)])) fun x ⟨x0, xm, kx⟩ =>
          ⟨s0, v, c0, m, ⟨x0, by rw [kx.gpr (by decide), z5], by rw [kx.gpr (by decide), z4'], xm.trans zm⟩,
            (kz.trans kx).mono (by decide)⟩
    · -- The tail's last block.
      refine two_post (two_taint [] (fun _ _ _ _ _ r hr => absurd hr List.not_mem_nil) (by taint_decide))
        fun a z ⟨s0, v, c0, m, ⟨z0, z5, z4, zm⟩, kz⟩ => ?_
      refine WP.mono (tE_ok z) fun t ⟨⟨t0, tm⟩, kt⟩ => ⟨s0, v, c0, m, ⟨?_, by rw [kt.gpr (by decide), z4],
        tm.trans zm⟩, (kz.trans kt).mono (by decide)⟩
      rw [t0, z5, t0_iff _ _ z0, exponentValid_sat]
  · -- The branch and the exit.
    refine RelCT.seq (R := Two F.S8) (RelCT.ite ?_ ?_ ?_) ?_
    · rintro s₁ s₂ ⟨a, ⟨x, vx, hx, mx, ⟨x0, -, -⟩, -⟩, ⟨y, vy, hy, my, ⟨y0, -, -⟩, -⟩, -⟩
      rw [Steps.eval_zero, Steps.eval_zero]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, x0, y0, sameEv hx hy, sameMv hx hy]
    · -- The valid branch.
      refine RelCT.mono (two_post (Φ := fun a s => F.S7 a s ∧ s.gpr .t0 = 0) (two_taint _ ?_ hT) ?_) ?_ fun _ _ h => h
      · rintro a s₁ s₂ ⟨⟨x, vx, hx, mx, ⟨-, -, xm⟩, kx⟩, -⟩ ⟨⟨y, vy, hy, my, ⟨-, -, ym⟩, ky⟩, -⟩ r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · rw [(mx.base kx xm).s11, (my.base ky ym).s11, (same hx hy).1]
        · rw [kx.gpr (H.hmr r hr), ky.gpr (H.hmr r hr)]
          exact H.hmv _ _ _ _ hx.1 hy.1 (hx.2.trans hy.2.symm) mx.1 my.1 r hr
      · rintro a t ⟨⟨s0, v, c0, m, ⟨t0, t4, tm⟩, kt⟩, hz⟩
        obtain ⟨ev, mv⟩ := t0.mp hz
        exact WP.mono (H.hv s0 c0.1 v t m.1 kt (m.base kt tm) t4 ev mv) fun u hu => ⟨s0, c0, hu⟩
      · rintro s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hc⟩
        have z1 := zero_of_eval hc
        obtain ⟨x, vx, hx, mx, ⟨x0, x4, xm⟩, kx⟩ := h₁
        obtain ⟨y, vy, hy, my, ⟨y0, y4, ym⟩, ky⟩ := h₂
        obtain ⟨ev, mv⟩ := x0.mp z1
        exact ⟨a, ⟨⟨x, vx, hx, mx, ⟨x0, x4, xm⟩, kx⟩, z1⟩,
          ⟨⟨y, vy, hy, my, ⟨y0, y4, ym⟩, ky⟩,
            y0.mpr ⟨(sameEv hx hy).mp ev, (sameMv hx hy).mp mv⟩⟩, hsp⟩
    · -- The other branch.
      refine RelCT.mono (two_post (Φ := F.S7) (two_taint [] (fun _ _ _ _ _ r hr => absurd hr List.not_mem_nil)
        (by taint_decide)) ?_) (fun _ _ h => h.1) fun _ _ h => h
      rintro a t ⟨s0, v, c0, m, ⟨-, -, tm⟩, kt⟩
      have bt := m.base kt tm
      refine WP.mono (WP.keep [.a0] (Q := fun u => u.mem = t.mem) (by
        have e : exec (.li .a0 0) t = some (t.write .a0 (BitVec.ofNat 64 0)) := by
          rw [exec_li (by decide)]; rfl
        brun [ret0, e]) (by rfl) (by rfl)) fun u ⟨um, ku⟩ => ⟨s0, c0, bt.of_regs ku um⟩
    · -- `restore`.
      refine two_taint [.s11] ?_ (by taint_decide)
      rintro a s₁ s₂ ⟨x, hx, bx⟩ ⟨y, hy, by'⟩ r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      rw [bx.s11, by'.s11, (same hx hy).1]

end VG.Proof.Rsa.RISCV64.KeyCheck
