module

public import VerifiedGarbage.Impl.AesCcm.AArch64
public import VerifiedGarbage.Proof.AesCcm.AArch64.Env
public import VerifiedGarbage.Proof.AesCcm.Mac
public import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.AesCcm.Words
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesCcm.AArch64.Blocks
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateCorrect
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Spec.Ccm.Contract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Ccm
public import VerifiedGarbage.TCB.AArch64.Isa
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.TCB.Code
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.Framework.Taint

/-! ### `AesCcm.AArch64.Entry`, which this module and modules that import it used -/

section

/-!
# AES-CCM on AArch64: the arguments and the entry

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the facts the proofs use about the arguments (`Args`,
`args_of_seal`, `args_of_open`). `entry` loads `work`, the tag length and
`tag` from the stack, saves our caller's registers at `W + 128` and keeps the
arguments in registers and in `W` (`entry_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm save saved)
open VG.Proof.AesGcm.AArch64 (savedMem savedR SavedAt save_ok save_ok256 covers_prefix readW_writeW_other savedMem_slot savedMem_frame
  covers_of_mem covers_left in_off)

/-- The public values of the arguments of `s`, with `384 + Nw` bytes of `work`. -/
def cxOf (Nw : Nat) (hNw : Nw ≤ 2176) (s : State) : Cx where
  K := s.gpr .x0
  W := stackArg s 2
  D := s.gpr .x6
  A := s.gpr .x4
  R := (s.gpr .x1).toNat
  tl := (stackArg s 1).toNat
  n := (s.gpr .x7).toNat
  al := (s.gpr .x5).toNat
  nl := (s.gpr .x3).toNat
  SP := s.sp
  T := stackArg s 0
  N := Nw
  N_le := hNw

/-- What `seal` and `open` are given: the public values `c`, and the nonce at
`N`. -/
structure Args (c : Cx) (N : Addr) (s : State) : Prop where
  lay : Lay c
  x0 : s.gpr .x0 = c.K
  x1 : s.gpr .x1 = BitVec.ofNat 64 c.R
  x2 : s.gpr .x2 = N
  x3 : s.gpr .x3 = BitVec.ofNat 64 c.nl
  x4 : s.gpr .x4 = c.A
  x5 : s.gpr .x5 = BitVec.ofNat 64 c.al
  x6 : s.gpr .x6 = c.D
  x7 : s.gpr .x7 = BitVec.ofNat 64 c.n
  sp : s.sp = c.SP
  w : stackArg s 2 = c.W
  tl : stackArg s 1 = BitVec.ofNat 64 c.tl
  t : stackArg s 0 = c.T
  perm : Perm c s
  nonce : Buf c s N c.nl
  nd : (⟨N, c.nl⟩ : Region).Disjoint ⟨c.D, c.n⟩
  argsC : Covers [args s] (s.rd ++ s.wr)
  argsW : (args s).Disjoint ⟨c.W, 384 + c.N⟩
  argsD : (args s).Disjoint ⟨c.D, c.n⟩

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- `Args` from the layout, with the buffers covered as each function's
permissions say. -/
theorem args_of_lay {Nw : Nat} (hNw : Nw ≤ 2176) {s : State} (h : oneLay Nw s)
    (hk : Covers [⟨s.gpr .x0, 240⟩] (s.rd ++ s.wr)) (hN : Covers [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨s.gpr .x4, (s.gpr .x5).toNat⟩] (s.rd ++ s.wr)) (ha : Covers [args s] (s.rd ++ s.wr))
    (hT : Covers [⟨stackArg s 0, (stackArg s 1).toNat⟩] (s.rd ++ s.wr))
    (hD : Covers [⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.wr) (hW : Covers [⟨stackArg s 2, 384 + Nw⟩] s.wr) :
    Args (cxOf Nw hNw s) (s.gpr .x2) s := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, b1, b2, b3, b4, b5, b6, _, hR, hv⟩ := h
  simp only [Spec.Ccm.valid, Spec.Ccm.tagLenOk, Spec.Ccm.nonceLenOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨⟨ht4, ht16⟩, hte⟩, hn7, hn13⟩, hp⟩, -⟩ := hv
  rw [Nat.pow_mul] at hp
  exact {
    lay := ⟨b1, b6, b4, b3, d2, d1, d9, d6, d5, hR, BitVec.isLt _, BitVec.isLt _, ht4, ht16, hte, hn7, hn13, hp,
      b5, d8, d7⟩
    x0 := rfl
    x1 := (ofNat_toNat64 _).symm
    x2 := rfl
    x3 := (ofNat_toNat64 _).symm
    x4 := rfl
    x5 := (ofNat_toNat64 _).symm
    x6 := rfl
    x7 := (ofNat_toNat64 _).symm
    sp := rfl
    w := rfl
    tl := (ofNat_toNat64 _).symm
    t := rfl
    perm := ⟨hk, hW, hD, hA, hT⟩
    nonce := ⟨hN, BitVec.isLt _, b2, d4⟩
    nd := d3
    argsC := ha
    argsW := d11.symm
    argsD := d10.symm }

/-- `seal`'s arguments, and its tag, to write. -/
theorem args_of_seal {Nw : Nat} (hNw : Nw ≤ 2176) {s : State} (h : sealPre Nw s) :
    Args (cxOf Nw hNw s) (s.gpr .x2) s ∧ Covers [⟨stackArg s 0, (stackArg s 1).toNat⟩] s.wr := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .x0, 240⟩ : Region), ⟨s.gpr .x2, (s.gpr .x3).toNat⟩, ⟨s.gpr .x4, (s.gpr .x5).toNat⟩,
      args s], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region), ⟨stackArg s 0, (stackArg s 1).toNat⟩,
      ⟨stackArg s 2, 384 + Nw⟩], Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨args_of_lay hNw hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp))
    (covers_left (mwr _ (by simp))) (mwr _ (by simp)) (mwr _ (by simp)), mwr _ (by simp)⟩

/-- `open`'s arguments, with its received tag, to read. -/
theorem args_of_open {Nw : Nat} (hNw : Nw ≤ 2176) {s : State} (h : openPre Nw s) : Args (cxOf Nw hNw s) (s.gpr .x2) s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .x0, 240⟩ : Region), ⟨s.gpr .x2, (s.gpr .x3).toNat⟩, ⟨s.gpr .x4, (s.gpr .x5).toNat⟩,
      ⟨stackArg s 0, (stackArg s 1).toNat⟩, args s], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region), ⟨stackArg s 2, 384 + Nw⟩], Covers [r] s.wr :=
    fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact args_of_lay hNw hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp))
    (mwr _ (by simp)) (mwr _ (by simp))

/-! ## The entry -/

/-- The memory after the entry: the registers saved and the arguments kept. -/
def entryMem (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Mem :=
  ((((savedMem m W g).writeW (W + BitVec.ofNat 64 216) (g .x4)).writeW (W + BitVec.ofNat 64 224) (g .x5)).writeW
    (W + BitVec.ofNat 64 232) (g .x3)).writeW (W + BitVec.ofNat 64 240) (g .x11)

/-- What the entry writes. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 120⟩

theorem entry_contains (W : Addr) {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 248) :
    (entryR W).Contains (W + BitVec.ofNat 64 d) 8 := by
  rw [show W + BitVec.ofNat 64 d = (W + BitVec.ofNat 64 128) + BitVec.ofNat 64 (d - 128) from
    (Offset.add_add_eq W (by omega_using [h₁])).symm]
  exact Offset.contains_base _ (by omega_using [h₂]) (by omega_using [h₂])

theorem entryMem_frame (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Frame [entryR W] m (entryMem m W g) := by
  have c (d : Nat) (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 248) := entry_contains W h₁ h₂
  exact (((((savedMem_frame m W g).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by first | decide | omega) (by first | decide | omega)⟩).writeW
    (List.mem_singleton_self _) _ (c 216 (by first | decide | omega) (by first | decide | omega))).writeW
    (List.mem_singleton_self _) _ (c 224 (by first | decide | omega) (by first | decide | omega))).writeW
    (List.mem_singleton_self _) _ (c 232 (by first | decide | omega) (by first | decide | omega))).writeW
    (List.mem_singleton_self _) _ (c 240 (by first | decide | omega) (by first | decide | omega))

theorem entryMem_saved (m : Mem) (W : Addr) {g : Reg → BitVec 64} {s₀ : State}
    (hg : ∀ p ∈ saved, g p.1 = s₀.gpr p.1) : SavedAt (entryMem m W g) W s₀ := by
  have h₀ : SavedAt (savedMem m W g) W s₀ := fun p hp => (savedMem_slot m W g p hp).trans (hg p hp)
  refine h₀.frame (rs := [⟨W + BitVec.ofNat 64 216, 32⟩]) ?_ ?_
  · have c (d : Nat) (h₁ : 216 ≤ d) (h₂ : d + 8 ≤ 248) :
        (⟨W + BitVec.ofNat 64 216, 32⟩ : Region).Contains (W + BitVec.ofNat 64 d) 8 := by
      rw [show W + BitVec.ofNat 64 d = (W + BitVec.ofNat 64 216) + BitVec.ofNat 64 (d - 216) from
        (Offset.add_add_eq W (by omega_using [h₁])).symm]
      exact Offset.contains_base _ (by omega_using [h₂]) (by omega_using [h₂])
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 216 (by first | decide | omega) (by first | decide | omega))).writeW
      (List.mem_singleton_self _) _ (c 224 (by first | decide | omega) (by first | decide | omega))).writeW
      (List.mem_singleton_self _) _ (c 232 (by first | decide | omega) (by first | decide | omega))).writeW
      (List.mem_singleton_self _) _ (c 240 (by first | decide | omega) (by first | decide | omega))
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint W (.inl (by first | decide | omega)) (by first | decide | omega) (by first | decide | omega)

theorem entryMem_slot (m : Mem) (W : Addr) (g : Reg → BitVec 64) :
    (entryMem m W g).readW (W + BitVec.ofNat 64 216) 64 = g .x4 ∧
    (entryMem m W g).readW (W + BitVec.ofNat 64 224) 64 = g .x5 ∧
    (entryMem m W g).readW (W + BitVec.ofNat 64 232) 64 = g .x3 ∧
    (entryMem m W g).readW (W + BitVec.ofNat 64 240) 64 = g .x11 := by
  simp only [entryMem]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  repeat (first
    | rw [Mem.readW_writeW_self64]
    | rw [readW_writeW_other _ _ _ (by first | decide | omega) (by first | decide | omega) (by first | decide | omega)])

/-- What the entry leaves. -/
structure Entered (c : Cx) (N : Addr) (s s₁ : State) : Prop where
  env : Env c s₁
  slots : Slots c s₁.mem
  saved : SavedAt s₁.mem c.W s
  frame : Frame [entryR c.W] s.mem s₁.mem
  x2 : s₁.gpr .x2 = N
  x3 : s₁.gpr .x3 = BitVec.ofNat 64 c.nl
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

/-- The loads of `work`, the tag length and `tag`. -/
theorem ldr_ok {c : Cx} {N : Addr} {s : State} (Ar : Args c N s) :
    WP isa (.block [.ldrSp .x9 16, .ldrSp .x10 8, .ldrSp .x11 0]) s fun s₀ => s₀.gpr .x9 = c.W ∧
      s₀.gpr .x10 = BitVec.ofNat 64 c.tl ∧ s₀.gpr .x11 = c.T ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s₀.gpr r = s.gpr r) ∧ s₀.sp = s.sp ∧
      s₀.mem = s.mem ∧ s₀.rd = s.rd ∧ s₀.wr = s.wr := by
  have hA : Covers [⟨s.sp, 24⟩] (s.rd ++ s.wr) := by
    have := Ar.argsC
    simpa [args, stackArgAddr] using this
  have a₀ : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa using in_off (d := 0) (n := 8) hA (by first | decide | omega) (by first | decide | omega)
  have a₈ : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 :=
    in_off (d := 8) (n := 8) hA (by first | decide | omega) (by first | decide | omega)
  have a₁₆ : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 16) 8 :=
    in_off (d := 16) (n := 8) hA (by first | decide | omega) (by first | decide | omega)
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [a₀, a₈, a₁₆], rfl⟩ fun s₀ hs₀ => ?_
  subst hs₀
  refine ⟨?_, ?_, ?_, fun r h₁ h₂ h₃ => by simp [gpr_write, h₁, h₂, h₃], rfl, rfl, rfl, rfl⟩
  · rw [← Ar.w]
    simp [gpr_write, stackArg, stackArgAddr, Mem.readW]
  · rw [← Ar.tl]
    simp [gpr_write, stackArg, stackArgAddr, Mem.readW]
  · rw [← Ar.t]
    simp [gpr_write, stackArg, stackArgAddr, Mem.readW]

/-- After the entry. -/
theorem entry_ok {c : Cx} {N : Addr} {s : State} (Ar : Args c N s) :
    WP isa (.block entry) s (Entered c N s) := by
  refine WP.block_append (WP.block_append (WP.mono (ldr_ok Ar) fun s₀ ⟨x9₀, x10₀, x11₀, g₀, sp₀, m₀, rd₀, wr₀⟩ => ?_))
  have hperm₀ : Perm c s₀ := Ar.perm.of_eq rd₀ wr₀
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok256 s₀ .x9 x9₀ (covers_prefix hperm₀.w (by omega))
  have w (d : Nat) (h : d + 8 ≤ 384 + c.N) := in_off hperm₀.w h (by have := c.N_le; omega)
  rw [← wr₁] at w
  have gx : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s₁.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by rw [g₁, g₀ r h₁ h₂ h₃]
  have x9₁ : s₁.gpr .x9 = c.W := by rw [g₁, x9₀]
  have x10₁ : s₁.gpr .x10 = BitVec.ofNat 64 c.tl := by rw [g₁, x10₀]
  have w₁ := w 216 (by first | decide | omega)
  have w₂ := w 224 (by first | decide | omega)
  have w₃ := w 232 (by first | decide | omega)
  have w₄ := w 240 (by first | decide | omega)
  obtain ⟨s₂, run₂, m₂, y19, y20, y21, y22, y27, y28, y2, y3, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x9, mov .x20 .x10, mov .x21 .x0, mov .x22 .x1, .str .x .x4 .x19 aadO,
        .str .x .x5 .x19 alenO, .str .x .x3 .x19 nlenO, .str .x .x11 .x19 tagO, mov .x27 .x6, mov .x28 .x7] s₁ =
        some s₂ ∧
      s₂.mem = (((s₁.mem.writeW (c.W + BitVec.ofNat 64 216) (s₁.gpr .x4)).writeW (c.W + BitVec.ofNat 64 224)
        (s₁.gpr .x5)).writeW (c.W + BitVec.ofNat 64 232) (s₁.gpr .x3)).writeW (c.W + BitVec.ofNat 64 240)
        (s₁.gpr .x11) ∧
      s₂.gpr .x19 = s₁.gpr .x9 ∧ s₂.gpr .x20 = s₁.gpr .x10 ∧ s₂.gpr .x21 = s₁.gpr .x0 ∧
      s₂.gpr .x22 = s₁.gpr .x1 ∧ s₂.gpr .x27 = s₁.gpr .x6 ∧ s₂.gpr .x28 = s₁.gpr .x7 ∧
      s₂.gpr .x2 = s₁.gpr .x2 ∧ s₂.gpr .x3 = s₁.gpr .x3 ∧
      s₂.sp = s₁.sp ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by carun [tagO, x9₁, w₁, w₂, w₃, w₄], ?_⟩
    simp only [Mem.writeW, gpr_write, mem_write, sp_write, rd_write, wr_write, ite_true, ite_false, reduceCtorEq,
      x9₁, and_self, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq, true_and]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have hm : s₂.mem = entryMem s.mem c.W s₀.gpr := by
    rw [m₂, m₁, m₀, entryMem, g₁]
  obtain ⟨e₁, e₂, e₃, e₄⟩ := entryMem_slot s.mem c.W s₀.gpr
  rw [g₀ .x4 (by first | decide | omega) (by first | decide | omega) (by first | decide | omega)] at e₁
  rw [g₀ .x5 (by first | decide | omega) (by first | decide | omega) (by first | decide | omega)] at e₂
  rw [g₀ .x3 (by first | decide | omega) (by first | decide | omega) (by first | decide | omega)] at e₃
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [y19, x9₁]
  · rw [y20, x10₁]
  · rw [y21, gx .x0 (by first | decide | omega) (by first | decide | omega) (by first | decide | omega), Ar.x0]
  · rw [y22, gx .x1 (by first | decide | omega) (by first | decide | omega) (by first | decide | omega), Ar.x1]
  · rw [y27, gx .x6 (by first | decide | omega) (by first | decide | omega) (by first | decide | omega), Ar.x6]
  · rw [y28, gx .x7 (by first | decide | omega) (by first | decide | omega) (by first | decide | omega), Ar.x7]
  · rw [sp₂, sp₁, sp₀, Ar.sp]
  · exact Ar.perm.of_eq (by rw [rd₂, rd₁, rd₀]) (by rw [wr₂, wr₁, wr₀])
  · rw [hm, e₁, Ar.x4]
  · rw [hm, e₂, Ar.x5]
  · rw [hm, e₃, Ar.x3]
  · rw [hm, e₄, x11₀]
  · rw [hm]
    exact entryMem_saved s.mem c.W fun p hp => by
      have h9 : p.1 ≠ .x9 ∧ p.1 ≠ .x10 ∧ p.1 ≠ .x11 := by
        revert hp; revert p; decide
      exact g₀ p.1 h9.1 h9.2.1 h9.2.2
  · rw [hm]; exact entryMem_frame _ _ _
  · rw [y2, gx .x2 (by first | decide | omega) (by first | decide | omega) (by first | decide | omega), Ar.x2]
  · rw [y3, gx .x3 (by first | decide | omega) (by first | decide | omega) (by first | decide | omega), Ar.x3]
  · rw [rd₂, rd₁, rd₀]
  · rw [wr₂, wr₁, wr₀]

end VG.Proof.AesCcm.AArch64

end

end

/-! ### `AesCcm.AArch64.Absorb`, which this module and modules that import it used -/

section

/-! ### `AesCcm.AArch64.B0`, which this module and modules that import it used -/

section

/-!
# AES-CCM on AArch64: `B₀` (`b0 y`)

Untrusted: everything here is checked by Lean. `flagsSeg` computes the flags
`4 (t − 2) + q − 1 + 64 [a > 0]` (which is A.2.1's for an even `t`,
`flags_ok`); `b0Seg y` writes `B₀` to `W + 32` from `Ctr₀` and zeroes the MAC
state at `W + y` (`b0Seg_ok`); `b0 y` then chains `B₀` into it (`b0_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8)
open VG.Impl.AesGcm.AArch64 (mov ptr imm)
open VG.Proof.AesGcm.AArch64 (Others add_ofNat_assoc eval_zero ofNat_sub)
open VG.Proof.AesCcm (length_bytesAt bytesAt_writeW64_at bytesAt_writeW8_base bytesAt_writeW64_base
  ctrBlock_take8 ctrBlock_drop8 ctr_or flags_val)

/-- What the pieces of the MAC write: the MAC state at `W + y`, `B` and the
working space of the functions called. -/
abbrev macR (W : Addr) (N y : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 y, 16⟩, ⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 384, N⟩]

theorem macR_mut {c : Cx} {y : Nat} (hy : y = 0 ∨ y = 96) : ∀ r ∈ macR c.W c.N y, ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_lo (by omega_arith)
  · exact sub_lo (by first | decide | omega)
  · exact sub_hi (by first | decide | omega) (by first | decide | omega)

/-- The flags, from the tag length, the nonce length in its slot and the
length of the associated data in `x24`. -/
theorem flags_ok {c : Cx} (L : Lay c) {s : State} (E : Env c s) (S : Slots c s.mem)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 c.al) :
    WP isa flagsSeg s fun s' =>
      s'.gpr .x9 = BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl) + if c.al = 0 then 0 else 64) ∧
      Others [.x9, .x10, .x11] s s' ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain rn := E.perm.wR (show 232 + 8 ≤ 384 + c.N by omega)
  have ht4 := L.t4
  have ht16 := L.t16
  have h13 := L.h13
  obtain ⟨s₁, run₁, x9₁, hg₁, hm₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.subImm .x .x9 .x20 2, .lsl .x .x9 .x9 2, .ldr .x .x10 .x19 nlenO, imm .x11 14,
        .sub .x .x11 .x11 .x10, .add .x .x9 .x9 .x11] s = some s₁ ∧
      s₁.gpr .x9 = BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl)) ∧ Others [.x9, .x10, .x11] s s₁ ∧
      s₁.mem = s.mem ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by carun [E.x19, rn], ?_⟩
    refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
    · have hn : s.mem.read (c.W + 232#64) 8 = BitVec.ofNat 64 c.nl := S.nlen
      simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, E.x20, hn]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft,
        BitVec.toNat_ofNat, Nat.shiftLeft_eq, Size.bits]
      have := L.h7
      omega_arith
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain h24₁ : s₁.gpr .x24 = BitVec.ofNat 64 c.al := by rw [hg₁ _ (by first | decide | omega), h24]
  refine WP.ite (decide (c.al = 0)) (eval_zero h24₁ L.al_lt) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.al = 0 := of_decide_eq_true ht
    exact WP.block_nil ⟨by rw [x9₁, h0]; rfl, hg₁, hm₁, sp₁, rd₁, wr₁⟩
  · have h0 : c.al ≠ 0 := of_decide_eq_false hf
    refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun s₂ hs₂ => ?_
    subst hs₂
    refine ⟨?_, fun r hr => ?_, hm₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_write, BitVec.setWidth_eq, ite_true, x9₁, h0, ite_false]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, Size.bits]
      omega_arith
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.1, hg₁ r (by simp [hr.1, hr.2.1, hr.2.2])]

/-- `B₀` in `B`, and the MAC state at `W + y` zeroed. -/
theorem b0Seg_ok {c : Cx} (L : Lay c) {s : State} (E : Env c s) {nonce : List Byte} (hnl : nonce.length = c.nl)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl) + if c.al = 0 then 0 else 64))
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.block (b0Seg y)) s fun s' => Env c s' ∧ (∀ r ∈ pieceRegs, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩, ⟨c.W + BitVec.ofNat 64 y, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 y) 16 = Spec.Cmac.zeros 16 ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 c.tl nonce c.al c.n := by
  have h7 := L.h7
  have h13 := L.h13
  obtain c₁ := E.perm.wR (show 48 + 8 ≤ 384 + c.N by omega)
  obtain c₂ := E.perm.wR (show 56 + 8 ≤ 384 + c.N by omega)
  obtain b₁ := E.perm.wW (show 32 + 8 ≤ 384 + c.N by omega)
  obtain b₂ := E.perm.wW (show 32 + 1 ≤ 384 + c.N by omega)
  obtain b₃ := E.perm.wW (show 40 + 8 ≤ 384 + c.N by omega)
  obtain y₁ := E.perm.wW (show y + 8 ≤ 384 + c.N by omega_arith)
  obtain y₂ := E.perm.wW (show y + 8 + 8 ≤ 384 + c.N by omega_arith)
  obtain ⟨mB, hmB⟩ : ∃ mB, mB = ((s.mem.writeW (c.W + BitVec.ofNat 64 32) (s.mem.readW (c.W + BitVec.ofNat 64 48) 64)).writeW
      (c.W + BitVec.ofNat 64 32) ((s.gpr .x9).setWidth 8 : Byte)).writeW (c.W + BitVec.ofNat 64 40)
      (s.mem.readW (c.W + BitVec.ofNat 64 56) 64 ||| byteRev64 (BitVec.ofNat 64 c.n)) := ⟨_, rfl⟩
  obtain ⟨s₃, run₃, hm₃, hg₃, sp₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa (b0Seg y) s = some s₃ ∧
      s₃.mem = (mB.writeW (c.W + BitVec.ofNat 64 y) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 (y + 8))
        (0 : BitVec 64) ∧
      Others [.x9, .x10, .x11, .x12] s s₃ ∧ s₃.sp = s.sp ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr := by
    obtain ya : y % 8 = 0 ∧ y < 32768 := by omega_arith
    obtain yb : (y + 8) % 8 = 0 ∧ y + 8 < 32768 := by omega_arith
    refine ⟨_, by carun [b0Seg, E.x19, c₁, c₂, b₁, b₂, b₃, y₁, y₂, ya, yb], ?_⟩
    refine ⟨?_, ?_, rfl, rfl, rfl⟩
    · rw [hmB]
      simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, E.x28]
      rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.of_runBlock ⟨s₃, run₃, E.others hg₃ (by first | decide | omega) sp₃ rd₃ wr₃, fun r hr => hg₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl <;> decide),
    rd₃, wr₃, ?_⟩
  -- What the block wrote.
  obtain e40 : c.W + BitVec.ofNat 64 40 = c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  obtain ey8 : c.W + BitVec.ofNat 64 (y + 8) = c.W + BitVec.ofNat 64 y + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  obtain cB : ∀ d k, 32 ≤ d → d + k ≤ 48 →
      (⟨c.W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains c.W h₁ (by omega_arith) (by first | decide | omega)
  obtain cY : ∀ d k, y ≤ d → d + k ≤ y + 16 →
      (⟨c.W + BitVec.ofNat 64 y, 16⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains c.W h₁ (by omega_arith) (by omega_arith)
  obtain fB : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem mB := by
    rw [hmB]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cB 32 8 (by first | decide | omega) (by first | decide | omega))).writeW
      (List.mem_singleton_self _) _ (cB 32 1 (by first | decide | omega) (by first | decide | omega))).writeW
      (List.mem_singleton_self _) _ (cB 40 8 (by first | decide | omega) (by first | decide | omega))
  obtain fY : Frame [⟨c.W + BitVec.ofNat 64 y, 16⟩] mB s₃.mem := by
    rw [hm₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cY y 8 (by omega_arith) (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (cY (y + 8) 8 (by omega_arith) (by omega_arith))
  obtain dYB : (⟨c.W + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by first | decide | omega)) (by first | decide | omega) (by first | decide | omega)
    · exact L.w_w (.inl (by first | decide | omega)) (by first | decide | omega) (by first | decide | omega)
  refine ⟨(fB.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans
    (fY.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩), ?_, ?_⟩
  · -- The state was zeroed.
    rw [hm₃, ey8, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
  · -- `B₀`.
    obtain hB₁ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 32) 16 = bytesAt mB (c.W + BitVec.ofNat 64 32) 16 :=
      Proof.AesGcm.AArch64.bytesAt_frame fY (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dYB)
        (by first | decide | omega)
    obtain hlo : le8 (s.mem.readW (c.W + BitVec.ofNat 64 48) 64) =
        BitVec.ofNat 8 (15 - nonce.length - 1) :: nonce.take 7 := by
      obtain h8 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 8 =
          (bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16).take 8 := by
        rw [Proof.Cmac.bytesAt_split, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
      rw [Proof.Cmac.le8_readW, h8, hc0, ctrBlock_take8 (by omega_arith)]
    obtain hhi : le8 (s.mem.readW (c.W + BitVec.ofNat 64 56) 64) = (Spec.Ccm.ctrBlock nonce 0).drop 8 := by
      obtain e56 : c.W + BitVec.ofNat 64 56 = c.W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
      rw [Proof.Cmac.le8_readW, ← hc0, Proof.Cmac.bytesAt_split, e56,
        List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
    obtain hb : ((s.gpr .x9).setWidth 8 : Byte) = Spec.Ccm.flags c.tl (15 - nonce.length) c.al := by
      rw [h9, hnl, flags_val L.t4 L.t16 L.te h7 h13]
    obtain hB : bytesAt mB (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 c.tl nonce c.al c.n := by
      rw [hmB, e40, bytesAt_writeW64_at _ _ _ (by first | decide | omega) (by first | decide | omega), bytesAt_writeW8_base _ _ _ (by first | decide | omega)
        (by first | decide | omega), bytesAt_writeW64_base _ _ _ (by first | decide | omega) (by first | decide | omega), hlo, hb,
        ctr_or (by omega_arith) (by omega_arith) hhi (by rw [hnl]; exact L.hn), ctrBlock_drop8 (by omega_arith)]
      simp only [Spec.Ccm.b0, List.drop_one, List.cons_append, List.tail_cons, List.take_succ_cons]
      obtain hX : (Spec.Ccm.flags c.tl (15 - nonce.length) c.al ::
          (List.take 7 nonce ++ List.drop 8 (bytesAt s.mem (c.W + BitVec.ofNat 64 32) 16))).length ≤ 8 + 8 := by
        simp [length_bytesAt]; omega_arith
      rw [List.take_append_of_le_length (by simp; omega_arith), List.take_of_length_le (by simp; omega_arith),
        List.drop_eq_nil_of_le hX, List.append_nil, ← List.append_assoc, List.take_append_drop]
    rw [hB₁, hB]

/-- What a piece of the MAC leaves: the environment, what it writes, the MAC
state `Y` at `W + y`, and the permissions. -/
structure MacStep (c : Cx) (y : Nat) (s : State) (Y : List Byte) (s' : State) : Prop where
  env : Env c s'
  frame : Frame (macR c.W c.N y) s.mem s'.mem
  out : bytesAt s'.mem (c.W + BitVec.ofNat 64 y) 16 = Y
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem k_macR {c : Cx} (L : Lay c) {y : Nat} (hy : y + 16 ≤ 384 + c.N) :
    ∀ r ∈ macR c.W c.N y, (⟨c.K, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.k_w' hy
  · exact L.k_w' (by first | decide | omega)
  · exact L.k_w' (by first | decide | omega)

theorem ciph_macR {c : Cx} (L : Lay c) {y : Nat} (hy : y + 16 ≤ 384 + c.N) {m m' : Mem} (hf : Frame (macR c.W c.N y) m m') :
    Spec.Ccm.ctxCiph m' c.K c.R = Spec.Ccm.ctxCiph m c.K c.R := by
  unfold Spec.Ccm.ctxCiph
  rw [Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => (k_macR L hy r hr).sub_left (Region.sub_prefix L.rb))
    (by have := L.rb; omega_arith)]

/-- A buffer missing `W` keeps its bytes. -/
theorem buf_macR {c : Cx} {s : State} {P : Addr} {len : Nat} (hP : Buf c s P len) {y : Nat}
    (hy : y + 16 ≤ 384 + c.N) {m m' : Mem} (hf : Frame (macR c.W c.N y) m m') : bytesAt m' P len = bytesAt m P len :=
  Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hP.wd hy
    · exact hP.wd (by first | decide | omega)
    · exact hP.wd (by first | decide | omega)) (by have := hP.lt; omega_arith)

/-- `B₀` chained into a zeroed MAC state at `W + y`. -/
theorem b0_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : Cx} (L : Lay c) (hv : v.scratch ≤ c.N) {s : State} (E : Env c s)
    (S : Slots c s.mem) (h24 : s.gpr .x24 = BitVec.ofNat 64 c.al) {nonce : List Byte}
    (hnl : nonce.length = c.nl) (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (b0 v.callee y) s fun s' => MacStep c y s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (Spec.Cmac.zeros 16) [Spec.Ccm.b0 c.tl nonce c.al c.n]) s' ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 := by
  refine WP.seq (WP.mono (flags_ok L E S h24) fun s₁ ⟨x9₁, hg₁, hm₁, sp₁, rd₁, wr₁⟩ => ?_)
  obtain E₁ : Env c s₁ := E.others hg₁ (by first | decide | omega) sp₁ rd₁ wr₁
  refine WP.seq (WP.mono (b0Seg_ok L E₁ hnl (by rw [hm₁]; exact hc0) x9₁ hy)
    fun s₃ ⟨E₃, g₃, rd₃, wr₃, f₃, hz, hB⟩ => ?_)
  refine WP.mono (updBlock_ok v L hv E₃ hy) fun s₄ ⟨E₄, g₄, rd₄, wr₄, f₄, h₄⟩ =>
    ⟨⟨E₄, ?_, ?_, by rw [rd₄, rd₃, rd₁], by rw [wr₄, wr₃, wr₁]⟩, ?_, ?_⟩
  · rw [← hm₁]
    refine (f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · rw [h₄, hz, hB, ← hm₁, ciph_macR L (y := y) (by omega_arith) (f₃.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩)]
  · rw [g₄ _ (by simp), g₃ _ (by simp), hg₁ _ (by first | decide | omega)]
  · rw [g₄ _ (by simp), g₃ _ (by simp), hg₁ _ (by first | decide | omega)]

end VG.Proof.AesCcm.AArch64

end

end

/-!
# AES-CCM on AArch64: a buffer padded, chained (`absorbPad y`)

Untrusted: everything here is checked by Lean. `absorbPad y` chains the
`len` bytes at `P`, padded with zeros to whole blocks, into the MAC state
at `W + y`: its whole blocks in one call of `vg_cmac_aes_update`, on none if
there are none (`absWhole_ok`), then its last `len mod 16` bytes copied into
the zeroed block `B` (`absTail_ok`); together, the blocks of the padded
string (`absorbPad_ok`, `Proof.AesCcm.blocks_pad16`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm copyLoop)
open VG.Proof.AesGcm.AArch64 (LoopPre copyLoop_ok loopRegs Others add_ofNat_assoc eval_zero ofNat_sub lsr_ofNat
  lsl4_ofNat and15 toNat_ofNat_of_lt)
open VG.Proof.CmacAes.Stream.AArch64 (upd_call upd_callLe)
open VG.Proof.AesCcm (length_bytesAt bytesAt_writeBytes_base bytesAt_prefix bytesAt_suffix)

/-- The arguments of the call for the whole blocks. -/
theorem absArgs_ok {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr}
    {len : Nat} (hP : Buf c s P len) (h23 : s.gpr .x23 = P) (h24 : s.gpr .x24 = BitVec.ofNat 64 len) :
    WP isa (.block (updArgs y ++ ([mov .x3 .x23, .lsr .x .x4 .x24 4] : List Instr))) s fun s₁ =>
      Proof.CmacAes.Stream.AArch64.UArgsW c.N s₁ c.K (c.W + BitVec.ofNat 64 y) P (c.W + BitVec.ofNat 64 384) c.R
        (len / 16) ∧ Env c s₁ ∧ Others [.x0, .x1, .x2, .x3, .x4, .x5] s s₁ ∧ s₁.mem = s.mem ∧
        s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have hl := hP.lt
  obtain ⟨s₁, run₁, hm₁, x0, x1, x2, x3, x4, x5, hg₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      (updArgs y ++ [mov .x3 .x23, .lsr .x .x4 .x24 4]) s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .x0 = c.K ∧ s₁.gpr .x1 = BitVec.ofNat 64 c.R ∧ s₁.gpr .x2 = c.W + BitVec.ofNat 64 y ∧
      s₁.gpr .x3 = P ∧ s₁.gpr .x4 = BitVec.ofNat 64 (len / 16) ∧ s₁.gpr .x5 = c.W + BitVec.ofNat 64 384 ∧
      Others [.x0, .x1, .x2, .x3, .x4, .x5] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    have hy' : y < 4096 := by omega_arith
    refine ⟨_, by carun [updArgs, hy'], ?_⟩
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp [gpr_write, E.x21]
    · simp [gpr_write, E.x22]
    · simp [gpr_write, E.x19]
    · simp [gpr_write, h23]
    · simp [gpr_write, h24, lsr_ofNat len 4 hl]
    · simp [gpr_write, E.x19]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  have E₁ : Env c s₁ := E.others hg₁ (by first | decide | omega) sp₁ rd₁ wr₁
  have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  have hq := ((hP.take hb).of_eq (s' := s₁) rd₁ wr₁).src
  have hqy : (⟨P, 16 * (len / 16)⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 y, 16⟩ :=
    (hP.take hb).wd (by omega_arith)
  exact WP.of_runBlock ⟨s₁, run₁, uargs L E₁ (by omega_arith) hq hqy (by omega_arith) x0 x1 x2 x3 x4 x5, E₁, hg₁, hm₁,
    rd₁, wr₁⟩

/-- What `absorbPad`'s pieces leave. -/
structure Absorbed (c : Cx) (y : Nat) (P : Addr) (len : Nat) (s : State) (Y : List Byte) (s' : State) :
    Prop where
  env : Env c s'
  x23 : s'.gpr .x23 = P
  x24 : s'.gpr .x24 = BitVec.ofNat 64 len
  frame : Frame (macR c.W c.N y) s.mem s'.mem
  out : bytesAt s'.mem (c.W + BitVec.ofNat 64 y) 16 = Y
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The whole blocks of the string. -/
theorem absWhole_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : Cx} (L : Lay c) (hv : v.scratch ≤ c.N) {s : State} (E : Env c s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : Buf c s P len) (h23 : s.gpr .x23 = P)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 len) :
    WP isa (.seq (.block (updArgs y ++ ([mov .x3 .x23, .lsr .x .x4 .x24 4] : List Instr))) (callUpdate v.callee)) s
      (Absorbed c y P len s
        (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
          (Spec.Cmac.blocks 16 ((bytesAt s.mem P len).take (16 * (len / 16)))))) := by
  refine WP.seq (WP.mono (absArgs_ok L E hy hP h23 h24) fun s₁ ⟨U, E₁, hg₁, hm₁, rd₁, wr₁⟩ => ?_)
  have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  refine WP.mono (upd_callLe v v.callee.name hv U) fun s₂ h =>
    ⟨E₁.of_saved h.saved h.sp h.rd h.wr, ?_, ?_, ?_, ?_, by rw [h.rd, rd₁], by rw [h.wr, wr₁]⟩
  · rw [h.saved _ (by first | decide | omega) (by first | decide | omega), hg₁ _ (by first | decide | omega), h23]
  · rw [h.saved _ (by first | decide | omega) (by first | decide | omega), hg₁ _ (by first | decide | omega), h24]
  · rw [← hm₁]
    exact h.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · rw [h.out, Proof.Cmac.Stream.blocksAt_eq, hm₁, ← bytesAt_prefix _ _ hb]
    rfl

/-- The last bytes of a string, padded to a block, if any are left after
its whole blocks. -/
def tailBlocks (x : List Byte) : List (List Byte) :=
  if x.length % 16 = 0 then [] else [x.drop (16 * (x.length / 16)) ++ Spec.Ccm.zeros (16 - x.length % 16)]

/-- The last `len mod 16` (not 0) bytes, padded with zeros in `B`. -/
theorem absTailPre_ok {c : Cx} {s : State} (E : Env c s)
    {P : Addr} {len : Nat} (hP : Buf c s P len) (h23 : s.gpr .x23 = P)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 len) (h13 : s.gpr .x13 = BitVec.ofNat 64 (len % 16))
    (h0 : len % 16 ≠ 0) :
    WP isa (.seq (.block (zero16 bO ++ ([.lsr .x .x10 .x24 4, .lsl .x .x10 .x10 4, .add .x .x12 .x23 .x10,
        ptr .x11 .x19 bO] : List Instr))) copyLoop) s fun s₃ =>
      Env c s₃ ∧ s₃.gpr .x23 = P ∧ s₃.gpr .x24 = BitVec.ofNat 64 len ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧
      Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₃.mem ∧
      bytesAt s₃.mem (c.W + BitVec.ofNat 64 32) 16 =
        (bytesAt s.mem P len).drop (16 * (len / 16)) ++ Spec.Ccm.zeros (16 - len % 16) := by
  have hl := hP.lt
  have hxl := length_bytesAt s.mem P len
  have w₁ := E.perm.wW (show 32 + 8 ≤ 384 + c.N by omega)
  have w₂ := E.perm.wW (show 40 + 8 ≤ 384 + c.N by omega)
  obtain ⟨s₂, run₂, hm₂, x11₂, x12₂, x13₂, hg₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      (zero16 bO ++ [.lsr .x .x10 .x24 4, .lsl .x .x10 .x10 4, .add .x .x12 .x23 .x10, ptr .x11 .x19 bO]) s =
        some s₂ ∧
      s₂.mem = (s.mem.writeW (c.W + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 40)
        (0 : BitVec 64) ∧
      s₂.gpr .x11 = c.W + BitVec.ofNat 64 32 ∧ s₂.gpr .x12 = P + BitVec.ofNat 64 (16 * (len / 16)) ∧
      s₂.gpr .x13 = BitVec.ofNat 64 (len % 16) ∧
      Others [.x9, .x10, .x11, .x12] s s₂ ∧ s₂.sp = s.sp ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by carun [E.x19, w₁, w₂], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp only [mem_write]; rfl
    · simp [gpr_write, E.x19]
    · simp [gpr_write, h23, h24, lsr_ofNat len 4 hl, lsl4_ofNat]
    · simp [gpr_write, h13]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have E₂ : Env c s₂ := E.others hg₂ (by first | decide | omega) sp₂ rd₂ wr₂
  have hb : 16 * (len / 16) + len % 16 = len := by omega_arith
  have hT := (hP.slice (a := 16 * (len / 16)) (k := len % 16) (by omega_arith)).of_eq (s' := s₂) rd₂ wr₂
  have dTB : (⟨P + BitVec.ofNat 64 (16 * (len / 16)), len % 16⟩ : Region).Disjoint
      ⟨c.W + BitVec.ofNat 64 32, len % 16⟩ := hT.wd (by omega_arith)
  have lp : LoopPre s₂ (P + BitVec.ofNat 64 (16 * (len / 16))) (c.W + BitVec.ofNat 64 32) (len % 16) :=
    ⟨by omega_arith, hT.rd, E₂.perm.wC (by omega_arith), dTB⟩
  refine WP.mono (copyLoop_ok s₂ x12₂ x11₂ x13₂ (by omega_arith) lp) fun s₃ ⟨hm₃, _, _, hg₃, sp₃, rd₃, wr₃⟩ => ?_
  have E₃ : Env c s₃ := E₂.others hg₃ (by first | decide | omega) sp₃ rd₃ wr₃
  -- What was written.
  have e40 : c.W + BitVec.ofNat 64 40 = c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  have fZ : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₂.mem := by
    rw [hm₂]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains c.W (d := 32) (n := 8) (e := 32) (k := 16) (by first | decide | omega) (by first | decide | omega) (by first | decide | omega))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains c.W (d := 40) (n := 8) (e := 32) (k := 16) (by first | decide | omega) (by first | decide | omega) (by first | decide | omega))
  have fC : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s₂.mem s₃.mem := by
    rw [hm₃]
    exact writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains c.W (d := 32) (n := len % 16) (e := 32) (k := 16) (by first | decide | omega) (by omega_arith) (by first | decide | omega))
  have fB : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₃.mem := fZ.trans fC
  have hB₃ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 32) 16 =
      (bytesAt s.mem P len).drop (16 * (len / 16)) ++ Spec.Ccm.zeros (16 - len % 16) := by
    have hs₁ : bytesAt s₂.mem (P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) =
        (bytesAt s.mem P len).drop (16 * (len / 16)) := by
      rw [Proof.AesGcm.AArch64.bytesAt_frame fZ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hT.wd (by first | decide | omega)) (by omega_arith),
        show len % 16 = len - 16 * (len / 16) by omega_arith, bytesAt_suffix _ _ (by omega_arith)]
    have hz : bytesAt s₂.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Cmac.zeros 16 := by
      rw [hm₂, e40, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
    rw [hm₃, bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]; omega_arith) (by first | decide | omega), hs₁, hz,
      List.length_drop, hxl]
    congr 1
    simp only [Spec.Cmac.zeros, Spec.Ccm.zeros, List.drop_replicate]
    congr 1
    omega_arith
  refine ⟨E₃, by rw [hg₃ _ (by first | decide | omega), hg₂ _ (by first | decide | omega), h23], by rw [hg₃ _ (by first | decide | omega), hg₂ _ (by first | decide | omega), h24],
    by rw [rd₃, rd₂], by rw [wr₃, wr₂], fB, hB₃⟩

/-- The last `len mod 16` (not 0) bytes, padded with zeros in `B`, chained. -/
theorem absTail_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : Cx} (L : Lay c) (hv : v.scratch ≤ c.N) {s : State} (E : Env c s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : Buf c s P len) (h23 : s.gpr .x23 = P)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 len) (h13 : s.gpr .x13 = BitVec.ofNat 64 (len % 16))
    (h0 : len % 16 ≠ 0) :
    WP isa (absTail v.callee y) s (Absorbed c y P len s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        (tailBlocks (bytesAt s.mem P len)))) := by
  have hxl := length_bytesAt s.mem P len
  refine WP.assoc (WP.seq (WP.mono (absTailPre_ok E hP h23 h24 h13 h0)
    fun s₃ ⟨E₃, x23₃, x24₃, rd₃, wr₃, fB, hB₃⟩ => ?_))
  have hY₃ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16 :=
    Proof.AesGcm.AArch64.bytesAt_frame fB (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases hy with rfl | rfl
      · exact L.w_w (.inl (by first | decide | omega)) (by first | decide | omega) (by first | decide | omega)
      · exact L.w_w (.inr (by first | decide | omega)) (by first | decide | omega) (by first | decide | omega)) (by first | decide | omega)
  refine WP.mono (updBlock_ok v L hv E₃ hy) fun s₄ ⟨E₄, g₄, hr₄, hw₄, f₄, h₄⟩ =>
    ⟨E₄, ?_, ?_, ?_, ?_, by rw [hr₄, rd₃], by rw [hw₄, wr₃]⟩
  · rw [g₄ _ (by simp), x23₃]
  · rw [g₄ _ (by simp), x24₃]
  · refine ((fB.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · rw [h₄, hY₃, hB₃, ciph_macR L (y := y) (by omega_arith) (fB.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)]
    simp only [tailBlocks, hxl, h0, ↓reduceIte]

/-- The length of the last bytes, `len mod 16`. -/
theorem absMask_ok {s : State} {len : Nat} (hl : len < 2 ^ 64)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 len) :
    WP isa (.block [imm .x9 15, .logic .and .x .x13 .x24 .x9]) s fun s₂ =>
      s₂.gpr .x13 = BitVec.ofNat 64 (len % 16) ∧ Others [.x9, .x13] s s₂ ∧ s₂.mem = s.mem ∧
      s₂.sp = s.sp ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
  obtain ⟨s₂, run₂, x13₂, hg₂, hm₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa [imm .x9 15, .logic .and .x .x13 .x24 .x9]
      s = some s₂ ∧ s₂.gpr .x13 = BitVec.ofNat 64 (len % 16) ∧ Others [.x9, .x13] s s₂ ∧ s₂.mem = s.mem ∧
      s₂.sp = s.sp ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by carun [], ?_⟩
    refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, h24]
      rw [and15, toNat_ofNat_of_lt hl]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  exact WP.of_runBlock ⟨s₂, run₂, x13₂, hg₂, hm₂, sp₂, rd₂, wr₂⟩

/-- The `len` bytes at `P`, padded with zeros to whole blocks, chained into
the MAC state at `W + y`. -/
theorem absorbPad_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : Cx} (L : Lay c) (hv : v.scratch ≤ c.N) {s : State} (E : Env c s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : Buf c s P len) (h23 : s.gpr .x23 = P)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 len) :
    WP isa (absorbPad v.callee y) s (Absorbed c y P len s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        (Spec.Cmac.blocks 16 (Spec.Ccm.pad16 (bytesAt s.mem P len))))) := by
  have hl := hP.lt
  refine WP.assoc (WP.seq (WP.mono (absWhole_ok v L hv E hy hP h23 h24) fun s₁ A₁ => ?_))
  refine WP.seq (WP.mono (absMask_ok hl A₁.x24) fun s₂ ⟨x13₂, hg₂, hm₂, sp₂, rd₂, wr₂⟩ => ?_)
  have E₂ : Env c s₂ := A₁.env.others hg₂ (by first | decide | omega) sp₂ rd₂ wr₂
  have hb := Proof.AesCcm.blocks_pad16 (bytesAt s.mem P len)
  rw [length_bytesAt] at hb
  have hRb := L.rb
  refine WP.ite (decide (len % 16 = 0)) (eval_zero x13₂ (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : len % 16 = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨E₂, by rw [hg₂ _ (by first | decide | omega), A₁.x23], by rw [hg₂ _ (by first | decide | omega), A₁.x24],
      by rw [hm₂]; exact A₁.frame, ?_, by rw [rd₂, A₁.rd], by rw [wr₂, A₁.wr]⟩
    rw [hm₂, A₁.out, hb]
    simp only [h0, ↓reduceIte, List.append_nil]
  · have h0 : len % 16 ≠ 0 := of_decide_eq_false hf
    refine WP.mono (absTail_ok v L hv E₂ hy (hP.of_eq (by rw [rd₂, A₁.rd]) (by rw [wr₂, A₁.wr]))
      (by rw [hg₂ _ (by first | decide | omega), A₁.x23]) (by rw [hg₂ _ (by first | decide | omega), A₁.x24]) x13₂ h0) fun s₃ A₃ =>
      ⟨A₃.env, A₃.x23, A₃.x24, A₁.frame.trans (by rw [← hm₂]; exact A₃.frame), ?_,
        by rw [A₃.rd, rd₂, A₁.rd], by rw [A₃.wr, wr₂, A₁.wr]⟩
    rw [A₃.out, hm₂, A₁.out, buf_macR hP (by omega_arith) A₁.frame, ciph_macR L (by omega_arith) A₁.frame,
      ← Proof.Cmac.chain_append, hb, tailBlocks, length_bytesAt]

end VG.Proof.AesCcm.AArch64

end

end

/-!
# AES-CCM on AArch64: the first block of the associated data

Untrusted: everything here is checked by Lean. `header` zeroes `B` and
writes the encoding of the length `a > 0` (A.2.2) at its start: `[a]₁₆`,
`0xff ‖ 0xfe ‖ [a]₃₂` or `0xff ‖ 0xff ‖ [a]₆₄`, by byte-reversing and
shifting `a` (`header_ok`); its length is in `x25`. `aadHead y` copies the
first `min (a, 16 − h)` bytes after it and chains the block (`aadHead_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8)
open VG.Impl.AesGcm.AArch64 (mov ptr imm copyLoop minK)
open VG.Proof.AesGcm.AArch64 (LoopPre copyLoop_ok minK_ok loopRegs minRegs Others add_ofNat_assoc eval_zero
  ofNat_sub lsr_ofNat toNat_ofNat_of_lt ofNat_add_ofNat)
open VG.Proof.AesCcm (hdrLen headLen length_bytesAt bytesAt_writeW64_at bytesAt_writeW64_base
  bytesAt_writeBytes_at bytesAt_prefix enc_lo enc_mid enc_hi)

/-- The sign of a difference of two numbers below `2⁶³`: whether the first
is the smaller. -/
theorem sign63 {x k : Nat} (hx : x < 2 ^ 63) (hk : k < 2 ^ 63) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 k) >>> 63 = BitVec.ofNat 64 (if x < k then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, toNat_ofNat_of_lt (by omega_using [hk]), toNat_ofNat_of_lt (by omega_using [hx]),
    Nat.shiftRight_eq_div_pow]
  split
  · rw [toNat_ofNat_of_lt (by first | decide | omega)]; omega_arith
  · rw [toNat_ofNat_of_lt (by first | decide | omega)]; omega_arith

/-- `B` zeroed, then the encoding of the length `a` of the associated data
(`x24`) at its start, and its length in `x25`. -/
theorem header_ok {c : Cx} {s : State} (E : Env c s) {a : Nat} (ha0 : 0 < a) (ha : a < 2 ^ 64)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 a) :
    WP isa header s fun s' => Env c s' ∧ s'.gpr .x25 = BitVec.ofNat 64 (hdrLen a) ∧
      Others [.x9, .x10, .x25] s s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a) := by
  obtain w₁ := E.perm.wW (show 32 + 8 ≤ 384 + c.N by omega)
  obtain w₂ := E.perm.wW (show 40 + 8 ≤ 384 + c.N by omega)
  obtain w₃ := E.perm.wW (show 34 + 8 ≤ 384 + c.N by omega)
  obtain e40 : c.W + BitVec.ofNat 64 40 = c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  obtain e34 : c.W + BitVec.ofNat 64 34 = c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 2 := by rw [add_ofNat_assoc]
  obtain cB : ∀ d k, 32 ≤ d → d + k ≤ 48 →
      (⟨c.W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains c.W h₁ (by omega_using [h₂]) (by first | decide | omega)
  -- `B` zeroed; `a >> 32`.
  obtain ⟨s₁, run₁, hm₁, x9₁, hg₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa (zero16 bO ++ [.lsr .x .x9 .x24 32]) s =
      some s₁ ∧
      s₁.mem = (s.mem.writeW (c.W + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 40)
        (0 : BitVec 64) ∧ s₁.gpr .x9 = BitVec.ofNat 64 (a / 2 ^ 32) ∧
      Others [.x9] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by carun [E.x19, w₁, w₂], ?_⟩
    refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp only [mem_write]; rfl
    · simp [gpr_write, h24, lsr_ofNat a 32 ha]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  obtain hz : bytesAt s₁.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.zeros 16 := by
    rw [hm₁, e40, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
  obtain fz : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₁.mem := by
    rw [hm₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (0 : BitVec 64) (cB 32 8 (by first | decide | omega) (by first | decide | omega))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64) (cB 40 8 (by first | decide | omega) (by first | decide | omega))
  obtain E₁ : Env c s₁ := E.others hg₁ (by first | decide | omega) sp₁ rd₁ wr₁
  obtain h24₁ : s₁.gpr .x24 = BitVec.ofNat 64 a := by rw [hg₁ _ (by first | decide | omega), h24]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (a / 2 ^ 32 = 0)) (eval_zero x9₁ (by omega_using [ha])) (fun ht => ?_) (fun hf => ?_)
  · have h₂ : a < 2 ^ 32 := by have := of_decide_eq_true ht; omega_using [this]
    obtain ⟨s₂, run₂, x9₂, hg₂, hm₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
        [.lsr .x .x9 .x24 8, .subImm .x .x9 .x9 255, .lsr .x .x9 .x9 63] s₁ = some s₂ ∧
        s₂.gpr .x9 = BitVec.ofNat 64 (if a / 256 < 255 then 1 else 0) ∧ Others [.x9] s₁ s₂ ∧
        s₂.mem = s₁.mem ∧ s₂.sp = s₁.sp ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
      refine ⟨_, by carun [], ?_⟩
      refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
      · simp only [gpr_write, BitVec.setWidth_eq, ite_true, h24₁, lsr_ofNat a 8 ha]
        exact sign63 (by omega_using [ha]) (by first | decide | omega)
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [gpr_write, hr]
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    obtain E₂ : Env c s₂ := E₁.others hg₂ (by first | decide | omega) sp₂ rd₂ wr₂
    obtain h24₂ : s₂.gpr .x24 = BitVec.ofNat 64 a := by rw [hg₂ _ (by first | decide | omega), h24₁]
    obtain w₁' := E₂.perm.wW (show 32 + 8 ≤ 384 + c.N by omega)
    refine WP.ite (decide ((if a / 256 < 255 then 1 else 0) = 0)) (eval_zero x9₂ (by split <;> decide))
      (fun ht => ?_) (fun hf => ?_)
    · -- `0xff ‖ 0xfe ‖ [a]₃₂`.
      obtain h₁ : ¬ a < 2 ^ 16 - 2 ^ 8 := by
        have := of_decide_eq_true ht; split at this <;> simp_all <;> omega_arith
      obtain kf : (BitVec.setWidth 64 (0xfeff : BitVec 16) <<< 0 : BitVec 64) = BitVec.ofNat 64 0xfeff := by decide
      obtain ⟨s₃, run₃, hm₃, x25₃, hg₃, sp₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa
          [.rev .x9 .x24, .lsr .x .x9 .x9 16, .movz .x .x10 0xfeff 0, .logic .orr .x .x9 .x9 .x10,
            .str .x .x9 .x19 bO, imm .x25 6] s₂ = some s₃ ∧
          s₃.mem = s₂.mem.writeW (c.W + BitVec.ofNat 64 32)
            (byteRev64 (BitVec.ofNat 64 a) >>> 16 ||| BitVec.ofNat 64 0xfeff) ∧
          s₃.gpr .x25 = BitVec.ofNat 64 6 ∧ Others [.x9, .x10, .x25] s₂ s₃ ∧
          s₃.sp = s₂.sp ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
        refine ⟨_, by carun [E₂.x19, w₁', kf], ?_⟩
        refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
        · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, h24₂]; rfl
        · simp [gpr_write]
        · intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp [gpr_write, hr]
      refine WP.of_runBlock ⟨s₃, run₃, E₂.others hg₃ (by first | decide | omega) sp₃ rd₃ wr₃,
        by rw [x25₃, Proof.AesCcm.hdrLen_mid h₁ h₂], fun r hr => ?_, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁],
        ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [hg₃ r (by simp [hr.1, hr.2.1, hr.2.2]), hg₂ r (by simp [hr.1]), hg₁ r (by simp [hr.1])]
      · rw [hm₃, hm₂]
        exact fz.writeW (List.mem_singleton_self _) _ (cB 32 8 (by first | decide | omega) (by first | decide | omega))
      · rw [hm₃, bytesAt_writeW64_base _ _ _ (by first | decide | omega) (by first | decide | omega), hm₂, hz]
        exact enc_mid h₁ h₂ _ rfl
    · -- `[a]₁₆`.
      obtain h₁ : a < 2 ^ 16 - 2 ^ 8 := by
        have := of_decide_eq_false hf; split at this <;> simp_all <;> omega_arith
      obtain ⟨s₃, run₃, hm₃, x25₃, hg₃, sp₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa
          [.rev .x9 .x24, .lsr .x .x9 .x9 48, .str .x .x9 .x19 bO, imm .x25 2] s₂ = some s₃ ∧
          s₃.mem = s₂.mem.writeW (c.W + BitVec.ofNat 64 32) (byteRev64 (BitVec.ofNat 64 a) >>> 48) ∧
          s₃.gpr .x25 = BitVec.ofNat 64 2 ∧ Others [.x9, .x10, .x25] s₂ s₃ ∧
          s₃.sp = s₂.sp ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
        refine ⟨_, by carun [E₂.x19, w₁'], ?_⟩
        refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
        · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, h24₂]; rfl
        · simp [gpr_write]
        · intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp [gpr_write, hr]
      refine WP.of_runBlock ⟨s₃, run₃, E₂.others hg₃ (by first | decide | omega) sp₃ rd₃ wr₃,
        by rw [x25₃, Proof.AesCcm.hdrLen_lo h₁], fun r hr => ?_, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁],
        ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [hg₃ r (by simp [hr.1, hr.2.1, hr.2.2]), hg₂ r (by simp [hr.1]), hg₁ r (by simp [hr.1])]
      · rw [hm₃, hm₂]
        exact fz.writeW (List.mem_singleton_self _) _ (cB 32 8 (by first | decide | omega) (by first | decide | omega))
      · rw [hm₃, bytesAt_writeW64_base _ _ _ (by first | decide | omega) (by first | decide | omega), hm₂, hz]
        exact enc_lo h₁ _ rfl
  · -- `0xff ‖ 0xff ‖ [a]₆₄`.
    obtain h₂ : ¬ a < 2 ^ 32 := by have := of_decide_eq_false hf; omega_using [this]
    obtain h₁ : ¬ a < 2 ^ 16 - 2 ^ 8 := by omega_using [h₂]
    obtain w₁' := E₁.perm.wW (show 32 + 8 ≤ 384 + c.N by omega)
    obtain w₃' := E₁.perm.wW (show 34 + 8 ≤ 384 + c.N by omega)
    obtain kf : (BitVec.setWidth 64 (0xffff : BitVec 16) <<< 0 : BitVec 64) = BitVec.ofNat 64 0xffff := by decide
    obtain ⟨s₃, run₃, hm₃, x25₃, hg₃, sp₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa
        [.movz .x .x9 0xffff 0, .str .x .x9 .x19 bO, .rev .x9 .x24, ptr .x10 .x19 (bO + 2),
          .str .x .x9 .x10 0, imm .x25 10] s₁ = some s₃ ∧
        s₃.mem = (s₁.mem.writeW (c.W + BitVec.ofNat 64 32) (BitVec.ofNat 64 0xffff)).writeW
          (c.W + BitVec.ofNat 64 34) (byteRev64 (BitVec.ofNat 64 a)) ∧
        s₃.gpr .x25 = BitVec.ofNat 64 10 ∧ Others [.x9, .x10, .x25] s₁ s₃ ∧
        s₃.sp = s₁.sp ∧ s₃.rd = s₁.rd ∧ s₃.wr = s₁.wr := by
      refine ⟨_, by carun [E₁.x19, w₁', w₃', kf], ?_⟩
      refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
      · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, h24₁]; rfl
      · simp [gpr_write]
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [gpr_write, hr]
    refine WP.of_runBlock ⟨s₃, run₃, E₁.others hg₃ (by first | decide | omega) sp₃ rd₃ wr₃,
      by rw [x25₃, Proof.AesCcm.hdrLen_hi h₁ h₂], fun r hr => ?_, by rw [rd₃, rd₁], by rw [wr₃, wr₁], ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [hg₃ r (by simp [hr.1, hr.2.1, hr.2.2]), hg₁ r (by simp [hr.1])]
    · rw [hm₃]
      exact (fz.writeW (List.mem_singleton_self _) _ (cB 32 8 (by first | decide | omega) (by first | decide | omega))).writeW
        (List.mem_singleton_self _) _ (cB 34 8 (by first | decide | omega) (by first | decide | omega))
    · rw [hm₃, e34, bytesAt_writeW64_at _ _ _ (by first | decide | omega) (by first | decide | omega),
        bytesAt_writeW64_base _ _ _ (by first | decide | omega) (by first | decide | omega), hz]
      exact enc_hi h₁ h₂ ha

end VG.Proof.AesCcm.AArch64
