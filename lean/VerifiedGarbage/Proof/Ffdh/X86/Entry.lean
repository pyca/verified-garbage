module

public import VerifiedGarbage.Impl.Ffdh.X86.Domain
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.MulArgs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Bignum.X86.PublicRt
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Proof.Ffdh.X86.Ops
public import VerifiedGarbage.Proof.Ffdh.X86.ABI
import VerifiedGarbage.Proof.Bignum.X86.CrtSave
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Dsa.X86.StackArgument
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Impl.Bignum.X86.CrtFn
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue
public import VerifiedGarbage.Proof.Framework.X86.Spill

/-! ### `Ffdh.X86.Frame`, which only this module used -/

section

/-!
# FFDH on i686: the frame of the synthetic arguments

`fill a` stores into the 76 bytes at `esp` the eighteen arguments of private
CRT's operations, `synth a g` for the function's arguments `g` (`fill_ok`):
argument `i` in the word at `esp + 4 + 4 i`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont.X86
open VG.Impl.Ffdh.X86 (Args slotOp argVal zeroVal optVal compVal val piece fill)
open VG.Impl.Bignum.X86.PublicRt (argAt)
open VG.Proof.Bignum.X86.PublicRt (frame_other)

/-- The value of an optional argument, or zero. -/
def optArg (g : Nat → BitVec 32) : Option Nat → BitVec 32
  | some j => g j
  | none => 0

/-- Synthetic argument `i`, from the function's arguments `g`. -/
def synth (a : Args) (g : Nat → BitVec 32) : Nat → BitVec 32
  | 0 => optArg g a.out
  | 1 => g a.plen
  | 2 => g a.dom
  | 3 => g a.plen
  | 4 => g a.dom + g a.plen
  | 5 => g a.plen
  | 6 => g a.dom + g a.plen + g a.plen
  | 7 => g a.plen
  | 8 => optArg g a.y
  | 9 => optArg g (a.y.map fun _ => a.plen)
  | 10 => optArg g a.x
  | 11 => optArg g (a.x.map (· + 1))
  | 12 => g a.dlen
  | 13 => optArg g a.ctx
  | 16 => g a.ws
  | 17 => g (a.ws + 1)
  | _ => 0

/-- Every argument position of `a` is below `n`. -/
structure Below (a : Args) (n : Nat) : Prop where
  out : ∀ j, a.out = some j → j < n
  dom : a.dom < n
  dlen : a.dlen < n
  plen : a.plen < n
  y : ∀ j, a.y = some j → j < n
  x : ∀ j, a.x = some j → j + 1 < n
  ws : a.ws + 1 < n
  ctx : ∀ j, a.ctx = some j → j < n

section
variable {is : List Instr} {Q : State → Prop}

/-- An operand at `esp` reads the same after writes to registers but `esp`, memory kept. -/
theorem src_esp {s t : State} {rs : List Reg} (K : Keeps rs s t) (esp : .esp ∉ rs) (m : t.mem = s.mem)
    {d : Nat} : readSrc t (.mem (at_ .esp d)) = readSrc s (.mem (at_ .esp d)) := by
  simp only [readSrc, State.load32, State.ea, at_, K.1 _ esp, m, K.2.1, K.2.2]; rfl

theorem optVal_ok {t : State} {g : Nat → BitVec 32} {n : Nat} {o : Option Nat} (ho : ∀ j, o = some j → j < n)
    (hr : ∀ j < n, readSrc t (.mem (argAt 19 j)) = some (g j))
    (k : ∀ u, Keeps [.eax] t u → u.mem = t.mem → u.gpr .eax = optArg g o → WP isa (.block is) u Q) :
    WP isa (.block (optVal o ++ is)) t Q := by
  cases o with
  | none => exact wp_movS rfl fun u U _ => k u U.keeps U.mem U.gpr
  | some j => exact wp_movS (hr j (ho j rfl)) fun u U _ => k u U.keeps U.mem U.gpr

/-- `val a i`: `eax` synthetic argument `i`; only `eax` and `ecx` change. -/
theorem val_ok {t : State} {a : Args} {g : Nat → BitVec 32} {n : Nat} (hb : Below a n)
    (hr : ∀ j < n, readSrc t (.mem (argAt 19 j)) = some (g j)) (i : Nat)
    (k : ∀ u, Keeps [.eax, .ecx] t u → u.mem = t.mem → u.gpr .eax = synth a g i → WP isa (.block is) u Q) :
    WP isa (.block (val a i ++ is)) t Q := by
  obtain opt : ∀ {o : Option Nat}, (∀ j, o = some j → j < n) → synth a g i = optArg g o → val a i = optVal o →
      WP isa (.block (val a i ++ is)) t Q := fun ho e v => by
    rw [v]; exact optVal_ok ho hr fun u K m e' => k u (K.mono (by decide)) m (by rw [e', e])
  obtain arg : ∀ {j : Nat}, j < n → synth a g i = g j → val a i = argVal j → WP isa (.block (val a i ++ is)) t Q :=
    fun hj e v => by
      rw [v]; exact wp_movS (hr _ hj) fun u U _ => k u (U.keeps.mono (by decide)) U.mem (by rw [U.gpr, e])
  obtain comp : ∀ {c : Nat}, c ≤ 2 → val a i = compVal a c →
      synth a g i = (List.replicate c (g a.plen)).foldl (· + ·) (g a.dom) → WP isa (.block (val a i ++ is)) t Q :=
    fun {c} hc v e => by
      rw [v]
      simp only [compVal, List.cons_append, List.nil_append]
      refine wp_movS (hr _ hb.dom) fun u₁ U₁ _ => ?_
      obtain r₁ : readSrc u₁ (.mem (argAt 19 a.plen)) = some (g a.plen) := by
        unfold argAt; rw [src_esp U₁.keeps (by decide) U₁.mem]; exact hr _ hb.plen
      refine wp_movS r₁ fun u₂ U₂ _ => ?_
      obtain e₂ : u₂.gpr .eax = g a.dom := by rw [U₂.other _ (by decide), U₁.gpr]
      have c₂ : u₂.gpr .ecx = g a.plen := U₂.gpr
      obtain K₂ : Keeps [.eax, .ecx] t u₂ := (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
      obtain M₂ : u₂.mem = t.mem := U₂.mem.trans U₁.mem
      match c, hc with
      | 0, _ => exact k u₂ K₂ M₂ (by rw [e, e₂]; rfl)
      | 1, _ =>
        refine wp_addS rfl fun u U _ => k u (K₂.trans (U.keeps.mono (by decide))) (U.mem.trans M₂) ?_
        rw [U.gpr, e₂, c₂, e]; rfl
      | 2, _ =>
        refine wp_addS rfl fun u₃ U₃ _ => wp_addS rfl fun u U _ =>
          k u ((K₂.trans (U₃.keeps.mono (by decide))).trans (U.keeps.mono (by decide))) (U.mem.trans (U₃.mem.trans M₂)) ?_
        rw [U.gpr, U₃.gpr, U₃.other _ (by decide), e₂, c₂, e]; rfl
  obtain zero : synth a g i = 0 → val a i = zeroVal → WP isa (.block (val a i ++ is)) t Q := fun e v => by
    rw [v]; exact wp_movS rfl fun u U _ => k u (U.keeps.mono (by decide)) U.mem (by rw [U.gpr, e])
  match i with
  | 0 => exact opt hb.out rfl rfl
  | 1 => exact arg hb.plen rfl rfl
  | 2 => exact comp (c := 0) (by decide) rfl rfl
  | 3 => exact arg hb.plen rfl rfl
  | 4 => exact comp (c := 1) (by decide) rfl rfl
  | 5 => exact arg hb.plen rfl rfl
  | 6 => exact comp (c := 2) (by decide) rfl rfl
  | 7 => exact arg hb.plen rfl rfl
  | 8 => exact opt hb.y rfl rfl
  | 9 => exact opt (o := a.y.map fun _ => a.plen) (fun j hj => by
      cases hy : a.y with
      | none => rw [hy] at hj; cases hj
      | some _ => rw [hy] at hj; cases hj; exact hb.plen) rfl rfl
  | 10 => exact opt (fun j hj => by have := hb.x j hj; omega_using [this]) rfl rfl
  | 11 => exact opt (o := a.x.map (· + 1)) (fun j hj => by
      cases hx : a.x with
      | none => rw [hx] at hj; cases hj
      | some _ => rw [hx] at hj; cases hj; exact hb.x _ hx) rfl rfl
  | 12 => exact arg hb.dlen rfl rfl
  | 13 => exact opt hb.ctx rfl rfl
  | 14 => exact zero rfl rfl
  | 15 => exact zero rfl rfl
  | 16 => exact arg (by have := hb.ws; omega_using [this]) rfl rfl
  | 17 => exact arg hb.ws rfl rfl
  | _ + 18 => exact zero rfl rfl

/-- The frame's word of synthetic argument `i`. -/
abbrev slotAddr (P : Addr) (i : Nat) : Addr := P + BitVec.ofNat 64 (4 + 4 * i)

/-- A store into the frame of 76 bytes at `esp`. -/
theorem frame76_store {t : State} {P : Addr} (hP : (t.gpr .esp).setWidth 64 = P)
    (hesp : (t.gpr .esp).toNat + 76 ≤ 2 ^ 32) (hfr : (⟨P, 76⟩ : Region) ∈ t.wr) {i : Nat} (hi : i < 18) :
    t.ea (slotOp i) = slotAddr P i ∧ InRegions t.wr (slotAddr P i) 4 := by
  refine ⟨?_, ⟨_, hfr, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩⟩
  rw [slotOp, at_, ea_mk, addr_eq (by omega_using [hesp, hi]), hP]

/-- A word of the frame, after a store to another. -/
theorem frame76_other (m : Mem) (P : Addr) (v : BitVec 32) {i j : Nat} (h : i ≠ j) (hi : i < 18) (hj : j < 18) :
    (m.writeW (slotAddr P i) v).readW (slotAddr P j) 32 = m.readW (slotAddr P j) 32 :=
  Mem.readW_writeW_sep (Offset.sep P (by omega_using [h]) (by omega_using [hj]) (by omega_using [hi])) (by decide)

/-- An argument at `esp` reads the same after changes to registers but `esp` and memory within
regions apart from it. -/
theorem src_frame {t u : State} {rs : List Reg} (K : Keeps rs t u) (esp : .esp ∉ rs) {R : List Region}
    (F : Frame R t.mem u.mem) {d : Nat} (hd : ∀ r ∈ R, Region.Disjoint ⟨t.ea (at_ .esp d), 4⟩ r) :
    readSrc u (.mem (at_ .esp d)) = readSrc t (.mem (at_ .esp d)) := by
  obtain e : u.ea (at_ .esp d) = t.ea (at_ .esp d) := by simp only [State.ea, at_, K.1 _ esp]
  simp only [readSrc, State.load32, e, K.2.1, K.2.2]
  rw [F.readW (r := ⟨t.ea (at_ .esp d), 4⟩) (Region.contains_self _ _) hd (by decide)]

/-- The first `c` synthetic arguments stored into the frame at `P` (`esp`), keeping everything else
but `eax` and `ecx`. -/
theorem fill_ok {t : State} {a : Args} {g : Nat → BitVec 32} {n : Nat} (hb : Below a n) {P : Addr}
    (hP : (t.gpr .esp).setWidth 64 = P) (hesp : (t.gpr .esp).toNat + 76 ≤ 2 ^ 32)
    (hfr : (⟨P, 76⟩ : Region) ∈ t.wr)
    (hr : ∀ j < n, readSrc t (.mem (argAt 19 j)) = some (g j))
    (hargs : ∀ j < n, Region.Disjoint ⟨t.ea (argAt 19 j), 4⟩ ⟨P, 76⟩) :
    ∀ c, c ≤ 18 → ∀ {is : List Instr} {Q : State → Prop},
      (∀ u, Keeps [.eax, .ecx] t u → Frame [⟨P, 76⟩] t.mem u.mem →
        (∀ i < c, u.mem.readW (slotAddr P i) 32 = synth a g i) → WP isa (.block is) u Q) →
      WP isa (.block ((List.range c).flatMap (piece a) ++ is)) t Q
  | 0, _, _, _, k => k t (Keeps.refl _ _) (Frame.refl _ _) fun _ h => absurd h (by omega_using [])
  | c + 1, hc, is, Q, k => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine fill_ok hb hP hesp hfr hr hargs c (by omega_using [hc]) fun u K F S => ?_
    obtain hr' : ∀ j < n, readSrc u (.mem (argAt 19 j)) = some (g j) := by
      intro j hj
      rw [← hr j hj]
      exact src_frame K (by decide) F fun r hr => by rw [List.mem_singleton.mp hr]; exact hargs j hj
    unfold piece
    rw [List.append_assoc]
    refine val_ok hb hr' c fun v Kv mv ev => ?_
    obtain Pv : (v.gpr .esp).setWidth 64 = P := by rw [Kv.1 _ (by decide), K.1 _ (by decide), hP]
    obtain ev' : (v.gpr .esp).toNat + 76 ≤ 2 ^ 32 := by rw [Kv.1 _ (by decide), K.1 _ (by decide)]; exact hesp
    obtain wv : (⟨P, 76⟩ : Region) ∈ v.wr := by rw [Kv.2.2, K.2.2]; exact hfr
    obtain ⟨ea, wr⟩ := frame76_store Pv ev' wv (i := c) (by omega_using [hc])
    refine wp_storeS ea wr fun w M => ?_
    refine k w ((K.trans Kv).trans (M.keeps _)) ?_ fun i hi => ?_
    · rw [M.mem, mv]
      exact F.trans (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega_using [hc]) (by omega_using [hc])))
    · rw [M.mem, mv]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [frame76_other _ _ _ (by omega_using [hi]) (by omega_using [hc]) (by omega_arith), S i hi]
      · rw [Mem.readW_writeW_self32, ev]

end

end VG.Proof.Ffdh.X86

end

end


/-!
# FFDH on i686: entry and return around the frame of the synthetic arguments

`wrap_ok`: `wrap a body` saves the callee-saved registers in the working
space's header, allocates the frame of the synthetic arguments and fills it,
so that `body` runs from a state of private CRT's operations (`In`), and
restores the registers: what `body` leaves in memory and `eax`, with the
caller's ABI preserved.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86

open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.CrtRt (In)
open VG.Impl.Ffdh.X86 (Args argsFrame fill entry wrap)
open VG.Proof.Dsa.X86 (argumentPointer stackAddress stackValue StackArgument)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The working space's base, its bytes, and the modulus's length. -/
abbrev wsBase (a : Args) (s : State) : Addr := argumentPointer s a.ws
abbrev wsSize (a : Args) (s : State) : Nat := (arg s (a.ws + 1)).toNat * 8
abbrev pLenOf (a : Args) (s : State) : Nat := (arg s a.plen).toNat

/-- The frame of the synthetic arguments, below the entry's `esp`. -/
abbrev frameAt (s : State) : Addr := (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64

/-- What `wrap a body` needs of the entry state, a function of `n` arguments, which it may overwrite. -/
structure WrapABI (a : Args) (n : Nat) (s : State) : Prop where
  below : Below a n
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32
  argsIn : (⟨argAddr s 0, 4 * n⟩ : Region) ∈ s.wr
  wsIn : (⟨wsBase a s, wsSize a s⟩ : Region) ∈ s.wr
  scratchArgs : Region.Disjoint ⟨wsBase a s, wsSize a s⟩ ⟨argAddr s 0, 4 * n⟩
  retScratch : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨wsBase a s, wsSize a s⟩
  belowScratch : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ ⟨wsBase a s, wsSize a s⟩
  scratchBound : (arg s a.ws).toNat + wsSize a s ≤ 2 ^ 32
  lower : 64 ≤ pLenOf a s
  upper : pLenOf a s ≤ 1024
  scratchLength : Spec.Rsa.scratchWords (pLenOf a s) ≤ (arg s (a.ws + 1)).toNat

section
variable {a : Args} {n : Nat} {s : State}

theorem WrapABI.argument (A : WrapABI a n s) {i : Nat} (hi : i < n) : StackArgument s (wsBase a s) (wsSize a s) i :=
  VG.Proof.Dsa.X86.stackArgument_of (count := n) (by have := A.stackBound; omega_using [this]) hi
    (List.mem_append_right _ A.argsIn) A.scratchArgs.symm

theorem WrapABI.need (A : WrapABI a n s) : CrtRt.need (pLenOf a s) ≤ wsSize a s := by
  have := A.scratchLength
  have := A.lower
  have := A.upper
  simp only [CrtRt.need, CrtRt.st, CrtRt.bc, CrtRt.mw, Spec.Rsa.modulusWords, Impl.Bignum.X86.CrtRt.numBase,
    Spec.Rsa.scratchWords, wsSize] at *
  omega_arith

theorem WrapABI.base_toNat (_ : WrapABI a n s) : (wsBase a s).toNat = (arg s a.ws).toNat := by
  simp only [wsBase, argumentPointer, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans (arg s a.ws).isLt (by decide : 2 ^ 32 < 2 ^ 64))]

/-- `entry a`: `edi` the working space, the callee-saved registers saved in its header. -/
theorem entry_ok (A : WrapABI a n s) :
    WP isa (.block (entry a)) s fun t =>
      Scr t (wsBase a s) (wsSize a s) ∧ Saved t.mem (off (wsBase a s)) s.gpr Impl.Bignum.X86.Crt.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧ Outside (wsBase a s) 0 (wsSize a s) s.mem t.mem := by
  obtain hz : 48 ≤ wsSize a s := by have := A.need; simp only [CrtRt.need, Impl.Bignum.X86.CrtRt.numBase] at this; omega_using [this]
  have hb := A.base_toNat
  obtain read := (A.argument (i := a.ws) (by have := A.below.ws; omega_using [this])).readSrc
  obtain stk : StkOk (s.gpr .esp) (wsBase a s) (wsSize a s) :=
    VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 172) A.stackLow (by rw [hb]; exact A.scratchBound)
      (by omega_using [hz]) A.belowScratch
  unfold entry
  rw [show Impl.Bignum.X86.CrtRt.save = Impl.Bignum.X86.Crt.save from rfl]
  simp only [List.singleton_append]
  refine wp_movS read fun u U _ => ?_
  refine WP.block_append (WP.mono (Crt.entrySave_ok (base := wsBase a s) (size := wsSize a s)
    (by rw [U.gpr]; rfl) (by rw [U.gpr]; exact A.scratchBound) hz (by rw [U.wr]; exact A.wsIn))
    fun v ⟨G, Rd, Wr, S, F⟩ => ?_)
  refine wp_movS rfl fun t T _ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [T.gpr, G, U.gpr]; rfl
    · rw [T.wr, Wr, U.wr]; exact A.wsIn
    · rw [hb]; exact A.scratchBound
    · rw [T.other _ (by decide), G, U.other _ (by decide)]
      exact stk
  · intro p hp
    rw [T.mem, S p hp]
    obtain H : p.1 ≠ .eax := by
      simp only [Impl.Bignum.X86.Crt.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    exact U.other _ H
  · refine ⟨?_, ?_, ?_⟩
    · intro reg hr
      rw [T.other reg (by intro H; subst reg; exact hr (by simp)), G]
      exact U.other reg (by intro H; subst reg; exact hr (by simp))
    · rw [T.rd, Rd, U.rd]
    · rw [T.wr, Wr, U.wr]
  · intro x hx
    rw [T.mem]
    obtain H : ¬ InRegions [⟨wsBase a s, wsSize a s⟩] x 1 := by
      simp only [InRegions, List.mem_singleton, exists_eq_left, Region.Contains]
      change ¬ (ofs (wsBase a s) x + 1 ≤ wsSize a s)
      omega_using [hx]
    exact (F x (by intro reg hreg hcontains; exact H ⟨reg, hreg, hcontains⟩)).trans (congrFun U.mem x)

/-- The entry's argument `j` read through the frame of the synthetic arguments. -/
theorem argAt_frame (A : WrapABI a n s) {s₁ : State} (K : Keeps [.eax, .edi] s s₁)
    (O : Outside (wsBase a s) 0 (wsSize a s) s.mem s₁.mem) {j : Nat} (hj : j < n) :
    readSrc (allocFrame argsFrame s₁) (.mem (argAt 19 j)) = some (arg s j) ∧
      Region.Disjoint ⟨(allocFrame argsFrame s₁).ea (argAt 19 j), 4⟩ ⟨frameAt s, argsFrame⟩ := by
  obtain SA := A.argument hj
  have fb : argsFrame = 76 := rfl
  have st' : stack = 172 := rfl
  obtain sp : s₁.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  have low := A.stackLow
  have top := A.stackBound
  obtain hE := (s.gpr .esp).isLt
  obtain ea : (allocFrame argsFrame s₁).ea (argAt 19 j) = stackAddress s j := by
    simp only [State.ea, argAt, at_, allocFrame_esp, sp, stackAddress, addr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, argsFrame]
    omega_using []
  obtain SE : stackAddress s j = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * j) := addr_eq (by omega_using [hj, top])
  obtain FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega_using [fb, st', low])
  refine ⟨?_, ?_⟩
  · simp only [readSrc, State.load32, ea, allocFrame_mem, allocFrame_rd, allocFrame_wr]
    obtain rd : InRegions (s₁.rd ++ ⟨(s₁.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64, argsFrame⟩ :: s₁.wr)
        (stackAddress s j) 4 := by
      obtain ⟨r, hr, hc⟩ := SA.read
      refine ⟨r, ?_, hc⟩
      rw [K.2.1, K.2.2] at *
      rcases List.mem_append.mp hr with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    rw [ite_eq_left_of_eq_true _ _ (eq_true rd)]
    obtain F := VG.Proof.Bignum.outside_frame O (by have := A.scratchBound; have := A.base_toNat; omega_arith)
    simp only [off, BitVec.add_zero] at F
    exact congrArg some (F.readW (r := ⟨stackAddress s j, 4⟩) (Region.contains_self _ _)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact SA.apart) (by decide))
  · rw [ea, SE, FA]
    exact Offset.disjoint_below _ (by omega_using [hj, fb, top])

/-- The state after the frame of the synthetic arguments is filled: private CRT's operations' inputs
`In`, from the entry state `s` and the state `s₁` after `entry`. -/
theorem frameIn_ok (A : WrapABI a n s) {s₁ : State} (S : Scr s₁ (wsBase a s) (wsSize a s))
    (K : Keeps [.eax, .edi] s s₁) (O : Outside (wsBase a s) 0 (wsSize a s) s.mem s₁.mem)
    {Ex : List Region → List Region → Prop} (hx : Ex s.rd (⟨frameAt s, argsFrame⟩ :: s.wr))
    {is : List Instr} {Q : State → Prop}
    (k : ∀ f, In Ex (wsBase a s) (wsSize a s) (pLenOf a s) (synth a (arg s)) f →
      f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame → f.rd = s.rd →
      f.wr = ⟨frameAt s, argsFrame⟩ :: s.wr →
      Frame [⟨wsBase a s, wsSize a s⟩, ⟨frameAt s, argsFrame⟩] s.mem f.mem →
      Frame [⟨frameAt s, argsFrame⟩] s₁.mem f.mem →
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esp → f.gpr r = s₁.gpr r) → WP isa (.block is) f Q) :
    WP isa (.block (fill a ++ is)) (allocFrame argsFrame s₁) Q := by
  obtain sp : s₁.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  have fb : argsFrame = 76 := rfl
  have st' : stack = 172 := rfl
  have low := A.stackLow
  have top := A.stackBound
  obtain hE := (s.gpr .esp).isLt
  have hb := A.base_toNat
  have bd := A.scratchBound
  have nd := A.need
  obtain hz : 48 ≤ wsSize a s := by
    have := nd; simp only [CrtRt.need, Impl.Bignum.X86.CrtRt.numBase] at this; omega_using [this]
  have lo := A.lower
  have hi := A.upper
  obtain FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega_using [fb, st', low])
  obtain t0esp : (allocFrame argsFrame s₁).gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame := by
    rw [allocFrame_esp, sp]
  obtain t0P : ((allocFrame argsFrame s₁).gpr .esp).setWidth 64 = frameAt s := by rw [t0esp]
  obtain espN : (s.gpr .esp - BitVec.ofNat 32 argsFrame).toNat = (s.gpr .esp).toNat - 76 :=
    VG.X86.sub_toNat (by omega_using [fb, st', low])
  refine fill_ok A.below t0P (by rw [t0esp, espN]; omega_using [])
    (by rw [allocFrame_wr, sp]; exact List.mem_cons_self ..)
    (fun j hj => (argAt_frame A K O hj).1) (fun j hj => (argAt_frame A K O hj).2) 18 (Nat.le_refl _)
    fun f Kf Ff Sf => ?_
  -- The frame lies below the entry's `esp`, within the 172 bytes apart from the working space.
  obtain frameSub : Region.Sub ⟨frameAt s, argsFrame⟩ ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
    rw [FA]; exact Offset.sub_below _ (by decide) (by decide)
  obtain frameWs : Region.Disjoint ⟨frameAt s, argsFrame⟩ ⟨wsBase a s, wsSize a s⟩ :=
    A.belowScratch.sub_left frameSub
  obtain espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame := by rw [Kf.1 _ (by decide), t0esp]
  obtain espfN : (f.gpr .esp).toNat = (s.gpr .esp).toNat - 76 := by rw [espf, espN]
  obtain edif : f.gpr .edi = s₁.gpr .edi := by rw [Kf.1 _ (by decide), allocFrame_gpr _ _ (by decide)]
  obtain rdf : f.rd = s.rd := by rw [Kf.2.1, allocFrame_rd, K.2.1]
  obtain wrf : f.wr = ⟨frameAt s, argsFrame⟩ :: s.wr := by rw [Kf.2.2, allocFrame_wr, sp, K.2.2]
  obtain belowf : Region.Disjoint (below (f.gpr .esp) 96) ⟨wsBase a s, wsSize a s⟩ := by
    refine A.belowScratch.sub_left ?_
    simp only [below]
    rw [espf, VG.X86.Taint.sub_setWidth (by rw [espN]; omega_using [st', low]),
      show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA,
      ← VG.Offset.sub_add_eq, show BitVec.ofNat 64 argsFrame + 96#64 = BitVec.ofNat 64 172 from rfl]
    exact Region.sub_prefix (by decide)
  obtain stackF : ∀ i < 18, CallArgument f (wsBase a s) (wsSize a s) i (synth a (arg s) i) := by
    intro i hi
    obtain SAd : stackAddress f i = slotAddr (frameAt s) i := by
      rw [stackAddress, espf, addr_eq (by rw [espN]; omega_using [hi])]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [SAd, rdf, wrf]
      exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), Offset.contains_base _ (by omega_using [fb, hi]) (by omega_using [hi])⟩
    · rw [SAd]; exact frameWs.sub_left (Offset.sub_base _ (by omega_using [fb, hi]))
    · show f.mem.readW (stackAddress f i) 32 = _
      rw [SAd]; exact Sf i hi
  obtain stk : StkOk (f.gpr .esp) (wsBase a s) (wsSize a s) := by
    refine VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 96) (by rw [espfN]; omega_using [st', low]) (by rw [hb]; exact bd)
      (by omega_using [hz]) ?_
    have := belowf
    simp only [below] at this
    rwa [VG.X86.Taint.sub_setWidth (by rw [espfN]; omega_using [st', low])] at this
  obtain Ft : Frame [⟨wsBase a s, wsSize a s⟩, ⟨frameAt s, argsFrame⟩] s.mem f.mem := by
    obtain F₁ := VG.Proof.Bignum.outside_frame O (by omega_using [bd])
    simp only [off, BitVec.add_zero] at F₁
    exact (F₁.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..).trans
      (by rw [← allocFrame_mem argsFrame s₁]
          exact Ff.mono fun r hr => by
            rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
  refine k f ⟨⟨by rw [edif]; exact S.edi, by rw [wrf]; exact List.mem_cons_of_mem _ (by rw [← K.2.2]; exact S.wr),
      S.nowrap, stk⟩, A.lower, A.upper, stackF, ?_, ⟨by rw [espfN]; omega_using [st', low], belowf⟩, by rw [espfN]; omega_using [], A.need,
      hb.symm, rfl, by rw [rdf, wrf]; exact hx⟩ espf rdf wrf Ft (by rw [← allocFrame_mem argsFrame s₁]; exact Ff) ?_
  · show arg s a.plen = _
    simp only [pLenOf, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro r h1 h2 h3
    rw [Kf.1 r (by simp [h1, h2]), allocFrame_gpr _ _ h3]

/-- The saved registers' words, within the working space's header. -/
theorem saved_keep {base : Addr} {m m' : Mem} {g : Reg → BitVec 32} {rs : List Region}
    (F : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨off base 32, 16⟩ r)
    (S : Saved m (off base) g Impl.Bignum.X86.Crt.savedRegisters) :
    Saved m' (off base) g Impl.Bignum.X86.Crt.savedRegisters := by
  intro p hp
  obtain B : 32 ≤ p.2 ∧ p.2 + 4 ≤ 48 := by
    simp only [Impl.Bignum.X86.Crt.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  exact (F.readW (r := ⟨off base 32, 16⟩) (Offset.contains base B.1 (by omega_using [B]) (by decide)) hd (by decide)).trans
    (S p hp)

/-- A range of `fR`, past the saved registers' words. -/
theorem fR_saved {base : Addr} {len size : Nat} (hn : base.toNat + size ≤ 2 ^ 32) (hf : CrtRt.need len ≤ size) :
    ∀ p ∈ fR len, Region.Disjoint ⟨off base 32, 16⟩ ⟨off base p.1, p.2⟩ := by
  have : 48 ≤ CrtRt.need len := by simp only [CrtRt.need, Impl.Bignum.X86.CrtRt.numBase]; omega_using []
  intro p hp
  simp only [fR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact Offset.disjoint base (d := 32) (n := 16) (e := 0) (k := 32) (.inr (Nat.le_refl _)) (by decide) (by decide)
  · exact Offset.disjoint base (d := 32) (n := 16) (e := 48) (k := CrtRt.need len - 48) (.inl (Nat.le_refl _))
      (by decide) (by omega_using [hn, hf])

/-- `wrap a body`: what `body` leaves in memory and `eax`, run from the state `In` of private CRT's
operations, with the ABI preserved and the statics where they were. `body` may also write the regions
`Out`, apart from the return address and the working space. -/
theorem wrap_syms_ok (A : WrapABI a n s) {body : Prog isa} (hsp : NoSp (.seq (.block (fill a)) body))
    {Ex : List Region → List Region → Prop} (hx : Ex s.rd (⟨frameAt s, argsFrame⟩ :: s.wr))
    {Out : List Region} (outRet : ∀ r ∈ Out, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r)
    (outWs : ∀ r ∈ Out, Region.Disjoint ⟨wsBase a s, wsSize a s⟩ r) {P : Mem → BitVec 32 → Prop}
    (hb : ∀ f, In Ex (wsBase a s) (wsSize a s) (pLenOf a s) (synth a (arg s)) f →
      f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame →
      Frame [⟨wsBase a s, wsSize a s⟩, ⟨frameAt s, argsFrame⟩] s.mem f.mem → f.syms = s.syms →
      WP isa body f fun t => P t.mem (t.gpr .eax) ∧
        Frame (Out ++ CrtRt.frameR (wsBase a s) (f.gpr .esp) (fR (pLenOf a s))) f.mem t.mem ∧
        Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f t) :
    WP isa (wrap a body) s fun u => P u.mem (u.gpr .eax) ∧ abiPreserved s u := by
  have fb : argsFrame = 76 := rfl
  have st' : stack = 172 := rfl
  have low := A.stackLow
  have top := A.stackBound
  obtain hE := (s.gpr .esp).isLt
  have hb' := A.base_toNat
  have bd := A.scratchBound
  have nd := A.need
  obtain hz : 48 ≤ wsSize a s := by
    have := nd; simp only [CrtRt.need, Impl.Bignum.X86.CrtRt.numBase] at this; omega_using [this]
  obtain FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega_using [fb, st', low])
  unfold wrap
  refine WP.seq (WP.mono_syms (entry_ok A) fun s₁ ⟨S, Sv, K, O⟩ sy₁ => ?_)
  obtain sp : s₁.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  -- The saved registers and the return address, kept by what the frame changes.
  have retWs := A.retScratch
  obtain retFrame : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨frameAt s, argsFrame⟩ := by
    rw [FA]; exact Offset.base_disjoint_below _ (by omega_using [fb])
  let R : State → Prop := fun u => P u.mem (u.gpr .eax) ∧ Scr u (wsBase a s) (wsSize a s) ∧
    Saved u.mem (off (wsBase a s)) s.gpr Impl.Bignum.X86.Crt.savedRegisters ∧ u.gpr .esp = s.gpr .esp ∧
    u.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32
  refine WP.seq (WP.mono (Q := R) (WP.frameAlloc (bytes := argsFrame) (by decide) (by decide) (by decide)
    (by rw [sp]; omega_using [fb, st', low]) hsp ?_) fun s₂ R₂ => ?_)
  · rw [show Impl.Ffdh.X86.fill a = Impl.Ffdh.X86.fill a ++ [] from (List.append_nil _).symm]
    refine WP.seq (WP.mono_syms (frameIn_ok A S K O hx (Q := fun f =>
        In Ex (wsBase a s) (wsSize a s) (pLenOf a s) (synth a (arg s)) f ∧
        f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame ∧ f.wr = ⟨frameAt s, argsFrame⟩ :: s.wr ∧
        Frame [⟨wsBase a s, wsSize a s⟩, ⟨frameAt s, argsFrame⟩] s.mem f.mem ∧
        Frame [⟨frameAt s, argsFrame⟩] s₁.mem f.mem ∧
        (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esp → f.gpr r = s₁.gpr r))
      fun f I espf _ wrf Ft Ff₁ regs => WP.block_nil ⟨I, espf, wrf, Ft, Ff₁, regs⟩)
      fun f ⟨I, espf, wrf, Ft, Ff₁, regs⟩ syf => ?_)
    refine WP.mono (hb f I espf Ft (syf.trans sy₁)) fun t ⟨Pt, Fb, Kt⟩ => ?_
    obtain espt : t.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame := (Kt.1 _ (by decide)).trans espf
    obtain ediT : t.gpr .edi = s₁.gpr .edi := (Kt.1 _ (by decide)).trans (regs _ (by decide) (by decide) (by decide))
    obtain espN : (s.gpr .esp - BitVec.ofNat 32 argsFrame).toNat = (s.gpr .esp).toNat - 76 :=
      VG.X86.sub_toNat (by omega_using [fb, st', low])
    obtain belowRet : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ (below (f.gpr .esp) 96) := by
      simp only [below]
      rw [espf, VG.X86.Taint.sub_setWidth (by rw [espN]; omega_using [st', low]),
        show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA,
        ← VG.Offset.sub_add_eq, show BitVec.ofNat 64 argsFrame + 96#64 = BitVec.ofNat 64 172 from rfl]
      exact (Offset.base_disjoint_below _ (n := 172) (k := 4) (by decide)).sub_right (Region.sub_prefix (by decide))
    obtain bnd : (wsBase a s).toNat + wsSize a s ≤ 2 ^ 32 := by rw [hb']; exact bd
    obtain savedSub : Region.Sub ⟨off (wsBase a s) 32, 16⟩ ⟨wsBase a s, wsSize a s⟩ :=
      Offset.sub_base _ (d := 32) (n := 16) (by omega_using [hz])
    obtain belowWs : Region.Disjoint ⟨off (wsBase a s) 32, 16⟩ (below (f.gpr .esp) 96) :=
      (I.room.apart.sub_right savedSub).symm
    obtain frameWs16 : Region.Disjoint ⟨off (wsBase a s) 32, 16⟩ ⟨frameAt s, argsFrame⟩ := by
      obtain frameSub : Region.Sub ⟨frameAt s, argsFrame⟩ ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
        rw [FA]; exact Offset.sub_below _ (by decide) (by decide)
      exact ((A.belowScratch.sub_left frameSub).sub_right savedSub).symm
    obtain Sv₁ : Saved f.mem (off (wsBase a s)) s.gpr Impl.Bignum.X86.Crt.savedRegisters :=
      saved_keep Ff₁ (fun r hr => by rw [List.mem_singleton.mp hr]; exact frameWs16) Sv
    obtain Svt : Saved t.mem (off (wsBase a s)) s.gpr Impl.Bignum.X86.Crt.savedRegisters := by
      refine saved_keep Fb (fun r hr => ?_) Sv₁
      rcases List.mem_append.mp hr with hr | hr
      · exact ((outWs r hr).sub_left savedSub)
      · rw [CrtRt.frameR, List.mem_cons, List.mem_map] at hr
        rcases hr with rfl | ⟨p, hp, rfl⟩
        · exact belowWs
        · exact fR_saved bnd nd p hp
    obtain F₀ := VG.Proof.Bignum.outside_frame O (by omega_using [bd])
    simp only [off, BitVec.add_zero] at F₀
    obtain Ret : t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
      rw [Fb.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) ?_ (by decide),
        Ff₁.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _)
          (fun r hr => by rw [List.mem_singleton.mp hr]; exact retFrame) (by decide),
        F₀.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _)
          (fun r hr => by rw [List.mem_singleton.mp hr]; exact retWs) (by decide)]
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact outRet r hr
      · rw [CrtRt.frameR, List.mem_cons, List.mem_map] at hr
        rcases hr with rfl | ⟨p, hp, rfl⟩
        · exact belowRet
        · have := fR_fit I p hp
          exact retWs.sub_right (Offset.sub_base _ (by omega_using [this]))
    refine ⟨by rw [freed_mem, freed_gpr _ _ (by decide)]; exact Pt, ⟨?_, ?_, S.nowrap, ?_⟩, Svt, ?_, Ret⟩
    · rw [freed_gpr _ _ (by decide), ediT]; exact S.edi
    · rw [freed_wr, Kt.2.2, wrf]; exact (K.2.2 ▸ S.wr)
    · rw [freed_esp, espt, BitVec.sub_add_cancel, ← sp]; exact S.stk
    · rw [freed_esp, espt, BitVec.sub_add_cancel]
  · obtain ⟨P₂, S₂, Sv₂, esp₂, ret₂⟩ := R₂
    refine WP.mono (Crt.entryRestore_ok S₂ hz Sv₂) fun u Rs => ?_
    refine ⟨by rw [Rs.mem, Rs.other .eax (by decide)]; exact P₂, ?_, by rw [Rs.mem]; exact ret₂⟩
    intro reg hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Rs.gpr (.ebx, 32) (by decide)
    · exact Rs.gpr (.esi, 40) (by decide)
    · exact Rs.gpr (.edi, 44) (by decide)
    · exact Rs.gpr (.ebp, 36) (by decide)
    · exact (Rs.other _ (by decide)).trans esp₂


theorem wrap_ok (A : WrapABI a n s) {body : Prog isa} (hsp : NoSp (.seq (.block (fill a)) body))
    {Ex : List Region → List Region → Prop} (hx : Ex s.rd (⟨frameAt s, argsFrame⟩ :: s.wr))
    {Out : List Region} (outRet : ∀ r ∈ Out, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r)
    (outWs : ∀ r ∈ Out, Region.Disjoint ⟨wsBase a s, wsSize a s⟩ r) {P : Mem → BitVec 32 → Prop}
    (hb : ∀ f, In Ex (wsBase a s) (wsSize a s) (pLenOf a s) (synth a (arg s)) f →
      f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame →
      Frame [⟨wsBase a s, wsSize a s⟩, ⟨frameAt s, argsFrame⟩] s.mem f.mem →
      WP isa body f fun t => P t.mem (t.gpr .eax) ∧
        Frame (Out ++ CrtRt.frameR (wsBase a s) (f.gpr .esp) (fR (pLenOf a s))) f.mem t.mem ∧
        Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f t) :
    WP isa (wrap a body) s fun u => P u.mem (u.gpr .eax) ∧ abiPreserved s u :=
  wrap_syms_ok A hsp hx outRet outWs fun f I e F _ => hb f I e F

end

end VG.Proof.Ffdh.X86
