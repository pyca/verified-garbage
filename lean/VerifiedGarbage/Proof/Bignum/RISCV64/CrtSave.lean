module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.Bignum.RISCV64.Crt
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreSave
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA private-key operation on RISC-V: saving, the arguments and the working spaces

* `save_ok`: the working space's address `S`, the ninth stack argument, into
  `t0` and `s6`, and `s0`–`s5`, `s7`–`s11`, `ra` and `s6` (`Crt.saved`) into
  its header from byte 112; `restore_ok`: them back through `s6`, `s6` last.
* `args_ok`: the arguments into the header's words 0–10 (`ArgsHdr`).
* `setupX_ok`: `X`'s registers (`W = 2 ⌈k / 8⌉` words, array 0 in `a7` and
  `ra`, the arrays' size in `s5` and `s11`, `W` in `t0`) and the bases of
  `P` and `Q` into the header's words 12 and 13 (`oBP`, `oBQ`).
* `setupP_ok`: a prime's working space's registers, from its base and
  length in the header (`wordsOf`: `max(2, ⌈len / 8⌉)` words).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64 (Scr off_add add_ofNat_zero)
open VG.Proof.Bignum (slot)

/-! ## Saving and restoring -/

/-- The saved registers' words, 104 bytes. -/
abbrev savR (w : Addr) : Region := ⟨w, 104⟩

theorem saved_inj : ∀ i < 13, ∀ j < 13, saved i = saved j → i = j := by decide

theorem saved_ne : ∀ i < 12, saved i ≠ .s6 := by decide

theorem saved_12 : saved 12 = .s6 := rfl

theorem sav_contains (w : Addr) {i : Nat} (hi : i < 13) : (savR w).Contains (Mont.off w (8 * i)) 8 :=
  Offset.contains_base w (by omega_using [hi]) (by omega_using [hi])

theorem sav_sep (w : Addr) {i j : Nat} (hi : i < 13) (hj : j < 13) (h : i ≠ j) :
    Mem.Sep (Mont.off w (8 * i)) 8 (Mont.off w (8 * j)) 8 :=
  Offset.sep w (by omega_using [hi, hj, h]) (by omega_using [hi]) (by omega_using [hj])

/-- The saved registers' words of the working space at `S`. -/
abbrev savW (S : Addr) : Addr := S + BitVec.ofNat 64 112

theorem savOff_eq (S : Addr) (i : Nat) : S + BitVec.ofNat 64 (savOff i) = Mont.off (savW S) (8 * i) := by
  rw [Mont.off, Offset.add_add, savOff]

/-- The first `n` registers are saved, from `s₀` (whose `t0` is the working
space). -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [savR (savW (s₀.gpr .t0))] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (Mont.off (savW (s₀.gpr .t0)) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_step (s₀ : State) (hin : ∀ i < 13, InRegions s₀.wr (Mont.off (savW (s₀.gpr .t0)) (8 * i)) 8)
    (hal : ∀ i < 13, (Mont.off (savW (s₀.gpr .t0)) (8 * i)).toNat % 8 = 0)
    {n : Nat} (hn : n < 13) {s : State}
    (h : SI s₀ n s) : WP isa (.block [.store .d (saved n) .t0 (savOff n)]) s (SI s₀ (n + 1)) := by
  have hw : s.gpr .t0 = s₀.gpr .t0 := by rw [h.gpr]
  have hout : InRegions s.wr (s.gpr .t0 + BitVec.ofNat 64 (savOff n)) 8 := by
    rw [h.wr, hw, savOff_eq]; exact hin n hn
  have ha : (s.gpr .t0 + BitVec.ofNat 64 (savOff n)).toNat % 8 = 0 := by
    rw [hw, savOff_eq]; exact hal n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show savOff n < 2048 by unfold savOff; omega_using [hn]) ha hout,
    Option.some.injEq, exists_eq_left', hw, savOff_eq]
  refine ⟨h.gpr, h.rd, h.wr, h.sp,
    h.frame.writeW (List.mem_singleton_self _) _ (sav_contains _ hn), fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [Mem.readW_writeW_sep (sav_sep _ (by omega_using [hi, hn]) hn (by omega_using [hi])) (by decide)]
    exact h.saved i hi
  · rw [Mem.readW_writeW_self64, h.gpr]

/-- The state after `save`, from `s₀`, the working space at `S`. -/
structure Saved (s₀ : State) (S : Addr) (s : State) : Prop where
  keep : Keep [.t0, .s6] s₀ s
  sp : s.sp = s₀.sp
  s6 : s.gpr .s6 = S
  t0 : s.gpr .t0 = S
  frame : Frame [savR (savW S)] s₀.mem s.mem
  saved : ∀ i < 13, s.mem.readW (Mont.off (savW S) (8 * i)) 64 = s₀.gpr (saved i)

theorem saved_ne_t0 : ∀ i < 13, saved i ≠ .t0 := by decide

/-- `save`, the working space `S` the ninth stack argument, readable and
aligned (as the stack pointer is), and its header's words 14–26 writable and
aligned. -/
theorem save_ok (s₀ : State) {S : Addr} (hS : stackArg s₀ 8 = S)
    (hst : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 8) 8) (hsp : s₀.sp.toNat % 8 = 0)
    (hin : ∀ i < 13, InRegions s₀.wr (Mont.off (savW S) (8 * i)) 8)
    (hal : ∀ i < 13, (Mont.off (savW S) (8 * i)).toNat % 8 = 0) :
    WP isa (.block save) s₀ (Saved s₀ S) := by
  rw [save, List.append_assoc]
  have hst' : InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 64) 8 := by
    simpa only [stackArgAddr] using hst
  have hsa : (s₀.sp + BitVec.ofNat 64 64).toNat % 8 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  have hv : s₀.mem.readW (s₀.sp + BitVec.ofNat 64 64) 64 = S := by
    rw [← hS]; rfl
  have first : WP isa (.block [.addSp .t0 64, .load .d .t0 .t0 0]) s₀ fun s₁ => s₁ = s₀.write .t0 S := by
    brun [exec_addSp (show 64 < 2048 by decide), add_ofNat_zero, hst', hsa, hv, write_write]
  refine WP.block_append (WP.mono first ?_)
  · rintro s₁ rfl
    have h0 : (s₀.write .t0 S).gpr .t0 = S := gpr_write_self _ _ _
    refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI (s₀.write .t0 S))
      (fun k s hk h => save_step (s₀.write .t0 S) (by rw [h0]; exact hin) (by rw [h0]; exact hal) hk h)
      13 (Nat.le_refl _) (s₀.write .t0 S)
      ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s h => ?_)
    have hf := h.frame
    have hsv := h.saved
    rw [h0] at hf hsv
    have hw : s.gpr .t0 = S := by rw [h.gpr, h0]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 0 by decide),
      BitVec.ofInt_ofNat, add_ofNat_zero, Option.some.injEq, exists_eq_left', hw]
    have k1 : Keep [.t0] s₀ (s₀.write .t0 S) := Keep.write _ _ _
    refine ⟨⟨fun r hr => ?_, h.rd, h.wr⟩, h.sp, gpr_write_self _ _ _, ?_, hf, fun i hi => ?_⟩
    · have hr6 : r ≠ .s6 := fun e => hr (by simp [e])
      have hr0 : r ∉ [Reg.t0] := fun e => hr (by simp_all)
      rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e hr6, h.gpr, k1.gpr hr0]
    · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (by decide), hw]
    · rw [mem_write, hsv i hi, gpr_write, ite_eq_right_iff.mpr fun e => absurd e (saved_ne_t0 i hi)]

/-- The first `n` registers are restored to `v`, from the state `sB` the
restoring starts in. -/
structure RI (sB : State) (S : Addr) (v : Nat → BitVec 64) (n : Nat) (s : State) : Prop where
  s6 : s.gpr .s6 = S
  restored : ∀ i < n, s.gpr (saved i) = v i
  others : ∀ r, (∀ i < 13, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp

theorem restore_step (sB : State) {S : Addr} {v : Nat → BitVec 64}
    (hsin : ∀ i < 13, InRegions sB.wr (Mont.off (savW S) (8 * i)) 8)
    (hal : ∀ i < 13, (Mont.off (savW S) (8 * i)).toNat % 8 = 0)
    (hsav : ∀ i < 13, sB.mem.readW (Mont.off (savW S) (8 * i)) 64 = v i)
    {n : Nat} (hn : n < 12) {s : State} (h : RI sB S v n s) :
    WP isa (.block [.load .d (saved n) .s6 (savOff n)]) s (RI sB S v (n + 1)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .s6 + BitVec.ofNat 64 (savOff n)) 8 := by
    rw [h.rd, h.wr, h.s6, savOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin n (by omega_using [hn])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have ha : (s.gpr .s6 + BitVec.ofNat 64 (savOff n)).toNat % 8 = 0 := by
    rw [h.s6, savOff_eq]; exact hal n (by omega_using [hn])
  have hv : s.mem.readW (S + BitVec.ofNat 64 (savOff n)) 64 = v n := by
    rw [h.mem, savOff_eq]; exact hsav n (by omega_using [hn])
  have hn6 := saved_ne n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show savOff n < 2048 by unfold savOff; omega_using [hn]) ha hin,
    Option.some.injEq, exists_eq_left', h.s6, hv]
  refine ⟨?_, fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (Ne.symm hn6)]; exact h.s6
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : saved i ≠ saved n := fun e =>
        absurd (saved_inj i (by omega_using [hi, hn]) n (by omega_using [hn]) e) (by omega_using [hi])
      rw [ite_eq_right_iff.mpr fun e' => absurd e' e]; exact h.restored i hi
    · rw [ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (hr n (by omega_using [hn]))]
    exact h.others r hr

/-- `restore`, from a state whose saved words, through `s6`, hold `v`. -/
theorem restore_ok (sB : State) {S : Addr} {v : Nat → BitVec 64} (hw : sB.gpr .s6 = S)
    (hsin : ∀ i < 13, InRegions sB.wr (Mont.off (savW S) (8 * i)) 8)
    (hal : ∀ i < 13, (Mont.off (savW S) (8 * i)).toNat % 8 = 0)
    (hsav : ∀ i < 13, sB.mem.readW (Mont.off (savW S) (8 * i)) 64 = v i) :
    WP isa (.block restore) sB fun s =>
      (∀ i < 13, s.gpr (saved i) = v i) ∧ (∀ r, (∀ i < 13, r ≠ saved i) → s.gpr r = sB.gpr r) ∧
      s.mem = sB.mem ∧ s.rd = sB.rd ∧ s.wr = sB.wr ∧ s.sp = sB.sp := by
  rw [restore]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (RI sB S v)
    (fun k s hk h => restore_step sB hsin hal hsav hk h) 12 (Nat.le_refl _) sB
    ⟨hw, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩) fun s h => ?_)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .s6 + BitVec.ofNat 64 (savOff 12)) 8 := by
    rw [h.rd, h.wr, h.s6, savOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin 12 (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have ha : (s.gpr .s6 + BitVec.ofNat 64 (savOff 12)).toNat % 8 = 0 := by
    rw [h.s6, savOff_eq]; exact hal 12 (by decide)
  have hv : s.mem.readW (S + BitVec.ofNat 64 (savOff 12)) 64 = v 12 := by
    rw [h.mem, savOff_eq]; exact hsav 12 (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show savOff 12 < 2048 by decide) ha hin,
    Option.some.injEq, exists_eq_left', h.s6, hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp⟩
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_iff.mpr fun e => absurd e (saved_ne i hi)]; exact h.restored i hi
    · rw [saved_12, ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (saved_12 ▸ hr 12 (by decide))]
    exact h.others r hr

/-! ## The arguments -/

/-- A Mont.word of the header after a write to another of its words. -/
theorem hdr_rw (m : Mem) (S : Addr) {d d' : Nat} (v : BitVec 64) (h : d' + 8 ≤ d ∨ d + 8 ≤ d')
    (hd : d < 256) (hd' : d' < 256) : (m.writeW (Mont.off S d) v).readW (Mont.off S d') 64 = m.readW (Mont.off S d') 64 :=
  Mem.readW_writeW_sep (Offset.sep S h (by omega_arith) (by omega_arith)) (by decide)

theorem out_wr (S : Addr) {m m' : Mem} (h : Mont.Outside S 0 88 m m') {d : Nat} (hd : d + 8 ≤ 88) (v : BitVec 64) :
    Mont.Outside S 0 88 m (m'.writeW (Mont.off S d) v) :=
  h.trans ((Mont.writeW_outside m' S v (by omega_arith)).mono (by omega_arith) (by omega_arith))

/-- The header's words that `args` writes: the arguments the code reads
again. -/
structure ArgsHdr (m : Mem) (S : Addr) (s : State) : Prop where
  out : Mont.word m S oOut = s.gpr .a0
  n : Mont.word m S oN = s.gpr .a2
  nLen : Mont.word m S oNLen = s.gpr .a3
  inp : Mont.word m S oIn = s.gpr .a4
  p : Mont.word m S oP = s.gpr .a6
  pLen : Mont.word m S oPLen = s.gpr .a7
  q : Mont.word m S oQ = stackArg s 0
  qLen : Mont.word m S oQLen = stackArg s 1
  dp : Mont.word m S oDP = stackArg s 2
  dq : Mont.word m S oDQ = stackArg s 4
  qinv : Mont.word m S oQInv = stackArg s 6

/-- `args`: the arguments into the header's words 0–10, the working space at
`s6` (writable, aligned), the stack arguments readable and apart from the
header's first 88 bytes. -/
theorem args_ok {s : State} {S : Addr} {Z : Nat} (hs : Scr s S Z) (hZ : 88 ≤ Z)
    (h6 : s.gpr .s6 = Mont.off S 0) (hsp : s.sp.toNat % 8 = 0)
    (hstk : ∀ j < 7, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 56, ∀ d < 88, Mem.Sep (s.sp + BitVec.ofNat 64 j) 8 (Mont.off S d) 8) :
    WP isa (.block args) s fun t =>
      (ArgsHdr t.mem S s ∧ Mont.Outside S 0 88 s.mem t.mem) ∧ Keep [.t2, .t3] s t := by
  have hnw := hs.nowrap
  have st : ∀ d, d + 8 ≤ 88 → d % 8 = 0 → InRegions s.wr (Mont.off S d) 8 ∧ (Mont.off S d).toNat % 8 = 0 :=
    fun d h1 h2 => ⟨hs.st (by omega_arith), hs.al8 (by omega_arith) h2⟩
  have ld : ∀ j < 7, InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * j)) 8 ∧
      (s.sp + BitVec.ofNat 64 (8 * j)).toNat % 8 = 0 := fun j hj =>
    ⟨hstk j hj, by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith⟩
  have sp0 : ∀ j, s.sp + BitVec.ofNat 64 0 + BitVec.ofNat 64 j = s.sp + BitVec.ofNat 64 j := fun j => by
    rw [add_ofNat_zero]
  have stk : ∀ (m : Mem) (v : BitVec 64) {j d : Nat}, j < 56 → d < 88 →
      (m.writeW (Mont.off S d) v).readW (s.sp + BitVec.ofNat 64 j) 64 = m.readW (s.sp + BitVec.ofNat 64 j) 64 :=
    fun m v j d hj hd => Mem.readW_writeW_sep (hsep j hj d hd) (by decide)
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold args
  brun [h6, oOut, oN, oNLen, oIn, oP, oPLen, oQ, oQLen, oDP, oDQ, oQInv, exec_addSp (show 0 < 2048 by decide),
    sp0, (st 0 (by decide) (by decide)).1, (st 0 (by decide) (by decide)).2,
    (st 8 (by decide) (by decide)).1, (st 8 (by decide) (by decide)).2,
    (st 16 (by decide) (by decide)).1, (st 16 (by decide) (by decide)).2,
    (st 24 (by decide) (by decide)).1, (st 24 (by decide) (by decide)).2,
    (st 32 (by decide) (by decide)).1, (st 32 (by decide) (by decide)).2,
    (st 40 (by decide) (by decide)).1, (st 40 (by decide) (by decide)).2,
    (st 48 (by decide) (by decide)).1, (st 48 (by decide) (by decide)).2,
    (st 56 (by decide) (by decide)).1, (st 56 (by decide) (by decide)).2,
    (st 64 (by decide) (by decide)).1, (st 64 (by decide) (by decide)).2,
    (st 72 (by decide) (by decide)).1, (st 72 (by decide) (by decide)).2,
    (st 80 (by decide) (by decide)).1, (st 80 (by decide) (by decide)).2,
    (ld 0 (by decide)).1, (ld 0 (by decide)).2, (ld 1 (by decide)).1, (ld 1 (by decide)).2, (ld 2 (by decide)).1,
    (ld 2 (by decide)).2, (ld 4 (by decide)).1, (ld 4 (by decide)).2, (ld 6 (by decide)).1, (ld 6 (by decide)).2]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals (try simp (disch := omega_arith) only [Mont.word, oOut, oN, oNLen, oIn, oP, oPLen, oQ, oQLen, oDP, oDQ,
    oQInv, hdr_rw, Mem.readW_writeW_self64, stk, stackArg, stackArgAddr, Nat.reduceMul])
  iterate 11 refine out_wr S ?_ (by decide) _
  exact Mont.Outside.refl _ _ _ _

/-! ## The working spaces' registers -/

theorem ofNat_shr3 (x : Nat) (h : x < 2 ^ 64) : BitVec.ofNat 64 x >>> 3 = BitVec.ofNat 64 (x / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

theorem ofNat_shl (a k : Nat) (_hk : k < 64) : BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (2 ^ k * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_mul_mod, Nat.mul_comm]

/-- The words of a prime's working space, for a length of `l` bytes:
`max(2, ⌈l / 8⌉)`. -/
def wordsOf (l : Nat) : Nat := if (l + 7) / 8 < 2 then 2 else (l + 7) / 8

theorem words_val {x : Nat} (h1 : 1 ≤ x) (h : x < 2 ^ 62) :
    BitVec.ofNat 64 x + (BitVec.ofNat 64 x - BitVec.ofNat 64 2) >>> 63 =
      BitVec.ofNat 64 (if x < 2 then 2 else x) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  split <;> omega_arith

theorem wordsOf_bounds {l : Nat} (h1 : 1 ≤ l) (h : l ≤ 1024) : 2 ≤ wordsOf l ∧ wordsOf l ≤ 128 := by
  unfold wordsOf; split <;> omega_arith

/-- `setupX`: `X`'s registers, `W = 2 ⌈k / 8⌉` words, and the bases of `P`
(after `X`'s eight arrays) and `Q` (after `P`'s header and 24 arrays of
`wordsOf p_len` words) into the header. -/
theorem setupX_ok {s : State} {S : Addr} {Z k pl : Nat} (hs : Scr s S Z) (hZ : 112 ≤ Z)
    (h6 : s.gpr .s6 = Mont.off S 0) (h3 : s.gpr .a3 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k ≤ 1024)
    (hpl : Mont.word s.mem S oPLen = BitVec.ofNat 64 pl) (hpl1 : 1 ≤ pl) (hpl' : pl ≤ 1024) :
    WP isa (.block setupX) s fun t =>
      (t.gpr .a7 = Mont.off S (slot (2 * ((k + 7) / 8)) 0) ∧ t.gpr .ra = Mont.off S (slot (2 * ((k + 7) / 8)) 0) ∧
        t.gpr .s5 = BitVec.ofNat 64 (8 * (2 * ((k + 7) / 8) + 2)) ∧
        t.gpr .s11 = BitVec.ofNat 64 (8 * (2 * ((k + 7) / 8) + 2)) ∧
        t.gpr .t0 = BitVec.ofNat 64 (2 * ((k + 7) / 8)) ∧
        Mont.word t.mem S oBP = Mont.off S (slot (2 * ((k + 7) / 8)) 8) ∧
        Mont.word t.mem S oBQ = Mont.off S (slot (2 * ((k + 7) / 8)) 8 + hdrBytes + 24 * (8 * (wordsOf pl + 2))) ∧
        Mont.Outside S oBP 16 s.mem t.mem) ∧
      Keep [.t2, .t3, .t4, .t5, .a7, .ra, .s5, .s11, .t0] s t := by
  have hnw := hs.nowrap
  have hpl8 : Mont.word s.mem S 40 = BitVec.ofNat 64 pl := hpl
  have wv := words_val (x := (pl + 7) / 8) (by omega_arith) (by omega_arith)
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold setupX area words
  brun [h6, h3, hdrBytes, oBP, oBQ, oPLen, BitVec.ofNat_add_ofNat, ofNat_shr3 (k + 7) (by omega_arith),
    ofNat_shr3 (pl + 7) (by omega_arith), ofNat_shl _ _ (show 1 < 64 by decide),
    ofNat_shl _ _ (show 3 < 64 by decide), Nat.reducePow, hs.st (show 96 + 8 ≤ Z by omega_arith),
    hs.al8 (show 96 + 8 ≤ Z by omega_arith) (by decide), hs.st (show 104 + 8 ≤ Z by omega_arith),
    hs.al8 (show 104 + 8 ≤ Z by omega_arith) (by decide), hs.ld (show 40 + 8 ≤ Z by omega_arith),
    hs.al8 (show 40 + 8 ≤ Z by omega_arith) (by decide), Mont.word_writeW_self, hdr_rw (d := 96) (d' := 40) s.mem S _ (Or.inl (by decide)) (by decide) (by decide),
    hpl8, wv]
  refine ⟨by simp [slot, hdrBytes], by simp [slot, hdrBytes], congrArg _ (by omega_arith),
    congrArg _ (by omega_arith), ?_, ?_, ?_⟩
  · rw [Mont.word, hdr_rw (d := 104) (d' := 96) _ S _ (Or.inl (by decide)) (by decide) (by decide),
      Mem.readW_writeW_self64]
    exact congrArg _ (by unfold slot hdrBytes; omega_arith)
  · exact congrArg _ (by unfold wordsOf slot hdrBytes; split <;> omega_arith)
  · exact ((Mont.writeW_outside _ S _ (by omega_arith)).mono (by decide) (by decide)).trans
      ((Mont.writeW_outside _ S _ (by omega_arith)).mono (by decide) (by decide))

/-- `setupP oB oLen`: a prime's working space at `Bp` (the header's Mont.word
`oB`), of `wordsOf l` words for its length `l` (the header's Mont.word `oLen`):
its array 0 in `a7` and `ra`, the arrays' size in `s5` and the words in `t0`
(and `t2`). -/
theorem setupP_ok {s : State} {S Bp : Addr} {Z l oB oLen : Nat} (hs : Scr s S Z) (h6 : s.gpr .s6 = Mont.off S 0)
    (hB : oB + 8 ≤ Z) (hB8 : oB % 8 = 0) (hB' : oB < 2048) (hL : oLen + 8 ≤ Z) (hL8 : oLen % 8 = 0)
    (hL' : oLen < 2048) (hbase : Mont.word s.mem S oB = Bp) (hlen : Mont.word s.mem S oLen = BitVec.ofNat 64 l)
    (hl1 : 1 ≤ l) (hl' : l ≤ 1024) :
    WP isa (.block (setupP oB oLen)) s fun t =>
      (t.gpr .a7 = Mont.off Bp (slot (wordsOf l) 0) ∧ t.gpr .ra = Mont.off Bp (slot (wordsOf l) 0) ∧
        t.gpr .s5 = BitVec.ofNat 64 (8 * (wordsOf l + 2)) ∧ t.gpr .t0 = BitVec.ofNat 64 (wordsOf l) ∧
        t.gpr .t2 = BitVec.ofNat 64 (wordsOf l) ∧ t.mem = s.mem) ∧
      Keep [.t2, .t3, .t4, .a7, .ra, .s5, .t0] s t := by
  have wv := words_val (x := (l + 7) / 8) (by omega_arith) (by omega_arith)
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold setupP area words
  brun [h6, hdrBytes, BitVec.ofNat_add_ofNat, ofNat_shr3 (l + 7) (by omega_arith),
    ofNat_shl _ _ (show 3 < 64 by decide), Nat.reducePow, hs.ld hB, hs.al8 hB hB8, hs.ld hL, hs.al8 hL hL8,
    hB', hL', hbase, hlen, wv, Nat.zero_add]
  have e0 : slot (wordsOf l) 0 = 256 := by simp [slot, hdrBytes]
  refine ⟨by rw [e0], by rw [e0], congrArg _ ?_, rfl⟩
  unfold wordsOf; split <;> omega_arith

end VG.Proof.Bignum.RISCV64.Crt
