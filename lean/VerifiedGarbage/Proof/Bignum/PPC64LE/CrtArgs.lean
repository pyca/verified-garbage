module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Bignum.PPC64LE.CrtSave`, which the modules that import this one used -/

section

/-!
# The RSA private-key operation on PPC64LE: saving and restoring

`save` loads the working space's address from the stack (its ninth argument
there) into `r11`, stores the 18 nonvolatile registers it uses from byte 112
of its header and copies its address into `r23` (`save_ok`); `restore` loads
them back through `r23`, `r23` last (`restore_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE.Crt

/-- The saved registers' words, 144 bytes. -/
abbrev savR (w : Addr) : Region := ⟨w, 144⟩

theorem saved_inj : ∀ i < 18, ∀ j < 18, saved i = saved j → i = j := by decide

theorem saved_ne : ∀ i < 17, saved i ≠ .r23 := by decide

theorem saved_17 : saved 17 = .r23 := rfl

theorem sav_contains (w : Addr) {i : Nat} (hi : i < 18) : (savR w).Contains (off w (8 * i)) 8 :=
  Offset.contains_base w (by omega_using [hi]) (by omega_using [hi])

theorem sav_sep (w : Addr) {i j : Nat} (hi : i < 18) (hj : j < 18) (h : i ≠ j) :
    Mem.Sep (off w (8 * i)) 8 (off w (8 * j)) 8 :=
  Offset.sep w (by omega_using [hi, hj, h]) (by omega_using [hi]) (by omega_using [hj])

/-- The saved registers' words of the working space at `S`. -/
abbrev savW (S : Addr) : Addr := S + BitVec.ofNat 64 112

theorem saveOff_eq (S : Addr) (i : Nat) : S + BitVec.ofNat 64 (112 + 8 * i) = off (savW S) (8 * i) := by
  rw [off, Offset.add_add]

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  frame : Frame [savR (savW (s₀.gpr .r11))] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (off (savW (s₀.gpr .r11)) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_step (s₀ : State) (hin : ∀ i < 18, InRegions s₀.wr (off (savW (s₀.gpr .r11)) (8 * i)) 8)
    {n : Nat} (hn : n < 18) {s : State}
    (h : SI s₀ n s) : WP isa (.block [.store .d (saved n) .r11 (savOff n)]) s (SI s₀ (n + 1)) := by
  simp only [savOff]
  have hw : s.gpr .r11 = s₀.gpr .r11 := by rw [h.gpr]
  have hout : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 ((112 + 8 * n))) 8 := by
    rw [h.wr, hw, saveOff_eq]; exact hin n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show Reg.r11 ≠ .r0 by decide) (show 112 + 8 * n < 2 ^ 15 ∧ (112 + 8 * n) % 4 = 0 by
      omega_using [hn]) hout, Option.some.injEq, exists_eq_left', hw, saveOff_eq]
  refine ⟨h.gpr, h.rd, h.wr, h.sp, h.lr,
    h.frame.writeW (List.mem_singleton_self _) _ (sav_contains _ hn), fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [Mem.readW_writeW_sep (sav_sep _ (by omega_using [hi, hn]) hn (by omega_using [hi])) (by decide)]
    exact h.saved i hi
  · rw [Mem.readW_writeW_self64, h.gpr]

/-- The state after `save`. -/
structure Saved (s₀ : State) (s : State) : Prop where
  keep : Keep [.r23] s₀ s
  r23 : s.gpr .r23 = s₀.gpr .r11
  frame : Frame [savR (savW (s₀.gpr .r11))] s₀.mem s.mem
  saved : ∀ i < 18, s.mem.readW (off (savW (s₀.gpr .r11)) (8 * i)) 64 = s₀.gpr (saved i)

theorem saveRegs_ok (s₀ : State) (hin : ∀ i < 18, InRegions s₀.wr (off (savW (s₀.gpr .r11)) (8 * i)) 8) :
    WP isa (.block ((List.range 18).flatMap (fun i => [.store .d (saved i) .r11 (savOff i)]) ++
      ([.addi .r23 .r11 0] : List Instr))) s₀ (Saved s₀) := by
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI s₀)
    (fun k s hk h => save_step s₀ hin hk h) 18 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s h => ?_)
  have hw : s.gpr .r11 = s₀.gpr .r11 := by rw [h.gpr]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi (show Reg.r11 ≠ .r0 by decide)
    (show 0 < 2 ^ 15 by decide), BitVec.add_zero, Option.some.injEq, exists_eq_left', hw]
  refine ⟨⟨fun r hr => ?_, h.rd, h.wr, h.sp, h.lr⟩, ?_, h.frame, h.saved⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e fun e => hr (by simp [e]), h.gpr]
  · rw [gpr_write, ite_eq_left_iff.mpr fun e => absurd rfl e]

/-- The first `n` registers are restored to `v`, from the state `sB` the
restoring starts in. -/
structure RI (sB : State) (S : Addr) (v : Nat → BitVec 64) (n : Nat) (s : State) : Prop where
  r23 : s.gpr .r23 = S
  restored : ∀ i < n, s.gpr (saved i) = v i
  others : ∀ r, (∀ i < 18, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp
  lr : s.lr = sB.lr

theorem restore_step (sB : State) {S : Addr} {v : Nat → BitVec 64}
    (hsin : ∀ i < 18, InRegions sB.wr (off (savW S) (8 * i)) 8)
    (hsav : ∀ i < 18, sB.mem.readW (off (savW S) (8 * i)) 64 = v i)
    {n : Nat} (hn : n < 17) {s : State} (h : RI sB S v n s) :
    WP isa (.block [.load .d (saved n) .r23 (savOff n)]) s (RI sB S v (n + 1)) := by
  simp only [savOff]
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 ((112 + 8 * n))) 8 := by
    rw [h.rd, h.wr, h.r23, saveOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin n (by omega_using [hn])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hv : s.mem.readW (S + BitVec.ofNat 64 ((112 + 8 * n))) 64 = v n := by
    rw [h.mem, saveOff_eq]; exact hsav n (by omega_using [hn])
  have hn23 := saved_ne n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r23 ≠ .r0 by decide) (show 112 + 8 * n < 2 ^ 15 ∧ (112 + 8 * n) % 4 = 0 by
      omega_using [hn]) hin, Option.some.injEq, exists_eq_left', h.r23, hv]
  refine ⟨?_, fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp, h.lr⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (Ne.symm hn23)]; exact h.r23
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : saved i ≠ saved n := fun e =>
        absurd (saved_inj i (by omega_using [hi, hn]) n (by omega_using [hn]) e) (by omega_using [hi])
      rw [ite_eq_right_iff.mpr fun e' => absurd e' e]; exact h.restored i hi
    · rw [ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (hr n (by omega_using [hn]))]
    exact h.others r hr

/-- `restore`, from a state whose saved words, through `r21`, hold `v`. -/
theorem restore_ok (sB : State) {S : Addr} {v : Nat → BitVec 64} (hw : sB.gpr .r23 = S)
    (hsin : ∀ i < 18, InRegions sB.wr (off (savW S) (8 * i)) 8)
    (hsav : ∀ i < 18, sB.mem.readW (off (savW S) (8 * i)) 64 = v i) :
    WP isa (.block VG.Impl.Bignum.PPC64LE.Crt.restore) sB fun s =>
      (∀ i < 18, s.gpr (saved i) = v i) ∧ (∀ r, (∀ i < 18, r ≠ saved i) → s.gpr r = sB.gpr r) ∧
      s.mem = sB.mem ∧ s.rd = sB.rd ∧ s.wr = sB.wr ∧ s.sp = sB.sp ∧ s.lr = sB.lr := by
  rw [VG.Impl.Bignum.PPC64LE.Crt.restore, show savOff 17 = 112 + 8 * 17 from rfl]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (RI sB S v)
    (fun k s hk h => restore_step sB hsin hsav hk h) 17 (Nat.le_refl _) sB
    ⟨hw, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩) fun s h => ?_)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 ((112 + 8 * 17))) 8 := by
    rw [h.rd, h.wr, h.r23, saveOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin 17 (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hv : s.mem.readW (S + BitVec.ofNat 64 ((112 + 8 * 17))) 64 = v 17 := by
    rw [h.mem, saveOff_eq]; exact hsav 17 (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r23 ≠ .r0 by decide) (show 112 + 8 * 17 < 2 ^ 15 ∧ (112 + 8 * 17) % 4 = 0 by decide) hin,
    Option.some.injEq, exists_eq_left', h.r23, hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp, h.lr⟩
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_iff.mpr fun e => absurd e (saved_ne i hi)]; exact h.restored i hi
    · rw [saved_17, ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (saved_17 ▸ hr 17 (by decide))]
    exact h.others r hr

/-- The ninth argument on the stack into `r11`. -/
theorem loadS_ok (s : State) (h : InRegions (s.rd ++ s.wr) (stackArgAddr s 8) 8) :
    WP isa (.block [.addSp .r11 160, .load .d .r11 .r11 0]) s fun t =>
      (t.gpr .r11 = stackArg s 8 ∧ t.mem = s.mem ∧ t.sp = s.sp) ∧ Keep [.r11] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [stackArgAddr, Nat.reduceMul, Nat.reduceAdd] at h
  have ea : exec (.addSp .r11 160) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 160)) := by
    simp [exec]
  prun [ea, h, BitVec.add_zero]
  rfl

/-- `save`: the working space from the stack, the registers saved there. -/
theorem save_ok (s₀ : State) (h : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 8) 8)
    (hin : ∀ i < 18, InRegions s₀.wr (off (savW (stackArg s₀ 8)) (8 * i)) 8) :
    WP isa (.block save) s₀ fun t => ∃ s₁ : State, s₁.gpr .r11 = stackArg s₀ 8 ∧ s₁.mem = s₀.mem ∧
      Keep [.r11] s₀ s₁ ∧ Saved s₁ t := by
  rw [save, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadS_ok s₀ h) fun s₁ ⟨⟨a11, m1, _⟩, k1⟩ => ?_
  refine WP.mono (saveRegs_ok s₁ (fun i hi => by rw [k1.wr, a11]; exact hin i hi)) fun t ht =>
    ⟨s₁, a11, m1, k1, ht⟩

end VG.Proof.Bignum.PPC64LE.Crt

end

end

/-!
# The RSA private-key operation on PPC64LE: the arguments

`args_ok`: the arguments, from the registers and the stack, into the
header's words 0–10.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- A store of `r` into the header's word at `o` (`r23`). -/
theorem st1_ok {s : State} {S : Addr} {Z o : Nat} {r : Reg} (hs : Scr s S Z) (h23 : s.gpr .r23 = S)
    (ho : o + 8 ≤ Z) (ho' : o < 2 ^ 15 ∧ o % 4 = 0) :
    WP isa (.block [.store .d r .r23 o]) s fun t =>
      (word t.mem S o = s.gpr r ∧ Outside S o 8 s.mem t.mem) ∧ Keep [] s t := by
  have hn := hs.nowrap
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show Reg.r23 ≠ .r0 by decide) ho' (by rw [h23]; exact hs.st ho), Option.some.injEq,
    exists_eq_left', h23]
  refine ⟨⟨Mem.readW_writeW_self64 _ _ _, writeW_outside s.mem S _ (by omega_arith)⟩,
    ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩

/-- A word apart from the working space, after a change within it. -/
theorem readW_out {S a : Addr} {Z o n : Nat} {m m' : Mem} (h : Outside S o n m m') (hn : o + n ≤ Z)
    (hsep : ∀ i < 8, ∀ x, ofs S x < Z → a + BitVec.ofNat 64 i ≠ x) : m'.readW a 64 = m.readW a 64 :=
  Mem.readW_congr fun i hi => h _ (by
    by_contra hc
    exact hsep i (by omega_arith) (a + BitVec.ofNat 64 i) (by omega_arith) rfl)

/-- A word of the stack into the header's word at `o`, through `r0`. -/
theorem ld1_ok {s : State} {S A : Addr} {Z o a : Nat} (hs : Scr s S Z) (h23 : s.gpr .r23 = S)
    (h11 : s.gpr .r11 = A) (ho : o + 8 ≤ Z) (ho' : o < 2 ^ 15 ∧ o % 4 = 0) (ha : a < 2 ^ 15 ∧ a % 4 = 0)
    (hrd : InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 a) 8) :
    WP isa (.block [.load .d .r0 .r11 a, .store .d .r0 .r23 o]) s fun t =>
      (word t.mem S o = s.mem.readW (A + BitVec.ofNat 64 a) 64 ∧ Outside S o 8 s.mem t.mem) ∧
        Keep [.r0] s t := by
  rw [show ([.load .d .r0 .r11 a, .store .d .r0 .r23 o] : List Instr) =
    [.load .d .r0 .r11 a] ++ [.store .d .r0 .r23 o] from rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.r0] (Q := fun t => t.gpr .r0 = s.mem.readW (A + BitVec.ofNat 64 a) 64 ∧
    t.mem = s.mem) (by prun [h11, exec_load_d (show Reg.r11 ≠ .r0 by decide) ha, hrd]) rfl)
    fun s₁ ⟨⟨a0, m1⟩, k1⟩ => ?_
  refine WP.mono (st1_ok (r := .r0) (hs.congr k1.wr) ((k1.gpr _ (by decide)).trans h23) ho ho')
    fun t ⟨⟨tw, to⟩, k2⟩ => ⟨⟨tw.trans a0, by rw [← m1]; exact to⟩, (k1.trans k2).mono⟩

theorem sp96 (s : State) (i : Nat) :
    s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 (8 * i) = stackArgAddr s i := by
  rw [stackArgAddr, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_arith

/-- `args`, after `save` (the working space at `S` in `r23`): the arguments
into the header. -/
theorem args_ok {s : State} {S : Addr} {Z : Nat} (hs : Scr s S Z) (hZ : 256 ≤ Z) (h23 : s.gpr .r23 = S)
    (hrd : ∀ i < 10, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8)
    (hsep : ∀ j < 10, ∀ i < 8, ∀ x, ofs S x < Z → stackArgAddr s j + BitVec.ofNat 64 i ≠ x) :
    WP isa (.block Crt.args) s fun t =>
      (word t.mem S oOut = s.gpr .r3 ∧ word t.mem S oN = s.gpr .r5 ∧ word t.mem S oNLen = s.gpr .r6 ∧
        word t.mem S oIn = s.gpr .r7 ∧ word t.mem S oP = s.gpr .r9 ∧ word t.mem S oPLen = s.gpr .r10 ∧
        word t.mem S oQ = stackArg s 0 ∧ word t.mem S oQLen = stackArg s 1 ∧ word t.mem S oDP = stackArg s 2 ∧
        word t.mem S oDQ = stackArg s 4 ∧ word t.mem S oQInv = stackArg s 6 ∧ Outside S 0 88 s.mem t.mem) ∧
      Keep [.r0, .r11] s t := by
  have hn := hs.nowrap
  rw [show Crt.args = [.store .d .r3 .r23 0] ++ ([.store .d .r5 .r23 8] ++ ([.store .d .r6 .r23 16] ++
    ([.store .d .r7 .r23 24] ++ ([.store .d .r9 .r23 32] ++ ([.store .d .r10 .r23 40] ++ ([.addSp .r11 96] ++
    ([.load .d .r0 .r11 0, .store .d .r0 .r23 48] ++ ([.load .d .r0 .r11 8, .store .d .r0 .r23 56] ++
    ([.load .d .r0 .r11 16, .store .d .r0 .r23 64] ++ ([.load .d .r0 .r11 32, .store .d .r0 .r23 72] ++
    [.load .d .r0 .r11 48, .store .d .r0 .r23 80])))))))))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (st1_ok (r := .r3) hs h23 (by omega_arith) (by decide)) fun s₁ ⟨⟨w1, F1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (st1_ok (r := .r5) (hs.congr k1.wr) ((k1.gpr _ (by decide)).trans h23) (by omega_arith) (by decide))
    fun s₂ ⟨⟨w2, F2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (st1_ok (r := .r6) (hs.congr k12.wr) ((k12.gpr _ (by decide)).trans h23) (by omega_arith) (by decide))
    fun s₃ ⟨⟨w3, F3⟩, k3⟩ => ?_
  obtain k13 := k12.trans k3
  rw [WP.block_append_iff]
  refine WP.mono (st1_ok (r := .r7) (hs.congr k13.wr) ((k13.gpr _ (by decide)).trans h23) (by omega_arith) (by decide))
    fun s₄ ⟨⟨w4, F4⟩, k4⟩ => ?_
  obtain k14 := k13.trans k4
  rw [WP.block_append_iff]
  refine WP.mono (st1_ok (r := .r9) (hs.congr k14.wr) ((k14.gpr _ (by decide)).trans h23) (by omega_arith) (by decide))
    fun s₅ ⟨⟨w5, F5⟩, k5⟩ => ?_
  obtain k15 := k14.trans k5
  rw [WP.block_append_iff]
  refine WP.mono (st1_ok (r := .r10) (hs.congr k15.wr) ((k15.gpr _ (by decide)).trans h23) (by omega_arith)
    (by decide)) fun s₆ ⟨⟨w6, F6⟩, k6⟩ => ?_
  obtain k16 := k15.trans k6
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = s.sp + BitVec.ofNat 64 96 ∧ t.mem = s₆.mem)
    (by
      obtain ea : exec (.addSp .r11 96) s₆ = some (s₆.write .r11 (s₆.sp + BitVec.ofNat 64 96)) := by simp [exec]
      prun [ea, k16.sp]) (by decide)) fun s₇ ⟨⟨a11, m7⟩, k7⟩ => ?_
  obtain k17 := k16.trans k7
  obtain O7 : Outside S 0 88 s.mem s₇.mem := by
    rw [m7]
    exact ((((F1.mono (by omega_arith) (by omega_arith)).trans (F2.mono (by omega_arith) (by omega_arith))).trans
      (F3.mono (by omega_arith) (by omega_arith))).trans ((F4.mono (by omega_arith) (by omega_arith)).trans
      (F5.mono (by omega_arith) (by omega_arith)))).trans (F6.mono (by omega_arith) (by omega_arith))
  obtain st : ∀ {u : State} (i : Nat), i < 10 → Outside S 0 88 s.mem u.mem → u.rd = s.rd → u.wr = s.wr →
      InRegions (u.rd ++ u.wr) (s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 (8 * i)) 8 ∧
      u.mem.readW (s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 (8 * i)) 64 = stackArg s i :=
    fun i hi O hr hw => by
      rw [sp96, hr, hw]
      exact ⟨hrd i hi, readW_out O (by omega_arith) (hsep i hi)⟩
  rw [WP.block_append_iff]
  obtain g7 := st (u := s₇) 0 (by decide) O7 k17.rd k17.wr
  refine WP.mono (ld1_ok (o := 48) (a := 0) (hs.congr k17.wr) ((k17.gpr _ (by decide)).trans h23) a11 (by omega_arith)
    (by decide) (by decide) g7.1) fun s₈ ⟨⟨w8, F8⟩, k8⟩ => ?_
  obtain k18 := k17.trans k8
  obtain O8 := O7.trans (F8.mono (by omega_arith) (by omega_arith))
  rw [WP.block_append_iff]
  obtain g8 := st (u := s₈) 1 (by decide) O8 k18.rd k18.wr
  refine WP.mono (ld1_ok (o := 56) (a := 8) (hs.congr k18.wr) ((k18.gpr _ (by decide)).trans h23)
    ((k8.gpr _ (by decide)).trans a11) (by omega_arith) (by decide) (by decide) g8.1) fun s₉ ⟨⟨w9, F9⟩, k9⟩ => ?_
  obtain k19 := k18.trans k9
  obtain O9 := O8.trans (F9.mono (by omega_arith) (by omega_arith))
  rw [WP.block_append_iff]
  obtain g9 := st (u := s₉) 2 (by decide) O9 k19.rd k19.wr
  refine WP.mono (ld1_ok (o := 64) (a := 16) (hs.congr k19.wr) ((k19.gpr _ (by decide)).trans h23)
    ((k9.gpr _ (by decide)).trans ((k8.gpr _ (by decide)).trans a11)) (by omega_arith) (by decide) (by decide) g9.1)
    fun s₁₀ ⟨⟨w10, F10⟩, k10⟩ => ?_
  obtain k110 := k19.trans k10
  obtain O10 := O9.trans (F10.mono (by omega_arith) (by omega_arith))
  rw [WP.block_append_iff]
  obtain g10 := st (u := s₁₀) 4 (by decide) O10 k110.rd k110.wr
  refine WP.mono (ld1_ok (o := 72) (a := 32) (hs.congr k110.wr) ((k110.gpr _ (by decide)).trans h23)
    ((((k8.trans k9).trans k10).gpr _ (by decide)).trans a11) (by omega_arith) (by decide) (by decide) g10.1)
    fun s₁₁ ⟨⟨w11, F11⟩, k11⟩ => ?_
  obtain k111 := k110.trans k11
  obtain O11 := O10.trans (F11.mono (by omega_arith) (by omega_arith))
  obtain g11 := st (u := s₁₁) 6 (by decide) O11 k111.rd k111.wr
  refine WP.mono (ld1_ok (o := 80) (a := 48) (hs.congr k111.wr) ((k111.gpr _ (by decide)).trans h23)
    (((((k8.trans k9).trans k10).trans k11).gpr _ (by decide)).trans a11) (by omega_arith) (by decide) (by decide)
    g11.1) fun t ⟨⟨w12, F12⟩, k12'⟩ => ?_
  have R11 : Outside S 80 8 s₁₁.mem t.mem := F12
  obtain R10 : Outside S 72 16 s₁₀.mem t.mem := (F11.mono (by omega_arith) (by omega_arith)).trans (R11.mono (by omega_arith) (by omega_arith))
  obtain R9 : Outside S 64 24 s₉.mem t.mem := (F10.mono (by omega_arith) (by omega_arith)).trans (R10.mono (by omega_arith) (by omega_arith))
  obtain R8 : Outside S 56 32 s₈.mem t.mem := (F9.mono (by omega_arith) (by omega_arith)).trans (R9.mono (by omega_arith) (by omega_arith))
  obtain R7 : Outside S 48 40 s₇.mem t.mem := (F8.mono (by omega_arith) (by omega_arith)).trans (R8.mono (by omega_arith) (by omega_arith))
  obtain R6 : Outside S 48 40 s₆.mem t.mem := by rw [← m7]; exact R7
  obtain R5 : Outside S 40 48 s₅.mem t.mem := (F6.mono (by omega_arith) (by omega_arith)).trans (R6.mono (by omega_arith) (by omega_arith))
  obtain R4 : Outside S 32 56 s₄.mem t.mem := (F5.mono (by omega_arith) (by omega_arith)).trans (R5.mono (by omega_arith) (by omega_arith))
  obtain R3 : Outside S 24 64 s₃.mem t.mem := (F4.mono (by omega_arith) (by omega_arith)).trans (R4.mono (by omega_arith) (by omega_arith))
  obtain R2 : Outside S 16 72 s₂.mem t.mem := (F3.mono (by omega_arith) (by omega_arith)).trans (R3.mono (by omega_arith) (by omega_arith))
  obtain R1 : Outside S 8 80 s₁.mem t.mem := (F2.mono (by omega_arith) (by omega_arith)).trans (R2.mono (by omega_arith) (by omega_arith))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, O11.trans (F12.mono (by omega_arith) (by omega_arith))⟩,
    (k111.trans k12').mono⟩
  · rw [oOut, R1.word (Or.inl (by omega_arith)) (by omega_arith), w1]
  · rw [oN, R2.word (Or.inl (by omega_arith)) (by omega_arith), w2, k1.gpr _ (by decide)]
  · rw [oNLen, R3.word (Or.inl (by omega_arith)) (by omega_arith), w3, k12.gpr _ (by decide)]
  · rw [oIn, R4.word (Or.inl (by omega_arith)) (by omega_arith), w4, k13.gpr _ (by decide)]
  · rw [oP, R5.word (Or.inl (by omega_arith)) (by omega_arith), w5, k14.gpr _ (by decide)]
  · rw [oPLen, R6.word (Or.inl (by omega_arith)) (by omega_arith), w6, k15.gpr _ (by decide)]
  · rw [oQ, R8.word (Or.inl (by omega_arith)) (by omega_arith), w8]; exact g7.2
  · rw [oQLen, R9.word (Or.inl (by omega_arith)) (by omega_arith), w9]; exact g8.2
  · rw [oDP, R10.word (Or.inl (by omega_arith)) (by omega_arith), w10]; exact g9.2
  · rw [oDQ, R11.word (Or.inl (by omega_arith)) (by omega_arith), w11]; exact g10.2
  · rw [oQInv, w12]; exact g11.2

/-- `argsG pc`: `args`, and with `pc` the cached values' address (`r31`)
into the header's `oR2`. -/
theorem argsG_ok {pc : Bool} {s : State} {S : Addr} {Z : Nat} (hs : Scr s S Z) (hZ : 256 ≤ Z)
    (h23 : s.gpr .r23 = S) (hrd : ∀ i < 10, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8)
    (hsep : ∀ j < 10, ∀ i < 8, ∀ x, ofs S x < Z → stackArgAddr s j + BitVec.ofNat 64 i ≠ x) :
    WP isa (.block (argsG pc)) s fun t =>
      (word t.mem S oOut = s.gpr .r3 ∧ word t.mem S oN = s.gpr .r5 ∧ word t.mem S oNLen = s.gpr .r6 ∧
        word t.mem S oIn = s.gpr .r7 ∧ word t.mem S oP = s.gpr .r9 ∧ word t.mem S oPLen = s.gpr .r10 ∧
        word t.mem S oQ = stackArg s 0 ∧ word t.mem S oQLen = stackArg s 1 ∧ word t.mem S oDP = stackArg s 2 ∧
        word t.mem S oDQ = stackArg s 4 ∧ word t.mem S oQInv = stackArg s 6 ∧ Outside S 0 96 s.mem t.mem ∧
        (pc = true → word t.mem S oR2 = s.gpr .r31)) ∧
      Keep [.r0, .r11] s t := by
  have hn := hs.nowrap
  cases pc
  · exact WP.mono (args_ok hs hZ h23 hrd hsep) fun t ⟨⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, O⟩, k⟩ =>
      ⟨⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, O.mono (by omega_arith) (by omega_arith), nofun⟩, k⟩
  · show WP isa (.block (Crt.args ++ [.store .d .r31 .r23 oR2])) s _
    rw [WP.block_append_iff]
    refine WP.mono (args_ok hs hZ h23 hrd hsep) fun t ⟨⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, O⟩, k⟩ => ?_
    refine WP.mono (st1_ok (r := .r31) (hs.congr k.wr) ((k.gpr _ (by decide)).trans h23)
      (by unfold oR2; omega_arith) (by decide)) fun u ⟨⟨u88, F⟩, ku⟩ => ?_
    obtain hw : ∀ d, d + 8 ≤ 88 → word u.mem S d = word t.mem S d := fun d hd =>
      F.word (Or.inl hd) (by omega_arith)
    refine ⟨⟨by rw [hw _ (by decide)]; exact w0, by rw [hw _ (by decide)]; exact w1,
      by rw [hw _ (by decide)]; exact w2, by rw [hw _ (by decide)]; exact w3, by rw [hw _ (by decide)]; exact w4,
      by rw [hw _ (by decide)]; exact w5, by rw [hw _ (by decide)]; exact w6, by rw [hw _ (by decide)]; exact w7,
      by rw [hw _ (by decide)]; exact w8, by rw [hw _ (by decide)]; exact w9, by rw [hw _ (by decide)]; exact w10,
      (O.mono (by omega_arith) (by omega_arith)).trans (F.mono (by unfold oR2; omega_arith) (by unfold oR2; omega_arith)),
      fun _ => u88.trans (k.gpr _ (by decide))⟩, (k.trans ku).mono⟩

end VG.Proof.Bignum.PPC64LE.Crt
