module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Offset

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
  refine ⟨⟨Mem.readW_writeW_self64 _ _ _, writeW_outside s.mem S _ (by omega)⟩,
    ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩

/-- A word apart from the working space, after a change within it. -/
theorem readW_out {S a : Addr} {Z o n : Nat} {m m' : Mem} (h : Outside S o n m m') (hn : o + n ≤ Z)
    (hsep : ∀ i < 8, ∀ x, ofs S x < Z → a + BitVec.ofNat 64 i ≠ x) : m'.readW a 64 = m.readW a 64 :=
  Mem.readW_congr fun i hi => h _ (by
    by_contra hc
    exact hsep i (by omega) (a + BitVec.ofNat 64 i) (by omega) rfl)

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
  omega

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
  refine WP.mono (st1_ok (r := .r3) hs h23 (by omega) (by decide)) fun s₁ ⟨⟨w1, F1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (st1_ok (r := .r5) (hs.congr k1.wr) ((k1.gpr _ (by decide)).trans h23) (by omega) (by decide))
    fun s₂ ⟨⟨w2, F2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (st1_ok (r := .r6) (hs.congr k12.wr) ((k12.gpr _ (by decide)).trans h23) (by omega) (by decide))
    fun s₃ ⟨⟨w3, F3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  rw [WP.block_append_iff]
  refine WP.mono (st1_ok (r := .r7) (hs.congr k13.wr) ((k13.gpr _ (by decide)).trans h23) (by omega) (by decide))
    fun s₄ ⟨⟨w4, F4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  rw [WP.block_append_iff]
  refine WP.mono (st1_ok (r := .r9) (hs.congr k14.wr) ((k14.gpr _ (by decide)).trans h23) (by omega) (by decide))
    fun s₅ ⟨⟨w5, F5⟩, k5⟩ => ?_
  have k15 := k14.trans k5
  rw [WP.block_append_iff]
  refine WP.mono (st1_ok (r := .r10) (hs.congr k15.wr) ((k15.gpr _ (by decide)).trans h23) (by omega)
    (by decide)) fun s₆ ⟨⟨w6, F6⟩, k6⟩ => ?_
  have k16 := k15.trans k6
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = s.sp + BitVec.ofNat 64 96 ∧ t.mem = s₆.mem)
    (by
      have ea : exec (.addSp .r11 96) s₆ = some (s₆.write .r11 (s₆.sp + BitVec.ofNat 64 96)) := by simp [exec]
      prun [ea, k16.sp]) (by decide)) fun s₇ ⟨⟨a11, m7⟩, k7⟩ => ?_
  have k17 := k16.trans k7
  have O7 : Outside S 0 88 s.mem s₇.mem := by
    rw [m7]
    exact ((((F1.mono (by omega) (by omega)).trans (F2.mono (by omega) (by omega))).trans
      (F3.mono (by omega) (by omega))).trans ((F4.mono (by omega) (by omega)).trans
      (F5.mono (by omega) (by omega)))).trans (F6.mono (by omega) (by omega))
  have st : ∀ {u : State} (i : Nat), i < 10 → Outside S 0 88 s.mem u.mem → u.rd = s.rd → u.wr = s.wr →
      InRegions (u.rd ++ u.wr) (s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 (8 * i)) 8 ∧
      u.mem.readW (s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 (8 * i)) 64 = stackArg s i :=
    fun i hi O hr hw => by
      rw [sp96, hr, hw]
      exact ⟨hrd i hi, readW_out O (by omega) (hsep i hi)⟩
  rw [WP.block_append_iff]
  have g7 := st (u := s₇) 0 (by decide) O7 k17.rd k17.wr
  refine WP.mono (ld1_ok (o := 48) (a := 0) (hs.congr k17.wr) ((k17.gpr _ (by decide)).trans h23) a11 (by omega)
    (by decide) (by decide) g7.1) fun s₈ ⟨⟨w8, F8⟩, k8⟩ => ?_
  have k18 := k17.trans k8
  have O8 := O7.trans (F8.mono (by omega) (by omega))
  rw [WP.block_append_iff]
  have g8 := st (u := s₈) 1 (by decide) O8 k18.rd k18.wr
  refine WP.mono (ld1_ok (o := 56) (a := 8) (hs.congr k18.wr) ((k18.gpr _ (by decide)).trans h23)
    ((k8.gpr _ (by decide)).trans a11) (by omega) (by decide) (by decide) g8.1) fun s₉ ⟨⟨w9, F9⟩, k9⟩ => ?_
  have k19 := k18.trans k9
  have O9 := O8.trans (F9.mono (by omega) (by omega))
  rw [WP.block_append_iff]
  have g9 := st (u := s₉) 2 (by decide) O9 k19.rd k19.wr
  refine WP.mono (ld1_ok (o := 64) (a := 16) (hs.congr k19.wr) ((k19.gpr _ (by decide)).trans h23)
    ((k9.gpr _ (by decide)).trans ((k8.gpr _ (by decide)).trans a11)) (by omega) (by decide) (by decide) g9.1)
    fun s₁₀ ⟨⟨w10, F10⟩, k10⟩ => ?_
  have k110 := k19.trans k10
  have O10 := O9.trans (F10.mono (by omega) (by omega))
  rw [WP.block_append_iff]
  have g10 := st (u := s₁₀) 4 (by decide) O10 k110.rd k110.wr
  refine WP.mono (ld1_ok (o := 72) (a := 32) (hs.congr k110.wr) ((k110.gpr _ (by decide)).trans h23)
    ((((k8.trans k9).trans k10).gpr _ (by decide)).trans a11) (by omega) (by decide) (by decide) g10.1)
    fun s₁₁ ⟨⟨w11, F11⟩, k11⟩ => ?_
  have k111 := k110.trans k11
  have O11 := O10.trans (F11.mono (by omega) (by omega))
  have g11 := st (u := s₁₁) 6 (by decide) O11 k111.rd k111.wr
  refine WP.mono (ld1_ok (o := 80) (a := 48) (hs.congr k111.wr) ((k111.gpr _ (by decide)).trans h23)
    (((((k8.trans k9).trans k10).trans k11).gpr _ (by decide)).trans a11) (by omega) (by decide) (by decide)
    g11.1) fun t ⟨⟨w12, F12⟩, k12'⟩ => ?_
  have R11 : Outside S 80 8 s₁₁.mem t.mem := F12
  have R10 : Outside S 72 16 s₁₀.mem t.mem := (F11.mono (by omega) (by omega)).trans (R11.mono (by omega) (by omega))
  have R9 : Outside S 64 24 s₉.mem t.mem := (F10.mono (by omega) (by omega)).trans (R10.mono (by omega) (by omega))
  have R8 : Outside S 56 32 s₈.mem t.mem := (F9.mono (by omega) (by omega)).trans (R9.mono (by omega) (by omega))
  have R7 : Outside S 48 40 s₇.mem t.mem := (F8.mono (by omega) (by omega)).trans (R8.mono (by omega) (by omega))
  have R6 : Outside S 48 40 s₆.mem t.mem := by rw [← m7]; exact R7
  have R5 : Outside S 40 48 s₅.mem t.mem := (F6.mono (by omega) (by omega)).trans (R6.mono (by omega) (by omega))
  have R4 : Outside S 32 56 s₄.mem t.mem := (F5.mono (by omega) (by omega)).trans (R5.mono (by omega) (by omega))
  have R3 : Outside S 24 64 s₃.mem t.mem := (F4.mono (by omega) (by omega)).trans (R4.mono (by omega) (by omega))
  have R2 : Outside S 16 72 s₂.mem t.mem := (F3.mono (by omega) (by omega)).trans (R3.mono (by omega) (by omega))
  have R1 : Outside S 8 80 s₁.mem t.mem := (F2.mono (by omega) (by omega)).trans (R2.mono (by omega) (by omega))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, O11.trans (F12.mono (by omega) (by omega))⟩,
    (k111.trans k12').mono⟩
  · rw [oOut, R1.word (Or.inl (by omega)) (by omega), w1]
  · rw [oN, R2.word (Or.inl (by omega)) (by omega), w2, k1.gpr _ (by decide)]
  · rw [oNLen, R3.word (Or.inl (by omega)) (by omega), w3, k12.gpr _ (by decide)]
  · rw [oIn, R4.word (Or.inl (by omega)) (by omega), w4, k13.gpr _ (by decide)]
  · rw [oP, R5.word (Or.inl (by omega)) (by omega), w5, k14.gpr _ (by decide)]
  · rw [oPLen, R6.word (Or.inl (by omega)) (by omega), w6, k15.gpr _ (by decide)]
  · rw [oQ, R8.word (Or.inl (by omega)) (by omega), w8]; exact g7.2
  · rw [oQLen, R9.word (Or.inl (by omega)) (by omega), w9]; exact g8.2
  · rw [oDP, R10.word (Or.inl (by omega)) (by omega), w10]; exact g9.2
  · rw [oDQ, R11.word (Or.inl (by omega)) (by omega), w11]; exact g10.2
  · rw [oQInv, w12]; exact g11.2

end VG.Proof.Bignum.PPC64LE.Crt
