module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Key
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Ops
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.Loops
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf

/-! ### `RsaKeyGen.PPC64LE.Key.Ops`, which only this module used -/

section

/-!
# `vg_rsa_keygen_key` on PPC64LE: the operations beyond the key routines'

`notS_ok`, `andNotS_ok` and `selS_ok` (the flag slots), `setDigit_ok` (a
digit of an array), and `sub3_self_ok` and `sel_self_ok`, the key routines'
subtraction and selection into their first operand, which their loops allow
(each digit is read before it is written).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Loops
open VG.Proof.Rsa VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (ptr sub3 sel subBody selBody countLoop)
open VG.Impl.RsaKeyGen.PPC64LE.Key (notS andNotS selS setDigit)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-! ## Flags -/

theorem not_arith (x : BitVec 32) (hx : x.toNat ≤ 1) :
    ((x.setWidth 64 ^^^ BitVec.ofNat 64 1).setWidth 32).toNat = 1 - x.toNat := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_xor, toNat_ext32]
  rcases (show x.toNat = 0 ∨ x.toNat = 1 by omega_arith) with e | e <;> rw [e] <;> decide

theorem andNot_arith (x y : BitVec 32) (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    (((x.setWidth 64 ^^^ BitVec.ofNat 64 1) &&& y.setWidth 64).setWidth 32).toNat =
      if x.toNat = 0 ∧ y.toNat = 1 then 1 else 0 := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_xor, toNat_ext32, toNat_ext32]
  rcases (show x.toNat = 0 ∨ x.toNat = 1 by omega_arith) with e | e <;>
    rcases (show y.toNat = 0 ∨ y.toNat = 1 by omega_arith) with f | f <;> rw [e, f] <;> decide

theorem selS_arith (x y z : BitVec 32) (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) (hz : z.toNat ≤ 1) :
    ((x.setWidth 64 ^^^ ((y.setWidth 64 ^^^ x.setWidth 64) &&& z.setWidth 64)).setWidth 32).toNat =
      if z.toNat = 1 then y.toNat else x.toNat := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_xor, toNat_ext32,
    toNat_ext32, toNat_ext32]
  rcases (show x.toNat = 0 ∨ x.toNat = 1 by omega_arith) with e | e <;>
    rcases (show y.toNat = 0 ∨ y.toNat = 1 by omega_arith) with f | f <;>
    rcases (show z.toNat = 0 ∨ z.toNat = 1 by omega_arith) with g | g <;> rw [e, f, g] <;> decide

/-- `notS d a`: the slot `d` := `1 - a`. -/
theorem notS_ok {s : State} {B : Addr} {Z w N d a : Nat} (h : Ws s B Z w N)
    (hd : d + 4 ≤ 160) (ha : a + 4 ≤ 160) (ba : slot s.mem B a ≤ 1) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → KeyWorkspace.Keep B w [] [d] s.mem t.mem →
      slot t.mem B d = 1 - slot s.mem B a → Keep opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (notS d a ++ rest)) s Q := by
  have hz : 160 ≤ Z := h.hdr_le
  have nw := h.nowrap
  rw [WP.block_append_iff]
  have hk : WP isa (.block (notS d a)) s fun u =>
      (u.mem = s.mem.writeW (off B d) (((s.mem.readW (off B a) 32).setWidth 64 ^^^
        BitVec.ofNat 64 1).setWidth 32)) ∧ Keep opRegs s u := by
    refine WP.mono (WP.keep [.r0, .r3] ?_ (by rfl)) fun u ⟨m, k⟩ => ⟨m, k.mono⟩
    prun [notS, h.r31, h.scr.ld (show a + 4 ≤ Z by omega_arith), h.scr.st (show d + 4 ≤ Z by omega_arith),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show a < 2 ^ 15 by omega_arith),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show d < 2 ^ 15 by omega_arith)]
  refine WP.mono hk fun u ⟨mu, ku⟩ => k u (h.of_keep ku) (by rw [mu]; exact keep_slot _ _ (by simp) (by omega_arith))
    ?_ ku
  rw [mu, slot_write_self, not_arith _ ba]

/-- `andNotS d a b`: the slot `d` := `(1 - a) b`. -/
theorem andNotS_ok {s : State} {B : Addr} {Z w N d a b : Nat} (h : Ws s B Z w N)
    (hd : d + 4 ≤ 160) (ha : a + 4 ≤ 160) (hb : b + 4 ≤ 160)
    (ba : slot s.mem B a ≤ 1) (bb : slot s.mem B b ≤ 1) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → KeyWorkspace.Keep B w [] [d] s.mem t.mem →
      slot t.mem B d = (if slot s.mem B a = 0 ∧ slot s.mem B b = 1 then 1 else 0) →
      Keep opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (andNotS d a b ++ rest)) s Q := by
  have hz : 160 ≤ Z := h.hdr_le
  have nw := h.nowrap
  rw [WP.block_append_iff]
  have hk : WP isa (.block (andNotS d a b)) s fun u =>
      (u.mem = s.mem.writeW (off B d) ((((s.mem.readW (off B a) 32).setWidth 64 ^^^ BitVec.ofNat 64 1) &&&
        (s.mem.readW (off B b) 32).setWidth 64).setWidth 32)) ∧ Keep opRegs s u := by
    refine WP.mono (WP.keep [.r0, .r3] ?_ (by rfl)) fun u ⟨m, k⟩ => ⟨m, k.mono⟩
    prun [andNotS, h.r31, h.scr.ld (show a + 4 ≤ Z by omega_arith), h.scr.ld (show b + 4 ≤ Z by omega_arith),
      h.scr.st (show d + 4 ≤ Z by omega_arith),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show a < 2 ^ 15 by omega_arith),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show b < 2 ^ 15 by omega_arith),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show d < 2 ^ 15 by omega_arith)]
  refine WP.mono hk fun u ⟨mu, ku⟩ => k u (h.of_keep ku) (by rw [mu]; exact keep_slot _ _ (by simp) (by omega_arith))
    ?_ ku
  rw [mu, slot_write_self, andNot_arith _ _ ba bb]

/-- `selS d a b c`: the slot `d` := `b` if `c` is 1, `a` if it is 0. -/
theorem selS_ok {s : State} {B : Addr} {Z w N d a b c : Nat} (h : Ws s B Z w N)
    (hd : d + 4 ≤ 160) (ha : a + 4 ≤ 160) (hb : b + 4 ≤ 160) (hc : c + 4 ≤ 160)
    (ba : slot s.mem B a ≤ 1) (bb : slot s.mem B b ≤ 1) (bc : slot s.mem B c ≤ 1) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → KeyWorkspace.Keep B w [] [d] s.mem t.mem →
      slot t.mem B d = (if slot s.mem B c = 1 then slot s.mem B b else slot s.mem B a) →
      Keep opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (selS d a b c ++ rest)) s Q := by
  have hz : 160 ≤ Z := h.hdr_le
  have nw := h.nowrap
  rw [WP.block_append_iff]
  have hk : WP isa (.block (selS d a b c)) s fun u =>
      (u.mem = s.mem.writeW (off B d) (((s.mem.readW (off B a) 32).setWidth 64 ^^^
        (((s.mem.readW (off B b) 32).setWidth 64 ^^^ (s.mem.readW (off B a) 32).setWidth 64) &&&
          (s.mem.readW (off B c) 32).setWidth 64)).setWidth 32)) ∧ Keep opRegs s u := by
    refine WP.mono (WP.keep [.r0, .r3, .r9] ?_ (by rfl)) fun u ⟨m, k⟩ => ⟨m, k.mono⟩
    prun [selS, h.r31, h.scr.ld (show a + 4 ≤ Z by omega_arith), h.scr.ld (show b + 4 ≤ Z by omega_arith),
      h.scr.ld (show c + 4 ≤ Z by omega_arith), h.scr.st (show d + 4 ≤ Z by omega_arith),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show a < 2 ^ 15 by omega_arith),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show b < 2 ^ 15 by omega_arith),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show c < 2 ^ 15 by omega_arith),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show d < 2 ^ 15 by omega_arith)]
  refine WP.mono hk fun u ⟨mu, ku⟩ => k u (h.of_keep ku) (by rw [mu]; exact keep_slot _ _ (by simp) (by omega_arith))
    ?_ ku
  rw [mu, slot_write_self, selS_arith _ _ _ ba bb bc]

/-! ## A digit of an array -/

/-- A number is its digits below `k`, digit `k` and the digits above. -/
theorem val32_split (m : Mem) (B : Addr) (d : Nat) {k n : Nat} (hk : k < n) :
    val32 m B d n = val32 m B d k + 2 ^ (32 * k) * w32 m B (d + 4 * k) +
      2 ^ (32 * (k + 1)) * val32 m B (d + 4 * k + 4) (n - k - 1) := by
  have e1 := val32_append m B d k (n - k)
  rw [show k + (n - k) = n by omega_arith] at e1
  rw [e1]
  obtain ⟨j, hj⟩ : ∃ j, n - k = j + 1 := ⟨n - k - 1, by omega_arith⟩
  rw [hj, val32, pow32_succ, Nat.add_sub_cancel, Nat.mul_add, ← Nat.mul_assoc (2 ^ (32 * k)) (2 ^ 32),
    Nat.mul_comm (2 ^ (32 * k)) (2 ^ 32)]
  omega_arith

/-- `setDigit j x`: the digit of `[j]` at the byte offset `4 k` in `r6` := `x`. -/
theorem setDigit_ok {s : State} {B : Addr} {Z w N j x k : Nat} (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 256) (hx : x < 2 ^ 15) (hk : k < w) (h6 : s.gpr .r6 = BitVec.ofNat 64 (4 * k))
    {rest : List Instr} {Q : State → Prop}
    (kk : ∀ t, Ws t B Z w N → KeyWorkspace.Keep B w [j] [] s.mem t.mem →
      num t.mem B w j + 2 ^ (32 * k) * w32 s.mem B (arr w j + 4 * k) =
        num s.mem B w j + 2 ^ (32 * k) * x → Keep [.r0, .r5] s t →
      w32 t.mem B (arr w j + 4 * w) = w32 s.mem B (arr w j + 4 * w) → WP isa (.block rest) t Q) :
    WP isa (.block (setDigit j x ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  unfold setDigit
  rw [List.append_assoc]
  refine ptr_ok h (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega_arith) ?_
  rw [WP.block_append_iff]
  have k₀ : Keep [.r5] s (s.write .r5 (off B (arr w j))) := Keep.write _ _ _
  have e5 : off B (arr w j) + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 0 = off B (arr w j + 4 * k) := by
    rw [BitVec.add_zero, off_add]
  have hk' : WP isa (.block [.add .r5 .r5 .r6, .li .r0 x, .store .w .r0 .r5 0])
      (s.write .r5 (off B (arr w j))) fun u =>
        (u.mem = s.mem.writeW (off B (arr w j + 4 * k)) ((BitVec.ofNat 64 x).setWidth 32)) ∧
          Keep [.r0, .r5] (s.write .r5 (off B (arr w j))) u := by
    refine WP.keep _ ?_ (by rfl)
    prun [h6, e5, exec_li hx, h.scr.st (show arr w j + 4 * k + 4 ≤ Z by omega_arith)]
  refine WP.mono hk' fun u ⟨mu, ku⟩ => ?_
  have kt : Keep [.r0, .r5] s u := (k₀.trans ku).mono
  have o := writeW32_outside s.mem B (d := arr w j + 4 * k) ((BitVec.ofNat 64 x).setWidth 32) (by omega_arith)
  refine kk u (h.of_keep kt) ?_ ?_ kt ?_
  · rw [mu]; exact KeyWorkspace.Keep.of_arr (d := 4 * k) o (by omega_arith) (by simp)
  · have hv : ((BitVec.ofNat 64 x).setWidth 32).toNat = x := by
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_arith
    have lo := o.val32 (d := arr w j) (k := k) (by omega_arith) (by omega_arith)
    have hi := o.val32 (d := arr w j + 4 * k + 4) (k := w - k - 1) (by omega_arith) (by omega_arith)
    simp only [num]
    rw [val32_split _ _ _ hk, val32_split s.mem _ _ hk, mu, lo, hi, w32_write_self, hv]
    grind
  · rw [mu]; exact o.w32 (by omega_arith) (by omega_arith)

/-! ## Into the first operand -/

/-- `sub3 o o b`: `[o] := [o] - [b]`, the borrow in `r9`. -/
theorem sub3_self_ok {s : State} {B : Addr} {Z w N o b : Nat} (h : Ws s B Z w N)
    (ho : o < N) (hb : b < N) (hN : N ≤ 256) (hob : o ≠ b) :
    WP isa (sub3 o o b) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o + num s.mem B w b = num s.mem B w o + 2 ^ (32 * w) * (t.gpr .r9).toNat ∧
      (t.gpr .r9).toNat ≤ 1 ∧ Keep opRegs s t :=
  sub3_gen_ok h ho ho hb hN (.inl (Nat.le_refl _)) (ahead_of_ne hob)

/-- `sel o o b sl`: `[o] := [b]` if the slot `sl` is 1, kept if it is 0. -/
theorem sel_self_ok {s : State} {B : Addr} {Z w N o b sl : Nat} (h : Ws s B Z w N)
    (ho : o < N) (hb : b < N) (hN : N ≤ 256) (hob : o ≠ b)
    (hsl : sl + 4 ≤ KeyWorkspace.hdr) (bit : slot s.mem B sl ≤ 1) :
    WP isa (sel o o b sl) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o = (if slot s.mem B sl = 0 then num s.mem B w o else num s.mem B w b) ∧
      Keep opRegs s t :=
  sel_gen_ok h ho ho hb hN (.inl (Nat.le_refl _)) (ahead_of_ne hob) hsl bit

end VG.Proof.RsaKeyGen.PPC64LE.Key

end

end


/-!
# `vg_rsa_keygen_key` on PPC64LE: the working space as values

`KS m B w V F`: the arrays hold `V` (`num m B w j = V j` for every array
`j`), the flag slots `X0`–`X8` hold `F`, and the extra digit of the
divisor's array `aDv` is 0. The key routines, restated on `KS`: each
updates `V` or `F` (`Function.update`) and keeps the frame of the body
(`KK`: memory but the arrays and the slots) and the registers but
`opsRegs`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (copy sub3 sel half eqS bitOf andS stBorrow sOdd sB sC)
open VG.Impl.RsaKeyGen.PPC64LE.Key (nArr aDv aT X0 X1 X2 X3 X4 X5 X6 X7 X8 notS andNotS selS setDigit ltS)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- The flag slots. -/
abbrev flags : List Nat := [X0, X1, X2, X3, X4, X5, X6, X7, X8]

/-- The slots the body writes. -/
abbrev allSlots : List Nat := [X0, X1, X2, X3, X4, X5, X6, X7, X8, sOdd, sB, sC]

/-- The arrays. -/
abbrev allArrs : List Nat := List.range nArr

/-- The registers the key routines change. -/
abbrev opsRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]

/-- The registers the body changes, but for the entry's: also the loops' count. -/
abbrev bodyRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

/-- The frame of the body: memory but the arrays and the slots. -/
abbrev KK (B : Addr) (w : Nat) (m m' : Mem) : Prop := KeyWorkspace.Keep B w allArrs allSlots m m'

/-- `V` with `v` at `j`. -/
def upd (V : Nat → Nat) (j v : Nat) : Nat → Nat := fun i => if i = j then v else V i

@[simp] theorem upd_self (V : Nat → Nat) (j v : Nat) : upd V j v j = v := by simp [upd]

theorem upd_ne {V : Nat → Nat} {j v i : Nat} (h : i ≠ j) : upd V j v i = V i := by simp [upd, h]

theorem flag01 (c : Prop) [Decidable c] : (if c then 1 else 0 : Nat) ≤ 1 := by split <;> omega_using []

/-- A selection under a flag of a condition. -/
theorem sel_flag (c : Prop) [Decidable c] (a b : Nat) :
    (if (if c then 1 else 0 : Nat) = 0 then a else b) = if c then b else a := by
  by_cases h : c <;> simp [h]

/-- Values through the environments of the steps: `simp only` with the
steps' equations, the side conditions (distinct arrays) by `decide`. -/
macro "vsimp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (set_option linter.unusedSimpArgs false in simp (disch := decide) only [$ls,*]))

/-- `a - b` modulo `2^(32 w)`. -/
def subW (w a b : Nat) : Nat := (a + 2 ^ (32 * w) - b) % 2 ^ (32 * w)

structure KS (m : Mem) (B : Addr) (w : Nat) (V F : Nat → Nat) : Prop where
  arrs : ∀ j < nArr, num m B w j = V j
  flg : ∀ d ∈ flags, slot m B d = F d
  dv : w32 m B (arr w aDv + 4 * w) = 0

theorem KS.lt {m : Mem} {B : Addr} {w : Nat} {V F : Nat → Nat} (h : KS m B w V F) {j : Nat}
    (hj : j < nArr) : V j < 2 ^ (32 * w) := by
  rw [← h.arrs j hj]; exact val32_lt _ _ _ _

/-- An update of the arrays' values, as a fresh environment. -/
theorem KS.vx {m : Mem} {B : Addr} {w : Nat} {V F : Nat → Nat} {o v : Nat} (h : KS m B w (upd V o v) F) :
    ∃ V', KS m B w V' F ∧ V' o = v ∧ ∀ j, j ≠ o → V' j = V j :=
  ⟨_, h, upd_self _ _ _, fun _ hj => upd_ne hj⟩

/-- An update of the flags, as a fresh environment. -/
theorem KS.fx {m : Mem} {B : Addr} {w : Nat} {V F : Nat → Nat} {d x : Nat} (h : KS m B w V (upd F d x)) :
    ∃ F', KS m B w V F' ∧ F' d = x ∧ ∀ e, e ≠ d → F' e = F e :=
  ⟨_, h, upd_self _ _ _, fun _ he => upd_ne he⟩

theorem KK.trans {B : Addr} {w : Nat} {m₁ m₂ m₃ : Mem} (h₁ : KK B w m₁ m₂) (h₂ : KK B w m₂ m₃) :
    KK B w m₁ m₃ := KeyWorkspace.Keep.trans h₁ h₂

theorem KK.refl (B : Addr) (w : Nat) (m : Mem) : KK B w m m := KeyWorkspace.Keep.refl _ _ _ _ _

theorem nArr_le : nArr ≤ 256 := by decide

theorem flag_hdr : ∀ d ∈ flags, d + 4 ≤ 160 := by decide

theorem flag_slot : ∀ d ∈ flags, d ∈ allSlots := by decide

theorem flag_sep : ∀ d ∈ flags, ∀ e ∈ flags, e ∉ [d] → ∀ x ∈ [d], e + 4 ≤ x ∨ x + 4 ≤ e := by decide

/-- `KS` after a step that writes the arrays `js` and the slots `ds`. -/
theorem KS.step {m m' : Mem} {B : Addr} {w : Nat} {V F : Nat → Nat} (h : KS m B w V F)
    {js ds : List Nat} (k : KeyWorkspace.Keep B w js ds m m')
    (fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64)
    {V' F' : Nat → Nat}
    (hV : ∀ j < nArr, j ∉ js → V' j = V j)
    (hV' : ∀ j ∈ js, num m' B w j = V' j)
    (hF : ∀ d ∈ flags, d ∉ ds → F' d = F d)
    (hF' : ∀ d ∈ ds, d ∈ flags → slot m' B d = F' d)
    (hdv : aDv ∈ js → w32 m' B (arr w aDv + 4 * w) = 0)
    (hds : ∀ d ∈ ds, d + 4 ≤ 160 := by decide)
    (hsep : ∀ e ∈ flags, e ∉ ds → ∀ d ∈ ds, e + 4 ≤ d ∨ d + 4 ≤ e := by decide) :
    KS m' B w V' F' := by
  refine ⟨fun j hj => ?_, fun d hd => ?_, ?_⟩
  · by_cases hm : j ∈ js
    · exact hV' j hm
    · rw [hV j hj hm, ← h.arrs j hj]
      exact k.num (fun x hx e => hm (e ▸ hx)) hds (fit j hj)
  · by_cases hm : d ∈ ds
    · exact hF' d hm hd
    · rw [hF d hd hm, ← h.flg d hd]
      exact k.slot (flag_hdr d hd) (hsep d hd hm)
  · by_cases hm : aDv ∈ js
    · exact hdv hm
    · rw [← h.dv]
      have hf := fit aDv (by decide)
      exact k.word (i := w) (by simp only [S]; omega_using []) (fun x hx e => hm (e ▸ hx)) hds hf

theorem arr_mem {o : Nat} (ho : o < nArr) : ∀ j ∈ [o], j ∈ allArrs := by
  intro j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  subst hj; exact List.mem_range.mpr ho

/-- Writing `KK` from the frame of one step. -/
theorem KK.of {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem} (k : KeyWorkspace.Keep B w js ds m m')
    (hj : ∀ j ∈ js, j ∈ allArrs := by decide) (hd : ∀ d ∈ ds, d ∈ allSlots := by decide) : KK B w m m' :=
  k.mono hj hd

/-! ## Arithmetic -/

theorem sub_val {x a b c M : Nat} (e : x + b = a + M * c) (hc : c ≤ 1) (hx : x < M) (ha : a < M)
    (hb : b < M) : x = (a + M - b) % M ∧ c = (if a < b then 1 else 0) := by
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  · have : b ≤ a := by omega
    refine ⟨?_, by simp only [show ¬ a < b by omega, ↓reduceIte]⟩
    rw [show a + M - b = (a - b) + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · have : a < b := by
      by_contra hh
      omega
    refine ⟨?_, by simp only [this, ↓reduceIte]⟩
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- `x + y = x - (0 - y)` modulo `2^(32 w)`. -/
theorem subW_neg {w x y : Nat} (hy : y < 2 ^ (32 * w)) :
    subW w x (subW w 0 y) = (x + y) % 2 ^ (32 * w) := by
  unfold subW
  rcases Nat.eq_zero_or_pos y with rfl | hy0
  · simp only [Nat.zero_add, Nat.sub_zero, Nat.mod_self, Nat.add_zero, Nat.add_mod_right]
  · rw [show 0 + 2 ^ (32 * w) - y = 2 ^ (32 * w) - y by omega_using [],
      Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos _) hy0),
      show x + 2 ^ (32 * w) - (2 ^ (32 * w) - y) = x + y by omega_using [hy]]

/-! ## The routines on values -/

section
variable {s : State} {B : Addr} {Z w : Nat} {V F : Nat → Nat}

theorem fit_of (h : Ws s B Z w nArr) : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64 := fun _ hj => h.fit64 hj

/-- `copy o a`. -/
theorem copyE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {o a : Nat} (ho : o < nArr := by decide)
    (ha : a < nArr := by decide) (hoa : o ≠ a := by decide) :
    WP isa (copy o a) s fun t => Ws t B Z w nArr ∧ KS t.mem B w (upd V o (V a)) F ∧
      KK B w s.mem t.mem ∧ Keep opsRegs s t := by
  refine WP.mono (copy_ok h ho ha nArr_le hoa) fun t ⟨ht, kt, v, kr, top⟩ => ⟨ht, ?_, KK.of kt
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, allArrs, List.mem_range]; exact ho)
    (by simp), kr.mono⟩
  refine ks.step kt (fit_of h) (fun j hj hn => ?_) (fun j hj => ?_) (fun _ _ _ => rfl)
    (fun d hd => by simp at hd) (fun hd => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rw [upd_ne hn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rw [hj, upd_self, v, ks.arrs a ha]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd; rw [top, ks.dv]

/-- `sub3 o a b`. -/
theorem sub3E (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {o a b : Nat} (ho : o < nArr := by decide)
    (ha : a < nArr := by decide) (hb : b < nArr := by decide) (hoa : o ≠ a := by decide)
    (hob : o ≠ b := by decide) (hodv : o ≠ aDv := by decide) :
    WP isa (sub3 o a b) s fun t => Ws t B Z w nArr ∧
      KS t.mem B w (upd V o (subW w (V a) (V b))) F ∧
      (t.gpr .r9).toNat = (if V a < V b then 1 else 0) ∧ KK B w s.mem t.mem ∧ Keep opsRegs s t := by
  refine WP.mono (sub3_ok h ho ha hb nArr_le hoa hob) fun t ⟨ht, kt, v, b9, kr⟩ => ?_
  rw [ks.arrs a ha, ks.arrs b hb] at v
  obtain ⟨e1, e2⟩ := sub_val v b9 (val32_lt _ _ _ _) (ks.lt ha) (ks.lt hb)
  refine ⟨ht, ?_, e2, KK.of kt (arr_mem ho) (by simp), kr.mono⟩
  refine ks.step kt (fit_of h) (fun j hj hn => ?_) (fun j hj => ?_) (fun _ _ _ => rfl)
    (fun d hd => by simp at hd) (fun hd => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rw [upd_ne hn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rw [hj, upd_self, e1]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    exact absurd hd.symm hodv

/-- `sub3 o o b`. -/
theorem sub3SelfE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {o b : Nat} (ho : o < nArr := by decide)
    (hb : b < nArr := by decide) (hob : o ≠ b := by decide) (hodv : o ≠ aDv := by decide) :
    WP isa (sub3 o o b) s fun t => Ws t B Z w nArr ∧
      KS t.mem B w (upd V o (subW w (V o) (V b))) F ∧ KK B w s.mem t.mem ∧
      Keep opsRegs s t := by
  refine WP.mono (sub3_self_ok h ho hb nArr_le hob) fun t ⟨ht, kt, v, b9, kr⟩ => ?_
  rw [ks.arrs o ho, ks.arrs b hb] at v
  obtain ⟨e1, -⟩ := sub_val v b9 (val32_lt _ _ _ _) (ks.lt ho) (ks.lt hb)
  refine ⟨ht, ?_, KK.of kt (arr_mem ho) (by simp), kr.mono⟩
  refine ks.step kt (fit_of h) (fun j hj hn => ?_) (fun j hj => ?_) (fun _ _ _ => rfl)
    (fun d hd => by simp at hd) (fun hd => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rw [upd_ne hn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rw [hj, upd_self, e1]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    exact absurd hd.symm hodv

/-- `sel o a b sl`, the slot a flag. -/
theorem selE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {o a b sl : Nat} (ho : o < nArr := by decide)
    (ha : a < nArr := by decide) (hb : b < nArr := by decide) (hoa : o ≠ a := by decide)
    (hob : o ≠ b := by decide) (hodv : o ≠ aDv := by decide) (hsl : sl ∈ flags := by decide)
    (bit : F sl ≤ 1) :
    WP isa (sel o a b sl) s fun t => Ws t B Z w nArr ∧
      KS t.mem B w (upd V o (if F sl = 0 then V a else V b)) F ∧ KK B w s.mem t.mem ∧
      Keep opsRegs s t := by
  have hsl' : sl + 4 ≤ KeyWorkspace.hdr := flag_hdr sl hsl
  rw [← ks.flg sl hsl] at bit ⊢
  refine WP.mono (sel_ok h ho ha hb nArr_le hoa hob hsl' bit) fun t ⟨ht, kt, v, kr⟩ => ?_
  refine ⟨ht, ?_, KK.of kt (arr_mem ho) (by simp), kr.mono⟩
  refine ks.step kt (fit_of h) (fun j hj hn => ?_) (fun j hj => ?_) (fun _ _ _ => rfl)
    (fun d hd => by simp at hd) (fun hd => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rw [upd_ne hn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rw [hj, upd_self, v, ks.arrs a ha, ks.arrs b hb]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    exact absurd hd.symm hodv

/-- `sel o o b sl`, the slot a flag. -/
theorem selSelfE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {o b sl : Nat} (ho : o < nArr := by decide)
    (hb : b < nArr := by decide) (hob : o ≠ b := by decide) (hodv : o ≠ aDv := by decide)
    (hsl : sl ∈ flags := by decide) (bit : F sl ≤ 1) :
    WP isa (sel o o b sl) s fun t => Ws t B Z w nArr ∧
      KS t.mem B w (upd V o (if F sl = 0 then V o else V b)) F ∧ KK B w s.mem t.mem ∧
      Keep opsRegs s t := by
  have hsl' : sl + 4 ≤ KeyWorkspace.hdr := flag_hdr sl hsl
  rw [← ks.flg sl hsl] at bit ⊢
  refine WP.mono (sel_self_ok h ho hb nArr_le hob hsl' bit) fun t ⟨ht, kt, v, kr⟩ => ?_
  refine ⟨ht, ?_, KK.of kt (arr_mem ho) (by simp), kr.mono⟩
  refine ks.step kt (fit_of h) (fun j hj hn => ?_) (fun j hj => ?_) (fun _ _ _ => rfl)
    (fun d hd => by simp at hd) (fun hd => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rw [upd_ne hn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rw [hj, upd_self, v, ks.arrs o ho, ks.arrs b hb]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    exact absurd hd.symm hodv

/-- `half j`, for `c` 0 or 1 in `r9`. -/
theorem halfE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {j c : Nat} (hj : j < nArr := by decide)
    (hjdv : j ≠ aDv := by decide) (h9 : (s.gpr .r9).toNat = c) (hc : c ≤ 1) :
    WP isa (half j) s fun t => Ws t B Z w nArr ∧
      KS t.mem B w (upd V j ((V j + 2 ^ (32 * w) * c) / 2)) F ∧ KK B w s.mem t.mem ∧
      Keep opsRegs s t := by
  refine WP.mono (half_ok h hj nArr_le (by omega_using [h9, hc])) fun t ⟨ht, kt, v, kr⟩ => ?_
  refine ⟨ht, ?_, KK.of kt (arr_mem hj) (by simp), kr.mono⟩
  refine ks.step kt (fit_of h) (fun i hi hn => ?_) (fun i hi => ?_) (fun _ _ _ => rfl)
    (fun d hd => by simp at hd) (fun hd => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rw [upd_ne hn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rw [hi, upd_self, v, ks.arrs j hj, h9]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    exact absurd hd.symm hjdv

/-- `eqS d a b`, the slot a flag. -/
theorem eqSE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {d a b : Nat} (ha : a < nArr := by decide)
    (hb : b < nArr := by decide) (hd : d ∈ flags := by decide) :
    WP isa (eqS d a b) s fun t => Ws t B Z w nArr ∧
      KS t.mem B w V (upd F d (if V a = V b then 1 else 0)) ∧ KK B w s.mem t.mem ∧
      Keep opsRegs s t := by
  have hd' : d + 4 ≤ 160 := flag_hdr d hd
  refine WP.mono (eqS_ok h ha hb nArr_le hd') fun t ⟨ht, kt, v, kr⟩ => ?_
  refine ⟨ht, ?_, KK.of kt (by simp) (by simpa using flag_slot d hd), kr.mono⟩
  have hsep := flag_sep d hd
  refine ks.step kt (fit_of h) (fun _ _ _ => rfl) (fun j hj => by simp at hj) (fun e he hn => ?_)
    (fun e he _ => ?_) (fun hj => by simp at hj) (by simpa using hd') hsep
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rw [upd_ne hn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rw [he, upd_self, v, ks.arrs a ha, ks.arrs b hb]

end

end VG.Proof.RsaKeyGen.PPC64LE.Key
