module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareCross
public import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquareGrouped
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxStep
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.Square
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideRow

/-! ### `Bignum.X86_64.AdxSquareDiagonalChoice`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxSquareDiagonalLoop`, which this module and modules that import it used -/

section

/-! The complete diagonal-addition loop for an ADX square. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

def diagonalValue (m : Mem) (B : Addr) (eb i : Nat) : Nat :=
  Square.diagonal (2 ^ 64) (fun j => (word m B (eb + 8 * j)).toNat) i

theorem diagonalValue_succ (m : Mem) (B : Addr) (eb i : Nat) :
    diagonalValue m B eb (i + 1) = diagonalValue m B eb i +
      (word m B (eb + 8 * i)).toNat * (word m B (eb + 8 * i)).toNat * 2 ^ (128 * i) := by
  unfold diagonalValue
  rw [Square.diagonal, ← Nat.pow_mul]
  have h : 2 ^ (128 * i) = 2 ^ (64 * i) * 2 ^ (64 * i) := by
    rw [← Nat.pow_add]; congr 1; omega_using []
  rw [h]
  grind

structure DiagInv (s₀ : State) (B : Addr) (Z A eb : Nat) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rdx, .r11, .r12, .rsi, .rbx, .rax, .rcx, .r15, .rbp, .r14] s₀ t
  rbp : t.gpr .rbp = BitVec.ofNat 64 i
  r14 : t.gpr .r14 = BitVec.ofNat 64 (2 * i)
  out : Outside B A (16 * i) s₀.mem t.mem
  val : wv t.mem B A (2 * i) + 2 ^ (128 * i) * (t.gpr .r15).toNat =
    2 * wv s₀.mem B A (2 * i) + diagonalValue s₀.mem B eb i

theorem diagStep_ok {core : List Instr} (hc : CoreOk core) {s₀ t : State} {B : Addr} {Z A eb w i : Nat}
    (h8 : s₀.gpr .r8 = off B A) (h9 : s₀.gpr .r9 = off B eb)
    (h10 : s₀.gpr .r10 = BitVec.ofNat 64 w) (hw : w < 2 ^ 60) (hi : i < w)
    (hA : A + 16 * w ≤ Z) (hb : eb + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ A ∨ A + 16 * w ≤ eb)
    (hI : DiagInv s₀ B Z A eb i t) :
    WP isa (AdxSquare.diagonalStepWith core) t fun t' =>
      t'.zf = some (decide (i + 1 = w)) ∧ DiagInv s₀ B Z A eb (i + 1) t' := by
  have hn := hI.scr.nowrap
  have kp := hI.keep
  refine WP.mono (diagonalStepWith_ok hc hI.scr ((kp.gpr (by decide)).trans h8)
    ((kp.gpr (by decide)).trans h9) hI.rbp hI.r14 ((kp.gpr (by decide)).trans h10)
    hi hw (by omega_using [hi, hA]) (by omega_using [hi, hb])) fun t' ⟨hv, ho, hbp, h14, hz, kt⟩ => ⟨hz, ?_⟩
  have rT : wv t.mem B (A + 16 * i) 2 = wv s₀.mem B (A + 16 * i) 2 := hI.out.wv (by omega_using []) (by omega_using [hi, hA, hn])
  have rX : word t.mem B (eb + 8 * i) = word s₀.mem B (eb + 8 * i) := hI.out.word (by omega_using [hi, sb]) (by omega_using [hi, hb, hn])
  have rL : wv t'.mem B A (2 * i) = wv t.mem B A (2 * i) := ho.wv (by omega_using []) (by omega_using [hi, hA, hn])
  rw [rT, rX] at hv
  refine ⟨hI.scr.congr kt.2.2, (kp.trans kt).mono (by decide), hbp, h14, ?_, ?_⟩
  · exact (hI.out.mono (o' := A) (n' := 16 * (i + 1)) (Nat.le_refl _) (by omega_using [])).trans
      (ho.mono (o' := A) (n' := 16 * (i + 1)) (by omega_using []) (by omega_using []))
  · have hval := hI.val
    rw [show 2 * (i + 1) = 2 * i + 2 by omega_using [], wv_add, wv_add s₀.mem B A, rL,
      show A + 8 * (2 * i) = A + 16 * i by omega_using [], show 64 * (2 * i) = 128 * i by omega_using [],
      show 128 * (i + 1) = 128 * i + 128 by omega_using [], Nat.pow_add, diagonalValue_succ]
    grind

/-- The doubled cross products plus the diagonal, with the final carry
accounted for explicitly. -/
theorem diagonalWith_ok {core : List Instr} (hc : CoreOk core) {s : State} {B : Addr} {Z A eb w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B A) (h9 : s.gpr .r9 = off B eb)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 w) (hw0 : 0 < w) (hw : w < 2 ^ 60)
    (hA : A + 16 * w ≤ Z) (hb : eb + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ A ∨ A + 16 * w ≤ eb) :
    WP isa (AdxSquare.diagonalWith core) s fun t =>
      wv t.mem B A (2 * w) + 2 ^ (128 * w) * (t.gpr .r15).toNat =
        2 * wv s.mem B A (2 * w) + diagonalValue s.mem B eb w ∧
      Outside B A (16 * w) s.mem t.mem ∧
      Keep [.rdx, .r11, .r12, .rsi, .rbx, .rax, .rcx, .r15, .rbp, .r14] s t := by
  unfold AdxSquare.diagonalWith
  have init : WP isa (.block [.mov32 .r15 (.imm 0), .mov32 .rbp (.imm 0), .mov32 .r14 (.imm 0)]) s fun t =>
      t.gpr .r15 = 0 ∧ t.gpr .rbp = 0 ∧ t.gpr .r14 = 0 ∧ t.mem = s.mem ∧ Keep [.r15, .rbp, .r14] s t := by
    refine WP.mono (WP.keep [.r15, .rbp, .r14] (Q := fun t =>
      t.gpr .r15 = 0 ∧ t.gpr .rbp = 0 ∧ t.gpr .r14 = 0 ∧ t.mem = s.mem) (by xrun) rfl)
      fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  refine WP.seq (WP.mono init fun s₁ ⟨h15, hbp, h14, hm, k₁⟩ => ?_)
  have hI : DiagInv s₁ B Z A eb 0 s₁ :=
    ⟨hs.congr k₁.2.2, Keep.refl _ _, hbp, h14, Outside.refl _ _ _ _, by
      simp [wv, h15, diagonalValue, Square.diagonal]⟩
  refine WP.mono (wp_upto (a := 0) hw0 (DiagInv s₁ B Z A eb)
    (fun i _ hi t h => diagStep_ok hc ((k₁.gpr (by decide)).trans h8) ((k₁.gpr (by decide)).trans h9)
      ((k₁.gpr (by decide)).trans h10) hw hi hA hb sb h) (fun _ h => h) hI)
    fun t h => ⟨?_, ?_, (k₁.trans h.keep).mono (by decide)⟩
  · have hv := h.val
    rw [hm] at hv
    exact hv
  · have ho := h.out
    rw [hm] at ho
    exact ho

end VG.Proof.Bignum.X86_64.AdxSquare

end

end

/-! ### `Bignum.X86_64.AdxSquareGroupedWord`, which only this module used -/

section

/-! Exact equations for the two independent live carry chains of a square. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxSquareGrouped
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

theorem word_ok (s : State) {dst addend : Reg} {c o : Bool}
    (hne : addend ≠ dst) (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block (AdxSquareGrouped.word dst addend)) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      (t.gpr dst).toNat + 2 ^ 64 * (c'.toNat + o'.toNat) =
        2 * (s.gpr dst).toNat + (s.gpr addend).toNat + c.toNat + o.toNat ∧
      Keeps [dst] s t := by
  rw [show AdxSquareGrouped.word dst addend =
    ([.adcx dst (.reg dst)] : List Instr) ++ [.adox dst (.reg addend)] from rfl,
    WP.block_append_iff]
  refine WP.mono (adcx_ok s (dst := dst) (src := .reg dst) rfl
    (fun _ h => nomatch h) hc) fun a ⟨ca, hca, hoa, ea, ka⟩ => ?_
  refine WP.mono (adox_ok a (dst := dst) (src := .reg addend) rfl
    (fun _ h => nomatch h) (hoa.trans ho)) fun t ⟨ot, hot, hct, et, kt⟩ => ?_
  refine ⟨ca, ot, hct.trans hca, hot, ?_, (ka.trans kt).mono (by simp)⟩
  rw [ka.gpr (r := addend) (by simpa using hne)] at et
  omega_using [ea, et]

theorem addPair_ok (s : State) {c o : Bool} (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block AdxSquareGrouped.addPair) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat +
          2 ^ 128 * (c'.toNat + o'.toNat) =
        2 * ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat) +
          (s.gpr .rcx).toNat + 2 ^ 64 * (s.gpr .rax).toNat + c.toNat + o.toNat ∧
      Keeps [.r11, .r12] s t := by
  unfold AdxSquareGrouped.addPair
  rw [WP.block_append_iff]
  refine WP.mono (word_ok s (dst := .r11) (addend := .rcx) (by decide) hc ho)
    fun a ⟨ca, oa, hca, hoa, ea, ka⟩ => ?_
  refine WP.mono (word_ok a (dst := .r12) (addend := .rax) (by decide) hca hoa)
    fun t ⟨ct, ot, hct, hot, et, kt⟩ => ?_
  refine ⟨ct, ot, hct, hot, ?_, (ka.trans kt).mono (by simp)⟩
  rw [ka.gpr (by decide : Reg.rax ∉ _), ka.gpr (by decide : Reg.r12 ∉ _)] at et
  rw [kt.gpr (by decide : Reg.r11 ∉ _)]
  omega_using [ea, et]

/-- Two cross-product words are doubled while adding one diagonal square.
Both outgoing flags remain explicit, so the next pair can consume them. -/
theorem pair_ok (s : State) {c o : Bool} (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block AdxSquareGrouped.pair) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat +
          2 ^ 128 * (c'.toNat + o'.toNat) =
        2 * ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat) +
          (s.gpr .rdx).toNat * (s.gpr .rdx).toNat + c.toNat + o.toNat ∧
      Keeps [.rax, .rcx, .r11, .r12] s t := by
  unfold AdxSquareGrouped.pair
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (mulx_ok s (hi := .rax) (lo := .rcx) (src := .reg .rdx) rfl
    (fun _ h => nomatch h) (by decide)) fun a ⟨ea, ca, oa, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (word_ok a (dst := .r11) (addend := .rcx) (by decide)
    (ca.trans hc) (oa.trans ho)) fun b ⟨cb, ob, hcb, hob, eb, kb⟩ => ?_
  refine WP.mono (word_ok b (dst := .r12) (addend := .rax) (by decide) hcb hob)
    fun t ⟨ct, ot, hct, hot, et, kt⟩ => ?_
  refine ⟨ct, ot, hct, hot, ?_, (ka.trans (kb.trans kt)).mono (by simp)⟩
  rw [ka.gpr (by decide : Reg.r11 ∉ _)] at eb
  rw [kb.gpr (by decide : Reg.rax ∉ _), kb.gpr (by decide : Reg.r12 ∉ _),
    ka.gpr (by decide : Reg.r12 ∉ _)] at et
  rw [kt.gpr (by decide : Reg.r11 ∉ _)]
  omega_using [ea, eb, et]

end VG.Proof.Bignum.X86_64.AdxSquareGrouped

end

end


/-! ## AdxSquareGroupedCarry -/

@[expose] public section

section

namespace VG.Proof.Bignum.X86_64.AdxSquareGrouped
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- Adding the previous group's carry to a single-limb square cannot
    overflow its two-limb representation. -/
theorem square_carry_lt (x : BitVec 64) {carry : Nat} (hc : carry ≤ 2) :
    x.toNat * x.toNat + carry < 2 ^ 128 := by
  have h := Nat.mul_self_le_mul_self (show x.toNat ≤ 2 ^ 64 - 1 by have := x.isLt; omega_arith)
  omega_arith

theorem inject_values (s : State) :
    WP isa (.block AdxSquareGrouped.injectCarry) s fun t =>
      t.gpr .rcx = s.gpr .rcx + s.gpr .r15 ∧
      t.gpr .rax = s.gpr .rax + (BitVec.ofBool (decide
        (2 ^ 64 ≤ (s.gpr .rcx).toNat + (s.gpr .r15).toNat))).setWidth 64 ∧
      t.mem = s.mem ∧ Keep [.rcx, .rax] s t := by
  refine WP.mono (WP.keep [.rcx, .rax] (Q := fun t =>
      t.gpr .rcx = s.gpr .rcx + s.gpr .r15 ∧
      t.gpr .rax = s.gpr .rax + (BitVec.ofBool (decide
        (2 ^ 64 ≤ (s.gpr .rcx).toNat + (s.gpr .r15).toNat))).setWidth 64 ∧
      t.mem = s.mem) ?_ rfl) fun t ⟨h,k⟩ => ⟨h.1,h.2.1,h.2.2,k⟩
  unfold AdxSquareGrouped.injectCarry
  xrun [] <;> simp

theorem inject_ok (s : State)
    (hbound : (s.gpr .rcx).toNat + 2 ^ 64 * (s.gpr .rax).toNat +
      (s.gpr .r15).toNat < 2 ^ 128) :
    WP isa (.block AdxSquareGrouped.injectCarry) s fun t =>
      (t.gpr .rcx).toNat + 2 ^ 64 * (t.gpr .rax).toNat =
        (s.gpr .rcx).toNat + 2 ^ 64 * (s.gpr .rax).toNat + (s.gpr .r15).toNat ∧
      Keeps [.rcx, .rax] s t := by
  refine WP.mono (inject_values s) fun t ⟨hl, hh, hm, hk⟩ => ?_
  refine ⟨?_, hk.1, hm, hk.2⟩
  let c := decide (2 ^ 64 ≤ (s.gpr .rcx).toNat + (s.gpr .r15).toNat)
  have he := adc_carry (s.gpr .rcx) (s.gpr .r15) false
  simp at he
  have hhi : (s.gpr .rax).toNat + c.toNat < 2 ^ 64 := by
    change (s.gpr .rcx + s.gpr .r15).toNat + 2 ^ 64 * c.toNat = _ at he
    omega_arith
  rw [hl, hh]
  simp only [BitVec.toNat_add, toNat_ofBool64]
  change _ + 2 ^ 64 * (((s.gpr .rax).toNat + c.toNat) % 2 ^ 64) = _
  rw [Nat.mod_eq_of_lt hhi]
  dsimp [c] at *
  omega_arith

theorem initialPair_ok (s : State) (hc : (s.gpr .r15).toNat ≤ 2) :
    WP isa (.block AdxSquareGrouped.initialPair) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧ t.gpr .rsi = 0 ∧
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat +
          2 ^ 128 * (c'.toNat + o'.toNat) =
        2 * ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat) +
          (s.gpr .rdx).toNat * (s.gpr .rdx).toNat + (s.gpr .r15).toNat ∧
      Keeps [.rax, .rcx, .rsi, .r11, .r12] s t := by
  unfold AdxSquareGrouped.initialPair
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (mulx_ok s (hi := .rax) (lo := .rcx) (src := .reg .rdx) rfl
    (fun _ h => nomatch h) (by decide)) fun a ⟨ea, _, _, ka⟩ => ?_
  have bound : (a.gpr .rcx).toNat + 2 ^ 64 * (a.gpr .rax).toNat +
      (a.gpr .r15).toNat < 2 ^ 128 := by
    rw [ea, ka.gpr (by decide : Reg.r15 ∉ _)]
    exact square_carry_lt _ hc
  rw [WP.block_append_iff]
  refine WP.mono (inject_ok a bound) fun b ⟨eb, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (xorRsi_ok b) fun d ⟨zd, cd, od, kd⟩ => ?_
  refine WP.mono (addPair_ok d cd od) fun t ⟨ct, ot, hct, hot, et, kt⟩ => ?_
  have kad := ka.trans (kb.trans kd)
  refine ⟨ct, ot, hct, hot, (kt.gpr (by decide)).trans zd, ?_,
    (kad.trans kt).mono (by decide)⟩
  rw [kad.gpr (by decide : Reg.r11 ∉ _), kad.gpr (by decide : Reg.r12 ∉ _),
    kd.gpr (by decide : Reg.rcx ∉ _), kd.gpr (by decide : Reg.rax ∉ _)] at et
  rw [ka.gpr (by decide : Reg.r15 ∉ _)] at eb
  simp only [Bool.toNat_false, Nat.add_zero] at et
  omega_arith

theorem close_ok (s : State) {c o : Bool} (hz : s.gpr .rsi = 0)
    (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block AdxSquareGrouped.close) s fun t =>
      (t.gpr .r15).toNat = c.toNat + o.toNat ∧
      (t.gpr .r15).toNat ≤ 2 ∧ Keeps [.r15] s t := by
  rw [show AdxSquareGrouped.close = ([.mov32 .r15 (.imm 0)] : List Instr) ++
    (([.adcx .r15 (.reg .rsi)] : List Instr) ++ [.adox .r15 (.reg .rsi)]) from rfl,
    WP.block_append_iff]
  refine WP.mono (movZero_ok s .r15) fun a ⟨za, ca, oa, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adcx_ok a (dst := .r15) (src := .reg .rsi) rfl
    (fun _ h => nomatch h) (ca.trans hc)) fun b ⟨cb, _, ob, eb, kb⟩ => ?_
  refine WP.mono (adox_ok b (dst := .r15) (src := .reg .rsi) rfl
    (fun _ h => nomatch h) (ob.trans (oa.trans ho))) fun t ⟨ot, _, _, et, kt⟩ => ?_
  have za' : a.gpr .rsi = 0 := (ka.gpr (by decide)).trans hz
  have zb' : b.gpr .rsi = 0 := (kb.gpr (by decide)).trans za'
  rw [za, za'] at eb
  rw [zb'] at et
  have hb := Bool.toNat_le c
  have ho' := Bool.toNat_le o
  simp only [show (0 : BitVec 64).toNat = 0 from rfl] at eb et
  refine ⟨?_, ?_, (ka.trans (kb.trans kt)).mono (by decide)⟩ <;> omega_arith

end VG.Proof.Bignum.X86_64.AdxSquareGrouped

end

/-! ## AdxSquareGroupedMemory -/
section

/-! The grouped diagonal accesses the same disjoint input and output words. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareGrouped
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem head_ok {s : State} {B : Addr} {Z A eb i k : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B A) (h9 : s.gpr .r9 = off B eb)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 i) (h14 : s.gpr .r14 = BitVec.ofNat 64 (2*i))
    (hA : A + 16*(i+k) + 16 ≤ Z) (hb : eb + 8*(i+k) + 8 ≤ Z) :
    WP isa (.block (AdxSquareGrouped.head k)) s fun t =>
      t.gpr .rdx = word s.mem B (eb + 8*(i+k)) ∧
      t.gpr .r11 = word s.mem B (A + 16*(i+k)) ∧
      t.gpr .r12 = word s.mem B (A + 16*(i+k) + 8) ∧
      t.cf = s.cf ∧ t.of = s.of ∧ Keeps [.rdx, .r11, .r12] s t := by
  have ea : off B A + BitVec.ofNat 64 (2*i) * BitVec.ofNat 64 8 +
      BitVec.ofInt 64 ((16*k : Nat) : Int) = off B (A + 16*(i+k)) := by
    rw [addrD]; congr 1; omega_arith
  have ea' : off B A + BitVec.ofNat 64 (2*i) * BitVec.ofNat 64 8 +
      BitVec.ofInt 64 ((16*k+8 : Nat) : Int) = off B (A + 16*(i+k) + 8) := by
    rw [addrD]; congr 1; omega_arith
  have eb' : off B eb + BitVec.ofNat 64 i * BitVec.ofNat 64 8 +
      BitVec.ofInt 64 ((8*k : Nat) : Int) = off B (eb + 8*(i+k)) := by
    rw [addrD]; congr 1; omega_arith
  refine WP.mono (WP.keep [.rdx, .r11, .r12] (Q := fun t =>
      t.gpr .rdx = word s.mem B (eb + 8*(i+k)) ∧
      t.gpr .r11 = word s.mem B (A + 16*(i+k)) ∧
      t.gpr .r12 = word s.mem B (A + 16*(i+k) + 8) ∧
      t.cf = s.cf ∧ t.of = s.of ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h,q⟩ => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,
      q.1,h.2.2.2.2.2,q.2⟩
  unfold AdxSquareGrouped.head
  xrun [State.ea, ix, h8, h9, hbp, h14, ea, ea', eb',
    hs.ld hb, hs.ld (show A + 16*(i+k) + 8 ≤ Z by omega_arith), hs.ld hA] <;> rfl

theorem store_ok {s : State} {B : Addr} {Z A i k : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B A) (h14 : s.gpr .r14 = BitVec.ofNat 64 (2*i))
    (hA : A + 16*(i+k) + 16 ≤ Z) :
    WP isa (.block (AdxSquareGrouped.store k)) s fun t =>
      t.mem = (s.mem.writeW (off B (A + 16*(i+k))) (s.gpr .r11)).writeW
        (off B (A + 16*(i+k) + 8)) (s.gpr .r12) ∧
      t.cf = s.cf ∧ t.of = s.of ∧ Keep [] s t := by
  have ea : off B A + BitVec.ofNat 64 (2*i) * BitVec.ofNat 64 8 +
      BitVec.ofInt 64 ((16*k : Nat) : Int) = off B (A + 16*(i+k)) := by
    rw [addrD]; congr 1; omega_arith
  have ea' : off B A + BitVec.ofNat 64 (2*i) * BitVec.ofNat 64 8 +
      BitVec.ofInt 64 ((16*k+8 : Nat) : Int) = off B (A + 16*(i+k) + 8) := by
    rw [addrD]; congr 1; omega_arith
  refine WP.mono (WP.keep [] (Q := fun t =>
      t.mem = (s.mem.writeW (off B (A + 16*(i+k))) (s.gpr .r11)).writeW
        (off B (A + 16*(i+k) + 8)) (s.gpr .r12) ∧ t.cf = s.cf ∧ t.of = s.of)
    ?_ rfl) fun t ⟨h,q⟩ => ⟨h.1,h.2.1,h.2.2,q⟩
  unfold AdxSquareGrouped.store
  xrun [State.ea, ix, h8, h14, ea, ea', hs.st (show A + 16*(i+k) + 8 ≤ Z by omega_arith), hs.st hA]

end VG.Proof.Bignum.X86_64.AdxSquareGrouped

end

/-! ## AdxSquareGroupedStep -/
section

/-! Load, compute and store one pair inside a grouped diagonal. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareGrouped
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

def CoreResult (carry : Nat) (s t : State) : Prop := ∃ c o : Bool,
  t.cf = some c ∧ t.of = some o ∧ t.gpr .rsi = 0 ∧
  (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (c.toNat + o.toNat) =
    2 * ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat) +
      (s.gpr .rdx).toNat * (s.gpr .rdx).toNat + carry ∧
  Keeps [.rax, .rcx, .rsi, .r11, .r12] s t

def stepRegs : List Reg := [.rdx, .r11, .r12, .rax, .rcx, .rsi]

theorem step_ok {s : State} {B : Addr} {Z A eb i k carry : Nat} (core : List Instr)
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B A) (h9 : s.gpr .r9 = off B eb)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 i) (h14 : s.gpr .r14 = BitVec.ofNat 64 (2*i))
    (hA : A + 16*(i+k) + 16 ≤ Z) (hb : eb + 8*(i+k) + 8 ≤ Z)
    (hc : ∀ a, Keeps [.rdx, .r11, .r12] s a → a.cf = s.cf → a.of = s.of →
      WP isa (.block core) a (CoreResult carry a)) :
    WP isa (AdxSquareGrouped.step k core) s fun t => ∃ c o : Bool,
      t.cf = some c ∧ t.of = some o ∧ t.gpr .rsi = 0 ∧
      wv t.mem B (A + 16*(i+k)) 2 + 2 ^ 128 * (c.toNat + o.toNat) =
        2 * wv s.mem B (A + 16*(i+k)) 2 +
          (word s.mem B (eb + 8*(i+k))).toNat * (word s.mem B (eb + 8*(i+k))).toNat + carry ∧
      Outside B (A + 16*(i+k)) 16 s.mem t.mem ∧ Keep stepRegs s t := by
  unfold AdxSquareGrouped.step
  refine WP.seq (WP.mono (head_ok hs h8 h9 hbp h14 hA hb)
    fun a ⟨hdx, h11, h12, cfa, ofa, ka⟩ => ?_)
  refine WP.seq (WP.mono (hc a ka cfa ofa) fun b ⟨cb, ob, hcb, hob, zb, eb', kb⟩ => ?_)
  have kab := ka.trans kb
  refine WP.mono (store_ok (hs.congr kab.2.2.2) ((kab.gpr (by decide)).trans h8)
    ((kab.gpr (by decide)).trans h14) hA) fun t ⟨hm, hct, hot, kt⟩ => ?_
  obtain ⟨hv, hout⟩ := AdxSquare.write2 b.mem B (A + 16*(i+k)) (b.gpr .r11) (b.gpr .r12)
    (by have := hs.nowrap; omega_arith)
  rw [← hm] at hv hout
  rw [kab.2.1] at hout
  refine ⟨cb, ob, hct.trans hcb, hot.trans hob, (kt.gpr (by simp)).trans zb, ?_, hout,
    (kab.keep.trans kt).mono (by decide)⟩
  rw [hv, AdxSquare.wv2]
  rw [h11, h12, hdx] at eb'
  exact eb'

theorem initialStep_ok {s : State} {B : Addr} {Z A eb i k : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B A) (h9 : s.gpr .r9 = off B eb)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 i) (h14 : s.gpr .r14 = BitVec.ofNat 64 (2*i))
    (hA : A + 16*(i+k) + 16 ≤ Z) (hb : eb + 8*(i+k) + 8 ≤ Z)
    (hc : (s.gpr .r15).toNat ≤ 2) :
    WP isa (AdxSquareGrouped.step k AdxSquareGrouped.initialPair) s fun t => ∃ c o : Bool,
      t.cf = some c ∧ t.of = some o ∧ t.gpr .rsi = 0 ∧
      wv t.mem B (A + 16*(i+k)) 2 + 2 ^ 128 * (c.toNat + o.toNat) =
        2 * wv s.mem B (A + 16*(i+k)) 2 +
          (word s.mem B (eb + 8*(i+k))).toNat * (word s.mem B (eb + 8*(i+k))).toNat +
            (s.gpr .r15).toNat ∧
      Outside B (A + 16*(i+k)) 16 s.mem t.mem ∧ Keep stepRegs s t := by
  apply step_ok _ hs h8 h9 hbp h14 hA hb
  intro a ka _ _
  have ha : a.gpr .r15 = s.gpr .r15 := ka.gpr (by decide)
  unfold CoreResult
  simpa only [ha] using initialPair_ok a (by simpa only [ha] using hc)

theorem nextStep_ok {s : State} {B : Addr} {Z A eb i k : Nat} {c o : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B A) (h9 : s.gpr .r9 = off B eb)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 i) (h14 : s.gpr .r14 = BitVec.ofNat 64 (2*i))
    (hA : A + 16*(i+k) + 16 ≤ Z) (hb : eb + 8*(i+k) + 8 ≤ Z)
    (hc : s.cf = some c) (ho : s.of = some o) (hz : s.gpr .rsi = 0) :
    WP isa (AdxSquareGrouped.step k AdxSquareGrouped.pair) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧ t.gpr .rsi = 0 ∧
      wv t.mem B (A + 16*(i+k)) 2 + 2 ^ 128 * (c'.toNat + o'.toNat) =
        2 * wv s.mem B (A + 16*(i+k)) 2 +
          (word s.mem B (eb + 8*(i+k))).toNat * (word s.mem B (eb + 8*(i+k))).toNat +
            c.toNat + o.toNat ∧
      Outside B (A + 16*(i+k)) 16 s.mem t.mem ∧ Keep stepRegs s t := by
  have base := step_ok (carry := c.toNat + o.toNat) AdxSquareGrouped.pair hs h8 h9 hbp h14 hA hb
  apply WP.mono (base ?_)
  · intro t ⟨ct, ot, hct, hot, zt, et, hout, kt⟩
    exact ⟨ct,ot,hct,hot,zt,by omega_arith,hout,kt⟩
  · intro a ka hca hoa
    refine WP.mono (pair_ok a (hca.trans hc) (hoa.trans ho)) fun t ⟨ct,ot,hct,hot,et,kt⟩ => ?_
    refine ⟨ct,ot,hct,hot,?_,by omega_arith,kt.mono (by decide)⟩
    exact (kt.gpr (by decide)).trans ((ka.gpr (by decide)).trans hz)

end VG.Proof.Bignum.X86_64.AdxSquareGrouped

end

/-! ## AdxSquareGroupedValue -/
section

namespace VG.Proof.Bignum.X86_64.AdxSquareGrouped
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxSquare (diagonalValue diagonalValue_succ)

/-- The processed prefix and its carry, whether held in a register or flags. -/
structure ValueInv (s₀ : State) (B : Addr) (A eb i carry : Nat) (t : State) : Prop where
  out : Outside B A (16*i) s₀.mem t.mem
  val : wv t.mem B A (2*i) + 2 ^ (128*i) * carry =
    2 * wv s₀.mem B A (2*i) + diagonalValue s₀.mem B eb i

theorem value_step {s₀ s t : State} {B : Addr} {Z A eb w i carry carry' : Nat}
    (hs : Scr s B Z) (hi : i < w) (hA : A + 16*w ≤ Z) (hb : eb + 8*w ≤ Z)
    (sep : eb + 8*w ≤ A ∨ A + 16*w ≤ eb)
    (h : ValueInv s₀ B A eb i carry s)
    (hv : wv t.mem B (A+16*i) 2 + 2^128*carry' =
      2*wv s.mem B (A+16*i) 2 +
        (word s.mem B (eb+8*i)).toNat * (word s.mem B (eb+8*i)).toNat + carry)
    (ho : Outside B (A+16*i) 16 s.mem t.mem) :
    ValueInv s₀ B A eb (i+1) carry' t := by
  have hn := hs.nowrap
  have rt : wv s.mem B (A+16*i) 2 = wv s₀.mem B (A+16*i) 2 := h.out.wv (by omega_arith) (by omega_arith)
  have rx : word s.mem B (eb+8*i) = word s₀.mem B (eb+8*i) := h.out.word (by omega_arith) (by omega_arith)
  have rl : wv t.mem B A (2*i) = wv s.mem B A (2*i) := ho.wv (by omega_arith) (by omega_arith)
  rw [rt,rx] at hv
  refine ⟨?_,?_⟩
  · exact (h.out.mono (o' := A) (n' := 16*(i+1)) (Nat.le_refl _) (by omega_arith)).trans
      (ho.mono (o' := A) (n' := 16*(i+1)) (by omega_arith) (by omega_arith))
  · have hp := h.val
    rw [show 2*(i+1) = 2*i+2 by omega_arith, wv_add, wv_add s₀.mem B A, rl,
      show A+8*(2*i) = A+16*i by omega_arith, show 64*(2*i) = 128*i by omega_arith,
      show 128*(i+1) = 128*i+128 by omega_arith, Nat.pow_add, diagonalValue_succ]
    grind

end VG.Proof.Bignum.X86_64.AdxSquareGrouped

end

/-! ## AdxSquareGroupedGroup -/
section

namespace VG.Proof.Bignum.X86_64.AdxSquareGrouped
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxSquare (DiagInv)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- After `j` words of a group from `t`: the carry in the flags, and the
value so far. -/
structure StepSt (s₀ t : State) (B : Addr) (A eb i j : Nat) (s : State) : Prop where
  keep : Keep stepRegs t s
  car : ∃ c o : Bool, s.cf = some c ∧ s.of = some o ∧ s.gpr .rsi = 0 ∧
    ValueInv s₀ B A eb (i + j) (c.toNat + o.toNat) s

/-- A group's first word, with the carry in `r15`. -/
theorem initStep_ok {s₀ t : State} {B : Addr} {Z A eb w i : Nat}
    (h8 : s₀.gpr .r8 = off B A) (h9 : s₀.gpr .r9 = off B eb) (hi : i+1 ≤ w)
    (hA : A+16*w ≤ Z) (hb : eb+8*w ≤ Z) (sep : eb+8*w ≤ A ∨ A+16*w ≤ eb)
    (hI : DiagInv s₀ B Z A eb i t) (hc : (t.gpr .r15).toNat ≤ 2) :
    WP isa (AdxSquareGrouped.step 0 AdxSquareGrouped.initialPair) t (StepSt s₀ t B A eb i 1) := by
  have v0 : ValueInv s₀ B A eb i (t.gpr .r15).toNat t := ⟨hI.out,hI.val⟩
  have l0 : Keep stepRegs t t := Keep.refl _ _
  have g0 := hI.keep
  refine WP.mono (initialStep_ok (k := 0) (hI.scr.congr l0.2.2)
    ((g0.gpr (by decide)).trans h8) ((g0.gpr (by decide)).trans h9)
    ((l0.gpr (by decide)).trans hI.rbp) ((l0.gpr (by decide)).trans hI.r14)
    (by omega_arith) (by omega_arith) hc) fun s1 ⟨cf1, of1, c1, o1, z1, e1, out1, k1⟩ => ?_
  refine ⟨(l0.trans k1).mono (by decide), cf1, of1, c1, o1, z1, ?_⟩
  have e : wv s1.mem B (A+16*(i+0)) 2 + 2^128*(cf1.toNat+of1.toNat) =
      2*wv t.mem B (A+16*(i+0)) 2 +
        (word t.mem B (eb+8*(i+0))).toNat * (word t.mem B (eb+8*(i+0))).toNat +
        (t.gpr .r15).toNat := by omega_arith
  simpa only [Nat.add_zero, Nat.add_assoc] using
    value_step (hI.scr.congr l0.2.2) (by omega_arith : i+0<w) hA hb sep (by simpa using v0) e out1

/-- A group's next word, with the carry in the flags: proven once for every
word of `group` and `group8`. -/
theorem pairStep_ok {s₀ t s : State} {B : Addr} {Z A eb w i j : Nat}
    (h8 : s₀.gpr .r8 = off B A) (h9 : s₀.gpr .r9 = off B eb) (hij : i+j+1 ≤ w)
    (hA : A+16*w ≤ Z) (hb : eb+8*w ≤ Z) (sep : eb+8*w ≤ A ∨ A+16*w ≤ eb)
    (hI : DiagInv s₀ B Z A eb i t) (hS : StepSt s₀ t B A eb i j s) :
    WP isa (AdxSquareGrouped.step j AdxSquareGrouped.pair) s (StepSt s₀ t B A eb i (j+1)) := by
  obtain ⟨l, c, o, hc, ho, hz, v⟩ := hS
  have g := hI.keep.trans l
  refine WP.mono (nextStep_ok (k := j) (hI.scr.congr l.2.2)
    ((g.gpr (by decide)).trans h8) ((g.gpr (by decide)).trans h9)
    ((l.gpr (by decide)).trans hI.rbp) ((l.gpr (by decide)).trans hI.r14)
    (by omega_arith) (by omega_arith) hc ho hz) fun s' ⟨c', o', hc', ho', hz', e', out', k'⟩ => ?_
  refine ⟨(l.trans k').mono (by decide), c', o', hc', ho', hz', ?_⟩
  have e : wv s'.mem B (A+16*(i+j)) 2 + 2^128*(c'.toNat+o'.toNat) =
      2*wv s.mem B (A+16*(i+j)) 2 +
        (word s.mem B (eb+8*(i+j))).toNat * (word s.mem B (eb+8*(i+j))).toNat +
        (c.toNat+o.toNat) := by omega_arith
  simpa only [Nat.add_assoc] using
    value_step (hI.scr.congr l.2.2) (by omega_arith : i+j<w) hA hb sep v e out'

theorem group_ok {s₀ t : State} {B : Addr} {Z A eb w i : Nat}
    (h8 : s₀.gpr .r8 = off B A) (h9 : s₀.gpr .r9 = off B eb)
    (h10 : s₀.gpr .r10 = BitVec.ofNat 64 w) (hw : w < 2 ^ 60) (hi : i+4 ≤ w)
    (hA : A+16*w ≤ Z) (hb : eb+8*w ≤ Z)
    (sep : eb+8*w ≤ A ∨ A+16*w ≤ eb)
    (hI : DiagInv s₀ B Z A eb i t) (hc : (t.gpr .r15).toNat ≤ 2) :
    WP isa AdxSquareGrouped.group t fun t' =>
      t'.zf = some (decide (i+4 = w)) ∧ DiagInv s₀ B Z A eb (i+4) t' ∧
        (t'.gpr .r15).toNat ≤ 2 := by
  simp only [AdxSquareGrouped.group, seqs]
  refine WP.seq (WP.mono (initStep_ok h8 h9 (by omega_arith) hA hb sep hI hc) fun s1 st1 => ?_)
  refine WP.seq (WP.mono (pairStep_ok (j := 1) h8 h9 (by omega_arith) hA hb sep hI st1)
    fun s2 st2 => ?_)
  refine WP.seq (WP.mono (pairStep_ok (j := 2) h8 h9 (by omega_arith) hA hb sep hI st2)
    fun s3 st3 => ?_)
  refine WP.seq (WP.mono (pairStep_ok (j := 3) h8 h9 (by omega_arith) hA hb sep hI st3)
    fun s4 st4 => ?_)
  obtain ⟨l4, cf4, of4, c4, o4, z4, v4⟩ := st4
  rw [WP.block_append_iff]
  refine WP.mono (close_ok s4 z4 c4 o4) fun s5 ⟨e5, bound5, k5⟩ => ?_
  have l5 := l4.trans k5.keep
  have g5 := hI.keep.trans l5
  have hbp5 : s5.gpr .rbp = BitVec.ofNat 64 i := (l5.gpr (by decide)).trans hI.rbp
  have h145 : s5.gpr .r14 = BitVec.ofNat 64 (2*i) := (l5.gpr (by decide)).trans hI.r14
  have h105 : s5.gpr .r10 = BitVec.ofNat 64 w := (g5.gpr (by decide)).trans h10
  have count : BitVec.ofNat 64 (2*i) + 8 = BitVec.ofNat 64 (2*(i+4)) := by
    rw [show 2*(i+4) = 2*i+8 by omega_arith, BitVec.ofNat_add]; rfl
  have finish : WP isa (.block [.alu .add .rbp (.imm 4), .alu .add .r14 (.imm 8), .alu .cmp .rbp (.reg .r10)]) s5 fun u =>
      u.gpr .rbp = BitVec.ofNat 64 (i+4) ∧ u.gpr .r14 = BitVec.ofNat 64 (2*(i+4)) ∧
      u.zf = some (decide (i+4=w)) ∧ u.mem = s5.mem ∧ Keep [.rbp,.r14] s5 u := by
    refine WP.mono (WP.keep [.rbp,.r14] (Q := fun u =>
      u.gpr .rbp = BitVec.ofNat 64 (i+4) ∧ u.gpr .r14 = BitVec.ofNat 64 (2*(i+4)) ∧
      u.zf = some (decide (i+4=w)) ∧ u.mem = s5.mem) ?_ rfl)
      fun u ⟨h,k⟩ => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,k⟩
    xrun [hbp5,h145,h105,ofNat_add_four,count,
      ofNat_sub_beq (show i+4 < 2^64 by omega_arith) (show w < 2^64 by omega_arith)]
  refine WP.mono finish fun u ⟨bp, r14, hz, hm, ku⟩ => ?_
  have gu := g5.trans ku
  have h15 : u.gpr .r15 = s5.gpr .r15 := ku.gpr (by decide)
  refine ⟨hz, ⟨hI.scr.congr (l5.trans ku).2.2, gu.mono (by decide), bp, r14, ?_, ?_⟩, ?_⟩
  · rw [hm,k5.2.1]; exact v4.out
  · rw [hm,k5.2.1,h15,e5]; exact v4.val
  · rw [h15]; exact bound5

theorem group8_ok {s₀ t : State} {B : Addr} {Z A eb w i : Nat}
    (h8 : s₀.gpr .r8 = off B A) (h9 : s₀.gpr .r9 = off B eb)
    (h10 : s₀.gpr .r10 = BitVec.ofNat 64 w) (hw : w < 2 ^ 60) (hi : i+8 ≤ w)
    (hA : A+16*w ≤ Z) (hb : eb+8*w ≤ Z)
    (sep : eb+8*w ≤ A ∨ A+16*w ≤ eb)
    (hI : DiagInv s₀ B Z A eb i t) (hc : (t.gpr .r15).toNat ≤ 2) :
    WP isa AdxSquareGrouped.group8 t fun t' =>
      t'.zf = some (decide (i+8 = w)) ∧ DiagInv s₀ B Z A eb (i+8) t' ∧
        (t'.gpr .r15).toNat ≤ 2 := by
  simp only [AdxSquareGrouped.group8, seqs]
  refine WP.seq (WP.mono (initStep_ok h8 h9 (by omega_arith) hA hb sep hI hc) fun s1 st1 => ?_)
  refine WP.seq (WP.mono (pairStep_ok (j := 1) h8 h9 (by omega_arith) hA hb sep hI st1)
    fun s2 st2 => ?_)
  refine WP.seq (WP.mono (pairStep_ok (j := 2) h8 h9 (by omega_arith) hA hb sep hI st2)
    fun s3 st3 => ?_)
  refine WP.seq (WP.mono (pairStep_ok (j := 3) h8 h9 (by omega_arith) hA hb sep hI st3)
    fun s4 st4 => ?_)
  refine WP.seq (WP.mono (pairStep_ok (j := 4) h8 h9 (by omega_arith) hA hb sep hI st4)
    fun s5 st5 => ?_)
  refine WP.seq (WP.mono (pairStep_ok (j := 5) h8 h9 (by omega_arith) hA hb sep hI st5)
    fun s6 st6 => ?_)
  refine WP.seq (WP.mono (pairStep_ok (j := 6) h8 h9 (by omega_arith) hA hb sep hI st6)
    fun s7 st7 => ?_)
  refine WP.seq (WP.mono (pairStep_ok (j := 7) h8 h9 (by omega_arith) hA hb sep hI st7)
    fun s8 st8 => ?_)
  obtain ⟨l8, cf8, of8, c8, o8, z8, v8⟩ := st8
  rw [WP.block_append_iff]
  refine WP.mono (close_ok s8 z8 c8 o8) fun s9 ⟨e9, bound9, k9⟩ => ?_
  have l9 := l8.trans k9.keep
  have g9 := hI.keep.trans l9
  have hbp9 : s9.gpr .rbp = BitVec.ofNat 64 i := (l9.gpr (by decide)).trans hI.rbp
  have h149 : s9.gpr .r14 = BitVec.ofNat 64 (2*i) := (l9.gpr (by decide)).trans hI.r14
  have h109 : s9.gpr .r10 = BitVec.ofNat 64 w := (g9.gpr (by decide)).trans h10
  have bump : BitVec.ofNat 64 i + 8 = BitVec.ofNat 64 (i+8) := by
    rw [BitVec.ofNat_add]; rfl
  have count : BitVec.ofNat 64 (2*i) + 16 = BitVec.ofNat 64 (2*(i+8)) := by
    rw [show 2*(i+8) = 2*i+16 by omega_arith, BitVec.ofNat_add]; rfl
  have finish : WP isa (.block [.alu .add .rbp (.imm 8), .alu .add .r14 (.imm 16), .alu .cmp .rbp (.reg .r10)]) s9 fun u =>
      u.gpr .rbp = BitVec.ofNat 64 (i+8) ∧ u.gpr .r14 = BitVec.ofNat 64 (2*(i+8)) ∧
      u.zf = some (decide (i+8=w)) ∧ u.mem = s9.mem ∧ Keep [.rbp,.r14] s9 u := by
    refine WP.mono (WP.keep [.rbp,.r14] (Q := fun u =>
      u.gpr .rbp = BitVec.ofNat 64 (i+8) ∧ u.gpr .r14 = BitVec.ofNat 64 (2*(i+8)) ∧
      u.zf = some (decide (i+8=w)) ∧ u.mem = s9.mem) ?_ rfl)
      fun u ⟨h,k⟩ => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,k⟩
    xrun [hbp9,h149,h109,bump,count,
      ofNat_sub_beq (show i+8 < 2^64 by omega_arith) (show w < 2^64 by omega_arith)]
  refine WP.mono finish fun u ⟨bp, r14, hz, hm, ku⟩ => ?_
  have gu := g9.trans ku
  have h15 : u.gpr .r15 = s9.gpr .r15 := ku.gpr (by decide)
  refine ⟨hz, ⟨hI.scr.congr (l9.trans ku).2.2, gu.mono (by decide), bp, r14, ?_, ?_⟩, ?_⟩
  · rw [hm,k9.2.1]; exact v8.out
  · rw [hm,k9.2.1,h15,e9]; exact v8.val
  · rw [h15]; exact bound9

end VG.Proof.Bignum.X86_64.AdxSquareGrouped

end

/-! ## AdxSquareGroupedLoop -/
section

/-! The terminating grouped diagonal loop, with the original memory frame. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareGrouped
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxSquare (DiagInv diagonalValue)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem diagonal_ok {s : State} {B : Addr} {Z A eb w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B A) (h9 : s.gpr .r9 = off B eb)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 w) (hw0 : 0 < w) (hw : w < 2^60)
    (hw4 : w % 4 = 0) (hA : A+16*w ≤ Z) (hb : eb+8*w ≤ Z)
    (sep : eb+8*w ≤ A ∨ A+16*w ≤ eb) :
    WP isa AdxSquareGrouped.diagonal s fun t =>
      wv t.mem B A (2*w) + 2^(128*w)*(t.gpr .r15).toNat =
        2*wv s.mem B A (2*w) + diagonalValue s.mem B eb w ∧
      Outside B A (16*w) s.mem t.mem ∧
      Keep [.rdx,.r11,.r12,.rsi,.rbx,.rax,.rcx,.r15,.rbp,.r14] s t := by
  have hdiv : 4*(w/4) = w := by omega_arith
  unfold AdxSquareGrouped.diagonal
  have init : WP isa (.block [.mov32 .r15 (.imm 0), .mov32 .rbp (.imm 0), .mov32 .r14 (.imm 0)]) s fun t =>
      t.gpr .r15 = 0 ∧ t.gpr .rbp = 0 ∧ t.gpr .r14 = 0 ∧ t.mem = s.mem ∧
      Keep [.r15,.rbp,.r14] s t := by
    refine WP.mono (WP.keep [.r15,.rbp,.r14] (Q := fun t =>
      t.gpr .r15 = 0 ∧ t.gpr .rbp = 0 ∧ t.gpr .r14 = 0 ∧ t.mem = s.mem)
      (by xrun) rfl) fun t ⟨h,k⟩ => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,k⟩
  refine WP.seq (WP.mono init fun s1 ⟨h15,hbp,h14,hm,k1⟩ => ?_)
  let Inv := fun j t => DiagInv s1 B Z A eb (4*j) t ∧ (t.gpr .r15).toNat ≤ 2
  have initial : Inv 0 s1 := ⟨
    ⟨hs.congr k1.2.2, Keep.refl _ _, hbp, h14, Outside.refl _ _ _ _, by
      simp [wv,h15,diagonalValue,Square.diagonal]⟩, by rw [h15]; decide⟩
  have body : ∀ j, 0 ≤ j → j < w/4 → ∀ t, Inv j t →
      WP isa AdxSquareGrouped.group t fun u =>
        u.zf = some (decide (j+1=w/4)) ∧ Inv (j+1) u := by
    intro j _ hj t ht
    refine WP.mono (group_ok ((k1.gpr (by decide)).trans h8) ((k1.gpr (by decide)).trans h9)
      ((k1.gpr (by decide)).trans h10) hw (by omega_arith : 4*j+4 ≤ w) hA hb sep ht.1 ht.2)
      fun u ⟨hz,hd,hc⟩ => ?_
    have eq : (4*j+4=w) = (j+1=w/4) := propext ⟨by omega_arith,by omega_arith⟩
    refine ⟨by simpa only [eq] using hz, ?_, hc⟩
    simpa only [Nat.mul_add, Nat.mul_one] using hd
  refine WP.mono (wp_upto (a := 0) (by omega_arith : 0 < w/4) Inv body (fun _ h => h) initial)
    fun t ⟨ht,_⟩ => ?_
  rw [hdiv] at ht
  refine ⟨?_,?_,(k1.trans ht.keep).mono (by simp)⟩
  · have hv := ht.val
    rw [hm] at hv
    exact hv
  · have ho := ht.out
    rw [hm] at ho
    exact ho

theorem diagonal8_ok {s : State} {B : Addr} {Z A eb w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B A) (h9 : s.gpr .r9 = off B eb)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 w) (hw0 : 0 < w) (hw : w < 2^60)
    (hw8 : w % 8 = 0) (hA : A+16*w ≤ Z) (hb : eb+8*w ≤ Z)
    (sep : eb+8*w ≤ A ∨ A+16*w ≤ eb) :
    WP isa AdxSquareGrouped.diagonal8 s fun t =>
      wv t.mem B A (2*w) + 2^(128*w)*(t.gpr .r15).toNat =
        2*wv s.mem B A (2*w) + diagonalValue s.mem B eb w ∧
      Outside B A (16*w) s.mem t.mem ∧
      Keep [.rdx,.r11,.r12,.rsi,.rbx,.rax,.rcx,.r15,.rbp,.r14] s t := by
  have hdiv : 8*(w/8) = w := by omega_arith
  unfold AdxSquareGrouped.diagonal8
  have init : WP isa (.block [.mov32 .r15 (.imm 0), .mov32 .rbp (.imm 0), .mov32 .r14 (.imm 0)]) s fun t =>
      t.gpr .r15 = 0 ∧ t.gpr .rbp = 0 ∧ t.gpr .r14 = 0 ∧ t.mem = s.mem ∧
      Keep [.r15,.rbp,.r14] s t := by
    refine WP.mono (WP.keep [.r15,.rbp,.r14] (Q := fun t =>
      t.gpr .r15 = 0 ∧ t.gpr .rbp = 0 ∧ t.gpr .r14 = 0 ∧ t.mem = s.mem)
      (by xrun) rfl) fun t ⟨h,k⟩ => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,k⟩
  refine WP.seq (WP.mono init fun s1 ⟨h15,hbp,h14,hm,k1⟩ => ?_)
  let Inv := fun j t => DiagInv s1 B Z A eb (8*j) t ∧ (t.gpr .r15).toNat ≤ 2
  have initial : Inv 0 s1 := ⟨
    ⟨hs.congr k1.2.2, Keep.refl _ _, hbp, h14, Outside.refl _ _ _ _, by
      simp [wv,h15,diagonalValue,Square.diagonal]⟩, by rw [h15]; decide⟩
  have body : ∀ j, 0 ≤ j → j < w/8 → ∀ t, Inv j t →
      WP isa AdxSquareGrouped.group8 t fun u =>
        u.zf = some (decide (j+1=w/8)) ∧ Inv (j+1) u := by
    intro j _ hj t ht
    refine WP.mono (group8_ok ((k1.gpr (by decide)).trans h8) ((k1.gpr (by decide)).trans h9)
      ((k1.gpr (by decide)).trans h10) hw (by omega_arith : 8*j+8 ≤ w) hA hb sep ht.1 ht.2)
      fun u ⟨hz,hd,hc⟩ => ?_
    have eq : (8*j+8=w) = (j+1=w/8) := propext ⟨by omega_arith,by omega_arith⟩
    refine ⟨by simpa only [eq] using hz, ?_, hc⟩
    simpa only [Nat.mul_add, Nat.mul_one] using hd
  refine WP.mono (wp_upto (a := 0) (by omega_arith : 0 < w/8) Inv body (fun _ h => h) initial)
    fun t ⟨ht,_⟩ => ?_
  rw [hdiv] at ht
  refine ⟨?_,?_,(k1.trans ht.keep).mono (by simp)⟩
  · have hv := ht.val
    rw [hm] at hv
    exact hv
  · have ho := ht.out
    rw [hm] at ho
    exact ho

end VG.Proof.Bignum.X86_64.AdxSquareGrouped

end

/-! ## AdxSquareDiagonalChoice -/
section

namespace VG.Proof.Bignum.X86_64.AdxSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem and7 (w : Nat) (hw : w < 2^64) :
    BitVec.ofNat 64 w &&& 7 = BitVec.ofNat 64 (w%8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw,
    show (7 : BitVec 64).toNat = 2^3-1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat]
  omega_arith

end VG.Proof.Bignum.X86_64.AdxSquare

end

end

end

/-! The full, unreduced ADX square in the Montgomery working space. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem diagonalValue_congr {m m' : Mem} {B : Addr} {eb w : Nat}
    (h : ∀ j < w, word m' B (eb + 8 * j) = word m B (eb + 8 * j)) :
    diagonalValue m' B eb w = diagonalValue m B eb w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    rw [diagonalValue_succ, diagonalValue_succ, ih (fun j hj => h j (by omega_arith)), h w (by omega_arith)]

theorem square_decomposition (m : Mem) (B : Addr) (eb w : Nat) :
    2 * crossValue m B eb w + diagonalValue m B eb w = wv m B eb w * wv m B eb w := by
  have h := Square.decomposition (2 ^ 64) (fun j => (word m B (eb + 8 * j)).toNat) w
  rw [value_words] at h
  exact (Nat.add_comm _ _).trans h.symm

/-- A diagonal: doubles the cross products at `A` and adds the squares of
the words at `eb`, for sizes `w` with `P w`. -/
structure DiagOk (diag : Prog isa) (P : Nat → Prop) : Prop where
  ok : ∀ {s : State} {B : Addr} {Z A eb w : Nat}, Scr s B Z →
    s.gpr .r8 = off B A → s.gpr .r9 = off B eb → s.gpr .r10 = BitVec.ofNat 64 w → 0 < w → w < 2^60 →
    P w → A+16*w ≤ Z → eb+8*w ≤ Z → (eb+8*w ≤ A ∨ A+16*w ≤ eb) →
    WP isa diag s fun t =>
      wv t.mem B A (2*w) + 2^(128*w)*(t.gpr .r15).toNat =
        2*wv s.mem B A (2*w) + diagonalValue s.mem B eb w ∧
      Outside B A (16*w) s.mem t.mem ∧
      Keep [.rdx,.r11,.r12,.rsi,.rbx,.rax,.rcx,.r15,.rbp,.r14] s t

theorem diagonal4_diag : DiagOk AdxSquareGrouped.diagonal (fun w => w % 4 = 0) :=
  ⟨fun hs h8 h9 h10 h0 hw h4 hA hb sep => AdxSquareGrouped.diagonal_ok hs h8 h9 h10 h0 hw h4 hA hb sep⟩

/-- All `2 w` product words are the exact square; the two high padding
words are zero. The input and header are preserved. -/
theorem rawSquareWith_ok {diag : Prog isa} {P : Nat → Prop} (hd : DiagOk diag P)
    {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw1 : 2 ≤ w) (hw : w < 2 ^ 31) (hP : P w)
    {a : Nat} (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) :
    WP isa (AdxSquare.rawSquareWith diag a) s fun t =>
      wv t.mem B (slot w aAcc + 16) (2 * w + 2) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      wv t.mem B (slot w aAcc + 16) (2 * w) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      Outside B (slot w aAcc + 16) (8 * (2 * w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  let A := slot w aAcc + 16
  let eb := slot w a
  have hA : A + 8 * (2 * w + 2) ≤ Z := by
    have := slot_le (w := w) (show aTmp < 8 by decide)
    unfold A slot aAcc aTmp at *
    omega_arith
  have hb : eb + 8 * w ≤ Z := by have := slot_le (w := w) ha; omega_arith
  have sb : eb + 8 * w ≤ A ∨ A + 8 * (2 * w + 2) ≤ eb := by
    have := slot_sep (w := w) ha1
    have := slot_sep (w := w) ha2
    unfold A eb slot aAcc aTmp at *
    omega_arith
  have hg : hdrBytes ≤ A := by unfold A slot; omega_arith
  unfold AdxSquare.rawSquareWith
  refine WP.seq (WP.mono (adxSetup_ok hs hdi hH hZ ha) fun s₁ ⟨h9₁, _, h8₁, hbx₁, hm₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (cross_ok (hs.congr k₁.2.2) h8₁ h9₁ hbx₁ hw1 (by omega_arith) hA hb sb)
    fun s₂ ⟨hv₂, ho₂, hz₂, k₂⟩ => ?_)
  rw [hm₁] at hv₂ ho₂
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.2.2
  have hH₂ := hH.of_outside ho₂ hg
  have read₂ : ∀ j < w, word s₂.mem B (eb + 8 * j) = word s.mem B (eb + 8 * j) :=
    fun j hj => ho₂.word (by omega_arith) (by omega_arith)
  have lo₂ : wv s₂.mem B A (2 * w) = crossValue s.mem B eb w := by
    have zero₂ : wv s₂.mem B (A + 8 * (2 * w)) 2 = 0 := wv_zero fun k hk => by
      rw [show A + 8 * (2 * w) + 8 * k = A + 8 * (2 * w + k) by omega_arith]
      exact hz₂ _ (by omega_arith) (by omega_arith)
    rw [wv_add, zero₂, Nat.mul_zero, Nat.add_zero] at hv₂
    exact hv₂
  refine WP.seq (WP.mono (adxSetup_ok hs₂ ((k12.gpr (by decide)).trans hdi) hH₂ hZ ha)
    fun s₃ ⟨h9₃, _, h8₃, hbx₃, hm₃, k₃⟩ => ?_)
  have mov : WP isa (.block [.mov .r10 (.reg .rbx)]) s₃ fun t =>
      t.gpr .r10 = BitVec.ofNat 64 w ∧ t.mem = s₃.mem ∧ Keep [.r10] s₃ t := by
    refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = BitVec.ofNat 64 w ∧ t.mem = s₃.mem)
      (by xrun [hbx₃]) rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  refine WP.seq (WP.mono mov fun s₄ ⟨h10₄, hm₄, k₄⟩ => ?_)
  have k14 := (k12.trans k₃).trans k₄
  refine WP.mono (hd.ok (hs.congr k14.2.2) ((k₄.gpr (by decide)).trans h8₃)
    ((k₄.gpr (by decide)).trans h9₃) h10₄ (by omega_arith) (by omega_arith) hP (by omega_arith) hb (by omega_arith))
    fun t ⟨hv, ho, kt⟩ => ?_
  rw [hm₄, hm₃] at hv ho
  rw [lo₂, diagonalValue_congr read₂, square_decomposition] at hv
  have bound : wv s.mem B eb w * wv s.mem B eb w < 2 ^ (128 * w) := by
    have hl := wv_lt s.mem B eb w
    have hp := Nat.mul_lt_mul'' hl hl
    rw [← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega_arith] at hp
    exact hp
  have carry : (t.gpr .r15).toNat = 0 := by
    by_contra hc
    have hc' : 1 ≤ (t.gpr .r15).toNat := by omega_arith
    have hm := Nat.mul_le_mul_left (2 ^ (128 * w)) hc'
    simp only [Nat.mul_one] at hm
    omega_arith
  have low : wv t.mem B A (2 * w) = wv s.mem B eb w * wv s.mem B eb w := by
    rw [carry, Nat.mul_zero, Nat.add_zero] at hv
    exact hv
  have high : wv t.mem B (A + 8 * (2 * w)) 2 = 0 := wv_zero fun k hk => by
    rw [ho.word (by omega_arith) (by omega_arith)]
    rw [show A + 8 * (2 * w) + 8 * k = A + 8 * (2 * w + k) by omega_arith]
    exact hz₂ _ (by omega_arith) (by omega_arith)
  refine ⟨?_, low, ho₂.trans (ho.mono (o' := A) (n' := 8 * (2 * w + 2)) (Nat.le_refl _) (by omega_arith)),
    (k14.trans kt).mono (by decide)⟩
  rw [wv_add, high, Nat.mul_zero, Nat.add_zero]
  exact low

end VG.Proof.Bignum.X86_64.AdxSquare
