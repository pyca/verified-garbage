module

import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareGroupedWord
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonal
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalStep
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalLoop
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega

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
  have init : WP isa (.block [.mov32 .r15 (.imm 0), .mov32 .rbp (.imm 0), .mov32 .r14 (.imm 0), .align 6]) s fun t =>
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

theorem and3 (w : Nat) (hw : w < 2^64) :
    BitVec.ofNat 64 w &&& 3 = BitVec.ofNat 64 (w%4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw,
    show (3 : BitVec 64).toNat = 2^2-1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat]
  omega_arith

theorem and7 (w : Nat) (hw : w < 2^64) :
    BitVec.ofNat 64 w &&& 7 = BitVec.ofNat 64 (w%8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw,
    show (7 : BitVec 64).toNat = 2^3-1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat]
  omega_arith

theorem test3_ok {s : State} {w : Nat} (h10 : s.gpr .r10 = BitVec.ofNat 64 w) (hw : w < 2^60) :
    WP isa (.block [.mov .rax (.reg .r10), .alu .and .rax (.imm 3), .alu .cmp .rax (.imm 0)]) s
      fun t => t.zf = some (decide (w%4=0)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.zf = some (decide (w%4=0)) ∧ t.mem = s.mem) ?_ rfl) fun t ⟨h,k⟩ => ⟨h.1,h.2,k⟩
  xrun [h10,and3 w (by omega_arith)]
  change (BitVec.ofNat 64 (w%4) - BitVec.ofNat 64 0 == 0) = _
  exact ofNat_sub_beq (by omega_arith) (by decide)

theorem test7_ok {s : State} {w : Nat} (h10 : s.gpr .r10 = BitVec.ofNat 64 w) (hw : w < 2^60) :
    WP isa (.block [.mov .rax (.reg .r10), .alu .and .rax (.imm 7), .alu .cmp .rax (.imm 0)]) s
      fun t => t.zf = some (decide (w%8=0)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.zf = some (decide (w%8=0)) ∧ t.mem = s.mem) ?_ rfl) fun t ⟨h,k⟩ => ⟨h.1,h.2,k⟩
  xrun [h10,show (BitVec.signExtend 64 (7 : BitVec 32) : BitVec 64) = 7 from rfl,and7 w (by omega_arith)]
  change (BitVec.ofNat 64 (w%8) - BitVec.ofNat 64 0 == 0) = _
  exact ofNat_sub_beq (by omega_arith) (by decide)

theorem diagonalChoice_ok {s : State} {B : Addr} {Z A eb w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B A) (h9 : s.gpr .r9 = off B eb)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 w) (hw0 : 0 < w) (hw : w < 2^60)
    (hA : A+16*w ≤ Z) (hb : eb+8*w ≤ Z)
    (sep : eb+8*w ≤ A ∨ A+16*w ≤ eb) :
    WP isa AdxSquare.diagonalChoice s fun t =>
      wv t.mem B A (2*w) + 2^(128*w)*(t.gpr .r15).toNat =
        2*wv s.mem B A (2*w) + diagonalValue s.mem B eb w ∧
      Outside B A (16*w) s.mem t.mem ∧
      Keep [.rdx,.r11,.r12,.rsi,.rbx,.rax,.rcx,.r15,.rbp,.r14] s t := by
  unfold AdxSquare.diagonalChoice
  refine WP.seq (WP.mono (test7_ok h10 hw) fun a ⟨hz,hm,ka⟩ => ?_)
  by_cases h8w : w%8=0
  · refine WP.ite true (by simp [eval,hz,h8w]) (fun _ => ?_) (by simp)
    refine WP.mono (AdxSquareGrouped.diagonal8_ok (hs.congr ka.2.2)
      ((ka.gpr (by decide)).trans h8) ((ka.gpr (by decide)).trans h9)
      ((ka.gpr (by decide)).trans h10) hw0 hw h8w hA hb sep) fun t ⟨hv,ho,kt⟩ => ?_
    rw [hm] at hv ho
    exact ⟨hv,ho,(ka.trans kt).mono (by decide)⟩
  · refine WP.ite false (by simp [eval,hz,h8w]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (test3_ok ((ka.gpr (by decide)).trans h10) hw)
      fun b ⟨hzb,hmb,kb⟩ => ?_)
    have kab := ka.trans kb
    have hmab : b.mem = s.mem := hmb.trans hm
    by_cases h4 : w%4=0
    · refine WP.ite true (by simp [eval,hzb,h4]) (fun _ => ?_) (by simp)
      refine WP.mono (AdxSquareGrouped.diagonal_ok (hs.congr kab.2.2)
        ((kab.gpr (by decide)).trans h8) ((kab.gpr (by decide)).trans h9)
        ((kab.gpr (by decide)).trans h10) hw0 hw h4 hA hb sep) fun t ⟨hv,ho,kt⟩ => ?_
      rw [hmab] at hv ho
      exact ⟨hv,ho,(kab.trans kt).mono (by decide)⟩
    · refine WP.ite false (by simp [eval,hzb,h4]) (by simp) (fun _ => ?_)
      refine WP.mono (diagonal_ok (hs.congr kab.2.2)
        ((kab.gpr (by decide)).trans h8) ((kab.gpr (by decide)).trans h9)
        ((kab.gpr (by decide)).trans h10) hw0 hw hA hb sep) fun t ⟨hv,ho,kt⟩ => ?_
      rw [hmab] at hv ho
      exact ⟨hv,ho,(kab.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.X86_64.AdxSquare

end
