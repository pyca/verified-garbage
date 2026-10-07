import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Sym
import VerifiedGarbage.Impl.Rsa.X86_64.Crt
import VerifiedGarbage.Proof.Bignum.Amm52
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.X86_64.StraightY
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSA with AVX512_IFMA on x86-64: lemmas

What the proofs of `CrtIfma` use that does not depend on the
layout: symbolic execution of the vector instructions (the lanes of a
`vpmadd52luq`/`vpmadd52huq` and of the moves between registers and memory),
writes of 32 bytes and of runs of `rax`, frames, MXCSR's bits, `2⁵²`-radix
numbers in memory, and the conditional subtraction's result.
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi xi_inj qw qword_paddq qword_psrlq pick2 sel4 sel4_lt
  qw_setV256 qw_lane lane_sel qw_vbin qw_vshift qw_vpblendd qw_vpbroadcastq qw_vmovq qw_vpermq hv_of
  mod2_lt qword256_eq)
open VG.Proof.X25519.X86_64.Ifma (mad52 qword_madd52)

/-! ## Terms -/

/-- A quadword of a general-purpose register, in terms of the start. -/
inductive G
  | gpr (r : Reg)
  /-- The quadword at `b + d`. -/
  | ld (b : Reg) (d : Nat)
  deriving DecidableEq, Repr

def G.eval (s₀ : State) : G → BitVec 64
  | .gpr r => s₀.gpr r
  | .ld b d => s₀.mem.readW (s₀.gpr b + BitVec.ofNat 64 d) 64

/-! ## The machine -/

/-- The base and offset of `[b + d]`. -/
def baseOff (m : MemOp) : Option (Reg × Nat) :=
  if m.index = none then
    match m.disp with
    | .ofNat n => some (m.base, n)
    | _ => none
  else none

/-! ## The machine agrees -/

/-- The bytes the code may load: `lim b` bytes from each base `b`. -/
def Ctx (lim : Reg → Nat) (s₀ : State) : Prop :=
  ∀ b d n, 0 < n → d + n ≤ lim b → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr b + BitVec.ofNat 64 d) n

theorem baseOff_ok {m : MemOp} {b : Reg} {o : Nat} (h : baseOff m = some (b, o)) (s : State) :
    s.ea m = s.gpr b + BitVec.ofNat 64 o := by
  unfold baseOff at h
  split at h
  · rename_i hi
    split at h
    · rename_i n hn
      cases h
      simp only [State.ea, hi, hn]
      exact congrArg _ (BitVec.ofInt_natCast ..)
    · cases h
  · cases h

end VG.Proof.Bignum.X86_64.AmmSym

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw pick2 sel4)
open VG.Proof.X25519.X86_64.Ifma (mad52 mad52_toNat)

/-- The operands of prime `p`. -/
def ops (a m : Nat → Nat → Nat) (k : Nat → Nat) (p : Nat) : Ops := ⟨a p, m p, k p⟩

theorem lo_comm (x y : Nat) : lo x y = lo y x := by unfold lo; rw [Nat.mul_comm]

theorem mad_lo {c x y : Nat} (hc : c + 2 ^ 52 < 2 ^ 64) :
    mad52 false (BitVec.ofNat 64 c) (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) =
      BitVec.ofNat 64 (c + lo y x) := by
  apply BitVec.eq_of_toNat_eq
  have := lo_lt y x
  rw [mad52_toNat]
  simp only [Bool.false_eq_true, ite_false, BitVec.toNat_ofNat]
  have e : ∀ v : Nat, v % 2 ^ 64 % 2 ^ 52 = v % 2 ^ 52 := fun v => Nat.mod_mod_of_dvd _ (by decide)
  rw [e, e, Nat.mul_comm, show y % 2 ^ 52 * (x % 2 ^ 52) % 2 ^ 52 = lo y x from rfl]
  rw [Nat.mod_eq_of_lt (show c % 2 ^ 64 + lo y x < 2 ^ 64 by
    have := Nat.mod_le c (2 ^ 64); omega), Nat.mod_eq_of_lt (show c + lo y x < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]

theorem mad_hi {c x y : Nat} (hc : c + 2 ^ 52 < 2 ^ 64) :
    mad52 true (BitVec.ofNat 64 c) (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) =
      BitVec.ofNat 64 (c + hi y x) := by
  apply BitVec.eq_of_toNat_eq
  have := hi_lt y x
  rw [mad52_toNat]
  simp only [ite_true, BitVec.toNat_ofNat]
  have e : ∀ v : Nat, v % 2 ^ 64 % 2 ^ 52 = v % 2 ^ 52 := fun v => Nat.mod_mod_of_dvd _ (by decide)
  rw [e, e, Nat.mul_comm, show y % 2 ^ 52 * (x % 2 ^ 52) / 2 ^ 52 = hi y x from rfl]
  rw [Nat.mod_eq_of_lt (show c % 2 ^ 64 + hi y x < 2 ^ 64 by
    have := Nat.mod_le c (2 ^ 64); omega), Nat.mod_eq_of_lt (show c + hi y x < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]

section
variable {s : State} {i : Nat} {L a m : Nat → Nat → Nat} {k b : Nat → Nat}

theorem shr_ofNat {x : Nat} (hx : x < 2 ^ 64) : BitVec.ofNat 64 x >>> 52 = BitVec.ofNat 64 (x / 2 ^ 52) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

theorem add_ofNat {x y : Nat} (h : x + y < 2 ^ 64) :
    BitVec.ofNat 64 x + BitVec.ofNat 64 y = BitVec.ofNat 64 (x + y) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show y < 2 ^ 64 by omega)]

end

end VG.Proof.Bignum.X86_64.AmmSym

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw)

/-- What a step keeps: everything but the vector registers and `rax`. -/
structure Keeps (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mxcsr : s'.mxcsr = s.mxcsr
  flags : s'.cf = s.cf ∧ s'.zf = s.zf ∧ s'.sf = s.sf ∧ s'.of = s.of

/-! ## The steps of a block -/

theorem ofNat_add64 (x : BitVec 64) (c d : Nat) :
    x + BitVec.ofNat 64 c + BitVec.ofNat 64 d = x + BitVec.ofNat 64 (c + d) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

end VG.Proof.Bignum.X86_64.AmmSym

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside ofs_off writeW_outside word_writeW_self)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw qword256_ymm)
open VG.Impl.Rsa.X86_64.CrtIfma (mask52)

/-! ## Writes of 32 bytes -/

/-- Writes `(e, v)` at `B + e`, the first first. -/
def wrList (m : Mem) (B : Addr) : List (Nat × BitVec 256) → Mem
  | [] => m
  | (e, v) :: rest => wrList (m.writeW (off B e) v) B rest

theorem writeW256_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 256) (h : d + 32 ≤ 2 ^ 64) :
    Outside base d 32 m (m.writeW (off base d) v) := by
  intro x hx
  apply Mem.write_apply
  simp only [ofs] at hx
  have : (x - off base d).toNat = (2 ^ 64 - d + (x - base).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x base (by omega)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- A word that no write of the list touches. -/
theorem word_wrList_other (B : Addr) :
    ∀ (l : List (Nat × BitVec 256)) (m : Mem) {d : Nat}, d + 8 ≤ 2 ^ 63 →
      (∀ x ∈ l, x.1 + 32 ≤ 2 ^ 63 ∧ (d + 8 ≤ x.1 ∨ x.1 + 32 ≤ d)) → word (wrList m B l) B d = word m B d
  | [], _, _, _, _ => rfl
  | (e, v) :: rest, m, d, hd, h => by
    have he := h (e, v) (List.mem_cons_self ..)
    rw [wrList, word_wrList_other B rest _ hd fun x hx => h x (List.mem_cons_of_mem _ hx)]
    exact (writeW256_outside m B v (by omega)).word (by omega) (by omega)

/-- The word at `e + 8 t` of the write `(e, v)`, after writes elsewhere. -/
theorem word_wrList_hit (B : Addr) (m : Mem) (l₁ l₂ : List (Nat × BitVec 256)) {e t : Nat} (v : BitVec 256)
    (ht : t < 4) (he : e + 32 ≤ 2 ^ 63)
    (h : ∀ x ∈ l₂, x.1 + 32 ≤ 2 ^ 63 ∧ (e + 8 * t + 8 ≤ x.1 ∨ x.1 + 32 ≤ e + 8 * t)) :
    word (wrList m B (l₁ ++ (e, v) :: l₂)) B (e + 8 * t) = v.extractLsb' (64 * t) 64 := by
  induction l₁ generalizing m with
  | nil =>
    rw [List.nil_append, wrList, word_wrList_other B l₂ _ (by omega) h]
    have := readW_writeW_inside m (off B e) v (k := 8 * t) (n := 8) (by omega) (by decide)
    simp only [word, off] at this ⊢
    rw [← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, this, show 8 * (8 * t) = 64 * t by omega]
  | cons x l₁ ih => exact ih _

/-! ## The stores -/

/-- The word at `e + 8 t` after writes of which only `(e, v)` touch it. -/
theorem word_wrList_unique (B : Addr) {e t : Nat} {v : BitVec 256} (ht : t < 4) (he : e + 32 ≤ 2 ^ 63) :
    ∀ (l : List (Nat × BitVec 256)) (m : Mem), (e, v) ∈ l →
      (∀ x ∈ l, x.1 + 32 ≤ 2 ^ 63 ∧ (x.1 = e ∨ e + 32 ≤ x.1 ∨ x.1 + 32 ≤ e)) → (∀ x ∈ l, x.1 = e → x.2 = v) →
      word (wrList m B l) B (e + 8 * t) = v.extractLsb' (64 * t) 64
  | [], _, h, _, _ => absurd h (List.not_mem_nil)
  | (e', v') :: rest, m, hm, hd, hv => by
    by_cases hr : (e, v) ∈ rest
    · rw [wrList]
      exact word_wrList_unique B ht he rest _ hr (fun x hx => hd x (List.mem_cons_of_mem _ hx))
        (fun x hx => hv x (List.mem_cons_of_mem _ hx))
    · have h0 : (e, v) = (e', v') := by
        rcases List.mem_cons.1 hm with h | h
        · exact h
        · exact absurd h hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0
      have := word_wrList_hit B m [] rest (e := e) (t := t) v ht he (fun x hx => by
        refine ⟨(hd x (List.mem_cons_of_mem _ hx)).1, ?_⟩
        rcases (hd x (List.mem_cons_of_mem _ hx)).2 with h | h | h
        · exact absurd (by rw [← hv x (List.mem_cons_of_mem _ hx) h]; exact h ▸ hx) hr
        · omega
        · omega)
      simpa only [List.nil_append] using this

/-! ## The carries -/

theorem and_mask {y : Nat} (hy : y < 2 ^ 64) : BitVec.ofNat 64 y &&& mask52 = BitVec.ofNat 64 (y % 2 ^ 52) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show mask52.toNat = 2 ^ 52 - 1 from rfl]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hy, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (show y % 2 ^ 52 < 2 ^ 64 by omega)]

/-- `s'` is `s` with `r := v`, and maybe other flags. -/
structure Upd (s s' : State) (r : Reg) (v : BitVec 64) : Prop where
  self : s'.gpr r = v
  other : ∀ r', r' ≠ r → s'.gpr r' = s.gpr r'
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mxcsr : s'.mxcsr = s.mxcsr

theorem upd_setReg (t : State) (r : Reg) (v : BitVec 64) (s : State) (hg : t.gpr = s.gpr) (hm : t.mem = s.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hx : t.mxcsr = s.mxcsr) : Upd s (t.setReg r v) r v :=
  ⟨RegUpd.gpr_setReg_self _ _ _, fun r' h => by rw [RegUpd.gpr_setReg_of_ne _ _ h, hg], hm, hrd, hwr, hx⟩

theorem ex_add_mem {s : State} {r : Reg} {m : MemOp} (hin : InRegions (s.rd ++ s.wr) (s.ea m) 8) :
    ∃ s', exec (.alu .add r (.mem m)) s = some s' ∧ Upd s s' r (s.gpr r + s.mem.readW (s.ea m) 64) :=
  ⟨_, by simp only [exec, execAlu, readSrc, State.load64, hin, ite_true, Option.bind_some]; rfl,
    upd_setReg (arithFlags s _ _ _) _ _ _ rfl rfl rfl rfl rfl⟩

theorem ex_mov {s : State} {d r : Reg} : ∃ s', exec (.mov d (.reg r)) s = some s' ∧ Upd s s' d (s.gpr r) :=
  ⟨_, rfl, upd_setReg _ _ _ _ rfl rfl rfl rfl rfl⟩

theorem ex_and {s : State} {d r : Reg} :
    ∃ s', exec (.alu .and d (.reg r)) s = some s' ∧ Upd s s' d (s.gpr d &&& s.gpr r) :=
  ⟨_, rfl, upd_setReg _ _ _ _ rfl rfl rfl rfl rfl⟩

theorem ex_shr {s : State} {d : Reg} : ∃ s', exec (.shift .shr d 52) s = some s' ∧ Upd s s' d (s.gpr d >>> 52) :=
  ⟨_, by simp only [exec, execShift, show (1 ≤ 52 ∧ 52 ≤ 63) by decide, and_self, ite_true],
    upd_setReg (s.setFlags (some ((s.gpr d).getLsbD (52 - 1))) (if 52 = 1 then some (s.gpr d).msb else none)
      (some (s.gpr d >>> 52 == 0)) (some (s.gpr d >>> 52).msb)) _ _ _ rfl rfl rfl rfl rfl⟩

theorem ex_store {s : State} {m : MemOp} {r : Reg} (hin : InRegions s.wr (s.ea m) 8) :
    ∃ s', exec (.store m r) s = some s' ∧ s'.mem = s.mem.writeW (s.ea m) (s.gpr r) ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr :=
  ⟨{ s with mem := s.mem.writeW (s.ea m) (s.gpr r) }, by simp only [exec, State.store64, hin, ite_true],
    rfl, rfl, rfl, rfl, rfl⟩

theorem add_ofNat' {x y : Nat} (h : x + y < 2 ^ 64) :
    BitVec.ofNat 64 x + BitVec.ofNat 64 y = BitVec.ofNat 64 (x + y) := add_ofNat h

/-! ## The whole multiplication -/

/-- Writes of 32 bytes below `n` leave the rest. -/
theorem wrList_outside (B : Addr) {n : Nat} (hn : n ≤ 2 ^ 63) :
    ∀ (l : List (Nat × BitVec 256)) (m : Mem), (∀ x ∈ l, x.1 + 32 ≤ n) → Outside B 0 n m (wrList m B l)
  | [], m, _ => Outside.refl B 0 n m
  | (e, v) :: rest, m, h => by
    have he := h (e, v) (List.mem_cons_self ..)
    exact ((writeW256_outside m B v (by omega)).mono (by omega) (by omega)).trans
      (wrList_outside B hn rest _ fun x hx => h x (List.mem_cons_of_mem _ hx))

end VG.Proof.Bignum.X86_64.AmmSym

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off)
open VG.Proof.Bignum.X86_64 (Scr)

theorem se_ofNat {c : Nat} (h : c < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 c) = BitVec.ofNat 64 c := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false (by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp; omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem off_add (B : Addr) (a d : Nat) : off B a + BitVec.ofNat 64 d = off B (a + d) := off_off B a d

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- `r := rbx + c`. -/
theorem setOff {s : State} {r : Reg} {c : Nat} {rest : List Instr} {Q : State → Prop} (hc : c < 2 ^ 31)
    (h : ∀ s', Upd s s' r (off (s.gpr .rbx) c) → WP isa (.block rest) s' Q) :
    WP isa (.block (.mov r (.reg .rbx) :: .alu .add r (.imm (BitVec.ofNat 32 c)) :: rest)) s Q := by
  rw [WP.block_cons_iff]
  refine ⟨s.setReg r (s.gpr .rbx), rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, h _ ⟨?_, fun r' hr' => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_self, se_ofNat hc]
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr', RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr']

theorem ofs_rebase' (B x : Addr) {o : Nat} (ho : o < 2 ^ 64) :
    (o ≤ ofs B x ∧ ofs (off B o) x = ofs B x - o) ∨ (ofs B x < o ∧ 2 ^ 64 - o ≤ ofs (off B o) x) := by
  simp only [ofs, off]
  rw [Offset.toNat_sub_add x B ho]
  have := (x - B).isLt
  by_cases h : o ≤ (x - B).toNat
  · left
    refine ⟨h, ?_⟩
    rw [show 2 ^ 64 - o + (x - B).toNat = (x - B).toNat - o + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · right
    refine ⟨by omega, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

end VG.Proof.Bignum.X86_64.AmmSym

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw qword256_ymm qw_vbin qw_vpbroadcastq qw_vmovq qw_load qw_lane qword_and
  qword_or)
open VG.Proof.MlKem.X86_64 (Keep)

/-- All ones if `c`. -/
def selMask (c : Bool) : BitVec 64 := if c then BitVec.allOnes 64 else 0

theorem lt_one_iff (x : BitVec 64) : decide (x.toNat < (1 : BitVec 64).toNat) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, ← BitVec.toNat_inj,
    show (1 : BitVec 64).toNat = 1 from rfl, show (0 : BitVec 64).toNat = 0 from rfl]
  constructor <;> intro h <;> omega

theorem xor_zero_iff {x y : BitVec 64} : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h
    have := congrArg (· ^^^ y) h
    simpa [BitVec.xor_assoc] using this
  · rintro rfl
    simp

theorem ofNat64_inj' {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · rintro rfl; rfl

/-- The mask of entry `i`. -/
theorem selMask_ok {s : State} {i v : Nat} (hi : i < 16) (hv : v < 16)
    (hc : s.gpr .rcx = BitVec.ofNat 64 i) (hd : s.gpr .rdx = BitVec.ofNat 64 v) :
    WP isa (.block [.mov .rax (.reg .rcx), .alu .xor .rax (.reg .rdx), .alu .cmp .rax (.imm 1),
      .alu .sbb .rax (.reg .rax)]) s fun s' => s'.gpr .rax = selMask (decide (i = v)) ∧ Keep [.rax] s s' ∧
        s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun s' => s'.gpr .rax = selMask (decide (i = v)) ∧
    s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mxcsr = s.mxcsr) (by
    xrun [hc, hd]
    and_intros
    any_goals rfl
    rw [lt_one_iff, show decide (BitVec.ofNat 64 i ^^^ BitVec.ofNat 64 v = 0) = decide (i = v) from
      decide_eq_decide.mpr (xor_zero_iff.trans (ofNat64_inj' (by omega) (by omega)))]
    cases decide (i = v) <;> rfl) rfl) fun s' ⟨⟨h, m, x, y, z⟩, k⟩ => ⟨h, k, m, x, y, z⟩

theorem selMask_and (w : BitVec 64) (c : Bool) : (w &&& selMask c) = if c then w else 0 := by
  cases c
  · simp [selMask]
  · simp only [selMask, ite_true, BitVec.and_allOnes]

theorem zero_or64 (x : BitVec 64) : 0 ||| x = x := by simp
theorem or_zero64 (x : BitVec 64) : x ||| 0 = x := by simp

theorem shr60 (w : BitVec 64) : w >>> 60 = BitVec.ofNat 64 (w.toNat / 2 ^ 60) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by have := w.isLt; omega)]

/-- Writes of 32 bytes within `[o, o + n)` leave the rest. -/
theorem wrList_outside' (B : Addr) {o n : Nat} (hn : o + n ≤ 2 ^ 63) :
    ∀ (l : List (Nat × BitVec 256)) (m : Mem), (∀ x ∈ l, o ≤ x.1 ∧ x.1 + 32 ≤ o + n) →
      Outside B o n m (wrList m B l)
  | [], m, _ => Outside.refl B o n m
  | (e, v) :: rest, m, h => by
    have he := h (e, v) (List.mem_cons_self ..)
    exact ((writeW256_outside m B v (by omega)).mono he.1 (by omega)).trans
      (wrList_outside' B hn rest _ fun x hx => h x (List.mem_cons_of_mem _ hx))

end VG.Proof.Bignum.X86_64.AmmSym

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off)
open VG.Proof.Bignum.X86_64 (Scr)

/-- A Montgomery product of `T ≡ x^E R` and `X ≡ x^v R`: `x^(E+v) R`. -/
theorem mont_mul2 {T T' X x E v R m : Nat} (hR : Nat.Coprime R m) (hT : T % m = x ^ E * R % m)
    (hX : X % m = x ^ v * R % m) (h : T' * R % m = T * X % m) : T' % m = x ^ (E + v) * R % m := by
  apply VG.Proof.Bignum.mont_cancel hR
  rw [h, Nat.mul_mod, hT, hX, ← Nat.mul_mod, Nat.pow_add]
  congr 1
  grind

end VG.Proof.Bignum.X86_64.AmmSym

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off)
open VG.Proof.Bignum.X86_64 (Scr)

/-- A word of 32 bytes outside a write of 32 bytes. -/
theorem readW256_outside {m m' : Mem} {B : Addr} {d e : Nat} (h : Outside B d 32 m m')
    (he : e + 32 ≤ d ∨ d + 32 ≤ e) (he' : e + 32 ≤ 2 ^ 64) : m'.readW (off B e) 256 = m.readW (off B e) 256 :=
  (Mem.readW_congr fun i hi => (h _ (by have : i < 32 := hi; rw [ofs_off B (by omega)]; omega)).symm).symm

end VG.Proof.Bignum.X86_64.AmmSym

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside)
open VG.Proof.Bignum.X86_64 (Scr)

/-- The squarings' count down, `ZF` at 0. -/
theorem r15Dec_ok {s : State} {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 4) (h15 : s.gpr .r15 = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .sub .r15 (.imm 1)]) s fun s' =>
      s'.gpr .r15 = BitVec.ofNat 64 (n - 1) ∧ s'.zf = some (decide (n - 1 = 0)) ∧
      VG.Proof.MlKem.X86_64.Keep [.r15] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r15] (Q := fun s' =>
    s'.gpr .r15 = BitVec.ofNat 64 (n - 1) ∧ s'.zf = some (decide (n - 1 = 0)) ∧ s'.mem = s.mem ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [h15]
    have e : BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1) := by
      rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← VG.Offset.ofNat_sub_ofNat hn]
    and_intros
    · exact e
    · rw [e]; congr 1
      by_cases h : n - 1 = 0
      · simp only [h, decide_true]; rfl
      · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
        intro h'
        have := congrArg BitVec.toNat h'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact h this
    all_goals rfl) rfl)
    fun s' ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, k, c, d⟩

theorem ea_at' (t : State) (r : Reg) (d : Nat) :
    t.ea (VG.Impl.Rsa.X86_64.CrtIfma.at_ r d) = t.gpr r + BitVec.ofNat 64 d := by
  simp only [State.ea, VG.Impl.Rsa.X86_64.CrtIfma.at_]
  exact congrArg _ (BitVec.ofInt_natCast ..)

theorem wp_seqs_app {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) {s : State} {Q : State → Prop}
    (h : WP isa (VG.Impl.Bignum.X86_64.seqs a) s fun t => WP isa (VG.Impl.Bignum.X86_64.seqs b) t Q) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (a ++ b)) s Q := by
  induction a generalizing s with
  | nil => exact absurd rfl ha
  | cons c a ih =>
    cases a with
    | nil =>
      obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hb
      exact WP.seq h
    | cons d rest =>
      simp only [VG.Impl.Bignum.X86_64.seqs, List.cons_append] at h ⊢
      exact WP.seq (WP.mono (WP.seq_iff.mp h) fun t ht => ih (by simp) ht)

end VG.Proof.Bignum.X86_64.AmmSym

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside)
open VG.Proof.Bignum.X86_64 (Scr)

theorem ror8_byte : ∀ b : BitVec 8, (b.setWidth 64).rotateRight 8 = BitVec.ofNat 64 (b.toNat * 2 ^ 56) := by
  decide +kernel

theorem ror60_v : ∀ b < 256, (BitVec.ofNat 64 (b * 2 ^ 56)).rotateRight 60 =
    BitVec.ofNat 64 (b % 16 * 2 ^ 60 + b / 16) := by
  decide +kernel

theorem ea_idx (t : State) (d : Nat) :
    t.ea { base := .rbx, index := some .r13, disp := ((d : Nat) : Int) } =
      t.gpr .rbx + t.gpr .r13 + BitVec.ofNat 64 d := by
  simp only [State.ea, BitVec.mul_one]
  exact congrArg _ (BitVec.ofInt_natCast ..)

/-- The windows' count down, `ZF` at 0. -/
theorem r14Dec_ok {s : State} {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 2) (h14 : s.gpr .r14 = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .sub .r14 (.imm 1)]) s fun s' =>
      s'.gpr .r14 = BitVec.ofNat 64 (n - 1) ∧ s'.zf = some (decide (n - 1 = 0)) ∧
      VG.Proof.MlKem.X86_64.Keep [.r14] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r14] (Q := fun s' =>
    s'.gpr .r14 = BitVec.ofNat 64 (n - 1) ∧ s'.zf = some (decide (n - 1 = 0)) ∧ s'.mem = s.mem ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [h14]
    have e : BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1) := by
      rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← VG.Offset.ofNat_sub_ofNat hn]
    and_intros
    · exact e
    · rw [e]; congr 1
      by_cases h : n - 1 = 0
      · simp only [h, decide_true]; rfl
      · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
        intro h'
        have := congrArg BitVec.toNat h'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact h this
    all_goals rfl) rfl)
    fun s' ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, k, c, d⟩

/-- `V` before window `j` of the byte `b`. -/
def vj (b j : Nat) : Nat := if j = 0 then b * 2 ^ 56 else b % 16 * 2 ^ 60 + b / 16

theorem win_exp {E b j : Nat} (hb : b < 256) (hj : j < 2) (n : Nat) (hn : n = if j = 0 then b / 16 else b % 16) :
    (E * 16 ^ j + b / 16 ^ (2 - j)) * 16 + n = E * 16 ^ (j + 1) + b / 16 ^ (2 - (j + 1)) := by
  subst hn
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceAdd,
    ite_true, ite_false, Nat.one_ne_zero] <;> omega

theorem ofs_off0 (B : Addr) {d : Nat} (h : d < 2 ^ 64) : ofs B (off B d) = d := by
  simp only [ofs, off, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

end VG.Proof.Bignum.X86_64.AmmSym

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside)
open VG.Proof.Bignum.X86_64 (Scr)

theorem Scr.mono {s : State} {B : Addr} {Z Z' : Nat} (h : Scr s B Z) (hz : Z' ≤ Z) : Scr s B Z' :=
  let ⟨B₀, o, L, hm, hb, hL, hL'⟩ := h.wr
  ⟨⟨B₀, o, L, hm, hb, by omega, hL'⟩, by have := h.nowrap; omega⟩

theorem and_ffff_hi (x : BitVec 32) : (x &&& 0xFFFF).extractLsb' 16 16 = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, hi, decide_true, Bool.true_and]
  rw [show (0xFFFF : BitVec 32) = BitVec.ofNat 32 (2 ^ 16 - 1) from rfl, BitVec.getLsbD_ofNat]
  simp only [Nat.testBit_two_pow_sub_one]
  simp

/-- Into Montgomery form: `X ≡ a c`, `K ≡ d` with `c d = R²` give `X K / R ≡ a R`. -/
theorem mont_into {X K X' a c d R m : Nat} (hR : Nat.Coprime R m) (hX : X % m = a * c % m) (hK : K % m = d % m)
    (e : c * d = R * R) (h : X' * R % m = X * K % m) : X' % m = a * R % m := by
  apply VG.Proof.Bignum.mont_cancel hR
  rw [h, Nat.mul_mod, hX, hK, ← Nat.mul_mod]
  congr 1
  rw [Nat.mul_assoc, e, Nat.mul_assoc]

theorem mont_into0 {X K X' c d R m y : Nat} (hR : Nat.Coprime R m) (hX : X % m = 1 * c % m)
    (hK : K % m = d % m) (e : c * d = R * R) (h : X' * R % m = X * K % m) : X' % m = y ^ 0 * R % m := by
  rw [Nat.pow_zero]; exact mont_into hR hX hK e h

theorem mont_into1 {X K X' a c d R m : Nat} (hR : Nat.Coprime R m) (hX : X % m = a * c % m)
    (hK : K % m = d % m) (e : c * d = R * R) (h : X' * R % m = X * K % m) : X' % m = a ^ 1 * R % m := by
  rw [Nat.pow_one]; exact mont_into hR hX hK e h

/-- Out of Montgomery form: `Y ≡ b R` gives `Y F / R ≡ b F`. -/
theorem mont_out {Y F Y' b R m : Nat} (hR : Nat.Coprime R m) (hY : Y % m = b * R % m)
    (h : Y' * R % m = Y * F % m) : Y' % m = b * F % m := by
  apply VG.Proof.Bignum.mont_cancel hR
  rw [h, Nat.mul_mod, hY, ← Nat.mul_mod]
  congr 1
  grind

/-! ## Writes above both regions -/

theorem writeW32_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 32) (h : d + 4 ≤ 2 ^ 64) :
    Outside base d 4 m (m.writeW (off base d) v) := by
  intro x hx
  apply Mem.write_apply
  simp only [ofs] at hx
  have : (x - off base d).toNat = (2 ^ 64 - d + (x - base).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x base (by omega)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

theorem _root_.VG.Proof.Bignum.Outside.readW32 {B : Addr} {o n : Nat} {m m' : Mem} (h : Outside B o n m m') {d : Nat}
    (hd : d + 4 ≤ o ∨ o + n ≤ d) (hd' : d + 4 ≤ 2 ^ 64) : m'.readW (off B d) 32 = m.readW (off B d) 32 :=
  (Mem.readW_congr fun i hi => (h _ (by have : i < 4 := hi; rw [ofs_off B (by omega)]; omega)).symm).symm

end VG.Proof.Bignum.X86_64.AmmSym

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside wv)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Impl.Rsa.X86_64.CrtIfma (mask52)

theorem testBit_hiMask {t i : Nat} (ht : t ≤ 64) (hi : i < 64) : (2 ^ 64 - 2 ^ t).testBit i = decide (t ≤ i) := by
  rw [show 2 ^ 64 - 2 ^ t = (2 ^ (64 - t) - 1) * 2 ^ t by
    rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel ht]]
  rw [Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases h : t ≤ i
  · simp only [h, decide_true, Bool.true_and]; exact decide_eq_true (by omega)
  · simp only [h, decide_false, Bool.false_and]

/-- `shl r t`: rotated right by `64 - t`, its low `t` bits cleared. -/
theorem shl_eq' (x : BitVec 64) {t : Nat} (h1 : 1 ≤ t) (h2 : t ≤ 63) :
    x.rotateRight (64 - t) &&& BitVec.ofNat 64 (2 ^ 64 - 2 ^ t) = x <<< t := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and,
    testBit_hiMask (show t ≤ 64 by omega) hi]
  by_cases h : i < t
  · simp [h, show ¬ t ≤ i by omega]
  · rw [BitVec.getLsbD_rotateRight_of_lt (by omega)]
    simp only [show t ≤ i by omega, decide_true, Bool.and_true, h, decide_false, Bool.not_false, Bool.true_and]
    rw [show 64 - (64 - t) = t by omega]
    simp [h, hi]

theorem drop_hi (a k y : Nat) (hk : 52 ≤ k) : (a + 2 ^ k * y) % 2 ^ 52 = a % 2 ^ 52 := by
  rw [show 2 ^ k = 2 ^ 52 * 2 ^ (k - 52) by rw [← Nat.pow_add, Nat.add_sub_cancel' hk], Nat.mul_assoc,
    Nat.add_mul_mod_self_left]

theorem div_split (a c s : Nat) (hs : s ≤ 64) : (a + 2 ^ 64 * c) / 2 ^ s = a / 2 ^ s + 2 ^ (64 - s) * c := by
  rw [show 2 ^ 64 * c = 2 ^ s * (2 ^ (64 - s) * c) by rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' hs],
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]

/-- A limb across two words, as the code assembles it. -/
theorem or_shr_shl (x y : BitVec 64) {s : Nat} (h1 : 1 ≤ s) (h2 : s ≤ 63) :
    (x >>> s ||| y <<< (64 - s)).toNat = x.toNat / 2 ^ s + y.toNat * 2 ^ (64 - s) % 2 ^ 64 := by
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  have hx : x.toNat / 2 ^ s < 2 ^ (64 - s) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.sub_add_cancel (by omega)]; exact x.isLt
  have e : y.toNat * 2 ^ (64 - s) % 2 ^ 64 = (y.toNat % 2 ^ s) * 2 ^ (64 - s) := by
    rw [show 2 ^ 64 = 2 ^ s * 2 ^ (64 - s) by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)],
      Nat.mul_mod_mul_right]
  rw [e, ← Nat.shiftLeft_eq, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.add_comm]

theorem and_mask' (x : BitVec 64) : x &&& mask52 = BitVec.ofNat 64 (x.toNat % 2 ^ 52) := by
  rw [← and_mask x.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem mod52_of_mod64 (X Y : Nat) : (X + Y % 2 ^ 64) % 2 ^ 52 = (X + Y) % 2 ^ 52 := by
  rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (show 2 ^ 52 ∣ 2 ^ 64 from Nat.pow_dvd_pow 2 (by decide)), ← Nat.add_mod]

theorem wv_one {m : Mem} {A : Addr} {d k : Nat} (hk : 1 ≤ k) :
    wv m A d k = (word m A d).toNat + 2 ^ 64 * wv m A (d + 8) (k - 1) := by
  have e := VG.Proof.Bignum.wv_add m A d 1 (k - 1)
  rw [show 1 + (k - 1) = k by omega] at e
  rw [e]
  simp only [VG.Proof.Bignum.wv, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.mul_one,
    Nat.add_zero]

/-- Limb `j` of `N`. -/
def limbN (N j : Nat) : Nat := N / 2 ^ (52 * j) % 2 ^ 52

/-! ## Back to words -/

/-- Limb `j`'s part of the word at bit `lo`. -/
def cj (lo j : Nat) (L : BitVec 64) : BitVec 64 :=
  if lo ≤ 52 * j then (if 52 * j = lo then L else L <<< (52 * j - lo)) else L >>> (lo - 52 * j)

theorem testBit_hi {x k j : Nat} (hx : x < 2 ^ k) (hj : k ≤ j) : x.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hj))

/-- Bit `i` of limb `j`'s part of the word at bit `lo`. -/
theorem cj_bit {lo j : Nat} {L : BitVec 64} (h1 : 52 * j < lo + 64) (h2 : lo < 52 * j + 52)
    {i : Nat} (hi : i < 64) :
    (cj lo j L).getLsbD i = (decide (52 * j ≤ lo + i) && L.toNat.testBit (lo + i - 52 * j)) := by
  unfold cj
  by_cases hl : lo ≤ 52 * j
  · by_cases he : 52 * j = lo
    · subst he
      simp [BitVec.testBit_toNat]
    · simp only [hl, he, ite_true, ite_false, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and,
        BitVec.testBit_toNat]
      by_cases hk : i < 52 * j - lo
      · simp [hk, show ¬ 52 * j ≤ lo + i by omega]
      · simp only [hk, decide_false, Bool.not_false, Bool.true_and, show 52 * j ≤ lo + i by omega, decide_true]
        congr 1; omega
  · simp only [hl, ite_false, BitVec.getLsbD_ushiftRight, show 52 * j ≤ lo + i by omega, decide_true,
      Bool.true_and, BitVec.testBit_toNat]
    congr 1; omega

/-- The bits of a number of limbs below `2⁵²`. -/
theorem testBit_lval {L : Nat → Nat} (hL : ∀ j, L j < 2 ^ 52) :
    ∀ n b, (lval L n).testBit b = (decide (b < 52 * n) && (L (b / 52)).testBit (b % 52))
  | 0, b => by rw [lval_zero]; simp
  | n + 1, b => by
    rw [lval_succ, Nat.add_comm, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ (lval_lt (fun j _ => hL j)),
      testBit_lval hL n b]
    by_cases hb : b < 52 * n
    · simp [hb, show b < 52 * (n + 1) by omega]
    · simp only [hb, ite_false]
      by_cases hb' : b < 52 * (n + 1)
      · simp only [hb', decide_true, Bool.true_and]
        rw [show b / 52 = n by omega, show b - 52 * n = b % 52 by omega]
      · simp only [hb', decide_false, Bool.false_and]
        exact testBit_hi (hL n) (by omega)

theorem getLsbD_foldl_or (f : Nat → BitVec 64) (i : Nat) :
    ∀ (l : List Nat) (a : BitVec 64), (l.foldl (fun a j => a ||| f j) a).getLsbD i =
      (a.getLsbD i || l.any fun j => (f j).getLsbD i)
  | [], a => by simp
  | j :: l, a => by
    rw [List.foldl_cons, getLsbD_foldl_or f i l, BitVec.getLsbD_or, List.any_cons, Bool.or_assoc]

theorem foldl_congr' {f g : BitVec 64 → Nat → BitVec 64} :
    ∀ (l : List Nat) {a : BitVec 64}, (∀ a j, j ∈ l → f a j = g a j) → l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | j :: l, a, h => by
    rw [List.foldl_cons, List.foldl_cons, h a j (List.mem_cons_self ..)]
    exact foldl_congr' l fun a j hj => h a j (List.mem_cons_of_mem _ hj)

/-! ## The numbers -/

theorem lval_limbN (N : Nat) : ∀ n, lval (limbN N) n = N % 2 ^ (52 * n)
  | 0 => by rw [lval_zero]; simp [Nat.mod_one]
  | n + 1 => by
    rw [lval_succ, lval_limbN N n, limbN, Nat.mul_succ, Nat.pow_add, Nat.mod_mul, Nat.mul_comm (N / _ % _)]

theorem limbN_lt (N j : Nat) : limbN N j < 2 ^ 52 := Nat.mod_lt _ (by decide)

theorem pow2_le {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) h

end VG.Proof.Bignum.X86_64.AmmSym

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Impl.Rsa.X86_64.CrtIfma (mask52)

/-- `k₀ = minv mod 2⁵²` from `minv`, the inverse of `-M` modulo `2⁶⁴`. -/
theorem k0_of {M : Nat} {mi : BitVec 64} (h : (M % 2 ^ 64 * mi.toNat + 1) % 2 ^ 64 = 0) :
    (limbN M 0 * (mi &&& mask52).toNat + 1) % 2 ^ 52 = 0 := by
  have hm : (mi &&& mask52).toNat = mi.toNat % 2 ^ 52 := by
    rw [BitVec.toNat_and, show mask52.toNat = 2 ^ 52 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [hm, limbN, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  have hd : 2 ^ 52 ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by decide)
  have h1 : ∀ a b : Nat, (a % 2 ^ 52 * (b % 2 ^ 52) + 1) % 2 ^ 52 = (a * b + 1) % 2 ^ 52 := fun a b => by
    rw [Nat.add_mod (a % 2 ^ 52 * (b % 2 ^ 52)), ← Nat.mul_mod, ← Nat.add_mod]
  have h3 : (M % 2 ^ 64 * mi.toNat + 1) % 2 ^ 52 = 0 := by rw [← Nat.mod_mod_of_dvd _ hd, h, Nat.zero_mod]
  rw [h1, ← h3, ← h1 (M % 2 ^ 64), Nat.mod_mod_of_dvd _ hd]
  exact (h1 M _).symm

/-- `2^k` and an odd number are coprime (with core's powers, as `vec_ok` states it). -/
theorem cop2 {m : Nat} (hm : m % 2 = 1) (k : Nat) : Nat.Coprime (2 ^ k) m :=
  Nat.Coprime.pow_left k (by show Nat.gcd 2 m = 1; rw [Nat.gcd_rec, hm]; rfl)

end VG.Proof.Bignum.X86_64.AmmSym

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside wv)
open VG.Proof.Bignum.X86_64 (Scr)

/-! ## Stores of `rax` -/

/-- `v` written at `C` plus each offset of `l` in turn. -/
def stMem (m : Mem) (C : Addr) (v : BitVec 64) : List Nat → Mem
  | [] => m
  | d :: l => stMem (m.writeW (off C d) v) C v l

theorem stMem_outside (m : Mem) (C : Addr) (v : BitVec 64) {lo n : Nat} (hn : lo + n ≤ 2 ^ 64) :
    ∀ l : List Nat, (∀ d ∈ l, lo ≤ d ∧ d + 8 ≤ lo + n) → Outside C lo n m (stMem m C v l)
  | [], _ => Outside.refl _ _ _ _
  | d :: l, h => by
    have hd := h d (List.mem_cons_self ..)
    exact ((writeW_outside m C v (by omega_arith)).mono (by omega_arith) (by omega_arith)).trans
      (stMem_outside _ C v hn l fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- A word the writes miss. -/
theorem word_stMem_other (C : Addr) (v : BitVec 64) {e : Nat} (he : e + 8 ≤ 2 ^ 64) :
    ∀ (l : List Nat) (m : Mem), (∀ d ∈ l, d + 8 ≤ e ∨ e + 8 ≤ d) → (∀ d ∈ l, d + 8 ≤ 2 ^ 64) →
      word (stMem m C v l) C e = word m C e
  | [], _, _, _ => rfl
  | d :: l, m, h, h' => by
    rw [stMem, word_stMem_other C v he l _ (fun x hx => h x (List.mem_cons_of_mem _ hx))
      (fun x hx => h' x (List.mem_cons_of_mem _ hx))]
    exact (writeW_outside m C v (h' d (List.mem_cons_self ..))).word (h d (List.mem_cons_self ..)).symm he

/-- A word written, which no other write overlaps. -/
theorem word_stMem (C : Addr) (v : BitVec 64) {e : Nat} :
    ∀ (l : List Nat) (m : Mem), e ∈ l → (∀ d ∈ l, d = e ∨ d + 8 ≤ e ∨ e + 8 ≤ d) →
      (∀ d ∈ l, d + 8 ≤ 2 ^ 64) → word (stMem m C v l) C e = v
  | [], _, h, _, _ => absurd h List.not_mem_nil
  | d :: l, m, h, hs, h' => by
    have h'' : ∀ x ∈ l, x + 8 ≤ 2 ^ 64 := fun x hx => h' x (List.mem_cons_of_mem _ hx)
    by_cases hl : e ∈ l
    · exact word_stMem C v l _ hl (fun x hx => hs x (List.mem_cons_of_mem _ hx)) h''
    · have hd : d = e := by
        rcases List.mem_cons.mp h with h | h
        · exact h.symm
        · exact absurd h hl
      subst hd
      rw [stMem, word_stMem_other C v (h' d (List.mem_cons_self ..)) l _ (fun x hx => by
        rcases hs x (List.mem_cons_of_mem _ hx) with h | h
        · exact absurd (h ▸ hx) hl
        · exact h) h'']
      exact VG.Proof.Bignum.word_writeW_self _ _ _ _

/-- A frame at `B + o` as one at `B`. -/
theorem Outside.rebase {B : Addr} {o n : Nat} {m m' : Mem} (h : Outside (off B o) 0 n m m')
    (ho : o < 2 ^ 64) (hn : o + n ≤ 2 ^ 64) : Outside B o n m m' := fun x hx => h x (by
  rcases ofs_rebase' B x ho with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact .inr (by omega_arith)
  · exact .inr (by omega_arith))

/-! ## The exponent's bytes -/

theorem writeB_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 8) (h : d + 1 ≤ 2 ^ 64) :
    Outside base d 1 m (m.writeW (off base d) v) := by
  intro x hx
  apply Mem.write_apply
  simp only [ofs] at hx
  have : (x - off base d).toNat = (2 ^ 64 - d + (x - base).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x base (by omega_arith)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega_arith,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith

theorem ofs_self (C : Addr) {i : Nat} (h : i < 2 ^ 64) : ofs C (C + BitVec.ofNat 64 i) = i := by
  rw [ofs, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem writeB_self (m : Mem) (a : Addr) (v : BitVec 8) : (m.writeW a v) a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero]
  ext i hi; simp

theorem setWidth_byte' (b : BitVec 8) : (b.setWidth 64).setWidth 8 = b := by
  ext i hi; simp

end VG.Proof.Bignum.X86_64.AmmSym

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## Facts about the area that the region's steps carry -/

theorem byte_frm {m m' : Mem} {B : Addr} {rs : List (Nat × Nat)} (hf : Frm B rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, d + 1 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hz : d < 2 ^ 64) : m' (off B d) = m (off B d) :=
  hf _ fun r hr => by rw [AmmSym.ofs_off0 B hz]; rcases hd r hr with h | h <;> omega_arith

theorem word_below_frm {m m' : Mem} {B : Addr} {rs : List (Nat × Nat)} {L : Nat} (hf : Frm B rs m m')
    (hr : ∀ r ∈ rs, L ≤ r.1) {d : Nat} (hd : d + 8 ≤ L) (hz : L ≤ 2 ^ 64) : word m' B d = word m B d :=
  hf.word_eq (fun r h => .inl (by have := hr r h; omega_arith)) (by omega_arith)

theorem _root_.VG.Proof.Bignum.Hdr.of_below {m m' : Mem} {B : Addr} {o wx : Nat} {mx : BitVec 64} (hH : Hdr m (off B o) wx mx)
    {rs : List (Nat × Nat)} (hf : Frm B rs m m') (hr : ∀ r ∈ rs, o + hdrBytes ≤ r.1)
    (hz : o + hdrBytes ≤ 2 ^ 64) : Hdr m' (off B o) wx mx := by
  have hh : ∀ i < 32, word m' (off B o) (8 * i) = word m (off B o) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact word_below_frm hf hr (by unfold hdrBytes; omega_arith) hz
  exact ⟨(hh _ (by decide)).trans hH.hw, (hh _ (by decide)).trans hH.hminv,
    fun j hj => (hh _ (by unfold sArr; omega_arith)).trans (hH.harr j hj)⟩

theorem wv_below_frm {m m' : Mem} {B : Addr} {rs : List (Nat × Nat)} {L : Nat} (hf : Frm B rs m m')
    (hr : ∀ r ∈ rs, L ≤ r.1) {d k : Nat} (hd : d + 8 * k ≤ L) (hz : L ≤ 2 ^ 64) : wv m' B d k = wv m B d k :=
  hf.wv_eq (fun r h => .inl (by have := hr r h; omega_arith)) (by omega_arith)

/-! ## The region's tail -/

theorem byte_of_word0 {m : Mem} {F : Addr} {d k : Nat} (h : word m F d = 0) (hk : k < 8) :
    m (off F (d + k)) = 0 := by
  have e := VG.X86_64.byte_readW m (off F d) (w := 64) (k := k) (by omega_arith)
  rw [show m.readW (off F d) 64 = word m F d from rfl, h, AmmSym.off_add] at e
  rw [← e]; simp

/-! ## The exponent's value -/

theorem os2ip_snoc (l : List Byte) (b : Byte) : Spec.Rsa.os2ip (l ++ [b]) = 256 * Spec.Rsa.os2ip l + b.toNat := by
  simp only [Spec.Rsa.os2ip, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem os2ip_zeros (l : List Byte) : ∀ k, Spec.Rsa.os2ip (List.replicate k 0 ++ l) = Spec.Rsa.os2ip l
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ, List.cons_append, ← os2ip_zeros l k]
    simp only [Spec.Rsa.os2ip, List.foldl_cons]
    rfl

end VG.Proof.Bignum.X86_64

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The conditional subtraction's result, for `R` abstract. -/
theorem csub_fin {Tl Tw Dv X V c R : Nat} (hR : X < R) (hD : Dv < R) (hTl : Tl < R) (hc : c ≤ 1)
    (hacc : Tl + R * Tw = V) (hV : V < 2 * X) (hsub : Dv + X = Tl + R * c) :
    (if Tw < c then Tl else Dv) = V % X := by
  have := VG.Proof.Bignum.csub_result (Tl := Tl) (Tw := Tw) (Tw1 := 0) hR hD hc hTl (by rw [Nat.mul_zero, Nat.add_zero, hacc]; exact hV)
    hsub
  rwa [Nat.mul_zero, Nat.add_zero, hacc] at this

end VG.Proof.Bignum.X86_64

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## `ifma`'s second half: the vector code and the results -/

/-- `p`'s value for prime 0, `q`'s for prime 1. -/
def two {α : Type} (x y : α) (p : Nat) : α := if p = 0 then x else y

/-- Back to `n`'s workspace. -/
theorem leaveB_ok {u : State} {B : Addr} {Z o : Nat} (hs : Scr u B Z) (hdi : u.gpr .rdi = off B o)
    (hlk : word u.mem (off B o) (8 * sLink) = B) (ho : o + 8 * 32 ≤ Z) :
    WP isa (.block [leave]) u fun u' => u'.gpr .rdi = B ∧ u'.mem = u.mem ∧ Keep [.rdi] u u' := by
  have hl : InRegions (u.rd ++ u.wr) (off (off B o) (8 * sLink)) 8 := by
    rw [off_off]; exact hs.ld (by unfold sLink sFn; omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun u' => u'.gpr .rdi = B ∧ u'.mem = u.mem) (by
    xrun [leave, State.ea, hdr, hdi, hdrOff, hl, hlk]) rfl) fun u' ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩

end VG.Proof.Bignum.X86_64
