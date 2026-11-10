module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.ESym
import VerifiedGarbage.Proof.Framework.X86_64.Avx

/-!
# Straight-line `EVEX.512` code, quadword by quadword

`ESym`'s symbolic run for the `EVEX.512` instructions of
`TCB/X86_64/Evex.lean` (`E5Op`), on the eight quadwords of all thirty-two
`zmm` registers: `ZSym.run` computes each quadword after a block as a term
(`ZT`) in the quadwords, general-purpose registers and memory before it,
and `zrun_ok` proves the machine agrees. It runs what a multiplication
with two numbers side by side in each register uses: `vpxorq` of a register
with itself, `vpaddq`, `vpandq`, `vpsrlq`, `vpermq`, `vpmadd52luq` and
`vpmadd52huq` and `vinserti64x4` of the high half, on registers; the loads
that fill a register's halves (`vmovdqu64 ymm, m256`, `vpbroadcastq ymm,
m64`, `vinserti64x4 zmm, zmm, m256, 1`); and `vmovq xmm, r64`.
-/
-- separate module: the symbolic run of EVEX.512 code, for any proof of such code, as `ESym` is of EVEX.256 code.

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64
open VG.Proof.Bignum.X86_64.AmmSym (baseOff baseOff_ok Ctx)
open VG.Proof.Poly1305.X86_64.Avx2 (qword_paddq qword_psrlq mod2_lt qword256_eq qword_and sel4 sel4_lt
  qword256_perm)
open VG.Proof.X25519.X86_64.Ifma (mad52 qword_madd52)
open VG.Impl.Rsa.X86_64.CrtIfma (vreg)

/-! ## Quadwords of `zmm` registers -/

/-- Quadword `k` (`k < 8`) of `zmm` register `r`. -/
def qz (s : State) (r : VReg) (k : Nat) : BitVec 64 := qword (s.vz r (k / 2)) (k % 2)

/-- The lanes of a register's low half are those of its `ymm` register. -/
theorem vz_lo (s : State) (r : VReg) {i : Nat} (hi : i < 2) : s.vz r i = lane256 (s.vy r) i := by
  cases r with
  | lo r =>
    simp only [State.vz, State.zlane, hi, ite_true, State.lane, State.vy, State.ymm, lane256]
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [Nat.mul_zero, lane_app0]; rfl
    · rw [Nat.mul_one, lane_app1]; rfl
  | hi r => simp only [State.vz, State.zlaneH, hi, ite_true, State.vy, lane256]

/-- A quadword of a register's low half is its `ymm` register's. -/
theorem qz_lo (s : State) (r : VReg) {k : Nat} (hk : k < 4) : qz s r k = qv s r k := by
  rw [qz, vz_lo s r (by omega), qv, qword256_eq]; rfl

/-- The lanes after an `EVEX.512` write. -/
theorem vz_setVz (s : State) (d r : VReg) (L : Nat → BitVec 128) {i : Nat} (hi : i < 4) :
    (s.setVz d (L 0) (L 1) (L 2) (L 3)).vz r i = if r = d then L i else s.vz r i := by
  cases d with
  | lo d =>
    cases r with
    | lo r =>
      simp only [State.setVz, State.vz, State.zlane, State.lane, State.setZ, VReg.lo.injEq]
      rcases VG.X86_64.cases4 hi with rfl | rfl | rfl | rfl <;>
        simp only [Nat.reduceLT, ite_true, ite_false, Nat.one_ne_zero, Nat.reduceSub, Nat.mul_zero, Nat.mul_one] <;>
        split <;> first | rfl | exact lane_app0 _ _ | exact lane_app1 _ _
    | hi r => simp only [State.setVz, State.vz, State.setZ, reduceCtorEq, ite_false]; rfl
  | hi d =>
    cases r with
    | lo r => simp only [State.setVz, State.vz, State.setZH, reduceCtorEq, ite_false]; rfl
    | hi r =>
      simp only [State.setVz, State.vz, State.zlaneH, State.setZH, VReg.hi.injEq]
      rcases VG.X86_64.cases4 hi with rfl | rfl | rfl | rfl <;>
        simp only [Nat.reduceLT, ite_true, ite_false, Nat.reduceSub, Nat.mul_zero, Nat.mul_one] <;>
        split <;> first | rfl | exact lane_app0 _ _ | exact lane_app1 _ _

/-- The lanes after an `EVEX.256` write: the high half is zero. -/
theorem vz_setVy (s : State) (d r : VReg) (v : BitVec 256) {i : Nat} (hi : i < 4) :
    (s.setVy d v).vz r i = if r = d then (if i < 2 then lane256 v i else 0) else s.vz r i := by
  cases d with
  | lo d =>
    cases r with
    | lo r =>
      simp only [State.setVy, State.vz, State.zlane, State.lane, State.setV, VReg.lo.injEq, lane256]
      rcases VG.X86_64.cases4 hi with rfl | rfl | rfl | rfl <;>
        simp only [Nat.reduceLT, ite_true, ite_false, Nat.one_ne_zero, Nat.reduceSub, Nat.mul_zero, Nat.mul_one] <;>
        split <;> first | rfl | exact (BitVec.eq_of_getLsbD_eq fun j hj => by simp)
    | hi r => simp only [State.setVy, State.vz, State.setV, reduceCtorEq, ite_false]; rfl
  | hi d =>
    cases r with
    | lo r => simp only [State.setVy, State.vz, reduceCtorEq, ite_false]; rfl
    | hi r =>
      simp only [State.setVy, State.vz, State.zlaneH, VReg.hi.injEq, lane256]
      rcases VG.X86_64.cases4 hi with rfl | rfl | rfl | rfl <;>
        simp only [Nat.reduceLT, ite_true, ite_false, Nat.reduceSub, Nat.mul_zero, Nat.mul_one] <;>
        split <;> first | rfl | exact (BitVec.eq_of_getLsbD_eq fun j hj => by simp)

theorem div2_lt {k : Nat} (hk : k < 8) : k / 2 < 4 := by omega

theorem qz_setVz (s : State) (d r : VReg) (L : Nat → BitVec 128) {k : Nat} (hk : k < 8) :
    qz (s.setVz d (L 0) (L 1) (L 2) (L 3)) r k = if r = d then qword (L (k / 2)) (k % 2) else qz s r k := by
  rw [qz, vz_setVz s d r L (div2_lt hk)]; split <;> rfl

theorem qz_setVy (s : State) (d r : VReg) (v : BitVec 256) {k : Nat} (hk : k < 8) :
    qz (s.setVy d v) r k = if r = d then (if k < 4 then qword256 v k else 0) else qz s r k := by
  rw [qz, vz_setVy s d r v (div2_lt hk)]
  by_cases hr : r = d
  · rw [ite_eq_left hr, ite_eq_left hr]
    by_cases hk4 : k < 4
    · rw [ite_eq_left (show k / 2 < 2 by omega), ite_eq_left hk4, qword256_eq]; rfl
    · rw [ite_eq_right (show ¬ k / 2 < 2 by omega), ite_eq_right hk4]
      apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [qword]
  · rw [ite_eq_right hr, ite_eq_right hr]; rfl

/-- A quadword of two lanes. -/
theorem qword256_cat2 (x1 x0 : BitVec 128) {t : Nat} (ht : t < 4) :
    qword256 (x1 ++ x0) t = qword (if t < 2 then x0 else x1) (t % 2) := by
  rw [qword256_eq]
  rcases VG.X86_64.cases4 ht with rfl | rfl | rfl | rfl
  · simp only [Nat.reduceDiv, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, ite_true, lane_app0]
  · simp only [Nat.reduceDiv, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, ite_true, lane_app0]
  · simp only [Nat.reduceDiv, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, ite_false, lane_app1]
  · simp only [Nat.reduceDiv, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, ite_false, lane_app1]

/-! ## Terms -/

/-- A quadword of a `zmm` register, in terms of the start. -/
inductive ZT
  /-- Quadword `k` of the register numbered `r`. -/
  | reg (r : Nat)
  | zero
  /-- The general-purpose register `g` in quadword 0, zero elsewhere. -/
  | lane0 (g : Reg)
  /-- The 32 bytes at `b + d` in the low half, zero in the high half. -/
  | ldy (b : Reg) (d : Nat)
  /-- The quadword at `b + d` in each quadword of the low half, zero in the
  high half. -/
  | bcy (b : Reg) (d : Nat)
  /-- The low half of `a`, and the low half of `b` as the high half. -/
  | ins (a b : ZT)
  /-- `vpmadd52luq`, `vpmadd52huq` (`h`). -/
  | mad (h : Bool) (c a b : ZT)
  | add (a b : ZT)
  | and (a b : ZT)
  | shr (a : ZT) (n : Nat)
  /-- `vpermq` by `o`: within each half, quadword `k` from quadword `sel4 o k`. -/
  | perm (a : ZT) (o : Nat)
  deriving DecidableEq, Repr

def ZT.eval (s₀ : State) : ZT → Nat → BitVec 64
  | .reg r, k => qz s₀ (vreg r) k
  | .zero, _ => 0
  | .lane0 g, k => if k = 0 then s₀.gpr g else 0
  | .ldy b d, k => if k < 4 then s₀.mem.readW (s₀.gpr b + BitVec.ofNat 64 (d + 8 * k)) 64 else 0
  | .bcy b d, k => if k < 4 then s₀.mem.readW (s₀.gpr b + BitVec.ofNat 64 d) 64 else 0
  | .ins a b, k => if k < 4 then a.eval s₀ k else b.eval s₀ (k - 4)
  | .mad h c a b, k => mad52 h (c.eval s₀ k) (a.eval s₀ k) (b.eval s₀ k)
  | .add a b, k => a.eval s₀ k + b.eval s₀ k
  | .and a b, k => a.eval s₀ k &&& b.eval s₀ k
  | .shr a n, k => a.eval s₀ k >>> n
  | .perm a o, k => a.eval s₀ (4 * (k / 4) + sel4 o (k % 4))

/-! ## The machine -/

/-- The terms of the thirty-two `zmm` registers, by number. -/
structure ZSym where
  reg : Nat → ZT

def ZSym.init : ZSym := ⟨.reg⟩

def ZSym.set (σ : ZSym) (d : VReg) (t : ZT) : ZSym :=
  { σ with reg := fun r => bif Nat.beq r (vi d) then t else σ.reg r }

def ZSym.e5 (σ : ZSym) : E5Op → Option ZSym
  | .bin .vpxorq d a b => if a = b then some (σ.set d .zero) else none
  | .bin .vpaddq d a b => some (σ.set d (.add (σ.reg (vi a)) (σ.reg (vi b))))
  | .bin .vpandq d a b => some (σ.set d (.and (σ.reg (vi a)) (σ.reg (vi b))))
  | .shift .vpsrlq d a n => if n.toNat < 64 then some (σ.set d (.shr (σ.reg (vi a)) n.toNat)) else none
  | .vpermq d a o => some (σ.set d (.perm (σ.reg (vi a)) o.toNat))
  | .vpmadd52 h d a b => some (σ.set d (.mad h (σ.reg (vi d)) (σ.reg (vi a)) (σ.reg (vi b))))
  | .vinserti64x4 d a b n => if n = 1 then some (σ.set d (.ins (σ.reg (vi a)) (σ.reg (vi b)))) else none
  | _ => none

/-- One instruction, with `lim b` the bytes readable from each base `b`
(which no instruction here changes). -/
def ZSym.step (lim : Reg → Nat) (σ : ZSym) : Instr → Option ZSym
  | .e5op o => σ.e5 o
  | .eop (.vmovq d g) => some (σ.set d (.lane0 g))
  | .evLoad d m => (baseOff m).bind fun bo =>
    if bo.2 + 32 ≤ lim bo.1 then some (σ.set d (.ldy bo.1 bo.2)) else none
  | .evBroadcastLoad d m => (baseOff m).bind fun bo =>
    if bo.2 + 8 ≤ lim bo.1 then some (σ.set d (.bcy bo.1 bo.2)) else none
  | .e5InsertLoad d a m n => (baseOff m).bind fun bo =>
    if n = 1 ∧ bo.2 + 32 ≤ lim bo.1 then some (σ.set d (.ins (σ.reg (vi a)) (.ldy bo.1 bo.2))) else none
  | _ => none

def ZSym.run (lim : Reg → Nat) (σ : ZSym) : List Instr → Option ZSym
  | [] => some σ
  | i :: is => (σ.step lim i).bind fun σ' => σ'.run lim is

/-! ## The machine agrees -/

/-- `s₀` with the vector registers of `s`. -/
def zr (s₀ s : State) : State :=
  { s₀ with xmm := s.xmm, ymmHi := s.ymmHi, zmmHi := s.zmmHi, ymmH := s.ymmH, zmmHiH := s.zmmHiH }

/-- The terms `σ` hold in `s`, which differs from `s₀` only in its vector
registers. -/
structure ZRel (σ : ZSym) (s₀ s : State) : Prop where
  reg : ∀ r k, k < 8 → qz s r k = (σ.reg (vi r)).eval s₀ k
  eq : zr s₀ s = s

theorem ZRel.gpr {σ : ZSym} {s₀ s : State} (h : ZRel σ s₀ s) : s.gpr = s₀.gpr := by rw [← h.eq]; rfl
theorem ZRel.mem {σ : ZSym} {s₀ s : State} (h : ZRel σ s₀ s) : s.mem = s₀.mem := by rw [← h.eq]; rfl
theorem ZRel.rd {σ : ZSym} {s₀ s : State} (h : ZRel σ s₀ s) : s.rd = s₀.rd := by rw [← h.eq]; rfl
theorem ZRel.wr {σ : ZSym} {s₀ s : State} (h : ZRel σ s₀ s) : s.wr = s₀.wr := by rw [← h.eq]; rfl
theorem ZRel.mxcsr {σ : ZSym} {s₀ s : State} (h : ZRel σ s₀ s) : s.mxcsr = s₀.mxcsr := by rw [← h.eq]; rfl
theorem ZRel.flags {σ : ZSym} {s₀ s : State} (h : ZRel σ s₀ s) :
    s.cf = s₀.cf ∧ s.zf = s₀.zf ∧ s.sf = s₀.sf ∧ s.of = s₀.of := by
  rw [← h.eq]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem ZRel.init (s₀ : State) : ZRel ZSym.init s₀ s₀ :=
  ⟨fun r k _ => by simp only [ZSym.init, ZT.eval, vreg_vi], rfl⟩

theorem zr_setVz {s₀ s : State} (h : zr s₀ s = s) (d : VReg) (l0 l1 l2 l3 : BitVec 128) :
    zr s₀ (s.setVz d l0 l1 l2 l3) = s.setVz d l0 l1 l2 l3 := by
  rw [← h]; cases d <;> rfl

theorem zr_setVy {s₀ s : State} (h : zr s₀ s = s) (d : VReg) (v : BitVec 256) :
    zr s₀ (s.setVy d v) = s.setVy d v := by
  rw [← h]; cases d <;> rfl

/-- An `EVEX.512` write of the lanes `L`. -/
theorem ZRel.setZ {σ : ZSym} {s₀ s : State} (h : ZRel σ s₀ s) {d : VReg} {t : ZT} {L : Nat → BitVec 128}
    (hv : ∀ k, k < 8 → qword (L (k / 2)) (k % 2) = t.eval s₀ k) :
    ZRel (σ.set d t) s₀ (s.setVz d (L 0) (L 1) (L 2) (L 3)) := by
  refine ⟨fun r k hk => ?_, zr_setVz h.eq d _ _ _ _⟩
  rw [qz_setVz s d r L hk]
  simp only [ZSym.set, Bool.cond_eq_ite, Nat.beq_eq, vi_inj]
  split
  · exact hv k hk
  · exact h.reg r k hk

/-- An `EVEX.256` write, which zeroes the high half. -/
theorem ZRel.setY {σ : ZSym} {s₀ s : State} (h : ZRel σ s₀ s) {d : VReg} {t : ZT} {v : BitVec 256}
    (hv : ∀ k, k < 4 → qword256 v k = t.eval s₀ k) (hz : ∀ k, 4 ≤ k → t.eval s₀ k = 0) :
    ZRel (σ.set d t) s₀ (s.setVy d v) := by
  refine ⟨fun r k hk => ?_, zr_setVy h.eq d v⟩
  rw [qz_setVy s d r v hk]
  simp only [ZSym.set, Bool.cond_eq_ite, Nat.beq_eq, vi_inj]
  split
  · split
    · exact hv k (by assumption)
    · exact (hz k (by omega)).symm
  · exact h.reg r k hk

theorem zstep_ok {lim : Reg → Nat} {s₀ : State} (hc : Ctx lim s₀) {σ σ' : ZSym} {s : State}
    (h : ZRel σ s₀ s) {i : Instr} (e : σ.step lim i = some σ') :
    ∃ s', exec i s = some s' ∧ ZRel σ' s₀ s' := by
  have hR : ∀ a k, k < 8 → (σ.reg (vi a)).eval s₀ k = qz s a k := fun a k hk => (h.reg a k hk).symm
  unfold ZSym.step at e
  split at e
  · rename_i o
    refine ⟨o.exec s, rfl, ?_⟩
    unfold ZSym.e5 at e
    split at e
    · rename_i d a b
      split at e
      · rename_i hab
        cases e
        subst hab
        refine h.setZ (L := fun i => EBinOp.vpxorq.sse.eval (s.vz a i) (s.vz a i)) fun k hk => ?_
        simp [EBinOp.sse, XBinOp.eval, qword, ZT.eval]
      · cases e
    · rename_i d a b
      cases e
      refine h.setZ (L := fun i => EBinOp.vpaddq.sse.eval (s.vz a i) (s.vz b i)) fun k hk => ?_
      simp only [EBinOp.sse, ZT.eval]
      rw [qword_paddq _ _ (mod2_lt k), hR a k hk, hR b k hk]; rfl
    · rename_i d a b
      cases e
      refine h.setZ (L := fun i => EBinOp.vpandq.sse.eval (s.vz a i) (s.vz b i)) fun k hk => ?_
      simp only [EBinOp.sse, XBinOp.eval, ZT.eval]
      rw [qword_and, hR a k hk, hR b k hk]; rfl
    · rename_i d a n
      split at e
      · rename_i hn
        cases e
        refine h.setZ (L := fun i => ZShiftOp.vpsrlq.sse.eval (s.vz a i) n) fun k hk => ?_
        simp only [ZShiftOp.sse, ZT.eval]
        rw [qword_psrlq _ hn (mod2_lt k), hR a k hk]; rfl
      · cases e
    · rename_i d a o
      cases e
      refine h.setZ (L := fun i => (if i < 2 then permQwords (s.vz a 1 ++ s.vz a 0) o
        else permQwords (s.vz a 3 ++ s.vz a 2) o).extractLsb' (128 * (i % 2)) 128) fun k hk => ?_
      simp only [ZT.eval]
      have hs := sel4_lt o.toNat (k % 4)
      rw [hR a _ (by omega), qz]
      by_cases hk4 : k < 4
      · have e1 : k / 2 % 2 = k / 2 := by omega
        have e2 : k % 4 = k := by omega
        have e3 : 4 * (k / 4) + sel4 o.toNat k = sel4 o.toNat k := by omega
        rw [e2] at hs
        rw [ite_eq_left (show k / 2 < 2 by omega), e1, ← qword256_eq, qword256_perm _ _ hk4,
          qword256_cat2 _ _ hs, e2, e3]
        by_cases h2 : sel4 o.toNat k < 2
        · rw [ite_eq_left h2, show sel4 o.toNat k / 2 = 0 by omega]
        · rw [ite_eq_right h2, show sel4 o.toNat k / 2 = 1 by omega]
      · have e1 : k / 2 % 2 = (k - 4) / 2 := by omega
        have e2 : k % 4 = k - 4 := by omega
        have e3 : k % 2 = (k - 4) % 2 := by omega
        rw [e2] at hs
        have e4 : (4 * (k / 4) + sel4 o.toNat (k - 4)) / 2 = 2 + sel4 o.toNat (k - 4) / 2 := by omega
        have e5 : (4 * (k / 4) + sel4 o.toNat (k - 4)) % 2 = sel4 o.toNat (k - 4) % 2 := by omega
        rw [ite_eq_right (show ¬ k / 2 < 2 by omega), e1, e3, ← qword256_eq,
          qword256_perm _ _ (show k - 4 < 4 by omega), qword256_cat2 _ _ hs, e2, e4, e5]
        by_cases h2 : sel4 o.toNat (k - 4) < 2
        · rw [ite_eq_left h2, show sel4 o.toNat (k - 4) / 2 = 0 by omega]
        · rw [ite_eq_right h2, show sel4 o.toNat (k - 4) / 2 = 1 by omega]
    · rename_i hh d a b
      cases e
      refine h.setZ (L := fun i => madd52 hh (s.vz d i) (s.vz a i) (s.vz b i)) fun k hk => ?_
      simp only [ZT.eval]
      rw [qword_madd52 _ _ _ _ (mod2_lt k), hR d k hk, hR a k hk, hR b k hk]; rfl
    · rename_i d a b n
      split at e
      · rename_i hn
        cases e
        subst hn
        refine h.setZ (L := insert64x4 (s.vz a) (s.vy b) 1) fun k hk => ?_
        simp only [ZT.eval, insert64x4, show (1 : BitVec 8).getLsbD 0 = true from rfl, ite_true]
        by_cases hk4 : k < 4
        · rw [ite_eq_left (show k / 2 < 2 by omega), ite_eq_left hk4, hR a k hk]; rfl
        · rw [ite_eq_right (show ¬ k / 2 < 2 by omega), ite_eq_right hk4, hR b _ (by omega),
            qz_lo s b (show k - 4 < 4 by omega), qv, qword256_eq, lane256,
            show k / 2 - 2 = (k - 4) / 2 by omega, show k % 2 = (k - 4) % 2 by omega]
      · cases e
    · cases e
  · rename_i d g
    cases e
    refine ⟨_, rfl, h.setY (fun k hk => ?_) fun k hk => ?_⟩
    · rw [qword256_low _ hk]; simp only [ZT.eval, h.gpr]
    · simp only [ZT.eval, show k ≠ 0 by omega, ite_false]
  · rename_i d m
    obtain ⟨⟨b, o⟩, hbo, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    case isFalse => cases e
    rename_i hlt
    cases e
    have ea : s.ea m = s₀.gpr b + BitVec.ofNat 64 o := by rw [baseOff_ok hbo, h.gpr]
    have hin : InRegions (s.rd ++ s.wr) (s₀.gpr b + BitVec.ofNat 64 o) 32 := by
      rw [h.rd, h.wr]; exact hc b o 32 (by decide) hlt
    refine ⟨s.setVy d (s.mem.readW (s₀.gpr b + BitVec.ofNat 64 o) 256),
      by simp only [exec, ea, State.load256, hin, ite_true, Option.map_some], ?_⟩
    refine h.setY (fun k hk => ?_) fun k hk => ?_
    · simp only [ZT.eval, hk, ite_true]
      have r1 := readW_extract s.mem (s₀.gpr b + BitVec.ofNat 64 o) (w := 256) (k := 8 * k)
        (n := 8) (by omega)
      rw [qword256, show 64 * k = 8 * (8 * k) by omega, r1, h.mem, BitVec.add_assoc, ← BitVec.ofNat_add]
    · simp only [ZT.eval, show ¬ k < 4 by omega, ite_false]
  · rename_i d m
    obtain ⟨⟨b, o⟩, hbo, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    case isFalse => cases e
    rename_i hlt
    cases e
    have ea : s.ea m = s₀.gpr b + BitVec.ofNat 64 o := by rw [baseOff_ok hbo, h.gpr]
    have hin : InRegions (s.rd ++ s.wr) (s₀.gpr b + BitVec.ofNat 64 o) 8 := by
      rw [h.rd, h.wr]; exact hc b o 8 (by decide) hlt
    refine ⟨s.setVy d (s.mem.readW (s₀.gpr b + BitVec.ofNat 64 o) 64 ++
        s.mem.readW (s₀.gpr b + BitVec.ofNat 64 o) 64 ++ s.mem.readW (s₀.gpr b + BitVec.ofNat 64 o) 64 ++
        s.mem.readW (s₀.gpr b + BitVec.ofNat 64 o) 64),
      by simp only [exec, ea, State.load64, hin, ite_true, Option.map_some], ?_⟩
    refine h.setY (fun k hk => ?_) fun k hk => ?_
    · rw [qword256_bcast _ hk]; simp only [ZT.eval, hk, ite_true, h.mem]
    · simp only [ZT.eval, show ¬ k < 4 by omega, ite_false]
  · rename_i d a m n
    obtain ⟨⟨b, o⟩, hbo, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    case isFalse => cases e
    rename_i hlt
    cases e
    obtain ⟨hn, hlt⟩ := hlt
    subst hn
    have ea : s.ea m = s₀.gpr b + BitVec.ofNat 64 o := by rw [baseOff_ok hbo, h.gpr]
    have hin : InRegions (s.rd ++ s.wr) (s₀.gpr b + BitVec.ofNat 64 o) 32 := by
      rw [h.rd, h.wr]; exact hc b o 32 (by decide) hlt
    refine ⟨s.setVz d (insert64x4 (s.vz a) (s.mem.readW (s₀.gpr b + BitVec.ofNat 64 o) 256) 1 0)
        (insert64x4 (s.vz a) (s.mem.readW (s₀.gpr b + BitVec.ofNat 64 o) 256) 1 1)
        (insert64x4 (s.vz a) (s.mem.readW (s₀.gpr b + BitVec.ofNat 64 o) 256) 1 2)
        (insert64x4 (s.vz a) (s.mem.readW (s₀.gpr b + BitVec.ofNat 64 o) 256) 1 3),
      by simp only [exec, ea, State.load256, hin, ite_true, Option.map_some], ?_⟩
    refine h.setZ (L := insert64x4 (s.vz a) (s.mem.readW (s₀.gpr b + BitVec.ofNat 64 o) 256) 1) fun k hk => ?_
    simp only [ZT.eval, insert64x4, show (1 : BitVec 8).getLsbD 0 = true from rfl, ite_true]
    by_cases hk4 : k < 4
    · rw [ite_eq_left (show k / 2 < 2 by omega), ite_eq_left hk4, hR a k hk]; rfl
    · have r1 := readW_extract s.mem (s₀.gpr b + BitVec.ofNat 64 o) (w := 256) (k := 8 * (k - 4))
        (n := 8) (by omega)
      rw [ite_eq_right (show ¬ k / 2 < 2 by omega), ite_eq_right hk4, ite_eq_left (show k - 4 < 4 by omega),
        lane256, show k / 2 - 2 = (k - 4) / 2 by omega, show k % 2 = (k - 4) % 2 by omega, ← qword256_eq,
        qword256, show 64 * (k - 4) = 8 * (8 * (k - 4)) by omega, r1, h.mem, BitVec.add_assoc,
        ← BitVec.ofNat_add]
  · cases e

/-- A block of instructions. -/
theorem zsrun_ok {lim : Reg → Nat} {s₀ : State} (hc : Ctx lim s₀) :
    ∀ (is : List Instr) {σ σ' : ZSym} {s : State}, ZRel σ s₀ s → σ.run lim is = some σ' →
      WP isa (.block is) s (ZRel σ' s₀)
  | [], _, _, _, h, e => by cases e; exact WP.block_nil h
  | i :: is, _, _, _, h, e => by
    simp only [ZSym.run, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    obtain ⟨s₁, hx, h₁⟩ := zstep_ok hc h e₁
    exact WP.block_cons_iff.2 ⟨s₁, hx, zsrun_ok hc is h₁ e₂⟩

/-- A block from a relation. -/
theorem zrun_ok {lim : Reg → Nat} {s₀ : State} (hc : Ctx lim s₀) {is : List Instr} {σ σ' : ZSym}
    {s : State} (h : ZRel σ s₀ s) (e : σ.run lim is = some σ') : WP isa (.block is) s (ZRel σ' s₀) :=
  zsrun_ok hc is h e

end VG.Proof.Bignum.X86_64.Ifma
