import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Lemmas
import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma

/-!
# Straight-line `EVEX.256` code, lane by lane

A symbolic run of the `EVEX.256` instructions of
`TCB/X86_64/Evex.lean`, on all thirty-two `ymm` registers (numbered as
`CrtIfma.vreg`): `ESym.run` computes each quadword after a block of them
as a term (`T`, its `reg r` quadword `k` of register `r` of the thirty-two)
in the quadwords, general-purpose registers and memory before it, and
`run_ok` proves the machine agrees. Besides the instructions of a
step of the multiplication (`vpxorq` of a register with itself, `vpaddq`,
`vpsrlq`, `vmovq` from `rax` and from a register, `vpbroadcastq`, `valignq`
and the memory form of `vpmadd52luq` and `vpmadd52huq`), it runs loads of
`rax` from memory (`AmmSym.G`).
-/

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64
open VG.Proof.Bignum.X86_64.AmmSym (G G.eval baseOff baseOff_ok Ctx)
open VG.Proof.Poly1305.X86_64.Avx2 (qword_paddq qword_psrlq cases4 mod2_lt qword256_eq qword256_cat qword_and qword_or)
open VG.Proof.X25519.X86_64.Ifma (mad52 qword_madd52)
open VG.Impl.Rsa.X86_64.CrtIfma (vreg)

/-! ## Registers by number -/

/-- The number of a register (`vreg (vi r) = r`). -/
def vi : VReg → Nat
  | .lo r => VG.Proof.Poly1305.X86_64.Avx2.xi r
  | .hi r => match r with
    | .xmm16 => 16 | .xmm17 => 17 | .xmm18 => 18 | .xmm19 => 19
    | .xmm20 => 20 | .xmm21 => 21 | .xmm22 => 22 | .xmm23 => 23
    | .xmm24 => 24 | .xmm25 => 25 | .xmm26 => 26 | .xmm27 => 27
    | .xmm28 => 28 | .xmm29 => 29 | .xmm30 => 30 | .xmm31 => 31

theorem vreg_vi (r : VReg) : vreg (vi r) = r := by
  cases r with
  | lo r => cases r <;> rfl
  | hi r => cases r <;> rfl

theorem vi_inj {r r' : VReg} : vi r = vi r' ↔ r = r' :=
  ⟨fun h => by rw [← vreg_vi r, ← vreg_vi r', h], fun h => h ▸ rfl⟩

theorem vi_vreg : ∀ n < 32, vi (vreg n) = n := by decide

/-! ## Quadwords -/

/-- Quadword `k` (`k < 4`) of `ymm` register `r`. -/
def qv (s : State) (r : VReg) (k : Nat) : BitVec 64 := qword256 (s.vy r) k

theorem extract_cat (v : BitVec 256) : v.extractLsb' 128 128 ++ v.extractLsb' 0 128 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_append]
  by_cases h : j < 128
  · simp [h]
  · simp [h, show j - 128 < 128 by omega, show 128 + (j - 128) = j by omega]

theorem qv_setVy (s : State) (d r : VReg) (v : BitVec 256) (k : Nat) :
    qv (s.setVy d v) r k = if r = d then qword256 v k else qv s r k := by
  cases d with
  | lo d =>
    cases r with
    | lo r =>
      simp only [qv, State.vy, State.setVy, VReg.lo.injEq]
      by_cases h : r = d
      · subst h
        simp only [ite_true, State.ymm, State.setV, ite_true, extract_cat]
      · simp only [h, ite_false, State.ymm, State.setV]
    | hi r => simp only [qv, State.vy, State.setVy, reduceCtorEq, ite_false]; rfl
  | hi d =>
    cases r with
    | lo r => simp only [qv, State.vy, State.setVy, reduceCtorEq, ite_false]; rfl
    | hi r =>
      simp only [qv, State.vy, State.setVy, VReg.hi.injEq]
      split <;> rfl

theorem lane_app0 (x y : BitVec 128) : (x ++ y).extractLsb' 0 128 = y := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, Nat.zero_add]
  rw [BitVec.getLsbD_append]; simp [hj]

theorem lane_app1 (x y : BitVec 128) : (x ++ y).extractLsb' 128 128 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_append]; simp [hj]

theorem qword256_lanes (f : BitVec 128 → BitVec 128 → BitVec 128) (a b : BitVec 256) {k : Nat} (hk : k < 4) :
    qword256 (lanes256 f a b) k =
      qword (f (a.extractLsb' (128 * (k / 2)) 128) (b.extractLsb' (128 * (k / 2)) 128)) (k % 2) := by
  rw [qword256_eq]
  simp only [lanes256, lane256]
  rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceDiv, Nat.reduceMul, lane_app0, lane_app1]

/-- Quadword `k` of a 128-bit lane of a 256-bit value. -/
theorem qword_lane256 (v : BitVec 256) (k : Nat) :
    qword (v.extractLsb' (128 * (k / 2)) 128) (k % 2) = qword256 v k := (qword256_eq v k).symm

/-! ## Quadwords after each instruction -/

theorem qword256_low (g : BitVec 64) {k : Nat} (hk : k < 4) :
    qword256 ((0 : BitVec 192) ++ g) k = if k = 0 then g else 0 := by
  apply BitVec.eq_of_toNat_eq
  have hg := g.isLt
  have e : ((0 : BitVec 192) ++ g).toNat = g.toNat := by
    rw [BitVec.toNat_append]; simp
  simp only [qword256, BitVec.extractLsb'_toNat, e, Nat.shiftRight_eq_div_pow]
  rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl
  · simp [Nat.mod_eq_of_lt hg]
  all_goals simp only [Nat.reduceMul, Nat.one_ne_zero, Nat.reduceEqDiff, ite_false]
  all_goals (rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hg (Nat.pow_le_pow_right (by decide) (by decide)))]; rfl)

theorem qword256_bcast (q : BitVec 64) {k : Nat} (hk : k < 4) : qword256 (q ++ q ++ q ++ q) k = q := by
  rw [qword256_cat _ _ _ _ hk]; split <;> (try split) <;> (try split) <;> rfl

theorem qword256_align (a b : BitVec 256) (n : BitVec 8) {k : Nat} (hk : k < 4) (hn : n.toNat < 4) :
    qword256 (alignQwords a b n) k =
      if k + n.toNat < 4 then qword256 b (k + n.toNat) else qword256 a (k + n.toNat - 4) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [alignQwords, Nat.mod_eq_of_lt hn, qword256, BitVec.getLsbD_extractLsb', hj, decide_true,
    Bool.true_and, BitVec.getLsbD_ushiftRight, Nat.zero_add]
  rw [decide_eq_true (show 64 * k + j < 256 by omega), Bool.true_and, BitVec.getLsbD_append]
  split
  · rename_i h1
    have hc : k + n.toNat < 4 := by omega
    simp only [hc, ite_true, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
    exact congrArg _ (by omega)
  · rename_i h1
    have hc : ¬ k + n.toNat < 4 := by omega
    simp only [hc, ite_false, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
    exact congrArg _ (by omega)

theorem qword256_madd (h : Bool) (dv av v : BitVec 256) {k : Nat} (hk : k < 4) :
    qword256 (madd52 h (lane256 dv 1) (lane256 av 1) (lane256 v 1) ++
      madd52 h (lane256 dv 0) (lane256 av 0) (lane256 v 0)) k =
      mad52 h (qword256 dv k) (qword256 av k) (qword256 v k) := by
  rw [qword256_eq, ← qword_lane256 dv, ← qword_lane256 av, ← qword_lane256 v]
  simp only [lane256]
  rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceDiv, Nat.reduceMul, Nat.reduceMod, lane_app0, lane_app1] <;>
    exact qword_madd52 _ _ _ _ (by decide)

/-! ## Terms -/

/-- A quadword of a vector register, in terms of the start. -/
inductive T
  /-- Quadword `k` of the vector register numbered `r`. -/
  | reg (r : Nat)
  | zero
  /-- `g` in quadword 0, zero elsewhere. -/
  | lane0 (g : G)
  /-- Quadword 0 of `a`, in every quadword. -/
  | bc (a : T)
  /-- Quadword `k` of the 32 bytes at `b + d`. -/
  | ld (b : Reg) (d : Nat)
  /-- `vpmadd52luq`, `vpmadd52huq` (`h`). -/
  | mad (h : Bool) (c a b : T)
  | add (a b : T)
  | shr (a : T) (n : Nat)
  /-- Quadword 0 of `a`, zero elsewhere. -/
  | low (a : T)
  /-- `valignq` of `a` (high) and `b` (low) by `n` quadwords. -/
  | align (a b : T) (n : Nat)
  | and (a b : T)
  | or (a b : T)
  deriving DecidableEq, Repr

def T.eval (s₀ : State) : T → Nat → BitVec 64
  | .reg r, k => qv s₀ (vreg r) k
  | .zero, _ => 0
  | .lane0 g, k => if k = 0 then g.eval s₀ else 0
  | .bc a, _ => a.eval s₀ 0
  | .ld b d, k => s₀.mem.readW (s₀.gpr b + BitVec.ofNat 64 (d + 8 * k)) 64
  | .mad h c a b, k => mad52 h (c.eval s₀ k) (a.eval s₀ k) (b.eval s₀ k)
  | .add a b, k => a.eval s₀ k + b.eval s₀ k
  | .shr a n, k => a.eval s₀ k >>> n
  | .low a, k => if k = 0 then a.eval s₀ 0 else 0
  | .align a b n, k => if k + n < 4 then b.eval s₀ (k + n) else a.eval s₀ (k + n - 4)
  | .and a b, k => a.eval s₀ k &&& b.eval s₀ k
  | .or a b, k => a.eval s₀ k ||| b.eval s₀ k

/-! ## The machine -/

/-- The terms of the thirty-two vector registers (by number) and of `rax`. -/
structure ESym where
  reg : Nat → T
  rax : G

def ESym.init : ESym := ⟨.reg, .gpr .rax⟩

def ESym.set (σ : ESym) (d : VReg) (t : T) : ESym := { σ with reg := fun r => if r = vi d then t else σ.reg r }

def ESym.eop (σ : ESym) : EOp → Option ESym
  | .bin .vpxorq d a b => if a = b then some (σ.set d .zero) else none
  | .bin .vpaddq d a b => some (σ.set d (.add (σ.reg (vi a)) (σ.reg (vi b))))
  | .bin .vpandq d a b => some (σ.set d (.and (σ.reg (vi a)) (σ.reg (vi b))))
  | .bin .vporq d a b => some (σ.set d (.or (σ.reg (vi a)) (σ.reg (vi b))))
  | .shift .vpsrlq d a n => if n.toNat < 64 then some (σ.set d (.shr (σ.reg (vi a)) n.toNat)) else none
  | .vpbroadcastq d a => some (σ.set d (.bc (σ.reg (vi a))))
  | .vmovq d r => if r = .rax then some (σ.set d (.lane0 σ.rax)) else none
  | .vmovqx d a => some (σ.set d (.low (σ.reg (vi a))))
  | .valignq d a b n => if n.toNat < 4 then some (σ.set d (.align (σ.reg (vi a)) (σ.reg (vi b)) n.toNat)) else none
  | _ => none

/-- One instruction, with `lim b` the bytes readable from each base `b`
(which no instruction here changes, but `rax`). -/
def ESym.step (lim : Reg → Nat) (σ : ESym) : Instr → Option ESym
  | .eop o => σ.eop o
  | .mov .rax (.mem m) => (baseOff m).bind fun bo =>
    if bo.1 ≠ .rax ∧ bo.2 + 8 ≤ lim bo.1 then some { σ with rax := .ld bo.1 bo.2 } else none
  | .evLoad d m => (baseOff m).bind fun bo =>
    if bo.1 ≠ .rax ∧ bo.2 + 32 ≤ lim bo.1 then some (σ.set d (.ld bo.1 bo.2)) else none
  | .evMadd52Load h d a m => (baseOff m).bind fun bo =>
    if bo.1 ≠ .rax ∧ bo.2 + 32 ≤ lim bo.1 then
      some (σ.set d (.mad h (σ.reg (vi d)) (σ.reg (vi a)) (.ld bo.1 bo.2)))
    else none
  | _ => none

def ESym.run (lim : Reg → Nat) (σ : ESym) : List Instr → Option ESym
  | [] => some σ
  | i :: is => (σ.step lim i).bind fun σ' => σ'.run lim is

/-! ## The machine agrees -/

/-- `s₀` with the vector registers and `rax` of `s`. -/
def vr (s₀ s : State) : State :=
  { s₀ with
    xmm := s.xmm
    ymmHi := s.ymmHi
    zmmHi := s.zmmHi
    ymmH := s.ymmH
    gpr := fun r => if r = .rax then s.gpr .rax else s₀.gpr r }

/-- The terms `σ` hold in `s`, which differs from `s₀` only in its vector
registers and `rax`. -/
structure SRel (σ : ESym) (s₀ s : State) : Prop where
  reg : ∀ r k, k < 4 → qv s r k = (σ.reg (vi r)).eval s₀ k
  rax : s.gpr .rax = σ.rax.eval s₀
  eq : vr s₀ s = s

theorem SRel.gpr {σ : ESym} {s₀ s : State} (h : SRel σ s₀ s) {r : Reg} (hr : r ≠ .rax) : s.gpr r = s₀.gpr r := by
  rw [← h.eq]; simp only [vr, hr, ite_false]
theorem SRel.mem {σ : ESym} {s₀ s : State} (h : SRel σ s₀ s) : s.mem = s₀.mem := by rw [← h.eq]; rfl
theorem SRel.rd {σ : ESym} {s₀ s : State} (h : SRel σ s₀ s) : s.rd = s₀.rd := by rw [← h.eq]; rfl
theorem SRel.wr {σ : ESym} {s₀ s : State} (h : SRel σ s₀ s) : s.wr = s₀.wr := by rw [← h.eq]; rfl
theorem SRel.mxcsr {σ : ESym} {s₀ s : State} (h : SRel σ s₀ s) : s.mxcsr = s₀.mxcsr := by rw [← h.eq]; rfl
theorem SRel.flags {σ : ESym} {s₀ s : State} (h : SRel σ s₀ s) :
    s.cf = s₀.cf ∧ s.zf = s₀.zf ∧ s.sf = s₀.sf ∧ s.of = s₀.of := by
  rw [← h.eq]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem vr_self (s : State) : vr s s = s := by
  simp only [vr]
  congr 1
  funext r
  split <;> simp_all

theorem SRel.init (s₀ : State) : SRel ESym.init s₀ s₀ :=
  ⟨fun r k _ => by simp only [ESym.init, T.eval, vreg_vi], rfl, vr_self s₀⟩

theorem vr_setVy {s₀ s : State} (h : vr s₀ s = s) (d : VReg) (v : BitVec 256) :
    vr s₀ (s.setVy d v) = s.setVy d v := by
  rw [← h]; cases d <;> rfl

theorem gpr_setVy (s : State) (d : VReg) (v : BitVec 256) (r : Reg) : (s.setVy d v).gpr r = s.gpr r := by
  cases d <;> rfl

theorem SRel.set {σ : ESym} {s₀ s : State} (h : SRel σ s₀ s) {d : VReg} {t : T} {v : BitVec 256}
    (hv : ∀ k, k < 4 → qword256 v k = t.eval s₀ k) : SRel (σ.set d t) s₀ (s.setVy d v) := by
  refine ⟨fun r k hk => ?_, (gpr_setVy s d v .rax).trans h.rax, vr_setVy h.eq d v⟩
  rw [qv_setVy]
  simp only [ESym.set, vi_inj]
  split
  · exact hv k hk
  · exact h.reg r k hk

theorem sstep_ok {lim : Reg → Nat} {s₀ : State} (hc : Ctx lim s₀) {σ σ' : ESym} {s : State}
    (h : SRel σ s₀ s) {i : Instr} (e : σ.step lim i = some σ') :
    ∃ s', exec i s = some s' ∧ SRel σ' s₀ s' := by
  have hR : ∀ a k, k < 4 → (σ.reg (vi a)).eval s₀ k = qv s a k := fun a k hk => (h.reg a k hk).symm
  unfold ESym.step at e
  split at e
  · rename_i o
    refine ⟨o.exec s, rfl, ?_⟩
    unfold ESym.eop at e
    split at e
    · rename_i d a b
      split at e
      · rename_i hab
        cases e
        subst hab
        refine h.set fun k hk => ?_
        rw [qword256_lanes _ _ _ hk]
        simp [EBinOp.sse, XBinOp.eval, qword, T.eval]
      · cases e
    · rename_i d a b
      cases e
      refine h.set fun k hk => ?_
      rw [qword256_lanes _ _ _ hk]
      simp only [EBinOp.sse, T.eval]
      rw [qword_paddq _ _ (mod2_lt k), qword_lane256, qword_lane256, hR a k hk, hR b k hk]; rfl
    · rename_i d a b
      cases e
      refine h.set fun k hk => ?_
      rw [qword256_lanes _ _ _ hk]
      simp only [EBinOp.sse, XBinOp.eval, T.eval]
      rw [qword_and, qword_lane256, qword_lane256, hR a k hk, hR b k hk]; rfl
    · rename_i d a b
      cases e
      refine h.set fun k hk => ?_
      rw [qword256_lanes _ _ _ hk]
      simp only [EBinOp.sse, XBinOp.eval, T.eval]
      rw [qword_or, qword_lane256, qword_lane256, hR a k hk, hR b k hk]; rfl
    · rename_i d a n
      split at e
      · rename_i hn
        cases e
        refine h.set fun k hk => ?_
        rw [qword256_lanes _ _ _ hk]
        simp only [ZShiftOp.sse, T.eval]
        rw [qword_psrlq _ hn (mod2_lt k), qword_lane256, hR a k hk]; rfl
      · cases e
    · rename_i d a
      cases e
      refine h.set fun k hk => ?_
      rw [qword256_bcast _ hk]
      simp only [T.eval]; rw [hR a 0 (by decide)]; rfl
    · rename_i d g
      split at e
      · rename_i hg
        cases e
        subst hg
        refine h.set fun k hk => ?_
        rw [qword256_low _ hk]
        simp only [T.eval, h.rax]
      · cases e
    · rename_i d a
      cases e
      refine h.set fun k hk => ?_
      rw [qword256_low _ hk]
      simp only [T.eval]; rw [hR a 0 (by decide)]; rfl
    · rename_i d a b n
      split at e
      · rename_i hn
        cases e
        refine h.set fun k hk => ?_
        rw [qword256_align _ _ _ hk hn]
        simp only [T.eval]
        split
        · rw [hR b _ (by omega)]; rfl
        · rw [hR a _ (by omega)]; rfl
      · cases e
    · cases e
  · rename_i m
    obtain ⟨⟨b, d⟩, hbo, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    case isFalse => cases e
    rename_i hlt
    cases e
    have ea : s.ea m = s₀.gpr b + BitVec.ofNat 64 d := by rw [baseOff_ok hbo, h.gpr hlt.1]
    have hin : InRegions (s.rd ++ s.wr) (s₀.gpr b + BitVec.ofNat 64 d) 8 := by
      rw [h.rd, h.wr]; exact hc b d 8 (by decide) hlt.2
    refine ⟨s.setReg .rax (s.mem.readW (s₀.gpr b + BitVec.ofNat 64 d) 64), ?_, ?_⟩
    · simp only [exec, readSrc, State.load64, ea, hin, ite_true, Option.map_some]
    · refine ⟨fun r k hk => h.reg r k hk, ?_, ?_⟩
      · simp only [State.setReg, ite_true, G.eval, h.mem]
      · rw [← h.eq]; simp only [vr, State.setReg]; congr 1; funext r; split <;> simp_all
  · rename_i d m
    obtain ⟨⟨b, o⟩, hbo, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    case isFalse => cases e
    rename_i hlt
    cases e
    have ea : s.ea m = s₀.gpr b + BitVec.ofNat 64 o := by rw [baseOff_ok hbo, h.gpr hlt.1]
    have hin : InRegions (s.rd ++ s.wr) (s₀.gpr b + BitVec.ofNat 64 o) 32 := by
      rw [h.rd, h.wr]; exact hc b o 32 (by decide) hlt.2
    refine ⟨s.setVy d (s.mem.readW (s₀.gpr b + BitVec.ofNat 64 o) 256),
      by simp only [exec, ea, State.load256, hin, ite_true, Option.map_some], ?_⟩
    refine h.set fun k hk => ?_
    simp only [T.eval]
    have r1 := readW_extract s.mem (s₀.gpr b + BitVec.ofNat 64 o) (w := 256) (k := 8 * k)
      (n := 8) (by omega)
    rw [qword256, show 64 * k = 8 * (8 * k) by omega, r1, h.mem, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rename_i hh d a m
    obtain ⟨⟨b, o⟩, hbo, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    case isFalse => cases e
    rename_i hlt
    cases e
    have ea : s.ea m = s₀.gpr b + BitVec.ofNat 64 o := by rw [baseOff_ok hbo, h.gpr hlt.1]
    have hin : InRegions (s.rd ++ s.wr) (s₀.gpr b + BitVec.ofNat 64 o) 32 := by
      rw [h.rd, h.wr]; exact hc b o 32 (by decide) hlt.2
    let v := s.mem.readW (s₀.gpr b + BitVec.ofNat 64 o) 256
    refine ⟨s.setVy d (madd52 hh (lane256 (s.vy d) 1) (lane256 (s.vy a) 1) (lane256 v 1) ++
      madd52 hh (lane256 (s.vy d) 0) (lane256 (s.vy a) 0) (lane256 v 0)),
      by simp only [exec, ea, State.load256, hin, ite_true, Option.map_some, v], ?_⟩
    refine h.set fun k hk => ?_
    rw [qword256_madd _ _ _ _ hk]
    simp only [T.eval]
    rw [← qv, ← qv, hR d k hk, hR a k hk]
    congr 1
    have r1 := readW_extract s.mem (s₀.gpr b + BitVec.ofNat 64 o) (w := 256) (k := 8 * k)
      (n := 8) (by omega)
    rw [qword256, show 64 * k = 8 * (8 * k) by omega, r1, h.mem, BitVec.add_assoc, ← BitVec.ofNat_add]
  · cases e

/-- A block of instructions. -/
theorem srun_ok {lim : Reg → Nat} {s₀ : State} (hc : Ctx lim s₀) :
    ∀ (is : List Instr) {σ σ' : ESym} {s : State}, SRel σ s₀ s → σ.run lim is = some σ' →
      WP isa (.block is) s (SRel σ' s₀)
  | [], _, _, _, h, e => by cases e; exact WP.block_nil h
  | i :: is, _, _, _, h, e => by
    simp only [ESym.run, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    obtain ⟨s₁, hx, h₁⟩ := sstep_ok hc h e₁
    exact WP.block_cons_iff.2 ⟨s₁, hx, srun_ok hc is h₁ e₂⟩

/-- A block from a relation. -/
theorem run_ok {lim : Reg → Nat} {s₀ : State} (hc : Ctx lim s₀) {is : List Instr} {σ σ' : ESym}
    {s : State} (h : SRel σ s₀ s) (e : σ.run lim is = some σ') : WP isa (.block is) s (SRel σ' s₀) :=
  srun_ok hc is h e

end VG.Proof.Bignum.X86_64.Ifma
