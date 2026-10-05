import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Load
import VerifiedGarbage.Impl.X25519.X86_64.Ifma
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.X25519.X86_64.Verified
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Lit
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Verified
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Ifma.Sym`. -/
section

/-!
# X25519 on x86-64 with AVX512_IFMA: straight-line vector code, lane by lane

The vector code of `vg_x25519_ifma` computes on the four quadwords (lanes) of
`ymm` registers, and loads and stores 32 bytes at constant offsets from the
working space (`rdi`). `Sym.run` computes each quadword after a block of such
instructions as a term (`T`) in the quadwords, general-purpose registers and
memory before it, and the stores as a list of terms; `srun_ok` proves the
machine agrees. The quadword lemmas of the instructions are Poly1305's
(`Proof/Poly1305/X86_64/Avx2/Sym.lean`), with those of `vpsubq`, `vpxor`,
`vpmadd52luq`, `vpmadd52huq` and `vperm2i128` added here.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi xi_inj qw qword_app0 qword_app1 qword_and
  qword_or qword_paddq qword_punpcklqdq qword_punpckhqdq qword_psllq qword_psrlq pick2
  qword_blendDwords qword256_eq qword256_ymm sel4 sel4_lt qw_setV256 qw_setV128 qw_lane lane_sel
  qw_vbin qw_vshift qw_vmovdqa qw_vpblendd qw_vpbroadcastq qw_vmovq qw_vpermq mod2_lt hv_of)

/-! ## Quadwords of the instructions added here -/

theorem qword_psubq (x y : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XBinOp.eval .psubq x y) i = qword x i - qword y i := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [XBinOp.eval]

theorem qword_xor (x y : BitVec 128) (i : Nat) : qword (x ^^^ y) i = qword x i ^^^ qword y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [qword, hj]

/-- The 52-bit multiply-add of `vpmadd52luq` (`h = false`) and `vpmadd52huq`
on one quadword. -/
def mad52 (h : Bool) (c a b : BitVec 64) : BitVec 64 :=
  let t : BitVec 128 := (a.extractLsb' 0 52).setWidth 128 * (b.extractLsb' 0 52).setWidth 128
  c + (if h then t.extractLsb' 52 52 else t.extractLsb' 0 52).setWidth 64

theorem qword_madd52 (h : Bool) (d a b : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (madd52 h d a b) i = VG.Proof.X25519.X86_64.Ifma.mad52 h (qword d i) (qword a i) (qword b i) := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp only [madd52, qword_app0, qword_app1] <;>
    rfl

theorem mad52_toNat (h : Bool) (c a b : BitVec 64) :
    (VG.Proof.X25519.X86_64.Ifma.mad52 h c a b).toNat = (c.toNat + (if h then a.toNat % 2 ^ 52 * (b.toNat % 2 ^ 52) / 2 ^ 52
      else a.toNat % 2 ^ 52 * (b.toNat % 2 ^ 52) % 2 ^ 52)) % 2 ^ 64 := by
  have ha : a.toNat % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hb : b.toNat % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hp : a.toNat % 2 ^ 52 * (b.toNat % 2 ^ 52) < 2 ^ 128 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (by decide)) (by decide)
  have hq : a.toNat % 2 ^ 52 * (b.toNat % 2 ^ 52) / 2 ^ 52 < 2 ^ 52 :=
    Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (by decide))
      (by decide))
  have e : ∀ x : BitVec 64, (x.extractLsb' 0 52).toNat = x.toNat % 2 ^ 52 := fun x => by
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  have h1 : a.toNat % 2 ^ 52 % 2 ^ 128 = a.toNat % 2 ^ 52 := Nat.mod_eq_of_lt (by omega)
  have h2 : b.toNat % 2 ^ 52 % 2 ^ 128 = b.toNat % 2 ^ 52 := Nat.mod_eq_of_lt (by omega)
  cases h
  · simp only [VG.Proof.X25519.X86_64.Ifma.mad52, Bool.false_eq_true, ite_false, BitVec.toNat_add, BitVec.toNat_setWidth,
      BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_mul, e, h1, h2, Nat.mod_eq_of_lt hp]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide) :
      a.toNat % 2 ^ 52 * (b.toNat % 2 ^ 52) % 2 ^ 52 < 2 ^ 64)]
  · simp only [VG.Proof.X25519.X86_64.Ifma.mad52, ite_true, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat,
      BitVec.toNat_mul, e, Nat.shiftRight_eq_div_pow, h1, h2, Nat.mod_eq_of_lt hp]
    rw [Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hq (by decide) :
      a.toNat % 2 ^ 52 * (b.toNat % 2 ^ 52) / 2 ^ 52 < 2 ^ 64)]

theorem qw_madd52 (h : Bool) (s : State) (d a b r : XReg) {k : Nat} (hk : k < 4) :
    qw ((if h then VOp.vpmadd52huq .l256 d a b else VOp.vpmadd52luq .l256 d a b).exec s) r k =
      if r = d then VG.Proof.X25519.X86_64.Ifma.mad52 h (qw s d k) (qw s a k) (qw s b k) else qw s r k := by
  have e : (if h then VOp.vpmadd52huq .l256 d a b else VOp.vpmadd52luq .l256 d a b).exec s =
      s.setV .l256 d (madd52 h (s.lane d 0) (s.lane a 0) (s.lane b 0))
        (madd52 h (s.lane d 1) (s.lane a 1) (s.lane b 1)) := by
    cases h <;> rfl
  rw [e, qw_setV256]
  split
  · have e2 : (if k / 2 = 0 then madd52 h (s.lane d 0) (s.lane a 0) (s.lane b 0)
        else madd52 h (s.lane d 1) (s.lane a 1) (s.lane b 1)) =
        madd52 h (s.lane d (k / 2)) (s.lane a (k / 2)) (s.lane b (k / 2)) := by
      rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;> rfl
    rw [e2, VG.Proof.X25519.X86_64.Ifma.qword_madd52 _ _ _ _ (mod2_lt k), qw_lane, qw_lane, qw_lane]
  · rfl

theorem qw_lo (s : State) (d a b r : XReg) {k : Nat} (hk : k < 4) :
    qw ((VOp.vpmadd52luq .l256 d a b).exec s) r k =
      if r = d then VG.Proof.X25519.X86_64.Ifma.mad52 false (qw s d k) (qw s a k) (qw s b k) else qw s r k :=
  VG.Proof.X25519.X86_64.Ifma.qw_madd52 false s d a b r hk

theorem qw_hi (s : State) (d a b r : XReg) {k : Nat} (hk : k < 4) :
    qw ((VOp.vpmadd52huq .l256 d a b).exec s) r k =
      if r = d then VG.Proof.X25519.X86_64.Ifma.mad52 true (qw s d k) (qw s a k) (qw s b k) else qw s r k :=
  VG.Proof.X25519.X86_64.Ifma.qw_madd52 true s d a b r hk

/-- `vperm2i128 d, a, b, 0x20` (`hi = false`: the low lanes of `a` and `b`)
and `0x31` (the high lanes). -/
def p2imm (hi : Bool) : BitVec 8 := if hi then 0x31 else 0x20

theorem qw_vperm2i128 (s : State) (d a b r : XReg) (hi : Bool) {k : Nat} (hk : k < 4) :
    qw ((VOp.vperm2i128 d a b (VG.Proof.X25519.X86_64.Ifma.p2imm hi)).exec s) r k =
      if r = d then (if k < 2 then qw s a (if hi then k + 2 else k)
        else qw s b (if hi then k else k - 2)) else qw s r k := by
  simp only [VOp.exec, qw_setV256]
  split
  · cases hi <;> rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;> rfl
  · rfl

/-! ## Terms -/

/-- A quadword, in terms of those where the code starts. -/
inductive T
  /-- Quadword `k` of the vector register numbered `r`. -/
  | reg (r : Nat)
  /-- A general-purpose register, in every quadword. -/
  | gpr (r : Reg)
  | zero
  /-- `a` in quadword 0, zero elsewhere. -/
  | lane0 (a : VG.Proof.X25519.X86_64.Ifma.T)
  /-- Quadword 0 of `a`, in every quadword. -/
  | bc (a : VG.Proof.X25519.X86_64.Ifma.T)
  /-- Quadword `k` of the 32 bytes at `rdi + d`. -/
  | ld (d : Nat)
  | add (a b : VG.Proof.X25519.X86_64.Ifma.T)
  | sub (a b : VG.Proof.X25519.X86_64.Ifma.T)
  | and (a b : VG.Proof.X25519.X86_64.Ifma.T)
  | xor (a b : VG.Proof.X25519.X86_64.Ifma.T)
  | or (a b : VG.Proof.X25519.X86_64.Ifma.T)
  | shl (a : VG.Proof.X25519.X86_64.Ifma.T) (n : Nat)
  | shr (a : VG.Proof.X25519.X86_64.Ifma.T) (n : Nat)
  | unpl (a b : VG.Proof.X25519.X86_64.Ifma.T)
  | unph (a b : VG.Proof.X25519.X86_64.Ifma.T)
  | perm (a : VG.Proof.X25519.X86_64.Ifma.T) (o : Nat)
  | blend (a b : VG.Proof.X25519.X86_64.Ifma.T) (sel : Nat)
  /-- `vpmadd52luq`, `vpmadd52huq` (`h`). -/
  | mad (h : Bool) (c a b : VG.Proof.X25519.X86_64.Ifma.T)
  /-- `vperm2i128` with `p2imm hi`. -/
  | p2 (a b : VG.Proof.X25519.X86_64.Ifma.T) (hi : Bool)
  /-- `a` in quadwords 0 and 1, zero in the others (`vzeroupper`). -/
  | low (a : VG.Proof.X25519.X86_64.Ifma.T)
  deriving DecidableEq, Repr

def T.eval (s₀ : State) : VG.Proof.X25519.X86_64.Ifma.T → Nat → BitVec 64
  | .reg r, k => qw s₀ (xr r) k
  | .gpr r, _ => s₀.gpr r
  | .zero, _ => 0
  | .lane0 a, k => if k = 0 then a.eval s₀ 0 else 0
  | .bc a, _ => a.eval s₀ 0
  | .ld d, k => s₀.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (d + 8 * k)) 64
  | .add a b, k => a.eval s₀ k + b.eval s₀ k
  | .sub a b, k => a.eval s₀ k - b.eval s₀ k
  | .and a b, k => a.eval s₀ k &&& b.eval s₀ k
  | .xor a b, k => a.eval s₀ k ^^^ b.eval s₀ k
  | .or a b, k => a.eval s₀ k ||| b.eval s₀ k
  | .shl a n, k => a.eval s₀ k <<< n
  | .shr a n, k => a.eval s₀ k >>> n
  | .unpl a b, k => if k % 2 = 0 then a.eval s₀ k else b.eval s₀ (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.eval s₀ (k + 1) else b.eval s₀ k
  | .perm a o, k => a.eval s₀ (sel4 o k)
  | .blend a b sel, k => pick2 (a.eval s₀ k) (b.eval s₀ k) (sel.testBit (2 * k)) (sel.testBit (2 * k + 1))
  | .mad h c a b, k => VG.Proof.X25519.X86_64.Ifma.mad52 h (c.eval s₀ k) (a.eval s₀ k) (b.eval s₀ k)
  | .p2 a b hi, k => if k < 2 then a.eval s₀ (if hi then k + 2 else k)
    else b.eval s₀ (if hi then k else k - 2)
  | .low a, k => if k < 2 then a.eval s₀ k else 0

/-- The 256 bits of four quadwords. -/
def T.val (s₀ : State) (t : VG.Proof.X25519.X86_64.Ifma.T) : BitVec 256 :=
  t.eval s₀ 3 ++ t.eval s₀ 2 ++ t.eval s₀ 1 ++ t.eval s₀ 0

/-! ## The machine -/

/-- The terms of the vector registers (by number), and the stores so far
(offset and term), the last first. -/
structure Sym where
  reg : Nat → VG.Proof.X25519.X86_64.Ifma.T
  st : List (Nat × VG.Proof.X25519.X86_64.Ifma.T)

def Sym.init : VG.Proof.X25519.X86_64.Ifma.Sym := ⟨.reg, []⟩

def Sym.set (σ : VG.Proof.X25519.X86_64.Ifma.Sym) (d : XReg) (t : VG.Proof.X25519.X86_64.Ifma.T) : VG.Proof.X25519.X86_64.Ifma.Sym := { σ with
                                                           reg := fun r => if r = xi d then t else σ.reg r }

def Sym.bin (σ : VG.Proof.X25519.X86_64.Ifma.Sym) (op : VBinOp) (d a b : XReg) : Option VG.Proof.X25519.X86_64.Ifma.Sym :=
  let A := σ.reg (xi a)
  let B := σ.reg (xi b)
  match op with
  | .vpaddq => some (σ.set d (.add A B))
  | .vpsubq => some (σ.set d (.sub A B))
  | .vpand => some (σ.set d (.and A B))
  | .vpxor => some (σ.set d (if a = b then .zero else .xor A B))
  | .vpor => some (σ.set d (.or A B))
  | .vpunpcklqdq => some (σ.set d (.unpl A B))
  | .vpunpckhqdq => some (σ.set d (.unph A B))
  | _ => none

def Sym.shift (σ : VG.Proof.X25519.X86_64.Ifma.Sym) (op : XShiftOp) (d a : XReg) (n : BitVec 8) : Option VG.Proof.X25519.X86_64.Ifma.Sym :=
  if n.toNat < 64 then
    match op with
    | .psllq => some (σ.set d (.shl (σ.reg (xi a)) n.toNat))
    | .psrlq => some (σ.set d (.shr (σ.reg (xi a)) n.toNat))
    | _ => none
  else none

def Sym.vop (σ : VG.Proof.X25519.X86_64.Ifma.Sym) : VOp → Option VG.Proof.X25519.X86_64.Ifma.Sym
  | .vbin op .l256 d a b => σ.bin op d a b
  | .vshift op .l256 d a n => σ.shift op d a n
  | .vmovdqa .l256 d a => some (σ.set d (σ.reg (xi a)))
  | .vpblendd .l256 d a b sel => some (σ.set d (.blend (σ.reg (xi a)) (σ.reg (xi b)) sel.toNat))
  | .vpbroadcastq .l256 d a => some (σ.set d (.bc (σ.reg (xi a))))
  | .vmovq d r => some (σ.set d (.lane0 (.gpr r)))
  | .vpermq d a o => some (σ.set d (.perm (σ.reg (xi a)) o.toNat))
  | .vpmadd52luq .l256 d a b =>
    some (σ.set d (.mad false (σ.reg (xi d)) (σ.reg (xi a)) (σ.reg (xi b))))
  | .vpmadd52huq .l256 d a b =>
    some (σ.set d (.mad true (σ.reg (xi d)) (σ.reg (xi a)) (σ.reg (xi b))))
  | .vperm2i128 d a b sel =>
    if sel = VG.Proof.X25519.X86_64.Ifma.p2imm false then some (σ.set d (.p2 (σ.reg (xi a)) (σ.reg (xi b)) false))
    else if sel = VG.Proof.X25519.X86_64.Ifma.p2imm true then some (σ.set d (.p2 (σ.reg (xi a)) (σ.reg (xi b)) true))
    else none
  | .vzeroupper => some { σ with reg := fun r => .low (σ.reg r) }
  | _ => none

/-- The offset of `[rdi + d]`. -/
def rdiOff (m : MemOp) : Option Nat :=
  if m.base = .rdi ∧ m.index = none then
    match m.disp with
    | .ofNat n => some n
    | _ => none
  else none

/-- Whether the 32 bytes at `d` miss every store. -/
def Sym.fresh (σ : VG.Proof.X25519.X86_64.Ifma.Sym) (d : Nat) : Bool := σ.st.all fun (e, _) => d + 32 ≤ e || e + 32 ≤ d

/-- One instruction. Loads read only what no store wrote. -/
def Sym.step (σ : VG.Proof.X25519.X86_64.Ifma.Sym) : Instr → Option VG.Proof.X25519.X86_64.Ifma.Sym
  | .vop o => σ.vop o
  | .vmovdquLoad .l256 d m => (VG.Proof.X25519.X86_64.Ifma.rdiOff m).bind fun o =>
    if o + 32 ≤ 4096 ∧ σ.fresh o then some (σ.set d (.ld o)) else none
  | .vmovdquStore .l256 m r => (VG.Proof.X25519.X86_64.Ifma.rdiOff m).bind fun o =>
    if o + 32 ≤ 4096 then some { σ with st := (o, σ.reg (xi r)) :: σ.st } else none
  | _ => none

def Sym.run (σ : VG.Proof.X25519.X86_64.Ifma.Sym) : List Instr → Option VG.Proof.X25519.X86_64.Ifma.Sym
  | [] => some σ
  | i :: is => (σ.step i).bind fun σ' => σ'.run is

/-! ## The machine agrees -/

/-- The stores `st` (the last first) applied to `m`, at `base + d`. -/
def stores (s₀ : State) (base : Addr) : List (Nat × VG.Proof.X25519.X86_64.Ifma.T) → Mem → Mem
  | [], m => m
  | (d, t) :: st, m => (VG.Proof.X25519.X86_64.Ifma.stores s₀ base st m).writeW (base + BitVec.ofNat 64 d) (t.val s₀)

/-- `s₀` with the vector registers and memory of `s`. -/
def vm (s₀ s : State) : State := { s₀ with xmm := s.xmm, ymmHi := s.ymmHi, zmmHi := s.zmmHi, mem := s.mem }

/-- The terms `σ` hold in `s`, which differs from `s₀` only in its vector
registers and the stores of `σ`. -/
structure SRel (σ : VG.Proof.X25519.X86_64.Ifma.Sym) (s₀ s : State) : Prop where
  reg : ∀ r k, k < 4 → qw s r k = (σ.reg (xi r)).eval s₀ k
  eq : VG.Proof.X25519.X86_64.Ifma.vm s₀ s = s
  mem : s.mem = VG.Proof.X25519.X86_64.Ifma.stores s₀ (s₀.gpr .rdi) σ.st s₀.mem

theorem SRel.gpr {σ : VG.Proof.X25519.X86_64.Ifma.Sym} {s₀ s : State} (h : VG.Proof.X25519.X86_64.Ifma.SRel σ s₀ s) : s.gpr = s₀.gpr := by rw [← h.eq]; rfl
theorem SRel.rd {σ : VG.Proof.X25519.X86_64.Ifma.Sym} {s₀ s : State} (h : VG.Proof.X25519.X86_64.Ifma.SRel σ s₀ s) : s.rd = s₀.rd := by rw [← h.eq]; rfl
theorem SRel.wr {σ : VG.Proof.X25519.X86_64.Ifma.Sym} {s₀ s : State} (h : VG.Proof.X25519.X86_64.Ifma.SRel σ s₀ s) : s.wr = s₀.wr := by rw [← h.eq]; rfl
theorem SRel.mxcsr {σ : VG.Proof.X25519.X86_64.Ifma.Sym} {s₀ s : State} (h : VG.Proof.X25519.X86_64.Ifma.SRel σ s₀ s) : s.mxcsr = s₀.mxcsr := by
  rw [← h.eq]; rfl
theorem SRel.flags {σ : VG.Proof.X25519.X86_64.Ifma.Sym} {s₀ s : State} (h : VG.Proof.X25519.X86_64.Ifma.SRel σ s₀ s) :
    s.cf = s₀.cf ∧ s.zf = s₀.zf ∧ s.sf = s₀.sf ∧ s.of = s₀.of := by
  rw [← h.eq]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem SRel.init (s₀ : State) : VG.Proof.X25519.X86_64.Ifma.SRel Sym.init s₀ s₀ :=
  ⟨fun r k _ => by simp only [Sym.init, T.eval, xr_xi], rfl, rfl⟩

theorem vm_vop {s₀ s : State} (h : VG.Proof.X25519.X86_64.Ifma.vm s₀ s = s) (o : VOp) : VG.Proof.X25519.X86_64.Ifma.vm s₀ (o.exec s) = o.exec s := by
  rw [← h]
  cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl

theorem vm_setV {s₀ s : State} (h : VG.Proof.X25519.X86_64.Ifma.vm s₀ s = s) (len : VLen) (d : XReg) (lo hi : BitVec 128) :
    VG.Proof.X25519.X86_64.Ifma.vm s₀ (s.setV len d lo hi) = s.setV len d lo hi := by
  rw [← h]; rfl

theorem SRel.set {σ : VG.Proof.X25519.X86_64.Ifma.Sym} {s₀ s : State} (h : VG.Proof.X25519.X86_64.Ifma.SRel σ s₀ s) {d : XReg} {t : VG.Proof.X25519.X86_64.Ifma.T} {s' : State}
    (hv : ∀ r k, k < 4 → qw s' r k = if r = d then t.eval s₀ k else qw s r k)
    (he : VG.Proof.X25519.X86_64.Ifma.vm s₀ s' = s') (hm : s'.mem = s.mem) : VG.Proof.X25519.X86_64.Ifma.SRel (σ.set d t) s₀ s' := by
  refine ⟨fun r k hk => ?_, he, hm.trans h.mem⟩
  rw [hv r k hk]
  simp only [Sym.set, xi_inj]
  split
  · rfl
  · exact h.reg r k hk

/-- The working space the code may load from and store to: every offset
`d` of a load or store is readable and writable at `rdi + d`. -/
def Ctx (s₀ : State) : Prop :=
  ∀ d, d + 32 ≤ 4096 → InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofNat 64 d) 32

theorem rdiOff_ok {m : MemOp} {o : Nat} (h : VG.Proof.X25519.X86_64.Ifma.rdiOff m = some o) (s : State) :
    s.ea m = s.gpr .rdi + BitVec.ofNat 64 o := by
  unfold VG.Proof.X25519.X86_64.Ifma.rdiOff at h
  split at h
  · rename_i hb
    split at h
    · rename_i n hn
      cases h
      simp only [State.ea, hb.1, hb.2, hn]
      exact congrArg _ (BitVec.ofInt_natCast ..)
    · cases h
  · cases h

theorem eq_of_qword256 {x y : BitVec 256} (h : ∀ k < 4, qword256 x k = qword256 y k) : x = y := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have := congrArg (fun v => v.getLsbD (j % 64)) (h (j / 64) (by omega))
  simp only [qword256, BitVec.getLsbD_extractLsb', show j % 64 < 64 by omega, decide_true,
    Bool.true_and, show 64 * (j / 64) + j % 64 = j by omega] at this
  exact this

theorem ymm_eq_qw (s : State) (r : XReg) :
    s.ymm r = qw s r 3 ++ qw s r 2 ++ qw s r 1 ++ qw s r 0 := by
  refine VG.Proof.X25519.X86_64.Ifma.eq_of_qword256 fun k hk => ?_
  rw [qword256_ymm _ _ hk, VG.Proof.Poly1305.X86_64.Avx2.qword256_cat _ _ _ _ hk]
  rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;> rfl

/-- A read of the 32 bytes at `d` that miss every store. -/
theorem stores_fresh (s₀ : State) (base : Addr) (m : Mem) :
    ∀ (st : List (Nat × VG.Proof.X25519.X86_64.Ifma.T)) {d : Nat}, d < 2 ^ 62 → (∀ e ∈ st, e.1 < 2 ^ 62) →
      (st.all fun (e, _) => d + 32 ≤ e || e + 32 ≤ d) = true →
      (VG.Proof.X25519.X86_64.Ifma.stores s₀ base st m).readW (base + BitVec.ofNat 64 d) 256 = m.readW (base + BitVec.ofNat 64 d) 256
  | [], _, _, _, _ => rfl
  | (e, t) :: st, d, hd, he, hf => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hf
    have e1 := readW_writeW_off (VG.Proof.X25519.X86_64.Ifma.stores s₀ base st m) base (t.val s₀) (d := d) (e := e) (n := 32)
      (by omega) (by have := he _ (List.mem_cons_self ..); simp at this; omega) (by omega)
    have e2 := VG.Proof.X25519.X86_64.Ifma.stores_fresh s₀ base m st hd (fun x hx => he x (List.mem_cons_of_mem _ hx)) hf.2
    exact e1.trans e2

theorem qw_load' (s : State) (d r : XReg) (a : Addr) (v : BitVec 256) (hv : v = s.mem.readW a 256)
    {k : Nat} (hk : k < 4) :
    qw (s.setV .l256 d (v.extractLsb' 0 128) (v.extractLsb' 128 128)) r k =
      if r = d then s.mem.readW (a + BitVec.ofNat 64 (8 * k)) 64 else qw s r k := by
  subst hv; exact VG.Proof.Poly1305.X86_64.Avx2.qw_load s d r a hk

/-- Offsets are small. -/
def Sym.small (σ : VG.Proof.X25519.X86_64.Ifma.Sym) : Prop := ∀ e ∈ σ.st, e.1 < 4096

theorem sstep_ok {s₀ : State} (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s₀) {σ σ' : VG.Proof.X25519.X86_64.Ifma.Sym} {s : State}
    (h : VG.Proof.X25519.X86_64.Ifma.SRel σ s₀ s) (hs : σ.small) {i : Instr} (e : σ.step i = some σ') :
    ∃ s', exec i s = some s' ∧ VG.Proof.X25519.X86_64.Ifma.SRel σ' s₀ s' ∧ σ'.small := by
  have hR : ∀ a k, k < 4 → (σ.reg (xi a)).eval s₀ k = qw s a k := fun a k hk => (h.reg a k hk).symm
  unfold Sym.step at e
  split at e
  · rename_i o
    refine ⟨o.exec s, rfl, ?_⟩
    have he := VG.Proof.X25519.X86_64.Ifma.vm_vop h.eq o
    have hm : (o.exec s).mem = s.mem := VOp.exec_mem o s
    unfold Sym.vop at e
    split at e
    · rename_i op d a b
      unfold Sym.bin at e
      split at e <;> cases e <;>
        refine ⟨h.set (hv_of (fun k hk => ?_) (fun r hr k _ => by rw [qw_vbin, ite_eq_right hr])) he hm,
          hs⟩ <;>
        rw [qw_vbin, ite_eq_left rfl] <;> simp only [VBinOp.sse, T.eval]
      · rw [qword_paddq _ _ (mod2_lt k), qw_lane, qw_lane, hR a k hk, hR b k hk]
      · rw [VG.Proof.X25519.X86_64.Ifma.qword_psubq _ _ (mod2_lt k), qw_lane, qw_lane, hR a k hk, hR b k hk]
      · rw [XBinOp.eval, qword_and, qw_lane, qw_lane, hR a k hk, hR b k hk]
      · rw [XBinOp.eval, VG.Proof.X25519.X86_64.Ifma.qword_xor, qw_lane, qw_lane]
        split
        · subst_vars; simp [T.eval]
        · rw [T.eval, hR a k hk, hR b k hk]
      · rw [XBinOp.eval, qword_or, qw_lane, qw_lane, hR a k hk, hR b k hk]
      · rw [qword_punpcklqdq _ _ (mod2_lt k)]
        split
        · rename_i h0; rw [hR a k hk, qw, h0]
        · rw [hR b (k - 1) (by omega), qw, show (k - 1) / 2 = k / 2 by omega,
            show (k - 1) % 2 = 0 by omega]
      · rw [qword_punpckhqdq _ _ (mod2_lt k)]
        split
        · rw [hR a (k + 1) (by omega), qw, show (k + 1) / 2 = k / 2 by omega,
            show (k + 1) % 2 = 1 by omega]
        · rw [hR b k hk, qw, show k % 2 = 1 by omega]
    · rename_i op d a n
      unfold Sym.shift at e
      split at e
      · rename_i hn
        split at e <;> cases e <;>
          refine ⟨h.set (hv_of (fun k hk => ?_) (fun r hr k _ => by rw [qw_vshift, ite_eq_right hr]))
            he hm, hs⟩ <;>
          rw [qw_vshift, ite_eq_left rfl] <;> simp only [T.eval]
        · rw [qword_psllq _ hn (mod2_lt k), qw_lane, hR a k hk]
        · rw [qword_psrlq _ hn (mod2_lt k), qw_lane, hR a k hk]
      · cases e
    · rename_i d a
      cases e
      exact ⟨h.set (hv_of (fun k hk => by rw [qw_vmovdqa _ _ _ _ hk, ite_eq_left rfl, hR a k hk])
        (fun r hr k hk => by rw [qw_vmovdqa _ _ _ _ hk, ite_eq_right hr])) he hm, hs⟩
    · rename_i d a b n
      cases e
      exact ⟨h.set (hv_of (fun k hk => by
          rw [qw_vpblendd _ _ _ _ _ _ hk, ite_eq_left rfl]; simp only [T.eval]; rw [hR a k hk, hR b k hk])
        (fun r hr k hk => by rw [qw_vpblendd _ _ _ _ _ _ hk, ite_eq_right hr])) he hm, hs⟩
    · rename_i d a
      cases e
      exact ⟨h.set (hv_of (fun k _ => by rw [qw_vpbroadcastq, ite_eq_left rfl]; exact (hR a 0 (by decide)).symm)
        (fun r hr k _ => by rw [qw_vpbroadcastq, ite_eq_right hr])) he hm, hs⟩
    · rename_i d g
      cases e
      exact ⟨h.set (hv_of (fun k hk => by rw [qw_vmovq _ _ _ _ hk, ite_eq_left rfl]; simp only [T.eval, h.gpr])
        (fun r hr k hk => by rw [qw_vmovq _ _ _ _ hk, ite_eq_right hr])) he hm, hs⟩
    · rename_i d a o
      cases e
      exact ⟨h.set (hv_of (fun k hk => by
          rw [qw_vpermq _ _ _ _ _ hk, ite_eq_left rfl]; simp only [T.eval]; rw [hR a _ (sel4_lt _ _)])
        (fun r hr k hk => by rw [qw_vpermq _ _ _ _ _ hk, ite_eq_right hr])) he hm, hs⟩
    · rename_i d a b
      cases e
      have q := fun r k (hk : k < 4) => VG.Proof.X25519.X86_64.Ifma.qw_lo s d a b r hk
      exact ⟨h.set (hv_of (fun k hk => by
          rw [q d k hk, ite_eq_left rfl]; simp only [T.eval]; rw [hR d k hk, hR a k hk, hR b k hk])
        (fun r hr k hk => by rw [q r k hk, ite_eq_right hr])) he hm, hs⟩
    · rename_i d a b
      cases e
      have q := fun r k (hk : k < 4) => VG.Proof.X25519.X86_64.Ifma.qw_hi s d a b r hk
      exact ⟨h.set (hv_of (fun k hk => by
          rw [q d k hk, ite_eq_left rfl]; simp only [T.eval]; rw [hR d k hk, hR a k hk, hR b k hk])
        (fun r hr k hk => by rw [q r k hk, ite_eq_right hr])) he hm, hs⟩
    · rename_i d a b sel
      have p2ok : ∀ hi, sel = VG.Proof.X25519.X86_64.Ifma.p2imm hi → σ.set d (.p2 (σ.reg (xi a)) (σ.reg (xi b)) hi) = σ' →
          VG.Proof.X25519.X86_64.Ifma.SRel σ' s₀ ((VOp.vperm2i128 d a b sel).exec s) ∧ σ'.small := by
        intro hi hs' e'
        subst hs' e'
        refine ⟨h.set (hv_of (fun k hk => ?_) (fun r hr k hk => by
          rw [VG.Proof.X25519.X86_64.Ifma.qw_vperm2i128 _ _ _ _ _ _ hk, ite_eq_right hr])) he hm, hs⟩
        rw [VG.Proof.X25519.X86_64.Ifma.qw_vperm2i128 _ _ _ _ _ _ hk, ite_eq_left rfl]; simp only [T.eval]
        split
        · rw [hR a _ (by split <;> omega)]
        · rw [hR b _ (by split <;> omega)]
      split at e
      · rename_i h0; cases e; exact p2ok false h0 rfl
      · split at e
        · rename_i h1; cases e; exact p2ok true h1 rfl
        · cases e
    · cases e
      refine ⟨⟨fun r k hk => ?_, he, hm.trans h.mem⟩, hs⟩
      simp only [T.eval]
      simp only [VOp.exec, qw, State.lane]
      rcases cases4 hk with rfl | rfl | rfl | rfl <;> simp [hR] <;> rfl
    · cases e
  · rename_i d m
    obtain ⟨o, ho, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    case isFalse => cases e
    rename_i hf
    cases e
    have ea : s.ea m = s₀.gpr .rdi + BitVec.ofNat 64 o := by rw [VG.Proof.X25519.X86_64.Ifma.rdiOff_ok ho, h.gpr]
    have hin : InRegions (s.rd ++ s.wr) (s₀.gpr .rdi + BitVec.ofNat 64 o) 32 := by
      rw [h.wr]
      obtain ⟨r, hr, hc⟩ := hc o (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    refine ⟨s.setV .l256 d ((s.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 o) 256).extractLsb' 0 128)
      ((s.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 o) 256).extractLsb' 128 128),
      by simp only [exec, ea, State.load256, hin, ite_true, Option.map_some], ?_, hs⟩
    refine h.set (hv_of (fun k hk => ?_) (fun r hr k hk => by rw [VG.Proof.X25519.X86_64.Ifma.qw_load' _ _ _ _ _ rfl hk, ite_eq_right hr]))
      (VG.Proof.X25519.X86_64.Ifma.vm_setV h.eq _ _ _ _) rfl
    rw [VG.Proof.X25519.X86_64.Ifma.qw_load' _ _ _ _ _ rfl hk, ite_eq_left rfl]
    simp only [T.eval]
    have r1 := readW_extract s.mem (s₀.gpr .rdi + BitVec.ofNat 64 o) (w := 256) (k := 8 * k) (n := 8)
      (by omega)
    have r2 := readW_extract s₀.mem (s₀.gpr .rdi + BitVec.ofNat 64 o) (w := 256) (k := 8 * k) (n := 8)
      (by omega)
    rw [h.mem, VG.Proof.X25519.X86_64.Ifma.stores_fresh _ _ _ _ (by omega) (fun e he => by have := hs e he; omega) hf.2] at r1
    rw [BitVec.add_assoc, ← BitVec.ofNat_add] at r2
    rw [h.mem]
    exact r1.symm.trans r2
  · rename_i m r
    obtain ⟨o, ho, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    case isFalse => cases e
    rename_i hlt
    cases e
    have ea : s.ea m = s₀.gpr .rdi + BitVec.ofNat 64 o := by rw [VG.Proof.X25519.X86_64.Ifma.rdiOff_ok ho, h.gpr]
    have hin : InRegions s.wr (s₀.gpr .rdi + BitVec.ofNat 64 o) 32 := by
      rw [h.wr]; exact hc o (by omega)
    have hy : s.ymm r = (σ.reg (xi r)).val s₀ := by
      rw [VG.Proof.X25519.X86_64.Ifma.ymm_eq_qw, T.val, h.reg r 3 (by decide), h.reg r 2 (by decide), h.reg r 1 (by decide),
        h.reg r 0 (by decide)]
    refine ⟨{ s with mem := s.mem.writeW (s₀.gpr .rdi + BitVec.ofNat 64 o) (s.ymm r) },
      by simp only [exec, ea, State.store256, hin, ite_true], ⟨fun r' k hk => h.reg r' k hk, ?_, ?_⟩,
      fun e he => ?_⟩
    · rw [← h.eq]; rfl
    · simp only [VG.Proof.X25519.X86_64.Ifma.stores, hy, h.mem]
    · simp only [List.mem_cons] at he
      rcases he with rfl | he
      · simp only; omega
      · exact hs e he
  · cases e

/-- A block of instructions. -/
theorem srun_ok {s₀ : State} (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s₀) :
    ∀ (is : List Instr) {σ σ' : VG.Proof.X25519.X86_64.Ifma.Sym} {s : State}, VG.Proof.X25519.X86_64.Ifma.SRel σ s₀ s → σ.small → σ.run is = some σ' →
      WP isa (.block is) s (VG.Proof.X25519.X86_64.Ifma.SRel σ' s₀)
  | [], _, _, _, h, _, e => by cases e; exact WP.block_nil h
  | i :: is, _, _, _, h, hs, e => by
    simp only [Sym.run, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    obtain ⟨s₁, hx, h₁, hs₁⟩ := VG.Proof.X25519.X86_64.Ifma.sstep_ok hc h hs e₁
    exact WP.block_cons_iff.2 ⟨s₁, hx, VG.Proof.X25519.X86_64.Ifma.srun_ok hc is h₁ hs₁ e₂⟩

/-- A block from its start. -/
theorem run_ok {s₀ : State} (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s₀) {is : List Instr} {σ : VG.Proof.X25519.X86_64.Ifma.Sym}
    (e : Sym.init.run is = some σ) : WP isa (.block is) s₀ (VG.Proof.X25519.X86_64.Ifma.SRel σ s₀) :=
  VG.Proof.X25519.X86_64.Ifma.srun_ok hc is (SRel.init s₀) (fun _ h => by cases h) e

end VG.Proof.X25519.X86_64.Ifma

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Ifma.Bound`. -/
section

/-!
# X25519 on x86-64 with AVX512_IFMA: terms as numbers

The limbs the ladder computes stay below `2⁶⁴`, and its differences never go
negative, so its additions, subtractions, multiply-adds and shifts never wrap.
`T.bnd` and `T.lb` bound each term from above and below, from bounds on the
registers and memory a block starts from; `T.ok` checks that nothing wraps
under those bounds (and that every blend picks whole quadwords); and `T.nat`
is its value as a number, with the reductions modulo `2⁶⁴` left out. `nat_ok`
proves that a term is `T.nat` and within its bounds where the kernel evaluates
`T.ok` of concrete terms to `true`, so the number a block computes is `nat` of
its term, which unfolds to the arithmetic of the ladder by definition.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi qw pick2 sel4 sel4_lt capW capW_ge orB orB_ge)

/-- Bounds on what a block starts from: the quadwords of each vector register
(`v`), each general-purpose register (`g`), and each quadword of the 32
bytes at each offset of the working space, from above (`m`) and below
(`ml`). -/
structure Bnds where
  v : Nat → Nat
  g : Reg → Nat
  m : Nat → Nat
  ml : Nat → Nat

/-- The values a block starts from, as numbers. -/
structure Env where
  v : Nat → Nat → Nat
  g : Reg → Nat
  m : Nat → Nat → Nat

def envOf (s₀ : State) : VG.Proof.X25519.X86_64.Ifma.Env :=
  ⟨fun r k => (qw s₀ (xr r) k).toNat, fun g => (s₀.gpr g).toNat,
    fun d k => (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (d + 8 * k)) 64).toNat⟩

/-- Whether `vpblendd`'s selector takes quadword `k` from its second source
(`some true`), its first (`some false`), or doublewords of both (`none`). -/
def selQ (sel k : Nat) : Option Bool :=
  match sel.testBit (2 * k), sel.testBit (2 * k + 1) with
  | true, true => some true
  | false, false => some false
  | _, _ => none

/-- The bound on the low 52 bits of a product. -/
def loB (a b : Nat) : Nat := min (2 ^ 52 - 1) (min a (2 ^ 52 - 1) * min b (2 ^ 52 - 1))
/-- The bound on the high 52 bits of a product. -/
def hiB (a b : Nat) : Nat := min a (2 ^ 52 - 1) * min b (2 ^ 52 - 1) / 2 ^ 52

def T.bnd (B : VG.Proof.X25519.X86_64.Ifma.Bnds) : VG.Proof.X25519.X86_64.Ifma.T → Nat → Nat
  | .reg r, _ => min (B.v r) (2 ^ 64 - 1)
  | .gpr g, _ => min (B.g g) (2 ^ 64 - 1)
  | .zero, _ => 0
  | .lane0 a, k => if k = 0 then a.bnd B 0 else 0
  | .bc a, _ => a.bnd B 0
  | .ld d, _ => min (B.m d) (2 ^ 64 - 1)
  | .add a b, k => capW (a.bnd B k + b.bnd B k)
  | .sub a _, k => a.bnd B k
  | .and a b, k => min (a.bnd B k) (b.bnd B k)
  | .xor _ _, _ => 2 ^ 64 - 1
  | .or a b, k => orB (a.bnd B k) (b.bnd B k)
  | .shl a n, k => capW (a.bnd B k * 2 ^ n)
  | .shr a n, k => a.bnd B k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.bnd B k else b.bnd B (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.bnd B (k + 1) else b.bnd B k
  | .perm a o, k => a.bnd B (sel4 o k)
  | .blend a b sel, k => match VG.Proof.X25519.X86_64.Ifma.selQ sel k with
    | some true => b.bnd B k
    | some false => a.bnd B k
    | none => 2 ^ 64 - 1
  | .mad false c a b, k => capW (c.bnd B k + VG.Proof.X25519.X86_64.Ifma.loB (a.bnd B k) (b.bnd B k))
  | .mad true c a b, k => capW (c.bnd B k + VG.Proof.X25519.X86_64.Ifma.hiB (a.bnd B k) (b.bnd B k))
  | .p2 a b hi, k => if k < 2 then a.bnd B (if hi then k + 2 else k) else b.bnd B (if hi then k else k - 2)
  | .low a, k => if k < 2 then a.bnd B k else 0

/-- A lower bound. -/
def T.lb (B : VG.Proof.X25519.X86_64.Ifma.Bnds) : VG.Proof.X25519.X86_64.Ifma.T → Nat → Nat
  | .ld d, _ => B.ml d
  | .add a b, k => a.lb B k + b.lb B k
  | .sub a b, k => a.lb B k - b.bnd B k
  | .perm a o, k => a.lb B (sel4 o k)
  | .blend a b sel, k => match VG.Proof.X25519.X86_64.Ifma.selQ sel k with
    | some true => b.lb B k
    | some false => a.lb B k
    | none => 0
  | .mad _ c _ _, k => c.lb B k
  | .bc a, _ => a.lb B 0
  | _, _ => 0

/-- The value of a term as a number, with no reductions modulo `2⁶⁴`: what
the code computes where `T.ok` holds. -/
def T.nat (E : VG.Proof.X25519.X86_64.Ifma.Env) : VG.Proof.X25519.X86_64.Ifma.T → Nat → Nat
  | .reg r, k => E.v r k
  | .gpr g, _ => E.g g
  | .zero, _ => 0
  | .lane0 a, k => if k = 0 then a.nat E 0 else 0
  | .bc a, _ => a.nat E 0
  | .ld d, k => E.m d k
  | .add a b, k => a.nat E k + b.nat E k
  | .sub a b, k => a.nat E k - b.nat E k
  | .and a b, k => a.nat E k &&& b.nat E k
  | .xor a b, k => a.nat E k ^^^ b.nat E k
  | .or a b, k => a.nat E k ||| b.nat E k
  | .shl a n, k => a.nat E k * 2 ^ n
  | .shr a n, k => a.nat E k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.nat E k else b.nat E (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.nat E (k + 1) else b.nat E k
  | .perm a o, k => a.nat E (sel4 o k)
  | .blend a b sel, k => match VG.Proof.X25519.X86_64.Ifma.selQ sel k with
    | some true => b.nat E k
    | _ => a.nat E k
  | .mad false c a b, k => c.nat E k + a.nat E k % 2 ^ 52 * (b.nat E k % 2 ^ 52) % 2 ^ 52
  | .mad true c a b, k => c.nat E k + a.nat E k % 2 ^ 52 * (b.nat E k % 2 ^ 52) / 2 ^ 52
  | .p2 a b hi, k => if k < 2 then a.nat E (if hi then k + 2 else k) else b.nat E (if hi then k else k - 2)
  | .low a, k => if k < 2 then a.nat E k else 0

/-- Nothing in `t` wraps, by the bounds `B`, and every blend picks whole
quadwords. -/
def T.ok (B : VG.Proof.X25519.X86_64.Ifma.Bnds) : VG.Proof.X25519.X86_64.Ifma.T → Nat → Bool
  | .reg _, _ | .gpr _, _ | .ld _, _ | .zero, _ => true
  | .lane0 a, k => if k = 0 then a.ok B 0 else true
  | .bc a, _ => a.ok B 0
  | .add a b, k => a.bnd B k + b.bnd B k < 2 ^ 64 && a.ok B k && b.ok B k
  | .sub a b, k => b.bnd B k ≤ a.lb B k && a.ok B k && b.ok B k
  | .and a b, k | .xor a b, k | .or a b, k => a.ok B k && b.ok B k
  | .shl a n, k => a.bnd B k * 2 ^ n < 2 ^ 64 && a.ok B k
  | .shr a _, k => a.ok B k
  | .unpl a b, k => if k % 2 = 0 then a.ok B k else b.ok B (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.ok B (k + 1) else b.ok B k
  | .perm a o, k => a.ok B (sel4 o k)
  | .blend a b sel, k => (VG.Proof.X25519.X86_64.Ifma.selQ sel k).isSome && a.ok B k && b.ok B k
  | .mad false c a b, k => c.bnd B k + VG.Proof.X25519.X86_64.Ifma.loB (a.bnd B k) (b.bnd B k) < 2 ^ 64 && c.ok B k && a.ok B k && b.ok B k
  | .mad true c a b, k => c.bnd B k + VG.Proof.X25519.X86_64.Ifma.hiB (a.bnd B k) (b.bnd B k) < 2 ^ 64 && c.ok B k && a.ok B k && b.ok B k
  | .p2 a b hi, k => if k < 2 then a.ok B (if hi then k + 2 else k) else b.ok B (if hi then k else k - 2)
  | .low a, k => if k < 2 then a.ok B k else true

/-- What a block starts from is within `B`. -/
structure EnvOK (s₀ : State) (B : VG.Proof.X25519.X86_64.Ifma.Bnds) : Prop where
  v : ∀ r k, k < 4 → (qw s₀ (xr r) k).toNat ≤ B.v r
  g : ∀ g, (s₀.gpr g).toNat ≤ B.g g
  m : ∀ d k, k < 4 → (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (d + 8 * k)) 64).toNat ≤ B.m d
  ml : ∀ d k, k < 4 → B.ml d ≤ (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (d + 8 * k)) 64).toNat

theorem pick2_tt (a b : BitVec 64) : pick2 a b true true = b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [pick2, ite_true, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : j < 32
  · simp [h]
  · simp only [h, decide_false, ite_false, decide_eq_true (show j - 32 < 32 by omega), Bool.true_and]
    exact congrArg _ (by omega)

theorem pick2_ff (a b : BitVec 64) : pick2 a b false false = a := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [pick2, Bool.false_eq_true, ite_false, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : j < 32
  · simp [h]
  · simp only [h, decide_false, ite_false, decide_eq_true (show j - 32 < 32 by omega), Bool.true_and]
    exact congrArg _ (by omega)

theorem pick2_sel (a b : BitVec 64) (sel k : Nat) (hs : (VG.Proof.X25519.X86_64.Ifma.selQ sel k).isSome = true) :
    pick2 a b (sel.testBit (2 * k)) (sel.testBit (2 * k + 1)) = if VG.Proof.X25519.X86_64.Ifma.selQ sel k = some true then b else a := by
  unfold VG.Proof.X25519.X86_64.Ifma.selQ at hs ⊢
  split at hs <;> simp only [Option.isSome_some, Option.isSome_none, reduceCtorEq] at hs
  · rename_i h1 h2
    rw [h1, h2, ite_eq_left rfl, VG.Proof.X25519.X86_64.Ifma.pick2_tt]
  · rename_i h1 h2
    rw [h1, h2, ite_eq_right (by simp), VG.Proof.X25519.X86_64.Ifma.pick2_ff]

theorem loB_ge {x y a b : Nat} (hx : x ≤ a) (hy : y ≤ b) :
    x % 2 ^ 52 * (y % 2 ^ 52) % 2 ^ 52 ≤ VG.Proof.X25519.X86_64.Ifma.loB a b := by
  unfold VG.Proof.X25519.X86_64.Ifma.loB
  have h1 : x % 2 ^ 52 ≤ min a (2 ^ 52 - 1) := Nat.le_min.2 ⟨Nat.le_trans (Nat.mod_le _ _) hx,
    Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  have h2 : y % 2 ^ 52 ≤ min b (2 ^ 52 - 1) := Nat.le_min.2 ⟨Nat.le_trans (Nat.mod_le _ _) hy,
    Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  exact Nat.le_min.2 ⟨Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide)),
    Nat.le_trans (Nat.mod_le _ _) (Nat.mul_le_mul h1 h2)⟩

theorem hiB_ge {x y a b : Nat} (hx : x ≤ a) (hy : y ≤ b) :
    x % 2 ^ 52 * (y % 2 ^ 52) / 2 ^ 52 ≤ VG.Proof.X25519.X86_64.Ifma.hiB a b := by
  unfold VG.Proof.X25519.X86_64.Ifma.hiB
  have h1 : x % 2 ^ 52 ≤ min a (2 ^ 52 - 1) := Nat.le_min.2 ⟨Nat.le_trans (Nat.mod_le _ _) hx,
    Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  have h2 : y % 2 ^ 52 ≤ min b (2 ^ 52 - 1) := Nat.le_min.2 ⟨Nat.le_trans (Nat.mod_le _ _) hy,
    Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  exact Nat.div_le_div_right (Nat.mul_le_mul h1 h2)

theorem nat_ok {s₀ : State} {B : VG.Proof.X25519.X86_64.Ifma.Bnds} (hE : VG.Proof.X25519.X86_64.Ifma.EnvOK s₀ B) :
    ∀ (t : VG.Proof.X25519.X86_64.Ifma.T) {k : Nat}, k < 4 → t.ok B k = true →
      (t.eval s₀ k).toNat = t.nat (VG.Proof.X25519.X86_64.Ifma.envOf s₀) k ∧ (t.eval s₀ k).toNat ≤ t.bnd B k ∧
        t.lb B k ≤ (t.eval s₀ k).toNat := by
  intro t
  induction t with
  | reg r =>
    intro k hk _
    exact ⟨by simp only [T.eval, T.nat, VG.Proof.X25519.X86_64.Ifma.envOf], Nat.le_min.2 ⟨hE.v r k hk, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩,
      Nat.zero_le _⟩
  | gpr g =>
    intro k _ _
    exact ⟨rfl, Nat.le_min.2 ⟨hE.g g, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩, Nat.zero_le _⟩
  | zero => intro k _ _; exact ⟨rfl, by simp [T.eval, T.bnd], Nat.zero_le _⟩
  | lane0 a ih =>
    intro k _ ho
    simp only [T.eval, T.nat, T.bnd, T.ok, T.lb] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact ⟨(ih (by decide) ho).1, (ih (by decide) ho).2.1, Nat.zero_le _⟩
    · simp
  | bc a ih =>
    intro k _ ho
    exact ih (by decide) ho
  | ld d =>
    intro k hk _
    exact ⟨rfl, Nat.le_min.2 ⟨hE.m d k hk, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩, hE.ml d k hk⟩
  | add a b iha ihb =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨⟨hs, oa⟩, ob⟩ := ho
    obtain ⟨ea, ba, la⟩ := iha hk oa
    obtain ⟨eb, bb, lb⟩ := ihb hk ob
    simp only [T.eval, T.nat, T.bnd, T.lb, BitVec.toNat_add]
    rw [← ea, ← eb]
    have := BitVec.isLt (a.eval s₀ k + b.eval s₀ k)
    rw [BitVec.toNat_add] at this
    refine ⟨Nat.mod_eq_of_lt (by omega), capW_ge (by rw [Nat.mod_eq_of_lt (by omega)]; omega) this, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  | sub a b iha ihb =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨⟨hs, oa⟩, ob⟩ := ho
    obtain ⟨ea, ba, la⟩ := iha hk oa
    obtain ⟨eb, bb, lb⟩ := ihb hk ob
    have hle : (b.eval s₀ k).toNat ≤ (a.eval s₀ k).toNat := by omega
    simp only [T.eval, T.nat, T.bnd, T.lb]
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 hle), ← ea, ← eb]
    exact ⟨rfl, by omega, by omega⟩
  | and a b iha ihb =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba, _⟩ := iha hk ho.1
    obtain ⟨eb, bb, _⟩ := ihb hk ho.2
    simp only [T.eval, T.nat, T.bnd, T.lb, BitVec.toNat_and]
    rw [← ea, ← eb]
    exact ⟨rfl, Nat.le_min.2 ⟨Nat.le_trans Nat.and_le_left ba, Nat.le_trans Nat.and_le_right bb⟩,
      Nat.zero_le _⟩
  | xor a b iha ihb =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba, _⟩ := iha hk ho.1
    obtain ⟨eb, bb, _⟩ := ihb hk ho.2
    have := BitVec.isLt (a.eval s₀ k ^^^ b.eval s₀ k)
    simp only [T.eval, T.nat, T.bnd, T.lb, BitVec.toNat_xor] at this ⊢
    rw [← ea, ← eb]
    exact ⟨rfl, Nat.le_sub_one_of_lt this, Nat.zero_le _⟩
  | or a b iha ihb =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba, _⟩ := iha hk ho.1
    obtain ⟨eb, bb, _⟩ := ihb hk ho.2
    have := BitVec.isLt (a.eval s₀ k ||| b.eval s₀ k)
    simp only [T.eval, T.nat, T.bnd, T.lb, BitVec.toNat_or] at this ⊢
    rw [← ea, ← eb]
    exact ⟨rfl, orB_ge ba bb this, Nat.zero_le _⟩
  | shl a n ih =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨ea, ba, _⟩ := ih hk ho.2
    have := BitVec.isLt (a.eval s₀ k <<< n)
    simp only [T.eval, T.nat, T.bnd, T.lb, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at this ⊢
    rw [← ea]
    have hm := Nat.mul_le_mul_right (2 ^ n) ba
    exact ⟨Nat.mod_eq_of_lt (by omega), capW_ge (by rw [Nat.mod_eq_of_lt (by omega)]; omega) this,
      Nat.zero_le _⟩
  | shr a n ih =>
    intro k hk ho
    obtain ⟨ea, ba, _⟩ := ih hk ho
    simp only [T.eval, T.nat, T.bnd, T.lb, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [← ea]
    exact ⟨rfl, Nat.div_le_div_right ba, Nat.zero_le _⟩
  | unpl a b iha ihb =>
    intro k hk ho
    simp only [T.eval, T.nat, T.bnd, T.ok, T.lb] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact ⟨(iha hk ho).1, (iha hk ho).2.1, Nat.zero_le _⟩
    · rename_i h; rw [ite_eq_right h] at ho
      exact ⟨(ihb (by omega) ho).1, (ihb (by omega) ho).2.1, Nat.zero_le _⟩
  | unph a b iha ihb =>
    intro k hk ho
    simp only [T.eval, T.nat, T.bnd, T.ok, T.lb] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho
      exact ⟨(iha (by omega) ho).1, (iha (by omega) ho).2.1, Nat.zero_le _⟩
    · rename_i h; rw [ite_eq_right h] at ho; exact ⟨(ihb hk ho).1, (ihb hk ho).2.1, Nat.zero_le _⟩
  | perm a o ih =>
    intro k _ ho
    exact ih (sel4_lt _ _) ho
  | blend a b sel iha ihb =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true] at ho
    obtain ⟨⟨hs, oa⟩, ob⟩ := ho
    obtain ⟨ea, ba, la⟩ := iha hk oa
    obtain ⟨eb, bb, lb⟩ := ihb hk ob
    simp only [T.eval, T.nat, T.bnd, T.lb]
    rw [VG.Proof.X25519.X86_64.Ifma.pick2_sel _ _ _ _ hs]
    rcases hq : VG.Proof.X25519.X86_64.Ifma.selQ sel k with _ | c
    · rw [hq] at hs; cases hs
    · cases c
      · exact ⟨ea, ba, la⟩
      · simp only [ite_true]; exact ⟨eb, bb, lb⟩
  | mad h c a b ihc iha ihb =>
    intro k hk ho
    have ha := BitVec.isLt (a.eval s₀ k)
    have hb := BitVec.isLt (b.eval s₀ k)
    cases h
    · simp only [T.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
      obtain ⟨⟨⟨hs, oc⟩, oa⟩, ob⟩ := ho
      obtain ⟨ec, bc, lc⟩ := ihc hk oc
      obtain ⟨ea, ba, _⟩ := iha hk oa
      obtain ⟨eb, bb, _⟩ := ihb hk ob
      have hl := VG.Proof.X25519.X86_64.Ifma.loB_ge ba bb
      simp only [T.eval, T.nat, T.bnd, T.lb]
      rw [VG.Proof.X25519.X86_64.Ifma.mad52_toNat]
      simp only [Bool.false_eq_true, ite_false]
      rw [← ec, ← ea, ← eb, Nat.mod_eq_of_lt (by omega)]
      exact ⟨rfl, capW_ge (by omega) (by omega), by omega⟩
    · simp only [T.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
      obtain ⟨⟨⟨hs, oc⟩, oa⟩, ob⟩ := ho
      obtain ⟨ec, bc, lc⟩ := ihc hk oc
      obtain ⟨ea, ba, _⟩ := iha hk oa
      obtain ⟨eb, bb, _⟩ := ihb hk ob
      have hl := VG.Proof.X25519.X86_64.Ifma.hiB_ge ba bb (x := (a.eval s₀ k).toNat) (y := (b.eval s₀ k).toNat)
      simp only [T.eval, T.nat, T.bnd, T.lb]
      rw [VG.Proof.X25519.X86_64.Ifma.mad52_toNat]
      simp only [ite_true]
      rw [← ec, ← ea, ← eb, Nat.mod_eq_of_lt (by omega)]
      exact ⟨rfl, capW_ge (by omega) (by omega), by omega⟩
  | p2 a b hi iha ihb =>
    intro k hk ho
    simp only [T.eval, T.nat, T.bnd, T.ok, T.lb] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho
      exact ⟨(iha (by split <;> omega) ho).1, (iha (by split <;> omega) ho).2.1, Nat.zero_le _⟩
    · rename_i h; rw [ite_eq_right h] at ho
      exact ⟨(ihb (by split <;> omega) ho).1, (ihb (by split <;> omega) ho).2.1, Nat.zero_le _⟩
  | low a ih =>
    intro k hk ho
    simp only [T.eval, T.nat, T.bnd, T.ok, T.lb] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact ⟨(ih hk ho).1, (ih hk ho).2.1, Nat.zero_le _⟩
    · simp

theorem SRel.nat {σ : VG.Proof.X25519.X86_64.Ifma.Sym} {s₀ s : State} (h : VG.Proof.X25519.X86_64.Ifma.SRel σ s₀ s) {B : VG.Proof.X25519.X86_64.Ifma.Bnds} (hE : VG.Proof.X25519.X86_64.Ifma.EnvOK s₀ B) {r : XReg}
    {k : Nat} (hk : k < 4) (ho : (σ.reg (xi r)).ok B k = true) :
    (qw s r k).toNat = (σ.reg (xi r)).nat (VG.Proof.X25519.X86_64.Ifma.envOf s₀) k ∧ (qw s r k).toNat ≤ (σ.reg (xi r)).bnd B k := by
  rw [h.reg r k hk]; exact ⟨(VG.Proof.X25519.X86_64.Ifma.nat_ok hE _ hk ho).1, (VG.Proof.X25519.X86_64.Ifma.nat_ok hE _ hk ho).2.1⟩

end VG.Proof.X25519.X86_64.Ifma

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Ifma.Mul`. -/
section

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi qw)

/-- The low halves of the products `a_i b_j` with `i + j = c`, summed as the
code does. -/
def accLo (a b : Nat → Nat) (c : Nat) : Nat :=
  (List.range 5).foldl (fun acc i =>
    if i ≤ c ∧ c - i < 5 then acc + a i % 2 ^ 52 * (b (c - i) % 2 ^ 52) % 2 ^ 52 else acc) 0

/-- The high halves of the products `a_i b_j` with `i + j + 1 = c`. -/
def accHi (a b : Nat → Nat) (c : Nat) : Nat :=
  (List.range 5).foldl (fun acc i =>
    if i + 1 ≤ c ∧ c - (i + 1) < 5 then acc + a i % 2 ^ 52 * (b (c - (i + 1)) % 2 ^ 52) / 2 ^ 52
    else acc) 0

/-- Limb `k` of `mul4`: column `k` plus 19 times column `k + 5`. -/
def mulNat (a b : Nat → Nat) (k : Nat) : Nat :=
  VG.Proof.X25519.X86_64.Ifma.accLo a b k + VG.Proof.X25519.X86_64.Ifma.accHi a b k * 2 ^ 1 + (VG.Proof.X25519.X86_64.Ifma.accLo a b (k + 5) + VG.Proof.X25519.X86_64.Ifma.accHi a b (k + 5) * 2 ^ 1) +
    (VG.Proof.X25519.X86_64.Ifma.accLo a b (k + 5) + VG.Proof.X25519.X86_64.Ifma.accHi a b (k + 5) * 2 ^ 1) * 2 ^ 1 +
    (VG.Proof.X25519.X86_64.Ifma.accLo a b (k + 5) + VG.Proof.X25519.X86_64.Ifma.accHi a b (k + 5) * 2 ^ 1) * 2 ^ 4

def mulS (a : Nat) (h : (Sym.init.run (mul4 a)).isSome := by decide +kernel) : VG.Proof.X25519.X86_64.Ifma.Sym :=
  (Sym.init.run (mul4 a)).get h

def mulB (a : Nat) : VG.Proof.X25519.X86_64.Ifma.Bnds :=
  ⟨fun r => if 5 ≤ r ∧ r < 10 then 2 ^ 52 - 1 else 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1,
    fun d => if a ≤ d ∧ d < a + 160 ∧ d % 32 = 0 then 2 ^ 52 - 1 else 2 ^ 64 - 1, fun _ => 0⟩

theorem mulS_eq (a : Nat) (h : (Sym.init.run (mul4 a)).isSome) :
    Sym.init.run (mul4 a) = some (VG.Proof.X25519.X86_64.Ifma.mulS a h) := (Option.some_get _).symm

def mulL : VG.Proof.X25519.X86_64.Ifma.Sym := VG.Proof.X25519.X86_64.Ifma.mulS OPL

theorem mulL_nat (E : VG.Proof.X25519.X86_64.Ifma.Env) (l : Nat) : ∀ k < 5, (mulL.reg k).nat E l =
    VG.Proof.X25519.X86_64.Ifma.mulNat (fun i => E.m (OPL + 32 * i) l) (fun j => E.v (5 + j) l) k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem mulL_ok : ∀ k < 5, ∀ l < 4, (mulL.reg k).ok (VG.Proof.X25519.X86_64.Ifma.mulB OPL) l = true ∧
    (mulL.reg k).bnd (VG.Proof.X25519.X86_64.Ifma.mulB OPL) l < 2 ^ 61 := by decide +kernel

theorem mulL_keep : ∀ r < 16, 5 ≤ r → r < 10 ∨ r = 15 → mulL.reg r = .reg r := by decide +kernel
theorem mulL_st : mulL.st = [] := by decide +kernel

def mulV : VG.Proof.X25519.X86_64.Ifma.Sym := VG.Proof.X25519.X86_64.Ifma.mulS OPV

theorem mulV_nat (E : VG.Proof.X25519.X86_64.Ifma.Env) (l : Nat) : ∀ k < 5, (mulV.reg k).nat E l =
    VG.Proof.X25519.X86_64.Ifma.mulNat (fun i => E.m (OPV + 32 * i) l) (fun j => E.v (5 + j) l) k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem mulV_ok : ∀ k < 5, ∀ l < 4, (mulV.reg k).ok (VG.Proof.X25519.X86_64.Ifma.mulB OPV) l = true ∧
    (mulV.reg k).bnd (VG.Proof.X25519.X86_64.Ifma.mulB OPV) l < 2 ^ 61 := by decide +kernel

theorem mulV_keep : ∀ r < 16, 5 ≤ r → r < 10 ∨ r = 15 → mulV.reg r = .reg r := by decide +kernel
theorem mulV_st : mulV.st = [] := by decide +kernel

def mulG : VG.Proof.X25519.X86_64.Ifma.Sym := VG.Proof.X25519.X86_64.Ifma.mulS OPG

theorem mulG_nat (E : VG.Proof.X25519.X86_64.Ifma.Env) (l : Nat) : ∀ k < 5, (mulG.reg k).nat E l =
    VG.Proof.X25519.X86_64.Ifma.mulNat (fun i => E.m (OPG + 32 * i) l) (fun j => E.v (5 + j) l) k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem mulG_ok : ∀ k < 5, ∀ l < 4, (mulG.reg k).ok (VG.Proof.X25519.X86_64.Ifma.mulB OPG) l = true ∧
    (mulG.reg k).bnd (VG.Proof.X25519.X86_64.Ifma.mulB OPG) l < 2 ^ 61 := by decide +kernel

theorem mulG_keep : ∀ r < 16, 5 ≤ r → r < 10 ∨ r = 15 → mulG.reg r = .reg r := by decide +kernel
theorem mulG_st : mulG.st = [] := by decide +kernel

end VG.Proof.X25519.X86_64.Ifma

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Ifma.Arith`. -/
section

/-!
# X25519 on x86-64 with AVX512_IFMA: the arithmetic of the lanes

A field element is five limbs `x₀ + 2⁵¹ x₁ + … + 2²⁰⁴ x₄` (`lv`), standing for
its residue modulo `p`. The identities between limbs are polynomial identities
in `R = 2⁵¹` (`2⁵² = 2R`, `2²⁵⁵ = R⁵`), proved as such.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG.Proof.X25519 VG.Spec.X25519

/-- The number five limbs stand for. -/
def lv (x : Nat → Nat) : Nat := x 0 + 2 ^ 51 * x 1 + 2 ^ 102 * x 2 + 2 ^ 153 * x 3 + 2 ^ 204 * x 4

/-- `lv` in `R = 2⁵¹`. -/
def lvR (R : Nat) (x : Nat → Nat) : Nat := x 0 + R * x 1 + R ^ 2 * x 2 + R ^ 3 * x 3 + R ^ 4 * x 4

theorem lv_eq (x : Nat → Nat) : VG.Proof.X25519.X86_64.Ifma.lv x = VG.Proof.X25519.X86_64.Ifma.lvR (2 ^ 51) x := by
  simp only [VG.Proof.X25519.X86_64.Ifma.lv, VG.Proof.X25519.X86_64.Ifma.lvR, ← Nat.pow_mul]

/-- The columns `c` of a product `x · y` (of numbers below `2R`, here `2⁵²`),
as `accLo` and `accHi` sum them: the low halves of the products `x_i y_j`
with `i + j = c` and the high halves with `i + j + 1 = c`. -/
def colR (R : Nat) (x y : Nat → Nat) (c : Nat) : Nat :=
  (List.range 5).foldl (fun acc i =>
    if i ≤ c ∧ c - i < 5 then acc + x i * y (c - i) % (2 * R) else acc) 0 +
  (List.range 5).foldl (fun acc i =>
    if i + 1 ≤ c ∧ c - (i + 1) < 5 then acc + x i * y (c - (i + 1)) / (2 * R) else acc) 0 * 2

/-- The product identity: `Σ_c col_c Rᶜ = x · y`, with columns `5–9`
separated (`lo + R⁵ hi`). -/
theorem colR_eq (R : Nat) (x y : Nat → Nat) :
    (VG.Proof.X25519.X86_64.Ifma.colR R x y 0 + R * VG.Proof.X25519.X86_64.Ifma.colR R x y 1 + R ^ 2 * VG.Proof.X25519.X86_64.Ifma.colR R x y 2 + R ^ 3 * VG.Proof.X25519.X86_64.Ifma.colR R x y 3 +
      R ^ 4 * VG.Proof.X25519.X86_64.Ifma.colR R x y 4) +
    R ^ 5 * (VG.Proof.X25519.X86_64.Ifma.colR R x y 5 + R * VG.Proof.X25519.X86_64.Ifma.colR R x y 6 + R ^ 2 * VG.Proof.X25519.X86_64.Ifma.colR R x y 7 + R ^ 3 * VG.Proof.X25519.X86_64.Ifma.colR R x y 8 +
      R ^ 4 * VG.Proof.X25519.X86_64.Ifma.colR R x y 9) = VG.Proof.X25519.X86_64.Ifma.lvR R x * VG.Proof.X25519.X86_64.Ifma.lvR R y := by
  have e : VG.Proof.X25519.X86_64.Ifma.lvR R x * VG.Proof.X25519.X86_64.Ifma.lvR R y =
      (x 0 * y 0) +
      R * (x 0 * y 1) +
      R ^ 2 * (x 0 * y 2) +
      R ^ 3 * (x 0 * y 3) +
      R ^ 4 * (x 0 * y 4) +
      R * (x 1 * y 0) +
      R ^ 2 * (x 1 * y 1) +
      R ^ 3 * (x 1 * y 2) +
      R ^ 4 * (x 1 * y 3) +
      R ^ 5 * (x 1 * y 4) +
      R ^ 2 * (x 2 * y 0) +
      R ^ 3 * (x 2 * y 1) +
      R ^ 4 * (x 2 * y 2) +
      R ^ 5 * (x 2 * y 3) +
      R ^ 6 * (x 2 * y 4) +
      R ^ 3 * (x 3 * y 0) +
      R ^ 4 * (x 3 * y 1) +
      R ^ 5 * (x 3 * y 2) +
      R ^ 6 * (x 3 * y 3) +
      R ^ 7 * (x 3 * y 4) +
      R ^ 4 * (x 4 * y 0) +
      R ^ 5 * (x 4 * y 1) +
      R ^ 6 * (x 4 * y 2) +
      R ^ 7 * (x 4 * y 3) +
      R ^ 8 * (x 4 * y 4) := by
    simp only [VG.Proof.X25519.X86_64.Ifma.lvR]; grind
  have h00 := Nat.mod_add_div (x 0 * y 0) (2 * R)
  have h01 := Nat.mod_add_div (x 0 * y 1) (2 * R)
  have h02 := Nat.mod_add_div (x 0 * y 2) (2 * R)
  have h03 := Nat.mod_add_div (x 0 * y 3) (2 * R)
  have h04 := Nat.mod_add_div (x 0 * y 4) (2 * R)
  have h10 := Nat.mod_add_div (x 1 * y 0) (2 * R)
  have h11 := Nat.mod_add_div (x 1 * y 1) (2 * R)
  have h12 := Nat.mod_add_div (x 1 * y 2) (2 * R)
  have h13 := Nat.mod_add_div (x 1 * y 3) (2 * R)
  have h14 := Nat.mod_add_div (x 1 * y 4) (2 * R)
  have h20 := Nat.mod_add_div (x 2 * y 0) (2 * R)
  have h21 := Nat.mod_add_div (x 2 * y 1) (2 * R)
  have h22 := Nat.mod_add_div (x 2 * y 2) (2 * R)
  have h23 := Nat.mod_add_div (x 2 * y 3) (2 * R)
  have h24 := Nat.mod_add_div (x 2 * y 4) (2 * R)
  have h30 := Nat.mod_add_div (x 3 * y 0) (2 * R)
  have h31 := Nat.mod_add_div (x 3 * y 1) (2 * R)
  have h32 := Nat.mod_add_div (x 3 * y 2) (2 * R)
  have h33 := Nat.mod_add_div (x 3 * y 3) (2 * R)
  have h34 := Nat.mod_add_div (x 3 * y 4) (2 * R)
  have h40 := Nat.mod_add_div (x 4 * y 0) (2 * R)
  have h41 := Nat.mod_add_div (x 4 * y 1) (2 * R)
  have h42 := Nat.mod_add_div (x 4 * y 2) (2 * R)
  have h43 := Nat.mod_add_div (x 4 * y 3) (2 * R)
  have h44 := Nat.mod_add_div (x 4 * y 4) (2 * R)
  rw [e, ← h00, ← h01, ← h02, ← h03, ← h04, ← h10, ← h11, ← h12, ← h13, ← h14, ← h20, ← h21, ← h22, ← h23, ← h24, ← h30, ← h31, ← h32, ← h33, ← h34, ← h40, ← h41, ← h42, ← h43, ← h44]
  clear e h00 h01 h02 h03 h04 h10 h11 h12 h13 h14 h20 h21 h22 h23 h24 h30 h31 h32 h33 h34 h40 h41 h42 h43 h44
  simp only [VG.Proof.X25519.X86_64.Ifma.colR, List.range, List.range.loop, List.foldl]
  simp (config := {decide := true}) only [Nat.zero_add, ite_true, ite_false]
  generalize x 0 * y 0 % (2 * R) = l00
  generalize x 0 * y 0 / (2 * R) = d00
  generalize x 0 * y 1 % (2 * R) = l01
  generalize x 0 * y 1 / (2 * R) = d01
  generalize x 0 * y 2 % (2 * R) = l02
  generalize x 0 * y 2 / (2 * R) = d02
  generalize x 0 * y 3 % (2 * R) = l03
  generalize x 0 * y 3 / (2 * R) = d03
  generalize x 0 * y 4 % (2 * R) = l04
  generalize x 0 * y 4 / (2 * R) = d04
  generalize x 1 * y 0 % (2 * R) = l10
  generalize x 1 * y 0 / (2 * R) = d10
  generalize x 1 * y 1 % (2 * R) = l11
  generalize x 1 * y 1 / (2 * R) = d11
  generalize x 1 * y 2 % (2 * R) = l12
  generalize x 1 * y 2 / (2 * R) = d12
  generalize x 1 * y 3 % (2 * R) = l13
  generalize x 1 * y 3 / (2 * R) = d13
  generalize x 1 * y 4 % (2 * R) = l14
  generalize x 1 * y 4 / (2 * R) = d14
  generalize x 2 * y 0 % (2 * R) = l20
  generalize x 2 * y 0 / (2 * R) = d20
  generalize x 2 * y 1 % (2 * R) = l21
  generalize x 2 * y 1 / (2 * R) = d21
  generalize x 2 * y 2 % (2 * R) = l22
  generalize x 2 * y 2 / (2 * R) = d22
  generalize x 2 * y 3 % (2 * R) = l23
  generalize x 2 * y 3 / (2 * R) = d23
  generalize x 2 * y 4 % (2 * R) = l24
  generalize x 2 * y 4 / (2 * R) = d24
  generalize x 3 * y 0 % (2 * R) = l30
  generalize x 3 * y 0 / (2 * R) = d30
  generalize x 3 * y 1 % (2 * R) = l31
  generalize x 3 * y 1 / (2 * R) = d31
  generalize x 3 * y 2 % (2 * R) = l32
  generalize x 3 * y 2 / (2 * R) = d32
  generalize x 3 * y 3 % (2 * R) = l33
  generalize x 3 * y 3 / (2 * R) = d33
  generalize x 3 * y 4 % (2 * R) = l34
  generalize x 3 * y 4 / (2 * R) = d34
  generalize x 4 * y 0 % (2 * R) = l40
  generalize x 4 * y 0 / (2 * R) = d40
  generalize x 4 * y 1 % (2 * R) = l41
  generalize x 4 * y 1 / (2 * R) = d41
  generalize x 4 * y 2 % (2 * R) = l42
  generalize x 4 * y 2 / (2 * R) = d42
  generalize x 4 * y 3 % (2 * R) = l43
  generalize x 4 * y 3 / (2 * R) = d43
  generalize x 4 * y 4 % (2 * R) = l44
  generalize x 4 * y 4 / (2 * R) = d44
  grind

theorem accLo_eq (a b : Nat → Nat) (c : Nat) :
    VG.Proof.X25519.X86_64.Ifma.accLo a b c = (List.range 5).foldl (fun acc i =>
      if i ≤ c ∧ c - i < 5 then acc + a i % 2 ^ 52 * (b (c - i) % 2 ^ 52) % (2 * 2 ^ 51) else acc) 0 := rfl

theorem accHi_eq (a b : Nat → Nat) (c : Nat) :
    VG.Proof.X25519.X86_64.Ifma.accHi a b c = (List.range 5).foldl (fun acc i =>
      if i + 1 ≤ c ∧ c - (i + 1) < 5 then acc + a i % 2 ^ 52 * (b (c - (i + 1)) % 2 ^ 52) / (2 * 2 ^ 51)
      else acc) 0 := rfl

theorem mulNat_col (a b : Nat → Nat) (k : Nat) :
    VG.Proof.X25519.X86_64.Ifma.mulNat a b k = VG.Proof.X25519.X86_64.Ifma.colR (2 ^ 51) (fun i => a i % 2 ^ 52) (fun j => b j % 2 ^ 52) k +
      19 * VG.Proof.X25519.X86_64.Ifma.colR (2 ^ 51) (fun i => a i % 2 ^ 52) (fun j => b j % 2 ^ 52) (k + 5) := by
  simp only [VG.Proof.X25519.X86_64.Ifma.mulNat, VG.Proof.X25519.X86_64.Ifma.colR, VG.Proof.X25519.X86_64.Ifma.accLo_eq, VG.Proof.X25519.X86_64.Ifma.accHi_eq]
  omega

/-- `mul4`'s limbs stand for the product of the low 52 bits of the limbs, modulo `p`. -/
theorem mulNat_mod (a b : Nat → Nat) :
    VG.Proof.X25519.X86_64.Ifma.lv (VG.Proof.X25519.X86_64.Ifma.mulNat a b) % VG.Spec.X25519.P = VG.Proof.X25519.X86_64.Ifma.lv (fun i => a i % 2 ^ 52) * VG.Proof.X25519.X86_64.Ifma.lv (fun j => b j % 2 ^ 52) % VG.Spec.X25519.P := by
  have e := VG.Proof.X25519.X86_64.Ifma.colR_eq (2 ^ 51) (fun i => a i % 2 ^ 52) (fun j => b j % 2 ^ 52)
  rw [VG.Proof.X25519.X86_64.Ifma.lv_eq, VG.Proof.X25519.X86_64.Ifma.lv_eq, VG.Proof.X25519.X86_64.Ifma.lv_eq, ← e, show (2 ^ 51 : Nat) ^ 5 = 2 ^ 255 by rfl, fold255]
  simp only [VG.Proof.X25519.X86_64.Ifma.lvR, VG.Proof.X25519.X86_64.Ifma.mulNat_col, Nat.zero_add, Nat.reduceAdd]
  congr 1
  omega

end VG.Proof.X25519.X86_64.Ifma

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Ifma.Block`. -/
section

/-!
# X25519 on x86-64 with AVX512_IFMA: what a block leaves in memory

After a block whose stores (`Sym.st`) are 32-byte slots apart, each quadword
of a slot it stored is its term, and every quadword it did not store is as
before.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64

/-- The quadword at `base + d`. -/
def mq (m : Mem) (base : Addr) (d : Nat) : BitVec 64 := m.readW (base + BitVec.ofNat 64 d) 64

theorem val_extract (s₀ : State) (t : VG.Proof.X25519.X86_64.Ifma.T) {l : Nat} (hl : l < 4) :
    (t.val s₀).extractLsb' (8 * (8 * l)) (8 * 8) = t.eval s₀ l := by
  have := VG.Proof.Poly1305.X86_64.Avx2.qword256_cat (t.eval s₀ 3) (t.eval s₀ 2) (t.eval s₀ 1)
    (t.eval s₀ 0) hl
  rw [show 8 * (8 * l) = 64 * l by omega]
  refine this.trans ?_
  rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

/-- A quadword no store touched. -/
theorem stores_mq_fresh (s₀ : State) (base : Addr) (m : Mem) :
    ∀ (st : List (Nat × VG.Proof.X25519.X86_64.Ifma.T)) {d : Nat}, d < 2 ^ 62 → (∀ e ∈ st, e.1 < 2 ^ 62) →
      (st.all fun (e, _) => d + 8 ≤ e || e + 32 ≤ d) = true →
      VG.Proof.X25519.X86_64.Ifma.mq (VG.Proof.X25519.X86_64.Ifma.stores s₀ base st m) base d = VG.Proof.X25519.X86_64.Ifma.mq m base d
  | [], _, _, _, _ => rfl
  | (e, t) :: st, d, hd, he, hf => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hf
    have e1 := readW_writeW_off (VG.Proof.X25519.X86_64.Ifma.stores s₀ base st m) base (t.val s₀) (d := d) (e := e) (n := 8)
      (by omega) (by have := he _ (List.mem_cons_self ..); simp at this; omega) (by omega)
    have e2 := VG.Proof.X25519.X86_64.Ifma.stores_mq_fresh s₀ base m st hd (fun x hx => he x (List.mem_cons_of_mem _ hx)) hf.2
    exact e1.trans e2

/-- Slots 32 bytes apart. -/
def Apart (st : List (Nat × VG.Proof.X25519.X86_64.Ifma.T)) : Prop := st.Pairwise fun x y => x.1 + 32 ≤ y.1 ∨ y.1 + 32 ≤ x.1

instance (st : List (Nat × VG.Proof.X25519.X86_64.Ifma.T)) : Decidable (VG.Proof.X25519.X86_64.Ifma.Apart st) := by unfold VG.Proof.X25519.X86_64.Ifma.Apart; infer_instance

/-- A quadword of a stored slot. -/
theorem stores_mq (s₀ : State) (base : Addr) (m : Mem) :
    ∀ (st : List (Nat × VG.Proof.X25519.X86_64.Ifma.T)) {e : Nat} {t : VG.Proof.X25519.X86_64.Ifma.T} {l : Nat}, (e, t) ∈ st → l < 4 →
      (∀ x ∈ st, x.1 < 2 ^ 62) → VG.Proof.X25519.X86_64.Ifma.Apart st → VG.Proof.X25519.X86_64.Ifma.mq (VG.Proof.X25519.X86_64.Ifma.stores s₀ base st m) base (e + 8 * l) = t.eval s₀ l
  | [], _, _, _, h, _, _, _ => by cases h
  | (e₀, t₀) :: st, e, t, l, h, hl, hs, ha => by
    simp only [VG.Proof.X25519.X86_64.Ifma.Apart, List.pairwise_cons] at ha
    simp only [VG.Proof.X25519.X86_64.Ifma.stores]
    rcases List.mem_cons.1 h with h | h
    · cases h
      rw [VG.Proof.X25519.X86_64.Ifma.mq, BitVec.ofNat_add, ← BitVec.add_assoc,
        readW_writeW_inside _ _ _ (k := 8 * l) (n := 8) (by omega) (by decide), VG.Proof.X25519.X86_64.Ifma.val_extract _ _ hl]
    · have h₀ := ha.1 _ h
      have e1 := readW_writeW_off (VG.Proof.X25519.X86_64.Ifma.stores s₀ base st m) base (t₀.val s₀) (d := e + 8 * l) (e := e₀) (n := 8)
        (by have := hs _ (List.mem_cons_of_mem _ h); simp at this; omega)
        (by have := hs _ (List.mem_cons_self ..); simp at this; omega)
        (by simp at h₀; omega)
      exact e1.trans (VG.Proof.X25519.X86_64.Ifma.stores_mq s₀ base m st h hl (fun x hx => hs x (List.mem_cons_of_mem _ hx)) ha.2)

end VG.Proof.X25519.X86_64.Ifma

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Ifma.Carry`. -/
section

/-!
# X25519 on x86-64 with AVX512_IFMA: carries

`carry r` leaves each limb's low 51 bits plus the bits from 51 up of the limb
below (of the top limb, times 19, for the lowest): the same number modulo `p`
(`carryNat_mod`), in limbs below `2⁵²` if they were below `2⁶³`.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519

/-- The limbs `carry` leaves, with the mask `m` and the constant `k19`. -/
def carryNat (m k19 : Nat) (x : Nat → Nat) : Nat → Nat
  | 0 => (x 0 &&& m) + x 4 / 2 ^ 51 % 2 ^ 52 * (k19 % 2 ^ 52) % 2 ^ 52
  | 1 => (x 1 &&& m) + x 0 / 2 ^ 51
  | 2 => (x 2 &&& m) + x 1 / 2 ^ 51
  | 3 => (x 3 &&& m) + x 2 / 2 ^ 51
  | _ => (x 4 &&& m) + x 3 / 2 ^ 51

theorem carryNat_mod (x : Nat → Nat) (h4 : x 4 < 2 ^ 63) :
    VG.Proof.X25519.X86_64.Ifma.lv (VG.Proof.X25519.X86_64.Ifma.carryNat (2 ^ 51 - 1) 19 x) % VG.Spec.X25519.P = VG.Proof.X25519.X86_64.Ifma.lv x % VG.Spec.X25519.P := by
  have e : VG.Proof.X25519.X86_64.Ifma.lv (VG.Proof.X25519.X86_64.Ifma.carryNat (2 ^ 51 - 1) 19 x) + 2 ^ 255 * (x 4 / 2 ^ 51) = VG.Proof.X25519.X86_64.Ifma.lv x + 19 * (x 4 / 2 ^ 51) := by
    simp only [VG.Proof.X25519.X86_64.Ifma.lv, VG.Proof.X25519.X86_64.Ifma.carryNat, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have := fold255 (VG.Proof.X25519.X86_64.Ifma.lv (VG.Proof.X25519.X86_64.Ifma.carryNat (2 ^ 51 - 1) 19 x)) (x 4 / 2 ^ 51)
  rw [e] at this
  simp only [VG.Spec.X25519.P] at this ⊢
  omega

/-- `carry r` run from its start. -/
def carryS (r : Nat → Nat) (h : (Sym.init.run (VG.Impl.X25519.X86_64.Ifma.carry r)).isSome := by decide +kernel) : VG.Proof.X25519.X86_64.Ifma.Sym :=
  (Sym.init.run (VG.Impl.X25519.X86_64.Ifma.carry r)).get h

theorem carryS_eq (r : Nat → Nat) (h : (Sym.init.run (VG.Impl.X25519.X86_64.Ifma.carry r)).isSome) :
    Sym.init.run (VG.Impl.X25519.X86_64.Ifma.carry r) = some (VG.Proof.X25519.X86_64.Ifma.carryS r h) := (Option.some_get _).symm

def carryI : VG.Proof.X25519.X86_64.Ifma.Sym := VG.Proof.X25519.X86_64.Ifma.carryS id
def carryF : VG.Proof.X25519.X86_64.Ifma.Sym := VG.Proof.X25519.X86_64.Ifma.carryS (5 + ·)

theorem carryI_nat (E : VG.Proof.X25519.X86_64.Ifma.Env) (l : Nat) : ∀ k < 5,
    (carryI.reg k).nat E l = VG.Proof.X25519.X86_64.Ifma.carryNat (E.m KM l) (E.m K19 l) (fun i => E.v i l) k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem carryF_nat (E : VG.Proof.X25519.X86_64.Ifma.Env) (l : Nat) : ∀ k < 5,
    (carryF.reg (5 + k)).nat E l = VG.Proof.X25519.X86_64.Ifma.carryNat (E.m KM l) (E.m K19 l) (fun i => E.v (5 + i) l) k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

/-- The bounds `carry r` needs: limbs below `2⁶³`, and the constants. -/
def carryB (r : Nat → Nat) : VG.Proof.X25519.X86_64.Ifma.Bnds :=
  ⟨fun i => if i = r 0 ∨ i = r 1 ∨ i = r 2 ∨ i = r 3 ∨ i = r 4 then 2 ^ 63 - 1 else 2 ^ 64 - 1,
    fun _ => 2 ^ 64 - 1, fun d => if d = KM then 2 ^ 51 - 1 else if d = K19 then 19 else 2 ^ 64 - 1,
    fun _ => 0⟩

theorem carryI_ok : ∀ k < 5, ∀ l < 4, (carryI.reg k).ok (VG.Proof.X25519.X86_64.Ifma.carryB id) l = true ∧
    (carryI.reg k).bnd (VG.Proof.X25519.X86_64.Ifma.carryB id) l < 2 ^ 52 := by decide +kernel

theorem carryF_ok : ∀ k < 5, ∀ l < 4, (carryF.reg (5 + k)).ok (VG.Proof.X25519.X86_64.Ifma.carryB (5 + ·)) l = true ∧
    (carryF.reg (5 + k)).bnd (VG.Proof.X25519.X86_64.Ifma.carryB (5 + ·)) l < 2 ^ 52 := by decide +kernel

theorem carryI_keep : ∀ r < 16, ¬ (r < 5 ∨ (10 ≤ r ∧ r < 13)) → carryI.reg r = .reg r := by
  decide +kernel

theorem carryF_keep : ∀ r < 16, ¬ ((5 ≤ r ∧ r < 13)) → carryF.reg r = .reg r := by
  decide +kernel

theorem carryI_st : carryI.st = [] := by decide +kernel
theorem carryF_st : carryF.st = [] := by decide +kernel

end VG.Proof.X25519.X86_64.Ifma

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Ifma.Stage`. -/
section

/-!
# X25519 on x86-64 with AVX512_IFMA: the stages' operands

The blocks between the carries and the products of an iteration, run
symbolically: each output limb, lane by lane, as a number (`rfl`), and its
bounds (`decide`).
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519

/-- A block run from its start. -/
def symOf (is : List Instr) (h : (Sym.init.run is).isSome := by decide +kernel) : VG.Proof.X25519.X86_64.Ifma.Sym :=
  (Sym.init.run is).get h

theorem symOf_eq (is : List Instr) (h : (Sym.init.run is).isSome) :
    Sym.init.run is = some (VG.Proof.X25519.X86_64.Ifma.symOf is h) := (Option.some_get _).symm

/-! ## Stage 1 -/

def s1a : VG.Proof.X25519.X86_64.Ifma.Sym := VG.Proof.X25519.X86_64.Ifma.symOf stage1a

/-- `(x₂ + z₂, x₂ + bias - z₂, x₃ + z₃, x₃ + bias - z₃)`, limb `j`. -/
def s1aNat (E : VG.Proof.X25519.X86_64.Ifma.Env) (j : Nat) : Nat → Nat
  | 0 => E.v j 0 + E.v j 1
  | 1 => E.v j 0 + (E.m (kb j) 1 - E.v j 1)
  | 2 => E.v j 2 + E.v j 3
  | _ => E.v j 2 + (E.m (kb j) 3 - E.v j 3)

theorem s1a_nat (E : VG.Proof.X25519.X86_64.Ifma.Env) : ∀ j < 5, ∀ l < 4, (s1a.reg j).nat E l = VG.Proof.X25519.X86_64.Ifma.s1aNat E j l := by
  intro j hj l hl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

/-- Bounds: limbs below `2⁶¹`, and the bias. -/
def s1aB : VG.Proof.X25519.X86_64.Ifma.Bnds :=
  ⟨fun i => if i < 5 then 2 ^ 61 - 1 else 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1,
    fun d => if d = KB0 then 2 ^ 62 - 38912 else if d = KB1 then 2 ^ 62 - 2048 else 2 ^ 64 - 1,
    fun d => if d = KB0 then 2 ^ 62 - 38912 else if d = KB1 then 2 ^ 62 - 2048 else 0⟩

theorem s1a_ok : ∀ j < 5, ∀ l < 4, (s1a.reg j).ok VG.Proof.X25519.X86_64.Ifma.s1aB l = true ∧ (s1a.reg j).bnd VG.Proof.X25519.X86_64.Ifma.s1aB l < 2 ^ 63 := by
  decide +kernel

theorem s1a_keep : ∀ r < 16, 5 ≤ r → ¬ (10 ≤ r ∧ r < 13) → s1a.reg r = .reg r := by decide +kernel
theorem s1a_st : s1a.st = [] := by decide +kernel

def s1b : VG.Proof.X25519.X86_64.Ifma.Sym := VG.Proof.X25519.X86_64.Ifma.symOf stage1b

theorem s1b_regs : ∀ j < 5, s1b.reg (5 + j) = .perm (.reg j) (ord 0 1 0 1).toNat := by decide +kernel
theorem s1b_st : s1b.st = [(OPL + 128, .perm (.reg 4) (ord 0 1 3 2).toNat),
    (OPL + 96, .perm (.reg 3) (ord 0 1 3 2).toNat), (OPL + 64, .perm (.reg 2) (ord 0 1 3 2).toNat),
    (OPL + 32, .perm (.reg 1) (ord 0 1 3 2).toNat), (OPL, .perm (.reg 0) (ord 0 1 3 2).toNat)] := by
  decide +kernel
theorem s1b_keep : ∀ r < 16, (r < 5 ∨ 11 ≤ r) → s1b.reg r = .reg r := by decide +kernel

/-! ## Stage 2 -/

def s2a : VG.Proof.X25519.X86_64.Ifma.Sym := VG.Proof.X25519.X86_64.Ifma.symOf stage2a

/-- `(DA + CB, DA + bias - CB, AA, AA + bias - BB)`, limb `j`. -/
def s2aV (E : VG.Proof.X25519.X86_64.Ifma.Env) (j : Nat) : Nat → Nat
  | 0 => E.v j 2 + E.v j 3
  | 1 => E.v j 2 + (E.m (kb j) 1 - E.v j 3)
  | 2 => E.v j 0 + 0
  | _ => E.v j 0 + (E.m (kb j) 3 - E.v j 1)

/-- `(DA + CB, DA + bias - CB, BB, a24)`, limb `j`. -/
def s2aW (E : VG.Proof.X25519.X86_64.Ifma.Env) (j : Nat) : Nat → Nat
  | 0 => E.v j 2 + E.v j 3
  | 1 => E.v j 2 + (E.m (kb j) 1 - E.v j 3)
  | 2 => E.v j 1
  | _ => E.m (KA24 + 32 * j) 3

theorem s2a_nat (E : VG.Proof.X25519.X86_64.Ifma.Env) : ∀ j < 5, ∀ l < 4,
    (s2a.reg (5 + j)).nat E l = VG.Proof.X25519.X86_64.Ifma.s2aV E j l ∧ (s2a.reg j).nat E l = VG.Proof.X25519.X86_64.Ifma.s2aW E j l := by
  intro j hj l hl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- Bounds: products below `2⁶¹`, the bias, and `a24`'s slot. -/
def s2aB : VG.Proof.X25519.X86_64.Ifma.Bnds :=
  ⟨fun i => if i < 5 then 2 ^ 61 - 1 else 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1,
    fun d => if d = KB0 then 2 ^ 62 - 38912 else if d = KB1 then 2 ^ 62 - 2048
      else if KA24 ≤ d ∧ d < KA24 + 160 ∧ d % 32 = 0 then 2 ^ 52 - 1 else 2 ^ 64 - 1,
    fun d => if d = KB0 then 2 ^ 62 - 38912 else if d = KB1 then 2 ^ 62 - 2048 else 0⟩

theorem s2a_ok : ∀ j < 5, ∀ l < 4, (s2a.reg (5 + j)).ok VG.Proof.X25519.X86_64.Ifma.s2aB l = true ∧
    (s2a.reg (5 + j)).bnd VG.Proof.X25519.X86_64.Ifma.s2aB l < 2 ^ 63 ∧ (s2a.reg j).ok VG.Proof.X25519.X86_64.Ifma.s2aB l = true ∧
    (s2a.reg j).bnd VG.Proof.X25519.X86_64.Ifma.s2aB l < 2 ^ 63 := by
  decide +kernel

theorem s2a_keep : ∀ r < 16, 14 ≤ r → s2a.reg r = .reg r := by decide +kernel
theorem s2a_st : s2a.st = [] := by decide +kernel

def s2b : VG.Proof.X25519.X86_64.Ifma.Sym := VG.Proof.X25519.X86_64.Ifma.symOf stage2b

theorem s2b_regs : ∀ j < 5, s2b.reg (5 + j) = .reg j := by decide +kernel
theorem s2b_st : s2b.st = [(OPV + 128, .reg 9), (OPV + 96, .reg 8), (OPV + 64, .reg 7),
    (OPV + 32, .reg 6), (OPV, .reg 5)] := by decide +kernel
theorem s2b_keep : ∀ r < 16, (r < 5 ∨ 10 ≤ r) → s2b.reg r = .reg r := by decide +kernel

/-! ## Stage 3 -/

def s3a : VG.Proof.X25519.X86_64.Ifma.Sym := VG.Proof.X25519.X86_64.Ifma.symOf stage3a

/-- `(1, AA + a24 E, 1, x₁)`, limb `j` (the constants from `KX1`). -/
def s3aH (E : VG.Proof.X25519.X86_64.Ifma.Env) (j : Nat) : Nat → Nat
  | 1 => E.m (OPV + 32 * j) 2 + E.v j 3
  | l => E.m (KX1 + 32 * j) l

/-- `(x₂', E, x₃', t)`, limb `j`. -/
def s3aG (E : VG.Proof.X25519.X86_64.Ifma.Env) (j : Nat) : Nat → Nat
  | 0 => E.v j 2
  | 1 => E.m (OPV + 32 * j) 3
  | 2 => E.v j 0
  | _ => E.v j 1

theorem s3a_nat (E : VG.Proof.X25519.X86_64.Ifma.Env) : ∀ j < 5, ∀ l < 4,
    (s3a.reg (5 + j)).nat E l = VG.Proof.X25519.X86_64.Ifma.s3aH E j l ∧ (s3a.reg j).nat E l = VG.Proof.X25519.X86_64.Ifma.s3aG E j l := by
  intro j hj l hl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- Bounds: products below `2⁶¹`, stage 2's first operand and `x₁`'s slot
below `2⁵²`. -/
def s3aB : VG.Proof.X25519.X86_64.Ifma.Bnds :=
  ⟨fun i => if i < 5 then 2 ^ 61 - 1 else 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1,
    fun d => if ((OPV ≤ d ∧ d < OPV + 160) ∨ (KX1 ≤ d ∧ d < KX1 + 160)) ∧ d % 32 = 0 then 2 ^ 52 - 1 else 2 ^ 64 - 1,
    fun _ => 0⟩

theorem s3a_ok : ∀ j < 5, ∀ l < 4, (s3a.reg (5 + j)).ok VG.Proof.X25519.X86_64.Ifma.s3aB l = true ∧
    (s3a.reg (5 + j)).bnd VG.Proof.X25519.X86_64.Ifma.s3aB l < 2 ^ 63 ∧ (s3a.reg j).ok VG.Proof.X25519.X86_64.Ifma.s3aB l = true ∧
    (s3a.reg j).bnd VG.Proof.X25519.X86_64.Ifma.s3aB l < 2 ^ 63 := by
  decide +kernel

theorem s3a_keep : ∀ r < 16, 13 ≤ r → s3a.reg r = .reg r := by decide +kernel
theorem s3a_st : s3a.st = [] := by decide +kernel

def s3b : VG.Proof.X25519.X86_64.Ifma.Sym := VG.Proof.X25519.X86_64.Ifma.symOf stage3b

theorem s3b_st : s3b.st = [(OPG + 128, .reg 4), (OPG + 96, .reg 3), (OPG + 64, .reg 2),
    (OPG + 32, .reg 1), (OPG, .reg 0)] := by decide +kernel
theorem s3b_keep : ∀ r < 16, s3b.reg r = .reg r := by decide +kernel

end VG.Proof.X25519.X86_64.Ifma

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Ifma.Phase`. -/
section

/-!
# X25519 on x86-64 with AVX512_IFMA: the blocks of an iteration

Each block of `vstep` as a fact about states: the limbs it leaves in registers
and slots (`lanes`, `slotv`), as numbers, from those it starts with, and what
it keeps.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw sel4)

theorem xi_xr : ∀ r < 16, xi (xr r) = r := by decide

/-- Limb `i` of lane `l` of the registers from `r` up. -/
def lanes (s : State) (r l i : Nat) : Nat := (qw s (xr (r + i)) l).toNat

/-- Limb `i` of lane `l` of the slot at `d`. -/
def slotv (m : Mem) (base : Addr) (d l i : Nat) : Nat := (VG.Proof.X25519.X86_64.Ifma.mq m base (d + 32 * i + 8 * l)).toNat

/-- The constants of the working space, with `x₁`'s limbs. -/
structure Consts (m : Mem) (base : Addr) (x1 : Nat → Nat) : Prop where
  km : ∀ l < 4, (VG.Proof.X25519.X86_64.Ifma.mq m base (KM + 8 * l)).toNat = 2 ^ 51 - 1
  k19 : ∀ l < 4, (VG.Proof.X25519.X86_64.Ifma.mq m base (K19 + 8 * l)).toNat = 19
  kb0 : ∀ l < 4, (VG.Proof.X25519.X86_64.Ifma.mq m base (KB0 + 8 * l)).toNat = 2 ^ 62 - 38912
  kb1 : ∀ l < 4, (VG.Proof.X25519.X86_64.Ifma.mq m base (KB1 + 8 * l)).toNat = 2 ^ 62 - 2048
  a24 : ∀ i < 5, ∀ l < 4, VG.Proof.X25519.X86_64.Ifma.slotv m base KA24 l i = if i = 0 ∧ l = 3 then 121665 else 0
  kx1 : ∀ i < 5, ∀ l < 4, VG.Proof.X25519.X86_64.Ifma.slotv m base KX1 l i = if l = 3 then x1 i else if i = 0 ∧ l ≠ 1 then 1 else 0
  x1 : ∀ i < 5, x1 i < 2 ^ 52
  k13 : ∀ l < 4, (VG.Proof.X25519.X86_64.Ifma.mq m base (K13 + 8 * l)).toNat = 2 ^ 13 - 1
  k26 : ∀ l < 4, (VG.Proof.X25519.X86_64.Ifma.mq m base (K26 + 8 * l)).toNat = 2 ^ 26 - 1
  k39 : ∀ l < 4, (VG.Proof.X25519.X86_64.Ifma.mq m base (K39 + 8 * l)).toNat = 2 ^ 39 - 1

/-- The constants the carries and the differences read. -/
structure CConsts (m : Mem) (base : Addr) : Prop where
  km : ∀ l < 4, (VG.Proof.X25519.X86_64.Ifma.mq m base (KM + 8 * l)).toNat = 2 ^ 51 - 1
  k19 : ∀ l < 4, (VG.Proof.X25519.X86_64.Ifma.mq m base (K19 + 8 * l)).toNat = 19
  kb0 : ∀ l < 4, (VG.Proof.X25519.X86_64.Ifma.mq m base (KB0 + 8 * l)).toNat = 2 ^ 62 - 38912
  kb1 : ∀ l < 4, (VG.Proof.X25519.X86_64.Ifma.mq m base (KB1 + 8 * l)).toNat = 2 ^ 62 - 2048

theorem Consts.c {m : Mem} {base : Addr} {x1 : Nat → Nat} (hk : VG.Proof.X25519.X86_64.Ifma.Consts m base x1) : VG.Proof.X25519.X86_64.Ifma.CConsts m base :=
  ⟨hk.km, hk.k19, hk.kb0, hk.kb1⟩

theorem envOf_m {s : State} {base : Addr} (hs : s.gpr .rdi = base) (d l : Nat) :
    (VG.Proof.X25519.X86_64.Ifma.envOf s).m d l = (VG.Proof.X25519.X86_64.Ifma.mq s.mem base (d + 8 * l)).toNat := by
  simp only [VG.Proof.X25519.X86_64.Ifma.envOf, VG.Proof.X25519.X86_64.Ifma.mq, hs]

theorem envOf_v (s : State) (r l : Nat) : (VG.Proof.X25519.X86_64.Ifma.envOf s).v r l = (qw s (xr r) l).toNat := rfl

/-- The environment's bounds, from the registers and memory. -/
theorem envOK_of {s : State} {base : Addr} (hs : s.gpr .rdi = base) {B : VG.Proof.X25519.X86_64.Ifma.Bnds}
    (hv : ∀ r l, l < 4 → (qw s (xr r) l).toNat ≤ B.v r) (hg : ∀ g, B.g g = 2 ^ 64 - 1)
    (hm : ∀ d l, l < 4 → (VG.Proof.X25519.X86_64.Ifma.mq s.mem base (d + 8 * l)).toNat ≤ B.m d)
    (hml : ∀ d l, l < 4 → B.ml d ≤ (VG.Proof.X25519.X86_64.Ifma.mq s.mem base (d + 8 * l)).toNat) : VG.Proof.X25519.X86_64.Ifma.EnvOK s B :=
  ⟨hv, fun g => by rw [hg]; exact Nat.le_sub_one_of_lt (BitVec.isLt _),
    fun d k hk => by have := hm d k hk; simpa only [VG.Proof.X25519.X86_64.Ifma.mq, hs] using this,
    fun d k hk => by have := hml d k hk; simpa only [VG.Proof.X25519.X86_64.Ifma.mq, hs] using this⟩

theorem lt64 (x : BitVec 64) : x.toNat ≤ 2 ^ 64 - 1 := Nat.le_sub_one_of_lt x.isLt

/-- What a block run symbolically leaves in a register. -/
theorem SRel.out {σ : VG.Proof.X25519.X86_64.Ifma.Sym} {s₀ s : State} (h : VG.Proof.X25519.X86_64.Ifma.SRel σ s₀ s) {B : VG.Proof.X25519.X86_64.Ifma.Bnds} (hE : VG.Proof.X25519.X86_64.Ifma.EnvOK s₀ B) {r l : Nat}
    (hr : r < 16) (hl : l < 4) (ho : (σ.reg r).ok B l = true) :
    (qw s (xr r) l).toNat = (σ.reg r).nat (VG.Proof.X25519.X86_64.Ifma.envOf s₀) l ∧ (qw s (xr r) l).toNat ≤ (σ.reg r).bnd B l := by
  have := h.nat hE (r := xr r) hl (by rw [VG.Proof.X25519.X86_64.Ifma.xi_xr r hr]; exact ho)
  rwa [VG.Proof.X25519.X86_64.Ifma.xi_xr r hr] at this

theorem SRel.keep {σ : VG.Proof.X25519.X86_64.Ifma.Sym} {s₀ s : State} (h : VG.Proof.X25519.X86_64.Ifma.SRel σ s₀ s) {r l : Nat} (hr : r < 16) (hl : l < 4)
    (hk : σ.reg r = .reg r) : qw s (xr r) l = qw s₀ (xr r) l := by
  rw [h.reg _ l hl, VG.Proof.X25519.X86_64.Ifma.xi_xr r hr, hk]; rfl

/-! ## Carries -/

theorem kx1_le {m : Mem} {base : Addr} {x1 : Nat → Nat} (hk : VG.Proof.X25519.X86_64.Ifma.Consts m base x1) {i l : Nat} (hi : i < 5)
    (hl : l < 4) : VG.Proof.X25519.X86_64.Ifma.slotv m base KX1 l i < 2 ^ 52 := by
  rw [hk.kx1 i hi l hl]; have := hk.x1 i hi; split <;> [omega; split <;> omega]

/-- What `carry r` leaves: limbs `r0` to `r0 + 4` carried. -/
def CarryPost (r0 : Nat) (s s' : State) : Prop :=
  VG.Proof.X25519.X86_64.Ifma.vm s s' = s' ∧ s'.mem = s.mem ∧
    (∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s' r0 l i = VG.Proof.X25519.X86_64.Ifma.carryNat (2 ^ 51 - 1) 19 (VG.Proof.X25519.X86_64.Ifma.lanes s r0 l) i ∧
      VG.Proof.X25519.X86_64.Ifma.lanes s' r0 l i < 2 ^ 52) ∧
    (∀ r < 16, ¬ (r0 ≤ r ∧ r < r0 + 5) → ¬ (10 ≤ r ∧ r < 13) → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l)

theorem carry_env {r : Nat → Nat} {r0 : Nat} (hr : ∀ i, r i = r0 + i) {s : State} {base : Addr}
    (hs : s.gpr .rdi = base) (hk : VG.Proof.X25519.X86_64.Ifma.CConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s r0 l i < 2 ^ 63) : VG.Proof.X25519.X86_64.Ifma.EnvOK s (VG.Proof.X25519.X86_64.Ifma.carryB r) := by
  refine VG.Proof.X25519.X86_64.Ifma.envOK_of hs (fun r' l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun _ _ _ => Nat.zero_le _)
  · simp only [VG.Proof.X25519.X86_64.Ifma.carryB, hr]
    split
    · rename_i h
      have : ∃ i < 5, r' = r0 + i := by rcases h with h | h | h | h | h <;> exact ⟨_, by omega, h⟩
      obtain ⟨i, hi, rfl⟩ := this
      exact Nat.le_sub_one_of_lt (hx l hl i hi)
    · exact VG.Proof.X25519.X86_64.Ifma.lt64 _
  · simp only [VG.Proof.X25519.X86_64.Ifma.carryB]
    split
    · subst_vars; rw [hk.km l hl]
    · split
      · subst_vars; rw [hk.k19 l hl]
      · exact VG.Proof.X25519.X86_64.Ifma.lt64 _

theorem carryI_wp {s : State} {base : Addr}
    (hs : s.gpr .rdi = base) (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s) (hk : VG.Proof.X25519.X86_64.Ifma.CConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s 0 l i < 2 ^ 63) :
    WP isa (.block (VG.Impl.X25519.X86_64.Ifma.carry id)) s (VG.Proof.X25519.X86_64.Ifma.CarryPost 0 s) := by
  have hE := VG.Proof.X25519.X86_64.Ifma.carry_env (r := id) (fun i => (Nat.zero_add i).symm) hs hk hx
  have e : Sym.init.run (VG.Impl.X25519.X86_64.Ifma.carry id) = some VG.Proof.X25519.X86_64.Ifma.carryI := VG.Proof.X25519.X86_64.Ifma.carryS_eq id _
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, VG.Proof.X25519.X86_64.Ifma.carryI_st]; rfl, fun l hl i hi => ?_, fun r hr h1 h2 l hl => ?_⟩
  · obtain ⟨o, b⟩ := VG.Proof.X25519.X86_64.Ifma.carryI_ok i hi l hl
    obtain ⟨e, be⟩ := h.out hE (by omega) hl o
    have hs' : (fun j => VG.Proof.X25519.X86_64.Ifma.lanes s 0 l j) = fun j => (VG.Proof.X25519.X86_64.Ifma.envOf s).v j l := by
      funext j; simp only [VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add, VG.Proof.X25519.X86_64.Ifma.envOf_v]
    refine ⟨?_, by simp only [VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add]; omega⟩
    simp only [VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add] at e ⊢
    rw [e, VG.Proof.X25519.X86_64.Ifma.carryI_nat _ _ i hi, VG.Proof.X25519.X86_64.Ifma.envOf_m hs, VG.Proof.X25519.X86_64.Ifma.envOf_m hs, hk.km l hl, hk.k19 l hl, ← hs']
  · exact h.keep hr hl (VG.Proof.X25519.X86_64.Ifma.carryI_keep r hr (by omega))

theorem carryF_wp {s : State} {base : Addr}
    (hs : s.gpr .rdi = base) (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s) (hk : VG.Proof.X25519.X86_64.Ifma.CConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s 5 l i < 2 ^ 63) :
    WP isa (.block (VG.Impl.X25519.X86_64.Ifma.carry (5 + ·))) s (VG.Proof.X25519.X86_64.Ifma.CarryPost 5 s) := by
  have hE := VG.Proof.X25519.X86_64.Ifma.carry_env (r := (5 + ·)) (fun i => rfl) hs hk hx
  have e : Sym.init.run (VG.Impl.X25519.X86_64.Ifma.carry (5 + ·)) = some VG.Proof.X25519.X86_64.Ifma.carryF := VG.Proof.X25519.X86_64.Ifma.carryS_eq (5 + ·) _
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, VG.Proof.X25519.X86_64.Ifma.carryF_st]; rfl, fun l hl i hi => ?_, fun r hr h1 h2 l hl => ?_⟩
  · obtain ⟨o, b⟩ := VG.Proof.X25519.X86_64.Ifma.carryF_ok i hi l hl
    obtain ⟨e, be⟩ := h.out hE (by omega) hl o
    have hs' : (fun j => VG.Proof.X25519.X86_64.Ifma.lanes s 5 l j) = fun j => (VG.Proof.X25519.X86_64.Ifma.envOf s).v (5 + j) l := by
      funext j; simp only [VG.Proof.X25519.X86_64.Ifma.lanes, VG.Proof.X25519.X86_64.Ifma.envOf_v]
    refine ⟨?_, by simp only [VG.Proof.X25519.X86_64.Ifma.lanes]; omega⟩
    simp only [VG.Proof.X25519.X86_64.Ifma.lanes] at e ⊢
    rw [e, VG.Proof.X25519.X86_64.Ifma.carryF_nat _ _ i hi, VG.Proof.X25519.X86_64.Ifma.envOf_m hs, VG.Proof.X25519.X86_64.Ifma.envOf_m hs, hk.km l hl, hk.k19 l hl, ← hs']
  · exact h.keep hr hl (VG.Proof.X25519.X86_64.Ifma.carryF_keep r hr (by omega))

/-! ## Memory -/

open VG.Proof.X25519.X86_64 (Outside ofs word off) in
/-- Stores to slots in `[o, o + n)` change nothing outside it. -/
theorem stores_outside (s₀ : State) (base : Addr) (m : Mem) {o n : Nat} (hn : o + n < 2 ^ 63) :
    ∀ st : List (Nat × VG.Proof.X25519.X86_64.Ifma.T), (∀ e ∈ st, o ≤ e.1 ∧ e.1 + 32 ≤ o + n) →
      Outside base o n m (VG.Proof.X25519.X86_64.Ifma.stores s₀ base st m)
  | [], _ => fun _ _ => rfl
  | (e, t) :: st, h => by
    intro x hx
    have h₀ := h _ (List.mem_cons_self ..)
    simp only at h₀
    simp only [VG.Proof.X25519.X86_64.Ifma.stores]
    rw [writeW_byte_off _ _ _ _ ?_]
    · exact VG.Proof.X25519.X86_64.Ifma.stores_outside s₀ base m hn st (fun x hx => h x (List.mem_cons_of_mem _ hx)) x hx
    · show 256 / 8 ≤ (x - (base + BitVec.ofNat 64 e)).toNat
      rw [Offset.sub_add_eq, Offset.toNat_sub_ofNat]
      simp only [ofs] at hx
      have := (x - base).isLt
      rw [Nat.mod_eq_of_lt (show e < 2 ^ 64 by omega)]
      omega

theorem mq_eq_word (m : Mem) (base : Addr) (d : Nat) : VG.Proof.X25519.X86_64.Ifma.mq m base d = word m base d := rfl

open VG.Proof.X25519.X86_64 (Outside) in
theorem Consts.outside {m m' : Mem} {base : Addr} {x1 : Nat → Nat} (hk : VG.Proof.X25519.X86_64.Ifma.Consts m base x1)
    (h : Outside base 1024 480 m m') : VG.Proof.X25519.X86_64.Ifma.Consts m' base x1 := by
  have w : ∀ d, 1504 ≤ d → d + 8 ≤ 4096 → VG.Proof.X25519.X86_64.Ifma.mq m' base d = VG.Proof.X25519.X86_64.Ifma.mq m base d := fun d h1 h2 => by
    rw [VG.Proof.X25519.X86_64.Ifma.mq_eq_word, VG.Proof.X25519.X86_64.Ifma.mq_eq_word]; exact h.word (by omega) (by omega)
  refine ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun i hi l hl => ?_,
    fun i hi l hl => ?_, hk.x1, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩
  · rw [w _ (by simp only [KM]; omega) (by simp only [KM]; omega)]; exact hk.km l hl
  · rw [w _ (by simp only [K19]; omega) (by simp only [K19]; omega)]; exact hk.k19 l hl
  · rw [w _ (by simp only [KB0]; omega) (by simp only [KB0]; omega)]; exact hk.kb0 l hl
  · rw [w _ (by simp only [KB1]; omega) (by simp only [KB1]; omega)]; exact hk.kb1 l hl
  · rw [VG.Proof.X25519.X86_64.Ifma.slotv, w _ (by simp only [KA24]; omega) (by simp only [KA24]; omega)]; exact hk.a24 i hi l hl
  · rw [VG.Proof.X25519.X86_64.Ifma.slotv, w _ (by simp only [KX1]; omega) (by simp only [KX1]; omega)]; exact hk.kx1 i hi l hl
  · rw [w _ (by simp only [K13]; omega) (by simp only [K13]; omega)]; exact hk.k13 l hl
  · rw [w _ (by simp only [K26]; omega) (by simp only [K26]; omega)]; exact hk.k26 l hl
  · rw [w _ (by simp only [K39]; omega) (by simp only [K39]; omega)]; exact hk.k39 l hl

/-! ## Products -/

/-- What `mul4 a` leaves: the product of the slot `a` and `ymm5–ymm9`, lane by
lane, in `ymm0–ymm4`. -/
def MulPost (base : Addr) (a : Nat) (s s' : State) : Prop :=
  VG.Proof.X25519.X86_64.Ifma.vm s s' = s' ∧ s'.mem = s.mem ∧
    (∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s' 0 l i = VG.Proof.X25519.X86_64.Ifma.mulNat (VG.Proof.X25519.X86_64.Ifma.slotv s.mem base a l) (VG.Proof.X25519.X86_64.Ifma.lanes s 5 l) i ∧
      VG.Proof.X25519.X86_64.Ifma.lanes s' 0 l i < 2 ^ 61) ∧
    (∀ r < 16, 5 ≤ r → r < 10 ∨ r = 15 → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l)

theorem mul4_wp {a : Nat} (ha : a % 32 = 0) {σ : VG.Proof.X25519.X86_64.Ifma.Sym}
    (he : Sym.init.run (mul4 a) = some σ)
    (hnat : ∀ E l, ∀ k < 5, (σ.reg k).nat E l = VG.Proof.X25519.X86_64.Ifma.mulNat (fun i => E.m (a + 32 * i) l) (fun j => E.v (5 + j) l) k)
    (hok : ∀ k < 5, ∀ l < 4, (σ.reg k).ok (VG.Proof.X25519.X86_64.Ifma.mulB a) l = true ∧ (σ.reg k).bnd (VG.Proof.X25519.X86_64.Ifma.mulB a) l < 2 ^ 61)
    (hkeep : ∀ r < 16, 5 ≤ r → r < 10 ∨ r = 15 → σ.reg r = .reg r) (hst : σ.st = [])
    {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s)
    (hx : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.slotv s.mem base a l i < 2 ^ 52)
    (hy : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s 5 l i < 2 ^ 52) :
    WP isa (.block (mul4 a)) s (VG.Proof.X25519.X86_64.Ifma.MulPost base a s) := by
  have hE : VG.Proof.X25519.X86_64.Ifma.EnvOK s (VG.Proof.X25519.X86_64.Ifma.mulB a) := by
    refine VG.Proof.X25519.X86_64.Ifma.envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun _ _ _ => Nat.zero_le _)
    · simp only [VG.Proof.X25519.X86_64.Ifma.mulB]
      split
      · rename_i h
        have := hy l hl (r - 5) (by omega)
        simp only [VG.Proof.X25519.X86_64.Ifma.lanes, show 5 + (r - 5) = r by omega] at this
        omega
      · exact VG.Proof.X25519.X86_64.Ifma.lt64 _
    · simp only [VG.Proof.X25519.X86_64.Ifma.mulB]
      split
      · rename_i h
        obtain ⟨i, hi, rfl⟩ : ∃ i < 5, d = a + 32 * i := ⟨(d - a) / 32, by omega, by omega⟩
        have := hx l hl i hi
        simp only [VG.Proof.X25519.X86_64.Ifma.slotv] at this
        omega
      · exact VG.Proof.X25519.X86_64.Ifma.lt64 _
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.run_ok hc he) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, hst]; rfl, fun l hl i hi => ?_, fun r hr h1 h2 l hl => h.keep hr hl (hkeep r hr h1 h2)⟩
  obtain ⟨o, b⟩ := hok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega) hl o
  simp only [VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add] at e ⊢
  refine ⟨?_, by omega⟩
  have hf : (fun i => (VG.Proof.X25519.X86_64.Ifma.envOf s).m (a + 32 * i) l) = VG.Proof.X25519.X86_64.Ifma.slotv s.mem base a l :=
    funext fun j => by rw [VG.Proof.X25519.X86_64.Ifma.envOf_m hs, VG.Proof.X25519.X86_64.Ifma.slotv]
  have hg : (fun j => (VG.Proof.X25519.X86_64.Ifma.envOf s).v (5 + j) l) = VG.Proof.X25519.X86_64.Ifma.lanes s 5 l := funext fun j => rfl
  rw [e, hnat _ _ i hi, hf, hg]

/-! ## The stages -/

/-- The bias's limb `j`. -/
def kbv (j : Nat) : Nat := if j = 0 then 2 ^ 62 - 38912 else 2 ^ 62 - 2048

theorem kb_m {m : Mem} {base : Addr} (hk : VG.Proof.X25519.X86_64.Ifma.CConsts m base) {j l : Nat} (hl : l < 4) :
    (VG.Proof.X25519.X86_64.Ifma.mq m base (kb j + 8 * l)).toNat = VG.Proof.X25519.X86_64.Ifma.kbv j := by
  simp only [kb, VG.Proof.X25519.X86_64.Ifma.kbv]; split
  · exact hk.kb0 l hl
  · exact hk.kb1 l hl

/-- Stage 1's sums and differences, limb `i` of lane `l`, from the lanes `x`
(`x l i`). -/
def sumDiff (x : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 0 => x 0 i + x 1 i
  | 1 => x 0 i + (VG.Proof.X25519.X86_64.Ifma.kbv i - x 1 i)
  | 2 => x 2 i + x 3 i
  | _ => x 2 i + (VG.Proof.X25519.X86_64.Ifma.kbv i - x 3 i)

theorem s1a_wp {s : State} {base : Addr} {x1 : Nat → Nat} (hs : s.gpr .rdi = base) (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s)
    (hk : VG.Proof.X25519.X86_64.Ifma.Consts s.mem base x1) (hx : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s 0 l i < 2 ^ 61) :
    WP isa (.block stage1a) s fun s' => VG.Proof.X25519.X86_64.Ifma.vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s' 0 l i = VG.Proof.X25519.X86_64.Ifma.sumDiff (VG.Proof.X25519.X86_64.Ifma.lanes s 0) l i ∧ VG.Proof.X25519.X86_64.Ifma.lanes s' 0 l i < 2 ^ 63) ∧
      (∀ r < 16, 5 ≤ r → ¬ (10 ≤ r ∧ r < 13) → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have hE : VG.Proof.X25519.X86_64.Ifma.EnvOK s VG.Proof.X25519.X86_64.Ifma.s1aB := by
    refine VG.Proof.X25519.X86_64.Ifma.envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun d l hl => ?_)
    · simp only [VG.Proof.X25519.X86_64.Ifma.s1aB]
      split
      · have := hx l hl r (by omega); simp only [VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add] at this; omega
      · exact VG.Proof.X25519.X86_64.Ifma.lt64 _
    · simp only [VG.Proof.X25519.X86_64.Ifma.s1aB]
      split
      · subst_vars; rw [hk.kb0 l hl]
      · split
        · subst_vars; rw [hk.kb1 l hl]
        · exact VG.Proof.X25519.X86_64.Ifma.lt64 _
    · simp only [VG.Proof.X25519.X86_64.Ifma.s1aB]
      split
      · subst_vars; rw [hk.kb0 l hl]
      · split
        · subst_vars; rw [hk.kb1 l hl]
        · exact Nat.zero_le _
  have e : Sym.init.run stage1a = some VG.Proof.X25519.X86_64.Ifma.s1a := VG.Proof.X25519.X86_64.Ifma.symOf_eq _ _
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, VG.Proof.X25519.X86_64.Ifma.s1a_st]; rfl, fun l hl i hi => ?_,
    fun r hr h1 h2 l hl => h.keep hr hl (VG.Proof.X25519.X86_64.Ifma.s1a_keep r hr h1 h2)⟩
  obtain ⟨o, b⟩ := VG.Proof.X25519.X86_64.Ifma.s1a_ok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega) hl o
  simp only [VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add] at e ⊢
  refine ⟨?_, by omega⟩
  rw [e, VG.Proof.X25519.X86_64.Ifma.s1a_nat _ i hi l hl]
  have kbe : (VG.Proof.X25519.X86_64.Ifma.envOf s).m (kb i) = fun l => (VG.Proof.X25519.X86_64.Ifma.mq s.mem base (kb i + 8 * l)).toNat := by
    funext l; rw [VG.Proof.X25519.X86_64.Ifma.envOf_m hs]
  rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
    simp only [VG.Proof.X25519.X86_64.Ifma.s1aNat, VG.Proof.X25519.X86_64.Ifma.sumDiff, VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add, VG.Proof.X25519.X86_64.Ifma.envOf_v, kbe, VG.Proof.X25519.X86_64.Ifma.kb_m hk.c (show 1 < 4 by decide),
      VG.Proof.X25519.X86_64.Ifma.kb_m hk.c (show 3 < 4 by decide)]

/-- What `stage1b` leaves: `(A, B, D, C)` in `OPL`, `(A, B, A, B)` in `ymm5–ymm9`. -/
theorem s1b_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s) :
    WP isa (.block stage1b) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VG.Proof.X25519.X86_64.Outside base OPL 160 s.mem s'.mem ∧
      (∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.slotv s'.mem base OPL l i = VG.Proof.X25519.X86_64.Ifma.lanes s 0 (sel4 (ord 0 1 3 2).toNat l) i ∧
        VG.Proof.X25519.X86_64.Ifma.lanes s' 5 l i = VG.Proof.X25519.X86_64.Ifma.lanes s 0 (sel4 (ord 0 1 0 1).toNat l) i) ∧
      (∀ r < 16, (r < 5 ∨ 11 ≤ r) → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have e : Sym.init.run stage1b = some VG.Proof.X25519.X86_64.Ifma.s1b := VG.Proof.X25519.X86_64.Ifma.symOf_eq _ _
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.run_ok hc e) fun s' h => ?_
  refine ⟨h.gpr, h.rd, h.wr, ?_, fun l hl i hi => ⟨?_, ?_⟩, fun r hr h1 l hl => h.keep hr hl (VG.Proof.X25519.X86_64.Ifma.s1b_keep r hr h1)⟩
  · rw [h.mem, hs]
    exact VG.Proof.X25519.X86_64.Ifma.stores_outside _ _ _ (by decide) _ (by rw [VG.Proof.X25519.X86_64.Ifma.s1b_st]; decide)
  · have hm : ∀ i < 5, ((OPL + 32 * i), T.perm (.reg i) (ord 0 1 3 2).toNat) ∈ s1b.st := by
      rw [VG.Proof.X25519.X86_64.Ifma.s1b_st]; decide
    rw [VG.Proof.X25519.X86_64.Ifma.slotv, h.mem, hs, VG.Proof.X25519.X86_64.Ifma.stores_mq _ _ _ _ (hm i hi) hl (by rw [VG.Proof.X25519.X86_64.Ifma.s1b_st]; decide) (by rw [VG.Proof.X25519.X86_64.Ifma.s1b_st]; decide)]
    simp only [T.eval, VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add]
  · have := h.reg (xr (5 + i)) l hl
    rw [VG.Proof.X25519.X86_64.Ifma.xi_xr _ (by omega), VG.Proof.X25519.X86_64.Ifma.s1b_regs i hi] at this
    simp only [VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add, this, T.eval]

/-- Stage 2's first operand from `(AA, BB, DA, CB)` (`x l i`):
`(DA + CB, DA + bias - CB, AA, AA + bias - BB)`. -/
def opV (x : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 0 => x 2 i + x 3 i
  | 1 => x 2 i + (VG.Proof.X25519.X86_64.Ifma.kbv i - x 3 i)
  | 2 => x 0 i + 0
  | _ => x 0 i + (VG.Proof.X25519.X86_64.Ifma.kbv i - x 1 i)

/-- Stage 2's second operand: `(DA + CB, DA + bias - CB, BB, a24)`. -/
def opW (x : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 0 => x 2 i + x 3 i
  | 1 => x 2 i + (VG.Proof.X25519.X86_64.Ifma.kbv i - x 3 i)
  | 2 => x 1 i
  | _ => if i = 0 then 121665 else 0

theorem s2a_wp {s : State} {base : Addr} {x1 : Nat → Nat} (hs : s.gpr .rdi = base) (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s)
    (hk : VG.Proof.X25519.X86_64.Ifma.Consts s.mem base x1) (hx : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s 0 l i < 2 ^ 61) :
    WP isa (.block stage2a) s fun s' => VG.Proof.X25519.X86_64.Ifma.vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s' 5 l i = VG.Proof.X25519.X86_64.Ifma.opV (VG.Proof.X25519.X86_64.Ifma.lanes s 0) l i ∧ VG.Proof.X25519.X86_64.Ifma.lanes s' 5 l i < 2 ^ 63 ∧
        VG.Proof.X25519.X86_64.Ifma.lanes s' 0 l i = VG.Proof.X25519.X86_64.Ifma.opW (VG.Proof.X25519.X86_64.Ifma.lanes s 0) l i ∧ VG.Proof.X25519.X86_64.Ifma.lanes s' 0 l i < 2 ^ 63) ∧
      (∀ r < 16, 14 ≤ r → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have hE : VG.Proof.X25519.X86_64.Ifma.EnvOK s VG.Proof.X25519.X86_64.Ifma.s2aB := by
    refine VG.Proof.X25519.X86_64.Ifma.envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun d l hl => ?_)
    · simp only [VG.Proof.X25519.X86_64.Ifma.s2aB]
      split
      · have := hx l hl r (by omega); simp only [VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add] at this; omega
      · exact VG.Proof.X25519.X86_64.Ifma.lt64 _
    · simp only [VG.Proof.X25519.X86_64.Ifma.s2aB]
      split
      · subst_vars; rw [hk.kb0 l hl]
      · split
        · subst_vars; rw [hk.kb1 l hl]
        · split
          · rename_i h
            obtain ⟨i, hi, rfl⟩ : ∃ i < 5, d = KA24 + 32 * i :=
              ⟨(d - KA24) / 32, by simp only [KA24] at h ⊢; omega, by simp only [KA24] at h ⊢; omega⟩
            have := hk.a24 i hi l hl
            simp only [VG.Proof.X25519.X86_64.Ifma.slotv] at this
            rw [this]; split <;> decide
          · exact VG.Proof.X25519.X86_64.Ifma.lt64 _
    · simp only [VG.Proof.X25519.X86_64.Ifma.s2aB]
      split
      · subst_vars; rw [hk.kb0 l hl]
      · split
        · subst_vars; rw [hk.kb1 l hl]
        · exact Nat.zero_le _
  have e : Sym.init.run stage2a = some VG.Proof.X25519.X86_64.Ifma.s2a := VG.Proof.X25519.X86_64.Ifma.symOf_eq _ _
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, VG.Proof.X25519.X86_64.Ifma.s2a_st]; rfl, fun l hl i hi => ?_,
    fun r hr h1 l hl => h.keep hr hl (VG.Proof.X25519.X86_64.Ifma.s2a_keep r hr h1)⟩
  obtain ⟨o1, b1, o2, b2⟩ := VG.Proof.X25519.X86_64.Ifma.s2a_ok i hi l hl
  obtain ⟨e1, be1⟩ := h.out hE (by omega) hl o1
  obtain ⟨e2, be2⟩ := h.out hE (by omega) hl o2
  obtain ⟨n1, n2⟩ := VG.Proof.X25519.X86_64.Ifma.s2a_nat (VG.Proof.X25519.X86_64.Ifma.envOf s) i hi l hl
  simp only [VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add] at e1 e2 ⊢
  refine ⟨?_, by omega, ?_, by omega⟩
  · rw [e1, n1]
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
      simp only [VG.Proof.X25519.X86_64.Ifma.s2aV, VG.Proof.X25519.X86_64.Ifma.opV, VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add, VG.Proof.X25519.X86_64.Ifma.envOf_v, VG.Proof.X25519.X86_64.Ifma.envOf_m hs, VG.Proof.X25519.X86_64.Ifma.kb_m hk.c (show 1 < 4 by decide),
        VG.Proof.X25519.X86_64.Ifma.kb_m hk.c (show 3 < 4 by decide)]
  · rw [e2, n2]
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
      simp only [VG.Proof.X25519.X86_64.Ifma.s2aW, VG.Proof.X25519.X86_64.Ifma.opW, VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add, VG.Proof.X25519.X86_64.Ifma.envOf_v, VG.Proof.X25519.X86_64.Ifma.envOf_m hs, VG.Proof.X25519.X86_64.Ifma.kb_m hk.c (show 1 < 4 by decide)]
    have := hk.a24 i hi 3 (by decide)
    simp only [VG.Proof.X25519.X86_64.Ifma.slotv] at this
    rw [this]
    simp

/-- What `stage2b` leaves: stage 2's first operand in `OPV`, the second in
`ymm5–ymm9`. -/
theorem s2b_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s) :
    WP isa (.block stage2b) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VG.Proof.X25519.X86_64.Outside base OPV 160 s.mem s'.mem ∧
      (∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.slotv s'.mem base OPV l i = VG.Proof.X25519.X86_64.Ifma.lanes s 5 l i ∧ VG.Proof.X25519.X86_64.Ifma.lanes s' 5 l i = VG.Proof.X25519.X86_64.Ifma.lanes s 0 l i) ∧
      (∀ r < 16, (r < 5 ∨ 10 ≤ r) → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have e : Sym.init.run stage2b = some VG.Proof.X25519.X86_64.Ifma.s2b := VG.Proof.X25519.X86_64.Ifma.symOf_eq _ _
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.run_ok hc e) fun s' h => ?_
  refine ⟨h.gpr, h.rd, h.wr, ?_, fun l hl i hi => ⟨?_, ?_⟩, fun r hr h1 l hl => h.keep hr hl (VG.Proof.X25519.X86_64.Ifma.s2b_keep r hr h1)⟩
  · rw [h.mem, hs]
    exact VG.Proof.X25519.X86_64.Ifma.stores_outside _ _ _ (by decide) _ (by rw [VG.Proof.X25519.X86_64.Ifma.s2b_st]; decide)
  · have hm : ∀ i < 5, ((OPV + 32 * i), T.reg (5 + i)) ∈ s2b.st := by
      rw [VG.Proof.X25519.X86_64.Ifma.s2b_st]; decide
    rw [VG.Proof.X25519.X86_64.Ifma.slotv, h.mem, hs, VG.Proof.X25519.X86_64.Ifma.stores_mq _ _ _ _ (hm i hi) hl (by rw [VG.Proof.X25519.X86_64.Ifma.s2b_st]; decide) (by rw [VG.Proof.X25519.X86_64.Ifma.s2b_st]; decide)]
    simp only [T.eval, VG.Proof.X25519.X86_64.Ifma.lanes]
  · have := h.reg (xr (5 + i)) l hl
    rw [VG.Proof.X25519.X86_64.Ifma.xi_xr _ (by omega), VG.Proof.X25519.X86_64.Ifma.s2b_regs i hi] at this
    simp only [VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add, this, T.eval]

/-- Stage 3's second operand, from stage 2's product `(x₃', t, x₂', a24 E)`
(`x l i`) and first operand `(…, …, AA, E)` (`v l i`): `(1, AA + a24 E, 1, x₁)`. -/
def opH (x1 : Nat → Nat) (x v : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 1 => v 2 i + x 3 i
  | 3 => x1 i
  | _ => if i = 0 then 1 else 0

/-- Stage 3's first operand: `(x₂', E, x₃', t)`. -/
def opG (x v : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 0 => x 2 i
  | 1 => v 3 i
  | 2 => x 0 i
  | _ => x 1 i

theorem s3a_wp {s : State} {base : Addr} {x1 : Nat → Nat} (hs : s.gpr .rdi = base) (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s)
    (hk : VG.Proof.X25519.X86_64.Ifma.Consts s.mem base x1) (hx : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s 0 l i < 2 ^ 61)
    (hv : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.slotv s.mem base OPV l i < 2 ^ 52) :
    WP isa (.block stage3a) s fun s' => VG.Proof.X25519.X86_64.Ifma.vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s' 5 l i = VG.Proof.X25519.X86_64.Ifma.opH x1 (VG.Proof.X25519.X86_64.Ifma.lanes s 0) (VG.Proof.X25519.X86_64.Ifma.slotv s.mem base OPV) l i ∧
        VG.Proof.X25519.X86_64.Ifma.lanes s' 5 l i < 2 ^ 63 ∧
        VG.Proof.X25519.X86_64.Ifma.lanes s' 0 l i = VG.Proof.X25519.X86_64.Ifma.opG (VG.Proof.X25519.X86_64.Ifma.lanes s 0) (VG.Proof.X25519.X86_64.Ifma.slotv s.mem base OPV) l i ∧ VG.Proof.X25519.X86_64.Ifma.lanes s' 0 l i < 2 ^ 63) ∧
      (∀ r < 16, 13 ≤ r → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have hE : VG.Proof.X25519.X86_64.Ifma.EnvOK s VG.Proof.X25519.X86_64.Ifma.s3aB := by
    refine VG.Proof.X25519.X86_64.Ifma.envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun _ _ _ => Nat.zero_le _)
    · simp only [VG.Proof.X25519.X86_64.Ifma.s3aB]
      split
      · have := hx l hl r (by omega); simp only [VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add] at this; omega
      · exact VG.Proof.X25519.X86_64.Ifma.lt64 _
    · simp only [VG.Proof.X25519.X86_64.Ifma.s3aB]
      split
      · rename_i h
        rcases h with ⟨h | h, h'⟩
        · obtain ⟨i, hi, rfl⟩ : ∃ i < 5, d = OPV + 32 * i :=
            ⟨(d - OPV) / 32, by simp only [OPV] at h h' ⊢; omega, by simp only [OPV] at h h' ⊢; omega⟩
          have := hv l hl i hi
          simp only [VG.Proof.X25519.X86_64.Ifma.slotv] at this
          omega
        · obtain ⟨i, hi, rfl⟩ : ∃ i < 5, d = KX1 + 32 * i :=
            ⟨(d - KX1) / 32, by simp only [KX1] at h h' ⊢; omega, by simp only [KX1] at h h' ⊢; omega⟩
          have := VG.Proof.X25519.X86_64.Ifma.kx1_le hk hi hl
          simp only [VG.Proof.X25519.X86_64.Ifma.slotv] at this
          omega
      · exact VG.Proof.X25519.X86_64.Ifma.lt64 _
  have e : Sym.init.run stage3a = some VG.Proof.X25519.X86_64.Ifma.s3a := VG.Proof.X25519.X86_64.Ifma.symOf_eq _ _
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, VG.Proof.X25519.X86_64.Ifma.s3a_st]; rfl, fun l hl i hi => ?_,
    fun r hr h1 l hl => h.keep hr hl (VG.Proof.X25519.X86_64.Ifma.s3a_keep r hr h1)⟩
  obtain ⟨o1, b1, o2, b2⟩ := VG.Proof.X25519.X86_64.Ifma.s3a_ok i hi l hl
  obtain ⟨e1, be1⟩ := h.out hE (by omega) hl o1
  obtain ⟨e2, be2⟩ := h.out hE (by omega) hl o2
  obtain ⟨n1, n2⟩ := VG.Proof.X25519.X86_64.Ifma.s3a_nat (VG.Proof.X25519.X86_64.Ifma.envOf s) i hi l hl
  simp only [VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add] at e1 e2 ⊢
  refine ⟨?_, by omega, ?_, by omega⟩
  · rw [e1, n1]
    have kx := hk.kx1 i hi l hl
    simp only [VG.Proof.X25519.X86_64.Ifma.slotv] at kx
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
      simp only [VG.Proof.X25519.X86_64.Ifma.s3aH, VG.Proof.X25519.X86_64.Ifma.opH, VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add, VG.Proof.X25519.X86_64.Ifma.envOf_v, VG.Proof.X25519.X86_64.Ifma.envOf_m hs, VG.Proof.X25519.X86_64.Ifma.slotv, kx] <;> simp
  · rw [e2, n2]
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
      simp only [VG.Proof.X25519.X86_64.Ifma.s3aG, VG.Proof.X25519.X86_64.Ifma.opG, VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add, VG.Proof.X25519.X86_64.Ifma.envOf_v, VG.Proof.X25519.X86_64.Ifma.envOf_m hs, VG.Proof.X25519.X86_64.Ifma.slotv]

/-- What `stage3b` leaves: stage 3's first operand in `OPG`. -/
theorem s3b_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s) :
    WP isa (.block stage3b) s fun s' => VG.Proof.X25519.X86_64.Ifma.vm s s' = s' ∧
      VG.Proof.X25519.X86_64.Outside base OPG 160 s.mem s'.mem ∧
      (∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.slotv s'.mem base OPG l i = VG.Proof.X25519.X86_64.Ifma.lanes s 0 l i) ∧
      (∀ r < 16, ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have e : Sym.init.run stage3b = some VG.Proof.X25519.X86_64.Ifma.s3b := VG.Proof.X25519.X86_64.Ifma.symOf_eq _ _
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, ?_, fun l hl i hi => ?_, fun r hr l hl => h.keep hr hl (VG.Proof.X25519.X86_64.Ifma.s3b_keep r hr)⟩
  · rw [h.mem, hs]
    exact VG.Proof.X25519.X86_64.Ifma.stores_outside _ _ _ (by decide) _ (by rw [VG.Proof.X25519.X86_64.Ifma.s3b_st]; decide)
  · have hm : ∀ i < 5, ((OPG + 32 * i), T.reg i) ∈ s3b.st := by
      rw [VG.Proof.X25519.X86_64.Ifma.s3b_st]; decide
    rw [VG.Proof.X25519.X86_64.Ifma.slotv, h.mem, hs, VG.Proof.X25519.X86_64.Ifma.stores_mq _ _ _ _ (hm i hi) hl (by rw [VG.Proof.X25519.X86_64.Ifma.s3b_st]; decide) (by rw [VG.Proof.X25519.X86_64.Ifma.s3b_st]; decide)]
    simp only [T.eval, VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add]

/-! ## The swap -/

/-- The mask into `ymm15`, then the swap. -/
def vsw : List Instr := [.vop (.vmovq (y 15) .rcx), .vop (.vpbroadcastq .l256 (y 15) (y 15))] ++ vswap

def swS : VG.Proof.X25519.X86_64.Ifma.Sym := VG.Proof.X25519.X86_64.Ifma.symOf VG.Proof.X25519.X86_64.Ifma.vsw

theorem swS_regs : ∀ j < 5, swS.reg j = .xor (.reg j)
    (.and (.xor (.perm (.reg j) (ord 2 3 0 1).toNat) (.reg j)) (.bc (.lane0 (.gpr .rcx)))) := by
  decide +kernel
theorem swS_keep : ∀ r < 15, 5 ≤ r → r ≠ 10 → swS.reg r = .reg r := by decide +kernel
theorem swS_st : swS.st = [] := by decide +kernel

theorem xor_mask (x y : BitVec 64) (b : Bool) :
    x ^^^ ((y ^^^ x) &&& VG.Proof.X25519.X86_64.mask b) = if b then y else x := by
  cases b
  · simp [VG.Proof.X25519.X86_64.mask]
  · simp only [VG.Proof.X25519.X86_64.mask, ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm y x, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem sel4_swap : ∀ l < 4, sel4 (ord 2 3 0 1).toNat l = l ^^^ 2 := by decide

theorem vsw_wp {s : State} (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s) {b : Bool} (hm : s.gpr .rcx = VG.Proof.X25519.X86_64.mask b) :
    WP isa (.block VG.Proof.X25519.X86_64.Ifma.vsw) s fun s' => VG.Proof.X25519.X86_64.Ifma.vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, qw s' (xr i) l = qw s (xr i) (if b then l ^^^ 2 else l)) ∧
      (∀ r < 15, 5 ≤ r → r ≠ 10 → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have e : Sym.init.run VG.Proof.X25519.X86_64.Ifma.vsw = some VG.Proof.X25519.X86_64.Ifma.swS := VG.Proof.X25519.X86_64.Ifma.symOf_eq _ _
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, VG.Proof.X25519.X86_64.Ifma.swS_st]; rfl, fun l hl i hi => ?_,
    fun r hr h1 h2 l hl => h.keep (by omega) hl (VG.Proof.X25519.X86_64.Ifma.swS_keep r hr h1 h2)⟩
  rw [h.reg _ l hl, VG.Proof.X25519.X86_64.Ifma.xi_xr _ (by omega), VG.Proof.X25519.X86_64.Ifma.swS_regs i hi]
  simp only [T.eval, ite_true, hm, VG.Proof.X25519.X86_64.Ifma.sel4_swap l hl]
  rw [VG.Proof.X25519.X86_64.Ifma.xor_mask]
  cases b <;> rfl

end VG.Proof.X25519.X86_64.Ifma

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Ifma.Lanes`. -/
section

/-!
# X25519 on x86-64 with AVX512_IFMA: limbs as field elements

Five limbs stand for an element of `GF(p)` (`fe5`); the sums, differences
(with the bias `2¹¹ p`), carries and products of the stages are the field's
operations on them.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG.Proof.X25519 VG.Spec.X25519

/-- The element of `GF(p)` five limbs stand for. -/
def fe5 (x : Nat → Nat) : Fe := toFe (VG.Proof.X25519.X86_64.Ifma.lv x)

theorem lv_congr {x y : Nat → Nat} (h : ∀ i < 5, x i = y i) : VG.Proof.X25519.X86_64.Ifma.lv x = VG.Proof.X25519.X86_64.Ifma.lv y := by
  simp only [VG.Proof.X25519.X86_64.Ifma.lv, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]

theorem fe5_congr {x y : Nat → Nat} (h : ∀ i < 5, x i = y i) : VG.Proof.X25519.X86_64.Ifma.fe5 x = VG.Proof.X25519.X86_64.Ifma.fe5 y := by
  rw [VG.Proof.X25519.X86_64.Ifma.fe5, VG.Proof.X25519.X86_64.Ifma.fe5, VG.Proof.X25519.X86_64.Ifma.lv_congr h]

theorem fe5_add {x y z : Nat → Nat} (h : ∀ i < 5, z i = x i + y i) : VG.Proof.X25519.X86_64.Ifma.fe5 z = VG.Proof.X25519.X86_64.Ifma.fe5 x + VG.Proof.X25519.X86_64.Ifma.fe5 y := by
  refine toFe_add (congrArg (· % VG.Spec.X25519.P) ?_)
  simp only [VG.Proof.X25519.X86_64.Ifma.lv, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]
  omega

theorem lv_kbv : VG.Proof.X25519.X86_64.Ifma.lv VG.Proof.X25519.X86_64.Ifma.kbv = 2 ^ 11 * VG.Spec.X25519.P := by decide

theorem fe5_sub {x y z : Nat → Nat} (h : ∀ i < 5, z i = x i + (VG.Proof.X25519.X86_64.Ifma.kbv i - y i)) (hy : ∀ i < 5, y i ≤ VG.Proof.X25519.X86_64.Ifma.kbv i) :
    VG.Proof.X25519.X86_64.Ifma.fe5 z = VG.Proof.X25519.X86_64.Ifma.fe5 x - VG.Proof.X25519.X86_64.Ifma.fe5 y := by
  refine toFe_sub ?_
  have e : VG.Proof.X25519.X86_64.Ifma.lv z + VG.Proof.X25519.X86_64.Ifma.lv y = VG.Proof.X25519.X86_64.Ifma.lv x + VG.Spec.X25519.P * 2 ^ 11 := by
    rw [Nat.mul_comm, ← VG.Proof.X25519.X86_64.Ifma.lv_kbv]
    have h0 := hy 0 (by decide); have h1 := hy 1 (by decide); have h2 := hy 2 (by decide)
    have h3 := hy 3 (by decide); have h4 := hy 4 (by decide)
    simp only [VG.Proof.X25519.X86_64.Ifma.lv, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]
    simp only [VG.Proof.X25519.X86_64.Ifma.kbv] at h0 h1 h2 h3 h4 ⊢
    omega
  rw [e, Nat.add_mul_mod_self_left]

theorem fe5_carry (x : Nat → Nat) (h4 : x 4 < 2 ^ 63) : VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.carryNat (2 ^ 51 - 1) 19 x) = VG.Proof.X25519.X86_64.Ifma.fe5 x :=
  toFe_congr (VG.Proof.X25519.X86_64.Ifma.carryNat_mod x h4)

theorem fe5_mul {a b : Nat → Nat} (ha : ∀ i < 5, a i < 2 ^ 52) (hb : ∀ i < 5, b i < 2 ^ 52) :
    VG.Proof.X25519.X86_64.Ifma.fe5 (fun k => VG.Proof.X25519.X86_64.Ifma.mulNat a b k) = VG.Proof.X25519.X86_64.Ifma.fe5 a * VG.Proof.X25519.X86_64.Ifma.fe5 b := by
  refine toFe_mul ?_
  rw [show (fun k => VG.Proof.X25519.X86_64.Ifma.mulNat a b k) = VG.Proof.X25519.X86_64.Ifma.mulNat a b from rfl, VG.Proof.X25519.X86_64.Ifma.mulNat_mod,
    VG.Proof.X25519.X86_64.Ifma.lv_congr (x := fun i => a i % 2 ^ 52) (y := a) (fun i hi => Nat.mod_eq_of_lt (ha i hi)),
    VG.Proof.X25519.X86_64.Ifma.lv_congr (x := fun i => b i % 2 ^ 52) (y := b) (fun i hi => Nat.mod_eq_of_lt (hb i hi))]

theorem fe5_one : VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => if i = 0 then 1 else 0) = 1 := rfl

theorem fe5_a24 : VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => if i = 0 then 121665 else 0) = a24 := rfl

end VG.Proof.X25519.X86_64.Ifma

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Ifma.Part1`. -/
section

/-!
# X25519 on x86-64 with AVX512_IFMA: stage 1 of an iteration

From `(x₂, z₂, x₃, z₃)` in the lanes of `ymm0–ymm4`, stage 1 and its product
leave `(AA, BB, DA, CB)` there.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.X25519.X86_64 (Scr Outside Outside.mono contains_sc)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw sel4)

theorem scr_ctx {s : State} {base : Addr} (hs : Scr s base) : VG.Proof.X25519.X86_64.Ifma.Ctx s := fun d hd => by
  rw [hs.rdi]; exact ⟨_, hs.wr, contains_sc hd⟩

theorem vm_gpr {s s' : State} (h : VG.Proof.X25519.X86_64.Ifma.vm s s' = s') : s'.gpr = s.gpr := by rw [← h]; rfl
theorem vm_rd {s s' : State} (h : VG.Proof.X25519.X86_64.Ifma.vm s s' = s') : s'.rd = s.rd := by rw [← h]; rfl
theorem vm_wr {s s' : State} (h : VG.Proof.X25519.X86_64.Ifma.vm s s' = s') : s'.wr = s.wr := by rw [← h]; rfl

theorem scr_of {s s' : State} {base : Addr} (hs : Scr s base) (hg : s'.gpr = s.gpr)
    (hw : s'.wr = s.wr) : Scr s' base := ⟨by rw [hg]; exact hs.rdi, by rw [hw]; exact hs.wr, hs.nowrap⟩

/-- What a part of an iteration keeps. -/
structure Kept (base : Addr) (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outside base 1024 480 s.mem s'.mem

theorem Kept.trans {base : Addr} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.X25519.X86_64.Ifma.Kept base s₁ s₂) (h₂ : VG.Proof.X25519.X86_64.Ifma.Kept base s₂ s₃) :
    VG.Proof.X25519.X86_64.Ifma.Kept base s₁ s₃ :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₁.mem.trans h₂.mem⟩

theorem Kept.vm {base : Addr} {s s' : State} (h : VG.Proof.X25519.X86_64.Ifma.vm s s' = s') (hm : s'.mem = s.mem) : VG.Proof.X25519.X86_64.Ifma.Kept base s s' :=
  ⟨VG.Proof.X25519.X86_64.Ifma.vm_gpr h, VG.Proof.X25519.X86_64.Ifma.vm_rd h, VG.Proof.X25519.X86_64.Ifma.vm_wr h, by rw [hm]; exact Outside.refl _ _ _ _⟩

/-- Stage 1 and its product. -/
theorem part1_ok {s : State} {base : Addr} {x1 : Nat → Nat} (hs : Scr s base) (hk : VG.Proof.X25519.X86_64.Ifma.Consts s.mem base x1)
    (hy : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s 0 l i < 2 ^ 61) :
    WP isa (.block (stage1 ++ mul4 OPL)) s fun s' => VG.Proof.X25519.X86_64.Ifma.Kept base s s' ∧
      (∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s' 0 l i < 2 ^ 61) ∧
      VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s' 0 0) = (VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 0) + VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 1)) * (VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 0) + VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 1)) ∧
      VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s' 0 1) = (VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 0) - VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 1)) * (VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 0) - VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 1)) ∧
      VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s' 0 2) = (VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 2) - VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 3)) * (VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 0) + VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 1)) ∧
      VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s' 0 3) = (VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 2) + VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 3)) * (VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 0) - VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 1)) := by
  have hr := hs.rdi
  simp only [stage1, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.s1a_wp hr (VG.Proof.X25519.X86_64.Ifma.scr_ctx hs) hk hy) fun s₁ ⟨v₁, m₁, u₁, _⟩ => ?_
  have hs₁ := VG.Proof.X25519.X86_64.Ifma.scr_of hs (VG.Proof.X25519.X86_64.Ifma.vm_gpr v₁) (VG.Proof.X25519.X86_64.Ifma.vm_wr v₁)
  have hk₁ : VG.Proof.X25519.X86_64.Ifma.Consts s₁.mem base x1 := by rw [m₁]; exact hk
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.carryI_wp hs₁.rdi (VG.Proof.X25519.X86_64.Ifma.scr_ctx hs₁) hk₁.c fun l hl i hi => (u₁ l hl i hi).2) fun s₂ ⟨v₂, m₂, u₂, _⟩ => ?_
  have hs₂ := VG.Proof.X25519.X86_64.Ifma.scr_of hs₁ (VG.Proof.X25519.X86_64.Ifma.vm_gpr v₂) (VG.Proof.X25519.X86_64.Ifma.vm_wr v₂)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.s1b_wp hs₂.rdi (VG.Proof.X25519.X86_64.Ifma.scr_ctx hs₂)) fun s₃ ⟨g₃, r₃, w₃, o₃, u₃, _⟩ => ?_
  have hs₃ := VG.Proof.X25519.X86_64.Ifma.scr_of hs₂ g₃ w₃
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.mul4_wp (a := OPL) (by decide) (VG.Proof.X25519.X86_64.Ifma.mulS_eq _ _) (VG.Proof.X25519.X86_64.Ifma.mulL_nat) VG.Proof.X25519.X86_64.Ifma.mulL_ok VG.Proof.X25519.X86_64.Ifma.mulL_keep VG.Proof.X25519.X86_64.Ifma.mulL_st
    hs₃.rdi (VG.Proof.X25519.X86_64.Ifma.scr_ctx hs₃) (fun l hl i hi => by rw [(u₃ l hl i hi).1]; exact (u₂ _ (VG.Proof.Poly1305.X86_64.Avx2.sel4_lt _ _) i hi).2)
    (fun l hl i hi => by rw [(u₃ l hl i hi).2]; exact (u₂ _ (VG.Proof.Poly1305.X86_64.Avx2.sel4_lt _ _) i hi).2))
    fun s₄ ⟨v₄, m₄, u₄, _⟩ => ?_
  have K : VG.Proof.X25519.X86_64.Ifma.Kept base s s₄ :=
    (((Kept.vm v₁ m₁).trans (Kept.vm v₂ m₂)).trans ⟨g₃, r₃, w₃, o₃.mono (by decide) (by decide)⟩).trans
      (Kept.vm v₄ m₄)
  -- the values of the lanes
  have fU : ∀ l < 4, VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s₂ 0 l) = VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.sumDiff (VG.Proof.X25519.X86_64.Ifma.lanes s 0) l i) := fun l hl => by
    rw [VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => (u₂ l hl i hi).1), VG.Proof.X25519.X86_64.Ifma.fe5_carry _ (by have := (u₁ l hl 4 (by decide)).2; omega)]
    exact VG.Proof.X25519.X86_64.Ifma.fe5_congr fun i hi => (u₁ l hl i hi).1
  have hle : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s 0 l i ≤ VG.Proof.X25519.X86_64.Ifma.kbv i := fun l hl i hi => by
    have := hy l hl i hi; simp only [VG.Proof.X25519.X86_64.Ifma.kbv]; split <;> omega
  have fA : VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.sumDiff (VG.Proof.X25519.X86_64.Ifma.lanes s 0) 0 i) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 0) + VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 1) :=
    VG.Proof.X25519.X86_64.Ifma.fe5_add fun i _ => rfl
  have fB : VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.sumDiff (VG.Proof.X25519.X86_64.Ifma.lanes s 0) 1 i) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 0) - VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 1) :=
    VG.Proof.X25519.X86_64.Ifma.fe5_sub (fun i _ => rfl) (hle 1 (by decide))
  have fC : VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.sumDiff (VG.Proof.X25519.X86_64.Ifma.lanes s 0) 2 i) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 2) + VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 3) :=
    VG.Proof.X25519.X86_64.Ifma.fe5_add fun i _ => rfl
  have fD : VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.sumDiff (VG.Proof.X25519.X86_64.Ifma.lanes s 0) 3 i) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 2) - VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 3) :=
    VG.Proof.X25519.X86_64.Ifma.fe5_sub (fun i _ => rfl) (hle 3 (by decide))
  have fM : ∀ l < 4, VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s₄ 0 l) =
      VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s₂ 0 (sel4 (ord 0 1 3 2).toNat l)) * VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s₂ 0 (sel4 (ord 0 1 0 1).toNat l)) :=
    fun l hl => by
      rw [VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => (u₄ l hl i hi).1),
        VG.Proof.X25519.X86_64.Ifma.fe5_mul (fun i hi => by rw [(u₃ l hl i hi).1]; exact (u₂ _ (VG.Proof.Poly1305.X86_64.Avx2.sel4_lt _ _) i hi).2)
          (fun i hi => by rw [(u₃ l hl i hi).2]; exact (u₂ _ (VG.Proof.Poly1305.X86_64.Avx2.sel4_lt _ _) i hi).2),
        VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => (u₃ l hl i hi).1), VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => (u₃ l hl i hi).2)]
  refine ⟨K, fun l hl i hi => (u₄ l hl i hi).2, ?_, ?_, ?_, ?_⟩
  · rw [fM 0 (by decide), show sel4 (ord 0 1 3 2).toNat 0 = 0 by decide, show sel4 (ord 0 1 0 1).toNat 0 = 0 by decide,
      fU 0 (by decide), fA]
  · rw [fM 1 (by decide), show sel4 (ord 0 1 3 2).toNat 1 = 1 by decide, show sel4 (ord 0 1 0 1).toNat 1 = 1 by decide,
      fU 1 (by decide), fB]
  · rw [fM 2 (by decide), show sel4 (ord 0 1 3 2).toNat 2 = 3 by decide, show sel4 (ord 0 1 0 1).toNat 2 = 0 by decide,
      fU 3 (by decide), fU 0 (by decide), fD, fA]
  · rw [fM 3 (by decide), show sel4 (ord 0 1 3 2).toNat 3 = 2 by decide, show sel4 (ord 0 1 0 1).toNat 3 = 1 by decide,
      fU 2 (by decide), fU 1 (by decide), fC, fB]

end VG.Proof.X25519.X86_64.Ifma

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Ifma.Part2`. -/
section

/-!
# X25519 on x86-64 with AVX512_IFMA: stages 2 and 3 of an iteration

From `(AA, BB, DA, CB)` in the lanes of `ymm0–ymm4`, stage 2 and its product
leave `(x₃', t, x₂', a24 E)` there (and its first operand, with `AA` and `E`,
in `OPV`); stage 3 and its product then leave `(x₂', z₂', x₃', z₃')`.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.X25519.X86_64 (Scr Outside Outside.mono)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

theorem lanes_keep {s s' : State} {r0 : Nat} (h : ∀ r < 16, r0 ≤ r → r < r0 + 5 → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l)
    (hr : r0 + 5 ≤ 16) : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s' r0 l i = VG.Proof.X25519.X86_64.Ifma.lanes s r0 l i := fun l hl i hi => by
  simp only [VG.Proof.X25519.X86_64.Ifma.lanes]; rw [h (r0 + i) (by omega) (by omega) (by omega) l hl]

theorem le_kbv {x : Nat} (i : Nat) (h : x < 2 ^ 61) : x ≤ VG.Proof.X25519.X86_64.Ifma.kbv i := by simp only [VG.Proof.X25519.X86_64.Ifma.kbv]; split <;> omega

/-- Stage 2 and its product. -/
theorem part2_ok {s : State} {base : Addr} {x1 : Nat → Nat} (hs : Scr s base) (hk : VG.Proof.X25519.X86_64.Ifma.Consts s.mem base x1)
    (hy : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s 0 l i < 2 ^ 61) :
    WP isa (.block (stage2 ++ mul4 OPV)) s fun s' => VG.Proof.X25519.X86_64.Ifma.Kept base s s' ∧
      (∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s' 0 l i < 2 ^ 61 ∧ VG.Proof.X25519.X86_64.Ifma.slotv s'.mem base OPV l i < 2 ^ 52) ∧
      VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.slotv s'.mem base OPV 2) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 0) ∧
      VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.slotv s'.mem base OPV 3) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 0) - VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 1) ∧
      VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s' 0 0) = (VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 2) + VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 3)) * (VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 2) + VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 3)) ∧
      VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s' 0 1) = (VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 2) - VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 3)) * (VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 2) - VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 3)) ∧
      VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s' 0 2) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 0) * VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 1) ∧
      VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s' 0 3) = (VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 0) - VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 1)) * Spec.X25519.a24 := by
  have hr := hs.rdi
  simp only [stage2, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.s2a_wp hr (VG.Proof.X25519.X86_64.Ifma.scr_ctx hs) hk hy) fun s₁ ⟨v₁, m₁, u₁, _⟩ => ?_
  have hs₁ := VG.Proof.X25519.X86_64.Ifma.scr_of hs (VG.Proof.X25519.X86_64.Ifma.vm_gpr v₁) (VG.Proof.X25519.X86_64.Ifma.vm_wr v₁)
  have hk₁ : VG.Proof.X25519.X86_64.Ifma.Consts s₁.mem base x1 := by rw [m₁]; exact hk
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.carryF_wp hs₁.rdi (VG.Proof.X25519.X86_64.Ifma.scr_ctx hs₁) hk₁.c fun l hl i hi => (u₁ l hl i hi).2.1)
    fun s₂ ⟨v₂, m₂, u₂, k₂⟩ => ?_
  have hs₂ := VG.Proof.X25519.X86_64.Ifma.scr_of hs₁ (VG.Proof.X25519.X86_64.Ifma.vm_gpr v₂) (VG.Proof.X25519.X86_64.Ifma.vm_wr v₂)
  have hk₂ : VG.Proof.X25519.X86_64.Ifma.Consts s₂.mem base x1 := by rw [m₂]; exact hk₁
  have e₂ := VG.Proof.X25519.X86_64.Ifma.lanes_keep (s := s₁) (s' := s₂) (r0 := 0) (fun r hr h1 h2 l hl => k₂ r hr (by omega) (by omega) l hl)
    (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.carryI_wp hs₂.rdi (VG.Proof.X25519.X86_64.Ifma.scr_ctx hs₂) hk₂.c fun l hl i hi => by
      rw [e₂ l hl i hi]; exact (u₁ l hl i hi).2.2.2)
    fun s₃ ⟨v₃, m₃, u₃, k₃⟩ => ?_
  have hs₃ := VG.Proof.X25519.X86_64.Ifma.scr_of hs₂ (VG.Proof.X25519.X86_64.Ifma.vm_gpr v₃) (VG.Proof.X25519.X86_64.Ifma.vm_wr v₃)
  have e₃ := VG.Proof.X25519.X86_64.Ifma.lanes_keep (s := s₂) (s' := s₃) (r0 := 5) (fun r hr h1 h2 l hl => k₃ r hr (by omega) (by omega) l hl)
    (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.s2b_wp hs₃.rdi (VG.Proof.X25519.X86_64.Ifma.scr_ctx hs₃)) fun s₄ ⟨g₄, r₄, w₄, o₄, u₄, _⟩ => ?_
  have hs₄ := VG.Proof.X25519.X86_64.Ifma.scr_of hs₃ g₄ w₄
  have b5 : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s₃ 5 l i < 2 ^ 52 := fun l hl i hi => by
    rw [e₃ l hl i hi]; exact (u₂ l hl i hi).2
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.mul4_wp (a := OPV) (by decide) (VG.Proof.X25519.X86_64.Ifma.mulS_eq _ _) (VG.Proof.X25519.X86_64.Ifma.mulV_nat) VG.Proof.X25519.X86_64.Ifma.mulV_ok VG.Proof.X25519.X86_64.Ifma.mulV_keep VG.Proof.X25519.X86_64.Ifma.mulV_st
    hs₄.rdi (VG.Proof.X25519.X86_64.Ifma.scr_ctx hs₄) (fun l hl i hi => by rw [(u₄ l hl i hi).1]; exact b5 l hl i hi)
    (fun l hl i hi => by rw [(u₄ l hl i hi).2]; exact (u₃ l hl i hi).2))
    fun s₅ ⟨v₅, m₅, u₅, _⟩ => ?_
  have K : VG.Proof.X25519.X86_64.Ifma.Kept base s s₅ :=
    ((((Kept.vm v₁ m₁).trans (Kept.vm v₂ m₂)).trans (Kept.vm v₃ m₃)).trans
      ⟨g₄, r₄, w₄, o₄.mono (by decide) (by decide)⟩).trans (Kept.vm v₅ m₅)
  -- the operands
  have fV : ∀ l < 4, VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.slotv s₅.mem base OPV l) = VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.opV (VG.Proof.X25519.X86_64.Ifma.lanes s 0) l i) := fun l hl => by
    rw [m₅, VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => (u₄ l hl i hi).1), VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => e₃ l hl i hi),
      VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => (u₂ l hl i hi).1), VG.Proof.X25519.X86_64.Ifma.fe5_carry _ (by have := (u₁ l hl 4 (by decide)).2.1; omega)]
    exact VG.Proof.X25519.X86_64.Ifma.fe5_congr fun i hi => (u₁ l hl i hi).1
  have fW : ∀ l < 4, VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s₄ 5 l) = VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.opW (VG.Proof.X25519.X86_64.Ifma.lanes s 0) l i) := fun l hl => by
    rw [VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => (u₄ l hl i hi).2), VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => (u₃ l hl i hi).1),
      VG.Proof.X25519.X86_64.Ifma.fe5_carry _ (by rw [e₂ l hl 4 (by decide)]; have := (u₁ l hl 4 (by decide)).2.2.2; omega)]
    exact VG.Proof.X25519.X86_64.Ifma.fe5_congr fun i hi => by rw [e₂ l hl i hi]; exact (u₁ l hl i hi).2.2.1
  have fM : ∀ l < 4, VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s₅ 0 l) = VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.opV (VG.Proof.X25519.X86_64.Ifma.lanes s 0) l i) * VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.opW (VG.Proof.X25519.X86_64.Ifma.lanes s 0) l i) :=
    fun l hl => by
      rw [VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => (u₅ l hl i hi).1),
        VG.Proof.X25519.X86_64.Ifma.fe5_mul (fun i hi => by rw [(u₄ l hl i hi).1]; exact b5 l hl i hi)
          (fun i hi => by rw [(u₄ l hl i hi).2]; exact (u₃ l hl i hi).2), ← m₅, fV l hl, fW l hl]
  have f0 : VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.opV (VG.Proof.X25519.X86_64.Ifma.lanes s 0) 0 i) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 2) + VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 3) := VG.Proof.X25519.X86_64.Ifma.fe5_add fun _ _ => rfl
  have f1 : VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.opV (VG.Proof.X25519.X86_64.Ifma.lanes s 0) 1 i) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 2) - VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 3) :=
    VG.Proof.X25519.X86_64.Ifma.fe5_sub (fun _ _ => rfl) (fun i hi => VG.Proof.X25519.X86_64.Ifma.le_kbv i (hy 3 (by decide) i hi))
  have f2 : VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.opV (VG.Proof.X25519.X86_64.Ifma.lanes s 0) 2 i) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 0) := VG.Proof.X25519.X86_64.Ifma.fe5_congr fun _ _ => rfl
  have f3 : VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.opV (VG.Proof.X25519.X86_64.Ifma.lanes s 0) 3 i) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 0) - VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 1) :=
    VG.Proof.X25519.X86_64.Ifma.fe5_sub (fun _ _ => rfl) (fun i hi => VG.Proof.X25519.X86_64.Ifma.le_kbv i (hy 1 (by decide) i hi))
  have g0 : VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.opW (VG.Proof.X25519.X86_64.Ifma.lanes s 0) 0 i) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 2) + VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 3) := VG.Proof.X25519.X86_64.Ifma.fe5_add fun _ _ => rfl
  have g1 : VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.opW (VG.Proof.X25519.X86_64.Ifma.lanes s 0) 1 i) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 2) - VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 3) :=
    VG.Proof.X25519.X86_64.Ifma.fe5_sub (fun _ _ => rfl) (fun i hi => VG.Proof.X25519.X86_64.Ifma.le_kbv i (hy 3 (by decide) i hi))
  have g2 : VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.opW (VG.Proof.X25519.X86_64.Ifma.lanes s 0) 2 i) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 1) := VG.Proof.X25519.X86_64.Ifma.fe5_congr fun _ _ => rfl
  have g3 : VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.opW (VG.Proof.X25519.X86_64.Ifma.lanes s 0) 3 i) = Spec.X25519.a24 := VG.Proof.X25519.X86_64.Ifma.fe5_a24
  refine ⟨K, fun l hl i hi => ⟨(u₅ l hl i hi).2, by rw [m₅, (u₄ l hl i hi).1]; exact b5 l hl i hi⟩,
    by rw [fV 2 (by decide), f2], by rw [fV 3 (by decide), f3],
    by rw [fM 0 (by decide), f0, g0], by rw [fM 1 (by decide), f1, g1],
    by rw [fM 2 (by decide), f2, g2], by rw [fM 3 (by decide), f3, g3]⟩

/-- Stage 3 and its product, with stage 2's first operand at `OPV`. -/
theorem part3_ok {s : State} {base : Addr} {x1 : Nat → Nat} (hs : Scr s base) (hk : VG.Proof.X25519.X86_64.Ifma.Consts s.mem base x1)
    (hy : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s 0 l i < 2 ^ 61 ∧ VG.Proof.X25519.X86_64.Ifma.slotv s.mem base OPV l i < 2 ^ 52) :
    WP isa (.block (stage3 ++ mul4 OPG)) s fun s' => VG.Proof.X25519.X86_64.Ifma.Kept base s s' ∧
      (∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s' 0 l i < 2 ^ 61) ∧
      VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s' 0 0) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 2) * 1 ∧
      VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s' 0 1) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.slotv s.mem base OPV 3) * (VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.slotv s.mem base OPV 2) + VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 3)) ∧
      VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s' 0 2) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 0) * 1 ∧
      VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s' 0 3) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 1) * VG.Proof.X25519.X86_64.Ifma.fe5 x1 := by
  have hr := hs.rdi
  simp only [stage3, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.s3a_wp hr (VG.Proof.X25519.X86_64.Ifma.scr_ctx hs) hk (fun l hl i hi => (hy l hl i hi).1) (fun l hl i hi => (hy l hl i hi).2))
    fun s₁ ⟨v₁, m₁, u₁, _⟩ => ?_
  have hs₁ := VG.Proof.X25519.X86_64.Ifma.scr_of hs (VG.Proof.X25519.X86_64.Ifma.vm_gpr v₁) (VG.Proof.X25519.X86_64.Ifma.vm_wr v₁)
  have hk₁ : VG.Proof.X25519.X86_64.Ifma.Consts s₁.mem base x1 := by rw [m₁]; exact hk
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.carryF_wp hs₁.rdi (VG.Proof.X25519.X86_64.Ifma.scr_ctx hs₁) hk₁.c fun l hl i hi => (u₁ l hl i hi).2.1)
    fun s₂ ⟨v₂, m₂, u₂, k₂⟩ => ?_
  have hs₂ := VG.Proof.X25519.X86_64.Ifma.scr_of hs₁ (VG.Proof.X25519.X86_64.Ifma.vm_gpr v₂) (VG.Proof.X25519.X86_64.Ifma.vm_wr v₂)
  have hk₂ : VG.Proof.X25519.X86_64.Ifma.Consts s₂.mem base x1 := by rw [m₂]; exact hk₁
  have e₂ := VG.Proof.X25519.X86_64.Ifma.lanes_keep (s := s₁) (s' := s₂) (r0 := 0) (fun r hr h1 h2 l hl => k₂ r hr (by omega) (by omega) l hl)
    (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.carryI_wp hs₂.rdi (VG.Proof.X25519.X86_64.Ifma.scr_ctx hs₂) hk₂.c fun l hl i hi => by
      rw [e₂ l hl i hi]; exact (u₁ l hl i hi).2.2.2)
    fun s₃ ⟨v₃, m₃, u₃, k₃⟩ => ?_
  have hs₃ := VG.Proof.X25519.X86_64.Ifma.scr_of hs₂ (VG.Proof.X25519.X86_64.Ifma.vm_gpr v₃) (VG.Proof.X25519.X86_64.Ifma.vm_wr v₃)
  have e₃ := VG.Proof.X25519.X86_64.Ifma.lanes_keep (s := s₂) (s' := s₃) (r0 := 5) (fun r hr h1 h2 l hl => k₃ r hr (by omega) (by omega) l hl)
    (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.s3b_wp hs₃.rdi (VG.Proof.X25519.X86_64.Ifma.scr_ctx hs₃)) fun s₄ ⟨v₄, o₄, u₄, k₄⟩ => ?_
  have hs₄ := VG.Proof.X25519.X86_64.Ifma.scr_of hs₃ (VG.Proof.X25519.X86_64.Ifma.vm_gpr v₄) (VG.Proof.X25519.X86_64.Ifma.vm_wr v₄)
  have e₄ := VG.Proof.X25519.X86_64.Ifma.lanes_keep (s := s₃) (s' := s₄) (r0 := 5) (fun r hr _ _ l hl => k₄ r hr l hl) (by decide)
  have b5 : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s₄ 5 l i < 2 ^ 52 := fun l hl i hi => by
    rw [e₄ l hl i hi, e₃ l hl i hi]; exact (u₂ l hl i hi).2
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.mul4_wp (a := OPG) (by decide) (VG.Proof.X25519.X86_64.Ifma.mulS_eq _ _) (VG.Proof.X25519.X86_64.Ifma.mulG_nat) VG.Proof.X25519.X86_64.Ifma.mulG_ok VG.Proof.X25519.X86_64.Ifma.mulG_keep VG.Proof.X25519.X86_64.Ifma.mulG_st
    hs₄.rdi (VG.Proof.X25519.X86_64.Ifma.scr_ctx hs₄) (fun l hl i hi => by rw [u₄ l hl i hi]; exact (u₃ l hl i hi).2) b5)
    fun s₅ ⟨v₅, m₅, u₅, _⟩ => ?_
  have K : VG.Proof.X25519.X86_64.Ifma.Kept base s s₅ :=
    ((((Kept.vm v₁ m₁).trans (Kept.vm v₂ m₂)).trans (Kept.vm v₃ m₃)).trans
      ⟨VG.Proof.X25519.X86_64.Ifma.vm_gpr v₄, VG.Proof.X25519.X86_64.Ifma.vm_rd v₄, VG.Proof.X25519.X86_64.Ifma.vm_wr v₄, o₄.mono (by decide) (by decide)⟩).trans (Kept.vm v₅ m₅)
  have fG : ∀ l < 4, VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.slotv s₄.mem base OPG l) = VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.opG (VG.Proof.X25519.X86_64.Ifma.lanes s 0) (VG.Proof.X25519.X86_64.Ifma.slotv s.mem base OPV) l i) :=
    fun l hl => by
      rw [VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => u₄ l hl i hi), VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => (u₃ l hl i hi).1),
        VG.Proof.X25519.X86_64.Ifma.fe5_carry _ (by rw [e₂ l hl 4 (by decide)]; have := (u₁ l hl 4 (by decide)).2.2.2; omega)]
      exact VG.Proof.X25519.X86_64.Ifma.fe5_congr fun i hi => by rw [e₂ l hl i hi]; exact (u₁ l hl i hi).2.2.1
  have fH : ∀ l < 4, VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s₄ 5 l) = VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.opH x1 (VG.Proof.X25519.X86_64.Ifma.lanes s 0) (VG.Proof.X25519.X86_64.Ifma.slotv s.mem base OPV) l i) :=
    fun l hl => by
      rw [VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => e₄ l hl i hi), VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => e₃ l hl i hi),
        VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => (u₂ l hl i hi).1), VG.Proof.X25519.X86_64.Ifma.fe5_carry _ (by have := (u₁ l hl 4 (by decide)).2.1; omega)]
      exact VG.Proof.X25519.X86_64.Ifma.fe5_congr fun i hi => (u₁ l hl i hi).1
  have fM : ∀ l < 4, VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s₅ 0 l) = VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.opG (VG.Proof.X25519.X86_64.Ifma.lanes s 0) (VG.Proof.X25519.X86_64.Ifma.slotv s.mem base OPV) l i) *
      VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => VG.Proof.X25519.X86_64.Ifma.opH x1 (VG.Proof.X25519.X86_64.Ifma.lanes s 0) (VG.Proof.X25519.X86_64.Ifma.slotv s.mem base OPV) l i) := fun l hl => by
    rw [VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => (u₅ l hl i hi).1),
      VG.Proof.X25519.X86_64.Ifma.fe5_mul (fun i hi => by rw [u₄ l hl i hi]; exact (u₃ l hl i hi).2) (b5 l hl), fG l hl, fH l hl]
  have h1 : VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => if i = 0 then 1 else 0) = 1 := VG.Proof.X25519.X86_64.Ifma.fe5_one
  refine ⟨K, fun l hl i hi => (u₅ l hl i hi).2, ?_, ?_, ?_, ?_⟩
  · rw [fM 0 (by decide)]; exact congrArg₂ _ (VG.Proof.X25519.X86_64.Ifma.fe5_congr fun _ _ => rfl) h1
  · rw [fM 1 (by decide)]
    exact congrArg₂ _ (VG.Proof.X25519.X86_64.Ifma.fe5_congr fun _ _ => rfl) (VG.Proof.X25519.X86_64.Ifma.fe5_add fun _ _ => rfl)
  · rw [fM 2 (by decide)]; exact congrArg₂ _ (VG.Proof.X25519.X86_64.Ifma.fe5_congr fun _ _ => rfl) h1
  · rw [fM 3 (by decide)]; exact congrArg₂ _ (VG.Proof.X25519.X86_64.Ifma.fe5_congr fun _ _ => rfl) (VG.Proof.X25519.X86_64.Ifma.fe5_congr fun _ _ => rfl)

end VG.Proof.X25519.X86_64.Ifma

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Ifma.Step`. -/
section

/-!
# X25519 on x86-64 with AVX512_IFMA: the ladder's loop

The loop invariant (`VInv`): the counter `rbx` counts down to `n`, the lanes
of `ymm0–ymm4` hold the ladder's `(x₂, z₂, x₃, z₃)` after the bits 254 down to
`n`, and `swap` its `swap`; since the loop's start only the registers `rax`,
`rbx`, `rcx`, `rdx`, the vector registers, `swap` and the operand slots
changed.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.X25519.X86_64 (Scr Outside Outside.mono ofs off word stepPre stepPre_ok mask
  contains_sc ofs_off' cswap_fst cswap_snd writeW_outside)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

/-- The bytes an iteration may change: `swap` and the operand slots. -/
def VFrame (base : Addr) (m m' : Mem) : Prop :=
  ∀ x, (ofs base x < 640 ∨ (648 ≤ ofs base x ∧ ofs base x < 1024) ∨ 1504 ≤ ofs base x) → m' x = m x

theorem VFrame.refl (base : Addr) (m : Mem) : VG.Proof.X25519.X86_64.Ifma.VFrame base m m := fun _ _ => rfl

theorem VFrame.trans {base : Addr} {m₁ m₂ m₃ : Mem} (h₁ : VG.Proof.X25519.X86_64.Ifma.VFrame base m₁ m₂) (h₂ : VG.Proof.X25519.X86_64.Ifma.VFrame base m₂ m₃) :
    VG.Proof.X25519.X86_64.Ifma.VFrame base m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem VFrame.of_slots {base : Addr} {m m' : Mem} (h : Outside base 1024 480 m m') : VG.Proof.X25519.X86_64.Ifma.VFrame base m m' :=
  fun x hx => h x (by omega)

theorem VFrame.of_swap {base : Addr} {m m' : Mem} (h : Outside base 640 8 m m') : VG.Proof.X25519.X86_64.Ifma.VFrame base m m' :=
  fun x hx => h x (by omega)

theorem Consts.of_word {m m' : Mem} {base : Addr} {x1 : Nat → Nat} (hk : VG.Proof.X25519.X86_64.Ifma.Consts m base x1)
    (w : ∀ d, 1504 ≤ d → d + 8 ≤ 2208 → VG.Proof.X25519.X86_64.Ifma.mq m' base d = VG.Proof.X25519.X86_64.Ifma.mq m base d) : VG.Proof.X25519.X86_64.Ifma.Consts m' base x1 := by
  refine ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun i hi l hl => ?_,
    fun i hi l hl => ?_, hk.x1, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩
  · rw [w _ (by simp only [KM]; omega) (by simp only [KM]; omega)]; exact hk.km l hl
  · rw [w _ (by simp only [K19]; omega) (by simp only [K19]; omega)]; exact hk.k19 l hl
  · rw [w _ (by simp only [KB0]; omega) (by simp only [KB0]; omega)]; exact hk.kb0 l hl
  · rw [w _ (by simp only [KB1]; omega) (by simp only [KB1]; omega)]; exact hk.kb1 l hl
  · rw [VG.Proof.X25519.X86_64.Ifma.slotv, w _ (by simp only [KA24]; omega) (by simp only [KA24]; omega)]; exact hk.a24 i hi l hl
  · rw [VG.Proof.X25519.X86_64.Ifma.slotv, w _ (by simp only [KX1]; omega) (by simp only [KX1]; omega)]; exact hk.kx1 i hi l hl
  · rw [w _ (by simp only [K13]; omega) (by simp only [K13]; omega)]; exact hk.k13 l hl
  · rw [w _ (by simp only [K26]; omega) (by simp only [K26]; omega)]; exact hk.k26 l hl
  · rw [w _ (by simp only [K39]; omega) (by simp only [K39]; omega)]; exact hk.k39 l hl

theorem Consts.of_frame {m m' : Mem} {base : Addr} {x1 : Nat → Nat} (hk : VG.Proof.X25519.X86_64.Ifma.Consts m base x1)
    (h : VG.Proof.X25519.X86_64.Ifma.VFrame base m m') : VG.Proof.X25519.X86_64.Ifma.Consts m' base x1 :=
  hk.of_word fun d h1 h2 => by
    rw [VG.Proof.X25519.X86_64.Ifma.mq_eq_word, VG.Proof.X25519.X86_64.Ifma.mq_eq_word]
    exact (Mem.readW_congr fun i hi => (h _ (by
      right; right; rw [VG.Proof.X25519.X86_64.ofs_off base (by omega)]; omega)).symm).symm

/-- The loop invariant, with the counter `rbx = n`. -/
structure VInv (base : Addr) (k : Nat) (u : Fe) (x1 : Nat → Nat) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  gpr : ∀ r, r ∉ [.rax, .rbx, .rcx, .rdx] → s.gpr r = s₀.gpr r
  rbx : s.gpr .rbx = BitVec.ofNat 64 n
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : VG.Proof.X25519.X86_64.Ifma.VFrame base s₀.mem s.mem
  consts : VG.Proof.X25519.X86_64.Ifma.Consts s.mem base x1
  hx1 : VG.Proof.X25519.X86_64.Ifma.fe5 x1 = u
  swap : word s.mem base SWAP = BitVec.ofNat 64 (ladderAfter k u n).swap
  lim : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s 0 l i < 2 ^ 61
  x2 : VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 0) = (ladderAfter k u n).x2
  z2 : VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 1) = (ladderAfter k u n).z2
  x3 : VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 2) = (ladderAfter k u n).x3
  z3 : VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 3) = (ladderAfter k u n).z3

theorem vstep_eq : vstep = stepPre ++ (VG.Proof.X25519.X86_64.Ifma.vsw ++ ((stage1 ++ mul4 OPL) ++ ((stage2 ++ mul4 OPV) ++
    ((stage3 ++ mul4 OPG) ++ ([.alu .test .rbx (.reg .rbx)] : List Instr))))) := by
  simp only [vstep, stepPre, VG.Proof.X25519.X86_64.Ifma.vsw, List.append_assoc, List.cons_append, List.nil_append]

theorem lanes_of_vec {s s' : State} (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi) (r l i : Nat) :
    VG.Proof.X25519.X86_64.Ifma.lanes s' r l i = VG.Proof.X25519.X86_64.Ifma.lanes s r l i := by
  simp only [VG.Proof.X25519.X86_64.Ifma.lanes, qw, State.lane, hx, hy]

theorem xor2_lt : ∀ l < 4, l ^^^ 2 < 4 := by decide

/-- One iteration: from the state after the bits down to `n + 1` to the state
after the bits down to `n`. -/
theorem vstep_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Fe} {x1 : Nat → Nat} {n : Nat} (hn : n < 255)
    (hbits : ∀ t < 255, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t))
    (hi : VG.Proof.X25519.X86_64.Ifma.VInv base k u x1 s₀ s (n + 1)) :
    WP isa (.block vstep) s fun s' => VG.Proof.X25519.X86_64.Ifma.VInv base k u x1 s₀ s' n ∧ s'.zf = some (decide (n = 0)) := by
  have hs := hi.scr
  have hbit : s.mem (off base (BITS + n)) = BitVec.ofNat 8 (bit k n) := by
    rw [hi.mem _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)]
    exact hbits n hn
  have hsw := ladderAfter_swap_le k u (n := n + 1) (by omega)
  rw [VG.Proof.X25519.X86_64.Ifma.vstep_eq, WP.block_append_iff]
  refine WP.mono (stepPre_ok hs hn hi.rbx (by have := bit_le k n; omega) (by omega) hbit hi.swap)
    fun s₁ ⟨b₁, m₁, g₁, rd₁, wr₁, mem₁, x₁, y₁⟩ => ?_
  have hs₁ : Scr s₁ base := ⟨(g₁ _ (by decide)).trans hs.rdi, wr₁ ▸ hs.wr, hs.nowrap⟩
  have o₁ : Outside base 640 8 s.mem s₁.mem := by
    rw [mem₁]; exact writeW_outside _ _ _ (by omega)
  have hk₁ := hi.consts.of_frame (VFrame.of_swap o₁)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.vsw_wp (VG.Proof.X25519.X86_64.Ifma.scr_ctx hs₁) m₁) fun s₂ ⟨v₂, mm₂, u₂, _⟩ => ?_
  have hs₂ := VG.Proof.X25519.X86_64.Ifma.scr_of hs₁ (VG.Proof.X25519.X86_64.Ifma.vm_gpr v₂) (VG.Proof.X25519.X86_64.Ifma.vm_wr v₂)
  have hk₂ : VG.Proof.X25519.X86_64.Ifma.Consts s₂.mem base x1 := by rw [mm₂]; exact hk₁
  -- the swapped lanes
  have sw₂ : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s₂ 0 l i =
      VG.Proof.X25519.X86_64.Ifma.lanes s 0 (if decide ((ladderAfter k u (n + 1)).swap ^^^ bit k n = 1) then l ^^^ 2 else l) i :=
    fun l hl i hi' => by
      simp only [VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add] at *
      rw [u₂ l hl i hi']
      exact congrArg _ (by simp only [qw, State.lane, x₁, y₁])
  have lim₂ : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s₂ 0 l i < 2 ^ 61 := fun l hl i hi' => by
    rw [sw₂ l hl i hi']; exact hi.lim _ (by split <;> [exact xor2_lt l hl; exact hl]) i hi'
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.part1_ok hs₂ hk₂ lim₂) fun s₃ ⟨K₃, lim₃, a₃, b₃, c₃, d₃⟩ => ?_
  have hs₃ := VG.Proof.X25519.X86_64.Ifma.scr_of hs₂ K₃.gpr K₃.wr
  have hk₃ := hk₂.of_frame (VFrame.of_slots K₃.mem)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.part2_ok hs₃ hk₃ lim₃) fun s₄ ⟨K₄, lim₄, v2₄, v3₄, a₄, b₄, c₄, d₄⟩ => ?_
  have hs₄ := VG.Proof.X25519.X86_64.Ifma.scr_of hs₃ K₄.gpr K₄.wr
  have hk₄ := hk₃.of_frame (VFrame.of_slots K₄.mem)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.part3_ok hs₄ hk₄ lim₄) fun s₅ ⟨K₅, lim₅, a₅, b₅, c₅, d₅⟩ => ?_
  have hs₅ := VG.Proof.X25519.X86_64.Ifma.scr_of hs₄ K₅.gpr K₅.wr
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  have rbx₅ : s₅.gpr .rbx = BitVec.ofNat 64 n := by rw [K₅.gpr, K₄.gpr, K₃.gpr, VG.Proof.X25519.X86_64.Ifma.vm_gpr v₂, b₁]
  have zf : (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == 0) = decide (n = 0) := by
    rw [BitVec.and_self]
    rcases Nat.eq_zero_or_pos n with rfl | h
    · rfl
    · rw [decide_eq_false (by omega)]
      apply beq_false_of_ne
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact absurd this (by simp; omega)
  -- the field elements
  have fsw : ∀ l < 4, VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s₂ 0 l) =
      VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 (if decide ((ladderAfter k u (n + 1)).swap ^^^ bit k n = 1) then l ^^^ 2 else l)) :=
    fun l hl => VG.Proof.X25519.X86_64.Ifma.fe5_congr fun i hi' => sw₂ l hl i hi'
  have L := ladderAfter_step k u hn
  have F : VG.Proof.X25519.X86_64.Ifma.VFrame base s.mem s₅.mem :=
    (((VFrame.of_swap o₁).trans (by rw [mm₂]; exact VFrame.refl _ _)).trans
      (VFrame.of_slots K₃.mem)).trans ((VFrame.of_slots K₄.mem).trans (VFrame.of_slots K₅.mem))
  have hl5 : ∀ l, VG.Proof.X25519.X86_64.Ifma.lanes (arithFlags s₅ (s₅.gpr .rbx &&& s₅.gpr .rbx) false false) 0 l = VG.Proof.X25519.X86_64.Ifma.lanes s₅ 0 l :=
    fun l => funext fun i => VG.Proof.X25519.X86_64.Ifma.lanes_of_vec rfl rfl 0 l i
  have hsw0 : VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s₂ 0 0) = (cswap ((ladderAfter k u (n + 1)).swap ^^^ bit k n)
      (ladderAfter k u (n + 1)).x2 (ladderAfter k u (n + 1)).x3).1 := by
    rw [fsw 0 (by decide), cswap_fst]; split <;> simp only [show (0 : Nat) ^^^ 2 = 2 by decide, hi.x2, hi.x3]
  have hsw1 : VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s₂ 0 1) = (cswap ((ladderAfter k u (n + 1)).swap ^^^ bit k n)
      (ladderAfter k u (n + 1)).z2 (ladderAfter k u (n + 1)).z3).1 := by
    rw [fsw 1 (by decide), cswap_fst]; split <;> simp only [show (1 : Nat) ^^^ 2 = 3 by decide, hi.z2, hi.z3]
  have hsw2 : VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s₂ 0 2) = (cswap ((ladderAfter k u (n + 1)).swap ^^^ bit k n)
      (ladderAfter k u (n + 1)).x2 (ladderAfter k u (n + 1)).x3).2 := by
    rw [fsw 2 (by decide), cswap_snd]; split <;> simp only [show (2 : Nat) ^^^ 2 = 0 by decide, hi.x2, hi.x3]
  have hsw3 : VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s₂ 0 3) = (cswap ((ladderAfter k u (n + 1)).swap ^^^ bit k n)
      (ladderAfter k u (n + 1)).z2 (ladderAfter k u (n + 1)).z3).2 := by
    rw [fsw 3 (by decide), cswap_snd]; split <;> simp only [show (3 : Nat) ^^^ 2 = 1 by decide, hi.z2, hi.z3]
  refine ⟨⟨⟨by rw [RegUpd.gpr_arithFlags]; exact hs₅.rdi, by rw [RegUpd.wr_arithFlags]; exact hs₅.wr,
    hs₅.nowrap⟩, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, hi.hx1, ?_, lim₅, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [RegUpd.gpr_arithFlags, K₅.gpr, K₄.gpr, K₃.gpr, VG.Proof.X25519.X86_64.Ifma.vm_gpr v₂,
      g₁ r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind), hi.gpr r hr]
  · rw [RegUpd.gpr_arithFlags, rbx₅]
  · rw [RegUpd.rd_arithFlags, K₅.rd, K₄.rd, K₃.rd, VG.Proof.X25519.X86_64.Ifma.vm_rd v₂, rd₁, hi.rd]
  · rw [RegUpd.wr_arithFlags, K₅.wr, K₄.wr, K₃.wr, VG.Proof.X25519.X86_64.Ifma.vm_wr v₂, wr₁, hi.wr]
  · rw [RegUpd.mem_arithFlags]; exact hi.mem.trans F
  · rw [RegUpd.mem_arithFlags]; exact hk₄.of_frame (VFrame.of_slots K₅.mem)
  · rw [RegUpd.mem_arithFlags]
    have w₁ : word s₅.mem base SWAP = word s₁.mem base SWAP := by
      have O : Outside base 1024 480 s₂.mem s₅.mem := (K₃.mem.trans K₄.mem).trans K₅.mem
      rw [O.word (by simp only [SWAP]; omega) (by simp only [SWAP]; omega), mm₂]
    rw [w₁, mem₁, L]
    simp only [VG.Proof.X25519.X86_64.word, Mem.readW_writeW_self64]
    rfl
  -- the ladder's formulas
  all_goals try rw [RegUpd.zf_arithFlags, rbx₅, zf]
  all_goals try simp only [hl5]
  all_goals rw [L, ladderStep_eq]
  all_goals simp only []
  · rw [a₅, c₄, a₃, b₃, hsw0, hsw1, Fin.mul_one]
  · rw [b₅, v3₄, v2₄, d₄, a₃, b₃, hsw0, hsw1, Fin.mul_comm _ Spec.X25519.a24]
  · rw [c₅, a₄, c₃, d₃, hsw0, hsw1, hsw2, hsw3, Fin.mul_one]
  · rw [d₅, b₄, c₃, d₃, hsw0, hsw1, hsw2, hsw3, hi.hx1, Fin.mul_comm _ u]

end VG.Proof.X25519.X86_64.Ifma

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Ifma.Finish`. -/
section

/-!
# X25519 on x86-64 with AVX512_IFMA: after the loop

`vfinish` carries the lanes twice, then from the lowest limb up, and stores
each lane as four 64-bit words: the same number modulo `p`, below `2²⁵⁶`.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.X25519.X86_64 (Scr Outside Outside.mono ofs off word val4 F E)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

/-! ## Numbers -/

/-- The limbs from the lowest up, each but the top one's bits from 51 up
passed to the next (`pre`), and masked (`cur`). -/
def pre (x : Nat → Nat) : Nat → Nat
  | 0 => x 0
  | 1 => x 1 + x 0 / 2 ^ 51
  | 2 => x 2 + (x 1 + x 0 / 2 ^ 51) / 2 ^ 51
  | 3 => x 3 + (x 2 + (x 1 + x 0 / 2 ^ 51) / 2 ^ 51) / 2 ^ 51
  | _ => x 4 + (x 3 + (x 2 + (x 1 + x 0 / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51

/-- The four words of a lane, with the masks `m`, `m13`, `m26`, `m39`. -/
def packW (x : Nat → Nat) (m m13 m26 m39 : Nat) : Nat → Nat
  | 0 => (VG.Proof.X25519.X86_64.Ifma.pre x 0 &&& m) ||| (VG.Proof.X25519.X86_64.Ifma.pre x 1 &&& m &&& m13) * 2 ^ 51
  | 1 => (VG.Proof.X25519.X86_64.Ifma.pre x 1 &&& m) / 2 ^ 13 ||| (VG.Proof.X25519.X86_64.Ifma.pre x 2 &&& m &&& m26) * 2 ^ 38
  | 2 => (VG.Proof.X25519.X86_64.Ifma.pre x 2 &&& m) / 2 ^ 26 ||| (VG.Proof.X25519.X86_64.Ifma.pre x 3 &&& m &&& m39) * 2 ^ 25
  | _ => (VG.Proof.X25519.X86_64.Ifma.pre x 3 &&& m) / 2 ^ 39 ||| pre x 4 * 2 ^ 12

def packS : VG.Proof.X25519.X86_64.Ifma.Sym := VG.Proof.X25519.X86_64.Ifma.symOf vpack

theorem packS_st : packS.st.map Prod.fst = [Z3, X3, Z2, X2] := by decide +kernel

/-- The term stored at `X2 + 32 m`. -/
def packT (m : Nat) : VG.Proof.X25519.X86_64.Ifma.T := ((packS.st.reverse).getD m (0, .zero)).2

theorem packT_mem : ∀ m < 4, (X2 + 32 * m, VG.Proof.X25519.X86_64.Ifma.packT m) ∈ packS.st := by decide +kernel

theorem packT_nat (E : VG.Proof.X25519.X86_64.Ifma.Env) : ∀ m < 4, ∀ j < 4, (VG.Proof.X25519.X86_64.Ifma.packT m).nat E j =
    VG.Proof.X25519.X86_64.Ifma.packW (fun i => E.v i m) (E.m KM m) (E.m K13 m) (E.m K26 m) (E.m K39 m) j := by
  intro m hm j hj
  rcases VG.X86_64.cases4 hm with rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hj with rfl | rfl | rfl | rfl <;> rfl

def packB : VG.Proof.X25519.X86_64.Ifma.Bnds :=
  ⟨fun r => if r < 5 then 2 ^ 51 + 18 else 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1,
    fun d => if d = KM then 2 ^ 51 - 1 else if d = K13 then 2 ^ 13 - 1 else if d = K26 then 2 ^ 26 - 1
      else if d = K39 then 2 ^ 39 - 1 else 2 ^ 64 - 1, fun _ => 0⟩

theorem packT_ok : ∀ m < 4, ∀ j < 4, (VG.Proof.X25519.X86_64.Ifma.packT m).ok VG.Proof.X25519.X86_64.Ifma.packB j = true := by decide +kernel

theorem packS_small : ∀ x ∈ packS.st, x.1 < 2 ^ 62 := by decide +kernel
theorem packS_apart : VG.Proof.X25519.X86_64.Ifma.Apart packS.st := by decide +kernel

theorem or_mul {a b n : Nat} (h : a < 2 ^ n) : a ||| b * 2 ^ n = a + b * 2 ^ n := by
  rw [Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq, Nat.add_comm]

/-- The four words stand for the limbs' number. -/
theorem packW_val (x : Nat → Nat) (hx : ∀ i < 5, x i ≤ 2 ^ 51 + 18) :
    VG.Proof.X25519.X86_64.Ifma.packW x (2 ^ 51 - 1) (2 ^ 13 - 1) (2 ^ 26 - 1) (2 ^ 39 - 1) 0 +
      2 ^ 64 * VG.Proof.X25519.X86_64.Ifma.packW x (2 ^ 51 - 1) (2 ^ 13 - 1) (2 ^ 26 - 1) (2 ^ 39 - 1) 1 +
      2 ^ 128 * VG.Proof.X25519.X86_64.Ifma.packW x (2 ^ 51 - 1) (2 ^ 13 - 1) (2 ^ 26 - 1) (2 ^ 39 - 1) 2 +
      2 ^ 192 * VG.Proof.X25519.X86_64.Ifma.packW x (2 ^ 51 - 1) (2 ^ 13 - 1) (2 ^ 26 - 1) (2 ^ 39 - 1) 3 = VG.Proof.X25519.X86_64.Ifma.lv x := by
  have h0 := hx 0 (by decide); have h1 := hx 1 (by decide); have h2 := hx 2 (by decide)
  have h3 := hx 3 (by decide); have h4 := hx 4 (by decide)
  simp only [VG.Proof.X25519.X86_64.Ifma.packW, VG.Proof.X25519.X86_64.Ifma.pre, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 13 ∣ 2 ^ 51),
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 26 ∣ 2 ^ 51), Nat.mod_mod_of_dvd _ (by decide : 2 ^ 39 ∣ 2 ^ 51)]
  rw [VG.Proof.X25519.X86_64.Ifma.or_mul (by omega), VG.Proof.X25519.X86_64.Ifma.or_mul (by omega), VG.Proof.X25519.X86_64.Ifma.or_mul (by omega), VG.Proof.X25519.X86_64.Ifma.or_mul (by omega)]
  simp only [VG.Proof.X25519.X86_64.Ifma.lv]
  omega

/-- A carry of limbs below `2⁵²` leaves limbs of at most `2⁵¹ + 18`. -/
theorem carryNat_le (x : Nat → Nat) (hx : ∀ i < 5, x i < 2 ^ 52) :
    ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.carryNat (2 ^ 51 - 1) 19 x i ≤ 2 ^ 51 + 18 := by
  have h0 := hx 0 (by decide); have h1 := hx 1 (by decide); have h2 := hx 2 (by decide)
  have h3 := hx 3 (by decide); have h4 := hx 4 (by decide)
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  · simp only [VG.Proof.X25519.X86_64.Ifma.carryNat, Nat.and_two_pow_sub_one_eq_mod]
    rcases (by omega : x 4 / 2 ^ 51 = 0 ∨ x 4 / 2 ^ 51 = 1) with e | e <;> rw [e] <;> omega
  all_goals simp only [VG.Proof.X25519.X86_64.Ifma.carryNat, Nat.and_two_pow_sub_one_eq_mod]; omega

theorem packB_env {s : State} {base : Addr} {x1 : Nat → Nat} (hs : s.gpr .rdi = base)
    (hk : VG.Proof.X25519.X86_64.Ifma.Consts s.mem base x1) (hx : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s 0 l i ≤ 2 ^ 51 + 18) : VG.Proof.X25519.X86_64.Ifma.EnvOK s VG.Proof.X25519.X86_64.Ifma.packB := by
  refine VG.Proof.X25519.X86_64.Ifma.envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun _ _ _ => Nat.zero_le _)
  · simp only [VG.Proof.X25519.X86_64.Ifma.packB]
    split
    · have := hx l hl r (by omega); simp only [VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add] at this; exact this
    · exact VG.Proof.X25519.X86_64.Ifma.lt64 _
  · simp only [VG.Proof.X25519.X86_64.Ifma.packB]
    split
    · subst_vars; rw [hk.km l hl]
    · split
      · subst_vars; rw [hk.k13 l hl]
      · split
        · subst_vars; rw [hk.k26 l hl]
        · split
          · subst_vars; rw [hk.k39 l hl]
          · exact VG.Proof.X25519.X86_64.Ifma.lt64 _

/-- `vfinish`: each lane as four words, in the slots `x2, z2, x3, z3`. -/
theorem vfinish_wp {s : State} {base : Addr} {x1 : Nat → Nat} (hs : Scr s base) (hk : VG.Proof.X25519.X86_64.Ifma.Consts s.mem base x1)
    (hy : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s 0 l i < 2 ^ 61) :
    WP isa (.block vfinish) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mxcsr = s.mxcsr ∧ Outside base 96 128 s.mem s'.mem ∧
      ∀ m < 4, F s'.mem base (X2 + 32 * m) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s 0 m) := by
  have hr := hs.rdi
  simp only [vfinish, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.carryI_wp hr (VG.Proof.X25519.X86_64.Ifma.scr_ctx hs) hk.c fun l hl i hi => by have := hy l hl i hi; omega)
    fun s₁ ⟨v₁, m₁, u₁, _⟩ => ?_
  have hs₁ := VG.Proof.X25519.X86_64.Ifma.scr_of hs (VG.Proof.X25519.X86_64.Ifma.vm_gpr v₁) (VG.Proof.X25519.X86_64.Ifma.vm_wr v₁)
  have hk₁ : VG.Proof.X25519.X86_64.Ifma.Consts s₁.mem base x1 := by rw [m₁]; exact hk
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.carryI_wp hs₁.rdi (VG.Proof.X25519.X86_64.Ifma.scr_ctx hs₁) hk₁.c fun l hl i hi => by have := (u₁ l hl i hi).2; omega)
    fun s₂ ⟨v₂, m₂, u₂, _⟩ => ?_
  have hs₂ := VG.Proof.X25519.X86_64.Ifma.scr_of hs₁ (VG.Proof.X25519.X86_64.Ifma.vm_gpr v₂) (VG.Proof.X25519.X86_64.Ifma.vm_wr v₂)
  have hk₂ : VG.Proof.X25519.X86_64.Ifma.Consts s₂.mem base x1 := by rw [m₂]; exact hk₁
  have b₂ : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s₂ 0 l i ≤ 2 ^ 51 + 18 := fun l hl i hi => by
    rw [(u₂ l hl i hi).1]; exact VG.Proof.X25519.X86_64.Ifma.carryNat_le _ (fun j hj => (u₁ l hl j hj).2) i hi
  have hE := VG.Proof.X25519.X86_64.Ifma.packB_env hs₂.rdi hk₂ b₂
  have e : Sym.init.run vpack = some VG.Proof.X25519.X86_64.Ifma.packS := VG.Proof.X25519.X86_64.Ifma.symOf_eq _ _
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.run_ok (VG.Proof.X25519.X86_64.Ifma.scr_ctx hs₂) e) fun s₃ h => ?_
  have v₃ : VG.Proof.X25519.X86_64.Ifma.vm s₂ s₃ = s₃ := h.eq
  refine ⟨(VG.Proof.X25519.X86_64.Ifma.vm_gpr v₃).trans ((VG.Proof.X25519.X86_64.Ifma.vm_gpr v₂).trans (VG.Proof.X25519.X86_64.Ifma.vm_gpr v₁)), (VG.Proof.X25519.X86_64.Ifma.vm_rd v₃).trans ((VG.Proof.X25519.X86_64.Ifma.vm_rd v₂).trans (VG.Proof.X25519.X86_64.Ifma.vm_rd v₁)),
    (VG.Proof.X25519.X86_64.Ifma.vm_wr v₃).trans ((VG.Proof.X25519.X86_64.Ifma.vm_wr v₂).trans (VG.Proof.X25519.X86_64.Ifma.vm_wr v₁)), ?_, ?_, fun m hm => ?_⟩
  · rw [h.mxcsr]; rw [← v₂, ← v₁]; rfl
  · rw [h.mem, hs₂.rdi, m₂, m₁]
    exact VG.Proof.X25519.X86_64.Ifma.stores_outside _ _ _ (by decide) _ (by decide +kernel)
  · -- the words of lane `m`
    have w : ∀ j < 4, (word s₃.mem base (X2 + 32 * m + 8 * j)).toNat =
        VG.Proof.X25519.X86_64.Ifma.packW (fun i => VG.Proof.X25519.X86_64.Ifma.lanes s₂ 0 m i) (2 ^ 51 - 1) (2 ^ 13 - 1) (2 ^ 26 - 1) (2 ^ 39 - 1) j := fun j hj => by
      rw [← VG.Proof.X25519.X86_64.Ifma.mq_eq_word, h.mem, hs₂.rdi, VG.Proof.X25519.X86_64.Ifma.stores_mq _ _ _ _ (VG.Proof.X25519.X86_64.Ifma.packT_mem m hm) hj VG.Proof.X25519.X86_64.Ifma.packS_small VG.Proof.X25519.X86_64.Ifma.packS_apart,
        (VG.Proof.X25519.X86_64.Ifma.nat_ok hE _ hj (VG.Proof.X25519.X86_64.Ifma.packT_ok m hm j hj)).1, VG.Proof.X25519.X86_64.Ifma.packT_nat _ m hm j hj, VG.Proof.X25519.X86_64.Ifma.envOf_m hs₂.rdi, VG.Proof.X25519.X86_64.Ifma.envOf_m hs₂.rdi,
        VG.Proof.X25519.X86_64.Ifma.envOf_m hs₂.rdi, VG.Proof.X25519.X86_64.Ifma.envOf_m hs₂.rdi, hk₂.km m hm, hk₂.k13 m hm, hk₂.k26 m hm, hk₂.k39 m hm]
      rfl
    have fe : VG.Proof.X25519.X86_64.fe s₃.mem base (X2 + 32 * m) = VG.Proof.X25519.X86_64.Ifma.lv (VG.Proof.X25519.X86_64.Ifma.lanes s₂ 0 m) := by
      simp only [VG.Proof.X25519.X86_64.fe, val4]
      have w0 := w 0 (by decide); have w1 := w 1 (by decide); have w2 := w 2 (by decide)
      have w3 := w 3 (by decide)
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at w0 w1 w2 w3
      rw [w0, show X2 + 32 * m + 16 = X2 + 32 * m + 8 * 2 by rfl, w2, w1, w3]
      exact VG.Proof.X25519.X86_64.Ifma.packW_val _ (b₂ m hm)
    show toFe _ = _
    rw [fe]
    rw [show toFe (VG.Proof.X25519.X86_64.Ifma.lv (VG.Proof.X25519.X86_64.Ifma.lanes s₂ 0 m)) = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s₂ 0 m) from rfl,
      VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => (u₂ m hm i hi).1), VG.Proof.X25519.X86_64.Ifma.fe5_carry _ (by have := (u₁ m hm 4 (by decide)).2; omega),
      VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => (u₁ m hm i hi).1), VG.Proof.X25519.X86_64.Ifma.fe5_carry _ (by have := hy m hm 4 (by decide); omega)]

end VG.Proof.X25519.X86_64.Ifma

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Ifma.Setup`. -/
section

/-!
# X25519 on x86-64 with AVX512_IFMA: before the loop

`vsetup` puts the constants into the working space and the ladder's first
state `(1, 0, x₁, 1)` into the lanes of `ymm0–ymm4`, with `x₁` split into
limbs from its four words at `X1`.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.X25519.X86_64 (Scr Outside Outside.mono ofs off word val4 F E fe)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

/-! ## The constants into registers -/

/-- The registers `consts` writes. -/
def cregs : List Reg := [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12]

theorem consts_wp (s : State) :
    WP isa (.block consts) s fun s' =>
      s'.gpr .rax = 0x7ffffffffffff ∧ s'.gpr .rcx = 19 ∧ s'.gpr .rdx = 0x4000000000000000 - 38912 ∧
      s'.gpr .rbp = 0x4000000000000000 - 2048 ∧ s'.gpr .r8 = 0x1fff ∧ s'.gpr .r9 = 0x3ffffff ∧
      s'.gpr .r10 = 0x7fffffffff ∧ s'.gpr .r11 = 1 ∧ s'.gpr .r12 = 121665 ∧
      (∀ r, r ∉ VG.Proof.X25519.X86_64.Ifma.cregs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [consts, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [VG.Proof.X25519.X86_64.Ifma.cregs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

/-! ## The vector block -/

def initS : VG.Proof.X25519.X86_64.Ifma.Sym := VG.Proof.X25519.X86_64.Ifma.symOf vinit

/-- Limb `j` of `x₁`, from its words (`w`) and the mask `m`. -/
def limbNat (w : Nat → Nat) (m : Nat) : Nat → Nat
  | 0 => w 0 &&& m
  | 1 => w 0 / 2 ^ 51 ||| (w 1 &&& m / 2 ^ 13) * 2 ^ 13
  | 2 => w 1 / 2 ^ 38 ||| (w 2 &&& m / 2 ^ 26) * 2 ^ 26
  | 3 => w 2 / 2 ^ 25 ||| (w 3 &&& m / 2 ^ 39) * 2 ^ 39
  | _ => w 3 / 2 ^ 12

theorem initS_regs (E : VG.Proof.X25519.X86_64.Ifma.Env) : ∀ j < 5, ∀ l < 4, (initS.reg j).nat E l =
    if l = 2 then VG.Proof.X25519.X86_64.Ifma.limbNat (fun k => E.m X1 k) (E.g .rax) j
    else if j = 0 ∧ (l = 0 ∨ l = 3) then E.g .r11 else 0 := by
  intro j hj l hl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

/-- The term `vinit` stores at `d`. -/
def initT (d : Nat) : VG.Proof.X25519.X86_64.Ifma.T := ((initS.st.find? fun x => x.1 == d).getD (0, .zero)).2

theorem initT_mem : ∀ d ∈ [KM, K19, KB0, KB1, K13, K26, K39, KX1, KX1 + 32, KX1 + 64, KX1 + 96, KX1 + 128,
    KA24, KA24 + 32, KA24 + 64, KA24 + 96, KA24 + 128], (d, VG.Proof.X25519.X86_64.Ifma.initT d) ∈ initS.st := by decide +kernel

theorem initT_kx1 (E : VG.Proof.X25519.X86_64.Ifma.Env) : ∀ j < 5, ∀ l < 4, (VG.Proof.X25519.X86_64.Ifma.initT (KX1 + 32 * j)).nat E l =
    if l = 3 then VG.Proof.X25519.X86_64.Ifma.limbNat (fun k => E.m X1 k) (E.g .rax) j
    else if j = 0 ∧ (l = 0 ∨ l = 2) then E.g .r11 else 0 := by
  intro j hj l hl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

theorem initT_a24 (E : VG.Proof.X25519.X86_64.Ifma.Env) : ∀ j < 5, ∀ l < 4, (VG.Proof.X25519.X86_64.Ifma.initT (KA24 + 32 * j)).nat E l =
    if j = 0 ∧ l = 3 then E.g .r12 else 0 := by
  intro j hj l hl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

theorem initT_const : ∀ x ∈ [(KM, Reg.rax), (K19, .rcx), (KB0, .rdx), (KB1, .rbp), (K13, .r8), (K26, .r9),
    (K39, .r10)], VG.Proof.X25519.X86_64.Ifma.initT x.1 = .bc (.lane0 (.gpr x.2)) := by decide +kernel

theorem initS_small : ∀ x ∈ initS.st, x.1 < 2 ^ 62 := by decide +kernel
theorem initS_apart : VG.Proof.X25519.X86_64.Ifma.Apart initS.st := by decide +kernel
theorem initS_range : ∀ x ∈ initS.st, 1664 ≤ x.1 ∧ x.1 + 32 ≤ 1664 + 544 := by decide +kernel

def initB : VG.Proof.X25519.X86_64.Ifma.Bnds :=
  ⟨fun _ => 2 ^ 64 - 1,
    fun g => if g = .rax then 2 ^ 51 - 1 else if g = .r11 then 1 else if g = .r12 then 121665 else 2 ^ 64 - 1,
    fun _ => 2 ^ 64 - 1, fun _ => 0⟩

theorem initS_ok : ∀ j < 5, ∀ l < 4, (initS.reg j).ok VG.Proof.X25519.X86_64.Ifma.initB l = true ∧ (initS.reg j).bnd VG.Proof.X25519.X86_64.Ifma.initB l < 2 ^ 52 := by
  decide +kernel

theorem initT_ok : ∀ d ∈ [KX1, KX1 + 32, KX1 + 64, KX1 + 96, KX1 + 128, KA24, KA24 + 32, KA24 + 64, KA24 + 96,
    KA24 + 128], ∀ l < 4, (VG.Proof.X25519.X86_64.Ifma.initT d).ok VG.Proof.X25519.X86_64.Ifma.initB l = true := by decide +kernel

/-- The limbs stand for the words' number. -/
theorem limbNat_lv (w : Nat → Nat) (hw : ∀ k < 4, w k < 2 ^ 64) :
    VG.Proof.X25519.X86_64.Ifma.lv (VG.Proof.X25519.X86_64.Ifma.limbNat w (2 ^ 51 - 1)) = w 0 + 2 ^ 64 * w 1 + 2 ^ 128 * w 2 + 2 ^ 192 * w 3 := by
  have e13 : (2 ^ 51 - 1) / 2 ^ 13 = 2 ^ 38 - 1 := by decide
  have e26 : (2 ^ 51 - 1) / 2 ^ 26 = 2 ^ 25 - 1 := by decide
  have e39 : (2 ^ 51 - 1) / 2 ^ 39 = 2 ^ 12 - 1 := by decide
  have h0 := hw 0 (by decide); have h1 := hw 1 (by decide); have h2 := hw 2 (by decide)
  simp only [VG.Proof.X25519.X86_64.Ifma.lv, VG.Proof.X25519.X86_64.Ifma.limbNat, e13, e26, e39, Nat.and_two_pow_sub_one_eq_mod]
  rw [VG.Proof.X25519.X86_64.Ifma.or_mul (by omega), VG.Proof.X25519.X86_64.Ifma.or_mul (by omega), VG.Proof.X25519.X86_64.Ifma.or_mul (by omega)]
  omega

/-- The limbs of `x₁`, from its words at `X1`. -/
def xl (m : Mem) (base : Addr) : Nat → Nat :=
  VG.Proof.X25519.X86_64.Ifma.limbNat (fun k => (word m base (X1 + 8 * k)).toNat) (2 ^ 51 - 1)

theorem initB_env {s : State} (ha : s.gpr .rax = 0x7ffffffffffff)
    (h11 : s.gpr .r11 = 1) (h12 : s.gpr .r12 = 121665) : VG.Proof.X25519.X86_64.Ifma.EnvOK s VG.Proof.X25519.X86_64.Ifma.initB := by
  refine ⟨fun r k _ => VG.Proof.X25519.X86_64.Ifma.lt64 _, fun g => ?_, fun d k _ => VG.Proof.X25519.X86_64.Ifma.lt64 _, fun _ _ _ => Nat.zero_le _⟩
  simp only [VG.Proof.X25519.X86_64.Ifma.initB]
  split
  · subst_vars; rw [ha]; decide
  · split
    · subst_vars; rw [h11]; decide
    · split
      · subst_vars; rw [h12]; decide
      · exact VG.Proof.X25519.X86_64.Ifma.lt64 _

theorem stores_const {s₀ : State} {base : Addr} {m : Mem} {st : List (Nat × VG.Proof.X25519.X86_64.Ifma.T)} {d : Nat} {r : Reg}
    (h : (d, T.bc (.lane0 (.gpr r))) ∈ st) (hs : ∀ x ∈ st, x.1 < 2 ^ 62) (ha : VG.Proof.X25519.X86_64.Ifma.Apart st) {l : Nat} (hl : l < 4) :
    VG.Proof.X25519.X86_64.Ifma.mq (VG.Proof.X25519.X86_64.Ifma.stores s₀ base st m) base (d + 8 * l) = s₀.gpr r := by
  rw [VG.Proof.X25519.X86_64.Ifma.stores_mq _ _ _ _ h hl hs ha]; simp only [T.eval, ite_true]

/-- `vsetup`: the constants, and `(1, 0, x₁, 1)` in the lanes. -/
theorem vsetup_wp {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block vsetup) s fun s' => (∀ r, r ∉ VG.Proof.X25519.X86_64.Ifma.cregs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr ∧ Outside base 1664 544 s.mem s'.mem ∧
      VG.Proof.X25519.X86_64.Ifma.Consts s'.mem base (VG.Proof.X25519.X86_64.Ifma.xl s.mem base) ∧
      (∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s' 0 l i =
        if l = 2 then VG.Proof.X25519.X86_64.Ifma.xl s.mem base i else if i = 0 ∧ (l = 0 ∨ l = 3) then 1 else 0) := by
  rw [vsetup, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.consts_wp s) fun s₁ ⟨ha, hc, hd, hb, h8, h9, h10, h11, h12, g₁, m₁, rd₁, wr₁, _, _, x₁⟩ => ?_
  have hs₁ : Scr s₁ base := ⟨by rw [g₁ _ (by decide)]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  have hE := VG.Proof.X25519.X86_64.Ifma.initB_env ha h11 h12
  have e : Sym.init.run vinit = some VG.Proof.X25519.X86_64.Ifma.initS := VG.Proof.X25519.X86_64.Ifma.symOf_eq _ _
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.run_ok (VG.Proof.X25519.X86_64.Ifma.scr_ctx hs₁) e) fun s₂ h => ?_
  have hmem : s₂.mem = VG.Proof.X25519.X86_64.Ifma.stores s₁ base initS.st s₁.mem := by rw [h.mem, hs₁.rdi]
  have hX : ∀ k, (VG.Proof.X25519.X86_64.Ifma.envOf s₁).m X1 k = (word s.mem base (X1 + 8 * k)).toNat := fun k => by
    rw [VG.Proof.X25519.X86_64.Ifma.envOf_m hs₁.rdi, m₁]; rfl
  have hxl : (fun k => (VG.Proof.X25519.X86_64.Ifma.envOf s₁).m X1 k) = fun k => (word s.mem base (X1 + 8 * k)).toNat :=
    funext hX
  have hg : ∀ r, (VG.Proof.X25519.X86_64.Ifma.envOf s₁).g r = (s₁.gpr r).toNat := fun _ => rfl
  have cst : ∀ d r l, (d, r) ∈ [(KM, Reg.rax), (K19, .rcx), (KB0, .rdx), (KB1, .rbp), (K13, .r8), (K26, .r9),
      (K39, .r10)] → l < 4 → (VG.Proof.X25519.X86_64.Ifma.mq s₂.mem base (d + 8 * l)).toNat = (s₁.gpr r).toNat := fun d r l hd hl => by
    have t := VG.Proof.X25519.X86_64.Ifma.initT_const _ hd
    have hm := VG.Proof.X25519.X86_64.Ifma.initT_mem d (by simp only [List.mem_cons] at hd ⊢; rcases hd with h | h | h | h | h | h | h | h <;>
                                  simp_all)
    simp only at t
    rw [t] at hm
    rw [hmem, VG.Proof.X25519.X86_64.Ifma.stores_const hm VG.Proof.X25519.X86_64.Ifma.initS_small VG.Proof.X25519.X86_64.Ifma.initS_apart hl]
  have kx : ∀ j < 5, ∀ l < 4, VG.Proof.X25519.X86_64.Ifma.slotv s₂.mem base KX1 l j =
      if l = 3 then VG.Proof.X25519.X86_64.Ifma.xl s.mem base j else if j = 0 ∧ l ≠ 1 then 1 else 0 := fun j hj l hl => by
    have hm := VG.Proof.X25519.X86_64.Ifma.initT_mem (KX1 + 32 * j) (by
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;> decide)
    rw [VG.Proof.X25519.X86_64.Ifma.slotv, hmem, VG.Proof.X25519.X86_64.Ifma.stores_mq _ _ _ _ hm hl VG.Proof.X25519.X86_64.Ifma.initS_small VG.Proof.X25519.X86_64.Ifma.initS_apart,
      (VG.Proof.X25519.X86_64.Ifma.nat_ok hE _ hl (VG.Proof.X25519.X86_64.Ifma.initT_ok _ (by
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;> decide) l hl)).1,
      VG.Proof.X25519.X86_64.Ifma.initT_kx1 _ j hj l hl, hxl, hg, hg, ha, h11]
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> simp [VG.Proof.X25519.X86_64.Ifma.xl]
  have ka : ∀ j < 5, ∀ l < 4, VG.Proof.X25519.X86_64.Ifma.slotv s₂.mem base KA24 l j = if j = 0 ∧ l = 3 then 121665 else 0 :=
    fun j hj l hl => by
      have hm := VG.Proof.X25519.X86_64.Ifma.initT_mem (KA24 + 32 * j) (by
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;> decide)
      rw [VG.Proof.X25519.X86_64.Ifma.slotv, hmem, VG.Proof.X25519.X86_64.Ifma.stores_mq _ _ _ _ hm hl VG.Proof.X25519.X86_64.Ifma.initS_small VG.Proof.X25519.X86_64.Ifma.initS_apart,
        (VG.Proof.X25519.X86_64.Ifma.nat_ok hE _ hl (VG.Proof.X25519.X86_64.Ifma.initT_ok _ (by
          rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;> decide) l hl)).1,
        VG.Proof.X25519.X86_64.Ifma.initT_a24 _ j hj l hl, hg, h12]
      rfl
  have lan : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s₂ 0 l i =
      if l = 2 then VG.Proof.X25519.X86_64.Ifma.xl s.mem base i else if i = 0 ∧ (l = 0 ∨ l = 3) then 1 else 0 := fun l hl i hi => by
    obtain ⟨o, _⟩ := VG.Proof.X25519.X86_64.Ifma.initS_ok i hi l hl
    have := (h.out hE (by omega) hl o).1
    simp only [VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add] at this ⊢
    rw [this, VG.Proof.X25519.X86_64.Ifma.initS_regs _ i hi l hl, hxl, hg, hg, ha, h11]
    rfl
  refine ⟨fun r hr => by rw [VG.Proof.X25519.X86_64.Ifma.vm_gpr h.eq, g₁ r hr], by rw [VG.Proof.X25519.X86_64.Ifma.vm_rd h.eq, rd₁], by rw [VG.Proof.X25519.X86_64.Ifma.vm_wr h.eq, wr₁],
    by rw [h.mxcsr, x₁], ?_, ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, ka, kx,
      fun i hi => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩, lan⟩
  · rw [hmem, m₁]; exact VG.Proof.X25519.X86_64.Ifma.stores_outside _ _ _ (by decide) _ VG.Proof.X25519.X86_64.Ifma.initS_range
  · rw [cst KM .rax l (by decide) hl, ha]; rfl
  · rw [cst K19 .rcx l (by decide) hl, hc]; rfl
  · rw [cst KB0 .rdx l (by decide) hl, hd]; rfl
  · rw [cst KB1 .rbp l (by decide) hl, hb]; rfl
  · have := (VG.Proof.X25519.X86_64.Ifma.initS_ok i hi 2 (by decide)).2
    have e := (h.out hE (by omega) (show 2 < 4 by decide) (VG.Proof.X25519.X86_64.Ifma.initS_ok i hi 2 (by decide)).1)
    have l2 := lan 2 (by decide) i hi
    simp only [VG.Proof.X25519.X86_64.Ifma.lanes, Nat.zero_add, ite_true] at l2
    rw [← l2]; omega
  · rw [cst K13 .r8 l (by decide) hl, h8]; rfl
  · rw [cst K26 .r9 l (by decide) hl, h9]; rfl
  · rw [cst K39 .r10 l (by decide) hl, h10]; rfl

end VG.Proof.X25519.X86_64.Ifma

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Ifma.Ladder`. -/
section

/-!
# X25519 on x86-64 with AVX512_IFMA: the ladder

`vladder`: `vsetup`, then with MXCSR `0x1FBF` the loop and `vfinish`, leaves
the ladder's final `(x₂, z₂, x₃, z₃)` in the slots `x2, z2, x3, z3`, and its
`swap` at `SWAP`, as `vg_x25519`'s ladder does (`LPost`).
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.X25519.X86_64 (Scr Outside Outside.mono ofs off word val4 F E fe clob contains_sc ea_sc
  writeW_outside LPost)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

/-! ## The loop -/

/-- The ladder's loop, from the counter `n ≥ 1` down to 0. -/
theorem vloop_ok {s₀ : State} {base : Addr} {k : Nat} {u : Fe} {x1 : Nat → Nat}
    (hbits : ∀ t < 255, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 255 → VG.Proof.X25519.X86_64.Ifma.VInv base k u x1 s₀ s n →
      WP isa (.loop (.block vstep) .ne) s fun s' => VG.Proof.X25519.X86_64.Ifma.VInv base k u x1 s₀ s' 0 := by
  intro n s h1 h2 hi
  refine WP.loop (M := isa) (body := .block vstep) (c := .ne)
    (Q := fun s' => VG.Proof.X25519.X86_64.Ifma.VInv base k u x1 s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 255 ∧ VG.Proof.X25519.X86_64.Ifma.VInv base k u x1 s₀ s m) ?_ n s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.vstep_ok (by omega) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [VG.X86_64.eval, hz, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, hi'⟩

/-! ## MXCSR -/

theorem mx_in {s : State} {base : Addr} (hs : Scr s base) {d n : Nat} (hd : d + n ≤ 4096) :
    InRegions s.wr (off base d) n := ⟨_, hs.wr, contains_sc hd⟩

theorem mx_in' {s : State} {base : Addr} (hs : Scr s base) {d n : Nat} (hd : d + n ≤ 4096) :
    InRegions (s.rd ++ s.wr) (off base d) n := ⟨_, List.mem_append_right _ hs.wr, contains_sc hd⟩

/-- What the MXCSR blocks keep. -/
structure MxKeep (base : Addr) (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outside base MX 8 s.mem s'.mem
  xmm : s'.xmm = s.xmm
  ymm : s'.ymmHi = s.ymmHi

theorem MxKeep.lanes {base : Addr} {s s' : State} (h : VG.Proof.X25519.X86_64.Ifma.MxKeep base s s') (r l i : Nat) :
    VG.Proof.X25519.X86_64.Ifma.lanes s' r l i = VG.Proof.X25519.X86_64.Ifma.lanes s r l i := VG.Proof.X25519.X86_64.Ifma.lanes_of_vec h.xmm h.ymm r l i

theorem outside_mx (m : Mem) (base : Addr) {d : Nat} (hd : MX ≤ d ∧ d + 4 ≤ MX + 8) (v : BitVec 32) :
    Outside base MX 8 m (m.writeW (off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by simp only [MX] at hd ⊢; omega)]
  simp only [ofs] at hx
  simp only [MX] at hd hx ⊢
  omega

/-- The save: MXCSR (its reserved bits cleared) into `r11`. -/
theorem save_wp {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block [.stmxcsr (sc MX), .mov32 .r11 (.mem (sc MX)), .alu32 .and .r11 (.imm 0xFFFF)]) s
      fun s' => (∀ r, r ≠ .r11 → s'.gpr r = s.gpr r) ∧
        (s'.gpr .r11).setWidth 32 = s.mxcsr &&& 0xFFFF ∧ VG.Proof.X25519.X86_64.Ifma.MxKeep base s s' := by
  apply WP.of_runBlock
  have h1 := VG.Proof.X25519.X86_64.Ifma.mx_in hs (show MX + 4 ≤ 4096 by decide)
  have h2 := VG.Proof.X25519.X86_64.Ifma.mx_in' hs (show MX + 4 ≤ 4096 by decide)
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, State.load32, readSrc32, ea_sc,
    hs.rdi, h1, h2, ite_true, Option.bind_some, Option.map_some, Mem.readW_writeW_self32, execAlu32,
    State.setReg32, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, ?_, ⟨rfl, rfl, VG.Proof.X25519.X86_64.Ifma.outside_mx _ _ (by simp only [MX]; omega) _, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  · simp only [RegUpd.gpr_setReg_self, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide),
      BitVec.setWidth_eq]

/-- `0x1FBF` into MXCSR, through `[MX + 4]` and `rax`. -/
theorem load_wp {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block [.mov32 .rax (.imm 0x1FBF), .store32 (sc (MX + 4)) .rax, .ldmxcsr (sc (MX + 4)), .lfence]) s
      fun s' => (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ VG.Proof.X25519.X86_64.Ifma.MxKeep base s s' := by
  apply WP.of_runBlock
  have h1 := VG.Proof.X25519.X86_64.Ifma.mx_in hs (show MX + 4 + 4 ≤ 4096 by decide)
  have h2 := VG.Proof.X25519.X86_64.Ifma.mx_in' hs (show MX + 4 + 4 ≤ 4096 by decide)
  have e : (BitVec.setWidth 32 (BitVec.setWidth 64 (0x1FBF : BitVec 32))).extractLsb' 16 16 = 0 := by decide
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, State.load32, readSrc32, ea_sc,
    RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.rd_setReg, hs.rdi, h1, h2, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, Option.map_some, Mem.readW_writeW_self32, State.setReg32, e, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun r hr => ?_, ⟨rfl, rfl, VG.Proof.X25519.X86_64.Ifma.outside_mx _ _ (by simp only [MX]; omega) _, rfl, rfl⟩⟩
  simp only [hr, ite_false]

/-- MXCSR back from `r11`, through `[MX]`. -/
theorem restore_wp {s : State} {base : Addr} (hs : Scr s base)
    (h11 : ((s.gpr .r11).setWidth 32).extractLsb' 16 16 = 0) :
    WP isa (.block [.store32 (sc MX) .r11, .ldmxcsr (sc MX)]) s
      fun s' => s'.gpr = s.gpr ∧ VG.Proof.X25519.X86_64.Ifma.MxKeep base s s' := by
  apply WP.of_runBlock
  have h1 := VG.Proof.X25519.X86_64.Ifma.mx_in hs (show MX + 4 ≤ 4096 by decide)
  have h2 := VG.Proof.X25519.X86_64.Ifma.mx_in' hs (show MX + 4 ≤ 4096 by decide)
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, State.load32, ea_sc, hs.rdi, h1,
    h2, ite_true, Option.bind_some, Mem.readW_writeW_self32, h11, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, ⟨rfl, rfl, VG.Proof.X25519.X86_64.Ifma.outside_mx _ _ (by simp only [MX]; omega) _, rfl, rfl⟩⟩

theorem and_ffff (v : BitVec 32) : (v &&& 0xFFFF).extractLsb' 16 16 = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, hi, decide_true, Bool.true_and]
  rw [show (0xFFFF : BitVec 32).getLsbD (16 + i) = false by revert i; decide]
  simp

/-! ## The ladder -/

theorem movRbx_wp (s : State) :
    WP isa (.block [.mov32 .rbx (.imm 255)]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 255 ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  exact ⟨rfl, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl, rfl, rfl⟩

theorem lfence_wp (s : State) : WP isa (.block [.lfence]) s fun s' => s' = s := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']

theorem fe5_one' : VG.Proof.X25519.X86_64.Ifma.fe5 (fun i => if i = 0 then 1 else 0) = 1 := VG.Proof.X25519.X86_64.Ifma.fe5_one
theorem fe5_zero : VG.Proof.X25519.X86_64.Ifma.fe5 (fun _ => 0) = 0 := rfl

theorem vladder_eq : vladder = .seq (.block vsetup) (.seq (.block [.stmxcsr (sc MX), .mov32 .r11 (.mem (sc MX)),
    .alu32 .and .r11 (.imm 0xFFFF)]) (.seq (.seq (.block [.mov32 .rax (.imm 0x1FBF), .store32 (sc (MX + 4)) .rax,
      .ldmxcsr (sc (MX + 4)), .lfence]) (.seq (.seq (.block [.mov32 .rbx (.imm 255)])
        (.seq (.loop (.block vstep) .ne) (.block vfinish))) (.block [.lfence])))
      (.block [.store32 (sc MX) .r11, .ldmxcsr (sc MX)]))) := rfl

/-- The ladder: from the words of `x₁` at `X1` and `swap = 0`, the ladder's
final state. -/
theorem vladder_ok {s₀ : State} {base : Addr} {k : Nat} {u : Fe} (hs : Scr s₀ base)
    (hbits : ∀ t < 255, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t))
    (hx1 : E s₀.mem base 2 = u) (hsw : word s₀.mem base SWAP = 0) :
    WP isa vladder s₀ (LPost base k u s₀) := by
  rw [VG.Proof.X25519.X86_64.Ifma.vladder_eq]
  refine WP.seq (WP.mono (VG.Proof.X25519.X86_64.Ifma.vsetup_wp hs) fun s₁ ⟨g₁, rd₁, wr₁, mx₁, o₁, hk₁, l₁⟩ => ?_)
  have hs₁ : Scr s₁ base := ⟨by rw [g₁ _ (by decide)]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  refine WP.seq (WP.mono (VG.Proof.X25519.X86_64.Ifma.save_wp hs₁) fun s₂ ⟨g₂, r11₂, k₂⟩ => ?_)
  have hs₂ : Scr s₂ base := ⟨by rw [g₂ _ (by decide)]; exact hs₁.rdi, by rw [k₂.wr]; exact hs₁.wr, hs.nowrap⟩
  refine WP.seq (WP.seq (WP.mono (VG.Proof.X25519.X86_64.Ifma.load_wp hs₂) fun s₃ ⟨g₃, k₃⟩ => ?_))
  have hs₃ : Scr s₃ base := ⟨by rw [g₃ _ (by decide)]; exact hs₂.rdi, by rw [k₃.wr]; exact hs₂.wr, hs.nowrap⟩
  refine WP.seq (WP.seq (WP.mono (VG.Proof.X25519.X86_64.Ifma.movRbx_wp s₃) fun s₄ ⟨b₄, g₄, m₄, rd₄, wr₄, x₄, y₄⟩ => ?_))
  have hs₄ : Scr s₄ base := ⟨by rw [g₄ _ (by decide)]; exact hs₃.rdi, by rw [wr₄]; exact hs₃.wr, hs.nowrap⟩
  -- memory up to the loop
  have O₄ : Outside base 64 2152 s₀.mem s₄.mem := by
    rw [m₄]
    exact ((o₁.mono (by decide) (by decide)).trans (k₂.mem.mono (by decide) (by decide))).trans
      (k₃.mem.mono (by decide) (by decide))
  have O₁₄ : Outside base MX 8 s₁.mem s₄.mem := by rw [m₄]; exact k₂.mem.trans k₃.mem
  have hk₄ : VG.Proof.X25519.X86_64.Ifma.Consts s₄.mem base (VG.Proof.X25519.X86_64.Ifma.xl s₀.mem base) := hk₁.of_word fun d h1 h2 => by
    rw [VG.Proof.X25519.X86_64.Ifma.mq_eq_word, VG.Proof.X25519.X86_64.Ifma.mq_eq_word]
    exact O₁₄.word (by simp only [MX]; omega) (by omega)
  have lan₄ : ∀ l < 4, ∀ i < 5, VG.Proof.X25519.X86_64.Ifma.lanes s₄ 0 l i =
      if l = 2 then VG.Proof.X25519.X86_64.Ifma.xl s₀.mem base i else if i = 0 ∧ (l = 0 ∨ l = 3) then 1 else 0 := fun l hl i hi => by
    rw [VG.Proof.X25519.X86_64.Ifma.lanes_of_vec x₄ y₄, k₃.lanes, k₂.lanes, l₁ l hl i hi]
  have bits₄ : ∀ t < 255, s₄.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t) := fun t ht => by
    have ho : ofs base (off base (BITS + t)) = BITS + t :=
      VG.Proof.X25519.X86_64.ofs_off' base (by simp only [BITS]; omega)
    rw [O₁₄ _ (by rw [ho]; simp only [BITS, MX]; omega), o₁ _ (by rw [ho]; simp only [BITS]; omega)]
    exact hbits t ht
  have fx1 : VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.xl s₀.mem base) = u := by
    rw [← hx1]
    show toFe _ = toFe _
    congr 1
    rw [VG.Proof.X25519.X86_64.Ifma.xl, VG.Proof.X25519.X86_64.Ifma.limbNat_lv _ (fun k _ => BitVec.isLt _)]
    rfl
  have I : VG.Proof.X25519.X86_64.Ifma.VInv base k u (VG.Proof.X25519.X86_64.Ifma.xl s₀.mem base) s₄ s₄ 255 := by
    refine ⟨hs₄, fun _ _ => rfl, b₄, rfl, rfl, VFrame.refl _ _, hk₄, fx1, ?_, fun l hl i hi => ?_, ?_, ?_, ?_, ?_⟩
    · show word s₄.mem base SWAP = BitVec.ofNat 64 0
      rw [O₁₄.word (by simp only [SWAP, MX]; omega) (by simp only [SWAP]; omega),
        o₁.word (by simp only [SWAP]; omega) (by simp only [SWAP]; omega), hsw]; rfl
    · rw [lan₄ l hl i hi]; have := hk₄.x1 i hi; split <;> [omega; split <;> omega]
    · rw [VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => lan₄ 0 (by decide) i hi)]; exact VG.Proof.X25519.X86_64.Ifma.fe5_one'
    · rw [VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => lan₄ 1 (by decide) i hi)]; simp only [Nat.one_ne_zero, false_or,
        show (1 : Nat) ≠ 3 by decide, and_false, ite_false]; exact VG.Proof.X25519.X86_64.Ifma.fe5_zero
    · rw [VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => lan₄ 2 (by decide) i hi)]; simp only [ite_true]; exact fx1
    · rw [VG.Proof.X25519.X86_64.Ifma.fe5_congr (fun i hi => lan₄ 3 (by decide) i hi)]
      simp only [show (3 : Nat) ≠ 2 by decide, ite_false, or_true, and_true]; exact VG.Proof.X25519.X86_64.Ifma.fe5_one'
  refine WP.seq (WP.mono (VG.Proof.X25519.X86_64.Ifma.vloop_ok bits₄ 255 s₄ (by decide) (by decide) I) fun s₅ V => ?_)
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.vfinish_wp V.scr V.consts V.lim) fun s₆ ⟨g₆, rd₆, wr₆, mx₆, o₆, f₆⟩ => ?_
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.lfence_wp s₆) fun s₇ e₇ => ?_
  subst e₇
  have hs₆ : Scr s₇ base := ⟨by rw [g₆]; exact V.scr.rdi, by rw [wr₆]; exact V.scr.wr, hs.nowrap⟩
  have r11₇ : s₇.gpr .r11 = s₂.gpr .r11 := by
    rw [g₆, V.gpr _ (by decide), g₄ _ (by decide), g₃ _ (by decide)]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.restore_wp hs₆ (by rw [r11₇, r11₂]; exact VG.Proof.X25519.X86_64.Ifma.and_ffff _)) fun s₈ ⟨g₈, k₈⟩ => ?_
  have fe8 : ∀ m (hm : m < 4), E s₈.mem base ⟨3 + m, by omega⟩ = VG.Proof.X25519.X86_64.Ifma.fe5 (VG.Proof.X25519.X86_64.Ifma.lanes s₅ 0 m) := fun m hm => by
    show toFe (fe s₈.mem base (32 * (3 + m))) = _
    have hm' : m < 4 := hm
    rw [k₈.mem.fe (d := 32 * (3 + m)) (by simp only [MX]; left; omega) (by omega)]
    have := f₆ m hm
    simp only [X2] at this
    rw [show 32 * (3 + m) = 96 + 32 * m by omega]
    exact this
  refine ⟨⟨by rw [g₈]; exact hs₆.rdi, by rw [k₈.wr]; exact hs₆.wr, hs.nowrap⟩, fun r hr hb => ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : r ∉ VG.Proof.X25519.X86_64.Ifma.cregs := fun h => hr (by simp only [VG.Proof.X25519.X86_64.Ifma.cregs, clob, List.mem_cons] at h ⊢; grind)
    have h2 : r ≠ .r11 := fun h => hr (by subst h; decide)
    have h3 : r ≠ .rax := fun h => hr (by subst h; decide)
    have h4 : r ∉ [Reg.rax, .rbx, .rcx, .rdx] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      intro h
      rcases h with h | h | h | h <;> subst h
      · exact hr (by decide)
      · exact hb rfl
      · exact hr (by decide)
      · exact hr (by decide)
    rw [g₈, g₆, V.gpr r h4, g₄ r hb, g₃ r h3, g₂ r h2, g₁ r h1]
  · rw [k₈.rd, rd₆, V.rd, rd₄, k₃.rd, k₂.rd, rd₁]
  · rw [k₈.wr, wr₆, V.wr, wr₄, k₃.wr, k₂.wr, wr₁]
  · have F₅ : Outside base 64 2152 s₄.mem s₅.mem := fun x hx => V.mem x (by omega)
    exact ((O₄.trans F₅).trans (o₆.mono (by decide) (by decide))).trans (k₈.mem.mono (by decide) (by decide))
  · exact (fe8 0 (by decide)).trans V.x2
  · exact (fe8 1 (by decide)).trans V.z2
  · exact (fe8 2 (by decide)).trans V.x3
  · exact (fe8 3 (by decide)).trans V.z3
  · rw [k₈.mem.word (by simp only [SWAP, MX]; omega) (by simp only [SWAP]; omega),
      o₆.word (by simp only [SWAP]; omega) (by simp only [SWAP]; omega)]
    exact V.swap

end VG.Proof.X25519.X86_64.Ifma

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Ifma.Verified`. -/
section

/-!
# X25519 on x86-64 with AVX512_IFMA: `Verified`

The proof of `vg_x25519` (`Proof/X25519/X86_64/Main.lean`) with the ladder
`vladder` (`vladder_ok`) and the field multiplications `adx` for the
inversion: correctness from `correct_of`; MXCSR's control bits kept, as the
ladder loads MXCSR only between saving it in `r11` and loading it back
(`ctlOk`); constant time by taint tracking (the only branches are on the loop
counters, and every address is an argument plus a constant or a counter);
satisfiability, and the shared contract.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64

theorem vladder_post {s : State} {base : Addr} {k : Nat} {u : Spec.X25519.Fe} (h : LPre base k u s) :
    WP isa Impl.X25519.X86_64.Ifma.vladder s (LPost base k u s) :=
  Ifma.vladder_ok h.scr h.bits h.x1 h.swap

theorem x25519Ifma_ok (s : State) (hs : Proof.X25519.x25519X86_64.pre s) :
    ∃ t s', Exec isa Impl.X25519.X86_64.x25519Ifma s t s' ∧ abiPreserved s s' ∧
      Proof.X25519.x25519X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct_of adx_ok VG.Proof.X25519.X86_64.vladder_post (Pre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_ctl (by lit_decide) he h.1, h.2⟩

theorem x25519Ifma_ct : ConstantTime isa Proof.X25519.x25519X86_64.pre
    Proof.X25519.x25519X86_64.pub Impl.X25519.X86_64.x25519Ifma := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem x25519Ifma_verified :
    Verified X86_64.target Impl.X25519.X86_64.x25519Ifma (Spec.X25519.x25519Contract X86_64.abi) :=
  Verified.of_correct VG.Proof.X25519.X86_64.x25519Ifma_ok VG.Proof.X25519.X86_64.x25519Ifma_ct (by
    sig_implies [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, X86_64.abi, X86_64.argRegs,
      Proof.X25519.x25519X86_64] [satState] using satState)

end VG.Proof.X25519.X86_64

end
