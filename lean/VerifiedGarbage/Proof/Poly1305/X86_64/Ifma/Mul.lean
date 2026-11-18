module

public import VerifiedGarbage.Impl.Poly1305.X86_64.Ifma
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Bound
public import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Sym
public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Sym
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block

/-! ### `Poly1305.X86_64.Ifma.Bound`, which only this module used -/

section

/-! ### `Poly1305.X86_64.Ifma.Sym`, which only this module used -/

section

/-!
# Poly1305 on x86-64 with AVX-512 IFMA: straight-line code, quadword by quadword

As for AVX-512 (`Avx512/Sym.lean`), `Sym.run` computes each quadword of the
`zmm` registers after a block of vector instructions as a term (`Q`) in the
quadwords, general-purpose registers and memory before it, and `srun_ok`
proves the machine agrees. The terms add `vpmadd52luq` and `vpmadd52huq`
(`mad`, with `X25519`'s `mad52` on each quadword) and a register zeroed by
`vpxord` of itself (`zero`); the products of `vpmuludq` and `vpandnq`, which
the code does not use, are left out.
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Ifma

open VG VG.X86_64
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi xi_inj qword_paddq qword_and qword_or qword_punpcklqdq
  qword_punpckhqdq qword_psllq qword_psrlq mod2_lt sel4 sel4_lt vec vec_gpr vec_mem vec_rd vec_wr vec_trans)
open VG.Proof.Poly1305.X86_64.Avx512 (qz cases8 div2_lt qz_zbin qz_vshift qz_vmovdqa64 qz_vpbroadcastq
  sel4_eq qz_vshufi32x4 qz_vmovq qz_load shufIdx shufIdx_lt ldIdx mbIdx ldIdx_ok mbIdx_ok qword_vv qz_bcst
  hv_of qz_lane vec_zop vec_setZ)
open VG.Proof.X25519.X86_64.Ifma (mad52 qword_madd52 qword_xor)

/-! ## The instructions added here -/

theorem qz_vpmadd52 (h : Bool) (s : State) (d a b r : XReg) {k : Nat} (hk : k < 8) :
    qz ((ZOp.vpmadd52 h d a b).exec s) r k =
      if r = d then mad52 h (qz s d k) (qz s a k) (qz s b k) else qz s r k := by
  simp only [ZOp.exec, qz]
  rw [State.zlane_setZ _ _ _ _ _ _ _ (div2_lt hk),
    pick4_lanes (fun i => madd52 h (s.zlane d i) (s.zlane a i) (s.zlane b i)) (div2_lt hk)]
  split
  · exact qword_madd52 _ _ _ _ (mod2_lt k)
  · rfl

theorem qword_pxor_self (x : BitVec 128) (i : Nat) : qword (XBinOp.eval .pxor x x) i = 0 := by
  simp only [XBinOp.eval, BitVec.xor_self]; simp [qword]

/-! ## Terms -/

/-- A quadword, in terms of those where the code starts. -/
inductive Q
  /-- Quadword `k` of the vector register numbered `r`. -/
  | reg (r : Nat)
  /-- A general-purpose register, in every quadword. -/
  | gpr (r : Reg)
  /-- `a` in quadword 0, zero elsewhere. -/
  | lane0 (a : Q)
  /-- Quadword 0 of `a`, in every quadword. -/
  | bc (a : Q)
  /-- Quadword `i + k` of memory at `rsi`. -/
  | ld (i : Nat)
  /-- The quadword of memory at `rdi + d`, in every quadword. -/
  | mb (d : Nat)
  /-- Zero. -/
  | zero
  | add (a b : Q)
  | and (a b : Q)
  | or (a b : Q)
  | shl (a : Q) (n : Nat)
  | shr (a : Q) (n : Nat)
  /-- `vpunpcklqdq`, `vpunpckhqdq`. -/
  | unpl (a b : Q)
  | unph (a b : Q)
  /-- `vshufi32x4` with the immediate `sel`. -/
  | shuf (a b : Q) (sel : Nat)
  /-- `vpmadd52luq` (`h = false`) or `vpmadd52huq` of `a` and `b`, added to `c`. -/
  | mad (h : Bool) (c a b : Q)
  deriving DecidableEq

def Q.eval (s₀ : State) : Q → Nat → BitVec 64
  | .reg r, k => qz s₀ (xr r) k
  | .gpr r, _ => s₀.gpr r
  | .lane0 a, k => if k = 0 then a.eval s₀ 0 else 0
  | .bc a, _ => a.eval s₀ 0
  | .ld i, k => s₀.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * (i + k))) 64
  | .mb d, _ => s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 (d : Int)) 64
  | .zero, _ => 0
  | .add a b, k => a.eval s₀ k + b.eval s₀ k
  | .and a b, k => a.eval s₀ k &&& b.eval s₀ k
  | .or a b, k => a.eval s₀ k ||| b.eval s₀ k
  | .shl a n, k => a.eval s₀ k <<< n
  | .shr a n, k => a.eval s₀ k >>> n
  | .unpl a b, k => if k % 2 = 0 then a.eval s₀ k else b.eval s₀ (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.eval s₀ (k + 1) else b.eval s₀ k
  | .shuf a b sel, k => if k / 2 < 2 then a.eval s₀ (shufIdx sel k) else b.eval s₀ (shufIdx sel k)
  | .mad h c a b, k => mad52 h (c.eval s₀ k) (a.eval s₀ k) (b.eval s₀ k)

/-! ## The machine -/

/-- The terms of the vector registers (by number). -/
structure Sym where
  reg : Nat → Q

def Sym.init : Sym := ⟨.reg⟩

def Sym.set (σ : Sym) (d : XReg) (t : Q) : Sym := ⟨fun r => if r = xi d then t else σ.reg r⟩

def Sym.zbin (σ : Sym) (op : ZBinOp) (d a b : XReg) : Option Sym :=
  let A := σ.reg (xi a)
  let B := σ.reg (xi b)
  match op with
  | .vpaddq => some (σ.set d (.add A B))
  | .vpandq => some (σ.set d (.and A B))
  | .vporq => some (σ.set d (.or A B))
  | .vpunpcklqdq => some (σ.set d (.unpl A B))
  | .vpunpckhqdq => some (σ.set d (.unph A B))
  | .vpxord => if a = b then some (σ.set d .zero) else none
  | _ => none

def Sym.zop (σ : Sym) : ZOp → Option Sym
  | .zbin op d a b => σ.zbin op d a b
  | .vshift op d a n =>
    if n.toNat < 64 then
      match op with
      | .vpsllq => some (σ.set d (.shl (σ.reg (xi a)) n.toNat))
      | .vpsrlq => some (σ.set d (.shr (σ.reg (xi a)) n.toNat))
    else none
  | .vmovdqa64 d a => some (σ.set d (σ.reg (xi a)))
  | .vpbroadcastq d a => some (σ.set d (.bc (σ.reg (xi a))))
  | .vshufi32x4 d a b n => some (σ.set d (.shuf (σ.reg (xi a)) (σ.reg (xi b)) n.toNat))
  | .vpmadd52 h d a b => some (σ.set d (.mad h (σ.reg (xi d)) (σ.reg (xi a)) (σ.reg (xi b))))
  | _ => none

/-- `op` with the quadword at `rdi + e` broadcast as its second source
(`vpandq` and `vporq`). -/
def Sym.bcst (σ : Sym) (op : ZBcstOp) (d a : XReg) (e : Nat) : Option Sym :=
  match op with
  | .vpandq => some (σ.set d (.and (σ.reg (xi a)) (.mb e)))
  | .vporq => some (σ.set d (.or (σ.reg (xi a)) (.mb e)))
  | .vpmuludq => none

/-- One instruction; loads only if `ld`. -/
def Sym.step (ld : Bool) (σ : Sym) : Instr → Option Sym
  | .zop o => σ.zop o
  | .vop (.vmovq d r) => some (σ.set d (.lane0 (.gpr r)))
  | .vmovdqu32Load d m => if ld then (ldIdx m).map fun i => σ.set d (.ld i) else none
  | .zbcst op d a m => if ld then (mbIdx m).bind (σ.bcst op d a) else none
  | _ => none

def Sym.run (ld : Bool) (σ : Sym) : List Instr → Option Sym
  | [] => some σ
  | i :: is => (σ.step ld i).bind fun σ' => σ'.run ld is

/-! ## The machine agrees -/

/-- The terms `σ` hold in `s`, which differs from `s₀` only in its vector
registers. -/
structure SRel (σ : Sym) (s₀ s : State) : Prop where
  reg : ∀ r k, k < 8 → qz s r k = (σ.reg (xi r)).eval s₀ k
  eq : vec s₀ s = s

theorem SRel.gpr {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.gpr = s₀.gpr := vec_gpr h.eq
theorem SRel.mem {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.mem = s₀.mem := vec_mem h.eq
theorem SRel.rd {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.rd = s₀.rd := vec_rd h.eq
theorem SRel.wr {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.wr = s₀.wr := vec_wr h.eq

theorem SRel.init (s₀ : State) : SRel Sym.init s₀ s₀ :=
  ⟨fun r k _ => by simp only [Sym.init, Q.eval, xr_xi], rfl⟩

theorem SRel.set {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) {d : XReg} {t : Q} {s' : State}
    (hv : ∀ r k, k < 8 → qz s' r k = if r = d then t.eval s₀ k else qz s r k)
    (he : vec s₀ s' = s') : SRel (σ.set d t) s₀ s' := by
  refine ⟨fun r k hk => ?_, he⟩
  rw [hv r k hk]
  simp only [Sym.set, xi_inj]
  split
  · rfl
  · exact h.reg r k hk

/-- What the loads may read: 128 bytes at `rsi`, and quadwords of the state
at `rdi`. -/
abbrev Ctx := Avx512.Ctx

theorem sstep_ok {ld : Bool} {s₀ : State} (hc : ld = true → Ctx s₀) {σ σ' : Sym} {s : State}
    (h : SRel σ s₀ s) {i : Instr} (e : σ.step ld i = some σ') : ∃ s', exec i s = some s' ∧ SRel σ' s₀ s' := by
  have hR : ∀ a k, k < 8 → (σ.reg (xi a)).eval s₀ k = qz s a k := fun a k hk => (h.reg a k hk).symm
  unfold Sym.step at e
  split at e
  · rename_i o
    refine ⟨o.exec s, rfl, ?_⟩
    have he := vec_zop h.eq o
    unfold Sym.zop at e
    split at e
    · rename_i op d a b
      unfold Sym.zbin at e
      split at e
      · cases e
        refine h.set (hv_of (fun k hk => ?_) (fun r hr k hk => by rw [qz_zbin _ _ _ _ _ _ hk, ite_eq_right hr])) he
        rw [qz_zbin _ _ _ _ _ _ hk, ite_eq_left rfl]; simp only [ZBinOp.sse, Q.eval]
        rw [qword_paddq _ _ (mod2_lt k), qz_lane, qz_lane, hR a k hk, hR b k hk]
      · cases e
        refine h.set (hv_of (fun k hk => ?_) (fun r hr k hk => by rw [qz_zbin _ _ _ _ _ _ hk, ite_eq_right hr])) he
        rw [qz_zbin _ _ _ _ _ _ hk, ite_eq_left rfl]; simp only [ZBinOp.sse, Q.eval]
        rw [XBinOp.eval, qword_and, qz_lane, qz_lane, hR a k hk, hR b k hk]
      · cases e
        refine h.set (hv_of (fun k hk => ?_) (fun r hr k hk => by rw [qz_zbin _ _ _ _ _ _ hk, ite_eq_right hr])) he
        rw [qz_zbin _ _ _ _ _ _ hk, ite_eq_left rfl]; simp only [ZBinOp.sse, Q.eval]
        rw [XBinOp.eval, qword_or, qz_lane, qz_lane, hR a k hk, hR b k hk]
      · cases e
        refine h.set (hv_of (fun k hk => ?_) (fun r hr k hk => by rw [qz_zbin _ _ _ _ _ _ hk, ite_eq_right hr])) he
        rw [qz_zbin _ _ _ _ _ _ hk, ite_eq_left rfl]; simp only [ZBinOp.sse, Q.eval]
        rw [qword_punpcklqdq _ _ (mod2_lt k)]
        split
        · rename_i h0; rw [hR a k hk, qz, h0]
        · rw [hR b (k - 1) (by omega_using [hk]), qz, show (k - 1) / 2 = k / 2 by omega_arith,
            show (k - 1) % 2 = 0 by omega_arith]
      · cases e
        refine h.set (hv_of (fun k hk => ?_) (fun r hr k hk => by rw [qz_zbin _ _ _ _ _ _ hk, ite_eq_right hr])) he
        rw [qz_zbin _ _ _ _ _ _ hk, ite_eq_left rfl]; simp only [ZBinOp.sse, Q.eval]
        rw [qword_punpckhqdq _ _ (mod2_lt k)]
        split
        · rw [hR a (k + 1) (by omega_arith), qz, show (k + 1) / 2 = k / 2 by omega_arith,
            show (k + 1) % 2 = 1 by omega_arith]
        · rw [hR b k hk, qz, show k % 2 = 1 by omega_arith]
      · split at e
        · rename_i hab
          cases e; subst hab
          refine h.set (hv_of (fun k hk => ?_) (fun r hr k hk => by rw [qz_zbin _ _ _ _ _ _ hk, ite_eq_right hr])) he
          rw [qz_zbin _ _ _ _ _ _ hk, ite_eq_left rfl]; simp only [ZBinOp.sse, Q.eval]
          exact qword_pxor_self _ _
        · cases e
      · cases e
    · rename_i op d a n
      split at e
      · rename_i hn
        split at e <;> cases e <;>
          refine h.set (hv_of (fun k hk => ?_)
            (fun r hr k hk => by rw [qz_vshift _ _ _ _ _ _ hk, ite_eq_right hr])) he <;>
          rw [qz_vshift _ _ _ _ _ _ hk, ite_eq_left rfl] <;> simp only [ZShiftOp.sse, Q.eval]
        · rw [qword_psllq _ hn (mod2_lt k), qz_lane, hR a k hk]
        · rw [qword_psrlq _ hn (mod2_lt k), qz_lane, hR a k hk]
      · cases e
    · rename_i d a
      cases e
      exact h.set (hv_of (fun k hk => by rw [qz_vmovdqa64 _ _ _ _ hk, ite_eq_left rfl, hR a k hk])
        (fun r hr k hk => by rw [qz_vmovdqa64 _ _ _ _ hk, ite_eq_right hr])) he
    · rename_i d a
      cases e
      exact h.set (hv_of (fun k hk => by
          rw [qz_vpbroadcastq _ _ _ _ hk, ite_eq_left rfl]; exact (hR a 0 (by decide)).symm)
        (fun r hr k hk => by rw [qz_vpbroadcastq _ _ _ _ hk, ite_eq_right hr])) he
    · rename_i d a b n
      cases e
      exact h.set (hv_of (fun k hk => by
          rw [qz_vshufi32x4 _ _ _ _ _ _ hk, ite_eq_left rfl]; simp only [Q.eval, shufIdx]
          split
          · exact (hR a _ (shufIdx_lt _ _)).symm
          · exact (hR b _ (shufIdx_lt _ _)).symm)
        (fun r hr k hk => by rw [qz_vshufi32x4 _ _ _ _ _ _ hk, ite_eq_right hr])) he
    · rename_i hb d a b
      cases e
      exact h.set (hv_of (fun k hk => by
          rw [qz_vpmadd52 _ _ _ _ _ _ hk, ite_eq_left rfl]; simp only [Q.eval, hR d k hk, hR a k hk, hR b k hk])
        (fun r hr k hk => by rw [qz_vpmadd52 _ _ _ _ _ _ hk, ite_eq_right hr])) he
    · cases e
  · rename_i d g
    cases e
    refine ⟨(VOp.vmovq d g).exec s, rfl, ?_⟩
    exact h.set (hv_of (fun k hk => by rw [qz_vmovq _ _ _ _ hk, ite_eq_left rfl]; simp only [Q.eval, h.gpr])
      (fun r hr k hk => by rw [qz_vmovq _ _ _ _ hk, ite_eq_right hr])) (by
        rw [← h.eq]; rfl)
  · rename_i d m
    split at e
    case isFalse => cases e
    rename_i hld
    obtain ⟨i, hs, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨hi, hea⟩ := ldIdx_ok hs
    have ea : s.ea m = s₀.gpr .rsi + BitVec.ofNat 64 (8 * i) := by rw [hea, h.gpr]
    have hin : InRegions (s.rd ++ s.wr) (s₀.gpr .rsi + BitVec.ofNat 64 (8 * i)) 64 := by
      rw [h.rd, h.wr]; exact (hc hld).ld i hi
    let v := s.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * i)) 512
    refine ⟨s.setZ d (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
      (v.extractLsb' 384 128), by simp only [exec, ea, State.load512, hin, ite_true, Option.map_some, v], ?_⟩
    refine h.set (hv_of (fun k hk => ?_) (fun r hr k hk => by rw [qz_load _ _ _ _ hk, ite_eq_right hr]))
      (vec_setZ h.eq _ _ _ _ _)
    rw [qz_load _ _ _ _ hk, ite_eq_left rfl, h.mem, Offset.add_add]; simp only [Q.eval, Nat.mul_add]
  · rename_i op d a m
    split at e
    case isFalse => cases e
    rename_i hld
    obtain ⟨i, hs, e'⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨h₁, h₂, hea⟩ := mbIdx_ok hs
    have ea : s.ea m = s₀.gpr .rdi + BitVec.ofInt 64 (i : Int) := by rw [hea, h.gpr]
    have hin : InRegions (s.rd ++ s.wr) (s₀.gpr .rdi + BitVec.ofInt 64 (i : Int)) 8 := by
      rw [h.rd, h.wr]; exact (hc hld).mb i h₁ h₂
    have hv : s.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 (i : Int)) 64 =
        s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 (i : Int)) 64 := by rw [h.mem]
    let v := s.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 (i : Int)) 64
    have hv' : v = s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 (i : Int)) 64 := hv
    refine ⟨s.setZ d (op.sse.eval (s.zlane a 0) (v ++ v)) (op.sse.eval (s.zlane a 1) (v ++ v))
      (op.sse.eval (s.zlane a 2) (v ++ v)) (op.sse.eval (s.zlane a 3) (v ++ v)),
      by simp only [exec, ea, State.load64, hin, ite_true, Option.map_some, v], ?_⟩
    have he := vec_setZ h.eq d (op.sse.eval (s.zlane a 0) (v ++ v)) (op.sse.eval (s.zlane a 1) (v ++ v))
      (op.sse.eval (s.zlane a 2) (v ++ v)) (op.sse.eval (s.zlane a 3) (v ++ v))
    cases op <;> simp only [Sym.bcst] at e' <;> cases e' <;>
      refine h.set (hv_of (fun k hk => ?_) (fun r hr k hk => by rw [qz_bcst _ _ _ _ _ _ hk, ite_eq_right hr]))
        he <;>
      rw [qz_bcst _ _ _ _ _ _ hk, ite_eq_left rfl] <;> simp only [ZBcstOp.sse, Q.eval]
    · rw [XBinOp.eval, qword_and, qz_lane, hR a k hk, qword_vv _ (mod2_lt k), hv']
    · rw [XBinOp.eval, qword_or, qz_lane, hR a k hk, qword_vv _ (mod2_lt k), hv']
  · cases e

/-- A block of instructions. -/
theorem srun_ok {ld : Bool} {s₀ : State} (hc : ld = true → Ctx s₀) :
    ∀ (is : List Instr) {σ σ' : Sym} {s : State}, SRel σ s₀ s → σ.run ld is = some σ' →
      WP isa (.block is) s (SRel σ' s₀)
  | [], _, _, _, h, e => by cases e; exact WP.block_nil h
  | i :: is, _, _, _, h, e => by
    simp only [Sym.run, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    obtain ⟨s₁, hx, h₁⟩ := sstep_ok hc h e₁
    exact WP.block_cons_iff.2 ⟨s₁, hx, srun_ok hc is h₁ e₂⟩

/-- A block from its start. -/
theorem run_ok {ld : Bool} {s₀ : State} (hc : ld = true → Ctx s₀) {is : List Instr} {σ : Sym}
    (e : Sym.init.run ld is = some σ) : WP isa (.block is) s₀ (SRel σ s₀) :=
  srun_ok hc is (SRel.init s₀) e

end VG.Proof.Poly1305.X86_64.Ifma

end

end

/-! ### `Poly1305.Limbs44`, which only this module used -/

section

/-!
# Poly1305 in 44-bit limbs

The arithmetic of vector implementations that keep numbers modulo `p` in
three limbs of 44 bits (`x₀ + 2⁴⁴ x₁ + 2⁸⁸ x₂`) and multiply them with 52-bit
multiply-adds (`vpmadd52luq`, `vpmadd52huq`): the low and high sums of the
limbs' products, with the terms past `2¹³⁰` taken from twenty times the
multiplier's limbs; the high sums folded into the low ones; and the carrying.
Each function sums in the order the code does, so that the terms the code
computes are these functions by definition.
-/

@[expose] public section

namespace VG.Proof.Poly1305.Limbs44

open VG.Spec.Poly1305 (P)

/-- The number whose limbs are `a 0`, `a 1` and `a 2` (of any size). -/
def val (a : Nat → Nat) : Nat := a 0 + 2 ^ 44 * a 1 + 2 ^ 88 * a 2

theorem P_eq : P = 1361129467683753853853498429727072845819 := by decide

/-- The 52-bit part of a product that a multiply-add adds: the high half if
`h`, else the low one, of the product of the sources' low 52 bits. -/
def madN (h : Bool) (a b : Nat) : Nat :=
  if h then a % 2 ^ 52 * (b % 2 ^ 52) / 2 ^ 52 else a % 2 ^ 52 * (b % 2 ^ 52) % 2 ^ 52

theorem madN_halves {a b : Nat} (ha : a < 2 ^ 52) (hb : b < 2 ^ 52) :
    madN false a b + 2 ^ 52 * madN true a b = a * b := by
  simp only [madN, Bool.false_eq_true, ite_false, ite_true, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact Nat.mod_add_div _ _

/-! ## Products -/

section
variable (a b c : Nat → Nat) (h : Bool)

/-- The halves `h` of the products of limb `j`, summed as the code does:
`a₀ b₀ + a₁ c₂ + a₂ c₁`, `a₀ b₁ + a₁ b₀ + a₂ c₂` and `a₀ b₂ + a₁ b₁ + a₂ b₀`,
with `c = 20 b` standing for the terms past `2¹³⁰` (`2¹³² ≡ 20`). -/
def ps : Nat → Nat
  | 0 => 0 + madN h (a 0) (b 0) + madN h (a 1) (c 2) + madN h (a 2) (c 1)
  | 1 => 0 + madN h (a 0) (b 1) + madN h (a 1) (b 0) + madN h (a 2) (c 2)
  | _ => 0 + madN h (a 0) (b 2) + madN h (a 1) (b 1) + madN h (a 2) (b 0)

/-- The high sums folded into the low ones: `u₀ 2⁸` into `l₁`, `u₁ 2⁸` into
`l₂` and `u₂ 5 · 2¹⁰ = u₂ 2¹² + u₂ 2¹⁰` into `l₀`. -/
def pf : Nat → Nat
  | 0 => ps a b c false 0 + ps a b c true 2 * 2 ^ 12 + ps a b c true 2 * 2 ^ 10
  | 1 => ps a b c false 1 + ps a b c true 0 * 2 ^ 8
  | _ => ps a b c false 2 + ps a b c true 1 * 2 ^ 8

end

theorem pf_val {a b c : Nat → Nat} (ha : ∀ i < 3, a i < 2 ^ 52) (hb : ∀ i < 3, b i < 2 ^ 52)
    (hc : ∀ i < 3, c i < 2 ^ 52) (c1 : c 1 = 20 * b 1) (c2 : c 2 = 20 * b 2) :
    val (pf a b c) + P * (4 * (a 1 * b 2 + a 2 * b 1 + 2 ^ 44 * (a 2 * b 2)) +
      2 ^ 10 * ps a b c true 2) = val a * val b := by
  have m : ∀ i < 3, ∀ j < 3, madN false (a i) (b j) + 2 ^ 52 * madN true (a i) (b j) = a i * b j :=
    fun i hi j hj => madN_halves (ha i hi) (hb j hj)
  have n : ∀ i < 3, ∀ j < 3, madN false (a i) (c j) + 2 ^ 52 * madN true (a i) (c j) = a i * c j :=
    fun i hi j hj => madN_halves (ha i hi) (hc j hj)
  have m00 := m 0 (by decide) 0 (by decide)
  have m01 := m 0 (by decide) 1 (by decide)
  have m02 := m 0 (by decide) 2 (by decide)
  have m10 := m 1 (by decide) 0 (by decide)
  have m11 := m 1 (by decide) 1 (by decide)
  have m20 := m 2 (by decide) 0 (by decide)
  have n12 := n 1 (by decide) 2 (by decide)
  have n21 := n 2 (by decide) 1 (by decide)
  have n22 := n 2 (by decide) 2 (by decide)
  simp only [c1, c2] at n12 n21 n22
  simp only [val, pf, ps, P_eq, c1, c2]
  grind

/-! ## Carrying -/

section
variable (f : Nat → Nat)

/-- The limbs carried from `f₀` up: `e₁ = f₁ + f₀ / 2⁴⁴`, `e₂ = f₂ + e₁ / 2⁴⁴`. -/
def e1 : Nat := f 1 + f 0 / 2 ^ 44
def e2 : Nat := f 2 + e1 f / 2 ^ 44
/-- `e₂`'s carry, times 20 (`c 2⁴ + c 2²`), added to `f₀`'s low bits. -/
def g0 (M : Nat) : Nat := (f 0 &&& M) + e2 f / 2 ^ 44 * 2 ^ 4 + e2 f / 2 ^ 44 * 2 ^ 2

/-- The limbs after carrying, with the mask `M = 2⁴⁴ - 1`. -/
def carry (M : Nat) : Nat → Nat
  | 0 => g0 f M &&& M
  | 1 => (e1 f &&& M) + g0 f M / 2 ^ 44
  | _ => e2 f &&& M

end

theorem and_mask (x : Nat) : x &&& 0xfffffffffff = x % 2 ^ 44 := by
  rw [show (0xfffffffffff : Nat) = 2 ^ 44 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

theorem carry_val (f : Nat → Nat) : val (carry f 0xfffffffffff) + P * (4 * (e2 f / 2 ^ 44)) = val f := by
  simp only [val, carry, g0, e2, e1, and_mask, P_eq]
  omega_arith

/-- The product of `a` and `b`, with `c = 20 b` for limbs 1 and 2, carried. -/
def mul (a b c : Nat → Nat) : Nat → Nat := carry (pf a b c) 0xfffffffffff

theorem mul_mod {a b c : Nat → Nat} (ha : ∀ i < 3, a i < 2 ^ 52) (hb : ∀ i < 3, b i < 2 ^ 52)
    (hc : ∀ i < 3, c i < 2 ^ 52) (c1 : c 1 = 20 * b 1) (c2 : c 2 = 20 * b 2) :
    val (mul a b c) % P = val a * val b % P := by
  have h₁ := carry_val (pf a b c)
  have h₂ := pf_val ha hb hc c1 c2
  rw [← h₂, ← h₁, Nat.add_assoc, ← Nat.mul_add, Nat.add_mul_mod_self_left, mul]

/-! ## Splitting words into limbs

The limbs of `lo + 2⁶⁴ hi + 2¹²⁸ t` (`lo, hi < 2⁶⁴`), as the code splits
them, are `lo & M`, `(lo >> 44 | hi << 20) & M` and `hi >> 24 | t << 40`
(for a block, `t = 1`, its pad bit). -/

theorem split1 {lo : Nat} (hlo : lo < 2 ^ 64) (hi : Nat) :
    ((lo / 2 ^ 44 ||| hi * 2 ^ 20 % 2 ^ 64) &&& 0xfffffffffff) = lo / 2 ^ 44 + 2 ^ 20 * (hi % 2 ^ 24) := by
  rw [show hi * 2 ^ 20 % 2 ^ 64 = 2 ^ 20 * (hi % 2 ^ 44) by omega_arith, Nat.or_comm,
    ← Nat.two_pow_add_eq_or_of_lt (show lo / 2 ^ 44 < 2 ^ 20 by omega_arith), and_mask]
  omega_arith

theorem split2 {hi : Nat} (hhi : hi < 2 ^ 64) (t : Nat) :
    (hi / 2 ^ 24 ||| t * 2 ^ 40 % 2 ^ 64) = 2 ^ 40 * (t % 2 ^ 24) + hi / 2 ^ 24 := by
  rw [show t * 2 ^ 40 % 2 ^ 64 = 2 ^ 40 * (t % 2 ^ 24) by omega_arith, Nat.or_comm,
    ← Nat.two_pow_add_eq_or_of_lt (show hi / 2 ^ 24 < 2 ^ 40 by omega_arith)]

theorem split_pad {hi : Nat} (hhi : hi < 2 ^ 64) : (hi / 2 ^ 24 ||| 0x10000000000) = 2 ^ 40 + hi / 2 ^ 24 := by
  have := split2 hhi 1
  rwa [show 1 * 2 ^ 40 % 2 ^ 64 = 0x10000000000 by decide, show 1 % 2 ^ 24 = 1 by decide, Nat.mul_one] at this

theorem split_val (lo hi t : Nat) :
    lo % 2 ^ 44 + 2 ^ 44 * (lo / 2 ^ 44 + 2 ^ 20 * (hi % 2 ^ 24)) + 2 ^ 88 * (2 ^ 40 * t + hi / 2 ^ 24) =
      lo + 2 ^ 64 * hi + 2 ^ 128 * t := by
  omega_arith

end VG.Proof.Poly1305.Limbs44

end

end

/-!
# Poly1305 on x86-64 with AVX-512 IFMA: terms as numbers

As for AVX-512 (`Avx512/Bound.lean`): the limbs the code computes stay far
below `2⁶⁴`, so its additions and left shifts never wrap. `Q.bnd` bounds each
term from bounds on the registers it starts from, `Q.ok` checks that its
additions (those of `vpmadd52luq` and `vpmadd52huq` included) and left shifts
do not wrap under those bounds, and `Q.nat` is its value as a number. A
multiply-add takes the low 52 bits of its sources (`% 2⁵²` in `Q.nat`), and
adds the low (or high) 52 bits of their product. `nat_ok` proves that a term
is `Q.nat` and within `Q.bnd` where the kernel evaluates `Q.ok` of concrete
terms to `true`; `Q.natw` is the value with every reduction kept, exact for
any term (`natw_ok`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Ifma

open VG VG.X86_64
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi capW orB capW_ge orB_ge)
open VG.Proof.Poly1305.X86_64.Avx512 (qz shufIdx shufIdx_lt)
open VG.Proof.X25519.X86_64.Ifma (mad52 mad52_toNat)
open VG.Proof.Poly1305.Limbs44 (madN)

/-- Bounds on the registers a block starts from: on each vector register's
quadwords (`v`), on the general-purpose registers, and on the quadwords of
memory at `rdi + d` (`mb`). -/
structure Bnds where
  v : XReg → Nat
  g : Reg → Nat
  mb : Nat → Nat

/-- The values a block starts from, as numbers. -/
abbrev Env := Avx512.Env
abbrev envOf := Avx512.envOf

/-- A bound on `madN h a b` from bounds on `a` and `b`. -/
def madB (h : Bool) (a b : Nat) : Nat :=
  if h then min a (2 ^ 52 - 1) * min b (2 ^ 52 - 1) / 2 ^ 52
  else min (min a (2 ^ 52 - 1) * min b (2 ^ 52 - 1)) (2 ^ 52 - 1)

theorem madN_le {h : Bool} {a b A B : Nat} (ha : a ≤ A) (hb : b ≤ B) : madN h a b ≤ madB h A B := by
  have a1 : a % 2 ^ 52 ≤ min A (2 ^ 52 - 1) :=
    Nat.le_min.2 ⟨Nat.le_trans (Nat.mod_le _ _) ha, Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  have b1 : b % 2 ^ 52 ≤ min B (2 ^ 52 - 1) :=
    Nat.le_min.2 ⟨Nat.le_trans (Nat.mod_le _ _) hb, Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  have p := Nat.mul_le_mul a1 b1
  cases h
  · simp only [madN, madB, Bool.false_eq_true, ite_false]
    exact Nat.le_min.2 ⟨Nat.le_trans (Nat.mod_le _ _) p, Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  · simp only [madN, madB, ite_true]
    exact Nat.div_le_div_right p

def Q.bnd (B : Bnds) : Q → Nat → Nat
  | .reg r, _ => min (B.v (xr r)) (2 ^ 64 - 1)
  | .gpr g, _ => min (B.g g) (2 ^ 64 - 1)
  | .lane0 a, k => if k = 0 then a.bnd B 0 else 0
  | .bc a, _ => a.bnd B 0
  | .ld _, _ => 2 ^ 64 - 1
  | .mb d, _ => min (B.mb d) (2 ^ 64 - 1)
  | .zero, _ => 0
  | .add a b, k => capW (a.bnd B k + b.bnd B k)
  | .and a b, k => min (a.bnd B k) (b.bnd B k)
  | .or a b, k => orB (a.bnd B k) (b.bnd B k)
  | .shl a n, k => capW (a.bnd B k * 2 ^ n)
  | .shr a n, k => a.bnd B k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.bnd B k else b.bnd B (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.bnd B (k + 1) else b.bnd B k
  | .shuf a b sel, k => if k / 2 < 2 then a.bnd B (shufIdx sel k) else b.bnd B (shufIdx sel k)
  | .mad h c a b, k => capW (c.bnd B k + madB h (a.bnd B k) (b.bnd B k))

/-- The value of a term as a number, with no reductions modulo `2⁶⁴`: what
the code computes where `Q.ok` holds. -/
def Q.nat (E : Env) : Q → Nat → Nat
  | .reg r, k => E.v r k
  | .gpr g, _ => E.g g
  | .lane0 a, k => if k = 0 then a.nat E 0 else 0
  | .bc a, _ => a.nat E 0
  | .ld i, k => E.m (i + k)
  | .mb d, _ => E.mb d
  | .zero, _ => 0
  | .add a b, k => a.nat E k + b.nat E k
  | .and a b, k => a.nat E k &&& b.nat E k
  | .or a b, k => a.nat E k ||| b.nat E k
  | .shl a n, k => a.nat E k * 2 ^ n
  | .shr a n, k => a.nat E k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.nat E k else b.nat E (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.nat E (k + 1) else b.nat E k
  | .shuf a b sel, k => if k / 2 < 2 then a.nat E (shufIdx sel k) else b.nat E (shufIdx sel k)
  | .mad h c a b, k => c.nat E k + madN h (a.nat E k) (b.nat E k)

/-- The value of a term as a number, reduced as the code does: exact
whatever the bounds (`natw_ok`). -/
def Q.natw (E : Env) : Q → Nat → Nat
  | .reg r, k => E.v r k
  | .gpr g, _ => E.g g
  | .lane0 a, k => if k = 0 then a.natw E 0 else 0
  | .bc a, _ => a.natw E 0
  | .ld i, k => E.m (i + k)
  | .mb d, _ => E.mb d
  | .zero, _ => 0
  | .add a b, k => (a.natw E k + b.natw E k) % 2 ^ 64
  | .and a b, k => a.natw E k &&& b.natw E k
  | .or a b, k => a.natw E k ||| b.natw E k
  | .shl a n, k => a.natw E k * 2 ^ n % 2 ^ 64
  | .shr a n, k => a.natw E k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.natw E k else b.natw E (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.natw E (k + 1) else b.natw E k
  | .shuf a b sel, k => if k / 2 < 2 then a.natw E (shufIdx sel k) else b.natw E (shufIdx sel k)
  | .mad h c a b, k => (c.natw E k + madN h (a.natw E k) (b.natw E k)) % 2 ^ 64

/-- No addition or left shift in `t` wraps, by the bounds `B`. -/
def Q.ok (B : Bnds) : Q → Nat → Bool
  | .reg _, _ | .gpr _, _ | .ld _, _ | .mb _, _ | .zero, _ => true
  | .lane0 a, k => if k = 0 then a.ok B 0 else true
  | .bc a, _ => a.ok B 0
  | .add a b, k => a.bnd B k + b.bnd B k < 2 ^ 64 && a.ok B k && b.ok B k
  | .and a b, k | .or a b, k => a.ok B k && b.ok B k
  | .shl a n, k => a.bnd B k * 2 ^ n < 2 ^ 64 && a.ok B k
  | .shr a _, k => a.ok B k
  | .unpl a b, k => if k % 2 = 0 then a.ok B k else b.ok B (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.ok B (k + 1) else b.ok B k
  | .shuf a b sel, k => if k / 2 < 2 then a.ok B (shufIdx sel k) else b.ok B (shufIdx sel k)
  | .mad h c a b, k =>
    c.bnd B k + madB h (a.bnd B k) (b.bnd B k) < 2 ^ 64 && c.ok B k && a.ok B k && b.ok B k

/-- The registers `s₀` starts from are within `B`. -/
structure EnvOK (s₀ : State) (B : Bnds) : Prop where
  v : ∀ r k, k < 8 → (qz s₀ r k).toNat ≤ B.v r
  g : ∀ g, (s₀.gpr g).toNat ≤ B.g g
  mb : ∀ d : Nat, (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 (d : Int)) 64).toNat ≤ B.mb d

theorem mad52_nat (h : Bool) (c a b : BitVec 64) :
    (mad52 h c a b).toNat = (c.toNat + madN h a.toNat b.toNat) % 2 ^ 64 := by
  rw [mad52_toNat]; cases h <;> rfl

theorem nat_ok {s₀ : State} {B : Bnds} (hE : EnvOK s₀ B) :
    ∀ (t : Q) {k : Nat}, k < 8 → t.ok B k = true →
      (t.eval s₀ k).toNat = t.nat (envOf s₀) k ∧ (t.eval s₀ k).toNat ≤ t.bnd B k := by
  intro t
  induction t with
  | reg r =>
    intro k hk _
    exact ⟨rfl, Nat.le_min.2 ⟨hE.v (xr r) k hk, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩⟩
  | gpr g =>
    intro k _ _
    exact ⟨rfl, Nat.le_min.2 ⟨hE.g g, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩⟩
  | lane0 a ih =>
    intro k _ ho
    simp only [Q.eval, Q.nat, Q.bnd, Q.ok] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact ih (by decide) ho
    · simp
  | bc a ih =>
    intro k _ ho
    exact ih (by decide) ho
  | ld i =>
    intro k _ _
    refine ⟨?_, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩
    simp only [Q.eval, Q.nat, envOf, Avx512.envOf, Nat.mul_add]
  | mb d =>
    intro k _ _
    exact ⟨rfl, Nat.le_min.2 ⟨hE.mb d, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩⟩
  | zero =>
    intro k _ _
    exact ⟨rfl, Nat.le_refl _⟩
  | add a b iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨⟨hs, oa⟩, ob⟩ := ho
    obtain ⟨ea, ba⟩ := iha hk oa
    obtain ⟨eb, bb⟩ := ihb hk ob
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_add]
    rw [← ea, ← eb]
    have := BitVec.isLt (a.eval s₀ k + b.eval s₀ k)
    rw [BitVec.toNat_add] at this
    exact ⟨Nat.mod_eq_of_lt (by omega_using [hs, ba, bb]), capW_ge (by rw [Nat.mod_eq_of_lt (by omega_using [hs, ba, bb])]; omega_using [ba, bb]) this⟩
  | and a b iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba⟩ := iha hk ho.1
    obtain ⟨eb, bb⟩ := ihb hk ho.2
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_and]
    rw [← ea, ← eb]
    exact ⟨rfl, Nat.le_min.2 ⟨Nat.le_trans Nat.and_le_left ba, Nat.le_trans Nat.and_le_right bb⟩⟩
  | or a b iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba⟩ := iha hk ho.1
    obtain ⟨eb, bb⟩ := ihb hk ho.2
    have := BitVec.isLt (a.eval s₀ k ||| b.eval s₀ k)
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_or] at this ⊢
    rw [← ea, ← eb]
    exact ⟨rfl, orB_ge ba bb this⟩
  | shl a n ih =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨ea, ba⟩ := ih hk ho.2
    have := BitVec.isLt (a.eval s₀ k <<< n)
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at this ⊢
    rw [← ea]
    have hm := Nat.mul_le_mul_right (2 ^ n) ba
    exact ⟨Nat.mod_eq_of_lt (by omega), capW_ge (by rw [Nat.mod_eq_of_lt (by omega)]; omega_using [hm]) this⟩
  | shr a n ih =>
    intro k hk ho
    obtain ⟨ea, ba⟩ := ih hk ho
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [← ea]
    exact ⟨rfl, Nat.div_le_div_right ba⟩
  | unpl a b iha ihb =>
    intro k hk ho
    simp only [Q.eval, Q.nat, Q.bnd, Q.ok] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact iha hk ho
    · rename_i h; rw [ite_eq_right h] at ho; exact ihb (by omega_using [hk]) ho
  | unph a b iha ihb =>
    intro k hk ho
    simp only [Q.eval, Q.nat, Q.bnd, Q.ok] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact iha (by omega_using [hk, h]) ho
    · rename_i h; rw [ite_eq_right h] at ho; exact ihb hk ho
  | shuf a b sel iha ihb =>
    intro k _ ho
    simp only [Q.eval, Q.nat, Q.bnd, Q.ok] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact iha (shufIdx_lt _ _) ho
    · rename_i h; rw [ite_eq_right h] at ho; exact ihb (shufIdx_lt _ _) ho
  | mad h c a b ihc iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨⟨⟨hs, oc⟩, oa⟩, ob⟩ := ho
    obtain ⟨ec, bc⟩ := ihc hk oc
    obtain ⟨ea, ba⟩ := iha hk oa
    obtain ⟨eb, bb⟩ := ihb hk ob
    have hm := madN_le (h := h) ba bb
    simp only [Q.eval, Q.nat, Q.bnd, mad52_nat]
    rw [← ec, ← ea, ← eb]
    have hlt : (c.eval s₀ k).toNat + madN h (a.eval s₀ k).toNat (b.eval s₀ k).toNat < 2 ^ 64 := by omega_using [hs, bc, hm]
    rw [Nat.mod_eq_of_lt hlt]
    exact ⟨rfl, capW_ge (by omega_using [bc, hm]) hlt⟩

theorem natw_ok (s₀ : State) : ∀ (t : Q) (k : Nat), (t.eval s₀ k).toNat = t.natw (envOf s₀) k := by
  intro t
  induction t with
  | reg r => intro k; rfl
  | gpr g => intro k; rfl
  | lane0 a ih =>
    intro k
    simp only [Q.eval, Q.natw]
    split
    · exact ih 0
    · rfl
  | bc a ih => intro k; exact ih 0
  | ld i => intro k; simp only [Q.eval, Q.natw, envOf, Avx512.envOf, Nat.mul_add]
  | mb d => intro k; rfl
  | zero => intro k; rfl
  | add a b iha ihb => intro k; simp only [Q.eval, Q.natw, BitVec.toNat_add, iha, ihb]
  | and a b iha ihb => intro k; simp only [Q.eval, Q.natw, BitVec.toNat_and, iha, ihb]
  | or a b iha ihb => intro k; simp only [Q.eval, Q.natw, BitVec.toNat_or, iha, ihb]
  | shl a n ih =>
    intro k; simp only [Q.eval, Q.natw, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, ih]
  | shr a n ih =>
    intro k; simp only [Q.eval, Q.natw, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ih]
  | unpl a b iha ihb =>
    intro k; simp only [Q.eval, Q.natw]; split
    · exact iha k
    · exact ihb _
  | unph a b iha ihb =>
    intro k; simp only [Q.eval, Q.natw]; split
    · exact iha _
    · exact ihb k
  | shuf a b sel iha ihb =>
    intro k; simp only [Q.eval, Q.natw]; split
    · exact iha _
    · exact ihb _
  | mad h c a b ihc iha ihb => intro k; simp only [Q.eval, Q.natw, mad52_nat, ihc, iha, ihb]

theorem SRel.nat {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) {B : Bnds} (hE : EnvOK s₀ B) {r : XReg}
    {k : Nat} (hk : k < 8) (ho : (σ.reg (xi r)).ok B k = true) :
    (qz s r k).toNat = (σ.reg (xi r)).nat (envOf s₀) k ∧ (qz s r k).toNat ≤ (σ.reg (xi r)).bnd B k := by
  rw [h.reg r k hk]; exact nat_ok hE _ hk ho

theorem SRel.natw {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) (r : XReg) {k : Nat} (hk : k < 8) :
    (qz s r k).toNat = (σ.reg (xi r)).natw (envOf s₀) k := by
  rw [h.reg r k hk]; exact natw_ok s₀ _ k

end VG.Proof.Poly1305.X86_64.Ifma

end

end

/-!
# Poly1305 on x86-64 with AVX-512 IFMA: the product

`mul` multiplies the eight quadwords of the accumulator `H` by those of `Y`,
with `S` twenty times limbs 1 and 2 of `Y`, and carries: `Limbs44.mul`, with
the limbs small enough that nothing wraps and the multiply-adds take them
whole.
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Ifma
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec)
open VG.Proof.Poly1305.X86_64.Avx512 (qz envOf_v)

/-- Limb `i` of quadword `k` of `H`, of `Y` and of `S`. -/
def hv (s : State) (k i : Nat) : Nat := (qz s (hreg i) k).toNat
def yv (s : State) (k i : Nat) : Nat := (qz s (yreg i) k).toNat
def sv (s : State) (k i : Nat) : Nat := (qz s (sreg i) k).toNat

def mulB : Bnds :=
  ⟨fun r => match r with
    | .xmm0 | .xmm1 | .xmm2 => 2 ^ 45
    | .xmm3 | .xmm4 | .xmm5 => 2 ^ 44
    | .xmm6 | .xmm7 => 20 * 2 ^ 44
    | _ => 2 ^ 64 - 1,
   fun _ => 2 ^ 64 - 1,
   fun d => if d = 104 then 2 ^ 44 - 1 else 2 ^ 64 - 1⟩

def mulS : Sym := (Sym.init.run true mul).get (by decide +kernel)

theorem mulS_eq : Sym.init.run true mul = some mulS := (Option.some_get _).symm

theorem mulS_ok : ∀ i < 3, ∀ k < 8,
    (mulS.reg (xi (hreg i))).ok mulB k = true ∧ (mulS.reg (xi (hreg i))).bnd mulB k ≤ 2 ^ 44 := by
  decide +kernel

theorem mulS_y : ∀ i < 3, mulS.reg (xi (yreg i)) = .reg (xi (yreg i)) ∧
    mulS.reg (xi (sreg i)) = .reg (xi (sreg i)) := by
  decide +kernel

/-- The limbs `mul` computes, from the registers and memory it starts with. -/
theorem mulS_nat (E : Env) (k : Nat) : ∀ i < 3, (mulS.reg (xi (hreg i))).nat E k =
    Limbs44.carry (Limbs44.pf (fun i => E.v (xi (hreg i)) k) (fun i => E.v (xi (yreg i)) k)
      (fun i => E.v (xi (sreg i)) k)) (E.mb 104) i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl

/-- What `mul` needs: `H` below `2⁴⁵`, `Y` at most `2⁴⁴`, `S` twenty times
limbs 1 and 2 of `Y`, and the mask in the state. -/
structure MulPre (s : State) : Prop where
  ctx : Ctx s
  mask : (envOf s).mb 104 = 0xfffffffffff
  h : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 45
  y : ∀ k < 8, ∀ i < 3, yv s k i ≤ 2 ^ 44
  s1 : ∀ k < 8, sv s k 1 = 20 * yv s k 1
  s2 : ∀ k < 8, sv s k 2 = 20 * yv s k 2

theorem MulPre.env {s : State} (hp : MulPre s) : EnvOK s mulB := by
  refine ⟨fun r k hk => ?_, fun _ => Nat.le_sub_one_of_lt (BitVec.isLt _), fun d => ?_⟩
  · have := BitVec.isLt (qz s r k)
    have h0 := hp.h k hk 0 (by decide)
    have h1 := hp.h k hk 1 (by decide)
    have h2 := hp.h k hk 2 (by decide)
    have y0 := hp.y k hk 0 (by decide)
    have y1 := hp.y k hk 1 (by decide)
    have y2 := hp.y k hk 2 (by decide)
    have e1 := hp.s1 k hk
    have e2 := hp.s2 k hk
    simp only [hv, yv, sv, hreg, yreg, sreg] at h0 h1 h2 y0 y1 y2 e1 e2
    cases r <;> simp only [mulB]
    all_goals omega_arith
  · have := BitVec.isLt (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 (d : Int)) 64)
    simp only [mulB]
    split
    · subst d; have := hp.mask; simp only [envOf, Avx512.envOf] at this; rw [this]
    · omega_using []

/-- What `mul` leaves: `H` times `Y`, carried, `Y` and `S` as they were, and
the rest but the sums and scratch registers as they were. -/
structure MulPost (s s' : State) : Prop where
  vec : vec s s' = s'
  y : ∀ i < 3, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k
  sr : ∀ i < 3, ∀ k < 8, qz s' (sreg i) k = qz s (sreg i) k
  h : ∀ k < 8, ∀ i < 3, hv s' k i = Limbs44.mul (hv s k) (yv s k) (sv s k) i
  hb : ∀ k < 8, ∀ i < 3, hv s' k i ≤ 2 ^ 44

theorem mul_ok {s : State} (hp : MulPre s) : WP isa (.block mul) s (MulPost s) := by
  refine WP.mono (run_ok (fun _ => hp.ctx) mulS_eq) fun s' h => ?_
  have hE := hp.env
  refine ⟨h.eq, fun i hi k hk => ?_, fun i hi k hk => ?_, fun k hk i hi => ?_, fun k hk i hi => ?_⟩
  · rw [h.reg _ k hk, (mulS_y i hi).1]; simp only [Q.eval, xr_xi]
  · rw [h.reg _ k hk, (mulS_y i hi).2]; simp only [Q.eval, xr_xi]
  · obtain ⟨e, -⟩ := h.nat hE hk (mulS_ok i hi k hk).1
    simp only [hv] at e ⊢
    rw [e, mulS_nat _ _ i hi, Limbs44.mul, hp.mask]
    simp only [envOf_v]
    rfl
  · obtain ⟨-, b⟩ := h.nat hE hk (mulS_ok i hi k hk).1
    exact Nat.le_trans b (mulS_ok i hi k hk).2

/-- `mul` modulo `p`. -/
theorem MulPre.mul_mod {s : State} (hp : MulPre s) {k : Nat} (hk : k < 8) :
    Limbs44.val (Limbs44.mul (hv s k) (yv s k) (sv s k)) % Spec.Poly1305.P =
      Limbs44.val (hv s k) * Limbs44.val (yv s k) % Spec.Poly1305.P := by
  refine Limbs44.mul_mod (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) (hp.s1 k hk) (hp.s2 k hk)
  · exact Nat.lt_of_le_of_lt (hp.h k hk i hi) (by decide)
  · exact Nat.lt_of_le_of_lt (hp.y k hk i hi) (by decide)
  · have y1 := hp.y k hk 1 (by decide)
    have y2 := hp.y k hk 2 (by decide)
    have e1 := hp.s1 k hk
    have e2 := hp.s2 k hk
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · have : sv s k 0 = sv s k 2 := rfl
      omega_using [y2, e2, this]
    · omega_using [y1, e1]
    · omega_using [y2, e2]

end VG.Proof.Poly1305.X86_64.Ifma
