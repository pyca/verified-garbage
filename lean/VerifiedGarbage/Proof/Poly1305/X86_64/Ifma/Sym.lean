module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Sym
public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Sym
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block

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
        · rw [hR b (k - 1) (by omega), qz, show (k - 1) / 2 = k / 2 by omega,
            show (k - 1) % 2 = 0 by omega]
      · cases e
        refine h.set (hv_of (fun k hk => ?_) (fun r hr k hk => by rw [qz_zbin _ _ _ _ _ _ hk, ite_eq_right hr])) he
        rw [qz_zbin _ _ _ _ _ _ hk, ite_eq_left rfl]; simp only [ZBinOp.sse, Q.eval]
        rw [qword_punpckhqdq _ _ (mod2_lt k)]
        split
        · rw [hR a (k + 1) (by omega), qz, show (k + 1) / 2 = k / 2 by omega,
            show (k + 1) % 2 = 1 by omega]
        · rw [hR b k hk, qz, show k % 2 = 1 by omega]
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
