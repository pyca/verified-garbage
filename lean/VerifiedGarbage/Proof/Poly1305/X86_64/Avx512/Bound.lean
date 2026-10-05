import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Load
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Impl.Poly1305.X86_64.Avx512

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Sym`. -/
section

/-!
# Poly1305 on x86-64 with AVX-512: straight-line code, quadword by quadword

The vector code of `vg_poly1305_blocks_avx512` moves, adds, multiplies, masks,
shifts and shuffles the eight quadwords of `zmm` registers, and loads 128
bytes at `rsi`. As for AVX2 (`Avx2/Sym.lean`), `Sym.run` computes each
quadword after a block of such instructions as a term (`Q`) in the quadwords,
general-purpose registers and memory before it, and `srun_ok` proves the
machine agrees. Every instruction but the loads, `vpunpck{l,h}qdq`,
`vshufi32x4`, `vmovq` and `vpbroadcastq` acts on each quadword on its own, so
a term is evaluated at a quadword `k < 8`. The second source of `vpmuludq`,
`vpandq` and `vporq` may be a quadword of the state at `rdi`, broadcast
(`zbcst`).
-/

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi xi_inj lo32 qword_paddq qword_pmuludq qword_and
  qword_or qword_andn qword_punpcklqdq qword_punpckhqdq qword_psllq qword_psrlq mod2_lt sel4 sel4_lt vec
  vec_gpr vec_mem vec_rd vec_wr vec_trans)

/-! ## Quadwords -/

/-- Quadword `k` (`k < 8`) of `zmm r`. -/
def qz (s : State) (r : XReg) (k : Nat) : BitVec 64 := qword (s.zlane r (k / 2)) (k % 2)

theorem cases8 {k : Nat} (hk : k < 8) :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega

theorem div2_lt {k : Nat} (hk : k < 8) : k / 2 < 4 := by omega

/-- The quadwords of the low 256 bits are those of `Avx2.qw`. -/
theorem qz_qw (s : State) (r : XReg) {k : Nat} (hk : k < 4) : VG.Proof.Poly1305.X86_64.Avx512.qz s r k = Avx2.qw s r k := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.qz, Avx2.qw, State.zlane, show k / 2 < 2 by omega, ite_true]

theorem qz_zbin (op : ZBinOp) (s : State) (d a b r : XReg) {k : Nat} (hk : k < 8) :
    VG.Proof.Poly1305.X86_64.Avx512.qz ((ZOp.zbin op d a b).exec s) r k =
      if r = d then qword (op.sse.eval (s.zlane a (k / 2)) (s.zlane b (k / 2))) (k % 2) else VG.Proof.Poly1305.X86_64.Avx512.qz s r k := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.qz, zlane_zbin _ _ _ _ _ _ (VG.Proof.Poly1305.X86_64.Avx512.div2_lt hk)]
  split <;> rfl

theorem qz_vshift (op : ZShiftOp) (s : State) (d a r : XReg) (n : BitVec 8) {k : Nat} (hk : k < 8) :
    VG.Proof.Poly1305.X86_64.Avx512.qz ((ZOp.vshift op d a n).exec s) r k =
      if r = d then qword (op.sse.eval (s.zlane a (k / 2)) n) (k % 2) else VG.Proof.Poly1305.X86_64.Avx512.qz s r k := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.qz, zlane_vshift _ _ _ _ _ _ (VG.Proof.Poly1305.X86_64.Avx512.div2_lt hk)]
  split <;> rfl

theorem qz_vmovdqa64 (s : State) (d a r : XReg) {k : Nat} (hk : k < 8) :
    VG.Proof.Poly1305.X86_64.Avx512.qz ((ZOp.vmovdqa64 d a).exec s) r k = if r = d then VG.Proof.Poly1305.X86_64.Avx512.qz s a k else VG.Proof.Poly1305.X86_64.Avx512.qz s r k := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.qz, zlane_vmovdqa64 _ _ _ _ (VG.Proof.Poly1305.X86_64.Avx512.div2_lt hk)]
  split <;> rfl

theorem qz_vpbroadcastq (s : State) (d a r : XReg) {k : Nat} (hk : k < 8) :
    VG.Proof.Poly1305.X86_64.Avx512.qz ((ZOp.vpbroadcastq d a).exec s) r k = if r = d then VG.Proof.Poly1305.X86_64.Avx512.qz s a 0 else VG.Proof.Poly1305.X86_64.Avx512.qz s r k := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.qz, zlane_vpbroadcastq _ _ _ _ (VG.Proof.Poly1305.X86_64.Avx512.div2_lt hk)]
  split
  · have : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases this with h | h <;> rw [h] <;> simp [State.zlane, State.lane]
  · rfl

theorem sel4_eq (n : BitVec 8) (i : Nat) : (n.extractLsb' (2 * i) 2).toNat = sel4 n.toNat i := by
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_mul, sel4]

theorem qz_vshufi32x4 (s : State) (d a b r : XReg) (n : BitVec 8) {k : Nat} (hk : k < 8) :
    VG.Proof.Poly1305.X86_64.Avx512.qz ((ZOp.vshufi32x4 d a b n).exec s) r k =
      if r = d then (if k / 2 < 2 then VG.Proof.Poly1305.X86_64.Avx512.qz s a else VG.Proof.Poly1305.X86_64.Avx512.qz s b) (2 * sel4 n.toNat (k / 2) + k % 2)
      else VG.Proof.Poly1305.X86_64.Avx512.qz s r k := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.qz, zlane_vshufi32x4 _ _ _ _ _ _ (VG.Proof.Poly1305.X86_64.Avx512.div2_lt hk)]
  split
  · rw [shuf4Lanes_eq, VG.Proof.Poly1305.X86_64.Avx512.sel4_eq]
    have h1 : (2 * sel4 n.toNat (k / 2) + k % 2) / 2 = sel4 n.toNat (k / 2) := by omega
    have h2 : (2 * sel4 n.toNat (k / 2) + k % 2) % 2 = k % 2 := by omega
    by_cases hl : k / 2 < 2 <;> simp only [hl, ite_true, ite_false, VG.Proof.Poly1305.X86_64.Avx512.qz, h1, h2]
  · rfl

theorem qz_vmovq (s : State) (d r : XReg) (g : Reg) {k : Nat} (hk : k < 8) :
    VG.Proof.Poly1305.X86_64.Avx512.qz ((VOp.vmovq d g).exec s) r k = if r = d then (if k = 0 then s.gpr g else 0) else VG.Proof.Poly1305.X86_64.Avx512.qz s r k := by
  simp only [VOp.exec, VG.Proof.Poly1305.X86_64.Avx512.qz, State.zlane_setV128 _ _ _ _ _ (VG.Proof.Poly1305.X86_64.Avx512.div2_lt hk)]
  split
  · rcases VG.Proof.Poly1305.X86_64.Avx512.cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Nat.zero_div, Nat.zero_mod, ite_true, Avx2.qword_app0]
    · simp only [show 1 / 2 = 0 from rfl, show 1 % 2 = 1 from rfl, ite_true, Avx2.qword_app1]; rfl
    all_goals simp [qword]
  · rfl

theorem qz_load (s : State) (d r : XReg) (a : Addr) {k : Nat} (hk : k < 8) :
    VG.Proof.Poly1305.X86_64.Avx512.qz (s.setZ d ((s.mem.readW a 512).extractLsb' 0 128) ((s.mem.readW a 512).extractLsb' 128 128)
      ((s.mem.readW a 512).extractLsb' 256 128) ((s.mem.readW a 512).extractLsb' 384 128)) r k =
      if r = d then s.mem.readW (a + BitVec.ofNat 64 (8 * k)) 64 else VG.Proof.Poly1305.X86_64.Avx512.qz s r k := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.qz]
  rw [State.zlane_setZ _ _ _ _ _ _ _ (VG.Proof.Poly1305.X86_64.Avx512.div2_lt hk),
    pick4_lanes (fun i => (s.mem.readW a 512).extractLsb' (128 * i) 128) (VG.Proof.Poly1305.X86_64.Avx512.div2_lt hk)]
  split
  · have e : qword ((s.mem.readW a 512).extractLsb' (128 * (k / 2)) 128) (k % 2) =
        (s.mem.readW a 512).extractLsb' (8 * (8 * k)) (8 * 8) := by
      apply BitVec.eq_of_getLsbD_eq; intro j hj
      simp only [qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
        decide_eq_true (show 64 * (k % 2) + j < 128 by omega)]
      exact congrArg _ (by omega)
    rw [e]
    exact readW_extract _ _ (by omega)
  · rfl

/-! ## Terms -/

/-- A quadword, in terms of those where the code starts. -/
inductive Q
  /-- Quadword `k` of the vector register numbered `r`. -/
  | reg (r : Nat)
  /-- A general-purpose register, in every quadword. -/
  | gpr (r : Reg)
  /-- `a` in quadword 0, zero elsewhere. -/
  | lane0 (a : VG.Proof.Poly1305.X86_64.Avx512.Q)
  /-- Quadword 0 of `a`, in every quadword. -/
  | bc (a : VG.Proof.Poly1305.X86_64.Avx512.Q)
  /-- Quadword `i + k` of memory at `rsi`. -/
  | ld (i : Nat)
  /-- The quadword of memory at `rdi + d`, in every quadword. -/
  | mb (d : Nat)
  | add (a b : VG.Proof.Poly1305.X86_64.Avx512.Q)
  /-- The product of the low doublewords. -/
  | mul (a b : VG.Proof.Poly1305.X86_64.Avx512.Q)
  | and (a b : VG.Proof.Poly1305.X86_64.Avx512.Q)
  /-- `~a & b`. -/
  | andn (a b : VG.Proof.Poly1305.X86_64.Avx512.Q)
  | or (a b : VG.Proof.Poly1305.X86_64.Avx512.Q)
  | shl (a : VG.Proof.Poly1305.X86_64.Avx512.Q) (n : Nat)
  | shr (a : VG.Proof.Poly1305.X86_64.Avx512.Q) (n : Nat)
  /-- `vpunpcklqdq`, `vpunpckhqdq`. -/
  | unpl (a b : VG.Proof.Poly1305.X86_64.Avx512.Q)
  | unph (a b : VG.Proof.Poly1305.X86_64.Avx512.Q)
  /-- `vshufi32x4` with the immediate `sel`. -/
  | shuf (a b : VG.Proof.Poly1305.X86_64.Avx512.Q) (sel : Nat)
  deriving DecidableEq, Repr

/-- The quadword of `vshufi32x4` with the immediate `sel` that quadword `k`
of the result is: in the first source for the lower two lanes, else the
second. -/
def shufIdx (sel k : Nat) : Nat := 2 * sel4 sel (k / 2) + k % 2

theorem shufIdx_lt (sel k : Nat) : VG.Proof.Poly1305.X86_64.Avx512.shufIdx sel k < 8 := by
  have := sel4_lt sel (k / 2)
  simp only [VG.Proof.Poly1305.X86_64.Avx512.shufIdx]; omega

def Q.eval (s₀ : State) : VG.Proof.Poly1305.X86_64.Avx512.Q → Nat → BitVec 64
  | .reg r, k => VG.Proof.Poly1305.X86_64.Avx512.qz s₀ (xr r) k
  | .gpr r, _ => s₀.gpr r
  | .lane0 a, k => if k = 0 then a.eval s₀ 0 else 0
  | .bc a, _ => a.eval s₀ 0
  | .ld i, k => s₀.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * (i + k))) 64
  | .mb d, _ => s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 (d : Int)) 64
  | .add a b, k => a.eval s₀ k + b.eval s₀ k
  | .mul a b, k => lo32 (a.eval s₀ k) * lo32 (b.eval s₀ k)
  | .and a b, k => a.eval s₀ k &&& b.eval s₀ k
  | .andn a b, k => ~~~a.eval s₀ k &&& b.eval s₀ k
  | .or a b, k => a.eval s₀ k ||| b.eval s₀ k
  | .shl a n, k => a.eval s₀ k <<< n
  | .shr a n, k => a.eval s₀ k >>> n
  | .unpl a b, k => if k % 2 = 0 then a.eval s₀ k else b.eval s₀ (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.eval s₀ (k + 1) else b.eval s₀ k
  | .shuf a b sel, k => if k / 2 < 2 then a.eval s₀ (VG.Proof.Poly1305.X86_64.Avx512.shufIdx sel k) else b.eval s₀ (VG.Proof.Poly1305.X86_64.Avx512.shufIdx sel k)

/-! ## The machine -/

/-- The terms of the vector registers (by number). -/
structure Sym where
  reg : Nat → VG.Proof.Poly1305.X86_64.Avx512.Q

def Sym.init : VG.Proof.Poly1305.X86_64.Avx512.Sym := ⟨.reg⟩

def Sym.set (σ : VG.Proof.Poly1305.X86_64.Avx512.Sym) (d : XReg) (t : VG.Proof.Poly1305.X86_64.Avx512.Q) : VG.Proof.Poly1305.X86_64.Avx512.Sym := ⟨fun r => if r = xi d then t else σ.reg r⟩

def Sym.zbin (σ : VG.Proof.Poly1305.X86_64.Avx512.Sym) (op : ZBinOp) (d a b : XReg) : Option VG.Proof.Poly1305.X86_64.Avx512.Sym :=
  let A := σ.reg (xi a)
  let B := σ.reg (xi b)
  match op with
  | .vpaddq => some (σ.set d (.add A B))
  | .vpmuludq => some (σ.set d (.mul A B))
  | .vpandq => some (σ.set d (.and A B))
  | .vpandnq => some (σ.set d (.andn A B))
  | .vporq => some (σ.set d (.or A B))
  | .vpunpcklqdq => some (σ.set d (.unpl A B))
  | .vpunpckhqdq => some (σ.set d (.unph A B))
  | _ => none

def Sym.zop (σ : VG.Proof.Poly1305.X86_64.Avx512.Sym) : ZOp → Option VG.Proof.Poly1305.X86_64.Avx512.Sym
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
  | _ => none

/-- A load of 64 bytes at `rsi + 8 i` (for `i` 0 or 8). -/
def ldIdx (m : MemOp) : Option Nat :=
  if m.base = .rsi ∧ m.index = none then
    if m.disp = 0 then some 0 else if m.disp = 64 then some 8 else none
  else none

/-- A quadword at `rdi + d` (for `56 ≤ d`, `d + 8 ≤ 120`). -/
def mbIdx (m : MemOp) : Option Nat :=
  if m.base = .rdi ∧ m.index = none ∧ 56 ≤ m.disp ∧ m.disp + 8 ≤ 120 then some m.disp.toNat else none

/-- `op` with the quadword at `rdi + e` broadcast as its second source. -/
def Sym.bcst (σ : VG.Proof.Poly1305.X86_64.Avx512.Sym) (op : ZBcstOp) (d a : XReg) (e : Nat) : VG.Proof.Poly1305.X86_64.Avx512.Sym :=
  match op with
  | .vpmuludq => σ.set d (.mul (σ.reg (xi a)) (.mb e))
  | .vpandq => σ.set d (.and (σ.reg (xi a)) (.mb e))
  | .vporq => σ.set d (.or (σ.reg (xi a)) (.mb e))

/-- One instruction; loads only if `ld`. -/
def Sym.step (ld : Bool) (σ : VG.Proof.Poly1305.X86_64.Avx512.Sym) : Instr → Option VG.Proof.Poly1305.X86_64.Avx512.Sym
  | .zop o => σ.zop o
  | .vop (.vmovq d r) => some (σ.set d (.lane0 (.gpr r)))
  | .vmovdqu32Load d m => if ld then (VG.Proof.Poly1305.X86_64.Avx512.ldIdx m).map fun i => σ.set d (.ld i) else none
  | .zbcst op d a m => if ld then (VG.Proof.Poly1305.X86_64.Avx512.mbIdx m).map (σ.bcst op d a) else none
  | _ => none

def Sym.run (ld : Bool) (σ : VG.Proof.Poly1305.X86_64.Avx512.Sym) : List Instr → Option VG.Proof.Poly1305.X86_64.Avx512.Sym
  | [] => some σ
  | i :: is => (σ.step ld i).bind fun σ' => σ'.run ld is

/-! ## The machine agrees -/

theorem vec_zop {s₀ s : State} (h : vec s₀ s = s) (o : ZOp) : vec s₀ (o.exec s) = o.exec s := by
  rw [← h]
  cases o <;> rfl

theorem vec_setV {s₀ s : State} (h : vec s₀ s = s) (len : VLen) (d : XReg) (lo hi : BitVec 128) :
    vec s₀ (s.setV len d lo hi) = s.setV len d lo hi := by
  rw [← h]; rfl

theorem vec_setZ {s₀ s : State} (h : vec s₀ s = s) (d : XReg) (a b c e : BitVec 128) :
    vec s₀ (s.setZ d a b c e) = s.setZ d a b c e := by
  rw [← h]; rfl

/-- The terms `σ` hold in `s`, which differs from `s₀` only in its vector
registers. -/
structure SRel (σ : VG.Proof.Poly1305.X86_64.Avx512.Sym) (s₀ s : State) : Prop where
  reg : ∀ r k, k < 8 → VG.Proof.Poly1305.X86_64.Avx512.qz s r k = (σ.reg (xi r)).eval s₀ k
  eq : vec s₀ s = s

theorem SRel.gpr {σ : VG.Proof.Poly1305.X86_64.Avx512.Sym} {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx512.SRel σ s₀ s) : s.gpr = s₀.gpr := vec_gpr h.eq
theorem SRel.mem {σ : VG.Proof.Poly1305.X86_64.Avx512.Sym} {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx512.SRel σ s₀ s) : s.mem = s₀.mem := vec_mem h.eq
theorem SRel.rd {σ : VG.Proof.Poly1305.X86_64.Avx512.Sym} {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx512.SRel σ s₀ s) : s.rd = s₀.rd := vec_rd h.eq
theorem SRel.wr {σ : VG.Proof.Poly1305.X86_64.Avx512.Sym} {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx512.SRel σ s₀ s) : s.wr = s₀.wr := vec_wr h.eq

theorem SRel.init (s₀ : State) : VG.Proof.Poly1305.X86_64.Avx512.SRel Sym.init s₀ s₀ :=
  ⟨fun r k _ => by simp only [Sym.init, Q.eval, xr_xi], rfl⟩

theorem SRel.set {σ : VG.Proof.Poly1305.X86_64.Avx512.Sym} {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx512.SRel σ s₀ s) {d : XReg} {t : VG.Proof.Poly1305.X86_64.Avx512.Q} {s' : State}
    (hv : ∀ r k, k < 8 → VG.Proof.Poly1305.X86_64.Avx512.qz s' r k = if r = d then t.eval s₀ k else VG.Proof.Poly1305.X86_64.Avx512.qz s r k)
    (he : vec s₀ s' = s') : VG.Proof.Poly1305.X86_64.Avx512.SRel (σ.set d t) s₀ s' := by
  refine ⟨fun r k hk => ?_, he⟩
  rw [hv r k hk]
  simp only [Sym.set, xi_inj]
  split
  · rfl
  · exact h.reg r k hk

/-- What the loads may read: 128 bytes at `rsi`, and quadwords of the state
at `rdi`. -/
structure Ctx (s₀ : State) : Prop where
  ld : ∀ i, i = 0 ∨ i = 8 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 (8 * i)) 64
  mb : ∀ d : Nat, 56 ≤ d → d + 8 ≤ 120 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi + BitVec.ofInt 64 (d : Int)) 8

theorem ldIdx_ok {m : MemOp} {i : Nat} (h : VG.Proof.Poly1305.X86_64.Avx512.ldIdx m = some i) :
    (i = 0 ∨ i = 8) ∧ ∀ s : State, s.ea m = s.gpr .rsi + BitVec.ofNat 64 (8 * i) := by
  unfold VG.Proof.Poly1305.X86_64.Avx512.ldIdx at h
  split at h
  · rename_i hb
    split at h
    · cases h
      refine ⟨.inl rfl, fun s => ?_⟩
      simp only [State.ea, hb.2, hb.1, *]; rfl
    · split at h
      · cases h
        refine ⟨.inr rfl, fun s => ?_⟩
        simp only [State.ea, hb.2, hb.1, *]; rfl
      · cases h
  · cases h

theorem mbIdx_ok {m : MemOp} {e : Nat} (h : VG.Proof.Poly1305.X86_64.Avx512.mbIdx m = some e) :
    56 ≤ e ∧ e + 8 ≤ 120 ∧ ∀ s : State, s.ea m = s.gpr .rdi + BitVec.ofInt 64 (e : Int) := by
  unfold VG.Proof.Poly1305.X86_64.Avx512.mbIdx at h
  split at h
  · rename_i hb
    obtain ⟨hr, hi, h₁, h₂⟩ := hb
    cases h
    have e : ((m.disp.toNat : Nat) : Int) = m.disp := Int.toNat_of_nonneg (by omega)
    refine ⟨by omega, by omega, fun s => ?_⟩
    simp only [State.ea, hi, hr, e]
  · cases h

theorem qword_vv (v : BitVec 64) {j : Nat} (hj : j < 2) : qword (v ++ v) j = v := by
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · exact Avx2.qword_app0 v v
  · exact Avx2.qword_app1 v v

theorem qz_bcst (op : ZBcstOp) (s : State) (d a r : XReg) (v : BitVec 64) {k : Nat} (hk : k < 8) :
    VG.Proof.Poly1305.X86_64.Avx512.qz (s.setZ d (op.sse.eval (s.zlane a 0) (v ++ v)) (op.sse.eval (s.zlane a 1) (v ++ v))
      (op.sse.eval (s.zlane a 2) (v ++ v)) (op.sse.eval (s.zlane a 3) (v ++ v))) r k =
      if r = d then qword (op.sse.eval (s.zlane a (k / 2)) (v ++ v)) (k % 2) else VG.Proof.Poly1305.X86_64.Avx512.qz s r k := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.qz]
  rw [State.zlane_setZ _ _ _ _ _ _ _ (VG.Proof.Poly1305.X86_64.Avx512.div2_lt hk),
    pick4_lanes (fun j => op.sse.eval (s.zlane a j) (v ++ v)) (VG.Proof.Poly1305.X86_64.Avx512.div2_lt hk)]
  split <;> rfl

theorem hv_of {s s' : State} {d : XReg} {f : Nat → BitVec 64} (hd : ∀ k, k < 8 → VG.Proof.Poly1305.X86_64.Avx512.qz s' d k = f k)
    (ho : ∀ r, r ≠ d → ∀ k, k < 8 → VG.Proof.Poly1305.X86_64.Avx512.qz s' r k = VG.Proof.Poly1305.X86_64.Avx512.qz s r k) :
    ∀ r k, k < 8 → VG.Proof.Poly1305.X86_64.Avx512.qz s' r k = if r = d then f k else VG.Proof.Poly1305.X86_64.Avx512.qz s r k := by
  intro r k hk
  by_cases hr : r = d
  · subst hr; rw [ite_eq_left rfl]; exact hd k hk
  · rw [ite_eq_right hr]; exact ho r hr k hk

theorem qz_lane (s : State) (r : XReg) (k : Nat) : qword (s.zlane r (k / 2)) (k % 2) = VG.Proof.Poly1305.X86_64.Avx512.qz s r k := rfl

theorem sstep_ok {ld : Bool} {s₀ : State} (hc : ld = true → VG.Proof.Poly1305.X86_64.Avx512.Ctx s₀) {σ σ' : VG.Proof.Poly1305.X86_64.Avx512.Sym} {s : State}
    (h : VG.Proof.Poly1305.X86_64.Avx512.SRel σ s₀ s) {i : Instr} (e : σ.step ld i = some σ') : ∃ s', exec i s = some s' ∧ VG.Proof.Poly1305.X86_64.Avx512.SRel σ' s₀ s' := by
  have hR : ∀ a k, k < 8 → (σ.reg (xi a)).eval s₀ k = VG.Proof.Poly1305.X86_64.Avx512.qz s a k := fun a k hk => (h.reg a k hk).symm
  unfold Sym.step at e
  split at e
  · rename_i o
    refine ⟨o.exec s, rfl, ?_⟩
    have he := VG.Proof.Poly1305.X86_64.Avx512.vec_zop h.eq o
    unfold Sym.zop at e
    split at e
    · rename_i op d a b
      unfold Sym.zbin at e
      split at e <;> cases e <;>
        refine h.set (VG.Proof.Poly1305.X86_64.Avx512.hv_of (fun k hk => ?_) (fun r hr k hk => by rw [VG.Proof.Poly1305.X86_64.Avx512.qz_zbin _ _ _ _ _ _ hk, ite_eq_right hr]))
          he <;>
        rw [VG.Proof.Poly1305.X86_64.Avx512.qz_zbin _ _ _ _ _ _ hk, ite_eq_left rfl] <;> simp only [ZBinOp.sse, Q.eval]
      · rw [qword_paddq _ _ (mod2_lt k), VG.Proof.Poly1305.X86_64.Avx512.qz_lane, VG.Proof.Poly1305.X86_64.Avx512.qz_lane, hR a k hk, hR b k hk]
      · rw [qword_pmuludq _ _ (mod2_lt k), VG.Proof.Poly1305.X86_64.Avx512.qz_lane, VG.Proof.Poly1305.X86_64.Avx512.qz_lane, hR a k hk, hR b k hk]
      · rw [XBinOp.eval, qword_and, VG.Proof.Poly1305.X86_64.Avx512.qz_lane, VG.Proof.Poly1305.X86_64.Avx512.qz_lane, hR a k hk, hR b k hk]
      · rw [XBinOp.eval, qword_andn _ _ (mod2_lt k), VG.Proof.Poly1305.X86_64.Avx512.qz_lane, VG.Proof.Poly1305.X86_64.Avx512.qz_lane, hR a k hk, hR b k hk]
      · rw [XBinOp.eval, qword_or, VG.Proof.Poly1305.X86_64.Avx512.qz_lane, VG.Proof.Poly1305.X86_64.Avx512.qz_lane, hR a k hk, hR b k hk]
      · rw [qword_punpcklqdq _ _ (mod2_lt k)]
        split
        · rename_i h0; rw [hR a k hk, VG.Proof.Poly1305.X86_64.Avx512.qz, h0]
        · rw [hR b (k - 1) (by omega), VG.Proof.Poly1305.X86_64.Avx512.qz, show (k - 1) / 2 = k / 2 by omega,
            show (k - 1) % 2 = 0 by omega]
      · rw [qword_punpckhqdq _ _ (mod2_lt k)]
        split
        · rw [hR a (k + 1) (by omega), VG.Proof.Poly1305.X86_64.Avx512.qz, show (k + 1) / 2 = k / 2 by omega,
            show (k + 1) % 2 = 1 by omega]
        · rw [hR b k hk, VG.Proof.Poly1305.X86_64.Avx512.qz, show k % 2 = 1 by omega]
    · rename_i op d a n
      split at e
      · rename_i hn
        split at e <;> cases e <;>
          refine h.set (VG.Proof.Poly1305.X86_64.Avx512.hv_of (fun k hk => ?_)
            (fun r hr k hk => by rw [VG.Proof.Poly1305.X86_64.Avx512.qz_vshift _ _ _ _ _ _ hk, ite_eq_right hr])) he <;>
          rw [VG.Proof.Poly1305.X86_64.Avx512.qz_vshift _ _ _ _ _ _ hk, ite_eq_left rfl] <;> simp only [ZShiftOp.sse, Q.eval]
        · rw [qword_psllq _ hn (mod2_lt k), VG.Proof.Poly1305.X86_64.Avx512.qz_lane, hR a k hk]
        · rw [qword_psrlq _ hn (mod2_lt k), VG.Proof.Poly1305.X86_64.Avx512.qz_lane, hR a k hk]
      · cases e
    · rename_i d a
      cases e
      exact h.set (VG.Proof.Poly1305.X86_64.Avx512.hv_of (fun k hk => by rw [VG.Proof.Poly1305.X86_64.Avx512.qz_vmovdqa64 _ _ _ _ hk, ite_eq_left rfl, hR a k hk])
        (fun r hr k hk => by rw [VG.Proof.Poly1305.X86_64.Avx512.qz_vmovdqa64 _ _ _ _ hk, ite_eq_right hr])) he
    · rename_i d a
      cases e
      exact h.set (VG.Proof.Poly1305.X86_64.Avx512.hv_of (fun k hk => by
          rw [VG.Proof.Poly1305.X86_64.Avx512.qz_vpbroadcastq _ _ _ _ hk, ite_eq_left rfl]; exact (hR a 0 (by decide)).symm)
        (fun r hr k hk => by rw [VG.Proof.Poly1305.X86_64.Avx512.qz_vpbroadcastq _ _ _ _ hk, ite_eq_right hr])) he
    · rename_i d a b n
      cases e
      exact h.set (VG.Proof.Poly1305.X86_64.Avx512.hv_of (fun k hk => by
          rw [VG.Proof.Poly1305.X86_64.Avx512.qz_vshufi32x4 _ _ _ _ _ _ hk, ite_eq_left rfl]; simp only [Q.eval, VG.Proof.Poly1305.X86_64.Avx512.shufIdx]
          split
          · exact (hR a _ (VG.Proof.Poly1305.X86_64.Avx512.shufIdx_lt _ _)).symm
          · exact (hR b _ (VG.Proof.Poly1305.X86_64.Avx512.shufIdx_lt _ _)).symm)
        (fun r hr k hk => by rw [VG.Proof.Poly1305.X86_64.Avx512.qz_vshufi32x4 _ _ _ _ _ _ hk, ite_eq_right hr])) he
    · cases e
  · rename_i d g
    cases e
    refine ⟨(VOp.vmovq d g).exec s, rfl, ?_⟩
    exact h.set (VG.Proof.Poly1305.X86_64.Avx512.hv_of (fun k hk => by rw [VG.Proof.Poly1305.X86_64.Avx512.qz_vmovq _ _ _ _ hk, ite_eq_left rfl]; simp only [Q.eval, h.gpr])
      (fun r hr k hk => by rw [VG.Proof.Poly1305.X86_64.Avx512.qz_vmovq _ _ _ _ hk, ite_eq_right hr])) (by
        rw [← h.eq]; rfl)
  · rename_i d m
    split at e
    case isFalse => cases e
    rename_i hld
    obtain ⟨i, hs, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨hi, hea⟩ := VG.Proof.Poly1305.X86_64.Avx512.ldIdx_ok hs
    have ea : s.ea m = s₀.gpr .rsi + BitVec.ofNat 64 (8 * i) := by rw [hea, h.gpr]
    have hin : InRegions (s.rd ++ s.wr) (s₀.gpr .rsi + BitVec.ofNat 64 (8 * i)) 64 := by
      rw [h.rd, h.wr]; exact (hc hld).ld i hi
    let v := s.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * i)) 512
    refine ⟨s.setZ d (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
      (v.extractLsb' 384 128), by simp only [exec, ea, State.load512, hin, ite_true, Option.map_some, v], ?_⟩
    refine h.set (VG.Proof.Poly1305.X86_64.Avx512.hv_of (fun k hk => ?_) (fun r hr k hk => by rw [VG.Proof.Poly1305.X86_64.Avx512.qz_load _ _ _ _ hk, ite_eq_right hr]))
      (VG.Proof.Poly1305.X86_64.Avx512.vec_setZ h.eq _ _ _ _ _)
    rw [VG.Proof.Poly1305.X86_64.Avx512.qz_load _ _ _ _ hk, ite_eq_left rfl, h.mem, Offset.add_add]; simp only [Q.eval, Nat.mul_add]
  · rename_i op d a m
    split at e
    case isFalse => cases e
    rename_i hld
    obtain ⟨i, hs, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨h₁, h₂, hea⟩ := VG.Proof.Poly1305.X86_64.Avx512.mbIdx_ok hs
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
    have he := VG.Proof.Poly1305.X86_64.Avx512.vec_setZ h.eq d (op.sse.eval (s.zlane a 0) (v ++ v)) (op.sse.eval (s.zlane a 1) (v ++ v))
      (op.sse.eval (s.zlane a 2) (v ++ v)) (op.sse.eval (s.zlane a 3) (v ++ v))
    cases op <;>
      refine h.set (VG.Proof.Poly1305.X86_64.Avx512.hv_of (fun k hk => ?_) (fun r hr k hk => by rw [VG.Proof.Poly1305.X86_64.Avx512.qz_bcst _ _ _ _ _ _ hk, ite_eq_right hr]))
        he <;>
      rw [VG.Proof.Poly1305.X86_64.Avx512.qz_bcst _ _ _ _ _ _ hk, ite_eq_left rfl] <;> simp only [ZBcstOp.sse, Q.eval]
    · rw [qword_pmuludq _ _ (mod2_lt k), VG.Proof.Poly1305.X86_64.Avx512.qz_lane, hR a k hk, VG.Proof.Poly1305.X86_64.Avx512.qword_vv _ (mod2_lt k), hv']
    · rw [XBinOp.eval, qword_and, VG.Proof.Poly1305.X86_64.Avx512.qz_lane, hR a k hk, VG.Proof.Poly1305.X86_64.Avx512.qword_vv _ (mod2_lt k), hv']
    · rw [XBinOp.eval, qword_or, VG.Proof.Poly1305.X86_64.Avx512.qz_lane, hR a k hk, VG.Proof.Poly1305.X86_64.Avx512.qword_vv _ (mod2_lt k), hv']
  · cases e

/-- A block of instructions. -/
theorem srun_ok {ld : Bool} {s₀ : State} (hc : ld = true → VG.Proof.Poly1305.X86_64.Avx512.Ctx s₀) :
    ∀ (is : List Instr) {σ σ' : VG.Proof.Poly1305.X86_64.Avx512.Sym} {s : State}, VG.Proof.Poly1305.X86_64.Avx512.SRel σ s₀ s → σ.run ld is = some σ' →
      WP isa (.block is) s (VG.Proof.Poly1305.X86_64.Avx512.SRel σ' s₀)
  | [], _, _, _, h, e => by cases e; exact WP.block_nil h
  | i :: is, _, _, _, h, e => by
    simp only [Sym.run, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    obtain ⟨s₁, hx, h₁⟩ := VG.Proof.Poly1305.X86_64.Avx512.sstep_ok hc h e₁
    exact WP.block_cons_iff.2 ⟨s₁, hx, VG.Proof.Poly1305.X86_64.Avx512.srun_ok hc is h₁ e₂⟩

/-- A block from its start. -/
theorem run_ok {ld : Bool} {s₀ : State} (hc : ld = true → VG.Proof.Poly1305.X86_64.Avx512.Ctx s₀) {is : List Instr} {σ : VG.Proof.Poly1305.X86_64.Avx512.Sym}
    (e : Sym.init.run ld is = some σ) : WP isa (.block is) s₀ (VG.Proof.Poly1305.X86_64.Avx512.SRel σ s₀) :=
  VG.Proof.Poly1305.X86_64.Avx512.srun_ok hc is (SRel.init s₀) e

end VG.Proof.Poly1305.X86_64.Avx512

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Bound`. -/
section

/-!
# Poly1305 on x86-64 with AVX-512: terms as numbers

As for AVX2 (`Avx2/Bound.lean`), on the eight quadwords of `zmm` registers.
The limbs the code computes stay far below `2⁶⁴`, so its additions, products
and shifts never wrap. `Q.bnd` bounds each term from bounds on the registers
it starts from, `Q.ok` checks that its additions and left shifts do not wrap
under those bounds, and `Q.nat` is its value as a number, with the reductions
modulo `2⁶⁴` (and to the low doubleword, for products) left out. `nat_ok`
proves that a term is `Q.nat` and within `Q.bnd` where the kernel evaluates
`Q.ok` of concrete terms to `true`, so the number a block computes is `nat` of
its term, which unfolds to the arithmetic of `Limbs26` by definition. `Q.natw`
is the value with every reduction kept, which `natw_ok` proves exact for any
term, for the blocks that shift bits out on purpose.
-/

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi lo32 capW orB capW_ge orB_ge lo32_toNat)

/-- Bounds on the registers a block starts from: on each vector register's
quadwords (`v`) and their low doublewords (`lo`), on the general-purpose
registers, and on the quadwords of memory at `rdi + d` (`mb`) and their low
doublewords (`mbl`). -/
structure Bnds where
  v : XReg → Nat
  lo : XReg → Nat
  g : Reg → Nat
  mb : Nat → Nat
  mbl : Nat → Nat

/-- The values a block starts from, as numbers. -/
structure Env where
  v : Nat → Nat → Nat
  g : Reg → Nat
  m : Nat → Nat
  mb : Nat → Nat

def envOf (s₀ : State) : VG.Proof.Poly1305.X86_64.Avx512.Env :=
  ⟨fun r k => (VG.Proof.Poly1305.X86_64.Avx512.qz s₀ (xr r) k).toNat, fun g => (s₀.gpr g).toNat,
    fun j => (s₀.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * j)) 64).toNat,
    fun d => (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 (d : Int)) 64).toNat⟩

/-- A bound on the low doubleword of `t`, whose bound is `b`. -/
def loB (B : VG.Proof.Poly1305.X86_64.Avx512.Bnds) (t : VG.Proof.Poly1305.X86_64.Avx512.Q) (b : Nat) : Nat :=
  match t with
  | .reg r => min (B.lo (xr r)) (min b (2 ^ 32 - 1))
  | .mb d => min (B.mbl d) (min b (2 ^ 32 - 1))
  | _ => min b (2 ^ 32 - 1)

def Q.bnd (B : VG.Proof.Poly1305.X86_64.Avx512.Bnds) : VG.Proof.Poly1305.X86_64.Avx512.Q → Nat → Nat
  | .reg r, _ => min (B.v (xr r)) (2 ^ 64 - 1)
  | .gpr g, _ => min (B.g g) (2 ^ 64 - 1)
  | .lane0 a, k => if k = 0 then a.bnd B 0 else 0
  | .bc a, _ => a.bnd B 0
  | .ld _, _ => 2 ^ 64 - 1
  | .mb d, _ => min (B.mb d) (2 ^ 64 - 1)
  | .add a b, k => capW (a.bnd B k + b.bnd B k)
  | .mul a b, k => VG.Proof.Poly1305.X86_64.Avx512.loB B a (a.bnd B k) * VG.Proof.Poly1305.X86_64.Avx512.loB B b (b.bnd B k)
  | .and a b, k => min (a.bnd B k) (b.bnd B k)
  | .andn _ b, k => b.bnd B k
  | .or a b, k => orB (a.bnd B k) (b.bnd B k)
  | .shl a n, k => capW (a.bnd B k * 2 ^ n)
  | .shr a n, k => a.bnd B k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.bnd B k else b.bnd B (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.bnd B (k + 1) else b.bnd B k
  | .shuf a b sel, k => if k / 2 < 2 then a.bnd B (VG.Proof.Poly1305.X86_64.Avx512.shufIdx sel k) else b.bnd B (VG.Proof.Poly1305.X86_64.Avx512.shufIdx sel k)

/-- The value of a term as a number, with no reductions modulo `2⁶⁴`: what
the code computes where `Q.ok` holds. -/
def Q.nat (E : VG.Proof.Poly1305.X86_64.Avx512.Env) : VG.Proof.Poly1305.X86_64.Avx512.Q → Nat → Nat
  | .reg r, k => E.v r k
  | .gpr g, _ => E.g g
  | .lane0 a, k => if k = 0 then a.nat E 0 else 0
  | .bc a, _ => a.nat E 0
  | .ld i, k => E.m (i + k)
  | .mb d, _ => E.mb d
  | .add a b, k => a.nat E k + b.nat E k
  | .mul a b, k => a.nat E k % 2 ^ 32 * (b.nat E k % 2 ^ 32)
  | .and a b, k => a.nat E k &&& b.nat E k
  | .andn a b, k => (2 ^ 64 - 1 - a.nat E k) &&& b.nat E k
  | .or a b, k => a.nat E k ||| b.nat E k
  | .shl a n, k => a.nat E k * 2 ^ n
  | .shr a n, k => a.nat E k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.nat E k else b.nat E (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.nat E (k + 1) else b.nat E k
  | .shuf a b sel, k => if k / 2 < 2 then a.nat E (VG.Proof.Poly1305.X86_64.Avx512.shufIdx sel k) else b.nat E (VG.Proof.Poly1305.X86_64.Avx512.shufIdx sel k)

/-- The value of a term as a number, reduced as the code does: exact
whatever the bounds (`natw_ok`), for the blocks that shift bits out on
purpose. -/
def Q.natw (E : VG.Proof.Poly1305.X86_64.Avx512.Env) : VG.Proof.Poly1305.X86_64.Avx512.Q → Nat → Nat
  | .reg r, k => E.v r k
  | .gpr g, _ => E.g g
  | .lane0 a, k => if k = 0 then a.natw E 0 else 0
  | .bc a, _ => a.natw E 0
  | .ld i, k => E.m (i + k)
  | .mb d, _ => E.mb d
  | .add a b, k => (a.natw E k + b.natw E k) % 2 ^ 64
  | .mul a b, k => a.natw E k % 2 ^ 32 * (b.natw E k % 2 ^ 32)
  | .and a b, k => a.natw E k &&& b.natw E k
  | .andn a b, k => (2 ^ 64 - 1 - a.natw E k) &&& b.natw E k
  | .or a b, k => a.natw E k ||| b.natw E k
  | .shl a n, k => a.natw E k * 2 ^ n % 2 ^ 64
  | .shr a n, k => a.natw E k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.natw E k else b.natw E (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.natw E (k + 1) else b.natw E k
  | .shuf a b sel, k => if k / 2 < 2 then a.natw E (VG.Proof.Poly1305.X86_64.Avx512.shufIdx sel k) else b.natw E (VG.Proof.Poly1305.X86_64.Avx512.shufIdx sel k)

/-- No addition or left shift in `t` wraps, by the bounds `B`. -/
def Q.ok (B : VG.Proof.Poly1305.X86_64.Avx512.Bnds) : VG.Proof.Poly1305.X86_64.Avx512.Q → Nat → Bool
  | .reg _, _ | .gpr _, _ | .ld _, _ | .mb _, _ => true
  | .lane0 a, k => if k = 0 then a.ok B 0 else true
  | .bc a, _ => a.ok B 0
  | .add a b, k => a.bnd B k + b.bnd B k < 2 ^ 64 && a.ok B k && b.ok B k
  | .mul a b, k | .and a b, k | .andn a b, k | .or a b, k => a.ok B k && b.ok B k
  | .shl a n, k => a.bnd B k * 2 ^ n < 2 ^ 64 && a.ok B k
  | .shr a _, k => a.ok B k
  | .unpl a b, k => if k % 2 = 0 then a.ok B k else b.ok B (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.ok B (k + 1) else b.ok B k
  | .shuf a b sel, k => if k / 2 < 2 then a.ok B (VG.Proof.Poly1305.X86_64.Avx512.shufIdx sel k) else b.ok B (VG.Proof.Poly1305.X86_64.Avx512.shufIdx sel k)

/-- The registers `s₀` starts from are within `B`. -/
structure EnvOK (s₀ : State) (B : VG.Proof.Poly1305.X86_64.Avx512.Bnds) : Prop where
  v : ∀ r k, k < 8 → (VG.Proof.Poly1305.X86_64.Avx512.qz s₀ r k).toNat ≤ B.v r
  lo : ∀ r k, k < 8 → (VG.Proof.Poly1305.X86_64.Avx512.qz s₀ r k).toNat % 2 ^ 32 ≤ B.lo r
  g : ∀ g, (s₀.gpr g).toNat ≤ B.g g
  mb : ∀ d : Nat, (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 (d : Int)) 64).toNat ≤ B.mb d
  mbl : ∀ d : Nat, (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 (d : Int)) 64).toNat % 2 ^ 32 ≤ B.mbl d

theorem loB_ge {s₀ : State} {B : VG.Proof.Poly1305.X86_64.Avx512.Bnds} (hE : VG.Proof.Poly1305.X86_64.Avx512.EnvOK s₀ B) {t : VG.Proof.Poly1305.X86_64.Avx512.Q} {k : Nat} (hk : k < 8) {b : Nat}
    (hb : (t.eval s₀ k).toNat ≤ b) : (t.eval s₀ k).toNat % 2 ^ 32 ≤ VG.Proof.Poly1305.X86_64.Avx512.loB B t b := by
  unfold VG.Proof.Poly1305.X86_64.Avx512.loB
  split
  · rename_i r
    have := hE.lo (xr r) k hk
    have h₁ := Nat.mod_le (VG.Proof.Poly1305.X86_64.Avx512.qz s₀ (xr r) k).toNat (2 ^ 32)
    have h₂ := Nat.mod_lt (VG.Proof.Poly1305.X86_64.Avx512.qz s₀ (xr r) k).toNat (show 2 ^ 32 > 0 by decide)
    simp only [Q.eval] at hb ⊢
    omega
  · rename_i d
    have := hE.mbl d
    have h₁ := Nat.mod_le (Q.eval s₀ (.mb d) k).toNat (2 ^ 32)
    have h₂ := Nat.mod_lt (Q.eval s₀ (.mb d) k).toNat (show 2 ^ 32 > 0 by decide)
    simp only [Q.eval] at hb h₁ h₂ ⊢
    omega
  · have h₁ := Nat.mod_le (t.eval s₀ k).toNat (2 ^ 32)
    have h₂ := Nat.mod_lt (t.eval s₀ k).toNat (show 2 ^ 32 > 0 by decide)
    omega

theorem nat_ok {s₀ : State} {B : VG.Proof.Poly1305.X86_64.Avx512.Bnds} (hE : VG.Proof.Poly1305.X86_64.Avx512.EnvOK s₀ B) :
    ∀ (t : VG.Proof.Poly1305.X86_64.Avx512.Q) {k : Nat}, k < 8 → t.ok B k = true →
      (t.eval s₀ k).toNat = t.nat (VG.Proof.Poly1305.X86_64.Avx512.envOf s₀) k ∧ (t.eval s₀ k).toNat ≤ t.bnd B k := by
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
    simp only [Q.eval, Q.nat, VG.Proof.Poly1305.X86_64.Avx512.envOf, Nat.mul_add]
  | mb d =>
    intro k _ _
    exact ⟨rfl, Nat.le_min.2 ⟨hE.mb d, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩⟩
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
    exact ⟨Nat.mod_eq_of_lt (by omega), capW_ge (by rw [Nat.mod_eq_of_lt (by omega)]; omega) this⟩
  | mul a b iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba⟩ := iha hk ho.1
    obtain ⟨eb, bb⟩ := ihb hk ho.2
    have la := VG.Proof.Poly1305.X86_64.Avx512.loB_ge hE hk ba
    have lb := VG.Proof.Poly1305.X86_64.Avx512.loB_ge hE hk bb
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_mul, lo32_toNat]
    rw [← ea, ← eb]
    have p₁ := Nat.mod_lt (a.eval s₀ k).toNat (show 2 ^ 32 > 0 by decide)
    have p₂ := Nat.mod_lt (b.eval s₀ k).toNat (show 2 ^ 32 > 0 by decide)
    have hp : (a.eval s₀ k).toNat % 2 ^ 32 * ((b.eval s₀ k).toNat % 2 ^ 32) < 2 ^ 64 :=
      Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le p₁ (Nat.le_of_lt p₂) (by decide)) (by decide)
    rw [Nat.mod_eq_of_lt hp]
    exact ⟨rfl, Nat.mul_le_mul la lb⟩
  | and a b iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba⟩ := iha hk ho.1
    obtain ⟨eb, bb⟩ := ihb hk ho.2
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_and]
    rw [← ea, ← eb]
    exact ⟨rfl, Nat.le_min.2 ⟨Nat.le_trans Nat.and_le_left ba, Nat.le_trans Nat.and_le_right bb⟩⟩
  | andn a b iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, _⟩ := iha hk ho.1
    obtain ⟨eb, bb⟩ := ihb hk ho.2
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_and, BitVec.toNat_not]
    rw [← ea, ← eb]
    exact ⟨rfl, Nat.le_trans Nat.and_le_right bb⟩
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
    exact ⟨Nat.mod_eq_of_lt (by omega), capW_ge (by rw [Nat.mod_eq_of_lt (by omega)]; omega) this⟩
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
    · rename_i h; rw [ite_eq_right h] at ho; exact ihb (by omega) ho
  | unph a b iha ihb =>
    intro k hk ho
    simp only [Q.eval, Q.nat, Q.bnd, Q.ok] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact iha (by omega) ho
    · rename_i h; rw [ite_eq_right h] at ho; exact ihb hk ho
  | shuf a b sel iha ihb =>
    intro k _ ho
    simp only [Q.eval, Q.nat, Q.bnd, Q.ok] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact iha (VG.Proof.Poly1305.X86_64.Avx512.shufIdx_lt _ _) ho
    · rename_i h; rw [ite_eq_right h] at ho; exact ihb (VG.Proof.Poly1305.X86_64.Avx512.shufIdx_lt _ _) ho

theorem natw_ok (s₀ : State) : ∀ (t : VG.Proof.Poly1305.X86_64.Avx512.Q) (k : Nat), (t.eval s₀ k).toNat = t.natw (VG.Proof.Poly1305.X86_64.Avx512.envOf s₀) k := by
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
  | ld i => intro k; simp only [Q.eval, Q.natw, VG.Proof.Poly1305.X86_64.Avx512.envOf, Nat.mul_add]
  | mb d => intro k; rfl
  | add a b iha ihb => intro k; simp only [Q.eval, Q.natw, BitVec.toNat_add, iha, ihb]
  | mul a b iha ihb =>
    intro k
    simp only [Q.eval, Q.natw, BitVec.toNat_mul, lo32_toNat, iha, ihb]
    have p₁ := Nat.mod_lt (a.natw (VG.Proof.Poly1305.X86_64.Avx512.envOf s₀) k) (show 2 ^ 32 > 0 by decide)
    have p₂ := Nat.mod_lt (b.natw (VG.Proof.Poly1305.X86_64.Avx512.envOf s₀) k) (show 2 ^ 32 > 0 by decide)
    exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le p₁ (Nat.le_of_lt p₂) (by decide)) (by decide))
  | and a b iha ihb => intro k; simp only [Q.eval, Q.natw, BitVec.toNat_and, iha, ihb]
  | andn a b iha ihb => intro k; simp only [Q.eval, Q.natw, BitVec.toNat_and, BitVec.toNat_not, iha, ihb]
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

theorem SRel.nat {σ : VG.Proof.Poly1305.X86_64.Avx512.Sym} {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx512.SRel σ s₀ s) {B : VG.Proof.Poly1305.X86_64.Avx512.Bnds} (hE : VG.Proof.Poly1305.X86_64.Avx512.EnvOK s₀ B) {r : XReg}
    {k : Nat} (hk : k < 8) (ho : (σ.reg (xi r)).ok B k = true) :
    (VG.Proof.Poly1305.X86_64.Avx512.qz s r k).toNat = (σ.reg (xi r)).nat (VG.Proof.Poly1305.X86_64.Avx512.envOf s₀) k ∧ (VG.Proof.Poly1305.X86_64.Avx512.qz s r k).toNat ≤ (σ.reg (xi r)).bnd B k := by
  rw [h.reg r k hk]; exact VG.Proof.Poly1305.X86_64.Avx512.nat_ok hE _ hk ho

theorem SRel.natw {σ : VG.Proof.Poly1305.X86_64.Avx512.Sym} {s₀ s : State} (h : VG.Proof.Poly1305.X86_64.Avx512.SRel σ s₀ s) (r : XReg) {k : Nat} (hk : k < 8) :
    (VG.Proof.Poly1305.X86_64.Avx512.qz s r k).toNat = (σ.reg (xi r)).natw (VG.Proof.Poly1305.X86_64.Avx512.envOf s₀) k := by
  rw [h.reg r k hk]; exact VG.Proof.Poly1305.X86_64.Avx512.natw_ok s₀ _ k

theorem envOf_v (s₀ : State) (r : XReg) (k : Nat) : (VG.Proof.Poly1305.X86_64.Avx512.envOf s₀).v (xi r) k = (VG.Proof.Poly1305.X86_64.Avx512.qz s₀ r k).toNat := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.envOf, xr_xi]

end VG.Proof.Poly1305.X86_64.Avx512

end
