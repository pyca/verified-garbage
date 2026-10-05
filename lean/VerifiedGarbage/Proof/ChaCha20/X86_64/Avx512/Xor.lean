import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512
import VerifiedGarbage.Proof.ChaCha20.StreamBytes
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Xor

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Rounds`. -/
section

/-!
# ChaCha20 on x86-64 with AVX-512: the rounds

Doubleword `j` of a register (doubleword `j % 4` of lane `j / 4`) holds a word
of block `j`, register `k` word `k`. Every instruction of the rounds acts on
each block as a step on its state (`zstep`), so the rounds are proven once on
the sixteen states and then, without the machine, equal to the
specification's.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx512

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)
open VG.Proof.ChaCha20

/-- The number of a vector register. -/
def xidx : XReg → Nat
  | .xmm0 => 0 | .xmm1 => 1 | .xmm2 => 2 | .xmm3 => 3
  | .xmm4 => 4 | .xmm5 => 5 | .xmm6 => 6 | .xmm7 => 7
  | .xmm8 => 8 | .xmm9 => 9 | .xmm10 => 10 | .xmm11 => 11
  | .xmm12 => 12 | .xmm13 => 13 | .xmm14 => 14 | .xmm15 => 15

theorem xidx_lt (r : XReg) : VG.Proof.ChaCha20.X86_64.Avx512.xidx r < 16 := by cases r <;> decide

theorem xidx_inj {r r' : XReg} : VG.Proof.ChaCha20.X86_64.Avx512.xidx r = VG.Proof.ChaCha20.X86_64.Avx512.xidx r' ↔ r = r' := by
  cases r <;> cases r' <;> decide

theorem xidx_zreg : ∀ k < 16, VG.Proof.ChaCha20.X86_64.Avx512.xidx (zreg k) = k := by decide

/-- Doubleword `j` of `r`: the word of block `j`. -/
abbrev zw (s : State) (r : XReg) (j : Nat) : Word := dword (s.zlane r (j / 4)) (j % 4)

/-- The sixteen states `vs 0, …, vs 15` are in the registers: word `k` of
block `j` in doubleword `j` of register `k`. -/
def ZH (vs : Nat → CState) (s : State) : Prop :=
  ∀ r j, j < 16 → VG.Proof.ChaCha20.X86_64.Avx512.zw s r j = (vs j)[VG.Proof.ChaCha20.X86_64.Avx512.xidx r]'(VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt r)

/-- The instructions of the rounds: `vpaddd`, `vpxord` and `vprold` on `zmm`
registers. -/
inductive ZI
  | add (d a b : XReg) | xor (d a b : XReg) | rol (d a : XReg) (n : BitVec 8)

def ZI.instr : VG.Proof.ChaCha20.X86_64.Avx512.ZI → Instr
  | .add d a b => z .vpaddd d a b
  | .xor d a b => z .vpxord d a b
  | .rol d a n => .zop (.vprold d a n)

/-- An instruction of the rounds, on one block's state. -/
def zstep (v : CState) : VG.Proof.ChaCha20.X86_64.Avx512.ZI → CState
  | .add d a b => v.set (VG.Proof.ChaCha20.X86_64.Avx512.xidx d) (v[VG.Proof.ChaCha20.X86_64.Avx512.xidx a]'(VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt a) + v[VG.Proof.ChaCha20.X86_64.Avx512.xidx b]'(VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt b)) (VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt d)
  | .xor d a b => v.set (VG.Proof.ChaCha20.X86_64.Avx512.xidx d) (v[VG.Proof.ChaCha20.X86_64.Avx512.xidx a]'(VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt a) ^^^ v[VG.Proof.ChaCha20.X86_64.Avx512.xidx b]'(VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt b)) (VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt d)
  | .rol d a n => v.set (VG.Proof.ChaCha20.X86_64.Avx512.xidx d) ((v[VG.Proof.ChaCha20.X86_64.Avx512.xidx a]'(VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt a)).rotateLeft (n.toNat % 32)) (VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt d)

theorem div4_lt {j : Nat} (hj : j < 16) : j / 4 < 4 := by omega
theorem mod4_lt (j : Nat) : j % 4 < 4 := Nat.mod_lt _ (by decide)

theorem getElem_set_xidx (v : CState) (d r : XReg) (x : Word) :
    (v.set (VG.Proof.ChaCha20.X86_64.Avx512.xidx d) x (VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt d))[VG.Proof.ChaCha20.X86_64.Avx512.xidx r]'(VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt r) = if r = d then x else v[VG.Proof.ChaCha20.X86_64.Avx512.xidx r]'(VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt r) := by
  rw [Vector.getElem_set]
  by_cases h : r = d
  · subst h; simp
  · simp [h, VG.Proof.ChaCha20.X86_64.Avx512.xidx_inj, Ne.symm h]

/-- One instruction of the rounds, on all sixteen blocks. -/
theorem step_ok (i : VG.Proof.ChaCha20.X86_64.Avx512.ZI) {vs : Nat → CState} {s : State} (h : VG.Proof.ChaCha20.X86_64.Avx512.ZH vs s) :
    ∃ s', exec i.instr s = some s' ∧ VG.Proof.ChaCha20.X86_64.Avx512.ZH (fun j => VG.Proof.ChaCha20.X86_64.Avx512.zstep (vs j) i) s' ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases i with
  | add d a b =>
    refine ⟨_, rfl, fun r j hj => ?_, by simp, by simp, by simp, by simp⟩
    simp only [VG.Proof.ChaCha20.X86_64.Avx512.zw, zlane_zbin _ _ _ _ _ _ (VG.Proof.ChaCha20.X86_64.Avx512.div4_lt hj), VG.Proof.ChaCha20.X86_64.Avx512.zstep, VG.Proof.ChaCha20.X86_64.Avx512.getElem_set_xidx]
    split
    · simp only [ZBinOp.sse, dword_paddd _ _ (VG.Proof.ChaCha20.X86_64.Avx512.mod4_lt j)]; rw [← h a j hj, ← h b j hj]
    · exact h r j hj
  | xor d a b =>
    refine ⟨_, rfl, fun r j hj => ?_, by simp, by simp, by simp, by simp⟩
    simp only [VG.Proof.ChaCha20.X86_64.Avx512.zw, zlane_zbin _ _ _ _ _ _ (VG.Proof.ChaCha20.X86_64.Avx512.div4_lt hj), VG.Proof.ChaCha20.X86_64.Avx512.zstep, VG.Proof.ChaCha20.X86_64.Avx512.getElem_set_xidx]
    split
    · simp only [ZBinOp.sse, dword_pxor]; rw [← h a j hj, ← h b j hj]
    · exact h r j hj
  | rol d a n =>
    refine ⟨_, rfl, fun r j hj => ?_, by simp, by simp, by simp, by simp⟩
    simp only [VG.Proof.ChaCha20.X86_64.Avx512.zw, zlane_vprold _ _ _ _ _ (VG.Proof.ChaCha20.X86_64.Avx512.div4_lt hj), VG.Proof.ChaCha20.X86_64.Avx512.zstep, VG.Proof.ChaCha20.X86_64.Avx512.getElem_set_xidx]
    split
    · rw [dword_rolDwords _ _ (VG.Proof.ChaCha20.X86_64.Avx512.mod4_lt j), ← h a j hj]
    · exact h r j hj

/-- The frame of the rounds. -/
structure Same (s₀ s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- Instructions of the rounds, in sequence, on all sixteen blocks. -/
theorem block_ok : ∀ (is : List VG.Proof.ChaCha20.X86_64.Avx512.ZI) {vs : Nat → CState} {s : State}, VG.Proof.ChaCha20.X86_64.Avx512.ZH vs s →
    WP isa (.block (is.map ZI.instr)) s fun s' => VG.Proof.ChaCha20.X86_64.Avx512.ZH (fun j => is.foldl VG.Proof.ChaCha20.X86_64.Avx512.zstep (vs j)) s' ∧ VG.Proof.ChaCha20.X86_64.Avx512.Same s s'
  | [], _, _, h => WP.block_nil ⟨h, rfl, rfl, rfl, rfl⟩
  | i :: is, _, _, h => by
    obtain ⟨s', he, h', g, m, r, w⟩ := VG.Proof.ChaCha20.X86_64.Avx512.step_ok i h
    exact WP.block_cons_iff.2 ⟨s', he, WP.mono (VG.Proof.ChaCha20.X86_64.Avx512.block_ok is h') fun _ ⟨ht, hs⟩ =>
      ⟨ht, hs.gpr.trans g, hs.mem.trans m, hs.rd.trans r, hs.wr.trans w⟩⟩

/-- `half`, as instructions of the rounds. -/
def halfZ (qs : List (XReg × XReg × XReg × XReg)) (r₁ r₂ : BitVec 8) : List VG.Proof.ChaCha20.X86_64.Avx512.ZI :=
  qs.map (fun (a, b, _, _) => .add a a b) ++
  qs.map (fun (a, _, _, d) => .xor d d a) ++
  qs.map (fun (_, _, _, d) => .rol d d r₁) ++
  qs.map (fun (_, _, c, d) => .add c c d) ++
  qs.map (fun (_, b, c, _) => .xor b b c) ++
  qs.map (fun (_, b, _, _) => .rol b b r₂)

theorem half_eq (qs : List (XReg × XReg × XReg × XReg)) (r₁ r₂ : BitVec 8) :
    half qs r₁ r₂ = (VG.Proof.ChaCha20.X86_64.Avx512.halfZ qs r₁ r₂).map ZI.instr := by
  simp only [half, VG.Proof.ChaCha20.X86_64.Avx512.halfZ, List.map_append, List.map_map]; rfl

def quartersZ (ws : List (Nat × Nat × Nat × Nat)) : List VG.Proof.ChaCha20.X86_64.Avx512.ZI :=
  let qs := ws.map fun (a, b, c, d) => (zreg a, zreg b, zreg c, zreg d)
  VG.Proof.ChaCha20.X86_64.Avx512.halfZ qs 16 12 ++ VG.Proof.ChaCha20.X86_64.Avx512.halfZ qs 8 7

theorem quarters_eq (ws : List (Nat × Nat × Nat × Nat)) :
    quarters ws = (VG.Proof.ChaCha20.X86_64.Avx512.quartersZ ws).map ZI.instr := by
  simp only [quarters, VG.Proof.ChaCha20.X86_64.Avx512.quartersZ, VG.Proof.ChaCha20.X86_64.Avx512.half_eq, List.map_append]

/-! ## The rounds on one block

The words after a round are terms in the words before it (`E`), computed by
the kernel for the code and for the specification and compared. -/

/-- A term in the words `var k` of a state. -/
inductive E
  | var (k : Nat) | add (a b : VG.Proof.ChaCha20.X86_64.Avx512.E) | xor (a b : VG.Proof.ChaCha20.X86_64.Avx512.E) | rol (a : VG.Proof.ChaCha20.X86_64.Avx512.E) (n : Nat)
  deriving DecidableEq

def E.eval (v : CState) : VG.Proof.ChaCha20.X86_64.Avx512.E → Word
  | .var k => if h : k < 16 then v[k] else 0
  | .add a b => a.eval v + b.eval v
  | .xor a b => a.eval v ^^^ b.eval v
  | .rol a n => (a.eval v).rotateLeft n

/-- A state of terms. -/
abbrev ES := Nat → VG.Proof.ChaCha20.X86_64.Avx512.E

def ES.set (f : VG.Proof.ChaCha20.X86_64.Avx512.ES) (i : Nat) (x : VG.Proof.ChaCha20.X86_64.Avx512.E) : VG.Proof.ChaCha20.X86_64.Avx512.ES := fun k => if k = i then x else f k

/-- `zstep` on terms. -/
def zstepE (f : VG.Proof.ChaCha20.X86_64.Avx512.ES) : VG.Proof.ChaCha20.X86_64.Avx512.ZI → VG.Proof.ChaCha20.X86_64.Avx512.ES
  | .add d a b => f.set (VG.Proof.ChaCha20.X86_64.Avx512.xidx d) (.add (f (VG.Proof.ChaCha20.X86_64.Avx512.xidx a)) (f (VG.Proof.ChaCha20.X86_64.Avx512.xidx b)))
  | .xor d a b => f.set (VG.Proof.ChaCha20.X86_64.Avx512.xidx d) (.xor (f (VG.Proof.ChaCha20.X86_64.Avx512.xidx a)) (f (VG.Proof.ChaCha20.X86_64.Avx512.xidx b)))
  | .rol d a n => f.set (VG.Proof.ChaCha20.X86_64.Avx512.xidx d) (.rol (f (VG.Proof.ChaCha20.X86_64.Avx512.xidx a)) (n.toNat % 32))

/-- `qround` on terms. -/
def qroundE (f : VG.Proof.ChaCha20.X86_64.Avx512.ES) (x y z w : Fin 16) : VG.Proof.ChaCha20.X86_64.Avx512.ES :=
  let a := E.add (f x) (f y); let d := E.rol (.xor (f w) a) 16
  let c := E.add (f z) d; let b := E.rol (.xor (f y) c) 12
  let a := E.add a b; let d := E.rol (.xor d a) 8
  let c := E.add c d; let b := E.rol (.xor b c) 7
  (((f.set x a).set y b).set z c).set w d

/-- The terms `f` evaluate to `v`, in the words of `v₀`. -/
def Rel (v₀ : CState) (f : VG.Proof.ChaCha20.X86_64.Avx512.ES) (v : CState) : Prop := ∀ k (hk : k < 16), (f k).eval v₀ = v[k]

theorem Rel.set {v₀ : CState} {f : VG.Proof.ChaCha20.X86_64.Avx512.ES} {v : CState} (h : VG.Proof.ChaCha20.X86_64.Avx512.Rel v₀ f v) {i : Nat} (hi : i < 16) {x : VG.Proof.ChaCha20.X86_64.Avx512.E}
    {y : Word} (hx : x.eval v₀ = y) : VG.Proof.ChaCha20.X86_64.Avx512.Rel v₀ (f.set i x) (v.set i y hi) := by
  intro k hk
  simp only [ES.set, Vector.getElem_set]
  by_cases e : k = i
  · subst e; simp [hx]
  · simp only [e, ite_false, Ne.symm e]; exact h k hk

theorem Rel.step {v₀ : CState} {f : VG.Proof.ChaCha20.X86_64.Avx512.ES} {v : CState} (h : VG.Proof.ChaCha20.X86_64.Avx512.Rel v₀ f v) (i : VG.Proof.ChaCha20.X86_64.Avx512.ZI) :
    VG.Proof.ChaCha20.X86_64.Avx512.Rel v₀ (VG.Proof.ChaCha20.X86_64.Avx512.zstepE f i) (VG.Proof.ChaCha20.X86_64.Avx512.zstep v i) := by
  cases i with
  | add d a b => exact h.set (VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt d) (by simp only [E.eval, h _ (VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt a), h _ (VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt b)])
  | xor d a b => exact h.set (VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt d) (by simp only [E.eval, h _ (VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt a), h _ (VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt b)])
  | rol d a n => exact h.set (VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt d) (by simp only [E.eval, h _ (VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt a)])

theorem Rel.foldl {v₀ : CState} {f : VG.Proof.ChaCha20.X86_64.Avx512.ES} {v : CState} (h : VG.Proof.ChaCha20.X86_64.Avx512.Rel v₀ f v) :
    ∀ is : List VG.Proof.ChaCha20.X86_64.Avx512.ZI, VG.Proof.ChaCha20.X86_64.Avx512.Rel v₀ (is.foldl VG.Proof.ChaCha20.X86_64.Avx512.zstepE f) (is.foldl VG.Proof.ChaCha20.X86_64.Avx512.zstep v)
  | [] => h
  | i :: is => (h.step i).foldl is

theorem Rel.qround {v₀ : CState} {f : VG.Proof.ChaCha20.X86_64.Avx512.ES} {v : CState} (h : VG.Proof.ChaCha20.X86_64.Avx512.Rel v₀ f v) (x y z w : Fin 16) :
    VG.Proof.ChaCha20.X86_64.Avx512.Rel v₀ (VG.Proof.ChaCha20.X86_64.Avx512.qroundE f x y z w) (VG.Spec.ChaCha20.qround v x y z w) := by
  simp only [VG.Proof.ChaCha20.X86_64.Avx512.qroundE]
  refine (((h.set x.2 ?_).set y.2 ?_).set z.2 ?_).set w.2 ?_ <;>
    simp only [E.eval, h _ x.2, h _ y.2, h _ z.2, h _ w.2, Fin.getElem_fin]

/-- The words of a state, as terms. -/
def vars : VG.Proof.ChaCha20.X86_64.Avx512.ES := .var

theorem rel_vars (v : CState) : VG.Proof.ChaCha20.X86_64.Avx512.Rel v VG.Proof.ChaCha20.X86_64.Avx512.vars v := fun k hk => by simp [VG.Proof.ChaCha20.X86_64.Avx512.vars, E.eval, hk]

theorem Rel.eq {v₀ : CState} {f : VG.Proof.ChaCha20.X86_64.Avx512.ES} {v v' : CState} (h : VG.Proof.ChaCha20.X86_64.Avx512.Rel v₀ f v) (h' : VG.Proof.ChaCha20.X86_64.Avx512.Rel v₀ f v') : v = v' :=
  Vector.ext fun k hk => (h k hk).symm.trans (h' k hk)

/-- Two states of terms agree on the words of a state. -/
def ES.eq16 (f g : VG.Proof.ChaCha20.X86_64.Avx512.ES) : Bool := (List.range 16).all fun k => f k == g k

theorem Rel.of_eq16 {v₀ : CState} {f g : VG.Proof.ChaCha20.X86_64.Avx512.ES} {v : CState} (h : VG.Proof.ChaCha20.X86_64.Avx512.Rel v₀ f v) (e : ES.eq16 f g = true) :
    VG.Proof.ChaCha20.X86_64.Avx512.Rel v₀ g v := by
  intro k hk
  simp only [ES.eq16, List.all_eq_true, List.mem_range, beq_iff_eq] at e
  rw [← e k hk]; exact h k hk

def cols : List (Nat × Nat × Nat × Nat) := [(0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15)]
def diags : List (Nat × Nat × Nat × Nat) := [(0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14)]

theorem cols_eq (v : CState) :
    (VG.Proof.ChaCha20.X86_64.Avx512.quartersZ VG.Proof.ChaCha20.X86_64.Avx512.cols).foldl VG.Proof.ChaCha20.X86_64.Avx512.zstep v =
      VG.Spec.ChaCha20.qround (VG.Spec.ChaCha20.qround (VG.Spec.ChaCha20.qround (VG.Spec.ChaCha20.qround v 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15 := by
  have e : ES.eq16 ((VG.Proof.ChaCha20.X86_64.Avx512.quartersZ VG.Proof.ChaCha20.X86_64.Avx512.cols).foldl VG.Proof.ChaCha20.X86_64.Avx512.zstepE VG.Proof.ChaCha20.X86_64.Avx512.vars)
      (VG.Proof.ChaCha20.X86_64.Avx512.qroundE (VG.Proof.ChaCha20.X86_64.Avx512.qroundE (VG.Proof.ChaCha20.X86_64.Avx512.qroundE (VG.Proof.ChaCha20.X86_64.Avx512.qroundE VG.Proof.ChaCha20.X86_64.Avx512.vars 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15) = true := by
    decide +kernel
  exact (((VG.Proof.ChaCha20.X86_64.Avx512.rel_vars v).foldl _).of_eq16 e).eq
    ((((VG.Proof.ChaCha20.X86_64.Avx512.rel_vars v).qround 0 4 8 12).qround 1 5 9 13 |>.qround 2 6 10 14).qround 3 7 11 15)

theorem diags_eq (v : CState) :
    (VG.Proof.ChaCha20.X86_64.Avx512.quartersZ VG.Proof.ChaCha20.X86_64.Avx512.diags).foldl VG.Proof.ChaCha20.X86_64.Avx512.zstep v =
      VG.Spec.ChaCha20.qround (VG.Spec.ChaCha20.qround (VG.Spec.ChaCha20.qround (VG.Spec.ChaCha20.qround v 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14 := by
  have e : ES.eq16 ((VG.Proof.ChaCha20.X86_64.Avx512.quartersZ VG.Proof.ChaCha20.X86_64.Avx512.diags).foldl VG.Proof.ChaCha20.X86_64.Avx512.zstepE VG.Proof.ChaCha20.X86_64.Avx512.vars)
      (VG.Proof.ChaCha20.X86_64.Avx512.qroundE (VG.Proof.ChaCha20.X86_64.Avx512.qroundE (VG.Proof.ChaCha20.X86_64.Avx512.qroundE (VG.Proof.ChaCha20.X86_64.Avx512.qroundE VG.Proof.ChaCha20.X86_64.Avx512.vars 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14) = true := by
    decide +kernel
  exact (((VG.Proof.ChaCha20.X86_64.Avx512.rel_vars v).foldl _).of_eq16 e).eq
    ((((VG.Proof.ChaCha20.X86_64.Avx512.rel_vars v).qround 0 5 10 15).qround 1 6 11 12 |>.qround 2 7 8 13).qround 3 4 9 14)

theorem innerBlock_eq (v : CState) : (VG.Proof.ChaCha20.X86_64.Avx512.quartersZ VG.Proof.ChaCha20.X86_64.Avx512.cols ++ VG.Proof.ChaCha20.X86_64.Avx512.quartersZ VG.Proof.ChaCha20.X86_64.Avx512.diags).foldl VG.Proof.ChaCha20.X86_64.Avx512.zstep v = innerBlock v := by
  rw [List.foldl_append, VG.Proof.ChaCha20.X86_64.Avx512.cols_eq, VG.Proof.ChaCha20.X86_64.Avx512.diags_eq]; rfl

theorem doubleRound_eq : doubleRound = (VG.Proof.ChaCha20.X86_64.Avx512.quartersZ VG.Proof.ChaCha20.X86_64.Avx512.cols ++ VG.Proof.ChaCha20.X86_64.Avx512.quartersZ VG.Proof.ChaCha20.X86_64.Avx512.diags).map ZI.instr := by
  simp only [doubleRound, VG.Proof.ChaCha20.X86_64.Avx512.quarters_eq, List.map_append, VG.Proof.ChaCha20.X86_64.Avx512.cols, VG.Proof.ChaCha20.X86_64.Avx512.diags]

/-! ## The rounds on the sixteen blocks -/

theorem Same.trans {s₀ s₁ s₂ : State} (h₁ : VG.Proof.ChaCha20.X86_64.Avx512.Same s₀ s₁) (h₂ : VG.Proof.ChaCha20.X86_64.Avx512.Same s₁ s₂) : VG.Proof.ChaCha20.X86_64.Avx512.Same s₀ s₂ :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem doubleRound_ok {vs : Nat → CState} {s : State} (h : VG.Proof.ChaCha20.X86_64.Avx512.ZH vs s) :
    WP isa (.block doubleRound) s fun s' => VG.Proof.ChaCha20.X86_64.Avx512.ZH (fun j => innerBlock (vs j)) s' ∧ VG.Proof.ChaCha20.X86_64.Avx512.Same s s' := by
  have e : (fun j => (VG.Proof.ChaCha20.X86_64.Avx512.quartersZ VG.Proof.ChaCha20.X86_64.Avx512.cols ++ VG.Proof.ChaCha20.X86_64.Avx512.quartersZ VG.Proof.ChaCha20.X86_64.Avx512.diags).foldl VG.Proof.ChaCha20.X86_64.Avx512.zstep (vs j)) = fun j => innerBlock (vs j) :=
    funext fun j => VG.Proof.ChaCha20.X86_64.Avx512.innerBlock_eq (vs j)
  rw [VG.Proof.ChaCha20.X86_64.Avx512.doubleRound_eq]
  exact WP.mono (VG.Proof.ChaCha20.X86_64.Avx512.block_ok _ h) fun _ ⟨h', hs⟩ => ⟨e ▸ h', hs⟩

theorem rounds_ok {vs : Nat → CState} {s₀ : State} (h : VG.Proof.ChaCha20.X86_64.Avx512.ZH vs s₀) :
    ∀ n, WP isa (rounds n) s₀ fun s => VG.Proof.ChaCha20.X86_64.Avx512.ZH (fun j => Nat.repeat innerBlock n (vs j)) s ∧ VG.Proof.ChaCha20.X86_64.Avx512.Same s₀ s
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.Avx512.rounds_ok h n) fun _ ⟨h₁, hs⟩ =>
      WP.mono (VG.Proof.ChaCha20.X86_64.Avx512.doubleRound_ok h₁) fun _ ⟨h₂, hs'⟩ => ⟨h₂, hs.trans hs'⟩)

end VG.Proof.ChaCha20.X86_64.Avx512

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Sym`. -/
section

/-!
# ChaCha20 on x86-64 with AVX-512: straight-line code, doubleword by doubleword

Outside the rounds, every instruction of the code moves, adds or XORs
doublewords of `zmm` registers and of three regions of memory: the state (at
`rdi`), `buf` (at `rcx`) and 1024 bytes of data (at `rsi`). `Sym.run` computes
each doubleword after a block of such instructions as a term (`T`) in the
doublewords before it, and `run_ok` proves the machine agrees; the terms
themselves are then compared by the kernel.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx512

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word)

/-- The base register of region `b`: the state, `buf` and the data. -/
def baseR : Nat → Reg
  | 0 => .rdi | 1 => .rcx | _ => .rsi

/-- The doublewords of region `b`. -/
def bsize : Nat → Nat
  | 0 => 16 | 1 => 80 | _ => 256

/-- The doublewords of region `b` that may be written: the saved registers in
`buf`, and the data. -/
def wsize : Nat → Nat
  | 0 => 0 | 1 => 32 | _ => 256

def bidx : Reg → Option Nat
  | .rdi => some 0 | .rcx => some 1 | .rsi => some 2 | _ => none

theorem bidx_some {r : Reg} {b : Nat} (h : VG.Proof.ChaCha20.X86_64.Avx512.bidx r = some b) : r = VG.Proof.ChaCha20.X86_64.Avx512.baseR b ∧ b < 3 := by
  cases r <;> simp only [VG.Proof.ChaCha20.X86_64.Avx512.bidx, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> decide

/-- Region `b`, where the code starts. -/
def regn (s₀ : State) (b : Nat) : Region := ⟨s₀.gpr (VG.Proof.ChaCha20.X86_64.Avx512.baseR b), 4 * VG.Proof.ChaCha20.X86_64.Avx512.bsize b⟩

/-- The regions written. -/
def wregs (s₀ : State) : List Region := [⟨s₀.gpr .rcx, 128⟩, ⟨s₀.gpr .rsi, 1024⟩]

/-- A doubleword, from the doublewords where the code starts. -/
inductive T
  /-- Doubleword `p` of `zmm r`. -/
  | reg (r p : Nat)
  /-- Doubleword `i` of region `b`. -/
  | mem (b i : Nat)
  | add (a b : VG.Proof.ChaCha20.X86_64.Avx512.T)
  | xor (a b : VG.Proof.ChaCha20.X86_64.Avx512.T)
  deriving DecidableEq

def T.eval (s₀ : State) : VG.Proof.ChaCha20.X86_64.Avx512.T → Word
  | .reg r p => VG.Proof.ChaCha20.X86_64.Avx512.zw s₀ (zreg r) p
  | .mem b i => s₀.mem.readW ((VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 32
  | .add a b => a.eval s₀ + b.eval s₀
  | .xor a b => a.eval s₀ ^^^ b.eval s₀

/-- The doublewords of the registers (by `xidx`) and regions, as terms. -/
structure Sym where
  reg : Nat → Nat → VG.Proof.ChaCha20.X86_64.Avx512.T
  mem : Nat → Nat → VG.Proof.ChaCha20.X86_64.Avx512.T
  /-- Whether memory may have been written. -/
  dirty : Bool

def Sym.init : VG.Proof.ChaCha20.X86_64.Avx512.Sym := ⟨.reg, .mem, false⟩

def Sym.setReg (σ : VG.Proof.ChaCha20.X86_64.Avx512.Sym) (d : Nat) (f : Nat → VG.Proof.ChaCha20.X86_64.Avx512.T) : VG.Proof.ChaCha20.X86_64.Avx512.Sym :=
  { σ with reg := fun r p => if r = d then f p else σ.reg r p }

/-- The two-bit field `i` of `o`. -/
def sel2 (o i : Nat) : Nat := o / 4 ^ i % 4

/-- Whether `zbinT` represents doubleword `p` of `op a b` as a term in
doublewords of `a` and `b`. Only its supported operations are accepted. -/
def dwordwise : ZBinOp → Bool
  | .vpaddd | .vpxord | .vpunpckldq | .vpunpckhdq | .vpunpcklqdq | .vpunpckhqdq => true
  | _ => false

/-- Doubleword `p` of `op a b`, for an operation that is `dwordwise`. -/
def zbinT (op : ZBinOp) (A B : Nat → VG.Proof.ChaCha20.X86_64.Avx512.T) (p : Nat) : VG.Proof.ChaCha20.X86_64.Avx512.T :=
  match op with
  | .vpaddd => .add (A (4 * (p / 4) + p % 4)) (B (4 * (p / 4) + p % 4))
  | .vpxord => .xor (A (4 * (p / 4) + p % 4)) (B (4 * (p / 4) + p % 4))
  | .vpunpckldq => if p % 4 % 2 = 0 then A (4 * (p / 4) + p % 4 / 2) else B (4 * (p / 4) + p % 4 / 2)
  | .vpunpckhdq =>
    if p % 4 % 2 = 0 then A (4 * (p / 4) + (2 + p % 4 / 2)) else B (4 * (p / 4) + (2 + p % 4 / 2))
  | .vpunpcklqdq => if p % 4 < 2 then A (4 * (p / 4) + p % 4) else B (4 * (p / 4) + (p % 4 - 2))
  | .vpunpckhqdq => if p % 4 < 2 then A (4 * (p / 4) + (2 + p % 4)) else B (4 * (p / 4) + p % 4)
  | _ => .reg 0 0

/-- The region and first doubleword of an access of `n` doublewords, within
the first `lim b` doublewords of its region `b`. -/
def slot (m : MemOp) (n : Nat) (lim : Nat → Nat) : Option (Nat × Nat) :=
  match VG.Proof.ChaCha20.X86_64.Avx512.bidx m.base, m.index, m.disp with
  | some b, none, .ofNat d => if d % 4 = 0 ∧ d / 4 + n ≤ lim b then some (b, d / 4) else none
  | _, _, _ => none

def Sym.step (σ : VG.Proof.ChaCha20.X86_64.Avx512.Sym) : Instr → Option VG.Proof.ChaCha20.X86_64.Avx512.Sym
  | .zop (.zbin op d a b) =>
    if VG.Proof.ChaCha20.X86_64.Avx512.dwordwise op then some (σ.setReg (VG.Proof.ChaCha20.X86_64.Avx512.xidx d) (VG.Proof.ChaCha20.X86_64.Avx512.zbinT op (σ.reg (VG.Proof.ChaCha20.X86_64.Avx512.xidx a)) (σ.reg (VG.Proof.ChaCha20.X86_64.Avx512.xidx b)))) else none
  | .zop (.vpshufd d a o) =>
    some (σ.setReg (VG.Proof.ChaCha20.X86_64.Avx512.xidx d) fun p => σ.reg (VG.Proof.ChaCha20.X86_64.Avx512.xidx a) (4 * (p / 4) + VG.Proof.ChaCha20.X86_64.Avx512.sel2 o.toNat (p % 4)))
  | .zop (.vshufi32x4 d a b n) =>
    some (σ.setReg (VG.Proof.ChaCha20.X86_64.Avx512.xidx d) fun p =>
      (if p / 4 < 2 then σ.reg (VG.Proof.ChaCha20.X86_64.Avx512.xidx a) else σ.reg (VG.Proof.ChaCha20.X86_64.Avx512.xidx b)) (4 * VG.Proof.ChaCha20.X86_64.Avx512.sel2 n.toNat (p / 4) + p % 4))
  | .vmovdqu32Load d m => (VG.Proof.ChaCha20.X86_64.Avx512.slot m 16 VG.Proof.ChaCha20.X86_64.Avx512.bsize).map fun (b, i) => σ.setReg (VG.Proof.ChaCha20.X86_64.Avx512.xidx d) fun p => σ.mem b (i + p)
  | .vbroadcasti32x4 d m =>
    (VG.Proof.ChaCha20.X86_64.Avx512.slot m 4 VG.Proof.ChaCha20.X86_64.Avx512.bsize).map fun (b, i) => σ.setReg (VG.Proof.ChaCha20.X86_64.Avx512.xidx d) fun p => σ.mem b (i + p % 4)
  | .vmovdqu32Store m r => (VG.Proof.ChaCha20.X86_64.Avx512.slot m 16 VG.Proof.ChaCha20.X86_64.Avx512.wsize).map fun (b, i) =>
    { σ with
      mem := fun b' i' => if b' = b ∧ i ≤ i' ∧ i' < i + 16 then σ.reg (VG.Proof.ChaCha20.X86_64.Avx512.xidx r) (i' - i) else σ.mem b' i'
      dirty := true }
  | _ => none

def Sym.run (σ : VG.Proof.ChaCha20.X86_64.Avx512.Sym) : List Instr → Option VG.Proof.ChaCha20.X86_64.Avx512.Sym
  | [] => some σ
  | i :: is => (σ.step i).bind fun σ' => σ'.run is

/-! ## The machine agrees -/

theorem ofInt_ofNat (d : Nat) : BitVec.ofInt 64 (Int.ofNat d) = BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toInt_eq; simp

theorem add_ofNat' (p : Addr) (d e : Nat) :
    p + BitVec.ofNat 64 d + BitVec.ofNat 64 e = p + BitVec.ofNat 64 (d + e) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem slot_ok {m : MemOp} {n : Nat} {lim : Nat → Nat} {b i : Nat} (h : VG.Proof.ChaCha20.X86_64.Avx512.slot m n lim = some (b, i)) :
    b < 3 ∧ i + n ≤ lim b ∧ ∀ s : State, s.ea m = s.gpr (VG.Proof.ChaCha20.X86_64.Avx512.baseR b) + BitVec.ofNat 64 (4 * i) := by
  unfold VG.Proof.ChaCha20.X86_64.Avx512.slot at h
  split at h
  · rename_i b' d hb hi hd
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨e, hb3⟩ := VG.Proof.ChaCha20.X86_64.Avx512.bidx_some hb
      refine ⟨hb3, hc.2, fun s => ?_⟩
      simp only [State.ea, hi, hd, VG.Proof.ChaCha20.X86_64.Avx512.ofInt_ofNat, ← e]
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hc.1)]
    · cases h
  · cases h

theorem bsize_le (b : Nat) : VG.Proof.ChaCha20.X86_64.Avx512.bsize b ≤ 256 := by
  unfold VG.Proof.ChaCha20.X86_64.Avx512.bsize; split <;> decide

theorem wsize_le (b : Nat) : VG.Proof.ChaCha20.X86_64.Avx512.wsize b ≤ VG.Proof.ChaCha20.X86_64.Avx512.bsize b := by
  unfold VG.Proof.ChaCha20.X86_64.Avx512.wsize VG.Proof.ChaCha20.X86_64.Avx512.bsize; split <;> decide

theorem regn_contains (s₀ : State) {b i n : Nat} (h : i + n ≤ VG.Proof.ChaCha20.X86_64.Avx512.bsize b) :
    (VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).Contains ((VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).base + BitVec.ofNat 64 (4 * i)) (4 * n) := by
  have := VG.Proof.ChaCha20.X86_64.Avx512.bsize_le b
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat _ (by omega)]
  simp only [VG.Proof.ChaCha20.X86_64.Avx512.regn]; omega

/-- The regions: writable (and so readable) and disjoint. -/
structure Ctx (s₀ : State) : Prop where
  w : ∀ b i n, b < 3 → i + n ≤ VG.Proof.ChaCha20.X86_64.Avx512.bsize b →
    InRegions s₀.wr ((VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).base + BitVec.ofNat 64 (4 * i)) (4 * n)
  d : ∀ b b', b < 3 → b' < 3 → b ≠ b' → (VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).Disjoint (VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b')

/-- The terms `σ` hold in `s`. -/
structure SRel (σ : VG.Proof.ChaCha20.X86_64.Avx512.Sym) (s₀ s : State) : Prop where
  reg : ∀ r p, p < 16 → VG.Proof.ChaCha20.X86_64.Avx512.zw s r p = (σ.reg (VG.Proof.ChaCha20.X86_64.Avx512.xidx r) p).eval s₀
  mem : ∀ b i, b < 3 → i < VG.Proof.ChaCha20.X86_64.Avx512.bsize b →
    s.mem.readW ((VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 32 = (σ.mem b i).eval s₀
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (VG.Proof.ChaCha20.X86_64.Avx512.wregs s₀) s₀.mem s.mem
  clean : σ.dirty = false → s.mem = s₀.mem

theorem zreg_xidx (r : XReg) : zreg (VG.Proof.ChaCha20.X86_64.Avx512.xidx r) = r := by cases r <;> rfl

theorem SRel.init (s₀ : State) : VG.Proof.ChaCha20.X86_64.Avx512.SRel Sym.init s₀ s₀ :=
  ⟨fun r p _ => by simp only [Sym.init, T.eval, VG.Proof.ChaCha20.X86_64.Avx512.zreg_xidx], fun _ _ _ _ => rfl, rfl, rfl, rfl,
    Frame.refl _ _, fun _ => rfl⟩

theorem SRel.setReg {σ : VG.Proof.ChaCha20.X86_64.Avx512.Sym} {s₀ s s' : State} (h : VG.Proof.ChaCha20.X86_64.Avx512.SRel σ s₀ s) {d : XReg} {f : Nat → VG.Proof.ChaCha20.X86_64.Avx512.T}
    (hz : ∀ r p, p < 16 → VG.Proof.ChaCha20.X86_64.Avx512.zw s' r p = if r = d then (f p).eval s₀ else VG.Proof.ChaCha20.X86_64.Avx512.zw s r p)
    (hm : s'.mem = s.mem) (hg : s'.gpr = s.gpr) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) :
    VG.Proof.ChaCha20.X86_64.Avx512.SRel (σ.setReg (VG.Proof.ChaCha20.X86_64.Avx512.xidx d) f) s₀ s' := by
  refine ⟨fun r p hp => ?_, fun b i hb hi => by rw [hm]; exact h.mem b i hb hi, hg.trans h.gpr,
    hr.trans h.rd, hw.trans h.wr, hm ▸ h.frame, fun hd => hm.trans (h.clean hd)⟩
  rw [hz r p hp]
  simp only [Sym.setReg, VG.Proof.ChaCha20.X86_64.Avx512.xidx_inj]
  split
  · rfl
  · exact h.reg r p hp

/-! ### Lane operations -/

theorem zw_split {s : State} {r : XReg} {p : Nat} : VG.Proof.ChaCha20.X86_64.Avx512.zw s r p = dword (s.zlane r (p / 4)) (p % 4) := rfl

theorem zbinT_eval {op : ZBinOp} (hop : VG.Proof.ChaCha20.X86_64.Avx512.dwordwise op = true) {A B : Nat → VG.Proof.ChaCha20.X86_64.Avx512.T} {s₀ : State}
    {x y : BitVec 128} {p : Nat}
    (hA : ∀ k, k < 4 → (A (4 * (p / 4) + k)).eval s₀ = dword x k)
    (hB : ∀ k, k < 4 → (B (4 * (p / 4) + k)).eval s₀ = dword y k) :
    (VG.Proof.ChaCha20.X86_64.Avx512.zbinT op A B p).eval s₀ = dword (op.sse.eval x y) (p % 4) := by
  have hq : p % 4 < 4 := Nat.mod_lt _ (by decide)
  simp only [VG.Proof.ChaCha20.X86_64.Avx512.zbinT]
  generalize p % 4 = q at *
  generalize 4 * (p / 4) = l at *
  have a0 := hA 0 (by decide); have a1 := hA 1 (by decide)
  have a2 := hA 2 (by decide); have a3 := hA 3 (by decide)
  have b0 := hB 0 (by decide); have b1 := hB 1 (by decide)
  have b2 := hB 2 (by decide); have b3 := hB 3 (by decide)
  rcases cases4 hq with rfl | rfl | rfl | rfl <;> cases op <;> (try cases hop) <;>
    simp only [ZBinOp.sse, T.eval, dword_paddd _ _ (show (0 : Nat) < 4 by decide),
      dword_paddd _ _ (show (1 : Nat) < 4 by decide), dword_paddd _ _ (show (2 : Nat) < 4 by decide),
      dword_paddd _ _ (show (3 : Nat) < 4 by decide), dword_pxor, dword_punpckldq, dword_punpckhdq,
      punpcklqdq_eq, punpckhqdq_eq, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
      dword_ofDwords_3, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff,
      ite_true, ite_false, a0, a1, a2, a3, b0, b1, b2, b3]

theorem zw_lk (s : State) (r : XReg) {l k : Nat} (hk : k < 4) :
    VG.Proof.ChaCha20.X86_64.Avx512.zw s r (4 * l + k) = dword (s.zlane r l) k := by
  simp only [VG.Proof.ChaCha20.X86_64.Avx512.zw_split]; rw [show (4 * l + k) / 4 = l by omega, show (4 * l + k) % 4 = k by omega]

theorem sel2_eq (o : BitVec 8) (i : Nat) : (o.extractLsb' (2 * i) 2).toNat = VG.Proof.ChaCha20.X86_64.Avx512.sel2 o.toNat i := by
  simp only [BitVec.extractLsb'_toNat, VG.Proof.ChaCha20.X86_64.Avx512.sel2, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem sel2_lt (o i : Nat) : VG.Proof.ChaCha20.X86_64.Avx512.sel2 o i < 4 := Nat.mod_lt _ (by decide)

theorem pick4_same (v : BitVec 128) {i : Nat} (hi : i < 4) : pick4 v v v v i = v := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl

theorem pick4_ext (v : BitVec 512) {l : Nat} (hl : l < 4) :
    pick4 (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128) (v.extractLsb' 384 128) l =
      v.extractLsb' (128 * l) 128 := by
  rcases cases4 hl with rfl | rfl | rfl | rfl <;> rfl

theorem dword_read512 (m : Mem) (a : Addr) {p : Nat} (hp : p < 16) :
    dword ((m.readW a 512).extractLsb' (128 * (p / 4)) 128) (p % 4) =
      m.readW (a + BitVec.ofNat 64 (4 * p)) 32 := by
  rw [dword, extract_extract _ _ _ _ _ (by omega), show 128 * (p / 4) + 32 * (p % 4) = 8 * (4 * p) by omega]
  exact readW_extract m a (w := 512) (k := 4 * p) (n := 4) (by omega)

theorem in_regn {s₀ s : State} (hc : VG.Proof.ChaCha20.X86_64.Avx512.Ctx s₀) {b : Nat} (hb : b < 3) (hw : s.wr = s₀.wr) {i n : Nat}
    (h : i + n ≤ VG.Proof.ChaCha20.X86_64.Avx512.bsize b) : InRegions s.wr ((VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).base + BitVec.ofNat 64 (4 * i)) (4 * n) :=
  hw ▸ hc.w b i n hb h

theorem in_regn' {s₀ s : State} (hc : VG.Proof.ChaCha20.X86_64.Avx512.Ctx s₀) {b : Nat} (hb : b < 3) (hw : s.wr = s₀.wr) {i n : Nat}
    (h : i + n ≤ VG.Proof.ChaCha20.X86_64.Avx512.bsize b) : InRegions (s.rd ++ s.wr) ((VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).base + BitVec.ofNat 64 (4 * i)) (4 * n) :=
  let ⟨r, hr, hc'⟩ := VG.Proof.ChaCha20.X86_64.Avx512.in_regn hc hb hw h; ⟨r, List.mem_append_right _ hr, hc'⟩

/-- One instruction. -/
theorem sstep_ok {s₀ : State} (hc : VG.Proof.ChaCha20.X86_64.Avx512.Ctx s₀) {σ σ' : VG.Proof.ChaCha20.X86_64.Avx512.Sym} {s : State} (h : VG.Proof.ChaCha20.X86_64.Avx512.SRel σ s₀ s) {i : Instr}
    (e : σ.step i = some σ') : ∃ s', exec i s = some s' ∧ VG.Proof.ChaCha20.X86_64.Avx512.SRel σ' s₀ s' := by
  unfold Sym.step at e
  split at e
  · rename_i op d a b
    split at e
    case isFalse => cases e
    rename_i hop
    cases e
    refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    rw [VG.Proof.ChaCha20.X86_64.Avx512.zw_split, zlane_zbin _ _ _ _ _ _ (VG.Proof.ChaCha20.X86_64.Avx512.div4_lt hp)]
    split
    · exact (VG.Proof.ChaCha20.X86_64.Avx512.zbinT_eval hop (fun k hk => (h.reg a _ (by omega)).symm.trans (VG.Proof.ChaCha20.X86_64.Avx512.zw_lk s a hk))
        (fun k hk => (h.reg b _ (by omega)).symm.trans (VG.Proof.ChaCha20.X86_64.Avx512.zw_lk s b hk))).symm
    · rfl
  · rename_i d a o
    cases e
    refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    rw [VG.Proof.ChaCha20.X86_64.Avx512.zw_split, zlane_vpshufd _ _ _ _ _ (VG.Proof.ChaCha20.X86_64.Avx512.div4_lt hp)]
    split
    · rw [dword_shufDwords _ _ (VG.Proof.ChaCha20.X86_64.Avx512.mod4_lt p), VG.Proof.ChaCha20.X86_64.Avx512.sel2_eq, ← VG.Proof.ChaCha20.X86_64.Avx512.zw_lk s a (VG.Proof.ChaCha20.X86_64.Avx512.sel2_lt _ _)]
      exact h.reg a _ (by have := VG.Proof.ChaCha20.X86_64.Avx512.sel2_lt o.toNat (p % 4); omega)
    · rfl
  · rename_i d a b n
    cases e
    refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    rw [VG.Proof.ChaCha20.X86_64.Avx512.zw_split, zlane_vshufi32x4 _ _ _ _ _ _ (VG.Proof.ChaCha20.X86_64.Avx512.div4_lt hp)]
    split
    · rw [shuf4Lanes_eq, VG.Proof.ChaCha20.X86_64.Avx512.sel2_eq]
      have := VG.Proof.ChaCha20.X86_64.Avx512.sel2_lt n.toNat (p / 4)
      by_cases hl : p / 4 < 2
      · simp only [hl, ite_true]
        rw [← VG.Proof.ChaCha20.X86_64.Avx512.zw_lk s a (VG.Proof.ChaCha20.X86_64.Avx512.mod4_lt p)]; exact h.reg a _ (by omega)
      · simp only [hl, ite_false]
        rw [← VG.Proof.ChaCha20.X86_64.Avx512.zw_lk s b (VG.Proof.ChaCha20.X86_64.Avx512.mod4_lt p)]; exact h.reg b _ (by omega)
    · rfl
  · rename_i d m
    obtain ⟨⟨b, i⟩, hs, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨hb, hi, hea⟩ := VG.Proof.ChaCha20.X86_64.Avx512.slot_ok hs
    have ea : s.ea m = (VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
    have hin := VG.Proof.ChaCha20.X86_64.Avx512.in_regn' hc hb h.wr hi
    refine ⟨s.setZ d ((s.mem.readW ((VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 512).extractLsb' 0 128)
      ((s.mem.readW ((VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 512).extractLsb' 128 128)
      ((s.mem.readW ((VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 512).extractLsb' 256 128)
      ((s.mem.readW ((VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 512).extractLsb' 384 128), by simp only [exec, ea, State.load512, hin, ite_true, Option.map_some],
      h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    rw [VG.Proof.ChaCha20.X86_64.Avx512.zw_split, State.zlane_setZ _ _ _ _ _ _ _ (VG.Proof.ChaCha20.X86_64.Avx512.div4_lt hp)]
    split
    · rw [VG.Proof.ChaCha20.X86_64.Avx512.pick4_ext _ (VG.Proof.ChaCha20.X86_64.Avx512.div4_lt hp), VG.Proof.ChaCha20.X86_64.Avx512.dword_read512 _ _ hp, VG.Proof.ChaCha20.X86_64.Avx512.add_ofNat', ← Nat.mul_add]
      exact h.mem b (i + p) hb (by omega)
    · rfl
  · rename_i d m
    obtain ⟨⟨b, i⟩, hs, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨hb, hi, hea⟩ := VG.Proof.ChaCha20.X86_64.Avx512.slot_ok hs
    have ea : s.ea m = (VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
    have hin := VG.Proof.ChaCha20.X86_64.Avx512.in_regn' hc hb h.wr hi
    refine ⟨s.setZ d (s.mem.readW ((VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 128)
      (s.mem.readW ((VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 128)
      (s.mem.readW ((VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 128)
      (s.mem.readW ((VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 128), by simp only [exec, ea, State.load128, hin, ite_true, Option.map_some],
      h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    rw [VG.Proof.ChaCha20.X86_64.Avx512.zw_split, State.zlane_setZ _ _ _ _ _ _ _ (VG.Proof.ChaCha20.X86_64.Avx512.div4_lt hp)]
    split
    · rw [VG.Proof.ChaCha20.X86_64.Avx512.pick4_same _ (VG.Proof.ChaCha20.X86_64.Avx512.div4_lt hp), dword_readW _ _ (VG.Proof.ChaCha20.X86_64.Avx512.mod4_lt p), VG.Proof.ChaCha20.X86_64.Avx512.add_ofNat', ← Nat.mul_add]
      exact h.mem b (i + p % 4) hb (by have := VG.Proof.ChaCha20.X86_64.Avx512.mod4_lt p; omega)
    · rfl
  · rename_i m r
    obtain ⟨⟨b, i⟩, hs, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨hb, hi, hea⟩ := VG.Proof.ChaCha20.X86_64.Avx512.slot_ok hs
    have hi' : i + 16 ≤ VG.Proof.ChaCha20.X86_64.Avx512.bsize b := Nat.le_trans hi (VG.Proof.ChaCha20.X86_64.Avx512.wsize_le b)
    have hb0 : b = 1 ∨ b = 2 := by
      rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | e | e
      · simp [VG.Proof.ChaCha20.X86_64.Avx512.wsize] at hi
      · exact .inl e
      · exact .inr e
    have ea : s.ea m = (VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
    have hin := VG.Proof.ChaCha20.X86_64.Avx512.in_regn hc hb h.wr hi'
    refine ⟨s.setMem (s.mem.writeW ((VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b).base + BitVec.ofNat 64 (4 * i)) (s.zmm r)),
      by simp only [exec, ea, State.store512_eq, hin, ite_true], ⟨fun r' p hp => ?_,
      fun b' i' hb' hi'' => ?_, by simp [h.gpr], by simp [h.rd], by simp [h.wr], ?_, fun hd => by cases hd⟩⟩
    · simp only [VG.Proof.ChaCha20.X86_64.Avx512.zw_split, State.setMem_zlane]; exact h.reg r' p hp
    · simp only [State.setMem_mem]
      by_cases hx : b' = b ∧ i ≤ i' ∧ i' < i + 16
      · obtain ⟨rfl, h₁, h₂⟩ := hx
        simp only [and_self, h₁, h₂, ite_true]
        rw [show (VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b').base + BitVec.ofNat 64 (4 * i') =
            (VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b').base + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 (4 * (i' - i)) by
          rw [VG.Proof.ChaCha20.X86_64.Avx512.add_ofNat']; congr 2; omega]
        refine (readW_writeW_inside s.mem _ (s.zmm r) (k := 4 * (i' - i)) (n := 4) (by omega)
          (by decide)).trans ?_
        rw [show 8 * (4 * (i' - i)) = 8 * (16 * ((i' - i) / 4) + 4 * ((i' - i) % 4)) by omega,
          State.zmm_extract _ _ (by omega) (VG.Proof.ChaCha20.X86_64.Avx512.mod4_lt _), ← VG.Proof.ChaCha20.X86_64.Avx512.zw_split]
        exact h.reg r _ (by omega)
      · rw [ite_eq_right hx]
        by_cases e : b' = b
        · subst e
          have hx' : i' + 1 ≤ i ∨ i + 16 ≤ i' := by omega
          have := VG.Proof.ChaCha20.X86_64.Avx512.bsize_le b'
          exact (VG.X86_64.readW_writeW_off s.mem _ (s.zmm r) (d := 4 * i') (e := 4 * i) (n := 4)
            (by omega) (by omega) (by omega)).trans (h.mem b' i' hb' hi'')
        · have f := (Frame.refl [VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b] s.mem).writeW (List.mem_singleton_self _) (s.zmm r)
            (VG.Proof.ChaCha20.X86_64.Avx512.regn_contains s₀ (n := 16) hi')
          rw [f.readW (r := VG.Proof.ChaCha20.X86_64.Avx512.regn s₀ b') (VG.Proof.ChaCha20.X86_64.Avx512.regn_contains s₀ (n := 1) (by omega))
            (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hc.d b' b hb' hb e)
            (by decide)]
          exact h.mem b' i' hb' hi''
    · simp only [State.setMem_mem]
      refine h.frame.writeW (r := if b = 1 then ⟨s₀.gpr .rcx, 128⟩ else ⟨s₀.gpr .rsi, 1024⟩)
        (by rcases hb0 with rfl | rfl <;> simp [VG.Proof.ChaCha20.X86_64.Avx512.wregs]) _ ?_
      rcases hb0 with rfl | rfl
      · simp only [VG.Proof.ChaCha20.X86_64.Avx512.regn, VG.Proof.ChaCha20.X86_64.Avx512.baseR, Region.Contains, ite_true]
        simp only [VG.Proof.ChaCha20.X86_64.Avx512.wsize] at hi; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega
      · simp only [VG.Proof.ChaCha20.X86_64.Avx512.regn, VG.Proof.ChaCha20.X86_64.Avx512.baseR, Region.Contains, show (2 : Nat) ≠ 1 by decide, ite_false]
        simp only [VG.Proof.ChaCha20.X86_64.Avx512.wsize] at hi; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega
  · cases e

/-- A block of instructions. -/
theorem srun_ok {s₀ : State} (hc : VG.Proof.ChaCha20.X86_64.Avx512.Ctx s₀) :
    ∀ (is : List Instr) {σ σ' : VG.Proof.ChaCha20.X86_64.Avx512.Sym} {s : State}, VG.Proof.ChaCha20.X86_64.Avx512.SRel σ s₀ s → σ.run is = some σ' →
      WP isa (.block is) s (VG.Proof.ChaCha20.X86_64.Avx512.SRel σ' s₀)
  | [], _, _, _, h, e => by cases e; exact WP.block_nil h
  | i :: is, _, _, _, h, e => by
    simp only [Sym.run, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    obtain ⟨s₁, hx, h₁⟩ := VG.Proof.ChaCha20.X86_64.Avx512.sstep_ok hc h e₁
    exact WP.block_cons_iff.2 ⟨s₁, hx, VG.Proof.ChaCha20.X86_64.Avx512.srun_ok hc is h₁ e₂⟩

end VG.Proof.ChaCha20.X86_64.Avx512

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Setup`. -/
section

/-!
# ChaCha20 on x86-64 with AVX-512: the sixteen input states
-/

namespace VG.Proof.ChaCha20.X86_64.Avx512

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Spec.ChaCha20 (Word stateAt)
open VG.Proof.ChaCha20

/-- The counter increments `0, …, 15`, as doublewords at `buf + 128`. -/
def Incs (m : Mem) (buf : Addr) : Prop :=
  ∀ j < 16, m.readW (buf + BitVec.ofNat 64 (4 * (32 + j))) 32 = BitVec.ofNat 32 j

/-- Word `k` of block `p` after the setup: word `k` of the state, plus `p`
for the counter. -/
def setupT (k p : Nat) : VG.Proof.ChaCha20.X86_64.Avx512.T := if k = 12 then .add (.mem 0 12) (.mem 1 (32 + p)) else .mem 0 k

def setupCheck : Bool :=
  match Sym.init.run setup with
  | some σ => !σ.dirty && (List.range 16).all fun k => (List.range 16).all fun p => σ.reg k p == VG.Proof.ChaCha20.X86_64.Avx512.setupT k p
  | none => false

theorem setupCheck_eq : VG.Proof.ChaCha20.X86_64.Avx512.setupCheck = true := by decide +kernel

theorem setup_run : ∃ σ, Sym.init.run setup = some σ ∧ σ.dirty = false ∧
    ∀ k < 16, ∀ p < 16, σ.reg k p = VG.Proof.ChaCha20.X86_64.Avx512.setupT k p := by
  have e := VG.Proof.ChaCha20.X86_64.Avx512.setupCheck_eq
  unfold VG.Proof.ChaCha20.X86_64.Avx512.setupCheck at e
  split at e
  · rename_i σ h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at e
    exact ⟨σ, h, e.1, e.2⟩
  · cases e

theorem stateAt_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 16) :
    m.readW (p + BitVec.ofNat 64 (4 * k)) 32 = (stateAt m p)[k] := by
  simp [stateAt]

theorem setup_ok {s : State} (hc : VG.Proof.ChaCha20.X86_64.Avx512.Ctx s) (hi : VG.Proof.ChaCha20.X86_64.Avx512.Incs s.mem (s.gpr .rcx)) :
    WP isa (.block setup) s fun s' =>
      VG.Proof.ChaCha20.X86_64.Avx512.ZH (fun j => ctr (stateAt s.mem (s.gpr .rdi)) j) s' ∧ s'.mem = s.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨σ, hr, hd, hk⟩ := VG.Proof.ChaCha20.X86_64.Avx512.setup_run
  refine WP.mono (VG.Proof.ChaCha20.X86_64.Avx512.srun_ok hc setup (SRel.init s) hr) fun s' h => ⟨fun r j hj => ?_,
    h.clean hd, h.gpr, h.rd, h.wr⟩
  rw [h.reg r j hj, hk _ (VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt r) j hj, Avx2.ctr_get _ _ _ (VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt r)]
  simp only [VG.Proof.ChaCha20.X86_64.Avx512.setupT]
  split
  · simp only [T.eval, VG.Proof.ChaCha20.X86_64.Avx512.regn, VG.Proof.ChaCha20.X86_64.Avx512.baseR]
    rw [VG.Proof.ChaCha20.X86_64.Avx512.stateAt_get _ _ (by decide), hi j hj]
  · simp only [T.eval, VG.Proof.ChaCha20.X86_64.Avx512.regn, VG.Proof.ChaCha20.X86_64.Avx512.baseR]
    exact VG.Proof.ChaCha20.X86_64.Avx512.stateAt_get _ _ (VG.Proof.ChaCha20.X86_64.Avx512.xidx_lt r)

end VG.Proof.ChaCha20.X86_64.Avx512

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Finish`. -/
section

/-!
# ChaCha20 on x86-64 with AVX-512: the sixteen blocks, into the data
-/

namespace VG.Proof.ChaCha20.X86_64.Avx512

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Spec.ChaCha20 (Word stateAt serialize)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx2 (plus)

/-- Word `w` of block `j` of the output: the rounds' result (in `zmm w`) plus
the input state, with the counter increment `j` for word 12. -/
def outT (w j : Nat) : VG.Proof.ChaCha20.X86_64.Avx512.T :=
  if w = 12 then .add (.add (.reg 12 j) (.mem 0 12)) (.mem 1 (32 + j)) else .add (.reg w j) (.mem 0 w)

def finishCheck : Bool :=
  match Sym.init.run finish with
  | some σ => (List.range 256).all fun i => σ.mem 2 i == .xor (.mem 2 i) (VG.Proof.ChaCha20.X86_64.Avx512.outT (i % 16) (i / 16))
  | none => false

theorem finishCheck_eq : VG.Proof.ChaCha20.X86_64.Avx512.finishCheck = true := by decide +kernel

theorem finish_run : ∃ σ, Sym.init.run finish = some σ ∧
    ∀ i < 256, σ.mem 2 i = .xor (.mem 2 i) (VG.Proof.ChaCha20.X86_64.Avx512.outT (i % 16) (i / 16)) := by
  have e := VG.Proof.ChaCha20.X86_64.Avx512.finishCheck_eq
  unfold VG.Proof.ChaCha20.X86_64.Avx512.finishCheck at e
  split at e
  · rename_i σ h
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at e
    exact ⟨σ, h, e⟩
  · cases e

/-- A byte, from the doubleword holding it. -/
theorem byte_dword (m : Mem) (a : Addr) (k : Nat) :
    m (a + BitVec.ofNat 64 k) = (m.readW (a + BitVec.ofNat 64 (4 * (k / 4))) 32).extractLsb' (8 * (k % 4)) 8 := by
  rw [byte_readW m _ (w := 32) (k := k % 4) (by omega), VG.Proof.ChaCha20.X86_64.Avx512.add_ofNat']
  congr 3; omega

theorem outT_eval {s : State} {vs : Nat → CState} (hz : VG.Proof.ChaCha20.X86_64.Avx512.ZH vs s) (hi : VG.Proof.ChaCha20.X86_64.Avx512.Incs s.mem (s.gpr .rcx)) {w j : Nat}
    (hw : w < 16) (hj : j < 16) :
    (VG.Proof.ChaCha20.X86_64.Avx512.outT w j).eval s = (plus vs (stateAt s.mem (s.gpr .rdi)) j)[w] := by
  have r := hz (zreg w) j hj
  simp only [VG.Proof.ChaCha20.X86_64.Avx512.xidx_zreg w hw] at r
  simp only [plus, Vector.getElem_zipWith, Avx2.ctr_get _ _ _ hw, VG.Proof.ChaCha20.X86_64.Avx512.outT]
  split
  · rename_i e; subst e
    simp only [T.eval, VG.Proof.ChaCha20.X86_64.Avx512.regn, VG.Proof.ChaCha20.X86_64.Avx512.baseR, r, VG.Proof.ChaCha20.X86_64.Avx512.stateAt_get _ _ (show 12 < 16 by decide), hi j hj,
      BitVec.add_assoc]
  · simp only [T.eval, VG.Proof.ChaCha20.X86_64.Avx512.regn, VG.Proof.ChaCha20.X86_64.Avx512.baseR, r, VG.Proof.ChaCha20.X86_64.Avx512.stateAt_get _ _ hw]

theorem finish_ok {s : State} (hc : VG.Proof.ChaCha20.X86_64.Avx512.Ctx s) (hi : VG.Proof.ChaCha20.X86_64.Avx512.Incs s.mem (s.gpr .rcx)) {vs : Nat → CState}
    (hz : VG.Proof.ChaCha20.X86_64.Avx512.ZH vs s) :
    WP isa (.block finish) s fun s' =>
      (∀ k < 1024, s'.mem (s.gpr .rsi + BitVec.ofNat 64 k) = s.mem (s.gpr .rsi + BitVec.ofNat 64 k) ^^^
        (serialize (plus vs (stateAt s.mem (s.gpr .rdi)) (k / 64))).getD (k % 64) 0) ∧
      Frame (VG.Proof.ChaCha20.X86_64.Avx512.wregs s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨σ, hr, hm⟩ := VG.Proof.ChaCha20.X86_64.Avx512.finish_run
  refine WP.mono (VG.Proof.ChaCha20.X86_64.Avx512.srun_ok hc finish (SRel.init s) hr) fun s' h => ⟨fun k hk => ?_, h.frame, h.gpr,
    h.rd, h.wr⟩
  have d := h.mem 2 (k / 4) (by decide) (by simp only [VG.Proof.ChaCha20.X86_64.Avx512.bsize]; omega)
  rw [hm _ (by omega)] at d
  simp only [T.eval, VG.Proof.ChaCha20.X86_64.Avx512.regn, VG.Proof.ChaCha20.X86_64.Avx512.baseR] at d
  rw [show k / 4 % 16 = k % 64 / 4 by omega, show k / 4 / 16 = k / 64 by omega] at d
  rw [VG.Proof.ChaCha20.X86_64.Avx512.byte_dword s'.mem, VG.Proof.ChaCha20.X86_64.Avx512.byte_dword s.mem, d, BitVec.extractLsb'_xor,
    serialize_getD _ (Nat.mod_lt _ (by decide)), VG.Proof.ChaCha20.X86_64.Avx512.outT_eval hz hi (by omega) (by omega),
    show k % 64 % 4 = k % 4 by omega]

end VG.Proof.ChaCha20.X86_64.Avx512

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor`. -/
section

/-!
# ChaCha20 keystream XOR on x86-64 with AVX-512

The loop over 1024-byte chunks (`Setup`, `Rounds`, `Finish`), the call of
`vg_chacha20_xor` for the rest, constant time and the calling convention. The
contract is that of `vg_chacha20_xor_avx2` (`Avx2.xorAvx2X86_64`): 16 bytes of
stack below the return address, for the call of `vg_chacha20_xor` and its call
of the block function.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx512

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize bytesAt)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx2 (APre est edp eL ebp edR eret estk S0 D0 KS frR eL_lt
  xorAvx2X86_64 add_ofNat in_dR)

/-! ## The loop invariant -/

/-- Before chunk `t`. -/
structure LInv (s₀ : State) (t : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = est s₀
  rcx : s.gpr .rcx = ebp s₀
  rsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (1024 * t)
  rdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - 1024 * t)
  le : 1024 * t ≤ eL s₀
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (est s₀) = ctr (S0 s₀) (16 * t)
  data : ∀ k < eL s₀, s.mem (edp s₀ + BitVec.ofNat 64 k) =
    if k < 1024 * t then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  incs : VG.Proof.ChaCha20.X86_64.Avx512.Incs s.mem (ebp s₀)
  frame : Frame (frR s₀) s₀.mem s.mem

/-- The keystream from block `16 t` on. -/
theorem ks_shift (S : CState) {L t k : Nat} (hk : k < L) (ht : 1024 * t ≤ k) :
    (keystream S L).getD k 0 =
      (serialize (Spec.ChaCha20.block (ctr (ctr S (16 * t)) ((k - 1024 * t) / 64)))).getD
        ((k - 1024 * t) % 64) 0 := by
  rw [keystream_getD _ hk, Avx2.ctr_ctr, show 16 * t + (k - 1024 * t) / 64 = k / 64 by omega,
    show (k - 1024 * t) % 64 = k % 64 by omega]

/-! ## The end of a chunk -/

set_option simprocs false in
theorem next_ok {s₀ : State} (hp : APre s₀) {t : Nat} (hge : 1024 ≤ eL s₀ - 1024 * t) {s : State}
    (hrdi : s.gpr .rdi = est s₀) (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (1024 * t))
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - 1024 * t)) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block next) s fun s' =>
      s'.gpr .rsi = edp s₀ + BitVec.ofNat 64 (1024 * (t + 1)) ∧
      s'.gpr .rdx = BitVec.ofNat 64 (eL s₀ - 1024 * (t + 1)) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      stateAt s'.mem (est s₀) = (stateAt s.mem (est s₀)).set 12 ((stateAt s.mem (est s₀))[12] + 16) ∧
      Frame [Avx2.stR (est s₀)] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.cf = some (decide (eL s₀ - 1024 * (t + 1) < 1024)) := by
  have hL := eL_lt s₀
  have c₁ : (Avx2.stR (est s₀)).Contains (Xor.off (est s₀) 48) 4 := contains_off (by omega) (by omega)
  have i₁ : InRegions (s.rd ++ s.wr) (Xor.off (est s₀) 48) 4 :=
    ⟨Avx2.stR (est s₀), by simp [hrd, hwr, hp.rd, hp.wr], c₁⟩
  have o₁ : InRegions s.wr (Xor.off (est s₀) 48) 4 := ⟨Avx2.stR (est s₀), by simp [hwr, hp.wr], c₁⟩
  simp only [Xor.off] at i₁ o₁
  apply WP.of_runBlock
  simp (config := {decide := true}) only [next, runBlock_cons, runStep_some, runBlock_nil, exec,
    VG.Proof.ChaCha20.X86_64.ea_at, readSrc, readSrc32, execAlu, execAlu32, arithFlags,
    State.load32, State.store32, State.setReg, State.setReg32, State.setFlags, hrdi, i₁, o₁, ite_true,
    ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  have hv : s.mem.readW (est s₀ + BitVec.ofInt 64 ((48 : Nat) : Int)) 32 = (stateAt s.mem (est s₀))[12] := by
    simp [stateAt]
  have hfs : Frame [Avx2.stR (est s₀)] s.mem (s.mem.writeW (Xor.off (est s₀) 48)
      ((stateAt s.mem (est s₀))[12] + 16)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  have se : BitVec.signExtend 64 (1024 : BitVec 32) = 1024 := by decide
  have e : (s.gpr .rdx - 1024).toNat = eL s₀ - 1024 * (t + 1) := by rw [hrdx]; bv_omega
  rw [hv, se]
  refine ⟨by rw [hrsi]; bv_omega, by rw [hrdx]; bv_omega, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃],
    Xor.stateAt_writeW_counter _ _ _, hfs, trivial, trivial, ?_⟩
  rw [e]; rfl

/-! ## The chunk of data -/

section
variable {s₀ : State} {t : Nat}

/-- The 1024 bytes of chunk `t`. -/
abbrev wR (s₀ : State) (t : Nat) : Region := ⟨edp s₀ + BitVec.ofNat 64 (1024 * t), 1024⟩

/-- The counter increments in `buf`. -/
abbrev incR (s₀ : State) : Region := ⟨ebp s₀ + BitVec.ofNat 64 128, 64⟩

/-- The saved registers in `buf`. -/
abbrev saveR (s₀ : State) : Region := ⟨ebp s₀, 128⟩

theorem win_sub (hw : 1024 * t + 1024 ≤ eL s₀) : Region.Sub (VG.Proof.ChaCha20.X86_64.Avx512.wR s₀ t) (edR s₀) := by
  have hL := eL_lt s₀
  intro x hx; simp only [Region.Contains] at *; bv_omega

theorem out_win (hw : 1024 * t + 1024 ≤ eL s₀) {k : Nat} (hk : k < eL s₀)
    (ho : k < 1024 * t ∨ 1024 * t + 1024 ≤ k) :
    ¬ (VG.Proof.ChaCha20.X86_64.Avx512.wR s₀ t).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := eL_lt s₀
  simp only [Region.Contains]; bv_omega

theorem save_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86_64.Avx512.saveR s₀) (Avx2.bufR (ebp s₀)) := Region.sub_prefix (by omega)

theorem inc_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86_64.Avx512.incR s₀) (Avx2.bufR (ebp s₀)) := by
  intro x hx; simp only [Region.Contains] at *; bv_omega

theorem inc_save (s₀ : State) : (VG.Proof.ChaCha20.X86_64.Avx512.incR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Avx512.saveR s₀) := by
  intro x h₁ h₂; simp only [Region.Contains] at *; bv_omega

end

/-- Where a chunk runs: the regions of `Sym`, from the loop's. -/
theorem ctx_of {s₀ : State} (hp : APre s₀) {t : Nat} (hw : 1024 * t + 1024 ≤ eL s₀) {s : State}
    (hrdi : s.gpr .rdi = est s₀) (hrcx : s.gpr .rcx = ebp s₀)
    (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (1024 * t)) (hwr : s.wr = s₀.wr) : VG.Proof.ChaCha20.X86_64.Avx512.Ctx s := by
  have hL := eL_lt s₀
  have r0 : VG.Proof.ChaCha20.X86_64.Avx512.regn s 0 = Avx2.stR (est s₀) := by simp only [VG.Proof.ChaCha20.X86_64.Avx512.regn, VG.Proof.ChaCha20.X86_64.Avx512.baseR, VG.Proof.ChaCha20.X86_64.Avx512.bsize, hrdi]
  have r1 : VG.Proof.ChaCha20.X86_64.Avx512.regn s 1 = Avx2.bufR (ebp s₀) := by simp only [VG.Proof.ChaCha20.X86_64.Avx512.regn, VG.Proof.ChaCha20.X86_64.Avx512.baseR, VG.Proof.ChaCha20.X86_64.Avx512.bsize, hrcx]
  have r2 : VG.Proof.ChaCha20.X86_64.Avx512.regn s 2 = VG.Proof.ChaCha20.X86_64.Avx512.wR s₀ t := by simp only [VG.Proof.ChaCha20.X86_64.Avx512.regn, VG.Proof.ChaCha20.X86_64.Avx512.baseR, VG.Proof.ChaCha20.X86_64.Avx512.bsize, hrsi]
  refine ⟨fun b i n hb h => ?_, fun b b' hb hb' ne => ?_⟩
  · rw [hwr, hp.wr]
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;> simp only [VG.Proof.ChaCha20.X86_64.Avx512.bsize] at h
    · rw [r0]
      exact ⟨Avx2.stR (est s₀), by simp, by
        simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega⟩
    · rw [r1]
      exact ⟨Avx2.bufR (ebp s₀), by simp, by
        simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega⟩
    · rw [r2]
      exact ⟨edR s₀, by simp, by simp only [Region.Contains]; bv_omega⟩
  · have d01 := hp.st_b
    have d02 := hp.st_d.sub_right (VG.Proof.ChaCha20.X86_64.Avx512.win_sub hw)
    have d12 := hp.d_b.symm.sub_right (VG.Proof.ChaCha20.X86_64.Avx512.win_sub hw)
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
      rcases (by omega : b' = 0 ∨ b' = 1 ∨ b' = 2) with rfl | rfl | rfl <;>
      simp only [r0, r1, r2] <;>
      first | exact absurd rfl ne | with_reducible assumption | exact d01.symm | exact d02.symm | exact d12.symm

theorem incs_frame {s₀ : State} {m m' : Mem} {rs : List Region} (h : VG.Proof.ChaCha20.X86_64.Avx512.Incs m (ebp s₀))
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (VG.Proof.ChaCha20.X86_64.Avx512.incR s₀).Disjoint r) : VG.Proof.ChaCha20.X86_64.Avx512.Incs m' (ebp s₀) := by
  intro j hj
  rw [← h j hj]
  refine hf.readW (r := VG.Proof.ChaCha20.X86_64.Avx512.incR s₀) ?_ hd (by decide)
  simp only [Region.Contains]; bv_omega

theorem calleeSaved_ne {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .rax ∧ r ≠ .rsi ∧ r ≠ .rdx :=
  Avx2.calleeSaved_ne hr

theorem body_eq : body = .seq (.block setup) (.seq (rounds 10) (.block (finish ++ next))) := rfl

theorem body_ok {s₀ : State} (hp : APre s₀) {t : Nat} (hge : 1024 ≤ eL s₀ - 1024 * t) {s : State}
    (h : VG.Proof.ChaCha20.X86_64.Avx512.LInv s₀ t s) :
    WP isa body s fun s' =>
      VG.Proof.ChaCha20.X86_64.Avx512.LInv s₀ (t + 1) s' ∧ s'.cf = some (decide (eL s₀ - 1024 * (t + 1) < 1024)) := by
  have hL := eL_lt s₀
  have hw : 1024 * t + 1024 ≤ eL s₀ := by omega
  have sw := VG.Proof.ChaCha20.X86_64.Avx512.win_sub hw
  have dsd := hp.st_d.sub_right sw
  have dbd := hp.d_b.symm.sub_right sw
  have hc : VG.Proof.ChaCha20.X86_64.Avx512.Ctx s := VG.Proof.ChaCha20.X86_64.Avx512.ctx_of hp hw h.rdi h.rcx h.rsi h.wr
  have hi : VG.Proof.ChaCha20.X86_64.Avx512.Incs s.mem (s.gpr .rcx) := by rw [h.rcx]; exact h.incs
  rw [VG.Proof.ChaCha20.X86_64.Avx512.body_eq]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.Avx512.setup_ok hc hi) fun s₁ ⟨hz₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.Avx512.rounds_ok hz₁ 10) fun s₂ ⟨hz₂, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have rd₂ : s₂.rd = s.rd := sm₂.rd.trans rd₁
  have wr₂ : s₂.wr = s.wr := sm₂.wr.trans wr₁
  have hc₂ : VG.Proof.ChaCha20.X86_64.Avx512.Ctx s₂ := VG.Proof.ChaCha20.X86_64.Avx512.ctx_of hp hw (by rw [g₂]; exact h.rdi) (by rw [g₂]; exact h.rcx)
    (by rw [g₂]; exact h.rsi) (by rw [wr₂]; exact h.wr)
  have hi₂ : VG.Proof.ChaCha20.X86_64.Avx512.Incs s₂.mem (s₂.gpr .rcx) := by rw [m₂, g₂]; exact hi
  refine WP.block_append (WP.mono (VG.Proof.ChaCha20.X86_64.Avx512.finish_ok hc₂ hi₂ hz₂) fun s₃ ⟨d₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have ws : VG.Proof.ChaCha20.X86_64.Avx512.wregs s₂ = [VG.Proof.ChaCha20.X86_64.Avx512.saveR s₀, VG.Proof.ChaCha20.X86_64.Avx512.wR s₀ t] := by simp only [VG.Proof.ChaCha20.X86_64.Avx512.wregs, g₂, h.rcx, h.rsi]
  rw [ws, m₂] at f₃
  simp only [g₂, m₂, h.rsi, h.rdi] at d₃
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  refine WP.mono (VG.Proof.ChaCha20.X86_64.Avx512.next_ok hp hge (by rw [g₃']; exact h.rdi) (by rw [g₃']; exact h.rsi)
    (by rw [g₃']; exact h.rdx) (by rw [rd₃, rd₂, h.rd]) (by rw [wr₃, wr₂, h.wr]))
    fun s₄ ⟨e₁, e₂, e₃, e₄, f₄, rd₄, wr₄, cf₄⟩ => ⟨?_, cf₄⟩
  have dss : (Avx2.stR (est s₀)).Disjoint (VG.Proof.ChaCha20.X86_64.Avx512.saveR s₀) := hp.st_b.sub_right (VG.Proof.ChaCha20.X86_64.Avx512.save_sub _)
  have FA : Frame [VG.Proof.ChaCha20.X86_64.Avx512.saveR s₀, VG.Proof.ChaCha20.X86_64.Avx512.wR s₀ t, Avx2.stR (est s₀)] s.mem s₄.mem :=
    (f₃.mono (by simp)).trans (f₄.mono (by simp))
  have hS₃ : stateAt s₃.mem (est s₀) = stateAt s.mem (est s₀) :=
    Xor.stateAt_frame f₃ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dss
      · exact dsd)
  have gk : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s₄.gpr r = s.gpr r := fun r a b c => by
    rw [e₃ r a b c, g₃']
  refine ⟨by rw [gk _ (by decide) (by decide) (by decide)]; exact h.rdi,
    by rw [gk _ (by decide) (by decide) (by decide)]; exact h.rcx, e₁, e₂, by omega,
    fun r hr => ?_, by rw [rd₄, rd₃, rd₂, h.rd], by rw [wr₄, wr₃, wr₂, h.wr], ?_,
    fun k hk => ?_, ?_, ?_⟩
  · obtain ⟨a, b, c⟩ := VG.Proof.ChaCha20.X86_64.Avx512.calleeSaved_ne hr
    rw [gk r a b c]; exact h.keep r hr
  · rw [e₄, hS₃, h.cnt, show 16 * (t + 1) = 16 * t + 16 by omega]
    exact Avx2.ctr_add _ _ 16
  · have n_st : ¬ (Avx2.stR (est s₀)).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
      hp.st_d _ hc (in_dR hk)
    have n_sv : ¬ (VG.Proof.ChaCha20.X86_64.Avx512.saveR s₀).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
      hp.d_b _ (in_dR hk) (VG.Proof.ChaCha20.X86_64.Avx512.save_sub _ _ hc)
    by_cases hin : 1024 * t ≤ k ∧ k < 1024 * t + 1024
    · have ea : edp s₀ + BitVec.ofNat 64 k =
          edp s₀ + BitVec.ofNat 64 (1024 * t) + BitVec.ofNat 64 (k - 1024 * t) := by
        rw [add_ofNat, Nat.add_sub_cancel' hin.1]
      have x₃ := d₃ (k - 1024 * t) (by omega)
      rw [← ea] at x₃
      rw [f₄ _ (by simpa using n_st), x₃, h.data k hk,
        ite_eq_right (by omega : ¬ k < 1024 * t), ite_eq_left (by omega : k < 1024 * (t + 1)),
        Avx2.plus_block, h.cnt, VG.Proof.ChaCha20.X86_64.Avx512.ks_shift _ hk hin.1]
    · have n_w := VG.Proof.ChaCha20.X86_64.Avx512.out_win hw hk (by omega)
      rw [FA _ (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact n_sv
          · exact n_w
          · exact n_st), h.data k hk]
      by_cases hlt : k < 1024 * t
      · rw [ite_eq_left hlt, ite_eq_left (by omega : k < 1024 * (t + 1))]
      · rw [ite_eq_right hlt, ite_eq_right (by omega : ¬ k < 1024 * (t + 1))]
  · refine VG.Proof.ChaCha20.X86_64.Avx512.incs_frame h.incs FA ?_
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact VG.Proof.ChaCha20.X86_64.Avx512.inc_save _
    · exact dbd.sub_left (VG.Proof.ChaCha20.X86_64.Avx512.inc_sub _)
    · exact (hp.st_b.sub_right (VG.Proof.ChaCha20.X86_64.Avx512.inc_sub _)).symm
  · refine h.frame.trans (FA.sub fun r hr' => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact ⟨Avx2.bufR (ebp s₀), by simp, VG.Proof.ChaCha20.X86_64.Avx512.save_sub _⟩
    · exact ⟨edR s₀, by simp, sw⟩
    · exact ⟨Avx2.stR (est s₀), by simp, fun _ h => h⟩

/-! ## The prologue -/

set_option simprocs false in
theorem cmp_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm 1024)]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.cf = some (decide ((s.gpr .rdx).toNat < 1024)) := by
  have se : BitVec.signExtend 64 (1024 : BitVec 32) = 1024 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se]
  exact ⟨trivial, trivial, trivial, trivial, rfl⟩

/-- The offsets in `buf` and values of the quadwords the prologue stores. -/
def incPairs : List (Nat × BitVec 64) :=
  [(128, 0x0000000100000000), (136, 0x0000000300000002), (144, 0x0000000500000004),
   (152, 0x0000000700000006), (160, 0x0000000900000008), (168, 0x0000000b0000000a),
   (176, 0x0000000d0000000c), (184, 0x0000000f0000000e)]

theorem consts_eq : consts = Avx2.pairsCode VG.Proof.ChaCha20.X86_64.Avx512.incPairs := rfl

theorem incPairs_le : ∀ p ∈ VG.Proof.ChaCha20.X86_64.Avx512.incPairs, p.1 + 8 ≤ 320 := by decide

/-- Read back a stored quadword. -/
local macro "qread" : tactic => `(tactic|
  simp (disch := decide) only [Avx2.storeAll, incPairs, List.foldl_cons, List.foldl_nil,
    Nat.reduceAdd, Avx2.readW64_off, Mem.readW_writeW_self64])

theorem incs_mem (m : Mem) (buf : Addr) : VG.Proof.ChaCha20.X86_64.Avx512.Incs (Avx2.storeAll buf VG.Proof.ChaCha20.X86_64.Avx512.incPairs m) buf := by
  intro j hj
  have E := readW_extract (Avx2.storeAll buf VG.Proof.ChaCha20.X86_64.Avx512.incPairs m) (buf + BitVec.ofNat 64 (128 + 8 * (j / 2)))
    (w := 64) (k := 4 * (j % 2)) (n := 4) (by omega)
  rw [add_ofNat, show 128 + 8 * (j / 2) + 4 * (j % 2) = 4 * (32 + j) by omega] at E
  rw [← E]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨
      j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd]; qread; decide)

theorem prologue_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.block (consts ++ ([.alu .cmp .rdx (.imm 1024)] : List Instr))) s₀ fun s =>
      VG.Proof.ChaCha20.X86_64.Avx512.LInv s₀ 0 s ∧ s.cf = some (decide (eL s₀ < 1024)) := by
  have hL := eL_lt s₀
  rw [VG.Proof.ChaCha20.X86_64.Avx512.consts_eq]
  refine WP.block_append (WP.mono (Avx2.pairs_ok VG.Proof.ChaCha20.X86_64.Avx512.incPairs VG.Proof.ChaCha20.X86_64.Avx512.incPairs_le (s := s₀) rfl hp.w_b)
    fun s₁ ⟨m₁, g₁, rd₁, wr₁⟩ => WP.mono (VG.Proof.ChaCha20.X86_64.Avx512.cmp_ok s₁) fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)
  have F : Frame [Avx2.bufR (ebp s₀)] s₀.mem s₂.mem := by
    rw [m₂, m₁]; exact Avx2.storeAll_frame (List.mem_singleton_self _) _ VG.Proof.ChaCha20.X86_64.Avx512.incPairs_le _
  have gk : ∀ r, r ≠ .rax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, g₁ r hr]
  refine ⟨⟨gk _ (by decide), gk _ (by decide), by rw [gk _ (by decide)]; simp,
    by rw [gk _ (by decide)]; simp, by omega, fun r hr => gk r (VG.Proof.ChaCha20.X86_64.Avx512.calleeSaved_ne hr).1,
    by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_, fun k hk => ?_, ?_, ?_⟩, ?_⟩
  · rw [Xor.stateAt_frame F (by simpa using hp.st_b), Nat.mul_zero, ctr_zero]
  · rw [F _ (by simpa using fun hc => hp.d_b _ (in_dR hk) hc)]
    simp
  · rw [m₂, m₁]; exact VG.Proof.ChaCha20.X86_64.Avx512.incs_mem _ _
  · exact F.mono (by simp)
  · rw [cf₂, g₁ _ (by decide)]

/-! ## The rest, by `vg_chacha20_xor` -/

section
variable {s₀ : State} {t : Nat}

/-- The data left for `vg_chacha20_xor`. -/
abbrev tR (s₀ : State) (t : Nat) : Region := ⟨edp s₀ + BitVec.ofNat 64 (1024 * t), eL s₀ - 1024 * t⟩

theorem tail_sub (ht : 1024 * t ≤ eL s₀) : Region.Sub (VG.Proof.ChaCha20.X86_64.Avx512.tR s₀ t) (edR s₀) := by
  have hL := eL_lt s₀
  intro x hx; simp only [Region.Contains] at *; bv_omega

theorem not_tail {k : Nat} (hk : k < 1024 * t) (ht : 1024 * t ≤ eL s₀) :
    ¬ (VG.Proof.ChaCha20.X86_64.Avx512.tR s₀ t).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := eL_lt s₀
  simp only [Region.Contains]; bv_omega

end

open VG.Proof.ChaCha20.X86_64.Avx2 (stk_ret stk_stk ret_stk vz_ok xor_nosp xor_depth bytes_of_bytesAt)

theorem tail_ok {s₀ : State} (hp : APre s₀) {t : Nat} (hlt : eL s₀ - 1024 * t < 1024) {s : State}
    (h : VG.Proof.ChaCha20.X86_64.Avx512.LInv s₀ t s) :
    WP isa (.seq (.block [.vop .vzeroupper]) (.call "vg_chacha20_xor" Impl.ChaCha20.X86_64.Xor.xor)) s
      fun s' => (gprPreserved s₀ s' ∧ xorAvx2X86_64.post s₀ s') ∧ s'.gpr .rsi = s₀.gpr .rcx := by
  have hL := eL_lt s₀
  have hle := h.le
  refine WP.seq (WP.mono (vz_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁⟩ => ?_)
  have hsp : s₁.gpr .rsp = s₀.gpr .rsp := by rw [g₁]; exact h.keep .rsp (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr _ h
  have hn : (BitVec.ofNat 64 (eL s₀ - 1024 * t)).toNat = eL s₀ - 1024 * t := toNat_ofNat_lt (by omega)
  have hwr : s₁.wr = frR s₀ := by rw [wr₁, h.wr, hp.wr]
  have hrd : s₁.rd = [] := by rw [rd₁, h.rd, hp.rd]
  refine WP.call (k := xorStack 8) Xor.xor_rsi xor_nosp (by rw [xor_depth]; decide)
    (rd := []) (wr := [Avx2.stR (est s₀), VG.Proof.ChaCha20.X86_64.Avx512.tR s₀ t, Avx2.bufR (ebp s₀)]) ?_ ?_ ?_ ?_
  · rw [xorStack_pre8]
    simp only [xorX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
      hne _ (by decide : Reg.rdx ≠ .rsp), hne _ (by decide : Reg.rcx ≠ .rsp), g₁, h.rdi, h.rsi,
      h.rdx, h.rcx, hsp, hn]
    have ts := VG.Proof.ChaCha20.X86_64.Avx512.tail_sub (s₀ := s₀) h.le
    exact ⟨trivial, trivial, hp.st_d.sub_right ts, hp.st_b, hp.d_b.sub_left ts,
      hp.stk_st.sub_left (stk_ret s₀), (hp.stk_d.sub_left (stk_ret s₀)).sub_right ts,
      hp.stk_b.sub_left (stk_ret s₀), hp.stk_st.sub_left (stk_stk s₀),
      (hp.stk_d.sub_left (stk_stk s₀)).sub_right ts, hp.stk_b.sub_left (stk_stk s₀),
      by have := hp.nowrap; bv_omega⟩
  · rw [hrd, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨Avx2.stR (est s₀), by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
    · exact ⟨edR s₀, by simp, 1024 * t, rfl, show 1024 * t + (eL s₀ - 1024 * t) ≤ eL s₀ by omega⟩
    · exact ⟨Avx2.bufR (ebp s₀), by simp, 0, by simp, show 0 + 320 ≤ 320 by omega⟩
  · rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨Avx2.stR (est s₀), by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
    · exact ⟨edR s₀, by simp, 1024 * t, rfl, show 1024 * t + (eL s₀ - 1024 * t) ≤ eL s₀ by omega⟩
    · exact ⟨Avx2.bufR (ebp s₀), by simp, 0, by simp, show 0 + 320 ≤ 320 by omega⟩
  · intro s₂ _ _ hcs hf _ ⟨s₃, hm₃, hg₃, hpost, hrsi₃⟩
    rw [xor_depth, hsp] at hf
    have ts := VG.Proof.ChaCha20.X86_64.Avx512.tail_sub (s₀ := s₀) h.le
    have hce : stateAt s₁.callEntry.mem (est s₀) = stateAt s₁.mem (est s₀) := by
      rw [State.callEntry_mem]
      exact Xor.stateAt_frame (rs := [estk s₀])
        ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
          rw [hsp]; exact below_call _ (by omega) (by omega)))
        (by simpa using hp.stk_st.symm)
    have Fce : Frame [estk s₀] s₁.mem s₁.callEntry.mem := by
      rw [State.callEntry_mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
        rw [hsp]; exact below_call _ (by omega) (by omega))
    simp only [xorX86_64, State.withRegions_gpr, State.withRegions_mem,
      hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
      hne _ (by decide : Reg.rdx ≠ .rsp), g₁, h.rdi, h.rsi, h.rdx, hce, hm₃, m₁, h.cnt] at hpost
    rw [hn] at hpost
    refine ⟨⟨⟨fun r hr => by rw [hcs r hr, g₁]; exact h.keep r hr, ?_⟩, ?_⟩, ?_⟩
    rotate_right
    · rw [← hg₃ .rsi (by decide), hrsi₃, State.withRegions_gpr, hne _ (by decide), g₁, h.rcx]
    · refine (hf.readW (r := eret s₀) (Region.contains_self _ _) ?_ (by decide)).trans ?_
      · intro r hr
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hp.ret_st
        · exact hp.ret_d.sub_right ts
        · exact hp.ret_b
        · exact ret_stk s₀
      · rw [m₁]
        refine h.frame.readW (Region.contains_self _ _) ?_ (by decide)
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.ret_st
        · exact hp.ret_d
        · exact hp.ret_b
    · refine bytesAt_xor (length_keystream _ _) fun k hk => ?_
      have hk2 : k < eL s₀ := hk
      have n_st : ¬ (Avx2.stR (est s₀)).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
        hp.st_d _ hc (in_dR hk)
      have n_b : ¬ (Avx2.bufR (ebp s₀)).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
        hp.d_b _ (in_dR hk) hc
      have n_sk : ¬ (estk s₀).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
        hp.stk_d _ hc (in_dR hk)
      by_cases hk' : k < 1024 * t
      · rw [hf _ (by
          intro r hr
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact n_st
          · exact VG.Proof.ChaCha20.X86_64.Avx512.not_tail hk' h.le
          · exact n_b
          · exact n_sk), m₁, h.data k hk, ite_eq_left hk']
      · have ea : edp s₀ + BitVec.ofNat 64 k =
            edp s₀ + BitVec.ofNat 64 (1024 * t) + BitVec.ofNat 64 (k - 1024 * t) := by
          rw [add_ofNat, Nat.add_sub_cancel' (by omega)]
        have x := bytes_of_bytesAt (length_keystream _ _) hpost (k := k - 1024 * t) (by omega)
        rw [← ea, Fce _ (by simpa using n_sk), m₁, h.data k hk2, ite_eq_right hk',
          keystream_getD _ (by omega)] at x
        rw [x, VG.Proof.ChaCha20.X86_64.Avx512.ks_shift _ hk2 (t := t) (by omega)]

/-! ## The whole function -/

theorem xor_eq : Impl.ChaCha20.X86_64.Avx512.xor =
    .seq (.block (consts ++ ([.alu .cmp .rdx (.imm 1024)] : List Instr)))
    (.seq (.ite .b (.block []) (.loop body .ae))
    (.seq (.block [.vop .vzeroupper]) (.call "vg_chacha20_xor" Impl.ChaCha20.X86_64.Xor.xor))) := rfl

theorem correct {s₀ : State} (hp : APre s₀) :
    WP isa Impl.ChaCha20.X86_64.Avx512.xor s₀ fun s' =>
      (gprPreserved s₀ s' ∧ xorAvx2X86_64.post s₀ s') ∧ s'.gpr .rsi = s₀.gpr .rcx := by
  rw [VG.Proof.ChaCha20.X86_64.Avx512.xor_eq]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.Avx512.prologue_ok hp) fun s₁ ⟨h₁, hc⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ t, eL s₀ - 1024 * t < 1024 ∧ VG.Proof.ChaCha20.X86_64.Avx512.LInv s₀ t s) ?_
    fun s₂ ⟨t, ht, h₂⟩ => VG.Proof.ChaCha20.X86_64.Avx512.tail_ok hp ht h₂)
  refine WP.ite (decide (eL s₀ < 1024)) (by simp [VG.X86_64.eval, hc]) (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil (M := isa) ⟨0, by omega, h₁⟩
  · simp only [decide_eq_false_iff_not] at h
    let Inv : Nat → State → Prop := fun n s =>
      ∃ t, n = eL s₀ - 1024 * t ∧ 1024 ≤ eL s₀ - 1024 * t ∧ VG.Proof.ChaCha20.X86_64.Avx512.LInv s₀ t s
    have hstep : ∀ n s, Inv n s → WP isa body s (fun s' =>
        (VG.X86_64.eval .ae s' = some false ∧ ∃ t, eL s₀ - 1024 * t < 1024 ∧ VG.Proof.ChaCha20.X86_64.Avx512.LInv s₀ t s') ∨
        (VG.X86_64.eval .ae s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨t, rfl, ht, hI⟩
      refine WP.mono (VG.Proof.ChaCha20.X86_64.Avx512.body_ok hp ht hI) fun s' ⟨h', hc'⟩ => ?_
      by_cases hl : eL s₀ - 1024 * (t + 1) < 1024
      · exact .inl ⟨by simp [VG.X86_64.eval, hc', hl], t + 1, hl, h'⟩
      · exact .inr ⟨by simp [VG.X86_64.eval, hc', hl], eL s₀ - 1024 * (t + 1), by omega, t + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep (eL s₀ - 1024 * 0) s₁ ⟨0, rfl, by omega, h₁⟩

/-! ## Constant time and the contract -/

/-- `vg_chacha20_xor_avx512` returns with `rsi` pointing at `buf`, as
`vg_chacha20_xor` does, for a caller that recomputes pointers from it. -/
theorem xor_rsi (s : State) (hs : xorAvx2X86_64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86_64.Avx512.xor s t s' ∧ abiPreserved s s' ∧
      (xorAvx2X86_64.post s s' ∧ s'.gpr .rsi = s.gpr .rcx) := by
  obtain ⟨t, s', he, ⟨h, hpost⟩, hr⟩ := VG.Proof.ChaCha20.X86_64.Avx512.correct (Avx2.APre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h, hpost, hr⟩

theorem xor_correct (s : State) (hs : xorAvx2X86_64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86_64.Avx512.xor s t s' ∧ abiPreserved s s' ∧
      xorAvx2X86_64.post s s' :=
  (VG.Proof.ChaCha20.X86_64.Avx512.xor_rsi s hs).imp fun _ ⟨s', he, ha, h, _⟩ => ⟨s', he, ha, h⟩

theorem xor_ct : ConstantTime isa xorAvx2X86_64.pre xorAvx2X86_64.pub
    Impl.ChaCha20.X86_64.Avx512.xor :=
  VG.Taint.constantTime (A := taint) Avx2.τ₀ (fun _ _ h₁ h₂ hp => Avx2.agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem xor_verified :
    Verified X86_64.target Impl.ChaCha20.X86_64.Avx512.xor
      (Spec.ChaCha20.xorContract X86_64.abi 16) :=
  Verified.of_correct VG.Proof.ChaCha20.X86_64.Avx512.xor_correct VG.Proof.ChaCha20.X86_64.Avx512.xor_ct
    (by sig_implies [Spec.ChaCha20.xorContract, Spec.ChaCha20.xorSig, X86_64.abi, X86_64.argRegs,
      xorAvx2X86_64, Proof.ChaCha20.xorX86_64]
      [Avx2.sat] using Avx2.sat)

end VG.Proof.ChaCha20.X86_64.Avx512

end
