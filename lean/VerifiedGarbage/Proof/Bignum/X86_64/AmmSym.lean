import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Sym
import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma

/-!
# RSA with AVX512_IFMA on x86-64: straight-line vector code, lane by lane

A step of the almost Montgomery multiplication (`CrtIfma.ammStep`) computes
on the quadwords (lanes) of `ymm` registers, from 32-byte memory operands
and a quadword loaded into `rax`, all at constant offsets from the
general-purpose registers `r8`, `r9` and `r10`, which it does not change.
`Sym.run` computes each quadword after such a block as a term (`A`) in the
quadwords, general-purpose registers and memory before it; `run_ok` proves
the machine agrees. The quadword lemmas of the instructions are those of
Poly1305 and X25519 (`Proof/Poly1305/X86_64/Avx2/Sym.lean`,
`Proof/X25519/X86_64/Ifma/Sym.lean`), and `qw_madd52m` that of the memory
form of `vpmadd52luq` and `vpmadd52huq`.
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi xi_inj qw qword_paddq qword_psrlq pick2 sel4 sel4_lt
  qw_setV256 qw_lane lane_sel qw_vbin qw_vshift qw_vpblendd qw_vpbroadcastq qw_vmovq qw_vpermq hv_of
  mod2_lt qword256_eq)
open VG.Proof.X25519.X86_64.Ifma (mad52 qword_madd52)

/-! ## Quadwords of the memory form of `vpmadd52luq` and `vpmadd52huq` -/

theorem qw_madd52m (h : Bool) (s : State) (d a r : XReg) (v : BitVec 256) {k : Nat} (hk : k < 4) :
    qw (s.setV .l256 d (madd52 h (s.lane d 0) (s.lane a 0) (v.extractLsb' 0 128))
        (madd52 h (s.lane d 1) (s.lane a 1) (v.extractLsb' 128 128))) r k =
      if r = d then mad52 h (qw s d k) (qw s a k) (v.extractLsb' (64 * k) 64) else qw s r k := by
  rw [qw_setV256]
  split
  · have e : (if k / 2 = 0 then madd52 h (s.lane d 0) (s.lane a 0) (v.extractLsb' 0 128)
        else madd52 h (s.lane d 1) (s.lane a 1) (v.extractLsb' 128 128)) =
        madd52 h (s.lane d (k / 2)) (s.lane a (k / 2)) (v.extractLsb' (128 * (k / 2)) 128) := by
      rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;> rfl
    rw [e, qword_madd52 _ _ _ _ (mod2_lt k), qw_lane, qw_lane]
    congr 1
    rw [← qword256_eq, qword256]
  · rfl

/-! ## Terms -/

/-- A quadword of a general-purpose register, in terms of the start. -/
inductive G
  | gpr (r : Reg)
  /-- The quadword at `b + d`. -/
  | ld (b : Reg) (d : Nat)
  deriving DecidableEq, Repr

/-- A quadword of a vector register, in terms of the start. -/
inductive A
  /-- Quadword `k` of the vector register numbered `r`. -/
  | reg (r : Nat)
  | zero
  /-- `g` in quadword 0, zero elsewhere. -/
  | lane0 (g : G)
  /-- Quadword 0 of `a`, in every quadword. -/
  | bc (a : A)
  /-- Quadword `k` of the 32 bytes at `b + d`. -/
  | ld (b : Reg) (d : Nat)
  /-- `vpmadd52luq`, `vpmadd52huq` (`h`). -/
  | mad (h : Bool) (c a b : A)
  | add (a b : A)
  | shr (a : A) (n : Nat)
  | perm (a : A) (o : Nat)
  | blend (a b : A) (sel : Nat)
  deriving DecidableEq, Repr

def G.eval (s₀ : State) : G → BitVec 64
  | .gpr r => s₀.gpr r
  | .ld b d => s₀.mem.readW (s₀.gpr b + BitVec.ofNat 64 d) 64

def A.eval (s₀ : State) : A → Nat → BitVec 64
  | .reg r, k => qw s₀ (xr r) k
  | .zero, _ => 0
  | .lane0 g, k => if k = 0 then g.eval s₀ else 0
  | .bc a, _ => a.eval s₀ 0
  | .ld b d, k => s₀.mem.readW (s₀.gpr b + BitVec.ofNat 64 (d + 8 * k)) 64
  | .mad h c a b, k => mad52 h (c.eval s₀ k) (a.eval s₀ k) (b.eval s₀ k)
  | .add a b, k => a.eval s₀ k + b.eval s₀ k
  | .shr a n, k => a.eval s₀ k >>> n
  | .perm a o, k => a.eval s₀ (sel4 o k)
  | .blend a b sel, k => pick2 (a.eval s₀ k) (b.eval s₀ k) (sel.testBit (2 * k)) (sel.testBit (2 * k + 1))

/-! ## The machine -/

/-- The terms of the vector registers (by number) and of `rax`. -/
structure Sym where
  reg : Nat → A
  rax : G

def Sym.init : Sym := ⟨.reg, .gpr .rax⟩

def Sym.set (σ : Sym) (d : XReg) (t : A) : Sym := { σ with reg := fun r => if r = xi d then t else σ.reg r }

/-- The base and offset of `[b + d]`. -/
def baseOff (m : MemOp) : Option (Reg × Nat) :=
  if m.index = none then
    match m.disp with
    | .ofNat n => some (m.base, n)
    | _ => none
  else none

def Sym.vop (σ : Sym) : VOp → Option Sym
  | .vbin .vpxor .l256 d a b => if a = b then some (σ.set d .zero) else none
  | .vbin .vpaddq .l256 d a b => some (σ.set d (.add (σ.reg (xi a)) (σ.reg (xi b))))
  | .vshift .psrlq .l256 d a n =>
    if n.toNat < 64 then some (σ.set d (.shr (σ.reg (xi a)) n.toNat)) else none
  | .vpblendd .l256 d a b sel => some (σ.set d (.blend (σ.reg (xi a)) (σ.reg (xi b)) sel.toNat))
  | .vpbroadcastq .l256 d a => some (σ.set d (.bc (σ.reg (xi a))))
  | .vmovq d r => if r = .rax then some (σ.set d (.lane0 σ.rax)) else none
  | .vpermq d a o => some (σ.set d (.perm (σ.reg (xi a)) o.toNat))
  | _ => none

/-- One instruction, with `lim b` the bytes readable from each base `b`
(which no instruction here changes, but `rax`). -/
def Sym.step (lim : Reg → Nat) (σ : Sym) : Instr → Option Sym
  | .vop o => σ.vop o
  | .mov .rax (.mem m) => (baseOff m).bind fun bo =>
    if bo.1 ≠ .rax ∧ bo.2 + 8 ≤ lim bo.1 then some { σ with rax := .ld bo.1 bo.2 } else none
  | .vpmadd52Load h d a m => (baseOff m).bind fun bo =>
    if bo.1 ≠ .rax ∧ bo.2 + 32 ≤ lim bo.1 then
      some (σ.set d (.mad h (σ.reg (xi d)) (σ.reg (xi a)) (.ld bo.1 bo.2)))
    else none
  | _ => none

def Sym.run (lim : Reg → Nat) (σ : Sym) : List Instr → Option Sym
  | [] => some σ
  | i :: is => (σ.step lim i).bind fun σ' => σ'.run lim is

/-! ## The machine agrees -/

/-- `s₀` with the vector registers and `rax` of `s`. -/
def vr (s₀ s : State) : State :=
  { s₀ with xmm := s.xmm, ymmHi := s.ymmHi, zmmHi := s.zmmHi, gpr := fun r => if r = .rax then s.gpr .rax else s₀.gpr r }

/-- The terms `σ` hold in `s`, which differs from `s₀` only in its vector
registers and `rax`. -/
structure SRel (σ : Sym) (s₀ s : State) : Prop where
  reg : ∀ r k, k < 4 → qw s r k = (σ.reg (xi r)).eval s₀ k
  rax : s.gpr .rax = σ.rax.eval s₀
  eq : vr s₀ s = s

theorem SRel.gpr {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) {r : Reg} (hr : r ≠ .rax) : s.gpr r = s₀.gpr r := by
  rw [← h.eq]; simp only [vr, hr, ite_false]
theorem SRel.mem {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.mem = s₀.mem := by rw [← h.eq]; rfl
theorem SRel.rd {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.rd = s₀.rd := by rw [← h.eq]; rfl
theorem SRel.wr {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.wr = s₀.wr := by rw [← h.eq]; rfl
theorem SRel.mxcsr {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.mxcsr = s₀.mxcsr := by rw [← h.eq]; rfl
theorem SRel.flags {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) :
    s.cf = s₀.cf ∧ s.zf = s₀.zf ∧ s.sf = s₀.sf ∧ s.of = s₀.of := by
  rw [← h.eq]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem vr_self (s : State) : vr s s = s := by
  simp only [vr]
  congr 1
  funext r
  split <;> simp_all

theorem SRel.init (s₀ : State) : SRel Sym.init s₀ s₀ :=
  ⟨fun r k _ => by simp only [Sym.init, A.eval, xr_xi], rfl, vr_self s₀⟩

theorem vr_vop {s₀ s : State} (h : vr s₀ s = s) (o : VOp) : vr s₀ (o.exec s) = o.exec s := by
  rw [← h]
  cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl

theorem vr_setV {s₀ s : State} (h : vr s₀ s = s) (len : VLen) (d : XReg) (lo hi : BitVec 128) :
    vr s₀ (s.setV len d lo hi) = s.setV len d lo hi := by
  rw [← h]; rfl

theorem SRel.set {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) {d : XReg} {t : A} {s' : State}
    (hv : ∀ r k, k < 4 → qw s' r k = if r = d then t.eval s₀ k else qw s r k)
    (he : vr s₀ s' = s') (hg : s'.gpr .rax = s.gpr .rax) : SRel (σ.set d t) s₀ s' := by
  refine ⟨fun r k hk => ?_, hg.trans h.rax, he⟩
  rw [hv r k hk]
  simp only [Sym.set, xi_inj]
  split
  · rfl
  · exact h.reg r k hk

/-- The bytes the code may load: `lim b` bytes from each base `b`. -/
def Ctx (lim : Reg → Nat) (s₀ : State) : Prop :=
  ∀ b d n, d + n ≤ lim b → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr b + BitVec.ofNat 64 d) n

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

theorem sstep_ok {lim : Reg → Nat} {s₀ : State} (hc : Ctx lim s₀) {σ σ' : Sym} {s : State}
    (h : SRel σ s₀ s) {i : Instr} (e : σ.step lim i = some σ') :
    ∃ s', exec i s = some s' ∧ SRel σ' s₀ s' := by
  have hR : ∀ a k, k < 4 → (σ.reg (xi a)).eval s₀ k = qw s a k := fun a k hk => (h.reg a k hk).symm
  unfold Sym.step at e
  split at e
  · rename_i o
    refine ⟨o.exec s, rfl, ?_⟩
    have he := vr_vop h.eq o
    have hg : (o.exec s).gpr .rax = s.gpr .rax := by cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl
    unfold Sym.vop at e
    split at e
    · rename_i d a b
      split at e
      · rename_i hab
        cases e
        subst hab
        refine h.set (hv_of (fun k hk => ?_) (fun r hr k _ => by rw [qw_vbin, ite_eq_right hr])) he hg
        rw [qw_vbin, ite_eq_left rfl]
        simp [VBinOp.sse, XBinOp.eval, qword, A.eval]
      · cases e
    · rename_i d a b
      cases e
      refine h.set (hv_of (fun k hk => ?_) (fun r hr k _ => by rw [qw_vbin, ite_eq_right hr])) he hg
      rw [qw_vbin, ite_eq_left rfl]
      simp only [VBinOp.sse, A.eval]
      rw [qword_paddq _ _ (mod2_lt k), qw_lane, qw_lane, hR a k hk, hR b k hk]
    · rename_i d a n
      split at e
      · rename_i hn
        cases e
        refine h.set (hv_of (fun k hk => ?_) (fun r hr k _ => by rw [qw_vshift, ite_eq_right hr])) he hg
        rw [qw_vshift, ite_eq_left rfl]
        simp only [A.eval]
        rw [qword_psrlq _ hn (mod2_lt k), qw_lane, hR a k hk]
      · cases e
    · rename_i d a b n
      cases e
      exact h.set (hv_of (fun k hk => by
          rw [qw_vpblendd _ _ _ _ _ _ hk, ite_eq_left rfl]; simp only [A.eval]; rw [hR a k hk, hR b k hk])
        (fun r hr k hk => by rw [qw_vpblendd _ _ _ _ _ _ hk, ite_eq_right hr])) he hg
    · rename_i d a
      cases e
      exact h.set (hv_of (fun k _ => by rw [qw_vpbroadcastq, ite_eq_left rfl]; exact (hR a 0 (by decide)).symm)
        (fun r hr k _ => by rw [qw_vpbroadcastq, ite_eq_right hr])) he hg
    · rename_i d g
      split at e
      · rename_i hgr
        cases e
        subst hgr
        exact h.set (hv_of (fun k hk => by rw [qw_vmovq _ _ _ _ hk, ite_eq_left rfl]; simp only [A.eval, h.rax])
          (fun r hr k hk => by rw [qw_vmovq _ _ _ _ hk, ite_eq_right hr])) he hg
      · cases e
    · rename_i d a o
      cases e
      exact h.set (hv_of (fun k hk => by
          rw [qw_vpermq _ _ _ _ _ hk, ite_eq_left rfl]; simp only [A.eval]; rw [hR a _ (sel4_lt _ _)])
        (fun r hr k hk => by rw [qw_vpermq _ _ _ _ _ hk, ite_eq_right hr])) he hg
    · cases e
  · rename_i m
    obtain ⟨⟨b, d⟩, hbo, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    case isFalse => cases e
    rename_i hlt
    cases e
    have ea : s.ea m = s₀.gpr b + BitVec.ofNat 64 d := by rw [baseOff_ok hbo, h.gpr hlt.1]
    have hin : InRegions (s.rd ++ s.wr) (s₀.gpr b + BitVec.ofNat 64 d) 8 := by
      rw [h.rd, h.wr]; exact hc b d 8 hlt.2
    refine ⟨s.setReg .rax (s.mem.readW (s₀.gpr b + BitVec.ofNat 64 d) 64), ?_, ?_⟩
    · simp only [exec, readSrc, State.load64, ea, hin, ite_true, Option.map_some]
    · refine ⟨fun r k hk => h.reg r k hk, ?_, ?_⟩
      · simp only [State.setReg, ite_true, G.eval, h.mem]
      · rw [← h.eq]; simp only [vr, State.setReg]; congr 1; funext r; split <;> simp_all
  · rename_i hh d a m
    obtain ⟨⟨b, o⟩, hbo, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    case isFalse => cases e
    rename_i hlt
    cases e
    have ea : s.ea m = s₀.gpr b + BitVec.ofNat 64 o := by rw [baseOff_ok hbo, h.gpr hlt.1]
    have hin : InRegions (s.rd ++ s.wr) (s₀.gpr b + BitVec.ofNat 64 o) 32 := by
      rw [h.rd, h.wr]; exact hc b o 32 hlt.2
    let v := s.mem.readW (s₀.gpr b + BitVec.ofNat 64 o) 256
    refine ⟨s.setV .l256 d (madd52 hh (s.lane d 0) (s.lane a 0) (v.extractLsb' 0 128))
      (madd52 hh (s.lane d 1) (s.lane a 1) (v.extractLsb' 128 128)),
      by simp only [exec, ea, State.load256, hin, ite_true, Option.map_some, v], ?_⟩
    refine h.set (hv_of (fun k hk => ?_) (fun r hr k hk => by rw [qw_madd52m _ _ _ _ _ _ hk, ite_eq_right hr]))
      (vr_setV h.eq _ _ _ _) rfl
    rw [qw_madd52m _ _ _ _ _ _ hk, ite_eq_left rfl]
    simp only [A.eval]
    rw [hR d k hk, hR a k hk]
    congr 1
    have r1 := readW_extract s.mem (s₀.gpr b + BitVec.ofNat 64 o) (w := 256) (k := 8 * k)
      (n := 8) (by omega)
    rw [show 64 * k = 8 * (8 * k) by omega, r1, h.mem, BitVec.add_assoc, ← BitVec.ofNat_add]
  · cases e

/-- A block of instructions. -/
theorem srun_ok {lim : Reg → Nat} {s₀ : State} (hc : Ctx lim s₀) :
    ∀ (is : List Instr) {σ σ' : Sym} {s : State}, SRel σ s₀ s → σ.run lim is = some σ' →
      WP isa (.block is) s (SRel σ' s₀)
  | [], _, _, _, h, e => by cases e; exact WP.block_nil h
  | i :: is, _, _, _, h, e => by
    simp only [Sym.run, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    obtain ⟨s₁, hx, h₁⟩ := sstep_ok hc h e₁
    exact WP.block_cons_iff.2 ⟨s₁, hx, srun_ok hc is h₁ e₂⟩

/-- A block from its start. -/
theorem run_ok {lim : Reg → Nat} {s₀ : State} (hc : Ctx lim s₀) {is : List Instr} {σ : Sym}
    (e : Sym.init.run lim is = some σ) : WP isa (.block is) s₀ (SRel σ s₀) :=
  srun_ok hc is (SRel.init s₀) e

end VG.Proof.Bignum.X86_64.AmmSym
