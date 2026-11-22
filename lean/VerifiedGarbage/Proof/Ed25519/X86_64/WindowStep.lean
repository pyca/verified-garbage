module

public import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyFrame
import VerifiedGarbage.Proof.Ed25519.X86_64.CachedPoint
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
public import VerifiedGarbage.Proof.Ed25519.Group.Double
public import VerifiedGarbage.Proof.Ed25519.Recode
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
import VerifiedGarbage.Proof.Ed25519.X86_64.Points
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X25519.X86_64.Lit
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyWindow
public import VerifiedGarbage.Proof.Ed25519.X86_64.PointTableAddr
public import VerifiedGarbage.Proof.Ed25519.BaseTable
import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddMemory
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ed25519.Point64Contract
public import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
public import VerifiedGarbage.Impl.Ed25519.X86_64.Point64
public import VerifiedGarbage.Proof.Ed25519.X86_64.FieldWide
import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Impl.Ed25519.X86_64.BaseOdd
import VerifiedGarbage.Proof.Ed25519.WindowConstants
public import VerifiedGarbage.Proof.Ed25519.Group.Extended
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Ed25519.X86_64.BaseOdd`, which this module and modules that import it used -/

section

/-!
# The static odd multiples of `-B`

`checkOdd` walks `baseOddAffine` a pair of entries at a time, comparing them projectively with
`[2m + 1]B` and its negation and adding `[2]B` with the specification's formula as it goes, so
the kernel evaluates 64 additions; each static entry is the caching of the negation of its
affine point by definition, so entry `e` represents `-[d]B` for the digit `d = dec (e + 1)`
whose byte is `e + 1` (`baseOddCached_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG.Spec.Ed25519 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open Spec.X25519 (Fe)

/-- `(x, y)` is the affine point of the projective `p`. -/
private def same (q : Fe × Fe) (p : Point) : Bool := q.1 * p.Z == p.X && q.2 * p.Z == p.Y && p.Z != 0

private theorem same_rep {q : Fe × Fe} {p : Point} {a : EPoint dZ} (h : Rep p a) (hs : same q p = true) :
    Rep (affPt q) a := by
  simp only [same, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hs
  obtain ⟨⟨hx, hy⟩, _⟩ := hs
  refine h.of_proj (show toZ 1 ≠ 0 by decide) ?_ ?_
    (by show toZ (q.1 * q.2) * toZ 1 = toZ q.1 * toZ q.2; rw [toZ_mul, toZ_one, mul_one])
  · show toZ q.1 * toZ p.Z = toZ p.X * toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hx]
  · show toZ q.2 * toZ p.Z = toZ p.Y * toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hy]

/-- Entries `2m` and `2m + 1` are `p` and `-p`, `p` moving on by `b2`. -/
private def checkOdd (b2 p : Point) : List (Fe × Fe) → Bool
  | q :: q' :: qs => same q p && same q' (negPoint p) && checkOdd b2 (pointAdd (affPt q) b2) qs
  | _ => true

private theorem checkOdd_ok (b2 : Point) (c : EPoint dZ) (hb : Rep b2 c) (p : Point) (a : EPoint dZ)
    (h : Rep p a) (qs : List (Fe × Fe)) (hc : checkOdd b2 p qs = true) (hl : qs.length % 2 = 0)
    (m : Nat) (hm : 2 * m + 1 < qs.length) :
    Rep (affPt (qs.getD (2 * m) (0, 1))) (a + m • c) ∧
      Rep (affPt (qs.getD (2 * m + 1) (0, 1))) (-(a + m • c)) := by
  induction m generalizing p a qs with
  | zero =>
    match qs, hc, hm with
    | q :: q' :: qs, hc, _ =>
      simp only [checkOdd, Bool.and_eq_true] at hc
      simp only [zero_smul, add_zero, List.getD_cons_zero, Nat.mul_zero, Nat.zero_add, List.getD_cons_succ]
      exact ⟨same_rep h hc.1.1, same_rep h.neg hc.1.2⟩
  | succ m ih =>
    match qs, hc, hm, hl with
    | q :: q' :: qs, hc, hm, hl =>
      simp only [checkOdd, Bool.and_eq_true] at hc
      simp only [List.length_cons] at hm hl
      have := ih (pointAdd (affPt q) b2) (a + c) (pointAdd_rep (same_rep h hc.1.1) hb) qs hc.2
        (by omega_using [hl]) (by omega_using [hm])
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega_using [], List.getD_cons_succ, List.getD_cons_succ,
        show 2 * m + 1 + 1 + 1 = 2 * m + 1 + 1 + 1 from rfl, List.getD_cons_succ, List.getD_cons_succ,
        succ_nsmul, show a + (m • c + c) = a + c + m • c by abel]
      exact this

private theorem odd_check : checkOdd (pointAdd basePoint basePoint) basePoint baseOddAffine = true := by
  decide +kernel

theorem baseOddAffine_length : baseOddAffine.length = 128 := by decide +kernel

/-- Entry `e < 128` of the static is the caching of a representative of `[dec (e + 1)](-B)`. -/
theorem baseOddCached_ok (e : Nat) (he : e < 128) :
    ∃ q, baseOddCached (baseOddAffine.getD e (0, 1)) = cache q ∧
      Rep q ((Recode.dec (e + 1)) • (-baseAff)) := by
  refine ⟨negPoint (affPt (baseOddAffine.getD e (0, 1))), rfl, ?_⟩
  have h := checkOdd_ok _ _ (pointAdd_rep basePoint_rep basePoint_rep) _ _ basePoint_rep _ odd_check
    (by rw [baseOddAffine_length]) (e / 2) (by rw [baseOddAffine_length]; omega_using [he])
  rw [smul_neg]
  apply Rep.neg
  rcases Nat.even_or_odd' e with ⟨m, rfl | rfl⟩
  · rw [show 2 * m / 2 = m by omega_using []] at h
    have hd : Recode.dec (2 * m + 1) = ((2 * m + 1 : Nat) : Int) := Recode.dec_odd (by omega_using [])
    rw [hd, natCast_zsmul]
    convert h.1 using 1
    rw [add_smul, mul_smul, one_smul, two_smul, ← two_nsmul, two_nsmul, smul_add]; abel
  · rw [show (2 * m + 1) / 2 = m by omega_using []] at h
    have hd : Recode.dec (2 * m + 1 + 1) = -((2 * m + 1 : Nat) : Int) := by
      rw [Recode.dec_even (by omega_using []) (by omega_using [])]; push_cast; ring
    rw [hd, neg_smul, natCast_zsmul]
    convert h.2 using 2
    rw [add_smul, mul_smul, one_smul, two_smul, ← two_nsmul, two_nsmul, smul_add]; abel

end VG.Proof.Ed25519.X86_64

end

end

/-! ### `Ed25519.X86_64.Point64.Keeps`, which this module and modules that import it used -/

section

/-! ### `Ed25519.X86_64.Point64.Fn`, which this module and modules that import it used -/

section

/-! ### `Ed25519.X86_64.FieldLazy`, which only this module used -/

section

/-!
# Ed25519 field programs on the wide scratch, with bounds

`field_liftB` lifts a field program's proof on the narrow scratch (4096 bytes)
to the wide one (8192), with bounds on the memory before and after.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr Outside Op clob F fe)

variable {fld : Arith} [EdArith fld]

/-- `field_lift`, with bounds before and after. -/
theorem field_liftB {s : State} {base : Addr} (hs : Scratch s base) (code : List Instr)
    (f : Env → Env) (Pre Post : Mem → Prop) (hpre : Pre s.mem)
    (correct : ∀ t, Scr t base → Pre t.mem → WP isa (.block code) t fun u =>
      Keep base t u ∧ env u.mem base = f (env t.mem base) ∧ Post u.mem) :
    WP isa (.block code) s fun t => Keep base s t ∧ env t.mem base = f (env s.mem base) ∧
      Post t.mem := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega_using [this]⟩
  obtain ⟨tr, t, he, hk, hv, hp⟩ := correct narrow hn hpre
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, ⟨hk.gpr, rfl, rfl, hk.mem⟩, hv, hp⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

end VG.Proof.Ed25519.X86_64

end

end


/-!
# Ed25519's point functions on x86-64: what they compute

Untrusted: everything here is checked by Lean. From `ws` in `rdi`, writable
for its 8192 bytes (`Scratch`), a function running the field program `ops`
(`fn_ok`) keeps every register but the field arithmetic's caller-saved ones
(`rax`, `rcx`, `rdx`, `r8`–`r11`): `saves` changes only `xmm0`–`xmm4`, the
program only the arithmetic's registers (`Keep`), and `restores` brings back
`rbp` and `r12`–`r15`, which `KeepReg.keeps` follows through `xmm0`–`xmm4`.
The program's values are `evalOps ops` of the slots', and it changes only the
bytes of its results (`fieldCode_frame`). The doubling's values are RFC
8032's formula's (`dblOps_formula`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Point64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Point64 VG.Proof.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (clob ofs)

variable {fld : Arith} [EdArith fld]

private theorem setXmm_gpr (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).gpr = s.gpr := rfl
private theorem setXmm_mem (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).mem = s.mem := rfl
private theorem setXmm_rd (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).rd = s.rd := rfl
private theorem setXmm_wr (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).wr = s.wr := rfl

/-- The registers the functions restore. -/
abbrev keptRegs : List Reg := kept.map Prod.fst

theorem saves_ok (s : State) :
    WP isa (.block saves) s fun t => t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [saves, kept, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, Option.some.injEq, exists_eq_left', setXmm_gpr, setXmm_mem, setXmm_rd, setXmm_wr]
  exact ⟨trivial, trivial, trivial, trivial⟩

theorem restores_ok (s : State) :
    WP isa (.block restores) s fun t => (∀ r, r ∉ keptRegs → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [restores, kept, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [keptRegs, kept, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    not_or] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2.1,
    RegUpd.gpr_setReg_of_ne _ _ hr.2.2.1, RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2.1,
    RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2.2]

/-- `fieldCode_frame` for the whole working space. -/
theorem fieldCodeWideF_ok {s : State} {base : Addr} (hs : Scratch s base) (ops : List FieldOp) :
    WP isa (.block (fieldCode fld ops)) s fun t => Keep base s t ∧
      env t.mem base = evalOps ops (env s.mem base) ∧ ∀ x, Outs ops base x → t.mem x = s.mem x :=
  field_liftB hs _ (evalOps ops) (· = s.mem) (fun m => ∀ x, Outs ops base x → m x = s.mem x) rfl
    fun _ ht hp => WP.mono (fieldCode_frame ops ht) fun u ⟨k, e, f⟩ =>
      ⟨k, e, fun x hx => by rw [f x hx, hp]⟩

/-- A function running the field program `ops`: every register but the field arithmetic's
caller-saved ones kept, the slots' values `evalOps ops` of theirs, and memory changed only at
the program's results. -/
theorem fn_ok {s : State} {base : Addr} (hs : Scratch s base) (ops : List FieldOp)
    (hk : ∀ r ∈ keptRegs, KeepReg.keeps r (fn fld ops) = true) :
    WP isa (fn fld ops) s fun t => (∀ r, (r ∉ clob ∨ r ∈ keptRegs) → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ env t.mem base = evalOps ops (env s.mem base) ∧
      ∀ x, Outs ops base x → t.mem x = s.mem x := by
  have hw : WP isa (fn fld ops) s fun t => (∀ r, r ∉ clob → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ env t.mem base = evalOps ops (env s.mem base) ∧
      ∀ x, Outs ops base x → t.mem x = s.mem x := by
    simp only [fn, List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (saves_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁⟩ => ?_
    have hs₁ : Scratch s₁ base := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
    rw [WP.block_append_iff]
    refine WP.mono (fieldCodeWideF_ok hs₁ ops) fun s₂ ⟨k₂, e₂, f₂⟩ => ?_
    refine WP.mono (restores_ok s₂) fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ => ?_
    refine ⟨fun r hr => ?_, by rw [rd₃, k₂.rd, rd₁], by rw [wr₃, k₂.wr, wr₁], by rw [m₃, e₂, m₁],
      fun x hx => by rw [m₃, f₂ x hx, m₁]⟩
    have hk' : r ∉ keptRegs := fun h => hr (by
      revert h; simp only [keptRegs, kept, clob, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl | rfl) <;> simp)
    rw [g₃ r hk', k₂.gpr r hr, g₁]
  obtain ⟨t, s', he, h⟩ := hw
  exact ⟨t, s', he, fun r hr => hr.elim (h.1 r) fun hm => Exec.gpr_keeps (hk r hm) he, h.2⟩

/-! ## The programs' values -/

/-- What `dblOps` leaves in slots 0–3. -/
def dblResult (e : Env) : Spec.Ed25519.Point :=
  let a := e 0 * e 0
  let b := e 1 * e 1
  let c := e 2 * e 2 + e 2 * e 2
  let ee := e 0 * e 1 + e 0 * e 1
  let g := b - a
  let f := g - c
  let h := g - b - b
  ⟨ee * f, g * h, f * g, ee * h⟩

theorem dblOps_formula (e : Env) (t : Bool) :
    evalOps (dblOps t) e 0 = (dblResult e).X ∧ evalOps (dblOps t) e 1 = (dblResult e).Y ∧
      evalOps (dblOps t) e 2 = (dblResult e).Z ∧ (t = true → evalOps (dblOps t) e 3 = (dblResult e).T) := by
  cases t
  · exact ⟨rfl, rfl, rfl, nofun⟩
  · exact ⟨rfl, rfl, rfl, fun _ => rfl⟩

end VG.Proof.Ed25519.X86_64.Point64

end

end

/-!
# The point functions keep `rbp` and `r12`–`r15`

Untrusted: everything here is checked by Lean. Each function saves the
registers in `xmm0`–`xmm4`, runs field code that writes no vector register,
and restores them (`fn`), so it keeps them (`fn_keeps`): one pass over the
code, where `KeepReg.keeps` evaluated on the code would take one for each
register.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Point64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Point64

variable {fld : Arith} [EdArith fld]

/-- The code between a function's saves and restores (`fn`'s five each). -/
def midCode : Prog isa → List Instr
  | .block l => (l.drop 5).take (l.length - 10)
  | _ => []

theorem midCode_fn (fld : Arith) (ops : List FieldOp) : midCode (fn fld ops) = fieldCode fld ops := by
  simp [midCode, fn, saves, restores, kept]

/-- A function keeps `rbp` and `r12`–`r15` if its field code writes no vector register: one
pass over the code, where `KeepReg.keeps` would take one for each register. -/
theorem fn_keeps {fld : Arith} {ops : List FieldOp}
    (h : (midCode (fn fld ops)).all (fun i => !KeepReg.writesVec i) = true) :
    ∀ r ∈ keptRegs, KeepReg.keeps r (fn fld ops) = true := by
  rw [midCode_fn] at h
  intro r hr
  refine KeepReg.keeps_around h fun b => ?_
  simp only [keptRegs, kept, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide

/-- The functions' bodies keep `rbp` and `r12`–`r15`. -/
theorem doubleFn_keeps (t : Bool) : ∀ r ∈ keptRegs, KeepReg.keeps r (doubleFn fld t) = true := by
  rcases EdArith.known (fld := fld) with rfl | rfl <;> cases t <;>
    exact fn_keeps (by lit_decide)

theorem addFn_keeps (t : Bool) : ∀ r ∈ keptRegs, KeepReg.keeps r (addFn fld t) = true := by
  rcases EdArith.known (fld := fld) with rfl | rfl <;> cases t <;>
    exact fn_keeps (by lit_decide)

theorem addAffineFn_keeps : ∀ r ∈ keptRegs, KeepReg.keeps r (addAffineFn fld) = true := by
  rcases EdArith.known (fld := fld) with rfl | rfl <;>
    exact fn_keeps (by lit_decide)

end VG.Proof.Ed25519.X86_64.Point64

end

end

/-! ### `Ed25519.X86_64.WindowEntry`, which this module and modules that import it used -/

section

/-!
# Loading a table entry

`pointFromTableQ` copies a table entry to slots 4–7 (`pointFromTableQ_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off F fe_st4 st4_outside Outside Keeps clob)
open VG.Impl.X25519.X86_64 (stores)

variable {fld : Arith} [EdArith fld]

theorem fromTableQuarterQ_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (j : Nat) (hj : j < 4) (ho : o + 128 ≤ 8192) :
    WP isa (.block (fromTableWords (32 * j) ++ stores (192 + 32 * j) .r8 .r9 .r10 .r11)) s fun t =>
      env t.mem base ⟨4 + j, by omega_using [hj]⟩ = F s.mem base (o + 32 * j) ∧
      TableKeep base (192 + 32 * j) 32 s t := by
  rw [WP.block_append_iff]
  refine WP.mono (fromTableWords_ok hs hp (32 * j) (by omega_using [hj, ho])) fun t ⟨hv, hk⟩ => ?_
  have ht := hs.of_keeps hk (by decide)
  refine WP.mono (stores8192_ok ht.rdi ht.wr (by omega_using [hj] : 192 + 32 * j + 32 ≤ 8192)
    .r8 .r9 .r10 .r11) fun u ⟨hm, hg, hrd, hwr⟩ => ?_
  refine ⟨?_, ⟨fun r hr => (congrFun hg r).trans (hk.1 r hr), hrd.trans hk.2.2.1,
    hwr.trans hk.2.2.2, ?_⟩⟩
  · change F u.mem base (64 + 32 * (4 + j)) = _
    rw [show 64 + 32 * (4 + j) = 192 + 32 * j by omega_using [], F, hm, fe_st4 _ _ (by omega_using [hj]), hv]
  · rw [hm, hk.2.1]; exact st4_outside _ _ (by omega_using [hj]) _ _ _ _

theorem fromTablePrefixQ_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192)
    (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j =>
      fromTableWords (32 * j) ++ stores (192 + 32 * j) .r8 .r9 .r10 .r11)) s fun t =>
      (∀ j (hj : j < n), env t.mem base ⟨4 + j, by omega_using [hn, hj]⟩ = F s.mem base (o + 32 * j)) ∧
      TableKeep base 192 (32 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun j hj => by omega,
      ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs hp (by omega_using [hn])) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (fromTableQuarterQ_ok (hk.scratch hs)
      ((hk.gpr _ (by decide)).trans hp) n (by omega_using [hn]) ho) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, (hk.mono (by omega_using []) (by omega_using [])).trans
      (ku.mono (by omega_using []) (by omega_using []))⟩
    by_cases h : j < n
    · have he : env u.mem base ⟨4 + j, by omega_using [hn, hj]⟩ = env t.mem base ⟨4 + j, by omega_using [hn, hj]⟩ :=
        Outside_F ku.mem (by simp only [offset]; omega_using [hn, hj]) (Or.inl (by simp only [offset]; omega_using [h]))
      rw [he, hv j h]
    · have he : j = n := by omega_using [hj, h]
      subst j
      rw [hu, Outside_F hk.mem (by omega_using [ho, hn]) (Or.inr (by omega_using [hlo]))]

theorem pointFromTableQ_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointFromTableQ) s fun t =>
      point (env t.mem base) 4 5 6 7 = tablePoint s.mem base o ∧ TableKeep base 192 128 s t := by
  refine WP.mono (fromTablePrefixQ_ok hs hp hlo ho 4 (by decide)) fun t ⟨hv, hk⟩ => ?_
  refine ⟨?_, hk⟩
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  change env t.mem base 4 = _ at h0
  change env t.mem base 5 = _ at h1
  change env t.mem base 6 = _ at h2
  change env t.mem base 7 = _ at h3
  simp only [tablePoint, point, h0, h1, h2, h3]

theorem Keep.of_tableQ {base : Addr} {s t : State}
    (h : TableKeep base 192 128 s t) : Keep base s t := by
  refine ⟨fun r hr => h.gpr r (fun hm => hr ?_), h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩
  exact (show ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∈ clob by decide) r hm

end VG.Proof.Ed25519.X86_64

end

end

/-! ### `Ed25519.X86_64.Point64.Ops`, which only this module used -/

section

/-!
# The point operations a caller runs

Untrusted: everything here is checked by Lean. The proofs of the code that
doubles and adds points (verification's table and windows) hold for any
point operations `pt` that change what the field programs `dblOps` and
`addCachedOps` inlined would (`PtOk`): `Keep` and the slots' values. The
functions' bodies, which calls of them run as (`Code.inline`), are such
operations (`bodies_ok`, from `fn_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Point64
open VG.Proof.X25519.X86_64 (clob ofs)

/-- Point operations that do what the field programs inlined would. -/
class PtOk (pt : Point64.Ops) : Prop where
  dbl : ∀ {s : State} {base : Addr}, Scratch s base → ∀ t,
    WP isa (pt.dbl t) s fun u => Keep base s u ∧ env u.mem base = evalOps (dblOps t) (env s.mem base)
  add : ∀ {s : State} {base : Addr}, Scratch s base → ∀ t,
    WP isa (pt.add t) s fun u => Keep base s u ∧ env u.mem base = evalOps (addCachedOps t) (env s.mem base)

namespace Point64

variable {fld : Arith} [EdArith fld]

/-- A body's `Keep`, from `fn_ok`: its results are in slots 0–15. -/
theorem fn_keep {s : State} {base : Addr} (hs : Scratch s base) (ops : List FieldOp)
    (hk : ∀ r ∈ keptRegs, KeepReg.keeps r (fn fld ops) = true)
    (hout : ∀ op ∈ ops, 64 ≤ offset op.out ∧ offset op.out + 32 ≤ 768) :
    WP isa (fn fld ops) s fun u => Keep base s u ∧ env u.mem base = evalOps ops (env s.mem base) :=
  WP.mono (fn_ok hs ops hk) fun _ ⟨hg, hrd, hwr, hv, hm⟩ =>
    ⟨⟨fun r hr => hg r (.inl hr), hrd, hwr, fun x hx => hm x fun op hop => by
      have := hout op hop; omega_using [hx, this]⟩, hv⟩

end Point64

instance {fld : Arith} [EdArith fld] : PtOk (Point64.bodies fld) where
  dbl hs t := Point64.fn_keep hs (dblOps t) (Point64.doubleFn_keeps t) (by cases t <;> decide)
  add hs t := Point64.fn_keep hs (addCachedOps t) (Point64.addFn_keeps t) (by cases t <;> decide)

end VG.Proof.Ed25519.X86_64

end

end


/-! Merged from `Proof.Ed25519.X86_64.WindowTables`. -/

@[expose] public section

section
/-!
# Verification's table: `[1]A … [15]A`

The table of multiples of `A` is built by repeated addition of `A`, each entry
representing its multiple (`Rep`); the negated multiples of `B` are a static
(`BaseTbl`).
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off Keeps clob Outside)
open VG.Impl.X25519.X86_64 (loads)

variable {fld : Arith} [EdArith fld] {pt : Point64.Ops} [PtOk pt]

theorem tableStart_ok {s : State} {base : Addr} (hp : s.gpr .rdi = base) (o : Nat) :
    WP isa (.block (tableStart o)) s fun t => t.gpr .rax = off base o ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [tableStart, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hp, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨BitVec.add_comm _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-! ## `[i]A` -/

theorem rbxSet_ok (s : State) (n : Nat) (hn : n < 2 ^ 31) :
    WP isa (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 n))]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 n ∧ Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]

/-- Slots 8–11 to the table entry at `rax`, a quarter at a time. -/
theorem cachedQuarter_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (j : Nat) (hj : j < 4) (ho : o + 128 ≤ 8192) :
    WP isa (.block (loads (320 + 32 * j) .r8 .r9 .r10 .r11 ++ tableWords (32 * j))) s fun t =>
      Proof.X25519.X86_64.F t.mem base (o + 32 * j) = env s.mem base ⟨8 + j, by omega_arith⟩ ∧
      TableKeep base (o + 32 * j) 32 s t := by
  rw [WP.block_append_iff, show 320 + 32 * j = offset ⟨8 + j, by omega_arith⟩ by simp only [offset]; omega_arith]
  refine WP.mono (loadsFieldWide_ok hs ⟨8 + j, by omega_arith⟩) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (tableWords_ok (hs.of_keeps hk (by decide)) ((hk.1 _ (by decide)).trans hp) (32 * j)
    (by omega_arith)) fun u ⟨hm, hg, hrd, hwr⟩ => ?_
  refine ⟨?_, ⟨fun r hr => (congrFun hg r).trans (hk.1 r hr), hrd.trans hk.2.2.1,
    hwr.trans hk.2.2.2, ?_⟩⟩
  · rw [Proof.X25519.X86_64.F, hm, Proof.X25519.X86_64.fe_st4 _ _ (by omega_arith), hv]
    rfl
  · rw [hm, hk.2.1]; exact Proof.X25519.X86_64.st4_outside _ _ (by omega_arith) _ _ _ _

theorem cachedPrefix_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j =>
      loads (320 + 32 * j) .r8 .r9 .r10 .r11 ++ tableWords (32 * j))) s fun t =>
      (∀ j (hj : j < n), Proof.X25519.X86_64.F t.mem base (o + 32 * j) = env s.mem base ⟨8 + j, by omega_arith⟩) ∧
      TableKeep base o (32 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun j hj => by omega_arith, ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs hp (by omega_arith)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (cachedQuarter_ok (hk.scratch hs) ((hk.gpr _ (by decide)).trans hp) n (by omega_arith) ho)
      fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, (hk.mono (by omega_arith) (by omega_arith)).trans (ku.mono (by omega_arith) (by omega_arith))⟩
    by_cases h : j < n
    · rw [Outside_F ku.mem (by omega_arith) (Or.inl (by omega_arith)), hv j h]
    · have he : j = n := by omega_arith
      subst j
      rw [hu, table_env hk.mem hlo]

theorem cachedToTable_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block cachedToTable) s fun t =>
      tablePoint t.mem base o = point (env s.mem base) 8 9 10 11 ∧ TableKeep base o 128 s t := by
  refine WP.mono (cachedPrefix_ok hs hp hlo ho 4 (by decide)) fun t ⟨hv, hk⟩ => ?_
  refine ⟨?_, hk⟩
  obtain h0 := hv 0 (by decide)
  obtain h1 := hv 1 (by decide)
  obtain h2 := hv 2 (by decide)
  obtain h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  simp only [tablePoint, point, h0, h1, h2, h3]
  rfl

/-- `cacheOps` caches the point in slots 0–3 into slots 8–11, keeping slots 0–3 and those from 16. -/
theorem cacheOps_eval (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    point (evalOps cacheOps e) 8 9 10 11 = cache (point e 0 1 2 3) ∧
      point (evalOps cacheOps e) 0 1 2 3 = point e 0 1 2 3 ∧
      ∀ i : Slot, 16 ≤ i.val → evalOps cacheOps e i = e i := by
  refine ⟨?_, rfl, point_ops_high _ (by decide) e⟩
  show (⟨e 1 - e 0, e 1 + e 0, e 3 * e 16 + e 3 * e 16, e 2 + e 2⟩ : Spec.Ed25519.Point) = _
  simp only [cache, point, hd]
  congr 1 <;> grind

theorem dblOpsH_eval (e : Env) :
    point (evalOps (dblOpsH true) e) 0 1 2 3 = dblPoint (point e 0 1 2 3) ∧
    evalOps (dblOpsH false) e 0 = (dblPoint (point e 0 1 2 3)).X ∧
    evalOps (dblOpsH false) e 1 = (dblPoint (point e 0 1 2 3)).Y ∧
    evalOps (dblOpsH false) e 2 = (dblPoint (point e 0 1 2 3)).Z :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- RFC 8032's doubling (`dblOps`) is `dbl-2008-hwcd` (`dblPoint`) with every coordinate
negated. -/
theorem dblOps_neg (e : Env) (t : Bool) :
    evalOps (dblOps t) e 0 = -(dblPoint (point e 0 1 2 3)).X ∧
      evalOps (dblOps t) e 1 = -(dblPoint (point e 0 1 2 3)).Y ∧
      evalOps (dblOps t) e 2 = -(dblPoint (point e 0 1 2 3)).Z ∧
      (t = true → evalOps (dblOps t) e 3 = -(dblPoint (point e 0 1 2 3)).T) := by
  obtain ⟨h0, h1, h2, h3⟩ := Point64.dblOps_formula e t
  refine ⟨h0.trans ?_, h1.trans ?_, h2.trans ?_, fun ht => (h3 ht).trans ?_⟩ <;>
    (simp only [Point64.dblResult, dblPoint, point]; grind)

theorem toZ_neg (a : Spec.X25519.Fe) : toZ (-a) = -toZ a := rfl

/-- `dblOps` doubles what the slots represent. -/
theorem dblOps_rep (e : Env) (t : Bool) {a : EPoint dZ} (ha : RepP (point e 0 1 2 3) a) :
    RepP (point (evalOps (dblOps t) e) 0 1 2 3) (a + a) ∧
      (t = true → Rep (point (evalOps (dblOps t) e) 0 1 2 3) (a + a)) := by
  obtain hr := dblPoint_rep ha
  obtain ⟨n0, n1, n2, n3⟩ := dblOps_neg e t
  refine ⟨⟨?_, ?_, ?_⟩, fun ht => ⟨?_, ?_, ?_, ?_⟩⟩
  · dsimp only [point]
    rw [n2, toZ_neg]; exact neg_ne_zero.mpr hr.z
  · dsimp only [point]
    rw [n0, n2, toZ_neg, toZ_neg, hr.x, mul_neg]
  · dsimp only [point]
    rw [n1, n2, toZ_neg, toZ_neg, hr.y, mul_neg]
  · dsimp only [point]
    rw [n2, toZ_neg]; exact neg_ne_zero.mpr hr.z
  · dsimp only [point]
    rw [n0, n2, toZ_neg, toZ_neg, hr.x, mul_neg]
  · dsimp only [point]
    rw [n1, n2, toZ_neg, toZ_neg, hr.y, mul_neg]
  · dsimp only [point]
    rw [n3 ht, n2, toZ_neg, toZ_neg, hr.t, mul_neg]

/-- The cached addition of the point operations: `pointAdd` of the accumulator and the
point whose cached form is in slots 4–7. -/
theorem addPtWide_ok {s : State} {base : Addr} (hs : Scratch s base)
    (q : Spec.Ed25519.Point) (hq : point (env s.mem base) 4 5 6 7 = cache q) :
    WP isa (pt.add true) s fun t =>
      Keep base s t ∧ point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i :=
  WP.mono (PtOk.add hs true) fun t ⟨hk, hv⟩ => by
    rw [hv]
    exact ⟨hk, pointAddCached_eval _ q hq, pointAddCached_high _⟩

theorem negOps_eval (e : Env) :
    point (evalOps negOps e) 0 1 2 3 = negPoint (point e 0 1 2 3) ∧
      ∀ i : Slot, 16 ≤ i.val → evalOps negOps e i = e i :=
  ⟨rfl, point_ops_high _ (by decide) e⟩

/-- The point in slots 8–11 to the entry at byte `o + 128 n` (`rbx = n`): what is kept. -/
theorem storeEntry_ok {s : State} {base : Addr} (hs : Scratch s base) (o n : Nat) (hlo : 3216 ≤ o)
    (hhi : o + 128 * n + 128 ≤ 7424) (hn : n < 64) (hc : s.gpr .rbx = BitVec.ofNat 64 n) :
    WP isa (.block (tableAddr o ++ cachedToTable)) s fun t =>
      tablePoint t.mem base (o + 128 * n) = point (env s.mem base) 8 9 10 11 ∧
      env t.mem base = env s.mem base ∧
      (∀ d, 768 ≤ d → (d + 128 ≤ o + 128 * n ∨ o + 128 * n + 128 ≤ d) → d + 128 ≤ 8192 →
        tablePoint t.mem base d = tablePoint s.mem base d) ∧
      t.gpr .rbx = s.gpr .rbx ∧ PowersKeep base 3216 4208 s t := by
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok hs.rdi o n hn hc) fun d ⟨dp, kd⟩ => ?_
  obtain kde : Keep base s d := Keep.of_keeps kd (by decide)
  refine WP.mono (cachedToTable_ok (hs.of_keep kde) dp (by omega_arith) (by omega_arith)) fun e ⟨ep, ke⟩ => ?_
  obtain ee : env e.mem base = env d.mem base := table_env ke.mem (by omega_arith)
  obtain kall : PowersKeep base 3216 4208 s e :=
    (PowersKeep.of_keep kde).trans ⟨fun r _ _ hr => ke.gpr r (fun hm => hr (by
      revert hm; simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl) <;> decide)), ke.rd, ke.wr,
      (TableFrame.table ke.mem).mono (by omega_arith) (by omega_arith)⟩
  refine ⟨by rw [ep, kd.2.1], by rw [ee, kd.2.1], fun d hd hsep hd' => ?_, ?_, kall⟩
  · rw [(TableFrame.table ke.mem).point hd hsep (by omega_arith), kd.2.1]
  · rw [ke.gpr _ (by decide), kd.1 _ (by decide)]

/-- The point `p` in slots 0–3 to entries `2m` (cached) and `2m + 1` (its negation, cached) of the
table at byte 5376, keeping a representative of the same point in slots 0–3. -/
theorem aTableStore_ok {s : State} {base : Addr} (hs : Scratch s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) {m : Nat} (hm : m < 8)
    (hc : s.gpr .rbx = BitVec.ofNat 64 (2 * m)) {a : EPoint dZ} (ha : Rep (point (env s.mem base) 0 1 2 3) a) :
    WP isa (.block (aTableStore fld)) s fun t =>
      tablePoint t.mem base (5376 + 128 * (2 * m)) = cache (point (env s.mem base) 0 1 2 3) ∧
      tablePoint t.mem base (5376 + 128 * (2 * m + 1)) = cache (negPoint (point (env s.mem base) 0 1 2 3)) ∧
      Rep (point (env t.mem base) 0 1 2 3) a ∧ env t.mem base 16 = env s.mem base 16 ∧
      (∀ d, 768 ≤ d → (d + 128 ≤ 5376 + 128 * (2 * m) ∨ 5376 + 128 * (2 * m + 2) ≤ d) → d + 128 ≤ 8192 →
        tablePoint t.mem base d = tablePoint s.mem base d) ∧
      t.gpr .rbx = s.gpr .rbx ∧ PowersKeep base 3216 4208 s t := by
  rw [aTableStore]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  -- Entry `2m`.
  refine WP.mono (fieldCodeWide_ok hs cacheOps) fun a1 ⟨k1, v1⟩ => ?_
  obtain ⟨c8, c0, chi⟩ := cacheOps_eval (env s.mem base) hd
  rw [← v1] at c8 c0 chi
  obtain hs1 := hs.of_keep k1
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (storeEntry_ok hs1 5376 (2 * m) (by decide) (by omega_arith) (by omega_arith)
    ((k1.gpr _ (by decide)).trans hc)) fun a2 ⟨e2, v2, o2, r2, k2⟩ => ?_
  obtain hs2 := k2.scratch hs1
  -- Entry `2m + 1`.
  rw [WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok hs2 (negOps ++ cacheOps)) fun a3 ⟨k3, v3⟩ => ?_
  obtain n3 := negOps_eval (env a2.mem base)
  obtain hd2 : env a2.mem base 16 = Spec.Ed25519.d := by rw [v2, chi 16 (by decide), hd]
  obtain ⟨c8', c0', chi'⟩ := cacheOps_eval (evalOps negOps (env a2.mem base)) (by rw [n3.2 16 (by decide), hd2])
  obtain v3' : env a3.mem base = evalOps cacheOps (evalOps negOps (env a2.mem base)) := by
    rw [v3]; simp only [evalOps, List.foldl_append]
  rw [← v3'] at c8' c0' chi'
  obtain hs3 := hs2.of_keep k3
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (storeEntry_ok hs3 5504 (2 * m) (by decide) (by omega_arith) (by omega_arith)
    ((k3.gpr _ (by decide)).trans (r2.trans ((k1.gpr _ (by decide)).trans hc)))) fun a4 ⟨e4, v4, o4, r4, k4⟩ => ?_
  obtain hs4 := k4.scratch hs3
  -- The point back.
  refine WP.mono (fieldCodeWide_ok hs4 negOps) fun t ⟨kt, vt⟩ => ?_
  obtain nt := negOps_eval (env a4.mem base)
  rw [← vt] at nt
  obtain p2 : point (env a2.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by rw [v2, c0]
  obtain p4 : point (env a4.mem base) 0 1 2 3 = negPoint (point (env s.mem base) 0 1 2 3) := by
    rw [v4, c0', n3.1, p2]
  obtain w1 := workspace_tablePoint (m := a3.mem) (m' := a4.mem) (base := base)
  refine ⟨?_, ?_, ?_, ?_, fun d hd hsep hd' => ?_, ?_, ?_⟩
  · rw [workspace_tablePoint kt.mem (by omega_arith) (by omega_arith),
      o4 _ (by omega_arith) (Or.inl (by omega_arith)) (by omega_arith), workspace_tablePoint k3.mem (by omega_arith) (by omega_arith), e2, c8]
  · rw [workspace_tablePoint kt.mem (by omega_arith) (by omega_arith),
      show 5376 + 128 * (2 * m + 1) = 5504 + 128 * (2 * m) by omega_arith, e4, c8', n3.1, p2]
  · rw [nt.1, p4]
    have := ha.neg.neg
    rwa [neg_neg] at this
  · rw [nt.2 16 (by decide), v4, chi' 16 (by decide), n3.2 16 (by decide), v2, chi 16 (by decide)]
  · rw [workspace_tablePoint kt.mem hd (by omega_arith), o4 _ hd (by omega_arith) hd',
      workspace_tablePoint k3.mem hd (by omega_arith), o2 _ hd (by omega_arith) hd',
      workspace_tablePoint k1.mem hd (by omega_arith)]
  · rw [kt.gpr _ (by decide), r4, k3.gpr _ (by decide), r2, k1.gpr _ (by decide)]
  · exact (((PowersKeep.of_keep k1).trans k2).trans ((PowersKeep.of_keep k3).trans k4)).trans
      (PowersKeep.of_keep kt)

/-- The table of `A`'s odd multiples, with `n` pairs of entries and `[2n - 1]A` in slots 0–3. -/
structure ATableInv (s₀ : State) (base : Addr) (A : EPoint dZ) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 8
  scratch : Scratch s base
  counter : s.gpr .rbx = BitVec.ofNat 64 (2 * n)
  d : env s.mem base 16 = Spec.Ed25519.d
  value : Rep (point (env s.mem base) 0 1 2 3) ((2 * n - 1) • A)
  two : ∃ q, tablePoint s.mem base 3216 = cache q ∧ Rep q ((2 : Nat) • A)
  table : ∀ e < 2 * n, ∃ q, tablePoint s.mem base (5376 + 128 * e) = cache q ∧
    Rep q ((Recode.dec (e + 1)) • A)
  a : tablePoint s.mem base 7424 = tablePoint s₀.mem base 7424
  keep : PowersKeep base 3216 4208 s₀ s

/-- The entries of `p` and `-p` represent `dec (2m + 1)` and `dec (2m + 2)` times `A`. -/
theorem pair_rep {p : Spec.Ed25519.Point} {A : EPoint dZ} {m : Nat} (h : Rep p ((2 * m + 1) • A)) :
    Rep p ((Recode.dec (2 * m + 1)) • A) ∧ Rep (negPoint p) ((Recode.dec (2 * m + 1 + 1)) • A) := by
  rw [Recode.dec_odd (by omega_arith), Recode.dec_even (by omega_arith) (by omega_arith)]
  refine ⟨by rw [natCast_zsmul]; exact h, ?_⟩
  rw [show (1 : Int) - ((2 * m + 1 + 1 : Nat) : Int) = -((2 * m + 1 : Nat) : Int) by push_cast; ring,
    neg_smul, natCast_zsmul]
  exact h.neg

theorem rbxStep_ok (s : State) (n : Nat) (hn : n < 8) (hc : s.gpr .rbx = BitVec.ofNat 64 (2 * n)) :
    WP isa (.block [.alu .add .rbx (.imm 2), .alu .cmp .rbx (.imm 16)]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (2 * (n + 1)) ∧ t.zf = some (decide (n + 1 = 8)) ∧ Keeps [.rbx] s t := by
  obtain ha : BitVec.ofNat 64 (2 * n) + (2 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (2 * (n + 1)) := by
    rw [show (2 : BitVec 32).signExtend 64 = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add]
    congr 1
  obtain hz : (BitVec.ofNat 64 (2 * (n + 1)) - (16 : BitVec 32).signExtend 64 == 0) = decide (n + 1 = 8) := by
    rw [show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hn]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags,
    hc, ha, hz, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem aTableBody_ok {s₀ s : State} {base : Addr} {A : EPoint dZ} {n : Nat} (hn : n < 8)
    (h : ATableInv s₀ base A n s) :
    WP isa (aTableBody fld pt) s fun t => t.zf = some (decide (n + 1 = 8)) ∧
      ATableInv s₀ base A (n + 1) t := by
  obtain ⟨q₂, hq₂, hr₂⟩ := h.two
  rw [aTableBody]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableStart_ok h.scratch.rdi 3216) fun a ⟨ap, ka⟩ => ?_
  obtain kae : Keep base s a := Keep.of_keeps ka (by decide)
  refine WP.mono (pointFromTableQ_ok (h.scratch.of_keep kae) ap (by decide) (by decide))
    fun b ⟨pb, kb⟩ => ?_
  obtain kbe := Keep.of_tableQ kb
  obtain b_low : ∀ i : Slot, i.val < 4 → env b.mem base i = env s.mem base i := by
    intro i hi
    change Proof.X25519.X86_64.F b.mem base (offset i) = Proof.X25519.X86_64.F s.mem base (offset i)
    rw [Outside_F kb.mem (by simp only [offset]; omega_arith) (Or.inl (by simp only [offset]; omega_arith)), ka.2.1]
  obtain b16 : env b.mem base 16 = env s.mem base 16 := by
    change Proof.X25519.X86_64.F b.mem base (offset 16) = Proof.X25519.X86_64.F s.mem base (offset 16)
    rw [Outside_F kb.mem (by simp only [offset]; omega_arith) (Or.inr (by simp only [offset]; omega_arith)), ka.2.1]
  obtain bp : point (env b.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, b_low 0 (by decide), b_low 1 (by decide), b_low 2 (by decide), b_low 3 (by decide)]
  obtain kab := kae.trans kbe
  refine WP.seq (WP.mono (addPtWide_ok (pt := pt) (h.scratch.of_keep kab) q₂
    (by rw [pb, ka.2.1, hq₂])) fun c ⟨kc, cp, ch⟩ => ?_)
  obtain crep : Rep (point (env c.mem base) 0 1 2 3) ((2 * (n + 1) - 1) • A) := by
    rw [cp, bp, show 2 * (n + 1) - 1 = (2 * n - 1) + 2 by have := h.positive; omega_arith, add_nsmul]
    exact pointAdd_rep h.value hr₂
  obtain kabc := kab.trans kc
  obtain cd : env c.mem base 16 = Spec.Ed25519.d := (ch 16 (by decide)).trans (b16.trans h.d)
  rw [WP.block_append_iff]
  refine WP.mono (aTableStore_ok (fld := fld) (h.scratch.of_keep kabc) cd hn
    ((kabc.gpr _ (by decide)).trans h.counter) crep) fun e ⟨e0, e1, ev, e16, eo, eb, ke⟩ => ?_
  refine WP.mono (rbxStep_ok e n hn (eb.trans ((kabc.gpr _ (by decide)).trans h.counter)))
    fun t ⟨tc, tz, kt⟩ => ?_
  obtain kall : PowersKeep base 3216 4208 s t :=
    ((PowersKeep.of_keep kabc).trans ke).trans (PowersKeep.of_keeps kt (by decide))
  obtain te : env t.mem base = env e.mem base := by rw [kt.2.1]
  obtain hp := pair_rep (m := n) (A := A) (p := point (env c.mem base) 0 1 2 3)
    (by rw [show 2 * n + 1 = 2 * (n + 1) - 1 by omega_arith]; exact crep)
  refine ⟨tz, by omega_arith, by omega_arith, kall.scratch h.scratch, tc, ?_, ?_, ?_, ?_, ?_, h.keep.trans kall⟩
  · rw [te, e16, cd]
  · rw [te]; exact ev
  · refine ⟨q₂, ?_, hr₂⟩
    rw [kt.2.1, eo 3216 (by decide) (Or.inl (by omega_arith)) (by decide),
      workspace_tablePoint kc.mem (by omega_arith) (by omega_arith), workspace_tablePoint kab.mem (by omega_arith) (by omega_arith), hq₂]
  · intro j hj
    rw [kt.2.1]
    by_cases hjn : j < 2 * n
    · rw [eo _ (by omega_arith) (Or.inl (by omega_arith)) (by omega_arith), workspace_tablePoint kc.mem (by omega_arith) (by omega_arith),
        workspace_tablePoint kab.mem (by omega_arith) (by omega_arith)]
      exact h.table j hjn
    · rcases (show j = 2 * n ∨ j = 2 * n + 1 by omega_arith) with rfl | rfl
      · exact ⟨_, e0, hp.1⟩
      · exact ⟨_, e1, hp.2⟩
  · rw [kt.2.1, eo 7424 (by decide) (Or.inr (by omega_arith)) (by decide),
      workspace_tablePoint kc.mem (by omega_arith) (by omega_arith),
      workspace_tablePoint kab.mem (by omega_arith) (by omega_arith)]
    exact h.a

theorem aTableInit_ok {s : State} {base : Addr} {A : EPoint dZ} (hs : Scratch s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (hA : Rep (tablePoint s.mem base 7424) A) :
    WP isa (aTableInit fld pt) s (ATableInv s base A 1) := by
  rw [aTableInit]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableStart_ok hs.rdi 7424) fun a ⟨ap, ka⟩ => ?_
  obtain kae : Keep base s a := Keep.of_keeps ka (by decide)
  refine WP.mono (pointFromTable_ok (hs.of_keep kae) ap (by decide) (by decide)) fun b ⟨pb, kb⟩ => ?_
  obtain kab := kae.trans (Keep.of_table kb)
  obtain hbs : env b.mem base 16 = env s.mem base 16 := by
    rw [tableLoad_high kb 16 (by decide), ka.2.1]
  obtain bA : Rep (point (env b.mem base) 0 1 2 3) A := by rw [pb, ka.2.1]; exact hA
  -- `[2]A`, cached at byte 3216.
  refine WP.seq (WP.mono (PtOk.dbl (pt := pt) (hs.of_keep kab) true) fun c₀ ⟨kc₀, vc₀⟩ => ?_)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok ((hs.of_keep kab).of_keep kc₀) cacheOps) fun c ⟨kc', vc''⟩ => ?_
  obtain kc : Keep base b c := kc₀.trans kc'
  obtain vc : env c.mem base = evalOps (dblOps true ++ cacheOps) (env b.mem base) := by
    rw [vc'', vc₀]; simp only [evalOps, List.foldl_append]
  obtain dh := point_ops_high (dblOps true) (by decide) (env b.mem base)
  obtain ⟨c8, _, chi⟩ := cacheOps_eval (evalOps (dblOps true) (env b.mem base))
    (by rw [dh 16 (by decide), hbs, hd])
  obtain vc' : env c.mem base = evalOps cacheOps (evalOps (dblOps true) (env b.mem base)) := by
    rw [vc]; simp only [evalOps, List.foldl_append]
  rw [← vc'] at c8 chi
  obtain kbc := kab.trans kc
  rw [WP.block_append_iff]
  refine WP.mono (tableStart_ok (hs.of_keep kbc).rdi 3216) fun c1 ⟨c1p, kc1⟩ => ?_
  obtain kc1e : Keep base c c1 := Keep.of_keeps kc1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (cachedToTable_ok ((hs.of_keep kbc).of_keep kc1e) c1p (by decide) (by decide))
    fun c2 ⟨c2p, kc2⟩ => ?_
  obtain hc2 : Scratch c2 base := ((hs.of_keep kbc).of_keep kc1e) |> kc2.scratch
  obtain c2e : env c2.mem base = env c.mem base := by rw [table_env kc2.mem (by decide), kc1.2.1]
  -- `[1]A` back into slots 0–3.
  rw [WP.block_append_iff]
  refine WP.mono (tableStart_ok hc2.rdi 7424) fun c3 ⟨c3p, kc3⟩ => ?_
  obtain kc3e : Keep base c2 c3 := Keep.of_keeps kc3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTable_ok (hc2.of_keep kc3e) c3p (by decide) (by decide)) fun c4 ⟨c4p, kc4⟩ => ?_
  obtain kc34 := kc3e.trans (Keep.of_table kc4)
  obtain hc4 : Scratch c4 base := hc2.of_keep kc34
  obtain t7424 : tablePoint c3.mem base 7424 = tablePoint s.mem base 7424 := by
    rw [kc3.2.1, (TableFrame.table kc2.mem).point (by decide) (Or.inr (by decide)) (by omega_arith), kc1.2.1,
      workspace_tablePoint kc.mem (by omega_arith) (by omega_arith), workspace_tablePoint kab.mem (by omega_arith) (by omega_arith)]
  obtain c4A : Rep (point (env c4.mem base) 0 1 2 3) A := by rw [c4p, t7424]; exact hA
  obtain c4d : env c4.mem base 16 = Spec.Ed25519.d := by
    rw [tableLoad_high kc4 16 (by decide), kc3.2.1, c2e, chi 16 (by decide), dh 16 (by decide), hbs, hd]
  rw [WP.block_append_iff]
  refine WP.mono (rbxSet_ok c4 0 (by decide)) fun c5 ⟨c5c, kc5⟩ => ?_
  obtain hc5 : Scratch c5 base := hc4.of_keeps kc5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (aTableStore_ok (fld := fld) (m := 0) (a := A) hc5 (by rw [kc5.2.1]; exact c4d) (by decide) c5c
    (by rw [kc5.2.1]; exact c4A)) fun e ⟨e0, e1, ev, e16, eo, eb, ke⟩ => ?_
  refine WP.mono (rbxSet_ok e 2 (by decide)) fun t ⟨tc, kt⟩ => ?_
  obtain k5 : PowersKeep base 3216 4208 s c5 :=
    (((PowersKeep.of_keep kbc).trans (PowersKeep.of_keep kc1e)).trans
      ⟨fun r _ _ hr => kc2.gpr r (fun hm => hr (by
        revert hm; simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (rfl | rfl | rfl | rfl) <;> decide)), kc2.rd, kc2.wr,
        (TableFrame.table kc2.mem).mono (by omega_arith) (by omega_arith)⟩).trans
      ((PowersKeep.of_keep kc34).trans (PowersKeep.of_keeps kc5 (by decide)))
  obtain kall : PowersKeep base 3216 4208 s t := (k5.trans ke).trans (PowersKeep.of_keeps kt (by decide))
  obtain te : env t.mem base = env e.mem base := by rw [kt.2.1]
  obtain c5p : point (env c5.mem base) 0 1 2 3 = point (env c4.mem base) 0 1 2 3 := by rw [kc5.2.1]
  obtain hp := pair_rep (m := 0) (A := A) (p := point (env c5.mem base) 0 1 2 3)
    (by rw [c5p]; simpa using c4A)
  refine ⟨by decide, by decide, kall.scratch hs, tc, ?_, ?_, ?_, ?_, ?_, kall⟩
  · rw [te, e16, kc5.2.1, c4d]
  · rw [te]; simpa using ev
  · refine ⟨point (evalOps (dblOps true) (env b.mem base)) 0 1 2 3, ?_, ?_⟩
    · rw [kt.2.1, eo 3216 (by decide) (Or.inl (by decide)) (by decide), kc5.2.1,
        workspace_tablePoint (Keep.of_table kc4).mem (by omega_arith) (by omega_arith), kc3.2.1, c2p, kc1.2.1, c8]
    · rw [two_nsmul]; exact (dblOps_rep (env b.mem base) true bA.proj).2 rfl
  · intro j hj
    rw [kt.2.1]
    rcases (show j = 0 ∨ j = 1 by omega_arith) with rfl | rfl
    · exact ⟨_, e0, hp.1⟩
    · exact ⟨_, e1, hp.2⟩
  · rw [kt.2.1, eo 7424 (by decide) (Or.inr (by decide)) (by decide), kc5.2.1,
      workspace_tablePoint (Keep.of_table kc4).mem (by omega_arith) (by omega_arith), t7424]

theorem aTable_ok {s : State} {base : Addr} {A : EPoint dZ} (hs : Scratch s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (hA : Rep (tablePoint s.mem base 7424) A) :
    WP isa (aTable fld pt) s (ATableInv s base A 8) := by
  rw [aTable]
  refine WP.seq (WP.mono (aTableInit_ok hs hd hA) fun a ha => ?_)
  apply WP.loop (fun n t => ATableInv s base A (8 - n) t ∧ 0 < n) (n := 7)
  · intro n t ⟨h, hn⟩
    have hp := h.positive
    refine WP.mono (aTableBody_ok (n := 8 - n) (by omega_arith) h) fun u ⟨uz, hu⟩ => ?_
    by_cases he : 8 - n + 1 = 8
    · exact Or.inl ⟨by simp only [eval, uz, he, decide_true, Option.map_some, Bool.not_true],
        by rw [← he]; exact hu⟩
    · exact Or.inr ⟨by simp only [eval, uz, decide_eq_false he, Option.map_some, Bool.not_false],
        n - 1, by omega_arith, by rw [show 8 - (n - 1) = 8 - n + 1 by omega_arith]; exact hu,
        by have := hu.bound; omega_arith⟩
  · exact ⟨ha, by decide⟩

end VG.Proof.Ed25519.X86_64
end

/-!
# Verification's windows: doublings, digits and table additions

The accumulator in slots 0–3 always represents a point of the group (`Rep`):
four doublings multiply it by 16, and a nonzero digit `v` adds entry `v - 1`
of a table, which represents `[v]X`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

variable {fld : Arith} [EdArith fld] {pt : Point64.Ops} [PtOk pt]

/-- What a window may change: the field workspace and the doublings' (below
byte 1888), and the registers it computes with. -/
structure WinKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → r ≠ .rsi → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 64 1824 s.mem t.mem

theorem WinKeep.refl (base : Addr) (s : State) : WinKeep base s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem WinKeep.trans {base : Addr} {s t u : State} (h : WinKeep base s t) (k : WinKeep base t u) :
    WinKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    h.mem.trans k.mem⟩

theorem WinKeep.scratch {base : Addr} {s t : State} (h : WinKeep base s t) (hs : Scratch s base) :
    Scratch t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem WinKeep.of_keep {base : Addr} {s t : State} (h : Keep base s t) : WinKeep base s t :=
  ⟨fun r hr _ _ => h.gpr r hr, h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩

theorem WinKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ r ∈ clob) : WinKeep base s t := by
  refine ⟨fun r hr hb hs => h.1 r (fun hm => ?_), h.2.2.1, h.2.2.2, by rw [h.2.1]; exact Outside.refl _ _ _ _⟩
  rcases hrs r hm with h | h | h
  · exact hb h
  · exact hs h
  · exact hr h

theorem WinKeep.counter {base : Addr} {s t : State} (h : WinKeep base s t) :
    t.mem.readW (off base 56) 64 = s.mem.readW (off base 56) 64 :=
  h.mem.word (Or.inl (by decide)) (by decide)

/-! ## Four doublings -/

theorem dblH_ok {s : State} {base : Addr} (hs : Scratch s base) (t : Bool) {a : EPoint dZ}
    (ha : RepP (point (env s.mem base) 0 1 2 3) a) :
    WP isa (.block (fieldCode fld (dblOpsH t))) s fun u => Keep base s u ∧
      RepP (point (env u.mem base) 0 1 2 3) (a + a) ∧
      (t = true → Rep (point (env u.mem base) 0 1 2 3) (a + a)) ∧
      ∀ i : Slot, 16 ≤ i.val → env u.mem base i = env s.mem base i := by
  refine WP.mono (fieldCodeWide_ok hs _) fun u ⟨ku, vu⟩ => ?_
  obtain hr := dblPoint_rep ha
  refine ⟨ku, ?_, fun ht => ?_, fun i hi => by
    rw [vu]; exact point_ops_high _ (by cases t <;> decide) _ i hi⟩
  · rw [vu]
    cases t
    · obtain ⟨_, ex, ey, ez⟩ := dblOpsH_eval (env s.mem base)
      refine ⟨?_, ?_, ?_⟩
      · show toZ (evalOps _ _ 2) ≠ 0
        rw [ez]; exact hr.z
      · show toZ (evalOps _ _ 0) = _ * toZ (evalOps _ _ 2)
        rw [ex, ez]; exact hr.x
      · show toZ (evalOps _ _ 1) = _ * toZ (evalOps _ _ 2)
        rw [ey, ez]; exact hr.y
    · rw [(dblOpsH_eval _).1]; exact hr.proj
  · subst ht
    rw [vu, (dblOpsH_eval _).1]; exact hr

/-! ## Digits -/

theorem addImm_ok (s : State) (r : Reg) (n : Nat) (hn : n < 2 ^ 31) :
    WP isa (.block [.alu .add r (.imm (BitVec.ofNat 32 n))]) s fun t =>
      t.gpr r = off (s.gpr r) n ∧ Keeps [r] s t := by
  obtain he : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
    rw [BitVec.signExtend_eq_setWidth_of_msb_false (by
      rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat]; omega_arith)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_arith
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, he,
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun k hk => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    show k ≠ r by simpa only [List.mem_singleton] using hk, ite_false]

theorem digitByte_ok {s : State} {base : Addr} (hs : Scratch s base) (ptr add : Nat)
    (hptr : ptr + 8 ≤ 8192) (hadd : add < 2 ^ 31) {P : Addr} (hp : s.mem.readW (off base ptr) 64 = P)
    (i : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i)
    (hr : InRegions (s.rd ++ s.wr) (off (off P add) i) 1) :
    WP isa (.block (digitByte ptr add)) s fun t =>
      t.gpr .rbx = (s.mem (off (off P add) i)).setWidth 64 ∧ Keeps [.rsi, .rax, .rbx] s t := by
  rw [digitByte, show ([.mov .rsi (.mem (Impl.X25519.X86_64.sc ptr)),
      .alu .add .rsi (.imm (BitVec.ofNat 32 add)), .mov .rax (.mem (Impl.X25519.X86_64.sc 56)),
      .movzx8 .rbx { base := .rsi, index := some .rax }] : List Instr) =
    [.mov .rsi (.mem (Impl.X25519.X86_64.sc ptr))] ++ ([.alu .add .rsi (.imm (BitVec.ofNat 32 add))] ++
      ([.mov .rax (.mem (Impl.X25519.X86_64.sc 56))] ++
        [.movzx8 .rbx { base := .rsi, index := some .rax }])) from rfl, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .rsi ptr hptr) fun a ⟨ap, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addImm_ok a .rsi add hadd) fun b ⟨bp, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPointer_ok ((hs.of_keeps ka (by decide)).of_keeps kb (by decide)) .rax 56
    (by decide)) fun c ⟨cp, kc⟩ => ?_
  obtain hm : c.mem = s.mem := kc.2.1.trans (kb.2.1.trans ka.2.1)
  obtain hrd : c.rd ++ c.wr = s.rd ++ s.wr := by
    rw [kc.2.2.1, kc.2.2.2, kb.2.2.1, kb.2.2.2, ka.2.2.1, ka.2.2.2]
  obtain crsi : c.gpr .rsi = off P add := by rw [kc.1 _ (by decide), bp, ap, hp]
  obtain crax : c.gpr .rax = BitVec.ofNat 64 i := by rw [cp, kb.2.1, ka.2.1, hc]
  obtain hea : c.ea { base := .rsi, index := some .rax } = off (off P add) i := by
    simp only [State.ea, crsi, crax]
    rw [BitVec.mul_one, show BitVec.ofInt 64 (0 : Int) = BitVec.ofNat 64 0 from rfl, BitVec.add_zero]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hea, State.load8, hrd, hr, hm,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun r hr => ?_, hm, kc.2.2.1.trans (kb.2.2.1.trans ka.2.2.1),
    kc.2.2.2.trans (kb.2.2.2.trans ka.2.2.2)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [RegUpd.gpr_setReg_of_ne _ _ hr.2.2, kc.1 r (by simp [hr.2.1]), kb.1 r (by simp [hr.1]),
    ka.1 r (by simp [hr.1])]

/-! ## Adding a table entry -/

/-- A point's `X : Y : Z`. -/
def xyz (p : Spec.Ed25519.Point) : Spec.X25519.Fe × Spec.X25519.Fe × Spec.X25519.Fe := (p.X, p.Y, p.Z)

theorem RepP.of_xyz {p q : Spec.Ed25519.Point} {a : EPoint dZ} (h : RepP q a) (e : xyz p = xyz q) :
    RepP p a := by
  simp only [xyz, Prod.mk.injEq] at e
  obtain ⟨ex, ey, ez⟩ := e
  exact ⟨by rw [ez]; exact h.z, by rw [ex, ez]; exact h.x, by rw [ey, ez]; exact h.y⟩

/-- `add` adds `q`, `f q` in slots 4–7, to the point in slots 0–3: its `X : Y : Z` always, its `T`
too if `t`. -/
def AddSpecT (add : Prog isa) (f : Spec.Ed25519.Point → Spec.Ed25519.Point) (t : Bool) : Prop :=
  ∀ (s : State) (base : Addr) (q : Spec.Ed25519.Point), Scratch s base →
    env s.mem base 16 = Spec.Ed25519.d → point (env s.mem base) 4 5 6 7 = f q →
    WP isa add s fun u => Keep base s u ∧
      xyz (point (env u.mem base) 0 1 2 3) = xyz (Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q) ∧
      (t = true → point (env u.mem base) 0 1 2 3 = Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q) ∧
      ∀ i : Slot, 16 ≤ i.val → env u.mem base i = env s.mem base i

theorem addCachedOps_xyz (t : Bool) (e : Env) :
    xyz (point (evalOps (addCachedOps t) e) 0 1 2 3) = xyz (point (evalOps pointAddCachedOps e) 0 1 2 3) := by
  cases t <;> rfl

theorem addCachedOps_true : addCachedOps true = pointAddCachedOps := rfl

theorem addCachedT_spec (t : Bool) : AddSpecT (pt.add t) cache t :=
  fun s _ q hs _ hq => WP.mono (PtOk.add hs t) fun _ ⟨hk, hv⟩ => by
    rw [hv]
    refine ⟨hk, by rw [addCachedOps_xyz, pointAddCached_eval _ q hq], fun ht => ?_,
      point_ops_high _ (by cases t <;> decide) _⟩
    subst ht
    rw [addCachedOps_true]; exact pointAddCached_eval _ q hq

/-- An addition, without `T`, of a cached point whose `Z` is 1 (`2Z = 2`), as the static's
entries are. -/
def AddAffSpec (add : Prog isa) : Prop :=
  ∀ (s : State) (base : Addr) (q : Spec.Ed25519.Point), Scratch s base →
    env s.mem base 16 = Spec.Ed25519.d → q.Z * 2 = 2 → point (env s.mem base) 4 5 6 7 = cache q →
    WP isa add s fun u => Keep base s u ∧
      xyz (point (env u.mem base) 0 1 2 3) = xyz (Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q) ∧
      ∀ i : Slot, 16 ≤ i.val → env u.mem base i = env s.mem base i

theorem addCached_aff : AddAffSpec (pt.add false) :=
  fun s base q hs hd _ hq => WP.mono (addCachedT_spec false s base q hs hd hq) fun _ ⟨k, x, _, h⟩ => ⟨k, x, h⟩

/-- The operations before and after the product `addAffOps` replaces. -/
private def affPre : List FieldOp := [.sub 8 1 0, .mul 8 8 4, .add 9 1 0, .mul 9 9 5, .mul 10 3 6]

private def affPost : List FieldOp :=
  [.sub 12 9 8, .sub 13 11 10, .add 14 11 10, .add 15 9 8, .mul 0 12 13, .mul 1 14 15, .mul 2 13 14]

private theorem addAffOps_split : addAffOps = affPre ++ .add 11 2 2 :: affPost := rfl

private theorem addCachedOps_split : addCachedOps false = affPre ++ .mul 11 2 7 :: affPost := rfl

/-- With `2Z = 2` in slot 7, `addAffOps` is `addCachedOps false`. -/
theorem addAffOps_eq (e : Env) (h7 : e 7 = 2) : evalOps addAffOps e = evalOps (addCachedOps false) e := by
  obtain h : ∀ e' : Env, e' 7 = 2 → evalOp (.add 11 2 2) e' = evalOp (.mul 11 2 7) e' := by
    -- `-lia`: Lean 4.36's `grind` builds a proof the kernel rejects from `lia`
    -- over `Fin` of a non-literal modulus (lean4#15857, fixed in 4.37).
    intro e' h; simp only [evalOp, h]; exact congrArg _ (by grind -lia)
  rw [addAffOps_split, addCachedOps_split]
  simp only [evalOps, List.foldl_append, List.foldl_cons]
  rw [h]
  exact h7

theorem addAff_aff : AddAffSpec (addAffIn fld) := by
  intro s base q hs _ hz hq
  refine WP.mono (fieldCodeWide_ok hs addAffOps) fun u ⟨ku, vu⟩ => ?_
  obtain h7 : env s.mem base 7 = 2 := (congrArg Spec.Ed25519.Point.T hq).trans hz
  rw [vu, addAffOps_eq _ h7]
  exact ⟨ku, by rw [addCachedOps_xyz, pointAddCached_eval _ q hq], point_ops_high _ (by decide) _⟩


theorem tableEntryAdd_ok {add : Prog isa} {f : Spec.Ed25519.Point → Spec.Ed25519.Point} {tb : Bool}
    (hadd : AddSpecT add f tb) {s : State} {base : Addr} (hs : Scratch s base) {o j : Nat}
    (hlo : 768 ≤ o) (hhi : o + 128 * j + 128 ≤ 8192) (hj : j < 64)
    (hc : s.gpr .rbx = BitVec.ofNat 64 j) (q : Spec.Ed25519.Point)
    (hq : tablePoint s.mem base (o + 128 * j) = f q) (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.seq (.block (tableAddr o ++ pointFromTableQ)) add) s fun t => Keep base s t ∧
      xyz (point (env t.mem base) 0 1 2 3) = xyz (Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q) ∧
      (tb = true → point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q) ∧
      env t.mem base 16 = env s.mem base 16 := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok hs.rdi o j hj hc) fun a ⟨pa, ka⟩ => ?_
  obtain kae : Keep base s a := Keep.of_keeps ka (by decide)
  refine WP.mono (pointFromTableQ_ok (hs.of_keep kae) pa (by omega_arith) (by omega_arith)) fun b ⟨pb, kb⟩ => ?_
  obtain kbe := Keep.of_tableQ kb
  obtain b_low : ∀ i : Slot, i.val < 4 → env b.mem base i = env s.mem base i := by
    intro i hi
    change Proof.X25519.X86_64.F b.mem base (offset i) = Proof.X25519.X86_64.F s.mem base (offset i)
    rw [Outside_F kb.mem (by simp only [offset]; omega_arith) (Or.inl (by simp only [offset]; omega_arith)), ka.2.1]
  obtain b_high : ∀ i : Slot, 8 ≤ i.val → env b.mem base i = env s.mem base i := by
    intro i hi
    change Proof.X25519.X86_64.F b.mem base (offset i) = Proof.X25519.X86_64.F s.mem base (offset i)
    rw [Outside_F kb.mem (by simp only [offset]; omega_arith) (Or.inr (by simp only [offset]; omega_arith)), ka.2.1]
  obtain bp : point (env b.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, b_low 0 (by decide), b_low 1 (by decide), b_low 2 (by decide), b_low 3 (by decide)]
  obtain bq : point (env b.mem base) 4 5 6 7 = f q := by rw [pb, ka.2.1, hq]
  refine WP.mono (hadd b base q (hs.of_keep (kae.trans kbe)) (by rw [b_high 16 (by decide)]; exact hd) bq)
    fun t ⟨kt, tx, tp, th⟩ => ?_
  exact ⟨(kae.trans kbe).trans kt, by rw [tx, bp], fun hb => by rw [tp hb, bp],
    by rw [th 16 (by decide), b_high 16 (by decide)]⟩

/-- Entries `e < 16` of the table at byte `o` are `f` of representatives of `[dec (e + 1)]X`. -/
def TableOf (f : Spec.Ed25519.Point → Spec.Ed25519.Point) (m : Mem) (base : Addr) (o : Nat)
    (X : EPoint dZ) : Prop :=
  ∀ e < 16, ∃ q, tablePoint m base (o + 128 * e) = f q ∧ Rep q ((Recode.dec (e + 1)) • X)

/-- The digit `v`'s entry `v - 1` of the table at byte `o` added to the point, unless `v` is zero;
an addition computes `T` if `tb`, and a zero digit leaves it as it was. -/
theorem addDigit_ok {add : Prog isa} {f : Spec.Ed25519.Point → Spec.Ed25519.Point} {tb : Bool}
    (hadd : AddSpecT add f tb) {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hlo : 768 ≤ o) (hhi : o + 2048 ≤ 8192) {X a : EPoint dZ} (htab : TableOf f s.mem base o X)
    (v : Nat) (hv : v ≤ 16) (hc : s.gpr .rbx = BitVec.ofNat 64 v) (hz : s.zf = some (decide (v = 0)))
    (hd : env s.mem base 16 = Spec.Ed25519.d) (hp : RepP (point (env s.mem base) 0 1 2 3) a)
    (ha : v ≠ 0 → Rep (point (env s.mem base) 0 1 2 3) a) :
    WP isa (addDigit o add) s fun t =>
      RepP (point (env t.mem base) 0 1 2 3) (a + (Recode.dec v) • X) ∧
      (tb = true ∧ v ≠ 0 ∨ v = 0 ∧ Rep (point (env s.mem base) 0 1 2 3) a →
        Rep (point (env t.mem base) 0 1 2 3) (a + (Recode.dec v) • X)) ∧
      env t.mem base 16 = env s.mem base 16 ∧ WinKeep base s t := by
  rw [addDigit]
  refine WP.ite (!decide (v = 0)) (by simp only [eval, hz, Option.map_some]) (fun h => ?_) (fun h => ?_)
  · have hv0 : v ≠ 0 := by simpa using h
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv0
    refine WP.seq (WP.mono (accumulateDec_ok s n hc) fun b ⟨bc, kb⟩ => ?_)
    obtain ⟨q, hq, hr⟩ := htab n (by omega_arith)
    refine WP.mono (tableEntryAdd_ok hadd (hs.of_keeps kb (by decide)) hlo (by omega_arith) (by omega_arith) bc q
      (by rw [kb.2.1]; exact hq) (by rw [kb.2.1]; exact hd)) fun t ⟨kt, tx, tp, td⟩ => ?_
    obtain hrep : Rep (Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q)
        (a + (Recode.dec (n + 1)) • X) := pointAdd_rep (ha hv0) hr
    rw [kb.2.1] at tx tp
    exact ⟨RepP.of_xyz hrep.proj tx, fun h' => by
        rcases h' with ⟨ht, _⟩ | ⟨h0, _⟩
        · rw [tp ht]; exact hrep
        · exact absurd h0 hv0,
      by rw [td, kb.2.1], (WinKeep.of_keeps kb (by decide)).trans (WinKeep.of_keep kt)⟩
  · have hv0 : v = 0 := by simpa using h
    subst hv0
    obtain e : a + (Recode.dec 0) • X = a := by simp [Recode.dec]
    refine WP.block_nil ⟨by rw [e]; exact hp, fun h' => ?_, rfl, WinKeep.refl _ _⟩
    rw [e]
    rcases h' with ⟨_, h0⟩ | ⟨_, hr⟩
    · exact absurd rfl h0
    · exact hr

/-! ## Windows -/

/-- What verification's windows keep: the tables, the inputs and where they are. -/
structure WinCtx (base kp sp T : Addr) (A : EPoint dZ) (s : State) : Prop where
  scratch : Scratch s base
  kHeader : s.mem.readW (off base 7952) 64 = kp
  sHeader : s.mem.readW (off base 7944) 64 = sp
  kRead : ∀ i < 64, InRegions (s.rd ++ s.wr) (off kp i) 1
  sRead : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sp 32) i) 1
  kFar : ∀ i < 64, 8192 ≤ ofs base (off kp i)
  sFar : ∀ i < 32, 8192 ≤ ofs base (off (off sp 32) i)
  kRead8 : ∀ j < 8, InRegions (s.rd ++ s.wr) (off kp (8 * j)) 8
  sRead8 : ∀ j < 4, InRegions (s.rd ++ s.wr) (off sp (32 + 8 * j)) 8
  aTab : TableOf cache s.mem base 5376 A
  bHeader : s.mem.readW (off base 7960) 64 = T
  bTab : BaseTbl s base T

theorem win_tablePoint {base : Addr} {m m' : Mem} (h : Outside base 56 1832 m m') {d : Nat}
    (hd : 1888 ≤ d) (hb : d + 128 ≤ 8192) : tablePoint m' base d = tablePoint m base d := by
  simp only [tablePoint]
  rw [Outside_F h (by omega_arith) (Or.inr (by omega_arith)), Outside_F h (by omega_arith) (Or.inr (by omega_arith)),
    Outside_F h (by omega_arith) (Or.inr (by omega_arith)), Outside_F h (by omega_arith) (Or.inr (by omega_arith))]

theorem TableOf.of_win {f : Spec.Ed25519.Point → Spec.Ed25519.Point} {base : Addr} {m m' : Mem}
    {o : Nat} {X : EPoint dZ} (h : TableOf f m base o X) (k : Outside base 56 1832 m m')
    (ho : 1888 ≤ o) (hb : o + 2048 ≤ 8192) : TableOf f m' base o X := by
  intro j hj
  obtain ⟨q, hq, hr⟩ := h j hj
  exact ⟨q, by rw [win_tablePoint k (by omega_arith) (by omega_arith)]; exact hq, hr⟩

theorem Outside.widen {base : Addr} {m m' : Mem} (h : Outside base 64 1824 m m') :
    Outside base 56 1832 m m' := h.mono (by decide) (by decide)

theorem WinKeep.header {base : Addr} {s t : State} (h : WinKeep base s t) {d : Nat} (hd : 1888 ≤ d)
    (hb : d + 8 ≤ 8192) : t.mem.readW (off base d) 64 = s.mem.readW (off base d) 64 :=
  h.mem.word (Or.inr (by omega_arith)) (by omega_arith)

theorem WinCtx.of_keep {base kp sp T : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp T A s)
    (k : WinKeep base s t) : WinCtx base kp sp T A t := by
  refine ⟨k.scratch h.scratch, (k.header (by decide) (by decide)).trans h.kHeader,
    (k.header (by decide) (by decide)).trans h.sHeader, ?_, ?_, h.kFar, h.sFar, ?_, ?_,
    h.aTab.of_win (Outside.widen k.mem) (by decide) (by decide),
    (k.header (by decide) (by decide)).trans h.bHeader, h.bTab.of_outside k.rd k.wr k.mem (by decide)⟩
  · intro i hi; rw [k.rd, k.wr]; exact h.kRead i hi
  · intro i hi; rw [k.rd, k.wr]; exact h.sRead i hi
  · intro i hi; rw [k.rd, k.wr]; exact h.kRead8 i hi
  · intro i hi; rw [k.rd, k.wr]; exact h.sRead8 i hi

theorem off_zero (p : Addr) : off p 0 = p := by
  simp only [off, BitVec.add_zero]

/-- Entry `j` of the static, `cache q`, added to the accumulator, with `T` if `tb`. -/
theorem staticEntryAdd_ok {add : Prog isa} (hadd : AddAffSpec add) {s : State} {base T : Addr} (hs : Scratch s base)
    (ht : BaseTbl s base T) (hT : s.mem.readW (off base 7960) 64 = T) {j : Nat} (hj : j < 128)
    (hc : s.gpr .rbx = BitVec.ofNat 64 j) (q : Spec.Ed25519.Point)
    (hq : tablePoint s.mem (off T (128 * j)) 0 = cache q) (hz : q.Z * 2 = 2)
    (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.seq (.block (baseAddr ++ pointFromTableQ)) add) s fun t => Keep base s t ∧
      xyz (point (env t.mem base) 0 1 2 3) = xyz (Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q) ∧
      env t.mem base 16 = env s.mem base 16 := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (baseAddr_ok hs hT j hj hc) fun a ⟨pa, ka⟩ => ?_
  obtain kae : Keep base s a := Keep.of_keeps ka (by decide)
  refine WP.mono (pointFromStaticQ_ok (hs.of_keep kae) pa (fun d hd => by
      rw [ka.2.2.1, ka.2.2.2]
      have := ht.read (128 * j + d) 8 (by omega_arith)
      simp only [off, Offset.add_add] at this ⊢
      exact this) (fun i hi => by
      have := ht.far (128 * j + i) (by omega_arith)
      simp only [off, Offset.add_add] at this ⊢
      exact this)) fun b ⟨pb, kb⟩ => ?_
  obtain kbe := Keep.of_tableQ kb
  obtain b_low : ∀ i : Slot, i.val < 4 → env b.mem base i = env s.mem base i := by
    intro i hi
    change Proof.X25519.X86_64.F b.mem base (offset i) = Proof.X25519.X86_64.F s.mem base (offset i)
    rw [Outside_F kb.mem (by simp only [offset]; omega_arith) (Or.inl (by simp only [offset]; omega_arith)), ka.2.1]
  obtain b_high : ∀ i : Slot, 8 ≤ i.val → env b.mem base i = env s.mem base i := by
    intro i hi
    change Proof.X25519.X86_64.F b.mem base (offset i) = Proof.X25519.X86_64.F s.mem base (offset i)
    rw [Outside_F kb.mem (by simp only [offset]; omega_arith) (Or.inr (by simp only [offset]; omega_arith)), ka.2.1]
  obtain bp : point (env b.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, b_low 0 (by decide), b_low 1 (by decide), b_low 2 (by decide), b_low 3 (by decide)]
  obtain bq : point (env b.mem base) 4 5 6 7 = cache q := by rw [pb, ka.2.1, hq]
  refine WP.mono (hadd b base q (hs.of_keep (kae.trans kbe))
    (by rw [b_high 16 (by decide)]; exact hd) hz bq) fun t ⟨kt, tx, th⟩ => ?_
  exact ⟨(kae.trans kbe).trans kt, by rw [tx, bp], by rw [th 16 (by decide), b_high 16 (by decide)]⟩

/-- `[dec v](-B)`, entry `v - 1` of the static, added to the accumulator, for the digit's byte
`v` in `rbx`, unless `v` is zero. -/
theorem addBase_ok {add : Prog isa} (hadd : AddAffSpec add) {s : State} {base : Addr} (hs : Scratch s base)
    {T : Addr} (hT : s.mem.readW (off base 7960) 64 = T) (ht : BaseTbl s base T) {a : EPoint dZ}
    (v : Nat) (hv : v ≤ 128) (hc : s.gpr .rbx = BitVec.ofNat 64 v) (hz : s.zf = some (decide (v = 0)))
    (hd : env s.mem base 16 = Spec.Ed25519.d) (hp : RepP (point (env s.mem base) 0 1 2 3) a)
    (ha : v ≠ 0 → Rep (point (env s.mem base) 0 1 2 3) a) :
    WP isa (addBase add) s fun t =>
      RepP (point (env t.mem base) 0 1 2 3) (a + (Recode.dec v) • (-baseAff)) ∧
      env t.mem base 16 = env s.mem base 16 ∧ WinKeep base s t := by
  rw [addBase]
  refine WP.ite (!decide (v = 0)) (by simp only [eval, hz, Option.map_some]) (fun h => ?_) (fun h => ?_)
  · have hv0 : v ≠ 0 := by simpa using h
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv0
    refine WP.seq (WP.mono (accumulateDec_ok s n hc) fun b ⟨bc, kb⟩ => ?_)
    obtain ⟨q, hq, hr⟩ := baseOddCached_ok n (by omega_arith)
    obtain htb : BaseTbl b base T := ht.of_mem kb.2.2.1 kb.2.2.2 fun p _ => by rw [kb.2.1]
    refine WP.mono (staticEntryAdd_ok hadd (hs.of_keeps kb (by decide)) htb (by rw [kb.2.1]; exact hT) (by omega_arith) bc q
      (by rw [kb.2.1, ht.entry n (by omega_arith), hq]) ((congrArg Spec.Ed25519.Point.T hq).symm.trans (one_mul _))
      (by rw [kb.2.1]; exact hd)) fun t ⟨kt, tx, td⟩ => ?_
    obtain hrep : Rep (Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q)
        (a + (Recode.dec (n + 1)) • (-baseAff)) := pointAdd_rep (ha hv0) hr
    rw [kb.2.1] at tx
    exact ⟨RepP.of_xyz hrep.proj tx, by rw [td, kb.2.1],
      (WinKeep.of_keeps kb (by decide)).trans (WinKeep.of_keep kt)⟩
  · have hv0 : v = 0 := by simpa using h
    subst hv0
    obtain e : a + (Recode.dec 0) • (-baseAff) = a := by simp [Recode.dec]
    exact WP.block_nil ⟨by rw [e]; exact hp, rfl, WinKeep.refl _ _⟩

end VG.Proof.Ed25519.X86_64
