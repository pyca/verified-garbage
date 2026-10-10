import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Fn
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit

/-!
# The point operations a caller runs

Untrusted: everything here is checked by Lean. The proofs of the code that
doubles and adds points (verification's table and windows) hold for any
point operations `pt` that change what the field programs `dblOps` and
`addCachedOps` inlined would (`PtOk`): `Keep` and the slots' values. The
functions' bodies, which calls of them run as (`Code.inline`), are such
operations (`bodies_ok`, from `fn_ok`).
-/

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

/-- The functions' bodies keep `rbp` and `r12`–`r15`. -/
theorem doubleFn_keeps (t : Bool) : ∀ r ∈ keptRegs, KeepReg.keeps r (doubleFn fld t) = true := by
  intro r hr
  simp only [keptRegs, kept, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases EdArith.known (fld := fld) with rfl | rfl <;> cases t <;>
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> lit_decide

theorem addFn_keeps (t : Bool) : ∀ r ∈ keptRegs, KeepReg.keeps r (addFn fld t) = true := by
  intro r hr
  simp only [keptRegs, kept, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases EdArith.known (fld := fld) with rfl | rfl <;> cases t <;>
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> lit_decide

theorem addAffineFn_keeps : ∀ r ∈ keptRegs, KeepReg.keeps r (addAffineFn fld) = true := by
  intro r hr
  simp only [keptRegs, kept, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases EdArith.known (fld := fld) with rfl | rfl <;>
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> lit_decide

/-- A body's `Keep`, from `fn_ok`: its results are in slots 0–15. -/
theorem fn_keep {s : State} {base : Addr} (hs : Scratch s base) (ops : List FieldOp)
    (hk : ∀ r ∈ keptRegs, KeepReg.keeps r (fn fld ops) = true)
    (hout : ∀ op ∈ ops, 64 ≤ offset op.out ∧ offset op.out + 32 ≤ 768) :
    WP isa (fn fld ops) s fun u => Keep base s u ∧ env u.mem base = evalOps ops (env s.mem base) :=
  WP.mono (fn_ok hs ops hk) fun _ ⟨hg, hrd, hwr, hv, hm⟩ =>
    ⟨⟨fun r hr => hg r (.inl hr), hrd, hwr, fun x hx => hm x fun op hop => by
      have := hout op hop; omega⟩, hv⟩

end Point64

instance {fld : Arith} [EdArith fld] : PtOk (Point64.bodies fld) where
  dbl hs t := Point64.fn_keep hs (dblOps t) (Point64.doubleFn_keeps t) (by cases t <;> decide)
  add hs t := Point64.fn_keep hs (addCachedOps t) (Point64.addFn_keeps t) (by cases t <;> decide)

end VG.Proof.Ed25519.X86_64
