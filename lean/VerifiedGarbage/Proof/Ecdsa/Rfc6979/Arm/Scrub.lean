module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubTab
import VerifiedGarbage.Proof.Framework.Arm.CallF
public meta import Lean
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: what every curve's signing on 32-bit ARM needs to be scrubbed, not one curve's proof

/-!
# Deterministic ECDSA on 32-bit ARM, without secret residue

The postcondition of `vg_ecdsa_<curve>_sign` reads the memory on return only
within `out` (`Arm.Scrub.PostOut`), as on RISC-V
(`Proof/Ecdsa/Rfc6979/RISCV64/Scrub.lean`): each implementation, generic over
the HMAC implementations its table holds, which it calls indirectly, is
emitted followed by a wipe of the stack its contract reserves and
instructions that set the registers a callee may change, but the result, and
the flags to constants (`Impl.Ecdsa.Arm.Fn`), and proven so by
`Arm.Scrub.verifiedScrubbedAll` (`Proof.Ecdsa.Arm.Fn`).

What that cleanup needs of the code (`Arm.Scrub.scrubSideF`: its frames
within the 544 bytes the contract reserves, and indirect calls only of
functions of its table) is proven once, for any curve's configuration
(`sign_okT`): from the code's own shape (`CodeOkT`,
`Proof/Rsa/Arm/ScrubTab.lean`), from what the curve's core states of its own
code (`CodeOk`, by `lit_decide` where the curve is proven), and from what each
HMAC implementation of the table states of its own (`HVar.scrub`): no HMAC
function's code is evaluated. `CodeOkT.icallsK` (`Proof/HmacTable/Arm.lean`) is `CodeOkT.icalls` for
called functions whose frames use some stack (HMAC's `finalize` pushes 8
bytes, its `init` for a key of any length 16), and `sign_okT_tac` walks the code as `code_okT` does, splitting the
choices the configuration makes (`Cfg.prepH`) and taking the core's code
from a hypothesis.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm.Scrub

open VG.Arm VG.Arm.Scrub
open VG.Proof.HmacTable.Arm (HVar tables)

/-- The `n` bytes at `q` read the memory only within a region at `q` of at
least `n` bytes. -/
theorem bytesAt_of {m₁ m₂ : Mem} {q : Addr} {N n : Nat} (hn : n ≤ N)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    Spec.Sha3.bytesAt m₂ q n = Spec.Sha3.bytesAt m₁ q n := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => (h _ ?_).symm
  have hi := List.mem_range.mp hi
  simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  omega_using [hn, hi]

/-- The postcondition reads the memory on return only within `out`. -/
theorem signOut (T : Spec.Ecdsa.Rfc6979.TableInstance) (cs : List (String × List (BitVec 64)))
    (vs : List HVar) :
    PostOut (specK T cs vs) (T.signSig.retBits 32) :=
  postOut_of_local ((ScrubAbi.consts cs).tables _ _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [out, d, dg, dl, sc, hm], _ =>
      simp only [Spec.Ecdsa.Rfc6979.TableInstance.signSig, Sig.bufs, List.mem_cons,
        forall_eq_or_imp, Elem.size, Nat.mul_one] at hb
      have e := bytesAt_of (n := 2 * T.ecdsa.curve.len) (Nat.le_refl _) hb.1
      intro H F h1 h2
      have h' := h H F h1 h2
      revert h'
      split
      · exact fun h' => ⟨h'.1, e.trans h'.2⟩
      · exact fun h' => ⟨h'.1, e.trans h'.2⟩

open VG.Proof.Rsa.Arm.Scrub (CodeOkT CodeOkT.block CodeOkT.seq CodeOkT.ite CodeOkT.loop CodeOkT.call
  CodeOkT.alloc CodeOkT.push CodeOkT.ofOk scrubSideF_ofT)
open VG.Impl.Ecdsa.Rfc6979.Arm (Cfg Fns)
open VG.Proof.HmacTable.Arm (CodeOkT.icallsK fnsOf_init fnsOf_upd fnsOf_fin)

open Lean Meta in
/-- `codeHead` (`Proof/Rsa/Arm/ScrubTab.lean`), stopping also at a choice
(`ite`), which `signOkTStep` splits. -/
meta partial def signCodeHead (c : Expr) : MetaM Expr := do
  let c := (← instantiateMVars c).headBeta
  let f := c.getAppFn
  if f.isFVar || c.isAppOf ``Code.icalls || c.isAppOf ``ite then return c
  if let some n := f.constName? then
    if n == ``Code.block || n == ``Code.seq || n == ``Code.ite || n == ``Code.loop ||
        n == ``Code.call || n == ``Code.frame || n == ``Code.icall then return c
  match ← unfoldDefinition? c with
  | some c' => signCodeHead c'
  | none =>
    let c' ← whnfCore c
    if c' == c then return c else signCodeHead c'

open Lean Meta Elab Tactic in
/-- One step of `sign_okT_tac` on the goal `g`: `code_okT`'s, but an indirect
call by `CodeOkT.icallsK` of functions that use at most 16 bytes of stack, a
choice of the configuration (`ite`) split, and
code that is no constructor (the core, `Cfg.coreC`) by a hypothesis that it
uses at most 16 bytes (`CodeOk`). -/
meta def signOkTStep (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let some (c, n, T) := (do
      guard (tgt.isAppOfArity ``CodeOkT 3)
      pure (tgt.getArg! 0, tgt.getArg! 1, tgt.getArg! 2)) | return [g]
  let run (g : MVarId) (stx : TacticM Syntax) : TacticM (List MVarId) := do
    setGoals [g]; evalTactic (← stx); getGoals
  let c ← signCodeHead c
  let g ← g.replaceTargetDefEq (mkApp3 (mkConst ``CodeOkT) c n T)
  if c.isAppOf ``ite then return ← run g `(tactic| split)
  if c.isAppOf ``Code.icalls then
    return ← run g `(tactic| exact CodeOkT.icallsK (k := 16) (by decide) ‹_›)
  match c.getAppFn.constName? with
  | some ``Code.block => run g `(tactic| exact CodeOkT.block)
  | some ``Code.seq => run g `(tactic| apply CodeOkT.seq)
  | some ``Code.ite => run g `(tactic| apply CodeOkT.ite)
  | some ``Code.loop => run g `(tactic| apply CodeOkT.loop)
  | some ``Code.call => run g `(tactic| apply CodeOkT.call)
  | some ``Code.frame =>
    let i ← whnfD (c.getArg! 2)
    if i.isAppOf ``VG.Arm.Instr.push then run g `(tactic| apply CodeOkT.push (by decide))
    else if i.isAppOf ``VG.Arm.Instr.alloc then run g `(tactic| apply CodeOkT.alloc (by decide))
    else throwError "sign_okT_tac: a frame of {i}"
  | _ => run g `(tactic| exact CodeOkT.ofOk (CodeOk.mono (n := 16) ‹_› (by decide)))

/-- Walk signing's code by the rules of `CodeOkT` (`signOkTStep`). -/
elab "sign_okT_tac" : tactic => do
  let mut todo ← Lean.Elab.Tactic.getGoals
  let mut rest := []
  while !todo.isEmpty do
    let g := todo.head!
    todo := todo.tail!
    let gs ← signOkTStep g
    if gs == [g] then rest := rest ++ [g] else todo := gs ++ todo
  Lean.Elab.Tactic.setGoals rest

/-- What the cleanup needs of signing's code, for any curve's configuration
`c`: its frames use at most the 544 bytes its contract reserves, and it calls
indirectly only functions named in `T`, given that of the functions of the
table (`hi`, `hu`, `hf`) and of the core's code (`hc`). -/
theorem sign_okT (c : Cfg) {T : List String}
    (hi : ∀ p ∈ c.f.init, CodeOk p.2 16 ∧ p.1 ∈ T) (hu : ∀ p ∈ c.f.upd, CodeOk p.2 16 ∧ p.1 ∈ T)
    (hf : ∀ p ∈ c.f.fin, CodeOk p.2 16 ∧ p.1 ∈ T) (hc : CodeOk c.coreC 16) : CodeOkT c.sign 544 T := by
  sign_okT_tac

/-- `scrubSideF` of signing's code, for any curve's configuration with the
functions of `tables vs`, from what its core states of its own code. -/
theorem sign_side {c : Cfg} {vs : List HVar} (hfs : c.f = HmacTable.Arm.fnsOf vs) (hc : CodeOk c.coreC 16) :
    scrubSideF c.sign 544 [("hmac", tables vs)] = true :=
  scrubSideF_ofT (sign_okT c (hfs ▸ fnsOf_init vs) (hfs ▸ fnsOf_upd vs) (hfs ▸ fnsOf_fin vs) hc) (by decide)

/-- `sign_side` of code `c` that is signing's code for `cfg`. -/
theorem sign_side_of {c : Prog isa} {cfg : Cfg} {vs : List HVar} (e : c = cfg.sign)
    (hfs : cfg.f = HmacTable.Arm.fnsOf vs) (hc : CodeOk cfg.coreC 16) :
    scrubSideF c 544 [("hmac", tables vs)] = true :=
  e ▸ sign_side hfs hc

end VG.Proof.Ecdsa.Rfc6979.Arm.Scrub
