module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.CachedJac
public import VerifiedGarbage.Proof.Weierstrass.JacAdd
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Weierstrass.PointContract

/-!
# The cached Jacobian addition in place

`CachedJac.head n S p q dst ++ jacTail S p q p` adds `q` (with its `Z²` at
`dst` and `Z³` at `dst + 8 n`) to `p` in place: the head reads `p`, and the
tail never reads `p`'s `X` or `Y` again, and reads its `Z` before writing it.
On numbered slots (`ipσ`: the temporaries `0 … 5`, `p` at `6 … 8`, then what
it only reads) it computes `jacAddF` (`ip_values`), and so on any slots
apart as `ipσ` numbers them (`ip_run`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.CachedJac
open VG VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Proof.Weierstrass

/-- The slots the addition in place writes: the temporaries and `p`. -/
def ipW (S : RcbSlots) (p : Pt) : List Nat := [S.t0, S.t1, S.t2, S.t3, S.t4, S.t5, p.x, p.y, p.z]

/-- The slots it only reads. -/
def ipR (n : Nat) (S : RcbSlots) (q : Pt) (dst : Nat) : List Nat := [S.a, S.b3, q.x, q.y, q.z, dst, dst + 8 * n]

/-- Slot `i` of the numbered program. -/
def ipσ (n : Nat) (S : RcbSlots) (p q : Pt) (dst i : Nat) : Nat := (ipW S p ++ ipR n S q dst).getD i S.a

/-- The head on numbered slots. -/
def headIPN : List FOp :=
  [.mul 0 8 8, .mul 2 6 14, .mul 3 11 0, .mul 4 7 15, .mul 5 12 8, .mul 5 5 0, .sub 3 3 2, .sub 5 5 4]

/-- The tail in place on numbered slots. -/
def tailIPN : List FOp := jacTail ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨6, 7, 8⟩ ⟨11, 12, 13⟩ ⟨6, 7, 8⟩

theorem ip_eq (n : Nat) (S : RcbSlots) (p q : Pt) (dst : Nat) :
    Impl.Weierstrass.X86_64.CachedJac.head n S p q dst ++ jacTail S p q p =
      (headIPN ++ tailIPN).map (FOp.rename (ipσ n S p q dst)) := rfl

theorem ipN_out : ∀ op ∈ headIPN ++ tailIPN, op.out < 9 := by decide

theorem ip_values {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F)
    (h2 : E 14 = E 13 * E 13) (h3 : E 15 = E 14 * E 13) :
    (runOps (headIPN ++ tailIPN) E 6, runOps (headIPN ++ tailIPN) E 7, runOps (headIPN ++ tailIPN) E 8) =
      jacAddF (E 6) (E 7) (E 8) (E 11) (E 12) (E 13) := by
  simp only [headIPN, tailIPN, jacTail, List.cons_append, List.nil_append,
    runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply]
  simp only [ite_true, h3, h2, jacAddF, Prod.mk.injEq]
  constructor
  · grind
  constructor <;> grind

/-- What `ip_run` needs of the slots: what is written has no duplicates, and
nothing only read (nor `S.a`, the default) is written. -/
structure IPApart (n : Nat) (S : RcbSlots) (p q : Pt) (dst : Nat) : Prop where
  nodup : (ipW S p).Nodup
  apart : ∀ x ∈ ipR n S q dst, x ∉ ipW S p

theorem ip_inj {n : Nat} {S : RcbSlots} {p q : Pt} {dst : Nat} (h : IPApart n S p q dst) {w : Nat}
    (hw : w < 9) (y : Nat) (hy : ipσ n S p q dst y = ipσ n S p q dst w) : y = w :=
  getD_append_inj h.nodup h.apart (h.apart _ (List.mem_cons_self ..)) hw y hy

/-- The addition in place computes `jacAddF`. -/
theorem ip_run {F : Type _} [Lean.Grind.CommRing F] {n : Nat} {S : RcbSlots} {p q : Pt} {dst : Nat}
    (hA : IPApart n S p q dst) (E : Nat → F) (h2 : E dst = E q.z * E q.z)
    (h3 : E (dst + 8 * n) = E dst * E q.z) :
    let ops := Impl.Weierstrass.X86_64.CachedJac.head n S p q dst ++ jacTail S p q p
    (runOps ops E p.x, runOps ops E p.y, runOps ops E p.z) =
      jacAddF (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) (E q.z) := by
  dsimp only
  rw [ip_eq]
  have he := runOps_rename (ipσ n S p q dst) (headIPN ++ tailIPN) E
    (fun op hop => ip_inj hA (ipN_out op hop))
  exact (congrArg₂ Prod.mk (congrFun he 6) (congrArg₂ Prod.mk (congrFun he 7) (congrFun he 8))).trans
    (ip_values (fun i => E (ipσ n S p q dst i)) h2 h3)

theorem ipσ_mem (n : Nat) (S : RcbSlots) (p q : Pt) (dst i : Nat) :
    ipσ n S p q dst i ∈ ipW S p ++ ipR n S q dst :=
  getD_append_mem (List.mem_cons_self ..) i

theorem ipσ_out (n : Nat) (S : RcbSlots) (p q : Pt) (dst : Nat) {i : Nat} (hi : i < 9) :
    ipσ n S p q dst i ∈ ipW S p := by
  rw [ipσ, getD_append_left (by simp [ipW]; omega)]
  exact List.getElem_mem _

end VG.Proof.Weierstrass.X86_64.CachedJac
