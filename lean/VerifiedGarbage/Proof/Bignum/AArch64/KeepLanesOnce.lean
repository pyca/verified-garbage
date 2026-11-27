module

public import VerifiedGarbage.Proof.Bignum.AArch64.KeepLanesSame

/-!
# `KeepLanes.keeps`, matching on each instruction once

`keepsS` asks of every instruction whether it changes the facts
(`unchanged`): whether it is an `ins` or a `umov` (`insView`, `umovView`, a
match on the instruction each), and whether it keeps each location of the
facts (`keepP`, whose `clobbers` matches on the instruction again for every
register of the facts). A match on an `Instr` costs the kernel a quarter of a
millisecond, and these were most of the check: 12,000 of them for the 1,500
different instructions of an RSA function. `keepsO` reads what `unchanged`
asks off the instruction once (`viewK`, with its cases closed,
`inline_match%`), and answers from that. `keepsO` is `keeps` (`keepsO_eq`).
-/
-- separate module: `Rsa/AArch64/CvCode.lean`'s check of its code (`WP.keepLanesS`) can take it as `RdCode`'s does.

@[expose] public section

namespace VG.Proof.Bignum.AArch64

namespace KeepLanes

open VG VG.AArch64

/-- What `unchanged` asks of an instruction: whether it is an `ins` or a
`umov` that `step` follows, and the registers it writes. -/
structure View where
  moves : Bool
  ds : List Reg
  vd : Option VReg

/-- An instruction's `View`. -/
def viewFn : Instr → View
  | .vop (.ins .d2 d _ _) => ⟨true, [], some d⟩
  | .umov .x d _ _ => ⟨true, [d], none⟩
  | i => ⟨false, dsts i, vdstOf i⟩

/-- `viewFn`, with its cases closed (`inline_match%`). -/
def viewK : Instr → View := inline_match% viewFn dsts dstOf vdstOf VOp.dst Option.toList

theorem viewK_eq (i : Instr) : viewK i = viewFn i := by
  cases i with
  | vop op => cases op with
    | ins a d k n => cases a <;> rfl
    | _ => rfl
  | umov sz d n k => cases sz <;> rfl
  | _ => rfl

/-- `keepP i`, from the registers `i` writes. -/
def keepV (ds : List Reg) (vd : Option VReg) : Loc → Bool
  | .g x => !ds.elem x
  | .l v _ => vd != some v

theorem keepV_eq (i : Instr) (x : Loc) : keepV (dsts i) (vdstOf i) x = keepP i x := by
  cases x with
  | g r =>
    show (!(dsts i).elem r) = !clobbers i r
    refine congrArg _ (Bool.eq_iff_iff.mpr ?_)
    rw [clobbers_iff, List.elem_iff]
  | l v j => rfl

/-- `unchanged`, from the instruction's `View`. -/
def unchangedV (A : Facts) : View → Bool
  | ⟨false, ds, vd⟩ => A.all fun p => keepV ds vd p.2
  | ⟨true, _, _⟩ => false

theorem unchangedV_eq (A : Facts) (i : Instr) : unchangedV A (viewK i) = unchanged A i := by
  rw [viewK_eq]
  have hk : (A.all fun p => keepV (dsts i) (vdstOf i) p.2) = A.all fun p => keepP i p.2 :=
    congrArg _ (funext fun p => keepV_eq i p.2)
  cases i with
  | vop op => cases op with
    | ins a d k n => cases a <;> first | rfl | exact hk
    | _ => exact hk
  | umov sz d n k => cases sz <;> first | rfl | exact hk
  | _ => exact hk

/-- `foldS`, with `unchangedV`. -/
def foldO (A : Facts) : List Instr → Facts
  | [] => A
  | i :: is => cond (unchangedV A (viewK i)) (foldO A is) (forceL (step A i) fun B => foldO B is)

theorem foldO_eq (A : Facts) (is : List Instr) : foldO A is = foldS A is := by
  induction is generalizing A with
  | nil => rfl
  | cons i is ih =>
    rw [foldO, foldS, unchangedV_eq, ih]
    exact congrArg _ (congrArg _ (funext fun B => ih B))

/-- `checkS`, with `foldO`. -/
def checkO : Facts → Prog isa → Option Facts
  | A, .block is => forceL A fun A => some (foldO A is)
  | A, .seq a b => (checkO A a).bind (checkO · b)
  | A, .ite _ t e => (checkO A t).bind fun B => (checkO A e).map fun C => B.filter (· ∈ C)
  | A, .loop body _ => loopInv (fun I => checkO I body) (A.length + 1) A
  | _, _ => none

theorem checkO_eq (A : Facts) (c : Prog isa) : checkO A c = checkS A c := by
  induction c generalizing A <;> simp only [checkO, checkS, foldO_eq, *]

/-- `keeps`, evaluated with `checkO`. -/
def keepsO (T : List Reg) (c : Prog isa) : Bool :=
  match checkO (T.map fun r => (r, .g r)) c with
  | some B => T.all fun r => B.contains (r, .g r)
  | none => false

theorem keepsO_eq (T : List Reg) (c : Prog isa) : keepsO T c = keepsS T c := by
  unfold keepsO keepsS
  rw [checkO_eq]
  rfl

end KeepLanes

open VG VG.AArch64 KeepLanes
open VG.Proof.MlKem.AArch64 (Keep)

/-- `WP.keepLanes`, with the registers' check evaluated as `KeepLanes.keepsO`. -/
theorem WP.keepLanesO {c : Prog isa} {s : State} {Q : State → Prop} (rs T : List Reg) (h : WP isa c s Q)
    (hc : writesOnly (rs ++ T) c = true) (hT : keepsO T c = true) (hn : c.noCalls = true)
    (hv : c.allInstrs keepsV = true) :
    WP isa c s fun s' => Q s' ∧ Keep rs s s' :=
  WP.keepLanesS rs T h hc (by rw [← keepsO_eq]; exact hT) hn hv

end VG.Proof.Bignum.AArch64
