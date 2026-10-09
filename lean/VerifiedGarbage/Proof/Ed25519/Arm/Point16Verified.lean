import VerifiedGarbage.Proof.Ed25519.Arm.SpecConv
import VerifiedGarbage.Proof.Ed25519.Arm.FnLit
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-!
# `vg_ed25519_r16_point_add` and `vg_ed25519_r16_point_double` on ARMv7, verified

Each function meets its contract of `Spec/Ed25519/Point16.lean`, with no
stack: the proof against `addF` (`doubleF`), the contract's facts by
register, from `asFn_ok` and `fieldCodeOn_ok` on the slots of the operands,
whose limbs the contract bounds (`opSlots`); the elements as the contract
reads them are the proofs' (`SpecConv`), and the memory the function keeps
is what `Keeps` says (`keeps_of_frame`, from the slots it writes, `pointW`).
Constant time by taint tracking: only the pointer, in `r0`, is public, and
every address is `ws` plus a constant or the product's row counter.
-/

namespace VG.Proof.Ed25519.Arm.Point16

open VG VG.Arm VG.Impl.Ed25519.Arm VG.Impl.Ed25519.Arm.Point16 VG.Proof.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed25519.Point16 (elemAt pointAt PointLimbs Keeps pAt qAt dAt)
open VG.Spec.X25519.Field16 (Limbs)

/-- The slots the functions write: the result's and the formula's
temporaries'. -/
def pointW : List Slot := [0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15]

/-- The working space, `r0`. -/
abbrev wsOf (s : State) : Addr := State.addr (s.gpr .r0)

/-- The working space's facts: `ws` in `r0`, its 8192 bytes the only region. -/
def fPre (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨wsOf s, 8192⟩] ∧ (s.gpr .r0).toNat + 8192 ≤ 2 ^ 32

/-- What two runs agree on: the stack pointer and the pointer. -/
def fPub (s₁ s₂ : State) : Prop := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0

def addF : Contract Arm.isa where
  pre s := fPre s ∧ PointLimbs s.mem (wsOf s) pAt ∧ PointLimbs s.mem (wsOf s) qAt ∧
    Limbs s.mem (wsOf s) (BitVec.ofNat 32 dAt) ∧ elemAt s.mem (wsOf s) dAt = Spec.Ed25519.d
  post s s' := PointLimbs s'.mem (wsOf s) pAt ∧
    pointAt s'.mem (wsOf s) pAt = Spec.Ed25519.pointAdd (pointAt s.mem (wsOf s) pAt) (pointAt s.mem (wsOf s) qAt) ∧
    Keeps (wsOf s) s.mem s'.mem
  pub := fPub

def doubleF : Contract Arm.isa where
  pre s := fPre s ∧ PointLimbs s.mem (wsOf s) pAt ∧
    Limbs s.mem (wsOf s) (BitVec.ofNat 32 dAt) ∧ elemAt s.mem (wsOf s) dAt = Spec.Ed25519.d
  post s s' := PointLimbs s'.mem (wsOf s) pAt ∧
    pointAt s'.mem (wsOf s) pAt = Spec.Ed25519.pointAdd (pointAt s.mem (wsOf s) pAt) (pointAt s.mem (wsOf s) pAt) ∧
    Keeps (wsOf s) s.mem s'.mem
  pub := fPub

/-- `Keeps` from the frame of a function that writes the slots `W` of the
result and the temporaries. -/
theorem keeps_of_frame {b : BitVec 32} {W : List Slot} (hW : ∀ j ∈ W, j.val < 4 ∨ (8 ≤ j.val ∧ j.val < 16))
    {m m' : Mem} (hf : Frame (wRegions b W ++ [saveR b]) m m') : Keeps (State.addr b) m m' := by
  intro i hi hp ht ho
  simp only [Spec.Ed25519.Point16.wsBytes, pAt, qAt, Spec.Ed25519.Point16.tmpAt, dAt,
    Spec.X25519.Field16.ownAt, Spec.X25519.Field16.ownEnd] at hi hp ht ho
  have hc : (⟨State.addr b + BitVec.ofNat 64 i, 1⟩ : Region).Contains (State.addr b + BitVec.ofNat 64 i) 1 := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  have hA := ACC_eq
  have hS := SAVE_eq
  refine hf _ fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      have := hW j hj
      have hj' := j.isLt
      exact Offset.disjoint _ (d := i) (n := 1) (e := offset j) (k := 64) (by simp only [offset]; omega)
        (by omega) (by simp only [offset]; omega) _ hc
    · rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (d := i) (n := 1) (e := ACC) (k := 128) (by omega) (by omega) (by omega) _ hc
  · rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (d := i) (n := 1) (e := SAVE) (k := 28) (by omega) (by omega) (by omega) _ hc

theorem pointW_ok : ∀ j ∈ pointW, j.val < 4 ∨ (8 ≤ j.val ∧ j.val < 16) := by decide

/-- The limbs of the point at `pAt` (`qAt` for `q = 4`). -/
theorem lim_point {m : Mem} {b : BitVec 32} {o q : Nat} (ho : o = 64 + 64 * q)
    (h : PointLimbs m (State.addr b) o) (i : Slot) (hi : q ≤ i.val ∧ i.val < q + 4) :
    Lim m (State.addr b) (offset i) :=
  lim_of_limbs (by simp only [ho, offset, Spec.Ed25519.Point16.elemBytes, Spec.X25519.Field16.elemBytes,
    Spec.X25519.Field16.limbs]; omega) (h (i.val - q) (by omega))

theorem limbs_point {m : Mem} {b : BitVec 32} {S : List Slot} (hl : LimOn m b S)
    (h : ∀ i : Slot, i.val < 4 → i ∈ S) : PointLimbs m (State.addr b) pAt := fun j hj =>
  limbs_of_lim (i := ⟨j, by omega⟩) (by simp only [pAt, offset, Spec.Ed25519.Point16.elemBytes,
    Spec.X25519.Field16.elemBytes, Spec.X25519.Field16.limbs]) (hl _ (h _ hj))

theorem d_slot {m : Mem} {b : BitVec 32} (hd : elemAt m (State.addr b) dAt = Spec.Ed25519.d) :
    env m b 16 = Spec.Ed25519.d := by
  rw [← hd]; exact (elemAt_eq m b 16).symm

/-- The function's facts, from the limbs of the slots `S`. -/
theorem fn_arm {ops : List FieldOp} {S S' : List Slot} (hS : limsAfter ops S = some S')
    (hW : ∀ op ∈ ops, opOut op ∈ pointW) (s : State) (hp : fPre s) (hl : LimOn s.mem (s.gpr .r0) S) :
    ∃ t s', Exec isa (asFn false (fieldCode ops)) s t s' ∧ abiPreserved s s' ∧ LimOn s'.mem (s.gpr .r0) S' ∧
      env s'.mem (s.gpr .r0) = evalOps ops (env s.mem (s.gpr .r0)) ∧ Keeps (wsOf s) s.mem s'.mem := by
  obtain ⟨_, hwr, hfit⟩ := hp
  have hc : Ctx (s.gpr .r0) s := ⟨rfl, hfit, by rw [hwr]; exact List.mem_singleton_self _⟩
  obtain ⟨t, s', he, hR, hF, hL, hE⟩ := asFn_ok (c := false) (W := pointW) (R := clob) (by decide)
    (fun s₁ hc₁ hl₁ => fieldCodeOn_ok ops hS hW hc₁ hl₁) hc hl
  exact ⟨t, s', he, ⟨fun r hr => hR.gpr r (by revert hr; cases r <;> decide), hR.sp⟩, hL, hE,
    keeps_of_frame pointW_ok hF⟩

theorem add_arm (s : State) (hs : addF.pre s) :
    ∃ t s', Exec isa addFn s t s' ∧ abiPreserved s s' ∧ addF.post s s' := by
  obtain ⟨hp, hpl, hql, hdl, hd⟩ := hs
  have hl : LimOn s.mem (s.gpr .r0) [0, 1, 2, 3, 4, 5, 6, 7, 16] := by
    intro i hi
    have hi' : i.val < 4 ∨ (4 ≤ i.val ∧ i.val < 8) ∨ i.val = 16 := by revert i; decide +kernel
    rcases hi' with hi' | hi' | hi'
    · exact lim_point (q := 0) rfl hpl i ⟨Nat.zero_le _, hi'⟩
    · exact lim_point (q := 4) rfl hql i hi'
    · exact lim_of_limbs (by rw [show i = 16 from Fin.ext hi']; rfl) hdl
  obtain ⟨S', hS'⟩ := Option.isSome_iff_exists.mp
    (by decide +kernel : (limsAfter pointAddOps [0, 1, 2, 3, 4, 5, 6, 7, 16]).isSome = true)
  obtain ⟨t, s', he, ha, hL, hE, hK⟩ := fn_arm hS' (by decide +kernel) s hp hl
  refine ⟨t, s', he, ha, limbs_point hL fun i hi => ?_, ?_, hK⟩
  · obtain ⟨op, hop, ho⟩ := (by decide +kernel : ∀ i : Slot, i.val < 4 → ∃ op ∈ pointAddOps, opOut op = i) i hi
    rw [← ho]; exact limsAfter_out hS' op hop
  · rw [show pAt = 64 + 64 * 0 from rfl, show qAt = 64 + 64 * 4 from rfl, pointAt_eq _ _ 0 (by decide),
      pointAt_eq _ _ 0 (by decide), pointAt_eq _ _ 4 (by decide), hE]
    exact pointAdd_eval _ (d_slot hd)

theorem double_arm (s : State) (hs : doubleF.pre s) :
    ∃ t s', Exec isa doubleFn s t s' ∧ abiPreserved s s' ∧ doubleF.post s s' := by
  obtain ⟨hp, hpl, hdl, hd⟩ := hs
  have hl : LimOn s.mem (s.gpr .r0) [0, 1, 2, 3, 16] := by
    intro i hi
    have hi' : i.val < 4 ∨ i.val = 16 := by revert i; decide +kernel
    rcases hi' with hi' | hi'
    · exact lim_point (q := 0) rfl hpl i ⟨Nat.zero_le _, hi'⟩
    · exact lim_of_limbs (by rw [show i = 16 from Fin.ext hi']; rfl) hdl
  obtain ⟨S', hS'⟩ := Option.isSome_iff_exists.mp
    (by decide +kernel : (limsAfter pointDoubleOps [0, 1, 2, 3, 16]).isSome = true)
  obtain ⟨t, s', he, ha, hL, hE, hK⟩ := fn_arm hS' (by decide +kernel) s hp hl
  refine ⟨t, s', he, ha, limbs_point hL fun i hi => ?_, ?_, hK⟩
  · obtain ⟨op, hop, ho⟩ := (by decide +kernel : ∀ i : Slot, i.val < 4 → ∃ op ∈ pointDoubleOps, opOut op = i) i hi
    rw [← ho]; exact limsAfter_out hS' op hop
  · rw [show pAt = 64 + 64 * 0 from rfl, pointAt_eq _ _ 0 (by decide), pointAt_eq _ _ 0 (by decide), hE]
    exact pointDouble_eval _ (d_slot hd)

/-! ## Constant time -/

theorem fPub_agree {s₁ s₂ : State} (h : fPub s₁ s₂) : ∀ r ∈ [Reg.r0], s₁.gpr r = s₂.gpr r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact h.2

theorem add_ct : ConstantTime isa addF.pre addF.pub addFn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (fPub_agree hp)) (by taint_decide)

theorem double_ct : ConstantTime isa doubleF.pre doubleF.pub doubleFn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (fPub_agree hp)) (by taint_decide)

/-! ## The shared contracts -/

/-- `d`'s value. -/
def dLit : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- The memory of `satF`: `d`'s limbs in slot 16 of the working space at
`0x1000`, and zeros elsewhere. -/
def satMem : Mem := fun a =>
  if 0x1440 ≤ a.toNat ∧ a.toNat < 0x1480 then
    BitVec.ofNat 8 (dLit / 2 ^ (16 * ((a.toNat - 0x1440) / 4)) % 65536 / 256 ^ ((a.toNat - 0x1440) % 4))
  else 0

/-- A state satisfying the preconditions: `ws` at `0x1000`, the points zero,
`d` in slot 16, and the stack at `0x10000`. -/
def satF : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x10000
  n := false
  z := false
  c := false
  v := false
  mem := satMem
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem sat_limbAt : ∀ o < 22, ∀ i < 16,
    Spec.X25519.Field16.limbAt satMem 0x1000 (BitVec.ofNat 32 (64 + 64 * o)) i < 2 ^ 16 := by
  decide +kernel

theorem sat_limbs (o : Nat) (ho : o < 22) : Limbs satMem 0x1000 (BitVec.ofNat 32 (64 + 64 * o)) :=
  sat_limbAt o ho

theorem sat_points (o : Nat) (ho : o + 4 ≤ 22) : PointLimbs satMem 0x1000 (64 + 64 * o) := fun j hj => by
  have := sat_limbs (o + j) (by omega)
  rwa [show 64 + 64 * (o + j) = 64 + 64 * o + Spec.Ed25519.Point16.elemBytes * j by
    simp only [Spec.Ed25519.Point16.elemBytes, Spec.X25519.Field16.elemBytes, Spec.X25519.Field16.limbs]; omega]
    at this

theorem sat_dval : Spec.X25519.Field16.valAt satMem 0x1000 (BitVec.ofNat 32 dAt) = dLit := by
  decide +kernel

theorem d_eq : Spec.Ed25519.d = Fin.ofNat Spec.X25519.P dLit := by decide +kernel

theorem sat_d : elemAt satMem 0x1000 dAt = Spec.Ed25519.d := by
  rw [d_eq, elemAt, sat_dval]

theorem add_sat : (Spec.Ed25519.Point16.addContract Arm.abi).pre satF := by
  unfold Spec.Ed25519.Point16.addContract
  exact Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, Spec.Ed25519.Point16.sig, Arm.abi, Arm.argRegs, Arm.Loc.val, satF]
    exact ⟨by decide, sat_points 0 (by decide), sat_points 4 (by decide), sat_limbs 16 (by decide), sat_d⟩)

theorem double_sat : (Spec.Ed25519.Point16.doubleContract Arm.abi).pre satF := by
  unfold Spec.Ed25519.Point16.doubleContract
  exact Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, Spec.Ed25519.Point16.sig, Arm.abi, Arm.argRegs, Arm.Loc.val, satF]
    exact ⟨by decide, sat_points 0 (by decide), sat_limbs 16 (by decide), sat_d⟩)

theorem addFn_verified : Verified Arm.target addFn (Spec.Ed25519.Point16.addContract Arm.abi) :=
  Verified.of_correct add_arm add_ct
    { pre := by sig_implies_pre [Spec.Ed25519.Point16.addContract, Spec.Ed25519.Point16.sig, addF, fPre,
        fPub, wsOf, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Spec.Ed25519.Point16.addContract, Spec.Ed25519.Point16.sig, addF, fPre,
        fPub, wsOf, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Spec.Ed25519.Point16.addContract, Spec.Ed25519.Point16.sig, addF, fPre,
        fPub, wsOf, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨satF, add_sat⟩ }

theorem doubleFn_verified : Verified Arm.target doubleFn (Spec.Ed25519.Point16.doubleContract Arm.abi) :=
  Verified.of_correct double_arm double_ct
    { pre := by sig_implies_pre [Spec.Ed25519.Point16.doubleContract, Spec.Ed25519.Point16.sig, doubleF, fPre,
        fPub, wsOf, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Spec.Ed25519.Point16.doubleContract, Spec.Ed25519.Point16.sig, doubleF, fPre,
        fPub, wsOf, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Spec.Ed25519.Point16.doubleContract, Spec.Ed25519.Point16.sig, doubleF, fPre,
        fPub, wsOf, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨satF, double_sat⟩ }

end VG.Proof.Ed25519.Arm.Point16
