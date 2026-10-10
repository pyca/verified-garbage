import VerifiedGarbage.Proof.Ed25519.Arm.Point16Verified
import VerifiedGarbage.Proof.X25519.Chain250
import VerifiedGarbage.Proof.Ed25519.Arm.Power

/-!
# `vg_gf25519_r16_pow250` on ARMv7, verified

The function meets `pow250Contract` of `Spec/X25519/Field16.lean`, with no
stack: the proof against `powF`, the contract's facts by register, from
`pow250Fn_ok` on slot 2's limbs, which the contract bounds; the chain's
results are `a^(2^250 - 1)` in slot 15 and `a^11` in slot 14
(`power250Env_eval`, `chainF_eq`), as residues of the limbs' values
(`val_of_env`), and the memory the function keeps is what `Keeps₂` says
(`keeps₂_of_frame`, from the slots it writes, 14 to 17). Constant time by
taint tracking, as for the point functions.
-/

namespace VG.Proof.Ed25519.Arm.Pow250

open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Proof.Ed25519.Arm.Point16 (wsOf fPre fPub fPub_agree)
open VG.Spec.X25519 (P)
open VG.Spec.X25519.Field16 (Limbs valAt Keeps₂ aAt eAt oAt)

def powF : Contract Arm.isa where
  pre s := fPre s ∧ Limbs s.mem (wsOf s) (BitVec.ofNat 32 aAt)
  post s s' := Limbs s'.mem (wsOf s) (BitVec.ofNat 32 oAt) ∧ Limbs s'.mem (wsOf s) (BitVec.ofNat 32 eAt) ∧
    valAt s'.mem (wsOf s) (BitVec.ofNat 32 oAt) % P = valAt s.mem (wsOf s) (BitVec.ofNat 32 aAt) ^ (2 ^ 250 - 1) % P ∧
    valAt s'.mem (wsOf s) (BitVec.ofNat 32 eAt) % P = valAt s.mem (wsOf s) (BitVec.ofNat 32 aAt) ^ 11 % P ∧
    Keeps₂ (wsOf s) s.mem s'.mem
  pub := fPub

theorem power250Env_eval (e : Env) :
    power250Env e 15 = (VG.Proof.X25519.chainF (e 2)).1 ∧ power250Env e 14 = (VG.Proof.X25519.chainF (e 2)).2 := by
  simp only [power250Env, opMul, opSqn, Function.update_apply]
  simp only [↓reduceIte, Fin.isValue, Fin.reduceEq]
  exact ⟨rfl, rfl⟩

/-- A slot holding a power of another, as residues of the limbs' values. -/
theorem val_of_env {m m' : Mem} {b : BitVec 32} {i j : Slot} {e : Nat}
    (h : env m' b i = VG.Proof.X25519.pw (env m b j) e) :
    V m' (State.addr b) (offset i) % P = V m (State.addr b) (offset j) ^ e % P := by
  have := congrArg Fin.val h
  simp only [env, FS, VG.Proof.X25519.toFe_val, VG.Proof.X25519.pw, Fin.val_ofNat] at this
  rw [this, ← Nat.pow_mod]

/-- `Keeps₂` from the function's frame. -/
theorem keeps₂_of_frame {b : BitVec 32} {m m' : Mem}
    (hf : Frame (wRegions b [14, 15, 16, 17] ++ [saveR b]) m m') : Keeps₂ (State.addr b) m m' := by
  intro i hi he ho
  simp only [Spec.X25519.Field16.powWsBytes, eAt, Spec.X25519.Field16.tmpEnd,
    Spec.X25519.Field16.ownAt, Spec.X25519.Field16.ownEnd] at hi he ho
  have hc : (⟨State.addr b + BitVec.ofNat 64 i, 1⟩ : Region).Contains (State.addr b + BitVec.ofNat 64 i) 1 := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  have hA := ACC_eq
  have hS := SAVE_eq
  refine hf _ fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      have hj' : 14 ≤ j.val ∧ j.val < 18 :=
        (by decide +kernel : ∀ j : Slot, j ∈ ([14, 15, 16, 17] : List Slot) → 14 ≤ j.val ∧ j.val < 18) j hj
      exact Offset.disjoint _ (d := i) (n := 1) (e := offset j) (k := 64) (by simp only [offset]; omega)
        (by omega) (by simp only [offset]; omega) _ hc
    · rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (d := i) (n := 1) (e := ACC) (k := 128) (by omega) (by omega) (by omega) _ hc
  · rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (d := i) (n := 1) (e := SAVE) (k := 28) (by omega) (by omega) (by omega) _ hc

theorem pow_arm (s : State) (hs : powF.pre s) :
    ∃ t s', Exec isa pow250Fn s t s' ∧ abiPreserved s s' ∧ powF.post s s' := by
  obtain ⟨⟨_, hwr, hfit⟩, ha⟩ := hs
  have hc : Ctx (s.gpr .r0) s := ⟨rfl, hfit, by rw [hwr]; exact List.mem_singleton_self _⟩
  have hl : LimOn s.mem (s.gpr .r0) [2] := fun i hi => by
    rw [List.mem_singleton.mp hi]; exact lim_of_limbs rfl ha
  obtain ⟨t, s', he, hR, hF, hL, hE⟩ := pow250Fn_ok (b := s.gpr .r0) [] hc hl
  obtain ⟨h15, h14⟩ := power250Env_eval (env s.mem (s.gpr .r0))
  rw [VG.Proof.X25519.chainF_eq] at h15 h14
  rw [← hE] at h15 h14
  have v15 := val_of_env h15
  have v14 := val_of_env h14
  refine ⟨t, s', he, ⟨fun r hr => hR.gpr r (by revert hr; cases r <;> decide), hR.sp⟩,
    limbs_of_lim rfl (hL 15 (by decide)), limbs_of_lim rfl (hL 14 (by decide)), ?_, ?_, keeps₂_of_frame hF⟩
  · rw [valAt_ofNat _ _ (by decide), valAt_ofNat _ _ (by decide)]
    generalize (2 ^ 250 - 1 : Nat) = n at v15 ⊢
    exact v15
  · rw [valAt_ofNat _ _ (by decide), valAt_ofNat _ _ (by decide)]
    exact v14

theorem pow_ct : ConstantTime isa powF.pre powF.pub pow250Fn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (fPub_agree hp)) (by taint_decide)

/-- A state satisfying the precondition: `ws` at `0x1000`, all zero, and
the stack at `0x10000`. -/
def satF : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x10000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem sat_limbs : ∀ i < 16, Spec.X25519.Field16.limbAt (fun _ => 0) 0x1000 (BitVec.ofNat 32 aAt) i < 2 ^ 16 := by
  decide +kernel

theorem pow_sat : (Spec.X25519.Field16.pow250Contract Arm.abi).pre satF := by
  unfold Spec.X25519.Field16.pow250Contract
  exact Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, Spec.X25519.Field16.pow250Sig, Arm.abi, Arm.argRegs, Arm.Loc.val, satF]
    exact ⟨by decide, sat_limbs⟩)

theorem pow250Fn_verified : Verified Arm.target pow250Fn (Spec.X25519.Field16.pow250Contract Arm.abi) :=
  Verified.of_correct pow_arm pow_ct
    { pre := by sig_implies_pre [Spec.X25519.Field16.pow250Contract, Spec.X25519.Field16.pow250Sig, powF, fPre,
        fPub, wsOf, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Spec.X25519.Field16.pow250Contract, Spec.X25519.Field16.pow250Sig, powF, fPre,
        fPub, wsOf, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Spec.X25519.Field16.pow250Contract, Spec.X25519.Field16.pow250Sig, powF, fPre,
        fPub, wsOf, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨satF, pow_sat⟩ }

end VG.Proof.Ed25519.Arm.Pow250
