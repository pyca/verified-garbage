import VerifiedGarbage.Proof.Ed25519.Arm.AsFn
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Covers

/-!
# Ed25519 on ARMv7: calls of field code made a function

`fnCall_ok`: a call of a function on the working space at `r0` that, from
any state whose elements' limbs are below `2^16` (`AllLim`), changes no
register but `r1`–`r3` and no memory but `FA`, and maps the elements by `f`
(as `asFn_ok` proves of field code made a function), keeps what field code
keeps (`Keep`: a call also changes `lr`) and maps the elements by `f`. The
call runs on the working space alone (`WP.call`).

`addCall_ok` and `doubleCall_ok`: the calls of point addition and doubling,
as the inlined formulas (`fieldCode_ok`).
-/

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

/-- What `fnCall_ok` asks of the function, as a contract on the working space. -/
def fnK (b : BitVec 32) (f : Env → Env) : Contract isa where
  pre t := t.rd = [] ∧ t.wr = [⟨State.addr b, 8192⟩] ∧ Ctx b t ∧ AllLim t.mem b
  post t t' := Rest fnClob t t' ∧ Frame [FA b] t.mem t'.mem ∧ AllLim t'.mem b ∧
    env t'.mem b = f (env t.mem b)
  pub _ _ := True

theorem fnCall_ok {n : String} {c : Prog isa} {b : BitVec 32} {f : Env → Env}
    (hfn : ∀ s, Ctx b s → AllLim s.mem b → WP isa c s fun t => Rest fnClob s t ∧
      Frame [FA b] s.mem t.mem ∧ AllLim t.mem b ∧ env t.mem b = f (env s.mem b))
    (hn : c.noCalls = true) {s : State} (hc : Ctx b s) (hl : AllLim s.mem b) :
    WP isa (.call n c) s fun t => Keep b s t ∧ AllLim t.mem b ∧ env t.mem b = f (env s.mem b) := by
  have hv : ∀ t, (fnK b f).pre t → ∃ tr t', Exec isa c t tr t' ∧ abiPreserved t t' ∧ (fnK b f).post t t' :=
    fun t ⟨_, _, ht, hlt⟩ => by
      obtain ⟨tr, t', he, hR, hF, hL, hV⟩ := hfn t ht hlt
      exact ⟨tr, t', he, ⟨fun r hr => hR.gpr r (by revert hr; cases r <;> decide), hR.sp⟩, hR, hF, hL, hV⟩
  have g : ∀ q, q ∉ VG.Arm.linkRegs → (s.callEntry.withRegions [] [⟨State.addr b, 8192⟩]).gpr q = s.gpr q :=
    fun q hq => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have hcov : Covers [⟨State.addr b, 8192⟩] s.wr :=
    Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact hc.wr
  refine WP.call (k := fnK b f) hv (rd := []) (wr := [⟨State.addr b, 8192⟩])
    ⟨rfl, rfl, ⟨by rw [g _ (by decide)]; exact hc.r0, hc.fit, List.mem_singleton_self _⟩,
      by rw [State.withRegions_mem, State.callEntry_mem]; exact hl⟩
    (Covers.right hcov) hcov ?_ hn
  intro t hrd hwr hsp _ _ _ ⟨hR, hF, hL, hV⟩
  simp only [State.withRegions_mem, State.callEntry_mem] at hF hL hV
  refine ⟨⟨⟨fun q hq => ?_, hrd, hwr, hsp⟩, hF⟩, hL, hV⟩
  have hR' := hR.gpr q (by revert hq; cases q <;> decide)
  simp only [State.withRegions_gpr] at hR'
  rw [hR', State.callEntry_gpr _ (by revert hq; cases q <;> decide)]

/-- `limsAfter` keeps the slots it starts from. -/
theorem limsAfter_sup : ∀ {ops : List FieldOp} {S S' : List Slot}, limsAfter ops S = some S' →
    ∀ i ∈ S, i ∈ S'
  | [], _, _, h => by cases h; exact fun _ hi => hi
  | op :: ops, S, S', h => by
    simp only [limsAfter] at h
    split at h
    · exact fun i hi => limsAfter_sup h i (List.mem_cons_of_mem _ hi)
    · cases h

/-- Every slot. -/
def allSlots : List Slot := List.finRange 22

theorem mem_allSlots (i : Slot) : i ∈ allSlots := List.mem_finRange i

/-- `asFn_ok` for field code that every operation of which reads only
slots with limbs below `2^16`, from every slot's. -/
theorem asFnAll_ok {c : Bool} {ops : List FieldOp} {S' : List Slot} (h : limsAfter ops allSlots = some S')
    {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b) :
    WP isa (asFn c (fieldCode ops)) s fun t => Rest fnClob s t ∧ Frame [FA b] s.mem t.mem ∧
      AllLim t.mem b ∧ env t.mem b = evalOps ops (env s.mem b) :=
  WP.mono (asFn_ok (R := clob) (fun r hr => by cases c <;> revert r <;> decide)
      (fun s₁ hc₁ hl₁ => fieldCodeOn_ok ops h (W := allSlots) (fun _ _ => mem_allSlots _) hc₁ hl₁) hc
      (LimOn.of_all hl allSlots))
    fun _ ⟨hr, hf, hl', he⟩ => ⟨hr, frameS_FA hf, hl'.all fun i => limsAfter_sup h i (mem_allSlots i), he⟩

/-- A call of `vg_ed25519_r16_point_add`, as the inlined addition. -/
theorem addCall_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b) :
    WP isa Point16.addCall s fun t => Keep b s t ∧ AllLim t.mem b ∧
      env t.mem b = evalOps pointAddOps (env s.mem b) :=
  fnCall_ok (fun _ hc hl => asFnAll_ok rfl hc hl) (by decide +kernel) hc hl

/-- A call of `vg_ed25519_r16_point_double`, as the inlined doubling. -/
theorem doubleCall_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b) :
    WP isa Point16.doubleCall s fun t => Keep b s t ∧ AllLim t.mem b ∧
      env t.mem b = evalOps pointDoubleOps (env s.mem b) :=
  fnCall_ok (fun _ hc hl => asFnAll_ok rfl hc hl) (by decide +kernel) hc hl

end VG.Proof.Ed25519.Arm
