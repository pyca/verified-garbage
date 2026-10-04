import VerifiedGarbage.Proof.Ed448.Arm.Verify.Hash
import VerifiedGarbage.Proof.Ed448.Arm.ScalarVerified
import VerifiedGarbage.Proof.Ed448.Arm.VerifyLocal
import VerifiedGarbage.Proof.Ed448.Arm.VerifyLit

/-!
# Ed448 verification on ARMv7: the challenge, the equation, and the body

`reduce_step`: `k`, the hash reduced modulo `L` by `vg_ed448_scalar_reduce`,
in the frame at `K`. `equation_step`: `vg_ed448_verify_equation`'s result,
for any code meeting its contract (`EqOk`, a hypothesis: only the
registration file imports the proof). `body_ok`: the whole body.
-/

namespace VG.Proof.Ed448.Arm.Verify

open VG.Proof.Ed448.Arm.Shake (Slot valid)

open VG VG.Arm VG.Impl.Ed448.Arm.Verify VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.Within Whole.FR Whole.call_ok)
open VG.Proof.Ed448.Arm (verifyEquationLocal scalarReduceLocal scalarReduce_ok)

/-- `vg_ed448_verify_equation` meets its contract. -/
abbrev EqOk : Prop := ∀ s, verifyEquationLocal.pre s →
  ∃ tr s', Exec isa Impl.Ed448.Arm.verifyEquation s tr s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s'

/-- `vg_ed448_verify_equation` is constant time under its contract. -/
abbrev EqCT : Prop :=
  ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub Impl.Ed448.Arm.verifyEquation

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

/-! ## `vg_ed448_scalar_reduce` -/

theorem reduce_noFrames : Impl.Ed448.Arm.scalarReduce.noFrames = true := by lit_decide
theorem equation_noFrames : Impl.Ed448.Arm.verifyEquation.noFrames = true := by lit_decide

def kReg (L : Lay) : Region := ⟨State.addr L.E + BitVec.ofNat 64 K, 57⟩
def hReg (L : Lay) : Region := ⟨State.addr L.E + BitVec.ofNat 64 HASH, 114⟩

theorem kWithin (L : Lay) : Whole.Within (kReg L) L.FR := ⟨K, rfl, by change 160 + 57 ≤ 248; decide⟩
theorem hWithin (L : Lay) : Whole.Within (hReg L) L.FR := ⟨HASH, rfl, by change 40 + 114 ≤ 248; decide⟩

def ReduceArgs (L : Lay) (t : State) : Prop :=
  t.gpr .r0 = L.E + BitVec.ofNat 32 K ∧ t.gpr .r1 = L.E + BitVec.ofNat 32 HASH ∧ t.gpr .r2 = L.scr

theorem reduce_pre (hL : L.Ok) (ha : ReduceArgs L t) :
    scalarReduceLocal.pre (t.callEntry.withRegions [hReg L] [kReg L, L.SCR]) := by
  obtain ⟨h0, h1, h2⟩ := ha
  have e0 : (t.callEntry.withRegions [hReg L] [kReg L, L.SCR]).gpr .r0 = L.E + BitVec.ofNat 32 K := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), h0]
  have e1 : (t.callEntry.withRegions [hReg L] [kReg L, L.SCR]).gpr .r1 = L.E + BitVec.ofNat 32 HASH := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), h1]
  have e2 : (t.callEntry.withRegions [hReg L] [kReg L, L.SCR]).gpr .r2 = L.scr := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), h2]
  simp only [scalarReduceLocal]
  rw [e0, e1, e2, State.withRegions_rd, State.withRegions_wr, hL.kit.frame_addr (by decide), hL.kit.frame_addr (by decide)]
  refine ⟨rfl, rfl, Offset.disjoint _ (by decide) (by decide) (by decide),
    hL.kc.sub_left (Offset.sub_base _ (by decide : K + 57 ≤ 280)),
    hL.kc.sub_left (Offset.sub_base _ (by decide : HASH + 114 ≤ 280)),
    hL.kit.frame_fit (by decide), hL.kit.frame_fit (by decide), hL.nc⟩

theorem reduce_covers (L : Lay) : Covers ([hReg L] ++ [kReg L, L.SCR]) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Shake.covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inl (hWithin L)
  · exact .inl (kWithin L)
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by simp⟩

theorem reduce_writes (L : Lay) : ∀ r ∈ [kReg L, L.SCR],
    Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inl (kWithin L)
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by simp⟩

theorem reduce_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith reduceArgs "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce) t fun u =>
      Ctx L g m₀ u ∧ Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 K) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.r0, .frame K), (.r1, .frame HASH), (.r2, scr 0)]) (stk := [])
    (by decide) (by simp [valid, scr, SC, Slot, K, HASH]) (by simp [preserved]) (by decide) (by simp))
    fun u ⟨hu, hm, hs, _⟩ => ?_)
  have h0 := hs (.r0, .frame K) (by simp)
  have h1 := hs (.r1, .frame HASH) (by simp)
  have h2 := hs (.r2, scr 0) (by simp)
  simp only [argValue, scr, Lay.value, BitVec.add_zero] at h0 h1 h2
  have he : Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114 =
      Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114 :=
    Shake.bytes_setup hm (D := hReg L) (Offset.base_disjoint _ (by decide) (by decide)) (by change 114 ≤ 2 ^ 64; decide)
  refine Whole.call_ok hu scalarReduce_ok reduce_noFrames (reduce_pre hL ⟨h0, h1, h2⟩) (reduce_covers L)
    (reduce_writes L) fun v hv _ hp => ⟨hv, ?_⟩
  change Spec.Ed448.bytesAt v.mem (State.addr (u.callEntry.gpr .r0)) 57 =
    Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt u.mem (State.addr (u.callEntry.gpr .r1)) 114) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), h0, h1, hL.kit.frame_addr (by decide),
    hL.kit.frame_addr (by decide), he] at hp
  exact hp

/-! ## `vg_ed448_verify_equation` -/

def EqArgs (L : Lay) (t : State) : Prop :=
  t.gpr .r0 = L.pk ∧ t.gpr .r1 = L.sig ∧ t.gpr .r2 = L.E + BitVec.ofNat 32 K ∧ t.gpr .r3 = L.scr

theorem equation_pre (hL : L.Ok) (ha : EqArgs L t) :
    verifyEquationLocal.pre (t.callEntry.withRegions [L.PK, L.SIG, kReg L] [L.SCR]) := by
  obtain ⟨h0, h1, h2, h3⟩ := ha
  have e : ∀ r, r ∉ linkRegs → (t.callEntry.withRegions [L.PK, L.SIG, kReg L] [L.SCR]).gpr r = t.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  simp only [verifyEquationLocal]
  rw [e .r0 (by decide), e .r1 (by decide), e .r2 (by decide), e .r3 (by decide), h0, h1, h2, h3,
    State.withRegions_rd, State.withRegions_wr, hL.kit.frame_addr (by decide)]
  exact ⟨rfl, rfl, hL.ps, hL.ss, hL.kc.sub_left (Offset.sub_base _ (by decide : K + 57 ≤ 280)), hL.np, hL.ns, hL.kit.frame_fit (by decide), hL.nc⟩

theorem equation_covers (L : Lay) :
    Covers ([L.PK, L.SIG, kReg L] ++ [L.SCR]) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Shake.covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inr ⟨L.PK, by simp [Lay.inputs], 0, (BitVec.add_zero _).symm, by simp⟩
  · exact .inr ⟨L.SIG, by simp [Lay.inputs], 0, (BitVec.add_zero _).symm, by simp⟩
  · exact .inl (kWithin L)
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by simp⟩

theorem equation_writes (L : Lay) : ∀ r ∈ [L.SCR],
    Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by simp⟩

/-- `1` if `b`, else `0`. -/
def signWord (b : Bool) : BitVec 32 := if b then 1 else 0

theorem equation_step (hv : EqOk) (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith equationArgs "vg_ed448_verify_equation" Impl.Ed448.Arm.verifyEquation) t fun u =>
      Ctx L g m₀ u ∧ u.gpr .r0 = signWord (Spec.Ed448.verifyEquation
        (Spec.Ed448.bytesAt m₀ (State.addr L.pk) 57) (Spec.Ed448.bytesAt m₀ (State.addr L.sig) 114)
        (Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 K) 57)) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.r0, .caller 0 0), (.r1, .caller 5 0), (.r2, .frame K), (.r3, scr 0)]) (stk := [])
    (by decide) (by simp [valid, scr, SC, Slot, K]) (by simp [preserved]) (by decide) (by simp))
    fun u ⟨hu, hm, hs, _⟩ => ?_)
  have h0 := hs (.r0, .caller 0 0) (by simp)
  have h1 := hs (.r1, .caller 5 0) (by simp)
  have h2 := hs (.r2, .frame K) (by simp)
  have h3 := hs (.r3, scr 0) (by simp)
  simp only [argValue, scr, Lay.value, BitVec.add_zero] at h0 h1 h2 h3
  have hk : Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 K) 57 =
      Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 K) 57 :=
    Shake.bytes_setup hm (D := kReg L) (Offset.base_disjoint _ (by decide) (by decide)) (by change 57 ≤ 2 ^ 64; decide)
  have hpk : Spec.Ed448.bytesAt u.mem (State.addr L.pk) 57 = Spec.Ed448.bytesAt m₀ (State.addr L.pk) 57 :=
    hu.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 57 ≤ 2 ^ 64; decide)
  have hsg : Spec.Ed448.bytesAt u.mem (State.addr L.sig) 114 = Spec.Ed448.bytesAt m₀ (State.addr L.sig) 114 :=
    hu.input_bytes hL (r := L.SIG) (by simp [Lay.inputs]) (by change 114 ≤ 2 ^ 64; decide)
  refine Whole.call_ok hu hv equation_noFrames (equation_pre hL ⟨h0, h1, h2, h3⟩) (equation_covers L)
    (equation_writes L) fun v hv' _ hp => ⟨hv', ?_⟩
  change v.gpr .r0 = if Spec.Ed448.verifyEquation
    (Spec.Ed448.bytesAt u.mem (State.addr (u.callEntry.gpr .r0)) 57)
    (Spec.Ed448.bytesAt u.mem (State.addr (u.callEntry.gpr .r1)) 114)
    (Spec.Ed448.bytesAt u.mem (State.addr (u.callEntry.gpr .r2)) 57) then 1 else 0 at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), h0, h1, h2, hL.kit.frame_addr (by decide), hk] at hp
  rw [hp, hpk, hsg]
  rfl

/-! ## The body -/

theorem take57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  simp [Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem verify_of_len {pk ctx msg sig : List Byte} (h : ctx.length ≤ 255) :
    Spec.Ed448.verify pk ctx msg sig = Spec.Ed448.verifyEquation pk sig
      (Spec.Ed448.scalarReduce (Spec.Ed448.hash ctx (sig.take 57 ++ pk ++ msg))) := by
  unfold Spec.Ed448.verify
  simp only [h, decide_true, Bool.true_and]

/-- The result of verification with a context of fewer than 256 bytes. -/
theorem body_ok (hv : EqOk) (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa body t fun u => Ctx L g m₀ u ∧ u.gpr .r0 = signWord (Spec.Ed448.verify
      (Spec.Ed448.bytesAt m₀ (State.addr L.pk) 57)
      (Spec.Ed448.bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat)
      (Spec.Ed448.bytesAt m₀ (State.addr L.msg) L.len.toNat)
      (Spec.Ed448.bytesAt m₀ (State.addr L.sig) 114)) := by
  refine WP.seq (WP.mono (hdr_ok hc hL ha) fun t1 ⟨hc1, hh⟩ => ?_)
  refine WP.seq (WP.mono (hash_ok hc1 hL ha hh) fun t2 ⟨hc2, hh2⟩ => ?_)
  refine WP.seq (WP.mono (reduce_step hc2 hL ha) fun t3 ⟨hc3, hk⟩ => ?_)
  refine WP.mono (equation_step hv hc3 hL ha) fun u ⟨hu, hr⟩ => ⟨hu, ?_⟩
  have hl : (Spec.Ed448.bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat).length ≤ 255 := by
    simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range]; have := hL.cl; omega
  rw [hr, hk, hh2, verify_of_len hl, take57]

theorem body_noFrames : body.noFrames = true := by
  simp only [Impl.Ed448.Arm.Verify.body, Impl.Ed448.Arm.Verify.hash, Impl.Ed448.Arm.Shake.zeroState,
    Impl.Ed448.Arm.Shake.absorb, Impl.Ed448.Arm.Shake.pad, Impl.Ed448.Arm.Shake.squeeze, callWith,
    Code.noFrames, Bool.and_self]
  rw [PublicKey.absorb_noFrames, PublicKey.pad_noFrames, PublicKey.squeeze_noFrames, reduce_noFrames,
    equation_noFrames]
  rfl

end VG.Proof.Ed448.Arm.Verify
