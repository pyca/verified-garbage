module

public import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.CTCommon
import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.PruneCT
public import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wrap
public import VerifiedGarbage.Spec.Ed25519.CachedSign
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Body
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Secret
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Finalize
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.BlocksCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.EntryCT
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Init
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! Merged from `Proof.Ed25519.Arm.SignCached.CTReady`. -/

@[expose] public section

section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm
variable {L : Lay} {s : State}

def reduce_ready (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 184) (ha : ReduceArgs L d s) : Whole.CallReady scalarReduceLocal L.E L.inputs L.outputs s := by
  have cov : Covers (reduceRd L ++ reduceWr L d) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (digestWithin L)
    · exact .inl (fieldWithin L (by omega))
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ reduceWr L d, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (fieldWithin L (by omega))
    · exact .inr (.inr (scratchWithin L))
  exact ⟨reduceRd L, reduceWr L d, reduce_pre hL hd ha, cov, ws⟩

def base_ready (hL : L.Ok) (ha : BaseArgs L s) (hsy : s.syms VG.Impl.Ed25519.Arm.combSym = L.T)
    (hw : Tbl L s.mem) : Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs s := by
  have cov : Covers (baseRd L ++ baseWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [baseRd, baseWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (fieldWithin L (by decide))
    · exact .inr ⟨L.TB, List.mem_append_left _ (tb_input L), 0, by simp⟩
    · exact .inr (output_covered (baseWithin L))
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ baseWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [baseWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (.inl (baseWithin L))
    · exact .inr (.inr (scratchWithin L))
  exact ⟨baseRd L, baseWr L, base_pre hL ha hsy hw, cov, ws⟩

def mul_ready {g m} (hc : Ctx L g m s) (hL : L.Ok) (ha : MulArgs L s) : Whole.CallReady scalarMulAddLocal L.E L.inputs L.outputs s := by
  have cov : Covers (mulRd L ++ mulWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [mulRd, mulWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact .inl (fieldWithin L (by decide))
    · exact .inl (fieldWithin L (by decide))
    · exact .inl (fieldWithin L (by decide))
    · exact .inl ⟨0, by simp, by change 0 + 4 ≤ 248; decide⟩
    · exact .inr (output_covered (halfWithin L))
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ mulWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [mulWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (.inl (halfWithin L))
    · exact .inr (.inr (scratchWithin L))
  exact ⟨mulRd L, mulWr L, mul_pre hc hL ha, cov, ws⟩

def init_ready (hL : L.Ok) (ha : s.gpr .r0 = L.scr) :
    Whole.CallReady (Proof.Sha512.initArm Spec.Sha512.H0_512) L.E L.inputs L.outputs s := by
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨[], Whole.initWr L.scr, Whole.init_pre ha hL.nc, Whole.covers_writes hw, hw⟩

def update_ready (hL : L.Ok) (he : s.sp = L.E) {count p len : BitVec 32}
    (hi : Input L p len) (ha : UpdateArgs L count p len s) :
    Whole.CallReady Proof.Sha512.updateArm L.E L.inputs L.outputs s := by
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨Whole.updateRd L.E p len, Whole.hashWr L.scr, update_pre hL he ha hi, update_covers hi, hw⟩

def finalize_ready (hL : L.Ok) (he : s.sp = L.E) {count : BitVec 32} (ha : FinalArgs L count s) :
    Whole.CallReady Proof.Sha512.finalizeArm L.E L.inputs L.outputs s :=
  ⟨Whole.finalizeRd L.E, Whole.finalizeWr L.scr (L.E + 184), finalize_pre hL he ha,
    finalize_covers hL, final_writes hL⟩

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.CTBody`. -/
section
/-! Merged from `Proof.Ed25519.Arm.SignCached.CTHash`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem init_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L [(.r0, .caller 5 0)] []))
      (.call Spec.Sha512.init512Api.name (Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct (Proof.Sha512.Arm.Stream.init_verified _).1
    (Proof.Sha512.Arm.Stream.init_verified _).2.1 rfl
  · intro g m t _ hs
    have h := hs.1 (.r0, .caller 5 0) (by simp)
    change t.gpr .r0 = L.scr + 0#32 at h
    rw [BitVec.add_zero] at h
    exact init_ready hL h
  · intro a b ar aw br bw h
    exact call_gpr_eq (p := (.r0, .caller 5 0)) h (by simp) (by simp [linkRegs])

theorem update_call_ct (hL : L.Ok) (count : Nat) (p n : Value)
    (hi : Input L (value L p) (value L n)) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L
      [(.r0, .caller 5 0), (.r2, .const count), (.r3, .const 0)] [p,n,.caller 5 192]))
      (.call "vg_sha512_update_scratch" Impl.Sha512.Arm.Stream.update)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct Proof.Sha512.Arm.Stream.Update.update_verified.1
    Proof.Sha512.Arm.Stream.Update.update_verified.2.1 Whole.update_noFrames
  · intro g m t hc hs
    have a0 := hs.1 (.r0, .caller 5 0) (by simp)
    change t.gpr .r0 = L.scr + 0#32 at a0
    rw [BitVec.add_zero] at a0
    exact update_ready hL hc.sp hi ⟨a0, hs.1 (.r2, .const count) (by simp),
      hs.1 (.r3, .const 0) (by simp), hs.2 0 (by simp), hs.2 1 (by simp), hs.2 2 (by simp)⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.r0, .caller 5 0)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r2, .const count)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r3, .const 0)) h (by simp) (by simp [linkRegs]),
      stack_arg_eq h (j := 0) (by simp), stack_arg_eq h (j := 1) (by simp), stack_arg_eq h (j := 2) (by simp)⟩

theorem finalize_call_ct (hL : L.Ok) (n : Nat) (b : Bool) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L
      [(.r0, .caller 5 0), (.r2, if b then .caller 4 n else .const n), (.r3, .const 0)]
      [.frame 184, .caller 5 192]))
      (.call "vg_sha512_finalize_scratch" Impl.Sha512.Arm.Stream.finalize)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct Proof.Sha512.Arm.Stream.Finalize.finalize_verified.1
    Proof.Sha512.Arm.Stream.Finalize.finalize_verified.2.1 Whole.finalize_noFrames
  · intro g m t hc hs
    have a0 := hs.1 (.r0, .caller 5 0) (by simp)
    change t.gpr .r0 = L.scr + 0#32 at a0
    rw [BitVec.add_zero] at a0
    exact finalize_ready hL hc.sp ⟨a0,
      hs.1 (.r2, if b then .caller 4 n else .const n) (by simp),
      hs.1 (.r3, .const 0) (by simp), hs.2 0 (by decide), hs.2 1 (by decide)⟩
  · intro a c ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.r0, .caller 5 0)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r2, if b then .caller 4 n else .const n)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r3, .const 0)) h (by simp) (by simp [linkRegs]),
      stack_arg_eq h (j := 0) (by decide), stack_arg_eq h (j := 1) (by decide)⟩

theorem init_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) init
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [(.r0, .caller 5 0)] [] (by decide) (by simp [Whole.valid])
    (by decide) (by simp) (by simp [preserved])).seq (init_call_ct hL)

theorem update_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (count : Nat) (p n : Value) (hc : count < 65536) (hp : Whole.valid p) (hn : Whole.valid n)
    (hi : Input L (value L p) (value L n)) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True)
      (update (setup [(.r0, .caller 5 0), (.r2, .const count), (.r3, .const 0)] [p,n,.caller 5 192]))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hv : ∀ x : Reg × Value, x ∈ [(.r0, .caller 5 0), (.r2, .const count), (.r3, .const 0)] →
      Whole.valid x.2 := by simp [Whole.valid,hc]
  have hvs : ∀ v ∈ [p,n,Value.caller 5 192], Whole.valid v := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl)
    · exact hp
    · exact hn
    · simp [Whole.valid]
  exact (setup_ct hL ha hb _ _ (by simp) hv (by simp) hvs (by simp [preserved])).seq
    (update_call_ct hL count p n hi)

theorem finalize_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (n : Nat) (hn : n < 256) (b : Bool) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (finalize n b)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hv : Whole.valid (if b then .caller 4 n else .const n) := by
    cases b <;> simp [Whole.valid] <;> omega
  have hvall : ∀ p : Reg × Value, p ∈ [(.r0, .caller 5 0),
      (.r2, if b then .caller 4 n else .const n), (.r3, .const 0)] → Whole.valid p.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    · simp [Whole.valid]
    · exact hv
    · simp [Whole.valid]
  exact (setup_ct hL ha hb _ _ (by simp) hvall (by decide) (by simp [Whole.valid])
    (by simp [preserved])).seq (finalize_call_ct hL n b)

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.CTHashPipeline`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem hashSeed_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (hashSeed)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hi : Input L (value L (.caller 1 0)) (value L (.const 32)) := by
    change Input L (L.seed + 0#32) 32#32
    rw [BitVec.add_zero]
    exact seed_input hL
  exact (init_ct hL ha hb).seq ((update_ct hL ha hb 0 (.caller 1 0) (.const 32)
    (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hi).seq
    (finalize_ct hL ha hb 32 (by decide) false))

theorem hashNonce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (hashNonce)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hp : Input L (value L (.frame 56)) (value L (.const 32)) := prefix_input hL
  have hm : Input L (value L (.caller 3 0)) (value L (.caller 4 0)) := by
    change Input L (L.msg + 0#32) (L.len + 0#32)
    rw [BitVec.add_zero, BitVec.add_zero]
    exact message_input hL
  exact (init_ct hL ha hb).seq ((update_ct hL ha hb 0 (.frame 56) (.const 32)
    (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hp).seq
    ((update_ct hL ha hb 32 (.caller 3 0) (.caller 4 0)
      (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hm).seq
      (finalize_ct hL ha hb 32 (by decide) true)))

theorem hashChallenge_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (hashChallenge)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have ho : Input L (value L (.caller 0 0)) (value L (.const 32)) := by
    change Input L (L.out + 0#32) 32#32
    rw [BitVec.add_zero]
    exact point_input hL
  have hk : Input L (value L (.caller 2 0)) (value L (.const 32)) := by
    change Input L (L.pk + 0#32) 32#32
    rw [BitVec.add_zero]
    exact key_input hL
  have hm : Input L (value L (.caller 3 0)) (value L (.caller 4 0)) := by
    change Input L (L.msg + 0#32) (L.len + 0#32)
    rw [BitVec.add_zero, BitVec.add_zero]
    exact message_input hL
  exact (init_ct hL ha hb).seq ((update_ct hL ha hb 0 (.caller 0 0) (.const 32)
    (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) ho).seq
    ((update_ct hL ha hb 32 (.caller 2 0) (.const 32)
      (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hk).seq
      ((update_ct hL ha hb 64 (.caller 3 0) (.caller 4 0)
        (by decide) (by simp [Whole.valid]) (by simp [Whole.valid]) hm).seq
        (finalize_ct hL ha hb 64 (by decide) true))))

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.CTPrimitives`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem reduce_call_ct (hL : L.Ok) (d : Nat) (hd : d + 32 ≤ 184) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L [(.r0, .frame d), (.r1, .frame 184), (.r2, .caller 5 0)] []))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.Arm.scalarReduce)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarReduce_ok scalarReduce_ct reduce_noFrames
  · intro g m t hc hs
    have a0 := hs.1 (.r0, .frame d) (by simp)
    have a1 := hs.1 (.r1, .frame 184) (by simp)
    have a2 := hs.1 (.r2, .caller 5 0) (by simp)
    change t.gpr .r2 = L.scr + 0#32 at a2
    rw [BitVec.add_zero] at a2
    exact reduce_ready hL hd ⟨a0, a1, a2⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.r0, .frame d)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r1, .frame 184)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r2, .caller 5 0)) h (by simp) (by simp [linkRegs])⟩

/-- What the call of `vg_ed25519_scalar_base` needs: its arguments, and the tables' address and
words. -/
def BaseReady (L : Lay) (t : State) : Prop :=
  AllArgs L [(.r0, .caller 0 0), (.r1, .frame 88), (.r2, .caller 5 0)] [] t ∧
    t.syms VG.Impl.Ed25519.Arm.combSym = L.T ∧ Tbl L t.mem

theorem base_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (BaseReady L))
      (.call "vg_ed25519_scalar_base" Impl.Ed25519.Arm.scalarBase)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarBase_ok scalarBase_ct base_noFrames
  · intro g m t hc hs
    have a0 := hs.1.1 (.r0, .caller 0 0) (by simp)
    change t.gpr .r0 = L.out + 0#32 at a0
    rw [BitVec.add_zero] at a0
    have a1 := hs.1.1 (.r1, .frame 88) (by simp)
    have a2 := hs.1.1 (.r2, .caller 5 0) (by simp)
    change t.gpr .r2 = L.scr + 0#32 at a2
    rw [BitVec.add_zero] at a2
    exact base_ready hL ⟨a0, a1, a2⟩ hs.2.1 hs.2.2
  · intro a b ar aw br bw h
    have h' : Two L g₁ g₂ m₁ m₂ (AllArgs L [(.r0, .caller 0 0), (.r1, .frame 88), (.r2, .caller 5 0)] []) a b :=
      ⟨h.1, h.2.1, h.2.2.1.1, h.2.2.2.1⟩
    have hsp := two_sp h'
    exact ⟨hsp, call_gpr_eq (p := (.r0, .caller 0 0)) h' (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r1, .frame 88)) h' (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r2, .caller 5 0)) h' (by simp) (by simp [linkRegs]),
      h.2.2.1.2.1.trans h.2.2.2.2.1.symm⟩

theorem mul_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L [(.r0, .caller 0 32), (.r1, .frame 88), (.r2, .frame 120), (.r3, .frame 24)] [.caller 5 0]))
      (.call "vg_ed25519_scalar_mul_add" Impl.Ed25519.Arm.scalarMulAdd)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarMulAdd_ok scalarMulAdd_ct mul_noFrames
  · intro g m t hc hs
    have a0 := hs.1 (.r0, .caller 0 32) (by simp)
    have a1 := hs.1 (.r1, .frame 88) (by simp)
    have a2 := hs.1 (.r2, .frame 120) (by simp)
    have a3 := hs.1 (.r3, .frame 24) (by simp)
    have a4 := hs.2 0 (by decide)
    change stackArg t 0 = L.scr + 0#32 at a4
    rw [BitVec.add_zero] at a4
    exact mul_ready hc hL ⟨a0, a1, a2, a3, a4⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.r0, .caller 0 32)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r1, .frame 88)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r2, .frame 120)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r3, .frame 24)) h (by simp) (by simp [linkRegs]),
      stack_arg_eq h (j := 0) (by decide)⟩

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.CTBlocks`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem copyWord_ct (k : Nat) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (copyWord k)) (fun a b => a.sp = b.sp) :=
  Whole.step_sp_ct (fun _ _ h => by simp only [addrs,h]) (Whole.frame_store_ct 0 (56+4*k) .r0)

theorem copyPrefix_ct :
    RelCT isa (fun a b => a.sp = b.sp) (.block copyPrefix) (fun a b => a.sp = b.sp) :=
  Whole.flatMap_sp_ct _ _ (fun _ _ => copyWord_ct _)

theorem saveSecret_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block saveSecret)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have ct := Whole.block_append_ct PublicKey.prune_sp_ct copyPrefix_ct
  refine two_wp (ct.mono (fun _ _ h => two_sp h) (fun _ _ _ => True.intro)) ?_ ?_
  · intro t hc _
    exact WP.mono (saveSecret_ok hc hL rfl) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (saveSecret_ok hc hL rfl) fun _ h => ⟨h.1, trivial⟩

theorem wipe_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block wipe)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine two_wp ((Whole.zeroWords_ct 6 56).mono (fun _ _ h => two_sp h) (fun _ _ _ => True.intro)) ?_ ?_
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩

end VG.Proof.Ed25519.Arm.SignCached
end

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem reduce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (d : Nat) (hd : d + 32 ≤ 184) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (reduce d)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hv : Whole.valid (.frame d) := by change d < 256; omega
  have hvall : ∀ p : Reg × Value, p ∈ [(.r0, .frame d), (.r1, .frame 184), (.r2, .caller 5 0)] → Whole.valid p.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    · exact hv
    · simp [Whole.valid]
    · simp [Whole.valid]
  exact (setup_ct hL ha hb _ [] (by simp) hvall (by decide) (by simp) (by simp [preserved])).seq
    (reduce_call_ct hL d hd)

theorem base_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (hw₁ : Tbl L m₁)
    (hw₂ : Tbl L m₂) :
    RelCT isa (fun a b => Two L g₁ g₂ m₁ m₂ (fun _ => True) a b ∧
        a.syms VG.Impl.Ed25519.Arm.combSym = L.T ∧ b.syms VG.Impl.Ed25519.Arm.combSym = L.T)
      (callWith baseArgs "vg_ed25519_scalar_base" Impl.Ed25519.Arm.scalarBase)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (Whole.keepSym VG.Impl.Ed25519.Arm.combSym L.T (setup_ct hL ha hb
    [(.r0, .caller 0 0), (.r1, .frame 88), (.r2, .caller 5 0)] []
    (by decide) (by simp [Whole.valid]) (by decide) (by simp [Whole.valid]) (by simp [preserved]))).seq
    ((base_call_ct hL).mono (fun a b ⟨⟨hca, hcb, hsa, hsb⟩, ya, yb⟩ =>
      ⟨hca, hcb, ⟨hsa, ya, hca.tbl hL hw₁⟩, ⟨hsb, yb, hcb.tbl hL hw₂⟩⟩) fun _ _ h => h)

theorem mul_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True)
      (callWith mulAddArgs "vg_ed25519_scalar_mul_add" Impl.Ed25519.Arm.scalarMulAdd)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [(.r0, .caller 0 32), (.r1, .frame 88), (.r2, .frame 120),
    (.r3, .frame 24)] [.caller 5 0]
    (by decide) (by simp [Whole.valid]) (by decide) (by simp [Whole.valid]) (by simp [preserved])).seq
    (mul_call_ct hL)

theorem body_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (hw₁ : Tbl L m₁)
    (hw₂ : Tbl L m₂) :
    RelCT isa (fun a b => Two L g₁ g₂ m₁ m₂ (fun _ => True) a b ∧
        a.syms VG.Impl.Ed25519.Arm.combSym = L.T ∧ b.syms VG.Impl.Ed25519.Arm.combSym = L.T) body
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (Whole.keepSym VG.Impl.Ed25519.Arm.combSym L.T ((hashSeed_ct hL ha hb).seq (saveSecret_ct hL))).seq
    (((Whole.keepSym VG.Impl.Ed25519.Arm.combSym L.T (hashNonce_ct hL ha hb)).seq
      ((Whole.keepSym VG.Impl.Ed25519.Arm.combSym L.T (reduce_ct hL ha hb 88 (by decide))).seq
      (base_ct hL ha hb hw₁ hw₂))).seq
      (((hashChallenge_ct hL ha hb).seq ((reduce_ct hL ha hb 120 (by decide)).seq
        (mul_ct hL ha hb))).seq (wipe_ct hL)))

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.Entry`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm

/-- The contract under the plain calling convention, without the tables. -/
def signCachedAbi : Contract isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 64⟩
    let seed : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let pk : Region := ⟨State.addr (s.gpr .r2), 32⟩
    let msg : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 8192⟩
    let args : Region := ⟨State.addr s.sp,8⟩
    let stk : Region := ⟨State.addr s.sp - 280,280⟩
    s.rd = [seed, pk, msg, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint msg ∧ out.Disjoint args ∧ out.Disjoint scr ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ msg.Disjoint scr ∧ args.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint scr ∧
      (s.gpr .r0).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧
      (stackArg s 1).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
      Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32)
  post s t := Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r0)) 64 = Spec.Ed25519.sign
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32)
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧
    s.gpr .r2 = t.gpr .r2 ∧ s.gpr .r3 = t.gpr .r3 ∧ stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1


def signCachedLocal : Contract isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 64⟩
    let seed : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let pk : Region := ⟨State.addr (s.gpr .r2), 32⟩
    let msg : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 8192⟩
    let args : Region := ⟨State.addr s.sp,8⟩
    let stk : Region := ⟨State.addr s.sp - 280,280⟩
    let tb : Region := TBL (s.syms VG.Impl.Ed25519.Arm.combSym)
    s.rd = [seed, pk, msg, args, tb] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint msg ∧ out.Disjoint args ∧ out.Disjoint scr ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ msg.Disjoint scr ∧ args.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint scr ∧
      (s.gpr .r0).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧
      (stackArg s 1).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
      Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32) ∧
      (s.syms VG.Impl.Ed25519.Arm.combSym).toNat + 98304 ≤ 2 ^ 32 ∧
      (∀ j < 64 * 192, s.mem.readW (State.addr (s.syms VG.Impl.Ed25519.Arm.combSym) +
        BitVec.ofNat 64 (8 * j)) 64 = VG.Impl.Ed25519.Arm.combWord j) ∧
      tb.Disjoint out ∧ tb.Disjoint scr ∧ tb.Disjoint stk
  post s t := Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r0)) 64 = Spec.Ed25519.sign
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32)
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧
    s.gpr .r2 = t.gpr .r2 ∧ s.gpr .r3 = t.gpr .r3 ∧ stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1 ∧
    s.syms VG.Impl.Ed25519.Arm.combSym = t.syms VG.Impl.Ed25519.Arm.combSym

def lay (s : State) : Lay :=
  ⟨s.gpr .r0, s.gpr .r1, s.gpr .r2, s.gpr .r3, stackArg s 0, stackArg s 1, Whole.base s,
    s.syms VG.Impl.Ed25519.Arm.combSym⟩

theorem entry_below {s : State} (h : signCachedLocal.pre s) : 280 ≤ s.sp.toNat := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, _, _⟩ := h
  exact hb

theorem entry_top {s : State} (h : signCachedLocal.pre s) : s.sp.toNat + 8 ≤ 2 ^ 32 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _⟩ := h
  exact ht

theorem original_args {s : State} (hb : 280 ≤ s.sp.toNat) :
    (lay s).ORIGINALARGS = ⟨State.addr s.sp,8⟩ := by
  unfold Lay.ORIGINALARGS lay
  rw [Whole.base_addr hb]
  change (⟨State.addr s.sp - 280 + 280,8⟩ : Region) = _
  rw [BitVec.sub_add_cancel]

theorem stack_eq {s : State} (hb : 280 ≤ s.sp.toNat) :
    Whole.stack s = ⟨State.addr s.sp-280,280⟩ := by
  unfold Whole.stack
  rw [Whole.base_addr hb]

theorem entry_writes {s : State} (h : signCachedLocal.pre s) :
    ∀ r ∈ s.wr, (Whole.stack s).Disjoint r := by
  have hb := entry_below h
  obtain ⟨_, hw, _, _, _, _, _, _, _, _, _, ko, _, _, _, kc, _⟩ := h
  intro r hr
  rw [hw] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [stack_eq hb]
  rcases hr with rfl | rfl
  · exact ko
  · exact kc

theorem lay_ok {s : State} (h : signCachedLocal.pre s) : (lay s).Ok := by
  obtain ⟨_, _, os, op, om, oa, oc, sc, pc, mc, ac, ko, ks, kp, km, kc, no, ns, np, nm, nc, hb, _, _,
    tf, _, tout, tscr, tstk⟩ := h
  have fr : Region.Sub (Whole.FR (Whole.base s)) (Whole.stack s) := Region.sub_prefix (by decide)
  have ar : Region.Sub (Whole.ARGS (Whole.base s)) (Whole.stack s) := Offset.sub_base _ (by decide)
  rw [← stack_eq hb] at ko ks kp km kc tstk
  refine ⟨?_, ?_, oc, ko.sub_left fr, no, ?_, ?_, kc.sub_left fr, np, nm, ns, nc, tf⟩
  · have he := Whole.base_top (s := s) hb
    have hs := s.sp.isLt
    change (Whole.base s).toNat + 272 ≤ 2 ^ 32
    omega
  · simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact os
    · exact op
    · exact om
    · rw [original_args hb]; exact oa
    · exact tout.symm
    · exact (ko.sub_left ar).symm
  · simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact sc
    · exact pc
    · exact mc
    · rw [original_args hb]; exact ac
    · exact tscr
    · exact kc.sub_left ar
  · simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ks.sub_left fr
    · exact kp.sub_left fr
    · exact km.sub_left fr
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact tstk.symm.sub_left fr
    · exact Offset.base_disjoint _ (by decide) (by decide)

theorem entry_ctx {s p : State} (h : signCachedLocal.pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    Ctx (lay s) s.gpr p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  change Whole.Ctx (Whole.base s) s.gpr p.mem (lay s).inputs (lay s).outputs _
  simp only [Lay.inputs, original_args (entry_below h)]
  simpa only [Whole.bodyRd, h.1, Whole.bodyWr, h.2.1, Lay.outputs,
    Lay.SEED, Lay.PK, Lay.MSG, Lay.OUT, Lay.SCR, Lay.ARGS, Lay.TB, Whole.ARGS, show BitVec.ofNat 64 248 = (248 : Addr) from rfl, lay,
    List.cons_append, List.nil_append] using hc

theorem entry_regions {s : State} (h : signCachedLocal.pre s) :
    (lay s).inputs = Whole.bodyRd s ∧ (lay s).outputs = s.wr := by
  simp only [Lay.inputs, original_args (entry_below h)]
  simp only [Whole.bodyRd, h.1, Lay.outputs, h.2.1,
    Lay.SEED, Lay.PK, Lay.MSG, Lay.OUT, Lay.SCR, Lay.ARGS, Lay.TB, Whole.ARGS,
    show BitVec.ofNat 64 248 = (248 : Addr) from rfl, lay, List.cons_append, List.nil_append]
  exact ⟨trivial, trivial⟩

theorem entry_args {s p : State} (h : signCachedLocal.pre s)
    (hp : Whole.Saved (Whole.entered s) 6 p) : Arguments (lay s) p.mem := by
  intro j hj
  have hw := Whole.saved_words (entry_below h) (by decide : 6 ≤ 6) (entry_top h) hp hj
  have he : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simpa only [Whole.originalWord, Impl.Ed25519.Arm.Whole.argReg, Nat.reduceLT, ite_true, ite_false,
      Nat.reduceSub, Nat.mul_zero, BitVec.add_zero, Lay.value, lay,
      stackArg, stackArgAddr] using hw

theorem entry_read {s : State} (h : signCachedLocal.pre s) : ∀ j < 6, 4 ≤ j →
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4*(j-4)))) 4 := by
  intro j hj h4
  have ht := entry_top h
  rw [addr_add (by omega)]
  exact ⟨⟨State.addr s.sp,8⟩, List.mem_append_left _ (by rw [h.1]; simp),
    Offset.contains_base _ (by omega) (by omega)⟩

theorem entry_input {s : State} (h : signCachedLocal.pre s) {m : Mem}
    (hf : Frame [Whole.stack s] s.mem m) {r : Region} (hr : r ∈ s.rd) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt m r.base r.len = Spec.Ed25519.bytesAt s.mem r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes ?_ hn (List.mem_range.mp hi)
  rintro R hR
  rw [List.mem_singleton.mp hR]
  have hb := entry_below h
  obtain ⟨hrd, _, _, _, _, _, _, _, _, _, _, _, ks, kp, km, _, _, _, _, _, _, _, _, _, _, _, _, _, tstk⟩ := h
  rw [hrd] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [← stack_eq hb] at ks kp km tstk
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ks.symm
  · exact kp.symm
  · exact km.symm
  · rw [← original_args hb]
    exact (Offset.base_disjoint _ (by decide) (by decide)).symm
  · exact tstk

theorem entry_key {s p : State} (h : signCachedLocal.pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    Spec.Ed25519.bytesAt p.mem (State.addr (lay s).pk) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt p.mem (State.addr (lay s).seed) 32) := by
  have hk : Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, _⟩ := h
    exact hk
  have hf := Whole.saved_frame (entry_below h) hp
  have hp' := entry_input h hf (r := ⟨State.addr (s.gpr .r2), 32⟩) (by rw [h.1]; simp) (by change 32 ≤ 2 ^ 64; decide)
  have hs' := entry_input h hf (r := ⟨State.addr (s.gpr .r1), 32⟩) (by rw [h.1]; simp) (by change 32 ≤ 2 ^ 64; decide)
  change Spec.Ed25519.bytesAt p.mem (State.addr (s.gpr .r2)) 32 =
    Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt p.mem (State.addr (s.gpr .r1)) 32)
  rw [hp', hs']
  exact hk

/-- The tables at the body's entry. -/
theorem entry_tbl {s p : State} (h : signCachedLocal.pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    Tbl (lay s) p.mem := fun j hj => by
  have hb := entry_below h
  have hf := Whole.saved_frame hb hp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hw, _, _, tstk⟩ := h
  rw [← hw j hj]
  refine hf.readW (r := TBL (s.syms VG.Impl.Ed25519.Arm.combSym))
    (Offset.contains_base _ (by omega) (by omega)) ?_ (by decide)
  intro r hr
  rw [List.mem_singleton.mp hr, stack_eq hb]
  exact tstk

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.CT`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached

theorem lay_eq {s t : State} (hp : signCachedLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2, h3, h4, h5, hy⟩ := hp
  simp only [lay, Whole.base, sp, h0, h1, h2, h3, h4, h5, hy]

theorem signCached_ct :
    ConstantTime isa signCachedLocal.pre signCachedLocal.pub code := by
  refine Whole.wrap_ct (by decide) (fun _ _ hp => hp.1)
    (fun _ h => entry_below h) (fun _ h => entry_top h) (fun _ h => entry_read h) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok (entry_ctx hs hp) (lay_ok hs) (entry_args hs hp) (entry_key hs hp)
      (entry_tbl hs hp) (congrFun hp.step.syms _)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args ht hqb
    have hqw : Tbl (lay s) q.mem := he ▸ entry_tbl ht hqb
    have hqy : (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)).syms VG.Impl.Ed25519.Arm.combSym =
        (lay s).T := (congrFun hqb.step.syms _).trans hp.2.2.2.2.2.2.2.symm
    exact ⟨(body_ct (lay_ok hs) (entry_args hs hpa) hqa (entry_tbl hs hpa) hqw _ _ _ _ _ _
      ⟨⟨entry_ctx hs hpa, hq, trivial, trivial⟩, congrFun hpa.step.syms _, hqy⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.Correct`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached

theorem body_noFrames : body.noFrames = true := by
  simp only [body, secretCode, nonceCode, challengeCode, hashSeed, hashNonce, hashChallenge,
    init, update, finalize, reduce, Impl.Ed25519.Arm.Whole.callWith, Code.noFrames,
    Impl.Sha512.Arm.Stream.init, Bool.and_self]
  rw [reduce_noFrames, base_noFrames, mul_noFrames]
  rfl

theorem signCached_ok {s : State} (h : signCachedLocal.pre s) :
    WP isa code s fun u => abiPreserved s u ∧ signCachedLocal.post s u := by
  have hw := Whole.wrap_ok body_noFrames (by decide : 6 ≤ 6) (entry_below h) (entry_top h) (entry_read h) (entry_writes h)
    (P := fun m m' _ => Spec.Ed25519.bytesAt m' (State.addr (s.gpr .r0)) 64 = Spec.Ed25519.sign
      (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r1)) 32)
      (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r3)) (stackArg s 0).toNat))
    (fun p hp => WP.mono (body_ok (entry_ctx h hp) (lay_ok h) (entry_args h hp) (entry_key h hp)
      (entry_tbl h hp) (congrFun hp.step.syms _))
      fun u ⟨hu, ho⟩ => ⟨by
        change Whole.Ctx (Whole.base s) s.gpr p.mem (lay s).inputs (lay s).outputs u at hu
        rw [(entry_regions h).1, (entry_regions h).2] at hu
        exact hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have hs := entry_input h hf (r := ⟨State.addr (s.gpr .r1), 32⟩) (by rw [h.1]; simp) (by change 32 ≤ 2 ^ 64; decide)
  have hm := entry_input h hf (r := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩) (by rw [h.1]; simp)
    (by have := (stackArg s 0).isLt; change (stackArg s 0).toNat ≤ 2 ^ 64; omega)
  change Spec.Ed25519.bytesAt u.mem (State.addr (s.gpr .r0)) 64 = _
  rw [hp, hs, hm]

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.Contract`. -/
section
/-! Merged from `Proof.Ed25519.Arm.SignCached.Sat`. -/
section
/-! A satisfiability witness with a matching seed and cached public key. -/
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm

def satSeed : List Byte := Spec.Ed25519.bytesAt (fun _ => 0) 0x2000 32
def satKey : List Byte := Spec.Ed25519.publicKey satSeed

theorem satKey_length : satKey.length = 32 := by
  simp only [satKey, Spec.Ed25519.publicKey, Spec.Ed25519.encodePoint, Spec.Ed25519.encodeLE,
    List.length_map, List.length_range]

def satMem (a : Addr) : Byte :=
  if a.toNat < 0x3000 then 0 else if a.toNat < 0x3020 then satKey[a.toNat - 0x3000]?.getD 0
  else if a = 0x9005 then 0x50 else 0

theorem sat_seed : Spec.Ed25519.bytesAt satMem 0x2000 32 = satSeed := by
  unfold satSeed Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  unfold satMem
  rw [ha]
  simp only [show 0x2000 + i < 0x3000 from by omega, ite_true]

theorem sat_key : Spec.Ed25519.bytesAt satMem 0x3000 32 = satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satKey_length]
  · intro i hi hj
    have hi' : i < 32 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, satMem, ha,
      show ¬ 0x3000 + i < 0x3000 from by omega, ite_false, show 0x3000 + i < 0x3020 from by omega, ite_true, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem := satMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 0⟩, ⟨0x9000, 8⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x5000, 8192⟩]

theorem sat : ∃ s, (Spec.Ed25519.signCachedContract Arm.abi 280).pre s := by
  refine ⟨satState, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, satState]
    sig_and_intros
    · decide +kernel
    · decide +kernel
    · change Spec.Ed25519.bytesAt satMem 0x3000 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt satMem 0x2000 32)
      rw [sat_seed, sat_key]
      rfl

end VG.Proof.Ed25519.Arm.SignCached
end

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm

theorem signCachedAbi_implies : signCachedAbi.Implies (Spec.Ed25519.signCachedContract Arm.abi 280) where
  pre := by
    intro s h
    sig_pre [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signCachedAbi, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Arm.stackArg, Arm.stackArgAddr] at h
    sig_split h
    sig_reduce [signCachedAbi, Arm.State.addr, Arm.stackArg, Arm.stackArgAddr]
    sig_simp [] []
    simp only [BitVec.add_zero, show (280#64) = (280 : Addr) from rfl] at *
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signCachedAbi, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Arm.stackArg, Arm.stackArgAddr]
  pub := by
    sig_implies_pub [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signCachedAbi, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Arm.stackArg, Arm.stackArgAddr]
  sat := sat


abbrev signSpec : Contract isa :=
  Spec.Ed25519.signCachedContract (Arm.abi.withConsts VG.Impl.Ed25519.Arm.combConsts) 280

theorem signCached_pre {s : State} (h : signSpec.pre s) : signCachedLocal.pre s := by
  have hp : (Spec.Ed25519.signCachedContract Arm.abi 280).pre (stripConsts VG.Impl.Ed25519.Arm.combConsts s) ∧
      ConstsOk VG.Impl.Ed25519.Arm.combConsts 280 s := pre_consts.mp h
  obtain ⟨rd, wr, os, op, om, oa, oc, sc, pc, mc, ac, ko, ks, kp, km, kc, no, ns, np, nm, nc, hb, ht, hk⟩ :=
    signCachedAbi_implies.pre _ hp.1
  have hk' := hp.2
  have mem : (VG.Impl.Ed25519.Arm.combSym, VG.Impl.Ed25519.Arm.combWords) ∈
      VG.Impl.Ed25519.Arm.combConsts := List.mem_singleton_self _
  have fit := hk'.fit mem
  rw [combWords_length] at fit
  have tr := hk'.2.2.1 _ (by rw [combConsts_regs]; exact List.mem_singleton_self _)
  refine ⟨?_, wr, os, op, om, oa, oc, sc, pc, mc, ac, ko, ks, kp, km, kc, no, ns, np, nm, nc, hb, ht, hk,
    fit, fun j hj => ?_, tr.2.1 _ (by rw [show s.wr = _ from wr]; exact List.mem_cons_self),
    tr.2.1 _ (by rw [show s.wr = _ from wr]; exact List.mem_cons_of_mem _ List.mem_cons_self),
    tr.2.2 _ (by simp [Arm.abi, stackBelow])⟩
  · have e1 := hk'.1
    rw [combConsts_regs] at e1
    have hl : VG.Impl.Ed25519.Arm.combConsts.length = 1 := rfl
    rw [hl] at e1
    change List.take (s.rd.length - VG.Impl.Ed25519.Arm.combConsts.length) s.rd = _ at rd
    rw [hl] at rd
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, e1, rd]
    rfl
  · have hw := hk'.2.1 _ mem j (by rw [combWords_length]; exact hj)
    dsimp only at hw
    rw [combWords_getD hj] at hw
    exact hw

/-- The witness's memory: `satMem` below the tables, the tables from `0x100000`. -/
def satMemT (a : Addr) : Byte := if a.toNat < 0x100000 then satMem a else baseSatMem a

theorem satMemT_frame : Frame [⟨0, 0x100000⟩] baseSatMem satMemT := by
  intro x hx
  have hn := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hn
  rw [show (x - 0 : Addr) = x from by simp] at hn
  simp only [satMemT, show ¬ x.toNat < 0x100000 by omega, ↓reduceIte]

def satStateT : State :=
  { satState with mem := satMemT, rd := satState.rd ++ [⟨0x100000, 98304⟩], syms := fun _ => 0x100000 }

theorem satT_held : ∀ i < 64 * 192,
    satStateT.mem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = VG.Impl.Ed25519.Arm.combWords.getD i 0 := by
  intro i hi
  rw [← baseSatMem_held i (by rw [combWords_length]; exact hi)]
  refine satMemT_frame.readW (r := ⟨0x100000 + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
    ?_ (by decide)
  intro r hr
  rw [List.mem_singleton.mp hr]
  have e : (0x100000 + BitVec.ofNat 64 (8 * i) : Addr).toNat = 0x100000 + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    change (0x100000 + 8 * i % 2 ^ 64) % 2 ^ 64 = _
    omega
  refine (Offset.disjoint_of_le (r₁ := ⟨0, 0x100000⟩) ?_ ?_).symm
  · change 0 + 0x100000 ≤ (0x100000 + BitVec.ofNat 64 (8 * i) : Addr).toNat
    omega
  · change (0x100000 + BitVec.ofNat 64 (8 * i) : Addr).toNat + 8 ≤ 2 ^ 64
    omega

theorem satT_bytes {p : Addr} (h : p.toNat + 32 ≤ 0x100000) :
    Spec.Ed25519.bytesAt satMemT p 32 = Spec.Ed25519.bytesAt satMem p 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have e : (p + BitVec.ofNat 64 i).toNat = p.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  simp only [satMemT, e, show p.toNat + i < 0x100000 by omega, ↓reduceIte]

theorem satT_key : Spec.Ed25519.bytesAt satMemT 0x3000 32 =
    Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt satMemT 0x2000 32) := by
  rw [satT_bytes (by decide), satT_bytes (by decide), sat_seed, sat_key]
  rfl

theorem signCached_sat : signSpec.pre satStateT := by
  have held := satT_held
  generalize eqs : satStateT = s
  sig_pre [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
    Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr,
    Arm.stackArg, Arm.stackArgAddr, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  rw [combWords_length]
  refine ⟨by decide, by decide, by decide, held, by decide, ?_, Region.disjoint_of_sep (by decide), by decide, ?_⟩
  · intro r hr
    change r ∈ [⟨0x1000, 64⟩, ⟨0x5000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · sig_and_intros
    rotate_right
    · change Spec.Ed25519.bytesAt satMemT 0x3000 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt satMemT 0x2000 32)
      exact satT_key
    all_goals first | exact Region.disjoint_of_sep (by decide +kernel) | decide +kernel

theorem signCached_implies : signCachedLocal.Implies signSpec where
  pre _ h := signCached_pre h
  post := by
    intro s s' _ h
    sig_post [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig, Spec.Ed25519.scratchWords,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArg, Arm.stackArgAddr,
      combConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig, Spec.Ed25519.scratchWords,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArg, Arm.stackArgAddr,
      combConsts_eq, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2, h3, a0, a1⟩ := h
    exact ⟨hsp, h0, h1, h2, h3, a0, a1, hsy⟩
  sat := ⟨satStateT, signCached_sat⟩

end VG.Proof.Ed25519.Arm.SignCached
end

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached

theorem signCached_verified :
    Verified Arm.target code signSpec :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => signCached_ok h) signCached_ct (.refl signCached_implies.sat_left))
    signCached_implies

end VG.Proof.Ed25519.Arm.SignCached
