module

public import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wrap
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed448.Arm.ScalarLit
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Ed448.Arm.Shake.CT
import Mathlib.Logic.Function.Basic
public import VerifiedGarbage.Proof.Ed448.Arm.Verify.Hash
public import VerifiedGarbage.Proof.Ed448.Arm.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.BlocksCT
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Ed448.Arm.VerifyLocal
public import VerifiedGarbage.Impl.Ed448.Arm.Verify
import VerifiedGarbage.Proof.Ed448.Arm.VerifyLit
import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Hash
import VerifiedGarbage.Proof.Framework.NativeTaintCore

/-! ### `Ed448.Arm.Verify.Body`, which only this module used -/

section

/-!
# Ed448 verification on ARMv7: the challenge, the equation, and the body

`reduce_step`: `k`, the hash reduced modulo `L` by `vg_ed448_scalar_reduce`,
in the frame at `K`. `equation_step`: `vg_ed448_verify_equation`'s result,
for any code meeting its contract (`EqOk`, a hypothesis: only the
registration file imports the proof). `body_ok`: the whole body.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm.Verify

open VG.Proof.Ed448.Arm.Shake (Slot valid)

open VG VG.Arm VG.Impl.Ed448.Arm.Verify VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.Within Whole.FR Whole.call_ok)
open VG.Proof.Ed448.Arm (verifyEquationLocal scalarReduceLocal scalarReduce_ok)

variable {fv : Bool}

/-- `vg_ed448_verify_equation` meets its contract. -/
abbrev EqOk (fv : Bool) : Prop := ∀ s, verifyEquationLocal.pre s →
  ∃ tr s', Exec isa (Impl.Ed448.Arm.verifyEquation fv) s tr s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s'

/-- `vg_ed448_verify_equation` is constant time under its contract. -/
abbrev EqCT (fv : Bool) : Prop :=
  ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub (Impl.Ed448.Arm.verifyEquation fv)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

/-! ## `vg_ed448_scalar_reduce` -/

theorem reduce_noFrames : Impl.Ed448.Arm.scalarReduce.noFrames = true := by lit_decide
theorem equation_noFrames : (Impl.Ed448.Arm.verifyEquation fv).noFrames = true := by
  cases fv <;> lit_decide

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

theorem equation_step (hv : EqOk fv) (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith equationArgs ("vg_ed448_verify_equation" ++ Impl.X448.Arm.suffix fv)
        (Impl.Ed448.Arm.verifyEquation fv)) t fun u =>
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
theorem body_ok (hv : EqOk fv) (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (body fv) t fun u => Ctx L g m₀ u ∧ u.gpr .r0 = signWord (Spec.Ed448.verify
      (Spec.Ed448.bytesAt m₀ (State.addr L.pk) 57)
      (Spec.Ed448.bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat)
      (Spec.Ed448.bytesAt m₀ (State.addr L.msg) L.len.toNat)
      (Spec.Ed448.bytesAt m₀ (State.addr L.sig) 114)) := by
  refine WP.seq (WP.mono (hdr_ok hc hL ha) fun t1 ⟨hc1, hh⟩ => ?_)
  refine WP.seq (WP.mono (hash_ok hc1 hL ha hh) fun t2 ⟨hc2, hh2⟩ => ?_)
  refine WP.seq (WP.mono (reduce_step hc2 hL ha) fun t3 ⟨hc3, hk⟩ => ?_)
  refine WP.mono (equation_step hv hc3 hL ha) fun u ⟨hu, hr⟩ => ⟨hu, ?_⟩
  have hl : (Spec.Ed448.bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat).length ≤ 255 := by
    simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range]; have := hL.cl; omega_using [this]
  rw [hr, hk, hh2, verify_of_len hl, take57]

theorem body_noFrames : (body fv).noFrames = true := by
  simp only [Impl.Ed448.Arm.Verify.body, Impl.Ed448.Arm.Verify.hash, Impl.Ed448.Arm.Shake.zeroState,
    Impl.Ed448.Arm.Shake.absorb, Impl.Ed448.Arm.Shake.pad, Impl.Ed448.Arm.Shake.squeeze, callWith,
    Code.noFrames, Bool.and_self]
  rw [PublicKey.absorb_noFrames, PublicKey.pad_noFrames, PublicKey.squeeze_noFrames, reduce_noFrames,
    equation_noFrames]
  rfl

end VG.Proof.Ed448.Arm.Verify

end

end

/-! ### `Ed448.Arm.Verify.Entry`, which only this module used -/

section

/-!
# Ed448 verification on ARMv7: the contract, and the frame

`verifyLocal`, the contract the proof is written against; `inner_ok`, the
frame (`Whole.wrap_ok`) around the body for a context of fewer than 256
bytes; `verify_ok`, the whole function, with the check of the context's
length before it.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm.Verify

open VG VG.Arm VG.Impl.Ed448.Arm.Verify VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.base Whole.base_addr Whole.base_top Whole.stack Whole.Saved Whole.entered
  Whole.saved_ctx Whole.saved_words Whole.saved_frame Whole.bodyRd Whole.bodyWr Whole.wrap_ok
  Whole.originalWord Whole.Ctx)
open VG.Proof.X25519.Arm (op2_lsr op2_imm)

variable {fv : Bool}

/-- `vg_ed448_verify(pk = r0, context = r1, ctxlen = r2, message = r3, len = [sp],
signature = [sp, #4], scratch = [sp, #8]) -> r0`, with 280 bytes of stack. -/
def verifyLocal : Contract isa where
  pre s :=
    let pk : Region := ⟨State.addr (s.gpr .r0), 57⟩
    let ctx : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
    let msg : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let sig : Region := ⟨State.addr (stackArg s 1), 114⟩
    let scr : Region := ⟨State.addr (stackArg s 2), 8192⟩
    let args : Region := ⟨State.addr s.sp, 12⟩
    let stk : Region := ⟨State.addr s.sp - 280, 280⟩
    s.rd = [pk, ctx, msg, sig, args] ∧ s.wr = [scr] ∧
      pk.Disjoint scr ∧ ctx.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧ args.Disjoint scr ∧
      stk.Disjoint pk ∧ stk.Disjoint ctx ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      (s.gpr .r0).toNat + 57 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 114 ≤ 2 ^ 32 ∧
      (stackArg s 2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32
  post s t := t.gpr .r0 = signWord (Spec.Ed448.verify
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r0)) 57)
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
    (Spec.Ed448.bytesAt s.mem (State.addr (stackArg s 1)) 114))
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 ∧
    s.gpr .r3 = t.gpr .r3 ∧ stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1 ∧
    stackArg s 2 = stackArg t 2 ∧
    Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r0)) 57 =
      Spec.Ed448.bytesAt t.mem (State.addr (t.gpr .r0)) 57 ∧
    Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
      Spec.Ed448.bytesAt t.mem (State.addr (t.gpr .r1)) (t.gpr .r2).toNat ∧
    Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat =
      Spec.Ed448.bytesAt t.mem (State.addr (t.gpr .r3)) (stackArg t 0).toNat ∧
    Spec.Ed448.bytesAt s.mem (State.addr (stackArg s 1)) 114 =
      Spec.Ed448.bytesAt t.mem (State.addr (stackArg t 1)) 114

def lay (s : State) : Lay :=
  ⟨s.gpr .r0, s.gpr .r1, s.gpr .r2, s.gpr .r3, stackArg s 0, stackArg s 1, stackArg s 2, Whole.base s⟩

section
variable {s : State} (h : verifyLocal.pre s)
include h

theorem entry_below : 280 ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem entry_top : s.sp.toNat + 12 ≤ 2 ^ 32 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem original_args : (lay s).ORIG = ⟨State.addr s.sp, 12⟩ := by
  unfold Lay.ORIG lay
  rw [Whole.base_addr (entry_below h)]
  congr 1
  rw [show (280 : Addr) = BitVec.ofNat 64 280 from rfl, BitVec.sub_add_cancel]

theorem stack_eq : Whole.stack s = ⟨State.addr s.sp - 280, 280⟩ := by
  unfold Whole.stack
  rw [Whole.base_addr (entry_below h)]

theorem entry_writes : ∀ r ∈ s.wr, (Whole.stack s).Disjoint r := by
  intro r hr
  rw [h.2.1, List.mem_singleton] at hr
  subst r
  rw [stack_eq h]
  exact h.2.2.2.2.2.2.2.2.2.2.2.1

theorem lay_ok (hl : (s.gpr .r2).toNat < 256) : (lay s).Ok := by
  have hb := entry_below h
  have ht := entry_top h
  have ho := original_args h
  have hs : (lay s).STK = ⟨State.addr s.sp - 280, 280⟩ := by
    unfold Lay.STK; rw [show State.addr (lay s).E = State.addr (Whole.base s) from rfl, Whole.base_addr hb]
  obtain ⟨_, _, ps, xs, ms, ss, os, kp, kx, km, ks, kc, np, nx, nm, ns, nc, _, _⟩ := h
  refine ⟨?_, hl, ps, xs, ms, ss, by rw [ho]; exact os, by rw [hs]; exact kp, by rw [hs]; exact kx,
    by rw [hs]; exact km, by rw [hs]; exact ks, by rw [hs]; exact kc, np, nx, nm, ns, nc⟩
  have := Whole.base_top hb
  change (Whole.base s).toNat + 292 ≤ 2 ^ 32
  omega_using [ht, this]

theorem entry_regions : (lay s).inputs = Whole.bodyRd s ∧ (lay s).outputs = s.wr := by
  simp only [Lay.inputs, original_args h]
  simp only [Whole.bodyRd, h.1, Lay.outputs, h.2.1, Lay.PK, Lay.CTX, Lay.MSG, Lay.SIG, Lay.SCR, Lay.ARGS,
    lay, List.cons_append, List.nil_append]
  exact ⟨trivial, trivial⟩

theorem entry_ctx {p : State} (hp : Whole.Saved (Whole.entered s) 6 p) :
    Ctx (lay s) s.gpr p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  change Whole.Ctx (Whole.base s) s.gpr p.mem (lay s).inputs (lay s).outputs _
  rw [(entry_regions h).1, (entry_regions h).2]
  exact hc

theorem entry_args {p : State} (hp : Whole.Saved (Whole.entered s) 6 p) : Arguments (lay s) p.mem := by
  have hb := entry_below h
  have ht := entry_top h
  intro j hj
  obtain ⟨hj11, hj | hj⟩ := hj
  · have hw := Whole.saved_words hb (by decide : 6 ≤ 6) (by omega_using [ht]) hp hj
    have he : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega_using [hj]
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa only [Whole.originalWord, Impl.Ed25519.Arm.Whole.argReg, Nat.reduceLT, ite_true, ite_false,
        Nat.reduceSub, Nat.reduceMul, Nat.mul_zero, BitVec.add_zero, Lay.value, lay, stackArg, stackArgAddr] using hw
  · obtain rfl : j = 10 := by omega_using [hj11, hj]
    have hf := Whole.saved_frame hb hp
    have hbt := Whole.base_top hb
    have ea : State.addr (Whole.base s) + BitVec.ofNat 64 (248 + 4 * 10) = State.addr (s.sp + BitVec.ofNat 32 8) := by
      rw [addr_add (by omega_using [ht]), Whole.base_addr hb, show (248 + 4 * 10 : Nat) = 280 + 8 from rfl,
        ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, show (280 : Addr) = BitVec.ofNat 64 280 from rfl,
        BitVec.sub_add_cancel]
    change p.mem.readW (State.addr (Whole.base s) + BitVec.ofNat 64 (248 + 4 * 10)) 32 = stackArg s 2
    rw [hf.readW (r := ⟨State.addr (Whole.base s) + BitVec.ofNat 64 (248 + 4 * 10), 4⟩) (Region.contains_self _ _)
      (by
        rintro r hr
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint_base _ (by omega_using []) (by omega_using [])) (by decide), ea]
    rfl

theorem entry_read : ∀ j < 6, 4 ≤ j →
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4)))) 4 := by
  have ht := entry_top h
  intro j hj h4
  have hj' : j = 4 ∨ j = 5 := by omega_using [hj, h4]
  refine ⟨⟨State.addr s.sp, 12⟩, List.mem_append_left _ (by rw [h.1]; simp), ?_⟩
  rw [addr_add (by have := s.sp.isLt; omega_using [ht, hj])]
  exact Offset.contains_base _ (d := 4 * (j - 4)) (by omega_using [hj]) (by omega_using [hj])

theorem entry_input {m : Mem} (hf : Frame [Whole.stack s] s.mem m) {r : Region} (hr : r ∈ s.rd)
    (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt m r.base r.len = Spec.Ed448.bytesAt s.mem r.base r.len := by
  unfold Spec.Ed448.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes ?_ hn (List.mem_range.mp hi)
  rintro R hR
  rw [List.mem_singleton.mp hR, stack_eq h]
  obtain ⟨hrd, _, _, _, _, _, _, kp, kx, km, ks, _⟩ := h
  rw [hrd] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact kp.symm
  · exact kx.symm
  · exact km.symm
  · exact ks.symm
  · exact Offset.base_disjoint_below _ (n := 280) (k := 12) (by decide)

end

/-- The frame around the body, for a context of fewer than 256 bytes. -/
theorem inner_ok (hv : EqOk fv) {s : State} (h : verifyLocal.pre s) (hl : (s.gpr .r2).toNat < 256) :
    WP isa (wrap 6 (body fv)) s fun u => abiPreserved s u ∧ verifyLocal.post s u := by
  have hw := Whole.wrap_ok (body_noFrames (fv := fv)) (by decide : 6 ≤ 6) (entry_below h)
    (by have := entry_top h; omega_using [this]) (entry_read h) (entry_writes h)
    (P := fun m _ r => r = signWord (Spec.Ed448.verify
      (Spec.Ed448.bytesAt m (State.addr (s.gpr .r0)) 57)
      (Spec.Ed448.bytesAt m (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
      (Spec.Ed448.bytesAt m (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
      (Spec.Ed448.bytesAt m (State.addr (stackArg s 1)) 114)))
    (fun p hp => WP.mono (body_ok hv (entry_ctx h hp) (lay_ok h hl) (entry_args h hp))
      fun u ⟨hu, ho⟩ => ⟨by
        change Whole.Ctx (Whole.base s) s.gpr p.mem (lay s).inputs (lay s).outputs u at hu
        rw [(entry_regions h).1, (entry_regions h).2] at hu
        exact hu, ho⟩)
    (hP := fun _ _ _ _ _ hp => hp)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have e0 := entry_input h hf (r := ⟨State.addr (s.gpr .r0), 57⟩) (by rw [h.1]; simp) (by change 57 ≤ 2 ^ 64; decide)
  have e1 := entry_input h hf (r := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩) (by rw [h.1]; simp)
    (by change (s.gpr .r2).toNat ≤ 2 ^ 64; have := (s.gpr .r2).isLt; omega_using [])
  have e3 := entry_input h hf (r := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩) (by rw [h.1]; simp)
    (by change (stackArg s 0).toNat ≤ 2 ^ 64; have := (stackArg s 0).isLt; omega_using [])
  have e5 := entry_input h hf (r := ⟨State.addr (stackArg s 1), 114⟩) (by rw [h.1]; simp)
    (by change 114 ≤ 2 ^ 64; decide)
  change u.gpr .r0 = _
  rw [hp]
  simp only at e0 e1 e3 e5
  rw [e0, e1, e3, e5]

/-- The check of the context's length: `r12 = ctxlen >> 8`, and Z set exactly when it is 0. -/
def checked (s : State) : State :=
  subFlags (s.setReg .r12 (s.gpr .r2 >>> 8)) (s.gpr .r2 >>> 8) 0

theorem check_exec (s : State) : WP isa (.block check) s fun u => u = checked s :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg .r12 (s.gpr .r2 >>> 8))
    (by simp only [exec]; rw [op2_lsr (by decide)]; rfl)
    (VG.Proof.X25519.Arm.WP.cons (s' := checked s)
      (by simp only [exec]; rw [op2_imm (v := 0) (by decide)]; rfl)
      (WP.block_nil rfl))

theorem checked_pre {s : State} (h : verifyLocal.pre s) : verifyLocal.pre (checked s) := h
theorem checked_post {s u : State} (h : verifyLocal.post (checked s) u) : verifyLocal.post s u := h
theorem checked_abi {s u : State} (h : abiPreserved (checked s) u) : abiPreserved s u := by
  refine ⟨fun r hr => (h.1 r hr).trans ?_, h.2⟩
  have : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
  exact RegUpd.gpr_setReg_of_ne _ _ this

theorem checked_z (s : State) : (checked s).z = (s.gpr .r2 >>> 8 - 0 == 0) := rfl

theorem shr8_eq_zero {x : BitVec 32} : (x >>> 8 - 0 == 0) = decide (x.toNat < 256) := by
  show (x >>> 8 - 0#32 == 0#32) = _
  rw [BitVec.sub_zero]
  by_cases h : x.toNat < 256
  · simp only [h, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [VG.Proof.X25519.Arm.toNat_shr]; simp; omega_using [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    rw [VG.Proof.X25519.Arm.toNat_shr] at this; simp at this; omega_using [h, this]

theorem verify_ok (hv : EqOk fv) {s : State} (h : verifyLocal.pre s) :
    WP isa (code fv) s fun u => abiPreserved s u ∧ verifyLocal.post s u := by
  refine WP.seq (WP.mono (check_exec s) fun u hu => ?_)
  subst hu
  refine WP.ite (decide ((s.gpr .r2).toNat < 256))
    (by rw [VG.Proof.X25519.Arm.eval_eq, checked_z, shr8_eq_zero]) (fun hb => ?_) (fun hb => ?_)
  · exact WP.mono (inner_ok hv (checked_pre h) (of_decide_eq_true hb)) fun u ⟨ha, hp⟩ =>
      ⟨checked_abi ha, checked_post hp⟩
  · refine VG.Proof.X25519.Arm.wp_movw fun u vu => WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · have h0 : r ≠ .r0 := by rintro rfl; simp [preserved] at hr
      have h12 : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
      rw [vu.other r h0]
      exact RegUpd.gpr_setReg_of_ne _ _ h12
    · rw [vu.sp]; rfl
    · change u.gpr .r0 = _
      rw [vu.gpr]
      have hl : ¬ (s.gpr .r2).toNat < 256 := by simpa using hb
      have hlen : ¬ (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat).length ≤ 255 := by
        simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range]; omega_using [hl]
      simp only [Spec.Ed448.verify, hlen, decide_false, Bool.false_and, signWord]
      rfl

end VG.Proof.Ed448.Arm.Verify

end

end

/-! ### `Ed448.Arm.Verify.CT`, which only this module used -/

section

/-!
# Ed448 verification on ARMv7: constant time

As Ed25519's complete operations on this target, with the blocks and calls
of `Proof/Ed448/Arm/Shake/CT.lean`: two runs from the same pointers, lengths
and `sp` set up the same arguments for every call, each callee is constant
time under its own contract, and the blocks between the calls address
memory only through `sp`, `r12` and `scratch`. The positions the
absorptions return, which the next ones start from, depend only on the
lengths.

`vg_ed448_verify_equation` branches on the bits of `S` and of the challenge,
which its contract takes as public: the two runs have the same inputs
(`SameIn`, from the contract's `leak`), so by correctness the same hash and
the same challenge in their frames (`Hashed`, `Reduced`), and they call it
with the same signature and challenge (`equation_ct`).
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm.Verify

open VG VG.Arm VG.Impl.Ed448.Arm.Verify VG.Impl.Ed25519.Arm.Whole
open VG.Impl.Ed448.Arm.Shake (firstArgs nextArgs absorb)
open VG.Proof.Ed25519.Arm (Whole.FR Whole.Within Whole.call_ok Whole.rel_wp Whole.callEx Whole.CallReady)
open VG.Proof.Ed448.Arm.Shake (Slot valid Kit argVal Two Slots valid_const valid_frame frame_within)
open VG.Proof.Ed448.Arm (verifyEquationLocal scalarReduceLocal scalarReduce_ok scalarReduce_ct)

variable {fv : Bool}

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

abbrev T2 (L : Lay) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem) (P : State → Prop) :=
  Two L.E L.inputs L.outputs g₁ g₂ m₁ m₂ P

/-! ## The hash -/

/-- An absorption of input data at the position the previous one returned. -/
theorem input_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (P : Nat) (hP : P < 136)
    {src len : Value} (vs : valid 11 src) (vl : valid 11 len) {R : Region} (hR : R ∈ L.inputs)
    (hw : Whole.Within ⟨State.addr (argVal L.E L.value src), (argVal L.E L.value len).toNat⟩ R)
    (hfit : (argVal L.E L.value src).toNat + (argVal L.E L.value len).toNat ≤ 2 ^ 32) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 P) (absorb (nextArgs SC src len))
      (T2 L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 ((P + (argVal L.E L.value len).toNat) % 136)) :=
  hL.kit.next_ct ha hb (scr_at L) P hP vs vl (.inr ⟨R, List.mem_append_left _ hR, hw⟩)
    (hL.kit.data_input hR hw).1 hfit

theorem hash_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True) Impl.Ed448.Arm.Verify.hash (T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hk := hL.kit
  have hd' : argVal L.E L.value (.frame HDR) = L.E + BitVec.ofNat 32 HDR := rfl
  have hkn : (argVal L.E L.value (.const 10)).toNat = 10 := rfl
  have a1 := hk.first_ct (g₁ := g₁) (g₂ := g₂) ha hb (scr_at L) (src := .frame HDR) (len := .const 10)
    (valid_frame (by decide)) (valid_const (by decide))
    (by rw [hd', hkn, hk.frame_addr (by decide)]; exact .inl (frame_within _ (by decide)))
    (by rw [hd', hkn, hk.frame_addr (by decide)]; exact hk.frame_kWr (by decide))
    (by rw [hd', hkn]; exact hk.frame_fit (by decide))
  let P1 : Nat := (0 + (argVal L.E L.value (.const 10)).toNat) % 136
  have x2 := input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P1 (Nat.mod_lt _ (by decide)) (src := .caller 1 0)
    (len := .caller 2 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (R := L.CTX) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact hL.nx)
  let P2 : Nat := (P1 + (argVal L.E L.value (.caller 2 0)).toNat) % 136
  have x3 := input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P2 (Nat.mod_lt _ (by decide)) (src := .caller 5 0)
    (len := .const 57) ⟨by decide, by decide⟩ (valid_const (by decide)) (R := L.SIG) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; have := hL.ns; simp; omega_using [this])
  let P3 : Nat := (P2 + (argVal L.E L.value (.const 57)).toNat) % 136
  have x4 := input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P3 (Nat.mod_lt _ (by decide)) (src := .caller 0 0)
    (len := .const 57) ⟨by decide, by decide⟩ (valid_const (by decide)) (R := L.PK) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; have := hL.np; simp; omega_using [this])
  let P4 : Nat := (P3 + (argVal L.E L.value (.const 57)).toNat) % 136
  have x5 := input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P4 (Nat.mod_lt _ (by decide)) (src := .caller 3 0)
    (len := .caller 4 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (R := L.MSG) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact hL.nm)
  let P5 : Nat := (P4 + (argVal L.E L.value (.caller 4 0)).toNat) % 136
  exact (hk.zeroState_ct ha hb (scr_at L)).seq (a1.seq (x2.seq (x3.seq (x4.seq (x5.seq
    ((hk.padStep_ct ha hb (scr_at L) P5 (Nat.mod_lt _ (by decide))).seq
      (hk.sqzStep_ct ha hb (scr_at L) (by decide) (by decide))))))))

/-! ## The challenge and the equation -/

theorem reduce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True)
      (callWith reduceArgs "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce)
      (T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  let args : List (Reg × Value) := [(.r0, .frame K), (.r1, .frame HASH), (.r2, scr 0)]
  have get : ∀ t, Slots L.E L.value args [] t → ReduceArgs L t := by
    intro t hs
    have h0 := hs.1 (.r0, .frame K) (by simp [args])
    have h1 := hs.1 (.r1, .frame HASH) (by simp [args])
    have h2 := hs.1 (.r2, scr 0) (by simp [args])
    simp only [argVal, scr, SC, Lay.value, BitVec.add_zero] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  refine (hL.kit.setup_ct ha hb args [] (by decide) (by simp [args, valid, scr, SC, Slot, K, HASH])
    (by simp [args, preserved]) (by decide) (by simp)).seq ?_
  apply Shake.Kit.call_ct scalarReduce_ok scalarReduce_ct
    (fun t _ h => ⟨[hReg L], [kReg L, L.SCR], reduce_pre hL (get t h), reduce_covers L, reduce_writes L⟩)
  · intro a b ar aw br bw hsp hg _
    exact ⟨hsp, hg (.r0, .frame K) (by simp [args]), hg (.r1, .frame HASH) (by simp [args]),
      hg (.r2, scr 0) (by simp [args])⟩
  · simp [args, linkRegs]
  · intro g m t hc hs
    exact Whole.call_ok hc scalarReduce_ok reduce_noFrames (reduce_pre hL (get t hs)) (reduce_covers L)
      (reduce_writes L) fun v hv _ _ => ⟨hv, trivial⟩

/-- The inputs' bytes are the same in the two runs' memories: a verification's inputs are
public. -/
def SameIn (L : Lay) (m₁ m₂ : Mem) : Prop :=
  Spec.Ed448.bytesAt m₁ (State.addr L.pk) 57 = Spec.Ed448.bytesAt m₂ (State.addr L.pk) 57 ∧
  Spec.Ed448.bytesAt m₁ (State.addr L.ctx) L.ctxLen.toNat =
    Spec.Ed448.bytesAt m₂ (State.addr L.ctx) L.ctxLen.toNat ∧
  Spec.Ed448.bytesAt m₁ (State.addr L.msg) L.len.toNat =
    Spec.Ed448.bytesAt m₂ (State.addr L.msg) L.len.toNat ∧
  Spec.Ed448.bytesAt m₁ (State.addr L.sig) 114 = Spec.Ed448.bytesAt m₂ (State.addr L.sig) 114

/-- The hash of the inputs in `m`. -/
def hashOf (L : Lay) (m : Mem) : List Byte :=
  Spec.Ed448.hash (Spec.Ed448.bytesAt m (State.addr L.ctx) L.ctxLen.toNat)
    (Spec.Ed448.bytesAt m (State.addr L.sig) 57 ++ Spec.Ed448.bytesAt m (State.addr L.pk) 57 ++
      Spec.Ed448.bytesAt m (State.addr L.msg) L.len.toNat)

theorem hashOf_eq (h : SameIn L m₁ m₂) : hashOf L m₁ = hashOf L m₂ := by
  unfold hashOf
  rw [h.1, h.2.1, h.2.2.1, ← take57 m₁ (State.addr L.sig), ← take57 m₂ (State.addr L.sig), h.2.2.2]

/-- A run with the hash in the frame. -/
def Hashed (L : Lay) (g : Reg → BitVec 32) (m : Mem) (t : State) : Prop :=
  Ctx L g m t ∧ Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114 = hashOf L m

/-- A run with the challenge in the frame. -/
def Reduced (L : Lay) (g : Reg → BitVec 32) (m : Mem) (t : State) : Prop :=
  Ctx L g m t ∧ Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 K) 57 =
    Spec.Ed448.scalarReduce (hashOf L m)

/-- A run before the call of `vg_ed448_verify_equation`: its arguments, and the signature and
the challenge they point to. -/
def EqReady (L : Lay) (g : Reg → BitVec 32) (m : Mem) (t : State) : Prop :=
  Ctx L g m t ∧ EqArgs L t ∧
    Spec.Ed448.bytesAt t.mem (State.addr L.sig) 114 = Spec.Ed448.bytesAt m (State.addr L.sig) 114 ∧
    Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 K) 57 = Spec.Ed448.scalarReduce (hashOf L m)

theorem equation_setup (hL : L.Ok) {g : Reg → BitVec 32} {m : Mem} (ha : Arguments L m) {t : State}
    (h : Reduced L g m t) : WP isa (.block equationArgs) t (EqReady L g m) := by
  refine WP.mono (setup_ok h.1 hL ha
    (args := [(.r0, .caller 0 0), (.r1, .caller 5 0), (.r2, .frame K), (.r3, scr 0)]) (stk := [])
    (by decide) (by simp [valid, scr, SC, Slot, K]) (by simp [preserved]) (by decide) (by simp))
    fun u ⟨hu, hm, hs, _⟩ => ?_
  have h0 := hs (.r0, .caller 0 0) (by simp)
  have h1 := hs (.r1, .caller 5 0) (by simp)
  have h2 := hs (.r2, .frame K) (by simp)
  have h3 := hs (.r3, scr 0) (by simp)
  simp only [argValue, scr, Lay.value, BitVec.add_zero] at h0 h1 h2 h3
  have hk : Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 K) 57 =
      Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 K) 57 :=
    Shake.bytes_setup hm (D := kReg L) (Offset.base_disjoint _ (by decide) (by decide)) (by change 57 ≤ 2 ^ 64; decide)
  exact ⟨hu, ⟨h0, h1, h2, h3⟩,
    hu.input_bytes hL (r := L.SIG) (by simp [Lay.inputs]) (by change 114 ≤ 2 ^ 64; decide), hk.trans h.2⟩

/-- The call of `vg_ed448_verify_equation`: the two runs give it the same signature and the same
challenge, the hash of the same inputs. -/
theorem equation_ct (hv : EqOk fv) (hct : EqCT fv) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (hin : SameIn L m₁ m₂) :
    RelCT isa (fun a b => Reduced L g₁ m₁ a ∧ Reduced L g₂ m₂ b)
      (callWith equationArgs ("vg_ed448_verify_equation" ++ Impl.X448.Arm.suffix fv)
        (Impl.Ed448.Arm.verifyEquation fv)) (fun _ _ => True) := by
  let args : List (Reg × Value) := [(.r0, .caller 0 0), (.r1, .caller 5 0), (.r2, .frame K), (.r3, scr 0)]
  have hs : RelCT isa (fun a b => Reduced L g₁ m₁ a ∧ Reduced L g₂ m₂ b) (.block equationArgs)
      (fun a b => EqReady L g₁ m₁ a ∧ EqReady L g₂ m₂ b) :=
    Whole.rel_wp ((hL.kit.setup_ct ha hb args [] (by decide) (by simp [args, valid, scr, SC, Slot, K])
      (by simp [args, preserved]) (by decide) (by simp)).mono
        (fun _ _ h => ⟨⟨h.1.1, trivial⟩, ⟨h.2.1, trivial⟩⟩) (fun _ _ _ => trivial))
      (fun _ h => equation_setup hL ha h) (fun _ h => equation_setup hL hb h)
  refine hs.seq (Whole.callEx hv hct fun a b h => ?_)
  obtain ⟨⟨ca, aa, sa, ka⟩, ⟨cb, ab, sb, kb⟩⟩ := h
  let ra : Whole.CallReady verifyEquationLocal L.E L.inputs L.outputs a :=
    ⟨[L.PK, L.SIG, kReg L], [L.SCR], equation_pre hL aa, equation_covers L, equation_writes L⟩
  let rb : Whole.CallReady verifyEquationLocal L.E L.inputs L.outputs b :=
    ⟨[L.PK, L.SIG, kReg L], [L.SCR], equation_pre hL ab, equation_covers L, equation_writes L⟩
  obtain ⟨cva, wa⟩ := ra.covers_state ca
  obtain ⟨cvb, wb⟩ := rb.covers_state cb
  have ea : ∀ r, r ∉ linkRegs → (a.callEntry.withRegions [L.PK, L.SIG, kReg L] [L.SCR]).gpr r = a.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  have eb : ∀ r, r ∉ linkRegs → (b.callEntry.withRegions [L.PK, L.SIG, kReg L] [L.SCR]).gpr r = b.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine ⟨_, _, _, _, ra.pre, rb.pre, ?_, cva, wa, cvb, wb⟩
  simp only [verifyEquationLocal]
  rw [ea .r0 (by decide), ea .r1 (by decide), ea .r2 (by decide), ea .r3 (by decide),
    eb .r0 (by decide), eb .r1 (by decide), eb .r2 (by decide), eb .r3 (by decide),
    aa.1, aa.2.1, aa.2.2.1, aa.2.2.2, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2,
    State.withRegions_mem, State.withRegions_mem, State.callEntry_mem, State.callEntry_mem,
    hL.kit.frame_addr (by decide), sa, sb, ka, kb, hashOf_eq hin]
  exact ⟨rfl, rfl, rfl, rfl, ca.sp.trans cb.sp.symm, hin.2.2.2, rfl⟩

/-! ## The body -/

theorem body_ct (hv : EqOk fv) (hct : EqCT fv) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (hin : SameIn L m₁ m₂) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True) (body fv) (fun _ _ => True) := by
  have h := hL.kit.hdr_ct (g₁ := g₁) (g₂ := g₂) ha hb (j := 2) (off := HDR) (by decide) hL.cl (by decide)
  have hh : RelCT isa (T2 L g₁ g₂ m₁ m₂ fun s =>
        Spec.Ed448.bytesAt s.mem (State.addr L.E + BitVec.ofNat 64 HDR) 10 = hdrBytes L)
      Impl.Ed448.Arm.Verify.hash (fun a b => Hashed L g₁ m₁ a ∧ Hashed L g₂ m₂ b) :=
    Whole.rel_wp ((hash_ct hL ha hb).mono (fun _ _ h => ⟨⟨h.1.1, trivial⟩, ⟨h.2.1, trivial⟩⟩)
      (fun _ _ _ => trivial)) (fun _ h => hash_ok h.1 hL ha h.2) (fun _ h => hash_ok h.1 hL hb h.2)
  have hr : RelCT isa (fun a b => Hashed L g₁ m₁ a ∧ Hashed L g₂ m₂ b)
      (callWith reduceArgs "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce)
      (fun a b => Reduced L g₁ m₁ a ∧ Reduced L g₂ m₂ b) :=
    Whole.rel_wp ((reduce_ct hL ha hb).mono (fun _ _ h => ⟨⟨h.1.1, trivial⟩, ⟨h.2.1, trivial⟩⟩)
      (fun _ _ _ => trivial))
      (fun _ h => WP.mono (reduce_step h.1 hL ha) fun _ ⟨hu, hk⟩ => ⟨hu, hk.trans (congrArg _ h.2)⟩)
      (fun _ h => WP.mono (reduce_step h.1 hL hb) fun _ ⟨hu, hk⟩ => ⟨hu, hk.trans (congrArg _ h.2)⟩)
  exact h.seq (hh.seq (hr.seq (equation_ct hv hct hL ha hb hin)))

end VG.Proof.Ed448.Arm.Verify

end

end


/-!
# Ed448 verification on ARMv7: constant time, and `Verified`

`verify_ct`: the check of the context's length leaks nothing and branches
on a length; the frame around the body is constant time (`inner_ct`, from
`body_ct`). `verify_verified`: against `Spec.Ed448.verifyContract Arm.abi
280`, for any code of `vg_ed448_verify_equation` meeting its contract
(`EqOk`, `EqCT`): the registration file passes its own.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm.Verify

open VG VG.Arm VG.Impl.Ed448.Arm.Verify VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.base Whole.wrap_ct Whole.bodyRd Whole.bodyWr Whole.quiet_block_ct Whole.Saved
  Whole.entered Whole.saved_frame)

variable {fv : Bool}

theorem lay_eq {s t : State} (hp : verifyLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2, h3, a0, a1, a2, _⟩ := hp
  simp only [lay, Whole.base, sp, h0, h1, h2, h3, a0, a1, a2]

/-- The inputs, which are public, are the same in the two runs' memories once the frames are
pushed. -/
theorem saved_inputs_eq {s t p q : State} (hs : verifyLocal.pre s) (ht : verifyLocal.pre t)
    (hp : verifyLocal.pub s t) (hpa : Whole.Saved (Whole.entered s) 6 p)
    (hqb : Whole.Saved (Whole.entered t) 6 q) : SameIn (lay s) p.mem q.mem := by
  have fp := Whole.saved_frame (entry_below hs) hpa
  have fq := Whole.saved_frame (entry_below ht) hqb
  obtain ⟨_, h0, h1, h2, h3, a0, a1, _, pk, ctx, msg, sig⟩ := hp
  have epk := entry_input hs fp (r := ⟨State.addr (s.gpr .r0), 57⟩) (by rw [hs.1]; simp)
    (by change 57 ≤ 2 ^ 64; decide)
  have fpk := entry_input ht fq (r := ⟨State.addr (t.gpr .r0), 57⟩) (by rw [ht.1]; simp)
    (by change 57 ≤ 2 ^ 64; decide)
  have ectx := entry_input hs fp (r := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩) (by rw [hs.1]; simp)
    (by have := (s.gpr .r2).isLt; change (s.gpr .r2).toNat ≤ 2 ^ 64; omega_using [])
  have fctx := entry_input ht fq (r := ⟨State.addr (t.gpr .r1), (t.gpr .r2).toNat⟩) (by rw [ht.1]; simp)
    (by have := (t.gpr .r2).isLt; change (t.gpr .r2).toNat ≤ 2 ^ 64; omega_using [])
  have emsg := entry_input hs fp (r := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩) (by rw [hs.1]; simp)
    (by have := (stackArg s 0).isLt; change (stackArg s 0).toNat ≤ 2 ^ 64; omega_using [])
  have fmsg := entry_input ht fq (r := ⟨State.addr (t.gpr .r3), (stackArg t 0).toNat⟩) (by rw [ht.1]; simp)
    (by have := (stackArg t 0).isLt; change (stackArg t 0).toNat ≤ 2 ^ 64; omega_using [])
  have esig := entry_input hs fp (r := ⟨State.addr (stackArg s 1), 114⟩) (by rw [hs.1]; simp)
    (by change 114 ≤ 2 ^ 64; decide)
  have fsig := entry_input ht fq (r := ⟨State.addr (stackArg t 1), 114⟩) (by rw [ht.1]; simp)
    (by change 114 ≤ 2 ^ 64; decide)
  change Spec.Ed448.bytesAt p.mem (State.addr (s.gpr .r0)) 57 =
      Spec.Ed448.bytesAt q.mem (State.addr (s.gpr .r0)) 57 ∧
    Spec.Ed448.bytesAt p.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
      Spec.Ed448.bytesAt q.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat ∧
    Spec.Ed448.bytesAt p.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat =
      Spec.Ed448.bytesAt q.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat ∧
    Spec.Ed448.bytesAt p.mem (State.addr (stackArg s 1)) 114 =
      Spec.Ed448.bytesAt q.mem (State.addr (stackArg s 1)) 114
  rw [epk, ectx, emsg, esig, h0, h1, h2, h3, a0, a1, fpk, fctx, fmsg, fsig]
  rw [h0] at pk
  rw [h1, h2] at ctx
  rw [h3, a0] at msg
  rw [a1] at sig
  exact ⟨pk, ctx, msg, sig⟩

/-- The frame around the body is constant time, for a context of fewer than 256 bytes. -/
theorem inner_ct (hv : EqOk fv) (hct : EqCT fv) :
    ConstantTime isa (fun s => verifyLocal.pre s ∧ (s.gpr .r2).toNat < 256) verifyLocal.pub (wrap 6 (body fv)) := by
  refine Whole.wrap_ct (by decide : 6 ≤ 6) (fun _ _ hp => hp.1) (fun _ hs => entry_below hs.1)
    (fun _ hs => by have := entry_top hs.1; omega_using [this]) (fun _ hs => entry_read hs.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok hv (entry_ctx hs.1 hp) (lay_ok hs.1 hs.2) (entry_args hs.1 hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht.1 hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args ht.1 hqb
    exact ⟨(body_ct hv hct (lay_ok hs.1 hs.2) (entry_args hs.1 hpa) hqa
      (saved_inputs_eq hs.1 ht.1 hp hpa hqb) _ _ _ _ _ _
      ⟨⟨entry_ctx hs.1 hpa, trivial⟩, ⟨hq, trivial⟩⟩ ea eb).1, trivial⟩

theorem checked_pub {s t : State} (h : verifyLocal.pub s t) : verifyLocal.pub (checked s) (checked t) := h

theorem checked_lt {s : State} (h : isa.eval .eq (checked s) = some true) : (s.gpr .r2).toNat < 256 := by
  rw [VG.Proof.X25519.Arm.eval_eq, checked_z, shr8_eq_zero] at h
  exact of_decide_eq_true (Option.some.inj h)

theorem verify_ct (hv : EqOk fv) (hct : EqCT fv) : ConstantTime isa verifyLocal.pre verifyLocal.pub (code fv) := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold code
  have hblk := ((Whole.quiet_block_ct check (by
      intro i hi s
      simp only [check, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> rfl)).mono
    (P' := fun s₁ s₂ => verifyLocal.pre s₁ ∧ verifyLocal.pre s₂ ∧ verifyLocal.pub s₁ s₂)
    (fun _ _ h => h.2.2.1) (fun _ _ _ => trivial)).wpDep (F := fun σ s' => s' = checked σ)
      (fun s₁ s₂ _ => ⟨check_exec s₁, check_exec s₂⟩)
  refine RelCT.seq hblk (RelCT.ite ?_ ?_ ?_)
  · rintro _ _ ⟨_, σ₁, σ₂, hp, rfl, rfl⟩
    rw [VG.Proof.X25519.Arm.eval_eq, VG.Proof.X25519.Arm.eval_eq, checked_z, checked_z, hp.2.2.2.2.2.1]
  · rintro _ _ t₁ t₂ s₁' s₂' ⟨⟨_, σ₁, σ₂, hp, rfl, rfl⟩, hev⟩ e₁ e₂
    have l₁ := checked_lt hev
    have l₂ : (σ₂.gpr .r2).toNat < 256 := hp.2.2.2.2.2.1 ▸ l₁
    exact ⟨inner_ct hv hct _ _ _ _ _ _ ⟨checked_pre hp.1, l₁⟩ ⟨checked_pre hp.2.1, l₂⟩
      (checked_pub hp.2.2) e₁ e₂, trivial⟩
  · refine ((Whole.quiet_block_ct [.movw .r0 0] (by
      intro i hi s
      rw [List.mem_singleton.mp hi]; rfl)).mono ?_ (fun _ _ _ => trivial))
    rintro _ _ ⟨⟨_, σ₁, σ₂, hp, rfl, rfl⟩, _⟩
    exact hp.2.2.1

/-! ## The contract -/

def verifySatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0 | .r3 => 0x3000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x9005 then 0x50 else if a = 0x900A then 0x01 else 0
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 114⟩, ⟨0x9000, 12⟩]
  wr := [⟨0x10000, 8192⟩]

private theorem argAddr_zero (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp [stackArgAddr]

/-- The contract's byte-to-natural encoding is injective. -/
private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

private theorem pre_bridge (s : State) (h : (Spec.Ed448.verifyContract Arm.abi 280).pre s) :
    verifyLocal.pre s := by
  sig_pre [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
    Spec.Ed448.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
  sig_split h
  sig_reduce [verifyLocal, Arm.State.addr]
  sig_simp [argAddr_zero, Arm.State.addr] [] at *
  simp only [Arm.State.addr, show (280#64) = (280 : Addr) from rfl] at *
  sig_and_intros
  all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›

theorem verify_implies : verifyLocal.Implies (Spec.Ed448.verifyContract Arm.abi 280) where
  pre := pre_bridge
  post s t _ h := by
    sig_post [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    rw [BitVec.setWidth_append_eq_right]
    exact h
  pub s t _ _ h := by
    sig_pub [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
    obtain ⟨sp, bytes, h0, h1, h2, h3, a0, a1, a2⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, sig⟩ := List.append_inj' hb (by
      simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range])
    obtain ⟨first, msg⟩ := List.append_inj' first (by
      simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range, a0])
    obtain ⟨pk, ctx⟩ := List.append_inj' first (by
      simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range, h2])
    exact ⟨sp, h0, h1, h2, h3, a0, a1, a2, pk, ctx, msg, sig⟩
  sat := by
    refine ⟨verifySatState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
        Spec.Ed448.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, verifySatState]
      decide +kernel

/-- `vg_ed448_verify` on ARMv7, for any code of `vg_ed448_verify_equation`
meeting its contract. -/
theorem verify_verified (hv : EqOk fv) (hct : EqCT fv) :
    Verified Arm.target (code fv) (Spec.Ed448.verifyContract Arm.abi 280) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => verify_ok hv h) (verify_ct hv hct) (.refl verify_implies.sat_left))
    verify_implies

end VG.Proof.Ed448.Arm.Verify
