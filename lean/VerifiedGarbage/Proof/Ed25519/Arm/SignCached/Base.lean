module

public import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Calls
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.Arm.FieldMemory
import VerifiedGarbage.Proof.Ed25519.Arm.FnCall
import VerifiedGarbage.Proof.Ed25519.Arm.MulFnFinal
import VerifiedGarbage.Proof.Ed25519.Arm.PackField
import VerifiedGarbage.Proof.Ed25519.Arm.PointAffine
import VerifiedGarbage.Proof.Ed25519.Arm.PointFromScalar
import VerifiedGarbage.Proof.Ed25519.Arm.PointMulBody
import VerifiedGarbage.Proof.Ed25519.Arm.Points
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTBody
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarCodec
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X25519.Arm.AddSub
import VerifiedGarbage.Proof.X25519.Arm.Cswap

@[expose] public section

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm
open VG.Impl.Ed25519.Arm (scalarBase)

def baseRd (L : Lay) : List Region := [field L 88, L.TB]
def baseWr (L : Lay) : List Region := [baseOut L, L.SCR]
def BaseArgs (L : Lay) (s : State) : Prop :=
  s.gpr .r0 = L.out ∧ s.gpr .r1 = L.E + 88 ∧ s.gpr .r2 = L.scr

theorem base_noFrames : scalarBase.noFrames = true := by lit_decide

/-- The comb's tables at `L.T` in `m`. -/
def Tbl (L : Lay) (m : Mem) : Prop :=
  ∀ j < 64 * 192, m.readW (State.addr L.T + BitVec.ofNat 64 (8 * j)) 64 = VG.Impl.Ed25519.Arm.combWord j

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem tb_input (L : Lay) : L.TB ∈ L.inputs := by simp [Lay.inputs]

/-- The tables in a memory the body leaves them in. -/
theorem Ctx.tbl (hc : Ctx L g m₀ s) (hL : L.Ok) (hw : Tbl L m₀) : Tbl L s.mem := fun j hj => by
  rw [← hw j hj]
  refine hc.frame.readW (r := L.TB) (Offset.contains_base _ (by omega) (by omega)) ?_ (by decide)
  intro R hR
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · exact (hL.os _ (tb_input L)).symm
  · exact hL.sc _ (tb_input L)
  · exact (hL.ks _ (tb_input L)).symm

theorem base_pre (hL : L.Ok) (ha : BaseArgs L s) (hsy : s.syms VG.Impl.Ed25519.Arm.combSym = L.T)
    (hw : Tbl L s.mem) :
    scalarBaseLocal.pre (s.callEntry.withRegions (baseRd L) (baseWr L)) := by
  have ae : State.addr (L.E + 88) = State.addr L.E + 88 := frame_addr hL (d := 88) (by decide)
  have sy : (s.callEntry.withRegions (baseRd L) (baseWr L)).syms VG.Impl.Ed25519.Arm.combSym = L.T := hsy
  simp only [scalarBaseLocal, sy, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_mem, State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), ha.1, ha.2.1, ha.2.2, ae]
  exact ⟨rfl, rfl, (hL.ko.sub_right (baseWithin L).sub).symm.sub_right (fieldWithin L (by decide)).sub,
    hL.oc.sub_left (baseWithin L).sub, field_scr hL (by decide),
    by have := hL.no; omega, frame_fit hL (by decide), hL.nc, hL.tfit, hw,
    ((hL.os _ (tb_input L)).sub_left (baseWithin L).sub).symm, hL.sc _ (tb_input L)⟩

theorem base_call (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : BaseArgs L s)
    (hsy : s.syms VG.Impl.Ed25519.Arm.combSym = L.T) (hw : Tbl L s.mem) :
    WP isa (.call "vg_ed25519_scalar_base" scalarBase) s fun t => Ctx L g m₀ t ∧
      Frame (baseWr L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.out) 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 88) 32) := by
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
  refine Whole.call_ok hc scalarBase_ok base_noFrames (base_pre hL ha hsy hw) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  change Spec.Ed25519.bytesAt t.mem (State.addr (s.callEntry.gpr .r0)) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r1)) 32) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), ha.1, ha.2.1] at hp
  have ae : State.addr (L.E + 88) = State.addr L.E + 88 := frame_addr hL (d := 88) (by decide)
  rw [ae] at hp
  exact hp

end VG.Proof.Ed25519.Arm.SignCached
