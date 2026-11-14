module

public import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Calls
import VerifiedGarbage.Proof.Sha512.Stream
import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ed25519.Arm.Whole.HashPre
public import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Args
public import VerifiedGarbage.Impl.Ed25519.Arm.SignCached
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarVerified
import VerifiedGarbage.Impl.Ed25519.Arm.Field
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarPass
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Framework.RegionsSub
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
import VerifiedGarbage.Proof.X25519.Arm.AddSub
import VerifiedGarbage.Proof.X25519.Arm.Cswap
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarMulAddVerified
import VerifiedGarbage.Proof.Ed25519.Signing
public import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Prune
import VerifiedGarbage.Proof.Ed25519.VerifyBytes

/-! ### `Ed25519.Arm.SignCached.HashFrame`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm
variable {L : Lay}

def slots (L : Lay) : Region := ⟨State.addr L.E, 24⟩
def hashWrites (L : Lay) : List Region := [L.SCR, slots L, digest L]

theorem setup_frame {m n : Mem} (hf : Frame [slots L] m n) : Frame (hashWrites L) m n :=
  hf.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨slots L, by simp [hashWrites], fun _ h => h⟩

theorem hash_frame {m n : Mem} {rs : List Region} (hf : Frame rs m n)
    (hw : ∀ r ∈ rs, Whole.Within r L.SCR ∨ Whole.Within r (digest L)) : Frame (hashWrites L) m n := by
  refine hf.sub fun r hr => ?_
  rcases hw r hr with hc | hd
  · exact ⟨L.SCR, by simp [hashWrites], hc.sub⟩
  · exact ⟨digest L, by simp [hashWrites], hd.sub⟩

theorem frame_bytes {m n : Mem} {ws : List Region} (hf : Frame ws m n) (r : Region)
    (hd : ∀ w ∈ ws, r.Disjoint w) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt n r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  exact Frame.bytes hf hd hn (List.mem_range.mp hi)

theorem setup_field_bytes {m n : Mem} (hf : Frame [slots L] m n)
    {d : Nat} (hd : d + 32 ≤ 248) (hmin : 24 ≤ d) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by
  apply frame_bytes hf (field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  exact Offset.disjoint_base _ hmin (by omega_using [hd])

theorem setup_repr {m n : Mem} (hL : L.Ok) (hf : Frame [slots L] m n) {msg : List Byte}
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 m (State.addr L.scr) msg) :
    Spec.Sha512.Repr Spec.Sha512.H0_512 n (State.addr L.scr) msg := by
  refine Proof.Sha512.Stream.repr_congr (mem := m) ?_ hr
  intro i hi
  exact hf.bytes (R := ⟨State.addr L.scr, 192⟩) (by
    rintro r hm; rw [List.mem_singleton.mp hm]
    exact (hL.kc.sub_left (Region.sub_prefix (by decide))).symm.sub_left (Region.sub_prefix (by decide)))
    (by change 192 ≤ 2 ^ 64; decide) hi

theorem hash_field_bytes {m n : Mem} (hL : L.Ok) (hf : Frame (hashWrites L) m n)
    {d : Nat} (hd : d + 32 ≤ 184) (hmin : 24 ≤ d) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by
  apply frame_bytes hf (field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact field_scr hL (by omega_using [hd])
  · exact Offset.disjoint_base _ (by omega_using [hmin]) (by omega_using [hd])
  · exact Offset.disjoint _ (by omega_using [hd]) (by omega_using [hd]) (by decide)

theorem hash_out_bytes {m n : Mem} (hL : L.Ok) (hf : Frame (hashWrites L) m n) :
    Spec.Ed25519.bytesAt n (State.addr L.out) 32 = Spec.Ed25519.bytesAt m (State.addr L.out) 32 := by
  apply frame_bytes hf (baseOut L) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.oc.sub_left (baseWithin L).sub
  · exact (hL.ko.sub_right (baseWithin L).sub).symm.sub_right (Region.sub_prefix (by decide))
  · exact (hL.ko.sub_right (baseWithin L).sub).symm.sub_right (digestWithin L).sub

theorem bytes_length (m : Mem) (p : Addr) (n : Nat) :
    (Spec.Ed25519.bytesAt m p n).length = n := by simp [Spec.Ed25519.bytesAt]

end VG.Proof.Ed25519.Arm.SignCached

end

end

/-! ### `Ed25519.Arm.SignCached.Reduce`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm
open VG.Impl.Ed25519.Arm (scalarReduce)

def reduceRd (L : Lay) : List Region := [digest L]
def reduceWr (L : Lay) (d : Nat) : List Region := [field L d, L.SCR]
def ReduceArgs (L : Lay) (d : Nat) (s : State) : Prop :=
  s.gpr .r0 = L.E + BitVec.ofNat 32 d ∧ s.gpr .r1 = L.E + 184 ∧ s.gpr .r2 = L.scr

theorem reduce_noFrames : scalarReduce.noFrames = true := by lit_decide

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem reduce_pre (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 184) (ha : ReduceArgs L d s) :
    scalarReduceLocal.pre (s.callEntry.withRegions (reduceRd L) (reduceWr L d)) := by
  have ad := frame_addr hL (d := d) (by omega_using [hd])
  have a184 : State.addr (L.E + 184) = State.addr L.E + 184 := frame_addr hL (d := 184) (by decide)
  simp only [scalarReduceLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), ha.1, ha.2.1, ha.2.2, ad, a184]
  have sep : (field L d).Disjoint (digest L) := Offset.disjoint _ (by omega_using [hd]) (by omega_using [hd]) (by decide)
  exact ⟨rfl, rfl, sep,
    field_scr hL (by omega_using [hd]), hL.kc.sub_left (digestWithin L).sub,
    frame_fit hL (by omega_using [hd]), frame_fit hL (by decide), hL.nc⟩

theorem reduce_call (hc : Ctx L g m₀ s) (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 184)
    (ha : ReduceArgs L d s) :
    WP isa (.call "vg_ed25519_scalar_reduce" scalarReduce) s fun t => Ctx L g m₀ t ∧
      Frame (reduceWr L d) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 d) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 184) 64) := by
  have cov : Covers (reduceRd L ++ reduceWr L d) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (digestWithin L)
    · exact .inl (fieldWithin L (by omega_using [hd]))
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ reduceWr L d, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (fieldWithin L (by omega_using [hd]))
    · exact .inr (.inr (scratchWithin L))
  refine Whole.call_ok hc scalarReduce_ok reduce_noFrames (reduce_pre hL hd ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  change Spec.Ed25519.bytesAt t.mem (State.addr (s.callEntry.gpr .r0)) 32 =
    Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r1)) 64) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), ha.1, ha.2.1] at hp
  have ad := frame_addr hL (d := d) (by omega_using [hd])
  have a184 : State.addr (L.E + 184) = State.addr L.E + 184 := frame_addr hL (d := 184) (by decide)
  rw [ad, a184] at hp
  exact hp

end VG.Proof.Ed25519.Arm.SignCached

end

end

/-! ### `Ed25519.Arm.SignCached.Base`, which only this module used -/

section

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
  refine hc.frame.readW (r := L.TB) (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])) ?_ (by decide)
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
    by have := hL.no; omega_using [this], frame_fit hL (by decide), hL.nc, hL.tfit, hw,
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

end

end

/-! ### `Ed25519.Arm.SignCached.MulAdd`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def mulRd (L : Lay) : List Region := [field L 88, field L 120, field L 24, ⟨State.addr L.E, 4⟩]
def mulWr (L : Lay) : List Region := [half L, L.SCR]
def MulArgs (L : Lay) (s : State) : Prop :=
  s.gpr .r0 = L.out + 32 ∧ s.gpr .r1 = L.E + 88 ∧ s.gpr .r2 = L.E + 120 ∧
    s.gpr .r3 = L.E + 24 ∧ stackArg s 0 = L.scr

theorem mul_noFrames : scalarMulAdd.noFrames = true := by lit_decide

theorem mul_pre (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : MulArgs L s) :
    scalarMulAddLocal.pre (s.callEntry.withRegions (mulRd L) (mulWr L)) := by
  have ao : State.addr (L.out + 32) = State.addr L.out + 32 := addr_add (k := 32) (by have := hL.no; omega_using [this])
  have fo : (L.out + 32).toNat + 32 ≤ 2 ^ 32 := by
    have hn := hL.no
    change (L.out.toNat + 32) % 2 ^ 32 + 32 ≤ 2 ^ 32
    rw [Nat.mod_eq_of_lt (by omega_using [hn] : L.out.toNat + 32 < 2 ^ 32)]
    omega_using [hn]
  have st : stackArg (s.callEntry.withRegions (mulRd L) (mulWr L)) 0 = stackArg s 0 := rfl
  have a88 : State.addr (L.E + 88) = State.addr L.E + 88 := frame_addr hL (d := 88) (by decide)
  have a120 : State.addr (L.E + 120) = State.addr L.E + 120 := frame_addr hL (d := 120) (by decide)
  have a24 : State.addr (L.E + 24) = State.addr L.E + 24 := frame_addr hL (d := 24) (by decide)
  have he := hc.sp
  simp only [scalarMulAddLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), st,
    ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2, ao, he,
    a88, a120, a24]
  exact ⟨rfl, rfl, hL.oc.sub_left (halfWithin L).sub,
    field_scr hL (by decide), field_scr hL (by decide), field_scr hL (by decide),
    (hL.ko.sub_right (halfWithin L).sub).symm.sub_right (Region.sub_prefix (by decide)),
    hL.kc.symm.sub_right (Region.sub_prefix (by decide)), fo,
    frame_fit hL (by decide), frame_fit hL (by decide), frame_fit hL (by decide),
    hL.nc, by have := hL.top; omega_using [this]⟩

theorem mul_call (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : MulArgs L s) :
    WP isa (.call "vg_ed25519_scalar_mul_add" scalarMulAdd) s fun t => Ctx L g m₀ t ∧
      Frame (mulWr L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.out + 32) 32 =
        Spec.Ed25519.scalarMulAdd (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 88) 32)
          (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 120) 32)
          (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 24) 32) := by
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
  refine Whole.call_ok hc scalarMulAdd_ok mul_noFrames (mul_pre hc hL ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  have ao : State.addr (L.out + 32) = State.addr L.out + 32 := addr_add (k := 32) (by have := hL.no; omega_using [this])
  change Spec.Ed25519.bytesAt t.mem (State.addr (s.callEntry.gpr .r0)) 32 =
    Spec.Ed25519.scalarMulAdd (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r1)) 32)
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r2)) 32)
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r3)) 32) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1] at hp
  have a88 : State.addr (L.E + 88) = State.addr L.E + 88 := frame_addr hL (d := 88) (by decide)
  have a120 : State.addr (L.E + 120) = State.addr L.E + 120 := frame_addr hL (d := 120) (by decide)
  have a24 : State.addr (L.E + 24) = State.addr L.E + 24 := frame_addr hL (d := 24) (by decide)
  rw [ao, a88, a120, a24] at hp
  exact hp

end VG.Proof.Ed25519.Arm.SignCached

end

end


/-! Merged from `Proof.Ed25519.Arm.SignCached.HashSteps`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.Arm.SignCached.HashReady`. -/
section
/-! Merged from `Proof.Ed25519.Arm.SignCached.HashInputs`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm
variable {L : Lay}

structure Input (L : Lay) (p n : BitVec 32) : Prop where
  cover : Whole.Within ⟨State.addr p, n.toNat⟩ L.FR ∨
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within ⟨State.addr p, n.toNat⟩ R
  scratch : Region.Disjoint ⟨State.addr p, n.toNat⟩ L.SCR
  args : Region.Disjoint ⟨State.addr p, n.toNat⟩ (slots L)
  fit : p.toNat + n.toNat ≤ 2 ^ 32

theorem input_self {r : Region} (hr : r ∈ L.inputs) :
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R :=
  ⟨r, List.mem_append_left _ hr, 0, by simp, by simp⟩

theorem input_slots (hL : L.Ok) {r : Region} (hr : r ∈ L.inputs) : r.Disjoint (slots L) :=
  (hL.ks _ hr).symm.sub_right (Region.sub_prefix (by decide))

theorem key_input (hL : L.Ok) : Input L L.pk 32 :=
  ⟨.inr (input_self (r := L.PK) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs]),
    input_slots hL (by simp [Lay.inputs]), hL.np⟩

theorem message_input (hL : L.Ok) : Input L L.msg L.len :=
  ⟨.inr (input_self (r := L.MSG) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs]),
    input_slots hL (by simp [Lay.inputs]), hL.nm⟩

theorem point_input (hL : L.Ok) : Input L L.out 32 :=
  ⟨.inr (output_covered (baseWithin L)), hL.oc.sub_left (baseWithin L).sub,
    (hL.ko.sub_right (baseWithin L).sub).symm.sub_right (Region.sub_prefix (by decide)),
    by have := hL.no; change L.out.toNat + 32 ≤ 2 ^ 32; omega_arith⟩

theorem prefix_input (hL : L.Ok) : Input L (L.E + 56) 32 := by
  have ae : State.addr (L.E + 56) = State.addr L.E + 56 := frame_addr hL (d := 56) (by decide)
  refine ⟨?_, ?_, ?_, frame_fit hL (d := 56) (by decide)⟩
  · rw [ae]
    exact .inl (fieldWithin L (by decide))
  · rw [ae]
    exact field_scr hL (by decide)
  · rw [ae]
    exact Offset.disjoint_base _ (by decide) (by decide)

end VG.Proof.Ed25519.Arm.SignCached
end

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm
variable {L : Lay}

theorem shaWithin (L : Lay) : Whole.Within (Whole.SHA L.scr) L.SCR :=
  ⟨0, by simp, by change 0 + 192 ≤ 8192; decide⟩
theorem workWithin (L : Lay) : Whole.Within (Whole.WORK L.scr) L.SCR :=
  ⟨192, rfl, by change 192 + 272 ≤ 8192; decide⟩
theorem argsWithin (L : Lay) {n : Nat} (hn : n ≤ 248) :
    Whole.Within (Whole.CALLARGS L.E n) L.FR := ⟨0, by simp, by change 0 + n ≤ 248; omega_arith⟩

theorem init_frame {m n : Mem} (hf : Frame (Whole.initWr L.scr) m n) : Frame (hashWrites L) m n := by
  apply hash_frame hf
  intro r hr; rw [List.mem_singleton.mp hr]
  exact .inl (shaWithin L)

theorem update_frame {m n : Mem} (hf : Frame (Whole.hashWr L.scr) m n) : Frame (hashWrites L) m n := by
  apply hash_frame hf
  simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inl (shaWithin L)
  · exact .inl (workWithin L)

theorem final_addr (hL : L.Ok) : State.addr (L.E + 184) = State.addr L.E + 184 :=
  frame_addr hL (d := 184) (by decide)

theorem finalize_frame (hL : L.Ok) {m n : Mem} (hf : Frame (Whole.finalizeWr L.scr (L.E + 184)) m n) :
    Frame (hashWrites L) m n := by
  apply hash_frame hf
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inl (shaWithin L)
  · exact .inr ⟨0, by rw [final_addr hL]; simp [digest], by change 0 + 64 ≤ 64; decide⟩
  · exact .inl (workWithin L)

theorem final_writes (hL : L.Ok) : ∀ r ∈ Whole.finalizeWr L.scr (L.E + 184),
    Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  apply writes
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inr (.inr (shaWithin L))
  · exact .inl ⟨184, final_addr hL, by change 184 + 64 ≤ 248; decide⟩
  · exact .inr (.inr (workWithin L))

theorem update_covers {p n : BitVec 32} (hi : Input L p n) :
    Covers (Whole.updateRd L.E p n ++ Whole.hashWr L.scr) (L.inputs ++ L.FR :: L.outputs) := by
  apply covers
  simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hi.cover
  · exact .inl (argsWithin L (by decide))
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], shaWithin L⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], workWithin L⟩

theorem finalize_covers (hL : L.Ok) :
    Covers (Whole.finalizeRd L.E ++ Whole.finalizeWr L.scr (L.E + 184)) (L.inputs ++ L.FR :: L.outputs) := by
  apply covers
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    exact .inl (argsWithin L (by decide))
  · rcases final_writes hL r hr with hf | ⟨R, hR, hw⟩
    · exact .inl hf
    · exact .inr ⟨R, List.mem_append_right _ hR, hw⟩

def UpdateArgs (L : Lay) (count p n : BitVec 32) (t : State) : Prop :=
  t.gpr .r0 = L.scr ∧ t.gpr .r2 = count ∧ t.gpr .r3 = 0 ∧
    stackArg t 0 = p ∧ stackArg t 1 = n ∧ stackArg t 2 = L.scr + 192

def FinalArgs (L : Lay) (count : BitVec 32) (t : State) : Prop :=
  t.gpr .r0 = L.scr ∧ t.gpr .r2 = count ∧ t.gpr .r3 = 0 ∧
    stackArg t 0 = L.E + 184 ∧ stackArg t 1 = L.scr + 192

theorem update_pre {t : State} (hL : L.Ok) (he : t.sp = L.E)
    {count p n : BitVec 32} (ha : UpdateArgs L count p n t) (hi : Input L p n) :
    Proof.Sha512.updateArm.pre (t.callEntry.withRegions (Whole.updateRd L.E p n) (Whole.hashWr L.scr)) :=
  Whole.update_pre he ha.1 ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.2.2.2 hi.scratch
    (hL.kc.sub_left (Region.sub_prefix (by decide))) hL.nc hi.fit (by have := hL.top; omega_arith)

theorem finalize_pre {t : State} (hL : L.Ok) (he : t.sp = L.E)
    {count : BitVec 32} (ha : FinalArgs L count t) :
    Proof.Sha512.finalizeArm.pre (t.callEntry.withRegions (Whole.finalizeRd L.E) (Whole.finalizeWr L.scr (L.E + 184))) := by
  refine Whole.finalize_pre he ha.1 ha.2.2.2.1 ha.2.2.2.2 ?_
    (hL.kc.sub_left (Region.sub_prefix (by decide))) ?_ hL.nc
    (frame_fit hL (d := 184) (by decide)) (by have := hL.top; omega_arith)
  · rw [final_addr hL]
    exact hL.kc.sub_left (digestWithin L).sub
  · rw [final_addr hL]
    exact Offset.base_disjoint _ (by decide) (by decide)

theorem count_zero_high (x : BitVec 32) : (0#32) ++ x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt, Nat.shiftLeft_eq]
  have hx := x.isLt
  simp only [BitVec.toNat_ofNat]
  change 0 * 2 ^ 32 + x.toNat = x.toNat % 2 ^ 64
  omega_arith

end VG.Proof.Ed25519.Arm.SignCached
end

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.SignCached
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem init_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa init s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr) [] := by
  refine WP.seq (WP.mono (args_regs_ok hc hL ha (args := [(.r0, .caller 5 0)])
    (by decide) (by simp [Whole.valid]) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.r0, .caller 5 0) (by simp)
  change u.gpr .r0 = L.scr + 0#32 at a0
  rw [BitVec.add_zero] at a0
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  refine WP.mono (Whole.init_call hu (Whole.init_pre a0 hL.nc) (Whole.covers_writes hw) hw a0)
    fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, hp⟩
  rw [hm] at hf
  exact init_frame hf

theorem update_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (count : Nat) (p n : Value) (hc16 : count < 65536) (hp : Whole.valid p) (hn : Whole.valid n)
    (hi : Input L (value L p) (value L n)) {prev : List Byte}
    (hcount : count = prev.length) (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (State.addr L.scr) prev) :
    WP isa (update (setup [(.r0, .caller 5 0), (.r2, .const count), (.r3, .const 0)]
      [p, n, .caller 5 192])) s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr)
        (prev ++ Spec.Ed25519.bytesAt s.mem (State.addr (value L p)) (value L n).toNat) := by
  have hv : ∀ (x : Reg × Value), x ∈ [(.r0, .caller 5 0), (.r2, .const count), (.r3, .const 0)] →
      Whole.valid x.2 := by simp [Whole.valid, hc16]
  have hvs : ∀ v ∈ [p, n, Value.caller 5 192], Whole.valid v := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl)
    · exact hp
    · exact hn
    · simp [Whole.valid]
  refine WP.seq (WP.mono (args_ok hc hL ha (by simp) hv (by simp) hvs (by simp [preserved]))
    fun u ⟨hu, hf, hs, hstack⟩ => ?_)
  have a0 := hs (.r0, .caller 5 0) (by simp)
  have a2 : u.gpr .r2 = BitVec.ofNat 32 count := hs (.r2, .const count) (by simp)
  have a3 : u.gpr .r3 = 0#32 := hs (.r3, .const 0) (by simp)
  have d0 := hstack 0 (by simp)
  have d1 := hstack 1 (by simp)
  have d2 := hstack 2 (by simp)
  change u.gpr .r0 = L.scr + 0#32 at a0
  rw [BitVec.add_zero] at a0
  have args : UpdateArgs L (BitVec.ofNat 32 count) (value L p) (value L n) u := ⟨a0,a2,a3,d0,d1,d2⟩
  have ce : Proof.Sha512.countArm u = BitVec.ofNat 64 prev.length := by
    unfold Proof.Sha512.countArm
    rw [a3,a2,count_zero_high]
    change BitVec.ofNat 64 (count % 2^32) = _
    rw [Nat.mod_eq_of_lt (by omega_arith),hcount]
  have huRepr := setup_repr hL hf hr
  have heq : Spec.Ed25519.bytesAt u.mem (State.addr (value L p)) (value L n).toNat =
      Spec.Ed25519.bytesAt s.mem (State.addr (value L p)) (value L n).toNat :=
    frame_bytes hf ⟨State.addr (value L p), (value L n).toNat⟩
      (by simp only [List.mem_singleton]; intro r he; subst r; exact hi.args)
      (by have := (value L n).isLt; change (value L n).toNat ≤ 2^64; omega_arith)
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  refine WP.mono (Whole.update_call hu (update_pre hL hu.sp args hi) (update_covers hi) hw
    a0 d0 d1 ce huRepr) fun t ⟨ht, hf', hrepr⟩ => ⟨ht, (setup_frame hf).trans (update_frame hf'), ?_⟩
  change Spec.Sha512.Repr _ t.mem _ (prev ++ Spec.Ed25519.bytesAt u.mem (State.addr (value L p)) (value L n).toNat) at hrepr
  rw [heq] at hrepr
  exact hrepr

theorem finalize_count (L : Lay) (n : Nat) (b : Bool) :
    value L (if b then Value.caller 4 n else .const n) =
      BitVec.ofNat 32 ((if b then L.len.toNat else 0) + n) := by
  cases b <;> simp [value, Lay.value, BitVec.ofNat_add]

theorem finalize_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (n : Nat) (hn : n < 256) (b : Bool) {msg : List Byte}
    (hlen : msg.length < 2^32) (hcount : (if b then L.len.toNat else 0) + n = msg.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (State.addr L.scr) msg) :
    WP isa (finalize n b) s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64 = Spec.Sha512.sha512 msg := by
  have hv : ∀ (x : Reg × Value), x ∈ [(.r0, .caller 5 0),
      (.r2, if b then .caller 4 n else .const n), (.r3, .const 0)] → Whole.valid x.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl)
    · simp [Whole.valid]
    · cases b <;> simp [Whole.valid] <;> omega_arith
    · simp [Whole.valid]
  refine WP.seq (WP.mono (args_ok hc hL ha (by simp) hv (by simp)
    (by simp [Whole.valid]) (by simp [preserved])) fun u ⟨hu,hf,hs,hstack⟩ => ?_)
  have a0 := hs (.r0, .caller 5 0) (by simp)
  have a2 := hs (.r2, if b then .caller 4 n else .const n) (by simp)
  have a3 : u.gpr .r3 = 0#32 := hs (.r3, .const 0) (by simp)
  have d0 := hstack 0 (by simp)
  have d1 := hstack 1 (by simp)
  change u.gpr .r0 = L.scr + 0#32 at a0
  rw [BitVec.add_zero] at a0
  rw [finalize_count,hcount] at a2
  have args : FinalArgs L (BitVec.ofNat 32 msg.length) u := ⟨a0,a2,a3,d0,d1⟩
  have ce : Proof.Sha512.countArm u = BitVec.ofNat 64 msg.length := by
    unfold Proof.Sha512.countArm
    rw [a3,a2,count_zero_high]
    change BitVec.ofNat 64 (msg.length % 2^32) = _
    rw [Nat.mod_eq_of_lt hlen]
  refine WP.mono (Whole.finalize_call hu (finalize_pre hL hu.sp args) (finalize_covers hL)
    (final_writes hL) a0 d0 ce (setup_repr hL hf hr) (by omega_arith))
    fun t ⟨ht,hf',hh⟩ => ⟨ht,(setup_frame hf).trans (finalize_frame hL hf'),?_⟩
  change Spec.Ed25519.bytesAt t.mem (State.addr (L.E + 184)) 64 = _ at hh
  rw [final_addr hL] at hh
  exact hh

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.Hashes`. -/
section
/-! Merged from `Proof.Ed25519.Arm.SignCached.HashUpdates`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem update_input (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (source count : Nat) (hj : source < 6) (hc16 : count < 65536) (hi : Input L (L.value source) 32)
    {prev : List Byte} (hcount : count = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (State.addr L.scr) prev) :
    WP isa (update (inputArgs source count)) s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr)
        (prev ++ Spec.Ed25519.bytesAt s.mem (State.addr (L.value source)) 32) := by
  have inp : Input L (value L (.caller source 0)) (value L (.const 32)) := by
    change Input L (L.value source + 0#32) 32#32
    rw [BitVec.add_zero]
    exact hi
  refine WP.mono (update_step hc hL ha count (.caller source 0) (.const 32) hc16
    ⟨hj, by decide⟩ (by simp [Whole.valid]) inp hcount hr) fun t ⟨ht, hf, hh⟩ => ⟨ht, hf, ?_⟩
  change Spec.Sha512.Repr _ t.mem _ (prev ++ Spec.Ed25519.bytesAt s.mem (State.addr (L.value source + 0#32)) 32) at hh
  rw [BitVec.add_zero] at hh
  exact hh

theorem update_prefix (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (State.addr L.scr) []) :
    WP isa (update prefixArgs) s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr)
        (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 56) 32) := by
  refine WP.mono (update_step hc hL ha 0 (.frame 56) (.const 32) (by decide)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (prefix_input hL) rfl hr) fun t ⟨ht, hf, hh⟩ => ⟨ht, hf, ?_⟩
  change Spec.Sha512.Repr _ t.mem _ ([] ++ Spec.Ed25519.bytesAt s.mem (State.addr (L.E + 56)) 32) at hh
  have ae : State.addr (L.E + 56) = State.addr L.E + 56 := frame_addr hL (d := 56) (by decide)
  rw [List.nil_append, ae] at hh
  exact hh

theorem update_message (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (count : Nat) (hc16 : count < 65536) {prev : List Byte} (hcount : count = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (State.addr L.scr) prev) :
    WP isa (update (messageArgs count)) s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr)
        (prev ++ Spec.Ed25519.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  have inp : Input L (value L (.caller 3 0)) (value L (.caller 4 0)) := by
    simpa only [value, Lay.value, BitVec.add_zero] using message_input hL
  refine WP.mono (update_step hc hL ha count (.caller 3 0) (.caller 4 0) hc16
    (by simp [Whole.valid]) (by simp [Whole.valid]) inp hcount hr) fun t ⟨ht, hf, hh⟩ => ⟨ht, hf, ?_⟩
  simp only [value, Lay.value, BitVec.add_zero] at hh
  rw [hc.input_bytes hL (r := L.MSG) (by simp [Lay.inputs]) (by have := L.len.isLt; change L.len.toNat ≤ 2^64; omega_arith)] at hh
  exact hh

end VG.Proof.Ed25519.Arm.SignCached
end

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem hashNonce_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (hashNonce) s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 56) 32 ++
          Spec.Ed25519.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (update_prefix hu hL ha ru) fun v ⟨hv, fv, rv⟩ => ?_)
  have keep := hash_field_bytes hL fu (d := 56) (by decide) (by decide)
  change Spec.Ed25519.bytesAt u.mem (State.addr L.E + (56 : BitVec 64)) 32 = Spec.Ed25519.bytesAt s.mem (State.addr L.E + (56 : BitVec 64)) 32 at keep
  rw [keep] at rv
  refine WP.seq (WP.mono (update_message hv hL ha 32 (by decide) (by rw [bytes_length]) rv)
    fun w ⟨hw, fw, rw'⟩ => ?_)
  refine WP.mono (finalize_step hw hL ha 32 (by decide) true ?_ ?_ rw')
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans (fw.trans ft)), hd⟩
  · rw [List.length_append, bytes_length, bytes_length]
    have := hL.message_bound; omega_arith
  · rw [List.length_append, bytes_length, bytes_length]
    simp only [ite_true]; omega_arith

theorem hashChallenge_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (hashChallenge) s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (State.addr L.out) 32 ++
          Spec.Ed25519.bytesAt m₀ (State.addr L.pk) 32 ++
          Spec.Ed25519.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (update_input hu hL ha 0 0 (by decide) (by decide) (point_input hL)
    (by decide) ru) fun v ⟨hv, fv, rv⟩ => ?_)
  change Spec.Sha512.Repr _ v.mem _ ([] ++ Spec.Ed25519.bytesAt u.mem (State.addr L.out) 32) at rv
  rw [List.nil_append, hash_out_bytes hL fu] at rv
  refine WP.seq (WP.mono (update_input hv hL ha 2 32 (by decide) (by decide) (key_input hL)
    (by rw [bytes_length]) rv) fun w ⟨hw, fw, rw'⟩ => ?_)
  have hk := hv.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  change Spec.Ed25519.bytesAt v.mem (State.addr L.pk) 32 = Spec.Ed25519.bytesAt m₀ (State.addr L.pk) 32 at hk
  change Spec.Sha512.Repr _ w.mem _ (_ ++ Spec.Ed25519.bytesAt v.mem (State.addr L.pk) 32) at rw'
  rw [hk] at rw'
  refine WP.seq (WP.mono (update_message hw hL ha 64 (by decide) (by rw [List.length_append, bytes_length, bytes_length])
    rw') fun z ⟨hz, fz, rz⟩ => ?_)
  refine WP.mono (finalize_step hz hL ha 64 (by decide) true ?_ ?_ rz)
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans (fw.trans (fz.trans ft))), hd⟩
  · rw [List.length_append, List.length_append, bytes_length, bytes_length, bytes_length]
    have := hL.message_bound; omega_arith
  · rw [List.length_append, List.length_append, bytes_length, bytes_length, bytes_length]
    simp only [ite_true]; omega_arith

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.Preserve`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm
variable {L : Lay} {m n : Mem}

theorem single_frame_bytes {d e k : Nat} (hf : Frame [⟨State.addr L.E + BitVec.ofNat 64 e, k⟩] m n)
    (hd : d + 32 ≤ 248) (he : e + k ≤ 248) (hs : d + 32 ≤ e ∨ e + k ≤ d) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by
  apply frame_bytes hf (field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ hs (by omega_arith) (by omega_arith)

theorem reduce_field_bytes (hL : L.Ok) {d out : Nat} (hf : Frame (reduceWr L out) m n)
    (hd : d + 32 ≤ 248) (ho : out + 32 ≤ 248) (hs : d + 32 ≤ out ∨ out + 32 ≤ d) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by
  apply frame_bytes hf (field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Offset.disjoint _ hs (by omega_arith) (by omega_arith)
  · exact field_scr hL hd

theorem base_field_bytes (hL : L.Ok) (hf : Frame (baseWr L) m n) {d : Nat} (hd : d + 32 ≤ 248) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by
  apply frame_bytes hf (field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [baseWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact (hL.ko.sub_left (fieldWithin L hd).sub).sub_right (baseWithin L).sub
  · exact field_scr hL hd

theorem reduce_out_bytes (hL : L.Ok) {d : Nat} (hf : Frame (reduceWr L d) m n) (hd : d + 32 ≤ 248) :
    Spec.Ed25519.bytesAt n (State.addr L.out) 32 = Spec.Ed25519.bytesAt m (State.addr L.out) 32 := by
  apply frame_bytes hf (baseOut L) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact ((hL.ko.sub_left (fieldWithin L hd).sub).sub_right (baseWithin L).sub).symm
  · exact hL.oc.sub_left (baseWithin L).sub

end VG.Proof.Ed25519.Arm.SignCached
end

/-! Merged from `Proof.Ed25519.Arm.SignCached.Prefix`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached

structure PrefixStep (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  regs : ∀ r, r ≠ .r0 → r ≠ .r12 → t.gpr r = s.gpr r

theorem PrefixStep.trans {s t u : State} (h : PrefixStep s t) (h' : PrefixStep t u) : PrefixStep s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp,
    fun r h0 h15 => (h'.regs r h0 h15).trans (h.regs r h0 h15)⟩

theorem copyWord_ok {s : State} {E : BitVec 32} (he : s.sp = E)
    (hf : E.toNat + 248 ≤ 2 ^ 32) (hr : (⟨State.addr E, 248⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < 8) :
    WP isa (.block (copyWord k)) s fun t => PrefixStep s t ∧
      t.mem = s.mem.writeW (State.addr E + BitVec.ofNat 64 (56 + 4 * k))
        (s.mem.readW (State.addr E + BitVec.ofNat 64 (216 + 4 * k)) 32) := by
  have ae : State.addr (E + BitVec.ofNat 32 (216 + 4 * k)) = State.addr E + BitVec.ofNat 64 (216 + 4 * k) :=
    addr_add (by omega_arith)
  have ad : State.addr (E + BitVec.ofNat 32 (56 + 4 * k)) = State.addr E + BitVec.ofNat 64 (56 + 4 * k) :=
    addr_add (by omega_arith)
  have source : InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 (216 + 4 * k)) 4 :=
    ⟨⟨State.addr E, 248⟩, List.mem_append_right _ hr, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have dest : InRegions s.wr (State.addr E + BitVec.ofNat 64 (56 + 4 * k)) 4 :=
    ⟨⟨State.addr E, 248⟩, hr, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hl : exec (.ldrSp .r0 (216 + 4 * k)) s =
      some (s.setReg .r0 (s.mem.readW (State.addr E + BitVec.ofNat 64 (216 + 4 * k)) 32)) := by
    simp only [exec, show 216 + 4 * k < 4096 from by omega_arith, ite_true,
      State.load32, he, ae, source, Option.map_some]
  have ha {t : State} : exec (.addSp .r12 0) t = some (t.setReg .r12 t.sp) := by
    simp only [exec, show 0 < 256 from by decide, ite_true, BitVec.add_zero]
  apply WP.of_runBlock
  simp only [copyWord, runBlock_cons, runStep_some, hl, ha, RegUpd.sp_setReg]
  rw [exec_str (by omega_arith) (by
    simpa only [RegUpd.wr_setReg, RegUpd.gpr_setReg_self, he, ad] using dest)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, ?_⟩, ?_⟩
  · intro r h0 h12
    simp only [RegUpd.gpr_setReg, h0, h12, ite_false]
  · simp only [RegUpd.mem_setReg, RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false, he, ad]

structure PrefixInv (E : BitVec 32) (s : State) (n : Nat) (t : State) : Prop where
  step : PrefixStep s t
  frame : Frame [⟨State.addr E + BitVec.ofNat 64 56, 32⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (State.addr E + BitVec.ofNat 64 (56 + 4 * j)) 32 =
    s.mem.readW (State.addr E + BitVec.ofNat 64 (216 + 4 * j)) 32

theorem copyPrefix_ok {s : State} {E : BitVec 32} (he : s.sp = E)
    (hf : E.toNat + 248 ≤ 2 ^ 32) (hw : (⟨State.addr E, 248⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap copyWord)) s (PrefixInv E s n)
  | 0, _ => WP.block_nil ⟨⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩, Frame.refl _ _, fun _ h => by omega_arith⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyPrefix_ok he hf hw n (by omega_arith)) fun u hu => ?_
    refine WP.mono (copyWord_ok (hu.step.sp.trans he) hf (hu.step.wr ▸ hw) (by omega_arith : n < 8))
      fun t ⟨kt, mt⟩ => ?_
    have same : u.mem.readW (State.addr E + BitVec.ofNat 64 (216 + 4 * n)) 32 =
        s.mem.readW (State.addr E + BitVec.ofNat 64 (216 + 4 * n)) 32 := by
      apply hu.frame.readW (Region.contains_self _ _) _ (by decide)
      simp only [List.mem_singleton]
      rintro r rfl
      exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by decide)
    rw [same] at mt
    refine ⟨hu.step.trans kt, ?_, fun j hj => ?_⟩
    · rw [mt]
      exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_arith) (by omega_arith) (by decide))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (a := State.addr E + BitVec.ofNat 64 (56 + 4 * j))
          (b := State.addr E + BitVec.ofNat 64 (56 + 4 * n)) ?_ (by decide)]
        · exact hu.words j (by omega_arith)
        · exact Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem prefix_ok {s : State} {E : BitVec 32} (he : s.sp = E)
    (hf : E.toNat + 248 ≤ 2 ^ 32) (hw : (⟨State.addr E, 248⟩ : Region) ∈ s.wr) :
    WP isa (.block copyPrefix) s fun t => PrefixStep s t ∧
      Frame [⟨State.addr E + 56, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr E + 56) 32 =
        Spec.Ed25519.bytesAt s.mem (State.addr E + 216) 32 := by
  refine WP.mono (copyPrefix_ok he hf hw 8 (by decide)) fun t ht => ⟨ht.step, ht.frame, ?_⟩
  unfold Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ed : State.addr E + 56 + BitVec.ofNat 64 i =
      (State.addr E + BitVec.ofNat 64 (56 + 4 * (i / 4))) + BitVec.ofNat 64 (i % 4) := by
    change State.addr E + BitVec.ofNat 64 56 + BitVec.ofNat 64 i = _
    rw [Offset.add_add, Offset.add_add]
    exact congrArg (fun n => State.addr E + BitVec.ofNat 64 n) (by omega_arith)
  have es : State.addr E + 216 + BitVec.ofNat 64 i =
      (State.addr E + BitVec.ofNat 64 (216 + 4 * (i / 4))) + BitVec.ofNat 64 (i % 4) := by
    change State.addr E + BitVec.ofNat 64 216 + BitVec.ofNat 64 i = _
    rw [Offset.add_add, Offset.add_add]
    exact congrArg (fun n => State.addr E + BitVec.ofNat 64 n) (by omega_arith)
  rw [ed, es, Mem.readW_byte t.mem _ (i := i % 4) (Nat.mod_lt _ (by decide)),
    Mem.readW_byte s.mem _ (i := i % 4) (Nat.mod_lt _ (by decide)), ht.words (i / 4) (by omega_arith)]

end VG.Proof.Ed25519.Arm.SignCached
end

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem prune_ctx {t : State} (hc : Ctx L g m₀ s) (ht : PublicKey.Step s t)
    (hf : Frame [⟨State.addr L.E + 24, 32⟩] s.mem t.mem) : Ctx L g m₀ t := by
  refine hc.of_frame ht.rd ht.wr ht.sp ?_ hf ?_
  · intro r hr _
    apply ht.regs <;> rintro rfl <;> simp [preserved] at hr
  · intro r hr; rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by decide : 24 + 32 ≤ 248))

theorem prefix_ctx {t : State} (hc : Ctx L g m₀ s) (ht : PrefixStep s t)
    (hf : Frame [⟨State.addr L.E + BitVec.ofNat 64 56, 32⟩] s.mem t.mem) : Ctx L g m₀ t := by
  refine hc.of_frame ht.rd ht.wr ht.sp ?_ hf ?_
  · intro r hr _
    apply ht.regs <;> rintro rfl <;> simp [preserved] at hr
  · intro r hr; rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by decide : 56 + 32 ≤ 248))

theorem saveSecret_ok (hc : Ctx L g m₀ s) (hL : L.Ok) {expanded : List Byte}
    (he : Spec.Ed25519.bytesAt s.mem (State.addr L.E + 184) 64 = expanded) :
    WP isa (.block saveSecret) s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32 =
        Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune expanded) ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 56) 32 = expanded.drop 32 := by
  rw [saveSecret, WP.block_append_iff]
  have fr : (⟨State.addr L.E, 248⟩ : Region) ∈ s.wr := by rw [hc.wr]; exact List.mem_cons_self
  have fit : L.E.toNat + 248 ≤ 2 ^ 32 := by have := hL.top; omega_arith
  refine WP.mono (PublicKey.prune_ok hc.sp fit fr he) fun u ⟨hu, hf, hs⟩ => ?_
  have hcu := prune_ctx hc hu hf
  refine WP.mono (prefix_ok hcu.sp fit (by rw [hcu.wr]; exact List.mem_cons_self))
    fun t ⟨ht, hft, hp⟩ => ⟨prefix_ctx hcu ht hft, ?_, ?_⟩
  · have keep := single_frame_bytes (L := L) hft (d := 24) (by decide) (by decide) (by decide)
    change Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32 = Spec.Ed25519.bytesAt u.mem (State.addr L.E + 24) 32 at keep
    rw [keep]
    have sc := Proof.Ed25519.bytesAt_encodeLE u.mem (State.addr L.E + 24) 32
    change Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem (State.addr L.E + 24) 32) = Spec.Ed25519.prune expanded at hs
    rw [hs] at sc
    exact sc
  · rw [hp]
    have keep := single_frame_bytes (L := L) (e := 24) (k := 32) hf (d := 216)
      (by decide) (by decide) (by decide)
    change Spec.Ed25519.bytesAt u.mem (State.addr L.E + 216) 32 = Spec.Ed25519.bytesAt s.mem (State.addr L.E + 216) 32 at keep
    rw [keep, ← he, Proof.Ed25519.signatureBytes_drop]
    rw [BitVec.add_assoc, show (184 : BitVec 64) + BitVec.ofNat 64 32 = (216 : BitVec 64) from rfl]

def scalar (E : List Byte) : List Byte := Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune E)
def nonce (L : Lay) (E : List Byte) (m : Mem) : List Byte := Spec.Ed25519.scalarReduce (Spec.Sha512.sha512
  (E.drop 32 ++ Spec.Ed25519.bytesAt m (State.addr L.msg) L.len.toNat))

/-- The digest `E` left at `frame 184` by the first step of signing. -/
def DigestReady (L : Lay) (E : List Byte) (t : State) : Prop :=
  Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64 = E

structure SecretReady (L : Lay) (E : List Byte) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32 = scalar E
  prefixBytes : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 56) 32 = E.drop 32

theorem secret_ok (hc : Ctx L g m₀ s) (hL : L.Ok) {E : List Byte} (hd : DigestReady L E s) :
    WP isa (.block saveSecret) s fun t => Ctx L g m₀ t ∧ SecretReady L E t :=
  WP.mono (saveSecret_ok hc hL hd) fun _ ⟨ht, hs, hp⟩ => ⟨ht, hs, hp⟩

end VG.Proof.Ed25519.Arm.SignCached
