import VerifiedGarbage.Proof.Ed448.Arm.SignCached.Hash
import VerifiedGarbage.Proof.Ed448.Arm.ScalarVerified
import VerifiedGarbage.Proof.Ed448.Arm.ScalarLit
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wipe

/-!
# Ed448 signing with a cached public key on ARMv7: the scalar calls

`reduceR_step`: `r`, the nonce's hash reduced modulo `L`, into the second
half of `out`; `base_step`: `R = [r]B` into its first half, given the
reference ladder's agreement with the specification (`BaseLadderOk`, a
hypothesis); `reduceK_step`: `k` at `K`; `mulAdd_step`:
`S = (r + k s) mod L` over `r` (`vg_ed448_scalar_mul_add`'s output may be
one of its inputs); `wipe_step`: the locals cleared. Each through
`Whole.call_ok` with the callee's contract on this target, and stating what
it may write.
-/

namespace VG.Proof.Ed448.Arm.SignCached

open VG VG.Arm VG.Impl.Ed448.Arm.SignCached VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.Ctx Whole.FR Whole.Within Whole.call_ok Whole.Ctx.zeroWords)
open VG.Proof.Ed448.Arm.Shake (Slot valid Kit Args argVal kWr kArgs valid_const valid_frame frame_within
  frame_bytes bytes_setup)
open VG.Proof.Ed448.Arm (scalarReduceLocal scalarReduce_ok scalarBaseLocal scalarBase_ok scalarMulAddLocal
  scalarMulAdd_ok)
open VG.Proof.Ed448 (BaseLadderOk)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem W.call {ex : List Region} {k : Nat} (hk : k ≤ 8) {m1 m2 m3 : Mem}
    (h1 : Frame [⟨State.addr L.E, k⟩] m1 m2) (h2 : Frame ex m2 m3) : Frame (W L ex) m1 m3 := by
  refine (Frame.sub h1 fun r hr => ⟨kArgs L.E 8, List.mem_cons_self, ?_⟩).trans
    (h2.mono fun r hr => List.mem_cons_of_mem _ (List.mem_append_left _ hr))
  rw [List.mem_singleton.mp hr]
  exact Region.sub_prefix hk

theorem gpr_entry {s : State} {rd wr : List Region} {r : Reg} (hr : r ∉ linkRegs) :
    (s.callEntry.withRegions rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

/-! ## `r` -/

theorem reduce_noFrames : Impl.Ed448.Arm.scalarReduce.noFrames = true := by lit_decide

def ReduceArgs (L : Lay) (out wide : BitVec 32) (t : State) : Prop :=
  t.gpr .r0 = out ∧ t.gpr .r1 = wide ∧ t.gpr .r2 = L.scr

/-- `vg_ed448_scalar_reduce` from 114 bytes of the frame at `HASH` into `O`. -/
theorem reduce_pre (hL : L.Ok) {o : BitVec 32} {O : Region} (hO : O = ⟨State.addr o, 57⟩)
    (hof : o.toNat + 57 ≤ 2 ^ 32) (hoh : O.Disjoint (L.fr HASH 114)) (hos : O.Disjoint L.SCR)
    (ha : ReduceArgs L o (L.E + BitVec.ofNat 32 HASH) t) :
    scalarReduceLocal.pre (t.callEntry.withRegions [L.fr HASH 114] [O, L.SCR]) := by
  obtain ⟨h0, h1, h2⟩ := ha
  subst hO
  simp only [scalarReduceLocal]
  rw [gpr_entry (by decide : Reg.r0 ∉ linkRegs), gpr_entry (by decide : Reg.r1 ∉ linkRegs),
    gpr_entry (by decide : Reg.r2 ∉ linkRegs), h0, h1, h2, State.withRegions_rd, State.withRegions_wr,
    hL.kit.frame_addr (by decide)]
  exact ⟨rfl, rfl, hoh, hos, hL.kit.stack_scr (by decide), hof, hL.kit.frame_fit (by decide), hL.nc⟩

theorem reduce_covers {O : Region} (hO : Whole.Within O (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within O R) :
    Covers ([L.fr HASH 114] ++ [O, L.SCR]) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Shake.covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inl (frame_within _ (by decide))
  · rcases hO with h | ⟨R, hR, h⟩
    · exact .inl h
    · exact .inr ⟨R, List.mem_append_right _ hR, h⟩
  · exact .inr ⟨L.SCR, List.mem_append_right _ (scr_in L), scr_within L⟩

theorem reduce_writes {O : Region} (hO : Whole.Within O (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within O R) :
    ∀ r ∈ [O, L.SCR], Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hO
  · exact .inr ⟨L.SCR, scr_in L, scr_within L⟩

/-- The call, from its arguments in registers. -/
theorem reduce_call (hc : Ctx L g m₀ t) (hL : L.Ok) {o : BitVec 32} {O : Region} (hO : O = ⟨State.addr o, 57⟩)
    (hof : o.toNat + 57 ≤ 2 ^ 32) (hoh : O.Disjoint (L.fr HASH 114)) (hos : O.Disjoint L.SCR)
    (hw : Whole.Within O (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within O R)
    (ha : ReduceArgs L o (L.E + BitVec.ofNat 32 HASH) t) :
    WP isa (.call "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce) t fun u => Ctx L g m₀ u ∧
      Frame [O, L.SCR] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (State.addr o) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114) := by
  refine Whole.call_ok hc scalarReduce_ok reduce_noFrames (reduce_pre hL hO hof hoh hos ha) (reduce_covers hw)
    (reduce_writes hw) fun v hv hf hp => ⟨hv, hf, ?_⟩
  change Spec.Ed448.bytesAt v.mem (State.addr (t.callEntry.gpr .r0)) 57 =
    Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem (State.addr (t.callEntry.gpr .r1)) 114) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), ha.1, ha.2.1, hL.kit.frame_addr (by decide)] at hp
  exact hp

/-- `r` into the second half of `out`. -/
theorem reduceR_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith reduceRArgs "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce) t fun u =>
      Ctx L g m₀ u ∧ Frame (W L [L.ob 57 57, L.SCR]) t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.out + BitVec.ofNat 64 57) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114) := by
  refine WP.seq (WP.mono (hL.kit.setup_ok hc ha
    (args := [(.r0, .caller 0 57), (.r1, .frame HASH), (.r2, .caller SC 0)]) (stk := [])
    (by decide) (by simp only [List.forall_mem_cons]
                    exact ⟨⟨by decide, by decide⟩, valid_frame (by decide), ⟨by decide, by decide⟩, fun _ h => nomatch h⟩)
    (by simp [preserved]) (by decide) (by simp))
    fun u ⟨hu, hm, hs, _⟩ => ?_)
  have h0 := hs (.r0, .caller 0 57) (by simp)
  have h1 := hs (.r1, .frame HASH) (by simp)
  have h2 := hs (.r2, .caller SC 0) (by simp)
  simp only [argVal, Lay.value, SC, BitVec.add_zero] at h0 h1 h2
  have he := bytes_setup hm (D := L.fr HASH 114) (Shake.frame_out (by decide) (by decide)) (by change 114 ≤ 2 ^ 64; decide)
  simp only at he
  refine WP.mono (reduce_call hu hL (o := L.out + BitVec.ofNat 32 57) (O := L.ob 57 57)
    (by rw [hL.ob_addr (by decide)]) (hL.ob_fit (by decide) (by decide)) (hL.ob_stk (by decide) (by decide))
    (hL.ob_scr (by decide)) (.inr ⟨L.OUT, out_in L, Lay.Ok.ob_within (by decide)⟩) ⟨h0, h1, h2⟩)
    fun v ⟨hv, hf, hp⟩ => ⟨hv, W.call (by simp) hm hf, ?_⟩
  rw [← hL.ob_addr (by decide), hp, he]

/-! ## `R` -/

theorem base_noFrames : Impl.Ed448.Arm.scalarBase.noFrames = true := PublicKey.base_noFrames

def BaseArgs (L : Lay) (t : State) : Prop :=
  t.gpr .r0 = L.out ∧ t.gpr .r1 = L.out + BitVec.ofNat 32 57 ∧ t.gpr .r2 = L.scr

theorem base_pre (hL : L.Ok) (ha : BaseArgs L t) :
    scalarBaseLocal.pre (t.callEntry.withRegions [L.ob 57 57] [L.R0, L.SCR]) := by
  obtain ⟨h0, h1, h2⟩ := ha
  simp only [scalarBaseLocal]
  rw [gpr_entry (by decide : Reg.r0 ∉ linkRegs), gpr_entry (by decide : Reg.r1 ∉ linkRegs),
    gpr_entry (by decide : Reg.r2 ∉ linkRegs), h0, h1, h2, State.withRegions_rd, State.withRegions_wr,
    hL.ob_addr (by decide)]
  exact ⟨rfl, rfl, hL.oc.sub_left (r0_sub L), hL.ob_scr (by decide), by have := hL.no; omega,
    hL.ob_fit (by decide) (by decide), hL.nc⟩

theorem base_covers (L : Lay) : Covers ([L.ob 57 57] ++ [L.R0, L.SCR]) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Shake.covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr ⟨L.OUT, List.mem_append_right _ (out_in L), Lay.Ok.ob_within (by decide)⟩
  · exact .inr ⟨L.OUT, List.mem_append_right _ (out_in L), r0_within L⟩
  · exact .inr ⟨L.SCR, List.mem_append_right _ (scr_in L), scr_within L⟩

theorem base_writes (L : Lay) : ∀ r ∈ [L.R0, L.SCR],
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inr ⟨L.OUT, out_in L, r0_within L⟩
  · exact .inr ⟨L.SCR, scr_in L, scr_within L⟩

theorem base_step (hl : BaseLadderOk) (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith baseArgs "vg_ed448_scalar_base" Impl.Ed448.Arm.scalarBase) t fun u =>
      Ctx L g m₀ u ∧ Frame (W L [L.R0, L.SCR]) t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.out) 57 =
        Spec.Ed448.scalarBase (Spec.Ed448.bytesAt t.mem (State.addr L.out + BitVec.ofNat 64 57) 57) := by
  refine WP.seq (WP.mono (hL.kit.setup_ok hc ha
    (args := [(.r0, .caller 0 0), (.r1, .caller 0 57), (.r2, .caller SC 0)]) (stk := [])
    (by decide) (by simp only [List.forall_mem_cons]
                    exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, fun _ h => nomatch h⟩)
    (by simp [preserved]) (by decide) (by simp))
    fun u ⟨hu, hm, hs, _⟩ => ?_)
  have h0 := hs (.r0, .caller 0 0) (by simp)
  have h1 := hs (.r1, .caller 0 57) (by simp)
  have h2 := hs (.r2, .caller SC 0) (by simp)
  simp only [argVal, Lay.value, SC, BitVec.add_zero] at h0 h1 h2
  have he := frame_bytes hm (D := L.ob 57 57) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (hL.ko.sub_left (Region.sub_prefix (by decide))).symm.sub_left
      (Lay.Ok.ob_sub (by decide))) (by change 57 ≤ 2 ^ 64; decide)
  simp only at he
  refine Whole.call_ok hu (scalarBase_ok hl) base_noFrames (base_pre hL ⟨h0, h1, h2⟩) (base_covers L)
    (base_writes L) fun v hv hf hp => ⟨hv, W.call (by simp) hm hf, ?_⟩
  change Spec.Ed448.bytesAt v.mem (State.addr (u.callEntry.gpr .r0)) 57 =
    Spec.Ed448.scalarBase (Spec.Ed448.bytesAt u.mem (State.addr (u.callEntry.gpr .r1)) 57) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), h0, h1, hL.ob_addr (by decide), he] at hp
  exact hp

/-! ## `k` -/

theorem reduceK_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith reduceKArgs "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce) t fun u =>
      Ctx L g m₀ u ∧ Frame (W L [L.fr K 57, L.SCR]) t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 K) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114) := by
  refine WP.seq (WP.mono (hL.kit.setup_ok hc ha
    (args := [(.r0, .frame K), (.r1, .frame HASH), (.r2, .caller SC 0)]) (stk := [])
    (by decide) (by simp only [List.forall_mem_cons]
                    exact ⟨valid_frame (by decide), valid_frame (by decide), ⟨by decide, by decide⟩, fun _ h => nomatch h⟩)
    (by simp [preserved]) (by decide) (by simp))
    fun u ⟨hu, hm, hs, _⟩ => ?_)
  have h0 := hs (.r0, .frame K) (by simp)
  have h1 := hs (.r1, .frame HASH) (by simp)
  have h2 := hs (.r2, .caller SC 0) (by simp)
  simp only [argVal, Lay.value, SC, BitVec.add_zero] at h0 h1 h2
  have he := bytes_setup hm (D := L.fr HASH 114) (Shake.frame_out (by decide) (by decide)) (by change 114 ≤ 2 ^ 64; decide)
  simp only at he
  refine WP.mono (reduce_call hu hL (o := L.E + BitVec.ofNat 32 K) (O := L.fr K 57)
    (by rw [hL.kit.frame_addr (by decide)]) (hL.kit.frame_fit (by decide)) (fr_fr (by decide) (by decide) (by decide))
    (hL.kit.stack_scr (by decide)) (.inl (frame_within _ (by decide))) ⟨h0, h1, h2⟩)
    fun v ⟨hv, hf, hp⟩ => ⟨hv, W.call (by simp) hm hf, ?_⟩
  rw [← hL.kit.frame_addr (by decide), hp, he]

/-! ## `S` -/

theorem mulAdd_noFrames : Impl.Ed448.Arm.scalarMulAdd.noFrames = true := by lit_decide

def MulArgs (L : Lay) (t : State) : Prop :=
  t.gpr .r0 = L.out + BitVec.ofNat 32 57 ∧ t.gpr .r1 = L.out + BitVec.ofNat 32 57 ∧
    t.gpr .r2 = L.E + BitVec.ofNat 32 K ∧ t.gpr .r3 = L.E + BitVec.ofNat 32 S ∧ stackArg t 0 = L.scr

def mulRd (L : Lay) : List Region := [L.ob 57 57, L.fr K 57, L.fr S 57, kArgs L.E 4]

theorem mul_pre (hL : L.Ok) (he : t.sp = L.E) (ha : MulArgs L t) :
    scalarMulAddLocal.pre (t.callEntry.withRegions (mulRd L) [L.ob 57 57, L.SCR]) := by
  obtain ⟨h0, h1, h2, h3, a0⟩ := ha
  have sa : stackArg (t.callEntry.withRegions (mulRd L) [L.ob 57 57, L.SCR]) 0 = stackArg t 0 := rfl
  have spa : State.addr (t.callEntry.withRegions (mulRd L) [L.ob 57 57, L.SCR]).sp = State.addr L.E := by
    simp [State.withRegions_sp, State.callEntry_sp, he]
  simp only [scalarMulAddLocal]
  rw [gpr_entry (by decide : Reg.r0 ∉ linkRegs), gpr_entry (by decide : Reg.r1 ∉ linkRegs),
    gpr_entry (by decide : Reg.r2 ∉ linkRegs), gpr_entry (by decide : Reg.r3 ∉ linkRegs), h0, h1, h2, h3,
    sa, a0, spa, State.withRegions_rd, State.withRegions_wr, hL.ob_addr (by decide),
    hL.kit.frame_addr (by decide), hL.kit.frame_addr (by decide)]
  have ht := hL.kit.top
  have hsp : (t.callEntry.withRegions (mulRd L) [L.ob 57 57, L.SCR]).sp = L.E := by
    simp [State.withRegions_sp, State.callEntry_sp, he]
  refine ⟨rfl, rfl, hL.ob_scr (by decide), hL.ob_scr (by decide), hL.kit.stack_scr (by decide),
    hL.kit.stack_scr (by decide),
    (hL.ko.sub_left (Region.sub_prefix (by decide : 4 ≤ 280))).symm.sub_left (Lay.Ok.ob_sub (by decide)),
    (hL.kc.sub_left (Region.sub_prefix (by decide : 4 ≤ 280))).symm,
    hL.ob_fit (by decide) (by decide), hL.ob_fit (by decide) (by decide), hL.kit.frame_fit (by decide),
    hL.kit.frame_fit (by decide), hL.nc, by rw [hsp]; omega⟩

theorem mul_covers (L : Lay) : Covers (mulRd L ++ [L.ob 57 57, L.SCR]) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Shake.covers_of fun r hr => ?_
  simp only [mulRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨L.OUT, List.mem_append_right _ (out_in L), Lay.Ok.ob_within (by decide)⟩
  · exact .inl (frame_within _ (by decide))
  · exact .inl (frame_within _ (by decide))
  · exact .inl (Shake.args_within _ (by decide))
  · exact .inr ⟨L.OUT, List.mem_append_right _ (out_in L), Lay.Ok.ob_within (by decide)⟩
  · exact .inr ⟨L.SCR, List.mem_append_right _ (scr_in L), scr_within L⟩

theorem mul_writes (L : Lay) : ∀ r ∈ [L.ob 57 57, L.SCR],
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inr ⟨L.OUT, out_in L, Lay.Ok.ob_within (by decide)⟩
  · exact .inr ⟨L.SCR, scr_in L, scr_within L⟩

theorem mulAdd_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith mulAddArgs "vg_ed448_scalar_mul_add" Impl.Ed448.Arm.scalarMulAdd) t fun u =>
      Ctx L g m₀ u ∧ Frame (W L [L.ob 57 57, L.SCR]) t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.out + BitVec.ofNat 64 57) 57 =
        Spec.Ed448.scalarMulAdd (Spec.Ed448.bytesAt t.mem (State.addr L.out + BitVec.ofNat 64 57) 57)
          (Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 K) 57)
          (Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 S) 57) := by
  refine WP.seq (WP.mono (hL.kit.setup_ok hc ha
    (args := [(.r0, .caller 0 57), (.r1, .caller 0 57), (.r2, .frame K), (.r3, .frame S)]) (stk := [.caller SC 0])
    (by decide) (by simp only [List.forall_mem_cons]; exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
      valid_frame (by decide), valid_frame (by decide), fun _ h => nomatch h⟩)
    (by simp [preserved]) (by decide)
    (by simp only [List.forall_mem_cons]; exact ⟨⟨by decide, by decide⟩, fun _ h => nomatch h⟩))
    fun u ⟨hu, hm, hs, st, _⟩ => ?_)
  have h0 := hs (.r0, .caller 0 57) (by simp)
  have h1 := hs (.r1, .caller 0 57) (by simp)
  have h2 := hs (.r2, .frame K) (by simp)
  have h3 := hs (.r3, .frame S) (by simp)
  have a0 := st 0 (by simp)
  simp only [argVal, Lay.value, SC, BitVec.add_zero, List.getElem_cons_zero] at h0 h1 h2 h3 a0
  have eo := frame_bytes hm (D := L.ob 57 57) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (hL.ko.sub_left (Region.sub_prefix (by decide))).symm.sub_left
      (Lay.Ok.ob_sub (by decide))) (by change 57 ≤ 2 ^ 64; decide)
  have ek := bytes_setup hm (D := L.fr K 57) (Shake.frame_out (by decide) (by decide)) (by change 57 ≤ 2 ^ 64; decide)
  have es := bytes_setup hm (D := L.fr S 57) (Shake.frame_out (by decide) (by decide)) (by change 57 ≤ 2 ^ 64; decide)
  simp only at eo ek es
  refine Whole.call_ok hu scalarMulAdd_ok mulAdd_noFrames (mul_pre hL hu.sp ⟨h0, h1, h2, h3, a0⟩) (mul_covers L)
    (mul_writes L) fun v hv hf hp => ⟨hv, W.call (by decide) hm hf, ?_⟩
  change Spec.Ed448.bytesAt v.mem (State.addr (u.callEntry.gpr .r0)) 57 =
    Spec.Ed448.scalarMulAdd (Spec.Ed448.bytesAt u.mem (State.addr (u.callEntry.gpr .r1)) 57)
      (Spec.Ed448.bytesAt u.mem (State.addr (u.callEntry.gpr .r2)) 57)
      (Spec.Ed448.bytesAt u.mem (State.addr (u.callEntry.gpr .r3)) 57) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    h0, h1, h2, h3, hL.ob_addr (by decide), hL.kit.frame_addr (by decide), hL.kit.frame_addr (by decide),
    eo, ek, es] at hp
  exact hp

/-! ## The locals, cleared -/

theorem wipe_step (hc : Ctx L g m₀ t) (hL : L.Ok) :
    WP isa (.block wipe) t fun u => Ctx L g m₀ u ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.out) 114 = Spec.Ed448.bytesAt t.mem (State.addr L.out) 114 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (by have := hL.top; omega) (start := 2) (count := 60) (by decide))
    fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  refine frame_bytes hf (D := L.OUT) (fun r hr => ?_) (by change 114 ≤ 2 ^ 64; decide)
  rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 4 * 2 + 4 * 60 ≤ 280))).symm

end VG.Proof.Ed448.Arm.SignCached
