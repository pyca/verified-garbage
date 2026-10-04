import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Hash
import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Prune
import VerifiedGarbage.Proof.Ed448.Arm.BaseVerified
import VerifiedGarbage.Proof.Ed448.Arm.BaseLit
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wipe
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wrap
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-!
# Ed448 public-key derivation on ARMv7: the pruning, the scalar's call, and the whole

`prune_step`: the hash's first 57 bytes pruned in place (`Spec.Ed448.prune`);
`base_step`: `vg_ed448_scalar_base` called on them, given the reference
ladder's agreement with the specification (`BaseLadderOk`, a hypothesis);
`wipe_step`: the frame cleared. `publicKey_ok`: the whole function, in
Ed25519's frame on this target (`Whole.wrap_ok`).
-/

namespace VG.Proof.Ed448.Arm.PublicKey

open VG VG.Arm VG.Impl.Ed448.Arm.PublicKey VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.Within Whole.FR Whole.valid Whole.call_ok Whole.Ctx.zeroWords
  Whole.base Whole.base_addr Whole.base_top Whole.stack Whole.Saved Whole.entered Whole.saved_ctx
  Whole.saved_words Whole.bodyRd Whole.bodyWr Whole.wrap_ok)
open VG.Proof.X448.Arm (writeW8_apply off_eq_iff)
open VG.Proof.Ed448 (BaseLadderOk)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

/-- Where the hash, and then the scalar, is. -/
abbrev hq (L : Lay) : Addr := State.addr L.E + BitVec.ofNat 64 HASH

/-! ## Pruning -/

theorem bytesAt_take57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  simp [Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem pruned_value {m : Mem} {q : Addr} :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt (((m.writeW q (BitVec.ofNat 8 ((m q).toNat &&& 252))).writeW
        (q + BitVec.ofNat 64 55) (BitVec.ofNat 8 ((m (q + BitVec.ofNat 64 55)).toNat ||| 128))).writeW
          (q + BitVec.ofNat 64 56) (0 : BitVec 8)) q 57) =
      (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m q 57) &&& (2 ^ 448 - 4)) ||| 2 ^ 447 := by
  have ne : ∀ i j, i < 57 → j < 57 → i ≠ j → q + BitVec.ofNat 64 i ≠ q + BitVec.ofNat 64 j :=
    fun i j hi hj h e => h ((off_eq_iff q (by omega) (by omega)).mp e)
  have z : q + BitVec.ofNat 64 0 = q := BitVec.add_zero q
  have ne0 : ∀ j, 0 < j → j < 57 → q + BitVec.ofNat 64 j ≠ q := fun j h1 h2 e =>
    absurd ((off_eq_iff q (d := j) (e := 0) (by omega) (by omega)).mp (e.trans z.symm)) (by omega)
  generalize hm' : ((m.writeW q (BitVec.ofNat 8 ((m q).toNat &&& 252))).writeW
        (q + BitVec.ofNat 64 55) (BitVec.ofNat 8 ((m (q + BitVec.ofNat 64 55)).toNat ||| 128))).writeW
          (q + BitVec.ofNat 64 56) (0 : BitVec 8) = m'
  have mid : Spec.Ed448.bytesAt m' (q + BitVec.ofNat 64 1) 54 = Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54 := by
    unfold Spec.Ed448.bytesAt
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [← hm', Offset.add_add, writeW8_apply, ite_eq_right (ne (1 + i) 56 (by omega) (by omega) (by omega)),
      writeW8_apply, ite_eq_right (ne (1 + i) 55 (by omega) (by omega) (by omega)), writeW8_apply,
      ite_eq_right (ne0 (1 + i) (by omega) (by omega))]
  have e0 : m' q = BitVec.ofNat 8 ((m q).toNat &&& 252) := by
    rw [← hm', writeW8_apply, ite_eq_right (ne0 56 (by omega) (by omega)).symm,
      writeW8_apply, ite_eq_right (ne0 55 (by omega) (by omega)).symm,
      writeW8_apply, ite_eq_left rfl]
  have e55 : m' (q + BitVec.ofNat 64 55) = BitVec.ofNat 8 ((m (q + BitVec.ofNat 64 55)).toNat ||| 128) := by
    rw [← hm', writeW8_apply, ite_eq_right (ne 55 56 (by omega) (by omega) (by omega)),
      writeW8_apply, ite_eq_left rfl]
  have e56 : m' (q + BitVec.ofNat 64 56) = BitVec.ofNat 8 0 := by
    rw [← hm', writeW8_apply, ite_eq_left rfl]; rfl
  rw [decodeLE_split, decodeLE_split, mid, e0, e55, e56]
  have h0 := (m q).isLt
  have h55 := (m (q + BitVec.ofNat 64 55)).isLt
  have hl : (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54).length = 54 := by simp [Spec.Ed448.bytesAt]
  have hM' := Proof.Ed448.decodeLE_lt' (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54)
  rw [hl] at hM'
  have hM : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54) < 2 ^ 432 :=
    Nat.lt_of_lt_of_le hM' (Nat.le_of_eq (by decide +kernel))
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left h0),
    Nat.mod_eq_of_lt (Nat.or_lt_two_pow (n := 8) h55 (by decide))]
  have kk := Proof.Ed448.prune_bytes (b56 := (m (q + BitVec.ofNat 64 56)).toNat) h0 hM h55
  exact kk.symm

theorem prune_step (hc : Ctx L g m₀ t) (hL : L.Ok) :
    WP isa prune t fun u => Ctx L g m₀ u ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt u.mem (hq L) 57) =
        Spec.Ed448.prune (Spec.Ed448.bytesAt t.mem (hq L) 114) := by
  unfold prune
  refine WP.seq (VG.Proof.X25519.Arm.WP.cons (s' := t.setReg .r12 (t.sp + BitVec.ofNat 32 HASH))
    (by simp [exec, HASH]) (WP.block_nil ?_))
  have hsp := hc.sp
  have ht := hL.top
  have e12 : (t.setReg .r12 (t.sp + BitVec.ofNat 32 HASH)).gpr .r12 = L.E + BitVec.ofNat 32 HASH := by
    simp [State.setReg, hsp]
  refine WP.mono (pruneOps_ok (q := hq L) (by rw [e12]; exact hash_addr hL)
    (by rw [e12, BitVec.toNat_add_of_lt (by change L.E.toNat + 24 < 2 ^ 32; omega)]
        change L.E.toNat + 24 + 57 ≤ 2 ^ 32; omega)
    (fun j hj => by
      have h := hc.writable_frame (Offset.contains_base (State.addr L.E) (d := HASH + j) (n := 1)
        (k := 248) (by simp only [HASH]; omega) (by simp only [HASH]; omega))
      rw [← Offset.add_add] at h
      exact h))
    fun u ⟨um, usp, urd, uwr, ug⟩ => ⟨?_, ?_⟩
  · refine hc.of_frame urd uwr usp ?_ (ws := [⟨hq L, 57⟩]) ?_ ?_
    · intro r hr _
      rw [ug r (by rintro rfl; simp [preserved] at hr)]
      exact RegUpd.gpr_setReg_of_ne _ _ (by rintro rfl; simp [preserved] at hr)
    · rw [um]
      refine (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _
        ?_).writeW (List.mem_singleton_self _) _ ?_
      · have h := Offset.contains_base (hq L) (d := 0) (n := 1) (k := 57) (by omega) (by omega)
        rw [show hq L + BitVec.ofNat 64 0 = hq L from BitVec.add_zero _] at h
        exact h
      · exact Offset.contains_base _ (by omega) (by omega)
      · exact Offset.contains_base _ (by omega) (by omega)
    · intro r hr
      rw [List.mem_singleton.mp hr]
      exact .inl (Offset.sub_base _ (by simp only [HASH]; omega))
  · rw [um, pruned_value]
    unfold Spec.Ed448.prune
    rw [bytesAt_take57]
    rfl

/-! ## `vg_ed448_scalar_base` -/

theorem base_noFrames : Impl.Ed448.Arm.scalarBase.noFrames = true := by lit_decide

def BaseArgs (L : Lay) (t : State) : Prop :=
  t.gpr .r0 = L.out ∧ t.gpr .r1 = L.E + BitVec.ofNat 32 HASH ∧ t.gpr .r2 = L.scr

theorem base_pre (hL : L.Ok) (ha : BaseArgs L t) :
    scalarBaseLocal.pre (t.callEntry.withRegions [⟨hq L, 57⟩] L.outputs) := by
  obtain ⟨h0, h1, h2⟩ := ha
  have e0 : (t.callEntry.withRegions [⟨hq L, 57⟩] L.outputs).gpr .r0 = L.out := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), h0]
  have e1 : (t.callEntry.withRegions [⟨hq L, 57⟩] L.outputs).gpr .r1 = L.E + BitVec.ofNat 32 HASH := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), h1]
  have e2 : (t.callEntry.withRegions [⟨hq L, 57⟩] L.outputs).gpr .r2 = L.scr := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), h2]
  simp only [scalarBaseLocal]
  rw [e0, e1, e2, State.withRegions_rd, State.withRegions_wr, hash_addr hL]
  have h := hL.top
  refine ⟨rfl, rfl, hL.oc, hL.kc.sub_left (Offset.sub_base _ (by decide : 24 + 57 ≤ 280)), hL.no, ?_, hL.nc⟩
  rw [BitVec.toNat_add_of_lt (by change L.E.toNat + 24 < 2 ^ 32; omega)]
  change L.E.toNat + 24 + 57 ≤ 2 ^ 32
  omega

theorem base_covers (L : Lay) : Covers ([⟨hq L, 57⟩] ++ L.outputs) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    exact ⟨Whole.FR L.E, List.mem_append_right _ List.mem_cons_self, 24, rfl, by change 24 + 57 ≤ 248; decide⟩
  · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), 0, by simp⟩

theorem base_writes (L : Lay) : ∀ r ∈ L.outputs,
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
  fun r hr => .inr ⟨r, hr, 0, (BitVec.add_zero _).symm, by simp⟩

def baseValues : List (Reg × Value) := [(.r0, .caller 0 0), (.r1, .frame HASH), (.r2, .caller 2 0)]

theorem base_step (hl : BaseLadderOk) (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith baseArgs "vg_ed448_scalar_base" Impl.Ed448.Arm.scalarBase) t fun u =>
      Ctx L g m₀ u ∧ Spec.Ed448.bytesAt u.mem (State.addr L.out) 57 =
        Spec.Ed448.scalarBase (Spec.Ed448.bytesAt t.mem (hq L) 57) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha (args := baseValues) (stk := [])
    (by decide) (by simp [baseValues, Whole.valid, HASH]) (by simp [baseValues]) (by simp [baseValues, preserved])
    (by decide) (by simp) (by simp)) fun u ⟨hu, hm, hav, _⟩ => ?_)
  have h0 := hav (.r0, .caller 0 0) (by simp [baseValues])
  have h1 := hav (.r1, .frame HASH) (by simp [baseValues])
  have h2 := hav (.r2, .caller 2 0) (by simp [baseValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  have he : Spec.Ed448.bytesAt u.mem (hq L) 57 = Spec.Ed448.bytesAt t.mem (hq L) 57 := by
    unfold Spec.Ed448.bytesAt
    refine List.map_congr_left fun i hi => hm.bytes (R := ⟨hq L, 57⟩) ?_
      (by change 57 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint_base _ (by decide) (by decide)
  refine Whole.call_ok hu (scalarBase_ok hl) base_noFrames (base_pre hL ⟨h0, h1, h2⟩) (base_covers L)
    (base_writes L) fun v hv _ hp => ⟨hv, ?_⟩
  change Spec.Ed448.bytesAt v.mem (State.addr (u.callEntry.gpr .r0)) 57 =
    Spec.Ed448.scalarBase (Spec.Ed448.bytesAt u.mem (State.addr (u.callEntry.gpr .r1)) 57) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), h0, h1, hash_addr hL, he] at hp
  exact hp

/-! ## The frame, cleared -/

theorem wipe_step (hc : Ctx L g m₀ t) (hL : L.Ok) :
    WP isa (.block wipe) t fun u => Ctx L g m₀ u ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.out) 57 = Spec.Ed448.bytesAt t.mem (State.addr L.out) 57 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (by have := hL.top; omega) (start := 6) (count := 56) (by decide))
    fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  unfold Spec.Ed448.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes (R := L.OUT) ?_
    (by change 57 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 4 * 6 + 4 * 56 ≤ 280))).symm

/-! ## The body -/

theorem body_ok (hl : BaseLadderOk) (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa body t fun u => Ctx L g m₀ u ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.out) 57 =
        Spec.Ed448.publicKey (Spec.Ed448.bytesAt m₀ (State.addr L.seed) 57) := by
  refine WP.seq (WP.mono (hash_ok hc hL ha) fun u ⟨hu, hh⟩ => ?_)
  refine WP.seq (WP.mono (prune_step hu hL) fun u' ⟨hu', hs⟩ => ?_)
  refine WP.seq (WP.mono (base_step hl hu' hL ha) fun u'' ⟨hu'', hp⟩ => ?_)
  refine WP.mono (wipe_step hu'' hL) fun w ⟨hw, hm⟩ => ⟨hw, ?_⟩
  rw [hm, hp, Spec.Ed448.scalarBase, hs, hh]
  rfl

theorem body_noFrames : body.noFrames = true := by
  simp only [body, Impl.Ed448.Arm.PublicKey.hash, zeroState, prune, callWith, Code.noFrames, Bool.and_self]
  rw [absorb_noFrames, pad_noFrames, squeeze_noFrames, base_noFrames]
  rfl

/-! ## The whole function -/

/-- `vg_ed448_public_key(out = r0, seed = r1, scratch = r2)`, with 280 bytes of stack. -/
def pkLocal : Contract isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 57⟩
    let seed : Region := ⟨State.addr (s.gpr .r1), 57⟩
    let scr : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    let stk : Region := ⟨State.addr s.sp - 280, 280⟩
    s.rd = [seed] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint scr ∧ seed.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint scr ∧
      (s.gpr .r0).toNat + 57 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 57 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ s.sp.toNat
  post s t := Spec.Ed448.bytesAt t.mem (State.addr (s.gpr .r0)) 57 =
    Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) 57)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2

def lay (s : State) : Lay := ⟨s.gpr .r0, s.gpr .r1, s.gpr .r2, Whole.base s⟩

theorem lay_ok {s : State} (h : pkLocal.pre s) : (lay s).Ok := by
  obtain ⟨_, _, os, oc, sc, ko, ks, kc, no, ns, nc, hb⟩ := h
  have he := Whole.base_addr hb
  have top := Whole.base_top hb
  have hs := s.sp.isLt
  refine ⟨by change (Whole.base s).toNat + 272 ≤ 2 ^ 32; omega, os, oc, sc, ?_, ?_, ?_, no, ns, nc⟩
  · change (⟨State.addr (Whole.base s), 280⟩ : Region).Disjoint _
    rw [he]; exact ko
  · change (⟨State.addr (Whole.base s), 280⟩ : Region).Disjoint _
    rw [he]; exact ks
  · change (⟨State.addr (Whole.base s), 280⟩ : Region).Disjoint _
    rw [he]; exact kc

theorem entry_below {s : State} (h : pkLocal.pre s) : 280 ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2

theorem entry_writes {s : State} (h : pkLocal.pre s) :
    ∀ r ∈ s.wr, (Whole.stack s).Disjoint r := by
  intro r hr
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (lay_ok h).ko
  · exact (lay_ok h).kc

theorem entry_ctx {s p : State} (h : pkLocal.pre s) (hp : Whole.Saved (Whole.entered s) 3 p) :
    Ctx (lay s) s.gpr p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  simpa only [Whole.bodyRd, h.1, Whole.bodyWr, h.2.1, Ctx, Lay.inputs, Lay.outputs,
    Lay.SEED, Lay.OUT, Lay.SCR, Lay.ARGS, lay, List.cons_append, List.nil_append] using hc

theorem entry_args {s p : State} (hs : 280 ≤ s.sp.toNat) (hp : Whole.Saved (Whole.entered s) 3 p) :
    Arguments (lay s) p.mem := by
  intro j hj
  have hw := Whole.saved_words hs (by decide : 3 ≤ 6)
    (by simp only [Nat.reduceSub, Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt s.sp.isLt) hp hj
  have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases he with rfl | rfl | rfl <;> exact hw

theorem publicKey_ok (hl : BaseLadderOk) {s : State} (h : pkLocal.pre s) :
    WP isa code s fun u => abiPreserved s u ∧ pkLocal.post s u := by
  have hw := Whole.wrap_ok body_noFrames (by decide : 3 ≤ 6) (entry_below h)
    (by simp only [Nat.reduceSub, Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt s.sp.isLt)
    (by intro j hj h4; omega) (entry_writes h)
    (P := fun m m' _ => Spec.Ed448.bytesAt m' (State.addr (s.gpr .r0)) 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt m (State.addr (s.gpr .r1)) 57))
    (fun p hp => WP.mono (body_ok hl (entry_ctx h hp) (lay_ok h) (entry_args (entry_below h) hp))
      fun u ⟨hu, ho⟩ => ⟨by
        simpa only [Whole.bodyRd, h.1, Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.OUT,
          Lay.SCR, Lay.ARGS, lay, h.2.1, List.cons_append, List.nil_append] using hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have hs : Spec.Ed448.bytesAt m (State.addr (s.gpr .r1)) 57 =
      Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) 57 := by
    unfold Spec.Ed448.bytesAt
    refine List.map_congr_left fun i hi => hf.bytes (R := ⟨State.addr (s.gpr .r1), 57⟩) ?_
      (by change 57 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact (lay_ok h).ks.symm
  change Spec.Ed448.bytesAt u.mem (State.addr (s.gpr .r0)) 57 = _
  rw [hp, hs]

end VG.Proof.Ed448.Arm.PublicKey
