import VerifiedGarbage.Proof.Ed448.AArch64.PublicKey.Hash
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe
import VerifiedGarbage.Proof.Ed448.AArch64.BaseVerified
import VerifiedGarbage.Proof.Ed448.Prune
import VerifiedGarbage.Proof.Ed448.ScalarWords

/-!
# Ed448 public-key derivation on AArch64: pruning and the base point

The first 57 bytes of the hash, pruned, are stored as the scalar at the
bottom of the frame (`prune_ok`), `[s]B` is encoded into `out` by
`vg_ed448_scalar_base` (`base_step`, given `BaseLadderOk`), and the scalar and
the hash in the frame are cleared (`wipe_step`).
-/

namespace VG.Proof.Ed448.AArch64.PublicKey

open VG VG.AArch64 VG.Impl.Ed448.AArch64.PublicKey
open VG.Impl.Ed25519.AArch64.Whole (setup callWith Value zeroWord)
open VG.Proof.Ed25519.AArch64.Whole (call_ok Within)

/-! ## Pruning -/

/-- Word `k` of the scalar, from word `k` of the hash. -/
def pruneValue (k : Nat) (x : BitVec 64) : BitVec 64 :=
  if k = 0 then x &&& BitVec.ofNat 64 (2 ^ 64 - 4)
  else if k = 6 then x ||| BitVec.ofNat 64 (2 ^ 63)
  else x

structure Step (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  v : t.v = s.v
  regs : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → t.gpr r = s.gpr r

theorem Step.refl (s : State) : Step s s := ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩

theorem Step.trans {s t u : State} (h : Step s t) (h' : Step t u) : Step s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, h'.v.trans h.v,
    fun r h9 h10 h14 h15 => (h'.regs r h9 h10 h14 h15).trans (h.regs r h9 h10 h14 h15)⟩

theorem pruneWord_ok {s : State} {k : Nat} (hk : k < 7)
    (hr : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (hashAt + 8 * k)) 8)
    (hw : InRegions s.wr (s.sp + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block (pruneWord k)) s fun t => Step s t ∧
      t.mem = s.mem.writeW (s.sp + BitVec.ofNat 64 (8 * k))
        (pruneValue k (s.mem.readW (s.sp + BitVec.ofNat 64 (hashAt + 8 * k)) 64)) := by
  have ho : (hashAt + 8 * k) % 8 = 0 ∧ hashAt + 8 * k < 32768 := by simp only [hashAt]; omega
  have hs : 8 * k < 4096 := by omega
  apply WP.of_runBlock
  by_cases h0 : k = 0
  · subst k
    simp only [hashAt, Nat.reduceMul, Nat.reduceAdd, BitVec.add_zero] at hr hw
    simp only [pruneWord, pruneLow, pruneValue, hashAt, ite_true, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.load, Size.bits, Size.bytes,
      State.read, State.store, addr, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, RegUpd.sp_write, RegUpd.v_write, BitVec.setWidth_eq,
      Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
      ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, hr, hw,
      BitVec.shiftLeft_zero, BitVec.add_zero, Mem.readW, Mem.writeW, Option.some.injEq,
      exists_eq_left']
    refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
    · intro r h9 h10 _ h15
      simp only [RegUpd.gpr_write, h9, h10, h15, ite_false]
    · rfl
  · by_cases h6 : k = 6
    · subst k
      simp only [hashAt, Nat.reduceMul, Nat.reduceAdd] at hr hw
      simp only [pruneWord, pruneHigh, pruneValue, hashAt, h0, ite_true, ite_false,
        List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
        exec, State.load, Size.bits, Size.bytes, State.read, State.store, addr,
        RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
        RegUpd.sp_write, RegUpd.v_write, BitVec.setWidth_eq,
        Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
        ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, hr, hw,
        BitVec.add_zero, Mem.readW, Mem.writeW, Option.some.injEq,
        exists_eq_left']
      refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
      · intro r h9 h10 _ h15
        simp only [RegUpd.gpr_write, h9, h10, h15, ite_false]
      · rfl
    · simp only [pruneWord, pruneValue, h0, h6, ite_false, List.cons_append, List.nil_append,
        runBlock_cons, runStep_some, runBlock_nil, exec, State.load, Size.bits, Size.bytes,
        State.read, State.store, addr, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
        RegUpd.wr_write, RegUpd.sp_write, RegUpd.v_write, BitVec.setWidth_eq,
        ho, hs, and_self, ite_true, ite_false, reduceCtorEq, Option.map_some,
        Option.bind_some, hr, hw, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, BitVec.add_zero,
        Mem.readW, Mem.writeW, Option.some.injEq, exists_eq_left']
      refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, True.intro⟩
      intro r h9 _ _ h15
      simp only [RegUpd.gpr_write, h9, h15, ite_false]

structure PruneInv (s : State) (n : Nat) (t : State) : Prop where
  step : Step s t
  frame : Frame [⟨s.sp, 64⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (s.sp + BitVec.ofNat 64 (8 * j)) 64 =
    pruneValue j (s.mem.readW (s.sp + BitVec.ofNat 64 (hashAt + 8 * j)) 64)

theorem prunePrefix_ok {s : State} (hw : (⟨s.sp, 256⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 7, WP isa (.block ((List.range n).flatMap pruneWord)) s (PruneInv s n)
  | 0, _ => WP.block_nil ⟨.refl s, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (prunePrefix_ok hw n (by omega)) fun u hu => ?_
    have ur : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (hashAt + 8 * n)) 8 := by
      rw [hu.step.sp, hu.step.wr]
      exact ⟨_, List.mem_append_right _ hw, Offset.contains_base _ (by simp only [hashAt]; omega) (by
        simp only [hashAt]; omega)⟩
    have uw : InRegions u.wr (u.sp + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [hu.step.sp, hu.step.wr]
      exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩
    refine WP.mono (pruneWord_ok (by omega) ur uw) fun t ⟨kt, mt⟩ => ?_
    rw [hu.step.sp] at mt
    have same : u.mem.readW (s.sp + BitVec.ofNat 64 (hashAt + 8 * n)) 64 =
        s.mem.readW (s.sp + BitVec.ofNat 64 (hashAt + 8 * n)) 64 := by
      apply hu.frame.readW (Region.contains_self _ _) _ (by decide)
      simp only [List.mem_singleton]
      rintro r rfl
      exact Offset.disjoint_base _ (by simp only [hashAt]; omega) (by simp only [hashAt]; omega)
    rw [same] at mt
    refine ⟨hu.step.trans kt, ?_, fun j hj => ?_⟩
    · rw [mt]
      exact hu.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep ?_ (by decide)]
        · exact hu.words j (by omega)
        · exact Offset.sep _ (by omega) (by omega) (by omega)

theorem byte_of_zero (m : Mem) (p : Addr) (h : m.readW p 64 = 0) : m p = 0 := by
  have e := Mem.extractLsb'_read m p (n := 8) (j := 0) (by decide)
  rw [BitVec.add_zero] at e
  rw [← e]
  have h' : m.read p 8 = 0 := by
    have : m.readW p 64 = m.read p 8 := by simp only [Mem.readW]; rfl
    rw [← this, h]
  rw [h']
  rfl

theorem take57 (m : Mem) (p : Addr) :
    (Spec.Sha3.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  simp [Spec.Sha3.bytesAt, Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem pruneValue_toNat0 (x : BitVec 64) : (pruneValue 0 x).toNat = x.toNat &&& (2 ^ 64 - 4) := by
  have c : (2 ^ 64 - 4) % 2 ^ 64 = 2 ^ 64 - 4 := by decide
  simp only [pruneValue, ite_true, BitVec.toNat_and, BitVec.toNat_ofNat, c]

theorem pruneValue_toNat6 (x : BitVec 64) : (pruneValue 6 x).toNat = x.toNat ||| 2 ^ 63 := by
  have c : 2 ^ 63 % 2 ^ 64 = 2 ^ 63 := by decide
  simp only [pruneValue, Nat.reduceEqDiff, ite_true, ite_false, BitVec.toNat_or, BitVec.toNat_ofNat, c]

/-- The hash at `sp + 128`, pruned, as the scalar at `sp`. -/
theorem prune_run {s : State} (hw : (⟨s.sp, 256⟩ : Region) ∈ s.wr) {h : List Byte}
    (hh : Spec.Sha3.bytesAt s.mem (s.sp + BitVec.ofNat 64 hashAt) 114 = h) :
    WP isa (.block prune) s fun t => Step s t ∧ Frame [⟨s.sp, 64⟩] s.mem t.mem ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt t.mem s.sp 57) = Spec.Ed448.prune h := by
  rw [prune, WP.block_append_iff]
  refine WP.mono (prunePrefix_ok hw 7 (by decide)) fun u hu => ?_
  refine WP.mono (VG.Proof.Ed25519.AArch64.Whole.zeroWord_ok hu.step.sp (by rw [hu.step.wr]; exact hw)
    (k := 7) (by decide)) fun t ⟨kt, mt⟩ => ⟨?_, ?_, ?_⟩
  · exact hu.step.trans ⟨kt.rd, kt.wr, kt.sp, kt.vec, fun r _ _ h14 h15 => kt.regs r h14 h15⟩
  · rw [mt]
    exact hu.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · have hw' : ∀ j < 7, t.mem.readW (s.sp + BitVec.ofNat 64 (8 * j)) 64 =
        pruneValue j (s.mem.readW (s.sp + BitVec.ofNat 64 (hashAt + 8 * j)) 64) := fun j hj => by
      rw [mt, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact hu.words j hj
    have hz : t.mem (s.sp + BitVec.ofNat 64 56) = 0 :=
      byte_of_zero _ _ (by rw [mt]; exact Mem.readW_writeW_self64 _ _ _)
    have w0 := hw' 0 (by decide)
    have w1 := hw' 1 (by decide)
    have w2 := hw' 2 (by decide)
    have w3 := hw' 3 (by decide)
    have w4 := hw' 4 (by decide)
    have w5 := hw' 5 (by decide)
    have w6 := hw' 6 (by decide)
    simp only [hashAt, Nat.reduceMul, Nat.reduceAdd] at w0 w1 w2 w3 w4 w5 w6
    rw [Spec.Ed448.prune, ← hh, take57, Proof.Ed448.decode57, Proof.Ed448.decode57]
    simp only [Offset.add_add, hashAt, Nat.reduceAdd]
    rw [w0, w1, w2, w3, w4, w5, w6, hz, pruneValue_toNat0, pruneValue_toNat6]
    simp only [pruneValue, Nat.reduceEqDiff, ite_false]
    exact (Proof.Ed448.prune_nat _ _ _ _ _ _ _ _ (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
      (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)).symm

/-! ## In the frame's body -/

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem prune_step (hc : Ctx L g vec m₀ t) {h : List Byte}
    (hh : Spec.Sha3.bytesAt t.mem (L.E + BitVec.ofNat 64 hashAt) 114 = h) :
    WP isa (.block prune) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt u.mem L.E 57) = Spec.Ed448.prune h := by
  have hwrite : (⟨t.sp, 256⟩ : Region) ∈ t.wr := by rw [hc.sp, hc.wr]; exact List.mem_cons_self
  have hh' : Spec.Sha3.bytesAt t.mem (t.sp + BitVec.ofNat 64 hashAt) 114 = h := by rw [hc.sp]; exact hh
  refine WP.mono (prune_run hwrite hh') fun u ⟨hu, hf, hp⟩ => ⟨?_, ?_⟩
  · refine hc.of_frame hu.rd hu.wr hu.sp ?_ ?_ hf ?_
    · intro r hr _
      apply hu.regs r <;> intro h <;> subst r <;> simp [preserved] at hr
    · intro r _; rw [hu.v]
    · rintro r hr
      rw [List.mem_singleton.mp hr, hc.sp]
      exact .inl (Region.sub_prefix (by decide))
  · rw [hc.sp] at hp
    exact hp

theorem base_noFrames : Impl.Ed448.AArch64.scalarBase.noFrames = true := by lit_decide

def baseValues : List (Reg × Value) := [(.x0, .caller 0 0), (.x1, .frame 0), (.x2, .caller 2 0)]

theorem base_pre (hL : L.Ok) {u : State} (hs : ∀ p ∈ baseValues, u.gpr p.1 = argValue L p.2) :
    Proof.Ed448.AArch64.scalarBaseLocal.pre (u.callEntry.withRegions [⟨L.E, 57⟩] L.outputs) := by
  have h0 := hs (.x0, .caller 0 0) (by simp [baseValues])
  have h1 := hs (.x1, .frame 0) (by simp [baseValues])
  have h2 := hs (.x2, .caller 2 0) (by simp [baseValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  simp only [Proof.Ed448.AArch64.scalarBaseLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h0, h1, h2]
  exact ⟨trivial, rfl, hL.oc, hL.kc.sub_left (Region.sub_prefix (by decide)), hL.nc⟩

theorem base_covers (L : Lay) : Covers ([⟨L.E, 57⟩] ++ L.outputs) (L.inputs ++ L.FR :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    exact ⟨L.FR, List.mem_append_right _ List.mem_cons_self, 0, (BitVec.add_zero _).symm,
      by change 0 + 57 ≤ 256; decide⟩
  · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), 0, (BitVec.add_zero _).symm, by simp⟩

theorem base_writes (L : Lay) : ∀ r ∈ L.outputs, Within r L.FR ∨ ∃ R ∈ L.outputs, Within r R :=
  fun r hr => .inr ⟨r, hr, 0, (BitVec.add_zero _).symm, by simp⟩

theorem base_step (hb : Proof.Ed448.BaseLadderOk) (hc : Ctx L g vec m₀ t) (hL : L.Ok)
    (ha : Arguments L m₀) {n : Nat}
    (hs : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt t.mem L.E 57) = n) :
    WP isa (callWith baseArgs "vg_ed448_scalar_base" Impl.Ed448.AArch64.scalarBase) t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Ed448.bytesAt u.mem L.out 57 =
        Spec.Ed448.encodePoint (Spec.Ed448.pointMul n Spec.Ed448.basePoint) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.x0, .caller 0 0), (.x1, .frame 0), (.x2, .caller 2 0)])
    (by decide) (by simp [VG.Proof.Ed25519.AArch64.Whole.valid]) (by simp) (by simp [preserved]))
    fun u ⟨hu, hm, hav⟩ => ?_)
  have h0 := hav (.x0, .caller 0 0) (by simp)
  have h1 := hav (.x1, .frame 0) (by simp)
  have h2 := hav (.x2, .caller 2 0) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  have hpre := base_pre hL (u := u) (fun p hp => hav p hp)
  refine call_ok hu (Proof.Ed448.AArch64.scalarBase_ok hb) base_noFrames hpre (base_covers L)
    (base_writes L) fun w hw _ hp => ⟨hw, ?_⟩
  change Spec.Ed448.bytesAt w.mem (u.callEntry.gpr .x0) 57 =
    Spec.Ed448.scalarBase (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x1) 57) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), h0, h1, hm] at hp
  rw [hp, Spec.Ed448.scalarBase, hs]

theorem wipe_step (hc : Ctx L g vec m₀ t) (hL : L.Ok) :
    WP isa (.block wipe) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed448.bytesAt u.mem L.out 57 = Spec.Ed448.bytesAt t.mem L.out 57 := by
  refine WP.mono (VG.Proof.Ed25519.AArch64.Whole.Ctx.zeroWords hc (start := 0) (count := 32) (by decide))
    fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  unfold Spec.Ed448.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes (R := L.OUT) ?_
    (by change 57 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 8 * 0 + 8 * 32 ≤ 336))).symm

end VG.Proof.Ed448.AArch64.PublicKey
