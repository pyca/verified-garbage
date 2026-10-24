module

public import VerifiedGarbage.Proof.Seed.AArch64.Verified
public import VerifiedGarbage.Proof.Seed.ModeBytes
public import VerifiedGarbage.Proof.Modes.AArch64.ViaV
public import VerifiedGarbage.Impl.Seed.AArch64.Modes
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Seed.AArch64.Lit

/-!
# SEED's core for the modes on AArch64

`dirCoreSpec d`: SEED's core for the direction `d`
(`Impl.Seed.AArch64.dirCore d`) meets what the modes need of a core of
16-byte blocks (`Proof.Modes.AArch64.BlockSpec`, with `bw = 2`), with the
key a schedule, its cipher `Spec.Seed.cipher` for encryption and
`Spec.Seed.invCipher` for decryption, and the key ready when its copy in the
core's slots is the schedule. As on x86-64 (`Proof/Seed/X86_64/ModeCore.lean`):
`crypt` is a batch (`batch_ok`) on the buffer's sixteen blocks, around
which `v29` and `v30` keep the data's address and the blocks left, since the
batch writes no vector register (`vSafe`).
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Seed.AArch64
open VG.Impl.Aes.AArch64 (sb movR)
open VG.Proof.Modes (over over_at over_frame)
open VG.Proof.Modes.AArch64 (ScrIn coreRegion blkRegion blkAddr BlockSpec copyN_wp addImm_ok movz_ok
  runBlock_app addr_add vSafe keepsV_of_vSafe dup_ok umov_ok extract_ofVDwords)
open VG.Spec.Seed (Direction)

/-- The schedule's copy and the buffer, with the scratch buffer at `B`. -/
abbrev schedAddr (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * schedSlot)
abbrev bufAt (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * bufSlot)

/-- The schedule at `x0`, outside the regions `rs`. -/
def ModeKeyArgs (s : State) (rs : List Region) (k : Spec.Seed.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .x0 = p ∧ k = Spec.Seed.scheduleAt s.mem p ∧ (⟨p, 128⟩ : Region) ∈ s.rd ∧
    p.toNat + 128 ≤ 2 ^ 64 ∧ ∀ r ∈ rs, Region.Disjoint ⟨p, 128⟩ r

/-- The schedule's copy is `k`. -/
def ReadyAt (m : Mem) (B : Addr) (k : Spec.Seed.Schedule) : Prop :=
  Spec.Seed.scheduleAt m (schedAddr B) = k

/-- The core's blocks are two words. -/
@[simp] theorem dirCore_bw (d : Direction) : (dirCore d).bw = 2 := rfl

theorem dirCipher_bytes (d : Direction) (k : Spec.Seed.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (Spec.Aes.bytesAt m p 16) = (cipher d k (Spec.Seed.blockAt m p)).toList := by
  have h : (Vector.ofFn fun i : Fin 16 => (Spec.Aes.bytesAt m p 16).getD i.val 0) = Spec.Seed.blockAt m p := by
    ext i hi; simp [Spec.Aes.bytesAt, Spec.Seed.blockAt]
  cases d <;> simp only [dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher, cipher, h]

/-- The core's slots, its buffer and the schedule's copy. -/
theorem core_eq (d : Direction) (B : Addr) : coreRegion (dirCore d) B = ⟨B, 1360⟩ := by
  simp only [coreRegion, dirCore, schedSlot, bufSlot, scratchSlots]
theorem blk_eq (d : Direction) (B : Addr) : blkRegion (dirCore d) B = ⟨B + BitVec.ofNat 64 976, 256⟩ := by
  simp only [blkRegion, dirCore, bufSlot, scratchSlots, Impl.Modes.AArch64.Core.G]
theorem total_eq (d : Direction) : (dirCore d).total = 182 := by
  simp only [dirCore, schedSlot, bufSlot, scratchSlots]

theorem sched_sub (B : Addr) : Region.Sub ⟨schedAddr B, 128⟩ ⟨B, 1360⟩ := Offset.sub_base B (by decide)
theorem sched_buf (B : Addr) : Region.Disjoint ⟨schedAddr B, 128⟩ ⟨B + BitVec.ofNat 64 976, 256⟩ :=
  Offset.disjoint B (.inr (by decide)) (by decide) (by decide)

theorem readyAt_frame {d : Direction} {m m' : Mem} {B : Addr} {k : Spec.Seed.Schedule} {rs : List Region}
    (h : ReadyAt m B k) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (blkRegion (dirCore d) B)) :
    ReadyAt m' B k := by
  rw [ReadyAt, scheduleAt_frame hf fun r hr => ?_]
  · exact h
  rcases hd r hr with h' | h'
  · rw [core_eq] at h'; exact h'.sub_left (sched_sub B)
  · rw [blk_eq] at h'; exact (sched_buf B).sub_right h'

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Seed.Schedule} (h : ModeKeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.x0], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : ModeKeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [hr .x0 List.mem_cons_self, hp], ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hk]
  exact (scheduleAt_frame hf hdis).symm

theorem prepare_wp (d : Direction) {s : State} {B : Addr} {rs : List Region} {k : Spec.Seed.Schedule}
    (hB : s.gpr sb = B) (hs : ScrIn s B (dirCore d).total) (hR : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs)
    (hk : ModeKeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => ReadyAt s'.mem B k ∧ s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, rfl, hin, hfit, hdis⟩ := hk
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hsep : Region.Disjoint ⟨p, 128⟩ ⟨B, 1456⟩ := (hdis _ hR).sub_right (Region.sub_prefix (by rw [total_eq]))
  refine WP.mono (copyN_wp (k := 16) (t := .x6) (u := .x6) (P := schedAddr B) (Q := p)
    ⟨by rw [hB], by rw [hp]; simp, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, fun w hw => ⟨_, hs.wr, by
        rw [addr_add, total_eq]; exact Offset.contains_base B (by simp only [schedSlot, bufSlot, scratchSlots]; omega)
          (by simp only [schedSlot, bufSlot, scratchSlots]; omega)⟩,
      fun w hw => ⟨_, List.mem_append_left _ hin, Offset.contains_base p (by omega) (by omega)⟩,
      (hsep.sub_right (Offset.sub_base B (by decide))).symm, by omega⟩) fun s' h => ?_
  refine ⟨scheduleAt_congr_at fun i hi => by rw [h.mem, over_at hi (by omega)],
    by rw [h.regs _ (by decide) (by decide), hB], h.regs _ (by decide) (by decide), h.regs _ (by decide) (by decide),
    ?_, h.rd, h.wr⟩
  rw [h.mem, core_eq]
  exact (over_frame _ _ _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, sched_sub B⟩

/-- The call keeps the vector registers `v28`, `v27`, `v29`, `v30` and `v31`. -/
theorem blockCall_vsafe (d : Direction) : vSafe .v28 (blockCall d) = true ∧ vSafe .v27 (blockCall d) = true ∧
    vSafe .v29 (blockCall d) = true ∧ vSafe .v30 (blockCall d) = true ∧ vSafe .v31 (blockCall d) = true := by
  -- One evaluation per direction, not one per register.
  have h : (vSafe .v28 (blockCall d) && vSafe .v27 (blockCall d) && vSafe .v29 (blockCall d) &&
      vSafe .v30 (blockCall d) && vSafe .v31 (blockCall d)) = true := by
    cases d <;> lit_decide
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- A block that writes no vector register `v` keeps it, from a run given by `runBlock`. -/
theorem runBlock_v {is : List Instr} {s s' : State} {v : VReg} (hv : ∀ i ∈ is, vdstOf i ≠ some v)
    (e : runBlock isa is s = some s') : s'.v v = s.v v := by
  have w : WP isa (.block is) s fun x => x = s' := WP.of_runBlock ⟨s', e, rfl⟩
  obtain ⟨t, u, he, rfl⟩ := w
  exact Exec.vec (c := .block is) hv he

theorem blockCall_eq (d : Direction) : blockCall d =
    .call (match d with | .encrypt => "vg_seed_encrypt_blocks" | .decrypt => "vg_seed_decrypt_blocks")
      (ecb d) := by cases d <;> rfl

theorem ecb_correct (d : Direction) (s : State) (hs : (contract d).pre s) :
    ∃ t s', Exec isa (ecb d) s t s' ∧ abiPreserved s s' ∧ (contract d).post s s' := by
  cases d
  · exact encrypt_correct (Nat.le_refl _) s hs
  · exact decrypt_correct (Nat.le_refl _) s hs

/-- Block `j` of blocks transformed by ECB. -/
theorem blockAt_of_ecb {K : Spec.Seed.Schedule} {d : Direction} {m m' : Mem} {D : Addr} {n : Nat}
    (h : Spec.Seed.blocksAt m' D n = Spec.Seed.ecb K d (Spec.Seed.blocksAt m D n)) {j : Nat} (hj : j < n) :
    Spec.Seed.blockAt m' (D + BitVec.ofNat 64 (16 * j)) = cipher d K (Spec.Seed.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  have := congrArg (fun l => l[j]?) h
  cases d <;> simpa [Spec.Seed.blocksAt, Spec.Seed.ecb, cipher, hj] using this

theorem toNat16 : (BitVec.ofNat 64 16).toNat = 16 := rfl

theorem crypt_wp (d : Direction) {s : State} {B : Addr} {k : Spec.Seed.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hr : ReadyAt s.mem B k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧ ReadyAt s'.mem B k ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore d) B j) (8 * (dirCore d).bw) =
        dirCipher d k (Spec.Aes.bytesAt s.mem (blkAddr (dirCore d) B j) (8 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hw := hs.wr
  rw [total_eq] at hw
  -- The return address, `sb`, the data's address and the blocks left to vector registers.
  let s₁ := (((s.setV .v28 (ofVDwords (s.gpr .x30) (s.gpr .x30))).setV .v27 (ofVDwords (s.gpr sb) (s.gpr sb))).setV
    .v29 (ofVDwords (s.gpr .x23) (s.gpr .x23))).setV .v30 (ofVDwords (s.gpr .x24) (s.gpr .x24))
  have e₁ : runBlock isa [.vop (.dup .d2 .v28 .x30), .vop (.dup .d2 .v27 sb), .vop (.dup .d2 .v29 .x23),
      .vop (.dup .d2 .v30 .x24)] s = some s₁ := by
    rw [show ([.vop (.dup .d2 .v28 .x30), .vop (.dup .d2 .v27 sb), .vop (.dup .d2 .v29 .x23),
      .vop (.dup .d2 .v30 .x24)] : List Instr) = [.vop (.dup .d2 .v28 .x30)] ++ ([.vop (.dup .d2 .v27 sb)] ++
      ([.vop (.dup .d2 .v29 .x23)] ++ [.vop (.dup .d2 .v30 .x24)])) from rfl,
      runBlock_app, dup_ok, Option.bind_some, runBlock_app, dup_ok, Option.bind_some, runBlock_app, dup_ok,
      Option.bind_some, dup_ok]
    rfl
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := addImm_ok s₁ .x0 sb (v := 8 * schedSlot) (by decide)
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₃ .x1 sb (v := 8 * bufSlot) (by decide)
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := movz_ok s₄ .x2 (v := 16) (by decide)
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := addImm_ok s₅ .x3 sb (v := 0) (by decide)
  have e₃₆ : runBlock isa ([.addImm .x .x0 sb (8 * schedSlot)] ++ ([.addImm .x .x1 sb (8 * bufSlot)] ++
      ([.movz .x .x2 (BitVec.ofNat 16 16) 0] ++ [.addImm .x .x3 sb 0]))) s₁ = some s₆ := by
    rw [runBlock_app, e₃, Option.bind_some, runBlock_app, e₄, Option.bind_some, runBlock_app, e₅,
      Option.bind_some, e₆]
  have v₆ : ∀ v ∈ [VReg.v27, .v28, .v29, .v30], s₆.v v = s₁.v v := fun v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> exact runBlock_v (by decide) e₃₆
  have g₆ : ∀ x, x ≠ .x0 → x ≠ .x1 → x ≠ .x2 → x ≠ .x3 → s₆.gpr x = s.gpr x :=
    fun x h2 h3 h4 h5 => by rw [o₆ x h5, o₅ x h4, o₄ x h3, o₃ x h2]; rfl
  have sb₆ : s₆.gpr sb = B := by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), hB]
  have x0₆ : s₆.gpr .x0 = schedAddr B := by
    rw [o₆ _ (by decide), o₅ _ (by decide), o₄ _ (by decide), r₃]; show s.gpr sb + _ = _; rw [hB]
  have x1₆ : s₆.gpr .x1 = bufAt B := by
    rw [o₆ _ (by decide), o₅ _ (by decide), r₄, o₃ _ (by decide)]; show s.gpr sb + _ = _; rw [hB]
  have x2₆ : s₆.gpr .x2 = BitVec.ofNat 64 16 := by rw [o₆ _ (by decide), r₅]
  have x3₆ : s₆.gpr .x3 = B := by
    rw [r₆, o₅ _ (by decide), o₄ _ (by decide), o₃ _ (by decide)]
    show s.gpr sb + _ = _; rw [hB]; exact BitVec.add_zero _
  have mem₆ : s₆.mem = s.mem := by rw [m₆, m₅, m₄, m₃]; rfl
  have rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₄, rd₃]; rfl
  have wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, wr₃]; rfl
  show WP isa (.seq (.block cryptHead) (.seq (blockCall d) (.block cryptTail))) s _
  refine WP.seq (WP.of_runBlock ⟨s₆, by
    rw [show cryptHead = [.vop (.dup .d2 .v28 .x30), .vop (.dup .d2 .v27 sb), .vop (.dup .d2 .v29 .x23),
      .vop (.dup .d2 .v30 .x24)] ++ ([.addImm .x .x0 sb (8 * schedSlot)] ++ ([.addImm .x .x1 sb (8 * bufSlot)] ++
      ([.movz .x .x2 (BitVec.ofNat 16 16) 0] ++ [.addImm .x .x3 sb 0]))) from rfl,
      runBlock_app, e₁, Option.bind_some, e₃₆], ?_⟩)
  -- The call.
  have sub : ∀ off len, off + len ≤ 1456 → ∃ r' ∈ s₆.wr, ∃ o,
      (B + BitVec.ofNat 64 off) = r'.base + BitVec.ofNat 64 o ∧ o + len ≤ r'.len :=
    fun off len h => ⟨_, by rw [wr₆']; exact hw, off, rfl, h⟩
  have sub0 : ∃ r' ∈ s₆.wr, ∃ o, B = r'.base + BitVec.ofNat 64 o ∧ o + 976 ≤ r'.len := by
    obtain ⟨r', h1, o, h2, h3⟩ := sub 0 976 (by decide)
    exact ⟨r', h1, o, by rw [← h2]; exact (BitVec.add_zero B).symm, h3⟩
  have w : WP isa (blockCall d) s₆ fun s' => s'.rd = s₆.rd ∧ s'.wr = s₆.wr ∧
      Frame [⟨bufAt B, 256⟩, ⟨B, 976⟩] s₆.mem s'.mem ∧ (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₆.gpr r) ∧
      Spec.Seed.blocksAt s'.mem (bufAt B) 16 =
        Spec.Seed.ecb (Spec.Seed.scheduleAt s₆.mem (schedAddr B)) d (Spec.Seed.blocksAt s₆.mem (bufAt B) 16) := by
    rw [blockCall_eq]
    refine WP.call (k := contract d) (ecb_correct d)
      (rd := [⟨schedAddr B, 128⟩]) (wr := [⟨bufAt B, 256⟩, ⟨B, 976⟩]) ?_
      (Covers.right (Covers.of_sub fun r hr => ?_)) (Covers.of_sub fun r hr => ?_)
      (fun s' hrd hwr _ hf hsv _ hpost => ?_) (by cases d <;> rfl)
    · simp only [contract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
        State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
        x0₆, x1₆, x2₆, x3₆, toNat16]
      refine ⟨trivial, trivial, sched_buf B,
        Offset.disjoint_base B (by simp only [schedSlot, bufSlot, scratchSlots]; omega)
          (by simp only [schedSlot, bufSlot, scratchSlots]; omega),
        Offset.disjoint_base B (by simp only [bufSlot, scratchSlots]; omega)
          (by simp only [bufSlot, scratchSlots]; omega), ?_⟩
      rw [bufAt, Offset.toNat_add_ofNat]
      simp only [bufSlot, scratchSlots]; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub (8 * schedSlot) 128 (by decide)
      · exact sub (8 * bufSlot) 256 (by decide)
      · exact sub0
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub (8 * bufSlot) 256 (by decide)
      · exact sub0
    · refine ⟨hrd, hwr, hf, hsv, ?_⟩
      change Spec.Seed.blocksAt _ _ _ = _ at hpost
      simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
        State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), x0₆, x1₆, x2₆, toNat16] at hpost
      exact hpost
  obtain ⟨t₇, s₇, e₇, rd₇, wr₇, f₇, -, res₇⟩ := w
  have v₇ : ∀ v ∈ [VReg.v27, .v28, .v29, .v30], s₇.v v = s₆.v v := fun v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact keepsV_of_vSafe (blockCall_vsafe d).2.1 _ _ _ e₇
    · exact keepsV_of_vSafe (blockCall_vsafe d).1 _ _ _ e₇
    · exact keepsV_of_vSafe (blockCall_vsafe d).2.2.1 _ _ _ e₇
    · exact keepsV_of_vSafe (blockCall_vsafe d).2.2.2.1 _ _ _ e₇
  have vv : ∀ v ∈ [VReg.v27, .v28, .v29, .v30], s₇.v v = s₁.v v := fun v hv => by
    rw [v₇ v hv, v₆ v hv]
  refine WP.seq ⟨t₇, s₇, e₇, ?_⟩
  -- The four registers back.
  let s₈ := s₇.write .x sb ((s₇.v .v27).extractLsb' 0 64)
  let s₉ := s₈.write .x .x30 ((s₈.v .v28).extractLsb' 0 64)
  let s₁₀ := s₉.write .x .x23 ((s₉.v .v29).extractLsb' 0 64)
  let s₁₁ := s₁₀.write .x .x24 ((s₁₀.v .v30).extractLsb' 0 64)
  refine WP.of_runBlock ⟨s₁₁, by
    rw [show cryptTail = [.umov .x sb .v27 0] ++ ([.umov .x .x30 .v28 0] ++ ([.umov .x .x23 .v29 0] ++
      [.umov .x .x24 .v30 0])) from rfl, runBlock_app, umov_ok, Option.bind_some, runBlock_app, umov_ok,
      Option.bind_some, runBlock_app, umov_ok, Option.bind_some, umov_ok], ?_⟩
  have m₁₁ : s₁₁.mem = s₇.mem := rfl
  have hv : ∀ v, s₁₁.v v = s₇.v v ∧ s₁₀.v v = s₇.v v ∧ s₉.v v = s₇.v v ∧ s₈.v v = s₇.v v :=
    fun v => ⟨rfl, rfl, rfl, rfl⟩
  have fcore : Frame [⟨B, 1360⟩] s.mem s₇.mem := by
    rw [← mem₆]
    refine f₇.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Offset.sub_base B (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, fun j hj => ?_, ?_, ?_⟩
  · rw [(Modes.AArch64.write_ok _ .x24 _).2.1 sb (by decide), (Modes.AArch64.write_ok _ .x23 _).2.1 sb (by decide),
      (Modes.AArch64.write_ok _ .x30 _).2.1 sb (by decide), (Modes.AArch64.write_ok _ sb _).1,
      vv .v27 (by simp)]
    show (ofVDwords (s.gpr sb) (s.gpr sb)).extractLsb' 0 64 = B
    rw [extract_ofVDwords, hB]
  · rw [(Modes.AArch64.write_ok _ .x24 _).2.1 .x23 (by decide), (Modes.AArch64.write_ok _ .x23 _).1,
      (hv .v29).2.2.1, vv .v29 (by simp)]
    show (ofVDwords (s.gpr .x23) (s.gpr .x23)).extractLsb' 0 64 = _
    rw [extract_ofVDwords]
  · rw [(Modes.AArch64.write_ok _ .x24 _).1, (hv .v30).2.1, vv .v30 (by simp)]
    show (ofVDwords (s.gpr .x24) (s.gpr .x24)).extractLsb' 0 64 = _
    rw [extract_ofVDwords]
  · rw [m₁₁, ReadyAt, scheduleAt_frame f₇ fun r hr => ?_, mem₆]
    · exact hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sched_buf B
    · exact Offset.disjoint_base B (by decide) (by decide)
  · rw [core_eq, m₁₁]; exact fcore
  · have hj16 : j < 16 := by simp only [dirCore, Impl.Modes.AArch64.Core.G] at hj; exact hj
    have ea : blkAddr (dirCore d) B j = bufAt B + BitVec.ofNat 64 (16 * j) := by
      rw [blkAddr, bufAt, Offset.add_add]; simp only [dirCore, bufSlot, scratchSlots]
    rw [dirCore_bw, show 8 * 2 = 16 from rfl, ea, dirCipher_bytes, bytesAt_eq, m₁₁,
      blockAt_of_ecb res₇ hj16, mem₆, hr]
  · show s₇.rd = _; rw [rd₇, rd₆']
  · show s₇.wr = _; rw [wr₇, wr₆']

/-- SEED's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Direction) : BlockSpec (dirCore d) where
  Key := Spec.Seed.Schedule
  cipher := dirCipher d
  KeyArgs := ModeKeyArgs
  Ready s B k := ReadyAt s.mem B k
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher]
  layout := ⟨by simp only [dirCore]; decide, by simp only [dirCore]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore, schedSlot, bufSlot, scratchSlots, Impl.Modes.AArch64.Core.G]; decide,
    by simp only [dirCore, schedSlot, bufSlot, scratchSlots]; decide,
    by simp only [dirCore, schedSlot, bufSlot, scratchSlots]; decide,
    by simp only [dirCore, bufSlot, scratchSlots]; decide⟩
  keyRegs_ok := by simp only [dirCore]; decide
  regs_ok := by simp only [dirCore, Modes.AArch64.regsOk]; decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame h hf hd _ _ := readyAt_frame h hf hd
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

end VG.Proof.Seed.AArch64
