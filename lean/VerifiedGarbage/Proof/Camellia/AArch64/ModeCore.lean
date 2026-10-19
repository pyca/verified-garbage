module

public import VerifiedGarbage.Proof.Modes.AArch64.ViaV
public import VerifiedGarbage.Impl.Camellia.AArch64.Ctr
public import VerifiedGarbage.Spec.Camellia.Cbc
public import VerifiedGarbage.Proof.Camellia.AArch64.PreparedBody
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Camellia.CtrCipher
import VerifiedGarbage.Proof.Camellia.AArch64.PreparedVerified
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Camellia's core for the modes on AArch64

`dirCoreSpec d`: Camellia's core for the direction `d`
(`Impl.Camellia.AArch64.dirCore d`) meets what the modes need of a core
(`Proof.Modes.AArch64.CoreSpec`), with the key the number of rounds and the
schedule's words, its cipher `Spec.Camellia.cipher` under them for
encryption and `Spec.Camellia.invCipher` for decryption, and the key ready
when the masks and the table of subkeys in `d`'s order are in the scratch
buffer (`ReadyAt`) and `x4` holds the number of rounds (which the modes do
not write). `modeCoreSpec` is encryption's, for CTR.

`prepare` and `crypt` call `vg_camellia_prepare_keys` and
`vg_camellia_crypt_prepared` (`WP.call`, with their contracts on AArch64,
`prepAArch64` and `cryptAArch64`) on the core's slots; around each call,
`v26`–`v30` keep `x4`, `sb`, the return address and the two registers the
modes keep for the core, since neither function writes a vector register.
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Camellia.AArch64
open VG.Impl.Aes.AArch64 (sb t0 kp movR)
open VG.Proof.Modes.AArch64 (ScrIn coreRegion bufRegion bufAddr Layout CoreSpec modeRegs dup_ok umov_ok
  extract_ofVDwords vSafe keepsV_of_vSafe runBlock_app)
open VG.Proof.Camellia (schedWords schedWords_getD wordAt_frame bytesAt_eq_blockAt ofFn_toList blockFn)
open VG.Spec.Camellia.Prepared (Holds Keeps)

/-- The number of rounds in `x1` and the schedule at `x0`, outside the
regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Nat × List (BitVec 64)) : Prop :=
  ∃ p : Addr, s.gpr .x0 = p ∧ s.gpr .x1 = BitVec.ofNat 64 k.1 ∧ (k.1 = 18 ∨ k.1 = 24) ∧
    k.2 = schedWords s.mem p k.1 ∧ (⟨p, 272⟩ : Region) ∈ s.rd ∧ p.toNat + 272 ≤ 2 ^ 64 ∧
    ∀ r ∈ rs, Region.Disjoint ⟨p, 272⟩ r

/-- The table of the subkeys of `k`'s rounds and words in the order of `d`,
and the number of rounds in `x4`. -/
def Ready (d : Dir) (s : State) (B : Addr) (k : Nat × List (BitVec 64)) : Prop :=
  (k.1 = 18 ∨ k.1 = 24) ∧ ReadyAt d k.1 s.mem B k.2 ∧ s.gpr .x4 = BitVec.ofNat 64 k.1

theorem mask_range {kv : Nat × BitVec 64} (hkv : kv ∈ layerMasks) : 48 ≤ kv.1 ∧ kv.1 < 53 := by
  simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
    simp [evenSlot, oddSlot, m4Slot, m2Slot, m3Slot]

theorem total_eq (d : Dir) : (dirCore d).total = slots + 12 := rfl

/-- A word of the core's slots outside the tail buffer is outside the regions
that are disjoint from the core's slots or within the tail buffer. -/
theorem word_disjoint {dir : Dir} {B : Addr} {d : Nat} (hd : d + 8 ≤ 8 * tailSlot) {r : Region}
    (hr : Region.Disjoint (coreRegion (dirCore dir) B) r ∨ Region.Sub r (bufRegion (dirCore dir) B)) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 d, 8⟩ r := by
  rcases hr with h | h
  · exact h.sub_left (VG.Offset.sub_base B (show d + 8 ≤ 8 * slots by rw [slots_eq]; rw [tailSlot_eq] at hd; omega))
  · refine Region.Disjoint.sub_right ?_ h
    show Region.Disjoint ⟨B + BitVec.ofNat 64 d, 8⟩ ⟨B + BitVec.ofNat 64 (8 * tailSlot), 128⟩
    exact VG.Offset.disjoint B (by simp only [tailSlot_eq] at hd ⊢; omega)
      (by simp only [tailSlot_eq] at hd; omega) (by simp only [tailSlot_eq]; omega)

theorem ready_frame {dir : Dir} {s s' : State} {B : Addr} {k : Nat × List (BitVec 64)} {rs : List Region}
    (h : Ready dir s B k) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore dir) B) r ∨ Region.Sub r (bufRegion (dirCore dir) B))
    (_ : Modes.AArch64.WrIn rs s s') (hg : ∀ r, r ∉ modeRegs (dirCore dir) → s'.gpr r = s.gpr r) :
    Ready dir s' B k := by
  obtain ⟨hR, ⟨hm, he⟩, hx4⟩ := h
  have hR' : ∀ d, d + 8 ≤ 8 * tailSlot →
      s'.mem.readW (B + BitVec.ofNat 64 d) 64 = s.mem.readW (B + BitVec.ofNat 64 d) 64 := fun d h1 =>
    hf.readW (Region.contains_self _ _) (fun r hr => word_disjoint h1 (hd r hr)) (by decide)
  have hg4 : k.1 / 6 ≤ 4 := by omega
  refine ⟨hR, ⟨fun kv hkv => ?_, fun i hi => (he i hi).congr fun j hj => ?_⟩, ?_⟩
  · have hk := mask_range hkv
    rw [← hm kv hkv]
    exact hR' (8 * kv.1) (by rw [tailSlot_eq]; omega)
  · exact hR' (8 * keySlot + 64 * i + 8 * j) (by rw [keySlot_eq, tailSlot_eq]; omega)
  · rw [hg .x4 (by cases dir <;> decide), hx4]

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Nat × List (BitVec 64)} (h : KeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.x0, .x1], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨p, hp, hx1, hR, hws, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [hr .x0 List.mem_cons_self, hp], by rw [hr .x1 (List.mem_cons_of_mem _ List.mem_cons_self), hx1],
    hR, ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hws]
  simp only [schedWords]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hl : 8 * i + 8 ≤ 272 := by simp only [Spec.Camellia.scheduleLength] at hi; omega
  exact (wordAt_frame hf fun r hr => (hdis r hr).sub_left (VG.Offset.sub_base p hl)).symm

/-- The cipher of the direction `d`. -/
def dirCipher : Dir → Spec.Camellia.Subkeys → Spec.Cbc.Cipher
  | .encrypt => Spec.Camellia.cipher
  | .decrypt => Spec.Camellia.invCipher

/-- The cipher on a block in memory: its block function. -/
theorem dirCipher_bytes (d : Dir) (K : Spec.Camellia.Subkeys) (m : Mem) (p : Addr) :
    dirCipher d K (Spec.Aes.bytesAt m p 16) = (blockFn K (specDir d) (Spec.Camellia.blockAt m p)).toList := by
  cases d
  · rw [dirCipher, Spec.Camellia.cipher, bytesAt_eq_blockAt, ofFn_toList]; rfl
  · rw [dirCipher, Spec.Camellia.invCipher, bytesAt_eq_blockAt, ofFn_toList]; rfl

/-! ## Around the calls -/

/-- The state after `keepHeadWith r`. -/
def kept (r : Reg) (s : State) : State :=
  ((((s.setV .v28 (ofVDwords (s.gpr .x30) (s.gpr .x30))).setV .v27 (ofVDwords (s.gpr sb) (s.gpr sb))).setV
    .v29 (ofVDwords (s.gpr .x23) (s.gpr .x23))).setV .v30 (ofVDwords (s.gpr .x24) (s.gpr .x24))).setV
    .v26 (ofVDwords (s.gpr r) (s.gpr r))

theorem keepHead_ok (r : Reg) (s : State) : runBlock isa (keepHeadWith r) s = some (kept r s) := by
  rw [show keepHeadWith r = [.vop (.dup .d2 .v28 .x30)] ++ ([.vop (.dup .d2 .v27 sb)] ++
      ([.vop (.dup .d2 .v29 .x23)] ++ ([.vop (.dup .d2 .v30 .x24)] ++ [.vop (.dup .d2 .v26 r)]))) from rfl,
    runBlock_app, dup_ok, Option.bind_some, runBlock_app, dup_ok, Option.bind_some, runBlock_app, dup_ok,
    Option.bind_some, runBlock_app, dup_ok, Option.bind_some, dup_ok]
  rfl

/-- The vector registers that keep the five. -/
abbrev keepVs : List VReg := [.v26, .v27, .v28, .v29, .v30]

theorem keepTail_ok (s : State) : ∃ s', runBlock isa keepTail s = some s' ∧
    s'.gpr sb = (s.v .v27).extractLsb' 0 64 ∧ s'.gpr .x30 = (s.v .v28).extractLsb' 0 64 ∧
    s'.gpr .x23 = (s.v .v29).extractLsb' 0 64 ∧ s'.gpr .x24 = (s.v .v30).extractLsb' 0 64 ∧
    s'.gpr .x4 = (s.v .v26).extractLsb' 0 64 ∧
    s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write .x sb ((s.v .v27).extractLsb' 0 64)
  let s₂ := s₁.write .x .x30 ((s₁.v .v28).extractLsb' 0 64)
  let s₃ := s₂.write .x .x23 ((s₂.v .v29).extractLsb' 0 64)
  let s₄ := s₃.write .x .x24 ((s₃.v .v30).extractLsb' 0 64)
  let s₅ := s₄.write .x .x4 ((s₄.v .v26).extractLsb' 0 64)
  refine ⟨s₅, by
    rw [show keepTail = [.umov .x sb .v27 0] ++ ([.umov .x .x30 .v28 0] ++ ([.umov .x .x23 .v29 0] ++
      ([.umov .x .x24 .v30 0] ++ [.umov .x .x4 .v26 0]))) from rfl, runBlock_app, umov_ok, Option.bind_some,
      runBlock_app, umov_ok, Option.bind_some, runBlock_app, umov_ok, Option.bind_some, runBlock_app, umov_ok,
      Option.bind_some, umov_ok], ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · rw [(Modes.AArch64.write_ok _ .x4 _).2.1 sb (by decide), (Modes.AArch64.write_ok _ .x24 _).2.1 sb (by decide),
      (Modes.AArch64.write_ok _ .x23 _).2.1 sb (by decide), (Modes.AArch64.write_ok _ .x30 _).2.1 sb (by decide),
      (Modes.AArch64.write_ok _ sb _).1]
  · rw [(Modes.AArch64.write_ok _ .x4 _).2.1 .x30 (by decide), (Modes.AArch64.write_ok _ .x24 _).2.1 .x30 (by decide),
      (Modes.AArch64.write_ok _ .x23 _).2.1 .x30 (by decide), (Modes.AArch64.write_ok _ .x30 _).1]; rfl
  · rw [(Modes.AArch64.write_ok _ .x4 _).2.1 .x23 (by decide), (Modes.AArch64.write_ok _ .x24 _).2.1 .x23 (by decide),
      (Modes.AArch64.write_ok _ .x23 _).1]; rfl
  · rw [(Modes.AArch64.write_ok _ .x4 _).2.1 .x24 (by decide), (Modes.AArch64.write_ok _ .x24 _).1]; rfl
  · rw [(Modes.AArch64.write_ok _ .x4 _).1]; rfl

/-- A block that writes no vector register `v` keeps it. -/
theorem runBlock_keepV {is : List Instr} {s s' : State} {v : VReg} (hv : ∀ i ∈ is, vdstOf i ≠ some v)
    (e : runBlock isa is s = some s') : s'.v v = s.v v := by
  have w : WP isa (.block is) s fun x => x = s' := WP.of_runBlock ⟨s', e, rfl⟩
  obtain ⟨t, u, he, rfl⟩ := w
  exact Exec.vec (c := .block is) hv he

/-- The five registers back, from a state whose `v26`–`v30` are `kept r s`'s. -/
theorem keepTail_kept {r : Reg} {s s₁ : State} (hv : ∀ v ∈ keepVs, s₁.v v = (kept r s).v v) :
    ∃ s', runBlock isa keepTail s₁ = some s' ∧ s'.gpr sb = s.gpr sb ∧ s'.gpr .x30 = s.gpr .x30 ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧ s'.gpr .x4 = s.gpr r ∧
      s'.mem = s₁.mem ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr := by
  obtain ⟨s', e', r27, r28, r29, r30, r26, m', rd', wr'⟩ := keepTail_ok s₁
  refine ⟨s', e', ?_, ?_, ?_, ?_, ?_, m', rd', wr'⟩
  · rw [r27, hv .v27 (by simp)]; exact extract_ofVDwords _
  · rw [r28, hv .v28 (by simp)]; exact extract_ofVDwords _
  · rw [r29, hv .v29 (by simp)]; exact extract_ofVDwords _
  · rw [r30, hv .v30 (by simp)]; exact extract_ofVDwords _
  · rw [r26, hv .v26 (by simp)]; exact extract_ofVDwords _

/-- Code that writes none of `v26`–`v30`. -/
def keepsVs (c : Prog isa) : Bool :=
  vSafe .v26 c && vSafe .v27 c && vSafe .v28 c && vSafe .v29 c && vSafe .v30 c

theorem prepareKeys_vsafe : keepsVs prepareKeys = true := by
  unfold keepsVs; lit_decide

theorem cryptPrepared_vsafe : keepsVs cryptPrepared = true := by
  unfold keepsVs; lit_decide

/-- A call of code that keeps `v26`–`v30` keeps them. -/
theorem call_keepsV {name : String} {c : Prog isa} (hc : keepsVs c = true)
    {s s' : State} {t : List Leak} (he : Exec isa (.call name c) s t s') :
    ∀ v ∈ keepVs, s'.v v = s.v v := fun v hv => by
  simp only [keepsVs, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h26, h27⟩, h28⟩, h29⟩, h30⟩ := hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact keepsV_of_vSafe (c := .call name c) h26 _ _ _ he
  · exact keepsV_of_vSafe (c := .call name c) h27 _ _ _ he
  · exact keepsV_of_vSafe (c := .call name c) h28 _ _ _ he
  · exact keepsV_of_vSafe (c := .call name c) h29 _ _ _ he
  · exact keepsV_of_vSafe (c := .call name c) h30 _ _ _ he

theorem toNat_slots : (BitVec.ofNat 64 slots).toNat = slots := by rw [BitVec.toNat_ofNat, slots_eq]

/-- The core's slots, as the calls' working space. -/
theorem ws_covers {s : State} {B : Addr} {d : Dir} (hs : ScrIn s B (dirCore d).total) :
    Covers [⟨B, 8 * slots⟩] s.wr := Covers.of_sub fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, hs.wr, 0, by rw [BitVec.add_zero], by show 0 + 8 * slots ≤ 8 * (dirCore d).total; rw [total_eq]; omega⟩

theorem toNat_rounds {R : Nat} (hR : R = 18 ∨ R = 24) : (BitVec.ofNat 64 R).toNat = R := by
  rcases hR with rfl | rfl <;> rfl

theorem prepare_wp (d : Dir) {s : State} {B : Addr} {rs : List Region} {k : Nat × List (BitVec 64)}
    (hB : s.gpr sb = B) (hs : ScrIn s B (dirCore d).total) (hR : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => Ready d s' B k ∧ s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨p, hp, hx1, hRr, hws, hin, hfit, hdis⟩ := hk
  simp only at hx1 hRr hws
  have hfB := hs.fit
  rw [total_eq] at hfB
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := Modes.AArch64.movz_ok (kept .x1 s) .x2 (v := dirFlagOf d)
    (by cases d <;> decide)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .x3 sb
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := Modes.AArch64.movz_ok s₃ .x4 (v := slots) (by decide)
  have eargs : runBlock isa ([.movz .x .x2 (BitVec.ofNat 16 (dirFlagOf d)) 0] ++ ([movR .x3 sb] ++
      [.movz .x .x4 (BitVec.ofNat 16 slots) 0])) (kept .x1 s) = some s₄ := by
    rw [runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  have v₄ : ∀ v ∈ keepVs, s₄.v v = (kept .x1 s).v v := fun v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> cases d <;> exact runBlock_keepV (by decide) eargs
  have x0₄ : s₄.gpr .x0 = p := by
    rw [o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide)]; exact hp
  have x1₄ : s₄.gpr .x1 = BitVec.ofNat 64 R := by
    rw [o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide)]; exact hx1
  have x2₄ : s₄.gpr .x2 = BitVec.ofNat 64 (dirFlagOf d) := by rw [o₄ _ (by decide), o₃ _ (by decide), r₂]
  have x3₄ : s₄.gpr .x3 = B := by rw [o₄ _ (by decide), r₃, o₂ _ (by decide)]; exact hB
  have x4₄ : s₄.gpr .x4 = BitVec.ofNat 64 slots := r₄
  have mem₄ : s₄.mem = s.mem := by rw [m₄, m₃, m₂]; rfl
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂]; rfl
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂]; rfl
  show WP isa (prepareCall d) s _
  refine WP.seq (WP.of_runBlock ⟨s₄, by rw [runBlock_app, keepHead_ok, Option.bind_some]; exact eargs, ?_⟩)
  have hsep : Region.Disjoint ⟨p, 272⟩ ⟨B, 8 * slots⟩ :=
    (hdis _ hR).sub_right (Region.sub_prefix (by rw [total_eq]; omega))
  have w : WP isa (.call (Spec.Camellia.Prepared.prepareApi layout).name prepareKeys) s₄ fun s' =>
      s'.rd = s₄.rd ∧ s'.wr = s₄.wr ∧ Frame [⟨B, 8 * slots⟩] s₄.mem s'.mem ∧
      Holds layout s'.mem B R (schedWords s.mem p R) (specDir d) := by
    refine WP.call (k := prepAArch64) prep_correct (rd := [⟨p, 272⟩]) (wr := [⟨B, 8 * slots⟩]) ?_
      (Covers.append_left (Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [rd₄']; exact hin))
        (Covers.right (by rw [wr₄']; exact ws_covers hs)))
      (by rw [wr₄']; exact ws_covers hs) (fun s' hrd hwr _ hf _ _ hpost => ⟨hrd, hwr, hf, ?_⟩) (by lit_decide)
    · have g0 : (s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).gpr .x0 = p := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), x0₄]
      have g1 : ((s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).gpr .x1).toNat = R := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), x1₄, toNat_rounds hRr]
      have g2 : (s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).gpr .x2 =
          BitVec.ofNat 64 (dirFlagOf d) := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), x2₄]
      have g3 : (s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).gpr .x3 = B := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), x3₄]
      have g4 : ((s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).gpr .x4).toNat = slots := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), x4₄, toNat_slots]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [State.withRegions_rd, g0]
      · rw [State.withRegions_wr, g3, g4, Nat.mul_comm]
      · rw [g0, g3, g4, Nat.mul_comm]; exact hsep
      · rw [g0]; exact hfit
      · rw [g3, g4]; omega
      · rw [g1]; exact hRr
      · rw [g2]; cases d <;> decide
      · rw [g4, size_eq]
    · obtain ⟨hH, -⟩ := hpost
      have hm : (s'.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).mem = s'.mem := rfl
      have hm₀ : (s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).mem = s.mem := by
        rw [State.withRegions_mem, State.callEntry_mem, mem₄]
      have g0 : (s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).gpr .x0 = p := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), x0₄]
      have g1 : ((s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).gpr .x1).toNat = R := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), x1₄, toNat_rounds hRr]
      have g2 : Spec.Camellia.Prepared.directionOf
          ((s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).gpr .x2).toNat = specDir d := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), x2₄]
        cases d <;> rfl
      have g3 : (s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).gpr .x3 = B := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), x3₄]
      change Holds layout _ _ _ _ _ at hH
      rw [hm, hm₀, g0, g1, g2, g3] at hH
      exact hH
  obtain ⟨t₅, s₅, e₅, rd₅, wr₅, f₅, hH⟩ := w
  refine WP.seq ⟨t₅, s₅, e₅, ?_⟩
  obtain ⟨s₆, e₆, b₆, -, x23₆, x24₆, x4₆, m₆, rd₆, wr₆⟩ := keepTail_kept (s := s) (s₁ := s₅) fun v hv => by
    rw [call_keepsV prepareKeys_vsafe e₅ v hv, v₄ v hv]
  refine WP.of_runBlock ⟨s₆, e₆, ⟨hRr, ?_, by rw [x4₆, hx1]⟩, by rw [b₆, hB], x23₆, x24₆, ?_,
    by rw [rd₆, rd₅, rd₄'], by rw [wr₆, wr₅, wr₄']⟩
  · rw [m₆]
    have := readyAt_of_words (words_of_holds hH)
    rw [ofSpecDir_specDir, ← hws] at this
    exact this
  · rw [m₆, ← mem₄]
    exact f₅.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (Nat.le_refl _)⟩

/-- Block `j` of blocks transformed by ECB. -/
theorem blockAt_of_ecb {K : Spec.Camellia.Subkeys} {d : Spec.Camellia.Direction} {m m' : Mem} {D : Addr} {n : Nat}
    (h : Spec.Camellia.blocksAt m' D n = Spec.Camellia.ecb K d (Spec.Camellia.blocksAt m D n)) {j : Nat} (hj : j < n) :
    Spec.Camellia.blockAt m' (D + BitVec.ofNat 64 (16 * j)) =
      blockFn K d (Spec.Camellia.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  have := congrArg (fun l => l[j]?) h
  rw [Proof.Camellia.ecb_eq] at this
  simpa [Spec.Camellia.blocksAt, hj] using this

/-- The table survives what a batch keeps. -/
theorem holds_of_keeps {R : Nat} (hR : R = 18 ∨ R = 24) {m m' : Mem} {B : Addr} {w : List (BitVec 64)}
    {d : Spec.Camellia.Direction} (h : Holds layout m B R w d)
    (hk : Keeps B slots layout.cryptScratch m m') : Holds layout m' B R w d := fun r hr i hi => by
  have hr' := hr
  rw [layout_table] at hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  have hg4 : R / 6 ≤ 4 := by omega
  rw [hk (r.1 + i) (by rw [slots_eq]; rcases hr' with rfl | rfl <;> dsimp only at hi ⊢ <;> omega) (by
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [evenSlot_eq, m3Slot_eq, keySlot_eq, savedSlot_eq, tailSlot_eq]
    rcases hr' with rfl | rfl <;> dsimp only at hi ⊢ <;> omega)]
  exact h r hr i hi

theorem crypt_wp (d : Dir) {s : State} {B : Addr} {k : Nat × List (BitVec 64)} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hr : Ready d s B k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Ready d s' B k ∧ Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, Spec.Aes.bytesAt s'.mem (bufAddr (dirCore d) B j) 16 =
        dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
          (Spec.Aes.bytesAt s.mem (bufAddr (dirCore d) B j) 16)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨hRr, hready, hx4⟩ := hr
  simp only at hRr hready hx4 ⊢
  have hfB := hs.fit
  rw [total_eq] at hfB
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok (kept .x4 s) .x0 .x4
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .x1 sb
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := Modes.AArch64.movz_ok s₃ .x2 (v := slots) (by decide)
  have eargs : runBlock isa ([movR .x0 .x4] ++ ([movR .x1 sb] ++ [.movz .x .x2 (BitVec.ofNat 16 slots) 0]))
      (kept .x4 s) = some s₄ := by
    rw [runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  have v₄ : ∀ v ∈ keepVs, s₄.v v = (kept .x4 s).v v := fun v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> exact runBlock_keepV (by decide) eargs
  have x0₄ : s₄.gpr .x0 = BitVec.ofNat 64 R := by
    rw [o₄ _ (by decide), o₃ _ (by decide), r₂]; exact hx4
  have x1₄ : s₄.gpr .x1 = B := by rw [o₄ _ (by decide), r₃, o₂ _ (by decide)]; exact hB
  have x2₄ : s₄.gpr .x2 = BitVec.ofNat 64 slots := r₄
  have mem₄ : s₄.mem = s.mem := by rw [m₄, m₃, m₂]; rfl
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂]; rfl
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂]; rfl
  show WP isa cryptCall s _
  refine WP.seq (WP.of_runBlock ⟨s₄, by
    rw [show keepHead = keepHeadWith .x4 from rfl, runBlock_app, keepHead_ok, Option.bind_some]; exact eargs, ?_⟩)
  have hH : Holds layout s.mem B R ws (specDir d) := by
    refine holds_of_words ?_
    rw [ofSpecDir_specDir]
    exact words_of_readyAt hready
  have w : WP isa (.call (Spec.Camellia.Prepared.cryptApi layout).name cryptPrepared) s₄ fun s' =>
      s'.rd = s₄.rd ∧ s'.wr = s₄.wr ∧ Frame [⟨B, 8 * slots⟩] s₄.mem s'.mem ∧
      Spec.Camellia.blocksAt s'.mem (B + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Camellia.ecb (Spec.Camellia.subkeysOfWords R ws) (specDir d)
          (Spec.Camellia.blocksAt s.mem (B + BitVec.ofNat 64 layout.buf) layout.blocks) ∧
      Keeps B slots layout.cryptScratch s.mem s'.mem := by
    refine WP.call (k := cryptAArch64) crypt_correct (rd := []) (wr := [⟨B, 8 * slots⟩]) ?_
      (Covers.append_left Covers.nil (Covers.right (by rw [wr₄']; exact ws_covers hs)))
      (by rw [wr₄']; exact ws_covers hs) (fun s' hrd hwr _ hf _ _ hpost => ⟨hrd, hwr, hf, ?_⟩) (by lit_decide)
    · have g0 : ((s₄.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .x0).toNat = R := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), x0₄, toNat_rounds hRr]
      have g1 : (s₄.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .x1 = B := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), x1₄]
      have g2 : ((s₄.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .x2).toNat = slots := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), x2₄, toNat_slots]
      have hm₀ : (s₄.callEntry.withRegions [] [⟨B, 8 * slots⟩]).mem = s.mem := by
        rw [State.withRegions_mem, State.callEntry_mem, mem₄]
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [State.withRegions_wr, g1, g2, Nat.mul_comm]
      · rw [g1, g2]; omega
      · rw [g0]; exact hRr
      · rw [g2, size_eq]
      · rw [g0, g1, hm₀]; exact ⟨ws, specDir d, hH⟩
    · obtain ⟨hB', hK⟩ := hpost
      have hm : (s'.withRegions [] [⟨B, 8 * slots⟩]).mem = s'.mem := rfl
      have hm₀ : (s₄.callEntry.withRegions [] [⟨B, 8 * slots⟩]).mem = s.mem := by
        rw [State.withRegions_mem, State.callEntry_mem, mem₄]
      have g0 : ((s₄.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .x0).toNat = R := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), x0₄, toNat_rounds hRr]
      have g1 : (s₄.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .x1 = B := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), x1₄]
      have g2 : ((s₄.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .x2).toNat = slots := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), x2₄, toNat_slots]
      rw [hm, hm₀, g0, g1] at hB'
      rw [hm, hm₀, g1, g2] at hK
      exact ⟨hB' ws (specDir d) hH, hK⟩
  obtain ⟨t₅, s₅, e₅, rd₅, wr₅, f₅, hE, hK⟩ := w
  refine WP.seq ⟨t₅, s₅, e₅, ?_⟩
  obtain ⟨s₆, e₆, b₆, -, x23₆, x24₆, x4₆, m₆, rd₆, wr₆⟩ := keepTail_kept (s := s) (s₁ := s₅) fun v hv => by
    rw [call_keepsV cryptPrepared_vsafe e₅ v hv, v₄ v hv]
  refine WP.of_runBlock ⟨s₆, e₆, by rw [b₆, hB], x23₆, x24₆, ⟨hRr, ?_, by rw [x4₆, hx4]⟩, ?_,
    fun j hj => ?_, by rw [rd₆, rd₅, rd₄'], by rw [wr₆, wr₅, wr₄']⟩
  · rw [m₆]
    have := readyAt_of_words (words_of_holds (holds_of_keeps hRr hH hK))
    rw [ofSpecDir_specDir] at this
    exact this
  · rw [m₆, ← mem₄]
    exact f₅.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (Nat.le_refl _)⟩
  · have hj' : j < 8 := hj
    have ha : bufAddr (dirCore d) B j = B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j) := by
      rw [VG.Offset.add_add]; rfl
    rw [ha, dirCipher_bytes, bytesAt_eq_blockAt, m₆, blockAt_of_ecb hE hj']

/-- The core's blocks are two words. -/
@[simp] theorem dirCore_bw (d : Dir) : (dirCore d).bw = 2 := rfl

/-- Camellia's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Dir) : CoreSpec (dirCore d) where
  Key := Nat × List (BitVec 64)
  cipher k := dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
  KeyArgs := KeyArgs
  Ready := Ready d
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Camellia.cipher, Spec.Camellia.invCipher]
  layout := ⟨by cases d <;> decide, by cases d <;> decide, by cases d <;> decide, by cases d <;> decide,
    by cases d <;> decide⟩
  keyRegs_ok := by cases d <;> decide
  regs_ok := by cases d <;> decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame := ready_frame
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

/-- Camellia's core for encryption, for CTR. -/
abbrev modeCoreSpec : CoreSpec modeCore := dirCoreSpec .encrypt

end VG.Proof.Camellia.AArch64
