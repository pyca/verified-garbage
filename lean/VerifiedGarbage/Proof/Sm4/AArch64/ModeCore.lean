module

public import VerifiedGarbage.Proof.Modes.AArch64.ViaV
public import VerifiedGarbage.Impl.Sm4.AArch64.Ctr
public import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Proof.Sm4.AArch64.PreparedBody
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Sm4.AArch64.PreparedVerified
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Sm4.Contract
public import VerifiedGarbage.Proof.Sm4.Prepared

/-!
# SM4's core for the modes on AArch64

`dirCoreSpec d`: SM4's core for the direction `d`
(`Impl.Sm4.AArch64.dirCore d`) meets what the modes need of a core
(`Proof.Modes.AArch64.CoreSpec`), with the key a schedule, its cipher
`Spec.Sm4.cipher` for encryption and `Spec.Sm4.invCipher` for decryption,
and the key ready when the masks and the table of round keys in `d`'s
order are in the scratch buffer (`ReadyAt`). `modeCoreSpec` is
encryption's, for CTR.

`prepare` and `crypt` call `vg_sm4_prepare_keys` and
`vg_sm4_crypt_prepared` (`WP.call`, with their contracts on AArch64,
`prepAArch64` and `cryptAArch64`) on the core's slots; around each call,
`v27`–`v30` keep `sb`, the return address and the two registers the modes
keep for the core, since neither function writes a vector register.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Sm4.AArch64
open VG.Impl.Aes.AArch64 (sb t0 movR)
open VG.Proof.Modes.AArch64 (ScrIn coreRegion bufRegion bufAddr Layout CoreSpec dup_ok umov_ok extract_ofVDwords
  vSafe keepsV_of_vSafe runBlock_app)
open VG.Proof.Sm4 (scheduleAt_congr bytesAt_eq_blockAt ofFn_toList crypt_eq)
open VG.Spec.Aes (bytesAt)

/-- The schedule at `x0`, outside the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Sm4.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .x0 = p ∧ k = Spec.Sm4.scheduleAt s.mem p ∧ (⟨p, 128⟩ : Region) ∈ s.rd ∧
    p.toNat + 128 ≤ 2 ^ 64 ∧ ∀ r ∈ rs, Region.Disjoint ⟨p, 128⟩ r

/-- The cipher of the direction `d`. -/
def dirCipher : Dir → Spec.Sm4.Schedule → Spec.Cbc.Cipher
  | .encrypt => Spec.Sm4.cipher
  | .decrypt => Spec.Sm4.invCipher

/-- The cipher of `d` on the 16 bytes at `p`: the 32 rounds with the round
keys in `d`'s order. -/
theorem dirCipher_bytes (d : Dir) (k : Spec.Sm4.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (bytesAt m p 16) =
      (outBlock (quads .enc (dirKeys d k) 8 (ofBlock (Spec.Sm4.blockAt m p)))).toList := by
  cases d
  · rw [dirCipher, Spec.Sm4.cipher, bytesAt_eq_blockAt, ofFn_toList, Spec.Sm4.encryptBlock, crypt_eq]; rfl
  · rw [dirCipher, Spec.Sm4.invCipher, bytesAt_eq_blockAt, ofFn_toList, Spec.Sm4.decryptBlock, crypt_eq]; rfl

/-- A word of the core's slots outside the tail buffer is outside the regions
that are disjoint from the core's slots or within the tail buffer. -/
theorem word_disjoint {dir : Dir} {B : Addr} {d : Nat} (hd : d + 8 ≤ 8 * tableEnd)
    (hout : d + 8 ≤ 8 * tailSlot ∨ 8 * tailSlot + 256 ≤ d) {r : Region}
    (hr : Region.Disjoint (coreRegion (dirCore dir) B) r ∨ Region.Sub r (bufRegion (dirCore dir) B)) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 d, 8⟩ r := by
  rcases hr with h | h
  · exact h.sub_left (VG.Offset.sub_base B (show d + 8 ≤ 8 * slots by rw [slots_eq]; rw [tableEnd_eq] at hd; omega_arith))
  · refine Region.Disjoint.sub_right ?_ h
    show Region.Disjoint ⟨B + BitVec.ofNat 64 d, 8⟩ ⟨B + BitVec.ofNat 64 (8 * tailSlot), 256⟩
    exact VG.Offset.disjoint B (by simp only [tailSlot_eq] at hout ⊢; omega_arith)
      (by simp only [tableEnd_eq] at hd; omega_arith) (by simp only [tailSlot_eq]; decide)

theorem readyAt_frame {dir : Dir} {m m' : Mem} {B : Addr} {k : Spec.Sm4.Schedule} {rs : List Region}
    (h : ReadyAt dir m B k) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore dir) B) r ∨ Region.Sub r (bufRegion (dirCore dir) B)) :
    ReadyAt dir m' B k := by
  have hR : ∀ d, d + 8 ≤ 8 * tableEnd → (d + 8 ≤ 8 * tailSlot ∨ 8 * tailSlot + 256 ≤ d) →
      m'.readW (B + BitVec.ofNat 64 d) 64 = m.readW (B + BitVec.ofNat 64 d) 64 := fun d h1 h2 =>
    hf.readW (Region.contains_self _ _) (fun r hr => word_disjoint h1 h2 (hd r hr)) (by decide)
  refine ⟨fun kv hkv => ?_, fun e he => (h.2 e he).congr fun j hj => ?_⟩
  · have := mask_range hkv
    rw [← h.1 kv hkv]
    exact hR (8 * kv.1) (by rw [tableEnd_eq]; omega_arith) (.inl (by rw [tailSlot_eq]; omega_arith))
  · exact hR (8 * tableSlot + 64 * e + 8 * j) (by rw [tableEnd_eq, tableSlot_eq]; omega_arith)
      (.inr (by rw [tailSlot_eq, tableSlot_eq]; omega_arith))

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Sm4.Schedule} (h : KeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.x0], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [hr .x0 List.mem_cons_self, hp], ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hk]
  exact (scheduleAt_congr fun i hi => hf.bytes (R := ⟨p, 128⟩) hdis (by show 128 ≤ 2 ^ 64; omega_arith) hi).symm

/-! ## Around the calls -/

/-- The state after `keepHead`. -/
def kept (s : State) : State :=
  (((s.setV .v28 (ofVDwords (s.gpr .x30) (s.gpr .x30))).setV .v27 (ofVDwords (s.gpr sb) (s.gpr sb))).setV
    .v29 (ofVDwords (s.gpr .x23) (s.gpr .x23))).setV .v30 (ofVDwords (s.gpr .x24) (s.gpr .x24))

theorem kept_mem (s : State) : (kept s).mem = s.mem := by
  simp only [kept, RegUpd.mem_setV]

theorem kept_rd (s : State) : (kept s).rd = s.rd := by
  simp only [kept, RegUpd.rd_setV]

theorem kept_wr (s : State) : (kept s).wr = s.wr := by
  simp only [kept, RegUpd.wr_setV]

theorem keepHead_ok (s : State) : runBlock isa keepHead s = some (kept s) := by
  rw [show keepHead = [.vop (.dup .d2 .v28 .x30)] ++ ([.vop (.dup .d2 .v27 sb)] ++
      ([.vop (.dup .d2 .v29 .x23)] ++ [.vop (.dup .d2 .v30 .x24)])) from rfl,
    runBlock_app, dup_ok, Option.bind_some, runBlock_app, dup_ok, Option.bind_some, runBlock_app, dup_ok,
    Option.bind_some, dup_ok]
  rfl

theorem keepTail_ok (s : State) : ∃ s', runBlock isa keepTail s = some s' ∧
    s'.gpr sb = (s.v .v27).extractLsb' 0 64 ∧ s'.gpr .x30 = (s.v .v28).extractLsb' 0 64 ∧
    s'.gpr .x23 = (s.v .v29).extractLsb' 0 64 ∧ s'.gpr .x24 = (s.v .v30).extractLsb' 0 64 ∧
    (∀ r, r ≠ sb → r ≠ .x30 → r ≠ .x23 → r ≠ .x24 → s'.gpr r = s.gpr r) ∧
    s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write .x sb ((s.v .v27).extractLsb' 0 64)
  let s₂ := s₁.write .x .x30 ((s₁.v .v28).extractLsb' 0 64)
  let s₃ := s₂.write .x .x23 ((s₂.v .v29).extractLsb' 0 64)
  let s₄ := s₃.write .x .x24 ((s₃.v .v30).extractLsb' 0 64)
  refine ⟨s₄, by
    rw [show keepTail = [.umov .x sb .v27 0] ++ ([.umov .x .x30 .v28 0] ++ ([.umov .x .x23 .v29 0] ++
      [.umov .x .x24 .v30 0])) from rfl, runBlock_app, umov_ok, Option.bind_some, runBlock_app, umov_ok,
      Option.bind_some, runBlock_app, umov_ok, Option.bind_some, umov_ok], ?_, ?_, ?_, ?_,
    fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl⟩
  · rw [(Modes.AArch64.write_ok _ .x24 _).2.1 sb (by decide), (Modes.AArch64.write_ok _ .x23 _).2.1 sb (by decide),
      (Modes.AArch64.write_ok _ .x30 _).2.1 sb (by decide), (Modes.AArch64.write_ok _ sb _).1]
  · rw [(Modes.AArch64.write_ok _ .x24 _).2.1 .x30 (by decide), (Modes.AArch64.write_ok _ .x23 _).2.1 .x30 (by decide),
      (Modes.AArch64.write_ok _ .x30 _).1]; rfl
  · rw [(Modes.AArch64.write_ok _ .x24 _).2.1 .x23 (by decide), (Modes.AArch64.write_ok _ .x23 _).1]; rfl
  · rw [(Modes.AArch64.write_ok _ .x24 _).1]; rfl
  · rw [(Modes.AArch64.write_ok _ .x24 _).2.1 r h4, (Modes.AArch64.write_ok _ .x23 _).2.1 r h3,
      (Modes.AArch64.write_ok _ .x30 _).2.1 r h2, (Modes.AArch64.write_ok _ sb _).2.1 r h1]

/-- A block that writes no vector register `v` keeps it. -/
theorem runBlock_keepV {is : List Instr} {s s' : State} {v : VReg} (hv : ∀ i ∈ is, vdstOf i ≠ some v)
    (e : runBlock isa is s = some s') : s'.v v = s.v v := by
  have w : WP isa (.block is) s fun x => x = s' := WP.of_runBlock ⟨s', e, rfl⟩
  obtain ⟨t, u, he, rfl⟩ := w
  exact Exec.vec (c := .block is) hv he

/-- The four registers back, from a state whose `v27`–`v30` are `kept s`'s. -/
theorem keepTail_kept {s s₁ : State} (hv : ∀ v ∈ [VReg.v27, .v28, .v29, .v30], s₁.v v = (kept s).v v) :
    ∃ s', runBlock isa keepTail s₁ = some s' ∧ s'.gpr sb = s.gpr sb ∧ s'.gpr .x30 = s.gpr .x30 ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧ s'.mem = s₁.mem ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr := by
  obtain ⟨s', e', r27, r28, r29, r30, -, m', rd', wr'⟩ := keepTail_ok s₁
  refine ⟨s', e', ?_, ?_, ?_, ?_, m', rd', wr'⟩
  · rw [r27, hv .v27 (by simp)]; exact extract_ofVDwords _
  · rw [r28, hv .v28 (by simp)]; exact extract_ofVDwords _
  · rw [r29, hv .v29 (by simp)]; exact extract_ofVDwords _
  · rw [r30, hv .v30 (by simp)]; exact extract_ofVDwords _

theorem prepareKeys_vsafe : vSafe .v27 prepareKeys = true ∧ vSafe .v28 prepareKeys = true ∧
    vSafe .v29 prepareKeys = true ∧ vSafe .v30 prepareKeys = true := by
  have h : (vSafe .v27 prepareKeys && vSafe .v28 prepareKeys && vSafe .v29 prepareKeys &&
      vSafe .v30 prepareKeys) = true := by lit_decide
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem cryptPrepared_vsafe : vSafe .v27 cryptPrepared = true ∧ vSafe .v28 cryptPrepared = true ∧
    vSafe .v29 cryptPrepared = true ∧ vSafe .v30 cryptPrepared = true := by
  have h : (vSafe .v27 cryptPrepared && vSafe .v28 cryptPrepared && vSafe .v29 cryptPrepared &&
      vSafe .v30 cryptPrepared) = true := by lit_decide
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- A call that keeps `v27`–`v30` keeps them. -/
theorem call_keepsV {name : String} {c : Prog isa}
    (hc : vSafe .v27 c = true ∧ vSafe .v28 c = true ∧ vSafe .v29 c = true ∧ vSafe .v30 c = true)
    {s s' : State} {t : List Leak} (he : Exec isa (.call name c) s t s') :
    ∀ v ∈ [VReg.v27, .v28, .v29, .v30], s'.v v = s.v v := fun v hv => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact keepsV_of_vSafe (c := .call name c) hc.1 _ _ _ he
  · exact keepsV_of_vSafe (c := .call name c) hc.2.1 _ _ _ he
  · exact keepsV_of_vSafe (c := .call name c) hc.2.2.1 _ _ _ he
  · exact keepsV_of_vSafe (c := .call name c) hc.2.2.2 _ _ _ he

theorem toNat_slots : (BitVec.ofNat 64 slots).toNat = slots := by rw [BitVec.toNat_ofNat, slots_eq]

theorem total_eq (d : Dir) : (dirCore d).total = slots + 12 := rfl

/-- The core's slots, as the calls' working space. -/
theorem ws_covers {s : State} {B : Addr} {d : Dir} (hs : ScrIn s B (dirCore d).total) :
    Covers [⟨B, 8 * slots⟩] s.wr := Covers.of_sub fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, hs.wr, 0, by rw [BitVec.add_zero], by show 0 + 8 * slots ≤ 8 * (dirCore d).total; rw [total_eq]; omega_arith⟩

theorem prepare_wp (d : Dir) {s : State} {B : Addr} {rs : List Region} {k : Spec.Sm4.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hR : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => ReadyAt d s'.mem B k ∧ s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, rfl, hin, hfit, hdis⟩ := hk
  subst hp
  have hfB := hs.fit
  rw [total_eq] at hfB
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := Modes.AArch64.movz_ok (kept s) .x1 (v := dirFlagOf d)
    (by cases d <;> decide)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .x2 sb
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := Modes.AArch64.movz_ok s₃ .x3 (v := slots) (by decide)
  have eargs : runBlock isa ([.movz .x .x1 (BitVec.ofNat 16 (dirFlagOf d)) 0] ++ ([movR .x2 sb] ++
      [.movz .x .x3 (BitVec.ofNat 16 slots) 0])) (kept s) = some s₄ := by
    rw [runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  have v₄ : ∀ v ∈ [VReg.v27, .v28, .v29, .v30], s₄.v v = (kept s).v v := fun v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> cases d <;> exact runBlock_keepV (by decide) eargs
  have g₄ : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₄ r h3, o₃ r h2, o₂ r h1]; rfl
  have x0₄ : s₄.gpr .x0 = s.gpr .x0 := g₄ _ (by decide) (by decide) (by decide)
  have x1₄ : s₄.gpr .x1 = BitVec.ofNat 64 (dirFlagOf d) := by rw [o₄ _ (by decide), o₃ _ (by decide), r₂]
  have x2₄ : s₄.gpr .x2 = B := by rw [o₄ _ (by decide), r₃, o₂ _ (by decide)]; exact hB
  have x3₄ : s₄.gpr .x3 = BitVec.ofNat 64 slots := r₄
  have mem₄ : s₄.mem = s.mem := by rw [m₄, m₃, m₂, kept_mem]
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, kept_rd]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, kept_wr]
  show WP isa (prepareCall d) s _
  refine WP.seq (WP.of_runBlock ⟨s₄, by rw [runBlock_app, keepHead_ok, Option.bind_some]; exact eargs, ?_⟩)
  have hsep : Region.Disjoint ⟨s.gpr .x0, 128⟩ ⟨B, 8 * slots⟩ :=
    (hdis _ hR).sub_right (Region.sub_prefix (by rw [total_eq]; omega_arith))
  have w : WP isa (.call "vg_sm4_prepare_keys" prepareKeys) s₄ fun s' =>
      s'.rd = s₄.rd ∧ s'.wr = s₄.wr ∧ Frame [⟨B, 8 * slots⟩] s₄.mem s'.mem ∧
      Proof.Sm4.Prepared.Holds layout s'.mem B (Spec.Sm4.scheduleAt s.mem (s.gpr .x0)) (specDirA d) := by
    refine WP.call (k := prepAArch64) prep_correct (rd := [⟨s.gpr .x0, 128⟩]) (wr := [⟨B, 8 * slots⟩]) ?_
      (Covers.append_left (Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [rd₄']; exact hin))
        (Covers.right (by rw [wr₄']; exact ws_covers hs)))
      (by rw [wr₄']; exact ws_covers hs) (fun s' hrd hwr _ hf _ _ hpost => ⟨hrd, hwr, hf, ?_⟩) (by lit_decide)
    · have g0 : (s₄.callEntry.withRegions [⟨s.gpr .x0, 128⟩] [⟨B, 8 * slots⟩]).gpr .x0 = s.gpr .x0 := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), x0₄]
      have g1 : (s₄.callEntry.withRegions [⟨s.gpr .x0, 128⟩] [⟨B, 8 * slots⟩]).gpr .x1 =
          BitVec.ofNat 64 (dirFlagOf d) := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), x1₄]
      have g2 : (s₄.callEntry.withRegions [⟨s.gpr .x0, 128⟩] [⟨B, 8 * slots⟩]).gpr .x2 = B := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), x2₄]
      have g3 : ((s₄.callEntry.withRegions [⟨s.gpr .x0, 128⟩] [⟨B, 8 * slots⟩]).gpr .x3).toNat = slots := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), x3₄, toNat_slots]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [State.withRegions_rd, g0]
      · rw [State.withRegions_wr, g2, g3, Nat.mul_comm]
      · rw [g0, g2, g3, Nat.mul_comm]; exact hsep
      · rw [g0]; exact hfit
      · rw [g2, g3]; omega_arith
      · rw [g1]; cases d <;> decide
      · rw [g3, size_eq]
    · obtain ⟨hH, -⟩ := hpost
      have hm : (s'.withRegions [⟨s.gpr .x0, 128⟩] [⟨B, 8 * slots⟩]).mem = s'.mem := rfl
      have hm₀ : (s₄.callEntry.withRegions [⟨s.gpr .x0, 128⟩] [⟨B, 8 * slots⟩]).mem = s.mem := by
        rw [State.withRegions_mem, State.callEntry_mem, mem₄]
      have g0 : (s₄.callEntry.withRegions [⟨s.gpr .x0, 128⟩] [⟨B, 8 * slots⟩]).gpr .x0 = s.gpr .x0 := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), x0₄]
      have g1 : Proof.Sm4.directionOf
          ((s₄.callEntry.withRegions [⟨s.gpr .x0, 128⟩] [⟨B, 8 * slots⟩]).gpr .x1).toNat = specDirA d := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), x1₄]
        cases d <;> rfl
      have g2 : (s₄.callEntry.withRegions [⟨s.gpr .x0, 128⟩] [⟨B, 8 * slots⟩]).gpr .x2 = B := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), x2₄]
      change Proof.Sm4.Prepared.Holds layout _ _ _ _ at hH
      rw [hm, hm₀, g0, g1, g2] at hH
      exact hH
  obtain ⟨t₅, s₅, e₅, rd₅, wr₅, f₅, hH⟩ := w
  refine WP.seq ⟨t₅, s₅, e₅, ?_⟩
  obtain ⟨s₆, e₆, b₆, -, x23₆, x24₆, m₆, rd₆, wr₆⟩ := keepTail_kept (s := s) (s₁ := s₅) fun v hv => by
    rw [call_keepsV prepareKeys_vsafe e₅ v hv, v₄ v hv]
  refine WP.of_runBlock ⟨s₆, e₆, ?_, by rw [b₆, hB], x23₆, x24₆, ?_, by rw [rd₆, rd₅, rd₄'], by rw [wr₆, wr₅, wr₄']⟩
  · rw [m₆]
    have := readyAt_of_words (words_of_holds hH)
    rw [ofSpecDir_specDirA] at this
    exact this
  · rw [m₆, ← mem₄]; exact f₅

/-- Block `j` of blocks transformed by ECB. -/
theorem blockAt_of_ecb {K : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction} {m m' : Mem} {D : Addr} {n : Nat}
    (h : Spec.Sm4.blocksAt m' D n = Spec.Sm4.ecb K d (Spec.Sm4.blocksAt m D n)) {j : Nat} (hj : j < n) :
    Spec.Sm4.blockAt m' (D + BitVec.ofNat 64 (16 * j)) =
      Proof.Sm4.blockFn K d (Spec.Sm4.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  have := congrArg (fun l => l[j]?) h
  rw [Proof.Sm4.ecb_eq] at this
  simpa [Spec.Sm4.blocksAt, hj] using this

/-- The table survives what a batch keeps. -/
theorem holds_of_keeps {m m' : Mem} {B : Addr} {k : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction}
    (h : Proof.Sm4.Prepared.Holds layout m B k d) (hk : Proof.Sm4.Prepared.Keeps B slots layout.cryptScratch m m') :
    Proof.Sm4.Prepared.Holds layout m' B k d := fun r hr i hi => by
  have hr' := hr
  rw [layout_table] at hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rw [hk (r.1 + i) (by rw [slots_eq]; rcases hr' with rfl | rfl <;> dsimp only at hi ⊢ <;> omega_arith) (by
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [evenSlot_eq, grpSlot_eq, tableSlot_eq, savedSlot_eq, slots_eq]
    rcases hr' with rfl | rfl <;> dsimp only at hi ⊢ <;> omega_arith)]
  exact h r hr i hi

theorem crypt_wp (d : Dir) {s : State} {B : Addr} {k : Spec.Sm4.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hr : ReadyAt d s.mem B k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      ReadyAt d s'.mem B k ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, bytesAt s'.mem (bufAddr (dirCore d) B j) 16 =
        dirCipher d k (bytesAt s.mem (bufAddr (dirCore d) B j) 16)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfB := hs.fit
  rw [total_eq] at hfB
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok (kept s) .x0 sb
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := Modes.AArch64.movz_ok s₂ .x1 (v := slots) (by decide)
  have eargs : runBlock isa ([movR .x0 sb] ++ [.movz .x .x1 (BitVec.ofNat 16 slots) 0]) (kept s) = some s₃ := by
    rw [runBlock_app, e₂, Option.bind_some, e₃]
  have v₃ : ∀ v ∈ [VReg.v27, .v28, .v29, .v30], s₃.v v = (kept s).v v := fun v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> exact runBlock_keepV (by decide) eargs
  have x0₃ : s₃.gpr .x0 = B := by rw [o₃ _ (by decide), r₂]; exact hB
  have x1₃ : s₃.gpr .x1 = BitVec.ofNat 64 slots := r₃
  have mem₃ : s₃.mem = s.mem := by rw [m₃, m₂, kept_mem]
  have rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂, kept_rd]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂, kept_wr]
  show WP isa cryptCall s _
  refine WP.seq (WP.of_runBlock ⟨s₃, by rw [runBlock_app, keepHead_ok, Option.bind_some]; exact eargs, ?_⟩)
  have hH : Proof.Sm4.Prepared.Holds layout s.mem B k (specDirA d) := by
    refine holds_of_words ?_
    rw [ofSpecDir_specDirA]
    exact words_of_readyAt hr
  have w : WP isa (.call "vg_sm4_crypt_prepared" cryptPrepared) s₃ fun s' =>
      s'.rd = s₃.rd ∧ s'.wr = s₃.wr ∧ Frame [⟨B, 8 * slots⟩] s₃.mem s'.mem ∧
      Spec.Sm4.blocksAt s'.mem (B + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Sm4.ecb k (specDirA d) (Spec.Sm4.blocksAt s.mem (B + BitVec.ofNat 64 layout.buf) layout.blocks) ∧
      Proof.Sm4.Prepared.Keeps B slots layout.cryptScratch s.mem s'.mem := by
    refine WP.call (k := cryptAArch64) crypt_correct (rd := []) (wr := [⟨B, 8 * slots⟩]) ?_
      (Covers.append_left Covers.nil (Covers.right (by rw [wr₃']; exact ws_covers hs)))
      (by rw [wr₃']; exact ws_covers hs) (fun s' hrd hwr _ hf _ _ hpost => ⟨hrd, hwr, hf, ?_⟩) (by lit_decide)
    · have g0 : (s₃.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .x0 = B := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), x0₃]
      have g1 : ((s₃.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .x1).toNat = slots := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), x1₃, toNat_slots]
      have hm₀ : (s₃.callEntry.withRegions [] [⟨B, 8 * slots⟩]).mem = s.mem := by
        rw [State.withRegions_mem, State.callEntry_mem, mem₃]
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩
      · rw [State.withRegions_wr, g0, g1, Nat.mul_comm]
      · rw [g0, g1]; omega_arith
      · rw [g1, size_eq]
      · rw [g0, hm₀]; exact ⟨k, specDirA d, hH⟩
    · obtain ⟨hB', hK⟩ := hpost
      have hm : (s'.withRegions [] [⟨B, 8 * slots⟩]).mem = s'.mem := rfl
      have hm₀ : (s₃.callEntry.withRegions [] [⟨B, 8 * slots⟩]).mem = s.mem := by
        rw [State.withRegions_mem, State.callEntry_mem, mem₃]
      have g0 : (s₃.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .x0 = B := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), x0₃]
      have g1 : ((s₃.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .x1).toNat = slots := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), x1₃, toNat_slots]
      rw [hm, hm₀, g0] at hB'
      rw [hm, hm₀, g0, g1] at hK
      exact ⟨hB' k (specDirA d) hH, hK⟩
  obtain ⟨t₄, s₄, e₄, rd₄, wr₄, f₄, hE, hK⟩ := w
  refine WP.seq ⟨t₄, s₄, e₄, ?_⟩
  obtain ⟨s₅, e₅, b₅, -, x23₅, x24₅, m₅, rd₅, wr₅⟩ := keepTail_kept (s := s) (s₁ := s₄) fun v hv => by
    rw [call_keepsV cryptPrepared_vsafe e₄ v hv, v₃ v hv]
  refine WP.of_runBlock ⟨s₅, e₅, by rw [b₅, hB], x23₅, x24₅, ?_, by rw [m₅, ← mem₃]; exact f₄,
    fun j hj => ?_, by rw [rd₅, rd₄, rd₃'], by rw [wr₅, wr₄, wr₃']⟩
  · rw [m₅]
    have := readyAt_of_words (words_of_holds (holds_of_keeps hH hK))
    rw [ofSpecDir_specDirA] at this
    exact this
  · have hj' : j < 16 := hj
    have ha : bufAddr (dirCore d) B j = B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j) := by
      rw [VG.Offset.add_add]; rfl
    rw [ha, dirCipher_bytes, bytesAt_eq_blockAt, m₅, blockAt_of_ecb hE hj', quads_spec]

/-- The core's blocks are two words. -/
@[simp] theorem dirCore_bw (d : Dir) : (dirCore d).bw = 2 := rfl

/-- SM4's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Dir) : CoreSpec (dirCore d) where
  Key := Spec.Sm4.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready s B k := ReadyAt d s.mem B k
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Sm4.cipher, Spec.Sm4.invCipher]
  layout := ⟨by cases d <;> decide, by cases d <;> decide, by cases d <;> decide, by cases d <;> decide,
    by cases d <;> decide⟩
  keyRegs_ok := by cases d <;> decide
  regs_ok := by cases d <;> decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame h hf hd _ _ := readyAt_frame h hf hd
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

/-- SM4's core for encryption, for CTR. -/
abbrev modeCoreSpec : CoreSpec modeCore := dirCoreSpec .encrypt

end VG.Proof.Sm4.AArch64
