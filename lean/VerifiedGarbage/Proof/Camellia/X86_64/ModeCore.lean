module

public import VerifiedGarbage.Proof.Camellia.X86_64.PreparedVerified
public import VerifiedGarbage.Proof.Modes.X86_64.Core
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Impl.Camellia.X86_64.Ctr
public import VerifiedGarbage.Spec.Camellia.Cbc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Camellia.CtrCipher
import VerifiedGarbage.Proof.Camellia.X86_64.Lit
import VerifiedGarbage.Proof.Camellia.X86_64.PairSum
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Camellia's core for the modes on x86-64

`dirCoreSpec d`: Camellia's core for the direction `d`
(`Impl.Camellia.X86_64.dirCore d`) meets what the modes need of a core
(`Proof.Modes.X86_64.CoreSpec`), with the key the number of rounds and the
schedule's words, its cipher `Spec.Camellia.cipher` (encryption) or
`Spec.Camellia.invCipher` (decryption) under them, and the key ready when
the masks and the table of subkeys in `d`'s order are in the scratch buffer
(`ReadyAt`) and `rdi` holds the number of rounds (which the modes do not
write). `modeCoreSpec` is encryption's, for CTR.

`prepare` is ECB's key setup, inline, and leaves the number of rounds in
`rdi`; `crypt` calls `vg_camellia_crypt_prepared` (`WP.call`, with its
contract on x86-64, `cryptCallX86_64`) on the core's slots, its return address
stored in the 8 bytes below `rsp`, which the core's slots are apart from.
The data's address, the blocks left and the number of rounds cross the call
in `r12`–`r14`, which the function restores; the slots' address stays in
`sb`, where the function moves `ws`.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (sb t0 setMasks st movS movR)
open VG.Proof.Modes.X86_64 (ScrIn coreRegion bufRegion bufAddr Layout CoreSpec modeRegs of_not_modeRegs stkRegion
  stkList coreFrame)
open VG.Proof.Camellia (schedWords schedWords_getD wordAt_frame bytesAt_eq_blockAt ofFn_toList encryptWith_eq
  decryptWith_eq dirPerm_lt specDir)
open VG.Spec.Camellia.Prepared (Holds)

/-- The number of rounds in `rsi` and the schedule at `rdi`, outside the
regions `rs`, and the 8 bytes below `rsp`, where the core's call stores its
return address, apart from `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Nat × List (BitVec 64)) : Prop :=
  ∃ p : Addr, s.gpr .rdi = p ∧ s.gpr .rsi = BitVec.ofNat 64 k.1 ∧ (k.1 = 18 ∨ k.1 = 24) ∧
    k.2 = schedWords s.mem p k.1 ∧ (⟨p, 272⟩ : Region) ∈ s.rd ∧ p.toNat + 272 ≤ 2 ^ 64 ∧
    (∀ r ∈ rs, Region.Disjoint ⟨p, 272⟩ r) ∧
    8 ≤ (s.gpr .rsp).toNat ∧ ∀ r ∈ rs, Region.Disjoint (stkRegion (s.gpr .rsp) 8) r

theorem dirCore_total (d : Dir) : (dirCore d).total = 409 := rfl

theorem stkList_dirCore (d : Dir) (rsp : Addr) : stkList (dirCore d) rsp = [stkRegion rsp 8] := rfl

/-- The masks and the table of subkeys in the order of `d`, the number of
rounds in `rdi`, and the 8 bytes below `rsp` apart from the slots. -/
def Ready (d : Dir) (s : State) (B : Addr) (k : Nat × List (BitVec 64)) : Prop :=
  (k.1 = 18 ∨ k.1 = 24) ∧ ReadyAt d k.1 s.mem B k.2 ∧ s.gpr .rdi = BitVec.ofNat 64 k.1 ∧
    8 ≤ (s.gpr .rsp).toNat ∧ Region.Disjoint (stkRegion (s.gpr .rsp) 8) ⟨B, 8 * 409⟩

/-- A word of the core's slots outside the tail buffer is outside the regions
that are disjoint from the core's slots or within the tail buffer. -/
theorem word_disjoint {dir : Dir} {B : Addr} {d : Nat} (hd : d + 8 ≤ 8 * tailSlot) {r : Region}
    (hr : Region.Disjoint (coreRegion (dirCore dir) B) r ∨ Region.Sub r (bufRegion (dirCore dir) B)) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 d, 8⟩ r := by
  rcases hr with h | h
  · exact h.sub_left (VG.Offset.sub_base B (by simp only [dirCore, tailSlot_eq, slots_eq] at hd ⊢; omega))
  · refine Region.Disjoint.sub_right ?_ h
    exact VG.Offset.disjoint B (by simp only [dirCore, tailSlot_eq] at hd ⊢; omega)
      (by simp only [tailSlot_eq] at hd; omega) (by simp only [dirCore, tailSlot_eq]; omega)

theorem ready_frame {d : Dir} {s s' : State} {B : Addr} {k : Nat × List (BitVec 64)} {rs : List Region}
    (h : Ready d s B k) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (bufRegion (dirCore d) B))
    (_ : Modes.X86_64.WrIn rs s s') (hg : ∀ r, r ∉ modeRegs (dirCore d) → s'.gpr r = s.gpr r) : Ready d s' B k := by
  obtain ⟨hR, ⟨hm, he⟩, hrdi, hst, hsdis⟩ := h
  have hR' : ∀ d, d + 8 ≤ 8 * tailSlot →
      s'.mem.readW (B + BitVec.ofNat 64 d) 64 = s.mem.readW (B + BitVec.ofNat 64 d) 64 := fun d h1 =>
    hf.readW (Region.contains_self _ _) (fun r hr => word_disjoint h1 (hd r hr)) (by decide)
  have hg4 : k.1 / 6 ≤ 4 := by omega
  have hsp : s'.gpr .rsp = s.gpr .rsp := hg .rsp (by simp only [modeRegs, dirCore]; decide)
  refine ⟨hR, ⟨fun kv hkv => ?_, fun i hi => (he i hi).congr fun j hj => ?_⟩, ?_, by rw [hsp]; exact hst,
    by rw [hsp]; exact hsdis⟩
  · have hk := mask_in hkv
    rw [evenSlot_eq, m3Slot_eq] at hk
    rw [← hm kv hkv]
    exact hR' (8 * kv.1) (by rw [tailSlot_eq]; omega)
  · exact hR' (8 * keySlot + 64 * i + 8 * j) (by rw [keySlot_eq, tailSlot_eq]; omega)
  · rw [hg .rdi (by simp only [modeRegs, dirCore]; decide), hrdi]

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Nat × List (BitVec 64)} (h : KeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.rdi, .rsi, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨p, hp, hrsi, hR, hws, hin, hfit, hdis, hst, hsdis⟩ := h
  have hsp : s'.gpr .rsp = s.gpr .rsp := hr .rsp (by simp)
  refine ⟨p, by rw [hr .rdi (by simp), hp], by rw [hr .rsi (by simp), hrsi],
    hR, ?_, by rw [hrd]; exact hin, hfit, hdis, by rw [hsp]; exact hst, by rw [hsp]; exact hsdis⟩
  rw [hws]
  simp only [schedWords]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hl : 8 * i + 8 ≤ 272 := by simp only [Spec.Camellia.scheduleLength] at hi; omega
  exact (wordAt_frame hf fun r hr => (hdis r hr).sub_left (VG.Offset.sub_base p hl)).symm

/-- A block whose head is one instruction, run from where that instruction leads. -/
theorem runBlock_head {i : Instr} {is : List Instr} {s s₁ : State} (h : runBlock isa [i] s = some s₁) :
    runBlock isa (i :: is) s = runBlock isa is s₁ := by
  rw [show i :: is = [i] ++ is from rfl, runBlock_append', h, Option.bind_some]

/-- Running from `s` with a region within its writable ones added to them. -/
theorem WP.widen_wr {c : Prog isa} {s : State} {r : Region} (hr : Covers [r] s.wr) {Q : State → Prop}
    (h : WP isa c (s.withRegions s.rd (r :: s.wr)) fun s' => Q (s'.withRegions s.rd s.wr)) : WP isa c s Q := by
  obtain ⟨t, s', he, hq⟩ := h
  have := Exec.widen he (Covers.append (Covers.refl _) (Covers.cons hr (Covers.refl _))) (Covers.cons hr (Covers.refl _))
  simp only [State.withRegions_rd, State.withRegions_withRegions, State.withRegions_self] at this
  exact ⟨t, _, this, hq⟩

/-- The key setup, with ECB's scratch buffer among the writable regions:
the masks and the table of `rsi`'s rounds, and the rounds in `rdi`. -/
theorem prepare_core (d : Dir) {s : State} {B p : Addr} {R : Nat} (hB : s.gpr sb = B)
    (hw : (⟨B, 8 * slots⟩ : Region) ∈ s.wr) (fitB : B.toNat + 8 * slots ≤ 2 ^ 64) (hp : s.gpr .rdi = p)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 R) (hRr : R = 18 ∨ R = 24) (hin : (⟨p, 272⟩ : Region) ∈ s.rd)
    (hfit : p.toNat + 272 ≤ 2 ^ 64) (hsep : Region.Disjoint ⟨p, 272⟩ ⟨B, 8 * slots⟩) :
    WP isa (dirCore d).prepare s fun s' => ReadyAt d R s'.mem B (schedWords s.mem p R) ∧
      s'.gpr .rdi = BitVec.ofNat 64 R ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .rdx = s.gpr .rdx ∧ s'.gpr .r8 = s.gpr .r8 ∧ Frame [⟨B, 8 * endSlot⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, -, g₁, rd₁, wr₁, f₁⟩ := setMasks_ok layerMasks hB hw
    (fun kv hkv => by
      simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
        simp [evenSlot, oddSlot, m4Slot, m2Slot, m3Slot, keySlot]) (by decide)
  obtain ⟨s₂, e₂, z₂, g₂, m₂, rd₂, wr₂⟩ := cmpImmZ_ok s₁ .rsi 18
  have hz : s₂.zf = some (decide (R = 18)) := by
    rw [z₂, g₁ _ (by decide), hrsi, show (18 : BitVec 32).signExtend 64 = BitVec.ofNat 64 18 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
  have b₂ : s₂.gpr sb = B := by rw [g₂, g₁ _ (by decide), hB]
  have hpre : KeyPre s₂ B p := ⟨b₂, by rw [wr₂, wr₁]; exact hw, fitB,
    List.mem_append_left _ (by rw [rd₂, rd₁]; exact hin), hfit, hsep⟩
  have rdi₂ : s₂.gpr .rdi = p := by rw [g₂, g₁ _ (by decide), hp]
  have mk₂ : MasksOk s₂ := fun kv hkv => by
    show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
    rw [m₂, g₂]; exact v₁ kv hkv
  show WP isa (.seq (.block (setMasks layerMasks ++ ([.alu .cmp .rsi (.imm 18)] : List Instr)))
    (.ite .e (.seq (keys d 3) (.block [.movImm64 .rdi 18])) (.seq (keys d 4) (.block [.movImm64 .rdi 24])))) s _
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append', e₁, Option.bind_some, e₂], ?_⟩)
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  have hg : g = 3 ∨ g = 4 := by omega
  -- After the table, the rounds to `rdi`.
  have hmov : ∀ (v : BitVec 64), v = BitVec.ofNat 64 R → ∀ s₃, KeysPost s₂ B p g (permOf d g) s₃ →
      WP isa (.block [.movImm64 .rdi v]) s₃ fun s' => ∃ s₃, KeysPost s₂ B p g (permOf d g) s₃ ∧
        s'.mem = s₃.mem ∧ (∀ r, r ≠ .rdi → s'.gpr r = s₃.gpr r) ∧ s'.gpr .rdi = BitVec.ofNat 64 R ∧
        s'.rd = s₃.rd ∧ s'.wr = s₃.wr := fun v hv s₃ k₃ => by
    obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movImm_ok s₃ .rdi v
    exact WP.of_runBlock ⟨s₄, e₄, s₃, k₃, m₄, o₄, by rw [r₄, hv], rd₄, wr₄⟩
  refine WP.mono (M := isa) (Q := fun s' => ∃ s₃, KeysPost s₂ B p g (permOf d g) s₃ ∧
        s'.mem = s₃.mem ∧ (∀ r, r ≠ .rdi → s'.gpr r = s₃.gpr r) ∧ s'.gpr .rdi = BitVec.ofNat 64 R ∧
        s'.rd = s₃.rd ∧ s'.wr = s₃.wr) (WP.ite (decide (R = 18)) (by simp [X86_64.eval, hz]) (fun h => ?_) (fun h => ?_))
    fun s₄ ⟨s₃, k₃, m₄, o₄, rdi₄, rd₄, wr₄⟩ => ?_
  · obtain rfl : R = 18 := of_decide_eq_true h
    obtain rfl : g = 3 := by omega
    exact WP.seq (WP.mono (keys_wp d (Or.inl rfl) hpre rdi₂ mk₂) fun s₃ ⟨k₃, _⟩ => hmov _ rfl s₃ k₃)
  · have hR4 : R = 24 := by have := of_decide_eq_false h; omega
    subst hR4
    obtain rfl : g = 4 := by omega
    exact WP.seq (WP.mono (keys_wp d (Or.inr rfl) hpre rdi₂ mk₂) fun s₃ ⟨k₃, _⟩ => hmov _ rfl s₃ k₃)
  have b₃ : s₃.gpr sb = B := k₃.pre.base
  have keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .rdi → r ≠ t0 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [o₄ r h3, k₃.regs r h1 h2 h3, g₂, g₁ r h4]
  refine ⟨⟨by rw [m₄]; exact k₃.masks.at b₃, fun i hi => ?_⟩, rdi₄,
    by rw [keep sb (by decide) (by decide) (by decide) (by decide), hB],
    keep _ (by decide) (by decide) (by decide) (by decide),
    keep _ (by decide) (by decide) (by decide) (by decide), keep _ (by decide) (by decide) (by decide) (by decide), ?_⟩
  · rw [hgR] at hi
    have := k₃.ent i hi
    rw [m₂] at this
    have hp' : permOf d g i < 8 * g + 2 := dirPerm_lt (specDir d) hi
    have hl : permOf d g i < Spec.Camellia.scheduleLength R := by simp only [Spec.Camellia.scheduleLength]; omega
    rw [keyEntry_eq, hgR, schedWords_getD _ _ hl, m₄]
    rw [wordAt_frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hsep.sub_left (VG.Offset.sub_base p (by simp only [Spec.Camellia.scheduleLength] at hl; omega))).sub_right
        (Region.sub_prefix (by rw [keySlot_eq, slots_eq]; omega))] at this
    exact this
  · have kf := k₃.frame
    rw [m₂] at kf
    rw [m₄]
    exact (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [keySlot_eq, endSlot_eq]; omega)⟩).trans kf

theorem prepare_wp (d : Dir) {s : State} {B : Addr} {rs : List Region} {k : Nat × List (BitVec 64)}
    (hB : s.gpr sb = B) (hs : ScrIn s B (dirCore d).total) (hR : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => Ready d s' B k ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .rdx = s.gpr .rdx ∧ s'.gpr .r8 = s.gpr .r8 ∧
      Frame (coreFrame (dirCore d) B (s.gpr .rsp)) s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨p, hp, hrsi, hRr, hws, hin, hfit, hdis, hst, hsdis⟩ := hk
  dsimp only at hrsi hRr hws
  subst hws
  have hfB := hs.fit
  rw [dirCore_total] at hfB
  have hsub : Covers [⟨B, 8 * slots⟩] s.wr := Covers.of_sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, hs.wr, 0, by simp, by show 0 + 8 * slots ≤ 8 * (dirCore d).total; rw [dirCore_total, slots_eq]; omega⟩
  have hsep : Region.Disjoint ⟨p, 272⟩ ⟨B, 8 * slots⟩ :=
    (hdis _ hR).sub_right (Region.sub_prefix (by rw [dirCore_total, slots_eq]; omega))
  refine WP.widen_wr hsub (WP.mono (prepare_core d (s := s.withRegions s.rd (⟨B, 8 * slots⟩ :: s.wr)) hB
    List.mem_cons_self (by rw [slots_eq]; omega) hp hrsi hRr hin hfit hsep)
    fun s' ⟨hr', rdi', b', rsp', rdx', r8', f'⟩ => ?_)
  change ReadyAt d R s'.mem B (schedWords s.mem p R) at hr'
  change s'.gpr .rsp = s.gpr .rsp at rsp'
  change Frame [⟨B, 8 * endSlot⟩] s.mem s'.mem at f'
  change Ready d s' B _ ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧ s'.gpr .rdx = s.gpr .rdx ∧
    s'.gpr .r8 = s.gpr .r8 ∧ Frame (coreFrame (dirCore d) B (s.gpr .rsp)) s.mem s'.mem ∧ s.rd = s.rd ∧ s.wr = s.wr
  refine ⟨⟨hRr, hr', rdi', by rw [rsp']; exact hst, by rw [rsp', ← dirCore_total d]; exact hsdis _ hR⟩, b', rsp',
    rdx', r8', f'.sub fun r hr => ?_, rfl, rfl⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self, Region.sub_prefix (by simp only [dirCore, endSlot_eq, slots_eq]; omega)⟩

/-- The cipher of the direction `d`. -/
def dirCipher : Dir → Spec.Camellia.Subkeys → Spec.Cbc.Cipher
  | .encrypt => Spec.Camellia.cipher
  | .decrypt => Spec.Camellia.invCipher

/-- The cipher of `d` on a block in memory: the block function. -/
theorem dirCipher_bytes (d : Dir) (sk : Spec.Camellia.Subkeys) (m : Mem) (p : Addr) :
    dirCipher d sk (Spec.Aes.bytesAt m p 16) =
      (Proof.Camellia.blockFn sk (specDir d) (Spec.Camellia.blockAt m p)).toList := by
  cases d
  · rw [dirCipher, Spec.Camellia.cipher, bytesAt_eq_blockAt, ofFn_toList]; rfl
  · rw [dirCipher, Spec.Camellia.invCipher, bytesAt_eq_blockAt, ofFn_toList]; rfl

/-- The table, through memory that differs only apart from the working space. -/
theorem holds_frame {m m' : Mem} {B : Addr} {R : Nat} {w : List (BitVec 64)} {d : Spec.Camellia.Direction}
    {rs : List Region} (hR : R = 18 ∨ R = 24) (h : Holds layout m B R w d) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨B, 8 * slots⟩ r) : Holds layout m' B R w d :=
  fun r hr i hi => by
    have hr' := hr
    rw [layout_table] at hr'
    have hi' : r.1 + i < 8 * slots := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      have : R / 6 ≤ 4 := by omega
      rw [slots_eq]; rcases hr' with rfl | rfl <;> dsimp only at hi ⊢ <;> omega
    rw [hf.bytes (R := ⟨B, 8 * slots⟩) hd (by show 8 * slots ≤ 2 ^ 64; rw [slots_eq]; omega) hi']
    exact h _ hr i hi

/-- The table survives what a batch keeps. -/
theorem holds_of_keeps {m m' : Mem} {B : Addr} {R : Nat} {w : List (BitVec 64)} {d : Spec.Camellia.Direction}
    (hR : R = 18 ∨ R = 24) (h : Holds layout m B R w d)
    (hk : Spec.Camellia.Prepared.Keeps B slots layout.cryptScratch m m') : Holds layout m' B R w d :=
  fun r hr i hi => by
    have hr' := hr
    rw [layout_table] at hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    have h4 : R / 6 ≤ 4 := by omega
    have hb : r.1 + i < 8 * slots ∧ ((384 ≤ r.1 + i ∧ r.1 + i < 424) ∨ (768 ≤ r.1 + i ∧ r.1 + i < 2944)) := by
      rw [slots_eq]; rcases hr' with rfl | rfl <;> dsimp only at hi ⊢ <;> omega
    rw [hk (r.1 + i) hb.1 (by
      simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      rw [evenSlot_eq, m3Slot_eq, keySlot_eq, endSlot_eq, savedSlot_eq, tailSlot_eq]
      omega)]
    exact h _ hr i hi

/-- A block, through memory that differs only apart from it. -/
theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 16⟩ r) : Spec.Camellia.blockAt m' p = Spec.Camellia.blockAt m p := by
  simp only [Spec.Camellia.blockAt]
  congr 1
  funext j
  exact hf.bytes (R := ⟨p, 16⟩) hd (by show 16 ≤ 2 ^ 64; omega) j.isLt

/-- Block `j` of blocks transformed by ECB. -/
theorem blockAt_of_ecb {K : Spec.Camellia.Subkeys} {d : Spec.Camellia.Direction} {m m' : Mem} {D : Addr} {n : Nat}
    (h : Spec.Camellia.blocksAt m' D n = Spec.Camellia.ecb K d (Spec.Camellia.blocksAt m D n)) {j : Nat}
    (hj : j < n) : Spec.Camellia.blockAt m' (D + BitVec.ofNat 64 (16 * j)) =
      Proof.Camellia.blockFn K d (Spec.Camellia.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  have := congrArg (fun l => l[j]?) h
  rw [Proof.Camellia.ecb_eq] at this
  simpa [Spec.Camellia.blocksAt, hj] using this

/-- A register `vg_camellia_crypt_prepared` never writes. -/
theorem crypt_keeps {r : Reg} (h : cryptPrepared.allInstrs (fun i => !Taint.clobbers i r) = true) :
    ∀ i ∈ instrs cryptPrepared, Taint.clobbers i r = false := by
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  exact fun i hi => by simpa using h i hi

theorem crypt_nosp : NoSp cryptPrepared := crypt_keeps (by lit_decide)

theorem crypt_depth : Code.depth cryptPrepared = 0 := rfl

theorem crypt_wp (d : Dir) {s : State} {B : Addr} {k : Nat × List (BitVec 64)} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hr : Ready d s B k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .rdx = s.gpr .rdx ∧ s'.gpr .r8 = s.gpr .r8 ∧ Ready d s' B k ∧
      Frame (coreFrame (dirCore d) B (s.gpr .rsp)) s.mem s'.mem ∧
      (∀ j < (dirCore d).G, Spec.Aes.bytesAt s'.mem (bufAddr (dirCore d) B j) 16 =
        dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
          (Spec.Aes.bytesAt s.mem (bufAddr (dirCore d) B j) 16)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨hRr, hready, hrdi, hst, sW⟩ := hr
  dsimp only at hRr hready hrdi ⊢
  have hw := hs.wr
  have hfit := hs.fit
  simp only [dirCore_total] at hw hfit
  have hH : Holds layout s.mem B R ws (specDir d) := by
    refine holds_of_words ?_
    rw [ofSpecDir_specDir]
    exact words_of_readyAt hready
  show WP isa cryptCall s _
  -- The registers to keep, to `r12`–`r15`, and the arguments.
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .r12 .rdx
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ .r13 .r8
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .r14 .rdi
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := movR_ok s₃ .rsi sb
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := movImm_ok s₅ .rdx (BitVec.ofNat 64 slots)
  refine WP.seq (WP.of_runBlock ⟨s₆, by
    rw [runBlock_head e₁, runBlock_head e₂, runBlock_head e₃, runBlock_head e₅, e₆], ?_⟩)
  have m₆' : s₆.mem = s.mem := by rw [m₆, m₅, m₃, m₂, m₁]
  have rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₃, rd₂, rd₁]
  have wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₃, wr₂, wr₁]
  have g₆ : ∀ r, r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .rsi → r ≠ .rdx → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h5 h6 => by rw [o₆ r h6, o₅ r h5, o₃ r h3, o₂ r h2, o₁ r h1]
  have rsp₆ : s₆.gpr .rsp = s.gpr .rsp := g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have rdi₆ : s₆.gpr .rdi = BitVec.ofNat 64 R := by
    rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), hrdi]
  have rsi₆ : s₆.gpr .rsi = B := by rw [o₆ _ (by decide), r₅, o₃ _ (by decide),
    o₂ _ (by decide), o₁ _ (by decide), hB]
  have rdx₆ : s₆.gpr .rdx = BitVec.ofNat 64 slots := r₆
  have r12₆ : s₆.gpr .r12 = s.gpr .rdx := by
    rw [o₆ _ (by decide), o₅ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), r₁]
  have r13₆ : s₆.gpr .r13 = s.gpr .r8 := by
    rw [o₆ _ (by decide), o₅ _ (by decide), o₃ _ (by decide), r₂, o₁ _ (by decide)]
  have r14₆ : s₆.gpr .r14 = BitVec.ofNat 64 R := by
    rw [o₆ _ (by decide), o₅ _ (by decide), r₃, o₂ _ (by decide), o₁ _ (by decide), hrdi]
  have hE := (s.gpr .rsp).isLt
  have stS : Region.Disjoint (stkRegion (s.gpr .rsp) 8) ⟨B, 8 * slots⟩ :=
    sW.sub_right (Region.sub_prefix (by rw [slots_eq]; omega))
  -- The return address the call stores.
  have hret : Frame [stkRegion (s.gpr .rsp) 8] s₆.mem s₆.callEntry.mem := by
    rw [State.callEntry_mem, rsp₆]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega))
  have hHE : Holds layout s₆.callEntry.mem B R ws (specDir d) :=
    holds_frame (m := s₆.mem) hRr (by rw [m₆']; exact hH) hret fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact stS.symm
  let sE := s₆.callEntry.withRegions [] [⟨B, 8 * slots⟩]
  have eRdi : sE.gpr .rdi = BitVec.ofNat 64 R := by
    show s₆.callEntry.gpr .rdi = _; rw [State.callEntry_gpr _ (by decide), rdi₆]
  have eRsi : sE.gpr .rsi = B := by
    show s₆.callEntry.gpr .rsi = B; rw [State.callEntry_gpr _ (by decide), rsi₆]
  have eRdx : sE.gpr .rdx = BitVec.ofNat 64 slots := by
    show s₆.callEntry.gpr .rdx = _; rw [State.callEntry_gpr _ (by decide), rdx₆]
  have eRsp : sE.gpr .rsp = s.gpr .rsp - 8 := by
    show s₆.callEntry.gpr .rsp = _; rw [State.callEntry_rsp, rsp₆]
  have tsl : (BitVec.ofNat 64 slots).toNat = slots := by rw [slots_eq]; rfl
  have tR : (BitVec.ofNat 64 R).toNat = R := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hsub : ∀ r ∈ ([⟨B, 8 * slots⟩] : List Region), ∃ r' ∈ s₆.wr, ∃ off,
      r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, by rw [wr₆']; exact hs.wr, 0, by simp, by
      show 0 + 8 * slots ≤ 8 * (dirCore d).total; rw [dirCore_total, slots_eq]; omega⟩
  refine WP.seq (WP.call (c := cryptPrepared) (k := cryptCallX86_64) cryptCall_correct crypt_nosp
    (by rw [crypt_depth]; decide) (rd := []) (wr := [⟨B, 8 * slots⟩]) ?_ ?_ ?_ ?_)
  · change cryptX86_64.pre sE
    simp only [cryptX86_64]
    rw [eRdi, eRsi, eRdx, eRsp, tsl, tR]
    refine ⟨rfl, by rw [Nat.mul_comm]; rfl, ?_, by rw [slots_eq]; omega, hRr, by rw [size_eq],
      ws, specDir d, hHE⟩
    rw [Nat.mul_comm slots 8]
    exact stS
  · exact Covers.right (Covers.of_sub hsub)
  · exact Covers.of_sub hsub
  rintro s₇ rd₇ wr₇ cs frame - ⟨s₂', mem₂, g₂', post, hsb⟩
  change cryptX86_64.post sE s₂' at post
  simp only [cryptX86_64] at post
  rw [eRdi, eRsi, eRdx, tsl, tR, mem₂] at post
  obtain ⟨hE', hK⟩ := post
  have hEcb := hE' ws (specDir d) hHE
  rw [crypt_depth, rsp₆, m₆'] at frame
  have frame' : Frame [⟨B, 8 * slots⟩, stkRegion (s.gpr .rsp) 8] s.mem s₇.mem := frame
  have hcs : ∀ r ∈ [Reg.r12, .r13, .r14, .rsp], r ∈ calleeSaved := by decide
  have keep₇ : ∀ r ∈ [Reg.r12, .r13, .r14, .rsp], s₇.gpr r = s₆.gpr r := fun r hr => cs r (hcs r hr)
  have sb₇ : s₇.gpr sb = B := by rw [← g₂' _ (by decide)]; exact hsb.trans eRsi
  -- The kept registers back.
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := movR_ok s₇ .rdx .r12
  obtain ⟨s₉, e₉, r₉, o₉, m₉, rd₉, wr₉⟩ := movR_ok s₈ .r8 .r13
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := movR_ok s₉ .rdi .r14
  have m₁₁' : s₁₁.mem = s₇.mem := by rw [m₁₁, m₉, m₈]
  have rsp₁₁ : s₁₁.gpr .rsp = s.gpr .rsp := by
    rw [o₁₁ _ (by decide), o₉ _ (by decide), o₈ _ (by decide), keep₇ .rsp (by simp), rsp₆]
  refine WP.of_runBlock ⟨s₁₁, by rw [runBlock_head e₈, runBlock_head e₉, e₁₁],
    by rw [o₁₁ _ (by decide), o₉ _ (by decide), o₈ _ (by decide), sb₇], rsp₁₁,
    by rw [o₁₁ _ (by decide), o₉ _ (by decide), r₈, keep₇ .r12 (by simp), r12₆],
    by rw [o₁₁ _ (by decide), r₉, o₈ _ (by decide), keep₇ .r13 (by simp), r13₆],
    ⟨hRr, ?_, by rw [r₁₁, o₉ _ (by decide), o₈ _ (by decide), keep₇ .r14 (by simp), r14₆],
      by rw [rsp₁₁]; exact hst, by rw [rsp₁₁]; exact sW⟩, ?_, fun j hj => ?_,
    by rw [rd₁₁, rd₉, rd₈, rd₇, rd₆'], by rw [wr₁₁, wr₉, wr₈, wr₇, wr₆']⟩
  · have := readyAt_of_words (words_of_holds (holds_of_keeps hRr hHE hK))
    rw [ofSpecDir_specDir, ← m₁₁'] at this
    exact this
  · rw [m₁₁']
    refine frame'.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by simp only [dirCore]; omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (by rw [stkList_dirCore]; exact List.mem_singleton_self _), fun _ h => h⟩
  · have hj' : j < 8 := hj
    have ha : bufAddr (dirCore d) B j = B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j) := by
      simp only [bufAddr, dirCore, layout, VG.Offset.add_add]
    have hblk : Spec.Camellia.blockAt sE.mem (B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j)) =
        Spec.Camellia.blockAt s.mem (B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j)) := by
      rw [← m₆']
      refine blockAt_frame hret fun r hr => ?_
      rw [List.mem_singleton] at hr; subst hr
      rw [VG.Offset.add_add]
      exact (stS.sub_right (VG.Offset.sub_base _ (by simp only [layout, tailSlot_eq, slots_eq]; omega))).symm
    rw [ha, dirCipher_bytes, bytesAt_eq_blockAt, m₁₁', blockAt_of_ecb hEcb hj', hblk]

/-- The core's blocks are two words. -/
@[simp] theorem dirCore_bw (d : Dir) : (dirCore d).bw = 2 := rfl

/-- Camellia's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Dir) : CoreSpec (dirCore d) where
  Key := Nat × List (BitVec 64)
  cipher k := dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
  KeyArgs := KeyArgs
  Ready := Ready d
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Camellia.cipher, Spec.Camellia.invCipher]
  layout := ⟨by simp only [dirCore]; decide, by simp only [dirCore]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore]; decide⟩
  keyRegs_ok := by simp only [dirCore]; decide
  regs_ok := by simp only [dirCore, Modes.X86_64.regsOk]; decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame := ready_frame
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

/-- Camellia's core for encryption, for CTR. -/
abbrev modeCoreSpec : CoreSpec modeCore := dirCoreSpec .encrypt

end VG.Proof.Camellia.X86_64
