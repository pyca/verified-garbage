module

public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesConstantTime
public import VerifiedGarbage.Proof.Idea.CbcScratch
public import VerifiedGarbage.Proof.Idea.FbScratch
public import VerifiedGarbage.Proof.Modes.PPC64LE.Core
public import VerifiedGarbage.Impl.Idea.PPC64LE.Modes
import VerifiedGarbage.Proof.Idea.ModeBytes
import VerifiedGarbage.Proof.Idea.PPC64LE.Ecb
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Idea.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Idea.PPC64LE.Block
public import VerifiedGarbage.Spec.Idea
public import VerifiedGarbage.Spec.Idea.Cbc
import VerifiedGarbage.Proof.Modes.PPC64LE.Modes
public import VerifiedGarbage.Proof.Modes.PPC64LE.Seq
public import VerifiedGarbage.Proof.Modes.Steps
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Idea.PPC64LE.ModesLit
meta import VerifiedGarbage.Proof.Idea.PPC64LE.ModesLit

/-! ### `Idea.PPC64LE.ModeCore`, which only this module used -/

section

/-!
# IDEA's core for the modes on PPC64LE

`coreSpec`: IDEA's core (`Impl.Idea.PPC64LE.core`) meets what the modes need
of a core (`Proof.Modes.PPC64LE.CoreSpec`), with the key a schedule of
subkeys, read in place through `r3`, its cipher `Spec.Idea.cipher`. The
schedule is readable and apart from the regions the mode writes
(`KeyArgs`), and from the scratch buffer (`Ready`), so nothing the mode or
the core writes changes it. The core runs ECB's block code on its buffer
(`cryptBlock_ok`).
-/

@[expose] public section

namespace VG.Proof.Idea.PPC64LE.Mode

open VG VG.PPC64LE VG.Impl.Idea.PPC64LE
open VG.Impl.Modes.PPC64LE (sb)
open VG.Proof.Modes.PPC64LE (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept)

/-- The schedule. -/
abbrev keyR (s : State) : Region := ⟨s.gpr .r3, 104⟩

/-- The schedule at `r3` is `k`, readable, and apart from the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Idea.Schedule) : Prop :=
  Spec.Idea.scheduleAt s.mem (s.gpr .r3) = k ∧ keyR s ∈ s.rd ++ s.wr ∧ ∀ r ∈ rs, (keyR s).Disjoint r

/-- The key's arguments, apart from the scratch buffer at `B` too. -/
def Ready (s : State) (B : Addr) (ws : List Region) (k : Spec.Idea.Schedule) : Prop :=
  KeyArgs s ws k ∧ (keyR s).Disjoint ⟨B, 8 * 8⟩

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Idea.Schedule} (h : KeyArgs s rs k)
    (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨hk, hin, hd⟩ := h
  refine ⟨?_, by rw [hrd, hwr, keyR, e]; exact hin, by rw [keyR, e]; exact hd⟩
  rw [e, Proof.Idea.scheduleAt_frame hf hd, hk]

theorem ready_frame {s s' : State} {B : Addr} {ws : List Region} {k : Spec.Idea.Schedule}
    {rs : List Region} (h : Ready s B ws k) (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, ∃ r' ∈ ws, Region.Sub r r') :
    Ready s' B ws k := by
  obtain ⟨⟨hk, hin, hd⟩, hB⟩ := h
  have hd' : ∀ r ∈ rs, (keyR s).Disjoint r := fun r hr => by
    obtain ⟨r', hr', hsub⟩ := hs r hr
    exact (hd r' hr').sub_right hsub
  refine ⟨⟨?_, by rw [hrd, hwr, keyR, e]; exact hin, by rw [keyR, e]; exact hd⟩, by rw [keyR, e]; exact hB⟩
  rw [e, Proof.Idea.scheduleAt_frame hf hd', hk]

theorem layout : Layout core := ⟨by decide, .inl rfl, by decide, by decide, by decide⟩

theorem prepare_wp {s : State} {B : Addr} {rs : List Region} {k : Spec.Idea.Schedule}
    (hB : s.gpr sb = B) (_hS : ScrIn s B core.total) (hm : (⟨B, 8 * core.total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa core.prepare s fun s' => Ready s' B rs k ∧ s'.gpr sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion core B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  wp_nil ⟨⟨hk, hk.2.2 _ hm⟩, hB, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩

/-- The kept registers are none the core writes. -/
theorem kept_apart : ∀ r ∈ kept, r ∉ [Reg.r0, .r4, .r6, .r7, .r8, .r9, .r10, .r11, .r12] := by decide

theorem crypt_wp {s : State} {B : Addr} {ws : List Region} {k : Spec.Idea.Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B core.total) (hR : Ready s B ws k) :
    WP isa core.crypt s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Ready s' B ws k ∧ Frame [coreRegion core B] s.mem s'.mem ∧
      (∀ j < core.G, Spec.Aes.bytesAt s'.mem (blkAddr core B j) (4 * core.bw) =
        Spec.Idea.cipher k (Spec.Aes.bytesAt s.mem (blkAddr core B j) (4 * core.bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 8 * 8 ≤ 2 ^ 64 := hS.fit
  have hW : (⟨B, 8 * 8⟩ : Region) ∈ s.wr := hS.wr
  obtain ⟨⟨hk, hin, hd⟩, hkB⟩ := hR
  simp only [core]
  -- The mask.
  refine WP.seq (WP.mono (WP.keep [.r0] (Q := fun t => t.gpr .r0 = 65535 ∧ t.mem = s.mem)
    (by unfold setMask; irun; rfl) (by decide) rfl) fun s₁ ⟨⟨h0₁, m₁⟩, k₁⟩ => ?_)
  -- The buffer's address.
  refine WP.seq (wp_addi (n := sb) (by decide) (by decide) fun s₂ u₂ => wp_nil ?_)
  have a₂ : s₂.gpr .r4 = B := by
    refine u₂.gpr.trans ?_
    show s₁.gpr .r5 + _ = B
    rw [k₁.gpr (show Reg.r5 ∉ [Reg.r0] by decide), show s.gpr .r5 = B from hB]
    simp [bufSlot]
  have K₂ : Keep [.r0, .r4] s s₂ := ⟨fun r hr => by
      rw [u₂.other r fun e => hr (by rw [e]; decide), k₁.gpr fun h => hr (by
        simp only [List.mem_singleton] at h; rw [h]; decide)],
    by rw [u₂.rd, k₁.2.1], by rw [u₂.wr, k₁.2.2]⟩
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, m₁]
  have r3₂ : s₂.gpr .r3 = s.gpr .r3 := K₂.gpr (by decide)
  have hk₂ : KeyOk k s₂ := by
    have h := keyOk_of s₂ (by rw [r3₂, K₂.2.1, K₂.2.2]; exact hin)
      (by rw [u₂.other _ (by decide)]; exact h0₁)
    rwa [m₂, r3₂, hk] at h
  have hread : BlockRead s₂ B := fun i hi => by
    rw [K₂.2.1, K₂.2.2]
    exact ⟨_, List.mem_append_right _ hW, Offset.contains_base _ (show i + 1 ≤ 8 * 8 by omega_using [hi]) (by omega_using [hi])⟩
  have hwrite : BlockWrite s₂ B := fun i hi => by
    rw [K₂.2.2]
    exact ⟨_, hW, Offset.contains_base _ (show i + 1 ≤ 8 * 8 by omega_using [hi]) (by omega_using [hi])⟩
  -- The block.
  refine WP.mono (cryptBlock_ok k s₂ a₂ hread hwrite hk₂) fun t ⟨b, f, e⟩ => ?_
  have Kt : Keep ([.r0, .r4] ++ roundWrites) s t := K₂.trans e
  have r3t : t.gpr .r3 = s.gpr .r3 := Kt.gpr (by decide)
  have ft : Frame [⟨B, 8⟩] s.mem t.mem := by rw [← m₂]; exact f
  have hB0 : blkAddr core B 0 = B := by simp [blkAddr, slotA, core, bufSlot]
  refine ⟨Kt.gpr (by decide) |>.trans hB, fun r hr => Kt.gpr (by
      have := kept_apart r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢; simp only [List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false]; omega),
    ⟨⟨?_, by rw [Kt.2.1, Kt.2.2, keyR, r3t]; exact hin, by rw [keyR, r3t]; exact hd⟩, by rw [keyR, r3t]; exact hkB⟩,
    by simp only [coreRegion, bufSlot]; exact ft, fun j hj => ?_, Kt.2.1, Kt.2.2⟩
  · rw [r3t, Proof.Idea.scheduleAt_frame ft fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hkB.sub_right (Region.sub_prefix (by decide)), hk]
  · obtain rfl : j = 0 := by simpa [core] using hj
    simp only [core] at hB0
    rw [show 4 * 2 = 8 from rfl, hB0, Proof.Idea.bytesAt_eq, b, ← m₂, Proof.Idea.cipher_bytes]

/-- IDEA's core meets what the modes need. -/
def coreSpec : CoreSpec core where
  Key := Spec.Idea.Schedule
  cipher := Spec.Idea.cipher
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len _ _ := by simp [Spec.Idea.cipher, core]
  layout := layout
  keyArgs_congr h e r w _ f := keyArgs_congr h e.r3 r w f
  ready_frame h e r w _ f hs _ := ready_frame h e.r3 r w f hs
  prepare_wp := prepare_wp
  crypt_wp := crypt_wp

end VG.Proof.Idea.PPC64LE.Mode

end

end


/-!
# IDEA's modes on PPC64LE meet their contracts

`cbcEncryptChained_verified`, `ofb_verified`, … : the modes of
`Proof/Modes/PPC64LE/` over IDEA's core (`Mode.coreSpec`), with the
working space as the fifth argument (`modeContract`), meet the contracts
with a scratch buffer of 8 words (`Proof.Idea.cbcEncChainedScratchContract`,
`fbScratchContract`).
-/

@[expose] public section

namespace VG.Proof.Idea.PPC64LE.Modes

open VG VG.PPC64LE VG.Impl.Idea.PPC64LE VG.Impl.Modes
open VG.Proof.Modes.PPC64LE (SeqPre ivR scrRegion S)
open VG.Proof.Idea.PPC64LE.Mode (coreSpec KeyArgs layout)

/-- IDEA under the subkeys at `r3`. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher := Spec.Idea.cipher (Spec.Idea.scheduleAt s.mem (s.gpr .r3))
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m (s.gpr .r4) 8
/-- The data, in blocks. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) := Spec.Idea.cbcBlocksAt m (s.gpr .r5) (s.gpr .r6).toNat

/-- The functions' postconditions. -/
def cbcEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cbcDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)
def ofbPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ofb.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ofb.next (ciph s) (ivAt s.mem s) (s.gpr .r6).toNat
def cfbEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cfbDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

/-- A mode's function on PPC64LE with its working space as the fifth
argument, and the postcondition `post`. -/
def modeContract (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 104⟩
    let iv : Region := ⟨s.gpr .r4, 8⟩
    let data : Region := ⟨s.gpr .r5, 8 * (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, 8 * 8⟩
    s.rd = [key] ∧ s.wr = [iv, data, scratch] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint scratch ∧ iv.Disjoint data ∧
      iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .r4).toNat + 8 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 8 * (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + 8 * 8 ≤ 2 ^ 64
  post := post
  pub := modePub

/-- `modeContract`'s precondition gives the modes'. -/
theorem seqPre_of {post : State → State → Prop} {M : Mode} (hstep : M.step = 8) {s : State}
    (h : (modeContract post).pre s) : SeqPre core M s := by
  obtain ⟨hrd, hwr, -, -, -, dVD, dVS, dDS, fV, fD, fS⟩ := h
  have e8 : 4 * core.bw = 8 := rfl
  have eS : scrRegion core (S s) = ⟨s.gpr .r7, 8 * 8⟩ := rfl
  have eV : ivR s core = ⟨s.gpr .r4, 8⟩ := rfl
  refine ⟨⟨by rw [hwr]; simp [core], fS⟩, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp,
    by rw [e8]; exact fV, by rw [hwr, hstep]; simp, by rw [hstep]; exact fD, by rw [hstep, eS]; exact dDS,
    by rw [eV, eS]; exact dVS, fun _ => by rw [eV, hstep]; exact dVD, ⟨by omega_using [hstep], by rw [e8]; omega_using [hstep]⟩, layout⟩

theorem keyArgs_of {post : State → State → Prop} {M : Mode} (hstep : M.step = 8) {s : State}
    (h : (modeContract post).pre s) :
    KeyArgs s (Proof.Modes.PPC64LE.wrs0 core M s) (Spec.Idea.scheduleAt s.mem (s.gpr .r3)) := by
  obtain ⟨hrd, -, -, dKD, dKS, -, -, -, -, -, -⟩ := h
  refine ⟨rfl, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), fun r hr => ?_⟩
  simp only [Proof.Modes.PPC64LE.wrs0, Proof.Modes.PPC64LE.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .r3) 104).Disjoint ⟨s.gpr .r5, M.step * (s.gpr .r6).toNat⟩
    rw [hstep]; exact dKD
  · exact dKS

/-- The data in blocks, as the modes' steps. -/
theorem cbcBlocksAt_eq (m : Mem) (p : Addr) (n : Nat) :
    Spec.Idea.cbcBlocksAt m p n = Proof.Modes.chunksAt 8 m p n :=
  Proof.Idea.cbcBlocksAt_eq m p n

/-! ## Correctness -/

theorem cbcEncryptChained_correct (s : State) (hs : (modeContract cbcEncPost).pre s) :
    ∃ t s', Exec isa cbcEncryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract cbcEncPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cbcEncChained_wp coreSpec
    (seqPre_of (M := Mode.cbcEncChained 2) rfl hs) (keyArgs_of (M := Mode.cbcEncChained 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem cbcDecryptChained_correct (s : State) (hs : (modeContract cbcDecPost).pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract cbcDecPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cbcDecChained_wp coreSpec
    (seqPre_of (M := Mode.cbcDecChained 2) rfl hs) (keyArgs_of (M := Mode.cbcDecChained 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem ofb_correct (s : State) (hs : (modeContract ofbPost).pre s) :
    ∃ t s', Exec isa ofb s t s' ∧ abiPreserved s s' ∧ (modeContract ofbPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.ofb_wp coreSpec
    (seqPre_of (M := Mode.ofb 2) rfl hs) (keyArgs_of (M := Mode.ofb 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2, h3⟩

theorem cfbEncrypt_correct (s : State) (hs : (modeContract cfbEncPost).pre s) :
    ∃ t s', Exec isa cfbEncrypt s t s' ∧ abiPreserved s s' ∧ (modeContract cfbEncPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cfbEnc_wp coreSpec
    (seqPre_of (M := Mode.cfbEnc 2) rfl hs) (keyArgs_of (M := Mode.cfbEnc 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem cfbDecrypt_correct (s : State) (hs : (modeContract cfbDecPost).pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ (modeContract cfbDecPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cfbDec_wp coreSpec
    (seqPre_of (M := Mode.cfbDec 2) rfl hs) (keyArgs_of (M := Mode.cfbDec 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

/-! ## The contracts -/

/-- A state satisfying the modes' precondition: the schedule at `0x1000`,
the IV at `0x3000`, no data at `0x4000`, and the scratch buffer at `0x5000`. -/
def modeSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r5 => 0x4000 | .r7 => 0x5000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 0⟩, ⟨0x5000, 64⟩]

theorem modePub_iff (s₁ s₂ : State) : modePub s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 := by
  simp [modePub]

theorem cbcEncryptChained_verified :
    Verified target cbcEncryptChained (Proof.Idea.cbcEncChainedScratchContract abi 8) := by
  refine Verified.of_correct cbcEncryptChained_correct (cbcEncryptChained_constantTime _) ?_
  sig_implies [Proof.Idea.cbcEncChainedScratchContract, Proof.Idea.cbcChainedScratchSig,
    Spec.Idea.cbcChainedSig, Proof.Idea.cbcEncChainedPost, abi, argRegs, modeContract, cbcEncPost,
    modePub_iff] [modeSat] using modeSat

theorem cbcDecryptChained_verified :
    Verified target cbcDecryptChained (Proof.Idea.cbcDecChainedScratchContract abi 8) := by
  refine Verified.of_correct cbcDecryptChained_correct (cbcDecryptChained_constantTime _) ?_
  sig_implies [Proof.Idea.cbcDecChainedScratchContract, Proof.Idea.cbcChainedScratchSig,
    Spec.Idea.cbcChainedSig, Proof.Idea.cbcDecChainedPost, abi, argRegs, modeContract, cbcDecPost,
    modePub_iff] [modeSat] using modeSat

theorem ofb_verified :
    Verified target ofb (Proof.Idea.fbScratchContract abi 8 Proof.Idea.ofbPost) := by
  refine Verified.of_correct ofb_correct (ofb_constantTime _) ?_
  sig_implies [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Spec.Idea.ofbSig,
    Proof.Idea.ofbPost, abi, argRegs, modeContract, ofbPost, modePub_iff] [modeSat] using modeSat

theorem cfbEncrypt_verified :
    Verified target cfbEncrypt (Proof.Idea.fbScratchContract abi 8 Proof.Idea.cfbEncPost) := by
  refine Verified.of_correct cfbEncrypt_correct (cfbEncrypt_constantTime _) ?_
  sig_implies [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Spec.Idea.ofbSig,
    Proof.Idea.cfbEncPost, abi, argRegs, modeContract, cfbEncPost, modePub_iff] [modeSat] using modeSat

theorem cfbDecrypt_verified :
    Verified target cfbDecrypt (Proof.Idea.fbScratchContract abi 8 Proof.Idea.cfbDecPost) := by
  refine Verified.of_correct cfbDecrypt_correct (cfbDecrypt_constantTime _) ?_
  sig_implies [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Spec.Idea.ofbSig,
    Proof.Idea.cfbDecPost, abi, argRegs, modeContract, cfbDecPost, modePub_iff] [modeSat] using modeSat

end VG.Proof.Idea.PPC64LE.Modes
