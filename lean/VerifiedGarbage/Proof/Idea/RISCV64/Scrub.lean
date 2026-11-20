module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Impl.Idea.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Idea.Contract
public import VerifiedGarbage.Spec.Idea.Cbc
public import VerifiedGarbage.Spec.Idea.Cfb
public import VerifiedGarbage.Spec.Idea.CfbFinal
public import VerifiedGarbage.Spec.Idea.Ofb
public import VerifiedGarbage.Spec.Idea.OfbFinal
public import VerifiedGarbage.Proof.Idea.RISCV64.Key
public import VerifiedGarbage.Proof.Idea.ScrubLocal
import VerifiedGarbage.Proof.Idea.Arith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Idea.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.Idea.RISCV64.Lit
import VerifiedGarbage.Proof.Idea.RISCV64.ModesLit
public import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
public import VerifiedGarbage.Impl.Idea.RISCV64.FbFinal
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
meta import VerifiedGarbage.Impl.Idea.RISCV64.FbFinal
meta import VerifiedGarbage.Spec.Idea.CfbFinal
meta import VerifiedGarbage.Spec.Idea.OfbFinal
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Idea.RISCV64.FbFinalLit
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Modes.RISCV64.Modes
public import VerifiedGarbage.Proof.Modes.RISCV64.Seq
public import VerifiedGarbage.Proof.Modes.Steps
import VerifiedGarbage.Proof.Idea.ModeBytes
meta import VerifiedGarbage.Proof.Idea.RISCV64.ModesLit
meta import VerifiedGarbage.Spec.Idea.Cbc
meta import VerifiedGarbage.Spec.Idea.Cfb
meta import VerifiedGarbage.Spec.Idea.Ofb
meta import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Impl.Idea.RISCV64.Modes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.Idea.RISCV64.Modes
public import VerifiedGarbage.Proof.Modes.RISCV64.Core
public import VerifiedGarbage.Proof.Idea.RISCV64.Ecb
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Modes.RISCV64.Core
meta import VerifiedGarbage.Proof.Idea.RISCV64.Ecb
meta import VerifiedGarbage.Proof.Idea.ModeBytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Modes.RISCV64.Modes
meta import VerifiedGarbage.Proof.Modes.RISCV64.Seq
meta import VerifiedGarbage.Proof.Modes.Steps

/-! ### `Idea.RISCV64.FbFinalVerified`, which only this module used -/

section

/-! ### `Idea.RISCV64.ModesVerified`, which this module and modules that import it used -/

section

/-! ### `Idea.RISCV64.ModeCore`, which only this module used -/

section

/-!
# IDEA's core for the modes on RISC-V

`coreSpec`: IDEA's core (`Impl.Idea.RISCV64.core`) meets what the modes need
of a core (`Proof.Modes.RISCV64.CoreSpec`), with the key a schedule of
subkeys, read in place through `a0`, its cipher `Spec.Idea.cipher`, as on
PPC64LE. The schedule is readable and apart from the regions the mode
writes (`KeyArgs`), and from the frame (`Ready`), so nothing the mode or
the core writes changes it. The core runs ECB's block code on its buffer
(`cryptBlock_ok`).
-/

@[expose] public section

namespace VG.Proof.Idea.RISCV64.Mode

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Idea.RISCV64
open VG.Impl.Modes.RISCV64 (sb)
open VG.Proof.Modes.RISCV64 (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept KeptBut)

/-- The schedule. -/
abbrev keyR (s : State) : Region := ⟨s.gpr .a0, 104⟩

/-- The schedule at `a0` is `k`, readable, and apart from the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Idea.Schedule) : Prop :=
  Spec.Idea.scheduleAt s.mem (s.gpr .a0) = k ∧ keyR s ∈ s.rd ++ s.wr ∧ ∀ r ∈ rs, (keyR s).Disjoint r

/-- The key's arguments, apart from the frame at `B` too. -/
def Ready (s : State) (B : Addr) (ws : List Region) (k : Spec.Idea.Schedule) : Prop :=
  KeyArgs s ws k ∧ (keyR s).Disjoint ⟨B, 8 * 8⟩

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Idea.Schedule} (h : KeyArgs s rs k)
    (e : s'.gpr .a0 = s.gpr .a0) (hrd : s'.rd = s.rd) (hwr : ∃ ws, s'.wr = ws ++ s.wr)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨hk, hin, hd⟩ := h
  obtain ⟨ws, hw⟩ := hwr
  refine ⟨?_, ?_, by rw [keyR, e]; exact hd⟩
  · rw [e, Proof.Idea.scheduleAt_frame hf hd, hk]
  · rw [hrd, hw, keyR, e]
    rcases List.mem_append.mp hin with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_append_right _ h)

theorem ready_frame {s s' : State} {B : Addr} {ws : List Region} {k : Spec.Idea.Schedule}
    {rs : List Region} (h : Ready s B ws k) (e : s'.gpr .a0 = s.gpr .a0) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, ∃ r' ∈ ws, Region.Sub r r') :
    Ready s' B ws k := by
  obtain ⟨⟨hk, hin, hd⟩, hB⟩ := h
  have hd' : ∀ r ∈ rs, (keyR s).Disjoint r := fun r hr => by
    obtain ⟨r', hr', hsub⟩ := hs r hr
    exact (hd r' hr').sub_right hsub
  refine ⟨⟨?_, by rw [hrd, hwr, keyR, e]; exact hin, by rw [keyR, e]; exact hd⟩, by rw [keyR, e]; exact hB⟩
  rw [e, Proof.Idea.scheduleAt_frame hf hd', hk]

theorem layout : Layout core :=
  ⟨by decide, .inl rfl, by decide, by decide, by decide, by decide, by decide⟩

theorem prepare_wp {s : State} {B : Addr} {rs : List Region} {k : Spec.Idea.Schedule}
    (hB : s.gpr sb = B) (_hS : ScrIn s B core.total) (hm : (⟨B, 8 * core.total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa core.prepare s fun s' => Ready s' B rs k ∧ s'.gpr sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion core B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.block_nil ⟨⟨hk, hk.2.2 _ hm⟩, hB, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩

/-- The registers the core writes. -/
abbrev coreWrites : List Reg := [.t2, .a1] ++ roundWrites

/-- The kept registers are none the core writes. -/
theorem kept_apart : ∀ r ∈ kept, r ∉ coreWrites := by decide

theorem crypt_wp {s : State} {B : Addr} {ws : List Region} {k : Spec.Idea.Schedule}
    (hB : s.gpr sb = B) (hS : ScrIn s B core.total) (hR : Ready s B ws k) :
    WP isa core.crypt s fun s' => s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Ready s' B ws k ∧ Frame [coreRegion core B] s.mem s'.mem ∧
      (∀ j < core.G, Spec.Aes.bytesAt s'.mem (blkAddr core B j) (4 * core.bw) =
        Spec.Idea.cipher k (Spec.Aes.bytesAt s.mem (blkAddr core B j) (4 * core.bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit : B.toNat + 8 * 8 ≤ 2 ^ 64 := hS.fit
  have hW : (⟨B, 8 * 8⟩ : Region) ∈ s.wr := hS.whole (by decide)
  obtain ⟨⟨hk, hin, hd⟩, hkB⟩ := hR
  simp only [core]
  -- The mask.
  refine WP.seq (WP.mono (WP.keep [.t2] (Q := fun t => t.gpr .t2 = 65535 ∧ t.mem = s.mem)
    (setMask_ok s) (by decide) rfl) fun s₁ ⟨⟨h2₁, m₁⟩, k₁⟩ => ?_)
  -- The buffer's address.
  refine WP.seq (wp_addi (by decide) fun s₂ u₂ => WP.block_nil ?_)
  have a₂ : s₂.gpr .a1 = B + BitVec.ofNat 64 48 := by
    rw [u₂.gpr, k₁.gpr (show sb ∉ [Reg.t2] by decide), hB]; rfl
  have K₂ : Keep [.t2, .a1] s s₂ := ⟨fun r hr => by
      rw [u₂.other r fun e => hr (by rw [e]; decide), k₁.gpr fun h => hr (by
        simp only [List.mem_singleton] at h; rw [h]; decide)],
    by rw [u₂.rd, k₁.2.1], by rw [u₂.wr, k₁.2.2]⟩
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, m₁]
  have a0₂ : s₂.gpr .a0 = s.gpr .a0 := K₂.gpr (by decide)
  have hk₂ : KeyOk k s₂ := by
    have h := keyOk_of s₂ (by rw [a0₂, K₂.2.1, K₂.2.2]; exact hin)
      (by rw [u₂.other _ (by decide)]; exact h2₁)
    rwa [m₂, a0₂, hk] at h
  have hc (i : Nat) (hi : i < 8) : (⟨B, 8 * 8⟩ : Region).Contains
      (B + BitVec.ofNat 64 48 + BitVec.ofNat 64 i) 1 := by
    rw [Offset.add_add]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
  have hread : BlockRead s₂ (B + BitVec.ofNat 64 48) := fun i hi => by
    rw [K₂.2.1, K₂.2.2]
    exact ⟨_, List.mem_append_right _ hW, hc i hi⟩
  have hwrite : BlockWrite s₂ (B + BitVec.ofNat 64 48) := fun i hi => by
    rw [K₂.2.2]
    exact ⟨_, hW, hc i hi⟩
  -- The block.
  refine WP.mono (cryptBlock_ok k s₂ a₂ hread hwrite hk₂) fun t ⟨b, f, e⟩ => ?_
  have Kt : Keep coreWrites s t := (K₂.trans e).mono (by decide)
  have a0t : t.gpr .a0 = s.gpr .a0 := Kt.gpr (by decide)
  have ft : Frame [⟨B + BitVec.ofNat 64 48, 8⟩] s.mem t.mem := by rw [← m₂]; exact f
  have hbuf : (keyR s).Disjoint ⟨B + BitVec.ofNat 64 48, 8⟩ :=
    hkB.sub_right (Offset.sub_base B (by omega_using []))
  have hB0 : blkAddr core B 0 = B + BitVec.ofNat 64 48 := by simp [blkAddr, slotA, core, bufSlot]
  refine ⟨(Kt.gpr (by decide)).trans hB, fun r hr => Kt.gpr (kept_apart r hr),
    ⟨⟨?_, by rw [Kt.2.1, Kt.2.2, keyR, a0t]; exact hin, by rw [keyR, a0t]; exact hd⟩,
      by rw [keyR, a0t]; exact hkB⟩,
    ft.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, fun j hj => ?_, Kt.2.1, Kt.2.2⟩
  · rw [a0t, Proof.Idea.scheduleAt_frame ft fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hbuf, hk]
  · simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by decide)
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
  keyArgs_congr h e r w _ f := keyArgs_congr h e.a0 r w f
  ready_frame h e r w _ f hs _ := ready_frame h e.a0 r w f hs
  prepare_wp := prepare_wp
  crypt_wp := crypt_wp

end VG.Proof.Idea.RISCV64.Mode

end

end

/-! ### `Idea.RISCV64.ModesConstantTime`, which only this module used -/

section

/-!
# Constant-time IDEA modes on RISC-V

Only the pointers and the count (`a0`–`a3`) and the stack pointer are
public. The modes keep their state in `s1`–`s4`, which the block code never
writes, and zero the frame through `t3`, a copy of its base made before the
caller's `s1`–`s4` come back from memory.
-/

@[expose] public section

namespace VG.Proof.Idea.RISCV64

open VG VG.RISCV64 VG.Impl.Idea.RISCV64

/-- The modes' public arguments: the stack pointer and `a0`–`a3`. -/
def modePub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.a0, .a1, .a2, .a3], s₁.gpr r = s₂.gpr r

theorem modes_ofRegs (s₁ s₂ : State) (h : modePub s₁ s₂) :
    taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3]) s₁ s₂ :=
  ⟨h.1, fun r hr => h.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem cbcEncryptChained_constantTime (pre : State → Prop) :
    ConstantTime isa pre modePub cbcEncryptChained :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cbcDecryptChained_constantTime (pre : State → Prop) :
    ConstantTime isa pre modePub cbcDecryptChained :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem ofb_constantTime (pre : State → Prop) : ConstantTime isa pre modePub ofb :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfbEncrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbEncrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfbDecrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbDecrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

end VG.Proof.Idea.RISCV64

end

end

/-!
# IDEA's modes on RISC-V meet their contracts

`cbcEncryptChained_verified`, `ofb_verified`, … : the modes of
`Proof/Modes/RISCV64/` over IDEA's core (`Mode.coreSpec`) meet the shared
contracts, with `stack := 64`: the mode's frame of 8 slots below the stack
pointer, which it zeroes before returning. The proofs are written against
`modeContract`, which states the frame.
-/

@[expose] public section

namespace VG.Proof.Idea.RISCV64.Modes

open VG VG.RISCV64 VG.Impl.Idea.RISCV64 VG.Impl.Modes
open VG.Proof.Modes.RISCV64 (SeqPre ivR scrRegion Fb)
open VG.Proof.Idea.RISCV64.Mode (coreSpec KeyArgs layout)
open VG.Proof.Idea.RISCV64 (modePub)

/-- The frame's bytes. -/
abbrev frameBytes : Nat := 64

/-- IDEA under the subkeys at `a0`. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher :=
  Spec.Idea.cipher (Spec.Idea.scheduleAt s.mem (s.gpr .a0))
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m (s.gpr .a1) 8
/-- The data, in blocks. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) :=
  Spec.Idea.cbcBlocksAt m (s.gpr .a2) (s.gpr .a3).toNat

/-- The functions' postconditions. -/
def cbcEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cbcDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)
def ofbPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ofb.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ofb.next (ciph s) (ivAt s.mem s) (s.gpr .a3).toNat
def cfbEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cfbDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

/-- A mode's function on RISC-V, with its frame below the stack pointer,
and the postcondition `post`. -/
def modeContract (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 104⟩
    let iv : Region := ⟨s.gpr .a1, 8⟩
    let data : Region := ⟨s.gpr .a2, 8 * (s.gpr .a3).toNat⟩
    let stack : Region := ⟨s.sp - frameBytes, frameBytes⟩
    s.rd = [key] ∧ s.wr = [iv, data] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ iv.Disjoint data ∧
      (s.gpr .a1).toNat + 8 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8 * (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ frameBytes ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint iv ∧
      stack.Disjoint data
  post := post
  pub := modePub

/-- `modeContract`'s precondition gives the modes'. -/
theorem seqPre_of {post : State → State → Prop} {M : Mode} (hstep : M.step = 8) {s : State}
    (h : (modeContract post).pre s) : SeqPre core M s := by
  obtain ⟨-, hwr, -, -, dVD, fV, fD, al, sp, -, dSV, dSD⟩ := h
  have e8 : 4 * core.bw = 8 := rfl
  have eS : scrRegion core (Fb s core) = ⟨s.sp - frameBytes, frameBytes⟩ := rfl
  have eV : ivR s core = ⟨s.gpr .a1, 8⟩ := rfl
  refine ⟨al, sp, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp, by rw [e8]; exact fV,
    by rw [hwr, hstep]; simp, by rw [hstep]; exact fD, by rw [hstep, eS]; exact dSD.symm,
    by rw [eV, eS]; exact dSV.symm, fun _ => by rw [eV, hstep]; exact dVD, ⟨by omega_using [hstep], by rw [e8]; omega_using [hstep]⟩,
    layout⟩

theorem keyArgs_of {post : State → State → Prop} {M : Mode} (hstep : M.step = 8) {s : State}
    (h : (modeContract post).pre s) :
    KeyArgs s (Proof.Modes.RISCV64.wrs0 core M s) (Spec.Idea.scheduleAt s.mem (s.gpr .a0)) := by
  obtain ⟨hrd, -, -, dKD, -, -, -, -, -, dSK, -, -⟩ := h
  refine ⟨rfl, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), fun r hr => ?_⟩
  simp only [Proof.Modes.RISCV64.wrs0, Proof.Modes.RISCV64.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .a0) 104).Disjoint ⟨s.gpr .a2, M.step * (s.gpr .a3).toNat⟩
    rw [hstep]; exact dKD
  · exact dSK.symm

/-- The data in blocks, as the modes' steps. -/
theorem cbcBlocksAt_eq (m : Mem) (p : Addr) (n : Nat) :
    Spec.Idea.cbcBlocksAt m p n = Proof.Modes.chunksAt 8 m p n := by
  simp only [Spec.Idea.cbcBlocksAt, Spec.Idea.blocksAt, Proof.Modes.chunksAt, List.map_map]
  exact List.map_congr_left fun i _ => (Proof.Idea.bytesAt_eq m _).symm

/-! ## Correctness -/

theorem cbcEncryptChained_correct (s : State) (hs : (modeContract cbcEncPost).pre s) :
    ∃ t s', Exec isa cbcEncryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract cbcEncPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cbcEncChained_wp coreSpec
    (seqPre_of (M := Mode.cbcEncChained 2) rfl hs) (keyArgs_of (M := Mode.cbcEncChained 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem cbcDecryptChained_correct (s : State) (hs : (modeContract cbcDecPost).pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract cbcDecPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cbcDecChained_wp coreSpec
    (seqPre_of (M := Mode.cbcDecChained 2) rfl hs) (keyArgs_of (M := Mode.cbcDecChained 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem ofb_correct (s : State) (hs : (modeContract ofbPost).pre s) :
    ∃ t s', Exec isa ofb s t s' ∧ abiPreserved s s' ∧ (modeContract ofbPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.ofb_wp coreSpec
    (seqPre_of (M := Mode.ofb 2) rfl hs) (keyArgs_of (M := Mode.ofb 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2, h3⟩

theorem cfbEncrypt_correct (s : State) (hs : (modeContract cfbEncPost).pre s) :
    ∃ t s', Exec isa cfbEncrypt s t s' ∧ abiPreserved s s' ∧ (modeContract cfbEncPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbEnc_wp coreSpec
    (seqPre_of (M := Mode.cfbEnc 2) rfl hs) (keyArgs_of (M := Mode.cfbEnc 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem cfbDecrypt_correct (s : State) (hs : (modeContract cfbDecPost).pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ (modeContract cfbDecPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbDec_wp coreSpec
    (seqPre_of (M := Mode.cfbDec 2) rfl hs) (keyArgs_of (M := Mode.cfbDec 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

/-! ## The contracts -/

/-- A state satisfying the modes' precondition: the subkeys at `0x1000`,
the IV at `0x3000`, no data at `0x4000`, and the stack below `0x8000`. -/
def modeSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a2 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 0⟩]

theorem modePub_iff (s₁ s₂ : State) : modePub s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 := by
  simp [modePub]

theorem cbcEncryptChained_verified :
    Verified RISCV64.target cbcEncryptChained
      (Spec.Idea.cbcEncryptChainedContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cbcEncryptChained_correct (cbcEncryptChained_constantTime _) ?_
  contract_implies [Spec.Idea.cbcEncryptChainedContract, Spec.Idea.cbcChainedSig,
    RISCV64.abi, RISCV64.argRegs, modeContract, cbcEncPost, modePub_iff] [modeSat] using modeSat

theorem cbcDecryptChained_verified :
    Verified RISCV64.target cbcDecryptChained
      (Spec.Idea.cbcDecryptChainedContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cbcDecryptChained_correct (cbcDecryptChained_constantTime _) ?_
  contract_implies [Spec.Idea.cbcDecryptChainedContract, Spec.Idea.cbcChainedSig,
    RISCV64.abi, RISCV64.argRegs, modeContract, cbcDecPost, modePub_iff] [modeSat] using modeSat

theorem ofb_verified : Verified RISCV64.target ofb (Spec.Idea.ofbContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct ofb_correct (ofb_constantTime _) ?_
  contract_implies [Spec.Idea.ofbContract, Spec.Idea.ofbSig, RISCV64.abi, RISCV64.argRegs,
    modeContract, ofbPost, modePub_iff] [modeSat] using modeSat

theorem cfbEncrypt_verified :
    Verified RISCV64.target cfbEncrypt (Spec.Idea.cfbEncryptContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cfbEncrypt_correct (cfbEncrypt_constantTime _) ?_
  contract_implies [Spec.Idea.cfbEncryptContract, Spec.Idea.cfbSig, RISCV64.abi,
    RISCV64.argRegs, modeContract, cfbEncPost, modePub_iff] [modeSat] using modeSat

theorem cfbDecrypt_verified :
    Verified RISCV64.target cfbDecrypt (Spec.Idea.cfbDecryptContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cfbDecrypt_correct (cfbDecrypt_constantTime _) ?_
  contract_implies [Spec.Idea.cfbDecryptContract, Spec.Idea.cfbSig, RISCV64.abi,
    RISCV64.argRegs, modeContract, cfbDecPost, modePub_iff] [modeSat] using modeSat

end VG.Proof.Idea.RISCV64.Modes

end

end

/-!
# IDEA-CFB64 and IDEA-OFB of a message's last piece on RISC-V meet their contracts

The modes' CFB and OFB over a message's last piece (`Proof.Modes.RISCV64.cfbEncFinal_wp`,
`cfbDecFinal_wp`, `ofbFinal_wp`) over IDEA's core (`Mode.coreSpec`) meet the contracts,
with `stack := 64`, the frame of the whole-block functions (`ModesVerified.lean`),
whose precondition, with the data `len` bytes, is `seq`'s for the data a byte
at a time (`byteMode`). Constant time as the whole-block functions.
-/

@[expose] public section

namespace VG.Proof.Idea.RISCV64.Modes

open VG VG.RISCV64 VG.Impl.Idea.RISCV64 VG.Impl.Modes
open VG.Proof.Modes.RISCV64 (SeqPre ivR scrRegion Fb byteMode)
open VG.Proof.Idea.RISCV64.Mode (coreSpec KeyArgs layout)
open VG.Proof.Idea.RISCV64 (modePub modes_ofRegs)

/-- The final functions' postconditions. -/
def encFinalPost (s s' : State) : Prop :=
  Spec.Cfb.EncryptFinal (ciph s) 8 s.mem s'.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3).toNat
def decFinalPost (s s' : State) : Prop :=
  Spec.Cfb.DecryptFinal (ciph s) 8 s.mem s'.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3).toNat
def ofbFinalPost (s s' : State) : Prop :=
  Spec.Ofb.CryptFinal (ciph s) 8 s.mem s'.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3).toNat

/-- A final function on RISC-V, with its frame below the stack pointer, the
data `len` bytes, and the postcondition `post`. -/
def finalContract (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 104⟩
    let iv : Region := ⟨s.gpr .a1, 8⟩
    let data : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let stack : Region := ⟨s.sp - frameBytes, frameBytes⟩
    s.rd = [key] ∧ s.wr = [iv, data] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ iv.Disjoint data ∧
      (s.gpr .a1).toNat + 8 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ frameBytes ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint iv ∧
      stack.Disjoint data
  post := post
  pub := modePub

theorem seqPreF_of {post : State → State → Prop} {s : State} (h : (finalContract post).pre s) :
    SeqPre core byteMode s := by
  obtain ⟨-, hwr, -, -, dVD, fV, fD, al, sp, -, dSV, dSD⟩ := h
  have e8 : 4 * core.bw = 8 := rfl
  have eS : scrRegion core (Fb s core) = ⟨s.sp - frameBytes, frameBytes⟩ := rfl
  have eV : ivR s core = ⟨s.gpr .a1, 8⟩ := rfl
  have eD : Proof.Modes.RISCV64.dataRegion (s.gpr .a2) byteMode.step (s.gpr .a3).toNat =
      ⟨s.gpr .a2, (s.gpr .a3).toNat⟩ := by
    simp only [Proof.Modes.RISCV64.dataRegion, byteMode, Nat.one_mul]
  refine ⟨al, sp, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp, by rw [e8]; exact fV,
    by rw [eD, hwr]; simp, by simp only [byteMode, Nat.one_mul]; exact fD, by rw [eD, eS]; exact dSD.symm,
    by rw [eV, eS]; exact dSV.symm, fun _ => by rw [eV, eD]; exact dVD, ⟨by decide, by rw [e8]; decide⟩, layout⟩

theorem keyArgsF_of {post : State → State → Prop} {s : State} (h : (finalContract post).pre s) :
    KeyArgs s (Proof.Modes.RISCV64.wrs0 core byteMode s) (Spec.Idea.scheduleAt s.mem (s.gpr .a0)) := by
  obtain ⟨hrd, -, -, dKD, -, -, -, -, -, dSK, -, -⟩ := h
  refine ⟨rfl, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), fun r hr => ?_⟩
  simp only [Proof.Modes.RISCV64.wrs0, Proof.Modes.RISCV64.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .a0) 104).Disjoint ⟨s.gpr .a2, 1 * (s.gpr .a3).toNat⟩
    rw [Nat.one_mul]; exact dKD
  · exact dSK.symm

theorem cfbEncryptFinal_correct (s : State) (hs : (finalContract encFinalPost).pre s) :
    ∃ t s', Exec isa cfbEncryptFinal s t s' ∧ abiPreserved s s' ∧ (finalContract encFinalPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbEncFinal_wp coreSpec (seqPreF_of hs) (keyArgsF_of hs))
    fun _ ⟨h1, h2, _⟩ => ⟨h1, h2⟩

theorem cfbDecryptFinal_correct (s : State) (hs : (finalContract decFinalPost).pre s) :
    ∃ t s', Exec isa cfbDecryptFinal s t s' ∧ abiPreserved s s' ∧ (finalContract decFinalPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbDecFinal_wp coreSpec (seqPreF_of hs) (keyArgsF_of hs))
    fun _ ⟨h1, h2, _⟩ => ⟨h1, h2⟩

theorem ofbFinal_correct (s : State) (hs : (finalContract ofbFinalPost).pre s) :
    ∃ t s', Exec isa ofbFinal s t s' ∧ abiPreserved s s' ∧ (finalContract ofbFinalPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.ofbFinal_wp coreSpec (seqPreF_of hs) (keyArgsF_of hs))
    fun _ ⟨h1, h2, _⟩ => ⟨h1, h2⟩

/-! ## Constant time -/

theorem cfbEncryptFinal_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbEncryptFinal :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfbDecryptFinal_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbDecryptFinal :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem ofbFinal_constantTime (pre : State → Prop) : ConstantTime isa pre modePub ofbFinal :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

/-! ## The contracts -/

theorem cfbEncryptFinal_verified :
    Verified RISCV64.target cfbEncryptFinal (Spec.Idea.cfbEncryptFinalContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cfbEncryptFinal_correct (cfbEncryptFinal_constantTime _) ?_
  contract_implies [Spec.Idea.cfbEncryptFinalContract, Spec.Idea.cfbFinalSig, RISCV64.abi,
    RISCV64.argRegs, finalContract, encFinalPost, modePub_iff] [modeSat] using modeSat

theorem cfbDecryptFinal_verified :
    Verified RISCV64.target cfbDecryptFinal (Spec.Idea.cfbDecryptFinalContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cfbDecryptFinal_correct (cfbDecryptFinal_constantTime _) ?_
  contract_implies [Spec.Idea.cfbDecryptFinalContract, Spec.Idea.cfbFinalSig, RISCV64.abi,
    RISCV64.argRegs, finalContract, decFinalPost, modePub_iff] [modeSat] using modeSat

theorem ofbFinal_verified :
    Verified RISCV64.target ofbFinal (Spec.Idea.ofbFinalContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct ofbFinal_correct (ofbFinal_constantTime _) ?_
  contract_implies [Spec.Idea.ofbFinalContract, Spec.Idea.ofbFinalSig, RISCV64.abi,
    RISCV64.argRegs, finalContract, ofbFinalPost, modePub_iff] [modeSat] using modeSat

end VG.Proof.Idea.RISCV64.Modes

end

end

/-!
# Idea on RISC-V, without secret residue

Each function, followed by `Impl.Scrub.RISCV64.scrubTail`
(`Impl.Idea.RISCV64.Fn`, the functions as emitted), which clears the
caller-saved registers and the stack its frames used. Their postconditions read the memory on return only
within their buffers (`RISCV64.Scrub.PostOut`), as on x86-64
(`Proof/Idea/X86_64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Idea.RISCV64.Scrub

open VG.Spec.Idea VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Idea.ScrubLocal

/-! ## Postconditions -/
theorem len_le (ln : BitVec 64) (k : Nat) :
    ((ArgWord.int abi.ptrBits).ofRaw ln).toNat * k ≤ ln.toNat * k :=
  Nat.le_refl _

theorem len_le1 (ln : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw ln).toNat ≤ ln.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

theorem expandKeyOut (stack : Nat) : PostOut (expandKeyContract RISCV64.abi stack) (expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show scheduleAt m₂ sc = _
    rw [scheduleAt_of hb.2]
    exact h

theorem invertKeyOut (stack : Nat) : PostOut (invertKeyContract RISCV64.abi stack) (invertKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨inv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [invertKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show scheduleAt m₂ inv = _
    rw [scheduleAt_of hb.2]
    exact h

theorem ecbOut (stack : Nat) : PostOut (ecbContract RISCV64.abi stack) (ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show blocksAt m₂ dt _ = _
    rw [blocksAt_of hb.2 (len_le ln 8)]
    exact h

theorem cbcEncryptOut (stack : Nat) : PostOut (cbcEncryptChainedContract RISCV64.abi stack) (cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cbcDecryptOut (stack : Nat) : PostOut (cbcDecryptChainedContract RISCV64.abi stack) (cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbEncryptOut (stack : Nat) : PostOut (cfbEncryptContract RISCV64.abi stack) (cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbDecryptOut (stack : Nat) : PostOut (cfbDecryptContract RISCV64.abi stack) (cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem ofbOut (stack : Nat) : PostOut (ofbContract RISCV64.abi stack) (ofbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbEncryptFinalOut (stack : Nat) : PostOut (cfbEncryptFinalContract RISCV64.abi stack) (cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [bytesAt_of hb.2.2 (len_le1 ln), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbDecryptFinalOut (stack : Nat) : PostOut (cfbDecryptFinalContract RISCV64.abi stack) (cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [bytesAt_of hb.2.2 (len_le1 ln), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem ofbFinalOut (stack : Nat) : PostOut (ofbFinalContract RISCV64.abi stack) (ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [bytesAt_of hb.2.2 (len_le1 ln), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

/-! ## The functions as emitted

Each theorem states that a function as emitted (`Impl.Idea.RISCV64.Fn`) meets its
contract in constant time and returns without secret residue
(`VerifiedScrubbed`, by `RISCV64.Scrub.verifiedScrubbed`, or
`verifiedScrubbedSelT` for the selective cleanup, whose residue analysis the
kernel evaluates here): what its registration binds. -/

/-- `Spec.Idea.expandKeyApi` as emitted (`Impl.Idea.RISCV64.Fn.expandKey`) meets its contract
in constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Idea.RISCV64.Fn.expandKey
      (Spec.Idea.expandKeyContract RISCV64.abi) 0 :=
  verifiedScrubbed (api := Spec.Idea.expandKeyApi) (W := 0) (rb := 0)
    { code := Impl.Idea.RISCV64.expandKey
      verified := Proof.Idea.RISCV64.expandKey_verified }
    (expandKeyOut _) (by dsimp only; lit_decide)

/-- `Spec.Idea.invertKeyApi` as emitted (`Impl.Idea.RISCV64.Fn.invertKey`) meets its contract
in constant time and returns without secret residue. -/
theorem invertKey_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Idea.RISCV64.Fn.invertKey
      (Spec.Idea.invertKeyContract RISCV64.abi) 0 :=
  verifiedScrubbed (api := Spec.Idea.invertKeyApi) (W := 0) (rb := 0)
    { code := Impl.Idea.RISCV64.invertKey
      verified := Proof.Idea.RISCV64.invertKey_verified }
    (invertKeyOut _) (by dsimp only; lit_decide)

/-- `Spec.Idea.ecbApi` as emitted (`Impl.Idea.RISCV64.Fn.ecb`) meets its contract
in constant time and returns without secret residue. -/
theorem ecb_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Idea.RISCV64.Fn.ecb
      (Spec.Idea.ecbContract RISCV64.abi) 0 :=
  verifiedScrubbed (api := Spec.Idea.ecbApi) (W := 0) (rb := 0)
    { code := Impl.Idea.RISCV64.ecb
      verified := Proof.Idea.RISCV64.ecb_verified }
    (ecbOut _) (by dsimp only; lit_decide)

/-- `Spec.Idea.cbcEncryptChainedApi` as emitted (`Impl.Idea.RISCV64.Fn.cbcEncryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Idea.RISCV64.Fn.cbcEncryptChained
      (Spec.Idea.cbcEncryptChainedContract RISCV64.abi Proof.Idea.RISCV64.Modes.frameBytes) 0 :=
  verifiedScrubbed (api := Spec.Idea.cbcEncryptChainedApi) (W := 64) (rb := 0)
    { code := Impl.Idea.RISCV64.cbcEncryptChained
      verified := Proof.Idea.RISCV64.Modes.cbcEncryptChained_verified }
    (cbcEncryptOut _) (by dsimp only; lit_decide)

/-- `Spec.Idea.cbcDecryptChainedApi` as emitted (`Impl.Idea.RISCV64.Fn.cbcDecryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Idea.RISCV64.Fn.cbcDecryptChained
      (Spec.Idea.cbcDecryptChainedContract RISCV64.abi Proof.Idea.RISCV64.Modes.frameBytes) 0 :=
  verifiedScrubbed (api := Spec.Idea.cbcDecryptChainedApi) (W := 64) (rb := 0)
    { code := Impl.Idea.RISCV64.cbcDecryptChained
      verified := Proof.Idea.RISCV64.Modes.cbcDecryptChained_verified }
    (cbcDecryptOut _) (by dsimp only; lit_decide)

/-- `Spec.Idea.cfbEncryptApi` as emitted (`Impl.Idea.RISCV64.Fn.cfbEncrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Idea.RISCV64.Fn.cfbEncrypt
      (Spec.Idea.cfbEncryptContract RISCV64.abi Proof.Idea.RISCV64.Modes.frameBytes) 0 :=
  verifiedScrubbed (api := Spec.Idea.cfbEncryptApi) (W := 64) (rb := 0)
    { code := Impl.Idea.RISCV64.cfbEncrypt
      verified := Proof.Idea.RISCV64.Modes.cfbEncrypt_verified }
    (cfbEncryptOut _) (by dsimp only; lit_decide)

/-- `Spec.Idea.cfbDecryptApi` as emitted (`Impl.Idea.RISCV64.Fn.cfbDecrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Idea.RISCV64.Fn.cfbDecrypt
      (Spec.Idea.cfbDecryptContract RISCV64.abi Proof.Idea.RISCV64.Modes.frameBytes) 0 :=
  verifiedScrubbed (api := Spec.Idea.cfbDecryptApi) (W := 64) (rb := 0)
    { code := Impl.Idea.RISCV64.cfbDecrypt
      verified := Proof.Idea.RISCV64.Modes.cfbDecrypt_verified }
    (cfbDecryptOut _) (by dsimp only; lit_decide)

/-- `Spec.Idea.cfbEncryptFinalApi` as emitted (`Impl.Idea.RISCV64.Fn.cfbEncryptFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Idea.RISCV64.Fn.cfbEncryptFinal
      (Spec.Idea.cfbEncryptFinalContract RISCV64.abi Proof.Idea.RISCV64.Modes.frameBytes) 0 :=
  verifiedScrubbed (api := Spec.Idea.cfbEncryptFinalApi) (W := 64) (rb := 0)
    { code := Impl.Idea.RISCV64.cfbEncryptFinal
      verified := Proof.Idea.RISCV64.Modes.cfbEncryptFinal_verified }
    (cfbEncryptFinalOut _) (by dsimp only; lit_decide)

/-- `Spec.Idea.cfbDecryptFinalApi` as emitted (`Impl.Idea.RISCV64.Fn.cfbDecryptFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Idea.RISCV64.Fn.cfbDecryptFinal
      (Spec.Idea.cfbDecryptFinalContract RISCV64.abi Proof.Idea.RISCV64.Modes.frameBytes) 0 :=
  verifiedScrubbed (api := Spec.Idea.cfbDecryptFinalApi) (W := 64) (rb := 0)
    { code := Impl.Idea.RISCV64.cfbDecryptFinal
      verified := Proof.Idea.RISCV64.Modes.cfbDecryptFinal_verified }
    (cfbDecryptFinalOut _) (by dsimp only; lit_decide)

/-- `Spec.Idea.ofbApi` as emitted (`Impl.Idea.RISCV64.Fn.ofb`) meets its contract
in constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Idea.RISCV64.Fn.ofb
      (Spec.Idea.ofbContract RISCV64.abi Proof.Idea.RISCV64.Modes.frameBytes) 0 :=
  verifiedScrubbed (api := Spec.Idea.ofbApi) (W := 64) (rb := 0)
    { code := Impl.Idea.RISCV64.ofb
      verified := Proof.Idea.RISCV64.Modes.ofb_verified }
    (ofbOut _) (by dsimp only; lit_decide)

/-- `Spec.Idea.ofbFinalApi` as emitted (`Impl.Idea.RISCV64.Fn.ofbFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Idea.RISCV64.Fn.ofbFinal
      (Spec.Idea.ofbFinalContract RISCV64.abi Proof.Idea.RISCV64.Modes.frameBytes) 0 :=
  verifiedScrubbed (api := Spec.Idea.ofbFinalApi) (W := 64) (rb := 0)
    { code := Impl.Idea.RISCV64.ofbFinal
      verified := Proof.Idea.RISCV64.Modes.ofbFinal_verified }
    (ofbFinalOut _) (by dsimp only; lit_decide)

end VG.Proof.Idea.RISCV64.Scrub
