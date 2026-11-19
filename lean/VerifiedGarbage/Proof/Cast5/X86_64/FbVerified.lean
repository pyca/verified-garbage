module

public import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Proof.Cast5.X86_64.EcbVerified
public import VerifiedGarbage.Proof.Cast5.ModeScratch
public import VerifiedGarbage.Proof.Modes.X86_64.FbLoop
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Modes.X86_64.Fb
import VerifiedGarbage.Proof.Modes.X86_64.KeepIv
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchConsts
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Cast5.X86_64.EcbVerified
meta import VerifiedGarbage.Proof.Cast5.ModeScratch
meta import VerifiedGarbage.Proof.Modes.X86_64.FbLoop
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Modes.X86_64.Fb
meta import VerifiedGarbage.Proof.Modes.X86_64.KeepIv
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
public import VerifiedGarbage.Proof.Cast5.ModeCipher
public import VerifiedGarbage.Proof.Modes.X86_64.Core
public import VerifiedGarbage.Impl.Cast5.X86_64.Modes
public import VerifiedGarbage.Proof.Cast5.X86_64.Block
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Modes.X86_64.Setup
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Modes.X86_64.Words
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Cast5.ModeCipher
meta import VerifiedGarbage.Proof.Modes.X86_64.Core
meta import VerifiedGarbage.Impl.Cast5.X86_64.Modes
meta import VerifiedGarbage.Proof.Cast5.X86_64.Block
meta import VerifiedGarbage.Proof.Cast5.Memory
meta import VerifiedGarbage.Proof.Modes.X86_64.Setup
meta import VerifiedGarbage.Proof.Modes.X86_64.Steps
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Modes.X86_64.Words
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Cast5.X86_64.ModeCore`, which this module and modules that import it used -/

section

/-!
# CAST5's core for the modes on x86-64

`dirCoreSpec up`: CAST5's core (`Impl.Cast5.X86_64.dirCore up`) meets what
the modes need of a core of one-word blocks (`Proof.Modes.X86_64.BlockSpec`),
with the key the subkeys and the number of rounds, its cipher encryption
(`up`) or decryption (`Proof.Cast5.dirCipher`), and the key ready (`Ready`)
when the schedule's copy in the core's slots is the subkeys, `rsi` holds
the number of rounds, and the table of S-boxes is where the static
`VG_CAST5_S1234` puts it, readable and apart from every writable region
(`TabAt`). `crypt` is ECB's block code (`encryptBlock_ok`,
`decryptBlock_ok`) on the buffer, between its own setup and finish.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86_64.Mode

open VG VG.X86_64 VG.Impl.Cast5.X86_64
open VG.Impl.Cast5 (s1234Sym s1234)
open VG.Impl.Aes.X86_64 (sb movR)
open VG.Proof.Cast5 (Held dirCipher dirCipher_length bytesAt_eq ofFn_bytesAt)
open VG.Proof.Modes (over over_at over_frame)
open VG.Proof.Modes.X86_64 (ScrIn WrIn coreRegion blkRegion blkAddr BlockSpec copyN_wp movR_ok addImm_ok
  signExtend_small runBlock_app runBlock_syms addr_add ld_ok stM_ok)

/-! ## Memory -/

theorem scheduleAt_congr_at {m m' : Mem} {p q : Addr}
    (h : ∀ i < 128, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    Spec.Cast5.scheduleAt m' q = Spec.Cast5.scheduleAt m p := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Cast5.scheduleAt, Vector.getElem_ofFn]
  rw [h _ (by omega_arith), h _ (by omega_arith), h _ (by omega_arith), h _ (by omega_arith)]

theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 128⟩ r) : Spec.Cast5.scheduleAt m' p = Spec.Cast5.scheduleAt m p :=
  scheduleAt_congr_at fun _ hi => hf.bytes (R := ⟨p, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) hi

theorem held_frame {rs : List Region} {m m' : Mem} {T : Addr} (h : Held m T s1234) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨T, 4096⟩ r) : Held m' T s1234 := by
  intro i hi
  rw [s1234_length] at hi
  rw [← h i (by rw [s1234_length]; exact hi)]
  exact hf.readW (r := ⟨T, 4096⟩) (Offset.contains_base _ (by omega_arith) (by omega_arith)) hd (by decide)

theorem toNat_add {B : Addr} {d : Nat} (h : B.toNat + d < 2 ^ 64) :
    (B + BitVec.ofNat 64 d).toNat = B.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : d < 2 ^ 64), Nat.mod_eq_of_lt h]

/-! ## The key -/

/-- The table of S-boxes at the static's address: readable, within the
address space, holding the S-boxes, and apart from every writable region. -/
structure TabAt (s : State) : Prop where
  rd : (⟨s.syms s1234Sym, 4096⟩ : Region) ∈ s.rd
  fit : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 64
  held : Held s.mem (s.syms s1234Sym) s1234
  sep : ∀ w ∈ s.wr, Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ w

/-- `TabAt` survives what keeps the regions and the statics and writes memory
apart from the table. -/
theorem TabAt.frame {s s' : State} (h : TabAt s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsy : s'.syms = s.syms) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ r) : TabAt s' := by
  refine ⟨?_, ?_, ?_, fun w hw => ?_⟩
  · rw [hrd, hsy]; exact h.rd
  · rw [hsy]; exact h.fit
  · rw [hsy]; exact held_frame h.held hf hd
  · rw [hwr] at hw; rw [hsy]; exact h.sep w hw

/-- The subkeys at `rdi` and the number of rounds in `rsi`, outside the
regions `rs`; the table, apart from them too. -/
def ModeKeyArgs (s : State) (rs : List Region) (kn : Spec.Cast5.Schedule × Nat) : Prop :=
  (∃ p : Addr, s.gpr .rdi = p ∧ kn.1 = Spec.Cast5.scheduleAt s.mem p ∧ (⟨p, 128⟩ : Region) ∈ s.rd ∧
    p.toNat + 128 ≤ 2 ^ 64 ∧ ∀ r ∈ rs, Region.Disjoint ⟨p, 128⟩ r) ∧
  s.gpr .rsi = BitVec.ofNat 64 kn.2 ∧ (kn.2 = 12 ∨ kn.2 = 16) ∧ TabAt s ∧
  ∀ r ∈ rs, Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ r

/-- The schedule's copy, with the scratch buffer at `B`. -/
abbrev schedAddr (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * schedSlot)

/-- The key `kn` is ready: its subkeys in the schedule's copy, its number of
rounds in `rsi`, and the table. -/
def Ready (s : State) (B : Addr) (kn : Spec.Cast5.Schedule × Nat) : Prop :=
  Spec.Cast5.scheduleAt s.mem (schedAddr B) = kn.1 ∧ s.gpr .rsi = BitVec.ofNat 64 kn.2 ∧
    (kn.2 = 12 ∨ kn.2 = 16) ∧ TabAt s

/-- The core's blocks are one word. -/
@[simp] theorem dirCore_bw (up : Bool) : (dirCore up).bw = 1 := rfl

theorem core_eq (up : Bool) (B : Addr) : coreRegion (dirCore up) B = ⟨B, 168⟩ := rfl
theorem blk_eq (up : Bool) (B : Addr) : blkRegion (dirCore up) B = ⟨B + BitVec.ofNat 64 16, 8⟩ := rfl
theorem total_eq (up : Bool) : (dirCore up).total = 29 := rfl

theorem sched_sub (B : Addr) : Region.Sub ⟨schedAddr B, 128⟩ ⟨B, 168⟩ := Offset.sub_base B (by decide)

theorem sched_buf (B : Addr) : Region.Disjoint ⟨schedAddr B, 128⟩ ⟨B + BitVec.ofNat 64 16, 8⟩ :=
  Offset.disjoint B (.inr (by decide)) (by decide) (by decide)

theorem rsi_not_mode (up : Bool) : Reg.rsi ∉ Modes.X86_64.modeRegs (dirCore up) := by
  simp only [Modes.X86_64.modeRegs, dirCore]; decide

theorem ready_frame {up : Bool} {s s' : State} {B : Addr} {kn : Spec.Cast5.Schedule × Nat} {rs : List Region}
    (h : Ready s B kn) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore up) B) r ∨ Region.Sub r (blkRegion (dirCore up) B))
    (hw : WrIn rs s s') (hg : ∀ r, r ∉ Modes.X86_64.modeRegs (dirCore up) → s'.gpr r = s.gpr r) :
    Ready s' B kn := by
  obtain ⟨hk, hsi, hn, hT⟩ := h
  refine ⟨?_, by rw [hg _ (rsi_not_mode up), hsi], hn, hT.frame hw.rd hw.wr hw.syms hf fun r hr => ?_⟩
  · rw [scheduleAt_frame hf fun r hr => ?_]
    · exact hk
    rcases hd r hr with h' | h'
    · rw [core_eq] at h'; exact h'.sub_left (sched_sub B)
    · rw [blk_eq] at h'; exact (sched_buf B).sub_right h'
  · obtain ⟨w, hw', hsub⟩ := hw.sub r hr
    exact (hT.sep w hw').sub_right hsub

theorem keyArgs_congr {s s' : State} {rs : List Region} {kn : Spec.Cast5.Schedule × Nat}
    (h : ModeKeyArgs s rs kn) (hr : ∀ r ∈ [Reg.rdi, .rsi], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsy : s'.syms = s.syms) (hf : Frame rs s.mem s'.mem) : ModeKeyArgs s' rs kn := by
  obtain ⟨⟨p, hp, hk, hin, hfit, hdis⟩, hsi, hn, hT, hdT⟩ := h
  refine ⟨⟨p, by rw [hr .rdi (by simp), hp], ?_, by rw [hrd]; exact hin, hfit, hdis⟩,
    by rw [hr .rsi (by simp), hsi], hn, hT.frame hrd hwr hsy hf hdT, by rw [hsy]; exact hdT⟩
  rw [hk]
  exact (scheduleAt_frame hf hdis).symm

theorem prepare_wp {up : Bool} {s : State} {B : Addr} {rs : List Region} {kn : Spec.Cast5.Schedule × Nat}
    (hB : s.gpr sb = B) (hs : ScrIn s B (dirCore up).total)
    (hR : (⟨B, 8 * (dirCore up).total⟩ : Region) ∈ rs) (hk : ModeKeyArgs s rs kn) :
    WP isa (dirCore up).prepare s fun s' => Ready s' B kn ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .r13 = s.gpr .r13 ∧
      Frame [coreRegion (dirCore up) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨⟨p, hp, hkk, hin, hfit, hdis⟩, hsi, hn, hT, hdT⟩ := hk
  have hfB := hs.fit
  rw [total_eq] at hfB
  obtain hsep : Region.Disjoint ⟨p, 128⟩ ⟨B, 168⟩ :=
    (hdis _ hR).sub_right (Region.sub_prefix (by rw [total_eq]; decide))
  obtain hcore : Frame [coreRegion (dirCore up) B] s.mem
      (over s.mem (schedAddr B) (8 * 16) fun i => s.mem (p + BitVec.ofNat 64 i)) := by
    rw [core_eq]
    exact (over_frame _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, sched_sub B⟩
  refine WP.mono_syms (copyN_wp (k := 16) (P := schedAddr B) (Q := p) ⟨by rw [hB], by rw [hp]; simp,
    by decide, by decide, fun w hw => ⟨_, hs.wr, by
      rw [addr_add, total_eq]; exact Offset.contains_base B (by simp only [schedSlot]; omega_arith)
        (by simp only [schedSlot]; omega_arith)⟩,
    fun w hw => ⟨_, List.mem_append_left _ hin, Offset.contains_base p (by omega_arith) (by omega_arith)⟩,
    (hsep.sub_right (sched_sub B)).symm, by omega_arith⟩) fun s' h hsy => ?_
  refine ⟨⟨?_, by rw [h.regs _ (by decide), hsi], hn, hT.frame h.rd h.wr hsy (by rw [h.mem]; exact hcore)
      fun r hr => ?_⟩, by rw [h.regs _ (by decide), hB], h.regs _ (by decide), h.regs _ (by decide),
    h.regs _ (by decide), by rw [h.mem]; exact hcore, h.rd, h.wr⟩
  · rw [h.mem, hkk]
    exact scheduleAt_congr_at fun i hi => over_at hi (by omega_arith)
  · simp only [List.mem_singleton] at hr; subst hr
    rw [core_eq]
    exact (hT.sep _ hs.wr).sub_right (Region.sub_prefix (by rw [total_eq]; decide))

/-! ## `crypt` -/

/-- The block's encryption (`up`) or decryption. -/
def dirBlock (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) (b : Spec.Cast5.Block) : Spec.Cast5.Block :=
  if up then Spec.Cast5.encryptBlock k n b else Spec.Cast5.decryptBlock k n b

theorem dirCipher_bytes (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) (m : Mem) (p : Addr) :
    dirCipher up k n (Spec.Aes.bytesAt m p 8) = (dirBlock up k n (Spec.Cast5.blockAt m p)).toList := by
  cases up <;> simp only [dirCipher, dirBlock, Spec.Cast5.cipher, Spec.Cast5.invCipher, ofFn_bytesAt,
    Bool.false_eq_true, ite_true, ite_false]

theorem block_ok (up : Bool) {u : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre u k n) :
    WP isa (if up then encryptBlock else decryptBlock) u
      (BPost u (dirBlock up k n (Spec.Cast5.blockAt u.mem (u.gpr .rdx)))) := by
  cases up
  · exact decryptBlock_ok h
  · exact encryptBlock_ok h

/-- What `modeSetup` does, with the scratch buffer at `B`. -/
theorem setup_run {s : State} {B : Addr} (hB : s.gpr sb = B) (hw : (⟨B, 8 * 29⟩ : Region) ∈ s.wr) :
    ∃ u, runBlock isa modeSetup s = some u ∧ u.gpr .r8 = B ∧ u.gpr .rdx = B + BitVec.ofNat 64 16 ∧
      u.gpr .rdi = schedAddr B ∧ (∀ x, x ≠ .r8 → x ≠ .rdx → x ≠ .rdi → u.gpr x = s.gpr x) ∧
      u.mem = (s.mem.writeW (B + BitVec.ofNat 64 24) (s.gpr .r12)).writeW (B + BitVec.ofNat 64 32)
        (s.gpr .r13) ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .r8 sb
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := stM_ok s₁ .r8 .r12 24
    ⟨_, by rw [wr₁]; exact hw, by rw [r₁, hB]; exact Offset.contains_base B (by omega_arith) (by omega_arith)⟩
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := stM_ok s₂ .r8 .r13 32
    ⟨_, by rw [wr₂, wr₁]; exact hw, by rw [g₂, r₁, hB]; exact Offset.contains_base B (by omega_arith) (by omega_arith)⟩
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movR_ok s₃ .rdx sb
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addImm_ok s₄ .rdx (BitVec.ofNat 32 (8 * bufSlot))
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := movR_ok s₅ .rdi sb
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇⟩ := addImm_ok s₆ .rdi (BitVec.ofNat 32 (8 * schedSlot))
  obtain sb₃ : s₃.gpr sb = B := by rw [g₃, g₂, o₁ _ (by decide), hB]
  refine ⟨s₇, ?_, ?_, ?_, ?_, fun x h1 h2 h3 => ?_, ?_, ?_, ?_⟩
  · show runBlock isa ([movR .r8 sb] ++ ([.store (Impl.Modes.X86_64.at_ .r8 24) .r12] ++
      ([.store (Impl.Modes.X86_64.at_ .r8 32) .r13] ++ ([movR .rdx sb] ++
      ([.alu .add .rdx (.imm (BitVec.ofNat 32 (8 * bufSlot)))] ++ ([movR .rdi sb] ++
      ([.alu .add .rdi (.imm (BitVec.ofNat 32 (8 * schedSlot)))] : List Instr))))))) s = some s₇
    rw [runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, runBlock_app,
      e₆, Option.bind_some, e₇]
  · rw [o₇ _ (by decide), o₆ _ (by decide), o₅ _ (by decide), o₄ _ (by decide), g₃, g₂, r₁, hB]
  · rw [o₇ _ (by decide), o₆ _ (by decide), r₅, r₄, sb₃, signExtend_small (by decide)]; rfl
  · rw [r₇, r₆, o₅ _ (by decide), o₄ _ (by decide), sb₃, signExtend_small (by decide)]
  · rw [o₇ _ h3, o₆ _ h3, o₅ _ h2, o₄ _ h2, g₃, g₂, o₁ _ h1]
  · rw [m₇, m₆, m₅, m₄, m₃, m₂, g₂, r₁, m₁, hB, o₁ _ (by decide), o₁ _ (by decide)]
  · rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]
  · rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]

/-- What `modeFinish` does. -/
theorem finish_run {v : State} {B : Addr} (h8 : v.gpr .r8 = B) (hw : (⟨B, 8 * 29⟩ : Region) ∈ v.wr) :
    ∃ s', runBlock isa modeFinish v = some s' ∧ s'.gpr .r12 = v.mem.readW (B + BitVec.ofNat 64 24) 64 ∧
      s'.gpr .r13 = v.mem.readW (B + BitVec.ofNat 64 32) 64 ∧ s'.gpr sb = B ∧
      (∀ x, x ≠ .r12 → x ≠ .r13 → x ≠ sb → s'.gpr x = v.gpr x) ∧ s'.mem = v.mem ∧ s'.rd = v.rd ∧
      s'.wr = v.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := ld_ok v .r12 .r8 24
    ⟨_, List.mem_append_right _ hw, by rw [h8]; exact Offset.contains_base B (by omega_arith) (by omega_arith)⟩
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := ld_ok s₁ .r13 .r8 32
    ⟨_, List.mem_append_right _ (by rw [wr₁]; exact hw), by
      rw [o₁ _ (by decide), h8]; exact Offset.contains_base B (by omega_arith) (by omega_arith)⟩
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ sb .r8
  refine ⟨s₃, ?_, ?_, ?_, ?_, fun x h1 h2 h3 => ?_, by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁],
    by rw [wr₃, wr₂, wr₁]⟩
  · show runBlock isa ([.mov .r12 (.mem (Impl.Modes.X86_64.at_ .r8 24))] ++
      ([.mov .r13 (.mem (Impl.Modes.X86_64.at_ .r8 32))] ++ ([movR sb .r8] : List Instr))) v = some s₃
    rw [runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]
  · rw [o₃ _ (by decide), o₂ _ (by decide), r₁, h8]
  · rw [o₃ _ (by decide), r₂, m₁, o₁ _ (by decide), h8]
  · rw [r₃, o₂ _ (by decide), o₁ _ (by decide), h8]
  · rw [o₃ _ h3, o₂ _ h2, o₁ _ h1]

/-- What `saveIv ++ modeSetup` does: `modeSetup`, with `xmm15`'s low half in `rcx`. -/
theorem setupIv_run {s : State} {B : Addr} (hB : s.gpr sb = B) (hw : (⟨B, 8 * 29⟩ : Region) ∈ s.wr) :
    ∃ u, runBlock isa (saveIv ++ modeSetup) s = some u ∧ u.gpr .r8 = B ∧ u.gpr .rdx = B + BitVec.ofNat 64 16 ∧
      u.gpr .rdi = schedAddr B ∧ (∀ x, x ≠ .r8 → x ≠ .rdx → x ≠ .rdi → x ≠ .rcx → u.gpr x = s.gpr x) ∧
      u.mem = (s.mem.writeW (B + BitVec.ofNat 64 24) (s.gpr .r12)).writeW (B + BitVec.ofNat 64 32)
        (s.gpr .r13) ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  obtain e₀ : runBlock isa saveIv s = some (s.setReg .rcx ((s.xmm .xmm15).extractLsb' 0 64)) := by
    simp only [saveIv, runBlock_cons, runStep_some, runBlock_nil, exec]
  obtain ⟨u, eu, u8, udx, udi, ug, um, urd, uwr⟩ := setup_run (s := s.setReg .rcx ((s.xmm .xmm15).extractLsb' 0 64))
    (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide)]; exact hB) hw
  refine ⟨u, by rw [runBlock_app, e₀, Option.bind_some, eu], u8, udx, udi, fun x h1 h2 h3 h4 => by
    rw [ug x h1 h2 h3, RegUpd.gpr_setReg_of_ne _ _ h4], ?_, urd, uwr⟩
  rw [um, RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide)]
  rfl

/-- What `modeFinish ++ restoreIv` does: `modeFinish`, then `xmm15` from `rcx`. -/
theorem finishIv_run {v : State} {B : Addr} (h8 : v.gpr .r8 = B) (hw : (⟨B, 8 * 29⟩ : Region) ∈ v.wr) :
    ∃ s', runBlock isa (modeFinish ++ restoreIv) v = some s' ∧
      s'.gpr .r12 = v.mem.readW (B + BitVec.ofNat 64 24) 64 ∧
      s'.gpr .r13 = v.mem.readW (B + BitVec.ofNat 64 32) 64 ∧ s'.gpr sb = B ∧
      (∀ x, x ≠ .r12 → x ≠ .r13 → x ≠ sb → x ≠ .rcx → s'.gpr x = v.gpr x) ∧ s'.mem = v.mem ∧ s'.rd = v.rd ∧
      s'.wr = v.wr := by
  obtain ⟨s₁, e₁, r12', r13', sb', g', m', rd', wr'⟩ := finish_run h8 hw
  obtain ⟨s₂, e₂, -, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .rcx (BitVec.ofNat 32 1)
  obtain e₃ : runBlock isa [.xop (.movq .xmm15 .rcx)] s₂ = some ((XOp.movq .xmm15 .rcx).exec s₂) := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec]
  have gx : ((XOp.movq .xmm15 .rcx).exec s₂).gpr = s₂.gpr := rfl
  refine ⟨(XOp.movq .xmm15 .rcx).exec s₂, ?_, ?_, ?_, ?_, fun x h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩
  · show runBlock isa (modeFinish ++ ([.alu .add .rcx (.imm (BitVec.ofNat 32 1))] ++
      [.xop (.movq .xmm15 .rcx)])) v = _
    rw [runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]
  · rw [gx, o₂ _ (by decide), r12']
  · rw [gx, o₂ _ (by decide), r13']
  · rw [gx, o₂ _ (by decide), sb']
  · rw [gx, o₂ _ h4, g' x h1 h2 h3]
  · show s₂.mem = v.mem; rw [m₂, m']
  · show s₂.rd = v.rd; rw [rd₂, rd']
  · show s₂.wr = v.wr; rw [wr₂, wr']

theorem crypt_wp {up : Bool} {s : State} {B : Addr} {kn : Spec.Cast5.Schedule × Nat} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore up).total) (hr : Ready s B kn) :
    WP isa (dirCore up).crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .r13 = s.gpr .r13 ∧ Ready s' B kn ∧
      Frame [coreRegion (dirCore up) B] s.mem s'.mem ∧
      (∀ j < (dirCore up).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore up) B j) (8 * (dirCore up).bw) =
        dirCipher up kn.1 kn.2 (Spec.Aes.bytesAt s.mem (blkAddr (dirCore up) B j) (8 * (dirCore up).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨k, n⟩ := kn
  obtain ⟨hk, hsi, hn, hT⟩ := hr
  have hw := hs.wr
  have hfB := hs.fit
  rw [total_eq] at hw hfB
  obtain dT := hT.sep _ hw
  -- The regions of the scratch buffer the core uses.
  obtain sWs : Region.Sub ⟨B, 16⟩ ⟨B, 8 * 29⟩ := Region.sub_prefix (by decide)
  obtain sBuf : Region.Sub ⟨B + BitVec.ofNat 64 16, 8⟩ ⟨B, 8 * 29⟩ := Offset.sub_base B (by decide)
  obtain sKeep : Region.Sub ⟨B + BitVec.ofNat 64 24, 16⟩ ⟨B, 8 * 29⟩ := Offset.sub_base B (by decide)
  obtain dSchedWs : Region.Disjoint ⟨schedAddr B, 128⟩ ⟨B, 16⟩ := by
    have := Offset.disjoint B (d := 40) (n := 128) (e := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  obtain dSchedKeep : Region.Disjoint ⟨schedAddr B, 128⟩ ⟨B + BitVec.ofNat 64 24, 16⟩ :=
    Offset.disjoint B (.inr (by decide)) (by decide) (by decide)
  obtain dKeepBuf : Region.Disjoint ⟨B + BitVec.ofNat 64 24, 16⟩ ⟨B + BitVec.ofNat 64 16, 8⟩ :=
    Offset.disjoint B (.inr (by decide)) (by decide) (by decide)
  obtain dKeepWs : Region.Disjoint ⟨B + BitVec.ofNat 64 24, 16⟩ ⟨B, 16⟩ := by
    have := Offset.disjoint B (d := 24) (n := 16) (e := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  have dBufKeep : Region.Disjoint ⟨B + BitVec.ofNat 64 16, 8⟩ ⟨B + BitVec.ofNat 64 24, 16⟩ := dKeepBuf.symm
  obtain inW : ∀ {t l}, t + l ≤ 8 * 29 → InRegions s.wr (B + BitVec.ofNat 64 t) l := fun ht =>
    ⟨_, hw, Offset.contains_base B ht (by omega_arith)⟩
  -- The setup.
  obtain ⟨u, eu, u8, udx, udi, ug, um, urd, uwr⟩ := setupIv_run hB hw
  obtain usy : u.syms = s.syms := runBlock_syms eu
  obtain fu : Frame [⟨B + BitVec.ofNat 64 24, 16⟩] s.mem u.mem := by
    rw [um]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains B (d := 24) (n := 8) (e := 24) (k := 16)
      (by decide) (by decide) (by decide))).writeW List.mem_cons_self _
      (Offset.contains B (d := 32) (n := 8) (e := 24) (k := 16) (by decide) (by decide) (by decide))
  obtain uk : Spec.Cast5.scheduleAt u.mem (schedAddr B) = k := by
    rw [scheduleAt_frame fu fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dSchedKeep]
    exact hk
  obtain uT : TabAt u := hT.frame urd uwr usy fu fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dT.sub_right sKeep
  obtain hpre : BPre u k n := by
    refine ⟨⟨?_, fun j hj => ?_, ?_, ?_, uT.held, ?_, ?_, ?_, uT.fit⟩, hn, by rw [ug _ (by decide) (by decide)
      (by decide) (by decide), hsi], ?_⟩
    · rw [udi, urd, uwr]
      exact ⟨_, List.mem_append_right _ hw, Offset.contains_base B (by decide) (by decide)⟩
    · rw [udi, ← scheduleAt_getD _ _ hj, uk]
    · rw [u8, uwr, show B = B + BitVec.ofNat 64 0 by rw [BitVec.add_zero]]; exact inW (by decide)
    · exact ⟨_, List.mem_append_left _ uT.rd, Region.contains_self _ _⟩
    · rw [udi, u8]; exact dSchedWs
    · rw [usy, u8]; exact dT.sub_right sWs
    · rw [udi, toNat_add (by simp only [schedSlot]; omega_arith)]; simp only [schedSlot]; omega_arith
    · rw [udx, uwr]; exact inW (by decide)
  show WP isa (cryptCode up) s _
  refine WP.seq (WP.of_runBlock ⟨u, eu, ?_⟩)
  refine WP.seq (WP.mono (block_ok up hpre) fun v ⟨vout, vf, _, _, _, vrd, vwr, vsy, vg⟩ => ?_)
  rw [u8, udx] at vf
  rw [udx] at vout
  obtain v8 : v.gpr .r8 = B := by rw [vg _ (by decide) (by decide) (by decide) (by decide), u8]
  obtain ⟨s', es, r12', r13', sb', g', m', rd', wr'⟩ := finishIv_run v8 (by rw [vwr, uwr]; exact hw)
  refine WP.of_runBlock ⟨s', es, ?_⟩
  obtain sy' : s'.syms = s.syms := by rw [runBlock_syms es, vsy, usy]
  obtain hvu : ∀ x, x ∉ roundRegs → x ≠ .r13 → x ≠ .rdx → x ≠ .rcx → x ≠ .r8 → x ≠ .rdi → x ≠ .r12 → x ≠ sb →
      s'.gpr x = s.gpr x := fun x h1 h2 h3 h4 h5 h6 h7 h8 => by
    rw [g' x h7 h2 h8 h4, vg x h1 h2 h3 h4, ug x h5 h3 h6 h4]
  -- The block and the working space, apart from the kept registers' slots.
  obtain keepV : ∀ d, 24 ≤ d → d + 8 ≤ 40 → v.mem.readW (B + BitVec.ofNat 64 d) 64 =
      u.mem.readW (B + BitVec.ofNat 64 d) 64 := fun d h1 h2 => by
    obtain sd : Region.Sub ⟨B + BitVec.ofNat 64 d, 8⟩ ⟨B + BitVec.ofNat 64 24, 16⟩ := Offset.sub B h1 (by omega_arith)
    refine vf.readW (r := ⟨B + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dKeepBuf.sub_left sd
    · exact dKeepWs.sub_left sd
  obtain fv : Frame [⟨B + BitVec.ofNat 64 16, 8⟩, ⟨B, 16⟩] u.mem s'.mem := by rw [m']; exact vf
  obtain fCore : Frame [coreRegion (dirCore up) B] s.mem s'.mem := by
    rw [core_eq]
    refine (fu.sub fun r hr => ?_).trans (fv.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base B (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_singleton_self _, Offset.sub_base B (by decide)⟩
      · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  obtain vrd' : s'.rd = s.rd := by rw [rd', vrd, urd]
  obtain vwr' : s'.wr = s.wr := by rw [wr', vwr, uwr]
  refine ⟨sb', hvu _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), ?_, ?_, ⟨?_, ?_, hn, hT.frame vrd' vwr' sy' fCore fun r hr => ?_⟩, fCore, fun j hj => ?_,
    vrd', vwr'⟩
  · rw [r12', keepV 24 (by decide) (by decide), um,
      Mem.readW_writeW_sep (Offset.sep B (.inl (by decide)) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]
  · rw [r13', keepV 32 (by decide) (by decide), um, Mem.readW_writeW_self64]
  · rw [m', scheduleAt_frame vf fun r hr => ?_]
    · exact uk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sched_buf B
    · exact dSchedWs
  · rw [g' _ (by decide) (by decide) (by decide) (by decide), vg _ (by decide) (by decide) (by decide) (by decide),
      ug _ (by decide) (by decide) (by decide) (by decide), hsi]
  · simp only [List.mem_singleton] at hr; subst hr
    rw [core_eq]; exact dT.sub_right (Region.sub_prefix (by decide))
  · have hj0 : j = 0 := by simp only [dirCore] at hj; omega_arith
    subst hj0
    have ea : blkAddr (dirCore up) B 0 = B + BitVec.ofNat 64 16 := rfl
    obtain hbu : Spec.Cast5.blockAt u.mem (B + BitVec.ofNat 64 16) = Spec.Cast5.blockAt s.mem (B + BitVec.ofNat 64 16) :=
      blockAt_frame fu _ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dBufKeep
    rw [dirCore_bw, ea, Nat.mul_one, dirCipher_bytes, bytesAt_eq, m', vout, hbu]

/-- CAST5's core, encrypting (`up`) or decrypting, meets what the modes need. -/
def dirCoreSpec (up : Bool) : BlockSpec (dirCore up) where
  Key := Spec.Cast5.Schedule × Nat
  cipher kn := dirCipher up kn.1 kn.2
  KeyArgs := ModeKeyArgs
  Ready := Ready
  cipher_len kn b := by rw [dirCore_bw]; exact dirCipher_length up kn.1 kn.2 b
  layout := ⟨by simp only [dirCore]; decide, by simp only [dirCore]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore, bufSlot, schedSlot]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore, schedSlot]; decide⟩
  keyRegs_ok := by simp only [dirCore]; decide
  regs_ok := by simp only [dirCore, Modes.X86_64.regsOk]; decide
  keyArgs_congr h hr hrd hwr hsy hf := keyArgs_congr h hr hrd hwr hsy hf
  ready_frame h hf hd hw hg := ready_frame h hf hd hw hg
  prepare_wp := prepare_wp
  crypt_wp := crypt_wp

end VG.Proof.Cast5.X86_64.Mode

end

end

/-!
# CAST5-OFB and -CFB64 on x86-64 meet their contracts

`ofb_wp`, `cfbEncrypt_wp`, `cfbDecrypt_wp`: the modes' OFB and CFB
(`Proof.Modes.X86_64.fb_wp`) over CAST5's core (`Mode.dirCoreSpec true`),
with the specification's results (`Proof.Modes.ofb_of`, …), the working
space at `r9`. The core keeps `xmm15`, where the modes keep the IV's address,
its upper half zero (`crypt_keepsIv`): `crypt` puts it back from `rcx`, which
the block code counts down by one (`block_rcx`). The table of
S-boxes is readable where the static `VG_CAST5_S1234` puts it and holds the
S-boxes. `ofb_verified`, …: each is correct and constant time, by the taint
analysis: the pointers, `rounds`, `n`, the stack pointer and the table's
address are public, and so is everything the code computes from them; the
subkeys, the IV and the data are secret. `ofb_framed`, … run them with their
working space on the stack: 240 bytes, the 29 words of the scratch buffer and
8 more, which the scrub after them zeroes (`Proof.Cast5.X86_64.Scrub`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.Impl.Cast5.X86_64
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)
open VG.Proof.Cast5.X86_64.Mode (dirCoreSpec TabAt dirCore_bw)

/-- The `n` blocks at `p`, as the modes read them. -/
theorem blocksOf_eq (m : Mem) (p : Addr) (n : Nat) :
    VG.Proof.Modes.blocksOf 8 m p n = Spec.Cast5.cbcBlocksAt m p n :=
  (Proof.Cast5.cbcBlocksAt_eq m p n).symm

/-- The data, in blocks. -/
abbrev dataOf (s : State) (m : Mem) : List (List Byte) :=
  Spec.Cast5.cbcBlocksAt m (s.gpr .rcx) (s.gpr .r8).toNat
/-- The chaining value. -/
abbrev ivOf (s : State) : List Byte := Spec.Aes.bytesAt s.mem (s.gpr .rdx) 8
/-- The subkeys. -/
abbrev keyOf (s : State) : Spec.Cast5.Schedule := Spec.Cast5.scheduleAt s.mem (s.gpr .rdi)

/-- The public arguments and the table's address. -/
def cbcPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.syms s1234Sym = s₂.syms s1234Sym

/-- `n` blocks. -/
abbrev blkLen (s : State) : Nat := (s.gpr .r8).toNat * 8

theorem blkLen_congr : ∀ s t : State, s.gpr .r8 = t.gpr .r8 → blkLen s = blkLen t := fun _ _ h => by
  simp only [blkLen, h]

/-- The facts of the feedback modes' precondition on this target, with the
data `len` bytes long and the working space at `r9`. -/
structure FPre (len : State → Nat) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rdi, 128⟩, ⟨s.syms s1234Sym, 4096⟩]
  wr : s.wr = [⟨s.gpr .rdx, 8⟩, ⟨s.gpr .rcx, len s⟩, ⟨s.gpr .r9, 232⟩]
  held : ∀ i < 512, s.mem.readW (s.syms s1234Sym + BitVec.ofNat 64 (8 * i)) 64 = s1234.getD i 0
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 64
  dTV : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .rdx, 8⟩
  dTD : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .rcx, len s⟩
  dTS : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .r9, 232⟩
  dKV : Region.Disjoint ⟨s.gpr .rdi, 128⟩ ⟨s.gpr .rdx, 8⟩
  dKD : Region.Disjoint ⟨s.gpr .rdi, 128⟩ ⟨s.gpr .rcx, len s⟩
  dKS : Region.Disjoint ⟨s.gpr .rdi, 128⟩ ⟨s.gpr .r9, 232⟩
  dVD : Region.Disjoint ⟨s.gpr .rdx, 8⟩ ⟨s.gpr .rcx, len s⟩
  dVS : Region.Disjoint ⟨s.gpr .rdx, 8⟩ ⟨s.gpr .r9, 232⟩
  dDS : Region.Disjoint ⟨s.gpr .rcx, len s⟩ ⟨s.gpr .r9, 232⟩
  dRV : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 8⟩
  dRD : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, len s⟩
  dRS : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .r9, 232⟩
  fK : (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64
  fD : (s.gpr .rcx).toNat + len s ≤ 2 ^ 64
  fS : (s.gpr .r9).toNat + 232 ≤ 2 ^ 64
  rounds : (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 16

/-- CAST5 encryption under the key of `s`. -/
abbrev ciphOf (s : State) : Spec.Cbc.Cipher := Spec.Cast5.cipher (keyOf s) (s.gpr .rsi).toNat

def ofbX : Contract isa where
  pre := FPre blkLen
  post s s' := dataOf s s'.mem = Spec.Ofb.crypt (ciphOf s) (ivOf s) (dataOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 8 = Spec.Ofb.next (ciphOf s) (ivOf s) (s.gpr .r8).toNat
  pub := cbcPub

def cfbEncX : Contract isa where
  pre := FPre blkLen
  post s s' := dataOf s s'.mem = Spec.Cfb.encrypt (ciphOf s) (ivOf s) (dataOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 8 = Spec.Cbc.next (ivOf s) (Spec.Cfb.encrypt (ciphOf s) (ivOf s) (dataOf s s.mem))
  pub := cbcPub

def cfbDecX : Contract isa where
  pre := FPre blkLen
  post s s' := dataOf s s'.mem = Spec.Cfb.decrypt (ciphOf s) (ivOf s) (dataOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 8 = Spec.Cbc.next (ivOf s) (dataOf s s.mem)
  pub := cbcPub

/-- The table, as the core needs it. -/
theorem FPre.tabAt {len : State → Nat} {s : State} (h : FPre len s) : TabAt s :=
  ⟨by rw [h.rd]; simp, h.fitT, fun i hi => h.held i (by rw [s1234_length] at hi; exact hi), fun w hw => by
    rw [h.wr] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact h.dTV
    · exact h.dTD
    · exact h.dTS⟩

/-! ## `xmm15` -/

theorem execBlock_app_inv {a b : List Instr} {s s' : State} {t : List Leak}
    (h : execBlock isa (a ++ b) s = some (s', t)) :
    ∃ u ta tb, execBlock isa a s = some (u, ta) ∧ execBlock isa b u = some (s', tb) := by
  rw [execBlock_append] at h
  obtain ⟨⟨u, ta⟩, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨v, tb⟩, h₃, h₄⟩ := Option.map_eq_some_iff.mp h₂
  simp only [Prod.mk.injEq] at h₄
  exact ⟨u, ta, tb, h₁, h₄.1 ▸ h₃⟩

theorem noClobber {c : Prog isa} {r : Reg} (h : c.allInstrs (fun i => !Taint.clobbers i r) = true) :
    ∀ i ∈ instrs c, Taint.clobbers i r = false := by
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  intro i hi
  simpa using h i hi

/-- `store` counts `rcx` down by one. -/
theorem store_rcx {s s' : State} {t : List Leak} (h : execBlock isa store s = some (s', t)) :
    s'.gpr .rcx = s.gpr .rcx - 1 := by
  obtain ⟨u, _, _, h₁, h₂⟩ := execBlock_app_inv (a := [.bswap32 .rbp, .store32 (at_ .rdx 0) .rbp, .bswap32 .rbx,
    .store32 (at_ .rdx 4) .rbx, .alu .add .rdx (imm 8)]) (b := [.alu .sub .rcx (imm 1)]) h
  rw [← execBlock_gpr (r := .rcx) (by decide) h₁]
  simp only [execBlock, isa, exec, execAlu, readSrc, imm, Option.bind_some, Option.map_some, Option.some.injEq,
    Prod.mk.injEq] at h₂
  rw [← h₂.1, RegUpd.gpr_setReg_self]
  rfl

/-- The block code counts `rcx` down by one. -/
theorem block_rcx (up : Bool) {s s' : State} {t : List Leak}
    (h : Exec isa (if up then encryptBlock else decryptBlock) s t s') : s'.gpr .rcx = s.gpr .rcx - 1 := by
  cases up
  · change Exec isa decryptBlock s t s' at h
    unfold decryptBlock at h
    cases h with
    | seq e₁ e₂ => cases e₂ with
      | seq e₃ e₄ => cases e₄ with
        | seq e₅ e₆ => cases e₆ with
          | block b =>
            rw [store_rcx b, Exec.gpr (noClobber (by decide +kernel)) e₅, Exec.gpr (noClobber (by decide +kernel)) e₃,
              Exec.gpr (noClobber (by decide +kernel)) e₁]
  · change Exec isa encryptBlock s t s' at h
    unfold encryptBlock at h
    cases h with
    | seq e₁ e₂ => cases e₂ with
      | seq e₃ e₄ => cases e₄ with
        | seq e₅ e₆ => cases e₆ with
          | seq e₇ e₈ => cases e₈ with
            | block b =>
              rw [store_rcx b, Exec.gpr (noClobber (by decide +kernel)) e₇,
                Exec.gpr (noClobber (by decide +kernel)) e₅, Exec.gpr (noClobber (by decide +kernel)) e₃,
                Exec.gpr (noClobber (by decide +kernel)) e₁]

/-- `movq xmm, r64` of a register's low half puts back one whose upper half is zero. -/
theorem movq_lo {v : BitVec 128} (h : v.extractLsb' 64 64 = 0) : (0 : BitVec 64) ++ v.extractLsb' 0 64 = v := by
  rw [← h]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h64 : i < 64
  · simp [h64, hi]
  · simp only [h64, decide_false, Bool.false_and, ite_false]
    simp only [Bool.true_and, show i - 64 < 64 by omega_using [hi], decide_true]
    congr 1; omega_using [h64]

/-- `crypt` keeps `xmm15`, its upper half zero, which it puts back from `rcx`. -/
theorem crypt_keepsIv : Modes.X86_64.KeepsIv (dirCore true).crypt := by
  intro s t s' h hz
  change Exec isa (cryptCode true) s t s' at h
  cases h with
  | seq e₁ e₂ => cases e₁ with
    | block b₁ => cases e₂ with
      | seq e₃ e₄ => cases e₄ with
        | block b₄ =>
          obtain ⟨u, _, _, h₁, h₂⟩ := execBlock_app_inv b₁
          obtain ⟨w, _, _, h₃, h₄⟩ := execBlock_app_inv b₄
          simp only [saveIv, execBlock, isa, exec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h₁
          have k₁ := execBlock_gpr (r := .rcx) (by decide) h₂
          have k₃ := execBlock_gpr (r := .rcx) (by decide) h₃
          have k₂ := block_rcx true e₃
          simp only [restoreIv, execBlock, isa, exec, execAlu, readSrc, imm, Option.bind_some, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at h₄
          have hw : w.gpr .rcx + BitVec.signExtend 64 (1#32) = (s.xmm .xmm15).extractLsb' 0 64 := by
            rw [k₃, k₂, k₁, ← h₁.1, RegUpd.gpr_setReg_self, show BitVec.signExtend 64 (1#32) = (1 : BitVec 64) from rfl,
              BitVec.sub_add_cancel]
          rw [← h₄.1]
          simp only [XOp.exec, RegUpd.gpr_setReg_self]
          rw [hw]
          exact movq_lo hz

/-- `crypt` and `prepare` keep `xmm15`. -/
theorem keepsIv_core : Modes.X86_64.KeepsIv (dirCore true).prepare ∧ Modes.X86_64.KeepsIv (dirCore true).crypt :=
  ⟨Modes.X86_64.keepsIv_of_ivSafe (by decide), crypt_keepsIv⟩

/-- What the modes' OFB and CFB give, for a mode `mo`: the data and the IV
as `fbOut` and `fbIn`, keeping the callee-saved registers. -/
theorem fb_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : FPre blkLen s₀) :
    WP isa ((dirCore true).fb mo modeRegs) s₀ fun s' => gprPreserved s₀ s' ∧
      Modes.blocksOf 8 s'.mem (s₀.gpr .rcx) (s₀.gpr .r8).toNat =
        (List.range (s₀.gpr .r8).toNat).map (Modes.fbOut mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rcx) (ivOf s₀)) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .rdx) 8 =
        Modes.fbIn mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rcx) (ivOf s₀) (s₀.gpr .r8).toNat := by
  have hwS : (⟨s₀.gpr .r9, 8 * 29⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have e : 8 * (dirCore true).bw * (s₀.gpr .r8).toNat = (s₀.gpr .r8).toNat * 8 := by
    rw [dirCore_bw, Nat.mul_one, Nat.mul_comm]
  refine WP.mono (Proof.Modes.X86_64.fb_wp (dirCoreSpec true) mo (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r9) (P := s₀.gpr .rdx) (D := s₀.gpr .rcx) (n := (s₀.gpr .r8).toNat)
    (k := (keyOf s₀, (s₀.gpr .rsi).toNat)) rfl rfl rfl rfl ⟨hwS, hp.fS⟩
    (by rw [hp.wr]; simp) (by rw [e, hp.wr]; simp) hp.dVS (by rw [e]; exact hp.dDS) (by rw [e]; exact hp.dVD)
    (by rw [e]; exact hp.fD)
    ⟨⟨s₀.gpr .rdi, rfl, rfl, by rw [hp.rd]; simp, hp.fK, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.dKS⟩,
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hp.rounds, hp.tabAt, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.dTS⟩ keepsIv_core)
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ => ⟨⟨hcs, ?_⟩, by rw [dirCore_bw] at hdata hiv; exact ⟨hdata, hiv⟩⟩
  rw [VG.Proof.Modes.X86_64.stkList_eq_nil rfl, List.append_nil] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.dRS
  · rw [e]; exact hp.dRD
  · exact hp.dRV

theorem ofb_wp {s₀ : State} (hp : ofbX.pre s₀) :
    WP isa ofb s₀ fun s' => gprPreserved s₀ s' ∧ ofbX.post s₀ s' :=
  WP.mono (fb_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofb_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rcx) (ivOf s₀) (s₀.gpr .r8).toNat
    refine ⟨hg, ?_, by rw [hv, h2]⟩
    change Spec.Cast5.cbcBlocksAt _ _ _ = Spec.Ofb.crypt _ _ (Spec.Cast5.cbcBlocksAt _ _ _)
    rw [← blocksOf_eq, ← blocksOf_eq, hd, h1]

theorem cfbEncrypt_wp {s₀ : State} (hp : cfbEncX.pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => gprPreserved s₀ s' ∧ cfbEncX.post s₀ s' :=
  WP.mono (fb_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEnc_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rcx) (ivOf s₀) (s₀.gpr .r8).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.Cast5.cbcBlocksAt _ _ _ = Spec.Cfb.encrypt _ _ (Spec.Cast5.cbcBlocksAt _ _ _)
      rw [← blocksOf_eq, ← blocksOf_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Cfb.encrypt _ _ (Spec.Cast5.cbcBlocksAt _ _ _))
      rw [hv, h2, blocksOf_eq]

theorem cfbDecrypt_wp {s₀ : State} (hp : cfbDecX.pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => gprPreserved s₀ s' ∧ cfbDecX.post s₀ s' :=
  WP.mono (fb_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDec_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rcx) (ivOf s₀) (s₀.gpr .r8).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.Cast5.cbcBlocksAt _ _ _ = Spec.Cfb.decrypt _ _ (Spec.Cast5.cbcBlocksAt _ _ _)
      rw [← blocksOf_eq, ← blocksOf_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Cast5.cbcBlocksAt _ _ _)
      rw [hv, h2, blocksOf_eq]

/-! ## Constant time -/

def fbTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], flags := false,
    lens := [8, 0, 8 * 29], bases := [(.r9, 2, 0)] }

theorem fbTaint_wf {len : State → Nat} (s : State) (hs : FPre len s) : Taint.Wf fbTaint s := by
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hs.wr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 8 ≤ 8; omega_using []) (List.Forall₂.cons
        (by change 0 ≤ len s; omega_using [])
        (List.Forall₂.cons (by change 8 * 29 ≤ 232; omega_using []) List.Forall₂.nil))
    · refine List.Pairwise.cons (fun r hr => ?_) (List.Pairwise.cons (fun r hr => ?_)
        (List.Pairwise.cons (by simp) List.Pairwise.nil))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hs.dVD
        · exact hs.dVS
      · obtain rfl := List.mem_singleton.mp hr; exact hs.dDS
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · change 8 ≤ 2 ^ 64; omega_using []
      · change len s ≤ 2 ^ 64
        have := hs.fD; omega_using [this]
      · change 232 ≤ 2 ^ 64; omega_using []
  · intro p hp
    simp only [fbTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hs.wr]
    change s.gpr .r9 = s.gpr .r9 + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem fbTaint_agree {len : State → Nat} (hlen : ∀ s t, s.gpr .r8 = t.gpr .r8 → len s = len t) (s t : State)
    (hs : FPre len s) (ht : FPre len t) (hp : cbcPub s t) :
    X86_64.Taint.AgreeS [s1234Sym] fbTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := hp
  refine ⟨⟨?_, ?_, fbTaint_wf s hs, fbTaint_wf t ht, ?_, ?_, ?_, X86_64.Taint.noXr⟩, fun n hn => ?_⟩
  · constructor
    · intro r hr
      simp only [fbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [p1, p2, p3, p4, p5, p6, p7]
    · intro h
      change false = true at h
      contradiction
  · intro _
    rw [hs.wr, ht.wr, p3, p4, p6, hlen s t p5]
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro r hr
    simp only [fbTaint, RegSet.not_mem_empty] at hr
  · simp only [List.mem_singleton] at hn
    subst hn
    exact p8

theorem ofb_ct : ConstantTime isa ofbX.pre ofbX.pub ofb :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)

theorem cfbEncrypt_ct : ConstantTime isa cfbEncX.pre cfbEncX.pub cfbEncrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)

theorem cfbDecrypt_ct : ConstantTime isa cfbDecX.pre cfbDecX.pub cfbDecrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)

/-! ## The contracts -/

/-- OFB's or CFB's contract with the working space as a sixth argument, under
the calling convention with the table (`cfbSig` is `ofbSig`). -/
abbrev fbK (post : Spec.Cast5.ofbSig.Post X86_64.abi.ptrBits) : Contract isa :=
  Proof.Cast5.modeScratchContract (X86_64.abi.withConsts ecbConsts) Spec.Cast5.ofbSig 29
    (Spec.Cast5.ofbPre X86_64.abi.ptrBits) post

/-- A state satisfying the precondition: one block, 16 rounds. -/
def fbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 1 | .r9 => 0x4000
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩, ⟨0x4000, 232⟩]
  syms _ := 0x100000

theorem fb_implies {postX : State → State → Prop} {post : Spec.Cast5.ofbSig.Post X86_64.abi.ptrBits}
    (hpost : ∀ s s', postX s s' → (fbK post).post s s') :
    ({ pre := FPre blkLen, post := postX, pub := cbcPub } : Contract isa).Implies (fbK post) where
  pre s h := by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
      Spec.Cast5.ofbPre, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow, s1234_length, Curry.withScratch] at h
    obtain ⟨hdr, hheld, hfit, hdw, -, -, htk, hw, dKV, dKD, dKS, dVD, dVS, dDS, -, spV, spD, spS, fK, -, fD, fS,
      hr⟩ := h
    refine ⟨?_, hw, hheld, hfit, hdw _ (by rw [hw]; exact List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), dKV, dKD, dKS,
      dVD, dVS, dDS, spV, spD, spS, fK, fD, fS, hr⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htk, hdr]
    rfl
  post s s' _ hq := hpost s s' hq
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig, X86_64.abi,
      X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch] at h
    obtain ⟨hsp, hsy, h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, hsp, hsy⟩
  sat := ⟨fbSat, by
    generalize e : fbSat = s
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
      Spec.Cast5.ofbPre, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow, s1234_length, Curry.withScratch]
    subst s
    refine ⟨rfl, ecbSatMem_held, by decide, ?_, ?_⟩
    · intro r hr
      change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 8⟩, ⟨0x4000, 232⟩] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
    · repeat' apply And.intro
      all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)⟩

theorem ofb_verified : Verified X86_64.target ofb (fbK (Proof.Cast5.ofbPost X86_64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := ofb_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := ofb) (by lit_decide) he hg, hpost⟩)
    ofb_ct (fb_implies fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
        Proof.Cast5.ofbPost, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

theorem cfbEncrypt_verified :
    Verified X86_64.target cfbEncrypt
      (Proof.Cast5.modeScratchContract (X86_64.abi.withConsts ecbConsts) Spec.Cast5.cfbSig 29
        (Spec.Cast5.cfbPre X86_64.abi.ptrBits) (Proof.Cast5.cfbEncPost X86_64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbEncrypt_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbEncrypt) (by lit_decide) he hg, hpost⟩)
    cfbEncrypt_ct (fb_implies (post := Proof.Cast5.cfbEncPost X86_64.abi.ptrBits) fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
        Proof.Cast5.cfbEncPost, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

theorem cfbDecrypt_verified :
    Verified X86_64.target cfbDecrypt
      (Proof.Cast5.modeScratchContract (X86_64.abi.withConsts ecbConsts) Spec.Cast5.cfbSig 29
        (Spec.Cast5.cfbPre X86_64.abi.ptrBits) (Proof.Cast5.cfbDecPost X86_64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbDecrypt_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbDecrypt) (by lit_decide) he hg, hpost⟩)
    cfbDecrypt_ct (fb_implies (post := Proof.Cast5.cfbDecPost X86_64.abi.ptrBits) fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
        Proof.Cast5.cfbDecPost, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

/-! ## The functions with their working space on the stack -/

/-- A state satisfying the functions' precondition, with 240 bytes of stack. -/
def fbFrameSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 1 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩]
  syms _ := 0x100000

theorem fbFrame_sat (post : Spec.Cast5.ofbSig.Post X86_64.abi.ptrBits) :
    ∃ s, (Spec.Cast5.ofbSig.contract (X86_64.abi.withConsts ecbConsts) (Spec.Cast5.ofbPre X86_64.abi.ptrBits) post
      true (0 + 240)).pre s := by
  refine ⟨fbFrameSat, ?_⟩
  generalize e : fbFrameSat = s
  sig_pre [Spec.Cast5.ofbSig, Spec.Cast5.ofbPre, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst s
  refine ⟨by decide, rfl, ecbSatMem_held, by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 8⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)

/-- OFB with its working space on the stack. -/
theorem ofb_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 ofb)
      (Proof.Cast5.ofbRoundsContract (X86_64.abi.withConsts ecbConsts) 240) :=
  X86_64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.ofbSig)
    (nm := "scratch") (e := .u64) (n := 29) (pre := Spec.Cast5.ofbPre X86_64.abi.ptrBits)
    (post := Proof.Cast5.ofbPost X86_64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 240)
    ofb_verified (by decide) (by decide) (by decide) (Code.all_of_spTest (by lit_decide))
    (by lit_decide) (by decide) (Proof.Cast5.ofbPostOut_local _) (fbFrame_sat _)

/-- CFB64 encryption with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 cfbEncrypt)
      (Proof.Cast5.cfbEncryptRoundsContract (X86_64.abi.withConsts ecbConsts) 240) :=
  X86_64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbSig)
    (nm := "scratch") (e := .u64) (n := 29) (pre := Spec.Cast5.cfbPre X86_64.abi.ptrBits)
    (post := Proof.Cast5.cfbEncPost X86_64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 240)
    cfbEncrypt_verified (by decide) (by decide) (by decide) (Code.all_of_spTest (by lit_decide))
    (by lit_decide) (by decide) (Proof.Cast5.cfbEncPostOut_local _) (fbFrame_sat _)

/-- CFB64 decryption with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 cfbDecrypt)
      (Proof.Cast5.cfbDecryptRoundsContract (X86_64.abi.withConsts ecbConsts) 240) :=
  X86_64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbSig)
    (nm := "scratch") (e := .u64) (n := 29) (pre := Spec.Cast5.cfbPre X86_64.abi.ptrBits)
    (post := Proof.Cast5.cfbDecPost X86_64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 240)
    cfbDecrypt_verified (by decide) (by decide) (by decide) (Code.all_of_spTest (by lit_decide))
    (by lit_decide) (by decide) (Proof.Cast5.cfbDecPostOut_local _) (fbFrame_sat _)

end VG.Proof.Cast5.X86_64
