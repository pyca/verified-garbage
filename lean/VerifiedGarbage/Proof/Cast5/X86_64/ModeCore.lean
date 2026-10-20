module

public import VerifiedGarbage.Proof.Cast5.X86_64.Ecb
public import VerifiedGarbage.Proof.Cast5.ModeCipher
public import VerifiedGarbage.Proof.Modes.X86_64.Core
public import VerifiedGarbage.Proof.Modes.X86_64.Words
public import VerifiedGarbage.Impl.Cast5.X86_64.Modes
public import VerifiedGarbage.Proof.Cast5.X86_64.Block
import Mathlib.Data.List.Induction
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Modes.X86_64.Setup
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesCbc.Spec
public import VerifiedGarbage.Proof.Cast5.Memory
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.Modes.Addr
public import VerifiedGarbage.Proof.Modes.X86_64.Counter
public import VerifiedGarbage.Proof.Modes.X86_64.Setup
public import VerifiedGarbage.Proof.Modes.X86_64.Steps
public import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Modes.X86_64.Counter
import VerifiedGarbage.Spec.Cast5.Contract

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
  rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]

theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 128⟩ r) : Spec.Cast5.scheduleAt m' p = Spec.Cast5.scheduleAt m p :=
  scheduleAt_congr_at fun _ hi => hf.bytes (R := ⟨p, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) hi

theorem held_frame {rs : List Region} {m m' : Mem} {T : Addr} (h : Held m T s1234) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨T, 4096⟩ r) : Held m' T s1234 := by
  intro i hi
  rw [s1234_length] at hi
  rw [← h i (by rw [s1234_length]; exact hi)]
  exact hf.readW (r := ⟨T, 4096⟩) (Offset.contains_base _ (by omega) (by omega)) hd (by decide)

theorem toNat_add {B : Addr} {d : Nat} (h : B.toNat + d < 2 ^ 64) :
    (B + BitVec.ofNat 64 d).toNat = B.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64), Nat.mod_eq_of_lt h]

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
  have hsep : Region.Disjoint ⟨p, 128⟩ ⟨B, 168⟩ :=
    (hdis _ hR).sub_right (Region.sub_prefix (by rw [total_eq]; decide))
  have hcore : Frame [coreRegion (dirCore up) B] s.mem
      (over s.mem (schedAddr B) (8 * 16) fun i => s.mem (p + BitVec.ofNat 64 i)) := by
    rw [core_eq]
    exact (over_frame _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, sched_sub B⟩
  refine WP.mono_syms (copyN_wp (k := 16) (P := schedAddr B) (Q := p) ⟨by rw [hB], by rw [hp]; simp,
    by decide, by decide, fun w hw => ⟨_, hs.wr, by
      rw [addr_add, total_eq]; exact Offset.contains_base B (by simp only [schedSlot]; omega)
        (by simp only [schedSlot]; omega)⟩,
    fun w hw => ⟨_, List.mem_append_left _ hin, Offset.contains_base p (by omega) (by omega)⟩,
    (hsep.sub_right (sched_sub B)).symm, by omega⟩) fun s' h hsy => ?_
  refine ⟨⟨?_, by rw [h.regs _ (by decide), hsi], hn, hT.frame h.rd h.wr hsy (by rw [h.mem]; exact hcore)
      fun r hr => ?_⟩, by rw [h.regs _ (by decide), hB], h.regs _ (by decide), h.regs _ (by decide),
    h.regs _ (by decide), by rw [h.mem]; exact hcore, h.rd, h.wr⟩
  · rw [h.mem, hkk]
    exact scheduleAt_congr_at fun i hi => over_at hi (by omega)
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
    ⟨_, by rw [wr₁]; exact hw, by rw [r₁, hB]; exact Offset.contains_base B (by omega) (by omega)⟩
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := stM_ok s₂ .r8 .r13 32
    ⟨_, by rw [wr₂, wr₁]; exact hw, by rw [g₂, r₁, hB]; exact Offset.contains_base B (by omega) (by omega)⟩
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movR_ok s₃ .rdx sb
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addImm_ok s₄ .rdx (BitVec.ofNat 32 (8 * bufSlot))
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := movR_ok s₅ .rdi sb
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇⟩ := addImm_ok s₆ .rdi (BitVec.ofNat 32 (8 * schedSlot))
  have sb₃ : s₃.gpr sb = B := by rw [g₃, g₂, o₁ _ (by decide), hB]
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
    ⟨_, List.mem_append_right _ hw, by rw [h8]; exact Offset.contains_base B (by omega) (by omega)⟩
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := ld_ok s₁ .r13 .r8 32
    ⟨_, List.mem_append_right _ (by rw [wr₁]; exact hw), by
      rw [o₁ _ (by decide), h8]; exact Offset.contains_base B (by omega) (by omega)⟩
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
  have e₀ : runBlock isa saveIv s = some (s.setReg .rcx ((s.xmm .xmm15).extractLsb' 0 64)) := by
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
  have e₃ : runBlock isa [.xop (.movq .xmm15 .rcx)] s₂ = some ((XOp.movq .xmm15 .rcx).exec s₂) := by
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
  have dT := hT.sep _ hw
  -- The regions of the scratch buffer the core uses.
  have sWs : Region.Sub ⟨B, 16⟩ ⟨B, 8 * 29⟩ := Region.sub_prefix (by decide)
  have sBuf : Region.Sub ⟨B + BitVec.ofNat 64 16, 8⟩ ⟨B, 8 * 29⟩ := Offset.sub_base B (by decide)
  have sKeep : Region.Sub ⟨B + BitVec.ofNat 64 24, 16⟩ ⟨B, 8 * 29⟩ := Offset.sub_base B (by decide)
  have dSchedWs : Region.Disjoint ⟨schedAddr B, 128⟩ ⟨B, 16⟩ := by
    have := Offset.disjoint B (d := 40) (n := 128) (e := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  have dSchedKeep : Region.Disjoint ⟨schedAddr B, 128⟩ ⟨B + BitVec.ofNat 64 24, 16⟩ :=
    Offset.disjoint B (.inr (by decide)) (by decide) (by decide)
  have dKeepBuf : Region.Disjoint ⟨B + BitVec.ofNat 64 24, 16⟩ ⟨B + BitVec.ofNat 64 16, 8⟩ :=
    Offset.disjoint B (.inr (by decide)) (by decide) (by decide)
  have dKeepWs : Region.Disjoint ⟨B + BitVec.ofNat 64 24, 16⟩ ⟨B, 16⟩ := by
    have := Offset.disjoint B (d := 24) (n := 16) (e := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  have dBufKeep : Region.Disjoint ⟨B + BitVec.ofNat 64 16, 8⟩ ⟨B + BitVec.ofNat 64 24, 16⟩ := dKeepBuf.symm
  have inW : ∀ {t l}, t + l ≤ 8 * 29 → InRegions s.wr (B + BitVec.ofNat 64 t) l := fun ht =>
    ⟨_, hw, Offset.contains_base B ht (by omega)⟩
  -- The setup.
  obtain ⟨u, eu, u8, udx, udi, ug, um, urd, uwr⟩ := setupIv_run hB hw
  have usy : u.syms = s.syms := runBlock_syms eu
  have fu : Frame [⟨B + BitVec.ofNat 64 24, 16⟩] s.mem u.mem := by
    rw [um]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains B (d := 24) (n := 8) (e := 24) (k := 16)
      (by decide) (by decide) (by decide))).writeW List.mem_cons_self _
      (Offset.contains B (d := 32) (n := 8) (e := 24) (k := 16) (by decide) (by decide) (by decide))
  have uk : Spec.Cast5.scheduleAt u.mem (schedAddr B) = k := by
    rw [scheduleAt_frame fu fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dSchedKeep]
    exact hk
  have uT : TabAt u := hT.frame urd uwr usy fu fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dT.sub_right sKeep
  have hpre : BPre u k n := by
    refine ⟨⟨?_, fun j hj => ?_, ?_, ?_, uT.held, ?_, ?_, ?_, uT.fit⟩, hn, by rw [ug _ (by decide) (by decide)
      (by decide) (by decide), hsi], ?_⟩
    · rw [udi, urd, uwr]
      exact ⟨_, List.mem_append_right _ hw, Offset.contains_base B (by decide) (by decide)⟩
    · rw [udi, ← scheduleAt_getD _ _ hj, uk]
    · rw [u8, uwr, show B = B + BitVec.ofNat 64 0 by rw [BitVec.add_zero]]; exact inW (by decide)
    · exact ⟨_, List.mem_append_left _ uT.rd, Region.contains_self _ _⟩
    · rw [udi, u8]; exact dSchedWs
    · rw [usy, u8]; exact dT.sub_right sWs
    · rw [udi, toNat_add (by simp only [schedSlot]; omega)]; simp only [schedSlot]; omega
    · rw [udx, uwr]; exact inW (by decide)
  show WP isa (cryptCode up) s _
  refine WP.seq (WP.of_runBlock ⟨u, eu, ?_⟩)
  refine WP.seq (WP.mono (block_ok up hpre) fun v ⟨vout, vf, _, _, _, vrd, vwr, vsy, vg⟩ => ?_)
  rw [u8, udx] at vf
  rw [udx] at vout
  have v8 : v.gpr .r8 = B := by rw [vg _ (by decide) (by decide) (by decide) (by decide), u8]
  obtain ⟨s', es, r12', r13', sb', g', m', rd', wr'⟩ := finishIv_run v8 (by rw [vwr, uwr]; exact hw)
  refine WP.of_runBlock ⟨s', es, ?_⟩
  have sy' : s'.syms = s.syms := by rw [runBlock_syms es, vsy, usy]
  have hvu : ∀ x, x ∉ roundRegs → x ≠ .r13 → x ≠ .rdx → x ≠ .rcx → x ≠ .r8 → x ≠ .rdi → x ≠ .r12 → x ≠ sb →
      s'.gpr x = s.gpr x := fun x h1 h2 h3 h4 h5 h6 h7 h8 => by
    rw [g' x h7 h2 h8 h4, vg x h1 h2 h3 h4, ug x h5 h3 h6 h4]
  -- The block and the working space, apart from the kept registers' slots.
  have keepV : ∀ d, 24 ≤ d → d + 8 ≤ 40 → v.mem.readW (B + BitVec.ofNat 64 d) 64 =
      u.mem.readW (B + BitVec.ofNat 64 d) 64 := fun d h1 h2 => by
    have sd : Region.Sub ⟨B + BitVec.ofNat 64 d, 8⟩ ⟨B + BitVec.ofNat 64 24, 16⟩ := Offset.sub B h1 (by omega)
    refine vf.readW (r := ⟨B + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dKeepBuf.sub_left sd
    · exact dKeepWs.sub_left sd
  have fv : Frame [⟨B + BitVec.ofNat 64 16, 8⟩, ⟨B, 16⟩] u.mem s'.mem := by rw [m']; exact vf
  have fCore : Frame [coreRegion (dirCore up) B] s.mem s'.mem := by
    rw [core_eq]
    refine (fu.sub fun r hr => ?_).trans (fv.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base B (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_singleton_self _, Offset.sub_base B (by decide)⟩
      · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  have vrd' : s'.rd = s.rd := by rw [rd', vrd, urd]
  have vwr' : s'.wr = s.wr := by rw [wr', vwr, uwr]
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
  · have hj0 : j = 0 := by simp only [dirCore] at hj; omega
    subst hj0
    have ea : blkAddr (dirCore up) B 0 = B + BitVec.ofNat 64 16 := rfl
    have hbu : Spec.Cast5.blockAt u.mem (B + BitVec.ofNat 64 16) = Spec.Cast5.blockAt s.mem (B + BitVec.ofNat 64 16) :=
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
