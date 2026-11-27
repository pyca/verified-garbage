module

import VerifiedGarbage.Proof.Modes.AArch64.Fb
public import VerifiedGarbage.Proof.Idea.FbScratch
import VerifiedGarbage.Proof.Idea.AArch64.ModesLit
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
public import VerifiedGarbage.Spec.Idea.Cfb
public import VerifiedGarbage.Impl.Idea.AArch64.Modes
public import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.Modes.AArch64.Fb
meta import VerifiedGarbage.Proof.Idea.FbScratch
meta import VerifiedGarbage.Proof.Idea.AArch64.ModesLit
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
meta import VerifiedGarbage.Spec.Idea.Cfb
meta import VerifiedGarbage.Impl.Idea.AArch64.Modes
meta import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Idea.ModeBytes
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Idea.ModeBytes
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Idea.AArch64.Ecb
import VerifiedGarbage.Proof.Idea.AArch64.Lit
import VerifiedGarbage.Proof.Idea.KeyBits
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Idea.AArch64.Ecb
meta import VerifiedGarbage.Proof.Idea.AArch64.Lit
meta import VerifiedGarbage.Proof.Idea.KeyBits
meta import VerifiedGarbage.Proof.Idea.Memory
meta import VerifiedGarbage.Proof.Modes.AArch64.Steps
meta import VerifiedGarbage.Proof.Modes.AArch64.Words
meta import VerifiedGarbage.Proof.Modes.Addr
meta import VerifiedGarbage.Spec.Ctr.Contract
public import VerifiedGarbage.Proof.Modes.AArch64.Core
public import VerifiedGarbage.Spec.Idea.Cbc
meta import VerifiedGarbage.Proof.Modes.AArch64.Core
meta import VerifiedGarbage.Spec.Idea.Cbc

/-! ### `Idea.AArch64.ModeCore`, which this module and modules that import it used -/

section

/-!
# IDEA's core for the modes on AArch64

`modeCoreSpec`: IDEA's core (`Impl.Idea.AArch64.modeCore`) meets what the
modes need of a core of one-word blocks (`Proof.Modes.AArch64.BlockSpec`),
with the key a schedule (of encryption or decryption subkeys), its cipher
`Spec.Idea.cipher`, and the key ready when its copy in the core's slots is
the schedule. As on x86-64 (`Proof/Idea/X86_64/FbVerified.lean`): `crypt` is
`vg_idea_ecb`'s block code (`cryptBlock_run`) on the buffer.
-/

@[expose] public section

namespace VG.Proof.Idea.AArch64

open VG VG.AArch64 VG.Impl.Idea.AArch64
open VG.Impl.Aes.AArch64 (sb)
open VG.Proof.Modes (over over_at over_frame)
open VG.Proof.Modes.AArch64 (ScrIn coreRegion blkRegion blkAddr BlockSpec copyN_wp addImm_ok runBlock_app addr_add)

/-- The schedule's copy, with the scratch buffer at `B`. -/
abbrev schedAddr (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * schedSlot)

/-- The schedule at `x0`, outside the regions `rs`. -/
def ModeKeyArgs (s : State) (rs : List Region) (k : Spec.Idea.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .x0 = p ∧ k = Spec.Idea.scheduleAt s.mem p ∧ (⟨p, 104⟩ : Region) ∈ s.rd ∧
    p.toNat + 104 ≤ 2 ^ 64 ∧ ∀ r ∈ rs, Region.Disjoint ⟨p, 104⟩ r

/-- The schedule's copy is `k`. -/
def ReadyAt (m : Mem) (B : Addr) (k : Spec.Idea.Schedule) : Prop :=
  Spec.Idea.scheduleAt m (schedAddr B) = k

/-- The core's blocks are one word. -/
@[simp] theorem modeCore_bw : modeCore.bw = 1 := rfl

/-- The core's slots, its buffer and the schedule's copy. -/
theorem core_eq (B : Addr) : coreRegion modeCore B = ⟨B, 112⟩ := rfl
theorem blk_eq (B : Addr) : blkRegion modeCore B = ⟨B + BitVec.ofNat 64 0, 8⟩ := rfl
theorem total_eq : modeCore.total = 26 := rfl

theorem sched_sub (B : Addr) : Region.Sub ⟨schedAddr B, 104⟩ ⟨B, 112⟩ := Offset.sub_base B (by decide)

theorem sched_buf (B : Addr) : Region.Disjoint ⟨schedAddr B, 104⟩ ⟨B + BitVec.ofNat 64 0, 8⟩ :=
  Offset.disjoint B (.inr (by decide)) (by decide) (by decide)

theorem readyAt_frame {m m' : Mem} {B : Addr} {k : Spec.Idea.Schedule} {rs : List Region}
    (h : ReadyAt m B k) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion modeCore B) r ∨ Region.Sub r (blkRegion modeCore B)) :
    ReadyAt m' B k := by
  rw [ReadyAt, scheduleAt_frame hf fun r hr => ?_]
  · exact h
  rcases hd r hr with h' | h'
  · rw [core_eq] at h'; exact h'.sub_left (sched_sub B)
  · rw [blk_eq] at h'; exact (sched_buf B).sub_right h'

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Idea.Schedule} (h : ModeKeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.x0], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : ModeKeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [hr .x0 List.mem_cons_self, hp], ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hk]
  exact (scheduleAt_frame hf hdis).symm

theorem prepare_wp {s : State} {B : Addr} {rs : List Region} {k : Spec.Idea.Schedule}
    (hB : s.gpr sb = B) (hs : ScrIn s B modeCore.total) (hR : (⟨B, 8 * modeCore.total⟩ : Region) ∈ rs)
    (hk : ModeKeyArgs s rs k) :
    WP isa modeCore.prepare s fun s' => ReadyAt s'.mem B k ∧ s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Frame [coreRegion modeCore B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, rfl, hin, hfit, hdis⟩ := hk
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hsep : Region.Disjoint ⟨p, 104⟩ ⟨B, 112⟩ :=
    (hdis _ hR).sub_right (Region.sub_prefix (by rw [total_eq]; decide))
  refine WP.mono (copyN_wp (k := 13) (t := .x6) (u := .x6) (P := schedAddr B) (Q := p)
    ⟨by rw [hB], by rw [hp]; simp, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, fun w hw => ⟨_, hs.wr, by
        rw [addr_add, total_eq]
        exact Offset.contains_base B (by simp only [schedSlot]; omega_arith) (by simp only [schedSlot]; omega_arith)⟩,
      fun w hw => ⟨_, List.mem_append_left _ hin, Offset.contains_base p (by omega_arith) (by omega_arith)⟩,
      (hsep.sub_right (sched_sub B)).symm, by omega_arith⟩) fun s' h => ?_
  refine ⟨scheduleAt_congr_at fun i hi => by rw [h.mem, over_at hi (by omega_arith)],
    by rw [h.regs _ (by decide) (by decide), hB], h.regs _ (by decide) (by decide), h.regs _ (by decide) (by decide),
    ?_, h.rd, h.wr⟩
  rw [h.mem, core_eq]
  exact (over_frame _ _ _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, sched_sub B⟩

theorem crypt_wp {s : State} {B : Addr} {k : Spec.Idea.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B modeCore.total) (hr : ReadyAt s.mem B k) :
    WP isa modeCore.crypt s fun s' => s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧ ReadyAt s'.mem B k ∧
      Frame [coreRegion modeCore B] s.mem s'.mem ∧
      (∀ j < modeCore.G, Spec.Aes.bytesAt s'.mem (blkAddr modeCore B j) (8 * modeCore.bw) =
        Spec.Idea.cipher k (Spec.Aes.bytesAt s.mem (blkAddr modeCore B j) (8 * modeCore.bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw := hs.wr
  rw [total_eq] at hw
  have hfB := hs.fit
  rw [total_eq] at hfB
  -- `x2` keeps `sb`; `x0` and `x1` to the schedule's copy and the buffer; the mask.
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := addImm_ok s .x2 sb (v := 0) (by decide)
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .x0 sb (v := 8 * schedSlot) (by decide)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := addImm_ok s₂ .x1 sb (v := 0) (by decide)
  obtain ⟨s₄, e₄, mk₄, k₄⟩ := setMask_run s₃
  have g₄ : ∀ x, x ≠ .x2 → x ≠ .x0 → x ≠ .x1 → x ≠ .x15 → s₄.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [k₄.reg x (by simp [h4]), o₃ x h3, o₂ x h2, o₁ x h1]
  have x2₄ : s₄.gpr .x2 = B := by
    rw [k₄.reg _ (by decide), o₃ _ (by decide), o₂ _ (by decide), r₁, hB]; simp
  have x0₄ : s₄.gpr .x0 = schedAddr B := by
    rw [k₄.reg _ (by decide), o₃ _ (by decide), r₂, o₁ _ (by decide), hB]
  have x1₄ : s₄.gpr .x1 = B := by
    rw [k₄.reg _ (by decide), r₃, o₂ _ (by decide), o₁ _ (by decide), hB]; simp
  have mem₄ : s₄.mem = s.mem := by rw [k₄.mem, m₃, m₂, m₁]
  have rd₄' : s₄.rd = s.rd := by rw [k₄.rd, rd₃, rd₂, rd₁]
  have wr₄' : s₄.wr = s.wr := by rw [k₄.wr, wr₃, wr₂, wr₁]
  have inS : ∀ {t n}, t + n ≤ 208 → 0 < n → InRegions s₄.wr (B + BitVec.ofNat 64 t) n := fun ht hn =>
    ⟨_, by rw [wr₄']; exact hw, Offset.contains_base B (by omega_arith) (by omega_arith)⟩
  -- The block.
  have hk : KeyOk k s₄ := ⟨by
      rw [x0₄]
      obtain ⟨r, h1, h2⟩ := inS (t := 8 * schedSlot) (n := 104) (by decide) (by decide)
      exact ⟨r, List.mem_append_right _ h1, h2⟩,
    by rw [x0₄, mem₄]; exact hr⟩
  obtain ⟨s₅, e₅, b₅, f₅, g₅, rd₅, wr₅, -⟩ := cryptBlock_run k s₄ x1₄
    (fun i hi => by
      obtain ⟨r, h1, h2⟩ := inS (t := i) (n := 1) (by omega_arith) (by decide)
      exact ⟨r, List.mem_append_right _ h1, by simpa using h2⟩)
    (fun i hi => by simpa using inS (t := i) (n := 1) (by omega_arith) (by decide)) hk mk₄
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := addImm_ok s₅ sb .x2 (v := 0) (by decide)
  refine WP.of_runBlock ⟨s₆, ?_, ?_⟩
  · show runBlock isa (([.addImm .x .x2 sb 0] ++ ([.addImm .x .x0 sb (8 * schedSlot)] ++
      ([.addImm .x .x1 sb 0] ++ ([setMask] : List Instr)))) ++ cryptBlock ++ [.addImm .x sb .x2 0]) s = some s₆
    rw [runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some,
      runBlock_app, e₃, Option.bind_some, e₄, Option.bind_some, e₅, Option.bind_some, e₆]
  have kp : ∀ x, x ∉ roundWrites → x ≠ .x2 → x ≠ .x0 → x ≠ .x1 → x ≠ .x15 → x ≠ sb → s₆.gpr x = s.gpr x :=
    fun x h0 h1 h2 h3 h4 h5 => by rw [o₆ _ h5, g₅ _ h0, g₄ _ h1 h2 h3 h4]
  have fB : Frame [⟨B, 8⟩] s.mem s₆.mem := by rw [m₆, ← mem₄]; exact f₅
  refine ⟨by rw [r₆, g₅ _ (by decide), x2₄]; simp,
    kp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    kp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, fun j hj => ?_,
    by rw [rd₆, rd₅, rd₄'], by rw [wr₆, wr₅, wr₄']⟩
  · rw [ReadyAt, scheduleAt_frame fB fun r hr => ?_]
    · exact hr
    · simp only [List.mem_singleton] at hr; subst hr
      have := sched_buf B; rwa [BitVec.add_zero] at this
  · rw [core_eq]
    exact fB.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  · have hj0 : j = 0 := by simp only [modeCore, Impl.Modes.AArch64.Core.G] at hj; omega_arith
    subst hj0
    have ea : blkAddr modeCore B 0 = B := by simp [modeCore]
    rw [modeCore_bw, ea, cipher_bytes, bytesAt_eq, m₆, b₅, mem₄]

/-- IDEA's core meets what the modes need. -/
def modeCoreSpec : BlockSpec modeCore where
  Key := Spec.Idea.Schedule
  cipher := Spec.Idea.cipher
  KeyArgs := ModeKeyArgs
  Ready s B k := ReadyAt s.mem B k
  cipher_len _ _ := by simp [Spec.Idea.cipher]
  layout := ⟨by simp only [modeCore]; decide, by simp only [modeCore]; decide, by simp only [modeCore]; decide,
    by simp only [modeCore]; decide, by simp only [modeCore]; decide, by simp only [modeCore]; decide,
    by simp only [modeCore]; decide⟩
  keyRegs_ok := by simp only [modeCore]; decide
  regs_ok := by simp only [modeCore, Modes.AArch64.regsOk]; decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame h hf hd _ _ := readyAt_frame h hf hd
  prepare_wp := prepare_wp
  crypt_wp := crypt_wp

end VG.Proof.Idea.AArch64

end

end

/-!
# IDEA-OFB and IDEA-CFB64 on AArch64 meet their contracts

`ofb_wp`, `cfbEncrypt_wp`, `cfbDecrypt_wp`: the modes' OFB and CFB
(`Proof.Modes.AArch64.fb_wp`) over IDEA's core (`modeCoreSpec`), with the
IV's address in `x25`, which the core never writes (`keepsReg_of_regSafe`),
and the specification's results (`Proof.Modes.ofb_of`, …). `ofb_verified`,
…: each is correct and constant time, by the taint analysis: the pointers,
`n` and the stack pointer are public, and so is everything the code computes
from them, which it keeps in registers; the IV is secret. `ofb_framed`, …
run them with their working space on the stack, zeroed on return: 208
bytes, the 26 words of the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Idea.AArch64

open VG VG.AArch64 VG.Impl.Idea.AArch64

/-- The precondition of the feedback modes on AArch64, with the data `len`
bytes long and the working space at `x4`. -/
def fbPre (len : State → Nat) (s : State) : Prop :=
  let sched : Region := ⟨s.gpr .x0, 104⟩
  let iv : Region := ⟨s.gpr .x1, 8⟩
  let data : Region := ⟨s.gpr .x2, len s⟩
  let scratch : Region := ⟨s.gpr .x4, 8 * 26⟩
  s.rd = [sched] ∧ s.wr = [iv, data, scratch] ∧ sched.Disjoint iv ∧ sched.Disjoint data ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .x0).toNat + 104 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .x2).toNat + len s ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8 * 26 ≤ 2 ^ 64

/-- The public arguments. -/
def fbPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `n` blocks. -/
abbrev blkLen (s : State) : Nat := 8 * (s.gpr .x3).toNat

/-- The schedule, IV and data of `s`'s arguments. -/
abbrev ciphOf (s : State) : Spec.Cbc.Cipher := Spec.Idea.cipher (Spec.Idea.scheduleAt s.mem (s.gpr .x0))
abbrev ivOf (s : State) : List Byte := Spec.Aes.bytesAt s.mem (s.gpr .x1) 8
abbrev blocksOf (s : State) (m : Mem) : List (List Byte) := Spec.Idea.cbcBlocksAt m (s.gpr .x2) (s.gpr .x3).toNat

def ofbAArch64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Ofb.crypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x1) 8 = Spec.Ofb.next (ciphOf s) (ivOf s) (s.gpr .x3).toNat
  pub := fbPub

def cfbEncAArch64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x1) 8 =
      Spec.Cbc.next (ivOf s) (Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

def cfbDecAArch64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.decrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x1) 8 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

/-- The core keeps `x25`, where the modes keep the IV's address. -/
theorem keeps_x25 :
    Modes.AArch64.KeepsReg .x25 modeCore.prepare ∧ Modes.AArch64.KeepsReg .x25 modeCore.crypt :=
  ⟨Modes.AArch64.keepsReg_of_regSafe (by lit_decide), Modes.AArch64.keepsReg_of_regSafe (by lit_decide)⟩

/-- What the modes' OFB and CFB give, for a mode `mo`: the data and the
IV as `fbOut` and `fbIn`, keeping the callee-saved registers. -/
theorem fb_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre blkLen s₀) :
    WP isa (modeCore.fb mo modeRegs .x25) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧
      Modes.blocksOf 8 s'.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat =
        (List.range (s₀.gpr .x3).toNat).map (Modes.fbOut mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀)) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .x1) 8 =
        Modes.fbIn mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 26⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.fb_wp modeCoreSpec mo (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x25)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.Idea.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp [Nat.mul_comm]) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ keeps_x25)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [modeCore_bw, Nat.mul_one] at hdata hiv; exact ⟨hdata, hiv⟩⟩

theorem ofb_wp {s₀ : State} (hp : ofbAArch64.pre s₀) :
    WP isa ofb s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ ofbAArch64.post s₀ s' :=
  WP.mono (fb_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofb_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat
    refine ⟨hg, ?_, by rw [hv, h2]⟩
    change Spec.Idea.cbcBlocksAt _ _ _ = Spec.Ofb.crypt _ _ (Spec.Idea.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]

theorem cfbEncrypt_wp {s₀ : State} (hp : cfbEncAArch64.pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbEncAArch64.post s₀ s' :=
  WP.mono (fb_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEnc_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.Idea.cbcBlocksAt _ _ _ = Spec.Cfb.encrypt _ _ (Spec.Idea.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Cfb.encrypt _ _ (Spec.Idea.cbcBlocksAt _ _ _))
      rw [hv, h2, cbcBlocksAt_eq]

theorem cfbDecrypt_wp {s₀ : State} (hp : cfbDecAArch64.pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbDecAArch64.post s₀ s' :=
  WP.mono (fb_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDec_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.Idea.cbcBlocksAt _ _ _ = Spec.Cfb.decrypt _ _ (Spec.Idea.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Idea.cbcBlocksAt _ _ _)
      rw [hv, h2, cbcBlocksAt_eq]

/-- The callee-saved registers and the rest of the ABI, from what a mode
keeps. -/
theorem abi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (h₁ : ∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19))
    (h₃ : ∀ r ∈ [Reg.x30], s'.gpr r = s.gpr r) (hv : c.allInstrs keepsV = true) : abiPreserved s s' :=
  ⟨Modes.AArch64.preserved_of h₁ h₃, Exec.sp he, Exec.preservedV he hv⟩

/-! ## Constant time -/

theorem fbTaint_agree {len : State → Nat} (s₁ s₂ : State) (_ : fbPre len s₁) (_ : fbPre len s₂)
    (hp : fbPub s₁ s₂) : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (one block). -/
def fbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩, ⟨0x4000, 8 * 26⟩]

/-- A state satisfying the contracts' precondition: the schedule at
`0x1000`, the IV at `0x2000`, one block at `0x3000`. -/
def fbFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩]

theorem ofb_verified :
    Verified AArch64.target ofb (Proof.Idea.fbScratchContract AArch64.abi 26 Proof.Idea.ofbPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (ofb_wp hs) (by lit_decide) (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Spec.Idea.ofbSig,
      Proof.Idea.ofbPost, ofbAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [fbSat] using fbSat)

theorem cfbEncrypt_verified :
    Verified AArch64.target cfbEncrypt (Proof.Idea.fbScratchContract AArch64.abi 26 Proof.Idea.cfbEncPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cfbEncrypt_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Spec.Idea.ofbSig,
      Proof.Idea.cfbEncPost, cfbEncAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [fbSat] using fbSat)

theorem cfbDecrypt_verified :
    Verified AArch64.target cfbDecrypt (Proof.Idea.fbScratchContract AArch64.abi 26 Proof.Idea.cfbDecPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cfbDecrypt_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Spec.Idea.ofbSig,
      Proof.Idea.cfbDecPost, cfbDecAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [fbSat] using fbSat)

theorem ofbFrameSat_pre : ∃ s, (Spec.Idea.ofbContract AArch64.abi 208).pre s := by
  implies_sat [Spec.Idea.ofbContract, Spec.Idea.ofbSig, AArch64.abi, AArch64.argRegs]
    [fbFrameSat] using fbFrameSat

theorem cfbEncFrameSat_pre : ∃ s, (Spec.Idea.cfbEncryptContract AArch64.abi 208).pre s := by
  implies_sat [Spec.Idea.cfbEncryptContract, Spec.Idea.cfbSig, Spec.Idea.ofbSig, AArch64.abi,
    AArch64.argRegs] [fbFrameSat] using fbFrameSat

theorem cfbDecFrameSat_pre : ∃ s, (Spec.Idea.cfbDecryptContract AArch64.abi 208).pre s := by
  implies_sat [Spec.Idea.cfbDecryptContract, Spec.Idea.cfbSig, Spec.Idea.ofbSig, AArch64.abi,
    AArch64.argRegs] [fbFrameSat] using fbFrameSat

/-- OFB with its working space on the stack. -/
theorem ofb_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 ofb)
      (Spec.Idea.ofbContract AArch64.abi 208) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Idea.ofbSig) (nm := "scratch") (e := .u64)
    (n := 26) (post := Proof.Idea.ofbPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 208) ofb_verified
    (by decide) (by decide) (by decide) (Proof.Idea.ofbPostOut_local _) ofbFrameSat_pre

/-- CFB64 encryption with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 cfbEncrypt)
      (Spec.Idea.cfbEncryptContract AArch64.abi 208) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Idea.cfbSig) (nm := "scratch") (e := .u64)
    (n := 26) (post := Proof.Idea.cfbEncPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 208) cfbEncrypt_verified
    (by decide) (by decide) (by decide) (Proof.Idea.cfbEncPostOut_local _) cfbEncFrameSat_pre

/-- CFB64 decryption with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 cfbDecrypt)
      (Spec.Idea.cfbDecryptContract AArch64.abi 208) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Idea.cfbSig) (nm := "scratch") (e := .u64)
    (n := 26) (post := Proof.Idea.cfbDecPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 208) cfbDecrypt_verified
    (by decide) (by decide) (by decide) (Proof.Idea.cfbDecPostOut_local _) cfbDecFrameSat_pre

end VG.Proof.Idea.AArch64
