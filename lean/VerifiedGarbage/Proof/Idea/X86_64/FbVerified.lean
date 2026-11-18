module

import VerifiedGarbage.Proof.Modes.X86_64.Fb
public import VerifiedGarbage.Proof.Idea.FbScratch
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Impl.Idea.X86_64.Modes
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Spec.Idea.Cfb
public import VerifiedGarbage.Proof.Modes.Fb
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Modes.X86_64.Fb
meta import VerifiedGarbage.Proof.Idea.FbScratch
meta import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Impl.Idea.X86_64.Modes
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Spec.Idea.Cfb
meta import VerifiedGarbage.Proof.Modes.Fb
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Idea.ModeBytes
meta import VerifiedGarbage.Proof.Idea.ModeBytes
public import VerifiedGarbage.Proof.Modes.X86_64.Core
public import VerifiedGarbage.Spec.Idea.Cbc
public import VerifiedGarbage.Proof.Idea.X86_64.Block
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Modes.X86_64.Words
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Idea.X86_64.Lit
meta import VerifiedGarbage.Proof.Modes.X86_64.Core
meta import VerifiedGarbage.Spec.Idea.Cbc
meta import VerifiedGarbage.Proof.Idea.X86_64.Block
meta import VerifiedGarbage.Proof.Idea.Memory
meta import VerifiedGarbage.Proof.Modes.X86_64.Steps
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Modes.X86_64.Words
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Idea.X86_64.Lit

/-! ### `Idea.X86_64.ModeCore`, which this module and modules that import it used -/

section

/-!
# IDEA's core for the modes on x86-64

`modeCoreSpec`: IDEA's core (`Impl.Idea.X86_64.modeCore`) meets what the
modes need of a core of one-word blocks (`Proof.Modes.X86_64.BlockSpec`),
with the key a schedule (of encryption or decryption subkeys), its cipher
`Spec.Idea.cipher`, and the key ready when its copy in the core's slots is
the schedule. `crypt` is `vg_idea_ecb`'s block code (`cryptBlock_run`) on the
buffer.
-/

@[expose] public section

namespace VG.Proof.Idea.X86_64

open VG VG.X86_64 VG.Impl.Idea.X86_64
open VG.Impl.Aes.X86_64 (sb)
open VG.Proof.Modes (over over_at over_frame)
open VG.Proof.Modes.X86_64 (ScrIn coreRegion blkRegion blkAddr BlockSpec copyN_wp movR_ok addImm_ok
  signExtend_small runBlock_app addr_add)

/-- The schedule's copy, with the scratch buffer at `B`. -/
abbrev schedAddr (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * schedSlot)

/-- The schedule at `rdi`, outside the regions `rs`. -/
def ModeKeyArgs (s : State) (rs : List Region) (k : Spec.Idea.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .rdi = p ∧ k = Spec.Idea.scheduleAt s.mem p ∧ (⟨p, 104⟩ : Region) ∈ s.rd ∧
    p.toNat + 104 ≤ 2 ^ 64 ∧ ∀ r ∈ rs, Region.Disjoint ⟨p, 104⟩ r

/-- The schedule's copy is `k`. -/
def ReadyAt (m : Mem) (B : Addr) (k : Spec.Idea.Schedule) : Prop :=
  Spec.Idea.scheduleAt m (schedAddr B) = k

/-- The core's blocks are one word. -/
@[simp] theorem modeCore_bw : modeCore.bw = 1 := rfl

/-- The core's slots, its buffer and the schedule's copy. -/
theorem core_eq (B : Addr) : coreRegion modeCore B = ⟨B, 112⟩ := rfl
theorem blk_eq (B : Addr) : blkRegion modeCore B = ⟨B + BitVec.ofNat 64 0, 8⟩ := rfl
theorem total_eq : modeCore.total = 22 := rfl

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
    (hr : ∀ r ∈ [Reg.rdi], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : ModeKeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [hr .rdi List.mem_cons_self, hp], ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hk]
  exact (scheduleAt_frame hf hdis).symm

theorem prepare_wp {s : State} {B : Addr} {rs : List Region} {k : Spec.Idea.Schedule}
    (hB : s.gpr sb = B) (hs : ScrIn s B modeCore.total) (hR : (⟨B, 8 * modeCore.total⟩ : Region) ∈ rs)
    (hk : ModeKeyArgs s rs k) :
    WP isa modeCore.prepare s fun s' => ReadyAt s'.mem B k ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .r13 = s.gpr .r13 ∧
      Frame [coreRegion modeCore B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, rfl, hin, hfit, hdis⟩ := hk
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hsep : Region.Disjoint ⟨p, 104⟩ ⟨B, 112⟩ := (hdis _ hR).sub_right (Region.sub_prefix (by rw [total_eq]; decide))
  refine WP.mono (copyN_wp (k := 13) (P := schedAddr B) (Q := p) ⟨by rw [hB], by rw [hp]; simp, by decide,
    by decide, fun w hw => ⟨_, hs.wr, by
      rw [addr_add, total_eq]; exact Offset.contains_base B (by simp only [schedSlot]; omega_using [hw]) (by simp only [schedSlot]; omega_using [hw])⟩,
    fun w hw => ⟨_, List.mem_append_left _ hin, Offset.contains_base p (by omega_using [hw]) (by omega_using [hw])⟩,
    (hsep.sub_right (sched_sub B)).symm, by omega_using []⟩) fun s' h => ?_
  refine ⟨scheduleAt_congr_at fun i hi => by rw [h.mem, over_at hi (by omega_using [])], by rw [h.regs _ (by decide), hB],
    h.regs _ (by decide), h.regs _ (by decide), h.regs _ (by decide), ?_, h.rd, h.wr⟩
  rw [h.mem, core_eq]
  exact (over_frame _ _ _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, sched_sub B⟩

/-- `KeyOk` of a schedule at `rdi` within the writable regions. -/
theorem keyOk_at (s : State) {p : Addr} (hp : s.gpr .rdi = p)
    (hin : ∀ d, d + 8 ≤ 104 → InRegions s.wr (p + BitVec.ofNat 64 d) 8) :
    KeyOk (Spec.Idea.scheduleAt s.mem p) s := by
  have hin' : ∀ d, d + 8 ≤ 104 → InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 d) 8 := fun d hd => by
    obtain ⟨r, h1, h2⟩ := hin d hd; exact ⟨r, List.mem_append_right _ h1, h2⟩
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun j hj => ?_⟩
  · rw [ea_at, hp]; exact hin' _ (by omega_using [hk])
  · rw [ea_at, hp]; exact subkey_read _ _ (by omega_using [hk])
  · rw [ea_at, hp]; exact subkey_read96 _ _ hj

theorem crypt_wp {s : State} {B : Addr} {k : Spec.Idea.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B modeCore.total) (hr : ReadyAt s.mem B k) :
    WP isa modeCore.crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .r13 = s.gpr .r13 ∧ ReadyAt s'.mem B k ∧
      Frame [coreRegion modeCore B] s.mem s'.mem ∧
      (∀ j < modeCore.G, Spec.Aes.bytesAt s'.mem (blkAddr modeCore B j) (8 * modeCore.bw) =
        Spec.Idea.cipher k (Spec.Aes.bytesAt s.mem (blkAddr modeCore B j) (8 * modeCore.bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw := hs.wr
  rw [total_eq] at hw
  have hfB := hs.fit
  rw [total_eq] at hfB
  -- `rcx` keeps `sb`; `rdi` and `rsi` to the schedule's copy and the buffer.
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .rcx sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ .rdi sb
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := addImm_ok s₂ .rdi (BitVec.ofNat 32 (8 * schedSlot))
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movR_ok s₃ .rsi sb
  have g₄ : ∀ x, x ≠ .rcx → x ≠ .rdi → x ≠ .rsi → s₄.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [o₄ x h3, o₃ x h2, o₂ x h2, o₁ x h1]
  have rcx₄ : s₄.gpr .rcx = B := by
    rw [o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), r₁, hB]
  have rdi₄ : s₄.gpr .rdi = schedAddr B := by
    rw [o₄ _ (by decide), r₃, r₂, o₁ _ (by decide), hB, signExtend_small (by decide)]
  have rsi₄ : s₄.gpr .rsi = B := by
    rw [r₄, o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide), hB]
  have mem₄ : s₄.mem = s.mem := by rw [m₄, m₃, m₂, m₁]
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, rd₁]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  have inS : ∀ {t n}, t + n ≤ 176 → 0 < n → InRegions s₄.wr (B + BitVec.ofNat 64 t) n := fun ht hn =>
    ⟨_, by rw [wr₄']; exact hw, Offset.contains_base B (by omega_using [ht]) (by omega_using [ht])⟩
  -- The block.
  have hk := keyOk_at s₄ rdi₄ fun d hd => by
    rw [addr_add]; exact inS (by simp only [schedSlot]; omega_using [hd]) (by decide)
  rw [mem₄, hr] at hk
  obtain ⟨s₅, e₅, b₅, f₅, g₅, rd₅, wr₅⟩ := cryptBlock_run k s₄ rsi₄
    (fun i hi => by
      obtain ⟨r, h1, h2⟩ := inS (t := i) (n := 1) (by omega_using [hi]) (by decide)
      exact ⟨r, List.mem_append_right _ h1, h2⟩)
    (fun i hi => inS (by omega_using [hi]) (by decide)) hk
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := movR_ok s₅ sb .rcx
  refine WP.of_runBlock ⟨s₆, ?_, ?_⟩
  · show runBlock isa (([Impl.Aes.X86_64.movR .rcx sb] ++ ([Impl.Aes.X86_64.movR .rdi sb] ++
      ([.alu .add .rdi (.imm (BitVec.ofNat 32 (8 * schedSlot)))] ++ ([Impl.Aes.X86_64.movR .rsi sb] : List Instr)))) ++
      cryptBlock ++ [Impl.Aes.X86_64.movR sb .rcx]) s = some s₆
    rw [runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some,
      runBlock_app, e₃, Option.bind_some, e₄, Option.bind_some, e₅, Option.bind_some, e₆]
  have kp : ∀ x, x ∉ roundWrites → x ≠ .rcx → x ≠ .rdi → x ≠ .rsi → x ≠ sb → s₆.gpr x = s.gpr x :=
    fun x h0 h1 h2 h3 h4 => by rw [o₆ _ h4, g₅ _ h0, g₄ _ h1 h2 h3]
  have fB : Frame [⟨B, 8⟩] s.mem s₆.mem := by rw [m₆, ← mem₄]; exact f₅
  refine ⟨by rw [r₆, g₅ _ (by decide), rcx₄], kp _ (by decide) (by decide) (by decide) (by decide) (by decide),
    kp _ (by decide) (by decide) (by decide) (by decide) (by decide),
    kp _ (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, fun j hj => ?_,
    by rw [rd₆, rd₅, rd₄'], by rw [wr₆, wr₅, wr₄']⟩
  · rw [ReadyAt, scheduleAt_frame fB fun r hr => ?_]
    · exact hr
    · simp only [List.mem_singleton] at hr; subst hr
      have := sched_buf B; rwa [BitVec.add_zero] at this
  · rw [core_eq]
    exact fB.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  · have hj0 : j = 0 := by simp only [modeCore] at hj; omega_using [hj]
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
    by simp only [modeCore]; decide, by simp only [modeCore]; decide, by simp only [modeCore]; decide⟩
  keyRegs_ok := by simp only [modeCore]; decide
  regs_ok := by simp only [modeCore, Modes.X86_64.regsOk]; decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame h hf hd _ _ := readyAt_frame h hf hd
  prepare_wp := prepare_wp
  crypt_wp := crypt_wp

end VG.Proof.Idea.X86_64

end

end

/-!
# IDEA-OFB and -CFB64 on x86-64 meet their contracts

`ofb_wp`, `cfbEncrypt_wp`, `cfbDecrypt_wp`: the modes' OFB and CFB
(`Proof.Modes.X86_64.fb_wp`) over IDEA's core (`modeCoreSpec`), with the
specification's results (`Proof.Modes.ofb_of`, …). `ofb_verified`, …: each
is correct and constant time, by the taint analysis: the pointers, `n` and
the stack pointer are public, and so is everything the code computes from
them; the IV is secret. `ofb_framed`, … run them with their working space on
the stack, zeroed on return: 184 bytes, the 22 words of the scratch buffer
and 8 more.
-/

@[expose] public section

namespace VG.Proof.Idea.X86_64

open VG VG.X86_64 VG.Impl.Idea.X86_64

/-- The precondition of the feedback modes on x86-64, with the data `len`
bytes long and the working space at `r8`. -/
def fbPre (len : State → Nat) (s : State) : Prop :=
  let sched : Region := ⟨s.gpr .rdi, 104⟩
  let iv : Region := ⟨s.gpr .rsi, 8⟩
  let data : Region := ⟨s.gpr .rdx, len s⟩
  let scratch : Region := ⟨s.gpr .r8, 8 * 22⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  s.rd = [sched] ∧ s.wr = [iv, data, scratch] ∧ sched.Disjoint iv ∧ sched.Disjoint data ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (s.gpr .rdi).toNat + 104 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + len s ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * 22 ≤ 2 ^ 64

/-- The public arguments. -/
def fbPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `n` blocks. -/
abbrev blkLen (s : State) : Nat := 8 * (s.gpr .rcx).toNat

/-- The schedule, IV and data of `s`'s arguments. -/
abbrev ciphOf (s : State) : Spec.Cbc.Cipher := Spec.Idea.cipher (Spec.Idea.scheduleAt s.mem (s.gpr .rdi))
abbrev ivOf (s : State) : List Byte := Spec.Aes.bytesAt s.mem (s.gpr .rsi) 8
abbrev blocksOf (s : State) (m : Mem) : List (List Byte) := Spec.Idea.cbcBlocksAt m (s.gpr .rdx) (s.gpr .rcx).toNat

def ofbX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Ofb.crypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 8 = Spec.Ofb.next (ciphOf s) (ivOf s) (s.gpr .rcx).toNat
  pub := fbPub

def cfbEncX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 8 =
      Spec.Cbc.next (ivOf s) (Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

def cfbDecX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.decrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 8 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

/-- What the modes' OFB and CFB give, for a mode `mo`: the data and the
IV as `fbOut` and `fbIn`, keeping the callee-saved registers. -/
theorem fb_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre blkLen s₀) :
    WP isa (modeCore.fb mo modeRegs) s₀ fun s' => gprPreserved s₀ s' ∧
      Modes.blocksOf 8 s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat =
        (List.range (s₀.gpr .rcx).toNat).map (Modes.fbOut mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀)) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .rsi) 8 = Modes.fbIn mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 22⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.fb_wp (modeCoreSpec) mo (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.Idea.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp [Nat.mul_comm]) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ ⟨Modes.X86_64.keepsIv_of_scal (by lit_decide), Modes.X86_64.keepsIv_of_scal (by lit_decide)⟩)
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ =>
    ⟨⟨hcs, ?_⟩, by rw [modeCore_bw, Nat.mul_one] at hdata hiv; exact ⟨hdata, hiv⟩⟩
  rw [VG.Proof.Modes.X86_64.stkList_eq_nil rfl, List.append_nil] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact dRS
  · exact dRD
  · exact dRV

theorem ofb_wp {s₀ : State} (hp : ofbX86_64.pre s₀) :
    WP isa ofb s₀ fun s' => gprPreserved s₀ s' ∧ ofbX86_64.post s₀ s' :=
  WP.mono (fb_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofb_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat
    refine ⟨hg, ?_, by rw [hv, h2]⟩
    change Spec.Idea.cbcBlocksAt _ _ _ = Spec.Ofb.crypt _ _ (Spec.Idea.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]

theorem cfbEncrypt_wp {s₀ : State} (hp : cfbEncX86_64.pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => gprPreserved s₀ s' ∧ cfbEncX86_64.post s₀ s' :=
  WP.mono (fb_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEnc_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.Idea.cbcBlocksAt _ _ _ = Spec.Cfb.encrypt _ _ (Spec.Idea.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Cfb.encrypt _ _ (Spec.Idea.cbcBlocksAt _ _ _))
      rw [hv, h2, cbcBlocksAt_eq]

theorem cfbDecrypt_wp {s₀ : State} (hp : cfbDecX86_64.pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => gprPreserved s₀ s' ∧ cfbDecX86_64.post s₀ s' :=
  WP.mono (fb_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDec_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.Idea.cbcBlocksAt _ _ _ = Spec.Cfb.decrypt _ _ (Spec.Idea.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Idea.cbcBlocksAt _ _ _)
      rw [hv, h2, cbcBlocksAt_eq]

/-! ## Constant time -/

/-- The initial taint: the registers of the arguments and the stack pointer are
public. It knows nothing of the writable regions: the code never reads a public
value back from them, and tracking them would cost the kernel at every store. -/
def fbTaint : X86_64.Taint.T := Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]

theorem fbTaint_agree {len : State → Nat} (_hlen : ∀ s t, s.gpr .rcx = t.gpr .rcx → len s = len t) (s t : State)
    (_ : fbPre len s) (_ : fbPre len t) (hp : fbPub s t) : X86_64.Taint.Agree fbTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [p1, p2, p3, p4, p5, p6]

theorem blkLen_congr : ∀ s t : State, s.gpr .rcx = t.gpr .rcx → blkLen s = blkLen t := fun _ _ h => by
  simp only [blkLen, h]

/-- A state satisfying the precondition (one block, or one byte). -/
def fbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩, ⟨0x4000, 8 * 22⟩]

theorem ofb_verified :
    Verified X86_64.target ofb (Proof.Idea.fbScratchContract X86_64.abi 22 Proof.Idea.ofbPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := ofb_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := ofb) (by lit_decide) he hg, hpost⟩)
    (VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)) (by
    sig_implies [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Spec.Idea.ofbSig,
      Proof.Idea.ofbPost, ofbX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [fbSat] using fbSat)

theorem cfbEncrypt_verified :
    Verified X86_64.target cfbEncrypt (Proof.Idea.fbScratchContract X86_64.abi 22 Proof.Idea.cfbEncPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbEncrypt_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbEncrypt) (by lit_decide) he hg, hpost⟩)
    (VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)) (by
    sig_implies [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Spec.Idea.ofbSig,
      Proof.Idea.cfbEncPost, cfbEncX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [fbSat] using fbSat)

theorem cfbDecrypt_verified :
    Verified X86_64.target cfbDecrypt (Proof.Idea.fbScratchContract X86_64.abi 22 Proof.Idea.cfbDecPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbDecrypt_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbDecrypt) (by lit_decide) he hg, hpost⟩)
    (VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)) (by
    sig_implies [Proof.Idea.fbScratchContract, Proof.Idea.fbScratchSig, Spec.Idea.ofbSig,
      Proof.Idea.cfbDecPost, cfbDecX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [fbSat] using fbSat)

/-- OFB with its working space on the stack. -/
theorem ofb_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 ofb)
      (Spec.Idea.ofbContract X86_64.abi 184) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Idea.ofbSig) (nm := "scratch") (e := .u64)
    (n := 22) (post := Proof.Idea.ofbPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 184) ofb_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Idea.ofbPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- CFB64 encryption with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 cfbEncrypt)
      (Spec.Idea.cfbEncryptContract X86_64.abi 184) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Idea.cfbSig) (nm := "scratch") (e := .u64)
    (n := 22) (post := Proof.Idea.cfbEncPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 184) cfbEncrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Idea.cfbEncPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- CFB64 decryption with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 cfbDecrypt)
      (Spec.Idea.cfbDecryptContract X86_64.abi 184) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Idea.cfbSig) (nm := "scratch") (e := .u64)
    (n := 22) (post := Proof.Idea.cfbDecPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 184) cfbDecrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Idea.cfbDecPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Idea.X86_64
