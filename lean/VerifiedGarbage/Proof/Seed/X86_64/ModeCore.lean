module

public import VerifiedGarbage.Proof.Seed.X86_64.Ecb
public import VerifiedGarbage.Proof.Seed.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Impl.X86_64Scal
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Modes.X86_64.Core
public import VerifiedGarbage.Impl.Seed.X86_64.Modes
public import VerifiedGarbage.Proof.Seed.ModeBytes
import VerifiedGarbage.Proof.Seed.X86_64.EcbCall
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Seed.X86_64.Lit
import VerifiedGarbage.Proof.Modes.X86_64.Fb
import VerifiedGarbage.Proof.Modes.X86_64.Words
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep

/-!
# SEED's core for the modes on x86-64

`dirCoreSpec d`: SEED's core for the direction `d`
(`Impl.Seed.X86_64.dirCore d`) meets what the modes need of a core of
16-byte blocks (`Proof.Modes.X86_64.BlockSpec`, with `bw = 2`), with the key
a schedule, its cipher `Spec.Seed.cipher` for encryption and
`Spec.Seed.invCipher` for decryption, and the key ready when its copy in the
core's slots is the schedule and the 8 bytes below `rsp` are apart from the
slots. `crypt` calls the blocks function of `d` (`WP.call`, with
`Proof.Seed.blocksContract`) on the buffer's sixteen blocks, its return
address stored in the 8 bytes below `rsp`; the scratch buffer's address,
the data's address and the blocks left cross the call in `xmm12` …
`xmm14`, since the callee writes no `xmm` register (`scalCode`).
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Seed.X86_64
open VG.Impl.Aes.X86_64 (sb)
open VG.Proof.Modes (over over_at over_frame)
open VG.Proof.Modes.X86_64 (ScrIn coreRegion blkRegion blkAddr BlockSpec copyN_wp movR_ok addImm_ok movImm_ok
  signExtend_small runBlock_app addr_add stkRegion stkList coreFrame WrIn)
open VG.Spec.Seed (Direction)

/-- The schedule's copy and the buffer, with the scratch buffer at `B`. -/
abbrev schedAddr (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * schedSlot)
abbrev bufAt (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * bufSlot)

/-- The schedule at `rdi`, outside the regions `rs`, and the 8 bytes below
`rsp`, where the core's call stores its return address, apart from `rs`. -/
def ModeKeyArgs (s : State) (rs : List Region) (k : Spec.Seed.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .rdi = p ∧ k = Spec.Seed.scheduleAt s.mem p ∧ (⟨p, 128⟩ : Region) ∈ s.rd ∧
    p.toNat + 128 ≤ 2 ^ 64 ∧ (∀ r ∈ rs, Region.Disjoint ⟨p, 128⟩ r) ∧
    8 ≤ (s.gpr .rsp).toNat ∧ ∀ r ∈ rs, Region.Disjoint (stkRegion (s.gpr .rsp) 8) r

/-- The schedule's copy is `k`, and the 8 bytes below `rsp` are apart from
the scratch buffer. -/
def Ready (s : State) (B : Addr) (k : Spec.Seed.Schedule) : Prop :=
  Spec.Seed.scheduleAt s.mem (schedAddr B) = k ∧ 8 ≤ (s.gpr .rsp).toNat ∧
    Region.Disjoint (stkRegion (s.gpr .rsp) 8) ⟨B, 8 * 192⟩

/-- The core's blocks are two words. -/
@[simp] theorem dirCore_bw (d : Direction) : (dirCore d).bw = 2 := rfl

theorem dirCipher_bytes (d : Direction) (k : Spec.Seed.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (Spec.Aes.bytesAt m p 16) = (cipher d k (Spec.Seed.blockAt m p)).toList := by
  have h : (Vector.ofFn fun i : Fin 16 => (Spec.Aes.bytesAt m p 16).getD i.val 0) = Spec.Seed.blockAt m p := by
    ext i hi; simp [Spec.Aes.bytesAt, Spec.Seed.blockAt]
  cases d <;> simp only [dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher, cipher, h]

/-- The core's slots, its buffer and the schedule's copy. -/
theorem core_eq (d : Direction) (B : Addr) : coreRegion (dirCore d) B = ⟨B, 1472⟩ := by
  simp only [coreRegion, dirCore, schedSlot, bufSlot]
theorem blk_eq (d : Direction) (B : Addr) : blkRegion (dirCore d) B = ⟨B + BitVec.ofNat 64 1088, 256⟩ := by
  simp only [blkRegion, dirCore, bufSlot]
theorem total_eq (d : Direction) : (dirCore d).total = 192 := by
  simp only [dirCore, schedSlot, bufSlot]
theorem stkList_dirCore (d : Direction) (rsp : Addr) : stkList (dirCore d) rsp = [stkRegion rsp 8] := rfl

theorem sched_sub (B : Addr) : Region.Sub ⟨schedAddr B, 128⟩ ⟨B, 1472⟩ := Offset.sub_base B (by decide)
theorem sched_buf (B : Addr) : Region.Disjoint ⟨schedAddr B, 128⟩ ⟨B + BitVec.ofNat 64 1088, 256⟩ :=
  Offset.disjoint B (.inr (by decide)) (by decide) (by decide)
theorem sched_work (B : Addr) : Region.Disjoint ⟨schedAddr B, 128⟩ ⟨B, 1088⟩ :=
  Offset.disjoint_base B (by decide) (by decide)

theorem ready_frame {d : Direction} {s s' : State} {B : Addr} {k : Spec.Seed.Schedule} {rs : List Region}
    (h : Ready s B k) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (blkRegion (dirCore d) B))
    (_ : WrIn rs s s') (hg : ∀ r, r ∉ Proof.Modes.X86_64.modeRegs (dirCore d) → s'.gpr r = s.gpr r) : Ready s' B k := by
  obtain ⟨hk, hst, hsd⟩ := h
  have hsp : s'.gpr .rsp = s.gpr .rsp := hg .rsp (by simp only [Proof.Modes.X86_64.modeRegs, dirCore]; decide)
  refine ⟨?_, by rw [hsp]; exact hst, by rw [hsp]; exact hsd⟩
  rw [scheduleAt_frame hf fun r hr => ?_]
  · exact hk
  rcases hd r hr with h' | h'
  · rw [core_eq] at h'; exact h'.sub_left (sched_sub B)
  · rw [blk_eq] at h'; exact (sched_buf B).sub_right h'

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Seed.Schedule} (h : ModeKeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.rdi, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : ModeKeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis, hst, hsd⟩ := h
  have hsp : s'.gpr .rsp = s.gpr .rsp := hr .rsp (by simp)
  refine ⟨p, by rw [hr .rdi (by simp), hp], ?_, by rw [hrd]; exact hin, hfit, hdis, by rw [hsp]; exact hst,
    by rw [hsp]; exact hsd⟩
  rw [hk]
  exact (scheduleAt_frame hf hdis).symm

theorem prepare_wp (d : Direction) {s : State} {B : Addr} {rs : List Region} {k : Spec.Seed.Schedule}
    (hB : s.gpr sb = B) (hs : ScrIn s B (dirCore d).total) (hR : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs)
    (hk : ModeKeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => Ready s' B k ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .r13 = s.gpr .r13 ∧
      Frame (coreFrame (dirCore d) B (s.gpr .rsp)) s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, rfl, hin, hfit, hdis, hst, hsd⟩ := hk
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hsep : Region.Disjoint ⟨p, 128⟩ ⟨B, 1536⟩ := (hdis _ hR).sub_right (Region.sub_prefix (by rw [total_eq]))
  refine WP.mono (copyN_wp (k := 16) (P := schedAddr B) (Q := p) ⟨by rw [hB], by rw [hp]; simp, by decide,
    by decide, fun w hw => ⟨_, hs.wr, by
      rw [addr_add, total_eq]; exact Offset.contains_base B (by simp only [schedSlot, bufSlot]; omega)
        (by simp only [schedSlot, bufSlot]; omega)⟩,
    fun w hw => ⟨_, List.mem_append_left _ hin, Offset.contains_base p (by omega) (by omega)⟩,
    (hsep.sub_right (Offset.sub_base B (by decide))).symm, by omega⟩) fun s' h => ?_
  have hsp : s'.gpr .rsp = s.gpr .rsp := h.regs .rsp (by decide)
  refine ⟨⟨scheduleAt_congr_at fun i hi => by rw [h.mem, over_at hi (by omega)], by rw [hsp]; exact hst,
      by rw [hsp, ← total_eq d]; exact hsd _ hR⟩,
    by rw [h.regs _ (by decide), hB], hsp, h.regs _ (by decide), h.regs _ (by decide), ?_, h.rd, h.wr⟩
  rw [h.mem]
  exact (over_frame _ _ _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, by rw [core_eq]; exact sched_sub B⟩

/-- Block `j` of blocks transformed by ECB. -/
theorem blockAt_of_ecb {K : Spec.Seed.Schedule} {d : Direction} {m m' : Mem} {D : Addr} {n : Nat}
    (h : Spec.Seed.blocksAt m' D n = Spec.Seed.ecb K d (Spec.Seed.blocksAt m D n)) {j : Nat} (hj : j < n) :
    Spec.Seed.blockAt m' (D + BitVec.ofNat 64 (16 * j)) = cipher d K (Spec.Seed.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  have := congrArg (fun l => l[j]?) h
  cases d <;> simpa [Spec.Seed.blocksAt, Spec.Seed.ecb, cipher, hj] using this

theorem toNat16 : (BitVec.ofNat 64 16).toNat = 16 := rfl

/-- The blocks functions write no `xmm` register. -/
theorem blockCall_scal (d : Direction) : scalCode (blockCall d) = true := by
  cases d <;> lit_decide

theorem crypt_wp (d : Direction) {s : State} {B : Addr} {k : Spec.Seed.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hr : Ready s B k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .r13 = s.gpr .r13 ∧ Ready s' B k ∧
      Frame (coreFrame (dirCore d) B (s.gpr .rsp)) s.mem s'.mem ∧
      (∀ j < (dirCore d).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore d) B j) (8 * (dirCore d).bw) =
        dirCipher d k (Spec.Aes.bytesAt s.mem (blkAddr (dirCore d) B j) (8 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hk, hst, hsd⟩ := hr
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hw := hs.wr
  rw [total_eq] at hw
  -- `sb`, the data's address and the blocks left to `xmm12` … `xmm14`.
  obtain ⟨s₁, e₁, x₁, g₁, m₁, rd₁, wr₁⟩ := Modes.X86_64.movqX_ok s .xmm12 sb
  obtain ⟨s₂, e₂, x₂, g₂, m₂, rd₂, wr₂⟩ := Modes.X86_64.movqX_ok s₁ .xmm13 .r12
  obtain ⟨s₃, e₃, x₃, g₃, m₃, rd₃, wr₃⟩ := Modes.X86_64.movqX_ok s₂ .xmm14 .r13
  have x₃₁₂ : s₃.xmm .xmm12 = (0 : BitVec 64) ++ s.gpr sb := by
    have h₂ : some (s₁.setXmm .xmm13 ((0 : BitVec 64) ++ s₁.gpr .r12)) = some s₂ := e₂
    have h₃ : some (s₂.setXmm .xmm14 ((0 : BitVec 64) ++ s₂.gpr .r13)) = some s₃ := e₃
    rw [← Option.some.inj h₃, RegUpd.xmm_setXmm_of_ne _ _ (by decide), ← Option.some.inj h₂,
      RegUpd.xmm_setXmm_of_ne _ _ (by decide), x₁]
  have x₃₁₃ : s₃.xmm .xmm13 = (0 : BitVec 64) ++ s.gpr .r12 := by
    have h₃ : some (s₂.setXmm .xmm14 ((0 : BitVec 64) ++ s₂.gpr .r13)) = some s₃ := e₃
    rw [← Option.some.inj h₃, RegUpd.xmm_setXmm_of_ne _ _ (by decide), x₂, g₁]
  have x₃₁₄ : s₃.xmm .xmm14 = (0 : BitVec 64) ++ s.gpr .r13 := by rw [x₃, g₂, g₁]
  -- The arguments: `rdi`, `rsi`, `rdx` and `rcx` to the schedule's copy, the buffer, its sixteen blocks and
  -- the working space.
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movR_ok s₃ .rdi sb
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addImm_ok s₄ .rdi (BitVec.ofNat 32 (8 * schedSlot))
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := movR_ok s₅ .rsi sb
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇⟩ := addImm_ok s₆ .rsi (BitVec.ofNat 32 (8 * bufSlot))
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := movImm_ok s₇ .rdx 16
  obtain ⟨s₉, e₉, r₉, o₉, m₉, rd₉, wr₉⟩ := movR_ok s₈ .rcx sb
  have g₉ : ∀ x, x ≠ .rdi → x ≠ .rsi → x ≠ .rdx → x ≠ .rcx → s₉.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [o₉ x h4, o₈ x h3, o₇ x h2, o₆ x h2, o₅ x h1, o₄ x h1, g₃, g₂, g₁]
  have sb₃ : s₃.gpr sb = B := by rw [g₃, g₂, g₁, hB]
  have rdi₉ : s₉.gpr .rdi = schedAddr B := by
    rw [o₉ _ (by decide), o₈ _ (by decide), o₇ _ (by decide), o₆ _ (by decide), r₅, r₄, sb₃,
      signExtend_small (by decide)]
  have rsi₉ : s₉.gpr .rsi = bufAt B := by
    rw [o₉ _ (by decide), o₈ _ (by decide), r₇, r₆, o₅ _ (by decide), o₄ _ (by decide), sb₃,
      signExtend_small (by decide)]
  have rdx₉ : s₉.gpr .rdx = 16 := by rw [o₉ _ (by decide), r₈]
  have rcx₉ : s₉.gpr .rcx = B := by
    rw [r₉, o₈ _ (by decide), o₇ _ (by decide), o₆ _ (by decide), o₅ _ (by decide), o₄ _ (by decide), sb₃]
  have rsp₉ : s₉.gpr .rsp = s.gpr .rsp := g₉ _ (by decide) (by decide) (by decide) (by decide)
  have mem₉ : s₉.mem = s.mem := by rw [m₉, m₈, m₇, m₆, m₅, m₄, m₃, m₂, m₁]
  have rd₉' : s₉.rd = s.rd := by rw [rd₉, rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]
  have wr₉' : s₉.wr = s.wr := by rw [wr₉, wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]
  have xmm₉ : s₉.xmm = s₃.xmm := by
    rw [Modes.X86_64.runBlock_vec (by decide) e₉, Modes.X86_64.runBlock_vec (by decide) e₈,
      Modes.X86_64.runBlock_vec (by decide) e₇, Modes.X86_64.runBlock_vec (by decide) e₆,
      Modes.X86_64.runBlock_vec (by decide) e₅, Modes.X86_64.runBlock_vec (by decide) e₄]
  show WP isa (.seq (.block cryptHead) (.seq (blockCall d) (.block cryptTail))) s _
  refine WP.seq (WP.of_runBlock ⟨s₉, by
    rw [show cryptHead = [.xop (.movq .xmm12 sb)] ++ ([.xop (.movq .xmm13 .r12)] ++ ([.xop (.movq .xmm14 .r13)] ++
      ([Impl.Aes.X86_64.movR .rdi sb] ++ ([.alu .add .rdi (.imm (BitVec.ofNat 32 (8 * schedSlot)))] ++
      ([Impl.Aes.X86_64.movR .rsi sb] ++ ([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * bufSlot)))] ++
      ([.movImm64 .rdx 16] ++ [Impl.Aes.X86_64.movR .rcx sb]))))))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some,
      runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, runBlock_app, e₆, Option.bind_some,
      runBlock_app, e₇, Option.bind_some, runBlock_app, e₈, Option.bind_some, e₉], ?_⟩)
  -- The call.
  have stS : Region.Disjoint (stkRegion (s.gpr .rsp) 8) ⟨B, 1536⟩ := hsd
  have sub : ∀ off len, off + len ≤ 1536 → ∃ r' ∈ s₉.wr, ∃ o,
      (B + BitVec.ofNat 64 off) = r'.base + BitVec.ofNat 64 o ∧ o + len ≤ r'.len :=
    fun off len h => ⟨_, by rw [wr₉']; exact hw, off, rfl, h⟩
  have sub0 : ∃ r' ∈ s₉.wr, ∃ o, B = r'.base + BitVec.ofNat 64 o ∧ o + 1088 ≤ r'.len := by
    obtain ⟨r', h1, o, h2, h3⟩ := sub 0 1088 (by decide)
    exact ⟨r', h1, o, by rw [← h2]; exact (BitVec.add_zero B).symm, h3⟩
  have w : WP isa (blockCall d) s₉ fun s' => (s'.rd = s₉.rd ∧ s'.wr = s₉.wr ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s₉.gpr r) ∧
      Frame [⟨bufAt B, 256⟩, ⟨B, 1088⟩, stkRegion (s.gpr .rsp) 8] s₉.mem s'.mem ∧
      Spec.Seed.blocksAt s'.mem (bufAt B) 16 =
        Spec.Seed.ecb (Spec.Seed.scheduleAt s₉.mem (schedAddr B)) d (Spec.Seed.blocksAt s₉.mem (bufAt B) 16)) ∧
      s'.xmm = s₉.xmm ∧ s'.ymmHi = s₉.ymmHi := by
    refine WP.vecKeep (blockCall_scal d) ?_
    rw [blockCall_eq]
    refine WP.call (k := Proof.Seed.blocksContract abi d) (blocks_verified d).1 (blocks_nosp d)
      (by rw [blocks_depth]; decide) (rd := [⟨schedAddr B, 128⟩]) (wr := [⟨bufAt B, 256⟩, ⟨B, 1088⟩]) ?_
      (Covers.of_sub fun r hr => ?_) (Covers.of_sub fun r hr => ?_)
      (fun s' hrd hwr hcs hf _ hpost => ?_)
    · sig_pre [Proof.Seed.blocksContract, Proof.Seed.blocksSig, abi, argRegs]
      rw [rdi₉, rsi₉, rdx₉, rcx₉, rsp₉, show (16 : BitVec 64).toNat * 16 = 256 from rfl]
      have hfit : ∀ off, off < 1536 → (B + BitVec.ofNat 64 off).toNat = B.toNat + off := fun off h => by
        rw [Offset.toNat_add_ofNat]; omega
      refine ⟨rfl, rfl, sched_buf B, sched_work B, Offset.disjoint_base B (by decide) (by decide),
        stS.sub_right (Offset.sub_base B (by decide)), stS.sub_right (Offset.sub_base B (by decide)),
        stS.sub_right (Region.sub_prefix (by decide)), ?_, ?_, by omega⟩
      · rw [schedAddr, hfit _ (by decide)]; simp only [schedSlot, bufSlot]; omega
      · rw [bufAt, hfit _ (by decide)]; simp only [bufSlot]; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hr
      rcases hr with rfl | rfl | rfl
      · obtain ⟨r', h1, o, h2, h3⟩ := sub (8 * schedSlot) 128 (by decide)
        exact ⟨r', List.mem_append_right _ h1, o, h2, h3⟩
      · obtain ⟨r', h1, o, h2, h3⟩ := sub (8 * bufSlot) 256 (by decide)
        exact ⟨r', List.mem_append_right _ h1, o, h2, h3⟩
      · obtain ⟨r', h1, o, h2, h3⟩ := sub0
        exact ⟨r', List.mem_append_right _ h1, o, h2, h3⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub (8 * bufSlot) 256 (by decide)
      · exact sub0
    · obtain ⟨s₂', hm₂, _, hpost⟩ := hpost
      rw [blocks_depth, rsp₉] at hf
      refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
      sig_reduce [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, abi, argRegs] at hpost
      rw [BitVec.setWidth_eq, rdi₉, rsi₉, rdx₉, show (16 : BitVec 64).toNat = 16 from rfl] at hpost
      have hfr := callEntry_frame' s₉
      rw [State.callEntry_mem, rsp₉] at hfr
      rw [rsp₉] at hpost
      rw [← hm₂, hpost, Proof.Seed.scheduleAt_frame hfr (p := schedAddr B) fun r hr => by
          rw [List.mem_singleton] at hr; subst hr; exact (stS.sub_right (Offset.sub_base B (by decide))).symm,
        Proof.Seed.blocksAt_frame hfr (p := bufAt B) (n := 16) (fun r hr => by
          rw [List.mem_singleton] at hr; subst hr; exact (stS.sub_right (Offset.sub_base B (by decide))).symm)
          (by decide)]
  obtain ⟨t₁₀, s₁₀, e₁₀, ⟨rd₁₀, wr₁₀, cs₁₀, f₁₀, res₁₀⟩, xmm₁₀, -⟩ := w
  refine WP.seq ⟨t₁₀, s₁₀, e₁₀, ?_⟩
  -- The three registers back.
  obtain ⟨u₁, q₁, v₁, p₁, n₁, rdu₁, wru₁, xu₁⟩ := Modes.X86_64.movqR_ok s₁₀ sb .xmm12
  obtain ⟨u₂, q₂, v₂, p₂, n₂, rdu₂, wru₂, xu₂⟩ := Modes.X86_64.movqR_ok u₁ .r12 .xmm13
  obtain ⟨u₃, q₃, v₃, p₃, n₃, rdu₃, wru₃, -⟩ := Modes.X86_64.movqR_ok u₂ .r13 .xmm14
  refine WP.of_runBlock ⟨u₃, by
    rw [show cryptTail = [.movqR sb .xmm12] ++ ([.movqR .r12 .xmm13] ++ [.movqR .r13 .xmm14]) from rfl,
      runBlock_app, q₁, Option.bind_some, runBlock_app, q₂, Option.bind_some, q₃], ?_⟩
  have xx : u₂.xmm = s₃.xmm := by rw [xu₂, xu₁, xmm₁₀, xmm₉]
  have mu : u₃.mem = s₁₀.mem := by rw [n₃, n₂, n₁]
  have rspu : u₃.gpr .rsp = s.gpr .rsp := by
    rw [p₃ _ (by decide), p₂ _ (by decide), p₁ _ (by decide), cs₁₀ .rsp (by decide), rsp₉]
  have fsched : ∀ r ∈ [(⟨bufAt B, 256⟩ : Region), ⟨B, 1088⟩, stkRegion (s.gpr .rsp) 8],
      Region.Disjoint ⟨schedAddr B, 128⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sched_buf B
    · exact sched_work B
    · exact (stS.sub_right (Offset.sub_base B (by decide))).symm
  refine ⟨?_, rspu, ?_, ?_, ⟨?_, by rw [rspu]; exact hst, by rw [rspu]; exact hsd⟩, ?_, fun j hj => ?_,
    by rw [rdu₃, rdu₂, rdu₁, rd₁₀, rd₉'], by rw [wru₃, wru₂, wru₁, wr₁₀, wr₉']⟩
  · rw [p₃ _ (by decide), p₂ _ (by decide), v₁, xmm₁₀, xmm₉, x₃₁₂, Modes.X86_64.extract_zero_append, hB]
  · rw [p₃ _ (by decide), v₂, xu₁, xmm₁₀, xmm₉, x₃₁₃, Modes.X86_64.extract_zero_append]
  · rw [v₃, xx, x₃₁₄, Modes.X86_64.extract_zero_append]
  · rw [mu, scheduleAt_frame f₁₀ fsched, mem₉]; exact hk
  · show Frame (coreRegion (dirCore d) B :: stkList (dirCore d) (s.gpr .rsp)) s.mem u₃.mem
    rw [stkList_dirCore, core_eq, mu, ← mem₉]
    refine f₁₀.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, Offset.sub_base B (by decide)⟩
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · have hj16 : j < 16 := by simp only [dirCore] at hj; exact hj
    have ea : blkAddr (dirCore d) B j = bufAt B + BitVec.ofNat 64 (16 * j) := by
      rw [blkAddr, bufAt, Offset.add_add]; simp only [dirCore, bufSlot]
    rw [dirCore_bw, show 8 * 2 = 16 from rfl, ea, dirCipher_bytes, bytesAt_eq, mu,
      blockAt_of_ecb res₁₀ hj16, mem₉, hk]

/-- SEED's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Direction) : BlockSpec (dirCore d) where
  Key := Spec.Seed.Schedule
  cipher := dirCipher d
  KeyArgs := ModeKeyArgs
  Ready := Ready
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher]
  layout := ⟨by simp only [dirCore]; decide, by simp only [dirCore]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore, schedSlot, bufSlot]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore, schedSlot, bufSlot]; decide⟩
  keyRegs_ok := by simp only [dirCore]; decide
  regs_ok := by simp only [dirCore, Modes.X86_64.regsOk]; decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame := ready_frame
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

end VG.Proof.Seed.X86_64
