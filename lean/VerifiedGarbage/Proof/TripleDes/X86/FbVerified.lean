module

public import VerifiedGarbage.Proof.TripleDes.FbScratch
import VerifiedGarbage.Proof.Modes.X86.Modes
import VerifiedGarbage.Proof.Modes.X86.Wide
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Proof.Modes.X86.Seq
import VerifiedGarbage.Proof.TripleDes.X86.BlockSum
import VerifiedGarbage.Proof.TripleDes.X86.FbLit
public import VerifiedGarbage.Impl.TripleDes.X86.Fb
meta import VerifiedGarbage.Proof.TripleDes.FbScratch
meta import VerifiedGarbage.Proof.Modes.X86.Modes
meta import VerifiedGarbage.Proof.Modes.X86.Wide
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Impl.StackScratch.X86
meta import VerifiedGarbage.Spec.TripleDes.Cfb
meta import VerifiedGarbage.Proof.Modes.X86.Seq
meta import VerifiedGarbage.Proof.TripleDes.X86.BlockSum
meta import VerifiedGarbage.Proof.TripleDes.X86.FbLit
meta import VerifiedGarbage.Impl.TripleDes.X86.Fb
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.TripleDes.X86.Ecb.Verified
public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Impl.TripleDes.X86.Modes
public import VerifiedGarbage.Proof.TripleDes.CbcBlocks
import VerifiedGarbage.Proof.Modes.X86.Ops
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Rc2.X86.Cbc.CallFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.X86.Ecb.Verified
meta import VerifiedGarbage.Proof.Modes.X86.Core
meta import VerifiedGarbage.Impl.TripleDes.X86.Modes
meta import VerifiedGarbage.Proof.TripleDes.CbcBlocks
meta import VerifiedGarbage.Proof.Modes.X86.Ops
meta import VerifiedGarbage.Proof.TripleDes.Schedule
meta import VerifiedGarbage.Proof.TripleDes.Bytes
meta import VerifiedGarbage.Proof.Rc2.X86.Cbc.CallFrame
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit

/-! ### `TripleDes.X86.ModeCore`, which only this module used -/

section

/-!
# Triple DES's core for the modes on x86 (32-bit)

`dirCoreSpec`: Triple DES's core, a block at a time
(`Impl.TripleDes.X86.dirCore`), meets what the modes need of a core
(`Proof.Modes.X86.CoreSpec`), with the key a schedule, read through the
first stack argument, its cipher `Spec.TripleDes.cipher`, and the key ready when the copy of
the schedule in the core's slots is the key. The block function's call
(`cryptCall_ok`) is from its contract (`blockContract`).

`wideCoreSpec d`: the same for the bitsliced core
(`Impl.TripleDes.X86.wideCore d`), whose `crypt` is a call of the bitsliced
function (`Ecb.batchFrame_ok`) on the buffer's 32 blocks.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86.Mode

open VG VG.X86 VG.X86.Wp VG.Impl.TripleDes.X86
open VG.Impl.Modes.X86 (sb at_ argOp slotAt)
open VG.Proof.Modes.X86 (coreRegion blkRegion blkAddr stkRegion slotA CoreSpec Layout ScrIn write4_apply)
open VG.Spec.Aes (bytesAt)
open VG.Spec.TripleDes (Direction)
open VG.Proof.TripleDes (dirCipher bytesAt_eq ofFn_bytesAt scheduleAt_copy scheduleAt_eq_of_frame)
open VG.Proof.Rc2.X86 (addr32)

/-! ## The schedule's copy -/

/-- `W` words from `[ecx + 4 w]` to slot `k + w`. -/
def copyCode (k W : Nat) : List Instr :=
  (List.range W).flatMap fun w => [.mov .eax (.mem (at_ .ecx (4 * w))), .store (slotAt (k + w)) .eax]

theorem copyCode_succ (k W : Nat) :
    copyCode k (W + 1) = copyCode k W ++
      ([.mov .eax (.mem (at_ .ecx (4 * W))), .store (slotAt (k + W)) .eax] : List Instr) := by
  simp [copyCode, List.range_succ]

theorem copyCode_wp {k : Nat} : ∀ (W : Nat) {s : State} {P B : BitVec 32}, s.gpr .ecx = P → s.gpr .edi = B →
    P.toNat + 4 * W ≤ 2 ^ 32 → B.toNat + 4 * (k + W) ≤ 2 ^ 32 →
    (∀ w < W, InRegions (s.rd ++ s.wr) (addr P (4 * w)) 4) → (∀ w < W, InRegions s.wr (addr B (4 * (k + w))) 4) →
    Region.Disjoint ⟨P.setWidth 64, 4 * W⟩ ⟨slotA B k, 4 * W⟩ → ∀ {is : List Instr} {Q : State → Prop},
    (∀ s', (∀ i < 4 * W, s'.mem (slotA B k + BitVec.ofNat 64 i) = s.mem (P.setWidth 64 + BitVec.ofNat 64 i)) →
      Frame [⟨slotA B k, 4 * W⟩] s.mem s'.mem → (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) →
    WP isa (.block (copyCode k W ++ is)) s Q
  | 0, s, _, _, _, _, _, _, _, _, _, _, _, k' => by
    simpa [copyCode] using k' s (fun i hi => by omega_arith) (Frame.refl _ _) (fun _ _ => rfl) rfl rfl
  | W + 1, s, P, B, hc, hd, hP, hB, hr, hw, hdis, is, Q, k' => by
    rw [copyCode_succ, List.append_assoc]
    obtain hdis' : Region.Disjoint ⟨P.setWidth 64, 4 * W⟩ ⟨slotA B k, 4 * W⟩ :=
      (hdis.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith))
    refine copyCode_wp W hc hd (by omega_arith) (by omega_arith) (fun w hw' => hr w (by omega_arith)) (fun w hw' => hw w (by omega_arith))
      hdis' fun s₁ m₁ f₁ g₁ rd₁ wr₁ => ?_
    simp only [List.cons_append]
    obtain hin : InRegions (s₁.rd ++ s₁.wr) (addr P (4 * W)) 4 := by rw [rd₁, wr₁]; exact hr W (by omega_arith)
    refine wp_ldm (by rw [g₁ _ (by decide)]; exact hc) hin fun s₂ u₂ => ?_
    refine wp_stm (B := B) (by rw [u₂.other _ (by decide), g₁ _ (by decide)]; exact hd)
      (by rw [u₂.wr, wr₁]; exact hw W (by omega_arith)) fun s₃ u₃ => ?_
    obtain eP : addr P (4 * W) = P.setWidth 64 + BitVec.ofNat 64 (4 * W) := addr_eq (by omega_arith)
    obtain eB : addr B (4 * (k + W)) = slotA B k + BitVec.ofNat 64 (4 * W) := by
      rw [addr_eq (by omega_arith), VG.Offset.add_add, Nat.mul_add]
    obtain m₃ : s₃.mem = s₁.mem.writeW (slotA B k + BitVec.ofNat 64 (4 * W))
        (s₁.mem.readW (P.setWidth 64 + BitVec.ofNat 64 (4 * W)) 32) := by
      rw [u₃.mem, u₂.mem, u₂.gpr, eP, eB]
    -- The new word's source is not among the copies so far.
    obtain src₁ : ∀ t < 4, s₁.mem (P.setWidth 64 + BitVec.ofNat 64 (4 * W) + BitVec.ofNat 64 t) =
        s.mem (P.setWidth 64 + BitVec.ofNat 64 (4 * W) + BitVec.ofNat 64 t) := fun t ht => by
      rw [VG.Offset.add_add]
      exact f₁.bytes (R := ⟨P.setWidth 64, 4 * (W + 1)⟩) (fun r hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hdis.sub_right (Region.sub_prefix (by omega_arith))) (by show 4 * (W + 1) ≤ 2 ^ 64; omega_arith)
        (by show 4 * W + t < 4 * (W + 1); omega_arith)
    refine k' s₃ (fun i hi => ?_) ?_ (fun r hr' => by rw [u₃.gpr, u₂.other r hr', g₁ r hr'])
      (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁])
    · rw [m₃, write4_apply]
      by_cases h : i < 4 * W
      · rw [ite_eq_right (fun h' => ?_), m₁ i h]
        have := (VG.Offset.lt_iff (slotA B k + BitVec.ofNat 64 i) (slotA B k) (d := 4 * W) (n := 4) (by omega_arith)).mp h'
        rw [VG.Proof.Modes.X86.sub_self_add _ (by omega_arith)] at this
        omega_arith
      · have e : slotA B k + BitVec.ofNat 64 i = slotA B k + BitVec.ofNat 64 (4 * W) + BitVec.ofNat 64 (i - 4 * W) := by
          rw [VG.Offset.add_add (slotA B k) (4 * W) (i - 4 * W), Nat.add_sub_cancel' (by omega_arith)]
        rw [e, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
          ite_eq_left (by omega_arith), ← Mem.readW_byte _ _ (by omega_arith), src₁ _ (by omega_arith), VG.Offset.add_add,
          Nat.add_sub_cancel' (by omega_arith)]
    · rw [m₃]
      obtain hc4 : (⟨slotA B k, 4 * (W + 1)⟩ : Region).Contains (slotA B k + BitVec.ofNat 64 (4 * W)) (32 / 8) :=
        VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
      exact (f₁.sub fun r hr' => ⟨⟨slotA B k, 4 * (W + 1)⟩, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr'; subst hr'; exact Region.sub_prefix (by omega_arith)⟩).writeW
        (List.mem_singleton_self _) _ hc4

/-! ## The key -/

/-- The schedule, at the address in the first stack argument, and that
argument, outside the regions `rs`, as is the core's stack. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.TripleDes.Schedule) : Prop :=
  ∃ p : BitVec 32, InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4 ∧ s.mem.readW (s.ea (argOp 0)) 32 = p ∧
    k = Spec.TripleDes.scheduleAt s.mem (p.setWidth 64) ∧ (⟨p.setWidth 64, 384⟩ : Region) ∈ s.rd ++ s.wr ∧
    p.toNat + 384 ≤ 2 ^ 32 ∧ (∀ r ∈ rs, Region.Disjoint ⟨p.setWidth 64, 384⟩ r) ∧
    (∀ r ∈ rs, Region.Disjoint ⟨s.ea (argOp 0), 4⟩ r) ∧ ∀ r ∈ rs, Region.Disjoint (stkRegion (s.gpr .esp) 16) r

theorem dirCore_total : dirCore.total = 236 := rfl

/-- The schedule's copy is `k`, the core's stack is apart from the scratch
buffer, which does not wrap around. -/
def Ready (s : State) (B : BitVec 32) (k : Spec.TripleDes.Schedule) : Prop :=
  Spec.TripleDes.scheduleAt s.mem (slotA B schedSlot) = k ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨B.setWidth 64, 4 * 236⟩ ∧ B.toNat + 4 * 236 ≤ 2 ^ 32

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.TripleDes.Schedule} (h : KeyArgs s rs k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨p, hin, hp, rfl, hsch, hfit, hdis, hadis, hsdis⟩ := h
  obtain hea : s'.ea (argOp 0) = s.ea (argOp 0) := by
    show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [hesp]
  refine ⟨p, by rw [hrd, hwr, hea]; exact hin, ?_, (scheduleAt_eq_of_frame _ hf hdis).symm,
    by rw [hrd, hwr]; exact hsch, hfit, hdis, by rw [hea]; exact hadis, by rw [hesp]; exact hsdis⟩
  rw [hea, hf.readW (Region.contains_self _ _) hadis (by decide), hp]

theorem ready_frame {s s' : State} {B : BitVec 32} {k : Spec.TripleDes.Schedule}
    {rs : List Region} (h : Ready s B k) (hesp : s'.gpr .esp = s.gpr .esp) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion dirCore B) r ∨ Region.Sub r (blkRegion dirCore B)) :
    Ready s' B k := by
  obtain ⟨hk, hs, hfit⟩ := h
  refine ⟨?_, by rw [hesp]; exact hs, hfit⟩
  rw [scheduleAt_eq_of_frame _ hf fun r hr => ?_]
  · exact hk
  rcases hd r hr with h' | h'
  · exact h'.sub_left (VG.Offset.sub_base _ (by simp only [dirCore, schedSlot, bufSlot]; omega_arith))
  · exact (VG.Offset.disjoint _ (.inr (by simp only [dirCore, schedSlot, bufSlot]; omega_arith)) (by simp only [schedSlot]; omega_arith)
      (by simp only [dirCore, bufSlot]; omega_arith)).sub_right h'

theorem prepare_wp {s : State} {B : BitVec 32} {rs : List Region} {k : Spec.TripleDes.Schedule}
    (hB : s.gpr sb = B) (hs : ScrIn s B dirCore.total)
    (hR : (⟨B.setWidth 64, 4 * dirCore.total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k)
    (_ : dirCore.stack ≤ (s.gpr .esp).toNat) :
    WP isa dirCore.prepare s fun s' => Ready s' B k ∧ s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion dirCore B, stkRegion (s.gpr .esp) dirCore.stack] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hin, hp, rfl, hsch, hfit, hdis, -, hsdis⟩ := hk
  have hfB := hs.fit
  rw [dirCore_total] at hfB
  obtain hsep : Region.Disjoint ⟨p.setWidth 64, 384⟩ ⟨B.setWidth 64, 4 * 236⟩ := hdis _ hR
  have hcopy : copySchedule = [.mov .ecx (.mem (argOp 0))] ++ copyCode schedSlot 96 := rfl
  show WP isa (.block copySchedule) s _
  rw [hcopy, ← List.append_nil (copyCode schedSlot 96), List.singleton_append]
  refine wp_ldm (B := s.gpr .esp) rfl hin fun s₁ u₁ => ?_
  rw [show s.mem.readW (addr (s.gpr .esp) (4 + 4 * 0)) 32 = p from hp] at u₁
  obtain hp64 : ∀ w < 96, addr p (4 * w) = p.setWidth 64 + BitVec.ofNat 64 (4 * w) := fun w hw => addr_eq (by omega_arith)
  refine copyCode_wp (P := p) (B := B) 96 u₁.gpr (by rw [u₁.other _ (by decide)]; exact hB) (by omega_arith) (by simp only [schedSlot]; omega_arith)
    (fun w hw => ?_) (fun w hw => ?_) ?_ fun s₂ m₂ f₂ g₂ rd₂ wr₂ => WP.block_nil ?_
  · rw [u₁.rd, u₁.wr, hp64 w hw]; exact ⟨_, hsch, VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [u₁.wr, addr_eq (by simp only [schedSlot]; omega_arith)]
    obtain hc : (⟨B.setWidth 64, 4 * 236⟩ : Region).Contains
        (B.setWidth 64 + BitVec.ofNat 64 (4 * (schedSlot + w))) 4 :=
      VG.Offset.contains_base _ (by simp only [schedSlot]; omega_arith) (by simp only [schedSlot]; omega_arith)
    have hw' := hs.wr
    rw [dirCore_total] at hw'
    exact ⟨_, hw', hc⟩
  · exact hsep.sub_right (VG.Offset.sub_base _ (by simp only [schedSlot]; omega_arith))
  obtain esp₂ : s₂.gpr .esp = s.gpr .esp := by rw [g₂ _ (by decide), u₁.other _ (by decide)]
  refine ⟨⟨?_, ?_, hfB⟩, by rw [g₂ _ (by decide), u₁.other _ (by decide)]; exact hB, esp₂,
    ?_, by rw [rd₂, u₁.rd], by rw [wr₂, u₁.wr]⟩
  · rw [scheduleAt_copy (p := p.setWidth 64) fun i hi => ?_]
    rw [m₂ i (by omega_arith), u₁.mem]
  · rw [esp₂]; have := hsdis _ hR; rw [dirCore_total] at this; exact this
  · rw [← u₁.mem]
    exact f₂.sub fun r hr => ⟨_, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.sub_base _ (by simp only [dirCore, schedSlot]; omega_arith)⟩

theorem addr32_add {B : BitVec 32} {d : Nat} (h : B.toNat + d < 2 ^ 32) :
    addr32 (B + BitVec.ofNat 32 d) = B.setWidth 64 + BitVec.ofNat 64 d := addr_eq h

theorem toNat_add {B : BitVec 32} {d : Nat} (h : B.toNat + d < 2 ^ 32) : (B + BitVec.ofNat 32 d).toNat = B.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : d < 2 ^ 32), Nat.mod_eq_of_lt h]

/-- The direction's cipher on the 8 bytes at `p` is the block function's result on the block there. -/
theorem dirCipher_bytes (d : Direction) (k : Spec.TripleDes.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (Spec.Aes.bytesAt m p 8) = (VG.Proof.TripleDes.X86.blockResult k d (Spec.TripleDes.blockAt m p)).toList := by
  cases d <;> simp only [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher,
    VG.Proof.TripleDes.X86.blockResult, ofFn_bytesAt]

/-! ## The block function's call -/

/-- Writing back the word read from `a` changes nothing. -/
theorem writeW_readW (m : Mem) (a : Addr) : m.writeW a (m.readW a 32) = m := by
  funext x
  rw [write4_apply]
  split
  · rename_i h
    rw [← Mem.readW_byte m a h, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  · rfl

theorem cryptCall_eq : cryptCall =
    .frame (.push [.eax, .ecx, .edx]) (.call "vg_triple_des_encrypt_block" encryptBlock) (.pop .eax 3) := rfl

/-- The block function's arguments: the schedule at `edx`, the block at
`ecx` and the working space at `eax`. -/
structure CallPre (s : State) : Prop where
  reads : Covers [⟨addr32 (s.gpr .edx), 384⟩, ⟨addr32 (s.gpr .ecx), 8⟩, ⟨addr32 (s.gpr .eax), 512⟩] (s.rd ++ s.wr)
  writes : Covers [⟨addr32 (s.gpr .ecx), 8⟩, ⟨addr32 (s.gpr .eax), 512⟩] s.wr
  keyScratch : (Region.mk (addr32 (s.gpr .edx)) 384).Disjoint ⟨addr32 (s.gpr .eax), 512⟩
  dataScratch : (Region.mk (addr32 (s.gpr .ecx)) 8).Disjoint ⟨addr32 (s.gpr .eax), 512⟩
  keyFit : (s.gpr .edx).toNat + 384 ≤ 2 ^ 32
  dataFit : (s.gpr .ecx).toNat + 8 ≤ 2 ^ 32
  bufFit : (s.gpr .eax).toNat + 512 ≤ 2 ^ 32
  stackLo : 16 ≤ (s.gpr .esp).toNat
  stackKey : (below (s.gpr .esp) 16).Disjoint ⟨addr32 (s.gpr .edx), 384⟩
  stackData : (below (s.gpr .esp) 16).Disjoint ⟨addr32 (s.gpr .ecx), 8⟩
  stackBuf : (below (s.gpr .esp) 16).Disjoint ⟨addr32 (s.gpr .eax), 512⟩

structure CallPost (s s' : State) : Prop where
  callee : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨addr32 (s.gpr .ecx), 8⟩, ⟨addr32 (s.gpr .eax), 512⟩, below (s.gpr .esp) 16] s.mem s'.mem
  output : Spec.TripleDes.blockAt s'.mem (addr32 (s.gpr .ecx)) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (addr32 (s.gpr .edx))) .encrypt
      (Spec.TripleDes.blockAt s.mem (addr32 (s.gpr .ecx)))

theorem cryptCall_ok (s : State) (hp : CallPre s) : WP isa cryptCall s (CallPost s) := by
  rw [cryptCall_eq]
  let rs : List Reg := [.eax, .ecx, .edx]
  obtain hrs : .esp ∉ rs := by decide
  have fit : 4 * rs.length + 4 ≤ (s.gpr .esp).toNat := hp.stackLo
  let sE := (pushed rs s).callEntry
  obtain a0 : arg sE 0 = s.gpr .edx := by rw [callEntry_arg fit hrs (by decide)]; rfl
  obtain a1 : arg sE 1 = s.gpr .ecx := by rw [callEntry_arg fit hrs (by decide)]; rfl
  obtain a2 : arg sE 2 = s.gpr .eax := by rw [callEntry_arg fit hrs (by decide)]; rfl
  obtain eA : argAddr sE 0 = ((s.gpr .esp) - BitVec.ofNat 32 12).setWidth 64 := by rw [callEntry_argAddr0]; rfl
  obtain eSp : sE.gpr .esp = s.gpr .esp - BitVec.ofNat 32 16 := by rw [callEntry_esp']; rfl
  obtain b12 : Region.Sub (below (s.gpr .esp) 12) (below (s.gpr .esp) 16) := below_sub (by decide) hp.stackLo
  obtain r4 : Region.Sub ⟨((s.gpr .esp) - BitVec.ofNat 32 16).setWidth 64, 4⟩ (below (s.gpr .esp) 16) :=
    Region.sub_prefix (by decide)
  refine VG.Proof.Rc2.X86.Cbc.callWithGpr (c := encryptBlock) (k := blockContract)
    encBlock_correct Ecb.block_nosp (by decide) hrs
    (by rw [Ecb.block_stack]; exact hp.stackLo) (rd := [⟨addr32 (s.gpr .edx), 384⟩, ⟨argAddr sE 0, 12⟩])
    (wr := [⟨addr32 (s.gpr .ecx), 8⟩, ⟨addr32 (s.gpr .eax), 512⟩]) ⟨?_, ?_, ?_⟩ ?_
  · change blockContract.pre (sE.withRegions _ _)
    simp only [blockContract, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp]
    refine ⟨trivial, trivial, hp.keyScratch, hp.dataScratch, hp.stackData.sub_left b12,
      hp.stackBuf.sub_left b12, hp.stackData.sub_left r4, hp.stackBuf.sub_left r4,
      hp.keyFit, hp.dataFit, hp.bufFit, ?_⟩
    rw [sub_toNat hp.stackLo]
    have := (s.gpr .esp).isLt
    omega_arith
  · intro a n ⟨r, hr, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
    · apply InRegions_append_cons.mpr
      left
      rw [eA] at hc
      exact hc
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hp.writes a n h
    exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩
  · intro s' rd wr cs frame ⟨s₂, mem₂, gpr₂, post⟩
    rw [Ecb.block_stack] at frame
    change blockContract.post (sE.withRegions _ _) s₂ at post
    simp only [blockContract, State.withRegions_mem, arg_withRegions, a0, a1] at post
    obtain stackFrame := callEntry_frame fit hrs
    change Frame [below (s.gpr .esp) 16] s.mem sE.mem at stackFrame
    obtain m16 : Frame [below (s.gpr .esp) 16] s₂.mem s'.mem :=
      Frame.below_mono (wr := []) mem₂ (by decide) hp.stackLo
    refine ⟨cs, rd, wr, frame, ?_⟩
    rw [VG.Proof.TripleDes.blockAt_eq_of_frame (p := addr32 (s.gpr .ecx)) m16
        (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hp.stackData.symm), post,
      VG.Proof.TripleDes.scheduleAt_eq_of_frame (p := addr32 (s.gpr .edx)) stackFrame
        (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hp.stackKey.symm),
      VG.Proof.TripleDes.blockAt_eq_of_frame (p := addr32 (s.gpr .ecx)) stackFrame
        (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hp.stackData.symm)]

theorem crypt_wp {s : State} {B : BitVec 32} {k : Spec.TripleDes.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B dirCore.total) (hr : Ready s B k) (hst : dirCore.stack ≤ (s.gpr .esp).toNat) :
    WP isa dirCore.crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ Ready s' B k ∧
      Frame [coreRegion dirCore B, stkRegion (s.gpr .esp) dirCore.stack] s.mem s'.mem ∧
      (∀ j < dirCore.G, bytesAt s'.mem (blkAddr dirCore B j) (4 * dirCore.bw) =
        dirCipher .encrypt k (bytesAt s.mem (blkAddr dirCore B j) (4 * dirCore.bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hk, hstk, hfB⟩ := hr
  have hw := hs.wr
  rw [dirCore_total] at hw
  have hst' : 16 ≤ (s.gpr .esp).toNat := hst
  have hB' : s.gpr .edi = B := hB
  obtain slotIn : ∀ o, o + 4 ≤ 4 * 236 → (⟨B.setWidth 64, 4 * 236⟩ : Region).Contains (addr B o) 4 := fun o h => by
    rw [addr_eq (by omega_arith)]; exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
  show WP isa (.seq (.block cryptSetup) (.seq cryptCall (.block cryptDone))) s _
  refine WP.seq ?_
  refine wp_ldm (b := .edi) (o := 4 * dSlot) hB' ⟨_, List.mem_append_right _ hw, slotIn _ (by simp only [dSlot, schedSlot]; omega_arith)⟩
    fun s₁ u₁ => wp_ldm (b := .edi) (o := 4 * nSlot) ((u₁.other _ (by decide)).trans hB')
      (by rw [u₁.rd, u₁.wr]; exact ⟨_, List.mem_append_right _ hw, slotIn _ (by simp only [nSlot, schedSlot]; omega_arith)⟩)
    fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => wp_mov fun s₆ u₆ =>
      wp_addi fun s₇ u₇ => WP.block_nil ?_
  obtain edi₇ : s₇.gpr .edi = B := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact hB'
  obtain esi₇ : s₇.gpr .esi = s.mem.readW (addr B (4 * dSlot)) 32 := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  obtain ebp₇ : s₇.gpr .ebp = s.mem.readW (addr B (4 * nSlot)) 32 := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.mem]
  obtain eax₇ : s₇.gpr .eax = B := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]; exact hB'
  obtain ecx₇ : s₇.gpr .ecx = B + BitVec.ofNat 32 512 := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hB]; rfl
  obtain edx₇ : s₇.gpr .edx = B + BitVec.ofNat 32 520 := by
    rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hB]; rfl
  obtain esp₇ : s₇.gpr .esp = s.gpr .esp := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain rd₇ : s₇.rd = s.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₇ : s₇.wr = s.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain aK : addr32 (s₇.gpr .edx) = B.setWidth 64 + BitVec.ofNat 64 520 := by rw [edx₇]; exact addr32_add (by omega_arith)
  obtain aD : addr32 (s₇.gpr .ecx) = B.setWidth 64 + BitVec.ofNat 64 512 := by rw [ecx₇]; exact addr32_add (by omega_arith)
  obtain aW : addr32 (s₇.gpr .eax) = B.setWidth 64 := by rw [eax₇]; rfl
  obtain scrSub : ∀ (off n : Nat), off + n ≤ 4 * 236 → ∃ r' ∈ s₇.wr, ∃ o,
      (B.setWidth 64 + BitVec.ofNat 64 off) = r'.base + BitVec.ofNat 64 o ∧ o + n ≤ r'.len :=
    fun off n h => ⟨_, by rw [wr₇]; exact hw, off, rfl, h⟩
  obtain e0 : B.setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 0 := by simp
  obtain hpre : CallPre s₇ := by
    refine ⟨Covers.right (Covers.of_sub fun r hr => ?_), Covers.of_sub fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [aK]; exact scrSub 520 384 (by omega_arith)
      · rw [aD]; exact scrSub 512 8 (by omega_arith)
      · rw [aW, e0]; exact scrSub 0 512 (by omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [aD]; exact scrSub 512 8 (by omega_arith)
      · rw [aW, e0]; exact scrSub 0 512 (by omega_arith)
    · rw [aK, aW]; exact VG.Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · rw [aD, aW]; exact VG.Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · rw [edx₇, toNat_add (by omega_arith)]; omega_arith
    · rw [ecx₇, toNat_add (by omega_arith)]; omega_arith
    · rw [eax₇]; omega_arith
    · rw [esp₇]; exact hst'
    · rw [esp₇, aK]; exact hstk.sub_right (VG.Offset.sub_base _ (by omega_arith))
    · rw [esp₇, aD]; exact hstk.sub_right (VG.Offset.sub_base _ (by omega_arith))
    · rw [esp₇, aW]; exact hstk.sub_right (Region.sub_prefix (by omega_arith))
  refine WP.seq (WP.mono (cryptCall_ok s₇ hpre) fun s' hc => ?_)
  have hfr := hc.mem
  rw [aD, aW, esp₇, m₇] at hfr
  obtain sb' : s'.gpr .edi = B := (hc.callee .edi (by decide)).trans edi₇
  obtain esp' : s'.gpr .esp = s.gpr .esp := (hc.callee .esp (by decide)).trans esp₇
  obtain wr' : s'.wr = s.wr := hc.wr.trans wr₇
  obtain outSlot : ∀ o, 520 + 384 ≤ o → o + 4 ≤ 4 * 236 →
      ∀ r ∈ [(⟨B.setWidth 64 + BitVec.ofNat 64 512, 8⟩ : Region), ⟨B.setWidth 64, 512⟩, below (s.gpr .esp) 16],
        Region.Disjoint ⟨addr B o, 4⟩ r := fun o h₁ h₂ r hr => by
    rw [addr_eq (by omega_arith)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact VG.Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact (hstk.sub_right (VG.Offset.sub_base _ (by omega_arith))).symm
  obtain keepD : s'.mem.readW (addr B (4 * dSlot)) 32 = s.mem.readW (addr B (4 * dSlot)) 32 :=
    hfr.readW (Region.contains_self _ _) (outSlot _ (by simp only [dSlot, schedSlot]; omega_arith)
      (by simp only [dSlot, schedSlot]; omega_arith)) (by decide)
  obtain keepN : s'.mem.readW (addr B (4 * nSlot)) 32 = s.mem.readW (addr B (4 * nSlot)) 32 :=
    hfr.readW (Region.contains_self _ _) (outSlot _ (by simp only [nSlot, schedSlot]; omega_arith)
      (by simp only [nSlot, schedSlot]; omega_arith)) (by decide)
  obtain inD : InRegions s.wr (addr B (4 * dSlot)) 4 := ⟨_, hw, slotIn _ (by simp only [dSlot, schedSlot]; omega_arith)⟩
  obtain inN : InRegions s.wr (addr B (4 * nSlot)) 4 := ⟨_, hw, slotIn _ (by simp only [nSlot, schedSlot]; omega_arith)⟩
  refine wp_stm (b := .edi) (B := B) (o := 4 * dSlot) sb' (wr' ▸ inD) fun s₈ u₈ => ?_
  refine wp_stm (b := .edi) (B := B) (o := 4 * nSlot) ((congrFun u₈.gpr _).trans sb')
    ((u₈.wr.trans wr') ▸ inN) fun s₉ u₉ => WP.block_nil ?_
  obtain m₉ : s₉.mem = s'.mem := by
    rw [u₉.mem, u₈.gpr, u₈.mem, hc.callee .esi (by decide), hc.callee .ebp (by decide), esi₇, ebp₇, ← keepD,
      writeW_readW, ← keepN, writeW_readW]
  obtain g₉ : ∀ r, s₉.gpr r = s'.gpr r := fun r => by rw [u₉.gpr, u₈.gpr]
  obtain copyOut : ∀ r ∈ [(⟨B.setWidth 64 + BitVec.ofNat 64 512, 8⟩ : Region), ⟨B.setWidth 64, 512⟩, below (s.gpr .esp) 16],
      Region.Disjoint ⟨slotA B schedSlot, 384⟩ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Offset.disjoint _ (.inr (by simp only [schedSlot]; omega_arith)) (by simp only [schedSlot]; omega_arith) (by omega_arith)
    · exact VG.Offset.disjoint_base _ (by simp only [schedSlot]; omega_arith) (by simp only [schedSlot]; omega_arith)
    · exact (hstk.sub_right (VG.Offset.sub_base _ (by simp only [schedSlot]; omega_arith))).symm
  refine ⟨by rw [g₉]; exact sb', by rw [g₉]; exact esp', ⟨?_, by rw [g₉, esp']; exact hstk, hfB⟩, ?_, fun j hj => ?_,
    by rw [u₉.rd, u₈.rd, hc.rd, rd₇], by rw [u₉.wr, u₈.wr, wr']⟩
  · rw [m₉, scheduleAt_eq_of_frame _ hfr copyOut]; exact hk
  · rw [m₉]
    refine hfr.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, VG.Offset.sub_base _ (by simp only [dirCore, schedSlot]; omega_arith)⟩
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by simp only [dirCore, schedSlot]; omega_arith)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · have hj0 : j = 0 := by simp only [dirCore] at hj; omega_arith
    subst hj0
    obtain eB : blkAddr dirCore B 0 = B.setWidth 64 + BitVec.ofNat 64 512 := by
      simp [blkAddr, slotA, dirCore, bufSlot]
    have ho := hc.output
    rw [aD, aK, m₇] at ho
    rw [m₉, show 4 * dirCore.bw = 8 from rfl, eB, bytesAt_eq, ho, dirCipher_bytes,
      show B.setWidth 64 + BitVec.ofNat 64 520 = slotA B schedSlot from rfl, hk]

/-- The core's blocks are two words. -/
@[simp] theorem dirCore_bw : dirCore.bw = 2 := rfl

/-- Triple DES's core, a block at a time, meets what the modes need. -/
def dirCoreSpec : CoreSpec dirCore where
  Key := Spec.TripleDes.Schedule
  cipher := dirCipher .encrypt
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len _ _ := by simp [dirCipher, Spec.TripleDes.cipher]
  layout := ⟨by simp only [dirCore]; decide, .inl rfl, by simp only [dirCore, schedSlot, bufSlot]; omega_arith,
    by simp only [dirCore]; omega_arith⟩
  keyArgs_congr h e r w _ f := keyArgs_congr h e r w f
  ready_frame h hesp _ _ _ hf _ hd := ready_frame h hesp hf hd
  prepare_wp := prepare_wp
  crypt_wp := crypt_wp

/-! ## The bitsliced core -/

open VG.Proof.TripleDes.Bitslice (blockOut)

theorem wideCore_total (d : Direction) : (wideCore d).total = 302 := rfl

/-- The schedule's copy is `k`, the core's stack is apart from the scratch
buffer, which does not wrap around. -/
def ReadyW (s : State) (B : BitVec 32) (k : Spec.TripleDes.Schedule) : Prop :=
  Spec.TripleDes.scheduleAt s.mem (slotA B wideSchedSlot) = k ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨B.setWidth 64, 4 * 302⟩ ∧ B.toNat + 4 * 302 ≤ 2 ^ 32

theorem readyW_frame {d : Direction} {s s' : State} {B : BitVec 32} {k : Spec.TripleDes.Schedule}
    {rs : List Region} (h : ReadyW s B k) (hesp : s'.gpr .esp = s.gpr .esp) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (wideCore d) B) r ∨ Region.Sub r (blkRegion (wideCore d) B)) :
    ReadyW s' B k := by
  obtain ⟨hk, hs, hfit⟩ := h
  refine ⟨?_, by rw [hesp]; exact hs, hfit⟩
  rw [scheduleAt_eq_of_frame _ hf fun r hr => ?_]
  · exact hk
  rcases hd r hr with h' | h'
  · exact h'.sub_left (VG.Offset.sub_base _ (by simp only [wideCore, wideSchedSlot]; decide))
  · exact (VG.Offset.disjoint _ (.inr (by simp only [wideCore, wideSchedSlot, Bitslice.bufSlot]; decide))
      (by simp only [wideSchedSlot]; decide) (by simp only [wideCore, Bitslice.bufSlot]; decide)).sub_right h'

theorem prepareW_wp (d : Direction) {s : State} {B : BitVec 32} {rs : List Region} {k : Spec.TripleDes.Schedule}
    (hB : s.gpr sb = B) (hs : ScrIn s B (wideCore d).total)
    (hR : (⟨B.setWidth 64, 4 * (wideCore d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k)
    (_ : (wideCore d).stack ≤ (s.gpr .esp).toNat) :
    WP isa (wideCore d).prepare s fun s' => ReadyW s' B k ∧ s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion (wideCore d) B, stkRegion (s.gpr .esp) (wideCore d).stack] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hin, hp, rfl, hsch, hfit, hdis, -, hsdis⟩ := hk
  have hfB := hs.fit
  rw [wideCore_total] at hfB
  obtain hsep : Region.Disjoint ⟨p.setWidth 64, 384⟩ ⟨B.setWidth 64, 4 * 302⟩ := hdis _ hR
  have hcopy : copyScheduleWide = [.mov .ecx (.mem (argOp 0))] ++ copyCode wideSchedSlot 96 := rfl
  show WP isa (.block copyScheduleWide) s _
  rw [hcopy, ← List.append_nil (copyCode wideSchedSlot 96), List.singleton_append]
  refine wp_ldm (B := s.gpr .esp) rfl hin fun s₁ u₁ => ?_
  rw [show s.mem.readW (addr (s.gpr .esp) (4 + 4 * 0)) 32 = p from hp] at u₁
  obtain hp64 : ∀ w < 96, addr p (4 * w) = p.setWidth 64 + BitVec.ofNat 64 (4 * w) := fun w hw => addr_eq (by omega_arith)
  have hS : wideSchedSlot = 196 := rfl
  refine copyCode_wp (P := p) (B := B) 96 u₁.gpr (by rw [u₁.other _ (by decide)]; exact hB) (by omega_arith)
    (by rw [hS]; omega_arith) (fun w hw => ?_) (fun w hw => ?_) ?_ fun s₂ m₂ f₂ g₂ rd₂ wr₂ => WP.block_nil ?_
  · rw [u₁.rd, u₁.wr, hp64 w hw]; exact ⟨_, hsch, VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [u₁.wr, addr_eq (by rw [hS]; omega_arith)]
    obtain hc : (⟨B.setWidth 64, 4 * 302⟩ : Region).Contains
        (B.setWidth 64 + BitVec.ofNat 64 (4 * (wideSchedSlot + w))) 4 :=
      VG.Offset.contains_base _ (by rw [hS]; omega_arith) (by rw [hS]; omega_arith)
    have hw' := hs.wr
    rw [wideCore_total] at hw'
    exact ⟨_, hw', hc⟩
  · exact hsep.sub_right (VG.Offset.sub_base _ (by rw [hS]; omega_arith))
  obtain esp₂ : s₂.gpr .esp = s.gpr .esp := by rw [g₂ _ (by decide), u₁.other _ (by decide)]
  refine ⟨⟨?_, ?_, hfB⟩, by rw [g₂ _ (by decide), u₁.other _ (by decide)]; exact hB, esp₂,
    ?_, by rw [rd₂, u₁.rd], by rw [wr₂, u₁.wr]⟩
  · rw [scheduleAt_copy (p := p.setWidth 64) fun i hi => ?_]
    rw [m₂ i (by omega_arith), u₁.mem]
  · rw [esp₂]; have := hsdis _ hR; rw [wideCore_total] at this; exact this
  · rw [← u₁.mem]
    exact f₂.sub fun r hr => ⟨_, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.sub_base _ (by simp only [wideCore, wideSchedSlot]; decide)⟩

theorem wideCall_eq (d : Direction) : wideCall d =
    .frame (.push [.eax, .edi])
      (.call (match d with | .encrypt => "vg_triple_des_encrypt_batch" | .decrypt => "vg_triple_des_decrypt_batch")
        (Ecb.batchCode d)) (.pop .eax 2) := by cases d <;> rfl

/-- The bitsliced function's result on a block is the direction's. -/
theorem blockOut_eq (d : Direction) (k : Spec.TripleDes.Schedule) (b : Spec.TripleDes.Block) :
    blockOut k d b = VG.Proof.TripleDes.X86.blockResult k d b := by cases d <;> rfl

theorem cryptW_wp (d : Direction) {s : State} {B : BitVec 32} {k : Spec.TripleDes.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (wideCore d).total) (hr : ReadyW s B k) (hst : (wideCore d).stack ≤ (s.gpr .esp).toNat) :
    WP isa (wideCore d).crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ ReadyW s' B k ∧
      Frame [coreRegion (wideCore d) B, stkRegion (s.gpr .esp) (wideCore d).stack] s.mem s'.mem ∧
      (∀ j < (wideCore d).G, bytesAt s'.mem (blkAddr (wideCore d) B j) (4 * (wideCore d).bw) =
        dirCipher d k (bytesAt s.mem (blkAddr (wideCore d) B j) (4 * (wideCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hk, hstk, hfB⟩ := hr
  have hw := hs.wr
  rw [wideCore_total] at hw
  have hst' : 16 ≤ (s.gpr .esp).toNat := hst
  have hB' : s.gpr .edi = B := hB
  show WP isa (.seq (.block wideSetup) (wideCall d)) s _
  refine WP.seq ?_
  show WP isa (.block [.mov .eax (.reg .edi), .alu .add .eax (.imm (BitVec.ofNat 32 784))]) s _
  refine wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => WP.block_nil ?_
  obtain edi₂ : s₂.gpr .edi = B := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hB'
  obtain eax₂ : s₂.gpr .eax = B + BitVec.ofNat 32 784 := by rw [u₂.gpr, u₁.gpr, hB']
  obtain esp₂ : s₂.gpr .esp = s.gpr .esp := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  obtain rd₂ : s₂.rd = s.rd := by rw [u₂.rd, u₁.rd]
  obtain wr₂ : s₂.wr = s.wr := by rw [u₂.wr, u₁.wr]
  obtain aK : addr32 (s₂.gpr .eax) = B.setWidth 64 + BitVec.ofNat 64 784 := by
    rw [eax₂]; exact addr32_add (by omega_arith)
  obtain aW : addr32 (s₂.gpr .edi) = B.setWidth 64 := by rw [edi₂]; rfl
  obtain scrSub : ∀ (off n : Nat), off + n ≤ 4 * 302 → ∃ r' ∈ s₂.wr, ∃ o,
      (B.setWidth 64 + BitVec.ofNat 64 off) = r'.base + BitVec.ofNat 64 o ∧ o + n ≤ r'.len :=
    fun off n h => ⟨_, by rw [wr₂]; exact hw, off, rfl, h⟩
  obtain e0 : B.setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 0 := by simp
  obtain b12 : Region.Sub (below (s.gpr .esp) 16) (stkRegion (s.gpr .esp) 16) := below_sub (by decide) hst'
  obtain hpre : Ecb.BatchCallPre .eax .edi s₂ := by
    refine ⟨Covers.right (Covers.of_sub fun r hr => ?_), Covers.of_sub fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [aK]; exact scrSub 784 384 (by omega_arith)
      · rw [aW, e0]; exact scrSub 0 784 (by omega_arith)
    · obtain rfl := List.mem_singleton.mp hr
      rw [aW, e0]; exact scrSub 0 784 (by omega_arith)
    · rw [aK, aW]; exact VG.Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · rw [eax₂, toNat_add (by omega_arith)]; omega_arith
    · rw [edi₂]; omega_arith
    · rw [esp₂]; omega_arith
    · rw [esp₂, aK]; exact (hstk.sub_left b12).sub_right (VG.Offset.sub_base _ (by omega_arith))
    · rw [esp₂, aW]; exact (hstk.sub_left b12).sub_right (Region.sub_prefix (by omega_arith))
  rw [wideCall_eq]
  refine WP.mono (Ecb.batchFrame_ok d (by decide) (by decide) s₂ hpre) fun s' hc => ?_
  have hfr := hc.mem
  rw [aW, esp₂, m₂] at hfr
  have hblk := hc.blocks
  rw [edi₂, aK, m₂] at hblk
  obtain copyOut : ∀ r ∈ [(⟨B.setWidth 64, 784⟩ : Region), below (s.gpr .esp) 16],
      Region.Disjoint ⟨slotA B wideSchedSlot, 384⟩ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Offset.disjoint_base _ (by simp only [wideSchedSlot]; decide) (by simp only [wideSchedSlot]; decide)
    · exact ((hstk.sub_left b12).sub_right (VG.Offset.sub_base _ (by simp only [wideSchedSlot]; decide))).symm
  refine ⟨(hc.callee .edi (by decide)).trans edi₂, (hc.callee .esp (by decide)).trans esp₂,
    ⟨?_, by rw [(hc.callee .esp (by decide)).trans esp₂]; exact hstk, hfB⟩, ?_, fun j hj => ?_,
    hc.rd.trans rd₂, hc.wr.trans wr₂⟩
  · rw [scheduleAt_eq_of_frame _ hfr copyOut]; exact hk
  · refine hfr.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by simp only [wideCore, wideSchedSlot]; decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, b12⟩
  · have hj32 : j < 32 := hj
    obtain eB : blkAddr (wideCore d) B j = VG.X86.Straight.wordAddr B (Bitslice.bufSlot + 2 * j) := by
      rw [VG.X86.Straight.wordAddr, addr_eq (by unfold Bitslice.bufSlot; omega_arith)]
      simp only [blkAddr, slotA, wideCore, VG.Offset.add_add]
      exact congrArg (fun t => B.setWidth 64 + BitVec.ofNat 64 t) (by omega_arith)
    rw [show 4 * (wideCore d).bw = 8 from rfl, eB, bytesAt_eq, hblk j hj32, dirCipher_bytes, blockOut_eq,
      show B.setWidth 64 + BitVec.ofNat 64 784 = slotA B wideSchedSlot from rfl, hk]

@[simp] theorem wideCore_bw (d : Direction) : (wideCore d).bw = 2 := rfl

/-- Triple DES's bitsliced core for the direction `d` meets what the modes need. -/
def wideCoreSpec (d : Direction) : CoreSpec (wideCore d) where
  Key := Spec.TripleDes.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready := ReadyW
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher]
  layout := ⟨by simp only [wideCore]; decide, .inl rfl, by simp only [wideCore, wideSchedSlot, Bitslice.bufSlot]; decide,
    by simp only [wideCore]; omega_arith⟩
  keyArgs_congr h e r w _ f := keyArgs_congr h e r w f
  ready_frame h hesp _ _ _ hf _ hd := readyW_frame h hesp hf hd
  prepare_wp := prepareW_wp d
  crypt_wp := cryptW_wp d

end VG.Proof.TripleDes.X86.Mode

end

end

/-!
# Triple DES-OFB, -CFB64 and -CFB8 on x86 (32-bit) meet their contracts

`ofb_wp`, `cfbEncrypt_wp`, … : the modes' OFB, CFB and CFB8
(`Proof.Modes.X86.ofb_wp`, …) over Triple DES's core in the encryption
direction (`Mode.dirCoreSpec .encrypt`), with the working space as a fifth
argument (`fbX86`, whose data is `st` bytes a step: 8, or 1 for CFB8, and
whose working space is `w` doublewords: 118, or 151 for the bitsliced core,
`Mode.wideCoreSpec`, which CFB64 decryption takes by groups of blocks,
`Proof.Modes.X86.cfbDecLevels_wp`). The
chaining value is written back, so it is writable, and the taint analysis
knows the argument words holding the addresses of the data, the chaining
value and the scratch buffer as the base addresses of the writable regions,
with room for the block function's call below `esp`. The `_framed` theorems
run them with their working space on the stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86.Cbc

open VG VG.X86 VG.Impl.TripleDes.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (stkRegion)
open VG.Proof.TripleDes (bytesAt_eq)

theorem scr_eq (s : State) :
    Modes.X86.scrR s dirCore = ⟨(arg s 4).setWidth 64, 8 * 118⟩ := by
  simp [Modes.X86.scrR, dirCore, schedSlot]

theorem scrW_eq (s : State) (d : Spec.TripleDes.Direction) :
    Modes.X86.scrR s (wideCore d) = ⟨(arg s 4).setWidth 64, 8 * 151⟩ := by
  simp [Modes.X86.scrR, wideCore, wideSchedSlot, Bitslice.wsWords]

/-- The data in blocks, as the modes' steps. -/
theorem cbcBlocksAt_eq (m : Mem) (p : Addr) (n : Nat) :
    Spec.TripleDes.cbcBlocksAt m p n = Proof.Modes.chunksAt 8 m p n := by
  simp only [Spec.TripleDes.cbcBlocksAt, Spec.TripleDes.blocksAt, Proof.Modes.chunksAt, List.map_map]
  exact List.map_congr_left fun i _ => (bytesAt_eq m _).symm

/-- The stack below `esp` is apart from the arguments and the return address. -/
theorem stk_apart {s : State} (hfit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32) (hlo : 16 ≤ (s.gpr .esp).toNat) :
    Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨argAddr s 0, 20⟩ ∧
      Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
  have e : (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16 :=
    VG.X86.Taint.sub_setWidth hlo
  have ea : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega_arith)
  refine ⟨?_, ?_⟩
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩ _
    rw [e, ea]; exact VG.Offset.disjoint_below_above _ (by decide)
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩ _
    have := VG.Offset.disjoint_below_above ((s.gpr .esp).setWidth 64) (m := 16) (a := 0) (l := 4) (by decide)
    rw [BitVec.add_zero] at this
    rw [e]; exact this

end VG.Proof.TripleDes.X86.Cbc

namespace VG.Proof.TripleDes.X86.Fb

open VG VG.X86 VG.Impl.TripleDes.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (SeqPre stkRegion ofb_wp cfbEnc_wp cfbDecLevels_wp cfb8Enc_wp cfb8Dec_wp)
open VG.Proof.TripleDes.X86.Mode (dirCoreSpec wideCoreSpec KeyArgs)
open VG.Proof.TripleDes.X86.Cbc (scr_eq scrW_eq stk_apart cbcBlocksAt_eq)

/-- Triple DES under the schedule at the first argument. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher :=
  Spec.TripleDes.cipher (Spec.TripleDes.scheduleAt s.mem ((arg s 0).setWidth 64))
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.TripleDes.bytesAt m ((arg s 1).setWidth 64) 8
/-- The data, in blocks. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) :=
  Spec.TripleDes.cbcBlocksAt m ((arg s 2).setWidth 64) (arg s 3).toNat
/-- The data, in bytes. -/
abbrev bytesOf (m : Mem) (s : State) : List Byte := Spec.TripleDes.bytesAt m ((arg s 2).setWidth 64) (arg s 3).toNat

/-- The functions' postconditions. -/
def ofbPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ofb.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ofb.next (ciph s) (ivAt s.mem s) (arg s 3).toNat
def cfbEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cfbDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)
def cfb8EncPost (s s' : State) : Prop :=
  bytesOf s'.mem s = Spec.Cfb8.encrypt (ciph s) (ivAt s.mem s) (bytesOf s.mem s) ∧
    ivAt s'.mem s = Spec.Cfb8.next (ivAt s.mem s) (Spec.Cfb8.encrypt (ciph s) (ivAt s.mem s) (bytesOf s.mem s))
def cfb8DecPost (s s' : State) : Prop :=
  bytesOf s'.mem s = Spec.Cfb8.decrypt (ciph s) (ivAt s.mem s) (bytesOf s.mem s) ∧
    ivAt s'.mem s = Spec.Cfb8.next (ivAt s.mem s) (bytesOf s.mem s)

/-- OFB, CFB64 or CFB8 on x86 with its working space, `w` doublewords, as
the fifth argument, `st` bytes of data a step, and the postcondition `post`. -/
def fbX86 (w st : Nat) (post : State → State → Prop) : Contract X86.isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, 384⟩
    let iv : Region := ⟨(arg s 1).setWidth 64, 8⟩
    let data : Region := ⟨(arg s 2).setWidth 64, st * (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * w⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack := below (s.gpr .esp) 16
    s.rd = [key, args] ∧ s.wr = [data, iv, scratch] ∧
    key.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
    ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
    stack.Disjoint data ∧ stack.Disjoint iv ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 384 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + st * (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * w ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ 16 ≤ (s.gpr .esp).toNat
  post := post
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- `fbX86`'s precondition gives the modes'. -/
theorem seqPre_of {st : Nat} {post : State → State → Prop} {M : Mode}
    (hstep : M.step = st) (hst : 0 < st) (hst8 : st ≤ 8) {s : State} (h : (fbX86 118 st post).pre s) :
    SeqPre dirCore M s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, dSD, dSV, dSS, fK, fV, fD, fS, fE, fLo⟩ := h
  have hL := dirCoreSpec.layout
  obtain ⟨sA, sR⟩ := stk_apart fE fLo
  refine ⟨(by rw [hrd]; simp [dirCore]), fE, ⟨(by rw [hwr]; simp [dirCore, schedSlot]),
      (by simp only [dirCore, schedSlot]; omega_arith)⟩, (by rw [hwr]; simp [dirCore]),
    (fun _ => by rw [hwr]; simp [dirCore]), (by simp only [dirCore]; omega_arith), (by rw [hwr, hstep]; simp [dirCore]),
    (by rw [hstep]; exact fD), ?_, ?_, (fun _ => ?_), ?_, ?_, ?_, ?_,
    (fun _ => dRV), (by rw [hstep]; exact dSD), ?_, sA, sR, (by simp [dirCore]; omega_arith),
    (by rw [hstep]; simp only [dirCore]; omega_arith), hL⟩
  · rw [hstep, scr_eq]; exact dDS
  · rw [scr_eq]; exact dVS
  · rw [hstep]; exact dVD
  · rw [scr_eq]; exact dAS
  · rw [hstep]; exact dAD
  · rw [scr_eq]; exact dRS
  · rw [hstep]; exact dRD
  · exact dSS.sub_right (VG.Offset.sub_base _ (by simp only [dirCore, schedSlot]; omega_arith))

theorem keyArgs_of {st : Nat} {post : State → State → Prop} {s : State}
    (h : (fbX86 118 st post).pre s) : KeyArgs s [Modes.X86.scrR s dirCore]
      (Spec.TripleDes.scheduleAt s.mem ((arg s 0).setWidth 64)) := by
  obtain ⟨hrd, -, dKS, -, -, -, -, -, dAS, -, -, -, -, -, dSS, fK, -, -, -, -, -⟩ := h
  refine ⟨arg s 0, ⟨⟨argAddr s 0, 20⟩, by rw [hrd]; simp, ?_⟩, rfl, rfl, by rw [hrd]; simp, fK,
    fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
  · show (⟨argAddr s 0, 20⟩ : Region).Contains (argAddr s 0) 4
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]; exact dKS
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact dAS.sub_left (Region.sub_prefix (by decide))
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]; exact dSS

/-- `fbX86`'s precondition gives the modes', for the bitsliced core. -/
theorem seqPreW_of {st : Nat} {post : State → State → Prop} {M : Mode} (d : Spec.TripleDes.Direction)
    (hstep : M.step = st) (hst : 0 < st) (hst8 : st ≤ 8) {s : State} (h : (fbX86 151 st post).pre s) :
    SeqPre (wideCore d) M s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, dSD, dSV, dSS, fK, fV, fD, fS, fE, fLo⟩ := h
  have hL := (wideCoreSpec d).layout
  obtain ⟨sA, sR⟩ := stk_apart fE fLo
  refine ⟨(by rw [hrd]; simp [wideCore]), fE, ⟨(by rw [hwr]; simp [wideCore, wideSchedSlot, Bitslice.wsWords]),
      (by simp only [wideCore, wideSchedSlot, Bitslice.wsWords]; omega_arith)⟩, (by rw [hwr]; simp [wideCore]),
    (fun _ => by rw [hwr]; simp [wideCore]), (by simp only [wideCore]; omega_arith), (by rw [hwr, hstep]; simp [wideCore]),
    (by rw [hstep]; exact fD), ?_, ?_, (fun _ => ?_), ?_, ?_, ?_, ?_,
    (fun _ => dRV), (by rw [hstep]; exact dSD), ?_, sA, sR, (by simp [wideCore]; omega_arith),
    (by rw [hstep]; simp only [wideCore]; omega_arith), hL⟩
  · rw [hstep, scrW_eq]; exact dDS
  · rw [scrW_eq]; exact dVS
  · rw [hstep]; exact dVD
  · rw [scrW_eq]; exact dAS
  · rw [hstep]; exact dAD
  · rw [scrW_eq]; exact dRS
  · rw [hstep]; exact dRD
  · exact dSS.sub_right (VG.Offset.sub_base _ (by simp only [wideCore, wideSchedSlot, Bitslice.wsWords]; omega_arith))

theorem keyArgsW_of {st : Nat} {post : State → State → Prop} (d : Spec.TripleDes.Direction) {s : State}
    (h : (fbX86 151 st post).pre s) : KeyArgs s [Modes.X86.scrR s (wideCore d)]
      (Spec.TripleDes.scheduleAt s.mem ((arg s 0).setWidth 64)) := by
  obtain ⟨hrd, -, dKS, -, -, -, -, -, dAS, -, -, -, -, -, dSS, fK, -, -, -, -, -⟩ := h
  refine ⟨arg s 0, ⟨⟨argAddr s 0, 20⟩, by rw [hrd]; simp, ?_⟩, rfl, rfl, by rw [hrd]; simp, fK,
    fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
  · show (⟨argAddr s 0, 20⟩ : Region).Contains (argAddr s 0) 4
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith
  · simp only [List.mem_singleton] at hr; subst hr; rw [scrW_eq]; exact dKS
  · simp only [List.mem_singleton] at hr; subst hr; rw [scrW_eq]
    exact dAS.sub_left (Region.sub_prefix (by decide))
  · simp only [List.mem_singleton] at hr; subst hr; rw [scrW_eq]; exact dSS

/-- The modes' levels fit the bitsliced core's 32 blocks. -/
theorem levels_fit (d : Spec.TripleDes.Direction) : ∀ g ∈ levels, 0 < g ∧ g ≤ (wideCore d).G := by
  intro g hg
  simp only [levels, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by show _ ≤ 32; decide⟩

theorem wideCore_ka (d : Spec.TripleDes.Direction) : (wideCore d).ka = 1 := rfl
theorem dataW_eq (d : Spec.TripleDes.Direction) (m : Mem) (s : State) :
    Proof.Modes.chunksAt (4 * (wideCore d).bw) m ((arg s 2).setWidth 64) (arg s 3).toNat = dataAt m s :=
  (cbcBlocksAt_eq _ _ _).symm
theorem ivW_eq (d : Spec.TripleDes.Direction) (m : Mem) (s : State) :
    Spec.Aes.bytesAt m ((arg s 1).setWidth 64) (4 * (wideCore d).bw) = ivAt m s := rfl
theorem cipherW_eq (s : State) :
    (wideCoreSpec .encrypt).cipher (Spec.TripleDes.scheduleAt s.mem ((arg s 0).setWidth 64)) = ciph s := rfl

theorem dirCore_ka : dirCore.ka = 1 := rfl

theorem data_eq (m : Mem) (s : State) :
    Proof.Modes.chunksAt (4 * dirCore.bw) m ((arg s 2).setWidth 64) (arg s 3).toNat = dataAt m s :=
  (cbcBlocksAt_eq _ _ _).symm
theorem iv_eq (m : Mem) (s : State) :
    Spec.Aes.bytesAt m ((arg s 1).setWidth 64) (4 * dirCore.bw) = ivAt m s := rfl
theorem bytes_eq (m : Mem) (s : State) :
    Spec.Aes.bytesAt m ((arg s 2).setWidth 64) (arg s 3).toNat = bytesOf m s := rfl
theorem cipher_eq (s : State) :
    dirCoreSpec.cipher (Spec.TripleDes.scheduleAt s.mem ((arg s 0).setWidth 64)) = ciph s := rfl

tactic_template "tdes_post_eq" h:ident h':ident : tactic =>
  `(tactic| simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.bytes0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp,
                     Proof.Modes.X86.P, Proof.Modes.X86.N, dirCore_ka, Nat.reduceAdd, data_eq, iv_eq, bytes_eq, cipher_eq]
                     at $h:ident $h':ident)

theorem ofb_wp_x86 {s₀ : State} (hp : (fbX86 118 8 ofbPost).pre s₀) :
    WP isa ofb s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 118 8 ofbPost).post s₀ s' :=
  WP.mono (ofb_wp dirCoreSpec (seqPre_of rfl (by decide) (by decide) hp) (keyArgs_of hp))
    fun _ ⟨h1, h2, h3⟩ => by tdes_post_eq h2 h3; exact ⟨h1, h2, h3⟩

theorem cfbEncrypt_wp {s₀ : State} (hp : (fbX86 118 8 cfbEncPost).pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 118 8 cfbEncPost).post s₀ s' :=
  WP.mono (cfbEnc_wp dirCoreSpec (seqPre_of rfl (by decide) (by decide) hp) (keyArgs_of hp))
    fun _ ⟨h1, h2, h3⟩ => by tdes_post_eq h2 h3; exact ⟨h1, h2, h3⟩

theorem cfbDecrypt_wp {s₀ : State} (hp : (fbX86 151 8 cfbDecPost).pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 151 8 cfbDecPost).post s₀ s' :=
  WP.mono (cfbDecLevels_wp (wideCoreSpec .encrypt) (levels_fit .encrypt)
      (seqPreW_of .encrypt rfl (by decide) (by decide) hp) (keyArgsW_of .encrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, wideCore_ka, Nat.reduceAdd, dataW_eq, ivW_eq, cipherW_eq] at h2 h3
      exact ⟨h1, h2, h3⟩

theorem cfb8Encrypt_wp {s₀ : State} (hp : (fbX86 118 1 cfb8EncPost).pre s₀) :
    WP isa cfb8Encrypt s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 118 1 cfb8EncPost).post s₀ s' :=
  WP.mono (cfb8Enc_wp dirCoreSpec (seqPre_of rfl (by decide) (by decide) hp) (keyArgs_of hp))
    fun _ ⟨h1, h2, h3⟩ => by tdes_post_eq h2 h3; exact ⟨h1, h2, h3⟩

theorem cfb8Decrypt_wp {s₀ : State} (hp : (fbX86 118 1 cfb8DecPost).pre s₀) :
    WP isa cfb8Decrypt s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 118 1 cfb8DecPost).post s₀ s' :=
  WP.mono (cfb8Dec_wp dirCoreSpec (seqPre_of rfl (by decide) (by decide) hp) (keyArgs_of hp))
    fun _ ⟨h1, h2, h3⟩ => by tdes_post_eq h2 h3; exact ⟨h1, h2, h3⟩

/-! ## Constant time -/

/-- The initial taint: `esp` public, the words holding `data`, `iv` and
`scratch` known to be the base addresses of the writable regions, and room
for the block function's call below `esp`. -/
def fbTaint (w : Nat) : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 8, 8 * w], argLen := 24,
    argBases := [(12, 0), (8, 1), (20, 2)], room := 16 }

theorem fbTaint_wf {w st : Nat} {post : State → State → Prop} {s : State} (hp : (fbX86 w st post).pre s) :
    VG.X86.Taint.Wf (fbTaint w) s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, dSD, dSV, dSS, fK, fV, fD, fS, fE, fLo⟩ := hp
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [fbTaint]; omega_arith, ?_⟩, ?_⟩ ?_
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil))
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨dVD.symm, dDS⟩, dVS, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_arith) dRD dAD
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_arith) dRV dAV
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_arith) dRS dAS
  · intro p hp'
    simp only [fbTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> refine ⟨by show _ ≤ 24; decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · intro _
    refine ⟨fLo, ?_⟩
    intro r hr
    have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16 =
        (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := (VG.X86.Taint.sub_setWidth fLo).symm
    change (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r
    rw [e]
    simp only [hwr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dSD
    · exact dSV
    · exact dSS

theorem fbTaint_agree {w st : Nat} {post : State → State → Prop} {s₁ s₂ : State} (h₁ : (fbX86 w st post).pre s₁)
    (h₂ : (fbX86 w st post).pre s₂) (hpub : (fbX86 w st post).pub s₁ s₂) : VG.X86.Taint.Agree (fbTaint w) s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  obtain ⟨-, hwr₁, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₁, -⟩ := id h₁
  obtain ⟨-, hwr₂, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₂, -⟩ := id h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, fbTaint_wf h₁, fbTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [fbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hwr₁, hwr₂, ha 1 (by omega_arith), ha 2 (by omega_arith), ha 3 (by omega_arith), ha 4 (by omega_arith)]
  · simp only [fbTaint] at hk
    rw [show VG.X86.Taint.depth (fbTaint w).stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 24) fE₁ h4 hk, VG.X86.Taint.argByte_eq (n := 24) fE₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_arith)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_arith))]
    exact congrArg _ (ha _ (by omega_arith))

theorem ofb_ct : ConstantTime isa (fbX86 118 8 ofbPost).pre (fbX86 118 8 ofbPost).pub ofb := by
  obtain ⟨_, h⟩ : ∃ h, (VG.X86.taint.check (fbTaint 118) ofb h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := VG.X86.taint) (fbTaint 118) (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

theorem cfbEncrypt_ct : ConstantTime isa (fbX86 118 8 cfbEncPost).pre (fbX86 118 8 cfbEncPost).pub cfbEncrypt := by
  obtain ⟨_, h⟩ : ∃ h, (VG.X86.taint.check (fbTaint 118) cfbEncrypt h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := VG.X86.taint) (fbTaint 118) (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

theorem cfbDecrypt_ct : ConstantTime isa (fbX86 151 8 cfbDecPost).pre (fbX86 151 8 cfbDecPost).pub cfbDecrypt :=
  VG.Taint.constantTime (A := VG.X86.taint) (fbTaint 151) (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfb8Encrypt_ct : ConstantTime isa (fbX86 118 1 cfb8EncPost).pre (fbX86 118 1 cfb8EncPost).pub cfb8Encrypt := by
  obtain ⟨_, h⟩ : ∃ h, (VG.X86.taint.check (fbTaint 118) cfb8Encrypt h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := VG.X86.taint) (fbTaint 118) (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

theorem cfb8Decrypt_ct : ConstantTime isa (fbX86 118 1 cfb8DecPost).pre (fbX86 118 1 cfb8DecPost).pub cfb8Decrypt := by
  obtain ⟨_, h⟩ : ∃ h, (VG.X86.taint.check (fbTaint 118) cfb8Decrypt h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := VG.X86.taint) (fbTaint 118) (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

/-! ## The contracts -/

/-- `fbX86` with the argument slots writable, as the signature's contract has
them; the code reads them only (`fb_verified` narrows to `fbX86`). -/
def wideContract (w st : Nat) (post : State → State → Prop) : Contract isa :=
  { fbX86 w st post with
    pre := fun s =>
      let key : Region := ⟨(arg s 0).setWidth 64, 384⟩
      let iv : Region := ⟨(arg s 1).setWidth 64, 8⟩
      let data : Region := ⟨(arg s 2).setWidth 64, st * (arg s 3).toNat⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * w⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack := below (s.gpr .esp) 16
      s.rd = [key] ∧ s.wr = [iv, data, scratch, args] ∧
      key.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
      stack.Disjoint data ∧ stack.Disjoint iv ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 384 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + st * (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * w ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ 16 ≤ (s.gpr .esp).toNat }

def narrowRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, 384⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (w st : Nat) (s : State) : List Region :=
  [⟨(arg s 2).setWidth 64, st * (arg s 3).toNat⟩, ⟨(arg s 1).setWidth 64, 8⟩, ⟨(arg s 4).setWidth 64, 8 * w⟩]

tactic_template "tdes_fb_narrow" : tactic =>
  `(tactic| simp only [VG.Proof.TripleDes.X86.Fb.fbX86, VG.Proof.TripleDes.X86.Fb.wideContract,
                     VG.Proof.TripleDes.X86.Fb.narrowRd, VG.Proof.TripleDes.X86.Fb.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr])

theorem wide_pre (w st : Nat) (post : State → State → Prop) (s : State) (h : (wideContract w st post).pre s) :
    (fbX86 w st post).pre (s.withRegions (narrowRd s) (narrowWr w st s)) := by
  obtain ⟨_, _, h⟩ := h
  tdes_fb_narrow
  exact ⟨trivial, trivial, h⟩

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0, 0x4000` at `0x8004`. -/
def satState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30
    else if a = 0x8015 then 0x40 else 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 944⟩, ⟨0x8004, 20⟩]

/-- `satState`, with the bitsliced core's scratch buffer. -/
def satStateW : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30
    else if a = 0x8015 then 0x40 else 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 1208⟩, ⟨0x8004, 20⟩]

theorem wide_implies_ofb :
    (wideContract 118 8 ofbPost).Implies (Proof.TripleDes.fbScratchContract X86.abi 118 Proof.TripleDes.ofbPost 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below] at h
    sig_split h
    sig_reduce [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [VG.X86.Taint.sub_setWidth (by omega_arith)]; try simp only [Nat.mul_comm] at *; with_reducible assumption)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, ofbPost, ciph, ivAt, dataAt, bytesOf]
  · sig_implies_pub [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
  · sig_implies_sat [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_cfbEnc :
    (wideContract 118 8 cfbEncPost).Implies (Proof.TripleDes.fbScratchContract X86.abi 118 Proof.TripleDes.cfbEncPost 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below] at h
    sig_split h
    sig_reduce [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [VG.X86.Taint.sub_setWidth (by omega_arith)]; try simp only [Nat.mul_comm] at *; with_reducible assumption)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, cfbEncPost, ciph, ivAt, dataAt, bytesOf]
  · sig_implies_pub [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
  · sig_implies_sat [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_cfbDec :
    (wideContract 151 8 cfbDecPost).Implies (Proof.TripleDes.fbScratchContract X86.abi 151 Proof.TripleDes.cfbDecPost 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below] at h
    sig_split h
    sig_reduce [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [VG.X86.Taint.sub_setWidth (by omega_arith)]; try simp only [Nat.mul_comm] at *; with_reducible assumption)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, cfbDecPost, ciph, ivAt, dataAt, bytesOf]
  · sig_implies_pub [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
  · sig_implies_sat [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
      [satStateW, arg, argAddr, Mem.readW, Mem.read] using satStateW

theorem wide_implies_cfb8Enc :
    (wideContract 118 1 cfb8EncPost).Implies (Proof.TripleDes.cfb8ScratchContract X86.abi 118 Proof.TripleDes.cfb8EncPost 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8EncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below] at h
    sig_split h
    sig_reduce [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8EncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [VG.X86.Taint.sub_setWidth (by omega_arith)]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.one_mul] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (rw [VG.X86.Taint.sub_setWidth (by omega_arith)]; simp only [Nat.one_mul] at *; with_reducible assumption)
  · sig_implies_post [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8EncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, cfb8EncPost, ciph, ivAt, dataAt, bytesOf]
  · sig_implies_pub [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8EncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
  · sig_implies_sat [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8EncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_cfb8Dec :
    (wideContract 118 1 cfb8DecPost).Implies (Proof.TripleDes.cfb8ScratchContract X86.abi 118 Proof.TripleDes.cfb8DecPost 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8DecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below] at h
    sig_split h
    sig_reduce [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8DecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [VG.X86.Taint.sub_setWidth (by omega_arith)]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.one_mul] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (rw [VG.X86.Taint.sub_setWidth (by omega_arith)]; simp only [Nat.one_mul] at *; with_reducible assumption)
  · sig_implies_post [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8DecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, cfb8DecPost, ciph, ivAt, dataAt, bytesOf]
  · sig_implies_pub [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8DecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
  · sig_implies_sat [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8DecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

/-- A state satisfying the functions' precondition: the schedule at `0x1000`,
the chaining value at `0x2000`, and no data at `0x3000`, as stack arguments
at `0x8004`, which are writable. -/
def frameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30 else 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x8004, 16⟩]

theorem frameSat_pre (post : Spec.TripleDes.ofbSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.TripleDes.ofbSig.contract X86.abi (post := post) (writeArgs := true) (stack := 984)).pre s := by
  implies_sat [Spec.TripleDes.ofbSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem frameSat_pre8 (post : Spec.TripleDes.cfb8Sig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.TripleDes.cfb8Sig.contract X86.abi (post := post) (writeArgs := true) (stack := 984)).pre s := by
  implies_sat [Spec.TripleDes.cfb8Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem frameSat_preW (post : Spec.TripleDes.ofbSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.TripleDes.ofbSig.contract X86.abi (post := post) (writeArgs := true) (stack := 1248)).pre s := by
  implies_sat [Spec.TripleDes.ofbSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem fb_verified {w st : Nat} {post : State → State → Prop} {c : Prog isa}
    (hwp : ∀ s, (fbX86 w st post).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (fbX86 w st post).post s s')
    (hct : ConstantTime isa (fbX86 w st post).pre (fbX86 w st post).pub c)
    (hR : ∀ s s' rd wr rd' wr', post (s.withRegions rd wr) (s'.withRegions rd' wr') → post s s')
    {k : Contract isa} (hi : (wideContract w st post).Implies k) : Verified X86.target c k := by
  have hsat := hi.sat_left
  have narrowSat : ∃ s, (fbX86 w st post).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wide_pre w st post s hs⟩
  apply Verified.of_implies _ hi
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat))
    narrowRd (narrowWr w st) (wide_pre w st post) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp_all only [or_true, true_or]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp_all only [or_true, true_or]
  · intro s s' _ h
    exact hR _ _ _ _ _ _ h
  · intro s₁ s₂ _ _ h
    tdes_fb_narrow
    exact h

theorem ofb_verified :
    Verified X86.target ofb (Proof.TripleDes.fbScratchContract X86.abi 118 Proof.TripleDes.ofbPost 16) :=
  fb_verified (fun _ hs => ofb_wp_x86 hs) ofb_ct (fun _ _ _ _ _ _ h => h) wide_implies_ofb
theorem cfbEncrypt_verified :
    Verified X86.target cfbEncrypt (Proof.TripleDes.fbScratchContract X86.abi 118 Proof.TripleDes.cfbEncPost 16) :=
  fb_verified (fun _ hs => cfbEncrypt_wp hs) cfbEncrypt_ct (fun _ _ _ _ _ _ h => h) wide_implies_cfbEnc
theorem cfbDecrypt_verified :
    Verified X86.target cfbDecrypt (Proof.TripleDes.fbScratchContract X86.abi 151 Proof.TripleDes.cfbDecPost 16) :=
  fb_verified (fun _ hs => cfbDecrypt_wp hs) cfbDecrypt_ct (fun _ _ _ _ _ _ h => h) wide_implies_cfbDec
theorem cfb8Encrypt_verified :
    Verified X86.target cfb8Encrypt (Proof.TripleDes.cfb8ScratchContract X86.abi 118 Proof.TripleDes.cfb8EncPost 16) :=
  fb_verified (fun _ hs => cfb8Encrypt_wp hs) cfb8Encrypt_ct (fun _ _ _ _ _ _ h => h) wide_implies_cfb8Enc
theorem cfb8Decrypt_verified :
    Verified X86.target cfb8Decrypt (Proof.TripleDes.cfb8ScratchContract X86.abi 118 Proof.TripleDes.cfb8DecPost 16) :=
  fb_verified (fun _ hs => cfb8Decrypt_wp hs) cfb8Decrypt_ct (fun _ _ _ _ _ _ h => h) wide_implies_cfb8Dec

/-- `ofb` with its working space on the stack. -/
theorem ofb_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 ofb)
      (Spec.TripleDes.ofbContract X86.abi 984) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.ofbSig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.TripleDes.ofbPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 968) ofb_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.ofbPost_local _) (Proof.TripleDes.ofbPostOut_local _) (frameSat_pre _)

/-- `cfbEncrypt` with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 cfbEncrypt)
      (Spec.TripleDes.cfbEncryptContract X86.abi 984) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbSig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.TripleDes.cfbEncPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 968) cfbEncrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cfbEncPost_local _) (Proof.TripleDes.cfbEncPostOut_local _) (frameSat_pre _)

/-- `cfbDecrypt` with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1232 4 302 cfbDecrypt)
      (Spec.TripleDes.cfbDecryptContract X86.abi 1248) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbSig) (nm := "scratch") (e := .u64)
    (n := 151) (post := Proof.TripleDes.cfbDecPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 1232) cfbDecrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cfbDecPost_local _) (Proof.TripleDes.cfbDecPostOut_local _) (frameSat_preW _)

/-- `cfb8Encrypt` with its working space on the stack. -/
theorem cfb8Encrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 cfb8Encrypt)
      (Spec.TripleDes.cfb8EncryptContract X86.abi 984) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cfb8Sig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.TripleDes.cfb8EncPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 968) cfb8Encrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cfb8EncPost_local _) (Proof.TripleDes.cfb8EncPostOut_local _) (frameSat_pre8 _)

/-- `cfb8Decrypt` with its working space on the stack. -/
theorem cfb8Decrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 cfb8Decrypt)
      (Spec.TripleDes.cfb8DecryptContract X86.abi 984) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cfb8Sig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.TripleDes.cfb8DecPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 968) cfb8Decrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cfb8DecPost_local _) (Proof.TripleDes.cfb8DecPostOut_local _) (frameSat_pre8 _)

end VG.Proof.TripleDes.X86.Fb
