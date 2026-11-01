module

public import VerifiedGarbage.Proof.Sm4.X86.PreparedBody
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sm4.Common
public import VerifiedGarbage.Proof.Sm4.X86.Prologue
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.X86.Lit
public import VerifiedGarbage.Impl.Sm4.X86.Prepared
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sm4.X86.LayersLit
meta import VerifiedGarbage.Proof.Sm4.X86.PreparedBody
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sm4.Common
meta import VerifiedGarbage.Proof.Sm4.X86.Prologue
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Sm4.X86.Lit
meta import VerifiedGarbage.Impl.Sm4.X86.Prepared
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4.X86.LayersLit
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Sm4.Contract
public import VerifiedGarbage.Proof.Sm4.Prepared
meta import VerifiedGarbage.Proof.Sm4.Prepared

/-!
# SM4's prepared round keys and batches on x86 (32-bit) meet their contracts

`prepare_verified` and `crypt_verified`: `vg_sm4_prepare_keys` and
`vg_sm4_crypt_prepared` against `Proof.Sm4.Prepared`, with `layout`, from
the bodies' runs (`prepareBody_wp`, `cryptBody_wp`). A batch's blocks are
ECB in the direction and under the round keys of any table encoding that its
working space holds: the run from it is the run from the table the
precondition gives (`Exec.det`). Constant time by the taint analysis, which
starts with `esp` and the argument words public, and knows the working
space's word as its region's base.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Sm4.X86
open VG.Impl.Aes.X86 (sb argOp)
open VG.Proof.Sm4 (specDirX86)
open VG.Proof.Sm4.Prepared (Holds Keeps)

theorem size_eq : layout.size = 4 * slots := rfl

theorem ea_argOp {s₀ s : State} (h : s.gpr .esp = s₀.gpr .esp) (i : Nat) : s.ea (argOp i) = argAddr s₀ i := by
  show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = _
  rw [h]; rfl

/-- Argument `i` of `n` is in the arguments' region. -/
theorem arg_in (s : State) {n : Nat} (hfit : (s.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) {i : Nat} (hi : i < n) :
    (⟨argAddr s 0, 4 * n⟩ : Region).Contains (argAddr s i) 4 := by
  have hs := setWidth_toNat (s.gpr .esp)
  rw [show argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) from addr_eq (by omega),
    show argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 from addr_eq (by omega)]
  exact VG.Offset.contains _ (by omega) (by omega) (by omega)

/-- The working space, of `2 L ≥ slots` slots. -/
theorem scrIn_of {rs : List Region} {b : BitVec 32} {L : Nat} (hr : (⟨b.setWidth 64, L * 8⟩ : Region) ∈ rs)
    (hfit : b.toNat + L * 8 ≤ 2 ^ 32) (hL : 4 * slots ≤ 8 * L) : ScrIn rs b :=
  ⟨⟨2 * L, by omega, by omega, by rw [show 4 * (2 * L) = L * 8 by omega]; exact hr⟩, by omega⟩

/-- Every byte of `ws` from `4 * slots` on keeps its value. -/
theorem keeps_of_frame {m m' : Mem} {b : BitVec 32} {L : Nat} {rs : List (Nat × Nat)}
    (hf : Frame [⟨b.setWidth 64, 4 * slots⟩] m m') (fit : b.toNat + L * 8 ≤ 2 ^ 32)
    (hrs : ∀ i, (∀ r ∈ rs, i < r.1 ∨ r.1 + r.2 ≤ i) → 4 * slots ≤ i) : Keeps (b.setWidth 64) L rs m m' :=
  fun i hi hout => hf _ fun r hr hc => by
    simp only [List.mem_singleton] at hr; subst hr
    simp only [Region.Contains] at hc
    rw [Mem.sub_ofNat_toNat _ (by have := setWidth_toNat b; omega)] at hc
    have := hrs i hout
    omega

/-! ## The preparation -/

/-- `vg_sm4_prepare_keys` on x86. -/
def prepX86 : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let ws : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat * 8⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, args] ∧ s.wr = [ws] ∧ sched.Disjoint ws ∧ args.Disjoint ws ∧ ret.Disjoint ws ∧
      (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat * 8 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧ (arg s 1).toNat ≤ 1 ∧ layout.size ≤ 8 * (arg s 3).toNat
  post s s' :=
    Holds layout s'.mem ((arg s 2).setWidth 64) (Spec.Sm4.scheduleAt s.mem ((arg s 0).setWidth 64))
        (Proof.Sm4.directionOf (arg s 1).toNat) ∧
      Keeps ((arg s 2).setWidth 64) (arg s 3).toNat layout.prepScratch s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

/-- The callee-saved registers and the return address, from what the bodies
keep. -/
theorem abi_of {s s' : State} (h₁ : ∀ i < 4, s'.gpr (sreg i) = s.gpr (sreg i)) (hesp : s'.gpr .esp = s.gpr .esp)
    (hret : s'.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32) :
    abiPreserved s s' := by
  refine ⟨fun r hr => ?_, hret⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by decide)
  · exact h₁ 1 (by decide)
  · exact h₁ 2 (by decide)
  · exact h₁ 3 (by decide)
  · exact hesp

theorem prep_correct (s : State) (hs : prepX86.pre s) :
    ∃ t s', Exec isa prepareKeys s t s' ∧ abiPreserved s s' ∧ prepX86.post s s' := by
  obtain ⟨hrd, hwr, dKW, dAW, dRW, fitK, fitW, fitE, -, hsz⟩ := hs
  rw [size_eq] at hsz
  let b := arg s 2
  have hw : ScrIn s.wr b := scrIn_of (L := (arg s 3).toNat) (by rw [hwr]; simp [b]) fitW (by omega)
  have hrA : (⟨argAddr s 0, 16⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  have dWS : ∀ r : Region, Region.Disjoint r ⟨b.setWidth 64, (arg s 3).toNat * 8⟩ →
      Region.Disjoint r ⟨b.setWidth 64, 4 * slots⟩ := fun r h => h.sub_right (Region.sub_prefix (by omega))
  have hE := setWidth_toNat (s.gpr .esp)
  have argSub : ∀ i < 4, Region.Sub ⟨argAddr s i, 4⟩ ⟨argAddr s 0, 16⟩ := fun i hi => by
    rw [show argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) from addr_eq (by omega),
      show argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 from addr_eq (by omega)]
    exact VG.Offset.sub _ (by omega) (by omega)
  obtain ⟨t, s', he, h₁, hesp, -, -, hf, hW⟩ := prepareBody_wp (s₀ := s) (b := b) (sched := arg s 0) hw
    (fun i hi => by rw [ea_argOp rfl]; exact ⟨_, List.mem_append_left _ hrA, arg_in s (n := 4) (by omega) (by omega)⟩)
    (by rw [ea_argOp rfl]; rfl) (by rw [ea_argOp rfl]; rfl) (by rw [hrd]; simp) fitK (dWS _ dKW)
    (fun i hi => by rw [ea_argOp rfl]; exact (dWS _ dAW).sub_left (argSub i (by omega)))
  refine ⟨t, s', he, abi_of h₁ hesp ?_, ?_, keeps_of_frame hf fitW fun i hi => ?_⟩
  · exact hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dWS _ dRW) (by decide)
  · refine holds_of_words hw.fit ?_
    rw [ofSpecDir_dirOf]
    rw [ea_argOp rfl] at hW
    exact hW
  · have := hi _ (List.mem_singleton_self _)
    simp only at this
    omega

/-- The initial taint: `esp` and the argument words public, and the working
space's word known as its region's base. -/
def prepTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [4 * slots], argLen := 20, argBases := [(12, 0)] }

theorem prepTaint_wf {s : State} (hp : prepX86.pre s) : VG.X86.Taint.Wf prepTaint s := by
  obtain ⟨_, hwr, _, dAW, dRW, _, fitW, fitE, _, hsz⟩ := hp
  rw [size_eq] at hsz
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [prepTaint]; omega, ?_⟩, ?_⟩
  · rw [hwr]
    exact .cons (by simp only; omega) .nil
  · simp only [hwr, List.pairwise_cons, List.not_mem_nil, List.Pairwise.nil, and_true]
    exact fun _ h => h.elim
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; simp only [setWidth_toNat]; omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) dRW dAW
  · intro p hp'
    simp only [prepTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    refine ⟨by decide, ?_⟩
    simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]

theorem prepTaint_agree {s₁ s₂ : State} (h₁ : prepX86.pre s₁) (h₂ : prepX86.pre s₂) (hpub : prepX86.pub s₁ s₂) :
    VG.X86.Taint.Agree prepTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, prepTaint_wf h₁, prepTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp, fun k h4 hk => ?_⟩
  · simp only [prepTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [h₁.2.1, h₂.2.1, ha 2 (by omega), ha 3 (by omega)]
  · simp only [prepTaint] at hk
    rw [show VG.X86.Taint.depth prepTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 20) h₁.2.2.2.2.2.2.2.1 h4 hk,
      VG.X86.Taint.argByte_eq (n := 20) h₂.2.2.2.2.2.2.2.1 h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem prep_ct : ConstantTime isa prepX86.pre prepX86.pub prepareKeys :=
  VG.Taint.constantTime (A := VG.X86.taint) prepTaint (fun _ _ h₁ h₂ hp => prepTaint_agree h₁ h₂ hp)
    (by native_taint_decide)

/-- Memory holding the arguments `0x1000, 0, 0x4000, 179` at `0x8004`. -/
def prepSat : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x800D then 0x40 else if a = 0x8010 then 0xB3 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x4000, 179 * 8⟩]

theorem prepare_verified :
    Verified X86.target prepareKeys (Proof.Sm4.Prepared.prepareContract layout X86.abi) :=
  Verified.of_correct prep_correct prep_ct (by
    sig_implies [Proof.Sm4.Prepared.prepareContract, Proof.Sm4.Prepared.prepareSig, prepX86, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, size_eq, slots]
      [prepSat, arg, argAddr, Mem.readW, Mem.read] using prepSat)

/-! ## A batch -/

/-- `vg_sm4_crypt_prepared` on x86. -/
def cryptX86 : Contract X86.isa where
  pre s :=
    let ws : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat * 8⟩
    let args : Region := ⟨argAddr s 0, 8⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [args] ∧ s.wr = [ws] ∧ args.Disjoint ws ∧ ret.Disjoint ws ∧
      (arg s 0).toNat + (arg s 1).toNat * 8 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 12 ≤ 2 ^ 32 ∧
      layout.size ≤ 8 * (arg s 1).toNat ∧ ∃ k d, Holds layout s.mem ((arg s 0).setWidth 64) k d
  post s s' :=
    (∀ k d, Holds layout s.mem ((arg s 0).setWidth 64) k d →
      Spec.Sm4.blocksAt s'.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Sm4.ecb k d (Spec.Sm4.blocksAt s.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 layout.buf) layout.blocks)) ∧
      Keeps ((arg s 0).setWidth 64) (arg s 1).toNat layout.cryptScratch s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 2, arg s₁ i = arg s₂ i

theorem blocks_of (B : Addr) {m m' : Mem} {k : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction}
    (h : ∀ j < 8, Spec.Sm4.blockAt m' (B + BitVec.ofNat 64 (4 * tailSlot + 16 * j)) =
        Proof.Sm4.blockFn k d (Spec.Sm4.blockAt m (B + BitVec.ofNat 64 (4 * tailSlot + 16 * j)))) :
    Spec.Sm4.blocksAt m' (B + BitVec.ofNat 64 layout.buf) layout.blocks =
      Spec.Sm4.ecb k d (Spec.Sm4.blocksAt m (B + BitVec.ofNat 64 layout.buf) layout.blocks) := by
  rw [Proof.Sm4.ecb_eq]
  simp only [Spec.Sm4.blocksAt, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  simp only [List.mem_range] at hj
  simp only [Function.comp_apply, VG.Offset.add_add]
  exact h j hj

theorem crypt_correct (s : State) (hs : cryptX86.pre s) :
    ∃ t s', Exec isa cryptPrepared s t s' ∧ abiPreserved s s' ∧ cryptX86.post s s' := by
  obtain ⟨hrd, hwr, dAW, dRW, fitW, fitE, hsz, k₀, d₀, hH⟩ := hs
  rw [size_eq] at hsz
  let b := arg s 0
  have hw : ScrIn s.wr b := scrIn_of (L := (arg s 1).toNat) (by rw [hwr]; simp [b]) fitW (by omega)
  have hE := setWidth_toNat (s.gpr .esp)
  have harg : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4 := by
    rw [ea_argOp rfl, hrd]; exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _),
      arg_in s (n := 2) (by omega) (by omega)⟩
  have hb : s.mem.readW (s.ea (argOp 0)) 32 = b := by rw [ea_argOp rfl]; rfl
  obtain ⟨t, s', he, h₁, hesp, -, -, hf, hkeep, -⟩ :=
    cryptBody_wp hw harg hb (readyAt_of_words (words_of_holds hw.fit hH))
  refine ⟨t, s', he, abi_of h₁ hesp ?_, fun k d hk => ?_, fun i hi hout => ?_⟩
  · exact hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dRW.sub_right (Region.sub_prefix (by omega)))
      (by decide)
  · obtain ⟨t₂, s₂, he₂, -, -, -, -, -, -, hB₂⟩ :=
      cryptBody_wp hw harg hb (readyAt_of_words (words_of_holds hw.fit hk))
    obtain ⟨-, rfl⟩ := Exec.det he he₂
    refine blocks_of _ fun j hj => ?_
    have := hB₂ j hj
    rw [specDirX86_ofSpecDir] at this
    exact this
  · simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    rw [tableSlot_eq, savedSlot_eq, slots_eq] at hout
    have hfit := hw.fit
    rw [slots_eq] at hfit
    by_cases ht : 384 ≤ i ∧ i < 1408
    · rw [table_byte hw.fit (by rw [tableEnd_eq]; omega), Mem.readW_byte s'.mem _ (by omega),
        Mem.readW_byte s.mem _ (by omega), hkeep _ (by rw [tableSlot_eq]; omega) (by rw [savedSlot_eq]; omega)]
    · refine hf _ fun r hr hc => ?_
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, slots_eq] at hc
      rw [Mem.sub_ofNat_toNat _ (by omega)] at hc
      omega

/-- The initial taint: `esp` and the argument words public, and the working
space's word known as its region's base. -/
def cryptTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [4 * slots], argLen := 12, argBases := [(4, 0)] }

theorem cryptTaint_wf {s : State} (hp : cryptX86.pre s) : VG.X86.Taint.Wf cryptTaint s := by
  obtain ⟨_, hwr, dAW, dRW, fitW, fitE, hsz, _⟩ := hp
  rw [size_eq] at hsz
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [cryptTaint]; omega, ?_⟩, ?_⟩
  · rw [hwr]
    exact .cons (by simp only; omega) .nil
  · simp only [hwr, List.pairwise_cons, List.not_mem_nil, List.Pairwise.nil, and_true]
    exact fun _ h => h.elim
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; simp only [setWidth_toNat]; omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 8) (by omega) dRW dAW
  · intro p hp'
    simp only [cryptTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    refine ⟨by decide, ?_⟩
    simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]

theorem cryptTaint_agree {s₁ s₂ : State} (h₁ : cryptX86.pre s₁) (h₂ : cryptX86.pre s₂) (hpub : cryptX86.pub s₁ s₂) :
    VG.X86.Taint.Agree cryptTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, cryptTaint_wf h₁, cryptTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp, fun k h4 hk => ?_⟩
  · simp only [cryptTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [h₁.2.1, h₂.2.1, ha 0 (by omega), ha 1 (by omega)]
  · simp only [cryptTaint] at hk
    rw [show VG.X86.Taint.depth cryptTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 12) h₁.2.2.2.2.2.1 h4 hk,
      VG.X86.Taint.argByte_eq (n := 12) h₂.2.2.2.2.2.1 h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem crypt_ct : ConstantTime isa cryptX86.pre cryptX86.pub cryptPrepared :=
  VG.Taint.constantTime (A := VG.X86.taint) cryptTaint (fun _ _ h₁ h₂ hp => cryptTaint_agree h₁ h₂ hp)
    (by native_taint_decide)

/-- Round keys of zeros, whose planes are zeros. -/
def zeroSchedule : Spec.Sm4.Schedule := Vector.replicate 32 0

theorem encode_zero (i : Nat) : layout.encode zeroSchedule .encrypt i = 0 := by
  show (Impl.Sm4.planeOf32 (keyEntry zeroSchedule .encrypt ((i / 4 - tableSlot) / 8)) _).extractLsb' _ 8 = 0
  have : keyEntry zeroSchedule .encrypt ((i / 4 - tableSlot) / 8) = 0 := by
    simp only [keyEntry, zeroSchedule, Vector.getD, Vector.replicate]
    unfold Array.getD
    split <;> simp
  rw [this]
  simp [Impl.Sm4.planeOf32, Impl.Sm4.planeBits]

/-- Memory holding the arguments `0x4000, 179` at `0x8004`, and zeros
elsewhere: the table of `zeroSchedule`. -/
def cryptSat : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x40 else if a = 0x8008 then 0xB3 else 0
  rd := [⟨0x8004, 8⟩]
  wr := [⟨0x4000, 179 * 8⟩]

theorem cryptSat_holds : Holds layout cryptSat.mem ((0x4000 : BitVec 32).setWidth 64) zeroSchedule .encrypt := by
  intro r hr i hi
  rw [layout_table, List.mem_singleton] at hr
  subst hr
  dsimp only at hi ⊢
  rw [encode_zero]
  have ha : ((0x4000 : BitVec 32).setWidth 64 + BitVec.ofNat 64 (384 + i)).toNat = 0x4000 + 384 + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show ((0x4000 : BitVec 32).setWidth 64).toNat = 0x4000 from rfl]
    omega
  have h1 : (0x4000 : BitVec 32).setWidth 64 + BitVec.ofNat 64 (384 + i) ≠ 0x8005 := fun h => by
    have := congrArg BitVec.toNat h; rw [ha] at this; simp at this; omega
  have h2 : (0x4000 : BitVec 32).setWidth 64 + BitVec.ofNat 64 (384 + i) ≠ 0x8008 := fun h => by
    have := congrArg BitVec.toNat h; rw [ha] at this; simp at this; omega
  simp only [cryptSat, h1, h2, ite_false]

theorem crypt_implies : cryptX86.Implies (Proof.Sm4.Prepared.cryptContract layout X86.abi) where
  pre := by
    sig_implies_pre [Proof.Sm4.Prepared.cryptContract, Proof.Sm4.Prepared.cryptSig, cryptX86, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]
  post := by
    sig_implies_post [Proof.Sm4.Prepared.cryptContract, Proof.Sm4.Prepared.cryptSig, cryptX86, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]
  pub := by
    sig_implies_pub [Proof.Sm4.Prepared.cryptContract, Proof.Sm4.Prepared.cryptSig, cryptX86, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]
  sat := by
    refine ⟨cryptSat, ?_⟩
    sig_pre [Proof.Sm4.Prepared.cryptContract, Proof.Sm4.Prepared.cryptSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    sig_and_intros
    all_goals first
      | decide
      | exact Region.disjoint_of_sep (by decide)
      | exact ⟨_, _, cryptSat_holds⟩
      | (rw [size_eq, slots_eq]; decide)
      | simp [cryptSat, arg, argAddr, Mem.readW, Mem.read]

theorem crypt_verified :
    Verified X86.target cryptPrepared (Proof.Sm4.Prepared.cryptContract layout X86.abi) :=
  Verified.of_correct crypt_correct crypt_ct crypt_implies

end VG.Proof.Sm4.X86
