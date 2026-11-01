module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.PreparedBody
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sm4.PPC64LE.LayersLit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.PreparedBody
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.LayersLit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Proof.Sm4.Contract
public import VerifiedGarbage.Proof.Sm4.Prepared
meta import VerifiedGarbage.Proof.Sm4.Prepared

/-!
# SM4's prepared round keys and batches on PPC64LE meet their contracts

`prepare_verified` and `crypt_verified`: `vg_sm4_prepare_keys` and
`vg_sm4_crypt_prepared` against `Proof.Sm4.Prepared`, with `layout`. Each
body runs from the state narrowed to ECB's scratch buffer (`prepareBody_wp`,
`cryptBody_wp`) and then from the whole working space (`Exec.widen`), which it
changes only where the narrowed run may. A batch's blocks are ECB in the
direction and under the round keys of any table encoding that its working
space holds: the run from it is the run from the table the precondition
gives (`Exec.det`). Constant time by the taint analysis: the pointers,
`ws_len` and `decrypt` are public.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.Sm4.PPC64LE
open VG.Proof.Sm4 (specDirA)
open VG.Proof.Sm4.Prepared (Holds Keeps)

/-! ## Narrowing the working space -/

/-- `s` with its writable region the first `8 * slots` bytes of `ws`. -/
abbrev narrow (s : State) (ws : Addr) : State := s.withRegions s.rd [⟨ws, 8 * slots⟩]

theorem narrow_covers (s : State) {ws : Addr} {len : Nat} (hw : s.wr = [⟨ws, len⟩]) (hl : 8 * slots ≤ len) :
    Covers ((narrow s ws).rd ++ (narrow s ws).wr) (s.rd ++ s.wr) ∧ Covers (narrow s ws).wr s.wr := by
  have h : Covers [⟨ws, 8 * slots⟩] s.wr := Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨ws, len⟩, by rw [hw]; simp, 0, by rw [BitVec.add_zero], by show 0 + 8 * slots ≤ len; omega⟩
  exact ⟨Covers.append (fun _ _ h => h) h, h⟩

/-- A run from the narrowed state is a run from `s`, to the state with `s`'s regions. -/
theorem exec_widen {c : Prog isa} {s s' : State} {t : List Leak} {ws : Addr} {len : Nat}
    (hw : s.wr = [⟨ws, len⟩]) (hl : 8 * slots ≤ len) (h : Exec isa c (narrow s ws) t s') :
    Exec isa c s t (s'.withRegions s.rd s.wr) := by
  have := Exec.widen h (narrow_covers s hw hl).1 (narrow_covers s hw hl).2
  rwa [State.withRegions_withRegions, State.withRegions_self] at this

/-- The bytes of `ws` from `8 * slots` on keep their values. -/
theorem keeps_of_frame {m m' : Mem} {ws : Addr} {wsLen : Nat} {rs : List (Nat × Nat)}
    (hf : Frame [⟨ws, 8 * slots⟩] m m') (fit : ws.toNat + wsLen * 8 ≤ 2 ^ 64)
    (hrs : ∀ i, (∀ r ∈ rs, i < r.1 ∨ r.1 + r.2 ≤ i) → 8 * slots ≤ i) :
    Keeps ws wsLen rs m m' := fun i hi hout =>
  hf _ fun r hr hc => by
    simp only [List.mem_singleton] at hr; subst hr
    simp only [Region.Contains] at hc
    rw [Mem.sub_ofNat_toNat ws (by omega)] at hc
    have := hrs i hout
    omega

/-! ## The preparation -/

/-- `vg_sm4_prepare_keys` on PPC64LE. -/
def prepPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .r3, 128⟩
    let ws : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat * 8⟩
    s.rd = [sched] ∧ s.wr = [ws] ∧ sched.Disjoint ws ∧ (s.gpr .r3).toNat + 128 ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + (s.gpr .r6).toNat * 8 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat ≤ 1 ∧
      layout.size ≤ 8 * (s.gpr .r6).toNat
  post s s' :=
    Holds layout s'.mem (s.gpr .r5) (Spec.Sm4.scheduleAt s.mem (s.gpr .r3))
        (Proof.Sm4.directionOf (s.gpr .r4).toNat) ∧
      Keeps (s.gpr .r5) (s.gpr .r6).toNat layout.prepScratch s.mem s'.mem
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

theorem size_eq : layout.size = 8 * slots := rfl

/-- The registers the bodies may write. -/
def bodyWrites : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
   .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- The callee-saved registers, from those the bodies restore and `r2`. -/
theorem helperAbi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hlr : s'.lr = s.lr) (h₁ : ∀ i < 18, s'.gpr (sreg i) = s.gpr (sreg i)) (h₂ : s'.gpr .r2 = s.gpr .r2) :
    abiPreserved s s' := by
  refine ⟨fun r hr => ?_, Exec.sp he, hlr⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact h₂
  · exact h₁ 0 (by omega)
  · exact h₁ 1 (by omega)
  · exact h₁ 2 (by omega)
  · exact h₁ 3 (by omega)
  · exact h₁ 4 (by omega)
  · exact h₁ 5 (by omega)
  · exact h₁ 6 (by omega)
  · exact h₁ 7 (by omega)
  · exact h₁ 8 (by omega)
  · exact h₁ 9 (by omega)
  · exact h₁ 10 (by omega)
  · exact h₁ 11 (by omega)
  · exact h₁ 12 (by omega)
  · exact h₁ 13 (by omega)
  · exact h₁ 14 (by omega)
  · exact h₁ 15 (by omega)
  · exact h₁ 16 (by omega)
  · exact h₁ 17 (by omega)

theorem prep_correct (s : State) (hs : prepPPC64LE.pre s) :
    ∃ t s', Exec isa prepareKeys s t s' ∧ abiPreserved s s' ∧ prepPPC64LE.post s s' := by
  obtain ⟨hrd, hwr, dSS, fitK, fitW, -, hsz⟩ := hs
  rw [size_eq] at hsz
  have hl : 8 * slots ≤ (s.gpr .r6).toNat * 8 := by omega
  have w := prepareBody_wp (s₀ := narrow s (s.gpr .r5)) hrd rfl
    (dSS.sub_right (Region.sub_prefix hl)) fitK (by show (s.gpr .r5).toNat + 8 * slots ≤ 2 ^ 64; omega)
  have hn : prepareKeys.noCalls = true := by lit_decide
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.keep bodyWrites w (by lit_decide) hn
  have f := (Exec.regions he (by lit_decide)).2.2.2
  have he' := exec_widen hwr hl he
  refine ⟨t, s'.withRegions s.rd s.wr, he',
    helperAbi_of he' (Exec.lr he' hn (by lit_decide)) h₁ (h₃.gpr (by decide)), ?_,
    keeps_of_frame f fitW fun i hi => ?_⟩
  · refine holds_of_words ?_
    rw [← specDirA_dirOf, ofSpecDir_specDirA]
    exact h₂
  · have := hi _ (List.mem_singleton_self _)
    simp only at this
    omega

theorem prepTaint_agree (s₁ s₂ : State) (_ : prepPPC64LE.pre s₁) (_ : prepPPC64LE.pre s₂)
    (hp : prepPPC64LE.pub s₁ s₂) : taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem prep_ct : ConstantTime isa prepPPC64LE.pre prepPPC64LE.pub prepareKeys :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) prepTaint_agree (by taint_decide)

/-- A state satisfying the preparation's precondition. -/
def prepSat : State where
  gpr r := match r with | .r3 => 0x1000 | .r5 => 0x2000 | .r6 => 402 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 402 * 8⟩]

theorem prepare_verified :
    Verified target prepareKeys (Proof.Sm4.Prepared.prepareContract layout abi) :=
  Verified.of_correct prep_correct prep_ct (by
    sig_implies [Proof.Sm4.Prepared.prepareContract, Proof.Sm4.Prepared.prepareSig, prepPPC64LE, abi,
      argRegs, size_eq, slots] [prepSat] using prepSat)

/-! ## A batch -/

/-- `vg_sm4_crypt_prepared` on PPC64LE. -/
def cryptPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let ws : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat * 8⟩
    s.rd = [] ∧ s.wr = [ws] ∧ (s.gpr .r3).toNat + (s.gpr .r4).toNat * 8 ≤ 2 ^ 64 ∧
      layout.size ≤ 8 * (s.gpr .r4).toNat ∧ ∃ k d, Holds layout s.mem (s.gpr .r3) k d
  post s s' :=
    (∀ k d, Holds layout s.mem (s.gpr .r3) k d →
      Spec.Sm4.blocksAt s'.mem (s.gpr .r3 + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Sm4.ecb k d (Spec.Sm4.blocksAt s.mem (s.gpr .r3 + BitVec.ofNat 64 layout.buf) layout.blocks)) ∧
      Keeps (s.gpr .r3) (s.gpr .r4).toNat layout.cryptScratch s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.sp = s₂.sp

theorem specDirA_ofSpecDir (d : Spec.Sm4.Direction) : specDirA (ofSpecDir d) = d := by cases d <;> rfl

theorem blocks_of (B : Addr) {m m' : Mem} {k : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction}
    (h : ∀ j < 16, Spec.Sm4.blockAt m' (B + BitVec.ofNat 64 (8 * tailSlot + 16 * j)) =
        Proof.Sm4.blockFn k d (Spec.Sm4.blockAt m (B + BitVec.ofNat 64 (8 * tailSlot + 16 * j)))) :
    Spec.Sm4.blocksAt m' (B + BitVec.ofNat 64 layout.buf) layout.blocks =
      Spec.Sm4.ecb k d (Spec.Sm4.blocksAt m (B + BitVec.ofNat 64 layout.buf) layout.blocks) := by
  rw [Proof.Sm4.ecb_eq]
  simp only [Spec.Sm4.blocksAt, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  simp only [List.mem_range] at hj
  simp only [Function.comp_apply, VG.Offset.add_add]
  exact h j hj

/-- The masks' bytes, the same in two working spaces holding tables. -/
theorem mask_byte {m m' : Mem} {B : Addr} {k k' : Spec.Sm4.Schedule} {d d' : Dir}
    (h : WordsAt m B k d) (h' : WordsAt m' B k' d') {i : Nat} (hi : 8 * evenSlot ≤ i ∧ i < 8 * (grpSlot + 1)) :
    m' (B + BitVec.ofNat 64 i) = m (B + BitVec.ofNat 64 i) := by
  have hw : (evenSlot ≤ i / 8 ∧ i / 8 ≤ grpSlot) ∨ (tableSlot ≤ i / 8 ∧ i / 8 < tableEnd) := .inl (by omega)
  rw [word_byte_addr, byte_of_readW m' (wordAddr B (i / 8)) (j := i % 8) (by omega),
    byte_of_readW m (wordAddr B (i / 8)) (j := i % 8) (by omega), h _ hw, h' _ hw]
  have hm : ∀ (k : Spec.Sm4.Schedule) (d : Dir), preparedWord k d (i / 8) =
      (keyMasks.find? (·.1 = i / 8)).elim 0 (·.2) := fun _ _ => by
    have hc : i / 8 < tableSlot := by rw [tableSlot_eq]; rw [grpSlot_eq] at hi; omega
    simp only [preparedWord, hc, ↓reduceIte]
  rw [hm, hm]

theorem crypt_correct (s : State) (hs : cryptPPC64LE.pre s) :
    ∃ t s', Exec isa cryptPrepared s t s' ∧ abiPreserved s s' ∧ cryptPPC64LE.post s s' := by
  obtain ⟨-, hwr, fitW, hsz, k₀, d₀, hH⟩ := hs
  rw [size_eq] at hsz
  have hl : 8 * slots ≤ (s.gpr .r4).toNat * 8 := by omega
  have hwN : (⟨(narrow s (s.gpr .r3)).gpr .r3, 8 * slots⟩ : Region) ∈ (narrow s (s.gpr .r3)).wr := by simp
  have fitN : ((narrow s (s.gpr .r3)).gpr .r3).toNat + 8 * slots ≤ 2 ^ 64 := by
    show (s.gpr .r3).toNat + 8 * slots ≤ 2 ^ 64; omega
  have hn : cryptPrepared.noCalls = true := by lit_decide
  obtain ⟨t, s', he, ⟨h₁, hR, hF, -, -, -⟩, h₃⟩ := WP.keep bodyWrites
    (cryptBody_wp hwN fitN (readyAt_of_words (words_of_holds hH))) (by lit_decide) hn
  have he' := exec_widen hwr hl he
  refine ⟨t, s'.withRegions s.rd s.wr, he', helperAbi_of he' (Exec.lr he' hn (by lit_decide)) h₁ (h₃.gpr (by decide)),
    fun k d hk => ?_, fun i hi hout => ?_⟩
  · obtain ⟨t₂, s₂, he₂, -, -, -, -, -, hB₂⟩ := cryptBody_wp hwN fitN (readyAt_of_words (words_of_holds hk))
    obtain ⟨-, rfl⟩ := Exec.det he he₂
    refine blocks_of _ fun j hj => ?_
    have := hB₂ j hj
    rw [specDirA_ofSpecDir] at this
    exact this
  · have hfit := fitW
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    rw [evenSlot_eq, grpSlot_eq, tableSlot_eq, savedSlot_eq, slots_eq] at hout
    by_cases hm : 384 ≤ i ∧ i < 408
    · exact mask_byte (words_of_holds hH) (words_of_readyAt hR) (by rw [evenSlot_eq, grpSlot_eq]; omega)
    · refine hF _ fun r hr hc => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [Region.Contains, narrow, State.withRegions_gpr] at hc
      · rw [Mem.sub_ofNat_toNat _ (by omega), tableSlot_eq] at hc; omega
      · rw [VG.Offset.sub_toNat' _ (by rw [savedSlot_eq]; omega) (by omega), savedSlot_eq] at hc
        split at hc <;> omega

theorem cryptTaint_agree (s₁ s₂ : State) (_ : cryptPPC64LE.pre s₁) (_ : cryptPPC64LE.pre s₂)
    (hp : cryptPPC64LE.pub s₁ s₂) : taint.Agree (Taint.ofRegs [.r3, .r4]) s₁ s₂ := by
  obtain ⟨h1, h2, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> with_reducible assumption

theorem crypt_ct : ConstantTime isa cryptPPC64LE.pre cryptPPC64LE.pub cryptPrepared :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4]) cryptTaint_agree (by taint_decide)

/-- Round keys of zeros. -/
def zeroSchedule : Spec.Sm4.Schedule := Vector.replicate 32 0

/-- A working space at `0x2000` holding the table of `zeroSchedule` for
encryption. -/
def cryptSatMem : Mem := fun a =>
  if 0x2000 ≤ a.toNat ∧ a.toNat < 0x2000 + 3216 then layout.encode zeroSchedule .encrypt (a.toNat - 0x2000) else 0

theorem cryptSat_holds : Holds layout cryptSatMem 0x2000 zeroSchedule .encrypt := by
  intro r hr i hi
  have hr' : r.1 + i < 3072 := by
    rw [layout_table] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only at hi ⊢ <;> omega
  have ht : ((0x2000 : Addr) + BitVec.ofNat 64 (r.1 + i)).toNat = 0x2000 + (r.1 + i) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0x2000 : Addr).toNat = 0x2000 from rfl]; omega
  have hc : 0x2000 ≤ 0x2000 + (r.1 + i) ∧ 0x2000 + (r.1 + i) < 0x2000 + 3216 := ⟨by omega, by omega⟩
  simp only [cryptSatMem, ht, hc, and_self, ↓reduceIte]
  rw [show 0x2000 + (r.1 + i) - 0x2000 = r.1 + i by omega]

/-- A state satisfying the batch's precondition. -/
def cryptSat : State where
  gpr r := match r with | .r3 => 0x2000 | .r4 => 402 | _ => 0
  lr := 0
  sp := 0x8000
  mem := cryptSatMem
  rd := []
  wr := [⟨0x2000, 402 * 8⟩]

theorem crypt_implies : cryptPPC64LE.Implies (Proof.Sm4.Prepared.cryptContract layout abi) where
  pre := by
    sig_implies_pre [Proof.Sm4.Prepared.cryptContract, Proof.Sm4.Prepared.cryptSig, cryptPPC64LE, abi,
      argRegs]
  post := by
    sig_implies_post [Proof.Sm4.Prepared.cryptContract, Proof.Sm4.Prepared.cryptSig, cryptPPC64LE, abi,
      argRegs]
  pub := by
    sig_implies_pub [Proof.Sm4.Prepared.cryptContract, Proof.Sm4.Prepared.cryptSig, cryptPPC64LE, abi,
      argRegs]
  sat := by
    refine ⟨cryptSat, ?_⟩
    sig_pre [Proof.Sm4.Prepared.cryptContract, Proof.Sm4.Prepared.cryptSig, abi, argRegs]
    sig_and_intros
    all_goals first
      | decide
      | exact ⟨_, _, cryptSat_holds⟩
      | (rw [size_eq, slots_eq]; decide)

theorem crypt_verified :
    Verified target cryptPrepared (Proof.Sm4.Prepared.cryptContract layout abi) :=
  Verified.of_correct crypt_correct crypt_ct crypt_implies

end VG.Proof.Sm4.PPC64LE
