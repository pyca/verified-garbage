module

public import VerifiedGarbage.Proof.Sm4.RISCV64.PreparedBody
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Sm4.RISCV64.Prologue
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sm4.RISCV64.LayersLit
import VerifiedGarbage.Proof.Framework.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Sm4.RISCV64.PreparedBody
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Sm4.RISCV64.Prologue
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4.RISCV64.LayersLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Proof.Sm4.Contract
public import VerifiedGarbage.Proof.Sm4.Prepared
meta import VerifiedGarbage.Proof.Sm4.Prepared

/-!
# SM4's prepared round keys and batches on RISCV64 meet their contracts

`prepare_verified` and `crypt_verified`: `vg_sm4_prepare_keys` and
`vg_sm4_crypt_prepared` against `Proof.Sm4.Prepared`, with `layout`. Each
body runs from the state narrowed to ECB's scratch buffer (`prepareBody_wp`,
`cryptBody_wp`) and then from the whole working space (`Exec.widen`), which it
changes only where the narrowed run may. A batch's blocks are ECB in the
direction and under the round keys of any table encoding that its working
space holds: the run from it is the run from the table the precondition
gives (`Exec.det`). Constant time by the taint analysis: the pointers,
`ws_len` and `decrypt` are public. As on PPC64LE
(`Proof/Sm4/PPC64LE/PreparedVerified.lean`), with the working space aligned
to 8 bytes.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.Sm4.RISCV64
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

/-- `vg_sm4_prepare_keys` on RISCV64. -/
def prepRISCV64 : Contract RISCV64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 128⟩
    let ws : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat * 8⟩
    s.rd = [sched] ∧ s.wr = [ws] ∧ sched.Disjoint ws ∧ (s.gpr .a0).toNat + 128 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat + (s.gpr .a3).toNat * 8 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat ≤ 1 ∧
      layout.size ≤ 8 * (s.gpr .a3).toNat ∧ (s.gpr .a2).toNat % 8 = 0
  post s s' :=
    Holds layout s'.mem (s.gpr .a2) (Spec.Sm4.scheduleAt s.mem (s.gpr .a0))
        (Proof.Sm4.directionOf (s.gpr .a1).toNat) ∧
      Keeps (s.gpr .a2) (s.gpr .a3).toNat layout.prepScratch s.mem s'.mem
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

theorem size_eq : layout.size = 8 * slots := rfl

/-- The registers the bodies may write: all but `ra`. -/
def bodyWrites : List Reg :=
  [.t0, .t1, .t2, .s0, .s1, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9,
   .s10, .s11, .t3, .t4, .t5, .t6]

/-- The callee-saved registers, from those the bodies restore. -/
theorem helperAbi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hra : s'.gpr .ra = s.gpr .ra) (h₁ : ∀ i < 12, s'.gpr (sreg i) = s.gpr (sreg i)) :
    abiPreserved s s' := by
  refine ⟨fun r hr => ?_, Exec.sp he, hra⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

theorem prep_correct (s : State) (hs : prepRISCV64.pre s) :
    ∃ t s', Exec isa prepareKeys s t s' ∧ abiPreserved s s' ∧ prepRISCV64.post s s' := by
  obtain ⟨hrd, hwr, dSS, fitK, fitW, -, hsz, hal⟩ := hs
  rw [size_eq] at hsz
  have hl : 8 * slots ≤ (s.gpr .a3).toNat * 8 := by omega
  have w := prepareBody_wp (s₀ := narrow s (s.gpr .a2)) hrd rfl
    (dSS.sub_right (Region.sub_prefix hl)) fitK (by show (s.gpr .a2).toNat + 8 * slots ≤ 2 ^ 64; omega) hal
  have hn : callFree prepareKeys = true := by lit_decide
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.keep bodyWrites w (by lit_decide) hn
  have f := (Exec.regions he (by lit_decide)).2.2.2
  have he' := exec_widen hwr hl he
  refine ⟨t, s'.withRegions s.rd s.wr, he', helperAbi_of he' (h₃.gpr (by decide)) h₁, ?_,
    keeps_of_frame f fitW fun i hi => ?_⟩
  · refine holds_of_words ?_
    rw [← specDirA_dirOf, ofSpecDir_specDirA]
    exact h₂
  · have := hi _ (List.mem_singleton_self _)
    simp only at this
    omega

theorem prepTaint_agree (s₁ s₂ : State) (_ : prepRISCV64.pre s₁) (_ : prepRISCV64.pre s₂)
    (hp : prepRISCV64.pub s₁ s₂) : taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h1, h2, h3, h4]

theorem prep_ct : ConstantTime isa prepRISCV64.pre prepRISCV64.pub prepareKeys :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) prepTaint_agree (by taint_decide)

/-- A state satisfying the preparation's precondition. -/
def prepSat : State where
  gpr r := match r with | .a0 => 0x1000 | .a2 => 0x2000 | .a3 => 396 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 396 * 8⟩]

theorem prepare_verified :
    Verified target prepareKeys (Proof.Sm4.Prepared.prepareContract layout abi) :=
  Verified.of_correct prep_correct prep_ct (by
    sig_implies [Proof.Sm4.Prepared.prepareContract, Proof.Sm4.Prepared.prepareSig, prepRISCV64, abi,
      argRegs, size_eq, slots, savedSlot, tableEnd, tableSlot] [prepSat] using prepSat)

/-! ## A batch -/

/-- `vg_sm4_crypt_prepared` on RISCV64. -/
def cryptRISCV64 : Contract RISCV64.isa where
  pre s :=
    let ws : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat * 8⟩
    s.rd = [] ∧ s.wr = [ws] ∧ (s.gpr .a0).toNat + (s.gpr .a1).toNat * 8 ≤ 2 ^ 64 ∧
      layout.size ≤ 8 * (s.gpr .a1).toNat ∧ (s.gpr .a0).toNat % 8 = 0 ∧ ∃ k d, Holds layout s.mem (s.gpr .a0) k d
  post s s' :=
    (∀ k d, Holds layout s.mem (s.gpr .a0) k d →
      Spec.Sm4.blocksAt s'.mem (s.gpr .a0 + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Sm4.ecb k d (Spec.Sm4.blocksAt s.mem (s.gpr .a0 + BitVec.ofNat 64 layout.buf) layout.blocks)) ∧
      Keeps (s.gpr .a0) (s.gpr .a1).toNat layout.cryptScratch s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.sp = s₂.sp

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
    (h : WordsAt m B k d) (h' : WordsAt m' B k' d') {i : Nat} (hi : 8 * evenSlot ≤ i ∧ i < 8 * (oneSlot + 1)) :
    m' (B + BitVec.ofNat 64 i) = m (B + BitVec.ofNat 64 i) := by
  have hw : (evenSlot ≤ i / 8 ∧ i / 8 ≤ oneSlot) ∨ (tableSlot ≤ i / 8 ∧ i / 8 < tableEnd) := .inl (by omega)
  rw [word_byte_addr, byte_of_readW m' (wordAddr B (i / 8)) (j := i % 8) (by omega),
    byte_of_readW m (wordAddr B (i / 8)) (j := i % 8) (by omega), h _ hw, h' _ hw]
  have hm : ∀ (k : Spec.Sm4.Schedule) (d : Dir), preparedWord k d (i / 8) =
      (keyMasks.find? (·.1 = i / 8)).elim 0 (·.2) := fun _ _ => by
    have hc : i / 8 < tableSlot := by rw [tableSlot_eq]; rw [oneSlot_eq] at hi; omega
    simp only [preparedWord, hc, ↓reduceIte]
  rw [hm, hm]

theorem crypt_correct (s : State) (hs : cryptRISCV64.pre s) :
    ∃ t s', Exec isa cryptPrepared s t s' ∧ abiPreserved s s' ∧ cryptRISCV64.post s s' := by
  obtain ⟨-, hwr, fitW, hsz, hal, k₀, d₀, hH⟩ := hs
  rw [size_eq] at hsz
  have hl : 8 * slots ≤ (s.gpr .a1).toNat * 8 := by omega
  have hwN : (⟨(narrow s (s.gpr .a0)).gpr .a0, 8 * slots⟩ : Region) ∈ (narrow s (s.gpr .a0)).wr := by simp
  have fitN : ((narrow s (s.gpr .a0)).gpr .a0).toNat + 8 * slots ≤ 2 ^ 64 := by
    show (s.gpr .a0).toNat + 8 * slots ≤ 2 ^ 64; omega
  have hn : callFree cryptPrepared = true := by lit_decide
  obtain ⟨t, s', he, ⟨h₁, hR, hF, -, -, -⟩, h₃⟩ := WP.keep bodyWrites
    (cryptBody_wp hwN fitN hal (readyAt_of_words (words_of_holds hH))) (by lit_decide) hn
  have he' := exec_widen hwr hl he
  refine ⟨t, s'.withRegions s.rd s.wr, he', helperAbi_of he' (h₃.gpr (by decide)) h₁,
    fun k d hk => ?_, fun i hi hout => ?_⟩
  · obtain ⟨t₂, s₂, he₂, -, -, -, -, -, hB₂⟩ := cryptBody_wp hwN fitN hal (readyAt_of_words (words_of_holds hk))
    obtain ⟨-, rfl⟩ := Exec.det he he₂
    refine blocks_of _ fun j hj => ?_
    have := hB₂ j hj
    rw [specDirA_ofSpecDir] at this
    exact this
  · have hfit := fitW
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    rw [evenSlot_eq, bsBase, tableSlot_eq, savedSlot_eq, slots_eq] at hout
    by_cases hm : 320 ≤ i ∧ i < 360
    · exact mask_byte (words_of_holds hH) (words_of_readyAt hR) (by rw [evenSlot_eq, oneSlot_eq]; omega)
    · refine hF _ fun r hr hc => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [Region.Contains, narrow, State.withRegions_gpr] at hc
      · rw [Mem.sub_ofNat_toNat _ (by omega), tableSlot_eq] at hc; omega
      · rw [VG.Offset.sub_toNat' _ (by rw [savedSlot_eq]; omega) (by omega), savedSlot_eq] at hc
        split at hc <;> omega

theorem cryptTaint_agree (s₁ s₂ : State) (_ : cryptRISCV64.pre s₁) (_ : cryptRISCV64.pre s₂)
    (hp : cryptRISCV64.pub s₁ s₂) : taint.Agree (Taint.ofRegs [.a0, .a1]) s₁ s₂ := by
  obtain ⟨h1, h2, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [h1, h2]

theorem crypt_ct : ConstantTime isa cryptRISCV64.pre cryptRISCV64.pub cryptPrepared :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1]) cryptTaint_agree (by taint_decide)

/-- Round keys of zeros. -/
def zeroSchedule : Spec.Sm4.Schedule := Vector.replicate 32 0

/-- A working space at `0x2000` holding the table of `zeroSchedule` for
encryption. -/
def cryptSatMem : Mem := fun a =>
  if 0x2000 ≤ a.toNat ∧ a.toNat < 0x2000 + 3168 then layout.encode zeroSchedule .encrypt (a.toNat - 0x2000) else 0

theorem cryptSat_holds : Holds layout cryptSatMem 0x2000 zeroSchedule .encrypt := by
  intro r hr i hi
  have hr' : r.1 + i < 3072 := by
    rw [layout_table] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only at hi ⊢ <;> omega
  have ht : ((0x2000 : Addr) + BitVec.ofNat 64 (r.1 + i)).toNat = 0x2000 + (r.1 + i) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0x2000 : Addr).toNat = 0x2000 from rfl]; omega
  have hc : 0x2000 ≤ 0x2000 + (r.1 + i) ∧ 0x2000 + (r.1 + i) < 0x2000 + 3168 := ⟨by omega, by omega⟩
  simp only [cryptSatMem, ht, hc, and_self, ↓reduceIte]
  rw [show 0x2000 + (r.1 + i) - 0x2000 = r.1 + i by omega]

/-- A state satisfying the batch's precondition. -/
def cryptSat : State where
  gpr r := match r with | .a0 => 0x2000 | .a1 => 396 | _ => 0
  sp := 0x8000
  mem := cryptSatMem
  rd := []
  wr := [⟨0x2000, 396 * 8⟩]

theorem crypt_implies : cryptRISCV64.Implies (Proof.Sm4.Prepared.cryptContract layout abi) where
  pre := by
    sig_implies_pre [Proof.Sm4.Prepared.cryptContract, Proof.Sm4.Prepared.cryptSig, cryptRISCV64, abi,
      argRegs]
  post := by
    sig_implies_post [Proof.Sm4.Prepared.cryptContract, Proof.Sm4.Prepared.cryptSig, cryptRISCV64, abi,
      argRegs]
  pub := by
    sig_implies_pub [Proof.Sm4.Prepared.cryptContract, Proof.Sm4.Prepared.cryptSig, cryptRISCV64, abi,
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

end VG.Proof.Sm4.RISCV64
