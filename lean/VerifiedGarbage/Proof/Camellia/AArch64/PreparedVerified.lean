module

public import VerifiedGarbage.Proof.Camellia.AArch64.PreparedBody
meta import VerifiedGarbage.Proof.Camellia.AArch64.PreparedBody
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Camellia.AArch64.Lit
meta import VerifiedGarbage.Proof.Camellia.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Camellia's prepared subkeys and batches on AArch64 meet their contracts

`prepare_verified` and `crypt_verified`: `vg_camellia_prepare_keys` and
`vg_camellia_crypt_prepared` against `Spec.Camellia.Prepared`, with
`layout`. Each body runs from the state narrowed to ECB's scratch buffer
(`prepareBody_wp`, `cryptBody_wp`) and then from the whole working space
(`Exec.widen`), which it changes only where the narrowed run may. A batch's
blocks are ECB in the direction and under the subkeys of any words whose
table its working space holds: the run from it is the run from the table
the precondition gives (`Exec.det`). Constant time by the taint analysis:
the pointers, `ws_len`, `rounds` and `decrypt` are public.
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Camellia.AArch64
open VG.Proof.Camellia (blockFn)
open VG.Spec.Camellia.Prepared (Holds Keeps)

/-! ## Narrowing the working space -/

/-- `s` with its writable region the first `8 * slots` bytes of `ws`. -/
abbrev narrow (s : State) (ws : Addr) : State := s.withRegions s.rd [⟨ws, 8 * slots⟩]

theorem narrow_covers (s : State) {ws : Addr} {len : Nat} (hw : s.wr = [⟨ws, len⟩]) (hl : 8 * slots ≤ len) :
    Covers ((narrow s ws).rd ++ (narrow s ws).wr) (s.rd ++ s.wr) ∧ Covers (narrow s ws).wr s.wr := by
  have h : Covers [⟨ws, 8 * slots⟩] s.wr := Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨ws, len⟩, by rw [hw]; simp, 0, by rw [BitVec.add_zero], by show 0 + 8 * slots ≤ len; omega⟩
  exact ⟨Covers.append (Covers.refl _) h, h⟩

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

theorem size_eq : layout.size = 8 * slots := rfl

/-- The callee-saved registers, from those the bodies restore and `x30`. -/
theorem helperAbi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hv : ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)
    (h₁ : ∀ i < 10, s'.gpr (sreg i) = s.gpr (sreg i)) (h₃ : s'.gpr .x30 = s.gpr .x30) :
    abiPreserved s s' := by
  refine ⟨fun r hr => ?_, Exec.sp he, hv⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact h₃

/-! ## The preparation -/

/-- `vg_camellia_prepare_keys` on AArch64. -/
def prepAArch64 : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 272⟩
    let ws : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat * 8⟩
    s.rd = [sched] ∧ s.wr = [ws] ∧ sched.Disjoint ws ∧ (s.gpr .x0).toNat + 272 ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + (s.gpr .x4).toNat * 8 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 18 ∨ (s.gpr .x1).toNat = 24) ∧ (s.gpr .x2).toNat ≤ 1 ∧
      layout.size ≤ 8 * (s.gpr .x4).toNat
  post s s' :=
    Holds layout s'.mem (s.gpr .x3) (s.gpr .x1).toNat
        (Spec.Camellia.Prepared.wordsAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Spec.Camellia.Prepared.directionOf (s.gpr .x2).toNat) ∧
      Keeps (s.gpr .x3) (s.gpr .x4).toNat layout.prepScratch s.mem s'.mem
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

theorem prep_correct (s : State) (hs : prepAArch64.pre s) :
    ∃ t s', Exec isa prepareKeys s t s' ∧ abiPreserved s s' ∧ prepAArch64.post s s' := by
  obtain ⟨hrd, hwr, dSS, fitK, fitW, hR, -, hsz⟩ := hs
  rw [size_eq] at hsz
  have hl : 8 * slots ≤ (s.gpr .x4).toNat * 8 := by omega
  have w := prepareBody_wp (s₀ := narrow s (s.gpr .x3)) hrd rfl
    (dSS.sub_right (Region.sub_prefix hl)) fitK (by show (s.gpr .x3).toNat + 8 * slots ≤ 2 ^ 64; omega) hR
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) w (by lit_decide) (by lit_decide)
  have f := (Exec.regions he (by lit_decide)).2.2.2
  have he' := exec_widen hwr hl he
  refine ⟨t, s'.withRegions s.rd s.wr, he',
    helperAbi_of he' (Exec.preservedV he' (by lit_decide)) h₁ (h₃ _ (by simp)), ?_, keeps_of_frame f fitW fun i hi => ?_⟩
  · refine holds_of_words ?_
    rw [← specDir_dirOf, ofSpecDir_specDir]
    exact h₂
  · have := hi _ (List.mem_singleton_self _)
    simp only at this
    omega

theorem prepTaint_agree (s₁ s₂ : State) (_ : prepAArch64.pre s₁) (_ : prepAArch64.pre s₂)
    (hp : prepAArch64.pub s₁ s₂) : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem prep_ct : ConstantTime isa prepAArch64.pre prepAArch64.pub prepareKeys :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) prepTaint_agree (by taint_decide)

/-- A state satisfying the preparation's precondition. -/
def prepSat : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 18 | .x3 => 0x2000 | .x4 => 406 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 406 * 8⟩]

theorem prepare_verified :
    Verified AArch64.target prepareKeys (Spec.Camellia.Prepared.prepareContract layout AArch64.abi) :=
  Verified.of_correct prep_correct prep_ct (by
    sig_implies [Spec.Camellia.Prepared.prepareContract, Spec.Camellia.Prepared.prepareSig, prepAArch64,
      AArch64.abi, AArch64.argRegs, size_eq, slots] [prepSat] using prepSat)

/-! ## A batch -/

/-- `vg_camellia_crypt_prepared` on AArch64. -/
def cryptAArch64 : Contract AArch64.isa where
  pre s :=
    let ws : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat * 8⟩
    s.rd = [] ∧ s.wr = [ws] ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat * 8 ≤ 2 ^ 64 ∧
      ((s.gpr .x0).toNat = 18 ∨ (s.gpr .x0).toNat = 24) ∧ layout.size ≤ 8 * (s.gpr .x2).toNat ∧
      ∃ w d, Holds layout s.mem (s.gpr .x1) (s.gpr .x0).toNat w d
  post s s' :=
    (∀ w d, Holds layout s.mem (s.gpr .x1) (s.gpr .x0).toNat w d →
      Spec.Camellia.blocksAt s'.mem (s.gpr .x1 + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Camellia.ecb (Spec.Camellia.subkeysOfWords (s.gpr .x0).toNat w) d
          (Spec.Camellia.blocksAt s.mem (s.gpr .x1 + BitVec.ofNat 64 layout.buf) layout.blocks)) ∧
      Keeps (s.gpr .x1) (s.gpr .x2).toNat layout.cryptScratch s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

theorem blocks_of (B : Addr) {m m' : Mem} {k : Spec.Camellia.Subkeys} {d : Spec.Camellia.Direction}
    (h : ∀ j < 8, Spec.Camellia.blockAt m' (B + BitVec.ofNat 64 (8 * tailSlot + 16 * j)) =
        blockFn k d (Spec.Camellia.blockAt m (B + BitVec.ofNat 64 (8 * tailSlot + 16 * j)))) :
    Spec.Camellia.blocksAt m' (B + BitVec.ofNat 64 layout.buf) layout.blocks =
      Spec.Camellia.ecb k d (Spec.Camellia.blocksAt m (B + BitVec.ofNat 64 layout.buf) layout.blocks) := by
  rw [Proof.Camellia.ecb_eq]
  simp only [Spec.Camellia.blocksAt, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  simp only [List.mem_range] at hj
  simp only [Function.comp_apply, VG.Offset.add_add]
  exact h j hj

/-- The masks' bytes, the same in two working spaces holding tables. -/
theorem mask_byte {R : Nat} {m m' : Mem} {B : Addr} {w w' : List (BitVec 64)} {d d' : Dir}
    (h : TableWordsAt R m B w d) (h' : TableWordsAt R m' B w' d') {i : Nat} (hi : 8 * evenSlot ≤ i ∧ i < 8 * (m3Slot + 1)) :
    m' (B + BitVec.ofNat 64 i) = m (B + BitVec.ofNat 64 i) := by
  have hw : (evenSlot ≤ i / 8 ∧ i / 8 ≤ m3Slot) ∨ (keySlot ≤ i / 8 ∧ i / 8 < keySlot + 8 * (8 * (R / 6) + 2)) :=
    .inl (by omega)
  rw [word_byte_addr, byte_of_readW m' (wordAddr B (i / 8)) (j := i % 8) (by omega),
    byte_of_readW m (wordAddr B (i / 8)) (j := i % 8) (by omega), h _ hw, h' _ hw]
  have hm : ∀ (w : List (BitVec 64)) (d : Dir), preparedWord R w d (i / 8) =
      (layerMasks.find? (·.1 = i / 8)).elim 0 (·.2) := fun _ _ => by
    have hc : i / 8 < keySlot := by rw [keySlot_eq]; rw [m3Slot_eq] at hi; omega
    simp only [preparedWord, hc, ↓reduceIte]
  rw [hm, hm]

theorem crypt_correct (s : State) (hs : cryptAArch64.pre s) :
    ∃ t s', Exec isa cryptPrepared s t s' ∧ abiPreserved s s' ∧ cryptAArch64.post s s' := by
  obtain ⟨-, hwr, fitW, hR, hsz, w₀, d₀, hH⟩ := hs
  rw [size_eq] at hsz
  have hl : 8 * slots ≤ (s.gpr .x2).toNat * 8 := by omega
  have hwN : (⟨(narrow s (s.gpr .x1)).gpr .x1, 8 * slots⟩ : Region) ∈ (narrow s (s.gpr .x1)).wr := by simp
  have fitN : ((narrow s (s.gpr .x1)).gpr .x1).toNat + 8 * slots ≤ 2 ^ 64 := by
    show (s.gpr .x1).toNat + 8 * slots ≤ 2 ^ 64; omega
  obtain ⟨t, s', he, ⟨h₁, hRd, hF, -, -, -⟩, h₃⟩ := WP.gprs (rs := [.x30])
    (cryptBody_wp hwN fitN hR (readyAt_of_words (words_of_holds hH))) (by lit_decide) (by lit_decide)
  have he' := exec_widen hwr hl he
  refine ⟨t, s'.withRegions s.rd s.wr, he', helperAbi_of he' (Exec.preservedV he' (by lit_decide)) h₁ (h₃ _ (by simp)),
    fun w d hk => ?_, fun i hi hout => ?_⟩
  · obtain ⟨t₂, s₂, he₂, -, -, -, -, -, hB₂⟩ := cryptBody_wp hwN fitN hR (readyAt_of_words (words_of_holds hk))
    obtain ⟨-, rfl⟩ := Exec.det he he₂
    refine blocks_of _ fun j hj => ?_
    have := hB₂ j hj
    rw [specDir_ofSpecDir] at this
    exact this
  · have hfit := fitW
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    rw [evenSlot_eq, m3Slot_eq, keySlot_eq, savedSlot_eq, tailSlot_eq] at hout
    by_cases hm : 384 ≤ i ∧ i < 424
    · exact mask_byte (words_of_holds hH) (words_of_readyAt hRd) (by rw [evenSlot_eq, m3Slot_eq]; omega)
    · refine hF _ fun r hr hc => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [Region.Contains, narrow, State.withRegions_gpr] at hc
      · rw [Mem.sub_ofNat_toNat _ (by omega), keySlot_eq] at hc; omega
      · rw [VG.Offset.sub_toNat' _ (by rw [savedSlot_eq]; omega) (by omega), savedSlot_eq] at hc
        split at hc <;> omega

theorem cryptTaint_agree (s₁ s₂ : State) (_ : cryptAArch64.pre s₁) (_ : cryptAArch64.pre s₂)
    (hp : cryptAArch64.pub s₁ s₂) : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

theorem crypt_ct : ConstantTime isa cryptAArch64.pre cryptAArch64.pub cryptPrepared :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) cryptTaint_agree (by taint_decide)

/-- A working space at `0x2000` holding the table of no words (all zeros)
for 18 rounds of encryption. -/
def cryptSatMem : Mem := fun a =>
  if 0x2000 ≤ a.toNat ∧ a.toNat < 0x2000 + 3248 then layout.encode 18 [] .encrypt (a.toNat - 0x2000) else 0

theorem cryptSat_holds : Holds layout cryptSatMem 0x2000 18 [] .encrypt := by
  intro r hr i hi
  have hr' : r.1 + i < 3248 := by
    rw [layout_table] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only at hi ⊢ <;> omega
  have ht : ((0x2000 : Addr) + BitVec.ofNat 64 (r.1 + i)).toNat = 0x2000 + (r.1 + i) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0x2000 : Addr).toNat = 0x2000 from rfl]; omega
  have hc : 0x2000 ≤ 0x2000 + (r.1 + i) ∧ 0x2000 + (r.1 + i) < 0x2000 + 3248 := ⟨by omega, by omega⟩
  simp only [cryptSatMem, ht, hc, and_self, ↓reduceIte]
  rw [show 0x2000 + (r.1 + i) - 0x2000 = r.1 + i by omega]

/-- A state satisfying the batch's precondition. -/
def cryptSat : State where
  gpr r := match r with | .x0 => 18 | .x1 => 0x2000 | .x2 => 406 | _ => 0
  sp := 0x8000
  mem := cryptSatMem
  rd := []
  wr := [⟨0x2000, 406 * 8⟩]

theorem crypt_implies : cryptAArch64.Implies (Spec.Camellia.Prepared.cryptContract layout AArch64.abi) where
  pre := by
    sig_implies_pre [Spec.Camellia.Prepared.cryptContract, Spec.Camellia.Prepared.cryptSig, cryptAArch64,
      AArch64.abi, AArch64.argRegs]
  post := by
    sig_implies_post [Spec.Camellia.Prepared.cryptContract, Spec.Camellia.Prepared.cryptSig, cryptAArch64,
      AArch64.abi, AArch64.argRegs]
  pub := by
    sig_implies_pub [Spec.Camellia.Prepared.cryptContract, Spec.Camellia.Prepared.cryptSig, cryptAArch64,
      AArch64.abi, AArch64.argRegs]
  sat := by
    refine ⟨cryptSat, ?_⟩
    sig_pre [Spec.Camellia.Prepared.cryptContract, Spec.Camellia.Prepared.cryptSig, AArch64.abi, AArch64.argRegs]
    sig_and_intros
    all_goals first
      | decide
      | exact ⟨_, _, cryptSat_holds⟩
      | (rw [size_eq, slots_eq]; decide)

theorem crypt_verified :
    Verified AArch64.target cryptPrepared (Spec.Camellia.Prepared.cryptContract layout AArch64.abi) :=
  Verified.of_correct crypt_correct crypt_ct crypt_implies

end VG.Proof.Camellia.AArch64
