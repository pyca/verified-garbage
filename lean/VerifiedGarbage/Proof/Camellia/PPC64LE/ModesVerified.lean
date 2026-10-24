module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesConstantTime
public import VerifiedGarbage.Proof.Camellia.CbcScratch
public import VerifiedGarbage.Proof.Camellia.FbScratch
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModeCore
import VerifiedGarbage.Proof.Modes.PPC64LE.Modes
public import VerifiedGarbage.Proof.Modes.PPC64LE.Seq
public import VerifiedGarbage.Proof.Modes.Steps
import VerifiedGarbage.Spec.Camellia.Cfb
import VerifiedGarbage.Spec.Camellia.Ofb
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
public import VerifiedGarbage.Spec.Camellia.Ctr
public import VerifiedGarbage.Spec.Cfb
public import VerifiedGarbage.Spec.Ofb

/-!
# Camellia's modes on PPC64LE meet their contracts

`cbcEncryptChained_verified`, `ofb_verified`, … : the modes of
`Proof/Modes/PPC64LE/` over Camellia's core (`Mode.dirCoreSpec`), run from
the state `wrap` makes of the arguments (`entry`, `wrap_wp`), with the
working space as the sixth argument (`modeContract`), meet the contracts
with a scratch buffer of 422 words (`Proof.Camellia.cbcEncChainedScratchContract`,
`ofbScratchContract`, …). `wrap` saves the caller's `r28` in the scratch
buffer's slot `extraSlot`, which the modes do not write (`Changes`), and
restores it.
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE.Modes

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Impl.Camellia.PPC64LE VG.Impl.Modes
open VG.Proof.Modes.PPC64LE (SeqPre ivR scrRegion S P Dp N Changes)
open VG.Proof.Camellia.PPC64LE (modePub)
open VG.Proof.Camellia.PPC64LE.Mode (dirCoreSpec KeyArgs dirCipher)
open VG.Proof.Camellia (schedWords)

/-! ## The wrapper -/

/-- The slot of the caller's `r28`. -/
abbrev extraA (s : State) : Addr := s.gpr .r8 + BitVec.ofNat 64 (8 * extraSlot)

/-- The state at the generic mode's entry: the caller's `r28` saved, the
number of rounds in `r28`, and the other arguments moved. -/
def entry (s : State) : State :=
  (((((({ s with mem := s.mem.writeW (extraA s) (s.gpr .r28) } : State).write .r28 (s.gpr .r4)).write .r4
    (s.gpr .r5)).write .r5 (s.gpr .r6)).write .r6 (s.gpr .r7)).write .r7 (s.gpr .r8))

theorem entry_gpr (s : State) (r : Reg) : (entry s).gpr r =
    if r = .r7 then s.gpr .r8 else if r = .r6 then s.gpr .r7 else if r = .r5 then s.gpr .r6 else
    if r = .r4 then s.gpr .r5 else if r = .r28 then s.gpr .r4 else s.gpr r := by
  simp only [entry, gpr_write]

@[simp] theorem entry_mem (s : State) : (entry s).mem = s.mem.writeW (extraA s) (s.gpr .r28) := rfl
@[simp] theorem entry_rd (s : State) : (entry s).rd = s.rd := rfl
@[simp] theorem entry_wr (s : State) : (entry s).wr = s.wr := rfl
@[simp] theorem entry_sp (s : State) : (entry s).sp = s.sp := rfl
@[simp] theorem entry_lr (s : State) : (entry s).lr = s.lr := rfl

theorem wrap_wp {p : Prog isa} {s : State} {Q : Mem → Prop}
    (hw : InRegions s.wr (extraA s) 8)
    (h : WP isa p (entry s) fun s' => abiPreserved (entry s) s' ∧ s'.gpr .r5 = s.gpr .r8 ∧
      s'.mem.readW (extraA s) 64 = s.gpr .r28 ∧ s'.wr = s.wr ∧ Q s'.mem) :
    WP isa (wrap p) s fun s' => abiPreserved s s' ∧ Q s'.mem := by
  unfold wrap
  refine WP.seq (WP.of_runBlock ⟨entry s, ?_, ?_⟩)
  · simp only [Impl.Modes.PPC64LE.mov, runBlock_cons, exec_std (by decide) hw, runStep_some, exec_or_self,
      runBlock_nil]
    simp only [entry, gpr_write]; rfl
  refine WP.seq (WP.mono h fun s₂ ⟨abi, sb, sv, wr, q⟩ => ?_)
  have hl : InRegions (s₂.rd ++ s₂.wr) (s₂.gpr Impl.Modes.PPC64LE.sb + BitVec.ofNat 64 (8 * extraSlot)) 8 := by
    show InRegions _ (s₂.gpr .r5 + _) 8
    rw [sb, wr]; obtain ⟨r, hr, hc⟩ := hw; exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_ld (by decide) hl, runStep_some, runBlock_nil], ?_⟩
  refine ⟨⟨fun r hr => ?_, by rw [sp_write, abi.2.1]; rfl, by rw [show (s₂.write _ _).lr = s₂.lr from rfl, abi.2.2]; rfl⟩,
    by rw [mem_write]; exact q⟩
  by_cases h28 : r = .r28
  · subst h28; rw [gpr_write_self]; show s₂.mem.readW (s₂.gpr .r5 + _) 64 = _; rw [sb]; exact sv
  · rw [gpr_write_of_ne _ _ h28, abi.1 r hr, entry_gpr]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> first | rfl | exact absurd rfl h28

/-! ## The functions' contracts -/

/-- Camellia, and its inverse, under the subkeys of the schedule at `r3` and `r4`'s rounds. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher :=
  Spec.Camellia.cipher (Spec.Camellia.subkeysAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
abbrev invCiph (s : State) : Spec.Cbc.Cipher :=
  Spec.Camellia.invCipher (Spec.Camellia.subkeysAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m (s.gpr .r5) 16
/-- The data, in blocks. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) := Spec.Cbc.blocksAt m (s.gpr .r6) (s.gpr .r7).toNat

/-- The functions' postconditions. -/
def cbcEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cbcDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (invCiph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)
def ofbPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ofb.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ofb.next (ciph s) (ivAt s.mem s) (s.gpr .r7).toNat
def cfbEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cfbDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

/-- A mode's function on PPC64LE with its working space as the sixth
argument, and the postcondition `post`. -/
def modeContract (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 272⟩
    let iv : Region := ⟨s.gpr .r5, 16⟩
    let data : Region := ⟨s.gpr .r6, 16 * (s.gpr .r7).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * modeSlots⟩
    s.rd = [key] ∧ s.wr = [iv, data, scratch] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint scratch ∧ iv.Disjoint data ∧
      iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .r3).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 16 * (s.gpr .r7).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * modeSlots ≤ 2 ^ 64 ∧
      ((s.gpr .r4).toNat = 18 ∨ (s.gpr .r4).toNat = 24)
  post := post
  pub := modePub

theorem modeSlots_eq : modeSlots = 422 := rfl
theorem extraSlot_eq : extraSlot = 420 := rfl

theorem entry_frame (s : State) : Frame [(⟨extraA s, 8⟩ : Region)] s.mem (entry s).mem :=
  (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)

section
variable {post : State → State → Prop} {s : State}

theorem extra_in (hs : (modeContract post).pre s) : InRegions s.wr (extraA s) 8 := by
  have h := hs
  obtain ⟨-, hwr, -⟩ := h
  exact ⟨⟨s.gpr .r8, 8 * modeSlots⟩, by rw [hwr]; simp, VG.Offset.contains_base _
    (by rw [extraSlot_eq, modeSlots_eq]; decide) (by rw [extraSlot_eq]; decide)⟩

/-- The slot `wrap` writes, apart from a region apart from the scratch buffer. -/
theorem extra_apart {R : Region} (h : R.Disjoint ⟨s.gpr .r8, 8 * modeSlots⟩) :
    ∀ r ∈ [(⟨extraA s, 8⟩ : Region)], R.Disjoint r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  exact h.sub_right (VG.Offset.sub_base _ (by rw [extraSlot_eq, modeSlots_eq]; decide))

theorem iv_entry (hs : (modeContract post).pre s) : Spec.Aes.bytesAt (entry s).mem (s.gpr .r5) 16 = Spec.Aes.bytesAt s.mem (s.gpr .r5) 16 := by
  have h := hs
  obtain ⟨-, -, -, -, -, -, dVS, -⟩ := h
  exact Proof.Modes.bytesAt_frame (entry_frame s) (extra_apart dVS) (by decide)

theorem data_entry (hs : (modeContract post).pre s) : Proof.Modes.chunksAt 16 (entry s).mem (s.gpr .r6) (s.gpr .r7).toNat =
    Proof.Modes.chunksAt 16 s.mem (s.gpr .r6) (s.gpr .r7).toNat := by
  have h := hs
  obtain ⟨-, -, -, -, -, -, -, dDS, -, -, fD, -⟩ := h
  exact Proof.Modes.PPC64LE.chunksAt_frame (entry_frame s) (extra_apart dDS) (by omega)

theorem key_entry (hs : (modeContract post).pre s) (R : Nat) (hR : R = 18 ∨ R = 24) :
    schedWords (entry s).mem (s.gpr .r3) R = schedWords s.mem (s.gpr .r3) R := by
  have h := hs
  obtain ⟨-, -, -, -, dKS, -⟩ := h
  simp only [schedWords]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hl : 8 * i + 8 ≤ 272 := by simp only [Spec.Camellia.scheduleLength] at hi; omega
  exact Proof.Camellia.wordAt_frame (entry_frame s) fun r hr =>
    (extra_apart dKS r hr).sub_left (VG.Offset.sub_base _ hl)

theorem rounds_of (hs : (modeContract post).pre s) : ((s.gpr .r4).toNat = 18 ∨ (s.gpr .r4).toNat = 24) := hs.2.2.2.2.2.2.2.2.2.2.2.2

/-- `modeContract`'s precondition gives the modes'. -/
theorem seqPre_of (hs : (modeContract post).pre s) {M : Mode} (d : Dir) (hstep : M.step = 16) : SeqPre (dirCore d) M (entry s) := by
  have h := hs
  obtain ⟨hrd, hwr, -, -, -, dVD, dVS, dDS, -, fV, fD, fS, -⟩ := h
  have e16 : 4 * (dirCore d).bw = 16 := rfl
  have eS : scrRegion (dirCore d) (S (entry s)) = ⟨s.gpr .r8, 8 * modeSlots⟩ := by
    simp [scrRegion, S, entry_gpr, dirCore]
  have eV : ivR (entry s) (dirCore d) = ⟨s.gpr .r5, 16⟩ := by simp [ivR, P, entry_gpr, dirCore]
  have eD : Proof.Modes.PPC64LE.dataRegion (Dp (entry s)) M.step (N (entry s)) = ⟨s.gpr .r6, 16 * (s.gpr .r7).toNat⟩ := by
    simp [Proof.Modes.PPC64LE.dataRegion, Dp, N, entry_gpr, hstep]
  refine ⟨⟨by rw [show (8 * (dirCore d).total) = 8 * modeSlots from rfl, show S (entry s) = s.gpr .r8 by
      simp [S, entry_gpr], entry_wr, hwr]; simp, by simpa [S, entry_gpr, dirCore] using fS⟩,
    by rw [eV, entry_rd, entry_wr, hwr]; simp, fun _ => by rw [eV, entry_wr, hwr]; simp,
    by rw [e16]; simpa [P, entry_gpr] using fV, by rw [eD, entry_wr, hwr]; simp,
    by rw [hstep]; simpa [Dp, N, entry_gpr] using fD, by rw [eD, eS]; exact dDS,
    by rw [eV, eS]; exact dVS, fun _ => by rw [eV, eD]; exact dVD, ⟨by omega, by rw [e16]; omega⟩,
    (dirCoreSpec d).layout⟩

theorem keyArgs_of (hs : (modeContract post).pre s) {M : Mode} (d : Dir) (hstep : M.step = 16) :
    KeyArgs (entry s) (Proof.Modes.PPC64LE.wrs0 (dirCore d) M (entry s))
      ((s.gpr .r4).toNat, schedWords s.mem (s.gpr .r3) (s.gpr .r4).toNat) := by
  have hR := rounds_of hs
  have h := hs
  obtain ⟨hrd, -, -, dKD, dKS, -, -, -, fK, -⟩ := h
  refine ⟨s.gpr .r3, by simp [entry_gpr], by simp [entry_gpr], hR, (key_entry hs _ hR).symm,
    by rw [entry_rd, hrd]; simp, fK, fun r hr => ?_⟩
  simp only [Proof.Modes.PPC64LE.wrs0, Proof.Modes.PPC64LE.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · simpa [Proof.Modes.PPC64LE.dataRegion, Dp, N, entry_gpr, hstep] using dKD
  · simpa [scrRegion, S, entry_gpr, dirCore] using dKS

/-- A mode over the core, wrapped: its results on the entry's memory. -/
theorem run_wrapped (hs : (modeContract post).pre s) {d : Dir} {M : Mode} (hstep : M.step = 16)
    {X : State → Prop}
    (hres : WP isa ((dirCore d).seq M) (entry s) fun s' => abiPreserved (entry s) s' ∧ X s')
    (hch : WP isa ((dirCore d).seq M) (entry s) (Changes (dirCore d) M (entry s))) :
    WP isa (wrap ((dirCore d).seq M)) s fun s' => abiPreserved s s' ∧ ∃ s₂ : State, s₂.mem = s'.mem ∧ X s₂ := by
  have h := hs
  obtain ⟨hrd, hwr, -, -, -, dVD, dVS, dDS, -, fV, fD, fS, -⟩ := h
  refine wrap_wp (Q := fun m => ∃ s₂ : State, s₂.mem = m ∧ X s₂) (extra_in hs) ?_
  obtain ⟨t, s', he, ⟨abi, r⟩, ch⟩ := WP.and hres hch
  refine ⟨t, s', he, abi, by simpa [S, entry_gpr, Impl.Modes.PPC64LE.sb] using ch.sb, ?_, by rw [(Exec.rdwr he).2.1]; rfl, s', rfl, r⟩
  have hfit := fS
  have ex : ∀ r ∈ [Proof.Modes.PPC64LE.coreRegion (dirCore d) (S (entry s)), Proof.Modes.PPC64LE.modeR (dirCore d) (S (entry s)),
      Proof.Modes.PPC64LE.dataRegion (Dp (entry s)) M.step (N (entry s)), ivR (entry s) (dirCore d)],
      Region.Disjoint ⟨extraA s, 8⟩ r := by
    intro r hr
    have eS : S (entry s) = s.gpr .r8 := by simp [S, entry_gpr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [eS]; exact VG.Offset.disjoint_base _ (by simp [extraSlot_eq, dirCore, slots_eq])
        (by rw [modeSlots_eq] at hfit; rw [extraSlot_eq]; omega)
    · rw [eS]; exact VG.Offset.disjoint _ (.inr (by simp [extraSlot_eq, dirCore, slots_eq]))
        (by rw [modeSlots_eq] at hfit; rw [extraSlot_eq]; omega) (by rw [modeSlots_eq] at hfit; simp [dirCore, slots_eq])
    · have e : Proof.Modes.PPC64LE.dataRegion (Dp (entry s)) M.step (N (entry s)) = ⟨s.gpr .r6, 16 * (s.gpr .r7).toNat⟩ := by
        simp [Proof.Modes.PPC64LE.dataRegion, Dp, N, entry_gpr, hstep]
      rw [e]
      exact (extra_apart dDS _ (List.mem_singleton_self _)).symm
    · have e : ivR (entry s) (dirCore d) = ⟨s.gpr .r5, 16⟩ := by simp [ivR, P, entry_gpr, dirCore]
      rw [e]
      exact (extra_apart dVS _ (List.mem_singleton_self _)).symm
  rw [ch.frame.readW (Region.contains_self _ _) ex (by decide), entry_mem, Mem.readW_writeW_self64]

end

/-! ## Correctness -/

attribute [local irreducible] Spec.Camellia.cipher Spec.Camellia.invCipher in
/-- The core's cipher is the contract's, without unfolding it. -/
theorem cipher_enc (m : Mem) (p : Addr) (R : Nat) :
    (dirCoreSpec .encrypt).cipher (R, schedWords m p R) = Spec.Camellia.cipher (Spec.Camellia.subkeysAt m p R) :=
  rfl

attribute [local irreducible] Spec.Camellia.cipher Spec.Camellia.invCipher in
theorem cipher_dec (m : Mem) (p : Addr) (R : Nat) :
    (dirCoreSpec .decrypt).cipher (R, schedWords m p R) = Spec.Camellia.invCipher (Spec.Camellia.subkeysAt m p R) :=
  rfl

theorem entry_args (s : State) : P (entry s) = s.gpr .r5 ∧ Dp (entry s) = s.gpr .r6 ∧
    N (entry s) = (s.gpr .r7).toNat := by
  simp [P, Dp, N, entry_gpr]

theorem cbcEncryptChained_correct (s : State) (hs : (modeContract cbcEncPost).pre s) :
    ∃ t s', Exec isa cbcEncryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract cbcEncPost).post s s' := by
  have hw := Proof.Modes.PPC64LE.cbcEncChained_wp (dirCoreSpec .encrypt)
    (seqPre_of hs .encrypt (M := Mode.cbcEncChained 4) rfl) (keyArgs_of hs .encrypt (M := Mode.cbcEncChained 4) rfl)
  have hc := Proof.Modes.PPC64LE.cbcEncChained_changes (dirCoreSpec .encrypt)
    (seqPre_of hs .encrypt (M := Mode.cbcEncChained 4) rfl) (keyArgs_of hs .encrypt (M := Mode.cbcEncChained 4) rfl)
  obtain ⟨eP, eD, eN⟩ := entry_args s
  rw [eP, eD, eN] at hw
  refine WP.mono (run_wrapped hs rfl hw hc) fun s' ⟨abi, s₂, hm, h2, h3⟩ => ⟨abi, ?_, ?_⟩
  all_goals rw [← hm]
  · simp only [Proof.Modes.PPC64LE.iv0, Proof.Modes.PPC64LE.blocks0, eP, eD, eN,
      show 4 * (dirCore Dir.encrypt).bw = 16 from rfl, iv_entry hs, data_entry hs, cipher_enc] at h2
    exact h2
  · simp only [Proof.Modes.PPC64LE.iv0, Proof.Modes.PPC64LE.blocks0, eP, eD, eN,
      show 4 * (dirCore Dir.encrypt).bw = 16 from rfl, iv_entry hs, data_entry hs, cipher_enc] at h3
    exact h3

theorem cbcDecryptChained_correct (s : State) (hs : (modeContract cbcDecPost).pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract cbcDecPost).post s s' := by
  have hw := Proof.Modes.PPC64LE.cbcDecChained_wp (dirCoreSpec .decrypt)
    (seqPre_of hs .decrypt (M := Mode.cbcDecChained 4) rfl) (keyArgs_of hs .decrypt (M := Mode.cbcDecChained 4) rfl)
  have hc := Proof.Modes.PPC64LE.cbcDecChained_changes (dirCoreSpec .decrypt)
    (seqPre_of hs .decrypt (M := Mode.cbcDecChained 4) rfl) (keyArgs_of hs .decrypt (M := Mode.cbcDecChained 4) rfl)
  obtain ⟨eP, eD, eN⟩ := entry_args s
  rw [eP, eD, eN] at hw
  refine WP.mono (run_wrapped hs rfl hw hc) fun s' ⟨abi, s₂, hm, h2, h3⟩ => ⟨abi, ?_, ?_⟩
  all_goals rw [← hm]
  · simp only [Proof.Modes.PPC64LE.iv0, Proof.Modes.PPC64LE.blocks0, eP, eD, eN,
      show 4 * (dirCore Dir.decrypt).bw = 16 from rfl, iv_entry hs, data_entry hs, cipher_dec] at h2
    exact h2
  · simp only [Proof.Modes.PPC64LE.iv0, Proof.Modes.PPC64LE.blocks0, eP, eD, eN,
      show 4 * (dirCore Dir.decrypt).bw = 16 from rfl, iv_entry hs, data_entry hs] at h3
    exact h3

theorem ofb_correct (s : State) (hs : (modeContract ofbPost).pre s) :
    ∃ t s', Exec isa ofb s t s' ∧ abiPreserved s s' ∧ (modeContract ofbPost).post s s' := by
  have hw := Proof.Modes.PPC64LE.ofb_wp (dirCoreSpec .encrypt)
    (seqPre_of hs .encrypt (M := Mode.ofb 4) rfl) (keyArgs_of hs .encrypt (M := Mode.ofb 4) rfl)
  have hc := Proof.Modes.PPC64LE.ofb_changes (dirCoreSpec .encrypt)
    (seqPre_of hs .encrypt (M := Mode.ofb 4) rfl) (keyArgs_of hs .encrypt (M := Mode.ofb 4) rfl)
  obtain ⟨eP, eD, eN⟩ := entry_args s
  rw [eP, eD, eN] at hw
  refine WP.mono (run_wrapped hs rfl hw hc) fun s' ⟨abi, s₂, hm, h2, h3⟩ => ⟨abi, ?_, ?_⟩
  all_goals rw [← hm]
  · simp only [Proof.Modes.PPC64LE.iv0, Proof.Modes.PPC64LE.blocks0, eP, eD, eN,
      show 4 * (dirCore Dir.encrypt).bw = 16 from rfl, iv_entry hs, data_entry hs, cipher_enc] at h2
    exact h2
  · simp only [Proof.Modes.PPC64LE.iv0, eP,
      show 4 * (dirCore Dir.encrypt).bw = 16 from rfl, iv_entry hs] at h3
    rw [cipher_enc] at h3
    exact h3

theorem cfbEncrypt_correct (s : State) (hs : (modeContract cfbEncPost).pre s) :
    ∃ t s', Exec isa cfbEncrypt s t s' ∧ abiPreserved s s' ∧ (modeContract cfbEncPost).post s s' := by
  have hw := Proof.Modes.PPC64LE.cfbEnc_wp (dirCoreSpec .encrypt)
    (seqPre_of hs .encrypt (M := Mode.cfbEnc 4) rfl) (keyArgs_of hs .encrypt (M := Mode.cfbEnc 4) rfl)
  have hc := Proof.Modes.PPC64LE.cfbEnc_changes (dirCoreSpec .encrypt)
    (seqPre_of hs .encrypt (M := Mode.cfbEnc 4) rfl) (keyArgs_of hs .encrypt (M := Mode.cfbEnc 4) rfl)
  obtain ⟨eP, eD, eN⟩ := entry_args s
  rw [eP, eD, eN] at hw
  refine WP.mono (run_wrapped hs rfl hw hc) fun s' ⟨abi, s₂, hm, h2, h3⟩ => ⟨abi, ?_, ?_⟩
  all_goals rw [← hm]
  · simp only [Proof.Modes.PPC64LE.iv0, Proof.Modes.PPC64LE.blocks0, eP, eD, eN,
      show 4 * (dirCore Dir.encrypt).bw = 16 from rfl, iv_entry hs, data_entry hs, cipher_enc] at h2
    exact h2
  · simp only [Proof.Modes.PPC64LE.iv0, Proof.Modes.PPC64LE.blocks0, eP, eD, eN,
      show 4 * (dirCore Dir.encrypt).bw = 16 from rfl, iv_entry hs, data_entry hs, cipher_enc] at h3
    exact h3

theorem cfbDecrypt_correct (s : State) (hs : (modeContract cfbDecPost).pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ (modeContract cfbDecPost).post s s' := by
  have hw := Proof.Modes.PPC64LE.cfbDec_wp (dirCoreSpec .encrypt)
    (seqPre_of hs .encrypt (M := Mode.cfbDec 4) rfl) (keyArgs_of hs .encrypt (M := Mode.cfbDec 4) rfl)
  have hc := Proof.Modes.PPC64LE.cfbDec_changes (dirCoreSpec .encrypt)
    (seqPre_of hs .encrypt (M := Mode.cfbDec 4) rfl) (keyArgs_of hs .encrypt (M := Mode.cfbDec 4) rfl)
  obtain ⟨eP, eD, eN⟩ := entry_args s
  rw [eP, eD, eN] at hw
  refine WP.mono (run_wrapped hs rfl hw hc) fun s' ⟨abi, s₂, hm, h2, h3⟩ => ⟨abi, ?_, ?_⟩
  all_goals rw [← hm]
  · simp only [Proof.Modes.PPC64LE.iv0, Proof.Modes.PPC64LE.blocks0, eP, eD, eN,
      show 4 * (dirCore Dir.encrypt).bw = 16 from rfl, iv_entry hs, data_entry hs, cipher_enc] at h2
    exact h2
  · simp only [Proof.Modes.PPC64LE.iv0, Proof.Modes.PPC64LE.blocks0, eP, eD, eN,
      show 4 * (dirCore Dir.encrypt).bw = 16 from rfl, iv_entry hs, data_entry hs] at h3
    exact h3

/-! ## The contracts -/

/-- A state satisfying the modes' precondition: the schedule at `0x1000`,
18 rounds, the IV at `0x2000`, no data at `0x3000`, and the scratch buffer at
`0x4000`. -/
def modeSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 18 | .r5 => 0x2000 | .r6 => 0x3000 | .r8 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 3376⟩]

theorem modePub_iff (s₁ s₂ : State) : modePub s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 := by
  simp [modePub]

theorem cbcEncryptChained_verified :
    Verified target cbcEncryptChained (Proof.Camellia.cbcEncChainedScratchContract abi 422) := by
  refine Verified.of_correct cbcEncryptChained_correct (cbcEncryptChained_constantTime _) ?_
  sig_implies [Proof.Camellia.cbcEncChainedScratchContract, Proof.Camellia.cbcChainedScratchSig,
    Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcChainedPre, Proof.Camellia.cbcEncChainedPost, abi, argRegs,
    modeContract, cbcEncPost, modePub_iff, modeSlots_eq] [modeSat] using modeSat

theorem cbcDecryptChained_verified :
    Verified target cbcDecryptChained (Proof.Camellia.cbcDecChainedScratchContract abi 422) := by
  refine Verified.of_correct cbcDecryptChained_correct (cbcDecryptChained_constantTime _) ?_
  sig_implies [Proof.Camellia.cbcDecChainedScratchContract, Proof.Camellia.cbcChainedScratchSig,
    Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcChainedPre, Proof.Camellia.cbcDecChainedPost, abi, argRegs,
    modeContract, cbcDecPost, modePub_iff, modeSlots_eq] [modeSat] using modeSat

theorem ofb_verified : Verified target ofb (Proof.Camellia.ofbScratchContract abi 422) := by
  refine Verified.of_correct ofb_correct (ofb_constantTime _) ?_
  sig_implies [Proof.Camellia.ofbScratchContract, Proof.Camellia.ofbScratchSig, Spec.Camellia.ofbSig,
    Spec.Camellia.ofbPre, Spec.Camellia.ofbPost, abi, argRegs, modeContract, ofbPost, modePub_iff,
    modeSlots_eq] [modeSat] using modeSat

theorem cfbEncrypt_verified : Verified target cfbEncrypt (Proof.Camellia.cfbEncScratchContract abi 422) := by
  refine Verified.of_correct cfbEncrypt_correct (cfbEncrypt_constantTime _) ?_
  sig_implies [Proof.Camellia.cfbEncScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig,
    Spec.Camellia.cfbPre, Spec.Camellia.cfbEncryptPost, abi, argRegs, modeContract, cfbEncPost, modePub_iff,
    modeSlots_eq] [modeSat] using modeSat

theorem cfbDecrypt_verified : Verified target cfbDecrypt (Proof.Camellia.cfbDecScratchContract abi 422) := by
  refine Verified.of_correct cfbDecrypt_correct (cfbDecrypt_constantTime _) ?_
  sig_implies [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig,
    Spec.Camellia.cfbPre, Spec.Camellia.cfbDecryptPost, abi, argRegs, modeContract, cfbDecPost, modePub_iff,
    modeSlots_eq] [modeSat] using modeSat

end VG.Proof.Camellia.PPC64LE.Modes
