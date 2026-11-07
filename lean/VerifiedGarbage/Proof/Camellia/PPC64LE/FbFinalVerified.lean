module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Camellia.CfbFinalScratch
public import VerifiedGarbage.Proof.Modes.PPC64LE.SeqFinal
public import VerifiedGarbage.Impl.Camellia.PPC64LE.FbFinal
public import VerifiedGarbage.Spec.Camellia.CfbFinal
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Camellia.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
import VerifiedGarbage.Proof.Camellia.PPC64LE.CallSum
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Modes.Addr
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.FbFinalLit
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.CallSum
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
meta import VerifiedGarbage.Proof.Camellia.CfbFinalScratch
meta import VerifiedGarbage.Proof.Modes.PPC64LE.SeqFinal
meta import VerifiedGarbage.Impl.Camellia.PPC64LE.FbFinal
meta import VerifiedGarbage.Spec.Camellia.CfbFinal
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Modes.Addr
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# Camellia-CFB128 of a message's last piece on PPC64LE meets its contracts

`cfbEncryptFinal_verified`, `cfbDecryptFinal_verified`: the modes' CFB over
a message's last piece (`Proof.Modes.PPC64LE.cfbEncFinal_wp`, …) over
Camellia's core (`Mode.dirCoreSpec`), run from the state `wrap` makes of the
arguments (`entry`, `wrap_wp`), with the working space as the sixth argument
(`finalContract`), as the whole-block functions are (`ModesVerified.lean`),
but the data `len` bytes, meet the contracts on the subkeys at the schedule
(`Proof.Camellia.cfbEncFinalScratchContract`, …) with a scratch buffer of 422
words. Each is constant time by the slot taint analysis with the prepared
function's summary, as theirs are; the `_framed` theorems run them with their
working space on the stack, zeroed on return, and give the specification's
contracts (`cfbEncryptFinal_of_sk`, …).
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE.FbFinal

open VG VG.PPC64LE VG.Impl.Camellia.PPC64LE VG.Impl.Modes
open VG.Proof.Modes.PPC64LE (SeqPre ivR scrRegion S P Dp N Changes byteMode)
open VG.Proof.Camellia.PPC64LE (modePub modeTaint cryptSum)
open VG.Proof.Camellia.PPC64LE.Mode (dirCoreSpec KeyArgs)
open VG.Proof.Camellia.PPC64LE.Modes (entry entry_gpr entry_mem entry_rd entry_wr extraA wrap_wp entry_frame
  modeSlots_eq extraSlot_eq cipher_enc entry_args ciph modeSat modePub_iff)
open VG.Proof.Camellia (schedWords)

/-- The functions' postconditions. -/
def encPost (s s' : State) : Prop :=
  Spec.Cfb.EncryptFinal (ciph s) 16 s.mem s'.mem (s.gpr .r5) (s.gpr .r6) (s.gpr .r7).toNat
def decPost (s s' : State) : Prop :=
  Spec.Cfb.DecryptFinal (ciph s) 16 s.mem s'.mem (s.gpr .r5) (s.gpr .r6) (s.gpr .r7).toNat

/-- A final CFB128 function on PPC64LE with its working space as the sixth
argument, the data `len` bytes, and the postcondition `post`. -/
def finalContract (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 272⟩
    let iv : Region := ⟨s.gpr .r5, 16⟩
    let data : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * modeSlots⟩
    s.rd = [key] ∧ s.wr = [iv, data, scratch] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint scratch ∧ iv.Disjoint data ∧
      iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .r3).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * modeSlots ≤ 2 ^ 64 ∧
      ((s.gpr .r4).toNat = 18 ∨ (s.gpr .r4).toNat = 24)
  post := post
  pub := modePub

section
variable {post : State → State → Prop} {s : State}

theorem extra_in (hs : (finalContract post).pre s) : InRegions s.wr (extraA s) 8 := by
  have h := hs
  obtain ⟨-, hwr, -⟩ := h
  exact ⟨⟨s.gpr .r8, 8 * modeSlots⟩, by rw [hwr]; simp, VG.Offset.contains_base _
    (by rw [extraSlot_eq, modeSlots_eq]; decide) (by rw [extraSlot_eq]; decide)⟩

/-- The slot `wrap` writes, apart from a region apart from the scratch buffer. -/
theorem extra_apart {R : Region} (h : R.Disjoint ⟨s.gpr .r8, 8 * modeSlots⟩) :
    ∀ r ∈ [(⟨extraA s, 8⟩ : Region)], R.Disjoint r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  exact h.sub_right (VG.Offset.sub_base _ (by rw [extraSlot_eq, modeSlots_eq]; decide))

theorem iv_entry (hs : (finalContract post).pre s) :
    Spec.Aes.bytesAt (entry s).mem (s.gpr .r5) 16 = Spec.Aes.bytesAt s.mem (s.gpr .r5) 16 := by
  have h := hs
  obtain ⟨-, -, -, -, -, -, dVS, -⟩ := h
  exact Proof.Modes.bytesAt_frame (entry_frame s) (extra_apart dVS) (by decide)

theorem data_entry (hs : (finalContract post).pre s) :
    Spec.Aes.bytesAt (entry s).mem (s.gpr .r6) (s.gpr .r7).toNat = Spec.Aes.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat := by
  have h := hs
  obtain ⟨-, -, -, -, -, -, -, dDS, -, -, fD, -⟩ := h
  exact Proof.Modes.bytesAt_frame (entry_frame s) (extra_apart dDS) (by omega)

theorem key_entry (hs : (finalContract post).pre s) (R : Nat) (hR : R = 18 ∨ R = 24) :
    schedWords (entry s).mem (s.gpr .r3) R = schedWords s.mem (s.gpr .r3) R := by
  have h := hs
  obtain ⟨-, -, -, -, dKS, -⟩ := h
  simp only [schedWords]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hl : 8 * i + 8 ≤ 272 := by simp only [Spec.Camellia.scheduleLength] at hi; omega
  exact Proof.Camellia.wordAt_frame (entry_frame s) fun r hr =>
    (extra_apart dKS r hr).sub_left (VG.Offset.sub_base _ hl)

theorem rounds_of (hs : (finalContract post).pre s) : ((s.gpr .r4).toNat = 18 ∨ (s.gpr .r4).toNat = 24) :=
  hs.2.2.2.2.2.2.2.2.2.2.2.2

theorem dataR_entry : Proof.Modes.PPC64LE.dataRegion (Dp (entry s)) byteMode.step (N (entry s)) =
    ⟨s.gpr .r6, (s.gpr .r7).toNat⟩ := by
  simp [Proof.Modes.PPC64LE.dataRegion, Dp, N, entry_gpr, byteMode]

/-- `finalContract`'s precondition gives the modes', for steps of a byte. -/
theorem seqPre_of (hs : (finalContract post).pre s) : SeqPre (dirCore .encrypt) byteMode (entry s) := by
  have h := hs
  obtain ⟨hrd, hwr, -, -, -, dVD, dVS, dDS, -, fV, fD, fS, -⟩ := h
  have e16 : 4 * (dirCore .encrypt).bw = 16 := rfl
  have eS : scrRegion (dirCore .encrypt) (S (entry s)) = ⟨s.gpr .r8, 8 * modeSlots⟩ := by
    simp [scrRegion, S, entry_gpr, dirCore]
  have eV : ivR (entry s) (dirCore .encrypt) = ⟨s.gpr .r5, 16⟩ := by simp [ivR, P, entry_gpr, dirCore]
  refine ⟨⟨by rw [show (8 * (dirCore .encrypt).total) = 8 * modeSlots from rfl, show S (entry s) = s.gpr .r8 by
      simp [S, entry_gpr], entry_wr, hwr]; simp, by simpa [S, entry_gpr, dirCore] using fS⟩,
    by rw [eV, entry_rd, entry_wr, hwr]; simp, fun _ => by rw [eV, entry_wr, hwr]; simp,
    by rw [e16]; simpa [P, entry_gpr] using fV, by rw [dataR_entry, entry_wr, hwr]; simp,
    by simpa [Dp, N, entry_gpr, byteMode] using fD, by rw [dataR_entry, eS]; exact dDS,
    by rw [eV, eS]; exact dVS, fun _ => by rw [eV, dataR_entry]; exact dVD, ⟨by decide, by rw [e16]; decide⟩,
    (dirCoreSpec .encrypt).layout⟩

theorem keyArgs_of (hs : (finalContract post).pre s) :
    KeyArgs (entry s) (Proof.Modes.PPC64LE.wrs0 (dirCore .encrypt) byteMode (entry s))
      ((s.gpr .r4).toNat, schedWords s.mem (s.gpr .r3) (s.gpr .r4).toNat) := by
  have hR := rounds_of hs
  have h := hs
  obtain ⟨hrd, -, -, dKD, dKS, -, -, -, fK, -⟩ := h
  refine ⟨s.gpr .r3, by simp [entry_gpr], by simp [entry_gpr], hR, (key_entry hs _ hR).symm,
    by rw [entry_rd, hrd]; simp, fK, fun r hr => ?_⟩
  simp only [Proof.Modes.PPC64LE.wrs0, Proof.Modes.PPC64LE.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · rw [dataR_entry]; exact dKD
  · simpa [scrRegion, S, entry_gpr, dirCore] using dKS

/-- A mode over the core, wrapped: its results on the entry's memory. -/
theorem run_wrapped (hs : (finalContract post).pre s) {M : Mode} {X : State → Prop}
    (hres : WP isa ((dirCore .encrypt).seqFinal M) (entry s) fun s' => abiPreserved (entry s) s' ∧ X s')
    (hch : WP isa ((dirCore .encrypt).seqFinal M) (entry s) (Changes (dirCore .encrypt) byteMode (entry s))) :
    WP isa (wrap ((dirCore .encrypt).seqFinal M)) s fun s' => abiPreserved s s' ∧
      ∃ s₂ : State, s₂.mem = s'.mem ∧ X s₂ := by
  have h := hs
  obtain ⟨hrd, hwr, -, -, -, dVD, dVS, dDS, -, fV, fD, fS, -⟩ := h
  refine wrap_wp (Q := fun m => ∃ s₂ : State, s₂.mem = m ∧ X s₂) (extra_in hs) ?_
  obtain ⟨t, s', he, ⟨abi, r⟩, ch⟩ := WP.and hres hch
  refine ⟨t, s', he, abi, by simpa [S, entry_gpr, Impl.Modes.PPC64LE.sb] using ch.sb, ?_,
    by rw [(Exec.rdwr he).2.1]; rfl, s', rfl, r⟩
  have hfit := fS
  have ex : ∀ r ∈ [Proof.Modes.PPC64LE.coreRegion (dirCore .encrypt) (S (entry s)),
      Proof.Modes.PPC64LE.modeR (dirCore .encrypt) (S (entry s)),
      Proof.Modes.PPC64LE.dataRegion (Dp (entry s)) byteMode.step (N (entry s)), ivR (entry s) (dirCore .encrypt)],
      Region.Disjoint ⟨extraA s, 8⟩ r := by
    intro r hr
    have eS : S (entry s) = s.gpr .r8 := by simp [S, entry_gpr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [eS]; exact VG.Offset.disjoint_base _ (by simp [extraSlot_eq, dirCore, slots_eq])
        (by rw [modeSlots_eq] at hfit; rw [extraSlot_eq]; omega)
    · rw [eS]; exact VG.Offset.disjoint _ (.inr (by simp [extraSlot_eq, dirCore, slots_eq]))
        (by rw [modeSlots_eq] at hfit; rw [extraSlot_eq]; omega) (by rw [modeSlots_eq] at hfit; simp [dirCore, slots_eq])
    · rw [dataR_entry]
      exact (extra_apart dDS _ (List.mem_singleton_self _)).symm
    · have e : ivR (entry s) (dirCore .encrypt) = ⟨s.gpr .r5, 16⟩ := by simp [ivR, P, entry_gpr, dirCore]
      rw [e]
      exact (extra_apart dVS _ (List.mem_singleton_self _)).symm
  rw [ch.frame.readW (Region.contains_self _ _) ex (by decide), entry_mem, Mem.readW_writeW_self64]

end

/-! ## Correctness -/

theorem cfbEncryptFinal_correct (s : State) (hs : (finalContract encPost).pre s) :
    ∃ t s', Exec isa cfbEncryptFinal s t s' ∧ abiPreserved s s' ∧ (finalContract encPost).post s s' := by
  have hw := Proof.Modes.PPC64LE.cfbEncFinal_wp (dirCoreSpec .encrypt) (seqPre_of hs) (keyArgs_of hs)
  have hc := Proof.Modes.PPC64LE.cfbEncFinal_changes (dirCoreSpec .encrypt) (seqPre_of hs) (keyArgs_of hs)
  obtain ⟨eP, eD, eN⟩ := entry_args s
  rw [eP, eD, eN] at hw
  refine WP.mono (run_wrapped hs hw hc) fun s' ⟨abi, s₂, hm, h⟩ => ⟨abi, ?_⟩
  rw [show 4 * (dirCore Dir.encrypt).bw = 16 from rfl, cipher_enc, hm] at h
  obtain ⟨h1, h2⟩ := h
  rw [iv_entry hs, data_entry hs] at h1 h2
  exact ⟨h1, h2⟩

theorem cfbDecryptFinal_correct (s : State) (hs : (finalContract decPost).pre s) :
    ∃ t s', Exec isa cfbDecryptFinal s t s' ∧ abiPreserved s s' ∧ (finalContract decPost).post s s' := by
  have hw := Proof.Modes.PPC64LE.cfbDecFinal_wp (dirCoreSpec .encrypt) (seqPre_of hs) (keyArgs_of hs)
  have hc := Proof.Modes.PPC64LE.cfbDecFinal_changes (dirCoreSpec .encrypt) (seqPre_of hs) (keyArgs_of hs)
  obtain ⟨eP, eD, eN⟩ := entry_args s
  rw [eP, eD, eN] at hw
  refine WP.mono (run_wrapped hs hw hc) fun s' ⟨abi, s₂, hm, h⟩ => ⟨abi, ?_⟩
  rw [show 4 * (dirCore Dir.encrypt).bw = 16 from rfl, cipher_enc, hm] at h
  obtain ⟨h1, h2⟩ := h
  rw [iv_entry hs, data_entry hs] at h1 h2
  exact ⟨h1, h2⟩

/-! ## Constant time -/

theorem final_agree {post : State → State → Prop} (s₁ s₂ : State)
    (h₁ : (finalContract post).pre s₁) (h₂ : (finalContract post).pre s₂) (hp : modePub s₁ s₂) :
    SlotTaint.Agree modeTaint s₁ s₂ := by
  obtain ⟨-, hw₁, -, -, -, dVD, dVS, dDS, -, fV, fD, fS, -⟩ := h₁
  obtain ⟨-, hw₂, -⟩ := h₂
  obtain ⟨hsp, hr⟩ := hp
  have r5 := hr .r5 (by simp)
  have r6 := hr .r6 (by simp)
  have r7 := hr .r7 (by simp)
  have r8 := hr .r8 (by simp)
  refine SlotTaint.agree_mk' hsp (fun r h => hr r (by simpa using h)) (by rw [hw₁, hw₂, r5, r6, r7, r8])
    ?_ ?_ ?_ ?_ ?_
  · rw [hw₁]
    exact .cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil))
  · rw [hw₁]
    refine .cons (fun r hr => ?_) (.cons (fun r hr => ?_) (.cons (fun r hr => absurd hr List.not_mem_nil) .nil))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dVD
      · exact dVS
    · simp only [List.mem_singleton] at hr; subst hr; exact dDS
  · rw [hw₁]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [SlotTaint.region, hw₁]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [SlotTaint.region, hw₂]

theorem cfbEncryptFinal_constantTime {post : State → State → Prop} :
    ConstantTime isa (finalContract post).pre modePub cfbEncryptFinal :=
  VG.Taint.constantTime_of_exists (A := slotTaint) modeTaint final_agree (by taint_decide_sum [cryptSum])

theorem cfbDecryptFinal_constantTime {post : State → State → Prop} :
    ConstantTime isa (finalContract post).pre modePub cfbDecryptFinal :=
  VG.Taint.constantTime_of_exists (A := slotTaint) modeTaint final_agree (by taint_decide_sum [cryptSum])

/-! ## The contracts -/

theorem cfbEncryptFinal_verified :
    Verified target cfbEncryptFinal (Proof.Camellia.cfbEncFinalScratchContract abi 422) := by
  refine Verified.of_correct cfbEncryptFinal_correct cfbEncryptFinal_constantTime ?_
  sig_implies [Proof.Camellia.cfbEncFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
    Curry.app, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre, Proof.Camellia.cfbEncryptFinalPostSk, abi,
    argRegs, finalContract, encPost, modePub_iff, modeSlots_eq] [modeSat] using modeSat

theorem cfbDecryptFinal_verified :
    Verified target cfbDecryptFinal (Proof.Camellia.cfbDecFinalScratchContract abi 422) := by
  refine Verified.of_correct cfbDecryptFinal_correct cfbDecryptFinal_constantTime ?_
  sig_implies [Proof.Camellia.cfbDecFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
    Curry.app, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre, Proof.Camellia.cfbDecryptFinalPostSk, abi,
    argRegs, finalContract, decPost, modePub_iff, modeSlots_eq] [modeSat] using modeSat

theorem cfbEncFinalFrameSat_pre : ∃ s, (Proof.Camellia.cfbEncryptFinalContractSk PPC64LE.abi (0 + 3408)).pre s := by
  implies_sat [Proof.Camellia.cfbEncryptFinalContractSk, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre,
    Proof.Camellia.cfbEncryptFinalPostSk, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

theorem cfbDecFinalFrameSat_pre : ∃ s, (Proof.Camellia.cfbDecryptFinalContractSk PPC64LE.abi (0 + 3408)).pre s := by
  implies_sat [Proof.Camellia.cfbDecryptFinalContractSk, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre,
    Proof.Camellia.cfbDecryptFinalPostSk, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

/-- The final CFB128 encryption with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 cfbEncryptFinal)
      (Spec.Camellia.cfbEncryptFinalContract PPC64LE.abi 3408) :=
  Proof.Camellia.cfbEncryptFinal_of_sk <|
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Camellia.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 422) (pre := Spec.Camellia.cfbFinalPre PPC64LE.abi.ptrBits)
    (post := Proof.Camellia.cfbEncryptFinalPostSk PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3408) (words := 422) cfbEncryptFinal_verified
    (by decide) (by decide) (by decide) (Proof.Camellia.cfbFinalPre_local _)
    (Proof.Camellia.cfbEncryptFinalPost_local _) (Proof.Camellia.cfbEncryptFinalPostOut_local _)
    cfbEncFinalFrameSat_pre

/-- The final CFB128 decryption with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 cfbDecryptFinal)
      (Spec.Camellia.cfbDecryptFinalContract PPC64LE.abi 3408) :=
  Proof.Camellia.cfbDecryptFinal_of_sk <|
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Camellia.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 422) (pre := Spec.Camellia.cfbFinalPre PPC64LE.abi.ptrBits)
    (post := Proof.Camellia.cfbDecryptFinalPostSk PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3408) (words := 422) cfbDecryptFinal_verified
    (by decide) (by decide) (by decide) (Proof.Camellia.cfbFinalPre_local _)
    (Proof.Camellia.cfbDecryptFinalPost_local _) (Proof.Camellia.cfbDecryptFinalPostOut_local _)
    cfbDecFinalFrameSat_pre

end VG.Proof.Camellia.PPC64LE.FbFinal
