module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesConstantTime
public import VerifiedGarbage.Proof.Cast5.PPC64LE.ModeCore
public import VerifiedGarbage.Proof.Cast5.ModeScratch
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Modes.PPC64LE.Seq
import VerifiedGarbage.Proof.Modes.PPC64LE.Modes
public import VerifiedGarbage.Proof.Cast5.PPC64LE.EcbVerified
import VerifiedGarbage.Proof.Cast5.ModeMem
import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# CAST5's modes on PPC64LE meet their contracts

`modeFn m` moves the arguments to the modes' registers and runs `m n` for
the count of rounds `n` (`modeFn_wp`), and each `m n` is a mode of
`Proof/Modes/PPC64LE/` over CAST5's core with `n` rounds
(`Mode.dirCoreSpec`). `cbcEncryptChained_verified`, `ofb_verified`, …: with
the working space as the sixth argument, each meets its contract with a
scratch buffer of 22 words (`Proof.Cast5.modeScratchContract`), under the
calling convention with the table (`abi.withConsts ecbConsts`). The proof's
contract (`modePC`) is `modeP` for the state without the table's region,
with what the contract says of the table (`ConstsOk`).
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE.Modes

open VG VG.PPC64LE VG.Impl.Cast5.PPC64LE VG.Impl.Modes
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)
open VG.Proof.Modes.PPC64LE (SeqPre)
open VG.Proof.Cast5.PPC64LE.Mode (dirCoreSpec KeyArgs layout)
open VG.Proof.Cast5.PPC64LE (modePub ConstsOk.held1 ConstsOk.rd1 ConstsOk.wr1 stripConsts_rd_mem s1234_len
  ecbSatMem ecbSatMem_held ecbConsts_eq)

/-! ## The arguments -/

/-- The subkeys on entry. -/
abbrev keyOf (s : State) : Spec.Cast5.Schedule := Spec.Cast5.scheduleAt s.mem (s.gpr .r3)
/-- The count of rounds. -/
abbrev rounds (s : State) : Nat := (s.gpr .r4).toNat
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m (s.gpr .r5) 8
/-- The data, in blocks. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) := Spec.Cast5.cbcBlocksAt m (s.gpr .r6) (s.gpr .r7).toNat

/-- The state after `modeFn`'s moves, from `s`: the arguments in the modes'
registers, and nothing else the caller sees changed. -/
structure Shifted (s s₁ : State) : Prop where
  r3 : s₁.gpr .r3 = s.gpr .r3
  r4 : s₁.gpr .r4 = s.gpr .r5
  r5 : s₁.gpr .r5 = s.gpr .r6
  r6 : s₁.gpr .r6 = s.gpr .r7
  r7 : s₁.gpr .r7 = s.gpr .r8
  other : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  mem : s₁.mem = s.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp
  lr : s₁.lr = s.lr
  syms : s₁.syms = s.syms

theorem Shifted.abi {s s₁ s' : State} (h : Shifted s s₁) (ha : abiPreserved s₁ s') : abiPreserved s s' :=
  ⟨fun r hr => (ha.1 r hr).trans (h.other r hr), ha.2.1.trans h.sp, ha.2.2.trans h.lr⟩

/-- `modeFn m` runs `m` with the count of rounds, from the state with the
arguments moved. -/
theorem modeFn_wp {m : Nat → Prog isa} {s : State} {Q : State → Prop} (hn : rounds s = 12 ∨ rounds s = 16)
    (h : ∀ s₁, Shifted s s₁ → WP isa (m (rounds s)) s₁ Q) : WP isa (modeFn m) s Q := by
  unfold modeFn
  refine WP.seq (WP.cons exec_logic (WP.cons exec_logic (WP.cons exec_logic (WP.cons exec_logic
    (WP.cons exec_logic (WP.cons (exec_subi (by decide) (by decide)) (WP.block_nil ?_)))))))
  generalize hs₁ : State.write _ _ _ = s₁
  have sh : Shifted s s₁ := by
    subst hs₁
    refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [State.write]
    · simp [State.write]
    · simp [State.write]
    · simp [State.write]
    · simp [State.write]
    · have h4 : r ≠ .r4 := by rintro rfl; simp [preserved] at hr
      have h5 : r ≠ .r5 := by rintro rfl; simp [preserved] at hr
      have h6 : r ≠ .r6 := by rintro rfl; simp [preserved] at hr
      have h7 : r ≠ .r7 := by rintro rfl; simp [preserved] at hr
      have h10 : r ≠ .r10 := by rintro rfl; simp [preserved] at hr
      simp [State.write, h4, h5, h6, h7, h10]
  have r10 : s₁.gpr .r10 = s.gpr .r4 - BitVec.ofNat 64 12 := by subst hs₁; simp [State.write]
  have e4 : s.gpr .r4 = BitVec.ofNat 64 (rounds s) := by simp only [rounds, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rcases hn with hn | hn
  · refine WP.ite true (by rw [eval_zero, r10, e4, hn]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hn ▸ h s₁ sh
  · refine WP.ite false (by rw [eval_zero, r10, e4, hn]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    exact hn ▸ h s₁ sh

/-! ## The modes' contract, as the proof states it -/

/-- The modes' public arguments, without the table's address. -/
def argPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8], s₁.gpr r = s₂.gpr r

/-- A mode's function on PPC64LE with its working space as the sixth
argument, and the postcondition `post`. -/
def modeP (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 128⟩
    let iv : Region := ⟨s.gpr .r5, 8⟩
    let data : Region := ⟨s.gpr .r6, 8 * (s.gpr .r7).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * 22⟩
    s.rd = [key] ∧ s.wr = [iv, data, scratch] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint scratch ∧ iv.Disjoint data ∧
      iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .r3).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 8 * (s.gpr .r7).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * 22 ≤ 2 ^ 64 ∧
      ((s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 16)
  post := post
  pub := argPub

/-- `modeP`, with the table. -/
def modePC (post : State → State → Prop) : Contract isa where
  pre s := (modeP post).pre (stripConsts ecbConsts s) ∧ ConstsOk ecbConsts 0 s
  post := post
  pub := modePub

/-- The functions' postconditions. -/
def cbcEncPost (s s' : State) : Prop :=
  let cs := Spec.Cbc.encrypt (Spec.Cast5.cipher (keyOf s) (rounds s)) (ivAt s.mem s) (dataAt s.mem s)
  dataAt s'.mem s = cs ∧ ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) cs
def cbcDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (Spec.Cast5.invCipher (keyOf s) (rounds s)) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)
def ofbPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ofb.crypt (Spec.Cast5.cipher (keyOf s) (rounds s)) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ofb.next (Spec.Cast5.cipher (keyOf s) (rounds s)) (ivAt s.mem s) (s.gpr .r7).toNat
def cfbEncPost (s s' : State) : Prop :=
  let cs := Spec.Cfb.encrypt (Spec.Cast5.cipher (keyOf s) (rounds s)) (ivAt s.mem s) (dataAt s.mem s)
  dataAt s'.mem s = cs ∧ ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) cs
def cfbDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.decrypt (Spec.Cast5.cipher (keyOf s) (rounds s)) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

section
variable {post : State → State → Prop} {s s₁ : State} (hs : (modePC post).pre s) (h₁ : Shifted s s₁)
include hs

theorem rounds_of : rounds s = 12 ∨ rounds s = 16 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, hn⟩, -⟩ := hs
  exact hn

include h₁

/-- `modePC`'s precondition gives the modes'. -/
theorem seqPre_of (up : Bool) {n : Nat} {M : Mode} (hstep : M.step = 8) :
    SeqPre (dirCore up n) M s₁ := by
  obtain ⟨⟨-, hwr, -, -, -, dVD, dVS, dDS, -, fV, fD, fS, -⟩, -⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr] at hwr dVD dVS dDS fV fD fS
  have eS : Proof.Modes.PPC64LE.scrRegion (dirCore up n) (Proof.Modes.PPC64LE.S s₁) = ⟨s.gpr .r8, 8 * 22⟩ := by
    simp only [Proof.Modes.PPC64LE.scrRegion, Proof.Modes.PPC64LE.S, h₁.r7]; rfl
  have eV : Proof.Modes.PPC64LE.ivR s₁ (dirCore up n) = ⟨s.gpr .r5, 8⟩ := by
    simp only [Proof.Modes.PPC64LE.ivR, Proof.Modes.PPC64LE.P, h₁.r4]; rfl
  have eD : Proof.Modes.PPC64LE.dataRegion (Proof.Modes.PPC64LE.Dp s₁) M.step (Proof.Modes.PPC64LE.N s₁) =
      ⟨s.gpr .r6, 8 * (s.gpr .r7).toNat⟩ := by
    simp only [Proof.Modes.PPC64LE.dataRegion, Proof.Modes.PPC64LE.Dp, Proof.Modes.PPC64LE.N, h₁.r5, h₁.r6, hstep]
  have hwr₁ : s₁.wr = [⟨s.gpr .r5, 8⟩, ⟨s.gpr .r6, 8 * (s.gpr .r7).toNat⟩, ⟨s.gpr .r8, 8 * 22⟩] := by
    rw [h₁.wr, hwr]
  refine ⟨⟨by rw [hwr₁]; simp [Proof.Modes.PPC64LE.S, h₁.r7, dirCore], by
      simp only [Proof.Modes.PPC64LE.S, h₁.r7]; exact fS⟩,
    by rw [eV, hwr₁]; simp, fun _ => by rw [eV, hwr₁]; simp,
    by simp only [Proof.Modes.PPC64LE.P, h₁.r4]; exact fV, by rw [eD, hwr₁]; simp,
    by simp only [Proof.Modes.PPC64LE.Dp, Proof.Modes.PPC64LE.N, h₁.r5, h₁.r6, hstep]; exact fD,
    by rw [eD, eS]; exact dDS, by rw [eV, eS]; exact dVS, fun _ => by rw [eV, eD]; exact dVD,
    ⟨by omega, by rw [hstep]; rfl⟩, layout up n⟩

/-- `modePC`'s precondition gives the key's arguments. -/
theorem keyArgs_of (up : Bool) {n : Nat} {M : Mode} (hstep : M.step = 8) :
    KeyArgs s₁ (Proof.Modes.PPC64LE.wrs0 (dirCore up n) M s₁) (keyOf s) := by
  obtain ⟨⟨hrd, hwr, -, dKD, dKS, -, -, -, fK, -, -, -, -⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr] at hrd hwr dKD dKS fK
  have trd : (⟨s.syms s1234Sym, 4096⟩ : Region) ∈ s.rd := s1234_len ▸ ConstsOk.rd1 hk
  have twr : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ r := s1234_len ▸ ConstsOk.wr1 hk
  have ews : Proof.Modes.PPC64LE.wrs0 (dirCore up n) M s₁ =
      [⟨s.gpr .r6, 8 * (s.gpr .r7).toNat⟩, ⟨s.gpr .r8, 8 * 22⟩] := by
    simp only [Proof.Modes.PPC64LE.wrs0, Proof.Modes.PPC64LE.wrs, Proof.Modes.PPC64LE.dataRegion,
      Proof.Modes.PPC64LE.scrRegion, Proof.Modes.PPC64LE.Dp, Proof.Modes.PPC64LE.N, Proof.Modes.PPC64LE.S,
      h₁.r5, h₁.r6, h₁.r7, hstep]
    rfl
  have hin : ∀ r ∈ Proof.Modes.PPC64LE.wrs0 (dirCore up n) M s₁, r ∈ s.wr := fun r hr => by
    rw [ews] at hr; rw [hwr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  refine ⟨by rw [h₁.mem, h₁.r3], ?_, by rw [h₁.r3]; exact fK, fun r hr => ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [h₁.rd, h₁.wr, Mode.keyR, h₁.r3]
    exact List.mem_append_left _ (stripConsts_rd_mem (by rw [hrd]; simp))
  · rw [ews] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [Mode.keyR, h₁.r3]; exact dKD
    · rw [Mode.keyR, h₁.r3]; exact dKS
  · rw [h₁.rd, h₁.wr, Mode.tblR, h₁.syms]; exact List.mem_append_left _ trd
  · rw [h₁.mem, h₁.syms]; exact ConstsOk.held1 hk
  · rw [Mode.tblR, h₁.syms]; exact twr r (hin r hr)

end

/-- The data in blocks, as the modes' steps. -/
theorem dataAt_eq (m : Mem) (s s₁ : State) (h₁ : Shifted s s₁) :
    Proof.Modes.chunksAt 8 m (Proof.Modes.PPC64LE.Dp s₁) (Proof.Modes.PPC64LE.N s₁) = dataAt m s := by
  rw [dataAt, Proof.Cast5.cbcBlocksAt_eq]
  simp only [Proof.Modes.PPC64LE.Dp, Proof.Modes.PPC64LE.N, h₁.r5, h₁.r6]

theorem ivAt_eq (m : Mem) (s s₁ : State) (h₁ : Shifted s s₁) :
    Spec.Aes.bytesAt m (Proof.Modes.PPC64LE.P s₁) 8 = ivAt m s := by
  simp only [Proof.Modes.PPC64LE.P, h₁.r4, ivAt]

/-! ## Correctness -/

/-- A mode's result from the modes' proof, in the functions' terms. -/
theorem post_eq {s s₁ : State} (h₁ : Shifted s s₁) {m : Mem} :
    Proof.Modes.chunksAt 8 m (Proof.Modes.PPC64LE.Dp s₁) (Proof.Modes.PPC64LE.N s₁) = dataAt m s ∧
      Spec.Aes.bytesAt m (Proof.Modes.PPC64LE.P s₁) 8 = ivAt m s ∧
      Proof.Modes.PPC64LE.N s₁ = (s.gpr .r7).toNat :=
  ⟨dataAt_eq m s s₁ h₁, ivAt_eq m s s₁ h₁, by simp only [Proof.Modes.PPC64LE.N, h₁.r6]⟩

theorem cbcEncryptChained_correct (s : State) (hs : (modePC cbcEncPost).pre s) :
    ∃ t s', Exec isa cbcEncryptChained s t s' ∧ abiPreserved s s' ∧ cbcEncPost s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.PPC64LE.cbcEncChained_wp
    (dirCoreSpec true _ (rounds_of hs)) (seqPre_of hs h₁ true (M := Mode.cbcEncChained 2) rfl)
    (keyArgs_of hs h₁ true (M := Mode.cbcEncChained 2) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨d0, i0, -⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, Proof.Modes.PPC64LE.iv0, Proof.Modes.PPC64LE.blocks0,
    ↓reduceIte] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', d0, i0, h₁.mem] at h3
  exact ⟨h2, h3⟩

theorem cbcDecryptChained_correct (s : State) (hs : (modePC cbcDecPost).pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧ cbcDecPost s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.PPC64LE.cbcDecChained_wp
    (dirCoreSpec false _ (rounds_of hs)) (seqPre_of hs h₁ false (M := Mode.cbcDecChained 2) rfl)
    (keyArgs_of hs h₁ false (M := Mode.cbcDecChained 2) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨d0, i0, -⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, Proof.Modes.PPC64LE.iv0, Proof.Modes.PPC64LE.blocks0,
    Bool.false_eq_true, ↓reduceIte] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', d0, i0, h₁.mem] at h3
  exact ⟨h2, h3⟩

theorem ofb_correct (s : State) (hs : (modePC ofbPost).pre s) :
    ∃ t s', Exec isa ofb s t s' ∧ abiPreserved s s' ∧ ofbPost s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.PPC64LE.ofb_wp
    (dirCoreSpec true _ (rounds_of hs)) (seqPre_of hs h₁ true (M := Mode.ofb 2) rfl)
    (keyArgs_of hs h₁ true (M := Mode.ofb 2) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨d0, i0, n0⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, Proof.Modes.PPC64LE.iv0, Proof.Modes.PPC64LE.blocks0,
    ↓reduceIte] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', i0, n0, h₁.mem] at h3
  exact ⟨h2, h3⟩

theorem cfbEncrypt_correct (s : State) (hs : (modePC cfbEncPost).pre s) :
    ∃ t s', Exec isa cfbEncrypt s t s' ∧ abiPreserved s s' ∧ cfbEncPost s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.PPC64LE.cfbEnc_wp
    (dirCoreSpec true _ (rounds_of hs)) (seqPre_of hs h₁ true (M := Mode.cfbEnc 2) rfl)
    (keyArgs_of hs h₁ true (M := Mode.cfbEnc 2) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨d0, i0, -⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, Proof.Modes.PPC64LE.iv0, Proof.Modes.PPC64LE.blocks0,
    ↓reduceIte] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', d0, i0, h₁.mem] at h3
  exact ⟨h2, h3⟩

theorem cfbDecrypt_correct (s : State) (hs : (modePC cfbDecPost).pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ cfbDecPost s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.PPC64LE.cfbDec_wp
    (dirCoreSpec true _ (rounds_of hs)) (seqPre_of hs h₁ true (M := Mode.cfbDec 2) rfl)
    (keyArgs_of hs h₁ true (M := Mode.cfbDec 2) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨d0, i0, -⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, Proof.Modes.PPC64LE.iv0, Proof.Modes.PPC64LE.blocks0,
    ↓reduceIte] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', d0, i0, h₁.mem] at h3
  exact ⟨h2, h3⟩

/-! ## The contracts -/

/-- A state satisfying `modeP`'s precondition: the subkeys at `0x1000`, 16
rounds, the IV at `0x2000`, no data at `0x3000` and the working space at
`0x4000`. -/
def modeSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 0x2000 | .r6 => 0x3000 | .r8 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 176⟩]

theorem argPub_iff (s₁ s₂ : State) : argPub s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 := by
  simp [argPub]

/-- A mode's scratch contract with the table, from `modeP`'s implying it
without. -/
theorem implies_consts {post : State → State → Prop} {sig : Sig}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post' : sig.Post abi.ptrBits}
    (h : (modeP post).Implies (Proof.Cast5.modeScratchContract abi sig 22 pre post'))
    (hpost : ∀ s s', post s s' → post (stripConsts ecbConsts s) s')
    (hsat : ∃ s, (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts) sig 22 pre post').pre s) :
    (modePC post).Implies (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts) sig 22 pre post') where
  pre s hs := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at hs
    exact ⟨h.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
  post s s' hs hp := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at hs ⊢
    exact post_consts.mpr (post_stripConsts.mp (h.post (stripConsts ecbConsts s) s' (pre_consts.mp hs).1
      (hpost s s' hp)))
  pub s₁ s₂ h₁ h₂ hp := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at h₁ h₂ hp
    have a := h.pub (stripConsts ecbConsts s₁) (stripConsts ecbConsts s₂) (pre_consts.mp h₁).1
      (pre_consts.mp h₂).1 (pub_stripConsts.mpr (pub_consts.mp hp).1)
    exact ⟨a.1, a.2, (pub_consts.mp hp).2 _ List.mem_cons_self⟩
  sat := hsat

/-- `modeSat` with the table, at `0x100000`. -/
def modeSatC : State :=
  { modeSat with mem := ecbSatMem, rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩], syms := fun _ => 0x100000 }

/-- `modeP`'s precondition, public data and witness are the scratch
contract's under `abi`, for any postcondition it implies. -/
theorem modeP_implies {post : State → State → Prop} {post' : Spec.Cast5.cbcChainedSig.Post abi.ptrBits}
    (hpost : ∀ s s', post s s' → (Proof.Cast5.modeScratchContract abi Spec.Cast5.cbcChainedSig 22
      (Proof.Cast5.cbcChainedPre abi.ptrBits) post').post s s') :
    (modeP post).Implies (Proof.Cast5.modeScratchContract abi Spec.Cast5.cbcChainedSig 22
      (Proof.Cast5.cbcChainedPre abi.ptrBits) post') where
  pre s h := by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, abi, argRegs, stackBelow] at h
    simp only [Curry.app, Nat.mul_comm _ 8] at h
    exact h
  post s s' _ hp := hpost s s' hp
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.cbcChainedSig, abi, argRegs] at h
    obtain ⟨hsp, h3, h4, h5, h6, h7, h8⟩ := h
    exact ⟨hsp, by simp [h3, h4, h5, h6, h7, h8]⟩
  sat := ⟨modeSat, by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, abi, argRegs, stackBelow]
    simp only [Curry.app]
    repeat' apply And.intro
    all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)⟩

theorem cbc_sat (post : Spec.Cast5.cbcChainedSig.Post abi.ptrBits) :
    ∃ s, (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts) Spec.Cast5.cbcChainedSig 22
      (Proof.Cast5.cbcChainedPre abi.ptrBits) post).pre s := by
  refine ⟨modeSatC, ?_⟩
  have hl : s1234.length = 512 := by rw [Impl.Cast5.s1234, table_length]
  have held := ecbSatMem_held
  generalize e : modeSatC = s
  sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
    Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, abi, argRegs, ecbConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow, Proof.Cast5.s1234_length]
  subst e
  simp only [Curry.app]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, ?_⟩
  · change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 0⟩, ⟨0x4000, 176⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)

theorem cbcEnc_implies : (modePC cbcEncPost).Implies (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts)
    Spec.Cast5.cbcChainedSig 22 (Proof.Cast5.cbcChainedPre abi.ptrBits) (Proof.Cast5.cbcEncChainedPost abi.ptrBits)) :=
  implies_consts (modeP_implies fun s s' hp => by
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcEncChainedPost, abi, argRegs]
    simp only [Curry.app]
    exact hp) (fun _ _ h => h) (cbc_sat _)

theorem cbcDec_implies : (modePC cbcDecPost).Implies (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts)
    Spec.Cast5.cbcChainedSig 22 (Proof.Cast5.cbcChainedPre abi.ptrBits) (Proof.Cast5.cbcDecChainedPost abi.ptrBits)) :=
  implies_consts (modeP_implies fun s s' hp => by
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcDecChainedPost, abi, argRegs]
    simp only [Curry.app]
    exact hp) (fun _ _ h => h) (cbc_sat _)

theorem ofb_implies : (modePC ofbPost).Implies (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts)
    Spec.Cast5.ofbSig 22 (Spec.Cast5.ofbPre abi.ptrBits) (Proof.Cast5.ofbPost abi.ptrBits)) :=
  implies_consts (modeP_implies fun s s' hp => by
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.ofbSig, Proof.Cast5.ofbPost, abi, argRegs]
    simp only [Curry.app]
    exact hp) (fun _ _ h => h) (cbc_sat _)

theorem cfbEnc_implies : (modePC cfbEncPost).Implies (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts)
    Spec.Cast5.cfbSig 22 (Spec.Cast5.cfbPre abi.ptrBits) (Proof.Cast5.cfbEncPost abi.ptrBits)) :=
  implies_consts (modeP_implies fun s s' hp => by
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.cfbSig, Proof.Cast5.cfbEncPost, abi, argRegs]
    simp only [Curry.app]
    exact hp) (fun _ _ h => h) (cbc_sat _)

theorem cfbDec_implies : (modePC cfbDecPost).Implies (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts)
    Spec.Cast5.cfbSig 22 (Spec.Cast5.cfbPre abi.ptrBits) (Proof.Cast5.cfbDecPost abi.ptrBits)) :=
  implies_consts (modeP_implies fun s s' hp => by
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.cfbSig, Proof.Cast5.cfbDecPost, abi, argRegs]
    simp only [Curry.app]
    exact hp) (fun _ _ h => h) (cbc_sat _)

/-! ## Verified, with the working space as an argument -/

theorem cbcEncryptChained_verified : Verified target cbcEncryptChained
    (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts) Spec.Cast5.cbcChainedSig 22
      (Proof.Cast5.cbcChainedPre abi.ptrBits) (Proof.Cast5.cbcEncChainedPost abi.ptrBits)) :=
  Verified.of_correct cbcEncryptChained_correct (cbcEncryptChained_constantTime _) cbcEnc_implies

theorem cbcDecryptChained_verified : Verified target cbcDecryptChained
    (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts) Spec.Cast5.cbcChainedSig 22
      (Proof.Cast5.cbcChainedPre abi.ptrBits) (Proof.Cast5.cbcDecChainedPost abi.ptrBits)) :=
  Verified.of_correct cbcDecryptChained_correct (cbcDecryptChained_constantTime _) cbcDec_implies

theorem ofb_verified : Verified target ofb
    (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts) Spec.Cast5.ofbSig 22
      (Spec.Cast5.ofbPre abi.ptrBits) (Proof.Cast5.ofbPost abi.ptrBits)) :=
  Verified.of_correct ofb_correct (ofb_constantTime _) ofb_implies

theorem cfbEncrypt_verified : Verified target cfbEncrypt
    (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts) Spec.Cast5.cfbSig 22
      (Spec.Cast5.cfbPre abi.ptrBits) (Proof.Cast5.cfbEncPost abi.ptrBits)) :=
  Verified.of_correct cfbEncrypt_correct (cfbEncrypt_constantTime _) cfbEnc_implies

theorem cfbDecrypt_verified : Verified target cfbDecrypt
    (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts) Spec.Cast5.cfbSig 22
      (Spec.Cast5.cfbPre abi.ptrBits) (Proof.Cast5.cfbDecPost abi.ptrBits)) :=
  Verified.of_correct cfbDecrypt_correct (cfbDecrypt_constantTime _) cfbDec_implies

end VG.Proof.Cast5.PPC64LE.Modes
