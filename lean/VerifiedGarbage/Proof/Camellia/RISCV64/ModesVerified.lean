module

public import VerifiedGarbage.Proof.Camellia.RISCV64.ModesConstantTime
public import VerifiedGarbage.Proof.Camellia.RISCV64.ModeCore
public import VerifiedGarbage.Spec.Camellia.Cbc
public import VerifiedGarbage.Spec.Camellia.Cfb
public import VerifiedGarbage.Spec.Camellia.Ofb
public import VerifiedGarbage.Spec.Camellia.Ctr
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Modes.RISCV64.Seq
public import VerifiedGarbage.Proof.Modes.Steps
public import VerifiedGarbage.Spec.Cfb
public import VerifiedGarbage.Spec.Ofb
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Modes.RISCV64.Modes
import VerifiedGarbage.Proof.Modes.RISCV64.Ctr
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Camellia.RISCV64.ModesConstantTime
meta import VerifiedGarbage.Proof.Camellia.RISCV64.ModeCore
meta import VerifiedGarbage.Spec.Camellia.Cbc
meta import VerifiedGarbage.Spec.Camellia.Cfb
meta import VerifiedGarbage.Spec.Camellia.Ofb
meta import VerifiedGarbage.Spec.Camellia.Ctr
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# Camellia's modes on RISC-V meet their contracts

`modeFn m` moves the arguments to the modes' registers and runs `m R` for
the number of rounds `R` (`modeFn_wp`), and each `m R` is a mode of
`Proof/Modes/RISCV64/` over Camellia's core with `R` rounds
(`Mode.dirCoreSpec`), as CAST5's are (`Proof/Cast5/RISCV64/ModesVerified.lean`).
`cbcEncryptChained_verified`, `ofb_verified`, …: each meets the shared
contract with `stack := 3248`: the mode's frame of 406 slots below the stack
pointer, which holds ECB's scratch buffer and which it zeroes before
returning. The proofs are written against `modeContract`, which states the
frame.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64.Modes

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Camellia.RISCV64 VG.Impl.Modes
open VG.Proof.Modes.RISCV64 (SeqPre)
open VG.Proof.Camellia.RISCV64.Mode (dirCoreSpec KeyArgs layout)
open VG.Proof.Camellia.RISCV64 (modePub)
open VG.Proof.Camellia (schedWords)

/-- The frame's bytes. -/
abbrev frameBytes : Nat := 3248

/-! ## The arguments -/

/-- The number of rounds. -/
abbrev rounds (s : State) : Nat := (s.gpr .a1).toNat
/-- Camellia, and its inverse, under the subkeys of the schedule at `a0` and `a1`'s rounds. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher :=
  Spec.Camellia.cipher (Spec.Camellia.subkeysAt s.mem (s.gpr .a0) (rounds s))
abbrev invCiph (s : State) : Spec.Cbc.Cipher :=
  Spec.Camellia.invCipher (Spec.Camellia.subkeysAt s.mem (s.gpr .a0) (rounds s))
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m (s.gpr .a2) 16
/-- The data, in blocks. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) := Spec.Cbc.blocksAt m (s.gpr .a3) (s.gpr .a4).toNat

/-- The state after `modeFn`'s moves, from `s`: the arguments in the modes'
registers, and nothing else the caller sees changed. -/
structure Shifted (s s₁ : State) : Prop where
  a0 : s₁.gpr .a0 = s.gpr .a0
  a1 : s₁.gpr .a1 = s.gpr .a2
  a2 : s₁.gpr .a2 = s.gpr .a3
  a3 : s₁.gpr .a3 = s.gpr .a4
  other : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  ra : s₁.gpr .ra = s.gpr .ra
  mem : s₁.mem = s.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp
  syms : s₁.syms = s.syms

theorem Shifted.abi {s s₁ s' : State} (h : Shifted s s₁) (ha : abiPreserved s₁ s') : abiPreserved s s' :=
  ⟨fun r hr => (ha.1 r hr).trans (h.other r hr), ha.2.1.trans h.sp, ha.2.2.trans h.ra⟩

/-- `modeFn m` runs `m` with the number of rounds, from the state with the
arguments moved. -/
theorem modeFn_wp {m : Nat → Prog isa} {s : State} {Q : State → Prop} (hn : rounds s = 18 ∨ rounds s = 24)
    (h : ∀ s₁, Shifted s s₁ → WP isa (m (rounds s)) s₁ Q) : WP isa (modeFn m) s Q := by
  unfold modeFn
  refine WP.seq (WP.cons (exec_addi (by decide)) (WP.cons (exec_addi (by decide)) (WP.cons (exec_addi (by decide))
    (WP.cons (exec_addi (by decide)) (WP.cons (exec_addi (by decide)) (WP.block_nil ?_))))))
  generalize hs₁ : State.write _ _ _ = s₁
  have sh : Shifted s s₁ := by
    subst hs₁
    refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · simp [State.write]
    · simp [State.write]
    · simp [State.write]
    · simp [State.write]
    · have h1 : r ≠ .a1 := by rintro rfl; simp [preserved] at hr
      have h2 : r ≠ .a2 := by rintro rfl; simp [preserved] at hr
      have h3 : r ≠ .a3 := by rintro rfl; simp [preserved] at hr
      have h0 : r ≠ .t0 := by rintro rfl; simp [preserved] at hr
      simp [State.write, h1, h2, h3, h0]
    · simp [State.write]
  have t0 : s₁.gpr .t0 = s.gpr .a1 + BitVec.ofInt 64 0 + BitVec.ofInt 64 (-18) := by
    subst hs₁; simp only [State.write]; simp
  have e1 : s.gpr .a1 = BitVec.ofNat 64 (rounds s) := by simp only [rounds, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rcases hn with hn | hn
  · refine WP.ite true (by rw [eval_zero, t0, e1, hn]; decide) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hn ▸ h s₁ sh
  · refine WP.ite false (by rw [eval_zero, t0, e1, hn]; decide) (fun h => absurd h (by decide)) (fun _ => ?_)
    exact hn ▸ h s₁ sh

/-! ## The modes' contract, as the proof states it -/

/-- A mode's function on RISC-V, with its frame below the stack pointer,
and the postcondition `post`. -/
def modeContract (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 272⟩
    let iv : Region := ⟨s.gpr .a2, 16⟩
    let data : Region := ⟨s.gpr .a3, 16 * (s.gpr .a4).toNat⟩
    let stack : Region := ⟨s.sp - frameBytes, frameBytes⟩
    s.rd = [key] ∧ s.wr = [iv, data] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ iv.Disjoint data ∧
      (s.gpr .a0).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + 16 * (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ frameBytes ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint iv ∧
      stack.Disjoint data ∧ ((s.gpr .a1).toNat = 18 ∨ (s.gpr .a1).toNat = 24)
  post s s' := ((s.gpr .a1).toNat = 18 ∨ (s.gpr .a1).toNat = 24) → post s s'
  pub := modePub

/-- The functions' postconditions. -/
def cbcEncPost (s s' : State) : Prop :=
  let cs := Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s)
  dataAt s'.mem s = cs ∧ ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) cs
def cbcDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (invCiph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)
def ofbPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ofb.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ofb.next (ciph s) (ivAt s.mem s) (s.gpr .a4).toNat
def cfbEncPost (s s' : State) : Prop :=
  let cs := Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s)
  dataAt s'.mem s = cs ∧ ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) cs
def cfbDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)
def ctrPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ctr.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ctr.next (ivAt s.mem s) (s.gpr .a4).toNat

section
variable {post : State → State → Prop} {s s₁ : State} (hs : (modeContract post).pre s) (h₁ : Shifted s s₁)
include hs

theorem rounds_of : rounds s = 18 ∨ rounds s = 24 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hn⟩ := hs
  exact hn

include h₁

/-- `modeContract`'s precondition gives the modes'. -/
theorem seqPre_of (d : Dir) (R : Nat) {M : Mode} (hstep : M.step = 16) : SeqPre (dirCore d R) M s₁ := by
  obtain ⟨-, hwr, -, -, dVD, -, fV, fD, al, sp, -, dSV, dSD, -⟩ := hs
  have eS : Proof.Modes.RISCV64.scrRegion (dirCore d R) (Proof.Modes.RISCV64.Fb s₁ (dirCore d R)) =
      ⟨s.sp - frameBytes, frameBytes⟩ := by
    simp only [Proof.Modes.RISCV64.scrRegion, Proof.Modes.RISCV64.Fb, h₁.sp]; rfl
  have eV : Proof.Modes.RISCV64.ivR s₁ (dirCore d R) = ⟨s.gpr .a2, 16⟩ := by
    simp only [Proof.Modes.RISCV64.ivR, Proof.Modes.RISCV64.P, h₁.a1]; rfl
  have eD : Proof.Modes.RISCV64.dataRegion (Proof.Modes.RISCV64.Dp s₁) M.step (Proof.Modes.RISCV64.N s₁) =
      ⟨s.gpr .a3, 16 * (s.gpr .a4).toNat⟩ := by
    simp only [Proof.Modes.RISCV64.dataRegion, Proof.Modes.RISCV64.Dp, Proof.Modes.RISCV64.N, h₁.a2, h₁.a3, hstep]
  have hwr₁ : s₁.wr = [⟨s.gpr .a2, 16⟩, ⟨s.gpr .a3, 16 * (s.gpr .a4).toNat⟩] := by rw [h₁.wr, hwr]
  refine ⟨by rw [h₁.sp]; exact al, by rw [h₁.sp]; exact sp, by rw [eV, hwr₁]; simp,
    fun _ => by rw [eV, hwr₁]; simp,
    by simp only [Proof.Modes.RISCV64.P, h₁.a1]; exact fV, by rw [eD, hwr₁]; simp,
    by simp only [Proof.Modes.RISCV64.Dp, Proof.Modes.RISCV64.N, h₁.a2, h₁.a3, hstep]; exact fD,
    by rw [eD, eS]; exact dSD.symm, by rw [eV, eS]; exact dSV.symm, fun _ => by rw [eV, eD]; exact dVD,
    ⟨by omega, by rw [hstep]; rfl⟩, layout d R⟩

/-- `modeContract`'s precondition gives the key's arguments. -/
theorem keyArgs_of (d : Dir) (R : Nat) {M : Mode} (hstep : M.step = 16) :
    KeyArgs R s₁ (Proof.Modes.RISCV64.wrs0 (dirCore d R) M s₁) (schedWords s.mem (s.gpr .a0) R) := by
  obtain ⟨hrd, -, -, dKD, -, fK, -, -, -, -, dSK, -, -, -⟩ := hs
  have ews : Proof.Modes.RISCV64.wrs0 (dirCore d R) M s₁ =
      [⟨s.gpr .a3, 16 * (s.gpr .a4).toNat⟩, ⟨s.sp - frameBytes, frameBytes⟩] := by
    simp only [Proof.Modes.RISCV64.wrs0, Proof.Modes.RISCV64.wrs, Proof.Modes.RISCV64.dataRegion,
      Proof.Modes.RISCV64.scrRegion, Proof.Modes.RISCV64.Dp, Proof.Modes.RISCV64.N, Proof.Modes.RISCV64.Fb,
      h₁.a2, h₁.a3, h₁.sp, hstep]
    rfl
  refine ⟨s.gpr .a0, h₁.a0, by rw [h₁.mem], by rw [h₁.rd, hrd]; simp, fK, fun r hr => ?_⟩
  rw [ews] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact dKD
  · exact dSK.symm

end

/-- A mode's result from the modes' proof, in the functions' terms. -/
theorem post_eq {s s₁ : State} (h₁ : Shifted s s₁) {m : Mem} :
    Proof.Modes.chunksAt 16 m (Proof.Modes.RISCV64.Dp s₁) (Proof.Modes.RISCV64.N s₁) = dataAt m s ∧
      Spec.Aes.bytesAt m (Proof.Modes.RISCV64.P s₁) 16 = ivAt m s ∧
      Proof.Modes.RISCV64.N s₁ = (s.gpr .a4).toNat := by
  refine ⟨?_, by simp only [Proof.Modes.RISCV64.P, h₁.a1, ivAt], by simp only [Proof.Modes.RISCV64.N, h₁.a3]⟩
  simp only [Proof.Modes.RISCV64.Dp, Proof.Modes.RISCV64.N, h₁.a2, h₁.a3]
  rfl

/-! ## Correctness -/

attribute [local irreducible] Spec.Camellia.cipher Spec.Camellia.invCipher in
/-- The core's cipher is the contract's, without unfolding it. -/
theorem cipher_enc (m : Mem) (p : Addr) {R : Nat} (hR : R = 18 ∨ R = 24) :
    (dirCoreSpec .encrypt R hR).cipher (schedWords m p R) = Spec.Camellia.cipher (Spec.Camellia.subkeysAt m p R) :=
  rfl

attribute [local irreducible] Spec.Camellia.cipher Spec.Camellia.invCipher in
theorem cipher_dec (m : Mem) (p : Addr) {R : Nat} (hR : R = 18 ∨ R = 24) :
    (dirCoreSpec .decrypt R hR).cipher (schedWords m p R) = Spec.Camellia.invCipher (Spec.Camellia.subkeysAt m p R) :=
  rfl

theorem bw_eq (d : Dir) (R : Nat) : 4 * (dirCore d R).bw = 16 := rfl

theorem cbcEncryptChained_correct (s : State) (hs : (modeContract cbcEncPost).pre s) :
    ∃ t s', Exec isa cbcEncryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract cbcEncPost).post s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.cbcEncChained_wp
    (dirCoreSpec .encrypt _ (rounds_of hs)) (seqPre_of hs h₁ .encrypt _ (M := Mode.cbcEncChained 4) rfl)
    (keyArgs_of hs h₁ .encrypt _ (M := Mode.cbcEncChained 4) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, fun _ => ?_⟩
  obtain ⟨d0, i0, -⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [Proof.Modes.RISCV64.iv0, Proof.Modes.RISCV64.blocks0, bw_eq, cipher_enc] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', d0, i0, h₁.mem] at h3
  exact ⟨h2, h3⟩

theorem cbcDecryptChained_correct (s : State) (hs : (modeContract cbcDecPost).pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract cbcDecPost).post s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.cbcDecChained_wp
    (dirCoreSpec .decrypt _ (rounds_of hs)) (seqPre_of hs h₁ .decrypt _ (M := Mode.cbcDecChained 4) rfl)
    (keyArgs_of hs h₁ .decrypt _ (M := Mode.cbcDecChained 4) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, fun _ => ?_⟩
  obtain ⟨d0, i0, -⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [Proof.Modes.RISCV64.iv0, Proof.Modes.RISCV64.blocks0, bw_eq, cipher_dec] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', d0, i0, h₁.mem] at h3
  exact ⟨h2, h3⟩

theorem ofb_correct (s : State) (hs : (modeContract ofbPost).pre s) :
    ∃ t s', Exec isa ofb s t s' ∧ abiPreserved s s' ∧ (modeContract ofbPost).post s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.ofb_wp
    (dirCoreSpec .encrypt _ (rounds_of hs)) (seqPre_of hs h₁ .encrypt _ (M := Mode.ofb 4) rfl)
    (keyArgs_of hs h₁ .encrypt _ (M := Mode.ofb 4) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, fun _ => ?_⟩
  obtain ⟨d0, i0, n0⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [Proof.Modes.RISCV64.iv0, Proof.Modes.RISCV64.blocks0, bw_eq, cipher_enc] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', i0, n0, h₁.mem] at h3
  exact ⟨h2, h3⟩

theorem cfbEncrypt_correct (s : State) (hs : (modeContract cfbEncPost).pre s) :
    ∃ t s', Exec isa cfbEncrypt s t s' ∧ abiPreserved s s' ∧ (modeContract cfbEncPost).post s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.cfbEnc_wp
    (dirCoreSpec .encrypt _ (rounds_of hs)) (seqPre_of hs h₁ .encrypt _ (M := Mode.cfbEnc 4) rfl)
    (keyArgs_of hs h₁ .encrypt _ (M := Mode.cfbEnc 4) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, fun _ => ?_⟩
  obtain ⟨d0, i0, -⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [Proof.Modes.RISCV64.iv0, Proof.Modes.RISCV64.blocks0, bw_eq, cipher_enc] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', d0, i0, h₁.mem] at h3
  exact ⟨h2, h3⟩

theorem cfbDecrypt_correct (s : State) (hs : (modeContract cfbDecPost).pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ (modeContract cfbDecPost).post s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.cfbDec_wp
    (dirCoreSpec .encrypt _ (rounds_of hs)) (seqPre_of hs h₁ .encrypt _ (M := Mode.cfbDec 4) rfl)
    (keyArgs_of hs h₁ .encrypt _ (M := Mode.cfbDec 4) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, fun _ => ?_⟩
  obtain ⟨d0, i0, -⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [Proof.Modes.RISCV64.iv0, Proof.Modes.RISCV64.blocks0, bw_eq, cipher_enc] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', d0, i0, h₁.mem] at h3
  exact ⟨h2, h3⟩

theorem ctr_correct (s : State) (hs : (modeContract ctrPost).pre s) :
    ∃ t s', Exec isa ctr s t s' ∧ abiPreserved s s' ∧ (modeContract ctrPost).post s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.ctr_wp
    (dirCoreSpec .encrypt _ (rounds_of hs)) rfl (seqPre_of hs h₁ .encrypt _ (M := Mode.ctr) rfl)
    (keyArgs_of hs h₁ .encrypt _ (M := Mode.ctr) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, fun _ => ?_⟩
  obtain ⟨d0, i0, n0⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [Proof.Modes.RISCV64.iv0, Proof.Modes.RISCV64.blocks0, bw_eq, cipher_enc] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', i0, n0, h₁.mem] at h3
  exact ⟨h2, h3⟩

/-! ## The contracts -/

/-- A state satisfying the modes' precondition: the schedule at `0x1000`,
18 rounds, the IV at `0x3000`, no data at `0x4000`, and the stack below
`0x8000`. -/
def modeSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 18 | .a2 => 0x3000 | .a3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 0⟩]

theorem modePub_iff (s₁ s₂ : State) : modePub s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 := by
  simp [modePub]

theorem cbcEncryptChained_verified :
    Verified RISCV64.target cbcEncryptChained (Spec.Camellia.cbcEncryptChainedContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cbcEncryptChained_correct (cbcEncryptChained_constantTime _) ?_
  contract_implies [Spec.Camellia.cbcEncryptChainedContract, Spec.Camellia.cbcChainedSig,
    RISCV64.abi, RISCV64.argRegs, modeContract, cbcEncPost, modePub_iff] [modeSat] using modeSat

theorem cbcDecryptChained_verified :
    Verified RISCV64.target cbcDecryptChained (Spec.Camellia.cbcDecryptChainedContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cbcDecryptChained_correct (cbcDecryptChained_constantTime _) ?_
  contract_implies [Spec.Camellia.cbcDecryptChainedContract, Spec.Camellia.cbcChainedSig,
    RISCV64.abi, RISCV64.argRegs, modeContract, cbcDecPost, modePub_iff] [modeSat] using modeSat

theorem ofb_verified : Verified RISCV64.target ofb (Spec.Camellia.ofbContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct ofb_correct (ofb_constantTime _) ?_
  contract_implies [Spec.Camellia.ofbContract, Spec.Camellia.ofbSig, Spec.Camellia.ofbPre, Spec.Camellia.ofbPost,
    RISCV64.abi, RISCV64.argRegs, modeContract, ofbPost, modePub_iff] [modeSat] using modeSat

theorem cfbEncrypt_verified :
    Verified RISCV64.target cfbEncrypt (Spec.Camellia.cfbEncryptContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cfbEncrypt_correct (cfbEncrypt_constantTime _) ?_
  contract_implies [Spec.Camellia.cfbEncryptContract, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre,
    Spec.Camellia.cfbEncryptPost, RISCV64.abi, RISCV64.argRegs, modeContract, cfbEncPost, modePub_iff]
    [modeSat] using modeSat

theorem cfbDecrypt_verified :
    Verified RISCV64.target cfbDecrypt (Spec.Camellia.cfbDecryptContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cfbDecrypt_correct (cfbDecrypt_constantTime _) ?_
  contract_implies [Spec.Camellia.cfbDecryptContract, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre,
    Spec.Camellia.cfbDecryptPost, RISCV64.abi, RISCV64.argRegs, modeContract, cfbDecPost, modePub_iff]
    [modeSat] using modeSat

theorem ctr_verified : Verified RISCV64.target ctr (Spec.Camellia.ctrContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct ctr_correct (ctr_constantTime _) ?_
  contract_implies [Spec.Camellia.ctrContract, Spec.Camellia.ctrSig, Spec.Camellia.ctrPre, Spec.Camellia.ctrPost,
    RISCV64.abi, RISCV64.argRegs, modeContract, ctrPost, modePub_iff] [modeSat] using modeSat

end VG.Proof.Camellia.RISCV64.Modes
