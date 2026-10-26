module

public import VerifiedGarbage.Proof.Cast5.RISCV64.ModesConstantTime
public import VerifiedGarbage.Proof.Cast5.RISCV64.ModeCore
public import VerifiedGarbage.Proof.Cast5.RISCV64.EcbVerified
public import VerifiedGarbage.Spec.Cast5.Cbc
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Modes.RISCV64.Seq
public import VerifiedGarbage.Proof.Modes.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Spec.Cast5
public import VerifiedGarbage.Spec.Cfb
public import VerifiedGarbage.Spec.Ofb
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Modes.RISCV64.Modes
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Cast5.RISCV64.ModesLit

/-!
# CAST5's modes on RISC-V meet their contracts

`modeFn m` moves the arguments to the modes' registers and runs `m n` for
the count of rounds `n` (`modeFn_wp`), and each `m n` is a mode of
`Proof/Modes/RISCV64/` over CAST5's core with `n` rounds
(`Mode.dirCoreSpec`), as on PPC64LE (`Proof/Cast5/PPC64LE/ModesVerified.lean`).
`cbcEncryptChained_verified`, `ofb_verified`, …: each meets the shared
contract with `stack := 128` (the mode's frame of 16 slots below the stack
pointer, which it zeroes before returning), under the calling convention
with the table (`abi.withConsts ecbConsts`). The proof's contract (`modePC`)
is `modeP` for the state without the table's region, with what the contract
says of the table (`ConstsOk`).
-/

@[expose] public section

namespace VG.Proof.Cast5.RISCV64.Modes

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Cast5.RISCV64 VG.Impl.Modes
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)
open VG.Proof.Modes.RISCV64 (SeqPre)
open VG.Proof.Cast5.RISCV64.Mode (dirCoreSpec KeyArgs layout)
open VG.Proof.Cast5.RISCV64 (modePub s1234_len ecbSatMem ecbSatMem_held ecbConsts_eq)

/-- The frame's bytes. -/
abbrev frameBytes : Nat := 128

/-! ## The arguments -/

/-- The subkeys on entry. -/
abbrev keyOf (s : State) : Spec.Cast5.Schedule := Spec.Cast5.scheduleAt s.mem (s.gpr .a0)
/-- The count of rounds. -/
abbrev rounds (s : State) : Nat := (s.gpr .a1).toNat
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m (s.gpr .a2) 8
/-- The data, in blocks. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) := Spec.Cast5.cbcBlocksAt m (s.gpr .a3) (s.gpr .a4).toNat

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

/-- `modeFn m` runs `m` with the count of rounds, from the state with the
arguments moved. -/
theorem modeFn_wp {m : Nat → Prog isa} {s : State} {Q : State → Prop} (hn : rounds s = 12 ∨ rounds s = 16)
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
  have t0 : s₁.gpr .t0 = s.gpr .a1 + BitVec.ofInt 64 0 + BitVec.ofInt 64 (-12) := by
    subst hs₁; simp only [State.write]; simp
  have e1 : s.gpr .a1 = BitVec.ofNat 64 (rounds s) := by simp only [rounds, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rcases hn with hn | hn
  · refine WP.ite true (by rw [eval_zero, t0, e1, hn]; decide) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hn ▸ h s₁ sh
  · refine WP.ite false (by rw [eval_zero, t0, e1, hn]; decide) (fun h => absurd h (by decide)) (fun _ => ?_)
    exact hn ▸ h s₁ sh

/-! ## The modes' contract, as the proof states it -/

/-- The modes' public arguments, without the table's address. -/
def argPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4

/-- A mode's function on RISC-V, with its frame below the stack pointer,
and the postcondition `post`. -/
def modeP (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 128⟩
    let iv : Region := ⟨s.gpr .a2, 8⟩
    let data : Region := ⟨s.gpr .a3, 8 * (s.gpr .a4).toNat⟩
    let stack : Region := ⟨s.sp - frameBytes, frameBytes⟩
    s.rd = [key] ∧ s.wr = [iv, data] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ iv.Disjoint data ∧
      (s.gpr .a0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + 8 * (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ frameBytes ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint iv ∧
      stack.Disjoint data ∧ ((s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 16)
  post := post
  pub := argPub

/-- `modeP`, with the table. -/
def modePC (post : State → State → Prop) : Contract isa where
  pre s := (modeP post).pre (stripConsts ecbConsts s) ∧ ConstsOk ecbConsts frameBytes s
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
    ivAt s'.mem s = Spec.Ofb.next (Spec.Cast5.cipher (keyOf s) (rounds s)) (ivAt s.mem s) (s.gpr .a4).toNat
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
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hn⟩, -⟩ := hs
  exact hn

include h₁

/-- `modePC`'s precondition gives the modes'. -/
theorem seqPre_of (up : Bool) {n : Nat} {M : Mode} (hstep : M.step = 8) :
    SeqPre (dirCore up n) M s₁ := by
  obtain ⟨⟨-, hwr, -, -, dVD, -, fV, fD, al, sp, -, dSV, dSD, -⟩, -⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp] at hwr dVD fV fD al sp dSV dSD
  have eS : Proof.Modes.RISCV64.scrRegion (dirCore up n) (Proof.Modes.RISCV64.Fb s₁ (dirCore up n)) =
      ⟨s.sp - frameBytes, frameBytes⟩ := by
    simp only [Proof.Modes.RISCV64.scrRegion, Proof.Modes.RISCV64.Fb, h₁.sp]; rfl
  have eV : Proof.Modes.RISCV64.ivR s₁ (dirCore up n) = ⟨s.gpr .a2, 8⟩ := by
    simp only [Proof.Modes.RISCV64.ivR, Proof.Modes.RISCV64.P, h₁.a1]; rfl
  have eD : Proof.Modes.RISCV64.dataRegion (Proof.Modes.RISCV64.Dp s₁) M.step (Proof.Modes.RISCV64.N s₁) =
      ⟨s.gpr .a3, 8 * (s.gpr .a4).toNat⟩ := by
    simp only [Proof.Modes.RISCV64.dataRegion, Proof.Modes.RISCV64.Dp, Proof.Modes.RISCV64.N, h₁.a2, h₁.a3, hstep]
  have hwr₁ : s₁.wr = [⟨s.gpr .a2, 8⟩, ⟨s.gpr .a3, 8 * (s.gpr .a4).toNat⟩] := by rw [h₁.wr, hwr]
  refine ⟨by rw [h₁.sp]; exact al, by rw [h₁.sp]; exact sp, by rw [eV, hwr₁]; simp,
    fun _ => by rw [eV, hwr₁]; simp,
    by simp only [Proof.Modes.RISCV64.P, h₁.a1]; exact fV, by rw [eD, hwr₁]; simp,
    by simp only [Proof.Modes.RISCV64.Dp, Proof.Modes.RISCV64.N, h₁.a2, h₁.a3, hstep]; exact fD,
    by rw [eD, eS]; exact dSD.symm, by rw [eV, eS]; exact dSV.symm, fun _ => by rw [eV, eD]; exact dVD,
    ⟨by omega, by rw [hstep]; rfl⟩, layout up n⟩

/-- `modePC`'s precondition gives the key's arguments. -/
theorem keyArgs_of (up : Bool) {n : Nat} {M : Mode} (hstep : M.step = 8) :
    KeyArgs s₁ (Proof.Modes.RISCV64.wrs0 (dirCore up n) M s₁) (keyOf s) := by
  obtain ⟨⟨hrd, hwr, -, dKD, -, fK, -, -, -, -, dSK, -, -, -⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp] at hrd hwr dKD fK dSK
  have trd : (⟨s.syms s1234Sym, 4096⟩ : Region) ∈ s.rd := s1234_len ▸ ConstsOk.rd1 hk
  have twr : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ r := s1234_len ▸ ConstsOk.wr1 hk
  have tst : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.sp - frameBytes, frameBytes⟩ := by
    have := (hk.2.2 _ List.mem_cons_self).2.2 ⟨s.sp - BitVec.ofNat 64 frameBytes, frameBytes⟩ (by
      simp [abi, stackBelow])
    simp only [s1234_len] at this; exact this
  have ews : Proof.Modes.RISCV64.wrs0 (dirCore up n) M s₁ =
      [⟨s.gpr .a3, 8 * (s.gpr .a4).toNat⟩, ⟨s.sp - frameBytes, frameBytes⟩] := by
    simp only [Proof.Modes.RISCV64.wrs0, Proof.Modes.RISCV64.wrs, Proof.Modes.RISCV64.dataRegion,
      Proof.Modes.RISCV64.scrRegion, Proof.Modes.RISCV64.Dp, Proof.Modes.RISCV64.N, Proof.Modes.RISCV64.Fb,
      h₁.a2, h₁.a3, h₁.sp, hstep]
    rfl
  refine ⟨by rw [h₁.mem, h₁.a0], ?_, by rw [h₁.a0]; exact fK, fun r hr => ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [h₁.rd, h₁.wr, Mode.keyR, h₁.a0]
    exact List.mem_append_left _ (stripConsts_rd_mem (by rw [hrd]; simp))
  · rw [ews] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [Mode.keyR, h₁.a0]; exact dKD
    · rw [Mode.keyR, h₁.a0]; exact dSK.symm
  · rw [h₁.rd, h₁.wr, Mode.tblR, h₁.syms]; exact List.mem_append_left _ trd
  · rw [h₁.mem, h₁.syms]; exact ConstsOk.held1 hk
  · rw [ews] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [Mode.tblR, h₁.syms]; exact twr _ (by rw [hwr]; simp)
    · rw [Mode.tblR, h₁.syms]; exact tst

end

/-- A mode's result from the modes' proof, in the functions' terms. -/
theorem post_eq {s s₁ : State} (h₁ : Shifted s s₁) {m : Mem} :
    Proof.Modes.chunksAt 8 m (Proof.Modes.RISCV64.Dp s₁) (Proof.Modes.RISCV64.N s₁) = dataAt m s ∧
      Spec.Aes.bytesAt m (Proof.Modes.RISCV64.P s₁) 8 = ivAt m s ∧
      Proof.Modes.RISCV64.N s₁ = (s.gpr .a4).toNat := by
  refine ⟨?_, by simp only [Proof.Modes.RISCV64.P, h₁.a1, ivAt], by simp only [Proof.Modes.RISCV64.N, h₁.a3]⟩
  rw [dataAt, Proof.Cast5.cbcBlocksAt_eq]
  simp only [Proof.Modes.RISCV64.Dp, Proof.Modes.RISCV64.N, h₁.a2, h₁.a3]

/-! ## Correctness -/

theorem cbcEncryptChained_correct (s : State) (hs : (modePC cbcEncPost).pre s) :
    ∃ t s', Exec isa cbcEncryptChained s t s' ∧ abiPreserved s s' ∧ cbcEncPost s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.cbcEncChained_wp
    (dirCoreSpec true _ (rounds_of hs)) (seqPre_of hs h₁ true (M := Mode.cbcEncChained 2) rfl)
    (keyArgs_of hs h₁ true (M := Mode.cbcEncChained 2) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨d0, i0, -⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, Proof.Modes.RISCV64.iv0, Proof.Modes.RISCV64.blocks0,
    ↓reduceIte] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', d0, i0, h₁.mem] at h3
  exact ⟨h2, h3⟩

theorem cbcDecryptChained_correct (s : State) (hs : (modePC cbcDecPost).pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧ cbcDecPost s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.cbcDecChained_wp
    (dirCoreSpec false _ (rounds_of hs)) (seqPre_of hs h₁ false (M := Mode.cbcDecChained 2) rfl)
    (keyArgs_of hs h₁ false (M := Mode.cbcDecChained 2) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨d0, i0, -⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, Proof.Modes.RISCV64.iv0, Proof.Modes.RISCV64.blocks0,
    Bool.false_eq_true, ↓reduceIte] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', d0, i0, h₁.mem] at h3
  exact ⟨h2, h3⟩

theorem ofb_correct (s : State) (hs : (modePC ofbPost).pre s) :
    ∃ t s', Exec isa ofb s t s' ∧ abiPreserved s s' ∧ ofbPost s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.ofb_wp
    (dirCoreSpec true _ (rounds_of hs)) (seqPre_of hs h₁ true (M := Mode.ofb 2) rfl)
    (keyArgs_of hs h₁ true (M := Mode.ofb 2) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨d0, i0, n0⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, Proof.Modes.RISCV64.iv0, Proof.Modes.RISCV64.blocks0,
    ↓reduceIte] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', i0, n0, h₁.mem] at h3
  exact ⟨h2, h3⟩

theorem cfbEncrypt_correct (s : State) (hs : (modePC cfbEncPost).pre s) :
    ∃ t s', Exec isa cfbEncrypt s t s' ∧ abiPreserved s s' ∧ cfbEncPost s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.cfbEnc_wp
    (dirCoreSpec true _ (rounds_of hs)) (seqPre_of hs h₁ true (M := Mode.cfbEnc 2) rfl)
    (keyArgs_of hs h₁ true (M := Mode.cfbEnc 2) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨d0, i0, -⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, Proof.Modes.RISCV64.iv0, Proof.Modes.RISCV64.blocks0,
    ↓reduceIte] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', d0, i0, h₁.mem] at h3
  exact ⟨h2, h3⟩

theorem cfbDecrypt_correct (s : State) (hs : (modePC cfbDecPost).pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ cfbDecPost s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.cfbDec_wp
    (dirCoreSpec true _ (rounds_of hs)) (seqPre_of hs h₁ true (M := Mode.cfbDec 2) rfl)
    (keyArgs_of hs h₁ true (M := Mode.cfbDec 2) rfl)) fun s' ⟨h1, h2, h3⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨d0, i0, -⟩ := post_eq h₁ (m := s₁.mem)
  obtain ⟨d', i', -⟩ := post_eq h₁ (m := s'.mem)
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, Proof.Modes.RISCV64.iv0, Proof.Modes.RISCV64.blocks0,
    ↓reduceIte] at h2 h3
  rw [d', d0, i0, h₁.mem] at h2
  rw [i', d0, i0, h₁.mem] at h3
  exact ⟨h2, h3⟩

/-! ## The contracts -/

/-- A state satisfying `modeP`'s precondition: the subkeys at `0x1000`, 16
rounds, the IV at `0x2000`, no data at `0x3000`, and the stack below
`0x8000`. -/
def modeSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 16 | .a2 => 0x2000 | .a3 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩]

/-- `modeSat` with the table, at `0x100000`. -/
def modeSatC : State :=
  { modeSat with mem := ecbSatMem, rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩], syms := fun _ => 0x100000 }

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post' : sig.Post abi.ptrBits}
  {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {post : State → State → Prop}

/-- A mode's contract with the table, from `modeP`'s implying it without. -/
theorem implies_consts (h : (modeP post).Implies (sig.contract abi pre post' true frameBytes leak))
    (hpost : ∀ s s', post s s' → post (stripConsts ecbConsts s) s')
    (hsat : ∃ s, (sig.contract (abi.withConsts ecbConsts) pre post' true frameBytes leak).pre s) :
    (modePC post).Implies (sig.contract (abi.withConsts ecbConsts) pre post' true frameBytes leak) where
  pre s hs := ⟨h.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
  post s s' hs hp := post_consts.mpr (post_stripConsts.mp (h.post (stripConsts ecbConsts s) s'
    (pre_consts.mp hs).1 (hpost s s' hp)))
  pub s₁ s₂ h₁ h₂ hp := by
    have a := h.pub (stripConsts ecbConsts s₁) (stripConsts ecbConsts s₂) (pre_consts.mp h₁).1
      (pre_consts.mp h₂).1 (pub_stripConsts.mpr (pub_consts.mp hp).1)
    obtain ⟨hsp, e0, e1, e2, e3, e4⟩ := a
    exact ⟨hsp, by simp only [stripConsts_gpr] at e0 e1 e2 e3 e4; simp [e0, e1, e2, e3, e4],
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
  sat := hsat

end

/-- `modeP`'s precondition and public data follow from the contract's, and
the contract's postcondition from `modeP`'s, with the table. `ls` unfolds
the contract and its signature. -/
local macro "mode_implies " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  refine implies_consts
    { pre := by
        intro s h
        sig_pre [$ls,*, abi, argRegs, stackBelow] at h
        obtain ⟨al, sp, hrd, hwr, dKV, dKD, dVD, dSK, dSV, dSD, fK, fV, fD, hn⟩ := h
        simp only [Nat.mul_comm _ 8] at hwr dKD dVD dSD fD
        exact ⟨hrd, hwr, dKV, dKD, dVD, fK, fV, fD, al, sp, dSK, dSV, dSD, hn⟩
      post := fun s s' _ h => by sig_post [$ls,*, abi, argRegs]; exact h
      pub := by sig_implies_pub [$ls,*, abi, argRegs, argPub]
      sat := by sig_implies_sat [$ls,*, abi, argRegs, stackBelow] [modeSat] using modeSat }
    (fun _ _ h => h) ⟨modeSatC, ?_⟩
  have hl : s1234.length = 512 := by rw [Impl.Cast5.s1234, table_length]
  have held := ecbSatMem_held
  rw [ecbConsts_eq]
  generalize s1234 = W at hl held ⊢
  generalize e : modeSatC = s
  sig_pre [$ls,*, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Or.inr rfl
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 0⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       -- (A `rfl` pattern in a macro names a new variable, by hygiene.)
       rcases hr with hr | hr <;> (subst hr; exact Region.disjoint_of_sep (by decide)))))

theorem cbcEnc_implies :
    (modePC cbcEncPost).Implies (Spec.Cast5.cbcEncryptChainedContract (abi.withConsts ecbConsts) frameBytes) := by
  mode_implies [Spec.Cast5.cbcEncryptChainedContract, Spec.Cast5.cbcChainedSig]

theorem cbcDec_implies :
    (modePC cbcDecPost).Implies (Spec.Cast5.cbcDecryptChainedContract (abi.withConsts ecbConsts) frameBytes) := by
  mode_implies [Spec.Cast5.cbcDecryptChainedContract, Spec.Cast5.cbcChainedSig]

theorem ofb_implies : (modePC ofbPost).Implies (Spec.Cast5.ofbContract (abi.withConsts ecbConsts) frameBytes) := by
  mode_implies [Spec.Cast5.ofbContract, Spec.Cast5.ofbSig, Spec.Cast5.ofbPre]

theorem cfbEnc_implies :
    (modePC cfbEncPost).Implies (Spec.Cast5.cfbEncryptContract (abi.withConsts ecbConsts) frameBytes) := by
  mode_implies [Spec.Cast5.cfbEncryptContract, Spec.Cast5.cfbSig, Spec.Cast5.cfbPre]

theorem cfbDec_implies :
    (modePC cfbDecPost).Implies (Spec.Cast5.cfbDecryptContract (abi.withConsts ecbConsts) frameBytes) := by
  mode_implies [Spec.Cast5.cfbDecryptContract, Spec.Cast5.cfbSig, Spec.Cast5.cfbPre]

/-! ## Verified -/

theorem cbcEncryptChained_verified : Verified target cbcEncryptChained
    (Spec.Cast5.cbcEncryptChainedContract (abi.withConsts ecbConsts) frameBytes) :=
  Verified.of_correct cbcEncryptChained_correct (cbcEncryptChained_constantTime _) cbcEnc_implies

theorem cbcDecryptChained_verified : Verified target cbcDecryptChained
    (Spec.Cast5.cbcDecryptChainedContract (abi.withConsts ecbConsts) frameBytes) :=
  Verified.of_correct cbcDecryptChained_correct (cbcDecryptChained_constantTime _) cbcDec_implies

theorem ofb_verified : Verified target ofb (Spec.Cast5.ofbContract (abi.withConsts ecbConsts) frameBytes) :=
  Verified.of_correct ofb_correct (ofb_constantTime _) ofb_implies

theorem cfbEncrypt_verified : Verified target cfbEncrypt
    (Spec.Cast5.cfbEncryptContract (abi.withConsts ecbConsts) frameBytes) :=
  Verified.of_correct cfbEncrypt_correct (cfbEncrypt_constantTime _) cfbEnc_implies

theorem cfbDecrypt_verified : Verified target cfbDecrypt
    (Spec.Cast5.cfbDecryptContract (abi.withConsts ecbConsts) frameBytes) :=
  Verified.of_correct cfbDecrypt_correct (cfbDecrypt_constantTime _) cfbDec_implies

end VG.Proof.Cast5.RISCV64.Modes
