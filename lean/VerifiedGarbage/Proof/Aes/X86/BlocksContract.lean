import VerifiedGarbage.Proof.Aes.X86.Common
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Spec.Aes.Contract

/-!
# AES on whole blocks on x86 (32-bit): the contract

The per-target contract both implementations of `vg_aes_encrypt_blocks` and
`vg_aes_decrypt_blocks` on x86 are proven against (`blocksX86`), and its
precondition by name (`BPre`).
-/

namespace VG.Proof.Aes

open _root_.VG.X86 in
/-- X86 (32-bit) contract for `vg_aes_encrypt_blocks(schedule: *const [u8; 240],
rounds: usize, data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])` (and
`vg_aes_decrypt_blocks`, with `f` the inverse cipher), whose arguments are on
the stack: replaces each of the `n` blocks at `data` with `f rounds w` of it,
for the key schedule `w`.

The code may read `schedule` (240 bytes) and the arguments (20 bytes above
the return address), and read and write `data` (`16 n` bytes) and `scratch`
(2048 bytes, whose contents on exit are unspecified). The writable buffers
may not overlap each other, `schedule`, the arguments or the return address;
nothing may wrap around the end of the (32-bit) address space. `rounds` is
10, 12 or 14. `esp` and the arguments are public; the key schedule and the
data are secret. -/
def blocksX86 (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 240⟩
    let data : Region := ⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 2048⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 * (arg s 3).toNat ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 2048 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
    ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)
  post s s' :=
    Spec.Aes.statesAt s'.mem ((arg s 2).setWidth 64) (arg s 3).toNat =
      (Spec.Aes.statesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat).map
        (f (arg s 1).toNat (Spec.Aes.bytesAt s.mem ((arg s 0).setWidth 64) (16 * ((arg s 1).toNat + 1))))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

end VG.Proof.Aes

namespace VG.Proof.Aes.X86

open VG VG.X86

section
variable (s : State)

abbrev bSchP : BitVec 32 := arg s 0
abbrev bRounds : Nat := (arg s 1).toNat
abbrev bDatP : BitVec 32 := arg s 2
abbrev bN : Nat := (arg s 3).toNat
abbrev bScrP : BitVec 32 := arg s 4
abbrev bSchR : Region := reg32 (bSchP s) 240
abbrev bDatR : Region := reg32 (bDatP s) (16 * bN s)
abbrev bScrR : Region := reg32 (bScrP s) 2048
abbrev bArgR : Region := ⟨argAddr s 0, 20⟩
abbrev bRetR : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩

end

/-- `blocksX86.pre`, by name. -/
structure BPre (s : State) : Prop where
  rd : s.rd = [bSchR s, bArgR s]
  wr : s.wr = [bDatR s, bScrR s]
  dSD : (bSchR s).Disjoint (bDatR s)
  dSB : (bSchR s).Disjoint (bScrR s)
  dDB : (bDatR s).Disjoint (bScrR s)
  aD : (bArgR s).Disjoint (bDatR s)
  aB : (bArgR s).Disjoint (bScrR s)
  rD : (bRetR s).Disjoint (bDatR s)
  rB : (bRetR s).Disjoint (bScrR s)
  fS : (bSchP s).toNat + 240 ≤ 2 ^ 32
  fD : (bDatP s).toNat + 16 * bN s ≤ 2 ^ 32
  fB : (bScrP s).toNat + 2048 ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  rounds : bRounds s = 10 ∨ bRounds s = 12 ∨ bRounds s = 14

theorem BPre.of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State}
    (h : (Proof.Aes.blocksX86 f).pre s) : BPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-! ## Where constant time starts -/

/-- The taint analysis starts with `esp` public, and the words holding
`data` and `scratch` known to be the base addresses of the writable regions. -/
def blocksτ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 2048], argLen := 24,
    argBases := [(12, 0), (20, 1)] }

theorem blocks_wf₀ {s : State} (hp : BPre s) : VG.X86.Taint.Wf blocksτ₀ s := by
  have hD := hp.fD; have hB := hp.fB; have hs := hp.fSp
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [blocksτ₀]; omega, ?_⟩, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.dDB, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [toNat_setWidth32] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.rD hp.aD
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.rB hp.aB
  · intro p hp'
    simp only [blocksτ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem blocks_agree₀ {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₁ s₂ : State}
    (h₁ : (Proof.Aes.blocksX86 f).pre s₁) (h₂ : (Proof.Aes.blocksX86 f).pre s₂)
    (hpub : (Proof.Aes.blocksX86 f).pub s₁ s₂) : VG.X86.Taint.Agree blocksτ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := BPre.of h₁; have hp₂ := BPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, blocks_wf₀ hp₁, blocks_wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [blocksτ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [bDatR, bScrR, bDatP, bN, bScrP, ha 2 (by omega), ha 3 (by omega), ha 4 (by omega)]
  · simp only [blocksτ₀] at hk
    rw [show VG.X86.Taint.depth blocksτ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 24) hp₁.fSp h4 hk, VG.X86.Taint.argByte_eq (n := 24) hp₂.fSp h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

/-- Memory holding the arguments `0x1000, 10, 0x3000, 0, 0x4000` at `0x8004`. -/
def blocksSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800D then 0x30
  else if a = 0x8015 then 0x40 else 0

/-- A state satisfying the precondition (with no data). -/
def blocksSat : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := blocksSatMem
  rd := [⟨0x1000, 240⟩, ⟨0x8004, 20⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 2048⟩]

end VG.Proof.Aes.X86
