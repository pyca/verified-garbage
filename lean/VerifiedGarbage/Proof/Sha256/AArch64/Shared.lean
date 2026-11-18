module

public import VerifiedGarbage.Proof.Sha256.Contract
public import VerifiedGarbage.Proof.Sha256.AArch64.Compress
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
public import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Digest
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Sha256.Scratch
public import VerifiedGarbage.Proof.Sha256.Digest
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Sha256.AArch64.Variant
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.Impl.Sha256.AArch64.Stream
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MdStream.AArch64.OneShot
public import VerifiedGarbage.Proof.Sha256.Md

/-! ### `Sha256.AArch64.OneShot`, which the modules that import this one used -/

section

/-!
# The one-shot SHA-256 and SHA-224 digests on AArch64, against their shared contracts

`Compress.oneShot_verified` proves each one-shot digest against
`OneShot.oneK`; `implies` moves it to `Spec.Sha256.digestContract`, whose
`stack` is the digest's frame.
-/

@[expose] public section

namespace VG.Proof.Sha256.AArch64.OneShot

open VG.AArch64 VG.Proof.MdStream.AArch64

/-- The stack the one-shot digests use: their frame. -/
abbrev stack : Nat := Impl.MdStream.AArch64.OneShot.frameBytes Impl.Sha256.AArch64.Stream.params

theorem implies {o : List Instr} {iv : Spec.Sha256.HashValue} {D : Nat} {digest : List Byte → List Byte}
    (hD : D ≤ 64) (hdg : ∀ m, (md.hash iv m).take D = digest m) :
    (OneShot.oneK (P := { Impl.Sha256.AArch64.Stream.params with out := o }) md iv D).Implies
      (Spec.Sha256.digestContract AArch64.abi D digest stack) := by
  refine
    { pre := fun s h => ?_
      post := fun s s' _ h => ?_
      pub := by implies_pub [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost,
        OneShot.oneK, AArch64.abi, AArch64.argRegs]
      sat := ⟨sat D, ?_⟩ }
  · sig_pre [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, AArch64.abi,
      AArch64.argRegs] at h
    obtain ⟨hsp, hrd, hwr, hdo, hfd, hfo, -, -⟩ := h
    exact pre_out ⟨hrd, hwr, hdo, hsp, hfd, hfo⟩
  · sig_post [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, AArch64.abi,
      AArch64.argRegs]
    rw [← hdg]
    exact h trivial
  · have hp := sat_pre₀ hD
    sig_pre [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, AArch64.abi,
      AArch64.argRegs]
    sig_and_intros
    all_goals first
      | exact hp.sp | rfl | exact hp.d_o | exact hp.f_d | exact hp.f_o | decide
      | exact (show 8192 + D ≤ 2 ^ 64 by omega_using [hD])

/-- SHA-256's digest is all of the final hash value. -/
theorem hash_take (m : List Byte) : (md.hash Spec.Sha256.H0 m).take 32 = Spec.Sha256.hash m := by
  rw [Proof.Sha256.hash_eq]
  exact List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.md.digest_length _))

/-- SHA-224's digest is the first 28 bytes of the final hash value. -/
theorem sha224_take (m : List Byte) : (md.hash Spec.Sha256.H0_224 m).take 28 = Spec.Sha256.sha224 m := rfl

end VG.Proof.Sha256.AArch64.OneShot

end

end

/-!
# Sha256 on AArch64: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha256/AArch64/Contract.lean`); these theorems move them to the shared
contracts of `Spec/Sha256/Contract.lean`, which the artifacts are emitted with.

`update_of` and `finalize_of` keep the working space in a frame of their
own: they are `updateScratch_of` and `finalizeScratch_of` (the scratch forms'
contracts with the 20 words of working space the code uses, its compression
function's 112 bytes and the 48 bytes of registers the streaming code saves)
run in a frame that allocates it (`Verified.stackScratch`).
-/

@[expose] public section

namespace VG.Proof.Sha256.AArch64.Shared

open _root_.VG.AArch64

theorem init :
    Verified AArch64.target Impl.Sha256.AArch64.Stream.init (Spec.Sha256.initContract AArch64.abi) :=
  Proof.Sha256.AArch64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha256.initContract, Spec.Sha256.initSig, Proof.Sha256.initAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sha256.AArch64.Stream.initSat] using Proof.Sha256.AArch64.Stream.initSat)

theorem init224 :
    Verified AArch64.target Impl.Sha256.AArch64.Stream.init224 (Spec.Sha256.init224Contract AArch64.abi) :=
  Proof.Sha256.AArch64.Stream.init224_verified.of_implies (by
    contract_implies [Spec.Sha256.init224Contract, Spec.Sha256.initSig, Proof.Sha256.initAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sha256.AArch64.Stream.initSat] using Proof.Sha256.AArch64.Stream.initSat)

theorem updateScratch_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha256.updateAArch64) :
    Verified AArch64.target code (Proof.Sha256.updateScratchContractW 20 AArch64.abi 16) :=
  hv.of_implies (by
    contract_implies [Proof.Sha256.updateScratchContractW, Proof.Sha256.updateScratchSigW,
      Proof.Sha256.updateAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Sha256.AArch64.Stream.Update.sat, MdStream.AArch64.Update.sat,
        Impl.Sha256.AArch64.Stream.params] using Proof.Sha256.AArch64.Stream.Update.sat)

theorem finalizeScratch_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha256.finalizeAArch64) :
    Verified AArch64.target code (Proof.Sha256.finalizeScratchContractW 20 AArch64.abi 16) :=
  hv.of_implies (by
    contract_implies [Proof.Sha256.finalizeScratchContractW, Proof.Sha256.finalizeScratchSigW,
      Proof.Sha256.finalizeAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Sha256.AArch64.Stream.Finalize.sat, MdStream.AArch64.Finalize.sat,
        Impl.Sha256.AArch64.Stream.params] using Proof.Sha256.AArch64.Stream.Finalize.sat)

/-- `update`: `updateScratch_of` with its working space in a frame of its own. -/
theorem update_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha256.updateAArch64) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 160 .x4 code)
      (Spec.Sha256.updateContract AArch64.abi (16 + 160)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 20) (stack := 16) (bytes := 160)
    (updateScratch_of hv) (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.Sha256.updatePostOut_local _ vs m m₁ m₂ r hl)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- `finalize`: `finalizeScratch_of` with its working space in a frame of its own. -/
theorem finalize_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha256.finalizeAArch64) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 160 .x3 code)
      (Spec.Sha256.finalizeContract AArch64.abi (16 + 160)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 20) (stack := 16) (bytes := 160)
    (finalizeScratch_of hv) (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.Sha256.finalizePostOut_local _ vs m m₁ m₂ r hl)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-! ## SHA-224's digest

SHA-224's `finalize` (`Compress.finalize224`) is verified against `finKD`;
for SHA-224's initial hash value (`finalize224K`), and with its working space
in a frame of its own, it is `Spec.Sha256.finalize224Contract`. -/

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩

theorem sub160 (a : Addr) : Region.Sub ⟨a, 160⟩ ⟨a, 160⟩ := Region.sub_prefix (Nat.le_refl _)

/-- `finKD` for SHA-224's digest of the messages hashed from its initial hash
value. -/
def finalize224K : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 96⟩
    let out : Region := ⟨s.gpr .x2, 28⟩
    let scratch : Region := ⟨s.gpr .x3, 160⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ m, Spec.Sha256.ReprFrom Spec.Sha256.H0_224 s.mem (s.gpr .x0) m →
    s.gpr .x1 = BitVec.ofNat 64 m.length → Spec.Sha256.bytesAt s'.mem (s.gpr .x2) 28 = Spec.Sha256.sha224 m
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

theorem finalize224K_of {code : Prog isa}
    (hv : Verified AArch64.target code (MdStream.AArch64.finKD (P := Impl.Sha256.AArch64.Stream.params224) md 28))
    (hsat : ∃ s, finalize224K.pre s) :
    Verified AArch64.target code finalize224K :=
  Verified.widen hv
    (fun s => [⟨s.gpr .x0, 96⟩, ⟨s.gpr .x2, 28⟩, ⟨s.gpr .x3, 160⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ =>
      ⟨h₁, rfl, h₃, h₄.sub_right (sub160 _), h₅.sub_right (sub160 _), h₆, h₇, h₈,
        h₉.sub_right (sub160 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) (.cons (pfx rfl) .nil)))
    (fun _ _ _ h m hr hc => (h _ m hr trivial hc).trans (sha224_eq m)) (fun _ _ _ _ h => h) hsat

/-- A state satisfying `finalize224K.pre`. -/
def finalize224Sat : State :=
  { Proof.Sha256.AArch64.Stream.Finalize.sat224 with wr := [⟨0x1000, 96⟩, ⟨0x2000, 28⟩, ⟨0x3000, 160⟩] }

theorem finalize224Scratch_of {code : Prog isa}
    (hv : Verified AArch64.target code (MdStream.AArch64.finKD (P := Impl.Sha256.AArch64.Stream.params224) md 28)) :
    Verified AArch64.target code (Proof.Sha256.finalize224ScratchContractW 20 AArch64.abi 16) := by
  have hi : finalize224K.Implies (Proof.Sha256.finalize224ScratchContractW 20 AArch64.abi 16) := by
    contract_implies [Proof.Sha256.finalize224ScratchContractW, Proof.Sha256.finalize224ScratchSigW,
      Spec.Sha256.finalize224Post, finalize224K, AArch64.abi, AArch64.argRegs]
      [finalize224Sat, Proof.Sha256.AArch64.Stream.Finalize.sat224, MdStream.AArch64.Finalize.satD,
        Impl.Sha256.AArch64.Stream.params] using finalize224Sat
  exact (finalize224K_of hv hi.sat_left).of_implies hi

/-- SHA-224's `finalize`: `finalize224Scratch_of` with its working space in a
frame of its own. -/
theorem finalize224_of {code : Prog isa}
    (hv : Verified AArch64.target code (MdStream.AArch64.finKD (P := Impl.Sha256.AArch64.Stream.params224) md 28)) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 160 .x3 code)
      (Spec.Sha256.finalize224Contract AArch64.abi (16 + 160)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 20) (stack := 16) (bytes := 160)
    (finalize224Scratch_of hv) (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.Sha256.finalize224PostOut_local _ vs m m₁ m₂ r hl)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sha256.AArch64.Shared
