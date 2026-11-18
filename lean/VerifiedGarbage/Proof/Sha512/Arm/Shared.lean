module

public import VerifiedGarbage.Proof.Sha512.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Sha512.Arm.Compress
public import VerifiedGarbage.Proof.Sha512.Arm.Stream.Finalize
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Init
public import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.Proof.Sha512.Scratch
public import VerifiedGarbage.Proof.Framework.Arm.StackScratch
public import VerifiedGarbage.Proof.Sha512.Digest
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.Contract
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Impl.MdStream.Arm
public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.Impl.Sha512.Arm.Stream
public import VerifiedGarbage.Proof.MdStream.Arm.Common
public import VerifiedGarbage.Spec.Sha512
public import VerifiedGarbage.Proof.MdStream.Arm.Finalize
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha512.Arm.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MdStream.Arm.Finalize
meta import VerifiedGarbage.Proof.Sha512.Arm.Stream.Finalize
meta import VerifiedGarbage.Proof.Sha512.Digest
meta import VerifiedGarbage.Proof.MdStream.Arm.Words
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Sha512.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Sha256.Stream

/-! ### `Sha512.Arm.Stream.Digest`, which only this module used -/

section

/-!
# Streaming SHA-384, SHA-512/256 and SHA-512/224 on ARMv7: `finalize`

`finalizeDigest` is the generic `finalize` (`Impl/MdStream/Arm.lean`) with a
digest of the first 48, 32 or 28 bytes of the final hash value
(`params384`, `params512_256`, `params512_224`), so it is verified by the
generic proof of a `finalize` writing a prefix of the final hash value
(`Finalize.verifiedD`), given what writing that prefix does (`ShapeD`), and
constant time by the taint analysis of its code.
-/

@[expose] public section

namespace VG.Proof.Sha512.Arm.Stream.Finalize

open VG VG.Arm VG.Proof.MdStream VG.Proof.MdStream.Arm
open VG.Impl.Sha512.Arm.Stream (outW outHi params384 params512_256 params512_224 finalizeDigest)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_frame)
open VG.Proof.Sha512.Arm (readW_hi)
open VG.Spec.Sha512 (stateAt wordBytes)

/-- The first `n` words of the hash value, big-endian, are the first `8 n`
bytes of its output. -/
theorem take_flatMap_wordBytes (l : List Spec.Sha512.Word) (n : Nat) :
    (l.flatMap wordBytes).take (8 * n) = (l.take n).flatMap wordBytes := by
  induction l generalizing n with
  | nil => simp
  | cons w l ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [List.flatMap_cons, List.take_succ_cons, List.flatMap_cons, List.take_append,
        List.take_of_length_le (by simp [wordBytes]; omega_using []), show 8 * (n + 1) - (wordBytes w).length = 8 * n by
          simp [wordBytes]; omega_using [], ih]

/-- The first `n` words of the digest, to `r6`, where `8 n` bytes may be written. -/
theorem out_take {n : Nat} (hn : n ≤ 8) (s : State) (f₀ : (s.gpr .r0).toNat + 64 ≤ 2 ^ 32)
    (f₆ : (s.gpr .r6).toNat + 8 * n ≤ 2 ^ 32) (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0)) 64)
    (hout : InRegions s.wr (State.addr (s.gpr .r6)) (8 * n))
    (hd : Region.Disjoint ⟨State.addr (s.gpr .r0), 64⟩ ⟨State.addr (s.gpr .r6), 8 * n⟩) :
    WP isa (.block ((List.range n).flatMap outW)) s fun s' => (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (State.addr (s.gpr .r6))
        ((Proof.Sha512.md.digest (Proof.Sha512.md.stateAt s.mem (State.addr (s.gpr .r0)))).take (8 * n)) := by
  rw [← List.append_nil ((List.range n).flatMap outW)]
  refine out_ok (W := 8 * n) (by omega_using [hn]) f₀ f₆ hd n (Nat.le_refl _) [] s _ rfl rfl hin hout
    fun s' g rd wr sp m => WP.block_nil ⟨g, rd, wr, sp, ?_⟩
  rw [m]
  exact congrArg _ (take_flatMap_wordBytes _ n).symm

/-- `(List.range 3).flatMap outW ++ outHi 3` writes the first 28 bytes of the digest. -/
theorem out224_ok (s : State) (f₀ : (s.gpr .r0).toNat + 64 ≤ 2 ^ 32) (f₆ : (s.gpr .r6).toNat + 28 ≤ 2 ^ 32)
    (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0)) 64)
    (hout : InRegions s.wr (State.addr (s.gpr .r6)) 28)
    (hd : Region.Disjoint ⟨State.addr (s.gpr .r0), 64⟩ ⟨State.addr (s.gpr .r6), 28⟩) :
    WP isa (.block ((List.range 3).flatMap outW ++ outHi 3)) s fun s' =>
      (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (State.addr (s.gpr .r6))
        ((Proof.Sha512.md.digest (Proof.Sha512.md.stateAt s.mem (State.addr (s.gpr .r0)))).take 28) := by
  refine out_ok (W := 28) (by decide) f₀ f₆ hd 3 (by decide) _ s _ rfl rfl hin hout
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  have hl : (((stateAt s.mem (State.addr (s.gpr .r0))).toList.take 3).flatMap wordBytes).length = 24 :=
    flat_length _ 3 (by decide)
  -- The high half of word 3 is not yet overwritten.
  have hread : s₁.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 28) 32 =
      s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 28) 32 := by
    rw [m₁]
    refine (writeBytes_frame _ _ _ (R := ⟨State.addr (s.gpr .r6), 28⟩) ?_).readW
      (r := ⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 28, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    · rw [hl]; simpa using Offset.contains_base (State.addr (s.gpr .r6)) (d := 0) (n := 24) (k := 28)
        (by decide) (by decide)
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact hd.sub_left (Offset.sub_base _ (by decide))
  simp only [outHi]
  refine wp_ldr (a := State.addr (s.gpr .r0) + BitVec.ofNat 64 28) (by decide)
    (by rw [g₁ _ (by decide) (by decide), addr_add (by omega_using [f₀])])
    (by rw [rd₁, wr₁]; exact InRegions.offset hin (by decide) (by decide)) fun s₂ u₂ => wp_rev fun s₃ u₃ => ?_
  refine wp_str (a := State.addr (s.gpr .r6) + BitVec.ofNat 64 24) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide) (by decide), addr_add (by omega_using [f₆])])
    (by rw [u₃.wr, u₂.wr, wr₁]; exact InRegions.offset hout (by decide) (by decide)) fun s₄ g₄ =>
      WP.block_nil ⟨fun r h9 h10 => by rw [g₄.gpr, u₃.other r h10, u₂.other r h10, g₁ r h9 h10],
        by rw [g₄.rd, u₃.rd, u₂.rd, rd₁], by rw [g₄.wr, u₃.wr, u₂.wr, wr₁], by rw [g₄.sp, u₃.sp, u₂.sp, sp₁], ?_⟩
  have e24 : ((Proof.Sha512.md.digest (Proof.Sha512.md.stateAt s.mem (State.addr (s.gpr .r0)))).take 28) =
      ((stateAt s.mem (State.addr (s.gpr .r0))).toList.take 3).flatMap wordBytes ++
        Spec.Sha256.wordBytes (s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 28) 32) := by
    rw [Proof.Sha512.digest_take28, ← Proof.Sha512.digest_take _ _ (n := 3) (by decide),
      show Proof.Sha512.md.digest (Proof.Sha512.md.stateAt s.mem (State.addr (s.gpr .r0))) =
        (stateAt s.mem (State.addr (s.gpr .r0))).toList.flatMap wordBytes from rfl,
      take_flatMap_wordBytes]
    rfl
  rw [g₄.mem, u₃.mem, u₃.gpr, u₂.gpr, u₂.mem, hread, writeW_rev, m₁, e24, ← hl,
    writeBytes_append _ _ _ _ (by rw [hl]; simp [Spec.Sha256.wordBytes])]

theorem shape384 : ShapeD (P := params384) Proof.Sha512.md 48 where
  le := by decide
  len := shape.len
  out s f₀ f₆ hin hout hd := out_take (n := 6) (by decide) s f₀ f₆ hin hout hd

theorem shape512_256 : ShapeD (P := params512_256) Proof.Sha512.md 32 where
  le := by decide
  len := shape.len
  out s f₀ f₆ hin hout hd := out_take (n := 4) (by decide) s f₀ f₆ hin hout hd

theorem shape512_224 : ShapeD (P := params512_224) Proof.Sha512.md 28 where
  le := by decide
  len := shape.len
  out s f₀ f₆ hin hout hd := out224_ok s f₀ f₆ hin hout hd

theorem finalize384_verified :
    Verified Arm.target (finalizeDigest params384) (MdStream.Arm.finKD (P := params384) Proof.Sha512.md 48) :=
  MdStream.Arm.Finalize.verifiedD (P := params384) (name := "vg_sha512_compress")
    ⟨dims.1, dims.2, dims.3, dims.4, dims.5, dims.6⟩ shape384 (callee.withOut ((List.range 6).flatMap outW))
    (VG.Taint.constantTime (A := taint) (MdStream.Arm.Finalize.τ₀D params384 48)
      (fun _ _ h₁ h₂ hp => MdStream.Arm.Finalize.agree₀D h₁ h₂ hp) (by taint_decide))

theorem finalize512_256_verified :
    Verified Arm.target (finalizeDigest params512_256)
      (MdStream.Arm.finKD (P := params512_256) Proof.Sha512.md 32) :=
  MdStream.Arm.Finalize.verifiedD (P := params512_256) (name := "vg_sha512_compress")
    ⟨dims.1, dims.2, dims.3, dims.4, dims.5, dims.6⟩ shape512_256 (callee.withOut ((List.range 4).flatMap outW))
    (VG.Taint.constantTime (A := taint) (MdStream.Arm.Finalize.τ₀D params512_256 32)
      (fun _ _ h₁ h₂ hp => MdStream.Arm.Finalize.agree₀D h₁ h₂ hp) (by taint_decide))

theorem finalize512_224_verified :
    Verified Arm.target (finalizeDigest params512_224)
      (MdStream.Arm.finKD (P := params512_224) Proof.Sha512.md 28) :=
  MdStream.Arm.Finalize.verifiedD (P := params512_224) (name := "vg_sha512_compress")
    ⟨dims.1, dims.2, dims.3, dims.4, dims.5, dims.6⟩ shape512_224
    (callee.withOut ((List.range 3).flatMap outW ++ outHi 3))
    (VG.Taint.constantTime (A := taint) (MdStream.Arm.Finalize.τ₀D params512_224 28)
      (fun _ _ h₁ h₂ hp => MdStream.Arm.Finalize.agree₀D h₁ h₂ hp) (by taint_decide))

/-- A state satisfying the precondition of `finalizeDigest` with a `D`-byte
digest. -/
abbrev satD (D : Nat) : State := MdStream.Arm.Finalize.satD params D

end VG.Proof.Sha512.Arm.Stream.Finalize

end

end

/-!
# Sha512 on Arm: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha512/Arm/Compress.lean`); these theorems move them to the shared
contracts of `Spec/Sha512/Contract.lean`, which the artifacts are emitted
with.

The shared contracts give the functions more scratch than these ones use (1328
bytes for `compress`, 1376 for `update` and `finalize`, sized for the x86-64
AVX2 compression function): the per-target contracts are first widened to
that scratch (`Verified.widen`, the same code running with the same trace and
result), then moved to the shared ones.

`update` and `finalize` keep their working space in a frame of their own:
they are `updateScratch` and `finalizeScratch` (the shared contracts with
the working space as an argument, which HMAC's, PBKDF2's and Ed25519's code
calls) run in a frame that allocates it (`Verified.stackScratch`).
-/

@[expose] public section

namespace VG.Proof.Sha512.Arm.Shared

open _root_.VG.Arm

/-- `updateArm` with 1376 bytes of scratch. -/
def updateWide : Contract Arm.isa :=
  { Proof.Sha512.updateArm with
    pre := fun s =>
      let state : Region := ⟨State.addr (s.gpr .r0), 192⟩
      let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
      let scratch : Region := ⟨State.addr (stackArg s 2), 1376⟩
      let args : Region := ⟨stackArgAddr s 0, 12⟩
      s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint scratch ∧
      (s.gpr .r0).toNat + 192 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
      (stackArg s 2).toNat + 1376 ≤ 2 ^ 32 ∧ s.sp.toNat + 12 ≤ 2 ^ 32 }

/-- `finalizeArm` with 1376 bytes of scratch. -/
def finalizeWide : Contract Arm.isa :=
  { Proof.Sha512.finalizeArm with
    pre := fun s =>
      let state : Region := ⟨State.addr (s.gpr .r0), 192⟩
      let out : Region := ⟨State.addr (stackArg s 0), 64⟩
      let scratch : Region := ⟨State.addr (stackArg s 1), 1376⟩
      let args : Region := ⟨stackArgAddr s 0, 8⟩
      s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      (s.gpr .r0).toNat + 192 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 64 ≤ 2 ^ 32 ∧
      (stackArg s 1).toNat + 1376 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32 }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub272 (a : Addr) : Region.Sub ⟨a, 272⟩ ⟨a, 1376⟩ := Region.sub_prefix (by decide)
theorem le272 {x : Nat} (h : x + 1376 ≤ 2 ^ 32) : x + 272 ≤ 2 ^ 32 := by omega_using [h]

/-- Rewrites the per-target contracts at a narrowed state (`stackArg` does
not unfold cheaply). -/
macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| plain_simp_names simp only [Proof.Sha512.compressArm, Proof.Sha512.updateArm, Proof.Sha512.finalizeArm,
                     Proof.Sha512.countArm, updateWide, finalizeWide, VG.Arm.stackArg_withRegions,
                     VG.Arm.stackArgAddr_withRegions, State.withRegions_gpr, State.withRegions_sp, State.withRegions_mem,
                     State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem updateWide_verified (hsat : ∃ s, updateWide.pre s) :
    Verified Arm.target Impl.Sha512.Arm.Stream.update updateWide :=
  Verified.widen Proof.Sha512.Arm.Stream.Update.update_verified
    (fun s => [⟨State.addr (s.gpr .r0), 192⟩, ⟨State.addr (stackArg s 2), 272⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃.sub_right (sub272 _), h₄, h₅.sub_right (sub272 _), h₆,
        h₇.sub_right (sub272 _), h₈, h₉, le272 h₁₀, h₁₁⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

theorem finalizeWide_verified (hsat : ∃ s, finalizeWide.pre s) :
    Verified Arm.target Impl.Sha512.Arm.Stream.finalize finalizeWide :=
  Verified.widen Proof.Sha512.Arm.Stream.Finalize.finalize_verified
    (fun s => [⟨State.addr (s.gpr .r0), 192⟩, ⟨State.addr (stackArg s 0), 64⟩,
      ⟨State.addr (stackArg s 1), 272⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃, h₄.sub_right (sub272 _), h₅.sub_right (sub272 _), h₆, h₇,
        h₈.sub_right (sub272 _), h₉, h₁₀, le272 h₁₁, h₁₂⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State := { Proof.Sha512.Arm.Stream.Update.sat with wr := [⟨0x1000, 192⟩, ⟨0, 1376⟩] }

/-- A state satisfying `finalizeWide.pre`. -/
def finalizeSat : State :=
  { Proof.Sha512.Arm.Stream.Finalize.sat with wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩, ⟨0x3000, 1376⟩] }

theorem init (iv : Spec.Sha512.HashValue) :
    Verified Arm.target (Impl.Sha512.Arm.Stream.init iv) (Spec.Sha512.initContract Arm.abi iv) :=
  (Proof.Sha512.Arm.Stream.init_verified iv).of_implies (by
    contract_implies [Spec.Sha512.initContract, Spec.Sha512.initSig, Proof.Sha512.initArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha512.Arm.Stream.initSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha512.Arm.Stream.initSat)

theorem updateWide_implies : updateWide.Implies (Proof.Sha512.updateScratchContract Arm.abi) := by
  sig_implies [Proof.Sha512.updateScratchContract, Proof.Sha512.updateScratchSig, updateWide, Proof.Sha512.updateArm,
    Proof.Sha512.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [updateSat, Proof.Sha512.Arm.Stream.Update.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
    Mem.read] using updateSat

theorem updateScratch :
    Verified Arm.target Impl.Sha512.Arm.Stream.update (Proof.Sha512.updateScratchContract Arm.abi) :=
  (updateWide_verified updateWide_implies.sat_left).of_implies updateWide_implies

theorem finalizeWide_implies : finalizeWide.Implies (Proof.Sha512.finalizeScratchContract Arm.abi) := by
  contract_implies [Proof.Sha512.finalizeScratchContract, Proof.Sha512.finalizeScratchSig, finalizeWide,
    Proof.Sha512.finalizeArm, Proof.Sha512.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr]
    [finalizeSat, Proof.Sha512.Arm.Stream.Finalize.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
    Mem.read] using finalizeSat

theorem finalizeScratch :
    Verified Arm.target Impl.Sha512.Arm.Stream.finalize (Proof.Sha512.finalizeScratchContract Arm.abi) :=
  (finalizeWide_verified finalizeWide_implies.sat_left).of_implies finalizeWide_implies

/-- A state satisfying `update`'s precondition. -/
def updateFrameSat : State :=
  { Proof.Sha512.Arm.Stream.Update.sat with rd := [⟨0, 0⟩, ⟨0x4000, 8⟩], wr := [⟨0x1000, 192⟩] }

theorem update : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 1392 2 Impl.Sha512.Arm.Stream.update)
    (Spec.Sha512.updateContract Arm.abi 1392) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 0) (bytes := 1392) (m := 2)
    updateScratch (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.updatePost_local _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha512.updatePostOut_local _ vs mm m₁ m₂ r hl hb h)
    (by implies_sat [Spec.Sha512.updateContract, Spec.Sha512.updateSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [updateFrameSat, Proof.Sha512.Arm.Stream.Update.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using updateFrameSat)

/-- A state satisfying `finalize`'s precondition. -/
def finalizeFrameSat : State :=
  { MdStream.Arm.Finalize.satBase with rd := [⟨0x5000, 4⟩], wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩] }

theorem finalize : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 1392 1 Impl.Sha512.Arm.Stream.finalize)
    (Spec.Sha512.finalizeContract Arm.abi 1392) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 0) (bytes := 1392) (m := 1)
    finalizeScratch (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.finalizePost_local _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha512.finalizePostOut_local _ vs mm m₁ m₂ r hl hb h)
    (by implies_sat [Spec.Sha512.finalizeContract, Spec.Sha512.finalizeSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finalizeFrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using finalizeFrameSat)

/-! ## The truncated digests

`finalizeDigest` (SHA-384's, SHA-512/256's and SHA-512/224's `finalize`) is
verified against `finKD`; widened to the shared scratch, for the algorithm's
initial hash value, and with its working space in a frame of its own, it is
`Spec.Sha512.finalizeDigestContract`. -/

/-- `finalizeWide` for the `D`-byte `digest` of the messages hashed from `iv`. -/
def finalizeDigestWide (iv : Spec.Sha512.HashValue) (D : Nat) (digest : List Byte → List Byte) :
    Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 192⟩
    let out : Region := ⟨State.addr (stackArg s 0), D⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 1376⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 192 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + D ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 1376 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ m, Spec.Sha512.Repr iv s.mem (State.addr (s.gpr .r0)) m → m.length < 2 ^ 64 →
    Proof.Sha512.countArm s = BitVec.ofNat 64 m.length →
    Spec.Sha512.bytesAt s'.mem (State.addr (stackArg s 0)) D = digest m
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-- Rewrites `finKD` and `finalizeDigestWide` at a narrowed state. -/
macro "narrowD" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| plain_simp_names simp only [MdStream.Arm.finKD, Proof.Sha512.countArm, finalizeDigestWide, MdStream.Arm.count,
                     VG.Arm.stackArg_withRegions, VG.Arm.stackArgAddr_withRegions, State.withRegions_gpr, State.withRegions_sp,
                     State.withRegions_mem, State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem finalizeDigestWide_verified {code : Prog Arm.isa} {o : List Instr} {D : Nat}
    {iv : Spec.Sha512.HashValue} {digest : List Byte → List Byte}
    (hv : Verified Arm.target code
      (MdStream.Arm.finKD (P := { Impl.Sha512.Arm.Stream.params with out := o }) Proof.Sha512.md D))
    (hdg : ∀ m, (Proof.Sha512.md.hash iv m).take D = digest m)
    (hsat : ∃ s, (finalizeDigestWide iv D digest).pre s) :
    Verified Arm.target code (finalizeDigestWide iv D digest) :=
  Verified.widen hv
    (fun s => [⟨State.addr (s.gpr .r0), 192⟩, ⟨State.addr (stackArg s 0), D⟩,
      ⟨State.addr (stackArg s 1), 272⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ := h
      narrowD
      exact ⟨h₁, rfl, h₃, h₄.sub_right (sub272 _), h₅.sub_right (sub272 _), h₆, h₇,
        h₈.sub_right (sub272 _), h₉, h₁₀, le272 h₁₁, h₁₂⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons ⟨rfl, Nat.le_refl _⟩ (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => by
      narrowD at h ⊢
      intro m hr hl hc
      exact (h iv m hr hl hc).trans (hdg m))
    (fun _ _ _ _ h => by narrowD; exact h) hsat

/-- A state satisfying `finalizeDigestWide.pre`. -/
def finalizeDigestSat (D : Nat) : State :=
  { Proof.Sha512.Arm.Stream.Finalize.satD D with wr := [⟨0x1000, 192⟩, ⟨0x2000, D⟩, ⟨0x3000, 1376⟩] }

theorem finalizeDigestWide_implies48 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 48 digest).Implies (finalizeDigestScratchContract Arm.abi iv 48 digest 0) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, Proof.Sha512.countArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finalizeDigestSat, Proof.Sha512.Arm.Stream.Finalize.satD, MdStream.Arm.Finalize.satD,
      MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finalizeDigestSat 48

theorem finalizeDigestWide_implies32 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 32 digest).Implies (finalizeDigestScratchContract Arm.abi iv 32 digest 0) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, Proof.Sha512.countArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finalizeDigestSat, Proof.Sha512.Arm.Stream.Finalize.satD, MdStream.Arm.Finalize.satD,
      MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finalizeDigestSat 32

theorem finalizeDigestWide_implies28 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 28 digest).Implies (finalizeDigestScratchContract Arm.abi iv 28 digest 0) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, Proof.Sha512.countArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finalizeDigestSat, Proof.Sha512.Arm.Stream.Finalize.satD, MdStream.Arm.Finalize.satD,
      MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finalizeDigestSat 28

theorem finalizeDigestScratch {code : Prog Arm.isa} {o : List Instr} {D : Nat}
    {iv : Spec.Sha512.HashValue} {digest : List Byte → List Byte} (hD : D = 48 ∨ D = 32 ∨ D = 28)
    (hv : Verified Arm.target code
      (MdStream.Arm.finKD (P := { Impl.Sha512.Arm.Stream.params with out := o }) Proof.Sha512.md D))
    (hdg : ∀ m, (Proof.Sha512.md.hash iv m).take D = digest m) :
    Verified Arm.target code (finalizeDigestScratchContract Arm.abi iv D digest 0) := by
  have hi : (finalizeDigestWide iv D digest).Implies (finalizeDigestScratchContract Arm.abi iv D digest 0) := by
    rcases hD with rfl | rfl | rfl
    exacts [finalizeDigestWide_implies48 iv digest, finalizeDigestWide_implies32 iv digest,
      finalizeDigestWide_implies28 iv digest]
  exact (finalizeDigestWide_verified hv hdg hi.sat_left).of_implies hi

/-- A state satisfying `Spec.Sha512.finalizeDigestContract`'s precondition. -/
def finalizeDigestFrameSat (D : Nat) : State :=
  { MdStream.Arm.Finalize.satBase with rd := [⟨0x5000, 4⟩], wr := [⟨0x1000, 192⟩, ⟨0x2000, D⟩] }

theorem finalizeDigestStack48 {code : Prog Arm.isa} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte}
    (hv : Verified Arm.target code (finalizeDigestScratchContract Arm.abi iv 48 digest 0)) :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 1392 1 code)
      (Spec.Sha512.finalizeDigestContract Arm.abi iv 48 digest 1392) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 0) (bytes := 1392) (m := 1)
    hv (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.finalizeDigestPost_local _ _ _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha512.finalizeDigestPostOut_local _ _ _ _ vs mm m₁ m₂ r hl hb h)
    (by implies_sat [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finalizeDigestFrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using finalizeDigestFrameSat 48)

theorem finalizeDigestStack32 {code : Prog Arm.isa} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte}
    (hv : Verified Arm.target code (finalizeDigestScratchContract Arm.abi iv 32 digest 0)) :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 1392 1 code)
      (Spec.Sha512.finalizeDigestContract Arm.abi iv 32 digest 1392) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 0) (bytes := 1392) (m := 1)
    hv (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.finalizeDigestPost_local _ _ _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha512.finalizeDigestPostOut_local _ _ _ _ vs mm m₁ m₂ r hl hb h)
    (by implies_sat [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finalizeDigestFrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using finalizeDigestFrameSat 32)

theorem finalizeDigestStack28 {code : Prog Arm.isa} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte}
    (hv : Verified Arm.target code (finalizeDigestScratchContract Arm.abi iv 28 digest 0)) :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 1392 1 code)
      (Spec.Sha512.finalizeDigestContract Arm.abi iv 28 digest 1392) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 0) (bytes := 1392) (m := 1)
    hv (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.finalizeDigestPost_local _ _ _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha512.finalizeDigestPostOut_local _ _ _ _ vs mm m₁ m₂ r hl hb h)
    (by implies_sat [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finalizeDigestFrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using finalizeDigestFrameSat 28)

theorem finalize384 : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 1392 1
      (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params384))
    (Spec.Sha512.finalizeDigestContract Arm.abi Spec.Sha512.H0_384 48 Spec.Sha512.sha384 1392) :=
  finalizeDigestStack48 (finalizeDigestScratch (.inl rfl) Proof.Sha512.Arm.Stream.Finalize.finalize384_verified (fun _ => rfl))

theorem finalize512_256 : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 1392 1
      (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params512_256))
    (Spec.Sha512.finalizeDigestContract Arm.abi Spec.Sha512.H0_512_256 32 Spec.Sha512.sha512_256 1392) :=
  finalizeDigestStack32 (finalizeDigestScratch (.inr (.inl rfl)) Proof.Sha512.Arm.Stream.Finalize.finalize512_256_verified (fun _ => rfl))

theorem finalize512_224 : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 1392 1
      (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params512_224))
    (Spec.Sha512.finalizeDigestContract Arm.abi Spec.Sha512.H0_512_224 28 Spec.Sha512.sha512_224 1392) :=
  finalizeDigestStack28 (finalizeDigestScratch (.inr (.inr rfl)) Proof.Sha512.Arm.Stream.Finalize.finalize512_224_verified (fun _ => rfl))

end VG.Proof.Sha512.Arm.Shared
