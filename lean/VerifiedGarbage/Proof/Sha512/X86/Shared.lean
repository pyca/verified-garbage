module

public import VerifiedGarbage.Proof.Sha512.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sha512.X86.Compress
public import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
public import VerifiedGarbage.Spec.Sha512.Contract
public import VerifiedGarbage.Proof.Sha512.X86.Lit
import VerifiedGarbage.Proof.Sha512.Scratch
public import VerifiedGarbage.Proof.Framework.X86.StackScratch
public import VerifiedGarbage.Proof.Sha512.Digest
public import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Impl.MdStream.X86
public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Spec.Sha512
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Impl.Sha512.X86.Stream
public import VerifiedGarbage.Proof.MdStream.X86.Update
public import VerifiedGarbage.Proof.Sha512.Md
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.MdStream.Prefix
import VerifiedGarbage.Proof.MdStream.X86.Words
import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.MdStream.X86.Update
meta import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
meta import VerifiedGarbage.Proof.Sha512.Digest
meta import VerifiedGarbage.Proof.MdStream.Prefix
meta import VerifiedGarbage.Proof.MdStream.X86.Words
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Sha512.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Sha256.Stream

/-! ### `Sha512.X86.Stream.Digest`, which only this module used -/

section

/-!
# Streaming SHA-384, SHA-512/256 and SHA-512/224 on x86 (32-bit): `finalize`

`finalizeDigest` is the generic `finalize` (`Impl/MdStream/X86.lean`) with a
digest of the first 48, 32 or 28 bytes of the final hash value
(`params384`, `params512_256`, `params512_224`), so it is verified by the
generic proof of a `finalize` writing a prefix of the final hash value
(`Finalize.verified_roD`), given what writing that prefix does (`ShapeD`),
and constant time by the taint analysis of its code.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86.Stream

open VG VG.X86 VG.Proof.MdStream VG.Proof.MdStream.X86
open VG.Impl.MdStream.X86 (out64)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_frame)
open VG.Impl.Sha512.X86.Stream (outHi params384 params512_256 params512_224 finalizeDigest)

/-- `out64 n` writes the first `8 n` bytes of the digest. -/
theorem out64_take {n : Nat} (hn : n ≤ 8) (s : State) (hbx : (s.gpr .ebx).toNat + 64 ≤ 2 ^ 32)
    (hax : (s.gpr .eax).toNat + 8 * n ≤ 2 ^ 32)
    (hin : InRegions (s.rd ++ s.wr) ((s.gpr .ebx).setWidth 64) 64)
    (hout : InRegions s.wr ((s.gpr .eax).setWidth 64) (8 * n))
    (hd : Region.Disjoint ⟨(s.gpr .ebx).setWidth 64, 64⟩ ⟨(s.gpr .eax).setWidth 64, 8 * n⟩) :
    WP isa (.block (out64 n)) s fun s' => (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mem = writeBytes s.mem ((s.gpr .eax).setWidth 64)
        ((md.digest (md.stateAt s.mem ((s.gpr .ebx).setWidth 64))).take (8 * n)) :=
  (out64_ok (n := n) (by omega_using [hn]) (by omega_using [hn, hbx]) hax (inRegions_prefix hin (by omega_using [hn])) hout
    (hd.sub_left (Region.sub_prefix (by omega_using [hn])))).mono
    fun _ ⟨g, rd, wr, m⟩ => ⟨g, rd, wr, by rw [m, digest_take_halves _ _ hn]⟩

/-- `out64 3 ++ outHi 3` writes the first 28 bytes of the digest. -/
theorem out224_ok (s : State) (hbx : (s.gpr .ebx).toNat + 64 ≤ 2 ^ 32)
    (hax : (s.gpr .eax).toNat + 28 ≤ 2 ^ 32)
    (hin : InRegions (s.rd ++ s.wr) ((s.gpr .ebx).setWidth 64) 64)
    (hout : InRegions s.wr ((s.gpr .eax).setWidth 64) 28)
    (hd : Region.Disjoint ⟨(s.gpr .ebx).setWidth 64, 64⟩ ⟨(s.gpr .eax).setWidth 64, 28⟩) :
    WP isa (.block (out64 3 ++ outHi 3)) s fun s' => (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mem = writeBytes s.mem ((s.gpr .eax).setWidth 64)
        ((md.digest (md.stateAt s.mem ((s.gpr .ebx).setWidth 64))).take 28) := by
  rw [WP.block_append_iff]
  refine (out64_ok (n := 3) (by decide) (by omega_using [hbx]) (by omega_using [hax]) (inRegions_prefix hin (by decide))
    (inRegions_prefix hout (by decide))
    ((hd.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)))).mono
    fun s₁ ⟨g₁, rd₁, wr₁, m₁⟩ => ?_
  have hl : ((List.range 3).flatMap fun k =>
      bytes32 true (s.mem.readW ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (8 * k + 4)) 32) ++
        bytes32 true (s.mem.readW ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (8 * k)) 32)).length = 24 :=
    length_flatMap_range _ (w := 8) (fun _ => by simp [bytes32_length]) 3
  -- The high half of word 3 is not yet overwritten.
  have hread : s₁.mem.readW ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 28) 32 =
      s.mem.readW ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 28) 32 := by
    rw [m₁]
    refine (writeBytes_frame _ _ _ (R := ⟨(s.gpr .eax).setWidth 64, 28⟩) ?_).readW
      (r := ⟨(s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 28, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    · rw [hl]
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
      decide
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact hd.sub_left (sub_offset (by decide) (by decide))
  simp only [outHi]
  refine wp_movm (a := (s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 28)
    (by rw [ea_at, g₁ _ (by decide), addr_eq (by omega_using [hbx])])
    (by rw [rd₁, wr₁]; exact out_in hin (by decide) (by decide)) fun s₂ u₂ => wp_bswap fun s₃ u₃ => ?_
  refine wp_store (a := (s.gpr .eax).setWidth 64 + BitVec.ofNat 64 24)
    (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), addr_eq (by omega_using [hax])])
    (by rw [u₃.wr, u₂.wr, wr₁]; exact out_in hout (by decide) (by decide)) fun s₄ u₄ =>
      WP.block_nil ⟨fun r h => by rw [u₄.gpr, u₃.other r h, u₂.other r h, g₁ r h],
        by rw [u₄.rd, u₃.rd, u₂.rd, rd₁], by rw [u₄.wr, u₃.wr, u₂.wr, wr₁], ?_⟩
  have w := fun (m : Mem) (a : Addr) (x : BitVec 32) => writeW32 m a true x
  simp only [ite_true] at w
  rw [u₄.mem, u₃.mem, u₂.mem, u₃.gpr, u₂.gpr, hread, w, m₁, digest_take28_halves,
    ← writeBytes_append _ _ _ _ (by rw [hl]; simp [bytes32_length]), hl]

theorem shape384 : ShapeD (P := params384) md 48 where
  le := by decide
  len := shape.len
  out s hbx hax hin hout hd := out64_take (n := 6) (by decide) s hbx hax hin hout hd

theorem shape512_256 : ShapeD (P := params512_256) md 32 where
  le := by decide
  len := shape.len
  out s hbx hax hin hout hd := out64_take (n := 4) (by decide) s hbx hax hin hout hd

theorem shape512_224 : ShapeD (P := params512_224) md 28 where
  le := by decide
  len := shape.len
  out s hbx hax hin hout hd := out224_ok s hbx hax hin hout hd

namespace Finalize

theorem finalize384_verified :
    Verified X86.target (finalizeDigest params384) (MdStream.X86.finKD (P := params384) md 272 48) :=
  MdStream.X86.Finalize.verified_roD (P := params384) (name := "vg_sha512_compress")
    ⟨dims.1, dims.2, dims.3, dims.4, dims.5⟩ shape384 (callee.withOut (out64 6))
    (VG.Taint.constantTime (A := sseTaint) (MdStream.X86.Finalize.τ₀D params384 272 48)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Finalize.agree₀D ⟨dims.1, dims.2, dims.3, dims.4, dims.5⟩
        (by decide) h₁ h₂ hp) (by taint_decide))

theorem finalize512_256_verified :
    Verified X86.target (finalizeDigest params512_256) (MdStream.X86.finKD (P := params512_256) md 272 32) :=
  MdStream.X86.Finalize.verified_roD (P := params512_256) (name := "vg_sha512_compress")
    ⟨dims.1, dims.2, dims.3, dims.4, dims.5⟩ shape512_256 (callee.withOut (out64 4))
    (VG.Taint.constantTime (A := sseTaint) (MdStream.X86.Finalize.τ₀D params512_256 272 32)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Finalize.agree₀D ⟨dims.1, dims.2, dims.3, dims.4, dims.5⟩
        (by decide) h₁ h₂ hp) (by taint_decide))

theorem finalize512_224_verified :
    Verified X86.target (finalizeDigest params512_224) (MdStream.X86.finKD (P := params512_224) md 272 28) :=
  MdStream.X86.Finalize.verified_roD (P := params512_224) (name := "vg_sha512_compress")
    ⟨dims.1, dims.2, dims.3, dims.4, dims.5⟩ shape512_224 (callee.withOut (out64 3 ++ outHi 3))
    (VG.Taint.constantTime (A := sseTaint) (MdStream.X86.Finalize.τ₀D params512_224 272 28)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Finalize.agree₀D ⟨dims.1, dims.2, dims.3, dims.4, dims.5⟩
        (by decide) h₁ h₂ hp) (by taint_decide))

end Finalize

end VG.Proof.Sha512.X86.Stream

end

end

/-!
# Sha512 on X86: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha512/X86/Compress.lean`); these theorems move them to the shared
contracts of `Spec/Sha512/Contract.lean`, which the artifacts are emitted
with.

The shared contracts give the functions more scratch than these ones use (1328
bytes for `compress`, 1376 for `update` and `finalize`, sized for the x86-64
AVX2 compression function): the per-target contracts are first widened to
that scratch (`Verified.widen`, the same code running with the same trace and
result), then moved to the shared ones. `update` and `finalize` call the
compression function, using the 20 bytes below the return address.

`update` and `finalize` keep their working space in a frame of their own:
they are `updateScratch` and `finalizeScratch` (the shared contracts with
the working space as an argument, which HMAC's, PBKDF2's and Ed25519's code
calls) run in a frame that allocates it (`Verified.stackScratch`).
-/

@[expose] public section

namespace VG.Proof.Sha512.X86.Shared

open _root_.VG.X86

/-- `updateX86` with 1376 bytes of scratch. -/
def updateWide : Contract X86.isa :=
  { Proof.Sha512.updateX86 with
    pre := fun s =>
      let state : Region := ⟨(arg s 0).setWidth 64, 192⟩
      let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
      let scratch : Region := ⟨(arg s 5).setWidth 64, 1376⟩
      let args : Region := ⟨argAddr s 0, 24⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
      s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint scratch ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
      stack.Disjoint data ∧
      (arg s 0).toNat + 192 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 5).toNat + 1376 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 }

/-- `finalizeX86` with 1376 bytes of scratch. -/
def finalizeWide : Contract X86.isa :=
  { Proof.Sha512.finalizeX86 with
    pre := fun s =>
      let state : Region := ⟨(arg s 0).setWidth 64, 192⟩
      let out : Region := ⟨(arg s 3).setWidth 64, 64⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, 1376⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
      s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 192 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 64 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 1376 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub272 (a : Addr) : Region.Sub ⟨a, 272⟩ ⟨a, 1376⟩ := Region.sub_prefix (by decide)
theorem le272 {x : Nat} (h : x + 1376 ≤ 2 ^ 32) : x + 272 ≤ 2 ^ 32 := by omega_using [h]

/-- Rewrites the per-target contracts at a narrowed state (`arg` does not
unfold cheaply). -/
macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| plain_simp_names simp only [Proof.Sha512.compressX86, Proof.Sha512.updateX86, Proof.Sha512.finalizeX86,
                     Proof.Sha512.countX86, updateWide, finalizeWide, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, State.withRegions_gpr, State.withRegions_mem, State.withRegions_rd,
                     State.withRegions_wr] $(loc)?)

theorem updateWide_verified (hsat : ∃ s, updateWide.pre s) :
    Verified X86.target Impl.Sha512.X86.Stream.update updateWide :=
  Verified.widen Proof.Sha512.X86.Stream.Update.update_verified
    (fun s => [⟨(arg s 0).setWidth 64, 192⟩, ⟨(arg s 5).setWidth 64, 272⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃.sub_right (sub272 _), h₄, h₅.sub_right (sub272 _), h₆,
        h₇.sub_right (sub272 _), h₈, h₉.sub_right (sub272 _), h₁₀, h₁₁.sub_right (sub272 _), h₁₂, h₁₃,
        h₁₄, le272 h₁₅, h₁₆, h₁₇⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

theorem finalizeWide_verified (hsat : ∃ s, finalizeWide.pre s) :
    Verified X86.target Impl.Sha512.X86.Stream.finalize finalizeWide :=
  Verified.widen Proof.Sha512.X86.Stream.Finalize.finalize_verified
    (fun s => [⟨(arg s 0).setWidth 64, 192⟩, ⟨(arg s 3).setWidth 64, 64⟩,
      ⟨(arg s 4).setWidth 64, 272⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃, h₄.sub_right (sub272 _), h₅.sub_right (sub272 _), h₆, h₇,
        h₈.sub_right (sub272 _), h₉, h₁₀, h₁₁.sub_right (sub272 _), h₁₂, h₁₃, h₁₄.sub_right (sub272 _),
        h₁₅, h₁₆, le272 h₁₇, h₁₈, h₁₉⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State :=
  { Proof.Sha512.X86.Stream.Update.sat with wr := [⟨0x1000, 192⟩, ⟨0x3000, 1376⟩] }

/-- A state satisfying `finalizeWide.pre`. -/
def finalizeSat : State :=
  { Proof.Sha512.X86.Stream.Finalize.sat with
    wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩, ⟨0x3000, 1376⟩] }

theorem init (iv : Spec.Sha512.HashValue) :
    Verified X86.target (Impl.Sha512.X86.Stream.init iv) (Spec.Sha512.initContract X86.abi iv) :=
  (Proof.Sha512.X86.Stream.init_verified iv).of_implies (by
    sig_implies [Spec.Sha512.initContract, Spec.Sha512.initSig, Proof.Sha512.initX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Sha512.X86.Stream.initSat, Proof.Sha512.X86.Stream.initSatMem, X86.arg, X86.argAddr, Mem.readW,
      Mem.read] using Proof.Sha512.X86.Stream.initSat)

theorem updateWide_implies : updateWide.Implies (Proof.Sha512.updateScratchContract X86.abi 20) := by
  sig_implies [Proof.Sha512.updateScratchContract, Proof.Sha512.updateScratchSig, updateWide, Proof.Sha512.updateX86,
    Proof.Sha512.countX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [updateSat, Proof.Sha512.X86.Stream.Update.sat, MdStream.X86.Update.sat, MdStream.X86.Update.sat₀,
      MdStream.X86.Update.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using updateSat

theorem updateScratch :
    Verified X86.target Impl.Sha512.X86.Stream.update (Proof.Sha512.updateScratchContract X86.abi 20) :=
  (updateWide_verified updateWide_implies.sat_left).of_implies updateWide_implies

theorem finalizeWide_implies : finalizeWide.Implies (Proof.Sha512.finalizeScratchContract X86.abi 20) := by
  contract_implies [Proof.Sha512.finalizeScratchContract, Proof.Sha512.finalizeScratchSig, finalizeWide,
    Proof.Sha512.finalizeX86, Proof.Sha512.countX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finalizeSat, Proof.Sha512.X86.Stream.Finalize.sat, MdStream.X86.Finalize.satR, MdStream.X86.Finalize.sat₀,
      MdStream.X86.Finalize.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finalizeSat

theorem finalizeScratch :
    Verified X86.target Impl.Sha512.X86.Stream.finalize (Proof.Sha512.finalizeScratchContract X86.abi 20) :=
  (finalizeWide_verified finalizeWide_implies.sat_left).of_implies finalizeWide_implies

/-- A state satisfying `update`'s precondition. -/
def updateFrameSat : State :=
  { MdStream.X86.Update.sat₀ with rd := [⟨0x2000, 0⟩, ⟨0x5004, 20⟩], wr := [⟨0x1000, 192⟩] }

theorem update : Verified X86.target
    (Impl.StackScratch.X86.withStackScratch 1404 5 Impl.Sha512.X86.Stream.update)
    (Spec.Sha512.updateContract X86.abi (20 + 1404)) :=
  X86.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 20) (bytes := 1404)
    updateScratch (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.updatePost_local _) (fun vs m m₁ m₂ r hl _ hb => Proof.Sha512.updatePostOut_local _ vs m m₁ m₂ r hl hb)
    (by implies_sat [Spec.Sha512.updateContract, Spec.Sha512.updateSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes]
      [updateFrameSat, MdStream.X86.Update.sat₀, MdStream.X86.Update.satMem, X86.arg, X86.argAddr,
        Mem.readW, Mem.read] using updateFrameSat)

/-- A state satisfying `finalize`'s precondition. -/
def finalizeFrameSat : State :=
  { MdStream.X86.Finalize.sat₀ with rd := [⟨0x5004, 16⟩], wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩] }

theorem finalize : Verified X86.target
    (Impl.StackScratch.X86.withStackScratch 1400 4 Impl.Sha512.X86.Stream.finalize)
    (Spec.Sha512.finalizeContract X86.abi (20 + 1400)) :=
  X86.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 20) (bytes := 1400)
    finalizeScratch (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.finalizePost_local _) (fun vs m m₁ m₂ r hl _ hb => Proof.Sha512.finalizePostOut_local _ vs m m₁ m₂ r hl hb)
    (by implies_sat [Spec.Sha512.finalizeContract, Spec.Sha512.finalizeSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes]
      [finalizeFrameSat, MdStream.X86.Finalize.sat₀, MdStream.X86.Finalize.satMem, X86.arg,
        X86.argAddr, Mem.readW, Mem.read] using finalizeFrameSat)

/-! ## The truncated digests

`finalizeDigest` (SHA-384's, SHA-512/256's and SHA-512/224's `finalize`) is
verified against `finKD`; widened to the shared scratch, for the algorithm's
initial hash value, and with its working space in a frame of its own, it is
`Spec.Sha512.finalizeDigestContract`. -/

/-- `finalizeWide` for the `D`-byte `digest` of the messages hashed from `iv`. -/
def finalizeDigestWide (iv : Spec.Sha512.HashValue) (D : Nat) (digest : List Byte → List Byte) :
    Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 192⟩
    let out : Region := ⟨(arg s 3).setWidth 64, D⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 1376⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 192 ≤ 2 ^ 32 ∧ (arg s 3).toNat + D ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 1376 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' := ∀ m, Spec.Sha512.Repr iv s.mem ((arg s 0).setWidth 64) m → m.length < 2 ^ 64 →
    Proof.Sha512.countX86 s = BitVec.ofNat 64 m.length →
    Spec.Sha512.bytesAt s'.mem ((arg s 3).setWidth 64) D = digest m
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- Rewrites `finKD` and `finalizeDigestWide` at a narrowed state. -/
macro "narrowD" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| plain_simp_names simp only [MdStream.X86.finKD, Proof.Sha512.countX86, finalizeDigestWide, MdStream.X86.count,
                     VG.X86.arg_withRegions, VG.X86.argAddr_withRegions, State.withRegions_gpr, State.withRegions_mem,
                     State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem finalizeDigestWide_verified {code : Prog X86.isa} {o : List Instr} {D : Nat}
    {iv : Spec.Sha512.HashValue} {digest : List Byte → List Byte}
    (hv : Verified X86.target code
      (MdStream.X86.finKD (P := { Impl.Sha512.X86.Stream.params with out := o }) md 272 D))
    (hdg : ∀ m, (md.hash iv m).take D = digest m) (hsat : ∃ s, (finalizeDigestWide iv D digest).pre s) :
    Verified X86.target code (finalizeDigestWide iv D digest) :=
  Verified.widen hv
    (fun s => [⟨(arg s 0).setWidth 64, 192⟩, ⟨(arg s 3).setWidth 64, D⟩,
      ⟨(arg s 4).setWidth 64, 272⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉⟩ := h
      narrowD
      exact ⟨h₁, rfl, h₃, h₄.sub_right (sub272 _), h₅.sub_right (sub272 _), h₆, h₇,
        h₈.sub_right (sub272 _), h₉, h₁₀, h₁₁.sub_right (sub272 _), h₁₂, h₁₃, h₁₄.sub_right (sub272 _),
        h₁₅, h₁₆, le272 h₁₇, h₁₈, h₁₉⟩)
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
  { MdStream.X86.Finalize.satRD Impl.Sha512.X86.Stream.params 272 D with
    wr := [⟨0x1000, 192⟩, ⟨0x2000, D⟩, ⟨0x3000, 1376⟩] }

theorem finalizeDigestWide_implies48 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 48 digest).Implies (finalizeDigestScratchContract X86.abi iv 48 digest 20) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, Proof.Sha512.countX86, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [finalizeDigestSat, MdStream.X86.Finalize.satRD, MdStream.X86.Finalize.sat₀,
      MdStream.X86.Finalize.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finalizeDigestSat 48

theorem finalizeDigestWide_implies32 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 32 digest).Implies (finalizeDigestScratchContract X86.abi iv 32 digest 20) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, Proof.Sha512.countX86, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [finalizeDigestSat, MdStream.X86.Finalize.satRD, MdStream.X86.Finalize.sat₀,
      MdStream.X86.Finalize.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finalizeDigestSat 32

theorem finalizeDigestWide_implies28 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 28 digest).Implies (finalizeDigestScratchContract X86.abi iv 28 digest 20) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, Proof.Sha512.countX86, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [finalizeDigestSat, MdStream.X86.Finalize.satRD, MdStream.X86.Finalize.sat₀,
      MdStream.X86.Finalize.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finalizeDigestSat 28

theorem finalizeDigestScratch {code : Prog X86.isa} {o : List Instr} {D : Nat}
    {iv : Spec.Sha512.HashValue} {digest : List Byte → List Byte} (hD : D = 48 ∨ D = 32 ∨ D = 28)
    (hv : Verified X86.target code
      (MdStream.X86.finKD (P := { Impl.Sha512.X86.Stream.params with out := o }) md 272 D))
    (hdg : ∀ m, (md.hash iv m).take D = digest m) :
    Verified X86.target code (finalizeDigestScratchContract X86.abi iv D digest 20) := by
  have hi : (finalizeDigestWide iv D digest).Implies (finalizeDigestScratchContract X86.abi iv D digest 20) := by
    rcases hD with rfl | rfl | rfl
    exacts [finalizeDigestWide_implies48 iv digest, finalizeDigestWide_implies32 iv digest,
      finalizeDigestWide_implies28 iv digest]
  exact (finalizeDigestWide_verified hv hdg hi.sat_left).of_implies hi

/-- A state satisfying `Spec.Sha512.finalizeDigestContract`'s precondition. -/
def finalizeDigestFrameSat (D : Nat) : State :=
  { MdStream.X86.Finalize.sat₀ with rd := [⟨0x5004, 16⟩], wr := [⟨0x1000, 192⟩, ⟨0x2000, D⟩] }

theorem finalizeDigestStack48 {code : Prog X86.isa} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte}
    (hv : Verified X86.target code (finalizeDigestScratchContract X86.abi iv 48 digest 20))
    (hsp : code.allInstrs (fun i => !Taint.clobbers i .esp) = true) (hd : stackUse code ≤ 20) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 1400 4 code)
      (Spec.Sha512.finalizeDigestContract X86.abi iv 48 digest (20 + 1400)) :=
  X86.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 20) (bytes := 1400)
    hv (by decide) hsp hd (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sha512.finalizeDigestPost_local _ _ _ _) (fun vs m m₁ m₂ r hl _ hb => Proof.Sha512.finalizeDigestPostOut_local _ _ _ _ vs m m₁ m₂ r hl hb)
    (by implies_sat [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes]
      [finalizeDigestFrameSat, MdStream.X86.Finalize.sat₀, MdStream.X86.Finalize.satMem, X86.arg,
        X86.argAddr, Mem.readW, Mem.read] using finalizeDigestFrameSat 48)

theorem finalizeDigestStack32 {code : Prog X86.isa} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte}
    (hv : Verified X86.target code (finalizeDigestScratchContract X86.abi iv 32 digest 20))
    (hsp : code.allInstrs (fun i => !Taint.clobbers i .esp) = true) (hd : stackUse code ≤ 20) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 1400 4 code)
      (Spec.Sha512.finalizeDigestContract X86.abi iv 32 digest (20 + 1400)) :=
  X86.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 20) (bytes := 1400)
    hv (by decide) hsp hd (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sha512.finalizeDigestPost_local _ _ _ _) (fun vs m m₁ m₂ r hl _ hb => Proof.Sha512.finalizeDigestPostOut_local _ _ _ _ vs m m₁ m₂ r hl hb)
    (by implies_sat [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes]
      [finalizeDigestFrameSat, MdStream.X86.Finalize.sat₀, MdStream.X86.Finalize.satMem, X86.arg,
        X86.argAddr, Mem.readW, Mem.read] using finalizeDigestFrameSat 32)

theorem finalizeDigestStack28 {code : Prog X86.isa} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte}
    (hv : Verified X86.target code (finalizeDigestScratchContract X86.abi iv 28 digest 20))
    (hsp : code.allInstrs (fun i => !Taint.clobbers i .esp) = true) (hd : stackUse code ≤ 20) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 1400 4 code)
      (Spec.Sha512.finalizeDigestContract X86.abi iv 28 digest (20 + 1400)) :=
  X86.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 20) (bytes := 1400)
    hv (by decide) hsp hd (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sha512.finalizeDigestPost_local _ _ _ _) (fun vs m m₁ m₂ r hl _ hb => Proof.Sha512.finalizeDigestPostOut_local _ _ _ _ vs m m₁ m₂ r hl hb)
    (by implies_sat [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes]
      [finalizeDigestFrameSat, MdStream.X86.Finalize.sat₀, MdStream.X86.Finalize.satMem, X86.arg,
        X86.argAddr, Mem.readW, Mem.read] using finalizeDigestFrameSat 28)

theorem finalize384 : Verified X86.target
    (Impl.StackScratch.X86.withStackScratch 1400 4
      (Impl.Sha512.X86.Stream.finalizeDigest Impl.Sha512.X86.Stream.params384))
    (Spec.Sha512.finalizeDigestContract X86.abi Spec.Sha512.H0_384 48 Spec.Sha512.sha384 (20 + 1400)) :=
  finalizeDigestStack48 (finalizeDigestScratch (.inl rfl) Proof.Sha512.X86.Stream.Finalize.finalize384_verified
    (fun _ => rfl)) (by lit_decide) (by lit_decide)

theorem finalize512_256 : Verified X86.target
    (Impl.StackScratch.X86.withStackScratch 1400 4
      (Impl.Sha512.X86.Stream.finalizeDigest Impl.Sha512.X86.Stream.params512_256))
    (Spec.Sha512.finalizeDigestContract X86.abi Spec.Sha512.H0_512_256 32 Spec.Sha512.sha512_256 (20 + 1400)) :=
  finalizeDigestStack32 (finalizeDigestScratch (.inr (.inl rfl))
    Proof.Sha512.X86.Stream.Finalize.finalize512_256_verified (fun _ => rfl)) (by lit_decide) (by lit_decide)

theorem finalize512_224 : Verified X86.target
    (Impl.StackScratch.X86.withStackScratch 1400 4
      (Impl.Sha512.X86.Stream.finalizeDigest Impl.Sha512.X86.Stream.params512_224))
    (Spec.Sha512.finalizeDigestContract X86.abi Spec.Sha512.H0_512_224 28 Spec.Sha512.sha512_224 (20 + 1400)) :=
  finalizeDigestStack28 (finalizeDigestScratch (.inr (.inr rfl))
    Proof.Sha512.X86.Stream.Finalize.finalize512_224_verified (fun _ => rfl)) (by lit_decide) (by lit_decide)

end VG.Proof.Sha512.X86.Shared
