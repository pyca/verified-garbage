import VerifiedGarbage.Proof.Sha256.X86.Stream.Variant
import VerifiedGarbage.Proof.Sha256.Digest

/-!
# Streaming SHA-224 on x86 (32-bit): `finalize224`

`finalize224` is the generic `finalize` (`Impl/MdStream/X86.lean`) with a
digest of the first 28 bytes of the final hash value (`params224`), so it is
verified by the generic proof of a `finalize` writing a prefix of the final
hash value (`Finalize.verified_roD`), for any verified compression function,
given what writing that prefix does (`ShapeD`) and that it is constant time
(each backend's taint analysis of its code). Widened to the shared scratch,
and with its working space in a frame of its own, it is
`Spec.Sha256.finalize224Contract`.
-/

namespace VG.Proof.Sha256.X86.Stream

open VG VG.X86 VG.Proof.MdStream VG.Proof.MdStream.X86
open VG.Impl.Sha256.X86.Stream (params224 finalize224)

theorem dims224 : Dims params224 160 := ⟨.inl rfl, by decide, by decide, by decide, by decide⟩

theorem shape224 : ShapeD (P := params224) md 28 where
  le := by decide
  len := shape.len
  out s hbx hax hin hout hd := by
    refine (out32_ok (n := 7) true (by decide) (by have : params224.N = 32 := rfl; omega) hax (inRegions_prefix hin (by decide)) hout
      (hd.sub_left (Region.sub_prefix (by decide)))).mono fun s' ⟨g, rd, wr, m⟩ => ⟨g, rd, wr, ?_⟩
    rw [m, digest_take _ _ (n := 7) (by decide)]

/-- `finalize224`, with any verified compression function, if it is constant
time. -/
theorem finalize224_of {name : String} {code : Prog isa} (hcomp : CalleeOk (P := params) md code)
    (ct : ConstantTime isa (finKD (P := params224) md 160 28).pre (finKD (P := params224) md 160 28).pub
      (finalize224 name code)) :
    Verified X86.target (finalize224 name code) (finKD (P := params224) md 160 28) :=
  MdStream.X86.Finalize.verified_roD (name := name) dims224 shape224 (hcomp.withOut _) ct

end VG.Proof.Sha256.X86.Stream

namespace VG.Proof.Sha256.X86.Shared

open VG VG.X86 VG.Proof.MdStream
open VG.Impl.Sha256.X86.Stream (params224)

/-- `finKD` widened to 608 bytes of scratch, for SHA-224's digest of the
messages hashed from its initial hash value. -/
def finalize224Wide : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 96⟩
    let out : Region := ⟨(arg s 3).setWidth 64, 28⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 608⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 96 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 28 ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 608 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' := ∀ m, Spec.Sha256.ReprFrom Spec.Sha256.H0_224 s.mem ((arg s 0).setWidth 64) m →
    Proof.Sha256.countX86 s = BitVec.ofNat 64 m.length →
    Spec.Sha256.bytesAt s'.mem ((arg s 3).setWidth 64) 28 = Spec.Sha256.sha224 m
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- Rewrites `finKD` and `finalize224Wide` at a narrowed state. -/
macro "narrow224" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [MdStream.X86.finKD, Proof.Sha256.countX86, finalize224Wide, MdStream.X86.count,
    VG.X86.arg_withRegions, VG.X86.argAddr_withRegions, State.withRegions_gpr, State.withRegions_mem,
    State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem finalize224Wide_of {code : Prog X86.isa}
    (hv : Verified X86.target code (MdStream.X86.finKD (P := params224) md 160 28))
    (hsat : ∃ s, finalize224Wide.pre s) : Verified X86.target code finalize224Wide :=
  Verified.widen hv
    (fun s => [⟨(arg s 0).setWidth 64, 96⟩, ⟨(arg s 3).setWidth 64, 28⟩,
      ⟨(arg s 4).setWidth 64, 160⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉⟩ := h
      narrow224
      exact ⟨h₁, rfl, h₃, h₄.sub_right (sub160 _), h₅.sub_right (sub160 _), h₆, h₇,
        h₈.sub_right (sub160 _), h₉, h₁₀, h₁₁.sub_right (sub160 _), h₁₂, h₁₃, h₁₄.sub_right (sub160 _),
        h₁₅, h₁₆, le160 h₁₇, h₁₈, h₁₉⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons ⟨rfl, Nat.le_refl _⟩ (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => by
      narrow224 at h ⊢
      intro m hr hc
      exact (h _ m hr trivial hc).trans (sha224_eq m))
    (fun _ _ _ _ h => by narrow224; exact h) hsat

/-- A state satisfying `finalize224Wide.pre`. -/
def finalize224Sat : State :=
  { MdStream.X86.Finalize.satRD params224 160 28 with
    wr := [⟨0x1000, 96⟩, ⟨0x2000, 28⟩, ⟨0x3000, 608⟩] }

theorem finalize224Wide_implies : finalize224Wide.Implies (Proof.Sha256.finalize224ScratchContract X86.abi 20) := by
  contract_implies [Proof.Sha256.finalize224ScratchContract, Proof.Sha256.finalize224ScratchSig,
    Spec.Sha256.finalize224Post, finalize224Wide, Proof.Sha256.countX86, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [finalize224Sat, MdStream.X86.Finalize.satRD, MdStream.X86.Finalize.sat₀,
      MdStream.X86.Finalize.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finalize224Sat

/-- `finalize224` with its working space in `scratch`. -/
theorem finalize224Scratch {code : Prog X86.isa}
    (hv : Verified X86.target code (MdStream.X86.finKD (P := params224) md 160 28)) :
    Verified X86.target code (Proof.Sha256.finalize224ScratchContract X86.abi 20) :=
  (finalize224Wide_of hv finalize224Wide_implies.sat_left).of_implies finalize224Wide_implies

/-- A state satisfying `Spec.Sha256.finalize224Contract`'s precondition. -/
def finalize224FrameSat : State :=
  { MdStream.X86.Finalize.sat₀ with rd := [⟨0x5004, 16⟩], wr := [⟨0x1000, 96⟩, ⟨0x2000, 28⟩] }

/-- `finalize224`: `finalize224Scratch` with its working space in a frame of
its own. -/
theorem finalize224_frame {code : Prog X86.isa}
    (h : Verified X86.target code (Proof.Sha256.finalize224ScratchContract X86.abi 20))
    (hsp : code.allInstrs (fun i => !Taint.clobbers i .esp) = true) (hd : stackUse code ≤ 20) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 632 4 code)
      (Spec.Sha256.finalize224Contract X86.abi (20 + 632)) :=
  X86.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 76) (stack := 20) (bytes := 632)
    h (by decide) hsp hd (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sha256.finalize224Post_local _)
    (by implies_sat [Spec.Sha256.finalize224Contract, Spec.Sha256.finalize224Sig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes]
      [finalize224FrameSat, MdStream.X86.Finalize.sat₀, MdStream.X86.Finalize.satMem, X86.arg,
        X86.argAddr, Mem.readW, Mem.read] using finalize224FrameSat)

end VG.Proof.Sha256.X86.Shared
