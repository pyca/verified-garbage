import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.CT
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: `Verified`

Untrusted: everything here is checked by Lean. The shared contract of
`vg_chacha20_poly1305_seal_gather`, with the 1808 bytes of stack below the
stack pointer that its frames and its call use (48 for our frame, 8 for
`tag` pushed for the call, 8 for its return address and 1744 for the
callee's contract) (`Spec.ChaCha20Poly1305.sealGatherContract`), implies
the one the proof is written against (`gatherX86_64`, `gather_implies`), and
so the code, calling an instance of `vg_chacha20_poly1305_seal` by its shared
contract (`sealFn`), is `Verified` against it (`sealGather_verified`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.SealGather

theorem sealGather_correct (w : Width) (F : SealFn) (s : State) (hs : gatherX86_64.pre s) :
    ∃ t s', Exec isa (sealGather w F.name F.code) s t s' ∧ abiPreserved s s' ∧ gatherX86_64.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := sealGather_wp w F hs
  exact ⟨t, s', he, ha, hp⟩

theorem filter_true' (l : List Region) : l.filter (fun _ => true) = l := List.filter_eq_self.mpr (by simp)

theorem filter_false' (l : List Region) : l.filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (by simp)

theorem filterMap_some' {β : Type} (f : Region → β) (l : List Region) :
    l.filterMap (fun x => some (f x)) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem filterMap_none' {β : Type} (l : List Region) : l.filterMap (fun _ => (none : Option β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Pairs of read-only regions give no facts. -/
theorem pairFacts_ro (l : List (Region × Bool)) (h : ∀ a ∈ l, a.2 = false) : Sig.pairFacts l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [Sig.pairFacts, ih fun b hb => h b (List.mem_cons_of_mem _ hb), List.append_nil]
    refine List.filterMap_eq_nil_iff.mpr fun b hb => ?_
    rw [h a List.mem_cons_self, h b (List.mem_cons_of_mem _ hb)]
    rfl

theorem stackArgs_three (s : State) : List.map (stackArg s) (List.range 3) =
    [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

theorem gatherPre_of_spec {s : State} (h : (Spec.ChaCha20Poly1305.sealGatherContract X86_64.abi 1808).pre s) :
    gatherPre s := by
  sig_pre [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, X86_64.abi, X86_64.argRegs, stackArgs_three, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, kt, nd, nt, ad, at_, dt, dds, ⟨dls, darg⟩, -, -, -⟩, -, -, -, rdd, rt,
    ⟨-, -, bk, bn, ba, bd, bt, bds, bls, -⟩, ok, on, oa, od, ot, ⟨ods, ol⟩, hgl, hpm⟩ := h
  exact ⟨rd, wr, kd, kt, nd, nt, ad, at_, dt, dds, dls, darg, rdd, rt, bk, bn, ba, bd, bt, bds, bls, ok, on, oa,
    od, ot, ods, ol, w₁, w₂, hgl, hpm⟩

theorem gatherPost_of {s s' : State} (h : gatherPost s s') :
    (Spec.ChaCha20Poly1305.sealGatherContract X86_64.abi 1808).post s s' := by
  sig_post [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPost, X86_64.abi, X86_64.argRegs, stackArgs_three, List.append_eq]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State}
    (hp : (Spec.ChaCha20Poly1305.sealGatherContract X86_64.abi 1808).pub s₁ s₂) : gatherPub s₁ s₂ := by
  sig_pub [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, X86_64.abi, X86_64.argRegs, stackArgs_three, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨qsp, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, hd⟩ := hp
  exact ⟨q₁, q₂, q₃, q₄, q₅, q₆, qsp, a₀, a₁, a₂, fun i hi => hd i (by simpa using hi)⟩

/-- A state satisfying the precondition of `vg_chacha20_poly1305_seal_gather`:
no slices, no additional data or text; `dst` at `0x4000` and `tag` at
`0x5000`, on the stack at `0x9008`. -/
def gatherSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .r8 => 0x3100 | .rsp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if 0x9000 ≤ a.toNat then (if a = 0x9009 then 0x40 else if a = 0x9019 then 0x50 else 0) else 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x9008, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩]

theorem gatherSat_pre : ∃ s, (Spec.ChaCha20Poly1305.sealGatherContract X86_64.abi 1808).pre s := by
  sig_implies_sat [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, X86_64.abi, X86_64.argRegs, stackArgs_three, List.append_eq]
    [gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.ChaCha20Poly1305.pMax] using gatherSat

theorem gather_implies : gatherX86_64.Implies (Spec.ChaCha20Poly1305.sealGatherContract X86_64.abi 1808) :=
  ⟨fun _ h => gatherPre_of_spec h, fun _ _ _ h => gatherPost_of h, fun _ _ _ _ h => gatherPub_of h, gatherSat_pre⟩

theorem sealGather_verified (w : Width) (F : SealFn) :
    Verified X86_64.target (sealGather w F.name F.code)
      (Spec.ChaCha20Poly1305.sealGatherContract X86_64.abi 1808) :=
  Verified.of_correct (k := gatherX86_64) (sealGather_correct w F) (sealGather_ct w F) gather_implies

open VG.Proof.ChaCha20.X86_64 VG.Impl.StackScratch.X86_64 in
/-- The instance of `vg_chacha20_poly1305_seal` calling the implementation
`v` of `vg_chacha20_xor`, with its working space in a frame of its own. -/
def sealFn (v : XorImpl) : SealFn where
  name := Spec.ChaCha20Poly1305.sealApi.name ++ v.suffix
  code := withStackArgScratchWiped 1720 1 84 (Impl.ChaCha20Poly1305.X86_64.«seal» v.callee v.poly)
  verified := Proof.ChaCha20Poly1305.X86_64.seal_framed v
  sp := SpSafe.of_all (X86_64.withStackArgScratchWiped_spSafe (Proof.ChaCha20Poly1305.X86_64.seal_spSafe v))
  depth := by
    have := Proof.ChaCha20Poly1305.X86_64.seal_xdepth v
    simp only [withStackArgScratchWiped, withStackArgScratch, Code.x86_64Depth, X86_64.Instr.frameBytes,
      Nat.zero_max, Nat.max_zero, Nat.max_le]
    omega

open VG.Proof.ChaCha20.X86_64 in
/-- How many bytes at a time the instance for `v` copies: as many as the
CPUs of the instance of `vg_chacha20_poly1305_seal` it calls can. -/
def width (v : XorImpl) : Width := .ofBlocks v.poly

open VG.Proof.ChaCha20.X86_64 in
/-- No instruction of the code, or of the instance it calls, writes `rsp`
but its frames' pushes and pops. -/
theorem sealGather_spSafe (v : XorImpl) :
    (sealGather (width v) (sealFn v).name (sealFn v).code).all (fun i => !X86_64.isa.writesSp i) = true := by
  have hc : (sealFn v).code.all (fun i => !X86_64.isa.writesSp i) = true :=
    X86_64.withStackArgScratchWiped_spSafe (Proof.ChaCha20Poly1305.X86_64.seal_spSafe v)
  simp only [sealGather, Code.all, hc, Bool.and_true, Bool.true_and]
  cases width v <;> decide +kernel

end VG.Proof.ChaCha20Poly1305.X86_64.Gather
