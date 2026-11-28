module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4AvxCorrect
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Avx
public meta import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4AvxCorrect
public meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
public meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
public meta import VerifiedGarbage.Proof.Framework.Taint
public meta import VerifiedGarbage.Impl.SlhDsa.X86_64.Thash4

/-!
# SLH-DSA on x86-64: `thash4` with AVX2, verified

`thash4 n fast` is `Verified` against `thash4Contract n 0`, for `n` 16, 24
and 32 and with or without AVX-512VL (`thash4_verified16`, …): its
correctness is `Thash4Avx.correct`; it keeps the callee-saved registers, the
return address and MXCSR (`hv_of`, which an implementation with calls can
use too); it is constant time by the taint analysis (`ct16`, …), from the
taint `τ₀` in which the arguments are public and `rdi` and `r8` point at the
lanes and `work`; and its precondition is satisfiable (`sat`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Thash4Avx

open VG VG.X86_64
open VG.Impl.SlhDsa.X86_64.Thash4
open VG.Proof.SlhDsa.X86_64 (Thash4Pre thash4Contract thash4Changes msg outAt retR workLen RcTable)
open VG.Spec.Sha3 (bytesAt)

variable {n stk : Nat}

/-! ## The calling convention -/

theorem ret_below (sp : Addr) {k : Nat} (hk : k + 8 ≤ 2 ^ 64) : Region.Disjoint ⟨sp, 8⟩ (below sp k) := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

/-- The return address is outside every region `thash4` may change. -/
theorem ret_changes {σ : State} (hp : Thash4Pre n stk σ) (hk : stk + 8 ≤ 2 ^ 64) :
    ∀ r ∈ thash4Changes n stk σ, Region.Disjoint (retR σ) r := by
  intro r hr
  simp only [thash4Changes, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with ⟨k, hk', rfl⟩ | rfl | rfl | rfl
  · exact hp.ret_lanes.sub_right (out_sub hp hk')
  · exact hp.ret_work.sub_right (sub_pre _ (by decide))
  · exact hp.ret_work.sub_right (sub_off _ (by decide))
  · exact ret_below _ hk

/-- The first part of `Verified` for code that computes `thash4` from every
state of the precondition, keeping the callee-saved registers, and never
loads MXCSR. -/
theorem hv_of {c : Prog isa} (hk : stk + 8 ≤ 2 ^ 64)
    (hc : ∀ σ, Thash4Pre n stk σ → WP isa c σ (fun s' =>
      (∀ k < 4, bytesAt s'.mem (outAt σ k) n = Spec.Sha3.shake256 (msg σ k) n) ∧
      Frame (thash4Changes n stk σ) σ.mem s'.mem ∧ ∀ r ∈ calleeSaved, s'.gpr r = σ.gpr r))
    (hmx : c.allInstrs (fun i => !loadsMxcsr i) = true) :
    ∀ s, (thash4Contract n stk).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (thash4Contract n stk).post s s' := by
  intro s hs
  obtain ⟨t, s', he, h1, h2, h3⟩ := hc s hs
  refine ⟨t, s', he, abiPreserved_of_exec hmx he ⟨h3, ?_⟩, h1, h2⟩
  exact h2.readW (r := retR s) (by simp [Region.Contains]) (ret_changes hs hk) (by decide)

/-! ## Constant time -/

/-- The initial taint: the arguments and `rsp` are public, and `rdi` and
`r8` point at the lanes (of unknown length) and `work`. -/
def τ₀ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false, lens := [0, workLen],
    bases := [(.rdi, 0, 0), (.r8, 1, 0)] }

theorem wf₀ {s : State} (h : Thash4Pre n stk s) : X86_64.Taint.Wf τ₀ s := by
  have hl := str_lt h
  refine ⟨fun _ => ⟨by simp [h.wr, τ₀], by simp [h.wr, h.lanes_work], ?_⟩, fun p hp => ?_⟩
  · simp only [h.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hl
    · simp [workLen]
  · simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, h.wr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Thash4Pre n stk s₁) (h₂ : Thash4Pre n stk s₂)
    (hpub : (thash4Contract n stk).pub s₁ s₂) : X86_64.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂, ?_, ?_,
    X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.wr, h₂.wr, p1, p2, p5]
  · intro sl h; simp [τ₀] at h
  · intro sl h; simp [τ₀] at h

theorem ct16 : ConstantTime isa (thash4Contract 16 0).pre (thash4Contract 16 0).pub (thash4 16 false) :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)
theorem ct24 : ConstantTime isa (thash4Contract 24 0).pre (thash4Contract 24 0).pub (thash4 24 false) :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)
theorem ct32 : ConstantTime isa (thash4Contract 32 0).pre (thash4Contract 32 0).pub (thash4 32 false) :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)
theorem ct16f : ConstantTime isa (thash4Contract 16 0).pre (thash4Contract 16 0).pub (thash4 16 true) :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)
theorem ct24f : ConstantTime isa (thash4Contract 24 0).pre (thash4Contract 24 0).pub (thash4 24 true) :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)
theorem ct32f : ConstantTime isa (thash4Contract 32 0).pre (thash4Contract 32 0).pub (thash4 32 true) :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

/-! ## The registers the code writes -/

theorem hcs_of {c : Prog isa} (h : (instrs c).all (fun i => calleeSaved.all fun r => !Taint.clobbers i r) = true) :
    ∀ r ∈ calleeSaved, ∀ i ∈ instrs c, Taint.clobbers i r = false := fun r hr i hi => by
  have := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
  simpa using this


theorem mx16 : (thash4 16 false).allInstrs (fun i => !loadsMxcsr i) = true := by decide +kernel
theorem mx24 : (thash4 24 false).allInstrs (fun i => !loadsMxcsr i) = true := by decide +kernel
theorem mx32 : (thash4 32 false).allInstrs (fun i => !loadsMxcsr i) = true := by decide +kernel
theorem mx16f : (thash4 16 true).allInstrs (fun i => !loadsMxcsr i) = true := by decide +kernel
theorem mx24f : (thash4 24 true).allInstrs (fun i => !loadsMxcsr i) = true := by decide +kernel
theorem mx32f : (thash4 32 true).allInstrs (fun i => !loadsMxcsr i) = true := by decide +kernel

/-! ## A state satisfying the precondition -/

/-- `work`'s address in the witness. -/
abbrev satW : Nat := 0x100000

/-- The witness's memory: the table of round constants in `work`, and zeros. -/
def satMem (x : Addr) : Byte :=
  if satW + 1600 ≤ x.toNat ∧ x.toNat < satW + 2368 then
    (Spec.Sha3.RC ((x.toNat - satW - 1600) / 32)).extractLsb' (8 * ((x.toNat - satW - 1600) % 8)) 8
  else 0

/-- A state satisfying the precondition, for outputs of `n` bytes. -/
def sat (n : Nat) : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rsi => 128 | .rdx => 8 | .rcx => 0x10000 + BitVec.ofNat 64 (n + 32) | .r8 => 0x100000
    | .rsp => 0x200000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := []
  wr := [⟨0x10000, 512⟩, ⟨0x100000, 2400⟩]

theorem sat_rc (n : Nat) : RcTable (sat n).mem ((sat n).gpr .r8) := by
  intro r hr k hk
  refine Proof.SlhDsa.X86_64.lane_ext fun d hd => ?_
  rw [byte_readW _ _ (by omega_using [hd])]
  show satMem _ = _
  have ha : (BitVec.ofNat 64 0x100000 + BitVec.ofNat 64 (1600 + 32 * r + 8 * k) + BitVec.ofNat 64 d).toNat =
      0x100000 + 1600 + 32 * r + 8 * k + d := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hr, hk, hd]
  simp only [satMem, satW, show ((sat n).gpr .r8) = BitVec.ofNat 64 0x100000 from rfl, ha]
  rw [ite_eq_left (by omega_using [hr, hk, hd]), show (0x100000 + 1600 + 32 * r + 8 * k + d - 0x100000 - 1600) / 32 = r by
      omega_using [hk, hd], show (0x100000 + 1600 + 32 * r + 8 * k + d - 0x100000 - 1600) % 8 = d by omega_using [hd]]

theorem sat_pre {n : Nat} (hn : n + 32 + n ≤ 128) : Thash4Pre n 0 (sat n) where
  rd := rfl
  wr := rfl
  lanes_work := Region.disjoint_of_sep (by
    show Region.sep ⟨(0x10000 : Addr), 4 * (128 : BitVec 64).toNat⟩ ⟨0x100000, workLen⟩ = true; decide)
  ret_lanes := Region.disjoint_of_sep (by
    show Region.sep ⟨(0x200000 : Addr), 8⟩ ⟨0x10000, 4 * (128 : BitVec 64).toNat⟩ = true; decide)
  ret_work := Region.disjoint_of_sep (by show Region.sep ⟨(0x200000 : Addr), 8⟩ ⟨0x100000, workLen⟩ = true; decide)
  stk_lanes := fun _ h => by simp [Region.Contains] at h
  stk_work := fun _ h => by simp [Region.Contains] at h
  lanes_fit := by show (0x10000 : BitVec 64).toNat + 4 * (128 : BitVec 64).toNat ≤ 2 ^ 64; decide
  work_fit := by show (0x100000 : BitVec 64).toNat + workLen ≤ 2 ^ 64; decide
  len_pos := by show 0 < (8 : BitVec 64).toNat; decide
  len_mod := by show (8 : BitVec 64).toNat % 8 = 0; decide
  len_le := by show (8 : BitVec 64).toNat ≤ (128 : BitVec 64).toNat; decide
  out_eq := rfl
  out_fit := hn
  rc := sat_rc n

/-! ## `Verified` -/

theorem verified_of {n : Nat} (fast : Bool) (hn : n % 8 = 0) (hn' : n ≤ 136) (hn'' : n + 32 + n ≤ 128)
    (hmx : (thash4 n fast).allInstrs (fun i => !loadsMxcsr i) = true)
    (hct : ConstantTime isa (thash4Contract n 0).pre (thash4Contract n 0).pub (thash4 n fast)) :
    Verified X86_64.target (thash4 n fast) (thash4Contract n 0) :=
  ⟨hv_of (by decide) (fun _ hp => correct hp hn hn' fast) hmx, hct, ⟨_, sat_pre hn''⟩⟩

theorem thash4_verified16 : Verified X86_64.target (thash4 16 false) (thash4Contract 16 0) :=
  verified_of false (by decide) (by decide) (by decide) mx16 ct16
theorem thash4_verified24 : Verified X86_64.target (thash4 24 false) (thash4Contract 24 0) :=
  verified_of false (by decide) (by decide) (by decide) mx24 ct24
theorem thash4_verified32 : Verified X86_64.target (thash4 32 false) (thash4Contract 32 0) :=
  verified_of false (by decide) (by decide) (by decide) mx32 ct32
theorem thash4_verified16f : Verified X86_64.target (thash4 16 true) (thash4Contract 16 0) :=
  verified_of true (by decide) (by decide) (by decide) mx16f ct16f
theorem thash4_verified24f : Verified X86_64.target (thash4 24 true) (thash4Contract 24 0) :=
  verified_of true (by decide) (by decide) (by decide) mx24f ct24f
theorem thash4_verified32f : Verified X86_64.target (thash4 32 true) (thash4Contract 32 0) :=
  verified_of true (by decide) (by decide) (by decide) mx32f ct32f

end VG.Proof.SlhDsa.X86_64.Thash4Avx
