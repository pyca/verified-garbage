module

import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.BlkCall
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CallTo
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyLoop
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Fn
import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Copy
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Calls
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Steps
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Callee
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Impl.Aes.X86_64.Alloc

/-! ### `AesGcm.X86_64.Gather.SplitCallee`, which this module and modules that import it used -/

section

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: `vg_aes_gcm_seal_split` called

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather`
copies the slices after the first of a short text to the output and
encrypts the text by a call of `vg_aes_gcm_seal_split` (or of its instance
for the key context of `vg_aes_gcm_init_precomputed`) from the first slice
where it is and the rest at the output, an artifact with its working space
in a frame of its own; so what the proof needs of it is its shared contract
(`Spec/Gcm/OutOfPlace.lean`), in the terms of this target, as
`SealCallee.lean` does for `vg_aes_gcm_seal` (`splitK`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64
open VG.Impl.AesGcm.X86_64 (Fn)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args ret rounds)

/-! ## `vg_aes_gcm_seal_split(ctx = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx, aad = r8,
aad_len = r9, src = [rsp + 8], src_len = [rsp + 16], dst = [rsp + 24], len = [rsp + 32],
tag = [rsp + 40])` -/

/-- What a call of `vg_aes_gcm_seal_split` needs, for a key context of kind
`M`: the layout of its shared contract with 2672 bytes of stack. -/
def splitPreK (M : CtxMode) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, M.len⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let src : Region := ⟨arg s 0, (arg s 1).toNat⟩
  let data : Region := ⟨arg s 2, (arg s 3).toNat⟩
  let tag : Region := ⟨arg s 4, 16⟩
  let stk : Region := below (s.gpr .rsp) 2672
  s.rd = [ctx, nonce, aad, src, args s 5] ∧ s.wr = [data, tag] ∧
    ctx.Disjoint data ∧ ctx.Disjoint tag ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    aad.Disjoint data ∧ aad.Disjoint tag ∧ src.Disjoint data ∧ src.Disjoint tag ∧ data.Disjoint tag ∧
    data.Disjoint (args s 5) ∧ tag.Disjoint (args s 5) ∧
    (ret s).Disjoint ctx ∧ (ret s).Disjoint nonce ∧ (ret s).Disjoint aad ∧ (ret s).Disjoint src ∧
    (ret s).Disjoint data ∧ (ret s).Disjoint tag ∧ (ret s).Disjoint (args s 5) ∧
    stk.Disjoint ctx ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint src ∧ stk.Disjoint data ∧
    stk.Disjoint tag ∧ stk.Disjoint (args s 5) ∧
    (s.gpr .rdi).toNat + M.len ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 64 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 64 ∧ (arg s 4).toNat + 16 ≤ 2 ^ 64 ∧
    2672 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64 ∧ rounds s ∧
    (arg s 1).toNat ≤ (arg s 3).toNat ∧ M.ok s.mem (s.gpr .rdi)

def splitPubK (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧
    arg s₁ 3 = arg s₂ 3 ∧ arg s₁ 4 = arg s₂ 4 ∧ s₁.mxcsr = s₂.mxcsr

def splitK (M : CtxMode) : Contract isa where
  pre := splitPreK M
  post := (Proof.AesGcm.sealSplitX86_64M M).post
  pub := splitPubK

theorem splitSpec_pre {s : State} (h : splitPreK CtxMode.base s) :
    (Proof.Gcm.sealSplitContract X86_64.abi 2672).pre s := by
  sig_split h
  clear h
  sig_pre [Proof.Gcm.sealSplitContract, Proof.Gcm.sealSplitSig, Proof.Gcm.sealSplitPre, X86_64.abi, X86_64.argRegs,
    List.range, List.range.loop]
  sig_reduce [Proof.Gcm.sealSplitContract, Proof.Gcm.sealSplitSig, Proof.Gcm.sealSplitPre, X86_64.abi, X86_64.argRegs,
    Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
    List.range, List.range.loop, VG.X86_64.below]
  -- Once, before the goal is split: not every hypothesis again for each conjunct.
  simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.base, BitVec.setWidth_eq] at *
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | omega

theorem splitSpecP_pre {s : State} (h : splitPreK CtxMode.powers s) :
    (Proof.Gcm.sealSplitPrecomputedContract X86_64.abi 2672).pre s := by
  sig_split h
  have a₀ := h
  clear h
  sig_pre [Proof.Gcm.sealSplitPrecomputedContract, Proof.Gcm.sealSplitPrecomputedSig,
    Proof.Gcm.sealSplitPrecomputedPre, X86_64.abi, X86_64.argRegs, List.range, List.range.loop]
  sig_reduce [Proof.Gcm.sealSplitPrecomputedContract, Proof.Gcm.sealSplitPrecomputedSig,
    Proof.Gcm.sealSplitPrecomputedPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args,
    Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
    VG.X86_64.below]
  -- Once, before the goal is split: not every hypothesis again for each conjunct.
  simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.powers, BitVec.setWidth_eq] at *
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | omega

theorem splitSpec_post {M : CtxMode} {s s' : State} (h : (Proof.Gcm.sealSplitContract X86_64.abi 2672).post s s')
    (hR : rounds s) : (Proof.AesGcm.sealSplitX86_64M M).post s s' := by
  sig_post [Proof.Gcm.sealSplitContract, Proof.Gcm.sealSplitSig, Proof.Gcm.sealSplitPre, X86_64.abi, X86_64.argRegs,
    Proof.Gcm.sealSplitPost] at h
  sig_reduce [Proof.Gcm.sealSplitContract, Proof.Gcm.sealSplitSig, X86_64.abi, X86_64.argRegs, X86_64.stackArg,
    X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem splitSpecP_post {M : CtxMode} {s s' : State} (h : (Proof.Gcm.sealSplitPrecomputedContract X86_64.abi 2672).post s s')
    (hR : rounds s) : (Proof.AesGcm.sealSplitX86_64M M).post s s' := by
  sig_post [Proof.Gcm.sealSplitPrecomputedContract, Proof.Gcm.sealSplitPrecomputedSig,
    Proof.Gcm.sealSplitPrecomputedPre, X86_64.abi, X86_64.argRegs, Proof.Gcm.sealSplitPost] at h
  sig_reduce [Proof.Gcm.sealSplitPrecomputedContract, Proof.Gcm.sealSplitPrecomputedSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem splitSpec_pub {s₁ s₂ : State} (h : splitPubK s₁ s₂) :
    (Proof.Gcm.sealSplitContract X86_64.abi 2672).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, aMd⟩ := h
  sig_pub [Proof.Gcm.sealSplitContract, Proof.Gcm.sealSplitSig, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.Gcm.sealSplitContract, Proof.Gcm.sealSplitSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀ a₁₁ a₁₂
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

theorem splitSpecP_pub {s₁ s₂ : State} (h : splitPubK s₁ s₂) :
    (Proof.Gcm.sealSplitPrecomputedContract X86_64.abi 2672).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, aMd⟩ := h
  sig_pub [Proof.Gcm.sealSplitPrecomputedContract, Proof.Gcm.sealSplitPrecomputedSig, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.Gcm.sealSplitPrecomputedContract, Proof.Gcm.sealSplitPrecomputedSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀ a₁₁ a₁₂
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-! ## The function called -/

abbrev SplitFn (M : CtxMode) := CallFn (splitK M) 2672

/-- `vg_aes_gcm_seal_split` from its shared contract. -/
def SplitFn.ofBase (f : Fn) (hv : Verified X86_64.target f.code (Proof.Gcm.sealSplitContract X86_64.abi 2672))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2672)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : SplitFn CtxMode.base :=
  CallFn.ofSpec f hv (fun _ h => splitSpec_pre h)
    (fun _ _ h h' => splitSpec_post (M := CtxMode.base) h' h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ h => splitSpec_pub h) sp xd mx

/-- `vg_aes_gcm_seal_split_precomputed` from its shared contract. -/
def SplitFn.ofPowers (f : Fn)
    (hv : Verified X86_64.target f.code (Proof.Gcm.sealSplitPrecomputedContract X86_64.abi 2672))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2672)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : SplitFn CtxMode.powers :=
  CallFn.ofSpec f hv (fun _ h => splitSpecP_pre h)
    (fun _ _ h h' => splitSpecP_post (M := CtxMode.powers) h' h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ h => splitSpecP_pub h) sp xd mx

end VG.Proof.AesGcm.X86_64.Gather

end

end

/-! ### `AesGcm.X86_64.Gather.SplitPath`, which this module and modules that import it used -/

section

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: a short copy, to `vg_aes_gcm_seal_split`

Untrusted: everything here is checked by Lean. What each block of the path
of a text whose slices after the first are fewer than `t` bytes does, from
the arguments kept in `work`: the test (`splitTest_wp`), the nonce and the
first slice kept, and the gathering's registers for the slices after it
(`splitEntry_ok`, `splitFirst_ok`, `splitKeep_ok`), what the gathering
needs (`splitGatherPre`) and leaves (`split_after`), and the arguments of
`vg_aes_gcm_seal_split` (`splitArgs_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (GatherPre GKeeps gatherRegs frame_of)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes
open VG.Spec.Gcm (gathered gatheredLen)

/-! ## The slices after the first -/

/-- `n + 1` descriptors list the slice of the first, then those of the `n`
after it. -/
theorem listed_zero (m : Mem) (p : Addr) (n : Nat) :
    Sig.listed 64 m .u8 p (n + 1) =
      ⟨(m.readW p 64).setWidth 64, (m.readW (p + BitVec.ofNat 64 8) 64).toNat * Elem.u8.size⟩ ::
        Sig.listed 64 m .u8 (p + BitVec.ofNat 64 16) n := by
  simp only [Sig.listed, List.range_succ_eq_map, List.map_cons, List.map_map]
  refine List.cons_eq_cons.mpr ⟨by simp, List.map_congr_left fun i _ => ?_⟩
  simp only [Function.comp]
  obtain e : p + BitVec.ofNat 64 ((i + 1) * (2 * (64 / 8))) =
      p + BitVec.ofNat 64 16 + BitVec.ofNat 64 (i * (2 * (64 / 8))) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith
  rw [e]

theorem gathered_zero (m : Mem) (p : Addr) (n : Nat) :
    gathered 64 m p (n + 1) = bytesAt m (m.readW p 64) (m.readW (p + BitVec.ofNat 64 8) 64).toNat ++
      gathered 64 m (p + BitVec.ofNat 64 16) n := by
  simp [gathered, listed_zero, Elem.size]

theorem gatheredLen_zero (m : Mem) (p : Addr) (n : Nat) :
    gatheredLen 64 m p (n + 1) = (m.readW (p + BitVec.ofNat 64 8) 64).toNat +
      gatheredLen 64 m (p + BitVec.ofNat 64 16) n := by
  simp [gatheredLen, listed_zero, Elem.size]

section
variable (s : State)

/-- The slices skipped: the first, if any. -/
abbrev k0 : Nat := if Cnt s = 0 then 0 else 1
/-- The first slice's length (0 if there is none) and address (the descriptors' if none). -/
abbrev fl : Nat := gl s (k0 s)
abbrev fb : Addr := if Cnt s = 0 then Src s else sb s 0

theorem k0_le : k0 s ≤ Cnt s := by unfold k0; split <;> omega_arith

/-- What the short path's threshold applies to: the text's length, or 0 if
its first slice holds all its whole blocks. -/
abbrev shortLen : Nat := if 16 * (L s / 16) ≤ fl s then 0 else L s

/-- What the choice between copying the text whole and sealing it from its
first slice applies to: 0 unless its first slice holds all its whole blocks,
and then that slice's length. -/
abbrev selLen : Nat := if fl s < 16 * (L s / 16) then 0 else fl s

theorem fl_eq : fl s = if Cnt s = 0 then 0 else sl s 0 := by
  unfold fl k0; split
  · exact gl_zero
  · rw [gl_succ, gl_zero, Nat.zero_add]

/-- The first slice's bytes. -/
theorem pt_k0 : pt s (k0 s) = bytesAt s.mem (fb s) (fl s) := by
  unfold fl fb k0; split
  · simp [pt, gathered, Sig.listed, gl_zero, bytesAt]
  · rw [pt_succ, gl_succ, gl_zero, Nat.zero_add]; simp [pt, gathered, Sig.listed]

/-- The text: the first slice, then those after it. -/
theorem pt_split : pt s (Cnt s) = pt s (k0 s) ++ gathered 64 s.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s) ∧
    gl s (Cnt s) = fl s + gatheredLen 64 s.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s) := by
  unfold fl k0; split
  · next h => simp [pt, gl, h, gl_zero, gathered, gatheredLen, Sig.listed]
  · next h =>
    obtain ⟨n, hn⟩ : ∃ n, Cnt s = n + 1 := ⟨Cnt s - 1, by omega_arith⟩
    rw [hn, Nat.add_sub_cancel]
    obtain e0 : pt s 0 = [] := by simp [pt, gathered, Sig.listed]
    obtain h0 : Src s + BitVec.ofNat 64 (16 * 0) = Src s := by simp
    refine ⟨?_, ?_⟩
    · show gathered 64 s.mem (Src s) (n + 1) = pt s (0 + 1) ++ _
      rw [gathered_zero, pt_succ, e0, List.nil_append, sb, sl, h0]
    · show gatheredLen 64 s.mem (Src s) (n + 1) = gl s (0 + 1) + _
      rw [gatheredLen_zero, gl_succ, gl_zero, Nat.zero_add, sl, h0]

/-- The slices after the first are slices of the text. -/
theorem listed_k0 : ∀ r ∈ Sig.listed 64 s.mem .u8 (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s), r ∈ lsR s := by
  intro r hr
  unfold k0 at hr; split at hr
  · simpa using hr
  · next h =>
    obtain ⟨n, hn⟩ : ∃ n, Cnt s = n + 1 := ⟨Cnt s - 1, by omega_arith⟩
    simp only [lsR, hn, Nat.add_sub_cancel, Nat.mul_one] at hr ⊢
    rw [listed_zero]
    exact List.mem_cons_of_mem _ hr

end

/-- `n` descriptors list the first `k` (none or one) slices, then the rest. -/
theorem gathered_k (m : Mem) (p : Addr) {n k : Nat} (hk : k = 0 ∨ (k = 1 ∧ n ≠ 0)) :
    gathered 64 m p n = gathered 64 m p k ++ gathered 64 m (p + BitVec.ofNat 64 (16 * k)) (n - k) := by
  rcases hk with rfl | ⟨rfl, hn⟩
  · simp [gathered, Sig.listed]
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega_arith⟩
    rw [gathered_zero, Nat.add_sub_cancel, show (1 : Nat) = 0 + 1 from rfl, gathered_zero]
    simp [gathered, Sig.listed]

/-- `k0`, for `gathered_k`. -/
theorem k0_cases (s : State) : k0 s = 0 ∨ (k0 s = 1 ∧ Cnt s ≠ 0) := by
  unfold k0; split <;> simp_all

/-! ## The test -/

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

theorem fl_le : fl s ≤ L s := gl_le hp (k0_le s)

/-- `work` in `r11`, no first slice yet, and `ZF` if there is no slice. -/
theorem splitT1_ok {st : State} (h : Base s (AL s) 0 st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 48)), .mov32 .r10 (imm 0), .mov .rax (.mem (at_ .r11 gLeft)),
      .alu .test .rax (.reg .rax)]) st fun st' =>
      st'.gpr .r11 = W s ∧ st'.gpr .r10 = 0 ∧ st'.zf = some (decide (Cnt s = 0)) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧
      st'.wr = st.wr := by
  obtain ⟨a₅, e₅⟩ := h.w hp
  obtain r₈ := h.slot hp (d := 64) (by decide)
  obtain hC : Cnt s < 2 ^ 64 := (stackArg s 1).isLt
  obtain hz := and_self_beq hC
  obtain hleft : st.mem.readW (W s + BitVec.ofNat 64 64) 64 = BitVec.ofNat 64 (Cnt s) := by
    rw [h.kept.left, Nat.sub_zero]
  apply WP.of_runBlock
  refine ⟨_, by simp only [gLeft]; xrun [a₅, e₅, r₈, hleft], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags, imm]
  · simp only [zf_arithFlags, gpr_setReg, ite_true, hz]
  · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- The first slice's length into `r10`. -/
theorem splitT2_ok (hc : Cnt s ≠ 0) {st : State} (h : Base s (AL s) 0 st) (h11 : st.gpr .r11 = W s) :
    WP isa (.block [.mov .r10 (.mem (at_ .r11 gDesc)), .mov .r10 (.mem (at_ .r10 8))]) st fun st' =>
      st'.gpr .r10 = BitVec.ofNat 64 (fl s) ∧ (∀ r, r ≠ .r10 → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧
      st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain r₇ := h.slot hp (d := 56) (by decide)
  obtain d₈ := desc_in hp h (i := 0) (by omega_arith) (d := 8) (by decide)
  obtain v₈ := sl_eq hp h.frame (i := 0) (by omega_arith)
  have hd : st.mem.readW (W s + BitVec.ofNat 64 56) 64 = Src s + BitVec.ofNat 64 (16 * 0) := h.kept.desc
  obtain hfl : fl s = sl s 0 := by rw [fl_eq]; simp [hc]
  apply WP.of_runBlock
  refine ⟨_, by simp only [gDesc]; xrun [h11, r₇, hd, d₈, v₈], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, hfl, v₈]
  · intro r a; simp [gpr_setReg, a]
  all_goals simp [mem_setReg, rd_setReg, wr_setReg]

/-- What follows the first slice is short below any threshold of the short path. -/
theorem sub_lt_of_shortLen {t : Nat} (ht : t < 2 ^ 31) (h : shortLen s < t) : L s - fl s < 2 ^ 63 := by
  have := fl_le hp
  unfold shortLen at h; split at h <;> omega_arith

/-- `CF` if the text is shorter than `t`, or its first slice holds all its
whole blocks. -/
theorem splitT3_ok {t : Nat} (ht : t < 2 ^ 31) {st : State} (h : Base s (AL s) 0 st) (h11 : st.gpr .r11 = W s)
    (h10 : st.gpr .r10 = BitVec.ofNat 64 (fl s)) :
    WP isa (.block [.mov .rax (.mem (at_ .r11 gLen)), .shift .shr .rax 4, .shift .shl .rax 4,
        .alu .cmp .r10 (.reg .rax), .mov .rax (.mem (at_ .r11 gLen)), .mov32 .r10 (imm 0), .cmov .ae .rax (.reg .r10),
        .alu .cmp .rax (imm t)]) st
      fun st' => st'.cf = some (decide (shortLen s < t)) ∧ (∀ r, r ≠ .rax → r ≠ .r10 → st'.gpr r = st.gpr r) ∧
        st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain r₅ := h.slot hp (d := 40) (by decide)
  obtain hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  obtain hfl := fl_le hp
  obtain hlen : st.mem.readW (W s + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (L s) := by
    rw [h.kept.len, ofNat_toNat]
  obtain it := imm_eq ht
  obtain r16 := round16 hL
  obtain m₁ : fl s % 18446744073709551616 = fl s := Nat.mod_eq_of_lt (by omega_arith)
  obtain m₂ : L s % 18446744073709551616 = L s := Nat.mod_eq_of_lt (by omega_arith)
  obtain m₃ : t % 18446744073709551616 = t := Nat.mod_eq_of_lt (by omega_arith)
  obtain m₄ : 16 * (L s / 16) % 18446744073709551616 = 16 * (L s / 16) := Nat.mod_eq_of_lt (by omega_arith)
  obtain l₁ := toNat_ofNat_of_lt (show fl s < 2 ^ 64 by omega_arith)
  obtain l₂ := toNat_ofNat_of_lt (show 16 * (L s / 16) < 2 ^ 64 by omega_arith)
  obtain l₃ := toNat_ofNat_of_lt (show t < 2 ^ 64 by omega_arith)
  apply WP.of_runBlock
  by_cases h₁ : 16 * (L s / 16) ≤ fl s
  · have h₁' : ¬fl s < 16 * (L s / 16) := by omega_arith
    refine ⟨_, by simp only [gLen]; xrun [h11, h10, r₅, hlen, it, r16, execCmov, eval, l₁, l₂, l₃, m₁, m₂, m₃, m₄, h₁',
      decide_false, Bool.not_false, Option.map_some], ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | (intro r a b; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, a, b, m₁, m₂, m₄, h₁, h₁'])
        | (simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
            wr_setReg, wr_setFlags, m₁, m₂, m₄, h₁, h₁']; done)
        | (simp [shortLen, h₁, h₁', BitVec.toNat_ofNat, m₁, m₂, m₃, m₄] <;> omega_arith)
  · have h₁' : fl s < 16 * (L s / 16) := by omega_arith
    refine ⟨_, by simp only [gLen]; xrun [h11, h10, r₅, hlen, it, r16, execCmov, eval, l₁, l₂, l₃, m₁, m₂, m₃, m₄, h₁',
      decide_true, Bool.not_true, Bool.false_eq_true, Option.map_some], ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | (intro r a b; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, a, b, m₁, m₂, m₄, h₁, h₁'])
        | (simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
            wr_setReg, wr_setFlags, m₁, m₂, m₄, h₁, h₁']; done)
        | (simp [shortLen, h₁, h₁', BitVec.toNat_ofNat, m₁, m₂, m₃, m₄] <;> omega_arith)

/-- After the first block of the test. -/
def G1 (s st : State) : Prop :=
  E2 s st ∧ st.gpr .r11 = W s ∧ st.gpr .r10 = 0 ∧ st.zf = some (decide (Cnt s = 0))

/-- Before the comparison. -/
def G2 (s st : State) : Prop := E2 s st ∧ st.gpr .r11 = W s ∧ st.gpr .r10 = BitVec.ofNat 64 (fl s)

theorem w_splitT1 {st : State} (h : E2 s st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 48)), .mov32 .r10 (imm 0), .mov .rax (.mem (at_ .r11 gLeft)),
      .alu .test .rax (.reg .rax)]) st (G1 s) := by
  obtain ⟨B, di, si, dx, cx⟩ := h
  refine WP.mono_mx (by decide) (splitT1_ok hp B) fun s₁ ⟨r11₁, r10₁, zf₁, g₁, m₁, rd₁, wr₁⟩ mxw => ?_
  obtain cs₁ : ∀ r ∈ calleeSaved, s₁.gpr r = st.gpr r := fun r hr => g₁ r
    (by intro e; subst e; simp [calleeSaved] at hr) (by intro e; subst e; simp [calleeSaved] at hr)
    (by intro e; subst e; simp [calleeSaved] at hr)
  exact ⟨⟨B.regs m₁ cs₁ rd₁ wr₁ mxw, by rw [g₁ _ (by decide) (by decide) (by decide), di],
    by rw [g₁ _ (by decide) (by decide) (by decide), si], by rw [g₁ _ (by decide) (by decide) (by decide), dx],
    by rw [g₁ _ (by decide) (by decide) (by decide), cx]⟩, r11₁, r10₁, zf₁⟩

omit hp in
theorem w_splitT2z (hc : Cnt s = 0) {st : State} (h : G1 s st) : G2 s st :=
  ⟨h.1, h.2.1, by rw [h.2.2.1, fl_eq]; simp [hc]⟩

theorem w_splitT2 (hc : Cnt s ≠ 0) {st : State} (h : G1 s st) :
    WP isa (.block [.mov .r10 (.mem (at_ .r11 gDesc)), .mov .r10 (.mem (at_ .r10 8))]) st (G2 s) := by
  obtain ⟨⟨B, di, si, dx, cx⟩, r11, -, -⟩ := h
  refine WP.mono_mx (by decide) (splitT2_ok hp hc B r11) fun s₂ ⟨r10₂, g₂, m₂, rd₂, wr₂⟩ mxw => ?_
  obtain cs₂ : ∀ r ∈ calleeSaved, s₂.gpr r = st.gpr r := fun r hr => g₂ r
    (by intro e; subst e; simp [calleeSaved] at hr)
  exact ⟨⟨B.regs m₂ cs₂ rd₂ wr₂ mxw, by rw [g₂ _ (by decide), di], by rw [g₂ _ (by decide), si],
    by rw [g₂ _ (by decide), dx], by rw [g₂ _ (by decide), cx]⟩, by rw [g₂ _ (by decide), r11], r10₂⟩

theorem w_splitT3 {t : Nat} (ht : t < 2 ^ 31) {st : State} (h : G2 s st) :
    WP isa (.block [.mov .rax (.mem (at_ .r11 gLen)), .shift .shr .rax 4, .shift .shl .rax 4,
        .alu .cmp .r10 (.reg .rax), .mov .rax (.mem (at_ .r11 gLen)), .mov32 .r10 (imm 0), .cmov .ae .rax (.reg .r10),
        .alu .cmp .rax (imm t)]) st
      fun st' => E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some (decide (shortLen s < t)) := by
  obtain ⟨⟨B, di, si, dx, cx⟩, r11, r10⟩ := h
  refine WP.mono_mx (by rfl) (splitT3_ok hp ht B r11 r10) fun s₃ ⟨cf₃, g₃, m₃, rd₃, wr₃⟩ mxw => ?_
  obtain cs₃ : ∀ r ∈ calleeSaved, s₃.gpr r = st.gpr r := fun r hr => g₃ r
    (by intro e; subst e; simp [calleeSaved] at hr) (by intro e; subst e; simp [calleeSaved] at hr)
  exact ⟨⟨B.regs m₃ cs₃ rd₃ wr₃ mxw, by rw [g₃ _ (by decide) (by decide), di], by rw [g₃ _ (by decide) (by decide), si],
    by rw [g₃ _ (by decide) (by decide), dx], by rw [g₃ _ (by decide) (by decide), cx]⟩,
    by rw [g₃ _ (by decide) (by decide), r11], cf₃⟩

/-- The first slice's length, if there is one. -/
theorem w_splitIte {st : State} (h : G1 s st) :
    WP isa (.ite .e (.block []) (.block [.mov .r10 (.mem (at_ .r11 gDesc)), .mov .r10 (.mem (at_ .r10 8))])) st
      (G2 s) :=
  WP.ite (decide (Cnt s = 0)) (by simp only [eval, h.2.2.2]) (fun e => WP.block_nil (w_splitT2z (by simpa using e) h))
    (fun e => w_splitT2 hp (by simpa using e) h)

/-- The lengths, then `last`. -/
theorem lenTest_wp {last : List Instr} {P : State → Prop} (h₃ : ∀ st, G2 s st → WP isa (.block last) st P)
    {st : State} (h : E2 s st) : WP isa (lenTest last) st P := by
  unfold lenTest
  exact WP.seq (WP.mono (w_splitT1 hp h) fun s₁ G =>
    WP.seq (WP.mono (w_splitIte hp G) fun s₂ G₂ => h₃ s₂ G₂))

/-- `work` in `r11`, and `CF` if the text is shorter than `q`. -/
theorem quickT_ok {q : Nat} (hq : q < 2 ^ 31) {st : State} (h : Base s (AL s) 0 st) :
    WP isa (.block (quickTest q)) st fun st' =>
      st'.gpr .r11 = W s ∧ st'.cf = some (decide (L s < q)) ∧
      (∀ r, r ≠ .rax → r ≠ .r11 → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧
      st'.wr = st.wr := by
  obtain ⟨a₅, e₅⟩ := h.w hp
  obtain r₅ := h.slot hp (d := 40) (by decide)
  obtain hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  obtain hlen : st.mem.readW (W s + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (L s) := by
    rw [h.kept.len, ofNat_toNat]
  obtain it := imm_eq hq
  obtain m₂ : L s % 18446744073709551616 = L s := Nat.mod_eq_of_lt (by omega_arith)
  obtain m₃ : q % 18446744073709551616 = q := Nat.mod_eq_of_lt (by omega_arith)
  obtain l₂ := toNat_ofNat_of_lt hL
  obtain l₃ := toNat_ofNat_of_lt (show q < 2 ^ 64 by omega_arith)
  apply WP.of_runBlock
  refine ⟨_, by simp only [quickTest, gLen]; xrun [a₅, e₅, r₅, hlen, it], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [BitVec.toNat_ofNat, m₂, m₃, l₂, l₃]
  · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

theorem w_quick {q : Nat} (hq : q < 2 ^ 31) {st : State} (h : E2 s st) :
    WP isa (.block (quickTest q)) st fun st' =>
      E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some (decide (L s < q)) := by
  obtain ⟨B, di, si, dx, cx⟩ := h
  refine WP.mono_mx (by rfl) (quickT_ok hp hq B) fun s₁ ⟨r11₁, cf₁, g₁, m₁, rd₁, wr₁⟩ mxw => ?_
  obtain cs₁ : ∀ r ∈ calleeSaved, s₁.gpr r = st.gpr r := fun r hr => g₁ r
    (by intro e; subst e; simp [calleeSaved] at hr) (by intro e; subst e; simp [calleeSaved] at hr)
  exact ⟨⟨B.regs m₁ cs₁ rd₁ wr₁ mxw, by rw [g₁ _ (by decide) (by decide), di], by rw [g₁ _ (by decide) (by decide), si],
    by rw [g₁ _ (by decide) (by decide), dx], by rw [g₁ _ (by decide) (by decide), cx]⟩, r11₁, cf₁⟩

/-- The length alone if the text is shorter than `q`, which decides `b`;
otherwise the lengths, then `last`. -/
theorem lenTestQ_wp {q : Nat} (hq : q < 2 ^ 31) {last : List Instr} {b : Bool} (hb : L s < q → b = true)
    (h₃ : ∀ st, G2 s st → WP isa (.block last) st fun st' => E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some b)
    {st : State} (h : E2 s st) :
    WP isa (lenTestQ q last) st fun st' => E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some b := by
  unfold lenTestQ
  refine WP.seq (WP.mono (w_quick hp hq h) fun s₁ ⟨E, r11, cf⟩ => ?_)
  refine WP.ite (decide (L s < q)) (by simp only [eval, cf]) (fun e => WP.block_nil ⟨E, r11, ?_⟩)
    (fun _ => lenTest_wp hp h₃ E)
  rw [cf, e, hb (by simpa using e)]

/-- The test of the texts the short path takes. -/
theorem splitTest_wp {t : Nat} (ht : t < 2 ^ 31) {st : State} (h : E2 s st) :
    WP isa (splitTest t) st fun st' => E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some (decide (shortLen s < t)) :=
  lenTestQ_wp hp ht (fun e => by unfold shortLen; split <;> simp <;> omega_arith) (fun _ G => w_splitT3 hp ht G) h

/-- `CF` unless the first slice holds all the whole blocks and at least `ts`
bytes. -/
theorem selT3_ok {ts : Nat} (hts : ts < 2 ^ 31) {st : State} (h : Base s (AL s) 0 st) (h11 : st.gpr .r11 = W s)
    (h10 : st.gpr .r10 = BitVec.ofNat 64 (fl s)) :
    WP isa (.block (selLast ts)) st
      fun st' => st'.cf = some (decide (selLen s < ts)) ∧
        (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → st'.gpr r = st.gpr r) ∧
        st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain r₅ := h.slot hp (d := 40) (by decide)
  obtain hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  obtain hfl := fl_le hp
  obtain hlen : st.mem.readW (W s + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (L s) := by
    rw [h.kept.len, ofNat_toNat]
  obtain it := imm_eq hts
  obtain r16 := round16 hL
  obtain m₁ : fl s % 18446744073709551616 = fl s := Nat.mod_eq_of_lt (by omega_arith)
  obtain m₃ : ts % 18446744073709551616 = ts := Nat.mod_eq_of_lt (by omega_arith)
  obtain m₄ : 16 * (L s / 16) % 18446744073709551616 = 16 * (L s / 16) := Nat.mod_eq_of_lt (by omega_arith)
  obtain l₁ := toNat_ofNat_of_lt (show fl s < 2 ^ 64 by omega_arith)
  obtain l₂ := toNat_ofNat_of_lt (show 16 * (L s / 16) < 2 ^ 64 by omega_arith)
  obtain l₃ := toNat_ofNat_of_lt (show ts < 2 ^ 64 by omega_arith)
  apply WP.of_runBlock
  by_cases h₁ : fl s < 16 * (L s / 16)
  · refine ⟨_, by simp only [selLast, gLen]; xrun [h11, h10, r₅, hlen, it, r16, execCmov, eval, l₁, l₂, l₃, m₁, m₃,
      m₄, h₁, decide_true, Option.map_some], ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | (intro r a b c; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, a, b, c, m₁, m₄, h₁])
        | (simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
            wr_setReg, wr_setFlags, m₁, m₄, h₁]; done)
        | (simp [selLen, h₁, BitVec.toNat_ofNat, m₁, m₃, m₄] <;> omega_arith)
  · refine ⟨_, by simp only [selLast, gLen]; xrun [h11, h10, r₅, hlen, it, r16, execCmov, eval, l₁, l₂, l₃, m₁, m₃,
      m₄, h₁, decide_false, Bool.false_eq_true, Option.map_some], ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | (intro r a b c; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, a, b, c, m₁, m₄, h₁])
        | (simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
            wr_setReg, wr_setFlags, m₁, m₄, h₁]; done)
        | (simp [selLen, h₁, BitVec.toNat_ofNat, m₁, m₃, m₄] <;> omega_arith)

theorem w_selT3 {ts : Nat} (hts : ts < 2 ^ 31) {st : State} (h : G2 s st) :
    WP isa (.block (selLast ts)) st
      fun st' => E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some (decide (selLen s < ts)) := by
  obtain ⟨⟨B, di, si, dx, cx⟩, r11, r10⟩ := h
  refine WP.mono_mx (by rfl) (selT3_ok hp hts B r11 r10) fun s₃ ⟨cf₃, g₃, m₃, rd₃, wr₃⟩ mxw => ?_
  obtain cs₃ : ∀ r ∈ calleeSaved, s₃.gpr r = st.gpr r := fun r hr => g₃ r
    (by intro e; subst e; simp [calleeSaved] at hr) (by intro e; subst e; simp [calleeSaved] at hr)
    (by intro e; subst e; simp [calleeSaved] at hr)
  obtain g : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r11], s₃.gpr r = st.gpr r := fun r hr => g₃ r
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  exact ⟨⟨B.regs m₃ cs₃ rd₃ wr₃ mxw, by rw [g _ (by simp), di], by rw [g _ (by simp), si], by rw [g _ (by simp), dx],
    by rw [g _ (by simp), cx]⟩, by rw [g _ (by simp), r11], cf₃⟩

/-- The choice, on the short path, between copying the text whole and
sealing it from its first slice. -/
theorem selTest_wp {ts : Nat} (hts : ts < 2 ^ 31) {st : State} (h : E2 s st) :
    WP isa (selTest ts) st fun st' => E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some (decide (selLen s < ts)) :=
  lenTest_wp hp (fun _ G => w_selT3 hp hts G) h

/-- A text on the short path that is not sealed from its first slice is
shorter than the threshold. -/
theorem lt_of_sel {t ts : Nat} (htt : ts + 16 ≤ t) (h₁ : shortLen s < t) (h₂ : selLen s < ts) :
    L s < t := by
  have := fl_le hp
  unfold shortLen at h₁; unfold selLen at h₂
  split at h₁ <;> split at h₂ <;> omega_arith

/-- A text sealed from its first slice has fewer than 16 bytes after it. -/
theorem sub_lt_of_sel {ts : Nat} (hts : 1 ≤ ts) (h : ¬selLen s < ts) : L s - fl s < 2 ^ 63 := by
  have := fl_le hp
  unfold selLen at h; split at h <;> omega_arith

end

/-! ## The nonce and the first slice kept -/

/-- `CBase`, with the first slice's address and length kept in the
streaming state's slots after the nonce. -/
structure PBase (s : State) (st : State) : Prop extends CBase s st where
  first : st.mem.readW (St s + BitVec.ofNat 64 16) 64 = fb s
  firstLen : st.mem.readW (St s + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (fl s)

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-- The nonce and its length kept, the slices in `r9`, `dst` in `rdi`, the
first descriptor in `r10`, an empty first slice in `rax` and `rcx`, and `ZF`
if there is no slice. -/
theorem splitEntry_ok {st : State} (h : Base s (AL s) 0 st) (h11 : st.gpr .r11 = W s) (hsi : st.gpr .rsi = Nn s)
    (hdx : st.gpr .rdx = s.gpr .rcx) :
    WP isa (.block splitEntry) st fun st' =>
      st'.gpr .r9 = BitVec.ofNat 64 (Cnt s) ∧ st'.gpr .rdi = Dst s ∧ st'.gpr .r10 = Src s ∧ st'.gpr .rax = Src s ∧
      st'.gpr .rcx = 0 ∧ st'.zf = some (decide (Cnt s = 0)) ∧ st'.gpr .r11 = W s ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ CBase s st' := by
  have hw := hp.w_w
  obtain r₈ := h.slot hp (d := 64) (by decide)
  obtain r₄ := h.slot hp (d := 32) (by decide)
  obtain r₇ := h.slot hp (d := 56) (by decide)
  obtain hC : Cnt s < 2 ^ 64 := (stackArg s 1).isLt
  obtain hz := and_self_beq hC
  obtain w : ∀ d, d + 8 ≤ 184 → InRegions st.wr (W s + BitVec.ofNat 64 d) (64 / 8) := fun d hd => by
    rw [h.wr]; exact w_in hp (by omega_arith)
  obtain hleft : st.mem.readW (W s + BitVec.ofNat 64 64) 64 = BitVec.ofNat 64 (Cnt s) := by
    rw [h.kept.left, Nat.sub_zero]
  obtain hdesc : st.mem.readW (W s + BitVec.ofNat 64 56) 64 = Src s := by
    rw [h.kept.desc]; simp
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [splitEntry, gState, gLeft, gDst, gDesc]
    xrun [h11, hsi, hdx, w 104 (by decide), w 112 (by decide), r₈, r₄, r₇, h.kept.dst, hleft, hdesc,
      readW_writeW_off], ?_⟩
  obtain cs : ∀ d, 104 ≤ d → d + 8 ≤ 184 → (stR s).Contains (W s + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => by
    obtain e : W s + BitVec.ofNat 64 d = St s + BitVec.ofNat 64 (d - 104) := by
      rw [St, BitVec.add_assoc, ofNat_add_ofNat]; congr 2; omega_arith
    rw [e]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain fS : Frame [stR s] st.mem
      ((st.mem.writeW (W s + BitVec.ofNat 64 104) (Nn s)).writeW (W s + BitVec.ofNat 64 112) (s.gpr .rcx)) :=
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cs 104 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cs 112 (by decide) (by decide))
  refine ⟨by simp [gpr_setReg, gpr_arithFlags], by simp [gpr_setReg, gpr_arithFlags],
    by simp [gpr_setReg, gpr_arithFlags], by simp [gpr_setReg, gpr_arithFlags, imm],
    by simp [gpr_setReg, gpr_arithFlags, imm], by simp only [zf_arithFlags, gpr_setReg, ite_true, hz, reduceCtorEq,
      ↓reduceIte], by simp [gpr_setReg, gpr_arithFlags, h11], fun r hr => ?_,
    ⟨⟨?_, fun r hr => ?_, by simp [rd_arithFlags, rd_setReg, h.rd], by simp [wr_arithFlags, wr_setReg, h.wr], ?_, ?_,
      h.mx⟩,
      ?_, ?_⟩⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags, h.rsp]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags] <;>
      exact h.saved _ (by decide)
  · simp only [mem_setReg, mem_arithFlags]
    exact h.kept.frame fS fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact kpR_stR
  · simp only [mem_setReg, mem_arithFlags]
    exact h.frame.trans (fS.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨wkR s, by simp, stR_sub⟩)
  · simp (disch := decide) only [mem_setReg, mem_arithFlags, St, readW_writeW_off, Mem.readW_writeW_self64]
  · simp (disch := decide) only [mem_setReg, mem_arithFlags, St, Offset.add_add, readW_writeW_off,
      Mem.readW_writeW_self64]

/-- What the gathering of the slices after the first needs in registers,
and the first slice in `rax` and `rcx`. -/
def FirstRegs (s st : State) : Prop :=
  st.gpr .rax = fb s ∧ st.gpr .rcx = BitVec.ofNat 64 (fl s) ∧ st.gpr .r9 = BitVec.ofNat 64 (Cnt s - k0 s) ∧
    st.gpr .r10 = Src s + BitVec.ofNat 64 (16 * k0 s) ∧ st.gpr .rdi = Dst s + BitVec.ofNat 64 (fl s) ∧
    st.gpr .r11 = W s

/-- The first slice, and past it. -/
theorem splitFirst_ok (hc : Cnt s ≠ 0) {st : State} (h : Base s (AL s) 0 st)
    (h9 : st.gpr .r9 = BitVec.ofNat 64 (Cnt s)) (hdi : st.gpr .rdi = Dst s) (h10 : st.gpr .r10 = Src s)
    (h11 : st.gpr .r11 = W s) :
    WP isa (.block splitFirst) st fun st' => FirstRegs s st' ∧ (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧
      st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain hC : Cnt s < 2 ^ 64 := (stackArg s 1).isLt
  obtain d₀ := desc_in hp h (i := 0) (by omega_arith) (d := 0) (by decide)
  obtain d₈ := desc_in hp h (i := 0) (by omega_arith) (d := 8) (by decide)
  obtain v₀ : st.mem.readW (Src s + BitVec.ofNat 64 (16 * 0) + BitVec.ofNat 64 0) 64 = sb s 0 := by
    simpa using sb_eq hp h.frame (i := 0) (by omega_arith)
  obtain v₈ := sl_eq hp h.frame (i := 0) (by omega_arith)
  obtain e0 : Src s + BitVec.ofNat 64 (16 * 0) = Src s := by simp
  rw [e0] at d₀ d₈ v₀ v₈
  obtain hk : k0 s = 1 := by simp [k0, hc]
  obtain hfl : fl s = sl s 0 := by rw [fl_eq]; simp [hc]
  obtain hfb : fb s = sb s 0 := by simp [fb, hc]
  obtain hsub : BitVec.ofNat 64 (Cnt s) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (Cnt s - 1) :=
    ofNat_sub (by omega_arith) hC
  obtain i16 := imm_eq (n := 16) (by decide)
  obtain i1 := imm_eq (n := 1) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by simp only [splitFirst, imm]; xrun [h10, d₀, d₈, v₀, v₈, i16, i1], ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, hfb]
  · simp [gpr_setReg, gpr_arithFlags, hfl]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ↓reduceIte, h9, hk, imm, i1, ← hsub]
  · simp [gpr_setReg, gpr_arithFlags, h10, hk, imm, i16]
  · simp [gpr_setReg, gpr_arithFlags, hdi, hfl]
  · simp [gpr_setReg, gpr_arithFlags, h11]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- The entry of the path, and the first slice if there is one. -/
theorem splitHead_wp {st : State} (h : Base s (AL s) 0 st) (h11 : st.gpr .r11 = W s) (hsi : st.gpr .rsi = Nn s)
    (hdx : st.gpr .rdx = s.gpr .rcx) :
    WP isa (.seq (.block splitEntry) (.ite .e (.block []) (.block splitFirst))) st fun st' =>
      FirstRegs s st' ∧ CBase s st' := by
  refine WP.seq (WP.mono (splitEntry_ok hp h h11 hsi hdx) fun s₁ ⟨r9, di, r10, ax, cx, zf, r11, cs, C⟩ => ?_)
  refine WP.ite (decide (Cnt s = 0)) (by simp only [eval, zf]) (fun e => ?_) (fun e => ?_)
  · have hc : Cnt s = 0 := by simpa using e
    refine WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, r11⟩, C⟩
    · rw [ax]; simp [fb, hc]
    · rw [cx, fl_eq]; simp [hc]
    · rw [r9]; simp [k0, hc]
    · rw [r10]; simp [k0, hc]
    · rw [di, fl_eq]; simp [hc]
  · have hc : Cnt s ≠ 0 := by simpa using e
    refine WP.mono_mx (by decide) (splitFirst_ok hp hc C.toBase r9 di r10 r11) fun s₂ ⟨F, cs₂, m₂, rd₂, wr₂⟩ mxw => ⟨F, ?_⟩
    exact ⟨C.toBase.regs m₂ cs₂ rd₂ wr₂ mxw, by rw [m₂]; exact C.nonce, by rw [m₂]; exact C.nonceLen⟩

/-- The first slice kept, and the next descriptor in `r11`. -/
theorem splitKeep_ok {st : State} (F : FirstRegs s st) (C : CBase s st) :
    WP isa (.block splitKeep) st fun st' => PBase s st' ∧ st'.gpr .r9 = BitVec.ofNat 64 (Cnt s - k0 s) ∧
      st'.gpr .rdi = Dst s + BitVec.ofNat 64 (fl s) ∧ st'.gpr .r11 = Src s + BitVec.ofNat 64 (16 * k0 s) ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) := by
  obtain ⟨ax, cx, r9, r10, di, r11⟩ := F
  have hw := hp.w_w
  obtain w : ∀ d, d + 8 ≤ 184 → InRegions st.wr (W s + BitVec.ofNat 64 d) (64 / 8) := fun d hd => by
    rw [C.wr]; exact w_in hp (by omega_arith)
  apply WP.of_runBlock
  refine ⟨_, by simp only [splitKeep, gState]; xrun [r11, ax, cx, r10, w 120 (by decide), w 128 (by decide)], ?_⟩
  obtain cs : ∀ d, 104 ≤ d → d + 8 ≤ 184 → (stR s).Contains (W s + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => by
    obtain e : W s + BitVec.ofNat 64 d = St s + BitVec.ofNat 64 (d - 104) := by
      rw [St, BitVec.add_assoc, ofNat_add_ofNat]; congr 2; omega_arith
    rw [e]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain fS : Frame [stR s] st.mem
      ((st.mem.writeW (W s + BitVec.ofNat 64 120) (fb s)).writeW (W s + BitVec.ofNat 64 128)
        (BitVec.ofNat 64 (fl s))) :=
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cs 120 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cs 128 (by decide) (by decide))
  obtain eS : ∀ d, St s + BitVec.ofNat 64 d = W s + BitVec.ofNat 64 (104 + d) := fun d => by
    rw [St, BitVec.add_assoc, ofNat_add_ofNat]
  refine ⟨⟨⟨⟨?_, fun r hr => ?_, by simp [rd_setReg, C.rd], by simp [wr_setReg, C.wr], ?_, ?_, C.mx⟩, ?_, ?_⟩, ?_, ?_⟩,
    by simp [gpr_setReg, r9], by simp [gpr_setReg, di], by simp [gpr_setReg, r10], fun r hr => ?_⟩
  · simp [gpr_setReg, C.rsp]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg] <;> exact C.saved _ (by decide)
  · simp only [mem_setReg]
    exact C.kept.frame fS fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact kpR_stR
  · simp only [mem_setReg]
    exact C.frame.trans (fS.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨wkR s, by simp, stR_sub⟩)
  · simp only [mem_setReg]
    rw [show St s = W s + BitVec.ofNat 64 104 from rfl, readW_writeW_off _ (by decide) (by decide) (by decide),
      readW_writeW_off _ (by decide) (by decide) (by decide)]
    exact C.nonce
  · simp only [mem_setReg]
    rw [eS, readW_writeW_off _ (by decide) (by decide) (by decide),
      readW_writeW_off _ (by decide) (by decide) (by decide), ← eS]
    exact C.nonceLen
  · simp only [mem_setReg]
    rw [eS, readW_writeW_off _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · simp only [mem_setReg]
    rw [eS, Mem.readW_writeW_self64]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]

omit hp in
/-- The descriptors of the slices after the first are descriptors of the text. -/
theorem dsK_sub : Region.Sub ⟨Src s + BitVec.ofNat 64 (16 * k0 s), (Cnt s - k0 s) * 16⟩ (dsR s) := by
  have := k0_le s
  exact Offset.sub_base _ (by rw [Nat.sub_mul]; omega_arith)

/-- The output after the first slice. -/
theorem dK_sub : Region.Sub ⟨Dst s + BitVec.ofNat 64 (fl s), L s - fl s⟩ (dR s) := by
  have := fl_le hp
  exact Offset.sub_base _ (by omega_arith)

/-- The slices after the first, through a frame of the regions written and
the stack. -/
theorem listedK_eq {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) :
    Sig.listed 64 m .u8 (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s) =
      Sig.listed 64 s.mem .u8 (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s) :=
  Sig.listed_congr 64 .u8 _ _ fun a ha => hf a fun r hr hc => ds_apart hp r hr a
    ((dsK_sub (s := s)) a (by simpa [Sig.descRegion] using ha)) hc

/-- Their bytes, through such a frame. -/
theorem gatheredK_eq {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) :
    gathered 64 m (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s) =
      gathered 64 s.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s) := by
  obtain e₁ := gathered_k m (Src s) (k0_cases s)
  obtain e₂ := gathered_k s.mem (Src s) (k0_cases s)
  rw [pt_eq hp hf (Nat.le_refl _)] at e₁
  rw [pt_eq hp hf (k0_le s)] at e₁
  exact List.append_cancel_left (e₁.symm.trans e₂)

/-- What the gathering of the slices after the first needs, after `splitKeep`. -/
theorem splitGatherPre {st : State} (hL : L s - fl s < 2 ^ 63) (h : Base s (AL s) 0 st)
    (h9 : st.gpr .r9 = BitVec.ofNat 64 (Cnt s - k0 s)) (hdi : st.gpr .rdi = Dst s + BitVec.ofNat 64 (fl s))
    (h11 : st.gpr .r11 = Src s + BitVec.ofNat 64 (16 * k0 s)) :
    GatherPre st (Src s + BitVec.ofNat 64 (16 * k0 s)) (Dst s + BitVec.ofNat 64 (fl s)) (Cnt s - k0 s)
      (L s - fl s) := by
  obtain hl := listedK_eq hp h.frame
  obtain hk := k0_le s
  obtain hC : Cnt s < 2 ^ 64 := (stackArg s 1).isLt
  obtain hL' : L s < 2 ^ 64 := (stackArg s 3).isLt
  have ws := hp.w_ds
  obtain hfl := fl_le hp
  obtain hdw : (Src s + BitVec.ofNat 64 (16 * k0 s)).toNat + (Cnt s - k0 s) * 16 ≤ 2 ^ 64 := by
    by_cases hz : Cnt s - k0 s = 0
    · rw [hz]; have := (Src s + BitVec.ofNat 64 (16 * k0 s)).isLt; omega_arith
    · have : (Src s + BitVec.ofNat 64 (16 * k0 s)).toNat = (Src s).toNat + 16 * k0 s := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k0 s) (by omega_arith),
          Nat.mod_eq_of_lt (by omega_arith)]
      rw [this, Nat.sub_mul]; omega_arith
  obtain cD : Covers [dsR s] (st.rd ++ st.wr) := by
    rw [h.rd, h.wr]; exact covers_left' (covers_of_mem (by rw [hp.rd]; simp))
  obtain cO : Covers [dR s] st.wr := by rw [h.wr, hp.wr]; exact covers_of_mem (by simp)
  refine ⟨h11, h9, hdi, by omega_arith, hdw, hL, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gatheredLen, hl, ← gatheredLen, ← hp.glen]
    have := (pt_split s).2
    simp only [gl] at this ⊢
    omega_arith
  · refine Covers.trans (Covers.of_sub fun r hr => ?_) cD
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨dsR s, List.mem_singleton_self _, 16 * k0 s, rfl, by simp only [dsR]; rw [Nat.sub_mul]; omega_arith⟩
  · rw [hl]
    intro r hr
    rw [h.rd, h.wr]
    exact covers_left' (covers_of_mem (by rw [hp.rd]; simp [listed_k0 s r hr]))
  · exact covers_off cO (by omega_arith) (by omega_arith)
  · exact (hp.ds_d.sub_left ((dsK_sub (s := s)))).sub_right (dK_sub hp)
  · rw [hl]; exact fun r hr => (hp.ls r (listed_k0 s r hr)).1.sub_right (dK_sub hp)

/-- `PBase`, with the slices after the first gathered in the output after it. -/
structure SPBase (s : State) (st : State) : Prop extends PBase s st where
  out : bytesAt st.mem (Dst s + BitVec.ofNat 64 (fl s)) (L s - fl s) =
    gathered 64 s.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s)

/-- After the gathering: the slices after the first in the output after it,
and the rest as it was. -/
theorem split_after {st st' : State} (h : PBase s st)
    (hm : st'.mem = WriteBytes.writeBytes st.mem (Dst s + BitVec.ofNat 64 (fl s))
      (gathered 64 st.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s))) (hk : GKeeps st st')
    (hmx : st'.mxcsr = st.mxcsr) : SPBase s st' := by
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have hg := gatheredK_eq hp h.frame
  have hlen : (gathered 64 s.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s)).length = L s - fl s := by
    rw [Proof.Gcm.length_gathered]
    have := (pt_split s).2
    have := hp.glen
    simp only [gl] at *
    omega_arith
  rw [hg] at hm
  have fD : Frame [⟨Dst s + BitVec.ofNat 64 (fl s), L s - fl s⟩] st.mem st'.mem := frame_of hm (by rw [hlen])
  have ns : ∀ r ∉ gatherRegs, st'.gpr r = st.gpr r := hk.gpr
  have sd : (stR s).Disjoint ⟨Dst s + BitVec.ofNat 64 (fl s), L s - fl s⟩ :=
    (hp.d_w.symm.sub_left stR_sub).sub_right (dK_sub hp)
  have hcs : ∀ r ∈ calleeSaved, r ∉ gatherRegs := by decide
  have dS : ∀ d, d + 8 ≤ 80 → (stR s).Contains (St s + BitVec.ofNat 64 d) (64 / 8) := fun d hd =>
    Offset.contains_base (St s) (d := d) (n := 8) (k := 80) hd (by omega_arith)
  have dS1 : ∀ r ∈ [(⟨Dst s + BitVec.ofNat 64 (fl s), L s - fl s⟩ : Region)], (stR s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact sd
  have rS : ∀ d, d + 8 ≤ 80 → st'.mem.readW (St s + BitVec.ofNat 64 d) 64 = st.mem.readW (St s + BitVec.ofNat 64 d) 64 :=
    fun d hd => fD.readW (dS d hd) dS1 (by decide)
  have e0 : St s + BitVec.ofNat 64 0 = St s := BitVec.add_zero _
  refine ⟨⟨⟨⟨by rw [ns .rsp (by decide), h.rsp], fun r hr => by rw [ns r (hcs r hr), h.saved r hr],
    hk.rd.trans h.rd, hk.wr.trans h.wr, ?_, ?_, hmx.trans h.mx⟩, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact h.kept.frame fD fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hp.d_w.symm.sub_left kpR_sub).sub_right (dK_sub hp)
  · exact h.frame.trans (fD.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s, by simp, dK_sub hp⟩)
  · have := rS 0 (by decide); rw [e0] at this; rw [this]; exact h.nonce
  · rw [rS 8 (by decide)]; exact h.nonceLen
  · rw [rS 16 (by decide)]; exact h.first
  · rw [rS 24 (by decide)]; exact h.firstLen
  · rw [hm, ← hlen]; exact bytesAt_writeBytes_self _ _ _ (by omega_arith)

/-- The arguments of `vg_aes_gcm_seal_split(ctx, rounds, nonce, nonce_len,
aad, aad_len, src, src_len, dst, len, tag)` but `ctx` and `rounds`, with
`tag`, `len`, `dst`, `src_len` and `src` to push. -/
theorem splitArgs_ok {st : State} (h : SPBase s st) :
    WP isa (.block splitArgs) st fun st' =>
      st'.gpr .rdx = Nn s ∧ st'.gpr .rcx = s.gpr .rcx ∧ st'.gpr .r8 = Ad s ∧ st'.gpr .r9 = AL s ∧
      st'.gpr .rax = Tg s ∧ st'.gpr .r10 = stackArg s 3 ∧ st'.gpr .rdi = BitVec.ofNat 64 (fl s) ∧
      st'.gpr .rsi = fb s ∧ st'.gpr .r11 = Dst s ∧ (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧
      st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have B := h.toBase
  obtain ⟨a₅, e₅⟩ := B.w hp
  obtain r₂ := B.slot hp (d := 16) (by decide)
  obtain r₃ := B.slot hp (d := 24) (by decide)
  obtain r₄ := B.slot hp (d := 32) (by decide)
  obtain r₅ := B.slot hp (d := 40) (by decide)
  obtain r₆ := B.slot hp (d := 48) (by decide)
  obtain r₁₃ := B.slot hp (d := 104) (by decide)
  obtain r₁₄ := B.slot hp (d := 112) (by decide)
  obtain r₁₅ := B.slot hp (d := 120) (by decide)
  obtain r₁₆ := B.slot hp (d := 128) (by decide)
  have n₀ : st.mem.readW (W s + BitVec.ofNat 64 104) 64 = Nn s := h.nonce
  obtain n₁ : st.mem.readW (W s + BitVec.ofNat 64 112) 64 = s.gpr .rcx := by
    rw [← h.nonceLen, St, Offset.add_add]
  obtain n₂ : st.mem.readW (W s + BitVec.ofNat 64 120) 64 = fb s := by
    rw [← h.first, St, Offset.add_add]
  obtain n₃ : st.mem.readW (W s + BitVec.ofNat 64 128) 64 = BitVec.ofNat 64 (fl s) := by
    rw [← h.firstLen, St, Offset.add_add]
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [splitArgs, gState, gAad, gAlen, gTag, gLen, gDst]
    xrun [a₅, e₅, r₂, r₃, r₄, r₅, r₆, r₁₃, r₁₄, r₁₅, r₁₆, n₀, n₁, n₂, n₃, B.kept.aad,
      B.kept.alen, B.kept.tag, B.kept.len, B.kept.dst], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [gpr_setReg]; done)
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  all_goals simp [mem_setReg, rd_setReg, wr_setReg]

end

end VG.Proof.AesGcm.X86_64.Gather

end

end

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: the call of `vg_aes_gcm_seal_split`

Untrusted: everything here is checked by Lean. The call of
`vg_aes_gcm_seal_split` on the first slice where it is and the slices after
it gathered in the output after it, with `src`, `src_len`, `dst`, `len` and
`tag` pushed for it and `ctx` and `rounds` loaded from `work` above them
(`splitCall_ok`): what it needs, from the layout of the entry state `s`
(`splitPre_of`), and that what it leaves is what `vg_aes_gcm_seal_gather`
must (`Done`); and the whole path of such a text (`copySplit_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gathered)
open VG.Proof.AesGcm.X86_64.StreamTo (covers_cons' covers_nil' sub_add_ofNat stackArg_entry)

section
variable (s : State)

/-- The first slice (empty, at the descriptors, if there is none). -/
abbrev fR : Region := ⟨fb s, fl s⟩

/-- What the call reads. -/
abbrev splitRd (M : CtxMode) : List Region := [kR M s, nR s, aR s, fR s, ⟨SP s - BitVec.ofNat 64 40, 40⟩]

end

/-- A region of the caller's is one of those with one more pushed. -/
theorem in_cons {rd wr : List Region} {x : Region} {a : Addr} {n : Nat} (h : InRegions (rd ++ wr) a n) :
    InRegions (rd ++ x :: wr) a n := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, ?_, hc⟩
  simp only [List.mem_append, List.mem_cons] at hr ⊢
  rcases hr with hr | hr
  exacts [Or.inl hr, Or.inr (Or.inr hr)]

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

omit hp in
/-- What is disjoint from every slice is disjoint from the first. -/
theorem fR_disj {r : Region} (h : ∀ q ∈ lsR s, q.Disjoint r) : (fR s).Disjoint r := by
  by_cases hc : Cnt s = 0
  · have e : (fR s).len = 0 := by show fl s = 0; simp only [fl_eq, hc, ↓reduceIte]
    intro a ha _
    unfold Region.Contains at ha
    omega_arith
  · have e : fR s = ⟨sb s 0, sl s 0⟩ := by
      show (⟨fb s, fl s⟩ : Region) = _
      simp only [fl_eq, fb, hc, ↓reduceIte]
    rw [e]; exact h _ (slice_mem s (by omega_arith))

theorem fR_apart : Apart (fR s) s :=
  apart_of (fR_disj fun q hq => (hp.ls q hq).1) (fR_disj fun q hq => (hp.ls q hq).2.1)
    (fR_disj fun q hq => (hp.ls q hq).2.2) (fR_disj fun q hq => (hp.b_ls q hq).symm).symm

theorem fR_wrap : (fb s).toNat + fl s ≤ 2 ^ 64 := by
  by_cases hc : Cnt s = 0
  · have e : fl s = 0 := by simp only [fl_eq, hc, ↓reduceIte]
    rw [e]; exact Nat.le_of_lt (fb s).isLt
  · have e₁ : fl s = sl s 0 := by simp only [fl_eq, hc, ↓reduceIte]
    obtain e₂ : fb s = sb s 0 := by simp only [fb, hc, ↓reduceIte]
    have := hp.w_ls _ (slice_mem s (i := 0) (by omega_arith))
    rw [e₁, e₂]; exact this

/-- The caller may read the first slice. -/
theorem fR_covers : Covers [fR s] s.rd := by
  by_cases hc : Cnt s = 0
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    obtain e : fl s = 0 := by simp only [fl_eq, hc, ↓reduceIte]
    refine ⟨dsR s, by rw [hp.rd]; simp, 0, ?_, by simp only [e]; omega_arith⟩
    show fb s = Src s + BitVec.ofNat 64 0
    simp only [fb, hc, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  · have e : fR s = ⟨sb s 0, sl s 0⟩ := by
      show (⟨fb s, fl s⟩ : Region) = _
      simp only [fl_eq, fb, hc, ↓reduceIte]
    rw [e, hp.rd]
    exact covers_of_mem (by simp [slice_mem s (i := 0) (by omega_arith)])

/-- What the call of `vg_aes_gcm_seal_split` needs. -/
theorem splitPre_of {u : State}
    (hrsp : u.gpr .rsp = SP s - BitVec.ofNat 64 48) (hrd : u.rd = splitRd s M) (hwr : u.wr = sealWr s)
    (h_di : u.gpr .rdi = K s) (h_si : u.gpr .rsi = s.gpr .rsi) (h_dx : u.gpr .rdx = Nn s)
    (h_cx : u.gpr .rcx = s.gpr .rcx) (h_8 : u.gpr .r8 = Ad s) (h_9 : u.gpr .r9 = AL s)
    (a0 : stackArg u 0 = fb s) (a1 : stackArg u 1 = BitVec.ofNat 64 (fl s)) (a2 : stackArg u 2 = Dst s)
    (a3 : stackArg u 3 = stackArg s 3) (a4 : stackArg u 4 = Tg s) (hok : M.ok u.mem (K s)) :
    (splitK M).pre u := by
  have wsp := hp.w_sp
  have wsp' := hp.w_sp'
  obtain hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  obtain hfl := fl_le hp
  obtain hflN : (BitVec.ofNat 64 (fl s)).toNat = fl s := toNat_ofNat_of_lt (by omega_arith)
  obtain hargs : (Proof.AesGcm.args u 5) = ⟨SP s - BitVec.ofNat 64 40, 40⟩ := by
    simp only [Proof.AesGcm.args, stackArgAddr, hrsp]
    rw [sub_add_ofNat _ (by decide)]
  obtain hret : (Proof.AesGcm.ret u) = ⟨SP s - BitVec.ofNat 64 48, 8⟩ := by simp only [Proof.AesGcm.ret, hrsp]
  obtain hstk : below (SP s - BitVec.ofNat 64 48) 2672 = ⟨SP s - BitVec.ofNat 64 2720, 2672⟩ := by
    simp only [below]
    rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
  obtain tA : Region.Sub ⟨SP s - BitVec.ofNat 64 40, 40⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  obtain tR' : Region.Sub ⟨SP s - BitVec.ofNat 64 48, 8⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  obtain tS : Region.Sub ⟨SP s - BitVec.ofNat 64 2720, 2672⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  obtain hsp48 : (SP s - BitVec.ofNat 64 48).toNat = (SP s).toNat - 48 := toNat_sub_ofNat (by omega_arith)
  obtain hsp40 : (SP s - BitVec.ofNat 64 40).toNat = (SP s).toNat - 40 := toNat_sub_ofNat (by omega_arith)
  obtain hsp2720 : (SP s - BitVec.ofNat 64 2720).toNat = (SP s).toNat - 2720 := toNat_sub_ofNat (by omega_arith)
  obtain d₁ : (⟨SP s - BitVec.ofNat 64 48, 8⟩ : Region).Disjoint ⟨SP s - BitVec.ofNat 64 40, 40⟩ :=
    Offset.disjoint_of_le (by simp only [hsp48, hsp40]; omega_arith) (by simp only [hsp40]; omega_arith)
  obtain d₂ : (⟨SP s - BitVec.ofNat 64 2720, 2672⟩ : Region).Disjoint ⟨SP s - BitVec.ofNat 64 40, 40⟩ :=
    Offset.disjoint_of_le (by simp only [hsp2720, hsp40]; omega_arith) (by simp only [hsp40]; omega_arith)
  obtain bF : (tR s).Disjoint (fR s) := (fR_disj fun q hq => (hp.b_ls q hq).symm).symm
  simp only [splitK, splitPreK, Proof.AesGcm.arg, hargs, hret, hrd, hwr, h_di, h_si, h_dx, h_cx, h_8, h_9, a0,
    a1, a2, a3, a4, hflN, hrsp, Proof.AesGcm.rounds, hstk]
  exact ⟨trivial, trivial, hp.k_d, hp.k_t, hp.n_d, hp.n_t, hp.a_d, hp.a_t,
    fR_disj fun q hq => (hp.ls q hq).1, fR_disj fun q hq => (hp.ls q hq).2.1, hp.d_t,
    hp.b_d.symm.sub_right tA, hp.b_t.symm.sub_right tA, hp.b_k.sub_left tR', hp.b_n.sub_left tR',
    hp.b_a.sub_left tR', bF.sub_left tR', hp.b_d.sub_left tR', hp.b_t.sub_left tR', d₁, hp.b_k.sub_left tS,
    hp.b_n.sub_left tS, hp.b_a.sub_left tS, bF.sub_left tS, hp.b_d.sub_left tS, hp.b_t.sub_left tS, d₂, hp.w_k,
    hp.w_n, hp.w_ad, fR_wrap hp, hp.w_d, hp.w_t, by rw [hsp48]; omega_arith, by rw [hsp48]; omega_arith, hp.rounds, hfl,
    hok⟩

/-- What the call of `vg_aes_gcm_seal_split` needs of the state it is made
from: the stack, the callee-saved registers and the regions as on entry, the
memory as on entry but where the code writes, `ctx` and `rounds` in `work`
(for `splitCtx`), and the slices after the first in the output after it. -/
structure SCBase (s st : State) : Prop where
  rsp : st.gpr .rsp = SP s
  saved : ∀ r ∈ calleeSaved, st.gpr r = s.gpr r
  rd : st.rd = s.rd
  wr : st.wr = s.wr
  frame : Frame (wR s ++ [tR s]) s.mem st.mem
  ctx : st.mem.readW (W s + BitVec.ofNat 64 0) 64 = K s
  rounds : st.mem.readW (W s + BitVec.ofNat 64 8) 64 = s.gpr .rsi
  out : bytesAt st.mem (Dst s + BitVec.ofNat 64 (fl s)) (L s - fl s) =
    gathered 64 s.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s)
  mx : st.mxcsr = s.mxcsr

omit hp in
theorem SPBase.toSC {st : State} (h : SPBase s st) : SCBase s st :=
  ⟨h.rsp, h.saved, h.rd, h.wr, h.frame, h.kept.ctx, h.kept.rounds, h.out, h.mx⟩

/-- `work`, above the five arguments pushed. -/
theorem pushedW {st : State} (h : SCBase s st) {p : State}
    (hP : p.gpr .rsp = SP s - BitVec.ofNat 64 40) (hrd : p.rd = st.rd)
    (hwr : p.wr = ⟨SP s - BitVec.ofNat 64 40, 40⟩ :: st.wr)
    (hf : Frame [⟨SP s - BitVec.ofNat 64 40, 40⟩] st.mem p.mem) :
    InRegions (p.rd ++ p.wr) (p.gpr .rsp + BitVec.ofNat 64 88) 8 ∧
      p.mem.readW (p.gpr .rsp + BitVec.ofNat 64 88) 64 = W s := by
  obtain e88 : p.gpr .rsp + BitVec.ofNat 64 88 = SP s + BitVec.ofNat 64 48 := by
    rw [hP, show (BitVec.ofNat 64 88 : Addr) = BitVec.ofNat 64 40 + BitVec.ofNat 64 48 from rfl,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  obtain fP : Frame (wR s ++ [tR s]) s.mem p.mem := h.frame.trans (frame_stk (s := s) (by decide) (by decide) hf)
  refine ⟨?_, by rw [e88]; exact keep_w hp fP⟩
  rw [e88, hrd, hwr, h.rd, h.wr]; exact in_cons (a_in hp (i := 5) (by decide))

/-- `ctx` and `rounds`, from `work` above the five arguments pushed. -/
theorem splitCtx_ok {st : State} (h : SCBase s st) {p : State}
    (hP : p.gpr .rsp = SP s - BitVec.ofNat 64 40) (hrd : p.rd = st.rd)
    (hwr : p.wr = ⟨SP s - BitVec.ofNat 64 40, 40⟩ :: st.wr)
    (hf : Frame [⟨SP s - BitVec.ofNat 64 40, 40⟩] st.mem p.mem) :
    WP isa (.block splitCtx) p fun q => q.gpr .rdi = K s ∧ q.gpr .rsi = s.gpr .rsi ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r11 → q.gpr r = p.gpr r) ∧ q.mem = p.mem ∧ q.rd = p.rd ∧
      q.wr = p.wr := by
  obtain ⟨a₈, e₈⟩ := pushedW hp h hP hrd hwr hf
  obtain hd : ∀ r ∈ [(⟨SP s - BitVec.ofNat 64 40, 40⟩ : Region)], (kpR s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.b_w.symm.sub_left kpR_sub).sub_right (stk_sub (s := s) (by decide) (by decide))
  obtain k : ∀ d, d + 8 ≤ 104 → p.mem.readW (W s + BitVec.ofNat 64 d) 64 = st.mem.readW (W s + BitVec.ofNat 64 d) 64 :=
    fun d hd' => hf.readW (Offset.contains_base _ hd' (by omega_arith)) hd (by decide)
  obtain kc : p.mem.readW (W s + BitVec.ofNat 64 0) 64 = K s := by rw [k 0 (by decide)]; exact h.ctx
  obtain kr : p.mem.readW (W s + BitVec.ofNat 64 8) 64 = s.gpr .rsi := by rw [k 8 (by decide)]; exact h.rounds
  obtain r₀ : InRegions (p.rd ++ p.wr) (W s + BitVec.ofNat 64 0) 8 := by
    rw [hrd, hwr, h.rd, h.wr]; exact in_cons (w_in' hp (by decide))
  obtain r₁ : InRegions (p.rd ++ p.wr) (W s + BitVec.ofNat 64 8) 8 := by
    rw [hrd, hwr, h.rd, h.wr]; exact in_cons (w_in' hp (by decide))
  apply WP.of_runBlock
  refine ⟨_, by simp only [splitCtx, gCtx, gRounds]; xrun [a₈, e₈, r₀, r₁, kc, kr], ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], fun r h₁ h₂ h₃ => by simp [gpr_setReg, h₁, h₂, h₃], ?_, ?_, ?_⟩
  all_goals simp [mem_setReg, rd_setReg, wr_setReg]

/-- The registers the call of `vg_aes_gcm_seal_split` is entered with. -/
structure SplitRegs (s st : State) : Prop where
  rdx : st.gpr .rdx = Nn s
  rcx : st.gpr .rcx = s.gpr .rcx
  r8 : st.gpr .r8 = Ad s
  r9 : st.gpr .r9 = AL s
  rax : st.gpr .rax = Tg s
  r10 : st.gpr .r10 = stackArg s 3
  rdi : st.gpr .rdi = BitVec.ofNat 64 (fl s)
  rsi : st.gpr .rsi = fb s
  r11 : st.gpr .r11 = Dst s

/-- The state the call of `vg_aes_gcm_seal_split` is made from, after the
push and `splitCtx`. -/
structure SplitQ (s st q : State) : Prop where
  di : q.gpr .rdi = K s
  si : q.gpr .rsi = s.gpr .rsi
  g : ∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r11 → q.gpr r = (pushed [.rax, .r10, .r11, .rdi, .rsi] st).gpr r
  m : q.mem = (pushed [.rax, .r10, .r11, .rdi, .rsi] st).mem
  rd : q.rd = (pushed [.rax, .r10, .r11, .rdi, .rsi] st).rd
  wr : q.wr = (pushed [.rax, .r10, .r11, .rdi, .rsi] st).wr
  mx : q.mxcsr = st.mxcsr

/-- What the call of `vg_aes_gcm_seal_split` needs, after the push and
`splitCtx`, and its stack arguments. -/
theorem splitCallEntry {st : State} (h : SCBase s st) (g : SplitRegs s st) {q : State} (Q : SplitQ s st q) :
    (splitK M).pre (q.callEntry.withRegions (splitRd s M) (sealWr s)) ∧
      Covers (splitRd s M ++ sealWr s) (q.rd ++ q.wr) ∧ Covers (sealWr s) q.wr ∧
      stackArg (q.callEntry.withRegions (splitRd s M) (sealWr s)) 0 = fb s ∧
      stackArg (q.callEntry.withRegions (splitRd s M) (sealWr s)) 1 = BitVec.ofNat 64 (fl s) ∧
      stackArg (q.callEntry.withRegions (splitRd s M) (sealWr s)) 2 = Dst s ∧
      stackArg (q.callEntry.withRegions (splitRd s M) (sealWr s)) 3 = stackArg s 3 ∧
      stackArg (q.callEntry.withRegions (splitRd s M) (sealWr s)) 4 = Tg s := by
  obtain ⟨q_di, q_si, q_g, q_m, q_rd, q_wr⟩ := Q
  obtain hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  obtain hfl := fl_le hp
  obtain hflN : (BitVec.ofNat 64 (fl s)).toNat = fl s := toNat_ofNat_of_lt (by omega_arith)
  have wsp := hp.w_sp
  have wsp' := hp.w_sp'
  have hsp := h.rsp
  obtain hn8 : 8 * [Reg.rax, .r10, .r11, .rdi, .rsi].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax, .r10, .r11, .rdi, .rsi] (by decide) hn8
  obtain hpj' : ∀ j (hj : j < 5), (pushed [.rax, .r10, .r11, .rdi, .rsi] st).mem.readW
      (SP s - BitVec.ofNat 64 (8 * (j + 1))) 64 = st.gpr ([Reg.rax, .r10, .r11, .rdi, .rsi][j]'hj) :=
    fun j hj => by rw [← hsp]; exact hpj j hj
  obtain hP : (pushed [.rax, .r10, .r11, .rdi, .rsi] st).gpr .rsp = SP s - BitVec.ofNat 64 40 := by
    rw [pushed_rsp, hsp]; rfl
  obtain hpf' : Frame [⟨SP s - BitVec.ofNat 64 40, 40⟩] st.mem (pushed [.rax, .r10, .r11, .rdi, .rsi] st).mem := by
    rw [hsp] at hpf; exact hpf
  obtain hPw : (pushed [.rax, .r10, .r11, .rdi, .rsi] st).wr = ⟨SP s - BitVec.ofNat 64 40, 40⟩ :: st.wr := by
    rw [pushed_wr, hsp]; rfl
  obtain qsp : q.gpr .rsp = SP s - BitVec.ofNat 64 40 := by
    rw [q_g _ (by decide) (by decide) (by decide), hP]
  obtain hE : Frame [⟨SP s - BitVec.ofNat 64 48, 8⟩] q.mem q.callEntry.mem := by
    have := callEntry_frame q
    rw [qsp] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  obtain hE' : Frame [⟨SP s - BitVec.ofNat 64 48, 8⟩] (pushed [.rax, .r10, .r11, .rdi, .rsi] st).mem
      q.callEntry.mem := by rw [← q_m]; exact hE
  obtain fS : Frame (wR s ++ [tR s]) st.mem q.callEntry.mem :=
    (frame_stk (s := s) (by decide) (by decide) hpf').trans (frame_stk (s := s) (by decide) (by decide) hE')
  obtain fU : Frame (wR s ++ [tR s]) s.mem q.callEntry.mem := h.frame.trans fS
  obtain gU : ∀ r, r ≠ .rsp → (q.callEntry.withRegions (splitRd s M) (sealWr s)).gpr r = q.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  obtain gS : ∀ r, r ≠ .rsp → r ≠ .rdi → r ≠ .rsi → r ≠ .r11 →
      (q.callEntry.withRegions (splitRd s M) (sealWr s)).gpr r = st.gpr r :=
    fun r h₀ h₁ h₂ h₃ => by rw [gU r h₀, q_g r h₁ h₂ h₃, pushed_gpr _ _ h₀]
  obtain hU : (q.callEntry.withRegions (splitRd s M) (sealWr s)).gpr .rsp = SP s - BitVec.ofNat 64 48 := by
    rw [State.withRegions_gpr, State.callEntry_rsp, qsp, ← Offset.sub_add_eq]; rfl
  obtain hQsp8 : 8 ≤ (SP s - BitVec.ofNat 64 40).toNat := by rw [toNat_sub_ofNat (by omega_arith)]; omega_arith
  obtain hQt : (SP s - BitVec.ofNat 64 40).toNat = (SP s).toNat - 40 := toNat_sub_ofNat (by omega_arith)
  obtain ea : ∀ j, j < 5 → stackArg (q.callEntry.withRegions (splitRd s M) (sealWr s)) j =
      (pushed [.rax, .r10, .r11, .rdi, .rsi] st).mem.readW (SP s - BitVec.ofNat 64 40 + BitVec.ofNat 64 (8 * j)) 64 :=
    fun j hj => by rw [← q_m]; exact stackArg_entry qsp hQsp8 _ _ (by rw [hQt]; omega_arith)
  obtain a0 := ea 0 (by decide)
  obtain a1 := ea 1 (by decide)
  obtain a2 := ea 2 (by decide)
  obtain a3 := ea 3 (by decide)
  obtain a4 := ea 4 (by decide)
  rw [show SP s - BitVec.ofNat 64 40 + BitVec.ofNat 64 (8 * 0) = SP s - BitVec.ofNat 64 (8 * (4 + 1)) from
    by simp, hpj' 4 (by decide)] at a0
  rw [show SP s - BitVec.ofNat 64 40 + BitVec.ofNat 64 (8 * 1) = SP s - BitVec.ofNat 64 (8 * (3 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 3 (by decide)] at a1
  rw [show SP s - BitVec.ofNat 64 40 + BitVec.ofNat 64 (8 * 2) = SP s - BitVec.ofNat 64 (8 * (2 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 2 (by decide)] at a2
  rw [show SP s - BitVec.ofNat 64 40 + BitVec.ofNat 64 (8 * 3) = SP s - BitVec.ofNat 64 (8 * (1 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 1 (by decide)] at a3
  rw [show SP s - BitVec.ofNat 64 40 + BitVec.ofNat 64 (8 * 4) = SP s - BitVec.ofNat 64 (8 * (0 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 0 (by decide)] at a4
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at a0 a1 a2 a3 a4
  rw [g.rsi] at a0
  rw [g.rdi] at a1
  rw [g.r11] at a2
  rw [g.r10] at a3
  rw [g.rax] at a4
  obtain hok : M.ok (q.callEntry.withRegions (splitRd s M) (sealWr s)).mem (K s) := by
    rw [State.withRegions_mem]
    exact M.frame fU (k_apart hp) hp.w_k hp.ok
  obtain hpre := splitPre_of hp hU rfl rfl (by rw [gU _ (by decide), q_di]) (by rw [gU _ (by decide), q_si])
    (by rw [gS _ (by decide) (by decide) (by decide) (by decide), g.rdx])
    (by rw [gS _ (by decide) (by decide) (by decide) (by decide), g.rcx])
    (by rw [gS _ (by decide) (by decide) (by decide) (by decide), g.r8])
    (by rw [gS _ (by decide) (by decide) (by decide) (by decide), g.r9]) a0 a1 a2 a3 a4 hok
  obtain hR : q.rd = s.rd := by rw [q_rd, pushed_rd, h.rd]
  obtain hW : q.wr = ⟨SP s - BitVec.ofNat 64 40, 40⟩ :: wR s := by rw [q_wr, hPw, h.wr, hp.wr]
  obtain cF : Covers [fR s] (q.rd ++ q.wr) := by rw [hR]; exact Covers.left (fR_covers hp)
  obtain cw : Covers (sealWr s) q.wr := by
    rw [hW]
    exact covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_of_mem (by simp)) covers_nil')
  obtain cr : Covers (splitRd s M ++ sealWr s) (q.rd ++ q.wr) := by
    rw [hR, hW] at cF ⊢
    rw [hp.rd] at cF ⊢
    exact covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_of_mem (by simp))
      (covers_cons' (covers_of_mem (by simp)) (covers_cons' cF (covers_cons' (covers_of_mem (by simp))
        (covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_of_mem (by simp)) covers_nil'))))))
  exact ⟨hpre, cr, cw, a0, a1, a2, a3, a4⟩

/-- The call of `vg_aes_gcm_seal_split` on the first slice where it is and
those after it gathered in the output after it, with `src`, `src_len`,
`dst`, `len` and `tag` pushed for it: what `vg_aes_gcm_seal_gather` must
leave. -/
theorem splitCall_ok (S : SplitFn M) {st : State} (h : SCBase s st) (g : SplitRegs s st) :
    WP isa (.frame (.push [.rax, .r10, .r11, .rdi, .rsi]) (.seq (.block splitCtx) (.call S.fn.name S.fn.code))
      (.pop .rax 5)) st (Done s) := by
  obtain hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  obtain hfl := fl_le hp
  obtain hflN : (BitVec.ofNat 64 (fl s)).toNat = fl s := toNat_ofNat_of_lt (by omega_arith)
  have wsp := hp.w_sp
  have wsp' := hp.w_sp'
  have hsp := h.rsp
  obtain hn8 : 8 * [Reg.rax, .r10, .r11, .rdi, .rsi].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax, .r10, .r11, .rdi, .rsi] (by decide) hn8
  obtain hpj' : ∀ j (hj : j < 5), (pushed [.rax, .r10, .r11, .rdi, .rsi] st).mem.readW
      (SP s - BitVec.ofNat 64 (8 * (j + 1))) 64 = st.gpr ([Reg.rax, .r10, .r11, .rdi, .rsi][j]'hj) :=
    fun j hj => by rw [← hsp]; exact hpj j hj
  obtain hP : (pushed [.rax, .r10, .r11, .rdi, .rsi] st).gpr .rsp = SP s - BitVec.ofNat 64 40 := by
    rw [pushed_rsp, hsp]; rfl
  obtain hpf' : Frame [⟨SP s - BitVec.ofNat 64 40, 40⟩] st.mem (pushed [.rax, .r10, .r11, .rdi, .rsi] st).mem := by
    rw [hsp] at hpf; exact hpf
  obtain hPw : (pushed [.rax, .r10, .r11, .rdi, .rsi] st).wr = ⟨SP s - BitVec.ofNat 64 40, 40⟩ :: st.wr := by
    rw [pushed_wr, hsp]; rfl
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.seq (WP.mono_mx (by decide)
    (splitCtx_ok hp h hP (pushed_rd _ _) hPw hpf') fun q ⟨q_di, q_si, q_g, q_m, q_rd, q_wr⟩ q_mx => ?_))
  obtain ⟨hpre, cr, cw, a0, a1, a2, a3, a4⟩ := splitCallEntry hp h g
    ⟨q_di, q_si, q_g, q_m, q_rd, q_wr, q_mx.trans (pushed_mxcsr _ _)⟩
  obtain qsp : q.gpr .rsp = SP s - BitVec.ofNat 64 40 := by
    rw [q_g _ (by decide) (by decide) (by decide), hP]
  obtain hE : Frame [⟨SP s - BitVec.ofNat 64 48, 8⟩] q.mem q.callEntry.mem := by
    have := callEntry_frame q
    rw [qsp] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  obtain hE' : Frame [⟨SP s - BitVec.ofNat 64 48, 8⟩] (pushed [.rax, .r10, .r11, .rdi, .rsi] st).mem
      q.callEntry.mem := by rw [← q_m]; exact hE
  obtain fS : Frame (wR s ++ [tR s]) st.mem q.callEntry.mem :=
    (frame_stk (s := s) (by decide) (by decide) hpf').trans (frame_stk (s := s) (by decide) (by decide) hE')
  obtain fU : Frame (wR s ++ [tR s]) s.mem q.callEntry.mem := h.frame.trans fS
  obtain gU : ∀ r, r ≠ .rsp → (q.callEntry.withRegions (splitRd s M) (sealWr s)).gpr r = q.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  obtain gS : ∀ r, r ≠ .rsp → r ≠ .rdi → r ≠ .rsi → r ≠ .r11 →
      (q.callEntry.withRegions (splitRd s M) (sealWr s)).gpr r = st.gpr r :=
    fun r h₀ h₁ h₂ h₃ => by rw [gU r h₀, q_g r h₁ h₂ h₃, pushed_gpr _ _ h₀]
  refine WP.call_sp_mx (k := splitK M) S.ok S.sp (by have := S.xd; omega_arith) hpre cr cw
    fun s' hrd' hwr' hcs hfr _ ⟨s₂, hm₂, _, hpost⟩ _ => ?_
  obtain r₃ := hcs _ (by decide : Reg.rsp ∈ calleeSaved)
  -- The first slice, and those after it in the output, which the push and the
  -- return address leave as they were.
  obtain eF : bytesAt q.callEntry.mem (fb s) (fl s) = pt s (k0 s) := by
    rw [pt_k0]; exact bytesAt_frame fU (fR_apart hp) (by have := fR_wrap hp; omega_arith)
  obtain fS2 : Frame [⟨SP s - BitVec.ofNat 64 40, 40⟩, ⟨SP s - BitVec.ofNat 64 48, 8⟩] st.mem q.callEntry.mem :=
    (hpf'.sub fun r hr => ⟨r, by simp at hr ⊢; exact Or.inl hr, fun _ h => h⟩).trans
      (hE'.sub fun r hr => ⟨r, by simp at hr ⊢; exact Or.inr hr, fun _ h => h⟩)
  obtain eD : (bytesAt q.callEntry.mem (Dst s) (L s)).drop (fl s) =
      gathered 64 s.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s) := by
    rw [show L s = fl s + (L s - fl s) by omega_arith, Proof.Cmac.Stream.bytesAt_append,
      List.drop_left' (length_bytesAt _ _ _), ← h.out]
    refine bytesAt_frame fS2 (fun r hr => ?_) (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.b_d.symm.sub_left (dK_sub hp)).sub_right (stk_sub (s := s) (by decide) (by decide))
    · exact (hp.b_d.symm.sub_left (dK_sub hp)).sub_right (stk_sub (s := s) (by decide) (by decide))
  simp only [splitK, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.arg, a0, a1, a2, a3, a4, State.withRegions_mem,
    gU _ (by decide : Reg.rdi ≠ .rsp), gU _ (by decide : Reg.rsi ≠ .rsp), q_di, q_si,
    gS _ (by decide : Reg.rdx ≠ .rsp) (by decide) (by decide) (by decide),
    gS _ (by decide : Reg.rcx ≠ .rsp) (by decide) (by decide) (by decide),
    gS _ (by decide : Reg.r8 ≠ .rsp) (by decide) (by decide) (by decide),
    gS _ (by decide : Reg.r9 ≠ .rsp) (by decide) (by decide) (by decide),
    g.rdx, g.rcx, g.r8, g.r9, hm₂, hflN, ciph_eq hp fU, hk_eq hp fU, iv_eq hp fU, ad_eq hp fU, eF, eD,
    ← (pt_split s).1] at hpost
  obtain hpost := hpost hfl
  obtain b4888 : Region.Sub (below (q.gpr .rsp) (S.fn.code.x86_64Depth + 8)) (tR s) := by
    obtain h₁ := below_sub (sp := q.gpr .rsp) (a := S.fn.code.x86_64Depth + 8) (b := 4848)
      (by have := S.xd; omega_arith) (by decide)
    obtain e : below (SP s - BitVec.ofNat 64 40) 4848 = ⟨SP s - BitVec.ofNat 64 4888, 4848⟩ := by
      simp only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add]
    rw [qsp] at h₁ ⊢
    rw [e] at h₁
    exact fun a h => stk_sub (s := s) (by decide) (by decide) a (h₁ a h)
  rw [q_m] at hfr
  obtain fC : Frame (wR s ++ [tR s]) st.mem s'.mem := by
    refine (hpf'.sub fun r hr => ?_).trans (hfr.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨tR s, by simp, stk_sub (s := s) (by decide) (by decide)⟩
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | rfl
      · exact ⟨dR s, by simp, fun _ h => h⟩
      · exact ⟨tgR s, by simp, fun _ h => h⟩
      · exact ⟨tR s, by simp, b4888⟩
  refine ⟨by rw [r₃, qsp, hP], by rw [hwr', q_wr], fun m u fm => ?_⟩
  -- The `pop` loses the frame's 40 bytes, in the stack below `SP`, apart from
  -- the outputs.
  obtain fm' : Frame [tR s] s'.mem m := by
    rw [hsp] at fm
    exact fm.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨tR s, List.mem_singleton_self _, stk_sub (s := s) (by decide) (by decide)⟩
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · dsimp only
    by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, qsp]
      show SP s - BitVec.ofNat 64 40 + BitVec.ofNat 64 40 = SP s
      exact BitVec.sub_add_cancel _ _
    · have n₁ : r ≠ .rdi := fun e => by subst e; simp [calleeSaved] at hr
      obtain n₂ : r ≠ .rsi := fun e => by subst e; simp [calleeSaved] at hr
      obtain n₃ : r ≠ .r11 := fun e => by subst e; simp [calleeSaved] at hr
      rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), hcs r hr, q_g r n₁ n₂ n₃,
        pushed_gpr _ _ hr', h.saved r hr]
  · exact ((h.frame.trans fC).trans (fm'.mono fun r hr => by simp at hr ⊢; simp [hr])).readW
      (Region.contains_self _ _) (ret_disj hp) (by decide)
  · show Spec.Gcm.encryptWith (ciph s) (hk s) 16 (iv s) (pt s (Cnt s)) (ad s) =
      (bytesAt m (Dst s) (L s), bytesAt m (Tg s) 16)
    rw [bytesAt_frame fm' (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.b_d.symm)
        (Nat.le_of_lt hL),
      bytesAt_frame fm' (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.b_t.symm) (by decide)]
    exact hpost

end

/-- `SPBase` through code that changes no memory, `rsp` or callee-saved register. -/
theorem SPBase.regs {s st st' : State} (h : SPBase s st) (hm : st'.mem = st.mem)
    (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr)
    (hmx : st'.mxcsr = st.mxcsr) : SPBase s st' :=
  ⟨⟨⟨h.toBase.regs hm hcs hrd hwr hmx, hm ▸ h.nonce, hm ▸ h.nonceLen⟩, hm ▸ h.first, hm ▸ h.firstLen⟩, hm ▸ h.out⟩

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-- The path of a text whose slices after the first are short, after the
test: those slices copied to the output after the first's length, and the
text encrypted by `vg_aes_gcm_seal_split` from the first slice where it is
and the rest at the output. -/
theorem copySplit_wp (S : SplitFn M) (hL : L s - fl s < 2 ^ 63) {st : State} (h : Base s (AL s) 0 st)
    (h11 : st.gpr .r11 = W s) (hsi : st.gpr .rsi = Nn s) (hdx : st.gpr .rdx = s.gpr .rcx) :
    WP isa (copySplit S.fn) st (Done s) := by
  unfold copySplit
  refine WP.seq (WP.mono (splitHead_wp hp h h11 hsi hdx) fun s₁ ⟨F₁, C₁⟩ => ?_)
  refine WP.seq (WP.mono (splitKeep_ok hp F₁ C₁) fun s₂ ⟨P₂, r9₂, rdi₂, r11₂, _⟩ => ?_)
  refine WP.seq (WP.mono_mx (by decide) (gatherCopy_wp s₂ (splitGatherPre hp hL P₂.toBase r9₂ rdi₂ r11₂))
    fun s₃ ⟨m₃, k₃⟩ x₃ => ?_)
  obtain B₃ := split_after hp P₂ m₃ k₃ x₃
  refine WP.seq (WP.mono_mx (by decide) (splitArgs_ok hp B₃)
    fun s₄ ⟨dx, cx, r8, r9, ax, r10, di, si, r11, cs, m, rd, wr⟩ x₄ => ?_)
  exact splitCall_ok hp S (B₃.regs m cs rd wr x₄).toSC ⟨dx, cx, r8, r9, ax, r10, di, si, r11⟩

end

end VG.Proof.AesGcm.X86_64.Gather
