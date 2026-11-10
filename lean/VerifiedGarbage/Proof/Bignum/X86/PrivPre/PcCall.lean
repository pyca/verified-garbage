module
-- separate module: the call of the public precompute, apart from primes' call, which builds on it

public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Args
public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Call
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.Scratch

/-! # `vg_rsa_private_precompute` on x86: the call of `vg_rsa_public_precompute`

Its arguments (`publicArgs_ok`: `pre`, `2 ⌈n_len / 8⌉` words, `n`, `n_len`,
the working space and its words), the state the call enters
(`callee_esp`, `callee_arg`), its precondition with the permissions
narrowed to `n`, `pre`'s first `16 ⌈n_len / 8⌉` bytes, the working space and
the six arguments (`pc_pre`), and the call (`pc_call`).
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.PrivPre
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Bignum.X86.PrivPre (copies preWords publicArgs incoming stackAt)

section
variable {s t u : State}

/-- `2 ⌈n_len / 8⌉`, as `preWords` computes it. -/
abbrev wW (s : State) : BitVec 32 := ((arg s 3 + 7) >>> 3) + ((arg s 3 + 7) >>> 3)

theorem wW_toNat (A : PPABI s) : (wW s).toNat = 2 * Spec.Rsa.modulusWords (arg s 3).toNat := by
  have l := A.lengths
  simp only [Spec.Rsa.lenValid] at l
  simp only [wW, Spec.Rsa.modulusWords, BitVec.toNat_add, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [show (7 : BitVec 32).toNat = 7 from rfl, Nat.mod_eq_of_lt (a := (arg s 3).toNat + 7) (by omega)]
  omega

/-- The arguments of `vg_rsa_public_precompute`. -/
def pubVal (s : State) : Nat → BitVec 32
  | 0 => arg s 0
  | 1 => wW s
  | 2 => arg s 2
  | 3 => arg s 3
  | 4 => arg s 8
  | _ => arg s 9

theorem preWords_ok {is : List Instr} {Q : State → Prop} (A : PPABI s) (B : Body s t)
    (k : ∀ u, Body s u → Keeps [.eax] t u → Frame [argR s 1] t.mem u.mem →
      u.mem.readW (slot s (4 * 1)) 32 = wW s → WP isa (.block is) u Q) :
    WP isa (.block (preWords ++ is)) t Q := by
  simp only [preWords, List.cons_append, List.nil_append]
  refine wp_movS (B.readArg A (by decide)) fun u₁ U₁ _ => wp_addi fun u₂ U₂ => wp_shr (by decide)
    fun u₃ U₃ _ => wp_add fun u₄ U₄ _ => ?_
  have K : Keeps [.eax] t u₄ :=
    ⟨fun r hr => by
      have hr' : r ≠ .eax := by simpa using hr
      rw [U₄.other _ hr', U₃.other _ hr', U₂.other _ hr', U₁.other _ hr'],
      by rw [U₄.rd, U₃.rd, U₂.rd, U₁.rd], by rw [U₄.wr, U₃.wr, U₂.wr, U₁.wr]⟩
  have M : u₄.mem = t.mem := by rw [U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  have B₄ : Body s u₄ := B.next (K.1 _ (by decide)) K.2.1 K.2.2 (by rw [M]; exact Frame.refl _ _)
  refine wp_slot A B₄ (d := 4) (by decide) fun u₅ B₅ M₅ => k u₅ B₅ ?_ ?_ ?_
  · exact ⟨fun r hr => by rw [M₅.gpr]; exact K.1 r hr, by rw [M₅.rd, K.2.1], by rw [M₅.wr, K.2.2]⟩
  · rw [M₅.mem, M]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [M₅.mem, Mem.readW_writeW_self32, U₄.gpr, U₃.gpr, U₂.gpr, U₁.gpr]

theorem publicArgs_ok (A : PPABI s) (B : Body s t) :
    WP isa (.block publicArgs) t fun u => Body s u ∧ Keeps [.eax] t u ∧
      Frame [⟨slot s 0, 24⟩] t.mem u.mem ∧ ∀ j < 6, u.mem.readW (slot s (4 * j)) 32 = pubVal s j := by
  rw [show publicArgs = copies [(0, 0)] ++ (preWords ++ (copies [(2, 2), (3, 3), (8, 4), (9, 5)] ++ [])) by
    simp [publicArgs]]
  have sub : ∀ j < 6, Region.Sub (argR s j) ⟨slot s 0, 24⟩ := fun j hj => by
    simp only [argR, slot]
    rw [show 100 + 4 * j = 100 + 0 + 4 * j by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
    exact Offset.sub_base _ (by omega)
  refine wp_copies A [(0, 0)] B (by decide) (by decide) fun u₁ B₁ K₁ F₁ V₁ => ?_
  refine preWords_ok A B₁ fun u₂ B₂ K₂ F₂ V₂ => ?_
  refine wp_copies A _ B₂ (by decide) (by decide) fun u₃ B₃ K₃ F₃ V₃ => WP.block_nil ?_
  have apart : ∀ {j j'}, j ≠ j' → j < 6 → j' < 6 → (argR s j).Disjoint (argR s j') :=
    fun h hj hj' => argR_apart h (by omega) (by omega)
  refine ⟨B₃, (K₁.trans K₂).trans K₃, ?_, fun j hj => ?_⟩
  · refine ((F₁.sub ?_).trans (F₂.sub ?_)).trans (F₃.sub ?_) <;> intro r hr <;>
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
      exact ⟨_, List.mem_singleton_self _, by rcases hr with rfl | rfl | rfl | rfl <;> exact sub _ (by decide)⟩
  · -- the value of each argument, kept by the later writes
    have r₃ : j < 2 → u₃.mem.readW (slot s (4 * j)) 32 = u₂.mem.readW (slot s (4 * j)) 32 := fun h2 =>
      F₃.readW (r := argR s j) (Region.contains_self _ _) (fun r hr => by
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact argR_apart (by omega) (by omega) (by omega)) (by decide)
    have r₂ : j = 0 → u₂.mem.readW (slot s (4 * j)) 32 = u₁.mem.readW (slot s (4 * j)) 32 := fun h0 =>
      F₂.readW (r := argR s j) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact argR_apart (by omega) (by omega) (by omega))
        (by decide)
    match j, hj, r₃, r₂ with
    | 0, _, r₃, r₂ =>
      have v := V₁ (0, 0) (List.mem_singleton_self _)
      simp only at v
      rw [r₃ (by decide), r₂ rfl, v]; rfl
    | 1, _, r₃, _ => rw [r₃ (by decide), V₂]; rfl
    | 2, _, _, _ =>
      have v := V₃ (2, 2) (by decide)
      simp only at v
      rw [v]; rfl
    | 3, _, _, _ =>
      have v := V₃ (3, 3) (by decide)
      simp only at v
      rw [v]; rfl
    | 4, _, _, _ =>
      have v := V₃ (8, 4) (by decide)
      simp only at v
      rw [v]; rfl
    | 5, _, _, _ =>
      have v := V₃ (9, 5) (by decide)
      simp only at v
      rw [v]; rfl

/-! ## The state a call enters -/

theorem sp4 (A : PPABI s) (B : Body s u) : u.gpr .esp - 4 = s.gpr .esp - BitVec.ofNat 32 100 := by
  have l := A.stackLow
  simp only [stackBytes] at l
  rw [B.sp]
  simp only [Impl.Bignum.X86.PrivPre.frameBytes]
  apply BitVec.eq_of_toNat_eq
  rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, sub_toNat (by rw [sub_toNat (by omega)]; omega),
    sub_toNat (by omega), sub_toNat (by omega)]
  omega

theorem e100_toNat (A : PPABI s) : (s.gpr .esp - BitVec.ofNat 32 100).toNat = (s.gpr .esp).toNat - 100 := by
  have l := A.stackLow
  simp only [stackBytes] at l
  rw [sub_toNat (by omega)]

theorem e100_sw (A : PPABI s) : (s.gpr .esp - BitVec.ofNat 32 100).setWidth 64 = bot s + BitVec.ofNat 64 96 := by
  have := esp_off A (a := 100) (b := 0) (by decide) (by decide)
  simpa using this

theorem e100_below (A : PPABI s) : (s.gpr .esp - BitVec.ofNat 32 100).setWidth 64 - 96#64 = bot s := by
  rw [e100_sw A]
  exact BitVec.add_sub_cancel _ _

theorem callee_esp (A : PPABI s) (B : Body s u) {rd wr : List Region} :
    (u.callEntry.withRegions rd wr).gpr .esp = s.gpr .esp - BitVec.ofNat 32 100 := by
  rw [State.withRegions_gpr, State.callEntry_esp, sp4 A B]

theorem callee_argAddr (A : PPABI s) (B : Body s u) {rd wr : List Region} :
    argAddr (u.callEntry.withRegions rd wr) 0 = slot s 0 := by
  rw [argAddr_withRegions, argAddr_callEntry, B.sp, Nat.mul_zero]
  have := esp_off A (a := 96) (b := 0) (by decide) (by decide)
  simpa only [Impl.Bignum.X86.PrivPre.frameBytes] using this

theorem callee_arg (A : PPABI s) (B : Body s u) {rd wr : List Region} {j : Nat} (hj : j < 18) :
    arg (u.callEntry.withRegions rd wr) j = u.mem.readW (slot s (4 * j)) 32 := by
  have l := A.stackLow
  have h := A.stackBound
  simp only [stackBytes] at l
  have e : (u.gpr .esp).toNat = (s.gpr .esp).toNat - 96 := by
    rw [B.sp, sub_toNat (by simp only [Impl.Bignum.X86.PrivPre.frameBytes]; omega)]; rfl
  rw [arg_withRegions, arg_callEntry (by omega) (by omega), B.sp]
  have := esp_off A (a := 96) (b := 4 * j) (by decide) (by omega)
  simp only [Impl.Bignum.X86.PrivPre.frameBytes] at this ⊢
  rw [this]

/-- A region of the stack the function uses. -/
theorem top_apart {d n : Nat} (h : d + n ≤ 196) {r : Region} (hr : (topR s).Disjoint r) :
    (⟨bot s + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r :=
  hr.sub_left (Offset.sub_base _ (by simpa [stackBytes] using h))

/-! ## The call -/

def pcRd (s : State) : List Region := [⟨argumentPointer s 2, (arg s 3).toNat⟩]
def pcWr (s : State) : List Region :=
  [⟨argumentPointer s 0, (wW s).toNat * 8⟩, wsR s, ⟨slot s 0, 24⟩]

theorem pc_pre (A : PPABI s) (B : Body s u) (V : ∀ j < 6, u.mem.readW (slot s (4 * j)) 32 = pubVal s j) :
    (Spec.Rsa.publicPrecomputeContract abi 96).pre (u.callEntry.withRegions (pcRd s) (pcWr s)) := by
  have hv : ∀ j < 6, arg (u.callEntry.withRegions (pcRd s) (pcWr s)) j = pubVal s j := fun j hj => by
    rw [callee_arg A B (by omega)]; exact V j hj
  have w := wW_toNat A
  have hl := A.preLength
  have lv := A.lengths
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords] at hl
  have preSub : Region.Sub ⟨argumentPointer s 0, (wW s).toNat * 8⟩ (preR s) := Region.sub_prefix (by omega)
  have top := A.belowPre
  sig_pre [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argSlots, argVal, argBytes,
    stackBelow]
  simp only [hv 0 (by decide), hv 1 (by decide), hv 2 (by decide), hv 3 (by decide), hv 4 (by decide),
    hv 5 (by decide), pubVal, callee_argAddr A B]
  rw [sp4 A B, e100_toNat A, e100_below A, e100_sw A]
  have l := A.stackLow
  have hb := A.stackBound
  simp only [stackBytes] at l
  have argsTop : ∀ {r : Region}, (topR s).Disjoint r → (⟨slot s 0, 24⟩ : Region).Disjoint r :=
    fun h => top_apart (d := 100) (by decide) h
  have retTop : ∀ {r : Region}, (topR s).Disjoint r → (⟨bot s + BitVec.ofNat 64 96, 4⟩ : Region).Disjoint r :=
    fun h => top_apart (by decide) h
  have belowTop : ∀ {r : Region}, (topR s).Disjoint r → (⟨bot s, 96⟩ : Region).Disjoint r :=
    fun h => h.sub_left (Region.sub_prefix (by simp [stackBytes]))
  refine ⟨by omega, by omega, rfl, rfl, A.preN.sub_left preSub, A.preWs.sub_left preSub,
    (argsTop (A.belowPre.sub_right preSub)).symm, A.nWs, (argsTop A.belowN).symm, (argsTop A.belowWs).symm,
    retTop (A.belowPre.sub_right preSub), retTop A.belowN, retTop A.belowWs,
    Offset.disjoint _ (by omega) (by omega) (by omega),
    belowTop (A.belowPre.sub_right preSub), belowTop A.belowN, belowTop A.belowWs,
    (Offset.base_disjoint _ (by omega) (by omega)), by have := A.preBound; omega, A.nBound, A.wsBound, lv,
    by rw [w]; rfl, VG.Proof.Rsa.publicScratch_le lv A.scratchLength⟩

/-- What `vg_rsa_public_precompute` leaves: its result, and `n`'s values at `pre`. -/
def PcOut (s v : State) : Prop :=
  match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat) with
  | some ws => v.gpr .eax = 1 ∧
      Spec.Rsa.wordsAt v.mem (argumentPointer s 0) (2 * Spec.Rsa.modulusWords (arg s 3).toNat) = ws
  | none => v.gpr .eax = 0 ∧
      Spec.Rsa.wordsAt v.mem (argumentPointer s 0) (2 * Spec.Rsa.modulusWords (arg s 3).toNat) =
        List.replicate (2 * Spec.Rsa.modulusWords (arg s 3).toNat) 0

/-- `n`'s bytes, apart from what the body writes. -/
theorem n_apart (A : PPABI s) : ∀ r ∈ bodyW s, (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint r := by
  intro r hr
  simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact A.preN.symm
  · exact A.nWs
  · exact A.belowN.symm

theorem Body.nBytes (A : PPABI s) (B : Body s u) :
    Spec.Rsa.bytesAt u.mem (argumentPointer s 2) (arg s 3).toNat =
      Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat := by
  unfold Spec.Rsa.bytesAt
  refine List.map_congr_left fun i hi => ?_
  have := (arg s 3).isLt
  exact B.frame.bytes (R := ⟨argumentPointer s 2, (arg s 3).toNat⟩) (n_apart A) (by simp; omega)
    (List.mem_range.mp hi)

theorem pc_covers (A : PPABI s) (B : Body s u) :
    Covers (pcRd s ++ pcWr s) (u.rd ++ u.wr) ∧ Covers (pcWr s) u.wr := by
  have w := wW_toNat A
  have hl := A.preLength
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords] at hl
  have cw : Covers (pcWr s) u.wr := by
    rw [B.wr, A.wr]
    refine Covers.of_forall fun r hr => ?_
    simp only [pcWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Covers.one ⟨preR s, by simp, by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega⟩
    · exact Covers.of_mem fun r hr => by simp at hr; subst hr; simp
    · exact Covers.one ⟨frameR s, by simp, by
        rw [frame_base A]; exact Offset.contains _ (by omega) (by omega) (by omega)⟩
  have cr : Covers (pcRd s ++ pcWr s) (u.rd ++ u.wr) := by
    refine Covers.append_left ?_ (Covers.right cw)
    rw [B.rd, A.rd]
    exact Covers.left (Covers.of_mem fun r hr => by simp [pcRd] at hr; subst hr; simp)
  exact ⟨cr, cw⟩

theorem pc_call {pcName : String} {pc : Prog isa}
    (pv : Verified target pc (Spec.Rsa.publicPrecomputeContract abi 96)) (pst : stackUse pc ≤ 96) (pns : NoSp pc)
    (A : PPABI s) (B : Body s u) (V : ∀ j < 6, u.mem.readW (slot s (4 * j)) 32 = pubVal s j) :
    WP isa (.call pcName pc) u fun v => Body s v ∧ Keeps [.eax, .ecx, .edx] u v ∧
      Frame (pcWr s ++ [⟨bot s, 100⟩]) u.mem v.mem ∧ PcOut s v := by
  have w := wW_toNat A
  have hl := A.preLength
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords] at hl
  have preSub : Region.Sub ⟨argumentPointer s 0, (wW s).toNat * 8⟩ (preR s) := Region.sub_prefix (by omega)
  have argsSub : Region.Sub ⟨slot s 0, 24⟩ (frameR s) := by
    rw [frame_base A]; exact Offset.sub _ (by omega) (by omega)
  obtain ⟨cr, cw⟩ := pc_covers A B
  refine WP.mono (body_call pv.1 pst pns A B (pc_pre A B V) cr cw fun r hr => ?_) fun v ⟨Bv, K, F, x, M, G, post⟩ =>
    ⟨Bv, K, F, ?_⟩
  · simp only [pcWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨preR s, by simp, preSub⟩
    · exact ⟨wsR s, by simp, fun _ h => h⟩
    · exact ⟨topR s, by simp, Offset.sub_base _ (by simp [stackBytes])⟩
  have hv : ∀ j < 6, arg (u.callEntry.withRegions (pcRd s) (pcWr s)) j = pubVal s j := fun j hj => by
    rw [callee_arg A B (by omega)]; exact V j hj
  sig_post [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argSlots, argVal, argBytes] at post
  simp only [hv 0 (by decide), hv 1 (by decide), hv 2 (by decide), hv 3 (by decide), pubVal, w] at post
  rw [BitVec.setWidth_append_eq_right, M, G .eax (by decide)] at post
  have hb : Spec.Rsa.bytesAt (u.mem.writeW ((u.gpr .esp - 4).setWidth 64) (u.unknowns 0)) (argumentPointer s 2)
      (arg s 3).toNat = Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat := by
    rw [← B.nBytes A]
    unfold Spec.Rsa.bytesAt
    refine List.map_congr_left fun i hi => ?_
    have := (arg s 3).isLt
    refine Frame.bytes (rs := [⟨(u.gpr .esp - 4).setWidth 64, 4⟩])
      ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      (R := ⟨argumentPointer s 2, (arg s 3).toNat⟩) (fun r hr => ?_) (by simp; omega) (List.mem_range.mp hi)
    obtain rfl := List.mem_singleton.mp hr
    rw [sp4 A B, e100_sw A]
    exact (top_apart (d := 96) (n := 4) (by decide) A.belowN).symm
  rw [hb] at post
  exact post

end
end VG.Proof.Bignum.X86.PrivPre
