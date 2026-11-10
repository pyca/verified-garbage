module

public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.PcCall
public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Fn
public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Time
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # `vg_rsa_private_precompute` on x86: the call of `primes`

Its arguments, `vg_rsa_private_crt`'s with `pre` as the output (its first
`n_len` bytes), `n` as the input, and `p`, `q`, `p` as `dP`, `dQ` and
`qInv` (`primesArgs_ok`), its precondition (`pr_pre`), and the call
(`pr_call`), which leaves `pre` as it was.
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.PrivPre
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Bignum.X86.PrivPre (copies primesPairs primesArgs incoming stackAt statusOffset primes)

section
variable {s t u : State}

/-- The arguments of `primes`. -/
def primesVal (s : State) : Nat → BitVec 32
  | 0 => arg s 0
  | 1 => arg s 3
  | 2 => arg s 2
  | 3 => arg s 3
  | 4 => arg s 2
  | 5 => arg s 3
  | 6 => arg s 4
  | 7 => arg s 5
  | 8 => arg s 6
  | 9 => arg s 7
  | 10 => arg s 4
  | 11 => arg s 5
  | 12 => arg s 6
  | 13 => arg s 7
  | 14 => arg s 4
  | 15 => arg s 5
  | 16 => arg s 8
  | _ => arg s 9

theorem primesArgs_ok (A : PPABI s) (B : Body s t) :
    WP isa (.block primesArgs) t fun u => Body s u ∧ Keeps [.eax] t u ∧
      Frame [⟨slot s 0, 84⟩] t.mem u.mem ∧ u.mem.readW (slot s 80) 32 = t.gpr .eax ∧
      ∀ j < 18, u.mem.readW (slot s (4 * j)) 32 = primesVal s j := by
  rw [show primesArgs = .store (stackAt statusOffset) .eax :: (copies primesPairs ++ []) by simp [primesArgs]]
  refine wp_slot A B (d := 80) (by decide) fun u₁ B₁ M₁ => ?_
  refine wp_copies A primesPairs B₁ (by decide) (by decide) fun u B' K F V => WP.block_nil ?_
  have Fs : Frame (primesPairs.map fun p => argR s p.2) u₁.mem u.mem := F
  refine ⟨B', ⟨fun r hr => by rw [K.1 r hr, M₁.gpr], by rw [K.2.1, M₁.rd], by rw [K.2.2, M₁.wr]⟩, ?_, ?_, ?_⟩
  · have sub : ∀ p ∈ primesPairs, Region.Sub (argR s p.2) ⟨slot s 0, 84⟩ := fun p hp => by
      have := (List.mem_map_of_mem (f := Prod.snd) hp)
      have h17 : p.2 < 18 := by revert this; generalize p.2 = j; decide +revert
      simp only [argR, slot]
      exact Offset.sub _ (by omega) (by omega)
    refine (?_ : Frame [⟨slot s 0, 84⟩] t.mem u₁.mem).trans (Fs.sub fun r hr => ?_)
    · rw [M₁.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
      exact ⟨_, List.mem_singleton_self _, sub p hp⟩
  · rw [Fs.readW (r := ⟨slot s 80, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide), M₁.mem,
      Mem.readW_writeW_self32]
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    have := (List.mem_map_of_mem (f := Prod.snd) hp)
    have h17 : p.2 < 18 := by revert this; generalize p.2 = j; decide +revert
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · intro j hj
    match j, hj with
    | 0, _ =>
      have v := V (0, 0) (by decide)
      simp only at v
      rw [v]; rfl
    | 1, _ =>
      have v := V (3, 1) (by decide)
      simp only at v
      rw [v]; rfl
    | 2, _ =>
      have v := V (2, 2) (by decide)
      simp only at v
      rw [v]; rfl
    | 3, _ =>
      have v := V (3, 3) (by decide)
      simp only at v
      rw [v]; rfl
    | 4, _ =>
      have v := V (2, 4) (by decide)
      simp only at v
      rw [v]; rfl
    | 5, _ =>
      have v := V (3, 5) (by decide)
      simp only at v
      rw [v]; rfl
    | 6, _ =>
      have v := V (4, 6) (by decide)
      simp only at v
      rw [v]; rfl
    | 7, _ =>
      have v := V (5, 7) (by decide)
      simp only at v
      rw [v]; rfl
    | 8, _ =>
      have v := V (6, 8) (by decide)
      simp only at v
      rw [v]; rfl
    | 9, _ =>
      have v := V (7, 9) (by decide)
      simp only at v
      rw [v]; rfl
    | 10, _ =>
      have v := V (4, 10) (by decide)
      simp only at v
      rw [v]; rfl
    | 11, _ =>
      have v := V (5, 11) (by decide)
      simp only at v
      rw [v]; rfl
    | 12, _ =>
      have v := V (6, 12) (by decide)
      simp only at v
      rw [v]; rfl
    | 13, _ =>
      have v := V (7, 13) (by decide)
      simp only at v
      rw [v]; rfl
    | 14, _ =>
      have v := V (4, 14) (by decide)
      simp only at v
      rw [v]; rfl
    | 15, _ =>
      have v := V (5, 15) (by decide)
      simp only at v
      rw [v]; rfl
    | 16, _ =>
      have v := V (8, 16) (by decide)
      simp only at v
      rw [v]; rfl
    | 17, _ =>
      have v := V (9, 17) (by decide)
      simp only at v
      rw [v]; rfl
    | _ + 18, h => omega

def prRd (s : State) : List Region :=
  [⟨argumentPointer s 2, (arg s 3).toNat⟩, ⟨argumentPointer s 2, (arg s 3).toNat⟩,
    ⟨argumentPointer s 4, (arg s 5).toNat⟩, ⟨argumentPointer s 6, (arg s 7).toNat⟩,
    ⟨argumentPointer s 4, (arg s 5).toNat⟩, ⟨argumentPointer s 6, (arg s 7).toNat⟩,
    ⟨argumentPointer s 4, (arg s 5).toNat⟩]
def prWr (s : State) : List Region :=
  [⟨argumentPointer s 0, (arg s 3).toNat⟩, wsR s, ⟨slot s 0, 72⟩]

theorem out_sub (A : PPABI s) : Region.Sub ⟨argumentPointer s 0, (arg s 3).toNat⟩ (preR s) := by
  have hl := A.preLength
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] at hl
  exact Region.sub_prefix (by omega)

theorem pr_pre (A : PPABI s) (B : Body s u) (V : ∀ j < 18, u.mem.readW (slot s (4 * j)) 32 = primesVal s j) :
    (Proof.Rsa.privateCrtContract abi 96).pre (u.callEntry.withRegions (prRd s) (prWr s)) := by
  have hv : ∀ j < 18, arg (u.callEntry.withRegions (prRd s) (prWr s)) j = primesVal s j := fun j hj => by
    rw [callee_arg A B hj]; exact V j hj
  have hl := A.preLength
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] at hl
  have os := out_sub A
  have l := A.stackLow
  have hb := A.stackBound
  simp only [stackBytes] at l
  have pb := A.preBound
  have nb := A.nBound
  have ppb := A.pBound
  have qb := A.qBound
  have wb := A.wsBound
  have lv := A.lengths
  have lv1 := lv.1
  have lv2 := lv.2
  have p1 := A.pPositive
  have p2 := A.pLength
  have q1 := A.qPositive
  have q2 := A.qLength
  have sl := A.scratchLength
  have o_n := A.preN.sub_left os
  have o_p := A.preP.sub_left os
  have o_q := A.preQ.sub_left os
  have o_w := A.preWs.sub_left os
  have n_w := A.nWs
  have p_w := A.pWs
  have q_w := A.qWs
  have o_a := (top_apart (d := 100) (n := 72) (by decide) (A.belowPre.sub_right os)).symm
  have n_a := (top_apart (d := 100) (n := 72) (by decide) A.belowN).symm
  have p_a := (top_apart (d := 100) (n := 72) (by decide) A.belowP).symm
  have q_a := (top_apart (d := 100) (n := 72) (by decide) A.belowQ).symm
  have w_a := (top_apart (d := 100) (n := 72) (by decide) A.belowWs).symm
  have r_o := top_apart (d := 96) (n := 4) (by decide) (A.belowPre.sub_right os)
  have r_n := top_apart (d := 96) (n := 4) (by decide) A.belowN
  have r_p := top_apart (d := 96) (n := 4) (by decide) A.belowP
  have r_q := top_apart (d := 96) (n := 4) (by decide) A.belowQ
  have r_w := top_apart (d := 96) (n := 4) (by decide) A.belowWs
  have r_a : (⟨bot s + BitVec.ofNat 64 96, 4⟩ : Region).Disjoint ⟨slot s 0, 72⟩ :=
    Offset.disjoint _ (by omega) (by omega) (by omega)
  have bs : Region.Sub ⟨bot s, 96⟩ (topR s) := Region.sub_prefix (by simp [stackBytes])
  have b_o := (A.belowPre.sub_right os).sub_left bs
  have b_n := A.belowN.sub_left bs
  have b_p := A.belowP.sub_left bs
  have b_q := A.belowQ.sub_left bs
  have b_w := A.belowWs.sub_left bs
  have b_a : (⟨bot s, 96⟩ : Region).Disjoint ⟨slot s 0, 72⟩ := Offset.base_disjoint _ (by omega) (by omega)
  sig_pre [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [hv 0 (by decide), hv 1 (by decide), hv 2 (by decide), hv 3 (by decide), hv 4 (by decide), hv 5 (by decide), hv 6 (by decide), hv 7 (by decide), hv 8 (by decide), hv 9 (by decide), hv 10 (by decide), hv 11 (by decide), hv 12 (by decide), hv 13 (by decide), hv 14 (by decide), hv 15 (by decide), hv 16 (by decide), hv 17 (by decide), primesVal, callee_argAddr A B]
  rw [sp4 A B, e100_toNat A, e100_below A, e100_sw A]
  repeat' apply And.intro
  all_goals first | (with_reducible assumption) | omega | rfl | trivial

theorem callee_mem (A : PPABI s) (B : Body s u) {rd wr : List Region} :
    Frame [⟨bot s + BitVec.ofNat 64 96, 4⟩] u.mem (u.callEntry.withRegions rd wr).mem := by
  rw [State.withRegions_mem, State.callEntry_mem, sp4 A B, e100_sw A]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-- Bytes apart from what the body writes, as the callee finds them. -/
theorem callee_bytes (A : PPABI s) (B : Body s u) {rd wr : List Region} {a : Addr} {n : Nat}
    (hR : ∀ r ∈ bodyW s, (⟨a, n⟩ : Region).Disjoint r) (hn : n < 2 ^ 32) :
    Spec.Rsa.bytesAt (u.callEntry.withRegions rd wr).mem a n = Spec.Rsa.bytesAt s.mem a n := by
  unfold Spec.Rsa.bytesAt
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [(callee_mem A B).bytes (R := ⟨a, n⟩) (fun r hr => ?_) (by simp; omega) hi]
  · exact B.frame.bytes (R := ⟨a, n⟩) hR (by simp; omega) hi
  · obtain rfl := List.mem_singleton.mp hr
    exact (top_apart (d := 96) (n := 4) (by decide) (hR (topR s) (by simp)).symm).symm

theorem p_apart (A : PPABI s) : ∀ r ∈ bodyW s, (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint r := by
  intro r hr
  simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact A.preP.symm
  · exact A.pWs
  · exact A.belowP.symm

theorem q_apart (A : PPABI s) : ∀ r ∈ bodyW s, (⟨argumentPointer s 6, (arg s 7).toNat⟩ : Region).Disjoint r := by
  intro r hr
  simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact A.preQ.symm
  · exact A.qWs
  · exact A.belowQ.symm

/-- The value of `n`, `p` or `q`. -/
abbrev valueAt (s : State) (i : Nat) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (argumentPointer s i) (arg s (i + 1)).toNat)

/-- What `primes` leaves: the result, `R_p² mod p` and `R_q² mod q` in the working space. -/
def PrOut (s v : State) : Prop :=
  v.gpr .eax = BitVec.ofNat 32 (decide (valueAt s 4 * valueAt s 6 = valueAt s 2)).toNat ∧
  val32 v.mem (argumentPointer s 8) (CrtRt.lo (arg s 3).toNat (.slot .wide 16))
      (2 * Spec.Rsa.primeWords (arg s 5).toNat) =
    2 ^ r2Exp (arg s 5).toNat % CrtRt.safeM (valueAt s 4) ∧
  val32 v.mem (argumentPointer s 8) (CrtRt.lo (arg s 3).toNat (.slot .wide 17))
      (2 * Spec.Rsa.primeWords (arg s 7).toNat) =
    2 ^ r2Exp (arg s 7).toNat % CrtRt.safeM (valueAt s 6)

theorem pr_call {prName : String} (st : stackUse primes ≤ 96) (ns : NoSp primes)
    (A : PPABI s) (B : Body s u) (V : ∀ j < 18, u.mem.readW (slot s (4 * j)) 32 = primesVal s j) :
    WP isa (.call prName primes) u fun v => Body s v ∧ Keeps [.eax, .ecx, .edx] u v ∧
      Frame [wsR s, ⟨bot s, 100⟩] u.mem v.mem ∧ PrOut s v := by
  have os := out_sub A
  have argsSub : Region.Sub ⟨slot s 0, 72⟩ (frameR s) := by
    rw [frame_base A]; exact Offset.sub _ (by omega) (by omega)
  have cw : Covers (prWr s) u.wr := by
    rw [B.wr, A.wr]
    refine Covers.of_forall fun r hr => ?_
    simp only [prWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have hl := A.preLength
      simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] at hl
      exact Covers.one ⟨preR s, by simp, by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega⟩
    · exact Covers.of_mem fun r hr => by simp at hr; subst hr; simp
    · exact Covers.one ⟨frameR s, by simp, by
        rw [frame_base A]; exact Offset.contains _ (by omega) (by omega) (by omega)⟩
  have cr : Covers (prRd s ++ prWr s) (u.rd ++ u.wr) := by
    refine Covers.append_left ?_ (Covers.right cw)
    rw [B.rd, A.rd]
    exact Covers.left (Covers.of_mem fun r hr => by
      simp only [prRd, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  refine WP.mono (body_call verified.1 st ns A B (pr_pre A B V) cr cw fun r hr => ?_)
    fun v ⟨Bv, K, F, w, M, G, post⟩ => ⟨Bv, K, ?_, ?_⟩
  · simp only [prWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨preR s, by simp, os⟩
    · exact ⟨wsR s, by simp, fun _ h => h⟩
    · exact ⟨topR s, by simp, Offset.sub_base _ (by simp [stackBytes])⟩
  · have hv : ∀ j < 18, arg (u.callEntry.withRegions (prRd s) (prWr s)) j = primesVal s j := fun j hj => by
      rw [callee_arg A B hj]; exact V j hj
    obtain ⟨-, -, -, PF⟩ := post
    have ws : (⟨argumentPointer (u.callEntry.withRegions (prRd s) (prWr s)) 16,
        (arg (u.callEntry.withRegions (prRd s) (prWr s)) 17).toNat * 8⟩ : Region) = wsR s := by
      simp only [argumentPointer, hv 16 (by decide), hv 17 (by decide), primesVal]
    rw [ws, M] at PF
    have bl : Region.Sub (below ((u.callEntry.withRegions (prRd s) (prWr s)).gpr .esp) 96) ⟨bot s, 100⟩ := by
      rw [State.withRegions_gpr, State.callEntry_esp]
      have l := A.stackLow
      simp only [stackBytes] at l
      have e : (u.gpr .esp).toNat = (s.gpr .esp).toNat - 96 := by
        rw [B.sp, sub_toNat (by simp only [Impl.Bignum.X86.PrivPre.frameBytes]; omega)]; rfl
      exact fun a h => below_frame A B (Nat.le_refl _) a
        (below_inner (sp := u.gpr .esp) (a := 96) (b := 100) (k := 4) (by decide) (by omega) a h)
    refine ((callee_mem A B).sub fun r hr => ?_).trans (PF.sub fun r hr => ?_)
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨bot s, 100⟩, by simp, Offset.sub_base _ (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨wsR s, by simp, fun _ h => h⟩
      · exact ⟨⟨bot s, 100⟩, by simp, bl⟩
  · have hv : ∀ j < 18, arg (u.callEntry.withRegions (prRd s) (prWr s)) j = primesVal s j := fun j hj => by
      rw [callee_arg A B hj]; exact V j hj
    have cv : ∀ {i a : Nat}, arg (u.callEntry.withRegions (prRd s) (prWr s)) i = arg s a →
        arg (u.callEntry.withRegions (prRd s) (prWr s)) (i + 1) = arg s (a + 1) →
        (∀ r ∈ bodyW s, (⟨argumentPointer s a, (arg s (a + 1)).toNat⟩ : Region).Disjoint r) →
        Crt.componentValue (u.callEntry.withRegions (prRd s) (prWr s)).mem
          (arg (u.callEntry.withRegions (prRd s) (prWr s))) i = valueAt s a := by
      intro i a h₁ h₂ hR
      unfold Crt.componentValue
      rw [h₁, h₂]
      exact congrArg _ (callee_bytes A B hR (arg s (a + 1)).isLt)
    have c2 := cv (i := 2) (a := 2) (hv 2 (by decide)) (hv 3 (by decide)) (n_apart A)
    have c6 := cv (i := 6) (a := 4) (hv 6 (by decide)) (hv 7 (by decide)) (p_apart A)
    have c8 := cv (i := 8) (a := 6) (hv 8 (by decide)) (hv 9 (by decide)) (q_apart A)
    obtain ⟨Pe, P16, P17, -⟩ := post
    rw [c2, c6, c8] at Pe
    rw [c6] at P16
    rw [c8] at P17
    simp only [argumentPointer, hv 16 (by decide), hv 3 (by decide), hv 7 (by decide), hv 9 (by decide),
      primesVal] at P16 P17
    rw [M] at P16 P17
    exact ⟨by rw [← G .eax (by decide)]; exact Pe, P16, P17⟩


end
end VG.Proof.Bignum.X86.PrivPre
